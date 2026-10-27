#!/usr/bin/env python3
"""
Nigerian news corpus pipeline: historical archives -> Supabase.

Outlets: Punch, Vanguard, The Guardian Nigeria, Premium Times, ThisDay, Daily Trust

Three steps, each resumable (stop it any time; run it again and it continues):

  1. discover   Find every article URL published in a date range and add it to the
                crawl_queue table. For each outlet it tries the WordPress API first
                (exact publish dates, 100 posts per request) and falls back to the
                site's XML sitemaps if the API is blocked or disallowed by robots.txt.

  2. crawl      Work through the queue: fetch each article (fast HTTP first, a real
                browser only if the site blocks it), extract the fields and upsert
                the article into Supabase. Nothing is saved to your disk.
                The six outlets are interleaved, so a slow site (Vanguard asks for 10 s
                between requests) doesn't hold up the others.

  3. update     For daily use: pull the latest articles from each RSS feed into the
                queue and crawl them. Schedule this once a day to keep the corpus
                current (it also stops a free Supabase project from pausing).

  status        Show progress per outlet.

Examples
  python ng_news_pipeline.py discover --since 2025-01-01 --until 2025-12-31
  python ng_news_pipeline.py discover --since 2025-01-01 --max-per-day 30 --outlets vanguard,punch
  python ng_news_pipeline.py crawl
  python ng_news_pipeline.py crawl --max-articles 500       # a quick first batch
  python ng_news_pipeline.py update
  python ng_news_pipeline.py status

Needs SUPABASE_URL and SUPABASE_KEY (the secret / service_role key) in a .env file
next to this script. Run schema.sql in the Supabase SQL editor first.

Finding articles (discover --method auto tries these in order per outlet):
  WordPress API -> XML sitemaps -> WordPress day archives (/YYYY/MM/DD/)
Punch and Vanguard protect their API and sitemaps with Cloudflare, so they use the day
archives, which are ordinary public pages.

The crawler obeys robots.txt (all "User-agent: *" sections, wildcards, and the
strictest Crawl-delay stated; Vanguard asks for 30 s) and finds articles only through
the sites' own API, sitemaps, archive pages and feeds. Keep the corpus for research;
republishing article text needs the publishers' permission.
"""

import argparse
import gzip
import hashlib
import html
import json
import logging
import os
import random
import re
import sys
import time
from collections import Counter, defaultdict, deque
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import urlencode, urljoin, urlparse
from zoneinfo import ZoneInfo

from dateutil import parser as dateparser
from dotenv import load_dotenv
from scrapling.fetchers import Fetcher

try:  # browser-based fallback; needs `scrapling install`
    from scrapling.fetchers import StealthyFetcher
except Exception:  # pragma: no cover
    StealthyFetcher = None

logging.getLogger("scrapling").setLevel(logging.WARNING)
try:  # Windows consoles/log files can choke on characters like the naira sign
    sys.stderr.reconfigure(errors="replace")
except AttributeError:
    pass

LAGOS = ZoneInfo("Africa/Lagos")
UTC = timezone.utc

# --------------------------------------------------------------------------- #
# Outlets (keys must match the `key` column of the outlets table)
# --------------------------------------------------------------------------- #
OUTLETS = {
    "punch": {
        "name": "Punch", "domain": "punchng.com", "home": "https://punchng.com/",
        "feeds": ["https://punchng.com/feed/"],
    },
    "vanguard": {
        "name": "Vanguard", "domain": "vanguardngr.com", "home": "https://www.vanguardngr.com/",
        "feeds": ["https://www.vanguardngr.com/feed/"],
    },
    "guardian": {
        "name": "The Guardian Nigeria", "domain": "guardian.ng", "home": "https://guardian.ng/",
        "feeds": ["https://guardian.ng/feed/"],
    },
    "premiumtimes": {
        "name": "Premium Times", "domain": "premiumtimesng.com", "home": "https://www.premiumtimesng.com/",
        "feeds": ["https://www.premiumtimesng.com/feed"],
    },
    "thisday": {
        "name": "ThisDay", "domain": "thisdaylive.com", "home": "https://www.thisdaylive.com/",
        "feeds": ["https://www.thisdaylive.com/feed/"],
    },
    "dailytrust": {
        "name": "Daily Trust", "domain": "dailytrust.com", "home": "https://dailytrust.com/",
        "feeds": ["https://dailytrust.com/feed/"],
    },
}

# URLs that are never articles
NON_ARTICLE = re.compile(
    r"/(tag|category|author|page|feed|search|wp-content|wp-json)/|\.(jpe?g|png|gif|webp|pdf|mp4|xml)$", re.I
)

# Where the article body usually lives, most specific first
BODY_SELECTORS = [
    "[itemprop='articleBody']", "div.entry-content", "div.post-content", "div.td-post-content",
    "div.article-content", "div.article-body", "div.single-content", "div.post-body",
    "div.story-content", "div.content-body", "article",
]
JUNK_PARA = re.compile(
    r"^(read also|also read|read more|related|advertisement|sponsored|subscribe|click here|"
    r"follow us|join our|download our|support (?:our|premium)|copyright|all rights reserved|"
    r"kindly share|share this)", re.I,
)
BLOCK_MARKERS = (
    "just a moment...", "attention required! | cloudflare",
    "enable javascript and cookies to continue", "access denied",
)
MIN_OK_WORDS = 80


def log(msg=""):
    print(msg, file=sys.stderr, flush=True)


def clean(text):
    return re.sub(r"\s+", " ", str(text or "")).strip()


# --------------------------------------------------------------------------- #
# Dates
# --------------------------------------------------------------------------- #
def to_utc(value):
    """Parse almost any date string; naive times are taken as Lagos time."""
    if not value:
        return None
    try:
        dt = dateparser.parse(str(value))
    except (ValueError, OverflowError, TypeError):
        return None
    if dt is None:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=LAGOS)
    return dt.astimezone(UTC)


def iso(dt):
    return dt.isoformat() if dt else None


def window_bounds(since, until):
    """[start, end) in UTC for whole Lagos calendar days since..until inclusive."""
    start = datetime.combine(since, datetime.min.time(), LAGOS).astimezone(UTC)
    end = datetime.combine(until + timedelta(days=1), datetime.min.time(), LAGOS).astimezone(UTC)
    return start, end


URL_DATE = re.compile(r"/((?:19|20)\d\d)/(\d{1,2})(?:/(\d{1,2}))?/")


def url_date(url):
    """Date embedded in the URL path, e.g. /2025/03/14/slug or /2025/03/slug.
    Returns (date, 'day' | 'month') or (None, None)."""
    m = URL_DATE.search(urlparse(url).path)
    if not m:
        return None, None
    y, mo, d = int(m.group(1)), int(m.group(2)), m.group(3)
    try:
        if d:
            return date(y, mo, int(d)), "day"
        return date(y, mo, 1), "month"
    except ValueError:
        return None, None


# --------------------------------------------------------------------------- #
# Fetching
# --------------------------------------------------------------------------- #
def raw_body(page):
    body = getattr(page, "body", None)
    if isinstance(body, bytes):
        return body
    if isinstance(body, str):
        return body.encode("utf-8", "ignore")
    return str(getattr(page, "html_content", "") or "").encode("utf-8", "ignore")


def looks_blocked(page, min_size):
    if page is None or getattr(page, "status", 0) != 200:
        return True
    body = raw_body(page)
    if len(body) < min_size:
        return True
    head = body[:5000].decode("utf-8", "ignore").lower()
    return any(marker in head for marker in BLOCK_MARKERS)


def fetch(url, use_stealth=True, min_size=2000, timeout=30):
    """Fast HTTP first; real browser only if the site pushes back.
    Returns (page, method, error)."""
    error = None
    try:
        page = Fetcher.get(url, impersonate="chrome", stealthy_headers=True, timeout=timeout, retries=2)
        if not looks_blocked(page, min_size):
            return page, "http", None
        error = f"http status {getattr(page, 'status', '?')} / looked blocked"
    except Exception as e:
        error = f"http {e.__class__.__name__}: {str(e)[:200]}"

    if use_stealth and StealthyFetcher is not None:
        try:
            page = StealthyFetcher.fetch(
                url, headless=True, network_idle=True, solve_cloudflare=True,
                block_ads=True, disable_resources=True, timeout=timeout * 1000,
            )
            if not looks_blocked(page, min_size):
                return page, "browser", None
            error += f"; browser status {getattr(page, 'status', '?')} / looked blocked"
        except Exception as e:
            error += f"; browser {e.__class__.__name__}: {str(e)[:200]}"
    return None, None, error


def fetch_bytes(url, use_stealth=False):
    """For sitemaps / feeds / JSON (small, non-HTML responses)."""
    page, _, err = fetch(url, use_stealth=use_stealth, min_size=2)
    if page is None:
        return None, err
    data = raw_body(page)
    if data[:2] == b"\x1f\x8b":  # .xml.gz sitemaps
        try:
            data = gzip.decompress(data)
        except OSError:
            pass
    return data, None


class RobotsRules:
    """The rules that apply to a generic crawler ("User-agent: *").

    Follows RFC 9309 (the robots.txt standard) rather than Python's built-in
    parser, which only reads the FIRST "User-agent: *" section and ignores
    wildcards. Vanguard's file has two such sections; its Disallow rules and
    30-second Crawl-delay are in the second one.
      - every "User-agent: *" section is merged
      - '*' and '$' wildcards are supported
      - the longest matching rule wins; Allow wins a tie
      - Crawl-delay: the strictest (largest) value stated
    """

    def __init__(self, text):
        self.rules = []  # (is_allow, pattern_length, regex)
        self.delay = 0.0
        self.sitemaps = []
        groups, current, last_was_agent = [], None, False
        for raw in text.splitlines():
            line = raw.split("#", 1)[0].strip()
            if ":" not in line:
                continue
            key, value = (part.strip() for part in line.split(":", 1))
            key = key.lower()
            if key == "sitemap":
                self.sitemaps.append(value)
                continue
            if key == "user-agent":
                if current is None or not last_was_agent:
                    current = {"agents": [], "rules": [], "delays": []}
                    groups.append(current)
                current["agents"].append(value.lower())
                last_was_agent = True
                continue
            last_was_agent = False
            if current is None:
                continue
            if key in ("allow", "disallow") and value:
                current["rules"].append((key == "allow", value))
            elif key == "crawl-delay":
                try:
                    current["delays"].append(float(value))
                except ValueError:
                    pass
        for g in groups:
            if "*" not in g["agents"]:
                continue
            for is_allow, path in g["rules"]:
                pattern = re.escape(path).replace(r"\*", ".*")
                if pattern.endswith(r"\$"):
                    pattern = pattern[:-2] + "$"
                self.rules.append((is_allow, len(path), re.compile(pattern)))
            self.delay = max([self.delay] + g["delays"])

    def allowed(self, url):
        p = urlparse(url)
        target = (p.path or "/") + (f"?{p.query}" if p.query else "")
        best = None  # (length, is_allow)
        for is_allow, length, regex in self.rules:
            if regex.match(target):
                if best is None or length > best[0] or (length == best[0] and is_allow):
                    best = (length, is_allow)
        return True if best is None else best[1]


class Robots:
    """robots.txt rules per site, fetched with Scrapling (urllib's own request is
    often rejected, which would wrongly mark the whole site as disallowed)."""

    def __init__(self):
        self.cache = {}

    def _get(self, url):
        p = urlparse(url)
        root = f"{p.scheme}://{p.netloc}"
        if root not in self.cache:
            rules = None
            try:
                page = Fetcher.get(root + "/robots.txt", impersonate="chrome", timeout=20)
                if page.status == 200:
                    rules = RobotsRules(raw_body(page).decode("utf-8", "ignore"))
                else:
                    log(f"  note: {root}/robots.txt returned {page.status}; no rules applied")
            except Exception as e:
                log(f"  note: couldn't read {root}/robots.txt ({e.__class__.__name__}); no rules applied")
            self.cache[root] = rules
        return self.cache[root]

    def allowed(self, url):
        rules = self._get(url)
        return rules is None or rules.allowed(url)

    def crawl_delay(self, url):
        rules = self._get(url)
        return rules.delay if rules else 0.0

    def sitemaps(self, url):
        rules = self._get(url)
        return list(rules.sitemaps) if rules else []


class Pacer:
    """Keeps a polite gap between requests to the same site."""

    def __init__(self, base_delay, robots):
        self.base = base_delay
        self.robots = robots
        self.next_ok = defaultdict(float)
        self.delays = {}

    def delay_for(self, url):
        host = urlparse(url).netloc
        if host not in self.delays:
            self.delays[host] = max(self.base, self.robots.crawl_delay(url))
        return self.delays[host]

    def ready_at(self, url):
        return self.next_ok[urlparse(url).netloc]

    def wait(self, url):
        host = urlparse(url).netloc
        pause = self.next_ok[host] - time.monotonic()
        if pause > 0:
            time.sleep(pause)
        d = self.delay_for(url)
        self.next_ok[host] = time.monotonic() + d + random.uniform(0, d * 0.3)


# --------------------------------------------------------------------------- #
# Supabase
# --------------------------------------------------------------------------- #
class Store:
    def __init__(self, url, key):
        from supabase import create_client
        self.sb = create_client(url, key)

    @staticmethod
    def _run(query, what):
        for attempt in range(4):
            try:
                return query.execute()
            except Exception as e:
                if attempt == 3:
                    raise
                wait = 2 ** attempt * 3
                log(f"    database error during {what} ({e.__class__.__name__}: {str(e)[:150]}); retry in {wait}s")
                time.sleep(wait)

    def outlet_ids(self):
        res = self._run(self.sb.table("outlets").select("id,key"), "load outlets")
        return {r["key"]: r["id"] for r in res.data}

    def enqueue(self, rows):
        for i in range(0, len(rows), 500):
            chunk = rows[i:i + 500]
            self._run(
                self.sb.table("crawl_queue").upsert(
                    chunk, on_conflict="url", ignore_duplicates=True, returning="minimal"
                ),
                "enqueue",
            )

    def pending(self, outlet_id, limit, since=None):
        q = (self.sb.table("crawl_queue")
             .select("url,outlet_id,published_hint,window_start,window_end,attempts,discovered_via")
             .eq("status", "pending").eq("outlet_id", outlet_id))
        if since is not None:  # only articles published on/after this moment
            q = q.gte("published_hint", iso(since))
        q = (q.order("attempts")  # retries go to the back of the line
             .order("published_hint", desc=True, nullsfirst=False)
             .limit(limit))
        return self._run(q, "load queue").data

    def mark(self, url, status, error=None, attempts=None):
        fields = {"status": status, "last_error": error, "updated_at": datetime.now(UTC).isoformat()}
        if attempts is not None:
            fields["attempts"] = attempts
        self._run(self.sb.table("crawl_queue").update(fields, returning="minimal").eq("url", url), "update queue")

    def save_article(self, row):
        self._run(
            self.sb.table("articles").upsert(row, on_conflict="url", returning="minimal", default_to_null=False),
            "save article",
        )

    def archive_days(self, outlet_id, start, end):
        """Days already queued from the day archives (for resuming discovery)."""
        days, offset = set(), 0
        while True:
            q = (self.sb.table("crawl_queue").select("published_hint")
                 .eq("outlet_id", outlet_id).eq("discovered_via", "archive")
                 .gte("published_hint", iso(start)).lt("published_hint", iso(end))
                 .order("published_hint").range(offset, offset + 999))
            data = self._run(q, "load archive progress").data
            for r in data:
                dt = to_utc(r["published_hint"])
                if dt:
                    days.add(dt.astimezone(LAGOS).date())
            if len(data) < 1000:
                return days
            offset += 1000

    def view(self, name):
        return self._run(self.sb.table(name).select("*"), f"read {name}").data


def open_store():
    here = Path(__file__).resolve().parent
    load_dotenv(here / ".env")
    load_dotenv(Path.cwd() / ".env")
    url, key = os.getenv("SUPABASE_URL"), os.getenv("SUPABASE_KEY")
    if not url or not key:
        sys.exit("Missing SUPABASE_URL / SUPABASE_KEY. Copy .env.example to .env and fill them in.")
    return Store(url, key)


# --------------------------------------------------------------------------- #
# Discovery: WordPress API
# --------------------------------------------------------------------------- #
def month_windows(start, end):
    """Split [start, end) (Lagos-local datetimes) into calendar-month chunks."""
    cur = start
    while cur < end:
        nxt = (cur.replace(day=1) + timedelta(days=32)).replace(day=1, hour=0, minute=0, second=0)
        yield cur, min(nxt, end)
        cur = min(nxt, end)


def discover_wp_api(outlet, since, until, robots, pacer):
    """Returns a list of candidates, or None if the API isn't usable for this site."""
    api = urljoin(outlet["home"], "wp-json/wp/v2/posts")
    if not robots.allowed(api):
        log("  WordPress API disallowed by robots.txt -> using sitemaps")
        return None

    start = datetime.combine(since, datetime.min.time())
    end = datetime.combine(until + timedelta(days=1), datetime.min.time())
    found, first = [], True
    for lo, hi in month_windows(start, end):
        page_no, month_count = 1, 0
        while True:
            params = {
                "after": lo.strftime("%Y-%m-%dT%H:%M:%S"), "before": hi.strftime("%Y-%m-%dT%H:%M:%S"),
                "per_page": 100, "page": page_no, "orderby": "date", "order": "asc",
                "_fields": "link,date_gmt,date",
            }
            url = f"{api}?{urlencode(params)}"
            pacer.wait(url)
            data, err = fetch_bytes(url)
            posts = None
            if data:
                try:
                    posts = json.loads(data)
                except ValueError:
                    posts = None
            if not isinstance(posts, list):
                if first:
                    log(f"  WordPress API not usable ({err or 'not JSON'}) -> using sitemaps")
                    return None
                # WordPress answers past-the-last-page with an error object: month done
                break
            first = False
            for p in posts:
                link = p.get("link")
                when = to_utc((p.get("date_gmt") + "Z") if p.get("date_gmt") else p.get("date"))
                if link:
                    found.append({"url": link, "hint": when, "via": "wp-api"})
            month_count += len(posts)
            if len(posts) < 100:
                break
            page_no += 1
        log(f"  {lo:%Y-%m}: {month_count} posts")
    return found or None


# --------------------------------------------------------------------------- #
# Discovery: XML sitemaps
# --------------------------------------------------------------------------- #
LOC = re.compile(r"<loc>\s*(?:<!\[CDATA\[)?\s*(.*?)\s*(?:\]\]>)?\s*</loc>", re.S | re.I)
LASTMOD = re.compile(r"<lastmod>\s*(.*?)\s*</lastmod>", re.S | re.I)
NEWS_DATE = re.compile(r"<(?:\w+:)?publication_date>\s*(.*?)\s*</(?:\w+:)?publication_date>", re.S | re.I)
SM_BLOCK = re.compile(r"<sitemap\b[^>]*>(.*?)</sitemap>", re.S | re.I)
URL_BLOCK = re.compile(r"<url\b[^>]*>(.*?)</url>", re.S | re.I)


def parse_sitemap(data):
    """Returns ('index', [(loc, lastmod)]) or ('urlset', [(loc, lastmod, news_date)])."""
    text = data.decode("utf-8", "ignore")
    blocks = SM_BLOCK.findall(text)
    if blocks:
        out = []
        for b in blocks:
            loc = LOC.search(b)
            lm = LASTMOD.search(b)
            if loc:
                out.append((html.unescape(loc.group(1)), to_utc(lm.group(1)) if lm else None))
        return "index", out
    out = []
    for b in URL_BLOCK.findall(text):
        loc = LOC.search(b)
        lm = LASTMOD.search(b)
        nd = NEWS_DATE.search(b)
        if loc:
            out.append((html.unescape(loc.group(1)),
                        to_utc(lm.group(1)) if lm else None,
                        to_utc(nd.group(1)) if nd else None))
    return "urlset", out


SKIP_SITEMAP = re.compile(
    r"tag|categor|author|user|page-sitemap|posts-page|misc|taxonom|attachment|image_of_the_day|"
    r"web-?stor|video|news-sitemap|local-sitemap", re.I)


def post_children(children):
    """Keep only the child sitemaps that list articles."""
    name = lambda u: urlparse(u).path.rsplit("/", 1)[-1]
    posts = [c for c in children if "post" in name(c[0]).lower() and not SKIP_SITEMAP.search(name(c[0]))]
    return posts or [c for c in children if not SKIP_SITEMAP.search(name(c[0]))]


def keep_entry(loc, lastmod, news_date, start, end, grace):
    """Decide whether a sitemap entry might be inside the window, and estimate
    its publish date. Returns (keep, hint)."""
    d, precision = url_date(loc)
    if precision == "day":
        hint = datetime.combine(d, datetime.min.time(), LAGOS).astimezone(UTC)
        return start <= hint < end, hint
    if precision == "month":
        m_start = datetime.combine(d, datetime.min.time(), LAGOS).astimezone(UTC)
        m_end = datetime.combine((d + timedelta(days=32)).replace(day=1), datetime.min.time(), LAGOS).astimezone(UTC)
        if not (m_start < end and m_end > start):
            return False, None
        hint = lastmod if lastmod and m_start <= lastmod < m_end else max(m_start, start)
        return True, hint
    if news_date:
        return start <= news_date < end, news_date
    if lastmod:
        # lastmod >= publish date, so anything last modified before the window
        # can't belong to it. Articles edited long after the window are dropped
        # (rare; adjust --lastmod-grace-days).
        return start <= lastmod < end + grace, lastmod
    return True, None  # no date info at all: keep, the crawl step checks the page


def discover_sitemaps(outlet, since, until, robots, pacer, grace_days):
    start, end = window_bounds(since, until)
    grace = timedelta(days=grace_days)
    home = outlet["home"]
    roots = [u for u in robots.sitemaps(home) if "news" not in u.lower()]
    roots += [urljoin(home, p) for p in ("sitemap_index.xml", "wp-sitemap.xml", "sitemap.xml")]
    seen_roots, found = set(), []

    def walk(url, depth, label):
        pacer.wait(url)
        # no browser here: a browser receives the styled, human-readable sitemap,
        # which has no machine-readable list in it, and it's slow
        data, err = fetch_bytes(url, use_stealth=False)
        if not data:
            log(f"    couldn't read {url}: {err}")
            return
        kind, entries = parse_sitemap(data)
        if kind == "index" and depth < 3:
            children = post_children(entries)
            # a child sitemap last modified before the window can't hold articles from it
            children = [c for c in children if c[1] is None or c[1] >= start]
            log(f"  {label}: {len(children)} article sitemaps to scan")
            for i, (child, _) in enumerate(children, 1):
                walk(child, depth + 1, label)
                if i % 25 == 0 or i == len(children):
                    log(f"    scanned {i}/{len(children)} sitemaps, {len(found)} articles in range so far")
        elif kind == "urlset":
            for loc, lastmod, news_date in entries:
                keep, hint = keep_entry(loc, lastmod, news_date, start, end, grace)
                if keep:
                    found.append({"url": loc, "hint": hint, "via": "sitemap"})

    for root in roots:
        if root in seen_roots or not robots.allowed(root):
            continue
        seen_roots.add(root)
        walk(root, 0, urlparse(root).path.lstrip("/"))
        if found:
            break
    return found


# --------------------------------------------------------------------------- #
# Discovery: WordPress day archives (/YYYY/MM/DD/) for sites that block both
# the API and their sitemaps (Punch and Vanguard). Every article comes with its
# exact publish day. Days are queued one at a time, so an interrupted run
# resumes after the last finished day.
# --------------------------------------------------------------------------- #
ARCHIVE_PATH = re.compile(r"^/(?:index\.php/)?\d{4}/\d{1,2}(?:/\d{1,2})?/?(?:page/\d+/?)?$")
LIST_LINKS = ("article a[href], h1 a[href], h2 a[href], h3 a[href], h4 a[href], "
              ".entry-title a[href], .post-title a[href]")
MAX_PAGES_PER_DAY = 60


def article_like(url, outlet):
    p = urlparse(url)
    if not p.netloc.lower().endswith(outlet["domain"]):
        return False
    path = p.path or "/"
    if path == "/" or NON_ARTICLE.search(path) or ARCHIVE_PATH.match(path):
        return False
    slug = [s for s in path.split("/") if s]
    return bool(slug) and slug[-1].count("-") >= 2  # headlines are several words long


def page_article_links(page, base, outlet):
    """Article links in a listing page's main list, in page order."""
    def collect(nodes):
        out = []
        for a in nodes:
            u = urljoin(base, a.attrib.get("href", "")).split("#")[0].split("?")[0]
            if article_like(u, outlet) and u not in out:
                out.append(u)
        return out
    links = collect(page.css(LIST_LINKS))
    return links if len(links) >= 3 else collect(page.css("a[href]"))


def total_pages_known(page, day_url):
    """True when page 1 shows how many pages the day has: numbered links beyond
    the next page, or no next page at all. A bare 'Older posts' link doesn't."""
    nxt, last, _ = pagination_info(page, day_url)
    return last > 2 or not nxt


def pagination_info(page, day_url):
    """(next page URL or None, highest page number linked, theme uses rel links?)"""
    nxt = ""
    for sel in ('link[rel="next"]', 'a[rel="next"]', "a.next", ".nav-previous a", ".pagination-next a"):
        nxt = first_attr(page, sel, "href")
        if nxt:
            break
    has_rel = bool(page.css('link[rel="next"], link[rel="prev"], a[rel="next"], a[rel="prev"]'))
    numbers = [1]
    pat = re.compile(re.escape(urlparse(day_url).path) + r"page/(\d+)/?$")
    for a in page.css("a[href]"):
        m = pat.search(urlparse(urljoin(day_url, a.attrib.get("href", ""))).path)
        if m:
            numbers.append(int(m.group(1)))
    if nxt and not urlparse(urljoin(day_url, nxt)).path.startswith(urlparse(day_url).path):
        nxt = None  # never wander outside this day
    return (urljoin(day_url, nxt) if nxt else None), max(numbers), has_rel


def discover_archives(outlet, outlet_id, since, until, robots, pacer, store, max_per_day):
    """Walks the day archives and queues each day as it finishes. Returns the
    number of URLs queued, or None if the archives can't be used."""
    home = outlet["home"]
    probe = urljoin(home, f"{since:%Y/%m/%d}/")
    if not robots.allowed(probe):
        log("  day archives disallowed by robots.txt")
        return None

    start, end = window_bounds(since, until)
    done_days = store.archive_days(outlet_id, start, end)
    if done_days:
        log(f"  resuming: {len(done_days)} days already queued from an earlier run")

    # Links on today's homepage are menus, sidebars and current news. None of them
    # belong to a past day's archive, so ignore them everywhere.
    seen = set()
    if until < datetime.now(LAGOS).date() - timedelta(days=2):
        pacer.wait(home)
        page, _, _ = fetch(home, use_stealth=False)
        if page is not None:
            seen.update(page_article_links(page, home, outlet))
            seen.update(urljoin(home, a.attrib.get("href", "")).split("#")[0].split("?")[0]
                        for a in page.css("a[href]"))

    total_queued, empty_streak, fail_streak, warned_paging = 0, 0, 0, False
    day = since
    while day <= until:
        if day in done_days:
            day += timedelta(days=1)
            continue
        day_url = urljoin(home, f"{day:%Y/%m/%d}/")
        pacer.wait(day_url)
        page, _, err = fetch(day_url, use_stealth=False)
        if page is None:
            if err and "404" in err:
                empty_streak += 1
                log(f"  {day}: no archive page (404)")
                if empty_streak >= 7 and total_queued == 0:
                    log("  7 days in a row without an archive page: this site doesn't offer them")
                    return None
            else:
                fail_streak += 1
                log(f"  {day}: couldn't read archive ({err})")
                if fail_streak >= 5:
                    log("  archive pages are being blocked; stopping here (run again later to resume)")
                    return total_queued if total_queued else None
            day += timedelta(days=1)
            continue
        empty_streak = fail_streak = 0

        day_links = [u for u in page_article_links(page, day_url, outlet) if u not in seen]
        nxt, last_page, has_rel = pagination_info(page, day_url)
        pages_read, pages_used = 1, None

        def read(url):
            nonlocal fail_streak, warned_paging
            if not robots.allowed(url):
                if not warned_paging:
                    log("  note: robots.txt disallows archive page 2 onwards; using page 1 of each day only")
                    warned_paging = True
                return None
            pacer.wait(url)
            pg, _, _ = fetch(url, use_stealth=False)
            return pg

        if max_per_day and last_page > 1 and total_pages_known(page, day_url):
            # random pages, so the sample covers the whole day (page 1 = latest).
            # If the page count isn't visible, the branch below reads every page
            # instead, so the earliest articles of the day aren't left out.
            # Every page (including page 1) has the same chance of being used, so
            # every article of the day has the same chance of being sampled.
            per_page = max(len(day_links), 1)
            k = min(last_page, max(2, -(-int(max_per_day * 1.5) // per_page)))
            rng = random.Random(f"{outlet_id}-{day}")
            chosen = sorted(rng.sample(range(1, last_page + 1), k))
            if 1 not in chosen:
                day_links = []
            for n in chosen:
                if n == 1:
                    continue
                pg = read(f"{day_url}page/{n}/")
                if pg is None:
                    break
                pages_read += 1
                day_links += [u for u in page_article_links(pg, day_url, outlet) if u not in seen and u not in day_links]
            pages_used = len(chosen)
        else:
            n = 1
            while pages_read < MAX_PAGES_PER_DAY:
                if not nxt and (has_rel or n >= last_page):
                    break
                url = nxt or f"{day_url}page/{n + 1}/"
                pg = read(url)
                if pg is None:
                    break
                new = [u for u in page_article_links(pg, day_url, outlet) if u not in seen and u not in day_links]
                if not new:
                    break
                day_links += new
                pages_read += 1
                n += 1
                nxt, last_page_seen, has_rel = pagination_info(pg, day_url)
                last_page = max(last_page, last_page_seen)

        seen.update(day_links)
        hint = datetime.combine(day, datetime.min.time(), LAGOS).astimezone(UTC)
        cands = [{"url": u, "hint": hint, "via": "archive"} for u in day_links]
        rows = candidates_to_rows(cands, outlet, outlet_id, since, until, max_per_day, seed=f"{outlet_id}-{day}")
        store.enqueue(rows)
        total_queued += len(rows)
        if pages_used is not None:
            pages_note = f"{pages_used} of {last_page} pages, picked at random"
        else:
            pages_note = f"all {pages_read} pages" if pages_read > 1 else "1 page"
        log(f"  {day}: {len(day_links)} articles collected ({pages_note}), {len(rows)} queued")
        day += timedelta(days=1)
    return total_queued


# --------------------------------------------------------------------------- #
# Discovery: RSS (daily updates)
# --------------------------------------------------------------------------- #
ITEM = re.compile(r"<item\b[^>]*>(.*?)</item>", re.S | re.I)
LINK = re.compile(r"<link>\s*(?:<!\[CDATA\[)?\s*(.*?)\s*(?:\]\]>)?\s*</link>", re.S | re.I)
PUBDATE = re.compile(r"<pubDate>\s*(.*?)\s*</pubDate>", re.S | re.I)


def discover_rss(outlet, pacer):
    found = []
    for feed in outlet["feeds"]:
        pacer.wait(feed)
        data, err = fetch_bytes(feed)
        if not data:
            log(f"  couldn't read feed {feed}: {err}")
            continue
        for block in ITEM.findall(data.decode("utf-8", "ignore")):
            link = LINK.search(block)
            pub = PUBDATE.search(block)
            if link:
                found.append({"url": html.unescape(link.group(1)),
                              "hint": to_utc(pub.group(1)) if pub else None, "via": "rss"})
    return found


# --------------------------------------------------------------------------- #
# Extraction
# --------------------------------------------------------------------------- #
def first_attr(page, selector, attr="content"):
    nodes = page.css(selector)
    return clean(nodes[0].attrib.get(attr, "")) if nodes else ""


def all_attr(page, selector, attr="content"):
    return [clean(n.attrib.get(attr, "")) for n in page.css(selector) if clean(n.attrib.get(attr, ""))]


def first_text(page, selector):
    nodes = page.css(selector)
    return clean(nodes[0].get_all_text(separator=" ")) if nodes else ""


def jsonld_article(page):
    for script in page.css('script[type="application/ld+json"]'):
        try:
            data = json.loads(str(script.text or ""))
        except (ValueError, TypeError):
            continue
        stack = data if isinstance(data, list) else [data]
        while stack:
            obj = stack.pop(0)
            if not isinstance(obj, dict):
                continue
            types = obj.get("@type", [])
            types = types if isinstance(types, list) else [types]
            if any("Article" in str(t) for t in types):
                return obj
            if isinstance(obj.get("@graph"), list):
                stack.extend(obj["@graph"])
    return {}


def ld_author(ld):
    a = ld.get("author")
    people = a if isinstance(a, list) else [a] if a else []
    names = []
    for p in people:
        name = p.get("name") if isinstance(p, dict) else p
        if name and clean(name) not in names:
            names.append(clean(name))
    return ", ".join(names)


def ld_text(value):
    if isinstance(value, list):
        return ", ".join(clean(v if not isinstance(v, dict) else v.get("url") or v.get("name")) for v in value if v)
    if isinstance(value, dict):
        return clean(value.get("url") or value.get("name") or "")
    return clean(value)


def extract_tags(page, ld):
    tags = all_attr(page, 'meta[property="article:tag"]')
    kw = ld.get("keywords")
    if isinstance(kw, list):
        tags += [clean(k) for k in kw]
    elif isinstance(kw, str):
        tags += [clean(k) for k in kw.split(",")]
    for sel in ('meta[name="news_keywords"]', 'meta[name="keywords"]'):
        tags += [clean(k) for k in first_attr(page, sel).split(",")]
    out = []
    for t in tags:
        if t and len(t) <= 80 and t.lower() not in {x.lower() for x in out}:
            out.append(t)
    return out[:30]


def extract_body(page):
    fallback = ""
    for selector in BODY_SELECTORS:
        for container in page.css(selector):
            paras = []
            for p in container.css("p"):
                t = clean(p.get_all_text(separator=" "))
                if len(t) < 25 or JUNK_PARA.match(t) or t in paras:
                    continue
                paras.append(t)
            text = "\n\n".join(paras)
            if len(text) >= 300:
                return text
            if len(text) > len(fallback):
                fallback = text
    return fallback


def extract_article(page, url):
    ld = jsonld_article(page)
    meta = lambda sel: first_attr(page, sel, "content")

    author = ld_author(ld) or meta('meta[name="author"]')
    if not author:
        a = meta('meta[property="article:author"]')
        author = "" if a.startswith("http") else a

    body = extract_body(page)
    ld_body = clean(ld.get("articleBody"))
    if len(body) < 300 and len(ld_body) > len(body):
        body = ld_body

    return {
        "title": clean(ld.get("headline")) or meta('meta[property="og:title"]') or first_text(page, "h1"),
        "canonical_url": first_attr(page, 'link[rel="canonical"]', "href") or url,
        "published_raw": clean(ld.get("datePublished")) or meta('meta[property="article:published_time"]')
                         or first_attr(page, "time[datetime]", "datetime"),
        "modified_raw": clean(ld.get("dateModified")) or meta('meta[property="article:modified_time"]'),
        "author_raw": author,
        "section": ld_text(ld.get("articleSection")) or meta('meta[property="article:section"]'),
        "summary": meta('meta[property="og:description"]') or meta('meta[name="description"]'),
        "image_url": ld_text(ld.get("image")) or meta('meta[property="og:image"]'),
        "tags": extract_tags(page, ld),
        "body_text": body,
    }


# Rough language check, enough to filter non-English articles out of English models.
EN_WORDS = set("the and of to in is that for on was with as by at from it be are has have said this".split())
PCM_WORDS = set("dey wey wetin una sabi pikin abeg dis dat wahala oya sef abi naim comot oyibo kpatakpata".split())
HA_WORDS = set("da na ta ya ba shi wanda kuma amma cikin zuwa sun yana tana daga wannan wajen domin saboda haka".split())


def detect_language(text):
    words = re.findall(r"[a-zà-ɏ']+", text.lower())[:500]
    if len(words) < 20:
        return "unknown"
    n = len(words)
    en = sum(w in EN_WORDS for w in words) / n
    pcm = sum(w in PCM_WORDS for w in words) / n
    ha = sum(w in HA_WORDS for w in words) / n
    if ha > 0.08 and ha > en:
        return "ha"
    if pcm >= 0.03:
        return "pcm"
    if en >= 0.08:
        return "en"
    return "unknown"


# --------------------------------------------------------------------------- #
# Commands
# --------------------------------------------------------------------------- #
def chosen_outlets(arg):
    keys = [k.strip().lower() for k in arg.split(",") if k.strip()]
    bad = [k for k in keys if k not in OUTLETS]
    if bad:
        sys.exit(f"Unknown outlet(s): {', '.join(bad)}. Choose from: {', '.join(OUTLETS)}")
    return keys


def candidates_to_rows(cands, outlet, outlet_id, since=None, until=None, max_per_day=None, seed=42):
    rows, seen = [], set()
    for c in cands:
        url = c["url"].split("#")[0]
        host = urlparse(url).netloc.lower()
        if url in seen or not host.endswith(outlet["domain"]) or NON_ARTICLE.search(urlparse(url).path):
            continue
        seen.add(url)
        rows.append({
            "url": url, "outlet_id": outlet_id, "discovered_via": c["via"],
            "published_hint": iso(c["hint"]),
            "window_start": since.isoformat() if since else None,
            "window_end": until.isoformat() if until else None,
            "_day": c["hint"].astimezone(LAGOS).date() if c["hint"] else None,
        })
    if max_per_day:
        by_day = defaultdict(list)
        for r in rows:
            by_day[r["_day"]].append(r)
        sampled = []
        for day, group in by_day.items():
            if day is None or len(group) <= max_per_day:
                sampled += group
                continue
            # one seed per outlet and day: re-running gives the same sample, and a
            # change to one day's article list never reshuffles the other days
            group = sorted(group, key=lambda r: r["url"])
            sampled += random.Random(f"{seed}-{outlet_id}-{day}").sample(group, max_per_day)
        rows = sampled
    for r in rows:
        r.pop("_day", None)
    return rows


def cmd_discover(args):
    store = open_store()
    ids = store.outlet_ids()
    today = datetime.now(LAGOS).date()
    if args.last_days:
        # the last N complete days in Lagos time (today is still in progress, so a
        # per-day sample of it would be unfair to articles published later today)
        since, until = today - timedelta(days=args.last_days), today - timedelta(days=1)
    elif args.since:
        since = date.fromisoformat(args.since)
        until = date.fromisoformat(args.until) if args.until else today
    else:
        sys.exit("discover needs --since YYYY-MM-DD or --last-days N")
    if until < since:
        sys.exit("--until is before --since")
    robots = Robots()
    pacer = Pacer(args.delay, robots)
    totals = {}

    methods = ["api", "sitemap", "archive"] if args.method == "auto" else [args.method]
    for key in chosen_outlets(args.outlets):
        outlet = OUTLETS[key]
        delay = pacer.delay_for(outlet["home"])
        log(f"\n== {outlet['name']}: articles from {since} to {until} (≥{delay:.0f}s between requests) ==")
        queued, used = 0, None
        for method in methods:
            if method == "archive":
                n = discover_archives(outlet, ids[key], since, until, robots, pacer, store, args.max_per_day)
                if n is not None:
                    queued, used = n, "day archives"
                    break
                continue
            if method == "api":
                cands = discover_wp_api(outlet, since, until, robots, pacer)
            else:
                cands = discover_sitemaps(outlet, since, until, robots, pacer, args.lastmod_grace_days)
                if not cands:
                    log("  sitemaps unavailable or empty")
            if cands:
                rows = candidates_to_rows(cands, outlet, ids[key], since, until, args.max_per_day)
                store.enqueue(rows)
                queued, used = len(rows), {"api": "WordPress API", "sitemap": "sitemaps"}[method]
                break
        totals[outlet["name"]] = (queued, delay)
        sampled = f" (sampled to at most {args.max_per_day}/day)" if args.max_per_day else ""
        if used:
            log(f"  queued {queued} article URLs via {used}{sampled}")
        else:
            log(f"  NO ARTICLES FOUND for {outlet['name']}: every discovery method failed (see messages above)")

    log("\nDiscovery finished. Queued per outlet (already-queued URLs are skipped automatically):")
    slowest = 0
    for name, (n, delay) in totals.items():
        hours = n * (delay * 1.15 + 1.5) / 3600
        slowest = max(slowest, hours)
        log(f"  {name:<22} {n:>7} URLs   ~{delay:.0f}s between requests   ~{hours:.1f} h to crawl")
    log(f"Outlets are crawled in parallel, so the whole crawl takes roughly {slowest:.1f} hours.")
    log("Next: python ng_news_pipeline.py crawl")


def crawl(store, keys, args):
    ids = store.outlet_ids()
    robots = Robots()
    pacer = Pacer(args.delay, robots)
    use_stealth = not args.no_stealth
    queues = {k: deque() for k in keys}
    exhausted = set()
    done = Counter()
    processed = 0
    started = time.monotonic()
    since = None
    if getattr(args, "last_days", 0):
        first_day = datetime.now(LAGOS).date() - timedelta(days=args.last_days)
        since = datetime.combine(first_day, datetime.min.time(), LAGOS).astimezone(UTC)
        log(f"Only crawling articles published since {first_day} (--last-days {args.last_days}).")

    def refill(k):
        if not queues[k] and k not in exhausted:
            rows = store.pending(ids[k], args.batch, since)
            queues[k].extend(rows)
            if not rows:
                exhausted.add(k)

    def process(k, item):
        outlet = OUTLETS[k]
        url = item["url"]
        if not robots.allowed(url):
            store.mark(url, "skipped_robots")
            return "skipped_robots"
        pacer.wait(url)
        page, method, err = fetch(url, use_stealth=use_stealth)
        if page is None:
            attempts = (item.get("attempts") or 0) + 1
            store.mark(url, "failed" if attempts >= args.max_attempts else "pending", err, attempts)
            log(f"  [{outlet['name']}] fetch failed ({attempts}/{args.max_attempts}): {url}  {err}")
            return "failed" if attempts >= args.max_attempts else "retry"

        art = extract_article(page, url)
        published = to_utc(art["published_raw"])
        hint = to_utc(item.get("published_hint"))
        if published and item.get("window_start") and item.get("window_end"):
            start, end = window_bounds(date.fromisoformat(item["window_start"]),
                                       date.fromisoformat(item["window_end"]))
            if not (start <= published < end):
                store.mark(url, "out_of_range")
                return "out_of_range"
        if not published and item.get("discovered_via") == "archive":
            # archive pages also link to menus, "about us" etc.; real articles carry a date
            store.mark(url, "not_article", "no publish date on page")
            return "not_article"
        published = published or hint

        text = art["body_text"]
        words = len(text.split())
        row = {
            "outlet_id": ids[k],
            "url": url,
            "canonical_url": art["canonical_url"],
            "title": art["title"] or None,
            "summary": art["summary"] or None,
            "body_text": text or None,
            "author_raw": art["author_raw"] or None,
            "published_at": iso(published),
            "published_raw": art["published_raw"] or None,
            "modified_at": iso(to_utc(art["modified_raw"])),
            "section": art["section"] or None,
            "tags": art["tags"] or None,
            "image_url": art["image_url"] or None,
            "word_count": words,
            "language": detect_language(text),
            "content_hash": hashlib.sha256(text.encode()).hexdigest() if text else None,
            "discovery_source": item.get("discovered_via"),
            "fetched_with": method,
            "http_status": getattr(page, "status", None),
            "extraction_ok": words >= MIN_OK_WORDS,
            "last_checked_at": datetime.now(UTC).isoformat(),
        }
        store.save_article(row)
        store.mark(url, "done")
        flag = "" if row["extraction_ok"] else "  (short/empty body: check)"
        log(f"  [{outlet['name']}] {words:>5} words  {(art['title'] or url)[:70]}{flag}")
        return "done"

    try:
        while True:
            for k in keys:
                refill(k)
            active = [k for k in keys if queues[k]]
            if not active:
                break
            # whichever outlet is allowed to make its next request soonest
            k = min(active, key=lambda x: pacer.ready_at(OUTLETS[x]["home"]))
            item = queues[k].popleft()
            try:
                result = process(k, item)
            except Exception as e:  # one bad page must not stop a multi-day crawl
                attempts = (item.get("attempts") or 0) + 1
                status = "failed" if attempts >= args.max_attempts else "pending"
                try:
                    store.mark(item["url"], status, f"{e.__class__.__name__}: {str(e)[:300]}", attempts)
                except Exception:
                    pass
                log(f"  [{OUTLETS[k]['name']}] error on {item['url']}: {e.__class__.__name__}: {e}")
                result = "error"
            done[(k, result)] += 1
            processed += 1
            if args.max_articles and done_count(done) >= args.max_articles:
                log(f"\nReached --max-articles {args.max_articles}.")
                break
            if args.max_minutes and time.monotonic() - started >= args.max_minutes * 60:
                log(f"\nReached --max-minutes {args.max_minutes}; the rest stays queued for next time.")
                break
            if processed % 100 == 0:
                rate = processed / max(time.monotonic() - started, 1) * 3600
                log(f"  ... {processed} processed this run (~{rate:.0f}/hour)")
    except KeyboardInterrupt:
        log("\nStopped. Progress is saved; run the same command to continue.")

    log("\nThis run:")
    for k in keys:
        n_done, n_fail = done[(k, "done")], done[(k, "failed")] + done[(k, "error")]
        n_skip = done[(k, "out_of_range")] + done[(k, "skipped_robots")] + done[(k, "not_article")]
        log(f"  {OUTLETS[k]['name']:<22} saved {n_done:>6}   failed {n_fail:>4}   skipped {n_skip:>4}")


def done_count(counter):
    return sum(v for (k, r), v in counter.items() if r == "done")


def cmd_crawl(args):
    crawl(open_store(), chosen_outlets(args.outlets), args)


def cmd_update(args):
    store = open_store()
    ids = store.outlet_ids()
    keys = chosen_outlets(args.outlets)
    robots = Robots()
    pacer = Pacer(args.delay, robots)
    for k in keys:
        cands = discover_rss(OUTLETS[k], pacer)
        rows = candidates_to_rows(cands, OUTLETS[k], ids[k])
        store.enqueue(rows)
        log(f"{OUTLETS[k]['name']}: {len(rows)} items in feed (new ones queued)")
    crawl(store, keys, args)


def cmd_status(args):
    store = open_store()
    log("Crawl queue:")
    log(f"  {'outlet':<22} {'status':<15} {'urls':>8}  {'earliest':<10}  latest")
    for r in store.view("crawl_progress"):
        log(f"  {r['outlet']:<22} {r['status']:<15} {r['urls']:>8}  {str(r['earliest'] or ''):<10}  {r['latest'] or ''}")
    log("\nArticles stored:")
    log(f"  {'outlet':<22} {'articles':>8}  {'earliest':<10}  {'latest':<10}  {'avg words':>9}  needs review")
    for r in store.view("corpus_summary"):
        log(f"  {r['outlet']:<22} {r['articles']:>8}  {str(r['earliest'] or ''):<10}  {str(r['latest'] or ''):<10}"
            f"  {str(r['avg_words'] or ''):>9}  {r['needs_review'] or 0}")


def main():
    ap = argparse.ArgumentParser(description="Nigerian news corpus pipeline (archives -> Supabase).")
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("--outlets", default=",".join(OUTLETS), help=f"comma-separated: {', '.join(OUTLETS)}")
        p.add_argument("--delay", type=float, default=2.0,
                       help="minimum seconds between requests to one site (robots.txt Crawl-delay wins if longer)")

    def crawl_opts(p):
        p.add_argument("--max-articles", type=int, default=0, help="stop after saving this many (0 = no limit)")
        p.add_argument("--max-minutes", type=float, default=0, help="stop after this many minutes (0 = no limit)")
        p.add_argument("--last-days", type=int, default=0,
                       help="only crawl articles published in the last N days (0 = everything queued)")
        p.add_argument("--batch", type=int, default=200, help="queue rows loaded per outlet at a time")
        p.add_argument("--max-attempts", type=int, default=3, help="give up on a URL after this many failures")
        p.add_argument("--no-stealth", action="store_true", help="never fall back to the browser fetcher")

    p = sub.add_parser("discover", help="queue article URLs for a date range")
    common(p)
    p.add_argument("--since", help="first day, YYYY-MM-DD")
    p.add_argument("--until", help="last day, YYYY-MM-DD (default: today)")
    p.add_argument("--last-days", type=int, default=0,
                   help="instead of --since/--until: the last N complete days (yesterday and before)")
    p.add_argument("--max-per-day", type=int, default=0,
                   help="randomly sample at most N articles per outlet per day (0 = keep all)")
    p.add_argument("--lastmod-grace-days", type=int, default=7,
                   help="sitemap entries without a URL date are kept if last modified up to N days after --until")
    p.add_argument("--method", choices=["auto", "api", "sitemap", "archive"], default="auto",
                   help="how to find articles (auto = WordPress API, then sitemaps, then day archives)")
    p.set_defaults(func=cmd_discover)

    p = sub.add_parser("crawl", help="fetch queued articles into Supabase")
    common(p)
    crawl_opts(p)
    p.set_defaults(func=cmd_crawl)

    p = sub.add_parser("update", help="queue the latest RSS items and crawl them (run daily)")
    common(p)
    crawl_opts(p)
    p.set_defaults(func=cmd_update)

    p = sub.add_parser("status", help="show progress")
    p.set_defaults(func=cmd_status)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
