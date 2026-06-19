"""
IH Solutions — Competitor Pricing Scraper (v2)

Tiered extraction strategy, most reliable first:

  1. JSON-LD        <script type="application/ld+json"> — schema.org
                    Product / Offer / Menu / MenuItem objects.
  2. Embedded JSON  __NEXT_DATA__, window.__PRELOADED_STATE__, etc.
                    Recursively walks the blob for {name, price} pairs.
  3. Microdata      itemprop="name" / itemprop="price" attributes.
  4. Card-based DOM Finds each price leaf, climbs to the smallest
                    ancestor that contains exactly ONE price group,
                    then takes the name from a heading / link /
                    title-classed element inside that "card".
                    (Replaces the old innermost-element heuristic,
                    which produced "£6.50" / "Price per unit" rows.)

Other fixes vs v1:
  - "Was £X" / strikethrough prices ignored; current price preferred.
  - "per kg" / "/kg" prices routed to price_per_kg, not food_item.
  - Size (300g, 175ml, x2...) pulled out of the name when present.
  - Rows whose name is just a price / boilerplate are dropped.
  - PDF text fallback now runs per page (v1 skipped it for all
    pages once any earlier page produced table rows).
  - Selenium fallback also triggers when a page has plenty of text
    but zero extractable items (e.g. skeleton screens with copy).
"""

import csv
import io
import json
import re
import time
from datetime import date
from pathlib import Path

import requests
import pdfplumber
from bs4 import BeautifulSoup, Tag

try:
    import pytesseract
    from PIL import Image, ImageOps
    from pytesseract import Output
    OCR_AVAILABLE = True
except ImportError:
    OCR_AVAILABLE = False

try:
    from selenium import webdriver
    from selenium.webdriver.chrome.service import Service
    from selenium.webdriver.common.by import By
    from selenium.webdriver.support.ui import WebDriverWait
    from selenium.webdriver.support import expected_conditions as EC
    from webdriver_manager.chrome import ChromeDriverManager
    SELENIUM_AVAILABLE = True
except ImportError:
    SELENIUM_AVAILABLE = False

import os
import uuid
import pandas as pd
from dotenv import load_dotenv
from sqlalchemy import create_engine

load_dotenv()
DB_URL = os.getenv("SUPABASE_DB_URL")

# Map each distinct location string your scraper emits to its postcode area letters
POSTCODE_AREAS = {
    "Manchester": "M",
    "Leeds":      "LS",
    "Bristol":    "BS",
    # ...one entry per distinct location value in your data
}

# =============================================================================
# CONFIG
# =============================================================================

INPUT_CSV  = "venues.csv"
OUTPUT_DIR = Path("output")
TODAY      = date.today().isoformat()

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "en-GB,en;q=0.9",
}

PRICE_RE      = re.compile(r"£\s?(\d+(?:\.\d{1,2})?)")
# Bare menu prices ("PORNSTAR MARTINI 11.45") — strict d.dd, must NOT be
# an ABV ("4.6%") or a calorie figure ("464Kcal")
BARE_PRICE_RE = re.compile(r"\b(\d{1,3}\.\d{2})\b(?!\s*%|\s*[Kk]cal)")
KCAL_RE       = re.compile(r"\d+\s*[Kk]cal")
# Integer-priced block menus (Electric Shuffle style): price alone on a
# line ("9", "7 / 12"), or trailing/leading a text line.
INT_PRICE_LINE_RE  = re.compile(r"^\s*(\d{1,2})(?:\s*/\s*(\d{1,2}))?\s*$")
TRAILING_INT_RE    = re.compile(r"(?<=[a-zA-Z)\u00e9])\s+(\d{1,2})\s*$")
LEADING_INT_RE     = re.compile(r"^\s*(\d{1,2})\s+(?=[A-Z\u00c0-\u00dc])")
DIET_TAG_RE        = re.compile(
    r"(?:\s+(?:V|Ve|Ve\*|VG|NGC|GF|DF|N|H))+\s*$")
SERVE_SIZE_RE = re.compile(
    r"\b(glass|pint|half pint|bottle|can|\d+\s?(?:ml|cl|l))\b", re.IGNORECASE)
PER_KG_RE     = re.compile(r"£\s?\d+(?:\.\d{1,2})?\s*(?:/|per\s*)kg", re.IGNORECASE)
SIZE_RE       = re.compile(
    r"\b(\d+(?:\.\d+)?\s?(?:g|kg|ml|cl|l|litre|oz)|x\s?\d+|\d+\s?(?:pack|pieces|pcs))\b",
    re.IGNORECASE,
)
WAS_PRICE_RE  = re.compile(r"\bwas\s*£\s?\d+(?:\.\d{1,2})?", re.IGNORECASE)

JS_DETECTION_THRESHOLD = 500
MIN_NAME_LEN           = 3
MAX_NAME_LEN           = 120   # longer = description blob, not a product name

BOILERPLATE = {
    "price per unit", "was", "now", "from", "save", "offer",
    "any 2 for", "any 3 for", "any 4 for", "add", "add to cart",
    "add to basket", "view", "view product", "shop now", "buy now",
    "per kg", "each", "typical price", "item price", "unit price",
    "more details", "quick view", "out of stock", "new", "online only",
    "portion size", "main meals", "menu", "filter", "sort by", "results",
}

# Elements inside a card that are likely to hold the product name,
# in priority order.
NAME_SELECTORS = [
    "h1", "h2", "h3", "h4", "h5", "h6",
    '[itemprop="name"]',
    '[class*="title" i]',
    '[class*="name" i]',
    '[data-testid*="name" i]',
    '[data-testid*="title" i]',
    "a",
    "strong", "b",
]

OUTPUT_COLUMNS = [
    "venue_name", "brand", "location", "postcode_area", "food_item", "price",
    "price_per_kg", "size", "is_drink", "type", "drink_item",
    "source_type", "source_url", "ingestion_date", "note",
]


# =============================================================================
# HELPERS
# =============================================================================

def is_pdf(url: str) -> bool:
    return url.lower().split("?")[0].endswith(".pdf")


def normalise_price(raw) -> str:
    """'£ 6.5', 6.5, '6.50' -> '£6.50'. Returns '' if unparseable/zero."""
    if raw is None:
        return ""
    s = str(raw).strip().replace("£", "").replace(",", "").strip()
    try:
        value = float(s)
    except ValueError:
        m = PRICE_RE.search(str(raw))
        if not m:
            return ""
        value = float(m.group(1))
    if value <= 0:
        return ""
    return f"£{value:.2f}"


def clean_name(name: str) -> str:
    """Strip prices, promo phrases and trailing prepositions from a name."""
    if not name:
        return ""
    name = PRICE_RE.sub("", name)
    name = WAS_PRICE_RE.sub("", name)
    name = re.sub(r"\s+", " ", name).strip(" -–|:,.\n\t")
    name = re.sub(r"\s+(for|at|from|was|now|only|just)\s*$", "", name,
                  flags=re.IGNORECASE).strip()
    # dangling multibuy fragments: "Kids' Meals (5 for", "Pies (2 for )"
    name = re.sub(r"\(\s*\d*\s*(?:for)?\s*\)?\s*$", "", name).strip(" -–|:,.")
    # dietary tags: "Buffalo V NGC" -> "Buffalo"
    name = DIET_TAG_RE.sub("", name).strip(" -–|:,.")
    return name


KEYLIKE_RE = re.compile(
    r"^[\w.-]+:[\w.-]+$"            # namespaced keys: brxsaas:offerPrices
    r"|^[a-z]+(?:[A-Z][a-zA-Z0-9]*)+$"  # camelCase identifiers
    r"|^[a-z0-9_.-]+$"                # snake/kebab keys with no spaces
)


def valid_name(name: str) -> bool:
    if not name:
        return False
    n = name.strip()
    if not (MIN_NAME_LEN <= len(n) <= MAX_NAME_LEN):
        return False
    if n.lower() in BOILERPLATE:
        return False
    if PRICE_RE.fullmatch(n) or re.fullmatch(r"[\d\s.£%]+", n):
        return False
    if not re.search(r"[A-Za-z]", n):
        return False
    # Machine identifiers (JSON keys, analytics fields), not product names.
    # Real product names contain a space or are capitalised words.
    if " " not in n and KEYLIKE_RE.match(n):
        return False
    if n.lower().startswith(("skip to", "go to", "back to", "sign in", "log in")):
        return False
    return True


def extract_size(name: str) -> tuple[str, str]:
    """Pull a pack/weight size out of a name. Returns (clean_name, size)."""
    m = SIZE_RE.search(name)
    if not m:
        return name, ""
    size = m.group(1).strip()
    cleaned = clean_name(name.replace(m.group(0), " "))
    # Don't strip the size if doing so destroys the name
    if valid_name(cleaned):
        return cleaned, size
    return name, size


# ── drink classification ─────────────────────────────────────────────
# Order matters: mocktail (non-alcoholic markers) must be checked before
# beer/wine so "Madri 0%" or "Virgin Mojito" don't classify as alcoholic.

MOCKTAIL_KW = [
    "mocktail", "virgin ", "non-alcoholic", "non alcoholic", "alcohol-free",
    "alcohol free", "0%", "0.0%", "nosecco", "nojito", "lyre's", "lyres",
    "everleaf", "seedlip", "crossip", "celibate",
]
# ABV of 0.5% or below counts as alcohol-free (UK convention)
LOW_ABV_RE = re.compile(r"\b0(?:\.[0-5])?\s*%")
BEER_KW = [
    "beer", "lager", "ipa", " ale", "pale ale", "stout", "pilsner", "cider",
    "beavertown", "birra", "red stripe", "pacifico", "daura", "shandy",
    "madri", "peroni", "corona", "moretti", "guinness", "carling", "foster",
    "heineken", "stella", "san miguel", "camden", "brewdog", "amstel",
    "estrella", "asahi", "kopparberg", "rekorderlig", "budweiser", "becks",
    "pint of", "half pint",
]
WINE_KW = [
    "wine", "merlot", "sauvignon", "pinot", "chardonnay", "rioja", "malbec",
    "shiraz", "zinfandel", "prosecco", "champagne", "rosé", "rose wine",
    "cabernet", "grigio", "blanc", "tempranillo", "verdejo", "picpoul",
    "albarino", "chenin", "riesling", "viognier", "cava", "sherry", "port ",
]
COCKTAIL_KW = [
    "cocktail", "mojito", "margarita", "martini", "negroni", "spritz",
    "colada", "daiquiri", "cosmopolitan", "old fashioned", "bellini",
    "bramble", "paloma", "mai tai", "long island", "sour", "punch",
    "sangria", "pimm", "g&t", "gin & tonic", "gin and tonic", "spiked",
    "vodka", "rum ", "tequila", "whisky", "whiskey", "bourbon", "brandy",
    "liqueur", "aperol", "campari", "baileys", "jagermeister", "disaronno",
    "limoncello", "hooch", "wkd", "smirnoff ice", "baby guinness",
    "sambuca", "sourz", "jager bomb", "shot", "tequila rose", "spritz",
]
SOFT_KW = [
    "soft drink", "coca-cola", "coca cola", "coke", "pepsi", "lemonade",
    "fanta", "sprite", "7up", "tango", "irn-bru", "irn bru", "juice",
    "smoothie", "milkshake", "shake", "squash", "cordial", "j2o",
    "appletiser", "red bull", "monster energy", "still water",
    "sparkling water", "mineral water", "tonic water", "ginger beer",
    "ginger ale", "iced tea", "tea", "coffee", "latte", "cappuccino",
    "espresso", "americano", "mocha", "flat white", "hot chocolate",
    "babyccino", "fruit shoot", "capri sun", "robinsons", "slush",
    "j20", "j2o", "float", "frobscottle", "oasis", "ribena", "vimto",
]
# unmistakable food words — veto drink classification from the NAME
# (handles "Rum & Raisin Ice Cream", "Beer-Battered Fish", "Coffee Cake",
# "Champagne Sorbet", "Whisky Sauce Steak"...)
FOOD_VETO_KW = [
    "ice cream", "cake", "sorbet", "cheesecake", "brownie", "pudding",
    "tart", "pie", "trifle", "battered", "glazed", "sauce", "gravy",
    "marinated", "infused", "cured", "braised", "burger", "pizza",
    "pasta", "risotto", "steak", "chicken", "beef", "pork", "lamb",
    "fish", "prawn", "salad", "soup", "sandwich", "wrap", "roll",
    "fries", "chips", "dessert", "mousse", "profiterole", "panna cotta",
    "tiramisu", "gateau", "fondant", "crumble", "waffle", "pancake",
    "jus", "butter", "stew", "casserole", "curry",
]

# generic drink words that flag is_drink even if type stays uncertain
GENERIC_DRINK_KW = [
    "drink", "beverage", "bottle of", "can of", "glass of", "jug of",
    "draught", "bottle", "on tap",
    "pitcher", "carafe", "175ml", "250ml", "330ml", "440ml", "500ml",
    "70cl", "75cl", "125ml",
]

DRINK_SIZE_RE = re.compile(
    r"\b(\d+(?:\.\d+)?\s?(?:ml|cl|l|ltr|litre|oz)|"
    r"(?:half\s+)?pint|bottle|can|jug|pitcher|carafe|"
    r"small|medium|large)\b",
    re.IGNORECASE,
)


def _contains(text: str, keywords: list) -> bool:
    return any(kw in text for kw in keywords)


def _classify_text(text: str) -> str:
    """Keyword cascade on one piece of text. Mocktail first so '0%' /
    'virgin' overrides alcoholic matches in the same string."""
    if _contains(text, MOCKTAIL_KW):
        return "mocktail"
    if _contains(text, COCKTAIL_KW):
        return "cocktails"
    if _contains(text, BEER_KW):
        return "beer"
    if _contains(text, WINE_KW):
        return "wine"
    if _contains(text, SOFT_KW):
        return "softdrinks"
    return ""


def classify_drink(name: str, description: str = "") -> tuple[str, str]:
    """Return (is_drink, drink_type). The NAME outranks the description:
    'Aperol Spritz' is a cocktail even though its description mentions
    prosecco. Description is only consulted when the name is inconclusive.
    Exception: a non-alcoholic marker anywhere ('0%', 'alcohol free')
    forces mocktail."""
    name_l = f" {name} ".lower()
    desc_l = f" {description} ".lower()

    # 0.x% ABV anywhere = alcohol-free serve of an alcoholic drink
    if LOW_ABV_RE.search(name_l) or LOW_ABV_RE.search(desc_l):
        return "yes", "mocktail"

    # 0. unmistakable food word in the name vetoes name-based alcohol
    #    matches ("Rum & Raisin Ice Cream", "Beer-Battered Fish") —
    #    unless the name ALSO has an explicit drink-format word
    #    ("Bacon Roll & Hot Drink" keeps its drink flag via step 2)
    food_veto = _contains(name_l, FOOD_VETO_KW)

    # 1. the NAME identifies the drink
    if not food_veto and _contains(name_l, MOCKTAIL_KW):
        return "yes", "mocktail"
    drink_type = "" if food_veto else _classify_text(name_l)
    if drink_type:
        # non-alcoholic marker in the description overrides to mocktail
        if _contains(desc_l, MOCKTAIL_KW):
            return "yes", "mocktail"
        return "yes", drink_type

    # 2. the name carries a generic drink signal ("glass of", "drink",
    #    "175ml"...) — it IS a drink; use the description to type it
    if _contains(name_l, GENERIC_DRINK_KW):
        if _contains(desc_l, MOCKTAIL_KW):
            return "yes", "mocktail"
        return "yes", _classify_text(desc_l)

    # 3. strong drink signal in the DESCRIPTION (bottle/can/ml sizes) —
    #    e.g. an unbranded name like "House Red" with "Merlot 175ml".
    #    Vetoed for clear food names ("Steak" + "served with 25ml jus").
    if not food_veto and _contains(desc_l, GENERIC_DRINK_KW):
        if _contains(desc_l, MOCKTAIL_KW):
            return "yes", "mocktail"
        return "yes", _classify_text(desc_l)

    return "no", ""


def extract_drink_size(name: str, description: str = "") -> str:
    for source in (name, description):
        m = DRINK_SIZE_RE.search(source or "")
        if m:
            return m.group(0).strip()
    return ""


def build_drink_item(name: str, description: str, size: str) -> str:
    parts = [f"name: {name}"]
    if description:
        parts.append(f"description: {description}")
    if size:
        parts.append(f"size: {size}")
    return "; ".join(parts)


def build_row(venue_name, location, url, food_item, price, source_type,
              size="", price_per_kg="") -> dict:
    return {
        "venue_name": venue_name, "brand": "", "location": location,
        "food_item": food_item.strip(), "price": price,
        "price_per_kg": price_per_kg, "size": size,
        "is_drink": "no", "type": "", "drink_item": "",
        "source_type": source_type, "source_url": url,
        "ingestion_date": TODAY, "note": "",
    }


class RowCollector:
    """Deduplicates and validates rows as they're added."""

    def __init__(self, venue_name, location, url, source_type):
        self.venue_name, self.location = venue_name, location
        self.url, self.source_type = url, source_type
        self.rows, self._seen = [], set()

    def add(self, name, price, size="", price_per_kg="", description="",
            force_food=False):
        name = clean_name(name)
        price = normalise_price(price)
        if not price or not valid_name(name):
            return False
        if not size:
            name, size = extract_size(name)
        key = (name.lower(), price)
        if key in self._seen:
            return False
        self._seen.add(key)

        description = re.sub(r"\s+", " ", (description or "")).strip()[:300]

        row = build_row(
            self.venue_name, self.location, self.url,
            name, price, self.source_type, size=size,
            price_per_kg=normalise_price(price_per_kg),
        )

        is_drink, drink_type = ("no", "") if force_food else \
            classify_drink(name, description)
        if is_drink == "yes":
            row["is_drink"] = "yes"
            row["type"] = drink_type
            drink_size = size or extract_drink_size(name, description)
            row["drink_item"] = build_drink_item(name, description, drink_size)
            if drink_size and not row["size"]:
                row["size"] = drink_size

        self.rows.append(row)
        return True


# =============================================================================
# FETCHERS
# =============================================================================

def fetch_html(url: str) -> tuple[BeautifulSoup, str]:
    """Returns (soup, raw_html). Falls back to Selenium for thin pages."""
    response = requests.get(url, headers=HEADERS, timeout=15)
    response.raise_for_status()
    html = response.text
    soup = make_soup(html)

    page_text = soup.get_text(separator=" ", strip=True)
    if len(page_text) >= JS_DETECTION_THRESHOLD:
        return soup, html

    print("(JS detected — retrying with Selenium...)", end=" ", flush=True)
    return fetch_html_selenium(url)


def make_soup(html: str) -> BeautifulSoup:
    soup = BeautifulSoup(html, "html.parser")
    for tag in soup(["style", "noscript", "svg", "iframe"]):
        tag.decompose()
    # NOTE: <script> tags are kept — JSON-LD and __NEXT_DATA__ live there.
    return soup


def fetch_html_selenium(url: str) -> tuple[BeautifulSoup, str]:
    if not SELENIUM_AVAILABLE:
        raise ImportError(
            "Page appears JavaScript-rendered but Selenium is not installed.\n"
            "Run: pip install selenium webdriver-manager"
        )

    options = webdriver.ChromeOptions()
    for arg in ("--headless=new", "--no-sandbox", "--disable-dev-shm-usage",
                "--disable-blink-features=AutomationControlled"):
        options.add_argument(arg)
    options.add_argument(f"user-agent={HEADERS['User-Agent']}")

    driver = webdriver.Chrome(
        service=Service(ChromeDriverManager().install()), options=options,
    )
    try:
        driver.get(url)
        WebDriverWait(driver, 15).until(
            EC.presence_of_element_located((By.TAG_NAME, "p"))
        )
        time.sleep(3)  # lazy-loaded prices
        html = driver.page_source
    finally:
        driver.quit()

    return make_soup(html), html


def fetch_pdf_bytes(url: str) -> bytes:
    response = requests.get(url, headers=HEADERS, timeout=20)
    response.raise_for_status()
    return response.content


# =============================================================================
# TIER 1 — JSON-LD (schema.org)
# =============================================================================

def extract_jsonld(soup: BeautifulSoup, collector: RowCollector) -> int:
    count = 0
    for script in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(script.string or "")
        except (json.JSONDecodeError, TypeError):
            continue
        count += _walk_jsonld(data, collector)
    return count


def _walk_jsonld(node, collector: RowCollector) -> int:
    count = 0
    if isinstance(node, list):
        for item in node:
            count += _walk_jsonld(item, collector)
        return count
    if not isinstance(node, dict):
        return 0

    node_type = node.get("@type", "")
    types = node_type if isinstance(node_type, list) else [node_type]
    types = [t.lower() for t in types if isinstance(t, str)]

    if any(t in ("product", "menuitem", "menusection_item") for t in types):
        name = node.get("name", "")
        desc = node.get("description", "")
        price = _price_from_offers(node.get("offers"))
        if price is None:
            price = node.get("price")
        if collector.add(str(name), price, description=str(desc or "")):
            count += 1

    # Recurse into every container key (itemListElement, hasMenuItem,
    # hasMenuSection, @graph, offers, mainEntity, ...)
    for value in node.values():
        if isinstance(value, (dict, list)):
            count += _walk_jsonld(value, collector)
    return count


def _price_from_offers(offers):
    if offers is None:
        return None
    if isinstance(offers, list):
        for o in offers:
            p = _price_from_offers(o)
            if p is not None:
                return p
        return None
    if isinstance(offers, dict):
        return offers.get("price") or offers.get("lowPrice")
    return None


# =============================================================================
# TIER 2 — embedded framework JSON (__NEXT_DATA__ etc.)
# =============================================================================

NAME_KEYS  = {"name", "title", "productname", "displayname", "itemname", "label"}
PRICE_KEYS = {"price", "currentprice", "sellprice", "nowprice", "amount",
              "priceamount", "value", "current"}

EMBEDDED_JSON_RE = re.compile(
    r"(?:__NEXT_DATA__|__PRELOADED_STATE__|__INITIAL_STATE__|__APOLLO_STATE__)"
    r"[^=]*=\s*({.+?})\s*(?:;|</script>)",
    re.DOTALL,
)


def extract_embedded_json(soup: BeautifulSoup, collector: RowCollector) -> int:
    count = 0
    for script in soup.find_all("script"):
        text = script.string or ""
        if not text:
            continue
        candidates = []
        if script.get("id") == "__NEXT_DATA__":
            candidates.append(text)
        else:
            candidates += [m.group(1) for m in EMBEDDED_JSON_RE.finditer(text)]
        for blob in candidates:
            try:
                data = json.loads(blob)
            except json.JSONDecodeError:
                continue
            count += _walk_state(data, collector, depth=0)
    return count


def _walk_state(node, collector: RowCollector, depth: int) -> int:
    if depth > 25:
        return 0
    count = 0
    if isinstance(node, list):
        for item in node:
            count += _walk_state(item, collector, depth + 1)
        return count
    if not isinstance(node, dict):
        return 0

    lower = {k.lower(): v for k, v in node.items()}
    name = next((lower[k] for k in NAME_KEYS if isinstance(lower.get(k), str)), None)
    # {"name": "brxsaas:offerPrices", "values": [...]} is attribute
    # metadata, not a product. Bail out before price matching.
    if name and not valid_name(clean_name(name)):
        name = None
    price = None
    for k in PRICE_KEYS:
        v = lower.get(k)
        if isinstance(v, (int, float, str)) and normalise_price(v):
            price = v
            break
        if isinstance(v, dict):  # e.g. price: {amount: 6.5, currency: GBP}
            for kk in PRICE_KEYS:
                vv = v.get(kk) if isinstance(v.get(kk), (int, float, str)) else None
                if vv is not None and normalise_price(vv):
                    price = vv
                    break
            if price is not None:
                break

    if name and price is not None:
        desc = next((lower[k] for k in ("description", "desc", "summary", "subtitle")
                     if isinstance(lower.get(k), str)), "")
        if collector.add(name, price, description=desc):
            count += 1

    for value in node.values():
        if isinstance(value, (dict, list)):
            count += _walk_state(value, collector, depth + 1)
    return count


# =============================================================================
# TIER 3 — microdata (itemprop attributes)
# =============================================================================

def extract_microdata(soup: BeautifulSoup, collector: RowCollector) -> int:
    count = 0
    for scope in soup.find_all(attrs={"itemtype": re.compile(r"(Product|MenuItem)", re.I)}):
        name_el  = scope.find(attrs={"itemprop": "name"})
        price_el = scope.find(attrs={"itemprop": "price"})
        if not name_el or not price_el:
            continue
        price = price_el.get("content") or price_el.get_text(strip=True)
        if collector.add(name_el.get_text(strip=True), price):
            count += 1
    return count


# =============================================================================
# TIER 4 — card-based DOM heuristic
# =============================================================================

def _visible_text(el: Tag) -> str:
    return el.get_text(separator=" ", strip=True)


def _count_price_groups(el: Tag) -> int:
    """How many *distinct price-bearing leaf elements* live under el."""
    leaves = 0
    for child in el.find_all(True):
        if child.find(True):          # not a leaf
            continue
        if PRICE_RE.search(child.get_text()):
            leaves += 1
    if leaves == 0 and PRICE_RE.search(_visible_text(el)):
        leaves = 1
    return leaves


def _is_struck_through(el: Tag) -> bool:
    """Was-price detection: <del>/<s> tags or strike-y class names."""
    for node in [el] + list(el.parents):
        if not isinstance(node, Tag):
            break
        if node.name in ("del", "s", "strike"):
            return True
        classes = " ".join(node.get("class", [])).lower()
        if any(w in classes for w in ("was", "strike", "old-price", "previous")):
            return True
        if node.name in ("li", "article", "section", "body"):
            break
    return False


def _classify_leaf(el: Tag, text: str) -> str:
    """Classify a price-bearing leaf: 'primary' | 'per_kg' | 'skip'."""
    lower = text.lower()
    if _is_struck_through(el):
        return "skip"
    if re.search(r"\bany\s+\d+\s+for\b", lower) or "meal deal" in lower:
        return "skip"                      # multibuy promos, not item prices
    if "per unit" in lower or "per kg" in lower or "/kg" in lower \
            or PER_KG_RE.search(text):
        return "per_kg"
    classes = " ".join(el.get("class", [])).lower()
    parent = el.find_parent()
    if parent is not None:
        classes += " " + " ".join(parent.get("class", [])).lower()
    if any(w in classes for w in ("per-unit", "ppu", "unit-price", "promo", "offer")):
        return "per_kg" if "unit" in classes or "ppu" in classes else "skip"
    return "primary"


def _count_primary_leaves(el: Tag, primary_ids: set, primaries: list) -> int:
    """Count by IDENTITY: BeautifulSoup tags hash/compare by content, so
    identical-looking price tags collapse in a set — must use id()."""
    n = 0
    el_id = id(el)
    for leaf in primaries:
        if leaf is el or any(id(p) == el_id for p in leaf.parents):
            n += 1
    return n


def extract_cards(soup: BeautifulSoup, collector: RowCollector) -> int:
    body = soup.body or soup
    count = 0

    # Strip chrome regions — nav menus, headers, footers, cookie banners
    for chrome in body.select(
        "nav, header, footer, aside, "
        "[role='navigation'], [class*='breadcrumb' i], [class*='cookie' i]"
    ):
        chrome.decompose()

    # 1. collect price-bearing leaves and classify them
    primary, per_kg_leaves = [], []
    for el in body.find_all(True):
        text = el.get_text(separator=" ", strip=True)
        if not PRICE_RE.search(text):
            continue
        if any(PRICE_RE.search(c.get_text()) for c in el.find_all(True)):
            continue  # keep innermost only
        kind = _classify_leaf(el, text)
        if kind == "primary":
            primary.append(el)
        elif kind == "per_kg":
            per_kg_leaves.append(el)

    primary_ids = {id(p) for p in primary}
    candidates = []

    for leaf in primary:
        leaf_text = _visible_text(leaf)
        m = PRICE_RE.search(leaf_text)
        price = m.group(0)

        # 2. card = smallest ancestor containing exactly ONE primary leaf
        card = leaf
        for ancestor in leaf.parents:
            if not isinstance(ancestor, Tag) or ancestor.name in ("body", "html"):
                break
            if _count_primary_leaves(ancestor, primary_ids, primary) > 1:
                break
            card = ancestor

        # 3. name inside the card, else just before it
        fallback = False
        name = _name_from_card(card, leaf)
        if not valid_name(clean_name(name or "")):
            name = _name_near_card(card)
            fallback = True
        if not name:
            continue

        # 4. attach a per-kg price if one lives in the same card
        per_kg_price = ""
        for aux in per_kg_leaves:
            if card in aux.parents or aux is card:
                am = PRICE_RE.search(_visible_text(aux))
                if am:
                    per_kg_price = am.group(0)
                    break

        description = _description_from_card(card, name, leaf)
        candidates.append((name, price, per_kg_price, fallback, description))

    # A fallback name shared by 2+ different prices is a section header
    # ("Beef Meals", "Vegetarian Meals"...) — drop those rows entirely.
    from collections import defaultdict
    fallback_prices = defaultdict(set)
    for name, price, _, fb, _d in candidates:
        if fb:
            fallback_prices[clean_name(name).lower()].add(price)

    for name, price, per_kg_price, fb, description in candidates:
        if fb and len(fallback_prices[clean_name(name).lower()]) > 1:
            continue
        if collector.add(name, price, price_per_kg=per_kg_price,
                         description=description):
            count += 1

    return count


def _tree_path_ids(el: Tag) -> list:
    return [id(p) for p in el.parents]


def _lca_depth(a: Tag, b: Tag) -> int:
    """Depth of the lowest common ancestor of a and b — higher means the
    two elements are more tightly grouped (same product tile, not just
    the same page section)."""
    a_path = [id(a)] + _tree_path_ids(a)
    b_anc = {id(b)} | set(_tree_path_ids(b))
    b_depth = {pid: i for i, pid in enumerate([id(b)] + _tree_path_ids(b))}
    for pid in a_path:
        if pid in b_anc:
            # convert "steps up from b" into absolute-ish depth score
            return -b_depth[pid]
    return -999


def _name_from_card(card: Tag, price_leaf: Tag) -> str:
    """Choose the name candidate CLOSEST to the price leaf in the tree.
    Prevents a section heading (h2 'Mains') beating the product's own
    h4 when a section contains a single priced item."""
    best, best_score = "", None
    for priority, selector in enumerate(NAME_SELECTORS):
        for el in card.select(selector):
            if el is price_leaf or price_leaf in el.find_all(True):
                continue
            candidate = clean_name(_visible_text(el))
            if not valid_name(candidate):
                continue
            # primary: proximity to the price leaf; secondary: selector rank
            score = (_lca_depth(el, price_leaf), -priority)
            if best_score is None or score > best_score:
                best, best_score = candidate, score
    if best:
        return best
    # last resort: card text minus the price
    text = _visible_text(card)
    idx = text.find(price_leaf.get_text(strip=True)[:20])
    candidate = clean_name(text[:idx] if idx > 0 else text)
    return candidate if valid_name(candidate) else ""


DESC_SELECTORS = [
    '[class*="desc" i]', '[itemprop="description"]',
    '[class*="subtitle" i]', '[class*="summary" i]', "p", "small",
]


def _description_from_card(card: Tag, name: str, price_leaf: Tag) -> str:
    """Best-effort description: a text element in the card that isn't
    the name and isn't the price."""
    name_l = (name or "").strip().lower()
    for selector in DESC_SELECTORS:
        for el in card.select(selector):
            if el is price_leaf or price_leaf in el.find_all(True):
                continue
            text = re.sub(r"\s+", " ", _visible_text(el)).strip()
            if not text or len(text) < 10:
                continue
            if text.lower() == name_l or PRICE_RE.search(text):
                continue
            return text[:300]
    return ""


def _name_near_card(card: Tag) -> str:
    for sibling in card.find_previous_siblings():
        if not isinstance(sibling, Tag):
            continue
        if PRICE_RE.search(sibling.get_text()):
            continue
        candidate = clean_name(_visible_text(sibling))
        if valid_name(candidate):
            return candidate
    return ""


# =============================================================================
# HTML PIPELINE
# =============================================================================

def extract_from_html(soup, url, venue_name, location) -> list[dict]:
    collector = RowCollector(venue_name, location, url, "html_menu")

    tiers = [
        ("json-ld",   extract_jsonld),
        ("embedded",  extract_embedded_json),
        ("microdata", extract_microdata),
        ("dom-cards", extract_cards),
    ]
    for tier_name, fn in tiers:
        found = fn(soup, collector)
        if found:
            print(f"[{tier_name}: {found}]", end=" ", flush=True)
        # JSON-LD / embedded results are authoritative — if either yields a
        # decent number of rows, skip the noisier DOM heuristic.
        if tier_name in ("json-ld", "embedded") and len(collector.rows) >= 5:
            break

    return collector.rows


# =============================================================================
# PDF PIPELINE
# =============================================================================

def _line_prices(line: str, use_bare: bool) -> list:
    """All price matches in a line: £-prefixed always; bare d.dd only in
    bare mode (menus that omit the currency symbol)."""
    matches = list(PRICE_RE.finditer(line))
    if not matches and use_bare:
        matches = list(BARE_PRICE_RE.finditer(line))
    return matches


def _is_section_header(line: str) -> bool:
    """ALL-CAPS short lines with no price are section headers.
    Must contain letters — otherwise bare price lines like "9" match,
    since "9" == "9".upper()."""
    s = line.strip()
    return (bool(s) and len(s) < 45 and s == s.upper()
            and bool(re.search(r"[A-Z]", s))
            and not BARE_PRICE_RE.search(s)
            and not INT_PRICE_LINE_RE.match(s))


def _pdf_description(lines: list, idx: int, use_bare: bool) -> str:
    """The line after a priced item is its description if it carries no
    price of its own, isn't a section header, and looks like prose."""
    if idx + 1 >= len(lines):
        return ""
    nxt = lines[idx + 1].strip()
    if not nxt or len(nxt) > 110:
        return ""
    if _line_prices(nxt, use_bare) or _is_section_header(nxt):
        return ""
    if not re.search(r"[a-z]", nxt):      # no lowercase = header/decoration
        return ""
    return nxt


def _extract_pdf_lines(lines: list, collector: RowCollector) -> int:
    """Line-based menu parsing. Handles £-prefixed and bare prices,
    multi-serve lines ("Glass 3.45 / Pint 4.30"), ABV/Kcal noise, and
    attaches the following line as a description."""
    # Bare-price mode: only when the text has (almost) no £ symbols but
    # plenty of price-shaped numbers — prevents false hits in normal docs.
    pound_hits = sum(1 for ln in lines if PRICE_RE.search(ln))
    bare_hits  = sum(1 for ln in lines if BARE_PRICE_RE.search(ln))
    use_bare   = pound_hits < 3 and bare_hits >= 5

    count = 0
    for i, raw in enumerate(lines):
        line = re.sub(r"\.{2,}", " ", raw).strip()   # dotted leaders
        if not line:
            continue
        prices = _line_prices(line, use_bare)
        if not prices:
            continue

        first = prices[0]
        has_kcal = bool(KCAL_RE.search(line))
        name = KCAL_RE.sub("", line[: first.start()]).strip(" -–|:,")
        if len(clean_name(name)) < MIN_NAME_LEN:
            continue
        description = _pdf_description(lines, i, use_bare)

        if len(prices) == 1:
            if collector.add(name, first.group(0), description=description,
                             force_food=has_kcal):
                count += 1
            continue

        # strip every trailing serve label from the base name once,
        # so "DRAUGHT Glass 3.45 / Pint 4.30" -> base "DRAUGHT"
        base_name = name
        while True:
            m_tail = None
            for m_tail in SERVE_SIZE_RE.finditer(base_name):
                pass
            if m_tail and base_name.lower().endswith(m_tail.group(0).lower()):
                base_name = base_name[: m_tail.start()].strip(" -–|:,")
            else:
                break

        # Multi-price line: "DRAUGHT Glass 3.45 / Pint 4.30" — pair each
        # price with the serve-size label immediately before it.
        prev_end = first.start()
        # leading name may itself end with a serve label ("... Glass")
        for m in prices:
            label_zone = line[: m.start()] if m is first else line[prev_end: m.start()]
            size_m = None
            for size_m in SERVE_SIZE_RE.finditer(label_zone):
                pass                                   # keep the LAST label
            size = size_m.group(0) if size_m else ""
            if collector.add(base_name, m.group(0), size=size,
                             description=description, force_food=has_kcal):
                count += 1
            prev_end = m.end()

    return count


# =============================================================================
# IMAGE MENUS — spatial OCR (multi-pass tesseract + geometry pairing)
# Requires: pip install pytesseract pillow  +  apt install tesseract-ocr
# =============================================================================

PRICE_TOK_RE = re.compile(r"^£?\d{1,3}(?:\.\d{1,2})?$")
def _mostly_caps(text: str) -> bool:
    letters = [c for c in text if c.isalpha()]
    if not letters:
        return False
    return sum(c.isupper() for c in letters) / len(letters) >= 0.65

def _harvest_words(img):
    """Multi-pass OCR, merged + deduped by position. The 1x pass matters:
    upscaling can DEGRADE isolated digits (price columns), while the 3x
    pass helps small body text — so run both."""
    passes = []
    passes.append((img, 1, ""))
    passes.append((img, 1, "--psm 11"))
    big = ImageOps.autocontrast(ImageOps.grayscale(img).resize(
        (img.width*3, img.height*3), Image.LANCZOS))
    passes.append((big, 3, ""))
    passes.append((big, 3, "--psm 11"))
    # binarised full image — sharpens faint digits
    gray = ImageOps.grayscale(img)
    bw = gray.point(lambda px: 255 if px > 150 else 0)
    passes.append((bw, 1, "--psm 11"))
    # overlapping 3x3 tiles, sparse mode — tight crops rescue isolated
    # digits that vanish in full-page segmentation
    w, h = img.width, img.height
    tw, th = w // 3, h // 3
    for gy in range(3):
        for gx in range(3):
            x0, y0 = max(0, gx*tw - 40), max(0, gy*th - 40)
            x1, y1 = min(w, (gx+1)*tw + 40), min(h, (gy+1)*th + 40)
            crop = img.crop((x0, y0, x1, y1))
            cbig = ImageOps.autocontrast(ImageOps.grayscale(crop).resize(
                (crop.width*4, crop.height*4), Image.LANCZOS))
            passes.append((cbig, 4, "--psm 11", (x0, y0)))

    words, seen = [], []
    for p in passes:
        im, scale, cfg = p[0], p[1], p[2]
        ox, oy = p[3] if len(p) > 3 else (0, 0)
        d = pytesseract.image_to_data(im, config=cfg, output_type=Output.DICT)
        for i in range(len(d["text"])):
            t = d["text"][i].strip()
            conf = int(d["conf"][i])
            if not t or conf < 35:
                continue
            # junk guards: tiny noise tokens need higher confidence
            if len(t) == 1 and not t.isdigit() and t != "&":
                continue
            if len(t) == 2 and not t.isdigit() and t != "&" and conf < 60:
                continue
            if not re.search(r"[A-Za-z0-9£&]", t):
                continue
            x = d["left"][i]//scale + ox
            y = d["top"][i]//scale + oy
            ww = d["width"][i]//scale
            hh = d["height"][i]//scale
            # dedupe on NORMALISED text + geometry:
            #  - same word from another pass at a slight offset
            #  - tile-cut fragments: "GHNUTS" inside "DOUGHNUTS"'s box
            norm = re.sub(r"\W+", "", t).lower()
            dup = False
            for sx, sy, sw, sn in seen:
                if abs(y - sy) > 12:
                    continue
                if abs(x - sx) < 26 and norm == sn:
                    dup = True; break
                if abs(x - sx) < 8:
                    dup = True; break
                # fragment check: this word starts inside an existing
                # word's horizontal span and its text is a substring
                if sx <= x <= sx + sw and norm and norm in sn:
                    dup = True; break
                # or the existing word is a fragment of this one — keep
                # the longer one by replacing nothing (first wins is
                # fine because full-image passes run before tiles)
            if dup:
                continue
            seen.append((x, y, ww, norm))
            words.append(dict(text=t, x=x, y=y, w=ww, h=hh))
    return words

def _rows(words):
    """Cluster words into visual rows by y-centre."""
    if not words:
        return []
    med_h = sorted(w["h"] for w in words)[len(words)//2]
    tol = max(8, int(med_h * 0.7))
    rows = []
    for w in sorted(words, key=lambda w: w["y"] + w["h"]/2):
        cy = w["y"] + w["h"]/2
        for row in rows:
            if abs(row["cy"] - cy) <= tol:
                row["words"].append(w)
                row["cy"] = sum(x["y"]+x["h"]/2 for x in row["words"])/len(row["words"])
                break
        else:
            rows.append({"cy": cy, "words": [w]})
    return rows, med_h

def _segments(rows, gap=45):
    """Split each row into segments on big x-gaps; split trailing price
    tokens into their own segment."""
    segs = []
    for row in rows:
        ws = sorted(row["words"], key=lambda w: w["x"])
        cur = [ws[0]]
        for w in ws[1:]:
            prev = cur[-1]
            if w["x"] - (prev["x"] + prev["w"]) > gap:
                segs.append(_mk_seg(cur, row["cy"])); cur = [w]
            else:
                cur.append(w)
        segs.append(_mk_seg(cur, row["cy"]))
    out = []
    for s in segs:
        toks = s["text"].split()
        if len(toks) > 1 and PRICE_TOK_RE.match(toks[-1]):
            lastw = s["words"][-1]
            if PRICE_TOK_RE.match(lastw["text"]):
                name_words = s["words"][:-1]
                out.append(_mk_seg(name_words, s["cy"]))
                out.append(_mk_seg([lastw], s["cy"]))
                continue
        out.append(s)
    return out

def _mk_seg(words, cy):
    return {"words": words, "cy": cy,
            "x0": min(w["x"] for w in words),
            "x1": max(w["x"]+w["w"] for w in words),
            "text": " ".join(w["text"] for w in words),
            "h": max(w["h"] for w in words)}

def _second_chance_price(img, cx, cy, med_h, avoid_cys=()):
    """OCR a single expected price cell that the main passes missed.
    The crop is clamped to the midpoints toward the nearest known
    prices above and below — geometrically excluding their digits, so
    whatever is read can only belong to this row."""
    top = cy - med_h * 1.9
    bot = cy + med_h * 2.2          # wrapped items centre the price low
    above = [a for a in avoid_cys if a < cy]
    below = [a for a in avoid_cys if a > cy]
    if above:
        top = max(top, (cy + max(above)) / 2)
    if below:
        bot = min(bot, (cy + min(below)) / 2)
    if bot - top < med_h:
        return ""
    box = (max(0, int(cx - 18)), max(0, int(top)),
           min(img.width, int(cx + 46)), min(img.height, int(bot)))
    crop = img.crop(box)
    big = ImageOps.autocontrast(ImageOps.grayscale(crop).resize(
        (crop.width * 6, crop.height * 6), Image.LANCZOS))
    txt = pytesseract.image_to_string(
        big, config="--psm 7 -c tessedit_char_whitelist=0123456789.£").strip()
    txt = txt.strip(".£ ")
    return txt if txt and PRICE_TOK_RE.match(txt) else ""


def extract_image_menu(img):
    words = _harvest_words(img)
    rows, med_h = _rows(words)
    segs = _segments(rows)

    prices = [s for s in segs if PRICE_TOK_RE.match(s["text"])]
    texts  = [s for s in segs if not PRICE_TOK_RE.match(s["text"])
              and len(s["text"]) >= 3]

    def name_ok(s):
        """Display-size header text can't be an item name."""
        return s["h"] <= med_h * 2.2

    items = []
    used_texts = set()
    for p in sorted(prices, key=lambda s: s["cy"]):
        pcx = (p["x0"]+p["x1"])/2
        best, best_cost = None, None
        for t in texts:
            if id(t) in used_texts: continue
            if not name_ok(t): continue
            if t["x0"] > pcx: continue                  # name must start left of price
            dy = abs(t["cy"] - p["cy"])
            if dy > med_h*1.8: continue
            dx = max(0, p["x0"] - t["x1"])
            if dx > 460: continue
            cost = dy*3 + dx*0.4
            if best_cost is None or cost < best_cost:
                best, best_cost = t, cost
        if best is None: continue
        used_texts.add(id(best))
        items.append({"name_seg": best, "price": p["text"].lstrip("£")})

    # post-pass A: lowercase desc carried the price -> real name is the
    # ALLCAPS segment directly above, same column
    for it in items:
        s = it["name_seg"]
        if re.search(r"[a-z]", s["text"]):
            cands = [t for t in texts if id(t) not in used_texts
                     and _mostly_caps(t["text"])
                     and 0 < s["cy"] - t["cy"] <= med_h*2.6
                     and t["x0"] < s["x1"] and t["x1"] > s["x0"]]
            if cands:
                up = min(cands, key=lambda t: s["cy"] - t["cy"])
                used_texts.add(id(up))
                it["desc"] = re.sub(r"\s*\d+(?:\.\d+)?\s*$", "", s["text"])
                it["name_seg"] = up

    # second-chance pass (runs LAST, leftovers only): a price COLUMN
    # (>=3 prices sharing an x) implies aligned names should be priced.
    # Re-OCR the exact missing cell, accepting only interior positions.
    price_segs = [s for s in segs if PRICE_TOK_RE.match(s["text"])]
    recovered_cys = []
    cols = {}
    for p in price_segs:
        cols.setdefault(round(p["x0"] / 14), []).append(p)
    for ps in cols.values():
        if len(ps) < 3:
            continue
        col_x = sum(p["x0"] for p in ps) / len(ps)
        y_lo, y_hi = min(p["cy"] for p in ps), max(p["cy"] for p in ps)
        # panel = names of items already paired to THIS column's prices
        panel_names = []
        for it in items:
            for p in ps:
                if abs(it["name_seg"]["cy"] - p["cy"]) < med_h*1.5:
                    panel_names.append(it["name_seg"]); break
        if len(panel_names) < 2:
            continue
        nx_lo = min(n["x0"] for n in panel_names) - 12
        nx_hi = max(n["x0"] for n in panel_names) + 60
        for t in texts:
            if id(t) in used_texts or not _mostly_caps(t["text"]) \
                    or not name_ok(t):
                continue
            # strictly interior to the column, both axes
            if not (nx_lo <= t["x0"] <= nx_hi and y_lo < t["cy"] < y_hi):
                continue
            avoid = [p["cy"] for p in ps] + recovered_cys
            recovered = _second_chance_price(
                img, col_x, t["cy"], med_h, avoid_cys=avoid)
            if recovered:
                used_texts.add(id(t))
                items.append({"name_seg": t, "price": recovered})
                # approximate digit position for later clamping
                recovered_cys.append(t["cy"] + med_h * 0.8)

    # post-pass B: merge wrapped continuation lines. When an unpriced
    # segment has priced neighbours both above and below, language
    # disambiguates: a generic tail word ("FRIES", "STICKS", "RINGS")
    # CONTINUES the item above it; a distinctive word ("CRISSCROSS")
    # STARTS a name whose price rides the next line.
    TAIL_WORDS = {"FRIES", "STICKS", "STICK", "RING", "RINGS", "BITES",
                  "CHIPS", "WINGS", "NUGGETS", "BREAD", "SAUCE", "ROLL",
                  "ROLLS", "BALLS", "DOGS", "MEAL"}
    for t in sorted(texts, key=lambda t: t["cy"]):
        if id(t) in used_texts or not _mostly_caps(t["text"]) or not name_ok(t):
            continue
        above, below = None, None
        for it in items:
            s = it["name_seg"]
            if not _mostly_caps(s["text"]): continue
            if not (t["x0"] < s["x1"] and t["x1"] > s["x0"]): continue
            dy = t["cy"] - s["cy"]
            if abs(dy) > med_h*3.0: continue
            if dy > 0 and (above is None or dy < t["cy"]-above["name_seg"]["cy"]):
                above = it
            if dy < 0 and (below is None or -dy < below["name_seg"]["cy"]-t["cy"]):
                below = it
        if above and below:
            is_tail = t["text"].strip().upper() in TAIL_WORDS
            best = above if is_tail else below
        else:
            best = above or below
        if best is None:
            continue
        used_texts.add(id(t))
        s = best["name_seg"]
        if t["cy"] < s["cy"]:      # continuation above -> prepend
            best["name_seg"] = _mk_seg(t["words"] + s["words"], s["cy"])
        else:                      # below -> append
            best["name_seg"] = _mk_seg(s["words"] + t["words"], s["cy"])

    # post-pass C: attach lowercase description right below the name
    for it in items:
        if it.get("desc"): continue
        s = it["name_seg"]
        for t in texts:
            if id(t) in used_texts: continue
            if not re.search(r"[a-z]", t["text"]): continue
            same_col = t["x0"] < s["x1"]+50 and t["x1"] > s["x0"]-50
            if same_col and 0 < t["cy"] - s["cy"] <= med_h*2.4:
                it["desc"] = t["text"]; used_texts.add(id(t)); break

    out = []
    UPSELL_RE = re.compile(r"^(add|with|served|choose|both|all of|please)\b", re.I)
    for it in items:
        name = it["name_seg"]["text"]
        if UPSELL_RE.match(name) and re.search(r"[a-z]", name):
            continue
        while re.search(r"\s+\b[a-z]{1,3}[.,=]?\s*$", name):   # OCR'd diet tags
            name = re.sub(r"\s+\b[a-z]{1,3}[.,=]?\s*$", "", name)
        name = re.sub(r"\s+[=|•·]+\s*", " ", name)
        name = re.sub(r"\b(\w+)([,.]?\s+\1\b)+", r"\1", name, flags=re.I)
        desc = it.get("desc", "")
        desc = re.sub(r"\b(\w+)([,.]?\s+\1\b)+", r"\1", desc, flags=re.I)
        it["desc"] = desc.strip(" '‘,.")
        out.append((name.strip(" .,|-"), it["price"], it.get("desc","")))
    return out



IMAGE_EXTS = (".png", ".jpg", ".jpeg", ".webp", ".gif", ".bmp", ".tiff")


def is_image(url: str) -> bool:
    return url.lower().split("?")[0].endswith(IMAGE_EXTS)


def extract_from_image(img, url, venue_name, location,
                       source_type="image_menu") -> list[dict]:
    if not OCR_AVAILABLE:
        raise ImportError(
            "Image menu found but OCR is not installed.\n"
            "Run: pip install pytesseract pillow\n"
            "And install the engine: sudo apt install tesseract-ocr"
        )
    collector = RowCollector(venue_name, location, url, source_type)
    for name, price, desc in extract_image_menu(img):
        collector.add(name, price, description=desc)
    return collector.rows


NOISE_LINE_RE = re.compile(
    r"per portion|service charge|allergen|calories|registered charity|"
    r"subject to change|gluten free|please|look out for|goes directly",
    re.IGNORECASE,
)


def _extract_pdf_blocks(lines: list, collector: RowCollector) -> int:
    """Block-style menus where the price is a bare integer on its own
    line AFTER the name and description:

        Buffalo V NGC          <- name
        Ranch dressing         <- description
        9                      <- price

    Also handles inline integers ("Waffle fries Ve NGC 5"), dual prices
    ("7 / 12"), and two-column extraction artefacts where the previous
    item's price fuses onto the next name ("7 Sweet tooth brioche buns").
    """
    count = 0
    pend_name, pend_desc = "", []

    def reset():
        nonlocal pend_name, pend_desc
        pend_name, pend_desc = "", []

    def close(prices, sizes=None):
        nonlocal count
        if not pend_name:
            return
        desc = ", ".join(pend_desc)[:300]
        for j, p in enumerate(prices):
            size = (sizes[j] if sizes and j < len(sizes) else "")
            if collector.add(pend_name, p, size=size, description=desc):
                count += 1
        reset()

    for raw in lines:
        line = raw.strip()
        if not line:
            continue
        # long prose / footer noise resets any half-built item
        if len(line) > 110 or NOISE_LINE_RE.search(line):
            reset()
            continue
        if _is_section_header(line):
            reset()
            continue

        # "9"  or  "7 / 12"  alone on the line -> closes the pending item
        m = INT_PRICE_LINE_RE.match(line)
        if m:
            prices = [m.group(1)] + ([m.group(2)] if m.group(2) else [])
            close(prices)
            continue

        # "7 Sweet tooth brioche buns V" -> price 7 closes pending,
        # remainder starts the next item
        m = LEADING_INT_RE.match(line)
        if m:
            close([m.group(1)])
            line = line[m.end():].strip()
            if line:
                pend_name = line
            continue

        # "Waffle fries Ve NGC 5" -> complete single-line item
        m = TRAILING_INT_RE.search(line)
        if m and not pend_name:
            name_part = line[: m.start()].strip()
            if collector.add(name_part, m.group(1)):
                count += 1
            continue
        if m and pend_name:
            # pending item never got a price (column break) — discard it,
            # this line is a complete item of its own
            reset()
            name_part = line[: m.start()].strip()
            if collector.add(name_part, m.group(1)):
                count += 1
            continue

        # £-prices on a text line still work in block menus
        pm = PRICE_RE.search(line)
        if pm:
            reset()
            name_part = line[: pm.start()].strip(" -–|:,")
            if len(clean_name(name_part)) >= MIN_NAME_LEN:
                if collector.add(name_part, pm.group(0)):
                    count += 1
            continue

        # otherwise: first text line = name, later ones = description
        if not pend_name:
            pend_name = line
        else:
            pend_desc.append(line)
            if len(pend_desc) > 3:        # runaway block, not an item
                reset()

    return count


def extract_from_pdf(pdf_bytes, url, venue_name, location) -> list[dict]:
    collector = RowCollector(venue_name, location, url, "pdf_menu")

    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for page in pdf.pages:
            page_found = 0

            for table in page.extract_tables() or []:
                for row in table:
                    if not row:
                        continue
                    row_text = " ".join(str(c) for c in row if c)
                    m = PRICE_RE.search(row_text)
                    if not m:
                        continue
                    name = row_text[: row_text.find(m.group(0))]
                    if collector.add(name, m.group(0)):
                        page_found += 1

            if page_found:        # per-PAGE check
                continue

            raw_text = page.extract_text() or ""

            # Scanned / image-only page: no text layer -> rasterise + OCR
            if len(raw_text.strip()) < 40 and OCR_AVAILABLE:
                try:
                    pil = page.to_image(resolution=150).original
                    for name, price, desc in extract_image_menu(pil):
                        collector.add(name, price, description=desc)
                    continue
                except Exception:
                    pass

            lines = raw_text.splitlines()

            # Choose parser: block mode when the page is full of
            # standalone-integer price lines and (almost) no £ / d.dd
            pound = sum(1 for ln in lines if PRICE_RE.search(ln))
            dec   = sum(1 for ln in lines if BARE_PRICE_RE.search(ln))
            ints  = sum(1 for ln in lines if INT_PRICE_LINE_RE.match(ln.strip())
                        or TRAILING_INT_RE.search(ln.strip()))
            if pound < 3 and dec < 3 and ints >= 4:
                _extract_pdf_blocks(lines, collector)
            else:
                _extract_pdf_lines(lines, collector)

    return collector.rows


# =============================================================================
# CSV I/O  (unchanged from v1 apart from minor cleanup)
# =============================================================================

def load_venues(csv_path: str) -> list[dict]:
    path = Path(csv_path)
    if not path.exists():
        raise FileNotFoundError(f"Input file not found: {csv_path}")

    venues = []
    with open(path, newline="", encoding="utf-8-sig") as f:
        # skipinitialspace: handles space-padded CSVs ("name, url, ...")
        # and quoted fields that follow a space (, "a, b")
        reader = csv.DictReader(f, skipinitialspace=True)
        reader.fieldnames = [h.strip().lower() for h in reader.fieldnames]
        for i, row in enumerate(reader, start=2):
            row = {k.strip().lower(): (v or "").strip()
                   for k, v in row.items()
                   if k is not None and isinstance(v, (str, type(None)))}
            url, location = row.get("url", ""), row.get("location", "")
            if not url:
                print(f"  [row {i}] Skipped — missing URL")
                continue
            if not location:
                print(f"  [row {i}] Skipped — missing location")
                continue
            # Multiple locations per venue: separated by ';' or '|'
            # e.g.  "Newcastle; Leeds; Manchester"
            locations = [loc.strip() for loc in re.split(r"[;|]", location)
                         if loc.strip()]
            venue_name = (row.get("venue_name") or row.get("name")
                          or url.split("/")[2])
            venues.append({"venue_name": venue_name, "url": url,
                           "locations": locations,
                           "note": row.get("note", "")})
    return venues


def save_rows(rows: list[dict], output_path: Path):
    output_path.parent.mkdir(parents=True, exist_ok=True)
    write_header = not output_path.exists() or output_path.stat().st_size == 0
    with open(output_path, "a", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=OUTPUT_COLUMNS,
                                extrasaction="ignore")
        if write_header:
            writer.writeheader()
        writer.writerows(rows)


# =============================================================================
# MAIN
# =============================================================================

SKIP_IMG_RE = re.compile(r"logo|icon|sprite|avatar|favicon|badge|social|"
                         r"payment|arrow|banner", re.IGNORECASE)


def _img_candidates(soup, base_url):
    """Rank <img> tags by likelihood of being a menu image.

    Pass 1: src/alt mentions 'menu'.  Pass 2 (only if pass 1 is empty):
    any content image, largest declared dimensions first.  Lazy-load
    attributes and srcset are honoured; obvious chrome (logos, icons,
    social badges) is skipped.
    """
    hinted, generic = [], []
    for im in soup.find_all("img"):
        cand = (im.get("src") or im.get("data-src")
                or im.get("data-lazy-src") or "")
        if not cand and im.get("srcset"):
            # srcset: take the last (usually largest) URL
            cand = im["srcset"].split(",")[-1].strip().split(" ")[0]
        if not cand:
            continue
        path = cand.lower().split("?")[0]
        if not path.endswith(IMAGE_EXTS):
            continue
        hint = (cand + " " + (im.get("alt") or "") + " "
                + " ".join(im.get("class") or [])).lower()
        if SKIP_IMG_RE.search(hint):
            continue
        try:
            w = int(re.sub(r"\D", "", str(im.get("width") or 0)) or 0)
            h = int(re.sub(r"\D", "", str(im.get("height") or 0)) or 0)
        except ValueError:
            w = h = 0
        if 0 < w < 200 or 0 < h < 200:      # declared tiny = chrome
            continue
        full = requests.compat.urljoin(base_url, cand)
        if "menu" in hint:
            hinted.append((w * h, full))
        else:
            generic.append((w * h, full))
    pool = hinted or generic
    pool.sort(key=lambda t: -t[0])           # biggest first, 0-area last
    seen, out = set(), []
    for _, u in pool:
        if u not in seen:
            seen.add(u)
            out.append(u)
    return out[:3]


def ocr_page_images(soup, url, venue_name, location) -> list[dict]:
    rows = []
    for iu in _img_candidates(soup, url):
        try:
            r = requests.get(iu, headers=HEADERS, timeout=20)
            r.raise_for_status()
            pil = Image.open(io.BytesIO(r.content))
            if pil.width < 400:              # actual tiny image: skip
                continue
            print(f"(OCR {iu.rsplit('/',1)[-1]}...)", end=" ", flush=True)
            rows += extract_from_image(pil, iu, venue_name, location)
        except Exception:
            continue
    return rows

def upload_to_supabase(rows: list[dict], run_id: str) -> None:
    if not DB_URL:
        print("  [Supabase] No SUPABASE_DB_URL set — skipping upload")
        return
    try:
        engine = create_engine(
            DB_URL,
            connect_args={"sslmode": "require", "connect_timeout": 10},
            pool_pre_ping=True,
        )
        df = pd.DataFrame(rows)
        df["scrape_run_id"] = run_id
        df.to_sql("raw_pricing", engine, if_exists="append", index=False)
        print(f"  [Supabase] Uploaded {len(df)} rows (run_id: {run_id})")
    except Exception as e:
        print(f"  [Supabase] Upload failed — {e}")

def main():
    output_path = OUTPUT_DIR / f"raw_pricing_{TODAY}.csv"

    # Fresh file every run — appending across runs mixes old bad rows
    # with new ones and creates duplicates.
    if output_path.exists():
        output_path.unlink()

    print()
    print("=" * 60)
    print("  IH Solutions — Competitor Pricing Scraper v2")
    print("=" * 60)
    print(f"  Input  : {INPUT_CSV}")
    print(f"  Output : {output_path}")
    print(f"  Date   : {TODAY}")
    print("=" * 60)
    print()

    try:
        venues = load_venues(INPUT_CSV)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return

    if not venues:
        print("No valid venues found in the CSV. Nothing to do.")
        return

    print(f"Loaded {len(venues)} venue(s)\n")

    total_rows, errors = 0, []
    run_id = str(uuid.uuid4())
    all_rows = []
    

    for i, venue in enumerate(venues, start=1):
        name, url = venue["venue_name"], venue["url"]
        note = venue.get("note", "")
        locations = venue["locations"]
        location = locations[0]          # scrape under the first location
        pdf = is_pdf(url)

        print(f"[{i}/{len(venues)}]  {name}")
        print(f"  url       : {url}")
        print(f"  locations : {', '.join(locations)}")
        print(f"  type      : {'pdf_menu' if pdf else 'html_menu'}")

        try:
            if is_image(url):
                print("  fetching image...", end=" ", flush=True)
                resp = requests.get(url, headers=HEADERS, timeout=20)
                resp.raise_for_status()
                img = Image.open(io.BytesIO(resp.content))
                print("OCR...", end=" ", flush=True)
                rows = extract_from_image(img, url, name, location)
            elif pdf:
                print("  fetching PDF...", end=" ", flush=True)
                rows = extract_from_pdf(fetch_pdf_bytes(url), url, name, location)
            else:
                print("  fetching HTML...", end=" ", flush=True)
                soup, _ = fetch_html(url)
                print("extracting...", end=" ", flush=True)
                rows = extract_from_html(soup, url, name, location)

                # No rows but the page embeds images? OCR the most
                # likely menu candidates.
                if not rows and OCR_AVAILABLE:
                    rows += ocr_page_images(soup, url, name, location)

                # Structured tiers found nothing AND DOM found nothing,
                # but the page had text? Probably a JS skeleton — retry.
                if not rows and SELENIUM_AVAILABLE:
                    print("(0 rows — retrying with Selenium...)", end=" ", flush=True)
                    soup, _ = fetch_html_selenium(url)
                    rows = extract_from_html(soup, url, name, location)
                    # the rendered page may reveal the menu images too
                    if not rows and OCR_AVAILABLE:
                        rows += ocr_page_images(soup, url, name, location)

            for r in rows:
                r["note"] = note

            # Fan out: one copy of every row per location. The menu is
            # fetched once; only the location column differs.
            if rows and len(locations) > 1:
                expanded = []
                for loc in locations:
                    for row in rows:
                        r = dict(row)
                        r["location"] = loc
                        expanded.append(r)
                rows = expanded

            print(f"{len(rows)} rows"
                  + (f" ({len(locations)} locations)" if len(locations) > 1 else ""))

            if rows:
                save_rows(rows, output_path)
                total_rows += len(rows)
                all_rows.extend(rows)
            else:
                print("  ⚠  No priced items found — check the URL points at an "
                      "actual menu/listing page, not a landing page")

        except requests.exceptions.HTTPError as e:
            msg = f"HTTP {e.response.status_code}"
            print(f"failed — {msg}")
            errors.append({"venue": name, "error": msg})
        except requests.exceptions.ConnectionError:
            print("failed — connection error")
            errors.append({"venue": name, "error": "connection error — check URL"})
        except requests.exceptions.Timeout:
            print("failed — timed out")
            errors.append({"venue": name, "error": "request timed out"})
        except Exception as e:
            print(f"failed — {e}")
            errors.append({"venue": name, "error": str(e)})

        print()
        if i < len(venues):
            time.sleep(2)

    print("=" * 60)
    print(f"  Venues processed : {len(venues)}")
    print(f"  Rows collected   : {total_rows}")
    print(f"  Errors           : {len(errors)}")
    if total_rows:
        print(f"  Saved to         : {output_path}")
    print("=" * 60)
    
    if all_rows:
        upload_to_supabase(all_rows, run_id)

    if errors:
        print("\nFailed venues:")
        for err in errors:
            print(f"  ✗  {err['venue']} — {err['error']}")


if __name__ == "__main__":
    main()
