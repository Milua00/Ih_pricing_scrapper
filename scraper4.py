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
    from selenium import webdriver
    from selenium.webdriver.chrome.service import Service
    from selenium.webdriver.common.by import By
    from selenium.webdriver.support.ui import WebDriverWait
    from selenium.webdriver.support import expected_conditions as EC
    from webdriver_manager.chrome import ChromeDriverManager
    SELENIUM_AVAILABLE = True
except ImportError:
    SELENIUM_AVAILABLE = False


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
    "venue_name", "brand", "location", "food_item", "price",
    "price_per_kg", "size", "is_drink", "type", "drink_item",
    "source_type", "source_url", "ingestion_date",
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
        "ingestion_date": TODAY,
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
    """ALL-CAPS short lines with no price are section headers."""
    s = line.strip()
    return bool(s) and len(s) < 45 and s == s.upper() and not BARE_PRICE_RE.search(s)


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

            lines = (page.extract_text() or "").splitlines()
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
        reader = csv.DictReader(f)
        reader.fieldnames = [h.strip().lower() for h in reader.fieldnames]
        for i, row in enumerate(reader, start=2):
            row = {k.strip().lower(): (v or "").strip() for k, v in row.items()}
            url, location = row.get("url", ""), row.get("location", "")
            if not url:
                print(f"  [row {i}] Skipped — missing URL")
                continue
            if not location:
                print(f"  [row {i}] Skipped — missing location")
                continue
            venue_name = (row.get("venue_name") or row.get("name")
                          or url.split("/")[2])
            venues.append({"venue_name": venue_name, "url": url,
                           "location": location})
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

    for i, venue in enumerate(venues, start=1):
        name, url, location = venue["venue_name"], venue["url"], venue["location"]
        pdf = is_pdf(url)

        print(f"[{i}/{len(venues)}]  {name}")
        print(f"  url  : {url}")
        print(f"  type : {'pdf_menu' if pdf else 'html_menu'}")

        try:
            if pdf:
                print("  fetching PDF...", end=" ", flush=True)
                rows = extract_from_pdf(fetch_pdf_bytes(url), url, name, location)
            else:
                print("  fetching HTML...", end=" ", flush=True)
                soup, _ = fetch_html(url)
                print("extracting...", end=" ", flush=True)
                rows = extract_from_html(soup, url, name, location)

                # Structured tiers found nothing AND DOM found nothing,
                # but the page had text? Probably a JS skeleton — retry.
                if not rows and SELENIUM_AVAILABLE:
                    print("(0 rows — retrying with Selenium...)", end=" ", flush=True)
                    soup, _ = fetch_html_selenium(url)
                    rows = extract_from_html(soup, url, name, location)

            print(f"{len(rows)} rows")

            if rows:
                save_rows(rows, output_path)
                total_rows += len(rows)
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

    if errors:
        print("\nFailed venues:")
        for err in errors:
            print(f"  ✗  {err['venue']} — {err['error']}")


if __name__ == "__main__":
    main()

