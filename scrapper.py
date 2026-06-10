import csv
import io
import re
import time
from datetime import date
from pathlib import Path

import requests
import pdfplumber
from bs4 import BeautifulSoup


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

PRICE_RE = re.compile(r"£\s?\d+\.?\d{0,2}")

OUTPUT_COLUMNS = [
    "venue_name",
    "brand",
    "location",
    "food_item",
    "price",
    "price_per_kg",
    "size",
    "source_type",
    "source_url",
    "ingestion_date",
]


# =============================================================================
# HELPERS
# =============================================================================

def is_pdf(url: str) -> bool:
    """Return True if the URL points to a PDF file."""
    return url.lower().split("?")[0].endswith(".pdf")


def build_row(
    venue_name: str,
    location: str,
    url: str,
    food_item: str,
    price: str,
    source_type: str,
    size: str = "",
    price_per_kg: str = "",
) -> dict:
    """Return a single output row as a dictionary."""
    return {
        "venue_name":     venue_name,
        "brand":          "",           # populated in the cleaning stage
        "location":       location,
        "food_item":      food_item.strip(),
        "price":          price.strip(),
        "price_per_kg":   price_per_kg,
        "size":           size,
        "source_type":    source_type,
        "source_url":     url,
        "ingestion_date": TODAY,
    }


# =============================================================================
# FETCHERS
# =============================================================================

def fetch_html(url: str) -> BeautifulSoup:
    """
    Fetch an HTML page and return a BeautifulSoup object.
    Raises requests.exceptions.HTTPError on 4xx / 5xx responses.
    """
    response = requests.get(url, headers=HEADERS, timeout=15)
    response.raise_for_status()

    soup = BeautifulSoup(response.text, "html.parser")

    # Remove noise — scripts and styles pollute the extracted text
    for tag in soup(["script", "style", "noscript"]):
        tag.decompose()

    return soup


def fetch_pdf_bytes(url: str) -> bytes:
    """Download a PDF and return its raw bytes."""
    response = requests.get(url, headers=HEADERS, timeout=20)
    response.raise_for_status()
    return response.content


# =============================================================================
# EXTRACTORS
# =============================================================================

def extract_from_html(
    soup: BeautifulSoup,
    url: str,
    venue_name: str,
    location: str,
) -> list[dict]:
    """
    Walk every HTML element. If the element's text contains a £ price
    and has no child elements that also contain a price (to avoid
    duplicating parent + child), record it as a row.
    """
    rows = []

    for element in soup.find_all(True):
        text = element.get_text(separator=" ", strip=True)

        price_match = PRICE_RE.search(text)
        if not price_match:
            continue

        # Skip container elements — only keep the innermost price-bearing tag
        children_with_price = [
            child for child in element.find_all(True)
            if PRICE_RE.search(child.get_text())
        ]
        if children_with_price:
            continue

        price = price_match.group(0).strip()

        # Item name = everything before the £ sign in this element's text
        item_name = text[: text.find(price)].strip(" -|:,\n")
        if not item_name:
            item_name = text  # fallback to full text if nothing precedes the price

        # Skip rows where item name is very short or looks like boilerplate
        if len(item_name) < 3:
            continue

        rows.append(
            build_row(venue_name, location, url, item_name, price, "html_menu")
        )

    return rows


def extract_from_pdf(
    pdf_bytes: bytes,
    url: str,
    venue_name: str,
    location: str,
) -> list[dict]:
    """
    Extract food items and prices from a PDF.
    Tries table extraction first (most menus are tabular),
    falls back to line-by-line text extraction.
    """
    rows = []

    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for page in pdf.pages:

            # ── attempt 1: structured table extraction ──────────────
            tables = page.extract_tables()
            if tables:
                for table in tables:
                    for row in table:
                        if not row:
                            continue
                        # Join all cells into one string for price searching
                        row_text = " ".join(str(cell) for cell in row if cell)
                        price_match = PRICE_RE.search(row_text)
                        if not price_match:
                            continue
                        price     = price_match.group(0).strip()
                        item_name = row_text[: row_text.find(price)].strip(" -|:,")
                        if len(item_name) < 3:
                            continue
                        rows.append(
                            build_row(
                                venue_name, location, url,
                                item_name, price, "pdf_menu"
                            )
                        )
                # If we got table rows, skip the text fallback for this page
                if rows:
                    continue

            # ── attempt 2: raw text line by line ────────────────────
            raw_text = page.extract_text()
            if not raw_text:
                continue

            for line in raw_text.splitlines():
                line = line.strip()
                price_match = PRICE_RE.search(line)
                if not price_match:
                    continue
                price     = price_match.group(0).strip()
                item_name = line[: line.find(price)].strip(" -|:,")
                if len(item_name) < 3:
                    continue
                rows.append(
                    build_row(
                        venue_name, location, url,
                        item_name, price, "pdf_menu"
                    )
                )

    return rows


# =============================================================================
# CSV I/O
# =============================================================================

def load_venues(csv_path: str) -> list[dict]:
    """
    Load the input CSV and return a list of venue dicts.

    Required columns : url, location
    Optional column  : venue_name
    """
    path = Path(csv_path)
    if not path.exists():
        raise FileNotFoundError(f"Input file not found: {csv_path}")

    venues = []
    with open(path, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)

        # Normalise headers — strip whitespace and lowercase
        reader.fieldnames = [h.strip().lower() for h in reader.fieldnames]

        for i, row in enumerate(reader, start=2):
            row = {k.strip().lower(): v.strip() for k, v in row.items()}

            url      = row.get("url", "")
            location = row.get("location", "")

            if not url:
                print(f"  [row {i}] Skipped — missing URL")
                continue
            if not location:
                print(f"  [row {i}] Skipped — missing location")
                continue

            # venue_name is optional; fall back to the URL hostname
            venue_name = (
                row.get("venue_name", "").strip()
                or row.get("name", "").strip()
                or url.split("/")[2]
            )

            venues.append({
                "venue_name": venue_name,
                "url":        url,
                "location":   location,
            })

    return venues


def save_rows(rows: list[dict], output_path: Path):
    """
    Append rows to the output CSV.
    Writes the header row only if the file does not yet exist.
    """
    output_path.parent.mkdir(parents=True, exist_ok=True)
    write_header = not output_path.exists() or output_path.stat().st_size == 0

    with open(output_path, "a", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f, fieldnames=OUTPUT_COLUMNS, extrasaction="ignore"
        )
        if write_header:
            writer.writeheader()
        writer.writerows(rows)


# =============================================================================
# MAIN
# =============================================================================

def main():
    output_path = OUTPUT_DIR / f"raw_pricing_{TODAY}.csv"

    print()
    print("=" * 60)
    print("  IH Solutions — Competitor Pricing Scraper")
    print("=" * 60)
    print(f"  Input  : {INPUT_CSV}")
    print(f"  Output : {output_path}")
    print(f"  Date   : {TODAY}")
    print("=" * 60)
    print()

    # ── load venue list ───────────────────────────────────────────
    try:
        venues = load_venues(INPUT_CSV)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return

    if not venues:
        print("No valid venues found in the CSV. Nothing to do.")
        return

    print(f"Loaded {len(venues)} venue(s)\n")

    # ── process each venue ────────────────────────────────────────
    total_rows = 0
    errors     = []

    for i, venue in enumerate(venues, start=1):
        name     = venue["venue_name"]
        url      = venue["url"]
        location = venue["location"]
        pdf      = is_pdf(url)

        print(f"[{i}/{len(venues)}]  {name}")
        print(f"  location : {location}")
        print(f"  url      : {url}")
        print(f"  type     : {'pdf_menu' if pdf else 'html_menu'}")

        try:
            if pdf:
                print("  fetching PDF...", end=" ", flush=True)
                pdf_bytes = fetch_pdf_bytes(url)
                print("done")

                print("  extracting...", end=" ", flush=True)
                rows = extract_from_pdf(pdf_bytes, url, name, location)

            else:
                print("  fetching HTML...", end=" ", flush=True)
                soup = fetch_html(url)
                print("done")

                print("  extracting...", end=" ", flush=True)
                rows = extract_from_html(soup, url, name, location)

            print(f"{len(rows)} rows found")

            if rows:
                save_rows(rows, output_path)
                total_rows += len(rows)
            else:
                print("  ⚠  No priced items found — site may use JavaScript rendering")

        except requests.exceptions.HTTPError as e:
            msg = f"HTTP {e.response.status_code}"
            print(f"failed — {msg}")
            errors.append({"venue": name, "error": msg})

        except requests.exceptions.ConnectionError:
            msg = "connection error — check URL"
            print(f"failed — {msg}")
            errors.append({"venue": name, "error": msg})

        except requests.exceptions.Timeout:
            msg = "request timed out"
            print(f"failed — {msg}")
            errors.append({"venue": name, "error": msg})

        except Exception as e:
            print(f"failed — {e}")
            errors.append({"venue": name, "error": str(e)})

        print()

        # Polite crawling — wait between requests
        if i < len(venues):
            time.sleep(2)

    # ── summary ───────────────────────────────────────────────────
    print("=" * 60)
    print(f"  Venues processed : {len(venues)}")
    print(f"  Rows collected   : {total_rows}")
    print(f"  Errors           : {len(errors)}")
    if total_rows > 0:
        print(f"  Saved to         : {output_path}")
    print("=" * 60)

    if errors:
        print("\nFailed venues:")
        for err in errors:
            print(f"  ✗  {err['venue']} — {err['error']}")

    if errors and total_rows == 0:
        print(
            "\nAll venues failed. Most common reasons:\n"
            "  1. Site uses JavaScript rendering — requests can't see the menu\n"
            "  2. Cloudflare or bot protection blocking the request\n"
            "  3. URL has changed — check it in your browser first\n"
        )


if __name__ == "__main__":
    main()