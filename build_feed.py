#!/usr/bin/env python3
"""
Convierte un canal PÚBLICO de Telegram en un feed RSS para el importador de Locucionar.

Lee https://t.me/s/<canal>, reconstruye cada gacetilla (título, bajada, cuerpo y fotos)
y genera docs/feed.xml. Pensado para correr cada pocos minutos en GitHub Actions.

Formato esperado de las gacetillas:
  - Título: primera línea en negrita
  - Bajada: línea(s) siguientes en cursiva
  - Cuerpo: el resto del texto
  - Fotos: mensajes aparte, publicados justo después del texto
"""
import json
import mimetypes
import os
import re
import sys
import unicodedata
from datetime import datetime, timedelta, timezone
from email.utils import format_datetime
from html import escape
from pathlib import Path

import requests
from bs4 import BeautifulSoup, Comment, NavigableString, Tag

# ---------------------------------------------------------------- configuración
CHANNEL = os.getenv("TG_CHANNEL", "PrensaMuniRGA")
BASE_URL = os.getenv("FEED_BASE_URL", "").rstrip("/")  # URL pública de docs/
OUT_DIR = Path(os.getenv("OUT_DIR", "docs"))
SOURCE_NAME = os.getenv("SOURCE_NAME", "Prensa Municipal RGA")
PAGES = int(os.getenv("TG_PAGES", "2"))                 # páginas del preview a leer (~20 mensajes c/u)
WAIT_MINUTES = int(os.getenv("WAIT_MINUTES", "15"))     # espera antes de publicar (ediciones / partes)
JOIN_MINUTES = int(os.getenv("JOIN_MINUTES", "10"))     # ventana para unir partes y fotos a una nota
MAX_ITEMS = int(os.getenv("MAX_ITEMS", "60"))           # notas que se conservan en el feed
EXTRA_IMAGES_IN_BODY = os.getenv("EXTRA_IMAGES_IN_BODY", "1") == "1"
DESCRIPTION_FULL = os.getenv("DESCRIPTION_FULL", "0") == "1"  # 1 = description lleva todo el texto

HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; isla365-feed/1.0)"}
IMG_DIR = OUT_DIR / "img"
STATE_FILE = OUT_DIR / "state.json"
FEED_FILE = OUT_DIR / "feed.xml"


# ---------------------------------------------------------------- descarga
def fetch_page(before=None):
    params = {"before": before} if before else None
    r = requests.get(f"https://t.me/s/{CHANNEL}", params=params, headers=HEADERS, timeout=30)
    r.raise_for_status()
    return r.text


def fetch_image(url, stem):
    """Descarga la foto a docs/img y devuelve el nombre de archivo (None si falla)."""
    IMG_DIR.mkdir(parents=True, exist_ok=True)
    existing = list(IMG_DIR.glob(stem + ".*"))
    if existing:
        return existing[0].name
    try:
        r = requests.get(url, headers=HEADERS, timeout=60)
        r.raise_for_status()
    except requests.RequestException as e:
        print(f"  ! no se pudo bajar la foto {stem}: {e}", file=sys.stderr)
        return None
    ctype = r.headers.get("content-type", "").split(";")[0].strip()
    ext = {"image/jpeg": ".jpg", "image/png": ".png", "image/webp": ".webp"}.get(ctype, ".jpg")
    (IMG_DIR / (stem + ext)).write_bytes(r.content)
    return stem + ext


# ---------------------------------------------------------------- parseo del HTML
def seg_html(text, href):
    t = escape(text.replace("\n", " ").replace("\xa0", " "))
    return f'<a href="{escape(href, quote=True)}">{t}</a>' if href else t


def to_line(segs):
    meaningful = [s for s in segs if s[0].strip()]
    if not meaningful:
        return None  # línea en blanco
    text = re.sub(r"\s+", " ", "".join(s[0] for s in segs).replace("\xa0", " ")).strip()
    html = "".join(seg_html(s[0], s[3]) for s in segs).strip()
    return {
        "text": text,
        "html": html,
        "bold": all(s[1] for s in meaningful),
        "italic": all(s[2] for s in meaningful),
    }


def text_to_lines(el):
    """Devuelve una lista de líneas {text, html, bold, italic}; None = línea en blanco."""
    lines = [[]]

    def walk(node, bold, italic, href):
        for ch in node.children:
            if isinstance(ch, Comment):
                continue
            if isinstance(ch, NavigableString):
                if str(ch):
                    lines[-1].append((str(ch), bold, italic, href))
            elif isinstance(ch, Tag):
                if ch.name == "br":
                    lines.append([])
                elif ch.name == "i" and "emoji" in (ch.get("class") or []):
                    # los emojis vienen envueltos en <i><b>: no son formato real
                    lines[-1].append((ch.get_text(), bold, italic, href))
                else:
                    link = ch.get("href", "") if ch.name == "a" else ""
                    walk(
                        ch,
                        bold or ch.name in ("b", "strong"),
                        italic or ch.name in ("i", "em"),
                        link if link.startswith("http") else href,
                    )

    walk(el, False, False, None)
    return [to_line(segs) for segs in lines]


def group_paragraphs(lines):
    paras, cur = [], []
    for ln in lines:
        if ln is None:
            if cur:
                paras.append("<p>" + "<br>".join(cur) + "</p>")
                cur = []
        else:
            cur.append(ln["html"])
    if cur:
        paras.append("<p>" + "<br>".join(cur) + "</p>")
    return paras


def parse_structure(lines):
    """Separa título (negrita), bajada (cursiva) y cuerpo."""
    i, n = 0, len(lines)
    while i < n and lines[i] is None:
        i += 1
    title_lines = []
    while i < n and lines[i] is not None and lines[i]["bold"]:
        title_lines.append(lines[i]["text"])
        i += 1
    if not title_lines:
        return {"title": None, "subtitle": "", "body": group_paragraphs(lines)}
    while i < n and lines[i] is None:
        i += 1
    sub = []
    while i < n and lines[i] is not None and lines[i]["italic"] and not lines[i]["bold"]:
        sub.append(lines[i]["text"])
        i += 1
    return {
        "title": " ".join(title_lines),
        "subtitle": " ".join(sub),
        "body": group_paragraphs(lines[i:]),
    }


def parse_dt(value):
    return datetime.fromisoformat(value).astimezone(timezone.utc)


def parse_messages(html):
    soup = BeautifulSoup(html, "html.parser")
    out = []
    for m in soup.select("div.tgme_widget_message[data-post]"):
        try:
            mid = int(m["data-post"].rsplit("/", 1)[1])
        except (ValueError, IndexError):
            continue
        t = m.select_one("a.tgme_widget_message_date time")
        if not t or not t.has_attr("datetime"):
            continue
        photos = []
        for a in m.select("a.tgme_widget_message_photo_wrap"):
            mm = re.search(r"url\(['\"]?([^'\")]+)", a.get("style", ""))
            if mm:
                photos.append(mm.group(1))
        text_el = m.select_one("div.js-message_text") or m.select_one("div.tgme_widget_message_text")
        struct = parse_structure(text_to_lines(text_el)) if text_el else None
        out.append({"id": mid, "time": parse_dt(t["datetime"]), "photos": photos, "struct": struct})
    return out


# ---------------------------------------------------------------- armado de notas
def build_notes(msgs):
    """Une mensajes sueltos en notas: título + bajada + cuerpo + fotos."""
    window = timedelta(minutes=JOIN_MINUTES)
    notes, cur = [], None
    for m in sorted(msgs, key=lambda x: x["id"]):
        s = m["struct"]
        if s and s["title"]:
            cur = {
                "first_id": m["id"],
                "pub": m["time"],
                "last": m["time"],
                "title": s["title"],
                "subtitle": s["subtitle"],
                "body": list(s["body"]),
                "photos": list(m["photos"]),
            }
            notes.append(cur)
        elif cur and m["time"] - cur["last"] <= window:
            if s and s["body"]:
                cur["body"] += s["body"]  # continuación de una nota larga
            cur["photos"] += m["photos"]
            cur["last"] = m["time"]
    return [n for n in notes if n["subtitle"] or n["body"]]


def norm_title(t):
    t = unicodedata.normalize("NFKD", t.lower())
    return re.sub(r"[^a-z0-9]", "", "".join(c for c in t if not unicodedata.combining(c)))


# ---------------------------------------------------------------- feed
def build_feed(items):
    def abs_img(name):
        return f"{BASE_URL}/img/{name}"

    newest = max((parse_dt(i["pub"]) for i in items), default=datetime.now(timezone.utc))
    p = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<rss version="2.0" xmlns:content="http://purl.org/rss/1.0/modules/content/" '
        'xmlns:media="http://search.yahoo.com/mrss/" xmlns:atom="http://www.w3.org/2005/Atom" '
        'xmlns:dc="http://purl.org/dc/elements/1.1/">',
        "<channel>",
        f"<title>{escape(SOURCE_NAME)}</title>",
        f"<link>https://t.me/{CHANNEL}</link>",
        f"<description>Gacetillas de {escape(SOURCE_NAME)}</description>",
        "<language>es-ar</language>",
        f"<lastBuildDate>{format_datetime(newest)}</lastBuildDate>",
        f'<atom:link href="{BASE_URL}/feed.xml" rel="self" type="application/rss+xml"/>',
    ]
    for it in sorted(items, key=lambda i: i["pub"], reverse=True):
        imgs = it.get("images", [])
        body = "".join(it["body"])
        if EXTRA_IMAGES_IN_BODY and len(imgs) > 1:
            body += "".join(f'<p><img src="{abs_img(n)}" alt=""></p>' for n in imgs[1:])
        short = it["subtitle"] or re.sub(r"<[^>]+>", "", " ".join(it["body"]))[:250]
        description = body if DESCRIPTION_FULL else escape(short)
        p.append("<item>")
        p.append(f"<title>{escape(it['title'])}</title>")
        p.append(f"<link>https://t.me/{CHANNEL}/{it['first_id']}</link>")
        p.append(f'<guid isPermaLink="false">{CHANNEL}-{it["first_id"]}</guid>')
        p.append(f"<pubDate>{format_datetime(parse_dt(it['pub']))}</pubDate>")
        p.append(f"<dc:creator>{escape(SOURCE_NAME)}</dc:creator>")
        p.append(f"<description><![CDATA[{description.replace(']]>', ']]&gt;')}]]></description>")
        p.append(f"<content:encoded><![CDATA[{body.replace(']]>', ']]&gt;')}]]></content:encoded>")
        if imgs:
            f = IMG_DIR / imgs[0]
            mime = mimetypes.guess_type(imgs[0])[0] or "image/jpeg"
            size = f.stat().st_size if f.exists() else 0
            p.append(f'<enclosure url="{abs_img(imgs[0])}" length="{size}" type="{mime}"/>')
            p.append(f'<media:content url="{abs_img(imgs[0])}" medium="image" type="{mime}"/>')
        p.append("</item>")
    p += ["</channel>", "</rss>"]
    return "\n".join(p) + "\n"


# ---------------------------------------------------------------- principal
def main():
    if not BASE_URL:
        sys.exit("Falta la variable FEED_BASE_URL (URL pública de la carpeta docs).")
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    IMG_DIR.mkdir(parents=True, exist_ok=True)

    state = {}
    if STATE_FILE.exists():
        state = {i["guid"]: i for i in json.loads(STATE_FILE.read_text("utf-8"))}

    msgs, before = {}, None
    for _ in range(PAGES):
        page = parse_messages(fetch_page(before))
        if not page:
            break
        for m in page:
            msgs[m["id"]] = m
        before = min(m["id"] for m in page)
    print(f"Mensajes leídos: {len(msgs)}")

    ready_before = datetime.now(timezone.utc) - timedelta(minutes=WAIT_MINUTES)
    seen_titles = {norm_title(i["title"]): g for g, i in state.items()}

    for n in build_notes(list(msgs.values())):
        guid = f"{CHANNEL}-{n['first_id']}"
        if n["last"] > ready_before:
            print(f"  · en espera: {n['title'][:60]}")
            continue
        key = norm_title(n["title"])
        if key in seen_titles and seen_titles[key] != guid:
            print(f"  · repetida, se omite: {n['title'][:60]}")
            continue
        if guid in state:
            continue  # ya está en el feed; no se vuelve a importar con cambios
        images = []
        for idx, url in enumerate(n["photos"]):
            name = fetch_image(url, f"{n['first_id']}_{idx}")
            if name:
                images.append(name)
        state[guid] = {
            "guid": guid,
            "first_id": n["first_id"],
            "pub": n["pub"].isoformat(),
            "title": n["title"],
            "subtitle": n["subtitle"],
            "body": n["body"],
            "images": images,
        }
        seen_titles[key] = guid
        print(f"  + nueva: {n['title'][:60]} ({len(images)} fotos)")

    items = sorted(state.values(), key=lambda i: i["pub"], reverse=True)[:MAX_ITEMS]

    used = {name for i in items for name in i.get("images", [])}
    for f in IMG_DIR.glob("*"):
        if f.name not in used:
            f.unlink()

    STATE_FILE.write_text(json.dumps(items, ensure_ascii=False, indent=1), "utf-8")
    FEED_FILE.write_text(build_feed(items), "utf-8")
    print(f"Feed listo: {len(items)} notas.")


if __name__ == "__main__":
    main()
