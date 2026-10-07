#!/usr/bin/env python3
"""Make a self-contained copy of viz/index.html for hosting on firstpair.org/learn/.

The /learn route allows inline scripts and styles but no external stylesheets, so the
Google Fonts are downloaded (Latin subset, woff2 or woff) and embedded as data: URIs.

  python3 viz/inline_fonts.py viz/index.html viz/arnold-meanders.html
"""
import base64
import re
import sys
import urllib.request

UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_0) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Safari/605.1.15"


def fetch(url):
    request = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()


source, target = sys.argv[1:3]
html = open(source, encoding="utf-8").read()
link = re.search(r'<link rel="stylesheet" href="(https://fonts\.googleapis\.com/[^"]+)">', html)
if not link:
    raise SystemExit("no Google Fonts stylesheet found")
css = fetch(link.group(1).replace("&amp;", "&")).decode("utf-8")

# Keep only the Latin subset of each face.
blocks = re.findall(r"/\* ([a-z-]+) \*/\s*(@font-face \{.*?\})", css, flags=re.S)
faces = []
for subset, block in blocks:
    if subset != "latin":
        continue
    url, kind = re.search(r"url\((https://[^)]+\.(woff2?))\)", block).groups()
    data = base64.b64encode(fetch(url)).decode("ascii")
    block = block.replace(url, f"data:font/{kind};base64,{data}")
    block = re.sub(r"\s*unicode-range:[^;]*;", "", block)
    faces.append(block)
if not faces:
    raise SystemExit("no Latin font faces found")

style = "<style>\n" + "\n".join(faces) + "\n</style>"
html = re.sub(r'<link rel="preconnect"[^>]*>\n', "", html)
html = html.replace(link.group(0), style)
open(target, "w", encoding="utf-8").write(html)
print(f"{target}: {len(faces)} font faces embedded, {len(html) // 1024} KB")
