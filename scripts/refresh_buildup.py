"""Refresh site/dist/buildup.html: re-embed parts.svg / chapters.svg and update the counts line.

Usage: python3 scripts/refresh_buildup.py site/graph.json
Run after scripts/module_graph.py.
"""
import json, pathlib, re, sys

root = pathlib.Path(__file__).resolve().parent.parent
dist = root / "site" / "dist"
page = dist / "buildup.html"
g = json.loads(pathlib.Path(sys.argv[1]).read_text())
nodes = g["nodes"] if isinstance(g, dict) else g
total = len(nodes)
thms = sum(1 for n in nodes if n.get("kind") == "theorem")
html = page.read_text()


def svg(name):
    s = (dist / f"{name}.svg").read_text()
    return s[s.index("<svg"):].strip()


for fig in ("parts", "chapters"):
    pat = re.compile(r'(<div class="fig" id="%s">)<svg.*?</svg>' % fig, re.S)
    html, n = pat.subn(lambda m: m.group(1) + svg(fig), html, count=1)
    assert n == 1, fig

html, n = re.subn(r"[\d,]+ definitions and theorems \([\d,]+ theorems\)",
                  f"{total:,} definitions and theorems ({thms:,} theorems)", html, count=1)
assert n == 1
page.write_text(html)
print(f"buildup.html: {total:,} declarations, {thms:,} theorems")
