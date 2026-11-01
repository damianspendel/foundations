"""Inline graph JSON into site/template.html -> site/index.html.
Usage: python3 scripts/build_site.py graph.json [repo-url]"""
import json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent.parent / "site"
graph = json.dumps(json.loads(pathlib.Path(sys.argv[1]).read_text()), separators=(",", ":"), ensure_ascii=False)
graph = graph.replace("</", "<\\/")
html = (root / "template.html").read_text().replace("/*GRAPH*/null", graph)
if len(sys.argv) > 2:
    html = html.replace('"/*REPO*/"', json.dumps(sys.argv[2]))
(root / "index.html").write_text(html)
print("wrote site/index.html", len(html), "bytes")
