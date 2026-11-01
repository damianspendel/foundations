"""Build the site into site/dist/: index.html (graph inlined) + src.json (Lean source per declaration).
Usage: python3 scripts/build_site.py graph.json [repo-url]"""
import json, pathlib, sys

root = pathlib.Path(__file__).resolve().parent.parent
site = root / "site"
dist = site / "dist"
dist.mkdir(exist_ok=True)

graph = json.loads(pathlib.Path(sys.argv[1]).read_text())

# Lean source for each declaration, sliced from its file by the recorded line range
cache, src = {}, {}
for n in graph["nodes"]:
    if not n.get("line"):
        continue
    f = root / (n["module"].replace(".", "/") + ".lean")
    if f not in cache:
        cache[f] = f.read_text().splitlines() if f.exists() else []
    lines = cache[f]
    start, end = n["line"] - 1, max(n.get("end", n["line"]), n["line"])
    # include the docstring directly above, if any
    s = start
    if s > 0 and lines[s - 1].rstrip().endswith("-/"):
        k = s - 1
        while k >= 0 and "/--" not in lines[k]:
            k -= 1
        if k >= 0:
            s = k
    src[n["name"]] = "\n".join(lines[s:end])
(dist / "src.json").write_text(json.dumps(src, ensure_ascii=False, separators=(",", ":")))

data = json.dumps(graph, separators=(",", ":"), ensure_ascii=False).replace("</", "<\\/")
html = (site / "template.html").read_text().replace("/*GRAPH*/null", data)
if len(sys.argv) > 2:
    html = html.replace('"/*REPO*/"', json.dumps(sys.argv[2]))
(dist / "index.html").write_text(html)
# keep a single-file copy at site/index.html for convenience
(site / "index.html").write_text(html)
print(f"wrote site/dist/index.html ({len(html)} bytes) and src.json ({len(src)} declarations)")
