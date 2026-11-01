"""Build two Graphviz diagrams of how the project builds on itself, from site/graph.json:
  site/dist/parts.svg    — the ten parts, arrows weighted by cross-part dependencies
  site/dist/chapters.svg — every file (chapter), transitively reduced, clustered by part
Usage: python3 scripts/module_graph.py site/graph.json"""
import collections, json, pathlib, subprocess, sys
import networkx as nx

root = pathlib.Path(__file__).resolve().parent.parent
g = json.loads(pathlib.Path(sys.argv[1]).read_text())
PARTS = ["Sets", "Numbers", "Logic", "Algebra", "Types", "Geometry", "Categories", "Topology",
         "Combinatorics", "Probability", "Bridges"]
ROMAN = ["I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX", "X", "XI"]
COLORS = ["#7b4fb0", "#1f7a6c", "#b5532c", "#2f62b5", "#8a6d1d", "#a1356f", "#3d7a2a", "#6a4c93",
          "#b06a00", "#00798c", "#5a5a5a"]
SUB = ["a model of ZF", "ℕ → ℤ → ℚ → ℝ → ℂ, analysis", "proofs, models, Gödel", "groups, rings, fields",
       "λ-calculus, Curry–Howard", "Euclid, Tarski, Klein", "Yoneda, Lawvere", "compactness, ODEs, Basel",
       "Ramsey, Kőnig, Hall", "Bayes, large numbers", "the parts joined"]

mod_of = {n["name"]: n["module"] for n in g["nodes"]}
part_of_mod = lambda m: m.split(".")[1] if m.count(".") >= 1 else m
title = {}
for m in g["modules"]:
    t = next((l[2:].strip() for l in m["doc"].splitlines() if l.startswith("# ")), m["module"].split(".")[-1])
    title[m["module"]] = t.replace("`", "")
heads = collections.Counter(n["module"] for n in g["nodes"] if n["headline"])
size = collections.Counter(n["module"] for n in g["nodes"])

# module-level edges (dependency -> user)
E = collections.Counter()
for n in g["nodes"]:
    for d in n["deps"]:
        a, b = mod_of.get(d), n["module"]
        if a and a != b:
            E[(a, b)] += 1

def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")

# ---------- parts ----------
PE = collections.Counter()
for (a, b), w in E.items():
    pa, pb = part_of_mod(a), part_of_mod(b)
    if pa != pb and pa in PARTS and pb in PARTS:
        PE[(pa, pb)] += w
pcount = collections.Counter(part_of_mod(n["module"]) for n in g["nodes"])
lines = ['digraph parts {', 'rankdir=BT; bgcolor="transparent"; nodesep=0.5; ranksep=0.7;',
         'node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=13, penwidth=0, margin="0.25,0.12"];',
         'edge [color="#8a94a3", arrowsize=0.7];']
for i, p in enumerate(PARTS):
    if pcount[p] == 0:
        continue
    lines.append(f'"{p}" [label=<<b>{ROMAN[i]} · {p}</b><br/><font point-size="10">{esc(SUB[i])}<br/>{pcount[p]} declarations</font>>, fillcolor="{COLORS[i]}", fontcolor="white"];')
mx = max(PE.values()) if PE else 1
for (a, b), w in sorted(PE.items()):
    lines.append(f'"{a}" -> "{b}" [penwidth={0.8 + 4 * (w / mx) ** 0.5:.2f}, tooltip="{w} uses of {a} in {b}"];')
# conceptual dependencies: parts that use Lean's built-in ℕ/ℤ are licensed by the bridge theorems
BRIDGE = [("Sets", "Numbers", "ω ≅ ℕ"), ("Numbers", "Logic", "ℕ bridge"), ("Numbers", "Algebra", "ℕ, ℤ bridges"),
          ("Numbers", "Types", "ℕ bridge"), ("Numbers", "Combinatorics", "ℕ bridge")]
for a, b, lab in BRIDGE:
    if (a, b) not in PE:
        lines.append(f'"{a}" -> "{b}" [style=dashed, color="#b8c0cc", penwidth=1.2, label=<<font point-size="9" color="#7d8796">{esc(lab)}</font>>];')
lines.append("}")
dist = root / "site" / "dist"
dist.mkdir(parents=True, exist_ok=True)
(dist / "parts.dot").write_text("\n".join(lines))
subprocess.run(["dot", "-Tsvg", str(dist / "parts.dot"), "-o", str(dist / "parts.svg")], check=True)

# ---------- chapters ----------
G = nx.DiGraph()
mods = [m["module"] for m in g["modules"] if part_of_mod(m["module"]) in PARTS and m["module"].count(".") == 2]
G.add_nodes_from(mods)
for (a, b), w in E.items():
    if a in G and b in G:
        G.add_edge(a, b)
try:
    R = nx.transitive_reduction(G)
except nx.NetworkXError:  # not a DAG (shouldn't happen: imports are acyclic)
    R = G
lines = ['digraph chapters {', 'rankdir=LR; bgcolor="transparent"; compound=true; nodesep=0.12; ranksep=0.35; newrank=true;',
         'node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=10, penwidth=0, margin="0.12,0.05", fontcolor="white"];',
         'edge [color="#9aa3b0", arrowsize=0.5, penwidth=0.7];']
for i, p in enumerate(PARTS):
    ms = [m for m in mods if part_of_mod(m) == p]
    if not ms:
        continue
    lines.append(f'subgraph "cluster_{p}" {{ label=<<b>{ROMAN[i]} · {p}</b>>; fontname="Helvetica"; fontsize=14; fontcolor="{COLORS[i]}"; color="{COLORS[i]}"; style="rounded,dashed";')
    for m in ms:
        t = title.get(m, m.split(".")[-1])
        if len(t) > 46:
            t = t[:44].rsplit(" ", 1)[0] + " …"
        star = " ★" * min(heads[m], 1)
        lines.append(f'  "{m}" [label="{esc(t)}{star}", fillcolor="{COLORS[i]}", tooltip="{esc(m)} — {size[m]} declarations, {heads[m]} headline results"];')
    lines.append("}")
for a, b in R.edges():
    cross = part_of_mod(a) != part_of_mod(b)
    lines.append(f'"{a}" -> "{b}"' + (' [color="#c58b2b", penwidth=1.1, constraint=false]' if cross else "") + ";")
lines.append("}")
(dist / "chapters.dot").write_text("\n".join(lines))
subprocess.run(["dot", "-Tsvg", str(dist / "chapters.dot"), "-o", str(dist / "chapters.svg")], check=True)
print("parts:", len(PE), "cross-part edges;", "chapters:", G.number_of_nodes(), "files,",
      G.number_of_edges(), "edges →", R.number_of_edges(), "after transitive reduction")
