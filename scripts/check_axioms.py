"""Fail if any declaration depends on an axiom outside the standard three (this catches sorry,
which elaborates to sorryAx, and native_decide, which adds Lean.ofReduceBool), or if the
sources declare a new axiom."""
import json, pathlib, re, sys
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
g = json.loads(pathlib.Path(sys.argv[1]).read_text())
bad = [(n["name"], sorted(set(n["axioms"]) - ALLOWED)) for n in g["nodes"] if set(n["axioms"]) - ALLOWED]
root = pathlib.Path(__file__).resolve().parent.parent / "Foundations"
pat = re.compile(r"^\s*(private\s+)?axiom\s+[A-Za-z_][\w.]*\s*[:({\[]")
src_hits = [f"{f}:{i+1}" for f in root.rglob("*.lean") for i, l in enumerate(f.read_text().splitlines())
            if pat.match(l) and not l.strip().startswith("--")]
print(f"{len(g['nodes'])} declarations checked")
if bad or src_hits:
    for n, a in bad: print("non-standard axioms:", n, a)
    for h in src_hits: print("suspicious source line:", h)
    sys.exit(1)
print("OK: only propext, Classical.choice, Quot.sound; no sorry, no native_decide, no axiom declarations")
