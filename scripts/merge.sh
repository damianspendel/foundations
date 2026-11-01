#!/usr/bin/env bash
# Merge worker copies into the main project, build, extract graph, build site.
set -e
cd "$(dirname "$0")/.."
imports=""
for p in ${PARTS:-Sets Numbers Logic Algebra Types Geometry Categories Topology Combinatorics Probability Bridges NumberTheory}; do
  src=/home/claude/work/${p,,}/Foundations
  if [ -f "$src/$p.lean" ]; then
    rm -rf Foundations/$p && cp -r "$src/$p" Foundations/ && cp "$src/$p.lean" Foundations/
    imports+="import Foundations.$p"$'\n'
  fi
done
: > Foundations.lean; for q in Sets Numbers Logic Algebra Types Geometry Categories Topology Combinatorics Probability Bridges NumberTheory; do if [ -f Foundations/$q.lean ]; then echo "import Foundations.$q" >> Foundations.lean; fi; done
grep -q 'name = "extract"' lakefile.toml || cat >> lakefile.toml <<'T'

[[lean_exe]]
name = "extract"
root = "Extract"
supportInterpreter = true
T
lake build 2>&1 | grep -E "error|sorry|✖" || true
lake build extract >/dev/null
lake exe extract Foundations Foundations > site/graph.json
python3 scripts/check_axioms.py site/graph.json
python3 scripts/build_site.py site/graph.json https://github.com/damianspendel/foundations
