#!/usr/bin/env bash
# Merge worker copies into the main project, build, extract graph, build site.
set -e
cd "$(dirname "$0")/.."
imports=""
for p in ${PARTS:-Sets Numbers Logic}; do
  src=/home/claude/work/${p,,}/Foundations
  if [ -f "$src/$p.lean" ]; then
    rm -rf Foundations/$p && cp -r "$src/$p" Foundations/ && cp "$src/$p.lean" Foundations/
    imports+="import Foundations.$p"$'\n'
  fi
done
printf "import Foundations.Sets\nimport Foundations.Numbers\nimport Foundations.Logic\n" > Foundations.lean
grep -q 'name = "extract"' lakefile.toml || cat >> lakefile.toml <<'T'

[[lean_exe]]
name = "extract"
root = "Extract"
supportInterpreter = true
T
lake build 2>&1 | grep -E "error|sorry|✖" || true
lake build extract >/dev/null
lake exe extract Foundations Foundations > site/graph.json
python3 scripts/build_site.py site/graph.json "$@"
