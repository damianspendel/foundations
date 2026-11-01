# Foundations of mathematics, from scratch

Sets, numbers, logic, algebra, type theory, geometry and category theory, built in Lean 4 on nothing but the kernel and its three
standard axioms (propositional extensionality, quotient soundness, classical choice).
No Mathlib. Every theorem is machine-checked, and CI rejects any declaration that depends
on anything else (including `sorry`).

Site: an interactive map of every definition and theorem, a chapter-by-chapter reading
mode, and demos — built from the compiled Lean environment (`site/`).

## Contents

| Part | Highlights |
|------|-----------|
| I · Sets | Aczel's model of ZF inside type theory; all ZF axioms as theorems; Russell; Cantor; ω ≅ ℕ with the Peano axioms; Dedekind's recursion theorem and ω-arithmetic; Schröder–Bernstein; ordinals and Burali-Forti; Zorn's lemma and the well-ordering theorem; transfinite induction; comparability of cardinals; κ·κ = κ; infinite ⇔ Dedekind-infinite; Hartogs; Kőnig |
| II · Numbers | Peano ℕ → ℤ → ℚ → ℝ (Cauchy) as quotients, each bridged to the previous; FTA (existence and uniqueness); √2 irrational; ℝ a complete ordered field; uncountability; categoricity of complete ordered fields; Dedekind cuts ≅ Cauchy reals; Bolzano–Weierstrass, IVT, EVT; ℂ not orderable; derivatives, Rolle, mean value theorem; series, exp, log, e irrational; Riemann integral, Heine–Cantor, fundamental theorem of calculus; sin, cos, π; addition formulas and periodicity; complex exponential and Euler's identity e^{iπ} + 1 = 0; π irrational (Niven); **fundamental theorem of algebra** (d'Alembert–Argand); complex modulus, polar form, de Moivre, k-th roots; arccos |
| III · Logic | Propositional soundness, completeness (Lindenbaum and Kalmár) and compactness; Hilbert ≡ natural deduction; first-order logic with de Bruijn indices; Gödel's completeness theorem (Henkin); compactness; Löwenheim–Skolem; PA and its standard model; a non-standard model of PA; partial recursive functions, halting, Rice, Kleene's recursion theorem; universal function, Kleene normal form, s-m-n; Gödel's β-function; **Gödel's first incompleteness theorem for PA** (via soundness: a true sentence PA neither proves nor refutes) |
| IV · Algebra | groups, subgroups, homomorphisms; Lagrange; Fermat and Euler; Cayley; the three isomorphism theorems; rings, ideals, ℤ/nℤ a field iff n prime; group actions, orbit–stabiliser; Cauchy (McKay); Sylow I; ring first isomorphism theorem; Chinese remainder theorem; polynomial rings, division algorithm, factor theorem, root bound; Euclidean ⇒ PID; unique factorisation in ℤ and F[x]; Gaussian integers; Fermat's two-squares theorem (Zagier) |
| VI · Geometry | Tarski's axioms; ℝ² is a model of all eleven; Euclid I.1 (equilateral triangle) holds in ℝ² but fails in ℚ² (√3 irrational), so Euclid needs a continuity principle; Pythagoras and its converse; Thales; law of cosines; Heron; triangle inequality |
| VII · Categories | categories, functors, natural transformations; the category of groups; **Yoneda lemma** and embedding; terminal objects, products, equalisers, pullbacks (unique up to unique iso); adjunctions, free monoid ⊣ forgetful, types are cartesian closed; **Lawvere's fixed-point theorem**, with Cantor and Russell as corollaries |
| V · Types | untyped λ-calculus and Church–Rosser; simply typed λ-calculus: subject reduction, progress, strong normalization (Tait); Curry–Howard; cut elimination; excluded middle, Peirce and double-negation elimination unprovable intuitionistically; System F preservation, progress and strong normalization (Girard); Church encodings; the metatheory is constructive (no choice) |

## What it stands on

Lean's type theory is the ground floor, not ZF: Part I builds a *model* of ZF inside it.
Lean's built-in `Nat`/`Int` are used only after the from-scratch constructions are proved
isomorphic to them. Each declaration's axioms are listed on the site.

## Build

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build                                   # kernel-checks everything
lake build extract && lake exe extract Foundations Foundations > site/graph.json
python3 scripts/check_axioms.py site/graph.json
python3 scripts/build_site.py site/graph.json https://github.com/damianspendel/foundations
# site/dist/ now holds index.html + src.json; serve it with: python3 -m http.server -d site/dist
```

## Deployment (GitHub Actions → Cloudflare Pages)

`.github/workflows/deploy.yml` builds, checks axioms, builds the site and deploys
`site/dist` to the Cloudflare Pages project `maths` on every push to `main`.
One-time setup in the repo's **Settings → Secrets and variables → Actions**:

- `CLOUDFLARE_API_TOKEN` — token with *Account → Cloudflare Pages → Edit*
- `CLOUDFLARE_ACCOUNT_ID` — the 32-character id in your dashboard URL

Without the secrets the workflow still builds and verifies, and uploads the site as a
downloadable artifact. Custom domain (`maths.misterbig.org`) is attached once in the
Cloudflare dashboard under the Pages project's *Custom domains*.

## Conventions

See `CONVENTIONS.md`: no `sorry`/`axiom`/`native_decide`, docstrings on everything,
headline results start with `**Name.**`, each file opens with a narrative.
