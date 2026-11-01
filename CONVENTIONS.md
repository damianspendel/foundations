# Conventions for the Foundations project

Goal: build the foundations of mathematics in Lean 4 **from scratch** — sets,
then number systems, then logic — with every result kernel-checked, plus a
website that visualises the dependency graph of all definitions and theorems.

## Toolchain
- Lean 4.35.0 is installed at `/opt/lean` (`lean`, `lake` on PATH). **No Mathlib, no
  Batteries, no network installs.** Only Lean core.
- Useful core tactics: `omega` (linear arithmetic on Nat/Int), `grind` (incl. commutative
  ring normalisation, linear arithmetic, congruence closure; you can register your own
  `Lean.Grind.CommRing` / order instances to make `grind` work on your types),
  `simp`, `decide`, `induction`, `cases`, `rcases`, `obtain`, `exact?` (slow — avoid in final code).
- 2 CPU cores shared by several workers: build only your own modules
  (`lake build Foundations.Numbers.Int`), not everything, and keep individual files
  under ~800 lines so rebuilds stay fast.

## Rules
1. **No `sorry`, no `axiom`, no `native_decide`, no `implemented_by`/`extern` tricks.**
   Final check per headline theorem: `#print axioms X` must show only a subset of
   `[propext, Classical.choice, Quot.sound]`. Do these checks in a scratch file, not in the library.
2. Every `def`, `structure`, `inductive`, `theorem` that matters gets a **docstring**
   (`/-- ... -/`) in plain English. The website shows these. Mark headline results by
   starting the docstring with `**Name.**`, e.g. `/-- **Cantor's theorem.** No ... -/`.
3. Each file starts with a module docstring `/-! # Title ... -/` giving a short narrative:
   what is constructed, why, and how it connects to the previous file.
4. Namespaces: `Foundations.Sets`, `Foundations.Numbers`, `Foundations.Logic` (sub-namespaces fine).
   Do not open or modify other parts' folders.
5. Files live in `Foundations/<Part>/<Name>.lean`; also maintain an aggregator
   `Foundations/<Part>.lean` that imports all files of your part in order.
6. Prefer clear, readable proofs over golfed ones, but finishing matters more than elegance.
   If a stretch goal is too hard, stop at a clean milestone rather than leaving broken files.
   **Every file you leave must build without errors or sorry.**
7. Lean's own `Nat`/`Int` may be used once your part has proved the bridge
   (an isomorphism with the from-scratch construction); state that bridge theorem explicitly.

## Report back
When done, report: the list of files in order, the headline theorems (name + one-line
statement), anything attempted but dropped, and the result of `#print axioms` on the headline theorems.
