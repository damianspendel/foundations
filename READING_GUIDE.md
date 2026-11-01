# Reading guide: where to start

About 5,600 checked definitions and theorems is too many to browse, so start here. The list
comes from an independent project-wide audit. Each entry gives the theorem name, the file, and
its meaning in plain words. On the site, type the name into the map's search box to see its
statement, its proof and everything it rests on.

| # | Result | File | In plain words |
|---|--------|------|----------------|
| 1 | `godel_first_incompleteness`, `PA_rosser` | `Logic/Incompleteness.lean`, `Logic/Rosser.lean` | If Peano Arithmetic is consistent, some sentence is neither provable nor refutable in it. |
| 2 | `godel_second_PA_unconditional` | `Logic/DerivabilityConditions.lean` | PA does not prove its own consistency, expressed with the provability formula `provH`. Read the caveat in the docstring: Gödel II depends on how provability is formalised. |
| 3 | `completeness`, `compactness` | `Logic/FOCompleteness.lean` | First-order logic proves exactly what is true in all models (Gödel 1929), for countable languages. |
| 4 | `halting_undecidable`, `tarski_undefinability` | `Logic/Undecidability.lean`, `Logic/DiagonalLemma.lean` | No program decides halting, and no arithmetic formula defines arithmetic truth. |
| 5 | `nonstandard_model` | `Logic/NonstandardArithmetic.lean` | PA has a countable model containing an "infinite" number. |
| 6 | `cut_elimination` | `Logic/CutElimination.lean` | Gentzen's Hauptsatz: every proof can be made cut-free, so the calculus is consistent syntactically. |
| 7 | `strong_normalization` | `Types/SystemFNormalization.lean` | Every well-typed program of System F terminates (Girard). |
| 8 | `goodstein_terminates` | `Logic/Goodstein.lean` | Every Goodstein sequence reaches 0, via the well-foundedness of ε₀. |
| 9 | `categoricity` | `Numbers/CompleteOrderedField.lean` | Any two complete ordered fields are uniquely isomorphic: "the" real numbers are well defined. |
| 10 | `fta`, `pi_irrational` | `Numbers/FTA.lean`, `Numbers/PiIrrational.lean` | Every non-constant complex polynomial has a root, and π is irrational. |
| 11 | `quintic_not_solvable_by_radicals` | `Algebra/QuinticNotRadical.lean` | No root of x⁵ − 6x + 3 can be written with + − × ÷ and n-th roots (Abel–Ruffini, Galois). |
| 12 | `quadratic_reciprocity` | `Algebra/Reciprocity.lean` | Gauss's "golden theorem" about squares modulo primes. |
| 13 | `parallel_postulate_independent` | `Geometry/Independence.lean` | Euclid's parallel postulate does not follow from the other axioms: the Klein model satisfies them but not Euclid's axiom. |
| 14 | `zorn`, `hartogs_theorem`, `schroeder_bernstein` | `Sets/Choice.lean`, `Sets/Hartogs.lean`, `Sets/SchroederBernstein.lean` | The core of set theory and cardinal arithmetic. |
| 15 | `basel`, `stirling`, `vitali` | `Topology/Basel.lean`, `Topology/Stirling.lean`, `Topology/Vitali.lean` | Σ 1/n² = π²/6; n! ≈ √(2πn)(n/e)ⁿ; there is no way to measure the length of *every* subset of [0, 1). |

Also worth a look: `El_summary` (`Bridges/ETCSvsZF.lean`: ZF sets sit fully and faithfully inside
the structural, categorical world), `reals_in_sets` (`Bridges/RealsInSets.lean`: ℝ built from pure
sets), `yoneda`, `lawvere_fixed_point` (one diagonal argument behind Cantor, Russell and Gödel),
`bertrand`, `A5_simple`, `sylow_first`, `dominated_convergence`.

## Honest caveats the audit raised

- **Gödel II** holds for the provability formula `provH`. It is not shown PA-provably equivalent to the textbook Con(PA).
- **Independence of the parallel postulate** is shown with models: "not provable" means "fails in a model". No formal proof system for geometry is built.
- **Constructible numbers** (doubling the cube, trisecting the angle) are defined algebraically, as Descartes and Wantzel did. The link to actual ruler-and-compass constructions is described, not formalised.
- **Gentzen's consistency proof of PA** is described, with only the abstract descent principle formalised. PA's consistency is proved through its standard model instead.
- **Lebesgue measure** is finite (taken on intervals); infinite measure on all of ℝ is not built.
- **Continuity on [a, b]** means two-sided continuity at every point of [a, b]. This loses nothing, since f can be extended constantly outside [a, b].
- **Duplicate notions** that are not unified: "countable" (injection into ℕ vs surjection from ℕ), "finite" (several versions), finite sums, and factorial (defined three times).
