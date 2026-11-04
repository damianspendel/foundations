import Foundations.Langlands.Padic
import Foundations.Langlands.Rep

/-!
# Part XV: Toward Langlands

The Langlands programme predicts a correspondence between Galois representations (arithmetic)
and automorphic representations (analysis), prime by prime and then globally. Nothing close to
that is formalised here. This part builds the first layers it stands on, from scratch:

* `Padic` — the local side at a prime `p`: the `p`-adic absolute value and the product formula,
  **Ostrowski's theorem** (every nontrivial absolute value on ℚ is equivalent to the usual one or
  to exactly one `|·|ₚ`), the `p`-adic integers `ℤₚ` as a complete ring, and **Hensel's lemma**.

* `Rep` — representations of finite groups, the language Langlands is written in: **Maschke's
  theorem**, **Schur's lemma** (with scalars over ℂ, via the fundamental theorem of algebra),
  characters and their **orthogonality**, multiplicities, and the bridge saying that for abelian
  groups the irreducible characters are exactly the Dirichlet-style characters of `DualGroup`.

Further pieces (cyclotomic fields, Gauss sums and reciprocity
as Galois theory) are added below as they are completed. Each sub-part's aggregator states
exactly what it proves and what it does not.
-/
