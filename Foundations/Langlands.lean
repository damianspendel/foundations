import Foundations.Langlands.Padic
import Foundations.Langlands.Rep
import Foundations.Langlands.Cyclotomic

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

* `Cyclotomic` — reciprocity as Galois theory, Langlands for GL(1) in its simplest case:
  irreducibility of `Φ_p` (Eisenstein), `Gal(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)ˣ` (`cycloGaloisIso`), Gauss sums
  with `g² = p*`, **quadratic reciprocity re-proved by Frobenius** (`quadratic_reciprocity_gauss`,
  Gauss's sixth proof), and Dirichlet characters read as characters of the Galois group, with
  `χ(Frob_q) = χ(q)` (`galChar_frobenius`).

Not formalised: ℚₚ as a field, Hasse's principle, Kronecker–Weber, Artin reciprocity in general,
modular forms, automorphic representations — that is, everything that makes Langlands Langlands.
Each sub-part's aggregator states exactly what it proves and what it does not.
-/
