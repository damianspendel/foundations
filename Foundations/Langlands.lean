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
  to exactly one `|·|ₚ`), the `p`-adic integers `ℤₚ` (complete, compact), **Hensel's lemma**, `ℚₚ` as a complete
  field with `ℚ` dense, the Hilbert symbol at every place, and **Hilbert's product formula**
  for all nonzero rationals (`hilbert_product_formula`).

* `Rep` — representations of finite groups, the language Langlands is written in: **Maschke's
  theorem**, **Schur's lemma** (with scalars over ℂ, via the fundamental theorem of algebra),
  characters and their **orthogonality**, multiplicities, and the bridge saying that for abelian
  groups the irreducible characters are exactly the Dirichlet-style characters of `DualGroup`.

* `Cyclotomic` — reciprocity as Galois theory, the prototype of GL(1) reciprocity:
  irreducibility of `Φ_p` (Eisenstein), `Gal(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)ˣ` (`cycloGaloisIso`), Gauss sums
  with `g² = p*`, **quadratic reciprocity re-proved by Frobenius** (`quadratic_reciprocity_gauss`,
  Gauss's sixth proof), and Dirichlet characters read as characters of the Galois group, with
  `χ(σ_q) = χ(q)` (`galChar_frobenius`), where `σ_q` is shown to be a Frobenius: it reduces
  to the `q`-th power map on `ℤ[ζ_p]` mod `q` (`reduce_galAut`). Also the degree `p − 1`, the
  quadratic subfield `ℚ(√p*)` as the fixed field of the squares, and, for **every** `n`,
  irreducibility of `Φ_n` (Dedekind's argument), `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/n)ˣ` (`cycloGaloisIsoN`),
  degree `φ(n)`, and the Frobenius congruence (`reduceN_galAut`); the **GL(1) dictionary**
  `dirichletGaloisN` between Dirichlet characters mod `n` and characters of `Gal(ℚ(ζ_n)/ℚ)`,
  matching at Frobenius and in finite unramified Euler products (`dirichletEuler_eq_artinEuler`).

Not formalised: Hasse's principle, Kronecker–Weber, Artin reciprocity in general,
modular forms, automorphic representations — that is, everything that makes Langlands Langlands.
Each sub-part's aggregator states exactly what it proves and what it does not.
-/
