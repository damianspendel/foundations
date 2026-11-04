import Foundations.Langlands.Cyclotomic.Basic
import Foundations.Langlands.Cyclotomic.GaussSum
import Foundations.Langlands.Cyclotomic.CyclotomicPoly
import Foundations.Langlands.Cyclotomic.Reciprocity
import Foundations.Langlands.Cyclotomic.Eisenstein
import Foundations.Langlands.Cyclotomic.Irreducible
import Foundations.Langlands.Cyclotomic.Field
import Foundations.Langlands.Cyclotomic.Galois
import Foundations.Langlands.Cyclotomic.Frobenius
import Foundations.Langlands.Cyclotomic.Degree
import Foundations.Langlands.Cyclotomic.Quadratic
import Foundations.Langlands.Cyclotomic.QuadraticFixed
import Foundations.Langlands.Cyclotomic.PrimePowerIrreducible
import Foundations.Langlands.Cyclotomic.PrimePowerGalois
import Foundations.Langlands.Cyclotomic.PrimePowerDegree

/-!
# Part XV, chapter 3: reciprocity as Galois theory (the cyclotomic case)

The Langlands programme predicts a correspondence between Galois representations and
automorphic forms. For `GL(1)`, i.e. one-dimensional representations, the prediction is class
field theory, and over `ℚ` its prototype is the cyclotomic field `ℚ(ζ_p)`. This chapter
formalises that prototype.

* **Gauss, 1801.** In the *Disquisitiones Arithmeticae* Gauss proved that `Φ_p = 1 + x + ⋯ +
  x^{p-1}` is irreducible over `ℚ`, studied the periods of `p`-th roots of unity, and showed
  that the quadratic Gauss sum `g = Σ (a/p) ζ^a` satisfies `g² = ±p`. Here: `Φ_p` is
  irreducible via Eisenstein's criterion applied to `Φ_p(x + 1)` (`cyclo_irreducible`), and
  `g² = p* = (-1)^((p-1)/2) p` holds in any commutative ring containing a suitable `p`-th root
  of unity (`gaussSum_sq`), in particular in `ℂ` (`gaussSum_sq_complex`). So `√p* ∈ ℚ(ζ_p)`
  (`sqrt_pstar_mem`).
* **Galois.** `Aut(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)ˣ`, with `a` acting by `ζ ↦ ζ^a` (`cycloGaloisIso`). The
  group is abelian, and `[ℚ(ζ_p) : ℚ] = p - 1` (`deg_cycloField`): the powers
  `1, ζ_p, …, ζ_p^{p-2}` form a basis.
* **Frobenius.** `σ_q` is defined as `ζ ↦ ζ^q`. On `ℤ[ζ_p] ⊆ ℚ(ζ_p)` (`intZeta`) there is a
  reduction homomorphism to `𝔽_q[x]/(Φ_p)` sending `ζ_p` to `x` (`reduce`), and
  `σ_q(α) ≡ α^q` for every `α ∈ ℤ[ζ_p]` (`reduce_galAut`). So `σ_q` is a genuine Frobenius
  element at `q`. The Gauss sum reduces to the Gauss sum modulo `q` (`reduce_gaussSum`).
* **The quadratic subfield.** `σ_a` fixes `ℚ(√p*)` exactly when `a` is a square mod `p`
  (`galAut_fixes_sqrtField_iff`), `√p*` is irrational (`gaussSum_not_rat`),
  `[ℚ(√p*) : ℚ] = 2` (`deg_sqrtField`), and the fixed field of the squares is `ℚ(√p*)`
  (`fixedField_squares`).
* **Gauss, 1808.** The sixth proof of quadratic reciprocity: in the characteristic-`q` ring
  `𝔽_q[x]/(Φ_p)`, Frobenius gives `g^q = (q/p) g`, while `g² = p*` gives
  `g^q = (p*)^((q-1)/2) g`. Hence `(q/p) ≡ (p*)^((q-1)/2) (mod q)`
  (`legendre_eq_pstar_pow_mod`) and the law of quadratic reciprocity
  (`quadratic_reciprocity_gauss`). In ℂ the same phenomenon reads `σ_a(√p*) = (a/p)√p*`, so the
  Frobenius automorphism `σ_q` fixes `√p*` exactly when `p*` is a square modulo `q`
  (`frobenius_fixes_sqrt_iff`).
* **Prime powers.** For `n = p^{k+1}`, `Φ_n = Σ_{j<p} x^{j p^k}` is irreducible over `ℚ`
  (`cycloPP_irreducible`, Eisenstein at `p` after `x ↦ x + 1`, using `Φ_n(x+1) ≡ x^{φ(n)}`
  mod `p`), `Aut(ℚ(ζ_n)/ℚ) ≅ (ℤ/n)ˣ` (`cycloGaloisIsoPP`), and `[ℚ(ζ_n) : ℚ] = (p - 1)p^k`
  (`deg_cycloFieldPP`). General `n` (irreducibility of every `Φ_n`) is not done.
* **Kummer** (1840s) made `ℤ[ζ_p]` the object of an arithmetic of ideal numbers. We use it only
  through its reduction map to `𝔽_q[x]/(Φ_p)`. We do not prove that this ring is
  `ℤ[ζ_p]/(q)`, nor anything about ideals of `ℤ[ζ_p]`.
* **Kronecker–Weber** (Kronecker 1853; Weber 1886; Hilbert 1896): every finite abelian
  extension of `ℚ` lies in a cyclotomic field. *Stated here in prose only; not formalised.*
* **Artin reciprocity** (1927): for an abelian extension, Frobenius elements depend only on the
  prime modulo the conductor, and characters of the Galois group correspond to characters of
  idèle class groups. In the cyclotomic case this is the fact that `σ_q` depends only on
  `q mod p`. The dictionary statement proved here is that a Dirichlet character `χ` mod `p`,
  transported to `Gal(ℚ(ζ_p)/ℚ)`, takes the value `χ(q)` at the Frobenius element `σ_q`
  (`galChar_frobenius`).
* **Langlands for `GL(1)`** is this correspondence between Galois characters and Dirichlet
  (more generally Hecke) characters. Langlands' conjectures (1967) extend it to `GL(n)`. Beyond
  the cyclotomic cases treated here (prime `p`, and prime powers for the Galois group), nothing
  of class field theory is claimed.

Files, in order: `Basic` (sums, binomial theorem, Legendre-symbol facts), `GaussSum`,
`CyclotomicPoly`, `Reciprocity`, `Eisenstein`, `Irreducible`, `Field`, `Galois`, `Frobenius`,
`Degree`, `Quadratic`, `QuadraticFixed`, `PrimePowerIrreducible`, `PrimePowerGalois`,
`PrimePowerDegree`.
-/
