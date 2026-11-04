import Foundations.Langlands.Cyclotomic.Basic
import Foundations.Langlands.Cyclotomic.GaussSum
import Foundations.Langlands.Cyclotomic.CyclotomicPoly
import Foundations.Langlands.Cyclotomic.Reciprocity
import Foundations.Langlands.Cyclotomic.Eisenstein
import Foundations.Langlands.Cyclotomic.Irreducible
import Foundations.Langlands.Cyclotomic.Field
import Foundations.Langlands.Cyclotomic.Galois

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
  group is abelian.
* **Gauss, 1808.** The sixth proof of quadratic reciprocity: in the characteristic-`q` ring
  `𝔽_q[x]/(Φ_p)`, Frobenius gives `g^q = (q/p) g`, while `g² = p*` gives
  `g^q = (p*)^((q-1)/2) g`. Hence `(q/p) ≡ (p*)^((q-1)/2) (mod q)`
  (`legendre_eq_pstar_pow_mod`) and the law of quadratic reciprocity
  (`quadratic_reciprocity_gauss`). In ℂ the same phenomenon reads `σ_a(√p*) = (a/p)√p*`, so the
  Frobenius automorphism `σ_q` fixes `√p*` exactly when `p*` is a square modulo `q`
  (`frobenius_fixes_sqrt_iff`).
* **Kummer** (1840s) made `ℤ[ζ_p]` the object of an arithmetic of ideal numbers. We use only its
  field of fractions and, modulo `q`, the ring `𝔽_q[x]/(Φ_p)`.
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
  the cyclotomic case for prime `p`, nothing of class field theory is claimed.

Files, in order: `Basic` (sums, binomial theorem, Legendre-symbol facts), `GaussSum`,
`CyclotomicPoly`, `Reciprocity`, `Eisenstein`, `Irreducible`, `Field`, `Galois`.
-/
