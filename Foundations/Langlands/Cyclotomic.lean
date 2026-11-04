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
import Foundations.Langlands.Cyclotomic.MonicPoly
import Foundations.Langlands.Cyclotomic.CyclotomicN
import Foundations.Langlands.Cyclotomic.Dedekind
import Foundations.Langlands.Cyclotomic.IrreducibleN
import Foundations.Langlands.Cyclotomic.GaloisN
import Foundations.Langlands.Cyclotomic.FrobeniusN
import Foundations.Langlands.Cyclotomic.DictionaryN
import Foundations.Langlands.Cyclotomic.EulerFactors
import Foundations.Langlands.Cyclotomic.QuadraticSplitting

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
  (`deg_cycloFieldPP`).
* **General `n` (Kronecker 1854, Dedekind 1857).** For every `n ≥ 1`,
  `Φ_n = ∏_{a < n, gcd(a,n) = 1} (x - ζ_n^a)` is defined over `ℂ` (`cycloC`), has degree
  `φ(n)` (`natDegree_cycloC`), and is the image of a monic integer polynomial `cycloZ n` of
  degree `φ(n)` (`map_cycloZ`, `natDegree_cycloZ`). It is irreducible over `ℚ`
  (`cycloQ_irreducible`) and is the minimal polynomial of `ζ_n` (`aeval_zetaN_eq_zero_iff`);
  for prime `p` it is the earlier `Φ_p` (`cycloQ_prime`). The proof is Dedekind's: for a prime
  `p ∤ n`, `ζ ↦ ζ^p` preserves the minimal polynomial (`dedekind_step`), by Gauss's lemma for
  monic factors (`int_of_monic_factor`) and the separability of `xⁿ - 1` modulo `p`
  (`isUnit_of_sq_dvd_X_pow_sub_one`). Consequently `Aut(ℚ(ζ_n)/ℚ) ≅ (ℤ/n)ˣ`
  (`cycloGaloisIsoN`), `[ℚ(ζ_n) : ℚ] = φ(n)` (`deg_cycloFieldN`), and for every prime `q ∤ n`
  the automorphism `σ_q` reduces to the `q`-th power map `ℤ[ζ_n] → 𝔽_q[x]/(Φ̄_n)`
  (`reduceN_galAut`).
* **Kummer** (1840s) made `ℤ[ζ_p]` the object of an arithmetic of ideal numbers. We use it only
  through its reduction map to `𝔽_q[x]/(Φ_p)`. We do not prove that this ring is
  `ℤ[ζ_p]/(q)`, nor anything about ideals of `ℤ[ζ_p]`.
* **Kronecker–Weber** (Kronecker 1853; Weber 1886; Hilbert 1896): every finite abelian
  extension of `ℚ` lies in a cyclotomic field. *Stated here in prose only; not formalised.*
* **Artin reciprocity** (1927): for an abelian extension, Frobenius elements depend only on the
  prime modulo the conductor, and characters of the Galois group correspond to characters of
  idèle class groups. In the cyclotomic case, one ingredient is the (proved) fact that `σ_q` depends
  only on `q mod n` (`frobN_congr`); Artin reciprocity itself is not formalised. For prime `p`, a Dirichlet character `χ` mod `p`, transported to `Gal(ℚ(ζ_p)/ℚ)`,
  takes the value `χ(q)` at the Frobenius element `σ_q` (`galChar_frobenius`).
* **The `GL(1)` dictionary for every `n ≥ 1`.** The characters of a commutative group form a
  commutative group (`characterCommGroup`), `Gal(ℚ(ζ_n)/ℚ)` is a finite abelian group of order
  `φ(n)` (`card_cycloGaloisN`), and transport along `cycloGaloisIsoN` is a group isomorphism
  `χ ↦ ρ_χ` from Dirichlet characters mod `n` to characters of `Gal(ℚ(ζ_n)/ℚ)`
  (`dirichletGaloisN`) with `ρ_χ(σ_q) = χ(q)` for every prime `q ∤ n`
  (`dirichletGaloisN_frobenius`). With Dirichlet's theorem on primes in progressions, every
  Galois element is `σ_q` for infinitely many primes `q` (`exists_frobenius_eq`, a qualitative
  cyclotomic Chebotarev), so `ρ_χ` is the unique Galois character with these Frobenius values
  (`dirichletGaloisN_unique`).
* **Euler factors.** Consequently the local factors `(1 - χ(q) q^{-s})⁻¹` of the Dirichlet
  `L`-function and `(1 - ρ_χ(Frob_q) q^{-s})⁻¹` of the Artin `L`-function agree at every prime
  `q ∤ n` (`localFactor_match`), and the finite partial Euler products agree
  (`dirichletEuler_eq_artinEuler`). These are identities of finite products in `ℂ`; nothing is
  claimed about analytic `L`-functions.
* **Splitting in `ℚ(√p*)`, via Frobenius.** For distinct odd primes `p, q`, the Frobenius `σ_q`
  fixes `ℚ(√p*)` iff `q` is a square mod `p` iff `p*` is a square mod `q`
  (`frobenius_sqrtField_tfae`, `frobenius_fixes_sqrtField_iff_pstar_sq`), the second equivalence
  being quadratic reciprocity. This is the Galois-side form of "`q` splits in `ℚ(√p*)`"; prime
  ideals are not formalised, so splitting itself is not stated.
* **Langlands for `GL(1)`** is this correspondence between Galois characters and Dirichlet
  (more generally Hecke) characters. Langlands' conjectures (1967) extend it to `GL(n)`. Beyond
  the cyclotomic fields treated here (`ℚ(ζ_n)` for all `n ≥ 1`: irreducibility, Galois group,
  degree, Frobenius congruence, the character dictionary; Gauss sums only for prime `p`), nothing
  of class field theory is claimed: in particular Kronecker–Weber, the identification of Hecke
  characters of `ℚ` with Dirichlet characters, and the analytic theory of Artin `L`-functions are
  not formalised.

Files, in order: `Basic` (sums, binomial theorem, Legendre-symbol facts), `GaussSum`,
`CyclotomicPoly`, `Reciprocity`, `Eisenstein`, `Irreducible`, `Field`, `Galois`, `Frobenius`,
`Degree`, `Quadratic`, `QuadraticFixed`, `PrimePowerIrreducible`, `PrimePowerGalois`,
`PrimePowerDegree`, `MonicPoly`, `CyclotomicN`, `Dedekind`, `IrreducibleN`, `GaloisN`,
`FrobeniusN`, `DictionaryN`, `EulerFactors`, `QuadraticSplitting`.
-/
