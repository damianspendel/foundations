import Foundations.Langlands.Cyclotomic.Basic

/-!
# The cyclotomic polynomial `Φ_p`

For a prime `p` the `p`-th roots of unity other than `1` are the roots of

  `Φ_p(x) = 1 + x + x² + ⋯ + x^{p-1} = (x^p - 1)/(x - 1)`,

the **cyclotomic polynomial** ("circle-dividing": its roots divide the unit circle into `p`
equal arcs). Gauss proved in 1801 (*Disquisitiones*, art. 341) that `Φ_p` is irreducible over
`ℚ`; Eisenstein's criterion (1850), applied to `Φ_p(x + 1)`, gives the short proof
formalised in `Irreducible.lean`. Kronecker (1854) and Dedekind (1857) extended irreducibility
to all cyclotomic polynomials `Φ_n`, which is treated in `CyclotomicN` and `IrreducibleN`.

This file defines `Φ_p` over any commutative ring, as the coefficient list `[1, 1, …, 1]`, and
records its basic properties: it is the sum `Σ_{j<p} Xʲ`; it satisfies
`(X - 1) Φ_p = X^p - 1`; it has degree `p - 1` with leading coefficient `1`; it is compatible
with ring homomorphisms; and over a domain it is not a unit when `p ≥ 2`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial

universe u

section Cyclo

variable {R : Type u} [CommRing R]

/-- **The cyclotomic polynomial** `Φ_n = 1 + X + ⋯ + X^{n-1}`, the coefficient list
`[1, 1, …, 1]` of length `n`. (For prime `n = p` this is the `p`-th cyclotomic polynomial.) -/
def cyclo (R : Type u) [CommRing R] (n : Nat) : Polynomial R := mk (List.replicate n 1)

/-- Prepending a coefficient: `a + a₁ X + a₂ X² + ⋯ = a + X · (a₁ + a₂ X + ⋯)`. -/
theorem mk_cons (a : R) (l : List R) : mk (a :: l) = C a + X * mk l := by
  apply ext; intro n
  rw [coeff_add, coeff_C]
  cases n with
  | zero => rw [coeff_X_mul_zero]; simp; exact (Ring.add_zero a).symm
  | succ k => rw [coeff_X_mul_succ]; simp; exact (Ring.zero_add _).symm

/-- **The geometric sum identity** `(x - 1)(1 + x + ⋯ + x^{n-1}) = xⁿ - 1` in any commutative
ring. -/
theorem geom_sum_mul (x : R) : ∀ n, (x + -1) * rsum (fun j => x ^ j) n = x ^ n + -1
  | 0 => by show (x + -1) * 0 = 1 + -1; grind
  | n + 1 => by
    show (x + -1) * (rsum (fun j => x ^ j) n + x ^ n) = x ^ n * x + -1
    have := geom_sum_mul x n
    grind

/-- `Φ_n` is the sum `Σ_{j<n} Xʲ` in the polynomial ring. -/
theorem cyclo_eq_rsum : ∀ n, cyclo R n = rsum (fun j => (X : Polynomial R) ^ j) n
  | 0 => rfl
  | n + 1 => by
    show mk (1 :: List.replicate n 1) = _
    rw [mk_cons, rsum_succ', C_one]
    show 1 + X * cyclo R n = _
    rw [cyclo_eq_rsum n, mul_rsum]
    show _ = (1 : Polynomial R) + _
    congr 1
    exact rsum_congr n fun k _ => CommRing.mul_comm _ _

/-- `(X - 1) Φ_n = Xⁿ - 1`. -/
theorem X_sub_one_mul_cyclo (n : Nat) : ((X : Polynomial R) + -1) * cyclo R n = X ^ n + -1 := by
  rw [cyclo_eq_rsum]; exact geom_sum_mul X n

/-- **Evaluating `Φ_n`**: `Φ_n(x) = 1 + x + ⋯ + x^{n-1}`. -/
theorem eval_cyclo (x : R) (n : Nat) : eval x (cyclo R n) = rsum (fun j => x ^ j) n := by
  rw [cyclo_eq_rsum]
  show (evalHom x).toFun _ = _
  rw [RingHom.map_rsum]
  apply rsum_congr; intro j _
  rw [RingHom.map_pow' (evalHom x)]
  show eval x X ^ j = _
  rw [eval_X]

/-- The coefficients of `Φ_n`: `1` below `n`, `0` from `n` on. -/
theorem coeff_cyclo (n k : Nat) : coeff (cyclo R n) k = if k < n then 1 else 0 := by
  show PolyList.coeff _ _ = _
  by_cases h : k < n
  · rw [ite_true_of h, coeff_geom_list n k h]
  · rw [ite_false_of h]
    apply PolyList.coeff_of_length_le
    rw [List.length_replicate]; omega

/-- `Φ_n` has degree `< n`. -/
theorem degLT_cyclo (n : Nat) : DegLT (cyclo R n) n := fun k hk => by
  rw [coeff_cyclo, ite_false_of (by omega)]

/-- `Φ_n` has degree exactly `n - 1` (for `n ≥ 1`, in a non-zero ring). -/
theorem natDegree_cyclo (h01 : (0 : R) ≠ 1) {n : Nat} (hn : 1 ≤ n) :
    natDegree (cyclo R n) = n - 1 := by
  apply natDegree_eq_of
  · exact (degLT_cyclo n).mono (by omega)
  · rw [coeff_cyclo, ite_true_of (by omega)]; exact fun h => h01 h.symm

/-- `Φ_n ≠ 0` for `n ≥ 1` in a non-zero ring. -/
theorem cyclo_ne_zero (h01 : (0 : R) ≠ 1) {n : Nat} (hn : 1 ≤ n) : cyclo R n ≠ 0 := by
  intro h
  have := coeff_cyclo (R := R) n 0
  rw [h, coeff_zero, ite_true_of (by omega)] at this
  exact h01 this

/-- `Φ_n` is compatible with ring homomorphisms: mapping its coefficients gives `Φ_n`. -/
theorem mapPoly_cyclo {S : Type u} [CommRing S] (φ : RingHom R S) (n : Nat) :
    mapPoly φ (cyclo R n) = cyclo S n := by
  apply ext; intro k
  rw [coeff_mapPoly, coeff_cyclo, coeff_cyclo]
  by_cases h : k < n
  · rw [ite_true_of h, ite_true_of h]; exact φ.map_one
  · rw [ite_false_of h, ite_false_of h]; exact φ.map_zero

/-- Over a domain, a polynomial of positive degree is not a unit. -/
theorem not_isUnit_of_natDegree_pos (hD : IsDomain R) {f : Polynomial R} (hf : f ≠ 0)
    (hdeg : 0 < natDegree f) : ¬ IsUnit f := by
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h; rw [h, Ring.mul_zero] at hg
    exact hD.1 (congrArg (fun r => coeff r 0) hg)
  have := natDegree_mul hD hf hg0
  rw [hg] at this
  have h1 : natDegree (1 : Polynomial R) = 0 := by
    apply natDegree_eq_of
    · intro n hn; show PolyList.coeff [1] n = 0
      cases n with
      | zero => omega
      | succ n => rfl
    · show (1 : R) ≠ 0; exact fun h => hD.1 h.symm
  omega

/-- Over a domain, `Φ_n` is not a unit for `n ≥ 2`. -/
theorem cyclo_not_isUnit (hD : IsDomain R) {n : Nat} (hn : 2 ≤ n) : ¬ IsUnit (cyclo R n) :=
  not_isUnit_of_natDegree_pos hD (cyclo_ne_zero hD.1 (by omega))
    (by rw [natDegree_cyclo hD.1 (by omega)]; omega)

end Cyclo

end Foundations.Langlands
