import Foundations.Langlands.Cyclotomic.Field

/-!
# The degree `[ℚ(ζ_p) : ℚ] = p - 1`

Because the minimal polynomial of `ζ_p` is `Φ_p`, of degree `p - 1`, the powers
`1, ζ_p, …, ζ_p^{p-2}` form a basis of `ℚ(ζ_p)` over `ℚ`.

* **They span.** Every element is `f(ζ_p)` for some `f ∈ ℚ[x]`. Dividing `f` by `Φ_p` leaves a
  remainder of degree `< p - 1` with the same value at `ζ_p`.
* **They are independent.** A relation `Σ_{i<p-1} cᵢ ζ_p^i = 0` gives a polynomial of degree
  `< p - 1` vanishing at `ζ_p`. It is a multiple of `Φ_p`, so it is zero.

Hence `[ℚ(ζ_p) : ℚ] = p - 1`, which matches `|Gal(ℚ(ζ_p)/ℚ)| = |(ℤ/p)ˣ| = p - 1`
(`Galois.lean`).
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield Foundations.Algebra.FiniteType

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

universe u

/-- Coefficients of `Σ_{k<n} aₖ Xᵏ`: `aₘ` for `m < n`, else `0`. -/
theorem coeff_rsum_monomial {R : Type u} [CommRing R] (a : Nat → R) (n m : Nat) :
    coeff (rsum (fun k => C (a k) * (X : Polynomial R) ^ k) n) m = if m < n then a m else 0 := by
  rw [coeff_rsum]
  have hterm : ∀ k, coeff (C (a k) * (X : Polynomial R) ^ k) m = if m = k then a k else 0 := by
    intro k
    rw [X_pow_eq_Xpow, CommRing.mul_comm, coeff_Xpow_mul]
    by_cases h : m = k
    · subst h; rw [ite_true_of (Nat.le_refl m), Nat.sub_self, coeff_C, ite_true_of rfl,
        ite_true_of rfl]
    · rw [ite_false_of h]
      by_cases h' : k ≤ m
      · rw [ite_true_of h', coeff_C, ite_false_of (by omega)]
      · rw [ite_false_of h']
  rw [rsum_congr n fun k _ => hterm k]
  by_cases hm : m < n
  · rw [ite_true_of hm, rsum_single _ n hm (fun k _ hk => ite_false_of (Ne.symm hk)),
      ite_true_of rfl]
  · rw [ite_false_of hm]
    exact rsum_zero n fun k hk => ite_false_of (by omega)

section Degree

variable {p : Nat} (hp : IsPrime p)

/-- The powers `ζ_p^i`, `i < p - 1`, as vectors of `ℚ(ζ_p)` over `ℚ`. -/
noncomputable def powerBasis : Fin (p - 1) → (cycloField hp).over Qc (Qc_le_cycloField hp) :=
  fun i => ⟨rpow (zeta p) i.val, rpow_mem (zeta_mem hp) i.val⟩

/-- `1, ζ_p, …, ζ_p^{p-2}` span `ℚ(ζ_p)` over `ℚ`. -/
theorem powerBasis_spans : Spans Qc (powerBasis hp) := by
  intro x
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  have hΦ0 := cyclo_ne_zero (R := Qc) hD.1 (n := p) (by have := hp.1; omega)
  have hdegΦ := natDegree_cyclo (R := Qc) hD.1 (n := p) (by have := hp.1; omega)
  obtain ⟨f, hf⟩ := x.2
  obtain ⟨q, r, hqr, hr⟩ := div_mod (Qc.isField C.isField) f (cyclo Qc p) hΦ0
  have hrd : DegLT r (p - 1) := by
    by_cases hr0 : r = 0
    · rw [hr0]; intro n _; exact coeff_zero n
    · rcases hr with h | h
      · exact absurd h hr0
      · rw [← hdegΦ]; exact (degLT_natDegree hr0).mono (by omega)
  have hfr : aeval Qc (zeta p) f = aeval Qc (zeta p) r := by
    rw [hqr, aeval_add, aeval_mul,
      (aeval_zeta_eq_zero_iff hp _).2 ⟨1, (Ring.mul_one _).symm⟩, Ring.mul_zero, Ring.zero_add]
  refine ⟨fun i => coeff r i.val, Subtype.ext ?_⟩
  rw [KSubspace.coe_isum]
  show x.1 = isum (fun i : Fin (p - 1) => (coeff r i.val).1 * rpow (zeta p) i.val)
  rw [isum_fin_eq_rsum (p - 1) (fun k => (coeff r k).1 * rpow (zeta p) k), ← hf, hfr]
  unfold aeval
  rw [eval_eq_rsum' (zeta p) _ (N := p - 1) (fun n hn => by rw [coeff_mapPoly, hrd n hn]; rfl)]
  exact rsum_congr _ fun k _ => by rw [coeff_mapPoly]; rfl

/-- `1, ζ_p, …, ζ_p^{p-2}` are linearly independent over `ℚ`. -/
theorem powerBasis_linIndep : LinIndep Qc (powerBasis hp) := by
  intro c hc
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  have h2 := hp.1
  let a : Nat → Qc := fun k => if h : k < p - 1 then c ⟨k, h⟩ else 0
  let r : Polynomial Qc := rsum (fun k => C (a k) * X ^ k) (p - 1)
  have hcoef : ∀ m, coeff r m = if m < p - 1 then a m else 0 := coeff_rsum_monomial a (p - 1)
  -- `r(ζ_p) = Σ cᵢ ζ_p^i = 0`
  have hr0 : aeval Qc (zeta p) r = 0 := by
    have h1 := congrArg Subtype.val hc
    rw [KSubspace.coe_isum] at h1
    have h1' : isum (fun i : Fin (p - 1) => (a i.val).1 * rpow (zeta p) i.val) = 0 := by
      refine Eq.trans ?_ h1; congr 1; funext i
      show (a i.val).1 * _ = (c i).1 * _
      simp only [a, dite_eq_left i.isLt]
      rfl
    rw [isum_fin_eq_rsum (p - 1) (fun k => (a k).1 * rpow (zeta p) k)] at h1'
    rw [← h1']
    show (aevalHom Qc (zeta p)).toFun r = _
    rw [RingHom.map_rsum]
    apply rsum_congr; intro k _
    rw [(aevalHom Qc (zeta p)).map_mul, RingHom.map_pow']
    show aeval Qc (zeta p) (C (a k)) * rpow (aeval Qc (zeta p) X) k = _
    rw [aeval_C, aeval_X]
  -- so `Φ_p ∣ r`, and `deg r < p - 1` forces `r = 0`
  obtain ⟨e, he⟩ := (aeval_zeta_eq_zero_iff hp r).1 hr0
  have hrz : r = 0 := by
    apply Classical.byContradiction; intro hne
    have he0 : e ≠ 0 := by intro h; rw [h, Ring.mul_zero] at he; exact hne he
    have hdeg := natDegree_mul hD (cyclo_ne_zero hD.1 (n := p) (by omega)) he0
    rw [← he, natDegree_cyclo hD.1 (by omega)] at hdeg
    have hlt : DegLT r (p - 1) := fun m hm => by rw [hcoef, ite_false_of (by omega)]
    unfold natDegree at hdeg
    have := len_le hlt
    have : len r ≠ 0 := fun h => hne (len_eq_zero.1 h)
    omega
  intro i
  have := hcoef i.val
  rw [hrz, coeff_zero, ite_true_of i.isLt] at this
  simp only [a, dite_eq_left i.isLt] at this
  exact this.symm

/-- **The degree of the cyclotomic field.** `[ℚ(ζ_p) : ℚ] = p - 1` for a prime `p`. -/
theorem deg_cycloField : deg Qc (cycloField hp) (Qc_le_cycloField hp) = p - 1 := by
  have h := card_eq_dim (Qc.isField C.isField) (cycloField_finite hp)
    (b := powerBasis hp) ⟨powerBasis_linIndep hp, powerBasis_spans hp⟩
  rw [card_fin] at h
  exact h.symm

end Degree

end Foundations.Langlands
