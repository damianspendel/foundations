import Foundations.Langlands.Padic.Hilbert
import Foundations.Langlands.Padic.CompactMetric
import Foundations.Algebra.QuadraticResidues

/-!
# `(u, p)ₚ` is the Legendre symbol

For an odd prime `p` and `p`-adic units `u`, `v`, the conic `z² = u x² + p v y²` has a
non-trivial point over ℚₚ exactly when `u` is a square modulo `p`
(`Qp.hilbertSolvable_unit_pv_iff`). For `v = 1` and a natural number `u` prime to `p` this says
**`(u, p)ₚ = (u/p)`** (`Qp.hilbert_p`), the Legendre symbol of `Algebra.QuadraticResidues`.

* If `u ≡ a² (mod p)`, then `u` is a square in ℤₚ (`Zp.exists_sq_of_modPow`), and `(1, 0, √u)`
  is a point.
* Conversely, take a point `(x, y, z)`. If `x = 0` then `z² = p y²`, impossible for `y ≠ 0`
  since `v(z²) = 2 v(z)` is even and `v(p y²) = 1 + 2 v(y)` is odd (similarly with `p v`). If
  `x ≠ 0`, put `w = z/x`, `t = y/x`, so `w² = u + p v t²`. When `v(t) ≥ 0`, `w` is a `p`-adic
  integer with `w² ≡ u (mod p)`. When `v(t) < 0`, the ultrametric inequality, used in both
  directions on `w² = u + p v t²`, forces `v(w²) = v(p v t²)`, again an even number equal to an
  odd one.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-! ## Valuations of special elements -/

/-- A unit of ℤₚ has valuation `0` in ℚₚ. -/
theorem val_ofZp_unit {u : Zp p} (hu : Zp.IsPUnit u) : val (ofZp u) = 0 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Zp.ModPow.refl 1 0)
  have h := Zp.val_pow_mul hP.prime 0 hu
  rw [Semiring.pow_zero, Semiring.one_mul] at h
  unfold ofZp; rw [val_mk hu0, h]; rfl

/-- `p ≠ 0` in ℤₚ. -/
theorem zp_p_ne_zero : (p : Zp p) ≠ 0 := by
  have := pow_ne_zero (p := p) 1
  rwa [show (p : Zp p) ^ 1 = p by grind] at this

/-- `v(p) = 1` in ℚₚ. -/
theorem val_p : val (ofZp (p : Zp p)) = 1 := by
  have hne : ((p : Int) : Zp p) ≠ 0 := zp_p_ne_zero
  have h := zp_val_intCast (p := p) (n := (p : Int)) (by have := hP.prime.1; omega)
  rw [vZ_self hP.prime] at h
  unfold ofZp; rw [val_mk zp_p_ne_zero]
  rw [show Zp.val hP.prime (p : Zp p) = Zp.val hP.prime ((p : Int) : Zp p) from rfl, h]; rfl

/-- `v(q²) = 2 v(q)`. -/
theorem val_sq {q : Qp p} (hq : q ≠ 0) : val (q * q) = 2 * val q := by
  rw [val_mul hq hq]; omega

/-- `v(−q) = v(q)`. -/
theorem val_neg {q : Qp p} (hq : q ≠ 0) : val (-q) = val q := by
  have h1 : (-1 : Qp p) ≠ 0 := fun h => zero_ne_one (p := p) (by grind)
  rw [show -q = -1 * q by grind, val_mul h1 hq, val_neg_one, Int.zero_add]

/-- A product of non-zero elements of ℚₚ is non-zero. -/
theorem mul_ne_zero' {q r : Qp p} (hq : q ≠ 0) (hr : r ≠ 0) : q * r ≠ 0 := fun h => by
  rcases Field.of_mul_eq_zero h with h | h <;> contradiction

/-- Non-zero `p`-adic integers have valuation `≥ 0`. -/
theorem val_ofZp_nonneg {x : Zp p} (hx : x ≠ 0) : 0 ≤ val (ofZp x) := by
  unfold ofZp; rw [val_mk hx]; omega

/-- Elements of non-negative valuation are `p`-adic integers. -/
theorem exists_ofZp_of_val_nonneg {q : Qp p} (hq : q ≠ 0) (h : 0 ≤ val q) :
    ∃ x, q = ofZp x := by
  apply exists_ofZp_of_abs_le_one
  rw [abs_of_ne hq, show (1 : Q) = (p : Q) ^ (-(0 : Int)) from rfl, zpow_neg_le_iff two_le_p]
  exact h

/-! ## The computation -/

/-- `p v ≠ 0` in ℚₚ for a unit `v`. -/
theorem ofZp_pv_ne_zero {v : Zp p} (hv : Zp.IsPUnit v) : ofZp ((p : Zp p) * v) ≠ 0 := by
  have hv0 : ofZp v ≠ 0 := fun h0 => hv ((ofZp_injective (h0.trans rfl)) ▸ Zp.ModPow.refl 1 0)
  have hP0 : ofZp (p : Zp p) ≠ 0 := fun h0 => zp_p_ne_zero (ofZp_injective (h0.trans rfl))
  rw [ofZp_mul]; exact mul_ne_zero' hP0 hv0

/-- `v(p v) = 1` for a unit `v`. -/
theorem val_pv {v : Zp p} (hv : Zp.IsPUnit v) : val (ofZp ((p : Zp p) * v)) = 1 := by
  have hv0 : ofZp v ≠ 0 := fun h0 => hv ((ofZp_injective (h0.trans rfl)) ▸ Zp.ModPow.refl 1 0)
  have hP0 : ofZp (p : Zp p) ≠ 0 := fun h0 => zp_p_ne_zero (ofZp_injective (h0.trans rfl))
  rw [ofZp_mul, val_mul hP0 hv0, val_p, val_ofZp_unit hv]; rfl

omit hP in
/-- If `W² = u + p S` in ℤₚ, then `u` is a square modulo `p`. -/
theorem sq_mod_of_eq {u W S : Zp p} (h : W * W = u + (p : Zp p) * S) :
    ∃ a : Int, Zp.ModPow 1 u ((a * a : Int) : Zp p) := by
  refine ⟨(Zp.rep W).seq 1, ?_⟩
  have hp0 : Zp.ModPow 1 (p : Zp p) 0 := Zp.modPow_intCast_zero (Int.dvd_refl _)
  have h1 : Zp.ModPow 1 (W * W - u) 0 := by
    rw [h, show u + (p : Zp p) * S - u = S * (p : Zp p) by grind]
    exact hp0.zero_mul _
  have h2 := (Zp.modPow_iff_sub.2 h1).symm.trans (Zp.modPow_rep 1 W).sq
  rwa [← Ring.intCast_mul] at h2

/-- The case `x ≠ 0`: from `w² = u + p v t²` in ℚₚ (`u`, `v` units), `u` is a square
modulo `p`. -/
theorem sq_mod_of_w {u v : Zp p} (hu : Zp.IsPUnit u) (hv : Zp.IsPUnit v) {w t : Qp p}
    (h : w * w = ofZp u + ofZp ((p : Zp p) * v) * (t * t)) :
    ∃ a : Int, Zp.ModPow 1 u ((a * a : Int) : Zp p) := by
  have hU0 : ofZp u ≠ 0 := fun h0 => hu ((ofZp_injective (h0.trans rfl)) ▸ Zp.ModPow.refl 1 0)
  have hP0 := ofZp_pv_ne_zero hv
  have hvU := val_ofZp_unit hu
  have hvP := val_pv hv
  -- is `t` integral?
  by_cases ht : t = 0 ∨ 0 ≤ val t
  · obtain ⟨T, rfl⟩ : ∃ T, t = ofZp T := by
      rcases ht with ht | ht
      · exact ⟨0, ht⟩
      · by_cases ht0 : t = 0
        · exact ⟨0, ht0⟩
        · exact exists_ofZp_of_val_nonneg ht0 ht
    have hw' : w * w = ofZp (u + ((p : Zp p) * v) * (T * T)) := by
      rw [h, ofZp_add, ofZp_mul ((p : Zp p) * v) (T * T), ofZp_mul T T]
    obtain ⟨W, rfl⟩ : ∃ W, w = ofZp W := by
      by_cases hw0 : w = 0
      · exact ⟨0, hw0⟩
      · apply exists_ofZp_of_val_nonneg hw0
        have hs : u + ((p : Zp p) * v) * (T * T) ≠ 0 := fun hs => by
          rw [hs] at hw'; exact mul_ne_zero' hw0 hw0 (hw'.trans rfl)
        have := val_ofZp_nonneg hs
        rw [← hw', val_sq hw0] at this; omega
    exact sq_mod_of_eq (S := v * (T * T)) (ofZp_injective (by
      rw [ofZp_mul, hw', show u + (p : Zp p) * v * (T * T) = u + (p : Zp p) * (v * (T * T)) by grind]))
  · -- `v(t) < 0`: parity contradiction
    exfalso
    have ht0 : t ≠ 0 := fun h0 => ht (Or.inl h0)
    have hvt : val t < 0 := by
      apply Classical.byContradiction; intro hn; exact ht (Or.inr (by omega))
    have hpt : ofZp ((p : Zp p) * v) * (t * t) ≠ 0 := mul_ne_zero' hP0 (mul_ne_zero' ht0 ht0)
    have hvpt : val (ofZp ((p : Zp p) * v) * (t * t)) = 1 + 2 * val t := by
      rw [val_mul hP0 (mul_ne_zero' ht0 ht0), val_sq ht0, hvP]
    by_cases hw0 : w = 0
    · -- `u = −p t²`
      have e : ofZp u = -(ofZp ((p : Zp p) * v) * (t * t)) := by
        rw [hw0] at h; grind
      have := val_neg hpt
      rw [← e, hvU, hvpt] at this; omega
    · have hww := mul_ne_zero' hw0 hw0
      have h1 := min_le_val_add hU0 hpt (h ▸ hww)
      rw [← h, val_sq hw0, hvU, hvpt] at h1
      have hnU : -ofZp u ≠ 0 := fun h0 => hU0 (by grind)
      have e2 : w * w + -ofZp u = ofZp ((p : Zp p) * v) * (t * t) := by rw [h]; grind
      have h2 := min_le_val_add hww hnU (e2 ▸ hpt)
      rw [e2, val_sq hw0, val_neg hU0, hvU, hvpt] at h2
      omega

/-- **The conic `z² = u x² + p v y²`.** For an odd prime `p` and `p`-adic units `u`, `v`, it
has a non-trivial point over ℚₚ iff `u` is a square modulo `p`. -/
theorem hilbertSolvable_unit_pv_iff (hodd : p % 2 = 1) {u v : Zp p} (hu : Zp.IsPUnit u)
    (hv : Zp.IsPUnit v) :
    HilbertSolvable (ofZp u) (ofZp ((p : Zp p) * v)) ↔
      ∃ a : Int, Zp.ModPow 1 u ((a * a : Int) : Zp p) := by
  have hP0 := ofZp_pv_ne_zero hv
  have hvP := val_pv hv
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    by_cases hx : x = 0
    · exfalso
      subst hx
      have h' : z * z = ofZp ((p : Zp p) * v) * (y * y) := by rw [h]; grind
      by_cases hy : y = 0
      · subst hy
        have hz : z * z = 0 := by rw [h']; grind
        have hz0 : z = 0 := by rcases Field.of_mul_eq_zero hz with hz | hz <;> exact hz
        rcases hne with hne | hne | hne <;> first | exact hne rfl | exact hne hz0
      · have hpy := mul_ne_zero' hP0 (mul_ne_zero' hy hy)
        have hz : z ≠ 0 := fun hz => by
          subst hz; exact hpy (by rw [← h']; grind)
        have := congrArg val h'
        rw [val_sq hz, val_mul hP0 (mul_ne_zero' hy hy), val_sq hy, hvP] at this
        omega
    · have hxi := Field.mul_inv_cancel hx
      apply sq_mod_of_w hu hv (w := z * x⁻¹) (t := y * x⁻¹)
      have : z * x⁻¹ * (z * x⁻¹) = (z * z) * (x⁻¹ * x⁻¹) := by grind
      rw [this, h]
      grind
  · rintro ⟨a, ha⟩
    have hpa : ¬ (p : Int) ∣ a := fun hpa => hu (ha.trans (by
      rw [Ring.intCast_mul]
      exact (Zp.modPow_intCast_zero hpa).zero_mul _))
    obtain ⟨X, hX⟩ := Zp.exists_sq_of_modPow hP.prime hodd hpa ha
    refine ⟨1, 0, ofZp X, Or.inl one_ne_zero', ?_⟩
    rw [← ofZp_mul, hX]; grind

/-- For natural numbers, "`u` is a square mod `p`" in the sense of `Algebra.IsQR` agrees with
the congruence `u ≡ a² (mod p)` in ℤₚ. -/
theorem isQR_iff {u : Nat} :
    Foundations.Algebra.IsQR u p ↔ ∃ a : Int, Zp.ModPow 1 ((u : Int) : Zp p) ((a * a : Int) : Zp p) := by
  have hp0 : (0 : Int) < p := by have := hP.prime.1; omega
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, Zp.modPow_intCast.2 ?_⟩
    rw [Int.pow_one]
    have hx' : ((x * x : Nat) : Int) % p = (u : Int) % p := by
      rw [← Int.natCast_emod, ← Int.natCast_emod, hx]
    have := Int.emod_eq_emod_iff_emod_sub_eq_zero.1 hx'.symm
    rw [Int.dvd_iff_emod_eq_zero]
    rw [show ((x * x : Nat) : Int) = (x : Int) * x by omega] at this
    exact this
  · rintro ⟨a, ha⟩
    have ha := Zp.modPow_intCast.1 ha
    rw [Int.pow_one] at ha
    refine ⟨a.natAbs, ?_⟩
    have h := Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.dvd_iff_emod_eq_zero.1 ha)
    rw [← Int.natAbs_mul_self] at h
    rw [← Int.natCast_emod, ← Int.natCast_emod] at h
    exact (Int.ofNat_inj.1 h).symm

/-- **`(u, p)ₚ = (u/p)`.** For an odd prime `p` and a natural number `u` prime to `p`, the
Hilbert symbol of `u` and `p` in ℚₚ is the Legendre symbol of `u` modulo `p`. -/
theorem hilbert_p (hodd : p % 2 = 1) {u : Nat} (hu : ¬ p ∣ u) :
    hilbert ((u : Int) : Qp p) ((p : Int) : Qp p) = Foundations.Algebra.legendre u p := by
  have hU : Zp.IsPUnit ((u : Int) : Zp p) := fun h => hu (by
    have h := Zp.modPow_intCast.1 (show Zp.ModPow 1 ((u : Int) : Zp p) ((0 : Int) : Zp p) from h)
    rw [Int.pow_one, Int.sub_zero] at h
    exact Int.ofNat_dvd.1 h)
  have h1 : Zp.IsPUnit (1 : Zp p) := (Zp.isUnit_iff hP.prime 1).1 ⟨1, by grind⟩
  have key := (hilbertSolvable_unit_pv_iff hodd hU h1).trans (isQR_iff (p := p) (u := u)).symm
  have e1 : ((u : Int) : Qp p) = ofZp ((u : Int) : Zp p) := rfl
  have e2 : ((p : Int) : Qp p) = ofZp ((p : Zp p) * 1) := by
    rw [show (p : Zp p) * 1 = p by grind]; rfl
  unfold Foundations.Algebra.legendre
  rw [e1, e2]
  by_cases hq : Foundations.Algebra.IsQR u p
  · simp only [hu, hq, ite_true, ite_false]
    exact (hilbert_eq_one_iff _ _).2 (key.2 hq)
  · simp only [hu, hq, ite_false]
    exact (hilbert_eq_neg_one_iff _ _).2 (fun h => hq (key.1 h))

end Qp

end Foundations.Langlands.Padic
