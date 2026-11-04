import Foundations.Langlands.Padic.QpComplete

/-!
# ℚ is dense in ℚₚ

Every `p`-adic number is a limit of rational numbers: given `q = x / pᴷ` and a precision `k`,
truncate the `p`-adic integer `x` to its approximation `a = x_{k+K} ∈ ℤ`; then
`|q − a/pᴷ|ₚ ≤ p^(−k)`. Together with `Qp.complete` (ℚₚ is complete) and `Qp.abs_ofQ` (the
absolute value of ℚₚ extends `|·|ₚ` on ℚ), this says that ℚₚ is a complete valued field
containing ℚ as a dense subfield: ℚₚ *is* the completion of ℚ for `|·|ₚ`, the local field of ℚ
at the place `p`. (The uniqueness of completions up to isometry is the general universal
property, not formalised here.)
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- `|1|ₚ = 1` in ℚₚ. -/
theorem abs_one : abs (1 : Qp p) = 1 := by
  have h := abs_pow (p := p) 0
  rw [show ((p : Zp p) ^ 0) = 1 from rfl] at h
  exact h

/-- **Density of ℚ in ℚₚ.** For every `p`-adic number `q` and every `k` there is a rational `r`
with `|q − r|ₚ ≤ p^(−k)`. -/
theorem dense (q : Qp p) (k : Nat) : ∃ r : Q, abs (q - ofQ r) ≤ (p : Q) ^ (-(k : Int)) := by
  induction q using ind with | h x K => ?_
  induction x using Zp.ind with | h xs => ?_
  have hp2 := two_le_p (p := p)
  have hp0 : (p : Q) ≠ 0 := by grind
  let a : Int := xs.seq (k + K)
  have hpK : (0 : Int) < (p : Int) ^ K := Int.pow_pos (by have := hP.prime.1; omega)
  refine ⟨Q.mk a ((p : Int) ^ K) hpK, ?_⟩
  -- notation: `c = pᴷ`
  let c : Qp p := ofZp ((p : Zp p) ^ K)
  have hc : c ≠ 0 := fun h => pow_ne_zero (p := p) K (mk_eq_zero.1 h)
  have hcinv := Field.mul_inv_cancel hc
  have hcK : (((p : Int) ^ K : Int) : Qp p) = c := by
    show ofZp _ = ofZp _; rw [Zp.pow_p_eq]; rfl
  have hq : mk (Zp.mk xs) K = c⁻¹ * ofZp (Zp.mk xs) := by
    rw [mk_eq_div]; show _ * _⁻¹ = _; grind
  rw [ofQ_mk, hcK, hq, show ((a : Int) : Qp p) = ofZp (a : Zp p) from rfl]
  have e : c⁻¹ * ofZp (Zp.mk xs) - ofZp (a : Zp p) * c⁻¹ =
      c⁻¹ * ofZp (Zp.mk xs - (a : Zp p)) := by
    rw [show Zp.mk xs - (a : Zp p) = Zp.mk xs + (-1) * (a : Zp p) by grind, ofZp_add, ofZp_mul,
      show ofZp (-1 : Zp p) = -1 from rfl]; grind
  rw [e, abs_mul]
  -- the truncation error is divisible by `p^(k+K)`
  have h1 := (abs_ofZp_le_iff (Zp.mk xs - (a : Zp p)) (k + K)).2
    (Zp.modPow_iff_sub.1 (by
      show (p : Int) ^ (k + K) ∣ xs.seq (k + K) - a
      rw [Int.sub_self]; exact Int.dvd_zero _))
  -- `|c⁻¹|ₚ = pᴷ`
  have hci : abs c⁻¹ = (p : Q) ^ (K : Int) := by
    have h := abs_mul c c⁻¹
    rw [hcinv, abs_one, abs_pow] at h
    have : (p : Q) ^ (K : Int) * (p : Q) ^ (-(K : Int)) = 1 := by
      rw [← Field.zpow_add hp0, show (K : Int) + -(K : Int) = 0 by omega, Field.zpow_zero]
    grind
  rw [hci]
  have hpk := zpow_pos (show (0 : Q) < p by grind) (K : Int)
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left h1 (Std.le_of_lt hpk)
  rw [← Field.zpow_add hp0, show (K : Int) + -(((k + K : Nat) : Int)) = -(k : Int) by omega] at h2
  exact h2

/-- **Every `p`-adic number is a limit of rationals.** For every `q ∈ ℚₚ` there is a sequence of
rationals `rₘ` with `rₘ → q` in ℚₚ. -/
theorem exists_seq_tendsto (q : Qp p) : ∃ r : Nat → Q, Converges (fun m => ofQ (r m)) q := by
  have hp2 := two_le_p (p := p)
  refine ⟨fun m => Classical.choose (dense q m), fun k => ⟨k, fun m hm => ?_⟩⟩
  have h := Classical.choose_spec (dense q m)
  have e : ofQ (p := p) (Classical.choose (dense q m)) - q =
      -1 * (q - ofQ (Classical.choose (dense q m))) := by grind
  show abs (ofQ (Classical.choose (dense q m)) - q) ≤ _
  rw [e, abs_mul]
  have hneg : abs (-1 : Qp p) = 1 := by
    have h := abs_mul (p := p) (-1) (-1)
    rw [show (-1 : Qp p) * -1 = 1 by grind, abs_one] at h
    have := abs_nonneg (p := p) (-1)
    have : (abs (-1 : Qp p) - 1) * (abs (-1 : Qp p) + 1) = 0 := by grind
    rcases Field.of_mul_eq_zero this with h | h <;> grind
  rw [hneg, Semiring.one_mul]
  exact Std.le_trans h (zpow_le_zpow (by grind) (by omega))

end Qp

end Foundations.Langlands.Padic
