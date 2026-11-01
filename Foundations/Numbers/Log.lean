import Foundations.Numbers.Exp

/-!
# Analysis on the reals IX: the logarithm

The exponential function is strictly increasing, and by the intermediate value theorem it takes
every positive value. Hence it has an inverse, the **natural logarithm** `log : (0, ∞) → ℝ`,
characterised by `exp (log y) = y`. Napier's original purpose for logarithms — turning
multiplication into addition — becomes the identity `log (x y) = log x + log y`, inherited from
the functional equation of `exp`.

Finally we differentiate the inverse function: `log' y = 1/y`. The proof writes `z = y · exp k`
with `k = log z − log y` and uses the quadratic estimate `|exp k − 1 − k| ≤ C k²` from the
exponential file, together with the continuity of `log` (which follows from monotonicity alone).
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-- `exp` is injective. -/
theorem exp_injective {x y : R} (h : exp x = exp y) : x = y := by
  rcases (by grind : x < y ∨ x = y ∨ y < x) with h' | h' | h'
  · have := exp_strictMono h'; grind
  · exact h'
  · have := exp_strictMono h'; grind

/-- `exp x < exp y ↔ x < y`. -/
theorem exp_lt_exp {x y : R} : exp x < exp y ↔ x < y := by
  constructor
  · intro h
    rcases (by grind : x < y ∨ x = y ∨ y < x) with h' | h' | h'
    · exact h'
    · rw [h'] at h; grind
    · have := exp_strictMono h'; grind
  · exact exp_strictMono

/-- **`exp` takes every positive value.** -/
theorem exists_exp_eq {y : R} (hy : 0 < y) : ∃ x, exp x = y := by
  have hc : ∀ x, ContinuousAt exp x := fun x => (hasDerivAt_exp x).continuousAt
  -- First for `y ≥ 1`, by the intermediate value theorem on `[0, y]`.
  have big : ∀ y : R, 1 ≤ y → ∃ x, exp x = y := fun y hy1 => by
    obtain ⟨x, -, -, hx⟩ := intermediate_value' (f := exp) (a := 0) (b := y) (v := y)
      (by grind) (fun x _ _ => hc x) (by rw [exp_zero]; exact hy1)
      (by have := one_add_le_exp (by grind : (0 : R) ≤ y); grind)
    exact ⟨x, hx⟩
  rcases (by grind : 1 ≤ y ∨ y < 1) with h | h
  · exact big y h
  · -- For `0 < y < 1` use `exp (−x) = 1 / exp x`.
    have hinv : 1 ≤ 1 / y := by
      have := one_div_le_one_div hy (Std.le_of_lt h); grind
    obtain ⟨x, hx⟩ := big (1 / y) hinv
    refine ⟨-x, ?_⟩
    have := exp_mul_exp_neg x
    rw [hx] at this
    grind

/-- **The natural logarithm**: for `y > 0`, the unique `x` with `exp x = y` (and `0` for
`y ≤ 0`, a value of no significance). -/
noncomputable def log (y : R) : R :=
  open Classical in if h : 0 < y then Classical.choose (exists_exp_eq h) else 0

/-- **`exp (log y) = y`** for `y > 0`. -/
theorem exp_log {y : R} (hy : 0 < y) : exp (log y) = y := by
  unfold log
  rw [dite_eq_left_of_eq_true (eq_true hy)]
  exact Classical.choose_spec (exists_exp_eq hy)

/-- **`log (exp x) = x`.** -/
theorem log_exp (x : R) : log (exp x) = x := exp_injective (exp_log (exp_pos x))

/-- `log 1 = 0`. -/
theorem log_one : log 1 = 0 := by rw [← exp_zero, log_exp]

/-- **Logarithms turn products into sums.** `log (x y) = log x + log y` for `x, y > 0`. -/
theorem log_mul {x y : R} (hx : 0 < x) (hy : 0 < y) : log (x * y) = log x + log y := by
  apply exp_injective
  rw [exp_log (OrderedRing.mul_pos hx hy), exp_add, exp_log hx, exp_log hy]

/-- **The logarithm is strictly increasing** on `(0, ∞)`. -/
theorem log_strictMono {x y : R} (hx : 0 < x) (hxy : x < y) : log x < log y := by
  rw [← exp_lt_exp, exp_log hx, exp_log (by grind)]; exact hxy

/-- **Continuity of the logarithm** at `y > 0` (with the extra information that nearby points
are positive). -/
theorem log_continuous {y : R} (hy : 0 < y) {η : R} (hη : 0 < η) :
    ∃ δ : R, 0 < δ ∧ ∀ z, abs (z - y) < δ → 0 < z ∧ abs (log z - log y) < η := by
  have h1 : exp (log y - η) < y := by
    have := exp_strictMono (by grind : log y - η < log y); rw [exp_log hy] at this; exact this
  have h2 : y < exp (log y + η) := by
    have := exp_strictMono (by grind : log y < log y + η); rw [exp_log hy] at this; exact this
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both (by grind : 0 < y - exp (log y - η))
    (by grind : 0 < exp (log y + η) - y)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hz' := abs_lt.1 hz
  have hzpos : 0 < z := by have := exp_pos (log y - η); grind
  refine ⟨hzpos, abs_lt.2 ⟨?_, ?_⟩⟩
  · have : exp (log y - η) < exp (log z) := by rw [exp_log hzpos]; grind
    have := exp_lt_exp.1 this; grind
  · have : exp (log z) < exp (log y + η) := by rw [exp_log hzpos]; grind
    have := exp_lt_exp.1 this; grind

/-- **The derivative of the logarithm.** `log' y = 1/y` for `y > 0`. -/
theorem hasDerivAt_log {y : R} (hy : 0 < y) : HasDerivAt log (1 / y) y := fun ε hε => by
  -- The quadratic estimate `|exp k − 1 − k| ≤ C k²` with `C = exp 1 / 2`.
  let C := exp 1 / 2
  have hC : 0 ≤ C := by have := exp_pos 1; grind
  have quad : ∀ k : R, abs k ≤ 1 → abs (exp k - 1 - k) ≤ C * (abs k * abs k) := fun k hk => by
    have := abs_exp_sub_le (x := 0) (y := k) (by rw [show k - 0 = k by grind]; exact hk)
    rw [exp_zero, abs_zero, show k - 0 = k by grind, show (0 : R) + 1 = 1 by grind] at this
    grind
  -- Choose how close `log z` must be to `log y`.
  obtain ⟨η₁, hη₁, hη₁a, hη₁b⟩ := exists_pos_le_both (by grind : (0 : R) < 1)
    (div_pos (by grind : (0 : R) < 1) (by grind : 0 < 2 * C + 1))
  obtain ⟨η, hη, hηa, hηb⟩ := exists_pos_le_both hη₁
    (div_pos (OrderedRing.mul_pos hε hy) (by grind : 0 < 2 * C + 1))
  obtain ⟨δ, hδ, hδ'⟩ := log_continuous hy hη
  refine ⟨δ, hδ, fun z hz => ?_⟩
  obtain ⟨hzpos, hk⟩ := hδ' z hz
  let k := log z - log y
  have hK := abs_nonneg k
  -- `z = y · exp k`.
  have hzk : z = y * exp k := by
    rw [show k = log z + -log y by grind, exp_add, ← exp_log hzpos]
    have := exp_mul_exp_neg (log y); rw [exp_log hy] at this; rw [log_exp]; grind
  have hq := quad k (by grind)
  clear quad hδ'
  -- `C |k| ≤ 1/2` and `C |k| ≤ ε y / 2`.
  have t1 : 2 * C + 1 ≠ 0 := by grind
  have c1 : C * abs k ≤ 1 / 2 := by
    have := OrderedRing.mul_le_mul_of_nonneg_left (show abs k ≤ 1 / (2 * C + 1) by grind) hC
    have e : (2 * C + 1) * (1 / (2 * C + 1)) = 1 := by grind
    have := div_pos (by grind : (0 : R) < 1) (by grind : 0 < 2 * C + 1)
    grind
  have c2 : C * abs k ≤ ε * y / 2 := by
    have := OrderedRing.mul_le_mul_of_nonneg_left
      (show abs k ≤ ε * y / (2 * C + 1) by grind) hC
    have e : (2 * C + 1) * (ε * y / (2 * C + 1)) = ε * y := by grind
    have := div_pos (OrderedRing.mul_pos hε hy) (by grind : 0 < 2 * C + 1)
    grind
  -- `|z − y| = y |exp k − 1| ≥ y |k| / 2`.
  have hzy : abs (z - y) = y * abs (exp k - 1) := by
    rw [hzk, show y * exp k - y = y * (exp k - 1) by grind, abs_mul, abs_of_nonneg (by grind)]
  have hlow : abs k / 2 ≤ abs (exp k - 1) := by
    have := abs_add (exp k - 1) (-(exp k - 1 - k))
    rw [abs_neg, show exp k - 1 + -(exp k - 1 - k) = k by grind] at this
    have := OrderedRing.mul_le_mul_of_nonneg_right c1 hK
    grind
  -- The error is `|k − (exp k − 1)| ≤ C k² ≤ (ε y / 2) |k| ≤ ε |z − y|`.
  have herr : log z - log y - 1 / y * (z - y) = -(exp k - 1 - k) := by
    have e1 : z - y = y * (exp k - 1) := by rw [hzk]; grind
    have : y ≠ 0 := by grind
    show k - 1 / y * (z - y) = _
    rw [e1]; grind
  rw [herr, abs_neg]
  have k1 := OrderedRing.mul_le_mul_of_nonneg_right c2 hK
  have k2 := OrderedRing.mul_le_mul_of_nonneg_left hlow (OrderedRing.mul_nonneg (Std.le_of_lt hε) (Std.le_of_lt hy))
  rw [hzy]
  grind

end R

end Foundations.Numbers
