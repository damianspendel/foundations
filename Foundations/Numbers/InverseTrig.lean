import Foundations.Numbers.ComplexModulus

/-!
# The inverse cosine

Cosine decreases strictly from `1` to `−1` on `[0, π]` (its derivative `−sin` is negative inside;
mean value theorem), so by the intermediate value theorem it is a bijection `[0, π] → [−1, 1]`.
Its inverse is the **arc cosine**: for `−1 ≤ x ≤ 1`, `arccos x` is the unique angle `θ ∈ [0, π]`
with `cos θ = x`.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-- **Cosine is strictly decreasing on `[0, π]`.** -/
theorem cos_strictAnti {x y : R} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ pi) : cos y < cos x := by
  obtain ⟨c, hc1, hc2, hc3⟩ := mean_value (f := cos) (f' := fun t => -sin t) hxy
    (fun t _ _ => continuousAt_cos t) (fun t _ _ => hasDerivAt_cos t)
  have := sin_pos_of_pos_of_lt_pi (x := c) (by grind) (by grind)
  have := OrderedRing.mul_pos this (by grind : (0 : R) < y - x)
  grind

/-- Cosine is injective on `[0, π]`. -/
theorem cos_injOn {x y : R} (hx0 : 0 ≤ x) (hx1 : x ≤ pi) (hy0 : 0 ≤ y) (hy1 : y ≤ pi)
    (h : cos x = cos y) : x = y := by
  rcases (by grind : x < y ∨ x = y ∨ y < x) with e | e | e
  · have := cos_strictAnti hx0 e hy1; grind
  · exact e
  · have := cos_strictAnti hy0 e hx1; grind

/-- Every `x ∈ [−1, 1]` is the cosine of an angle in `[0, π]`. -/
theorem exists_arccos {x : R} (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    ∃ θ, 0 ≤ θ ∧ θ ≤ pi ∧ cos θ = x := by
  obtain ⟨θ, h0, hπ, hθ⟩ := intermediate_value' (f := fun t => 0 - cos t) (a := 0) (b := pi)
    (v := -x) (Std.le_of_lt pi_pos)
    (fun t _ _ => continuousAt_sub (continuousAt_const 0 t) (continuousAt_cos t))
    (by show 0 - cos 0 ≤ -x; rw [cos_zero]; grind)
    (by show -x ≤ 0 - cos pi; rw [cos_pi]; grind)
  exact ⟨θ, h0, hπ, by have : 0 - cos θ = -x := hθ; grind⟩

/-- **The arc cosine**: for `x ∈ [−1, 1]`, the angle `θ ∈ [0, π]` with `cos θ = x` (and `0`
outside `[−1, 1]`, a value of no significance). -/
noncomputable def arccos (x : R) : R :=
  open Classical in if h : -1 ≤ x ∧ x ≤ 1 then Classical.choose (exists_arccos h.1 h.2) else 0

/-- `arccos x ∈ [0, π]` and `cos (arccos x) = x` for `x ∈ [−1, 1]`. -/
theorem arccos_spec {x : R} (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    0 ≤ arccos x ∧ arccos x ≤ pi ∧ cos (arccos x) = x := by
  unfold arccos
  rw [dite_eq_left_of_eq_true (eq_true ⟨h1, h2⟩)]
  exact Classical.choose_spec (exists_arccos h1 h2)

/-- **`cos (arccos x) = x`** for `x ∈ [−1, 1]`. -/
theorem cos_arccos {x : R} (h1 : -1 ≤ x) (h2 : x ≤ 1) : cos (arccos x) = x :=
  (arccos_spec h1 h2).2.2

/-- **`arccos (cos θ) = θ`** for `θ ∈ [0, π]`. -/
theorem arccos_cos {θ : R} (h0 : 0 ≤ θ) (h1 : θ ≤ pi) : arccos (cos θ) = θ := by
  have hc := abs_le.1 (abs_cos_le θ)
  obtain ⟨a0, a1, a2⟩ := arccos_spec hc.1 hc.2
  exact cos_injOn a0 a1 h0 h1 a2

/-- `arccos 1 = 0`, `arccos (−1) = π`. -/
theorem arccos_one_neg_one : arccos 1 = 0 ∧ arccos (-1) = pi := by
  constructor
  · have := arccos_cos (θ := 0) (Std.le_refl 0) (Std.le_of_lt pi_pos); rwa [cos_zero] at this
  · have := arccos_cos (θ := pi) (Std.le_of_lt pi_pos) (Std.le_refl pi); rwa [cos_pi] at this

end R

end Foundations.Numbers
