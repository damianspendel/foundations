import Foundations.Algebra.S5Generation
import Foundations.Numbers.Derivative

/-!
# The real roots of `x⁵ - 6x + 3`

The standard example of a quintic that cannot be solved by radicals is `q(x) = x⁵ - 6x + 3`. The
Galois-theoretic argument needs one piece of analysis: `q` has **exactly three real roots**.
Complex conjugation then fixes three of the five complex roots and swaps the other two, so it
acts on the roots as a transposition.

This file proves the count, using the real numbers `R` of Part II.

* **At least three.** `q(-2) = -17 < 0`, `q(-1) = 8 > 0`, `q(1) = -2 < 0` and `q(2) = 23 > 0`. The
  intermediate value theorem gives roots in `[-2, -1]`, `[-1, 1]` and `[1, 2]`, and the signs at
  the end points keep them apart.
* **At most three.** Four real roots would give, by Rolle's theorem, three distinct zeros of
  the derivative `q'(x) = 5x⁴ - 6`. But `5s⁴ = 5t⁴` forces `t = ±s`, so `q'` has at most two
  real zeros.

The headline `quintic_three_real_roots` packages both halves: there are real numbers
`r₁ < r₂ < r₃` with `q(rᵢ) = 0`, and every real root of `q` is one of them.
-/

namespace Foundations.Algebra

open Foundations.Numbers Foundations.Numbers.R

/-- The quintic `q(x) = x⁵ - 6x + 3` as a real function. -/
def quinticR (x : R) : R := x ^ 5 - 6 * x + 3

/-- The derivative of `q` is `q'(x) = 5x⁴ - 6`. -/
theorem hasDerivAt_quinticR (x : R) : HasDerivAt quinticR (5 * x ^ 4 - 6) x := by
  have h := ((hasDerivAt_pow 4 x).sub ((hasDerivAt_id x).const_mul 6)).add (hasDerivAt_const 3 x)
  have e : (((4 : Nat) : R) + 1) * x ^ 4 - 6 * 1 + 0 = 5 * x ^ 4 - 6 := by grind
  rw [e] at h
  exact h.congr fun y => rfl

/-- `q` is continuous everywhere. -/
theorem continuousAt_quinticR (x : R) : ContinuousAt quinticR x :=
  (hasDerivAt_quinticR x).continuousAt

/-- In `R`, a product vanishes only if a factor does. -/
theorem real_mul_eq_zero {a b : R} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · exact Or.inr (by grind)

/-- Real squares are non-negative. -/
theorem real_sq_nonneg (a : R) : 0 ≤ a * a := by
  rcases (by grind : 0 ≤ a ∨ a ≤ 0) with h | h
  · exact Lean.Grind.OrderedRing.mul_nonneg h h
  · exact Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos h h

/-- If `5s⁴ = 6` and `5t⁴ = 6` then `t = s` or `t = -s`. -/
theorem fourth_root_pm {s t : R} (hs : 5 * s ^ 4 - 6 = 0) (ht : 5 * t ^ 4 - 6 = 0) :
    t = s ∨ t = -s := by
  have e : (t - s) * ((t + s) * (s * s + t * t)) = 0 := by grind
  have hpos : s * s + t * t ≠ 0 := by
    have := real_sq_nonneg s; have := real_sq_nonneg t
    intro h0
    have hs0 : s * s = 0 := by grind
    rcases real_mul_eq_zero hs0 with h | h <;> (rw [h] at hs; grind)
  rcases real_mul_eq_zero e with h | h
  · exact Or.inl (by grind)
  · rcases real_mul_eq_zero h with h' | h'
    · exact Or.inr (by grind)
    · exact absurd h' hpos

/-- **The derivative has at most two real zeros.** Three zeros `s₁ < s₂ < s₃` of `5x⁴ - 6` are
impossible. -/
theorem no_three_critical {s₁ s₂ s₃ : R} (h12 : s₁ < s₂) (h23 : s₂ < s₃)
    (h1 : 5 * s₁ ^ 4 - 6 = 0) (h2 : 5 * s₂ ^ 4 - 6 = 0) (h3 : 5 * s₃ ^ 4 - 6 = 0) : False := by
  rcases fourth_root_pm h1 h2 with e2 | e2 <;> rcases fourth_root_pm h1 h3 with e3 | e3 <;> grind

/-- Rolle's theorem for `q`: between two distinct roots lies a zero of `q'`. -/
theorem rolle_quinticR {a b : R} (hab : a < b) (ha : quinticR a = 0) (hb : quinticR b = 0) :
    ∃ c, a < c ∧ c < b ∧ 5 * c ^ 4 - 6 = 0 :=
  rolle (f' := fun x => 5 * x ^ 4 - 6) hab (fun x _ _ => continuousAt_quinticR x)
    (fun x _ _ => hasDerivAt_quinticR x) (by rw [ha, hb])

/-- **At most three real roots.** `q` has no four distinct real roots `r₁ < r₂ < r₃ < r₄`. -/
theorem quinticR_no_four_roots {r₁ r₂ r₃ r₄ : R} (h12 : r₁ < r₂) (h23 : r₂ < r₃) (h34 : r₃ < r₄)
    (h1 : quinticR r₁ = 0) (h2 : quinticR r₂ = 0) (h3 : quinticR r₃ = 0) (h4 : quinticR r₄ = 0) :
    False := by
  obtain ⟨s₁, a1, b1, c1⟩ := rolle_quinticR h12 h1 h2
  obtain ⟨s₂, a2, b2, c2⟩ := rolle_quinticR h23 h2 h3
  obtain ⟨s₃, a3, b3, c3⟩ := rolle_quinticR h34 h3 h4
  exact no_three_critical (by grind) (by grind) c1 c2 c3

/-- A root of `q` in `[a, b]` from a sign change `q a ≤ 0 ≤ q b` or `q b ≤ 0 ≤ q a`. -/
theorem quinticR_root_between {a b : R} (hab : a ≤ b)
    (h : (quinticR a ≤ 0 ∧ 0 ≤ quinticR b) ∨ (0 ≤ quinticR a ∧ quinticR b ≤ 0)) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ quinticR c = 0 := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact intermediate_value hab (fun x _ _ => continuousAt_quinticR x) ha hb
  · obtain ⟨c, h1, h2, h3⟩ := intermediate_value (f := fun x => -quinticR x) hab
      (fun x _ _ => (hasDerivAt_quinticR x).neg.continuousAt) (by grind) (by grind)
    exact ⟨c, h1, h2, by grind⟩

/-- **`x⁵ - 6x + 3` has exactly three real roots.** There are reals `r₁ < r₂ < r₃` that are
roots, with `-2 < r₁ < -1 < r₂ < 1 < r₃ < 2`, and every real root equals one of them. -/
theorem quintic_three_real_roots :
    ∃ r₁ r₂ r₃ : R, r₁ < r₂ ∧ r₂ < r₃ ∧ quinticR r₁ = 0 ∧ quinticR r₂ = 0 ∧ quinticR r₃ = 0 ∧
      ∀ x, quinticR x = 0 → x = r₁ ∨ x = r₂ ∨ x = r₃ := by
  have v1 : quinticR (-2) = -17 := by unfold quinticR; grind
  have v2 : quinticR (-1) = 8 := by unfold quinticR; grind
  have v3 : quinticR 1 = -2 := by unfold quinticR; grind
  have v4 : quinticR 2 = 23 := by unfold quinticR; grind
  obtain ⟨r₁, a1, b1, c1⟩ := quinticR_root_between (a := -2) (b := -1) (by grind)
    (Or.inl ⟨by rw [v1]; grind, by rw [v2]; grind⟩)
  obtain ⟨r₂, a2, b2, c2⟩ := quinticR_root_between (a := -1) (b := 1) (by grind)
    (Or.inr ⟨by rw [v2]; grind, by rw [v3]; grind⟩)
  obtain ⟨r₃, a3, b3, c3⟩ := quinticR_root_between (a := 1) (b := 2) (by grind)
    (Or.inl ⟨by rw [v3]; grind, by rw [v4]; grind⟩)
  -- the end points are not roots, so the three roots are distinct
  have n1 : r₁ ≠ -1 := fun h => by rw [h, v2] at c1; grind
  have n2 : r₂ ≠ 1 := fun h => by rw [h, v3] at c2; grind
  have h12 : r₁ < r₂ := by grind
  have h23 : r₂ < r₃ := by grind
  refine ⟨r₁, r₂, r₃, h12, h23, c1, c2, c3, fun x hx => ?_⟩
  apply Classical.byContradiction
  intro hne
  have d1 : x ≠ r₁ := fun h => hne (Or.inl h)
  have d2 : x ≠ r₂ := fun h => hne (Or.inr (Or.inl h))
  have d3 : x ≠ r₃ := fun h => hne (Or.inr (Or.inr h))
  rcases (by grind : x < r₁ ∨ (r₁ < x ∧ x < r₂) ∨ (r₂ < x ∧ x < r₃) ∨ r₃ < x) with
    h | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · exact quinticR_no_four_roots h h12 h23 hx c1 c2 c3
  · exact quinticR_no_four_roots h h' h23 c1 hx c2 c3
  · exact quinticR_no_four_roots h12 h h' c1 c2 hx c3
  · exact quinticR_no_four_roots h12 h23 h c1 c2 c3 hx

end Foundations.Algebra
