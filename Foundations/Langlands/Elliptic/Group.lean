import Foundations.Langlands.Elliptic.AssocFull
import Foundations.Algebra.VectorSpace

/-!
# The group of points

This file assembles the case analysis for associativity and concludes that the points of an
elliptic curve form an abelian group (`Point.instAddAbGroup`, using the library's
`Foundations.Algebra.AddAbGroup`).

The cases, for `S = (P + Q) + R` and `T = P + (Q + R)`:

1. one of `P, Q, R` is `O`: immediate;
2. `P + Q = O`, `Q + R = O`, `S = O` or `T = O`: then one point is determined by the other
   two (`Q = −P`, `R = −Q`, `R = −(P + Q)`, `P = −(Q + R)`) and the identity follows from
   the cancellation law `P + (−P + Q) = Q` and `−(A + B) = −A + −B` (file `Cancel`);
3. `R = P`: commutativity; `R = −P`: cancellation;
4. otherwise `x_P ≠ x_R`, and either `x_P, x_Q, x_R` are distinct, or `Q = P`, or `Q = R`. In
   each case there is a parabola with full Vieta data through the three points (tangent at the
   doubled point, `Curve.parabola_of_distinct`, `Curve.parabola_of_double`), and the key lemma
   `Point.add_add_eq_neg_of_parabola`, applied to `(P, Q, R)` and to a permutation, shows that
   `S` and `T` are both `−P₄`.
-/

namespace Foundations.Langlands.Elliptic

universe u

variable {K : Type u} [Lean.Grind.Field K]

namespace Point

variable {E : Curve K} [DecidableEq K]

/-- `−P + P = O`. -/
theorem neg_add_self (P : Point E) : -P + P = 0 := by
  rw [add_comm]; exact add_neg_self P

/-- Associativity for three affine points, in the main case: no partial or total sum is `O`,
and `R ≠ ±P`. -/
theorem add_assoc_main {x₁ y₁ x₂ y₂ x₃ y₃ : K}
    (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) (h₃ : E.OnCurve x₃ y₃)
    (hA : (some x₁ y₁ h₁ + some x₂ y₂ h₂ : Point E) ≠ 0)
    (hB : (some x₂ y₂ h₂ + some x₃ y₃ h₃ : Point E) ≠ 0)
    (hS : (some x₁ y₁ h₁ + some x₂ y₂ h₂ : Point E) + some x₃ y₃ h₃ ≠ 0)
    (hT : (some x₁ y₁ h₁ : Point E) + (some x₂ y₂ h₂ + some x₃ y₃ h₃) ≠ 0)
    (hR₁ : (some x₃ y₃ h₃ : Point E) ≠ some x₁ y₁ h₁)
    (hR₂ : (some x₃ y₃ h₃ : Point E) ≠ -some x₁ y₁ h₁) :
    (some x₁ y₁ h₁ + some x₂ y₂ h₂ : Point E) + some x₃ y₃ h₃ =
      some x₁ y₁ h₁ + (some x₂ y₂ h₂ + some x₃ y₃ h₃) := by
  have hT' : (some x₂ y₂ h₂ + some x₃ y₃ h₃ : Point E) + some x₁ y₁ h₁ ≠ 0 := by
    rwa [add_comm (some x₂ y₂ h₂ + _)]
  rw [add_comm (some x₁ y₁ h₁) (some x₂ y₂ h₂ + _)]
  -- `x₁ ≠ x₃`
  have h₁₃ : x₁ ≠ x₃ := by
    intro hx
    by_cases hy : y₁ + y₃ = 0
    · exact hR₂ (by
        show some x₃ y₃ h₃ = some x₁ (-y₁) _
        rw [some_eq_some]; exact ⟨hx.symm, by grind⟩)
    · have := E.eq_of_x_eq h₁ h₃ hx hy
      exact hR₁ (by rw [some_eq_some]; exact ⟨hx.symm, this⟩)
  by_cases h₁₂ : x₁ = x₂
  · -- `Q = P`: a doubling first
    have hy : ¬ (x₁ = x₂ ∧ y₁ + y₂ = 0) := fun h => hA ((addSome_eq_zero_iff h₁ h₂).2 h)
    have hy₂ := E.eq_of_x_eq h₁ h₂ h₁₂ (fun h => hy ⟨h₁₂, h⟩)
    subst h₁₂ hy₂
    obtain ⟨α, β, γ, x₄, e₁, e₃, hP⟩ := E.parabola_of_double h₁ h₃ hy h₁₃ hS
    obtain ⟨_, eL⟩ := add_add_eq_neg_of_parabola hP h₁ h₁ h₃ e₁ e₁ e₃ hA hS
    obtain ⟨_, eR⟩ := add_add_eq_neg_of_parabola hP.swap h₁ h₃ h₁ e₁ e₃ e₁ hB hT'
    rw [eL, eR]
  · by_cases h₂₃ : x₂ = x₃
    · -- `Q = R`: a doubling second
      have hy : ¬ (x₂ = x₃ ∧ y₂ + y₃ = 0) := fun h => hB ((addSome_eq_zero_iff h₂ h₃).2 h)
      have hy₃ := E.eq_of_x_eq h₂ h₃ h₂₃ (fun h => hy ⟨h₂₃, h⟩)
      subst h₂₃ hy₃
      have h₂₁ : x₂ ≠ x₁ := fun h => h₁₂ h.symm
      obtain ⟨α, β, γ, x₄, e₂, e₁, hP⟩ := E.parabola_of_double h₂ h₁ hy h₂₁ hT'
      obtain ⟨_, eL⟩ := add_add_eq_neg_of_parabola hP.cycle.cycle h₁ h₂ h₂ e₁ e₂ e₂ hA hS
      obtain ⟨_, eR⟩ := add_add_eq_neg_of_parabola hP h₂ h₂ h₁ e₂ e₂ e₁ hB hT'
      rw [eL, eR]
    · -- three distinct `x`-coordinates
      obtain ⟨α, β, γ, x₄, e₁, e₂, e₃, hP⟩ := E.parabola_of_distinct h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hS
      obtain ⟨_, eL⟩ := add_add_eq_neg_of_parabola hP h₁ h₂ h₃ e₁ e₂ e₃ hA hS
      obtain ⟨_, eR⟩ := add_add_eq_neg_of_parabola hP.cycle h₂ h₃ h₁ e₂ e₃ e₁ hB hT'
      rw [eL, eR]

/-- **Associativity of the chord–tangent law.** For all points `P, Q, R` of an elliptic curve
`E` over a field of characteristic not `2` or `3`, `(P + Q) + R = P + (Q + R)`. -/
theorem add_assoc (P Q R : Point E) : (P + Q) + R = P + (Q + R) := by
  by_cases hA : P + Q = 0
  · have hQ := eq_neg_of_add_eq_zero hA
    subst hQ
    rw [hA, zero_add, add_neg_add_cancel]
  by_cases hB : Q + R = 0
  · have hR := eq_neg_of_add_eq_zero hB
    subst hR
    rw [hB, add_zero, add_add_neg_cancel]
  by_cases hS : (P + Q) + R = 0
  · have hR := eq_neg_of_add_eq_zero hS
    subst hR
    rw [hS, neg_add, add_comm (-P), add_neg_add_cancel, add_neg_self]
  by_cases hT : P + (Q + R) = 0
  · have hP : P = -(Q + R) := by
      have := eq_neg_of_add_eq_zero (by rwa [add_comm] at hT : (Q + R) + P = 0)
      exact this
    subst hP
    rw [hT, neg_add, add_comm (-Q + -R) Q, add_neg_add_cancel, neg_add_self]
  by_cases hR₁ : R = P
  · subst hR₁
    rw [add_comm Q R, add_comm R (R + Q)]
  by_cases hR₂ : R = -P
  · subst hR₂
    rw [add_comm P Q, add_add_neg_cancel, add_comm Q (-P), add_neg_add_cancel]
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show (some x₁ y₁ h₁ + 0) + R = some x₁ y₁ h₁ + (0 + R)
      rw [add_zero, zero_add]
    | some x₂ y₂ h₂ =>
      cases R with
      | zero =>
        show (some x₁ y₁ h₁ + some x₂ y₂ h₂) + 0 = some x₁ y₁ h₁ + (some x₂ y₂ h₂ + 0)
        rw [add_zero, add_zero]
      | some x₃ y₃ h₃ => exact add_assoc_main h₁ h₂ h₃ hA hB hS hT hR₁ hR₂

/-- **The group of points of an elliptic curve.** With the chord–tangent addition, `O` as zero
and `(x, y) ↦ (x, −y)` as negation, the points of `E` form an abelian group. -/
instance instAddAbGroup : Foundations.Algebra.AddAbGroup (Point E) where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  neg_add_cancel := neg_add_self

end Point

end Foundations.Langlands.Elliptic
