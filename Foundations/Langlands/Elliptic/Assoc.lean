import Foundations.Langlands.Elliptic.Weierstrass

/-!
# Associativity of the chord–tangent law: the generic case

Associativity is the one group axiom that is not visible in the picture. Classically it is
deduced from the Cayley–Bacharach theorem on nine points of two cubics, or from the
identification of `E` with its Picard group (so with divisor classes, as in Weil's work), or
analytically from the Weierstrass `℘`-function over `ℂ`. Here we take the brute-force route
of explicit formulas, but organised so that every step is a small polynomial identity that
`grind` checks in the library's `Lean.Grind.Field` normal form.

## The idea: one symmetric parabola

Given three affine points `P₁, P₂, P₃` with pairwise distinct `x`-coordinates, interpolate them
by a parabola `y = αx² + βx + γ`. Substituting into the curve gives a quartic
`(αx² + βx + γ)² − (x³ + ax + b)` with roots `x₁, x₂, x₃`; if `α ≠ 0` (the points are not
collinear) it has a fourth root `x₄`, and `P₄ = (x₄, αx₄² + βx₄ + γ)` is on the curve. The data
`(α, β, γ, x₄)` depend only on the *set* `{P₁, P₂, P₃}`.

Key lemma (`add_add_eq_neg`): `(P₁ + P₂) + P₃ = −P₄`. Algebraically, after naming the slope
`λ = α(x₁ + x₂) + β` of the chord `P₁P₂`, this comes down to two polynomial identities saying
that `P₁ + P₂`, `P₃`, `P₄` are collinear, given only the two Vieta relations
`2αβ − 1 = −α²(x₁ + x₂ + x₃ + x₄)` and `β² + 2αγ = α² e₂(x₁, x₂, x₃, x₄)`.

Since `−P₄` is symmetric in `P₁, P₂, P₃`, applying the key lemma to `(P₁, P₂, P₃)` and to
`(P₂, P₃, P₁)` and using commutativity gives associativity (`add_assoc_generic`).

## Scope

This proves associativity in the **generic case**: all three points affine, with pairwise
distinct `x`-coordinates, and with neither partial sum `P₁ + P₂` nor `P₂ + P₃` sharing an
`x`-coordinate with the remaining point. Every addition that occurs is then a chord addition.
The remaining cases — some point is `O`; two of the `x`-coordinates coincide (doublings and
inverse pairs); a partial sum is `O` or vertical over the third point — are handled in
`AssocFull` and `Group`, which strengthen the key lemma to use all four Vieta relations.
-/

namespace Foundations.Langlands.Elliptic

universe u

variable {K : Type u} [Lean.Grind.Field K]

namespace Curve

variable (E : Curve K)

/-- **Interpolating parabola.** For three points with pairwise distinct `x`-coordinates,
`(α, β, γ)` with `yᵢ = αxᵢ² + βxᵢ + γ`: `α` is the second divided difference of the `y`'s,
`β = λ₁₂ − α(x₁ + x₂)` and `γ = y₁ − αx₁² − βx₁`. -/
theorem exists_parabola {x₁ y₁ x₂ y₂ x₃ y₃ : K} (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃)
    (h₂₃ : x₂ ≠ x₃) : ∃ α β γ : K, y₁ = α * x₁ ^ 2 + β * x₁ + γ ∧
      y₂ = α * x₂ ^ 2 + β * x₂ + γ ∧ y₃ = α * x₃ ^ 2 + β * x₃ + γ := by
  have d₁₂ : x₂ - x₁ ≠ 0 := fun h => h₁₂ (by grind)
  have d₂₃ : x₃ - x₂ ≠ 0 := fun h => h₂₃ (by grind)
  have d₁₃ : x₃ - x₁ ≠ 0 := fun h => h₁₃ (by grind)
  let l₁₂ := (y₂ - y₁) / (x₂ - x₁)
  let l₂₃ := (y₃ - y₂) / (x₃ - x₂)
  have e₁₂ : l₁₂ * (x₂ - x₁) = y₂ - y₁ := by simp only [l₁₂]; grind
  have e₂₃ : l₂₃ * (x₃ - x₂) = y₃ - y₂ := by simp only [l₂₃]; grind
  let α := (l₂₃ - l₁₂) / (x₃ - x₁)
  have eα : α * (x₃ - x₁) = l₂₃ - l₁₂ := by simp only [α]; grind
  refine ⟨α, l₁₂ - α * (x₁ + x₂), y₁ - α * x₁ ^ 2 - (l₁₂ - α * (x₁ + x₂)) * x₁, by grind,
    by grind, ?_⟩
  grind

/-- **Second divided difference.** If three points with pairwise distinct `x`-coordinates on
`E` lie on the parabola `y = αx² + βx + γ`, then the quartic
`(αx² + βx + γ)² − (x³ + ax + b)`, which vanishes at `x₁, x₂, x₃`, has vanishing second divided
difference: `α² h₂ + (2αβ − 1)(x₁ + x₂ + x₃) + β² + 2αγ = 0`, where
`h₂ = x₁² + x₂² + x₃² + x₁x₂ + x₁x₃ + x₂x₃`. -/
theorem second_divided_difference {α β γ x₁ x₂ x₃ : K} (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃)
    (h₂₃ : x₂ ≠ x₃) (h₁ : E.OnCurve x₁ (α * x₁ ^ 2 + β * x₁ + γ))
    (h₂ : E.OnCurve x₂ (α * x₂ ^ 2 + β * x₂ + γ))
    (h₃ : E.OnCurve x₃ (α * x₃ ^ 2 + β * x₃ + γ)) :
    α ^ 2 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₁ * x₂ + x₁ * x₃ + x₂ * x₃)
      + (2 * α * β - 1) * (x₁ + x₂ + x₃) + (β ^ 2 + 2 * α * γ) = 0 := by
  unfold OnCurve at h₁ h₂ h₃
  have d₁₂ : x₁ - x₂ ≠ 0 := fun h => h₁₂ (by grind)
  have d₂₃ : x₂ - x₃ ≠ 0 := fun h => h₂₃ (by grind)
  have d₁₃ : x₁ - x₃ ≠ 0 := fun h => h₁₃ (by grind)
  -- first divided differences
  have D : ∀ u v : K, u - v ≠ 0 →
      (α * u ^ 2 + β * u + γ) ^ 2 = u ^ 3 + E.a * u + E.b →
      (α * v ^ 2 + β * v + γ) ^ 2 = v ^ 3 + E.a * v + E.b →
      α ^ 2 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) + (2 * α * β - 1) * (u ^ 2 + u * v + v ^ 2)
        + (β ^ 2 + 2 * α * γ) * (u + v) + (2 * β * γ - E.a) = 0 := by
    intro u v huv hu hv
    have : (u - v) * (α ^ 2 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)
        + (2 * α * β - 1) * (u ^ 2 + u * v + v ^ 2)
        + (β ^ 2 + 2 * α * γ) * (u + v) + (2 * β * γ - E.a)) = 0 := by grind
    grind
  have D₁₂ := D x₁ x₂ d₁₂ h₁ h₂
  have D₁₃ := D x₁ x₃ d₁₃ h₁ h₃
  have : (x₂ - x₃) * (α ^ 2 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₁ * x₂ + x₁ * x₃ + x₂ * x₃)
      + (2 * α * β - 1) * (x₁ + x₂ + x₃) + (β ^ 2 + 2 * α * γ)) = 0 := by grind
  grind

/-- **The fourth point of the parabola.** Three points of `E` with pairwise distinct
`x`-coordinates, such that `P₁ + P₂` does not lie over `x₃`, lie on a parabola
`y = αx² + βx + γ` with `α ≠ 0`, and there is `x₄` satisfying the two Vieta relations
`2αβ − 1 = −α²(x₁ + x₂ + x₃ + x₄)` and `β² + 2αγ = α² e₂(x₁, x₂, x₃, x₄)`. -/
theorem exists_fourth_point [DecidableEq K] {x₁ y₁ x₂ y₂ x₃ y₃ : K}
    (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) (h₃ : E.OnCurve x₃ y₃)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃)
    (hQ : E.slope x₁ y₁ x₂ y₂ ^ 2 - x₁ - x₂ ≠ x₃) :
    ∃ α β γ x₄ : K, α ≠ 0 ∧ y₁ = α * x₁ ^ 2 + β * x₁ + γ ∧
      y₂ = α * x₂ ^ 2 + β * x₂ + γ ∧ y₃ = α * x₃ ^ 2 + β * x₃ + γ ∧
      2 * α * β - 1 = -α ^ 2 * (x₁ + x₂ + x₃ + x₄) ∧
      β ^ 2 + 2 * α * γ = α ^ 2 * (x₁ * x₂ + x₁ * x₃ + x₁ * x₄ + x₂ * x₃ + x₂ * x₄ + x₃ * x₄) := by
  obtain ⟨α, β, γ, e₁, e₂, e₃⟩ := exists_parabola (y₁ := y₁) (y₂ := y₂) (y₃ := y₃) h₁₂ h₁₃ h₂₃
  subst e₁ e₂ e₃
  have D := E.second_divided_difference h₁₂ h₁₃ h₂₃ h₁ h₂ h₃
  have hα : α ≠ 0 := by
    intro hα0
    subst hα0
    have r := (E.slope_rel_ne h₁ h₂ h₁₂).1
    have d : x₂ - x₁ ≠ 0 := fun h => h₁₂ (by grind)
    have hs : E.slope x₁ (0 * x₁ ^ 2 + β * x₁ + γ) x₂ (0 * x₂ ^ 2 + β * x₂ + γ) = β := by
      have : (E.slope x₁ (0 * x₁ ^ 2 + β * x₁ + γ) x₂ (0 * x₂ ^ 2 + β * x₂ + γ) - β)
        * (x₂ - x₁) = 0 := by grind
      grind
    rw [hs] at hQ
    exact hQ (by grind)
  have hα2 : α ^ 2 ≠ 0 := by grind
  let x₄ := (1 - 2 * α * β) / α ^ 2 - x₁ - x₂ - x₃
  have e₄ : α ^ 2 * (x₄ + x₁ + x₂ + x₃) = 1 - 2 * α * β := by simp only [x₄]; grind
  exact ⟨α, β, γ, x₄, hα, rfl, rfl, rfl, by grind, by grind⟩

end Curve

namespace Point

variable {E : Curve K} [DecidableEq K]

/-- Reading off the slope: if `λ` is a chord slope of two points with distinct
`x`-coordinates (`y₂ − y₁ = λ(x₂ − x₁)`), then it is the slope used by the addition law. -/
theorem slope_eq_of {x₁ y₁ x₂ y₂ l : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂)
    (hx : x₁ ≠ x₂) (hl : y₂ - y₁ = l * (x₂ - x₁)) : E.slope x₁ y₁ x₂ y₂ = l := by
  have r := (E.slope_rel_ne h₁ h₂ hx).1
  have d : x₂ - x₁ ≠ 0 := fun h => hx (by grind)
  have : (E.slope x₁ y₁ x₂ y₂ - l) * (x₂ - x₁) = 0 := by grind
  grind

/-- The chord sum of two affine points with distinct `x`-coordinates, given a chord slope `λ`. -/
theorem addSome_of_slope {x₁ y₁ x₂ y₂ l : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂)
    (hx : x₁ ≠ x₂) (hl : y₂ - y₁ = l * (x₂ - x₁)) :
    ∃ h, addSome x₁ y₁ h₁ x₂ y₂ h₂ = some (l ^ 2 - x₁ - x₂) (l * (x₁ - (l ^ 2 - x₁ - x₂)) - y₁) h := by
  have hn : ¬ (x₁ = x₂ ∧ y₁ + y₂ = 0) := fun h => hx h.1
  have hs := slope_eq_of h₁ h₂ hx hl
  have r₂ := (E.slope_rel_ne h₁ h₂ hx).2
  rw [hs] at r₂
  refine ⟨E.third_point_onCurve h₁ hl r₂, ?_⟩
  rw [addSome_of_not h₁ h₂ hn, some_eq_some, hs]
  exact ⟨rfl, rfl⟩

/-- **Key lemma: `(P₁ + P₂) + P₃ = −P₄`.** Let `P₁, P₂, P₃` lie on the parabola
`y = αx² + βx + γ`, with `x₁ ≠ x₂`, and let `x₄` satisfy the Vieta relations
`2αβ − 1 = −α²(x₁ + x₂ + x₃ + x₄)` and `β² + 2αγ = α² e₂(x₁, …, x₄)`. If `P₁ + P₂` does not lie
over `x₃`, then `(P₁ + P₂) + P₃ = (x₄, −(αx₄² + βx₄ + γ))`. -/
theorem add_add_eq_neg {α β γ x₁ x₂ x₃ x₄ : K}
    (h₁ : E.OnCurve x₁ (α * x₁ ^ 2 + β * x₁ + γ)) (h₂ : E.OnCurve x₂ (α * x₂ ^ 2 + β * x₂ + γ))
    (h₃ : E.OnCurve x₃ (α * x₃ ^ 2 + β * x₃ + γ)) (h₁₂ : x₁ ≠ x₂)
    (hs₁ : 2 * α * β - 1 = -α ^ 2 * (x₁ + x₂ + x₃ + x₄))
    (hs₂ : β ^ 2 + 2 * α * γ = α ^ 2 * (x₁ * x₂ + x₁ * x₃ + x₁ * x₄ + x₂ * x₃ + x₂ * x₄ + x₃ * x₄))
    (hQ : (α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂ ≠ x₃) :
    ∃ h, (some x₁ _ h₁ + some x₂ _ h₂ : Point E) + some x₃ _ h₃ =
      some x₄ (-(α * x₄ ^ 2 + β * x₄ + γ)) h := by
  -- the chord `P₁P₂` has slope `λ = α(x₁ + x₂) + β`
  obtain ⟨hQc, eQ⟩ := addSome_of_slope (l := α * (x₁ + x₂) + β) h₁ h₂ h₁₂ (by grind)
  rw [some_add_some, eQ]
  -- `P₁ + P₂`, `P₃` and `P₄` are collinear, on the line of slope `α(x₃ + x₄) + β`
  have hcol : (α * x₃ ^ 2 + β * x₃ + γ)
      - ((α * (x₁ + x₂) + β) * (x₁ - ((α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂))
        - (α * x₁ ^ 2 + β * x₁ + γ))
      = (α * (x₃ + x₄) + β) * (x₃ - ((α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂)) := by grind
  obtain ⟨hR, eR⟩ := addSome_of_slope (l := α * (x₃ + x₄) + β) hQc h₃ hQ hcol
  rw [some_add_some, eR]
  have hx : (α * (x₃ + x₄) + β) ^ 2 - ((α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂) - x₃ = x₄ := by grind
  refine ⟨?_, ?_⟩
  · have hy : (α * (x₃ + x₄) + β) * (((α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂)
        - ((α * (x₃ + x₄) + β) ^ 2 - ((α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂) - x₃))
        - ((α * (x₁ + x₂) + β) * (x₁ - ((α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂))
          - (α * x₁ ^ 2 + β * x₁ + γ)) = -(α * x₄ ^ 2 + β * x₄ + γ) := by grind
    rw [hy, hx] at hR
    exact hR
  · rw [some_eq_some]
    exact ⟨hx, by grind⟩

/-- **Associativity, generic case.** Let `P₁, P₂, P₃` be affine points of `E` with pairwise
distinct `x`-coordinates, such that `P₁ + P₂` does not lie over `x₃` and `P₂ + P₃` does not lie
over `x₁` (the `x`-coordinate of `Pᵢ + Pⱼ` being `λᵢⱼ² − xᵢ − xⱼ`). Then
`(P₁ + P₂) + P₃ = P₁ + (P₂ + P₃)`. -/
theorem add_assoc_generic {x₁ y₁ x₂ y₂ x₃ y₃ : K}
    (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) (h₃ : E.OnCurve x₃ y₃)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃)
    (hQ : E.slope x₁ y₁ x₂ y₂ ^ 2 - x₁ - x₂ ≠ x₃)
    (hR : E.slope x₂ y₂ x₃ y₃ ^ 2 - x₂ - x₃ ≠ x₁) :
    (some x₁ y₁ h₁ + some x₂ y₂ h₂ : Point E) + some x₃ y₃ h₃ =
      some x₁ y₁ h₁ + (some x₂ y₂ h₂ + some x₃ y₃ h₃) := by
  obtain ⟨α, β, γ, x₄, -, e₁, e₂, e₃, hs₁, hs₂⟩ := E.exists_fourth_point h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hQ
  subst e₁ e₂ e₃
  have s₁₂ := slope_eq_of (l := α * (x₁ + x₂) + β) h₁ h₂ h₁₂ (by grind)
  have s₂₃ := slope_eq_of (l := α * (x₂ + x₃) + β) h₂ h₃ h₂₃ (by grind)
  rw [s₁₂] at hQ
  rw [s₂₃] at hR
  obtain ⟨hL, eL⟩ := add_add_eq_neg (x₄ := x₄) h₁ h₂ h₃ h₁₂ hs₁ hs₂ hQ
  obtain ⟨hM, eM⟩ := add_add_eq_neg (x₄ := x₄) h₂ h₃ h₁ h₂₃ (by grind) (by grind) hR
  rw [eL, add_comm (some x₁ _ h₁), eM]

end Point

end Foundations.Langlands.Elliptic
