import Foundations.Langlands.Elliptic.Assoc
import Foundations.Langlands.Elliptic.Cancel

/-!
# Associativity in all cases

The generic proof in `Assoc` interpolated three points by a parabola `y = αx² + βx + γ` and
used only two of the four Vieta relations of the quartic
`(αx² + βx + γ)² − (x³ + ax + b) = α² (x − x₁)(x − x₂)(x − x₃)(x − x₄)`. Using **all four**
(`Curve.Parabola`) the key lemma `(P₁ + P₂) + P₃ = −P₄` becomes a purely polynomial statement
that needs no distinctness at all (`Point.add_add_eq_neg_of_parabola`): whenever neither
addition produces `O`, the slopes `α(x₁ + x₂) + β` and `α(x₃ + x₄) + β` satisfy both chord
relations, which characterise the slope of the addition law even for tangents
(`Curve.slope_eq_of_rel`).

What remains is to find such a parabola. For three points with distinct `x`-coordinates it is
the interpolating parabola (`Curve.parabola_of_distinct`); for a doubled point `D` and a
further point `E` it is the parabola through `E` tangent to the curve at `D`
(`Curve.parabola_of_double`). In both cases `α ≠ 0` exactly because the three points are not
on a line, i.e. because the sum is not `O`.

All other configurations reduce to the cancellation law of `Cancel`
(`P + (−P + Q) = Q`), negation being additive, and commutativity:
a partial sum or the total sum is `O`, or `P₃ = ±P₁`. The result is **associativity of the
chord–tangent law for all points** (`Point.add_assoc`), and with `Weierstrass` and `Cancel`,
the points of `E` form an abelian group (`Point.instAddAbGroup`, in `Group`).
-/

namespace Foundations.Langlands.Elliptic

universe u

variable {K : Type u} [Lean.Grind.Field K]

namespace Curve

variable (E : Curve K)

/-- **Parabola data.** The four Vieta relations saying that
`(αx² + βx + γ)² − (x³ + ax + b) = α² (x − x₁)(x − x₂)(x − x₃)(x − x₄)` as polynomials in `x`. -/
structure Parabola (α β γ x₁ x₂ x₃ x₄ : K) : Prop where
  /-- The `x³` coefficient. -/
  s₁ : 2 * α * β - 1 = -α ^ 2 * (x₁ + x₂ + x₃ + x₄)
  /-- The `x²` coefficient. -/
  s₂ : β ^ 2 + 2 * α * γ = α ^ 2 * (x₁ * x₂ + x₁ * x₃ + x₁ * x₄ + x₂ * x₃ + x₂ * x₄ + x₃ * x₄)
  /-- The `x` coefficient. -/
  s₃ : 2 * β * γ - E.a = -α ^ 2 * (x₁ * x₂ * x₃ + x₁ * x₂ * x₄ + x₁ * x₃ * x₄ + x₂ * x₃ * x₄)
  /-- The constant coefficient. -/
  s₄ : γ ^ 2 - E.b = α ^ 2 * (x₁ * x₂ * x₃ * x₄)

variable {E}

/-- Parabola data are invariant under the cyclic permutation `(x₁, x₂, x₃) ↦ (x₂, x₃, x₁)`. -/
theorem Parabola.cycle {α β γ x₁ x₂ x₃ x₄ : K} (h : E.Parabola α β γ x₁ x₂ x₃ x₄) :
    E.Parabola α β γ x₂ x₃ x₁ x₄ :=
  ⟨by grind [h.s₁], by grind [h.s₂], by grind [h.s₃], by grind [h.s₄]⟩

/-- Parabola data are invariant under swapping `x₂` and `x₃`. -/
theorem Parabola.swap {α β γ x₁ x₂ x₃ x₄ : K} (h : E.Parabola α β γ x₁ x₂ x₃ x₄) :
    E.Parabola α β γ x₁ x₃ x₂ x₄ :=
  ⟨by grind [h.s₁], by grind [h.s₂], by grind [h.s₃], by grind [h.s₄]⟩

/-- On a parabola with full Vieta data, the chord slope `α(x₁ + x₂) + β` satisfies the second
chord relation, also when `x₁ = x₂`. -/
theorem Parabola.rel {α β γ x₁ x₂ x₃ x₄ y₁ y₂ : K} (h : E.Parabola α β γ x₁ x₂ x₃ x₄)
    (hy₁ : y₁ = α * x₁ ^ 2 + β * x₁ + γ) (hy₂ : y₂ = α * x₂ ^ 2 + β * x₂ + γ) :
    (α * (x₁ + x₂) + β) * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a := by
  have := h.s₁; have := h.s₂; have := h.s₃
  subst hy₁ hy₂
  grind

/-- `X + Y = 0` gives `X = −Y`. -/
theorem eq_neg_of_add {X Y : K} (h : X + Y = 0) : X = -Y := by grind

/-- `X − Y = 0` gives `X = Y`. -/
theorem eq_of_sub {X Y : K} (h : X - Y = 0) : X = Y := by grind

/-- For `α ≠ 0` the equation `α² (x + s) = c` has a solution `x`. -/
theorem exists_sq_mul_add {α s c : K} (h : α ≠ 0) : ∃ x : K, α ^ 2 * (x + s) = c := by
  have h2 : α ^ 2 ≠ 0 := by grind
  exact ⟨c / α ^ 2 - s, by grind⟩

/-- Rearranging the first Vieta relation. -/
theorem vieta_one {α β x s : K} (e : α ^ 2 * (x + s) = 1 - 2 * α * β) :
    2 * α * β - 1 = -α ^ 2 * (s + x) := by grind

/-- A linear polynomial `v t + w` vanishing at two distinct points is zero. -/
theorem linear_eq_zero {v w t₁ t₂ : K} (k₁ : v * t₁ + w = 0) (k₂ : v * t₂ + w = 0)
    (d : t₁ ≠ t₂) : v = 0 ∧ w = 0 := by
  have d' : t₁ - t₂ ≠ 0 := fun h => d (by grind)
  have : v * (t₁ - t₂) = 0 := by grind
  have hv : v = 0 := by grind
  exact ⟨hv, by grind⟩

/-- A quadratic `u t² + v t + w` with a double root at `t₁` and a root at `t₃ ≠ t₁` is zero. -/
theorem quadratic_eq_zero {u v w t₁ t₃ : K} (k₁ : u * t₁ ^ 2 + v * t₁ + w = 0)
    (k₂ : 2 * u * t₁ + v = 0) (k₃ : u * t₃ ^ 2 + v * t₃ + w = 0) (d : t₁ ≠ t₃) :
    u = 0 ∧ v = 0 ∧ w = 0 := by
  have d' : (t₃ - t₁) ^ 2 ≠ 0 := by
    have : t₃ - t₁ ≠ 0 := fun h => d (by grind)
    grind
  have : u * (t₃ - t₁) ^ 2 = 0 := by grind
  have hu : u = 0 := by grind
  subst hu
  have hv : v = 0 := by grind
  exact ⟨rfl, hv, by grind⟩

/-- On a parabola the chord slope is `α(x₁ + x₂) + β`: `y₂ − y₁ = (α(x₁ + x₂) + β)(x₂ − x₁)`. -/
theorem chord_of_parabola {α β γ x₁ x₂ y₁ y₂ : K}
    (hy₁ : y₁ = α * x₁ ^ 2 + β * x₁ + γ) (hy₂ : y₂ = α * x₂ ^ 2 + β * x₂ + γ) :
    y₂ - y₁ = (α * (x₁ + x₂) + β) * (x₂ - x₁) := by
  subst hy₁ hy₂; grind

/-- The third point of the chord `P₁P₂` has the same `x`-coordinate as the third point of the
chord `P₃P₄`. -/
theorem Parabola.third {α β γ x₁ x₂ x₃ x₄ : K} (h : E.Parabola α β γ x₁ x₂ x₃ x₄) :
    (α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂ = (α * (x₃ + x₄) + β) ^ 2 - x₃ - x₄ := by
  have := h.s₁; grind

/-- The second chord relation for the pair `x₃, x₄` (slope `α(x₃ + x₄) + β`). -/
theorem Parabola.rel₃₄ {α β γ x₁ x₂ x₃ x₄ y₃ y₄ : K} (h : E.Parabola α β γ x₁ x₂ x₃ x₄)
    (hy₃ : y₃ = α * x₃ ^ 2 + β * x₃ + γ) (hy₄ : y₄ = α * x₄ ^ 2 + β * x₄ + γ) :
    (α * (x₃ + x₄) + β) * (y₃ + y₄) = x₃ ^ 2 + x₃ * x₄ + x₄ ^ 2 + E.a := by
  have := h.s₁; have := h.s₂; have := h.s₃
  subst hy₃ hy₄
  grind

/-- **Collinearity.** `P₁ + P₂` lies on the line through `P₃` with slope `α(x₃ + x₄) + β`. -/
theorem Parabola.collinear {α β γ x₁ x₂ x₃ x₄ y₁ y₃ : K} (h : E.Parabola α β γ x₁ x₂ x₃ x₄)
    (hy₁ : y₁ = α * x₁ ^ 2 + β * x₁ + γ) (hy₃ : y₃ = α * x₃ ^ 2 + β * x₃ + γ) :
    (α * (x₁ + x₂) + β) * (x₁ - ((α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂)) - y₁
      = y₃ + (α * (x₃ + x₄) + β) * (((α * (x₁ + x₂) + β) ^ 2 - x₁ - x₂) - x₃) := by
  have := h.s₁; have := h.s₂
  subst hy₁ hy₃; grind

/-- A point on the line through `(x₃, y₃)` with slope `n` gives the first chord relation. -/
theorem chord_of_collinear {n x₃ y₃ xQ yQ : K} (h : yQ = y₃ + n * (xQ - x₃)) :
    y₃ - yQ = n * (x₃ - xQ) := by grind

/-- The `x`-coordinate of the third point. -/
theorem third_x {n x₃ x₄ xQ : K} (h : xQ = n ^ 2 - x₃ - x₄) : n ^ 2 - xQ - x₃ = x₄ := by grind

/-- The `y`-coordinate of the third point. -/
theorem third_y {n x₃ x₄ xQ y₃ y₄ yQ : K} (h : xQ = n ^ 2 - x₃ - x₄)
    (hQ : yQ = y₃ + n * (xQ - x₃)) (h₄ : y₄ - y₃ = n * (x₄ - x₃)) :
    n * (xQ - (n ^ 2 - xQ - x₃)) - yQ = -y₄ := by
  subst hQ; grind

variable (E)

/-- **The interpolating parabola, with all four Vieta relations.** Three points of `E` with
pairwise distinct `x`-coordinates whose sum `(P₁ + P₂) + P₃` is not `O` lie on a parabola
`y = αx² + βx + γ` with full parabola data `(α, β, γ, x₄)`. -/
theorem parabola_of_distinct [DecidableEq K] {x₁ y₁ x₂ y₂ x₃ y₃ : K}
    (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) (h₃ : E.OnCurve x₃ y₃)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃)
    (hS : (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : Point E) + Point.some x₃ y₃ h₃ ≠ 0) :
    ∃ α β γ x₄ : K, y₁ = α * x₁ ^ 2 + β * x₁ + γ ∧ y₂ = α * x₂ ^ 2 + β * x₂ + γ ∧
      y₃ = α * x₃ ^ 2 + β * x₃ + γ ∧ E.Parabola α β γ x₁ x₂ x₃ x₄ := by
  obtain ⟨α, β, γ, e₁, e₂, e₃⟩ := exists_parabola (y₁ := y₁) (y₂ := y₂) (y₃ := y₃) h₁₂ h₁₃ h₂₃
  have h₁' : E.OnCurve x₁ (α * x₁ ^ 2 + β * x₁ + γ) := e₁ ▸ h₁
  have h₂' : E.OnCurve x₂ (α * x₂ ^ 2 + β * x₂ + γ) := e₂ ▸ h₂
  have h₃' : E.OnCurve x₃ (α * x₃ ^ 2 + β * x₃ + γ) := e₃ ▸ h₃
  have D := E.second_divided_difference h₁₂ h₁₃ h₂₃ h₁' h₂' h₃'
  have hα : α ≠ 0 := by
    intro hα0
    apply hS
    have hn : ¬ (x₁ = x₂ ∧ y₁ + y₂ = 0) := fun h => h₁₂ h.1
    obtain ⟨hQ, eQ⟩ := Point.addSome_of_slope (l := β) h₁ h₂ h₁₂ (by subst hα0; grind)
    rw [Point.some_add_some, eQ, Point.some_add_some]
    apply (Point.addSome_eq_zero_iff _ _).2
    subst hα0
    have hx : β ^ 2 - x₁ - x₂ = x₃ := by grind
    exact ⟨hx, by grind⟩
  have hα2 : α ^ 2 ≠ 0 := by grind
  obtain ⟨x₄, e₄⟩ := exists_sq_mul_add (s := x₁ + x₂ + x₃) (c := 1 - 2 * α * β) hα
  have s₁ : 2 * α * β - 1 = -α ^ 2 * (x₁ + x₂ + x₃ + x₄) := by grind
  have s₂ : β ^ 2 + 2 * α * γ =
      α ^ 2 * (x₁ * x₂ + x₁ * x₃ + x₁ * x₄ + x₂ * x₃ + x₂ * x₄ + x₃ * x₄) := by grind
  -- the remaining remainder `v x + w` vanishes at `x₁` and `x₂`
  unfold OnCurve at h₁' h₂'
  have k : ∀ t : K, (α * t ^ 2 + β * t + γ) ^ 2 = t ^ 3 + E.a * t + E.b →
      (t - x₁) * (t - x₂) * (t - x₃) * (t - x₄) = 0 →
      (2 * β * γ - E.a + α ^ 2 * (x₁ * x₂ * x₃ + x₁ * x₂ * x₄ + x₁ * x₃ * x₄ + x₂ * x₃ * x₄)) * t
        + (γ ^ 2 - E.b - α ^ 2 * (x₁ * x₂ * x₃ * x₄)) = 0 := by
    intro t ht hp
    have : (2 * β * γ - E.a + α ^ 2 * (x₁ * x₂ * x₃ + x₁ * x₂ * x₄ + x₁ * x₃ * x₄ + x₂ * x₃ * x₄))
        * t + (γ ^ 2 - E.b - α ^ 2 * (x₁ * x₂ * x₃ * x₄))
        = ((α * t ^ 2 + β * t + γ) ^ 2 - (t ^ 3 + E.a * t + E.b))
          - α ^ 2 * ((t - x₁) * (t - x₂) * (t - x₃) * (t - x₄))
          - (β ^ 2 + 2 * α * γ - α ^ 2 * (x₁ * x₂ + x₁ * x₃ + x₁ * x₄ + x₂ * x₃ + x₂ * x₄ + x₃ * x₄))
            * t ^ 2
          - (2 * α * β - 1 + α ^ 2 * (x₁ + x₂ + x₃ + x₄)) * t ^ 3 := by grind
    rw [this, ht, hp, s₂, s₁]; grind
  have k₁ := k x₁ h₁' (by grind)
  have k₂ := k x₂ h₂' (by grind)
  obtain ⟨hv, hw⟩ := linear_eq_zero k₁ k₂ h₁₂
  exact ⟨α, β, γ, x₄, e₁, e₂, e₃, ⟨s₁, s₂, by rw [eq_neg_of_add hv]; grind, eq_of_sub hw⟩⟩

/-- **The tangent parabola.** If `D = (x₁, y₁)` with `y₁ ≠ 0` and `P₃ = (x₃, y₃)` with
`x₃ ≠ x₁` are points of `E` with `(D + D) + P₃ ≠ O`, there is a parabola through `P₃` tangent
to `E` at `D`, with full parabola data `(α, β, γ, x₄)` for the roots `x₁, x₁, x₃, x₄`. -/
theorem parabola_of_double [DecidableEq K] {x₁ y₁ x₃ y₃ : K}
    (h₁ : E.OnCurve x₁ y₁) (h₃ : E.OnCurve x₃ y₃) (hy : ¬ (x₁ = x₁ ∧ y₁ + y₁ = 0))
    (h₁₃ : x₁ ≠ x₃)
    (hS : (Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ : Point E) + Point.some x₃ y₃ h₃ ≠ 0) :
    ∃ α β γ x₄ : K, y₁ = α * x₁ ^ 2 + β * x₁ + γ ∧
      y₃ = α * x₃ ^ 2 + β * x₃ + γ ∧ E.Parabola α β γ x₁ x₁ x₃ x₄ := by
  obtain ⟨-, r₂⟩ := E.slope_rel h₁ h₁ hy
  generalize hl : E.slope x₁ y₁ x₁ y₁ = l at r₂
  have d : x₃ - x₁ ≠ 0 := fun h => h₁₃ (by grind)
  have d2 : (x₃ - x₁) ^ 2 ≠ 0 := by grind
  obtain ⟨α, eα⟩ : ∃ α : K, α * (x₃ - x₁) ^ 2 = y₃ - y₁ - l * (x₃ - x₁) :=
    ⟨(y₃ - y₁ - l * (x₃ - x₁)) / (x₃ - x₁) ^ 2, by grind⟩
  obtain ⟨β, hβ⟩ : ∃ β : K, β = l - 2 * α * x₁ := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : K, γ = y₁ - l * x₁ + α * x₁ ^ 2 := ⟨_, rfl⟩
  have e₁ : y₁ = α * x₁ ^ 2 + β * x₁ + γ := by subst hβ hγ; grind
  have e₃ : y₃ = α * x₃ ^ 2 + β * x₃ + γ := by subst hβ hγ; grind
  have c₁ : y₁ ^ 2 = x₁ ^ 3 + E.a * x₁ + E.b := h₁
  have c₃ : y₃ ^ 2 = x₃ ^ 3 + E.a * x₃ + E.b := h₃
  have hα : α ≠ 0 := by
    intro hα0
    apply hS
    obtain ⟨hQ, eQ⟩ := Point.addSome_of_rel (E := E) (l := l) h₁ h₁ hy (by grind) r₂
    rw [Point.some_add_some, eQ, Point.some_add_some]
    apply (Point.addSome_eq_zero_iff _ _).2
    rw [hα0] at eα
    have hy₃ : y₃ = y₁ + l * (x₃ - x₁) := by grind
    have hcub : (x₃ - x₁) ^ 2 * (x₃ - (l ^ 2 - x₁ - x₁)) = 0 := by
      have : (x₃ - x₁) ^ 2 * (x₃ - (l ^ 2 - x₁ - x₁))
          = (x₃ ^ 3 + E.a * x₃ + E.b) - (l * (x₃ - x₁) + y₁) ^ 2 := by grind
      rw [this, ← c₃, hy₃]; grind
    have hx : l ^ 2 - x₁ - x₁ = x₃ := by grind
    exact ⟨hx, by grind⟩
  have hα2 : α ^ 2 ≠ 0 := by grind
  clear hS hl hy
  obtain ⟨x₄, e₄⟩ := exists_sq_mul_add (s := x₁ + x₁ + x₃) (c := 1 - 2 * α * β) hα
  have s₁ : 2 * α * β - 1 = -α ^ 2 * (x₁ + x₁ + x₃ + x₄) := vieta_one e₄
  -- the remainder `u x² + v x + w`
  generalize hu : β ^ 2 + 2 * α * γ
    - α ^ 2 * (x₁ * x₁ + x₁ * x₃ + x₁ * x₄ + x₁ * x₃ + x₁ * x₄ + x₃ * x₄) = u
  generalize hv : 2 * β * γ - E.a
    + α ^ 2 * (x₁ * x₁ * x₃ + x₁ * x₁ * x₄ + x₁ * x₃ * x₄ + x₁ * x₃ * x₄) = v
  generalize hw : γ ^ 2 - E.b - α ^ 2 * (x₁ * x₁ * x₃ * x₄) = w
  have k : ∀ t : K, u * t ^ 2 + v * t + w
      = ((α * t ^ 2 + β * t + γ) ^ 2 - (t ^ 3 + E.a * t + E.b))
        - α ^ 2 * ((t - x₁) * (t - x₁) * (t - x₃) * (t - x₄))
        - (2 * α * β - 1 + α ^ 2 * (x₁ + x₁ + x₃ + x₄)) * t ^ 3 := by
    intro t; rw [← hu, ← hv, ← hw]; grind
  have k₁ : u * x₁ ^ 2 + v * x₁ + w = 0 := by rw [k, ← e₁, ← c₁, s₁]; grind
  have k₃ : u * x₃ ^ 2 + v * x₃ + w = 0 := by rw [k, ← e₃, ← c₃, s₁]; grind
  -- the derivative of the remainder at `x₁` vanishes: tangency
  have k₂ : 2 * u * x₁ + v = 0 := by
    have : 2 * u * x₁ + v = 2 * (α * x₁ ^ 2 + β * x₁ + γ) * (2 * α * x₁ + β)
        - (3 * x₁ ^ 2 + E.a) - 3 * (2 * α * β - 1 + α ^ 2 * (x₁ + x₁ + x₃ + x₄)) * x₁ ^ 2 := by
      rw [← hu, ← hv]; grind
    rw [this, ← e₁, s₁]
    have : 2 * α * x₁ + β = l := by subst hβ; grind
    rw [this]; grind
  obtain ⟨u0, v0, w0⟩ := quadratic_eq_zero k₁ k₂ k₃ h₁₃
  clear k k₁ k₂ k₃
  exact ⟨α, β, γ, x₄, e₁, e₃, ⟨s₁, eq_of_sub (hu.trans u0),
    by rw [eq_neg_of_add (hv.trans v0)]; grind, eq_of_sub (hw.trans w0)⟩⟩

end Curve

namespace Point

variable {E : Curve K} [DecidableEq K]

/-- **Key lemma, all configurations: `(P₁ + P₂) + P₃ = −P₄`.** Let `P₁, P₂, P₃` lie on the
parabola `y = αx² + βx + γ` with full parabola data `(α, β, γ, x₄)`. If neither `P₁ + P₂` nor
`(P₁ + P₂) + P₃` is `O`, then `(P₁ + P₂) + P₃ = (x₄, −(αx₄² + βx₄ + γ))`. No distinctness of
the points is assumed. -/
theorem add_add_eq_neg_of_parabola {α β γ x₁ x₂ x₃ x₄ y₁ y₂ y₃ : K}
    (hP : E.Parabola α β γ x₁ x₂ x₃ x₄)
    (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) (h₃ : E.OnCurve x₃ y₃)
    (hy₁ : y₁ = α * x₁ ^ 2 + β * x₁ + γ) (hy₂ : y₂ = α * x₂ ^ 2 + β * x₂ + γ)
    (hy₃ : y₃ = α * x₃ ^ 2 + β * x₃ + γ)
    (hQ : (some x₁ y₁ h₁ + some x₂ y₂ h₂ : Point E) ≠ 0)
    (hS : (some x₁ y₁ h₁ + some x₂ y₂ h₂ : Point E) + some x₃ y₃ h₃ ≠ 0) :
    ∃ h, (some x₁ y₁ h₁ + some x₂ y₂ h₂ : Point E) + some x₃ y₃ h₃ =
      some x₄ (-(α * x₄ ^ 2 + β * x₄ + γ)) h := by
  have hn : ¬ (x₁ = x₂ ∧ y₁ + y₂ = 0) := fun h =>
    hQ ((addSome_eq_zero_iff h₁ h₂).2 h)
  obtain ⟨hQc, eQ⟩ := addSome_of_rel (l := α * (x₁ + x₂) + β) h₁ h₂ hn (Curve.chord_of_parabola hy₁ hy₂)
    (hP.rel hy₁ hy₂)
  rw [some_add_some, eQ] at hS ⊢
  rw [some_add_some] at hS ⊢
  -- the line through `P₃` and `P₄` has slope `n` and passes through `P₁ + P₂`
  have C₂ := hP.third
  have C₁ := hP.collinear hy₁ hy₃
  have F₁ := hP.rel₃₄ (y₄ := α * x₄ ^ 2 + β * x₄ + γ) hy₃ rfl
  have F₅ := Curve.chord_of_parabola (x₁ := x₃) (x₂ := x₄) (y₂ := α * x₄ ^ 2 + β * x₄ + γ) hy₃ rfl
  have r₂ := E.chain_rel F₁ C₂ C₁ F₅
  have hn' := fun h => hS ((addSome_eq_zero_iff _ _).2 h)
  obtain ⟨hR, eR⟩ := addSome_of_rel (l := α * (x₃ + x₄) + β) hQc h₃ hn'
    (Curve.chord_of_collinear C₁) r₂
  rw [eR]
  have hx := Curve.third_x C₂
  have hy := Curve.third_y C₂ C₁ F₅
  refine ⟨?_, ?_⟩
  · rw [hy, hx] at hR; exact hR
  · rw [some_eq_some]; exact ⟨hx, hy⟩

omit [DecidableEq K] in
/-- `−(−P) = P`, in instance notation. -/
theorem neg_neg' (P : Point E) : -(-P) = P := neg_neg P

/-- If `P + Q = O` then `Q = −P`. -/
theorem eq_neg_of_add_eq_zero {P Q : Point E} (h : P + Q = 0) : Q = -P := by
  have := add_neg_add_cancel (-P) Q
  rw [neg_neg', h, add_zero] at this
  exact this.symm

/-- `(Q + P) + (−P) = Q`. -/
theorem add_add_neg_cancel (Q P : Point E) : (Q + P) + -P = Q := by
  rw [add_comm, add_comm Q]
  have := add_neg_add_cancel (-P) Q
  rwa [neg_neg'] at this

end Point

end Foundations.Langlands.Elliptic
