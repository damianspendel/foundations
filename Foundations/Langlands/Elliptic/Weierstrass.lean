/-!
# Elliptic curves in short Weierstrass form: the chord–tangent law

**Diophantus** (*Arithmetica*, c. 250 AD) already produced new rational solutions of cubic
equations from old ones by drawing lines; **Fermat** and **Newton** made the method explicit:
a line through two rational points of a plane cubic meets it in a third rational point (the
*chord* construction), and the tangent at one rational point does the same (the *tangent*
construction). **Poincaré** (1901) recognised that these constructions make the set of rational
points into an abelian group once a point at infinity is taken as the identity, and asked
whether this group is finitely generated; **Mordell** (1922) proved that it is.

This file sets up the algebra over an arbitrary field `K` (any `Lean.Grind.Field` with decidable
equality, so that `grind` can do the field algebra):

* a curve `E : y² = x³ + a x + b` with the nondegeneracy hypothesis `4a³ + 27b² ≠ 0` and
  `2 ≠ 0`, `3 ≠ 0` in `K` (characteristic not `2` or `3`);
* its points: the affine solutions together with a point at infinity `O`;
* negation `(x, y) ↦ (x, −y)`;
* addition by the explicit chord–tangent formulas.

We prove that addition lands on the curve (this is built into the definition, via
`third_point_onCurve`), that `O` is a two-sided identity, that `P + (−P) = O`, and that addition
is commutative. Associativity is the subject of the next file, `Assoc`.

The formulas: for affine `P₁ = (x₁, y₁)`, `P₂ = (x₂, y₂)`,
* if `x₁ ≠ x₂`, the slope is `λ = (y₂ − y₁)/(x₂ − x₁)`;
* if `x₁ = x₂` and `y₁ + y₂ = 0`, the sum is `O`;
* if `x₁ = x₂` and `y₁ + y₂ ≠ 0` (then `y₁ = y₂ ≠ 0`), the tangent slope is
  `λ = (3x₁² + a)/(y₁ + y₂)` (that is, `(3x₁² + a)/(2y₁)`);

and then `x₃ = λ² − x₁ − x₂`, `y₃ = λ(x₁ − x₃) − y₁`.
-/

namespace Foundations.Langlands.Elliptic

universe u

/-- **Short Weierstrass curve.** An elliptic curve `y² = x³ + a x + b` over a field `K`, with
nonzero discriminant `4a³ + 27b² ≠ 0`, over a field in which `2` and `3` are nonzero. -/
structure Curve (K : Type u) [Lean.Grind.Field K] where
  /-- The coefficient of `x`. -/
  a : K
  /-- The constant coefficient. -/
  b : K
  /-- Nonsingularity: `4a³ + 27b² ≠ 0`. -/
  disc_ne : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0
  /-- The characteristic is not `2`. -/
  two_ne : (2 : K) ≠ 0
  /-- The characteristic is not `3`. -/
  three_ne : (3 : K) ≠ 0

variable {K : Type u} [Lean.Grind.Field K]

namespace Curve

variable (E : Curve K)

/-- The affine point `(x, y)` lies on the curve: `y² = x³ + a x + b`. -/
def OnCurve (x y : K) : Prop := y ^ 2 = x ^ 3 + E.a * x + E.b

/-- **Chord–tangent third point.** If `(x₁, y₁)` and `(x₂, y₂)` lie on the curve and the slope
`λ` satisfies `y₂ − y₁ = λ(x₂ − x₁)` and `λ(y₁ + y₂) = x₁² + x₁x₂ + x₂² + a` (which says that
the line of slope `λ` through `(x₁, y₁)` meets the curve again at `x₂`, with multiplicity two if
`x₁ = x₂`), then the reflected third intersection point
`(λ² − x₁ − x₂, λ(x₁ − x₃) − y₁)` lies on the curve. -/
theorem third_point_onCurve {x₁ y₁ x₂ y₂ l : K} (h₁ : E.OnCurve x₁ y₁)
    (r₁ : y₂ - y₁ = l * (x₂ - x₁)) (r₂ : l * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a) :
    E.OnCurve (l ^ 2 - x₁ - x₂) (l * (x₁ - (l ^ 2 - x₁ - x₂)) - y₁) := by
  unfold OnCurve at *
  grind

/-- Negation `(x, y) ↦ (x, −y)` preserves the curve. -/
theorem onCurve_neg {x y : K} (h : E.OnCurve x y) : E.OnCurve x (-y) := by
  unfold OnCurve at *; grind

/-- The *slope* used to add two affine points: the chord slope `(y₂ − y₁)/(x₂ − x₁)` if
`x₁ ≠ x₂`, and otherwise the tangent slope `(3x₁² + a)/(y₁ + y₂)`. -/
def slope [DecidableEq K] (x₁ y₁ x₂ y₂ : K) : K :=
  if x₁ = x₂ then (3 * x₁ ^ 2 + E.a) / (y₁ + y₂) else (y₂ - y₁) / (x₂ - x₁)

/-- For two points with different `x`-coordinates the slope satisfies both chord relations. -/
theorem slope_rel_ne [DecidableEq K] {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁)
    (h₂ : E.OnCurve x₂ y₂) (hx : x₁ ≠ x₂) :
    y₂ - y₁ = E.slope x₁ y₁ x₂ y₂ * (x₂ - x₁) ∧
      E.slope x₁ y₁ x₂ y₂ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a := by
  unfold OnCurve at *
  have hs : E.slope x₁ y₁ x₂ y₂ = (y₂ - y₁) / (x₂ - x₁) := by simp [slope, hx]
  have hne : x₂ - x₁ ≠ 0 := fun h => hx (by grind)
  have r₁ : y₂ - y₁ = E.slope x₁ y₁ x₂ y₂ * (x₂ - x₁) := by rw [hs]; grind
  refine ⟨r₁, ?_⟩
  have : (E.slope x₁ y₁ x₂ y₂ * (y₁ + y₂) - (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a)) * (x₂ - x₁) = 0 := by
    grind
  grind

/-- Two points on the curve with the same `x`-coordinate have `y₂ = ± y₁`; if `y₁ + y₂ ≠ 0`
then `y₂ = y₁`. -/
theorem eq_of_x_eq {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ + y₂ ≠ 0) : y₂ = y₁ := by
  unfold OnCurve at *
  have : (y₂ - y₁) * (y₁ + y₂) = 0 := by grind
  grind

/-- For two points with equal `x`-coordinate and `y₁ + y₂ ≠ 0` (a doubling) the tangent slope
satisfies both chord relations. -/
theorem slope_rel_eq [DecidableEq K] {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁)
    (h₂ : E.OnCurve x₂ y₂) (hx : x₁ = x₂) (hy : y₁ + y₂ ≠ 0) :
    y₂ - y₁ = E.slope x₁ y₁ x₂ y₂ * (x₂ - x₁) ∧
      E.slope x₁ y₁ x₂ y₂ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a := by
  have hy' := E.eq_of_x_eq h₁ h₂ hx hy
  have hs : E.slope x₁ y₁ x₂ y₂ = (3 * x₁ ^ 2 + E.a) / (y₁ + y₂) := by simp [slope, hx]
  subst hx hy'
  refine ⟨by grind, ?_⟩
  rw [hs]; grind

/-- The slope relations hold whenever the sum is not `O`, i.e. unless `x₁ = x₂` and
`y₁ + y₂ = 0`. -/
theorem slope_rel [DecidableEq K] {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁)
    (h₂ : E.OnCurve x₂ y₂) (h : ¬ (x₁ = x₂ ∧ y₁ + y₂ = 0)) :
    y₂ - y₁ = E.slope x₁ y₁ x₂ y₂ * (x₂ - x₁) ∧
      E.slope x₁ y₁ x₂ y₂ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a := by
  by_cases hx : x₁ = x₂
  · exact E.slope_rel_eq h₁ h₂ hx (fun hy => h ⟨hx, hy⟩)
  · exact E.slope_rel_ne h₁ h₂ hx

/-- The slope is symmetric in the two points. -/
theorem slope_comm [DecidableEq K] (x₁ y₁ x₂ y₂ : K) :
    E.slope x₁ y₁ x₂ y₂ = E.slope x₂ y₂ x₁ y₁ := by
  unfold slope
  by_cases hx : x₁ = x₂
  · subst hx; simp only [ite_true]; grind
  · have hx' : x₂ ≠ x₁ := fun h => hx h.symm
    simp only [hx, hx', ite_false]
    have h1 : x₂ - x₁ ≠ 0 := fun h => hx (by grind)
    have h2 : x₁ - x₂ ≠ 0 := fun h => hx (by grind)
    grind

end Curve

/-- **Points of an elliptic curve.** A point of `E` is either the point at infinity `O`
(`zero`) or an affine point `(x, y)` with `y² = x³ + a x + b`. -/
inductive Point (E : Curve K) where
  /-- The point at infinity `O`, the identity of the group law. -/
  | zero : Point E
  /-- An affine point `(x, y)` of the curve. -/
  | some (x y : K) (h : E.OnCurve x y) : Point E

namespace Point

variable {E : Curve K}

/-- Two affine points are equal iff their coordinates are. -/
theorem some_eq_some {x₁ y₁ x₂ y₂ : K} {h₁ : E.OnCurve x₁ y₁} {h₂ : E.OnCurve x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **Negation.** `−O = O` and `−(x, y) = (x, −y)`: reflection in the `x`-axis. -/
def neg : Point E → Point E
  | zero => zero
  | some x y h => some x (-y) (E.onCurve_neg h)

/-- Negation is an involution. -/
theorem neg_neg (P : Point E) : neg (neg P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    show some x (-(-y)) _ = some x y h
    rw [some_eq_some]; exact ⟨rfl, by grind⟩

variable [DecidableEq K]

/-- The sum of two affine points: `O` if `x₁ = x₂` and `y₁ + y₂ = 0`, and otherwise the
reflected third intersection of the chord (or tangent) with the curve. -/
def addSome (x₁ y₁ : K) (h₁ : E.OnCurve x₁ y₁) (x₂ y₂ : K) (h₂ : E.OnCurve x₂ y₂) : Point E :=
  if h : x₁ = x₂ ∧ y₁ + y₂ = 0 then zero
  else
    some (E.slope x₁ y₁ x₂ y₂ ^ 2 - x₁ - x₂)
      (E.slope x₁ y₁ x₂ y₂ * (x₁ - (E.slope x₁ y₁ x₂ y₂ ^ 2 - x₁ - x₂)) - y₁)
      (E.third_point_onCurve h₁ (E.slope_rel h₁ h₂ h).1 (E.slope_rel h₁ h₂ h).2)

/-- **Chord–tangent addition.** `O` is the identity, and two affine points are added by
`addSome`. That the result lies on the curve is part of the definition (it is
`Curve.third_point_onCurve`). -/
def add : Point E → Point E → Point E
  | zero, Q => Q
  | P, zero => P
  | some x₁ y₁ h₁, some x₂ y₂ h₂ => addSome x₁ y₁ h₁ x₂ y₂ h₂

/-- `P + Q` is the chord–tangent sum. -/
instance : Add (Point E) := ⟨add⟩
/-- `−P` is the reflection in the `x`-axis. -/
instance : Neg (Point E) := ⟨neg⟩
/-- `0` is the point at infinity `O`. -/
instance : Zero (Point E) := ⟨zero⟩

/-- Unfolding the sum of two affine points. -/
theorem some_add_some (x₁ y₁ x₂ y₂ : K) (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) :
    (some x₁ y₁ h₁ : Point E) + some x₂ y₂ h₂ = addSome x₁ y₁ h₁ x₂ y₂ h₂ := rfl

/-- The sum of two affine points that are not mirror images is the explicit affine point. -/
theorem addSome_of_not {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂)
    (h : ¬ (x₁ = x₂ ∧ y₁ + y₂ = 0)) :
    addSome x₁ y₁ h₁ x₂ y₂ h₂ = some (E.slope x₁ y₁ x₂ y₂ ^ 2 - x₁ - x₂)
      (E.slope x₁ y₁ x₂ y₂ * (x₁ - (E.slope x₁ y₁ x₂ y₂ ^ 2 - x₁ - x₂)) - y₁)
      (E.third_point_onCurve h₁ (E.slope_rel h₁ h₂ h).1 (E.slope_rel h₁ h₂ h).2) := by
  unfold addSome; split
  · contradiction
  · rfl

/-- **Left identity.** `O + P = P`. -/
theorem zero_add (P : Point E) : (0 : Point E) + P = P := rfl

/-- **Right identity.** `P + O = P`. -/
theorem add_zero (P : Point E) : P + (0 : Point E) = P := by
  cases P <;> rfl

/-- **Additive inverse.** `P + (−P) = O`. -/
theorem add_neg_self (P : Point E) : P + (-P) = (0 : Point E) := by
  cases P with
  | zero => rfl
  | some x y h =>
    show addSome x y h x (-y) (E.onCurve_neg h) = zero
    have h' : x = x ∧ y + -y = 0 := ⟨rfl, by grind⟩
    unfold addSome; split
    · rfl
    · contradiction

/-- **Commutativity.** `P + Q = Q + P`. -/
theorem add_comm (P Q : Point E) : P + Q = Q + P := by
  cases P with
  | zero => exact (add_zero Q).symm
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      rw [some_add_some, some_add_some]
      by_cases h : x₁ = x₂ ∧ y₁ + y₂ = 0
      · have h' : x₂ = x₁ ∧ y₂ + y₁ = 0 := ⟨h.1.symm, by grind⟩
        unfold addSome
        repeat' split
        all_goals first | rfl | contradiction
      · have h' : ¬ (x₂ = x₁ ∧ y₂ + y₁ = 0) := fun h' => h ⟨h'.1.symm, by grind⟩
        rw [addSome_of_not h₁ h₂ h, addSome_of_not h₂ h₁ h', some_eq_some, E.slope_comm x₂]
        have r := (E.slope_rel h₁ h₂ h).1
        refine ⟨by grind, ?_⟩
        grind

end Point

end Foundations.Langlands.Elliptic
