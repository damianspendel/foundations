import Foundations.Geometry.Euclid

/-!
# Pythagoras, Thales, and the triangle inequality

With coordinates, the classical metric theorems of plane geometry become
algebraic identities — Descartes' programme in miniature. The "angle at `b`"
between `a` and `c` is measured by the **dot product** `(a − b)·(c − b)`; it is
a right angle when the dot product vanishes.

* **The law of cosines** `|ac|² = |ab|² + |bc|² − 2 (a − b)·(c − b)` is a polynomial
  identity, and **Pythagoras' theorem** (Euclid I.47) and its converse (I.48)
  follow at once.
* **Thales' theorem**: a point `b` sees a segment `ac` at a right angle exactly when
  it lies on the circle with diameter `ac`.
* **Heron's formula**, in the squared form `16·Area² = 4|ab|²|ac|² − (|ab|² + |ac|² − |bc|²)²`,
  expresses the area through the sides.

These hold over every ordered field. The **triangle inequality**
`|ac| ≤ |ab| + |bc|` concerns lengths themselves, i.e. square roots, so we prove it
in `ℝ²`, via the Cauchy–Schwarz inequality, which in turn comes from Lagrange's
identity `|u|²|v|² − (u·v)² = (u × v)²`.

Since the Babylonians (Plimpton 322, c. 1800 BC), Pythagoras' theorem has been
the bridge between geometry and arithmetic; it is also the reason why the
plane's distance is the square root of a sum of squares — the very formula with
which `CartesianModel.lean` *defined* congruence. Within the model, Pythagoras
is thus almost a tautology; its content lies in the fact that the model
satisfies Tarski's purely geometric axioms, from which (by Tarski's
completeness theorem) every such metric fact follows.
-/

set_option linter.unusedSectionVars false

namespace Foundations.Geometry

open Lean.Grind Foundations.Numbers

namespace Pt

section Identities

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- The **dot product** `(a − b)·(c − b)`, measuring the angle at `b`. -/
def dot (a b c : Pt K) : K := (a.x - b.x) * (c.x - b.x) + (a.y - b.y) * (c.y - b.y)

/-- The angle `abc` is a **right angle** when `(a − b)·(c − b) = 0`. -/
def RightAngle (a b c : Pt K) : Prop := dot a b c = 0

/-- **The law of cosines**: `|ac|² = |ab|² + |bc|² − 2 (a − b)·(c − b)`. -/
theorem law_of_cosines (a b c : Pt K) : d2 a c = d2 a b + d2 b c - 2 * dot a b c := by
  unfold d2 dot; grind

/-- **Pythagoras' theorem** (Euclid I.47): if the angle at `b` is right, then
`|ab|² + |bc|² = |ac|²`. -/
theorem pythagoras {a b c : Pt K} (h : RightAngle a b c) : d2 a b + d2 b c = d2 a c := by
  rw [law_of_cosines a b c]; unfold RightAngle at h; rw [h]; grind

/-- **The converse of Pythagoras** (Euclid I.48): if `|ab|² + |bc|² = |ac|²`, the angle at
`b` is right. -/
theorem pythagoras_converse {a b c : Pt K} (h : d2 a b + d2 b c = d2 a c) : RightAngle a b c := by
  have := law_of_cosines a b c
  unfold RightAngle; grind

/-- The **midpoint** of a segment. -/
def midpoint (a c : Pt K) : Pt K := ⟨(a.x + c.x) / 2, (a.y + c.y) / 2⟩

/-- The dot product at `b` in terms of the midpoint `m` of `ac`:
`(a − b)·(c − b) = |mb|² − |ma|²`. -/
theorem dot_eq_midpoint (a b c : Pt K) :
    dot a b c = d2 (midpoint a c) b - d2 (midpoint a c) a := by
  unfold dot d2 midpoint; dsimp only; grind

/-- **Thales' theorem**: a point on the circle with diameter `ac` sees `ac` at a right
angle. -/
theorem thales {a b c : Pt K} (h : d2 (midpoint a c) b = d2 (midpoint a c) a) :
    RightAngle a b c := by
  unfold RightAngle; rw [dot_eq_midpoint, h]; grind

/-- **Converse of Thales' theorem**: if the angle at `b` is right, `b` lies on the circle
with diameter `ac`. -/
theorem thales_converse {a b c : Pt K} (h : RightAngle a b c) :
    d2 (midpoint a c) b = d2 (midpoint a c) a := by
  unfold RightAngle at h; rw [dot_eq_midpoint] at h; grind

/-- The **oriented double area** of triangle `abc`: the cross product `(b − a) × (c − a)`. -/
def area2 (a b c : Pt K) : K := (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

/-- **Heron's formula** (squared form): `4·(2·Area)² = 4|ab|²|ac|² − (|ab|² + |ac|² − |bc|²)²`,
the area of a triangle expressed through its sides alone. -/
theorem heron (a b c : Pt K) :
    4 * (area2 a b c * area2 a b c) =
      4 * d2 a b * d2 a c - (d2 a b + d2 a c - d2 b c) * (d2 a b + d2 a c - d2 b c) := by
  unfold area2 d2; grind

/-- **Lagrange's identity** in the plane: `|u|²|v|² − (u·v)² = (u × v)²`, with `u = b − a`,
`v = c − b`. -/
theorem lagrange (a b c : Pt K) :
    d2 a b * d2 b c - dot a b c * dot a b c =
      ((b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x)) *
      ((b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x)) := by
  unfold d2 dot; grind

/-- If `0 ≤ q` and `p² ≤ q²` then `p ≤ q`. -/
theorem le_of_sq_le {p q : K} (hq : 0 ≤ q) (h : p * p ≤ q * q) : p ≤ q := by
  apply Classical.byContradiction
  intro hn
  have hp : 0 < p := by grind
  have h₁ := OrderedRing.mul_le_mul_of_nonneg_left (by grind : q ≤ p) hq
  have h₂ := OrderedRing.mul_lt_mul_of_pos_left (by grind : q < p) hp
  grind

end Identities

/-! ## Lengths in ℝ² -/

/-- The **distance** between two points of `ℝ²`: the non-negative square root of the
squared distance. -/
noncomputable def dist (a b : Pt R) : R := Classical.choose (R.exists_sqrt (d2_nonneg a b))

/-- Distances are non-negative. -/
theorem dist_nonneg (a b : Pt R) : 0 ≤ dist a b :=
  (Classical.choose_spec (R.exists_sqrt (d2_nonneg a b))).1

/-- The square of the distance is the squared distance. -/
theorem dist_mul_self (a b : Pt R) : dist a b * dist a b = d2 a b :=
  (Classical.choose_spec (R.exists_sqrt (d2_nonneg a b))).2

/-- Distance is symmetric. -/
theorem dist_comm (a b : Pt R) : dist a b = dist b a := by
  apply eq_of_sq_eq (dist_nonneg a b) (dist_nonneg b a)
  rw [dist_mul_self, dist_mul_self, d2_comm]

/-- **Pythagoras with lengths**: for a right angle at `b`, `|ab|² + |bc|² = |ac|²`. -/
theorem pythagoras_dist {a b c : Pt R} (h : RightAngle a b c) :
    dist a b * dist a b + dist b c * dist b c = dist a c * dist a c := by
  rw [dist_mul_self, dist_mul_self, dist_mul_self]; exact pythagoras h

/-- **The Cauchy–Schwarz inequality** in the plane: `(a − b)·(c − b) ≤ |ab| · |bc|`. -/
theorem cauchy_schwarz (a b c : Pt R) : dot a b c ≤ dist a b * dist b c := by
  apply le_of_sq_le (OrderedRing.mul_nonneg (dist_nonneg a b) (dist_nonneg b c))
  have hl := lagrange a b c
  have hs := sq_nonneg' ((b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x))
  have e : dist a b * dist b c * (dist a b * dist b c) = d2 a b * d2 b c := by
    rw [← dist_mul_self a b, ← dist_mul_self b c]; grind
  grind

/-- **The triangle inequality**: `|ac| ≤ |ab| + |bc|`. -/
theorem triangle_inequality (a b c : Pt R) : dist a c ≤ dist a b + dist b c := by
  apply le_of_sq_le (by have := dist_nonneg a b; have := dist_nonneg b c; grind)
  have hlc : d2 a c = d2 a b + d2 b c + 2 * ((b.x - a.x) * (c.x - b.x) + (b.y - a.y) * (c.y - b.y)) := by
    unfold d2; grind
  -- the angle term: use Cauchy–Schwarz for the reflected point
  have hcs' := cauchy_schwarz ⟨2 * b.x - a.x, 2 * b.y - a.y⟩ b c
  have e₁ : dot ⟨2 * b.x - a.x, 2 * b.y - a.y⟩ b c =
      (b.x - a.x) * (c.x - b.x) + (b.y - a.y) * (c.y - b.y) := by unfold dot; dsimp only; grind
  have e₂ : dist ⟨2 * b.x - a.x, 2 * b.y - a.y⟩ b = dist a b := by
    apply eq_of_sq_eq (dist_nonneg _ _) (dist_nonneg _ _)
    rw [dist_mul_self, dist_mul_self]; unfold d2; dsimp only; grind
  rw [e₁, e₂] at hcs'
  rw [dist_mul_self a c]
  have := dist_mul_self a b
  have := dist_mul_self b c
  grind

end Pt

end Foundations.Geometry
