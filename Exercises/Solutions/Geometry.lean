import Foundations.Geometry.Pythagoras

/-!
# Exercises VI: Geometry

Problems on Part VI (`Foundations/Geometry`): reasoning from Tarski's axioms for plane
geometry, and computing in the Cartesian model `K²` (squared distances `d2`, dot products,
midpoints) and in `ℝ²` with true lengths `dist`.

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in `Exercises/Problems/Geometry.lean`.

*Tip for coordinate exercises.* After `unfold Pt.d2 Pt.midpoint` (and `dsimp only` to reduce
the coordinates of explicit points), most identities in an ordered field are closed by
`grind`, which normalises ring expressions and handles division by non-zero numerals.
-/

set_option linter.unusedSectionVars false

namespace Exercises.Geometry

open Lean.Grind Foundations.Numbers Foundations.Geometry

/-! ## Tarski's axioms -/

section Tarski

open TarskiPlane

variable {P : Type} [TarskiPlane P]

/-- **Exercise 6.1 (★) — Reversing both segments.** If `ab ≡ cd` then `ba ≡ dc`.

*Hint:* reverse one segment at a time.

*Uses:* `TarskiPlane.cong_left_comm`, `TarskiPlane.cong_right_comm`. -/
theorem cong_comm_both {a b c d : P} (h : Cong a b c d) : Cong b a d c := by
  -- SOLUTION
  exact cong_right_comm (cong_left_comm h)
  -- END

/-- **Exercise 6.2 (★★) — Three distinct points.** A Tarski plane has three pairwise distinct
points.

*Hint:* the lower-dimension axiom gives three points no one of which lies between the other
two. If two of them were equal, one of the trivial betweenness facts `B a b b` or `B a a b`
would contradict this.

*Uses:* `TarskiPlane.lower_dim`, `TarskiPlane.bet_trivial`, `TarskiPlane.bet_trivial'`. -/
theorem exists_three_distinct : ∃ a b c : P, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  -- SOLUTION
  obtain ⟨a, b, c, h₁, h₂, h₃⟩ := TarskiPlane.lower_dim (P := P)
  refine ⟨a, b, c, ?_, ?_, ?_⟩
  · rintro rfl; exact h₁ (bet_trivial' a c)
  · rintro rfl; exact h₁ (bet_trivial a b)
  · rintro rfl; exact h₃ (bet_trivial' a b)
  -- END

end Tarski

/-! ## The Cartesian plane -/

section Cartesian

open Pt

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- **Exercise 6.3 (★★) — Apollonius' theorem.** For any triangle `abc` with `m` the midpoint
of `ac`: `|ab|² + |bc|² = 2 |mb|² + |ac|² / 2`. (The median formula; with `b` the fourth vertex
of a parallelogram it becomes the parallelogram law.)

*Hint:* a pure computation in coordinates.

*Uses:* `Pt.d2`, `Pt.midpoint`, `grind`. -/
theorem apollonius (a b c : Pt K) :
    d2 a b + d2 b c = 2 * d2 (midpoint a c) b + d2 a c / 2 := by
  -- SOLUTION
  unfold d2 midpoint
  grind
  -- END

/-- **Exercise 6.4 (★★) — The median to the hypotenuse.** If the angle at `b` is right, the
midpoint `m` of the hypotenuse `ac` satisfies `4 |mb|² = |ac|²`: the median from the right
angle is half the hypotenuse.

*Hint:* by the converse of Thales' theorem, `|mb| = |ma|`; and `|ma|` is half of `|ac|`,
a short computation.

*Uses:* `Pt.thales_converse`, `Pt.d2`, `Pt.midpoint`. -/
theorem median_hypotenuse {a b c : Pt K} (h : RightAngle a b c) :
    4 * d2 (midpoint a c) b = d2 a c := by
  -- SOLUTION
  rw [thales_converse h]
  unfold d2 midpoint
  grind
  -- END

end Cartesian

/-! ## Lengths in ℝ² and the rational plane -/

section Lengths

open Pt OF

/-- **Exercise 6.5 (★★★) — The reverse triangle inequality.** In `ℝ²`, two sides of a
triangle differ by at most the third: `| |ab| − |bc| | ≤ |ac|`.

*Hint:* `abs_le` reduces the goal to two inequalities. Each one is an instance of the
triangle inequality for a suitable ordering of the three points, combined with the symmetry
of `dist`.

*Uses:* `Pt.triangle_inequality`, `Pt.dist_comm`, `OF.abs_le`. -/
theorem reverse_triangle (a b c : Pt R) : abs (dist a b - dist b c) ≤ dist a c := by
  -- SOLUTION
  have h₁ := triangle_inequality a c b
  have h₂ := triangle_inequality b a c
  rw [dist_comm c b] at h₁
  rw [dist_comm b a] at h₂
  exact abs_le.2 ⟨by grind, by grind⟩
  -- END

/-- **Exercise 6.6 (★★) — √12 is not rational, geometrically.** No point of the rational
plane on the x-axis is at squared distance `12` from the origin.

*Hint:* such a point `(q, 0)` would have `q² = 12`, and then `(q/2)² = 3`.

*Uses:* `sqrt_three_irrational`, `Pt.d2`. -/
theorem no_rat_point_sq_dist_12 : ¬ ∃ q : Q, d2 (⟨0, 0⟩ : Pt Q) ⟨q, 0⟩ = 12 := by
  -- SOLUTION
  rintro ⟨q, hq⟩
  unfold d2 at hq
  dsimp only at hq
  exact sqrt_three_irrational ⟨q / 2, by grind⟩
  -- END

end Lengths

end Exercises.Geometry
