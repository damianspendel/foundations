import Foundations.Geometry.CartesianModel

/-!
# Euclid I.1, and why the rational plane is not enough

The very first proposition of Euclid's *Elements* reads: *on a given finite
straight line to construct an equilateral triangle.* Euclid draws the circle
with centre `A` through `B` and the circle with centre `B` through `A`, and
takes for `C` "the point in which the circles cut one another". He never
proves that there is such a point. Two thousand years later this gap, noticed
by Leibniz among others, became one of the motivations for Hilbert's axiom of
completeness and Dedekind's analysis of continuity.

In coordinates the gap is plain to see. For `A = (0, 0)` and `B = (1, 0)` the
two circles meet in `(1/2, ±√3/2)`. In the **real** plane these points exist,
because the reals have square roots (`euclid_I_1`). In the **rational** plane —
the plane of all points with rational coordinates, already infinitely dense,
and with all the same definitions — they do not, because `√3` is irrational
(`no_equilateral_rat`). The circles pass "through" each other without meeting.

So the rational plane satisfies most of Tarski's axioms (all the ones proved in
`CartesianModel.lean` for every ordered field), but fails:

* **segment construction**: the diagonal of the unit square, of length `√2`,
  cannot be laid off along the `x`-axis (`rat_not_segment_construction`);
* **continuity**: the points of the `x`-axis with `x² < 2` and those with
  `x² > 2` are separated by no rational point (`rat_not_continuous`).

The moral, which runs through modern geometry from Descartes to Hilbert, is
that a plane is fixed by its number field: the "same" axioms of incidence and
order yield different spaces over `ℚ`, over the constructible numbers, over the
real algebraic numbers, or over `ℝ`, and Euclid's constructions tacitly assume
enough of them.
-/

set_option linter.unusedSectionVars false

namespace Foundations.Geometry

open Lean.Grind Foundations.Numbers

/-! ## Equilateral triangles -/

section Equilateral

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- Collinear points have vanishing "cross product": `B a b c` implies
`(b − a) × (c − a) = 0`. -/
theorem Pt.cross_of_bet {a b c : Pt K} (h : Pt.Bet a b c) :
    (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x) = 0 := by
  obtain ⟨t, -, -, h₁, h₂⟩ := h
  rw [h₁, h₂]; grind

/-- Over any ordered field containing a square root of `3`, every segment `ab` is the side
of an equilateral triangle `abc`; for `a ≠ b` the apex `c` is off the line `ab`. -/
theorem equilateral_of_sqrt3 {r : K} (hr : r * r = 3) (a b : Pt K) :
    ∃ c : Pt K, Pt.Cong a b a c ∧ Pt.Cong a b b c ∧
      (a ≠ b → ¬ Pt.Bet a c b ∧ ¬ Pt.Bet c a b ∧ ¬ Pt.Bet a b c) := by
  refine ⟨⟨(a.x + b.x) / 2 - r / 2 * (b.y - a.y), (a.y + b.y) / 2 + r / 2 * (b.x - a.x)⟩,
    ?_, ?_, ?_⟩
  · unfold Pt.Cong Pt.d2; dsimp only; grind
  · unfold Pt.Cong Pt.d2; dsimp only; grind
  · intro hab
    have hD := Pt.d2_pos hab
    unfold Pt.d2 at hD
    have hr0 : r ≠ 0 := by intro h; rw [h] at hr; grind
    -- the apex is off the line: the "cross product" of `b − a` and `c − a` is `(r/2)|ab|² ≠ 0`
    have hcross : (b.x - a.x) * ((a.y + b.y) / 2 + r / 2 * (b.x - a.x) - a.y) -
        (b.y - a.y) * ((a.x + b.x) / 2 - r / 2 * (b.y - a.y) - a.x) ≠ 0 := by
      intro h0
      have : r * ((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y)) = 0 := by grind
      have : (a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y) = 0 := by grind
      grind
    refine ⟨fun h => hcross ?_, fun h => hcross ?_, fun h => hcross ?_⟩
    · have := Pt.cross_of_bet h; dsimp only at this; grind
    · have := Pt.cross_of_bet h; dsimp only at this; grind
    · have := Pt.cross_of_bet h; dsimp only at this; grind

/-- **Euclid, Elements I.1.** In the real plane, on every segment `ab` there is an
equilateral triangle `abc` (non-degenerate when `a ≠ b`). The proof needs `√3`,
supplied by the existence of square roots in `ℝ` — the continuity Euclid assumed. -/
theorem euclid_I_1 (a b : Pt R) :
    ∃ c : Pt R, Pt.Cong a b a c ∧ Pt.Cong a b b c ∧
      (a ≠ b → ¬ Pt.Bet a c b ∧ ¬ Pt.Bet c a b ∧ ¬ Pt.Bet a b c) := by
  obtain ⟨r, _, hr⟩ := R.exists_sqrt (z := 3) (by grind)
  exact equilateral_of_sqrt3 hr a b

end Equilateral

/-! ## The irrationality of √3 -/

/-- No natural number squared is three times a positive square (infinite descent). -/
theorem nat_sq_ne_three_sq : ∀ b : Nat, 0 < b → ∀ a : Nat, a * a ≠ 3 * (b * b) := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro hb a h
    obtain ⟨c, hc | hc | hc⟩ : ∃ c, a = 3 * c ∨ a = 3 * c + 1 ∨ a = 3 * c + 2 := ⟨a / 3, by omega⟩
    · subst hc
      have h' : b * b = 3 * (c * c) := by grind
      obtain ⟨e, he | he | he⟩ : ∃ e, b = 3 * e ∨ b = 3 * e + 1 ∨ b = 3 * e + 2 :=
        ⟨b / 3, by omega⟩
      · subst he
        exact ih e (by omega) (by omega) c (by grind)
      · subst he; grind
      · subst he; grind
    · subst hc; grind
    · subst hc; grind

/-- **Irrationality of √3.** No rational number squares to `3`. -/
theorem sqrt_three_irrational : ¬ ∃ q : Q, q * q = 3 := by
  rintro ⟨q, hq⟩
  induction q using Q.ind with | h n d hd => ?_
  simp only [Q.mk_mul, Q.ofNat_def, Q.mk_eq_mk] at hq
  have hq' : n * n = 3 * (d * d) := by grind
  have h1 : (n * n).natAbs = (3 * (d * d)).natAbs := by rw [hq']
  simp only [Int.natAbs_mul] at h1
  exact nat_sq_ne_three_sq d.natAbs (by omega) n.natAbs h1

/-! ## The rational plane -/

/-- **Euclid I.1 fails in the rational plane.** No point with rational coordinates is
at (squared) distance `1` from both `(0, 0)` and `(1, 0)`: the two circles of Euclid's
construction do not meet in `ℚ²`. -/
theorem no_equilateral_rat :
    ¬ ∃ c : Pt Q, Pt.d2 ⟨0, 0⟩ c = 1 ∧ Pt.d2 ⟨1, 0⟩ c = 1 := by
  rintro ⟨c, h₁, h₂⟩
  unfold Pt.d2 at h₁ h₂
  dsimp only at h₁ h₂
  have hx : c.x = 1 / 2 := by grind
  exact sqrt_three_irrational ⟨2 * c.y, by rw [hx] at h₁; grind⟩

/-- Restated with Tarski's equidistance: the unit segment from `(0,0)` to `(1,0)` is not
the side of any equilateral triangle in `ℚ²`. -/
theorem rat_no_equilateral_on_unit :
    ¬ ∃ c : Pt Q, Pt.Cong ⟨0, 0⟩ ⟨1, 0⟩ ⟨0, 0⟩ c ∧ Pt.Cong ⟨0, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ c := by
  rintro ⟨c, h₁, h₂⟩
  refine no_equilateral_rat ⟨c, ?_, ?_⟩
  · rw [← h₁]; unfold Pt.d2; dsimp only; grind
  · rw [← h₂]; unfold Pt.d2; dsimp only; grind

/-- **Segment construction fails in `ℚ²`**: on the ray from `(0,0)` through `(1,0)` one
cannot lay off, beyond `(1,0)`, a segment as long as the diagonal from `(0,0)` to
`(1,1)` — its length would be `√2`. -/
theorem rat_not_segment_construction :
    ¬ ∃ x : Pt Q, Pt.Bet ⟨0, 0⟩ ⟨1, 0⟩ x ∧ Pt.Cong ⟨1, 0⟩ x ⟨0, 0⟩ ⟨1, 1⟩ := by
  rintro ⟨x, ⟨t, -, -, h₁, h₂⟩, h⟩
  dsimp only at h₁ h₂
  unfold Pt.Cong Pt.d2 at h
  dsimp only at h
  have ht : t ≠ 0 := by intro h0; rw [h0] at h₁; grind
  have hy : x.y = 0 := by grind
  rw [hy] at h
  exact Q.sqrt_two_irrational ⟨x.x - 1, by grind⟩

section Cuts

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- Below a non-negative `r` with `r² < 2` there is room: some `r' > r` still has `r'² < 2`. -/
theorem exists_above_of_sq_lt_two {r : K} (hr : 0 ≤ r) (h : r * r < 2) :
    ∃ r', r < r' ∧ r' * r' < 2 := by
  have hd : (0 : K) < 2 * r + 3 := by grind
  have hd' : 2 * r + 3 ≠ 0 := by grind
  obtain ⟨δ0, δ1⟩ := div_mem_unit (u := 2 - r * r) (v := 2 * r + 3) (by grind)
    (by have := sq_nonneg' r; grind) hd
  have hδ : (2 - r * r) / (2 * r + 3) * (2 * r + 3) = 2 - r * r := by grind
  have hδpos : 0 < (2 - r * r) / (2 * r + 3) := by
    rcases Std.le_iff_lt_or_eq.1 δ0 with h' | h'
    · exact h'
    · rw [← h'] at hδ; grind
  have hsq := mul_le_of_le_one δ1 δ0
  refine ⟨r + (2 - r * r) / (2 * r + 3), by grind, ?_⟩
  grind

/-- Above a positive `r` with `r² > 2` there is room: some `0 < r' < r` still has
`r'² > 2`. -/
theorem exists_below_of_sq_gt_two {r : K} (hr : 0 < r) (h : 2 < r * r) :
    ∃ r', 0 < r' ∧ r' < r ∧ 2 < r' * r' := by
  have hr' : 2 * r ≠ 0 := by grind
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (r * r - 2) / (2 * r) := ⟨_, rfl⟩
  have e : δ * (2 * r) = r * r - 2 := by rw [hδ]; grind
  have hδpos : 0 < δ := by
    rw [hδ, Field.div_eq_mul_inv]
    exact OrderedRing.mul_pos (by grind) (Field.IsOrdered.inv_pos_iff.2 (by grind))
  have hδr : δ < r := by
    apply Classical.byContradiction
    intro hn
    have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : r ≤ δ) (by grind : (0 : K) ≤ r)
    grind
  have hsq := OrderedRing.mul_pos hδpos hδpos
  exact ⟨r - δ, by grind, by grind, by grind⟩

end Cuts

/-- From `B (u,0) (r,0) (v,0)` with `u < v`: `u ≤ r ≤ v`. -/
theorem bet_axis {u r v : Q} {s : Q} (huv : u < v)
    (h : Pt.Bet (⟨u, 0⟩ : Pt Q) ⟨r, s⟩ ⟨v, 0⟩) : u ≤ r ∧ r ≤ v ∧ s = 0 := by
  obtain ⟨t, t0, t1, h₁, h₂⟩ := h
  dsimp only at h₁ h₂
  have a := OrderedRing.mul_nonneg t0 (by grind : (0 : Q) ≤ v - u)
  have b := mul_le_of_le_one t1 (by grind : (0 : Q) ≤ v - u)
  exact ⟨by grind, by grind, by grind⟩

/-- **Continuity fails in `ℚ²`.** The points `(x, 0)` with `x ≥ 0`, `x² < 2` all
precede, as seen from the origin, the points `(y, 0)` with `y ≥ 0`, `y² > 2`; but no
rational point lies between the two families — the gap is at `√2`. -/
theorem rat_not_continuous :
    ¬ ∀ φ ψ : Pt Q → Prop, (∃ a, ∀ x y, φ x → ψ y → Pt.Bet a x y) →
      ∃ b, ∀ x y, φ x → ψ y → Pt.Bet x b y := by
  intro hcont
  let φ : Pt Q → Prop := fun p => p.y = 0 ∧ 0 ≤ p.x ∧ p.x * p.x < 2
  let ψ : Pt Q → Prop := fun p => p.y = 0 ∧ 0 ≤ p.x ∧ 2 < p.x * p.x
  have hlt : ∀ x y : Q, 0 ≤ x → 0 ≤ y → x * x < 2 → 2 < y * y → x < y := by
    intro x y hx hy h₁ h₂
    apply Classical.byContradiction
    intro hn
    have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : y ≤ x) hy
    have := OrderedRing.mul_le_mul_of_nonneg_right (by grind : y ≤ x) hx
    grind
  obtain ⟨b, hb⟩ := hcont φ ψ ⟨⟨0, 0⟩, fun x y hx hy => by
    obtain ⟨hx0, hx1, hx2⟩ := hx
    obtain ⟨hy0, hy1, hy2⟩ := hy
    have := hlt _ _ hx1 hy1 hx2 hy2
    exact Pt.bet_of_line (o := ⟨0, 0⟩) (w := ⟨1, 0⟩) (α := 0) (β := x.x) (γ := y.x)
      ⟨by grind, by grind⟩ ⟨by grind, by grind⟩ ⟨by grind, by grind⟩ (Or.inl ⟨hx1, by grind⟩)⟩
  have hφ1 : φ ⟨1, 0⟩ := ⟨rfl, by grind, by grind⟩
  have hψ2 : ψ ⟨2, 0⟩ := ⟨rfl, by grind, by grind⟩
  obtain ⟨hb1, hb2, hby⟩ := bet_axis (by grind) (show Pt.Bet ⟨1, 0⟩ ⟨b.x, b.y⟩ ⟨2, 0⟩ from hb _ _ hφ1 hψ2)
  have hne : b.x * b.x ≠ 2 := fun h => Q.sqrt_two_irrational ⟨b.x, h⟩
  rcases Std.lt_trichotomy (b.x * b.x) 2 with hlt2 | heq | hgt2
  · obtain ⟨r', hr', hr'2⟩ := exists_above_of_sq_lt_two (by grind) hlt2
    have hφ' : φ ⟨r', 0⟩ := ⟨rfl, by grind, hr'2⟩
    obtain ⟨h₁, -, -⟩ := bet_axis (by have := hlt r' 2 (by grind) (by grind) hr'2 (by grind); grind)
      (show Pt.Bet ⟨r', 0⟩ ⟨b.x, b.y⟩ ⟨2, 0⟩ from hb _ _ hφ' hψ2)
    grind
  · exact hne heq
  · obtain ⟨r', hr'0, hr', hr'2⟩ := exists_below_of_sq_gt_two (by grind) hgt2
    have hψ' : ψ ⟨r', 0⟩ := ⟨rfl, by grind, hr'2⟩
    obtain ⟨-, h₂, -⟩ := bet_axis (by have := hlt 1 r' (by grind) (by grind) (by grind) hr'2; grind)
      (show Pt.Bet ⟨1, 0⟩ ⟨b.x, b.y⟩ ⟨r', 0⟩ from hb _ _ hφ1 hψ')
    grind

/-- **The rational plane satisfies the field-independent Tarski axioms**: (A1)–(A3),
(A5)–(A10) hold in `ℚ²` (they hold over every ordered field). Together with the two
failures above, this locates exactly where the real numbers are needed. -/
theorem rat_plane_axioms :
    (∀ a b : Pt Q, Pt.Cong a b b a) ∧
    (∀ a b c : Pt Q, Pt.Cong a b c c → a = b) ∧
    (∀ a b : Pt Q, Pt.Bet a b a → a = b) ∧
    (∀ a b c p q : Pt Q, Pt.Bet a p c → Pt.Bet b q c → ∃ x, Pt.Bet p x b ∧ Pt.Bet q x a) ∧
    (∃ a b c : Pt Q, ¬ Pt.Bet a b c ∧ ¬ Pt.Bet b c a ∧ ¬ Pt.Bet c a b) ∧
    (∀ a b c d t : Pt Q, Pt.Bet a d t → Pt.Bet b d c → a ≠ d →
      ∃ x y, Pt.Bet a b x ∧ Pt.Bet a c y ∧ Pt.Bet x t y) :=
  ⟨Pt.cong_pseudo_refl, Pt.cong_identity, Pt.bet_identity, Pt.pasch, Pt.lower_dim, Pt.euclid⟩

end Foundations.Geometry
