import Foundations.Geometry.Pythagoras

/-!
# The Beltrami–Klein model of the hyperbolic plane

For two thousand years geometers tried to *prove* Euclid's fifth postulate from
the others. Saccheri (*Euclides ab omni naevo vindicatus*, 1733) assumed its
negation and derived consequence after strange consequence, until he declared
the hypothesis "repugnant to the nature of the straight line". Gauss, privately,
and then Bolyai (1832) and Lobachevsky (1829) took the opposite view: the
negation leads to a coherent **non-Euclidean geometry**, in which through a
point outside a line pass infinitely many lines not meeting it. But was it
coherent? That was settled only by *models*: Beltrami (1868) showed that
hyperbolic geometry is realised inside Euclidean geometry, and Klein (1871)
gave the projective description used here.

**The model.** Points are the points *strictly inside* the unit disc of `ℝ²`.
Lines are the open chords — so betweenness is ordinary betweenness, and
everything about incidence and order is inherited from the Cartesian plane.
Only *congruence* changes: it is given by the Cayley–Klein invariant

  `Q(a, b) = (1 − a·b)² / ((1 − |a|²)(1 − |b|²))`,

which is `cosh²` of the hyperbolic distance (no logarithms needed). Segments
near the boundary circle are very long: the boundary is infinitely far away.

In this file we set up the model and verify the Tarski axioms that do not need
the heavier algebra: the congruence axioms (A1)–(A3), the betweenness axioms
(A6)–(A8), the upper dimension axiom (A9), and continuity (A11). The essential
tool is the *convexity of the disc*: a point between two points of the disc is
in the disc. We also introduce `ch a b = √Q(a, b)`, the hyperbolic cosine of
the distance, and show `ch a b ≥ 1` with equality exactly when `a = b`.

And we show the decisive fact: **Euclid's axiom fails** — there is a point
inside an angle such that no segment through it meets both arms; equivalently,
through a point off a line there pass two different lines that never meet it
(`playfair_fails`). Segment construction and the five-segment axiom are proved
in `KleinSegment.lean`.
-/

set_option linter.unusedSectionVars false

namespace Foundations.Geometry

open Lean.Grind Foundations.Numbers

namespace Klein

/-! ## Squared norms, dot products and the invariant -/

/-- The squared Euclidean norm `|a|²`. -/
def n2 (a : Pt R) : R := a.x * a.x + a.y * a.y

/-- The Euclidean dot product `a·b`. -/
def dot (a b : Pt R) : R := a.x * b.x + a.y * b.y

/-- The **Cayley–Klein invariant** `Q(a, b) = (1 − a·b)² / ((1 − |a|²)(1 − |b|²))`,
equal to `cosh²` of the hyperbolic distance between `a` and `b`. -/
noncomputable def inv (a b : Pt R) : R :=
  (1 - dot a b) * (1 - dot a b) / ((1 - n2 a) * (1 - n2 b))

/-- The points of the **Klein model**: points strictly inside the unit circle. -/
abbrev KPt : Type := {p : Pt R // n2 p < 1}

/-- Hyperbolic **betweenness**: Euclidean betweenness of points of the disc. -/
def KBet (a b c : KPt) : Prop := Pt.Bet a.1 b.1 c.1

/-- Hyperbolic **congruence**: equality of the Cayley–Klein invariants. -/
def KCong (a b c d : KPt) : Prop := inv a.1 b.1 = inv c.1 d.1

/-- `√(1 − |a|²)` (zero outside the disc). -/
noncomputable def s (a : Pt R) : R :=
  open Classical in
  if h : 0 ≤ 1 - n2 a then Classical.choose (R.exists_sqrt h) else 0

/-- Inside the disc, `s a` is the positive square root of `1 − |a|²`. -/
theorem s_spec {a : Pt R} (ha : n2 a < 1) : 0 < s a ∧ s a * s a = 1 - n2 a := by
  have h : 0 ≤ 1 - n2 a := by grind
  have hs : s a = Classical.choose (R.exists_sqrt h) := by unfold s; simp [h]
  obtain ⟨h₁, h₂⟩ := Classical.choose_spec (R.exists_sqrt h)
  rw [← hs] at h₁ h₂
  refine ⟨?_, h₂⟩
  rcases Std.le_iff_lt_or_eq.1 h₁ with h' | h'
  · exact h'
  · rw [← h'] at h₂; grind

/-- The **hyperbolic cosine** of the distance: `ch a b = (1 − a·b) / (√(1−|a|²) √(1−|b|²))`. -/
noncomputable def ch (a b : Pt R) : R := (1 - dot a b) / (s a * s b)

/-- Squared norms are non-negative. -/
theorem n2_nonneg (a : Pt R) : 0 ≤ n2 a := by
  have := sq_nonneg' a.x; have := sq_nonneg' a.y; unfold n2; grind

/-- `2 a·b ≤ |a|² + |b|²`. -/
theorem two_dot_le (a b : Pt R) : 2 * dot a b ≤ n2 a + n2 b := by
  have := sq_nonneg' (a.x - b.x); have := sq_nonneg' (a.y - b.y); unfold dot n2; grind

/-- Inside the disc, `a·b < 1`. -/
theorem dot_lt_one {a b : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) : dot a b < 1 := by
  have := two_dot_le a b; grind

/-- **Convexity of the disc**: a point between two points of the disc lies in the disc. -/
theorem n2_lt_of_bet {a b c : Pt R} (ha : n2 a < 1) (hc : n2 c < 1) (h : Pt.Bet a b c) :
    n2 b < 1 := by
  obtain ⟨t, t0, t1, h₁, h₂⟩ := h
  have ex : b.x = (1 - t) * a.x + t * c.x := by grind
  have ey : b.y = (1 - t) * a.y + t * c.y := by grind
  have e : n2 b = (1 - t) * (1 - t) * n2 a + 2 * (t * (1 - t)) * dot a c + t * t * n2 c := by
    unfold n2 dot; rw [ex, ey]; grind
  have htt : 0 ≤ t * (1 - t) := OrderedRing.mul_nonneg t0 (by grind)
  have hd := OrderedRing.mul_le_mul_of_nonneg_left (two_dot_le a c) htt
  have k₁ := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt ha) (by grind : (0 : R) ≤ 1 - t)
  -- `|b|² ≤ (1−t)|a|² + t|c|² < 1`
  by_cases ht : t = 0
  · subst ht; grind
  · have tpos : 0 < t := by grind
    have k₃ := OrderedRing.mul_lt_mul_of_pos_left hc tpos
    grind

/-- **The basic inequality**: `(1 − a·b)² − (1 − |a|²)(1 − |b|²) ≥ |a − b|² (1 − |b|²)`. -/
theorem key_ineq (a b : Pt R) :
    Pt.d2 a b * (1 - n2 b) ≤ (1 - dot a b) * (1 - dot a b) - (1 - n2 a) * (1 - n2 b) := by
  -- the difference is `|a−b|²|b|² − ((a−b)×b)² ≥ 0` (Lagrange)
  have := sq_nonneg' ((a.x - b.x) * b.x + (a.y - b.y) * b.y)
  unfold Pt.d2 n2 dot; grind

/-- The invariant is at least `1`, with equality only for equal points. -/
theorem one_le_inv {a b : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) : 1 ≤ inv a b := by
  have hk := key_ineq a b
  have hd := Pt.d2_nonneg a b
  have hpos : 0 < (1 - n2 a) * (1 - n2 b) := OrderedRing.mul_pos (by grind) (by grind)
  have := OrderedRing.mul_nonneg hd (by grind : (0 : R) ≤ 1 - n2 b)
  unfold inv
  have hne : (1 - n2 a) * (1 - n2 b) ≠ 0 := by grind
  have e : (1 - dot a b) * (1 - dot a b) / ((1 - n2 a) * (1 - n2 b)) - 1 =
      ((1 - dot a b) * (1 - dot a b) - (1 - n2 a) * (1 - n2 b)) / ((1 - n2 a) * (1 - n2 b)) := by
    grind
  have : 0 ≤ ((1 - dot a b) * (1 - dot a b) - (1 - n2 a) * (1 - n2 b)) /
      ((1 - n2 a) * (1 - n2 b)) := by
    rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg (by grind) (by have := Field.IsOrdered.inv_pos_iff.2 hpos; grind)
  grind

/-- `Q(a, b) = 1` only if `a = b`. -/
theorem eq_of_inv_eq_one {a b : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) (h : inv a b = 1) :
    a = b := by
  have hk := key_ineq a b
  have hne : (1 - n2 a) * (1 - n2 b) ≠ 0 := by
    have := OrderedRing.mul_pos (by grind : (0 : R) < 1 - n2 a) (by grind : (0 : R) < 1 - n2 b)
    grind
  unfold inv at h
  have h' : (1 - dot a b) * (1 - dot a b) = (1 - n2 a) * (1 - n2 b) := by grind
  have : Pt.d2 a b * (1 - n2 b) ≤ 0 := by grind
  apply Pt.eq_of_d2_eq_zero
  apply Classical.byContradiction
  intro hd
  have hd' : 0 < Pt.d2 a b := by have := Pt.d2_nonneg a b; grind
  have := OrderedRing.mul_pos hd' (by grind : (0 : R) < 1 - n2 b)
  grind

/-- `Q(a, a) = 1`. -/
theorem inv_self {a : Pt R} (ha : n2 a < 1) : inv a a = 1 := by
  unfold inv
  have : 1 - dot a a = 1 - n2 a := by unfold dot n2; grind
  rw [this]
  have : 1 - n2 a ≠ 0 := by grind
  grind

/-- The invariant is symmetric. -/
theorem inv_comm (a b : Pt R) : inv a b = inv b a := by unfold inv dot; grind

/-! ## The hyperbolic cosine -/

/-- `ch a b > 0` inside the disc. -/
theorem ch_pos {a b : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) : 0 < ch a b := by
  obtain ⟨sa, -⟩ := s_spec ha
  obtain ⟨sb, -⟩ := s_spec hb
  have := dot_lt_one ha hb
  unfold ch; rw [Field.div_eq_mul_inv]
  exact OrderedRing.mul_pos (by grind) (Field.IsOrdered.inv_pos_iff.2 (OrderedRing.mul_pos sa sb))

/-- `ch² = Q`. -/
theorem ch_mul_self {a b : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) : ch a b * ch a b = inv a b := by
  obtain ⟨sa, ea⟩ := s_spec ha
  obtain ⟨sb, eb⟩ := s_spec hb
  unfold ch inv
  rw [← ea, ← eb]
  have : s a ≠ 0 := by grind
  have : s b ≠ 0 := by grind
  grind

/-- `ch a b ≥ 1`. -/
theorem one_le_ch {a b : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) : 1 ≤ ch a b :=
  Pt.le_of_sq_le (Std.le_of_lt (ch_pos ha hb)) (by rw [ch_mul_self ha hb]; have := one_le_inv ha hb; grind)

/-- `ch a a = 1`. -/
theorem ch_self {a : Pt R} (ha : n2 a < 1) : ch a a = 1 :=
  eq_of_sq_eq (Std.le_of_lt (ch_pos ha ha)) (by grind) (by rw [ch_mul_self ha ha, inv_self ha]; grind)

/-- `ch` is symmetric. -/
theorem ch_comm (a b : Pt R) : ch a b = ch b a := by unfold ch dot; grind

/-- **Congruence via `ch`**: `ab ≡ cd` iff `ch a b = ch c d`. -/
theorem inv_eq_iff_ch_eq {a b c d : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) (hc : n2 c < 1)
    (hd : n2 d < 1) : inv a b = inv c d ↔ ch a b = ch c d := by
  constructor
  · intro h
    exact eq_of_sq_eq (Std.le_of_lt (ch_pos ha hb)) (Std.le_of_lt (ch_pos hc hd))
      (by rw [ch_mul_self ha hb, ch_mul_self hc hd, h])
  · intro h
    rw [← ch_mul_self ha hb, ← ch_mul_self hc hd, h]

/-! ## The axioms of congruence and order -/

/-- (A1) in the Klein model. -/
theorem cong_pseudo_refl (a b : KPt) : KCong a b b a := inv_comm _ _

/-- (A2) in the Klein model. -/
theorem cong_inner_trans (a b p q r s : KPt) (h₁ : KCong a b p q) (h₂ : KCong a b r s) :
    KCong p q r s := h₁.symm.trans h₂

/-- (A3) in the Klein model. -/
theorem cong_identity (a b c : KPt) (h : KCong a b c c) : a = b := by
  unfold KCong at h
  rw [inv_self c.2] at h
  exact Subtype.ext (eq_of_inv_eq_one a.2 b.2 h)

/-- (A6) in the Klein model. -/
theorem bet_identity (a b : KPt) (h : KBet a b a) : a = b :=
  Subtype.ext (Pt.bet_identity _ _ h)

/-- (A7) **Pasch's axiom** in the Klein model: the Euclidean intersection point lies in the
disc by convexity. -/
theorem pasch (a b c p q : KPt) (h₁ : KBet a p c) (h₂ : KBet b q c) :
    ∃ x, KBet p x b ∧ KBet q x a := by
  obtain ⟨x, hx₁, hx₂⟩ := Pt.pasch _ _ _ _ _ h₁ h₂
  exact ⟨⟨x, n2_lt_of_bet p.2 b.2 hx₁⟩, hx₁, hx₂⟩

/-- (A8) **Lower dimension** in the Klein model. -/
theorem lower_dim : ∃ a b c : KPt, ¬ KBet a b c ∧ ¬ KBet b c a ∧ ¬ KBet c a b := by
  refine ⟨⟨⟨0, 0⟩, by unfold n2; grind⟩, ⟨⟨1 / 2, 0⟩, by unfold n2; grind⟩,
    ⟨⟨0, 1 / 2⟩, by unfold n2; grind⟩, ?_, ?_, ?_⟩ <;>
    rintro ⟨t, -, -, h₁, h₂⟩ <;> dsimp only at h₁ h₂ <;> grind

/-- Three points whose differences are orthogonal to a non-zero vector are collinear:
one of them lies between the other two. -/
theorem bet_of_perp {a b c : Pt R} {nx ny : R} (hn : ¬ (nx = 0 ∧ ny = 0))
    (hab : (b.x - a.x) * nx + (b.y - a.y) * ny = 0)
    (hac : (c.x - a.x) * nx + (c.y - a.y) * ny = 0) :
    Pt.Bet a b c ∨ Pt.Bet b c a ∨ Pt.Bet c a b := by
  have hN : nx * nx + ny * ny ≠ 0 := by
    intro h
    exact hn (sum_sq_eq_zero h)
  let w : Pt R := ⟨-ny, nx⟩
  have hb' : b.x = a.x + ((b.x - a.x) * (-ny) + (b.y - a.y) * nx) / (nx * nx + ny * ny) * w.x ∧
      b.y = a.y + ((b.x - a.x) * (-ny) + (b.y - a.y) * nx) / (nx * nx + ny * ny) * w.y := by
    have e₁ := congrArg (· * nx) hab
    have e₂ := congrArg (· * ny) hab
    dsimp only [w] at *
    constructor <;> grind
  have hc' : c.x = a.x + ((c.x - a.x) * (-ny) + (c.y - a.y) * nx) / (nx * nx + ny * ny) * w.x ∧
      c.y = a.y + ((c.x - a.x) * (-ny) + (c.y - a.y) * nx) / (nx * nx + ny * ny) * w.y := by
    have e₁ := congrArg (· * nx) hac
    have e₂ := congrArg (· * ny) hac
    dsimp only [w] at *
    constructor <;> grind
  have ha' : a.x = a.x + 0 * w.x ∧ a.y = a.y + 0 * w.y := ⟨by grind, by grind⟩
  generalize ((b.x - a.x) * (-ny) + (b.y - a.y) * nx) / (nx * nx + ny * ny) = β at hb'
  generalize ((c.x - a.x) * (-ny) + (c.y - a.y) * nx) / (nx * nx + ny * ny) = γ at hc'
  rcases Std.le_total (a := (0 : R)) (b := β) with h₁ | h₁ <;>
    rcases Std.le_total (a := β) (b := γ) with h₂ | h₂ <;>
    rcases Std.le_total (a := (0 : R)) (b := γ) with h₃ | h₃
  all_goals first
    | exact Or.inl (Pt.bet_of_line ha' hb' hc' (by grind))
    | exact Or.inr (Or.inl (Pt.bet_of_line hb' hc' ha' (by grind)))
    | exact Or.inr (Or.inr (Pt.bet_of_line hc' ha' hb' (by grind)))

/-- Points hyperbolically equidistant from `p` and `q` satisfy a *linear* equation:
`(1 − a·p)/√(1−|p|²) = (1 − a·q)/√(1−|q|²)`. -/
theorem equidistant_linear {a p q : Pt R} (ha : n2 a < 1) (hp : n2 p < 1) (hq : n2 q < 1)
    (h : inv a p = inv a q) : (1 - dot a p) * s q = (1 - dot a q) * s p := by
  rw [inv_eq_iff_ch_eq ha hp ha hq] at h
  obtain ⟨sa, -⟩ := s_spec ha
  obtain ⟨sp, -⟩ := s_spec hp
  obtain ⟨sq, -⟩ := s_spec hq
  unfold ch at h
  have : s a ≠ 0 := by grind
  have : s p ≠ 0 := by grind
  have : s q ≠ 0 := by grind
  grind

/-- (A9) **Upper dimension** in the Klein model: the hyperbolic perpendicular bisector of
`pq` is a chord. -/
theorem upper_dim (a b c p q : KPt) (hpq : p ≠ q) (ha : KCong a p a q) (hb : KCong b p b q)
    (hc : KCong c p c q) : KBet a b c ∨ KBet b c a ∨ KBet c a b := by
  have la := equidistant_linear a.2 p.2 q.2 ha
  have lb := equidistant_linear b.2 p.2 q.2 hb
  have lc := equidistant_linear c.2 p.2 q.2 hc
  obtain ⟨sp, ep⟩ := s_spec p.2
  obtain ⟨sq, eq⟩ := s_spec q.2
  -- the normal vector `n = s_q p − s_p q`
  have hn : ¬ (p.1.x * s q.1 - q.1.x * s p.1 = 0 ∧ p.1.y * s q.1 - q.1.y * s p.1 = 0) := by
    rintro ⟨h₁, h₂⟩
    apply hpq
    -- then `|p|² s_q² = |q|² s_p²`, so `|p| = |q|`, so `s_p = s_q`, so `p = q`
    have e : n2 p.1 * (s q.1 * s q.1) = n2 q.1 * (s p.1 * s p.1) := by
      show (p.1.x * p.1.x + p.1.y * p.1.y) * (s q.1 * s q.1) =
        (q.1.x * q.1.x + q.1.y * q.1.y) * (s p.1 * s p.1)
      have hx : p.1.x * s q.1 = q.1.x * s p.1 := by grind
      have hy : p.1.y * s q.1 = q.1.y * s p.1 := by grind
      have hx2 : (p.1.x * s q.1) * (p.1.x * s q.1) = (q.1.x * s p.1) * (q.1.x * s p.1) := by
        rw [hx]
      have hy2 : (p.1.y * s q.1) * (p.1.y * s q.1) = (q.1.y * s p.1) * (q.1.y * s p.1) := by
        rw [hy]
      grind
    rw [ep, eq] at e
    have hpq2 : n2 p.1 = n2 q.1 := by grind
    have hs : s p.1 = s q.1 := eq_of_sq_eq (by grind) (by grind) (by rw [ep, eq, hpq2])
    rw [hs] at h₁ h₂
    have : s q.1 ≠ 0 := by grind
    exact Subtype.ext (Pt.ext' (by grind) (by grind))
  exact bet_of_perp hn (by unfold dot at la lb; grind) (by unfold dot at la lc; grind)

/-- (A11) **Continuity** in the Klein model, inherited from the Cartesian plane: the
separating point lies between points of the disc, hence in the disc. -/
theorem continuity (φ ψ : KPt → Prop) (h : ∃ a, ∀ x y, φ x → ψ y → KBet a x y) :
    ∃ b, ∀ x y, φ x → ψ y → KBet x b y := by
  obtain ⟨a, ha⟩ := h
  by_cases hφ : ∃ x0, φ x0
  case neg => exact ⟨a, fun x _ hx _ => absurd ⟨x, hx⟩ hφ⟩
  by_cases hψ : ∃ y0, ψ y0
  case neg => exact ⟨a, fun _ y _ hy => absurd ⟨y, hy⟩ hψ⟩
  obtain ⟨x0, hx0⟩ := hφ
  obtain ⟨y0, hy0⟩ := hψ
  obtain ⟨b, hb⟩ := Pt.continuity_of_lub R.exists_lub (fun p => ∃ h, φ ⟨p, h⟩)
    (fun p => ∃ h, ψ ⟨p, h⟩) ⟨a.1, fun x y ⟨hx, hφx⟩ ⟨hy, hψy⟩ => ha ⟨x, hx⟩ ⟨y, hy⟩ hφx hψy⟩
  have hb1 : n2 b < 1 := n2_lt_of_bet x0.2 y0.2 (hb x0.1 y0.1 ⟨x0.2, hx0⟩ ⟨y0.2, hy0⟩)
  exact ⟨⟨b, hb1⟩, fun x y hx hy => hb x.1 y.1 ⟨x.2, hx⟩ ⟨y.2, hy⟩⟩

/-! ## The failure of Euclid's axiom -/

/-- The origin, as a point of the Klein model. -/
def O : KPt := ⟨⟨0, 0⟩, by unfold n2; grind⟩

/-- **Euclid's axiom fails in the Klein model.** Take the angle at the origin between
the arms through `b = (1/2, 0)` and `c = (0, 1/2)`, and the point `t = (3/5, 3/5)` inside it
(beyond the midpoint `d` of `bc`). Any segment through `t` with endpoints on the two arms
would have endpoints `(σ, 0)`, `(0, ρ)` with `3/5 = (1−λ)σ` and `3/5 = λρ`; since
`σ, ρ < 1` inside the disc this gives `6/5 = (1−λ)σ + λρ < 1`, which is absurd. In
the Euclidean plane the endpoints would simply lie outside the unit circle. -/
theorem not_euclid : ¬ ∀ a b c d t : KPt, KBet a d t → KBet b d c → a ≠ d →
    ∃ x y, KBet a b x ∧ KBet a c y ∧ KBet x t y := by
  intro h
  let b : KPt := ⟨⟨1 / 2, 0⟩, by unfold n2; grind⟩
  let c : KPt := ⟨⟨0, 1 / 2⟩, by unfold n2; grind⟩
  let d : KPt := ⟨⟨1 / 4, 1 / 4⟩, by unfold n2; grind⟩
  let t : KPt := ⟨⟨3 / 5, 3 / 5⟩, by unfold n2; grind⟩
  have hdt : KBet O d t := ⟨5 / 12, by grind, by grind, by dsimp only [O, d, t]; grind,
    by dsimp only [O, d, t]; grind⟩
  have hbdc : KBet b d c := ⟨1 / 2, by grind, by grind, by dsimp only [b, d, c]; grind,
    by dsimp only [b, d, c]; grind⟩
  have hOd : O ≠ d := by
    intro e
    have := congrArg (fun p : KPt => p.1.x) e
    dsimp only [O, d] at this
    grind
  obtain ⟨x, y, ⟨μ, μ0, μ1, hx₁, hx₂⟩, ⟨ν, ν0, ν1, hy₁, hy₂⟩, ⟨l, l0, l1, ht₁, ht₂⟩⟩ :=
    h O b c d t hdt hbdc hOd
  dsimp only [O, b, c, t] at hx₁ hx₂ hy₁ hy₂ ht₁ ht₂
  have xin := x.2
  have yin := y.2
  unfold n2 at xin yin
  -- `x = (σ, 0)` with `0 < σ < 1`, `y = (0, ρ)` with `0 < ρ < 1`
  have hμ : μ ≠ 0 := by intro h0; rw [h0] at hx₁; grind
  have hν : ν ≠ 0 := by intro h0; rw [h0] at hy₂; grind
  have xy0 : x.1.y = 0 := by grind
  have yx0 : y.1.x = 0 := by grind
  have xpos : 0 < x.1.x := by
    apply Classical.byContradiction; intro hn
    have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : x.1.x ≤ 0) μ0
    grind
  have ypos : 0 < y.1.y := by
    apply Classical.byContradiction; intro hn
    have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : y.1.y ≤ 0) ν0
    grind
  have x1 : x.1.x < 1 := by
    apply Classical.byContradiction; intro hn
    have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : (1 : R) ≤ x.1.x) (by grind : (0 : R) ≤ x.1.x)
    have := sq_nonneg' x.1.y
    grind
  have y1 : y.1.y < 1 := by
    apply Classical.byContradiction; intro hn
    have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : (1 : R) ≤ y.1.y) (by grind : (0 : R) ≤ y.1.y)
    have := sq_nonneg' y.1.x
    grind
  -- `3/5 = (1 − l) σ ≤ 1 − l` and `3/5 = l ρ ≤ l`, so `6/5 ≤ 1`
  have k₁ := mul_le_of_le_one (Std.le_of_lt x1) (by grind : (0 : R) ≤ 1 - l)
  have k₂ := mul_le_of_le_one (Std.le_of_lt y1) l0
  rw [xy0, yx0] at *
  grind

end Klein

end Foundations.Geometry
