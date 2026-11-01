import Foundations.Geometry.Tarski
import Foundations.Numbers

/-!
# The Cartesian plane is a model of Tarski's axioms

Descartes' *La Géométrie* (1637) turned geometry into algebra: a point of the
plane is a pair of numbers `(x, y)`, and geometric relations become equations
between coordinates. Here we run Descartes' idea backwards to *justify* the
axioms: over any ordered field `K` we define

* `B a b c` iff `b = a + t (c − a)` for some `t` with `0 ≤ t ≤ 1`, and
* `ab ≡ cd` iff `|ab|² = |cd|²`, where `|ab|² = (a₁−b₁)² + (a₂−b₂)²`

(using *squared* distances, so that no square roots are needed), and check
Tarski's axioms one by one.

The outcome is instructive. **Nine of the eleven axioms hold in `K²` for every
ordered field `K`** — even for the rationals. The other two depend on the number
field:

* **segment construction** needs square roots of non-negative elements (to lay
  off a segment of length `√(|bc|²)` on a ray); it holds whenever `K` is
  *Euclidean* in this sense, for instance for `ℝ`;
* **continuity** needs the least-upper-bound property; it holds for `ℝ` by the
  completeness theorem of Part II.

Hence **`ℝ²` is a model of all of Tarski's axioms** — a relative consistency
proof: if the real numbers (built in Part II from the rationals, hence from the
natural numbers) are consistent, so is Euclidean geometry. This was Hilbert's
strategy in the *Grundlagen*. In `Euclid.lean` we see that `ℚ²` really does
fail both axioms: *which* geometry we get is fixed by the number field from
which the space is built.
-/

set_option linter.unusedSectionVars false

namespace Foundations.Geometry

open Lean.Grind

section Algebra

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-! ## A little ordered-field algebra -/

/-- Squares are non-negative. -/
theorem sq_nonneg' (u : K) : 0 ≤ u * u := by
  by_cases h : 0 ≤ u
  · exact OrderedRing.mul_nonneg h h
  · have := OrderedRing.mul_nonneg (by grind : 0 ≤ -u) (by grind : 0 ≤ -u); grind

/-- A sum of two squares vanishes only if both terms vanish. -/
theorem sum_sq_eq_zero {u v : K} (h : u * u + v * v = 0) : u = 0 ∧ v = 0 := by
  have hu := sq_nonneg' u
  have hv := sq_nonneg' v
  have hu' : u * u = 0 := by grind
  have hv' : v * v = 0 := by grind
  exact ⟨by grind, by grind⟩

/-- A quotient `u / v` with `0 ≤ u ≤ v`, `0 < v` lies in the unit interval. -/
theorem div_mem_unit {u v : K} (hu : 0 ≤ u) (huv : u ≤ v) (hv : 0 < v) :
    0 ≤ u / v ∧ u / v ≤ 1 := by
  have hi : 0 < v⁻¹ := Field.IsOrdered.inv_pos_iff.2 hv
  have h1 := OrderedRing.mul_nonneg hu (by grind : 0 ≤ v⁻¹)
  have h2 := OrderedRing.mul_le_mul_of_nonneg_right huv (by grind : 0 ≤ v⁻¹)
  have h3 : v * v⁻¹ = 1 := Field.mul_inv_cancel (by grind)
  rw [Field.div_eq_mul_inv]
  grind

/-- Non-negative numbers with equal squares are equal. -/
theorem eq_of_sq_eq {p q : K} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p * p = q * q) : p = q := by
  by_cases hs : p + q = 0
  · grind
  · have : (p - q) * (p + q) = 0 := by grind
    grind

/-- `t · s ≤ s` when `t ≤ 1` and `s ≥ 0`. -/
theorem mul_le_of_le_one {t s : K} (ht : t ≤ 1) (hs : 0 ≤ s) : t * s ≤ s := by
  have := OrderedRing.mul_le_mul_of_nonneg_right ht hs
  grind

end Algebra

/-! ## Points, betweenness and equidistance -/

/-- A **point of the Cartesian plane** `K²`: a pair of coordinates. -/
structure Pt (K : Type) where
  /-- The first coordinate. -/
  x : K
  /-- The second coordinate. -/
  y : K

namespace Pt

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- Points with equal coordinates are equal. -/
theorem ext' {p q : Pt K} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p; cases q; simp only at hx hy; rw [hx, hy]

/-- The **squared distance** `|ab|² = (a₁ − b₁)² + (a₂ − b₂)²`. -/
def d2 (a b : Pt K) : K := (a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y)

/-- **Equidistance** in `K²`: equal squared distances. -/
def Cong (a b c d : Pt K) : Prop := d2 a b = d2 c d

/-- **Betweenness** in `K²`: `b = a + t (c − a)` for some `t ∈ [0, 1]`. -/
def Bet (a b c : Pt K) : Prop :=
  ∃ t : K, 0 ≤ t ∧ t ≤ 1 ∧ b.x - a.x = t * (c.x - a.x) ∧ b.y - a.y = t * (c.y - a.y)

/-- Squared distances are non-negative. -/
theorem d2_nonneg (a b : Pt K) : 0 ≤ d2 a b := by
  have := sq_nonneg' (a.x - b.x); have := sq_nonneg' (a.y - b.y); unfold d2; grind

/-- Squared distance zero means equal points. -/
theorem eq_of_d2_eq_zero {a b : Pt K} (h : d2 a b = 0) : a = b := by
  obtain ⟨h₁, h₂⟩ := sum_sq_eq_zero h
  exact ext' (by grind) (by grind)

/-- The squared distance of a point to itself is zero. -/
theorem d2_self (a : Pt K) : d2 a a = 0 := by unfold d2; grind

/-- Squared distance is symmetric. -/
theorem d2_comm (a b : Pt K) : d2 a b = d2 b a := by unfold d2; grind

/-- Distinct points are at positive squared distance. -/
theorem d2_pos {a b : Pt K} (h : a ≠ b) : 0 < d2 a b := by
  have := d2_nonneg a b
  have : d2 a b ≠ 0 := fun h' => h (eq_of_d2_eq_zero h')
  grind

/-- **Points on a line**: if `a, b, c` are `o + α w`, `o + β w`, `o + γ w` and `β`
lies between `α` and `γ`, then `B a b c`. -/
theorem bet_of_line {a b c o w : Pt K} {α β γ : K}
    (ha : a.x = o.x + α * w.x ∧ a.y = o.y + α * w.y)
    (hb : b.x = o.x + β * w.x ∧ b.y = o.y + β * w.y)
    (hc : c.x = o.x + γ * w.x ∧ c.y = o.y + γ * w.y)
    (h : (α ≤ β ∧ β ≤ γ) ∨ (γ ≤ β ∧ β ≤ α)) : Bet a b c := by
  by_cases hαγ : α = γ
  · refine ⟨0, Std.le_refl 0, by grind, ?_, ?_⟩ <;> grind
  · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · obtain ⟨t0, t1⟩ := div_mem_unit (u := β - α) (v := γ - α) (by grind) (by grind) (by grind)
      refine ⟨(β - α) / (γ - α), t0, t1, ?_, ?_⟩
      · have : γ - α ≠ 0 := by grind
        grind
      · have : γ - α ≠ 0 := by grind
        grind
    · obtain ⟨t0, t1⟩ := div_mem_unit (u := α - β) (v := α - γ) (by grind) (by grind) (by grind)
      refine ⟨(α - β) / (α - γ), t0, t1, ?_, ?_⟩
      · have : α - γ ≠ 0 := by grind
        grind
      · have : α - γ ≠ 0 := by grind
        grind

/-! ## The axioms valid over every ordered field -/

/-- (A1) in `K²`. -/
theorem cong_pseudo_refl (a b : Pt K) : Cong a b b a := d2_comm a b

/-- (A2) in `K²`. -/
theorem cong_inner_trans (a b p q r s : Pt K) (h₁ : Cong a b p q) (h₂ : Cong a b r s) :
    Cong p q r s := h₁.symm.trans h₂

/-- (A3) in `K²`. -/
theorem cong_identity (a b c : Pt K) (h : Cong a b c c) : a = b :=
  eq_of_d2_eq_zero (h.trans (d2_self c))

/-- (A6) in `K²`. -/
theorem bet_identity (a b : Pt K) (h : Bet a b a) : a = b := by
  obtain ⟨t, -, -, h₁, h₂⟩ := h
  exact ext' (by grind) (by grind)

/-- Stewart's relation for a point `b = a + t (c − a)`:
`|bd|² = (1−t)|ad|² + t|cd|² − t(1−t)|ac|²`. -/
theorem stewart {a b c d : Pt K} {t : K} (hx : b.x - a.x = t * (c.x - a.x))
    (hy : b.y - a.y = t * (c.y - a.y)) :
    d2 b d = (1 - t) * d2 a d + t * d2 c d - t * (1 - t) * d2 a c := by
  have ex : b.x = a.x + t * (c.x - a.x) := by grind
  have ey : b.y = a.y + t * (c.y - a.y) := by grind
  unfold d2; rw [ex, ey]; grind

/-- For `b = a + t (c − a)`: `|ab|² = t² |ac|²`. -/
theorem d2_left {a b c : Pt K} {t : K} (hx : b.x - a.x = t * (c.x - a.x))
    (hy : b.y - a.y = t * (c.y - a.y)) : d2 a b = t * t * d2 a c := by
  have ex : b.x = a.x + t * (c.x - a.x) := by grind
  have ey : b.y = a.y + t * (c.y - a.y) := by grind
  unfold d2; rw [ex, ey]; grind

/-- For `b = a + t (c − a)`: `|bc|² = (1−t)² |ac|²`. -/
theorem d2_right {a b c : Pt K} {t : K} (hx : b.x - a.x = t * (c.x - a.x))
    (hy : b.y - a.y = t * (c.y - a.y)) : d2 b c = (1 - t) * (1 - t) * d2 a c := by
  have ex : b.x = a.x + t * (c.x - a.x) := by grind
  have ey : b.y = a.y + t * (c.y - a.y) := by grind
  unfold d2; rw [ex, ey]; grind

/-- (A5) **The five-segment axiom** in `K²`, via Stewart's relation. -/
theorem five_segment (a b c d a' b' c' d' : Pt K) (hab : a ≠ b) (h₁ : Bet a b c)
    (h₂ : Bet a' b' c') (e₁ : Cong a b a' b') (e₂ : Cong b c b' c') (e₃ : Cong a d a' d')
    (e₄ : Cong b d b' d') : Cong c d c' d' := by
  obtain ⟨t, t0, t1, hx, hy⟩ := h₁
  obtain ⟨s, s0, s1, hx', hy'⟩ := h₂
  unfold Cong at *
  have l₁ := d2_left hx hy
  have l₂ := d2_left hx' hy'
  have r₁ := d2_right hx hy
  have r₂ := d2_right hx' hy'
  have st₁ := stewart (d := d) hx hy
  have st₂ := stewart (d := d') hx' hy'
  have D0 := d2_nonneg a c
  have D0' := d2_nonneg a' c'
  -- the "geometric mean" `t (1−t) |ac|²` is determined by `|ab|²` and `|bc|²`
  have p0 : 0 ≤ t * (1 - t) * d2 a c :=
    OrderedRing.mul_nonneg (OrderedRing.mul_nonneg t0 (by grind)) D0
  have p0' : 0 ≤ s * (1 - s) * d2 a' c' :=
    OrderedRing.mul_nonneg (OrderedRing.mul_nonneg s0 (by grind)) D0'
  have psq : (t * (1 - t) * d2 a c) * (t * (1 - t) * d2 a c) =
      (s * (1 - s) * d2 a' c') * (s * (1 - s) * d2 a' c') := by
    have e : (t * (1 - t) * d2 a c) * (t * (1 - t) * d2 a c) = d2 a b * d2 b c := by
      rw [l₁, r₁]; grind
    have e' : (s * (1 - s) * d2 a' c') * (s * (1 - s) * d2 a' c') = d2 a' b' * d2 b' c' := by
      rw [l₂, r₂]; grind
    rw [e, e', e₁, e₂]
  have peq := eq_of_sq_eq p0 p0' psq
  -- hence `|ac|² = |a'c'|²`
  have hD : d2 a c = d2 a' c' := by
    have u : d2 a c = d2 a b + 2 * (t * (1 - t) * d2 a c) + d2 b c := by rw [l₁, r₁]; grind
    have u' : d2 a' c' = d2 a' b' + 2 * (s * (1 - s) * d2 a' c') + d2 b' c' := by
      rw [l₂, r₂]; grind
    rw [u, u', e₁, e₂, peq]
  -- and `t = s`
  have hab' : 0 < d2 a b := d2_pos hab
  have hDpos : d2 a c ≠ 0 := by intro h0; rw [h0] at l₁; grind
  have hts : t = s := by
    apply eq_of_sq_eq t0 s0
    have : t * t * d2 a c = s * s * d2 a c := by rw [← l₁, e₁, l₂, hD]
    grind
  subst hts
  have ht0 : t ≠ 0 := by intro h0; rw [h0] at l₁; grind
  have key : t * d2 c d = t * d2 c' d' := by grind
  grind

/-- (A7) **Pasch's axiom** in `K²`: the cevians `bp` and `aq` of triangle `abc` meet,
at an explicitly computed point. -/
theorem pasch (a b c p q : Pt K) (h₁ : Bet a p c) (h₂ : Bet b q c) :
    ∃ x, Bet p x b ∧ Bet q x a := by
  obtain ⟨s, s0, s1, hpx, hpy⟩ := h₁
  obtain ⟨r, r0, r1, hqx, hqy⟩ := h₂
  have hrs : s * r ≤ r := mul_le_of_le_one s1 r0
  have hsr : r * s ≤ s := mul_le_of_le_one r1 s0
  by_cases hD : r + s - r * s = 0
  · have hs : s = 0 := by grind
    have hr : r = 0 := by grind
    refine ⟨a, ⟨0, Std.le_refl 0, by grind, by grind, by grind⟩,
      ⟨1, by grind, Std.le_refl 1, by grind, by grind⟩⟩
  · have hDpos : 0 < r + s - r * s := by grind
    obtain ⟨l0, l1⟩ := div_mem_unit (u := s - r * s) (v := r + s - r * s) (by grind) (by grind) hDpos
    obtain ⟨m0, m1⟩ := div_mem_unit (u := r - r * s) (v := r + s - r * s) (by grind) (by grind) hDpos
    refine ⟨⟨p.x + (s - r * s) / (r + s - r * s) * (b.x - p.x),
        p.y + (s - r * s) / (r + s - r * s) * (b.y - p.y)⟩,
      ⟨(s - r * s) / (r + s - r * s), l0, l1, ?_, ?_⟩,
      ⟨(r - r * s) / (r + s - r * s), m0, m1, ?_, ?_⟩⟩ <;> dsimp only <;> grind

/-- (A8) **Lower dimension** in `K²`: `(0,0)`, `(1,0)`, `(0,1)` are not collinear. -/
theorem lower_dim : ∃ a b c : Pt K, ¬ Bet a b c ∧ ¬ Bet b c a ∧ ¬ Bet c a b := by
  refine ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ?_, ?_, ?_⟩ <;>
    rintro ⟨t, -, -, h₁, h₂⟩ <;> dsimp only at h₁ h₂ <;> grind

/-- (A9) **Upper dimension** in `K²`: points equidistant from `p ≠ q` lie on the
perpendicular bisector, a line, so one of any three of them lies between the others. -/
theorem upper_dim (a b c p q : Pt K) (hpq : p ≠ q) (ha : Cong a p a q) (hb : Cong b p b q)
    (hc : Cong c p c q) : Bet a b c ∨ Bet b c a ∨ Bet c a b := by
  unfold Cong d2 at ha hb hc
  obtain ⟨nx, hnx⟩ : ∃ nx, nx = q.x - p.x := ⟨_, rfl⟩
  obtain ⟨ny, hny⟩ : ∃ ny, ny = q.y - p.y := ⟨_, rfl⟩
  have hN : nx * nx + ny * ny ≠ 0 := by
    intro h
    obtain ⟨h₁, h₂⟩ := sum_sq_eq_zero h
    exact hpq (ext' (by grind) (by grind))
  -- `b − a` and `c − a` are orthogonal to `n = q − p`
  have hab : (b.x - a.x) * nx + (b.y - a.y) * ny = 0 := by grind
  have hac : (c.x - a.x) * nx + (c.y - a.y) * ny = 0 := by grind
  -- so they are multiples of `w = (−n_y, n_x)`
  let w : Pt K := ⟨-ny, nx⟩
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
  rcases Std.le_total (a := (0 : K)) (b := β) with h₁ | h₁ <;>
    rcases Std.le_total (a := β) (b := γ) with h₂ | h₂ <;>
    rcases Std.le_total (a := (0 : K)) (b := γ) with h₃ | h₃
  all_goals first
    | exact Or.inl (bet_of_line ha' hb' hc' (by grind))
    | exact Or.inr (Or.inl (bet_of_line hb' hc' ha' (by grind)))
    | exact Or.inr (Or.inr (bet_of_line hc' ha' hb' (by grind)))

/-- (A10) **Euclid's axiom** in `K²`: stretch the segments `ab`, `ac` by the factor `1/u`. -/
theorem euclid (a b c d t : Pt K) (h₁ : Bet a d t) (h₂ : Bet b d c) (had : a ≠ d) :
    ∃ x y, Bet a b x ∧ Bet a c y ∧ Bet x t y := by
  obtain ⟨u, u0, u1, hdx, hdy⟩ := h₁
  obtain ⟨s, s0, s1, hdx', hdy'⟩ := h₂
  have hu : u ≠ 0 := by
    intro h0
    exact had (ext' (by grind) (by grind))
  refine ⟨⟨a.x + (b.x - a.x) / u, a.y + (b.y - a.y) / u⟩,
    ⟨a.x + (c.x - a.x) / u, a.y + (c.y - a.y) / u⟩,
    ⟨u, u0, u1, ?_, ?_⟩, ⟨u, u0, u1, ?_, ?_⟩, ⟨s, s0, s1, ?_, ?_⟩⟩ <;> dsimp only <;> grind

/-! ## The two axioms that depend on the number field -/

/-- (A4) **Segment construction** holds in `K²` whenever non-negative elements of `K`
have square roots. -/
theorem segment_construction_of_sqrt (hsq : ∀ z : K, 0 ≤ z → ∃ r, 0 ≤ r ∧ r * r = z)
    (q a b c : Pt K) : ∃ x, Bet q a x ∧ Cong a x b c := by
  by_cases hqa : q = a
  · subst hqa
    obtain ⟨r, _, hr⟩ := hsq (d2 b c) (d2_nonneg b c)
    refine ⟨⟨q.x + r, q.y⟩, ⟨0, Std.le_refl 0, by grind, by grind, by grind⟩, ?_⟩
    unfold Cong; rw [← hr]; unfold d2; dsimp only; grind
  · have hE := d2_pos hqa
    have hz : 0 ≤ d2 b c / d2 q a := by
      rw [Field.div_eq_mul_inv]
      exact OrderedRing.mul_nonneg (d2_nonneg b c)
        (by have := Field.IsOrdered.inv_pos_iff.2 hE; grind)
    obtain ⟨k, k0, hk⟩ := hsq _ hz
    obtain ⟨t0, t1⟩ := div_mem_unit (u := 1) (v := 1 + k) (by grind) (by grind) (by grind)
    have hk1 : 1 + k ≠ 0 := by grind
    have hE' : d2 q a ≠ 0 := by grind
    refine ⟨⟨a.x + k * (a.x - q.x), a.y + k * (a.y - q.y)⟩, ⟨1 / (1 + k), t0, t1, ?_, ?_⟩, ?_⟩
    · dsimp only; grind
    · dsimp only; grind
    · unfold Cong
      have e : d2 a ⟨a.x + k * (a.x - q.x), a.y + k * (a.y - q.y)⟩ = k * k * d2 q a := by
        unfold d2; dsimp only; grind
      rw [e, hk]
      grind

/-- (A11) **Continuity** holds in `K²` whenever `K` has the least-upper-bound property:
the points of `φ` and `ψ` lie on a ray from `a`, and the supremum of the parameters
of the `φ`-points gives the separating point. -/
theorem continuity_of_lub (hL : Foundations.Numbers.OF.LUBProperty K) (φ ψ : Pt K → Prop)
    (h : ∃ a, ∀ x y, φ x → ψ y → Bet a x y) : ∃ b, ∀ x y, φ x → ψ y → Bet x b y := by
  obtain ⟨a, ha⟩ := h
  by_cases hψ : ∃ y0, ψ y0
  case neg => exact ⟨a, fun x y _ hy => absurd ⟨y, hy⟩ hψ⟩
  obtain ⟨y0, hy0⟩ := hψ
  by_cases hφ : ∃ x1, φ x1 ∧ x1 ≠ a
  case neg =>
    refine ⟨a, fun x y hx _ => ?_⟩
    have : x = a := Classical.byContradiction fun hne => hφ ⟨x, hx, hne⟩
    subst this
    exact ⟨0, Std.le_refl 0, by grind, by grind, by grind⟩
  obtain ⟨x1, hx1, hx1a⟩ := hφ
  have hya : y0 ≠ a := by
    intro e
    subst e
    exact hx1a (bet_identity _ _ (ha x1 y0 hx1 hy0)).symm
  obtain ⟨wx, hwx⟩ : ∃ wx, wx = y0.x - a.x := ⟨_, rfl⟩
  obtain ⟨wy, hwy⟩ : ∃ wy, wy = y0.y - a.y := ⟨_, rfl⟩
  have hw : ¬ (wx = 0 ∧ wy = 0) := fun ⟨h₁, h₂⟩ => hya (ext' (by grind) (by grind))
  have uniq : ∀ t t' : K, t * wx = t' * wx → t * wy = t' * wy → t = t' := by
    intro t t' h₁ h₂
    by_cases hx : wx = 0
    · have : wy ≠ 0 := fun h' => hw ⟨hx, h'⟩
      grind
    · grind
  obtain ⟨t1, t10, t11, e1, e2⟩ := ha x1 y0 hx1 hy0
  have ht1 : t1 ≠ 0 := by
    intro h0
    exact hx1a (ext' (by grind) (by grind))
  -- every `ψ`-point lies on the ray from `a` through `y0`
  have hray : ∀ y, ψ y → ∃ s, 0 ≤ s ∧ y.x - a.x = s * wx ∧ y.y - a.y = s * wy := by
    intro y hy
    obtain ⟨l, l0, l1, f1, f2⟩ := ha x1 y hx1 hy
    have hl : l ≠ 0 := by
      intro h0
      exact hx1a (ext' (by grind) (by grind))
    obtain ⟨d0, -⟩ : 0 ≤ (t1 / l) ∧ True := by
      refine ⟨?_, trivial⟩
      rw [Field.div_eq_mul_inv]
      exact OrderedRing.mul_nonneg t10
        (by have := Field.IsOrdered.inv_pos_iff.2 (by grind : 0 < l); grind)
    exact ⟨t1 / l, d0, by grind, by grind⟩
  -- parameters of `φ`-points are at most those of `ψ`-points
  have hle : ∀ x y t s, φ x → ψ y → x.x - a.x = t * wx → x.y - a.y = t * wy →
      y.x - a.x = s * wx → y.y - a.y = s * wy → 0 ≤ s → t ≤ s := by
    intro x y t s hx hy g1 g2 g3 g4 hs
    obtain ⟨m, _, m1, k1, k2⟩ := ha x y hx hy
    have : t = m * s := uniq _ _ (by grind) (by grind)
    have := mul_le_of_le_one m1 hs
    grind
  let T : K → Prop := fun t => ∃ x, φ x ∧ x.x - a.x = t * wx ∧ x.y - a.y = t * wy
  obtain ⟨L, hLub, hLleast⟩ := hL T ⟨t1, x1, hx1, by grind, by grind⟩
    ⟨1, fun t ⟨x, hx, g1, g2⟩ => hle x y0 t 1 hx hy0 g1 g2 (by grind) (by grind) (by grind)⟩
  refine ⟨⟨a.x + L * wx, a.y + L * wy⟩, fun x y hx hy => ?_⟩
  obtain ⟨t, _, _, g1, g2⟩ := ha x y0 hx hy0
  have htL : t ≤ L := hLub t ⟨x, hx, by grind, by grind⟩
  obtain ⟨s, hs0, g3, g4⟩ := hray y hy
  have hLs : L ≤ s := hLleast s fun t' ⟨x', hx', k1, k2⟩ => hle x' y t' s hx' hy k1 k2 g3 g4 hs0
  exact bet_of_line (o := a) (w := ⟨wx, wy⟩) (α := t) (β := L) (γ := s)
    ⟨by grind, by grind⟩ ⟨rfl, rfl⟩ ⟨by grind, by grind⟩ (Or.inl ⟨htL, hLs⟩)

end Pt

/-! ## ℝ² is a Tarski plane -/

open Foundations.Numbers

/-- Non-negative reals have square roots (Part II's `n`-th root theorem with `n = 2`). -/
theorem R.exists_sqrt {z : R} (hz : 0 ≤ z) : ∃ r : R, 0 ≤ r ∧ r * r = z := by
  obtain ⟨r, hr, e⟩ := R.exists_nth_root hz (n := 2) (by omega)
  exact ⟨r, hr, by rw [← e]; grind⟩

/-- **ℝ² is a model of Tarski's axioms** for plane Euclidean geometry, with betweenness
and equidistance defined by coordinates. Segment construction uses square roots of
reals; continuity uses the completeness of `ℝ`. -/
noncomputable instance cartesianPlane : TarskiPlane (Pt R) where
  B := Pt.Bet
  Cong := Pt.Cong
  cong_pseudo_refl := Pt.cong_pseudo_refl
  cong_inner_trans := Pt.cong_inner_trans
  cong_identity := Pt.cong_identity
  segment_construction := Pt.segment_construction_of_sqrt fun _ hz => R.exists_sqrt hz
  five_segment := Pt.five_segment
  bet_identity := Pt.bet_identity
  pasch := Pt.pasch
  lower_dim := Pt.lower_dim
  upper_dim := Pt.upper_dim
  euclid := Pt.euclid
  continuity := Pt.continuity_of_lub R.exists_lub

/-- **Consistency of Euclidean geometry relative to the reals**: Tarski's axioms have a
model (`ℝ²`). -/
theorem tarski_consistent : Nonempty (TarskiPlane (Pt R)) := ⟨cartesianPlane⟩

end Foundations.Geometry
