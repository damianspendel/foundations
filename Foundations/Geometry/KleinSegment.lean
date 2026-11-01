import Foundations.Geometry.KleinModel

/-!
# The Klein model: segment construction and the five-segment axiom

The two remaining Tarski axioms for the Klein model involve *measuring*.

**Segment construction** asks for a point `x` on a given ray from `a` with
`Q(a, x)` equal to a prescribed value `K ≥ 1`. Along the ray `x = a + s u` the
condition is a quadratic equation in `s` with a positive leading coefficient and
a non-positive constant term, so it has a non-negative root; one checks that the
root lies inside the disc (the boundary is infinitely far away). The square root
comes from the completeness of `ℝ` (Part II).

**The five-segment axiom** is a hyperbolic Stewart theorem. Write
`ch a b = √Q(a, b)` for the hyperbolic cosine of the distance. If `b` lies on the
chord from `a` to `c`, then for *every* point `z`

  `ch(b, z) = λ · ch(a, z) + μ · ch(c, z)`

with coefficients `λ, μ ≥ 0` depending only on `a, b, c` (this is linearity of
`1 − b·z` in `b`, i.e. the hyperboloid model in disguise). Putting `z = a, b, c`
gives three equations which pin down `λ`, `μ` and `γ = ch(a, c)` from
`p = ch(a, b)` and `q = ch(b, c)` alone: `γ` is a root of
`γ² − 2pqγ + p² + q² − 1 = 0` (the hyperbolic law `cosh(u+v) = cosh u cosh v +
sinh u sinh v`), and it is the *larger* root because `γ − pq = λμ(γ² − 1) ≥ 0`.
So two configurations with the same `p`, `q` have the same `λ`, `μ`, and the
equation for `z = d` transfers `ch(a, d)`, `ch(b, d)` to `ch(c, d)`.
-/

set_option linter.unusedSectionVars false

namespace Foundations.Geometry

open Lean.Grind Foundations.Numbers

namespace Klein

/-! ## Segment construction -/

/-- `σ = (r − B)/(2A)` with `r² = B² + 4AC` solves `Aσ² + Bσ − C = 0`. -/
theorem quad_root {A B C r σ : R} (hA : A ≠ 0) (hr : r * r = B * B + 4 * A * C)
    (hσ : (r - B) / (2 * A) = σ) : A * (σ * σ) + B * σ - C = 0 := by
  have h2A : 2 * A ≠ 0 := by grind
  have h2 : 2 * A * σ = r - B := by rw [← hσ]; grind
  have hsq : (2 * A * σ) * (2 * A * σ) = (r - B) * (r - B) := by rw [h2]
  have hB2 : B * (2 * A * σ) = B * (r - B) := by rw [h2]
  have h4 : 4 * A * (A * (σ * σ) + B * σ - C) = 0 := by grind
  have h4' : 4 * A ≠ 0 := by grind
  grind

/-- On the ray from `a` (inside the disc) in a direction `u ≠ 0`, every value `K ≥ 1` of
the invariant is attained, at a point inside the disc. -/
theorem exists_on_ray {a u : Pt R} (ha : n2 a < 1) (hu : 0 < n2 u) {K : R} (hK : 1 ≤ K) :
    ∃ σ : R, 0 ≤ σ ∧ n2 ⟨a.x + σ * u.x, a.y + σ * u.y⟩ < 1 ∧
      inv a ⟨a.x + σ * u.x, a.y + σ * u.y⟩ = K := by
  obtain ⟨α, hα⟩ : ∃ α, α = 1 - n2 a := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = dot a u := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = n2 u := ⟨_, rfl⟩
  have αpos : 0 < α := by grind
  have γpos : 0 < γ := by grind
  have Kαγ : 0 < K * α * γ := OrderedRing.mul_pos (OrderedRing.mul_pos (by grind) αpos) γpos
  have Apos : 0 < β * β + K * α * γ := by have := sq_nonneg' β; grind
  have C0 : 0 ≤ (K - 1) * (α * α) := OrderedRing.mul_nonneg (by grind) (sq_nonneg' α)
  have D0 : 0 ≤ (2 * α * β * (K - 1)) * (2 * α * β * (K - 1)) +
      4 * (β * β + K * α * γ) * ((K - 1) * (α * α)) := by
    have := sq_nonneg' (2 * α * β * (K - 1))
    have := OrderedRing.mul_nonneg (Std.le_of_lt Apos) C0
    grind
  obtain ⟨r, r0, hr⟩ := R.exists_sqrt D0
  have rB : 2 * α * β * (K - 1) ≤ r := by
    by_cases hB : 2 * α * β * (K - 1) ≤ 0
    · grind
    · apply Pt.le_of_sq_le r0
      rw [hr]
      have := OrderedRing.mul_nonneg (Std.le_of_lt Apos) C0
      grind
  have hA : β * β + K * α * γ ≠ 0 := by grind
  refine ⟨(r - 2 * α * β * (K - 1)) / (2 * (β * β + K * α * γ)), ?_, ?_⟩
  · rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg (by grind)
      (by have := Field.IsOrdered.inv_pos_iff.2 (by grind : (0 : R) < 2 * (β * β + K * α * γ))
          grind)
  generalize hσ : (r - 2 * α * β * (K - 1)) / (2 * (β * β + K * α * γ)) = σ
  -- the quadratic equation
  have quad : (β * β + K * α * γ) * (σ * σ) + 2 * α * β * (K - 1) * σ - (K - 1) * (α * α) = 0 := by
    obtain ⟨A, hAdef⟩ : ∃ A, A = β * β + K * α * γ := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B, B = 2 * α * β * (K - 1) := ⟨_, rfl⟩
    obtain ⟨C, hCdef⟩ : ∃ C, C = (K - 1) * (α * α) := ⟨_, rfl⟩
    have hA' : A ≠ 0 := by rw [hAdef]; exact hA
    have hσ' : (r - B) / (2 * A) = σ := by rw [hAdef, hBdef]; exact hσ
    have hr' : r * r = B * B + 4 * A * C := by rw [hAdef, hBdef, hCdef]; exact hr
    have goal : A * (σ * σ) + B * σ - C = 0 := quad_root hA' hr' hσ'
    rw [hAdef, hBdef, hCdef] at goal
    exact goal
  have E : (α - σ * β) * (α - σ * β) = K * α * (α - 2 * σ * β - σ * σ * γ) := by grind
  have hn2 : 1 - n2 ⟨a.x + σ * u.x, a.y + σ * u.y⟩ = α - 2 * σ * β - σ * σ * γ := by
    rw [hα, hβ, hγ]; unfold n2 dot; grind
  have hdot : 1 - dot a ⟨a.x + σ * u.x, a.y + σ * u.y⟩ = α - σ * β := by
    rw [hα, hβ]; unfold n2 dot; grind
  have hne : α - σ * β ≠ 0 := by
    intro h0
    have : K * α * (α - 2 * σ * β - σ * σ * γ) = 0 := by rw [← E, h0]; grind
    have hKα : K * α ≠ 0 := by have := OrderedRing.mul_pos (by grind : (0 : R) < K) αpos; grind
    have : α - 2 * σ * β - σ * σ * γ = 0 := by grind
    have := OrderedRing.mul_nonneg (sq_nonneg' σ) (Std.le_of_lt γpos)
    grind
  have sqpos : 0 < (α - σ * β) * (α - σ * β) := by
    have := sq_nonneg' (α - σ * β)
    rcases Std.le_iff_lt_or_eq.1 this with h | h
    · exact h
    · exact absurd (by grind : α - σ * β = 0) hne
  have inside : 0 < α - 2 * σ * β - σ * σ * γ := by
    apply Classical.byContradiction
    intro hn
    have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : α - 2 * σ * β - σ * σ * γ ≤ 0)
      (Std.le_of_lt (OrderedRing.mul_pos (by grind : (0 : R) < K) αpos))
    grind
  refine ⟨by grind, ?_⟩
  unfold inv
  have e1 : (1 - dot a ⟨a.x + σ * u.x, a.y + σ * u.y⟩) = α - σ * β := hdot
  rw [e1, hn2, ← hα, E]
  have : α * (α - 2 * σ * β - σ * σ * γ) ≠ 0 := by
    have := OrderedRing.mul_pos αpos inside; grind
  grind

/-- (A4) **Segment construction** in the Klein model. -/
theorem segment_construction (q a b c : KPt) : ∃ x, KBet q a x ∧ KCong a x b c := by
  have hK := one_le_inv b.2 c.2
  by_cases hqa : q = a
  · subst hqa
    obtain ⟨σ, _, hin, hinv⟩ := exists_on_ray (u := ⟨1, 0⟩) q.2 (by unfold n2; grind) hK
    exact ⟨⟨_, hin⟩, ⟨0, Std.le_refl 0, by grind, by grind, by grind⟩, hinv⟩
  · have hu : 0 < n2 ⟨a.1.x - q.1.x, a.1.y - q.1.y⟩ := by
      have := Pt.d2_pos (fun h => hqa (Subtype.ext h.symm) : a.1 ≠ q.1)
      unfold Pt.d2 at this; unfold n2; grind
    obtain ⟨σ, σ0, hin, hinv⟩ := exists_on_ray a.2 hu hK
    obtain ⟨t0, t1⟩ := div_mem_unit (u := 1) (v := 1 + σ) (by grind) (by grind) (by grind)
    have : 1 + σ ≠ 0 := by grind
    refine ⟨⟨_, hin⟩, ⟨1 / (1 + σ), t0, t1, ?_, ?_⟩, hinv⟩ <;> dsimp only <;> grind

/-! ## The hyperbolic Stewart relation -/

/-- Clearing the denominators of `ch`: `s_x s_z ch(x, z) = 1 − x·z`. -/
theorem ch_mul {x z : Pt R} (hx : n2 x < 1) (hz : n2 z < 1) : s x * s z * ch x z = 1 - dot x z := by
  obtain ⟨sx, -⟩ := s_spec hx
  obtain ⟨sz, -⟩ := s_spec hz
  have : s x * s z ≠ 0 := by have := OrderedRing.mul_pos sx sz; grind
  unfold ch
  grind

/-- **Linearity along a chord**: if `b = a + t (c − a)` then for every `z` in the disc,
`s_b · ch(b, z) = (1 − t) s_a · ch(a, z) + t s_c · ch(c, z)`. -/
theorem stewart_ch {a b c z : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) (hc : n2 c < 1)
    (hz : n2 z < 1) {t : R} (hx : b.x - a.x = t * (c.x - a.x)) (hy : b.y - a.y = t * (c.y - a.y)) :
    s b * ch b z = (1 - t) * s a * ch a z + t * s c * ch c z := by
  obtain ⟨sa, -⟩ := s_spec ha
  obtain ⟨sb, -⟩ := s_spec hb
  obtain ⟨sc, -⟩ := s_spec hc
  obtain ⟨sz, -⟩ := s_spec hz
  have ex : b.x = a.x + t * (c.x - a.x) := by grind
  have ey : b.y = a.y + t * (c.y - a.y) := by grind
  have ha' := ch_mul ha hz
  have hb' := ch_mul hb hz
  have hc' := ch_mul hc hz
  have lin : 1 - dot b z = (1 - t) * (1 - dot a z) + t * (1 - dot c z) := by
    unfold dot; rw [ex, ey]; grind
  have key : s z * (s b * ch b z) = s z * ((1 - t) * s a * ch a z + t * s c * ch c z) := by
    grind
  have : s z ≠ 0 := by grind
  grind

/-- **The determination lemma.** If `1 = λp + μq`, `p = λ + μγ`, `q = λγ + μ` with
`λ ≥ 0`, `μ > 0`, `γ > 1`, and the same holds for `λ', μ', γ'` with the *same* `p, q`,
then `λ = λ'` and `μ = μ'`. -/
theorem determination {p q l m g l' m' g' : R} (hl : 0 ≤ l) (hm : 0 < m) (hg : 1 < g)
    (hl' : 0 ≤ l') (hm' : 0 < m') (hg' : 1 < g')
    (e₁ : 1 = l * p + m * q) (e₂ : p = l + m * g) (e₃ : q = l * g + m)
    (e₁' : 1 = l' * p + m' * q) (e₂' : p = l' + m' * g') (e₃' : q = l' * g' + m') :
    l = l' ∧ m = m' := by
  -- `γ` solves `γ² − 2pqγ + p² + q² − 1 = 0`
  have hl1 : l * (1 - g * g) = p - q * g := by rw [e₂, e₃]; grind
  have hm1 : m * (1 - g * g) = q - p * g := by rw [e₂, e₃]; grind
  have hl1' : l' * (1 - g' * g') = p - q * g' := by rw [e₂', e₃']; grind
  have hm1' : m' * (1 - g' * g') = q - p * g' := by rw [e₂', e₃']; grind
  have quad : g * g - 2 * p * q * g + p * p + q * q - 1 = 0 := by
    have k₀ : (1 - g * g) = (l * p + m * q) * (1 - g * g) := by rw [← e₁]; grind
    have k₁ : p * (l * (1 - g * g)) = p * (p - q * g) := by rw [hl1]
    have k₂ : q * (m * (1 - g * g)) = q * (q - p * g) := by rw [hm1]
    grind
  have quad' : g' * g' - 2 * p * q * g' + p * p + q * q - 1 = 0 := by
    have k₀ : (1 - g' * g') = (l' * p + m' * q) * (1 - g' * g') := by rw [← e₁']; grind
    have k₁ : p * (l' * (1 - g' * g')) = p * (p - q * g') := by rw [hl1']
    have k₂ : q * (m' * (1 - g' * g')) = q * (q - p * g') := by rw [hm1']
    grind
  -- and it is the larger root: `γ − pq = λμ(γ² − 1) ≥ 0`
  have ge : g - p * q = l * m * (g * g - 1) := by
    have e1s : 1 = l * (l + m * g) + m * (l * g + m) := by rw [e₂, e₃] at e₁; exact e₁
    have k : g = (l * (l + m * g) + m * (l * g + m)) * g := by rw [← e1s]; grind
    rw [e₂, e₃]
    grind
  have ge' : g' - p * q = l' * m' * (g' * g' - 1) := by
    have e1s : 1 = l' * (l' + m' * g') + m' * (l' * g' + m') := by rw [e₂', e₃'] at e₁'; exact e₁'
    have k : g' = (l' * (l' + m' * g') + m' * (l' * g' + m')) * g' := by rw [← e1s]; grind
    rw [e₂', e₃']
    grind
  have ge0 := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hl (Std.le_of_lt hm))
    (by have := OrderedRing.mul_lt_mul_of_pos_left hg (by grind : (0 : R) < g); grind :
      (0 : R) ≤ g * g - 1)
  have ge0' := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hl' (Std.le_of_lt hm'))
    (by have := OrderedRing.mul_lt_mul_of_pos_left hg' (by grind : (0 : R) < g'); grind :
      (0 : R) ≤ g' * g' - 1)
  have hgg : g = g' := by
    have hprod : (g - g') * (g + g' - 2 * p * q) = 0 := by grind
    by_cases h : g - g' = 0
    · grind
    · have : g + g' - 2 * p * q = 0 := by grind
      grind
  subst hgg
  have hne : 1 - g * g ≠ 0 := by
    have := OrderedRing.mul_lt_mul_of_pos_left hg (by grind : (0 : R) < g); grind
  have hl2 : l * (1 - g * g) = l' * (1 - g * g) := by rw [hl1, hl1']
  have hm2 : m * (1 - g * g) = m' * (1 - g * g) := by rw [hm1, hm1']
  exact ⟨by grind, by grind⟩

/-! ## The five-segment axiom -/

/-- The data of a point `b` on the chord `ac`: coefficients `λ, μ` with
`ch(b, z) = λ ch(a, z) + μ ch(c, z)` for all `z`, `λ ≥ 0`, and `μ > 0` when `a ≠ b`. -/
theorem chord_coeffs {a b c : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) (hc : n2 c < 1)
    (hab : a ≠ b) (h : Pt.Bet a b c) :
    ∃ l m : R, 0 ≤ l ∧ 0 < m ∧ ∀ z, n2 z < 1 → ch b z = l * ch a z + m * ch c z := by
  obtain ⟨t, t0, t1, hx, hy⟩ := h
  obtain ⟨sa, -⟩ := s_spec ha
  obtain ⟨sb, -⟩ := s_spec hb
  obtain ⟨sc, -⟩ := s_spec hc
  have ht : t ≠ 0 := by
    intro h0
    exact hab (Pt.ext' (by rw [h0] at hx; grind) (by rw [h0] at hy; grind))
  have hsb : s b ≠ 0 := by grind
  refine ⟨(1 - t) * s a / s b, t * s c / s b, ?_, ?_, fun z hz => ?_⟩
  · rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (by grind) (by grind))
      (by have := Field.IsOrdered.inv_pos_iff.2 sb; grind)
  · rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_pos (OrderedRing.mul_pos (by grind) sc) (Field.IsOrdered.inv_pos_iff.2 sb)
  · have := stewart_ch ha hb hc hz hx hy
    grind

/-- `ch a b = 1` only for `a = b`. -/
theorem eq_of_ch_eq_one {a b : Pt R} (ha : n2 a < 1) (hb : n2 b < 1) (h : ch a b = 1) : a = b :=
  eq_of_inv_eq_one ha hb (by rw [← ch_mul_self ha hb, h]; grind)

/-- (A5) **The five-segment axiom** in the Klein model. -/
theorem five_segment (a b c d a' b' c' d' : KPt) (hab : a ≠ b) (h₁ : KBet a b c)
    (h₂ : KBet a' b' c') (e₁ : KCong a b a' b') (e₂ : KCong b c b' c') (e₃ : KCong a d a' d')
    (e₄ : KCong b d b' d') : KCong c d c' d' := by
  have hab₁ : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  have h₁' : Pt.Bet a.1 b.1 c.1 := h₁
  have h₂' : Pt.Bet a'.1 b'.1 c'.1 := h₂
  have hab' : a'.1 ≠ b'.1 := by
    intro h
    have : inv a.1 b.1 = 1 := by
      unfold KCong at e₁; rw [e₁, h, inv_self b'.2]
    exact hab₁ (eq_of_inv_eq_one a.2 b.2 this)
  unfold KCong at *
  rw [inv_eq_iff_ch_eq a.2 b.2 a'.2 b'.2] at e₁
  rw [inv_eq_iff_ch_eq b.2 c.2 b'.2 c'.2] at e₂
  rw [inv_eq_iff_ch_eq a.2 d.2 a'.2 d'.2] at e₃
  rw [inv_eq_iff_ch_eq b.2 d.2 b'.2 d'.2] at e₄
  rw [inv_eq_iff_ch_eq c.2 d.2 c'.2 d'.2]
  obtain ⟨l, m, hl, hm, hz⟩ := chord_coeffs a.2 b.2 c.2 hab₁ h₁
  obtain ⟨l', m', hl', hm', hz'⟩ := chord_coeffs a'.2 b'.2 c'.2 hab' h₂
  -- `γ = ch(a, c) > 1`
  have hac : a.1 ≠ c.1 := by
    intro h
    rw [← h] at h₁'
    exact hab₁ (Pt.bet_identity _ _ h₁')
  have hac' : a'.1 ≠ c'.1 := by
    intro h
    rw [← h] at h₂'
    exact hab' (Pt.bet_identity _ _ h₂')
  have hg : 1 < ch a.1 c.1 := by
    have := one_le_ch a.2 c.2
    have : ch a.1 c.1 ≠ 1 := fun h => hac (eq_of_ch_eq_one a.2 c.2 h)
    grind
  have hg' : 1 < ch a'.1 c'.1 := by
    have := one_le_ch a'.2 c'.2
    have : ch a'.1 c'.1 ≠ 1 := fun h => hac' (eq_of_ch_eq_one a'.2 c'.2 h)
    grind
  -- the three equations at `z = b, a, c`
  have E₁ := hz b.1 b.2
  have E₂ := hz a.1 a.2
  have E₃ := hz c.1 c.2
  have E₁' := hz' b'.1 b'.2
  have E₂' := hz' a'.1 a'.2
  have E₃' := hz' c'.1 c'.2
  rw [ch_self b.2] at E₁
  rw [ch_self a.2] at E₂
  rw [ch_self c.2] at E₃
  rw [ch_self b'.2] at E₁'
  rw [ch_self a'.2] at E₂'
  rw [ch_self c'.2] at E₃'
  have c₁ := ch_comm c.1 b.1
  have c₂ := ch_comm b.1 a.1
  have c₃ := ch_comm c.1 a.1
  have c₁' := ch_comm c'.1 b'.1
  have c₂' := ch_comm b'.1 a'.1
  have c₃' := ch_comm c'.1 a'.1
  have hp : ch a'.1 b'.1 = ch a.1 b.1 := e₁.symm
  have hq : ch b'.1 c'.1 = ch b.1 c.1 := e₂.symm
  obtain ⟨rfl, rfl⟩ := determination (p := ch a.1 b.1) (q := ch b.1 c.1) hl hm hg hl' hm' hg'
    (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
  -- transfer through `z = d`
  have Fd := hz d.1 d.2
  have Fd' := hz' d'.1 d'.2
  rw [← e₃, ← e₄] at Fd'
  have : m * ch c.1 d.1 = m * ch c'.1 d'.1 := by grind
  have : m ≠ 0 := by grind
  grind

end Klein

end Foundations.Geometry
