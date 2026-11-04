import Foundations.Langlands.Modular.FundamentalDomain

/-!
# Points of F have maximal height; interior points are inequivalent

The existence half of the fundamental-domain theorem (`FundamentalDomain`) moved every point
into `F = {|Re τ| ≤ 1/2, |τ| ≥ 1}`. This file proves the converse estimates.

* **Height is maximal on F** (`one_le_Q_of_mem_F`, `im_smul_le_of_mem_F`). For `τ = x + iy ∈ F`
  and any bottom row `(c, d) ≠ (0, 0)`,

    `|cτ + d|² = c²|τ|² + 2cdx + d² ≥ c² − |cd| + d² ≥ 1`,

  using `|τ| ≥ 1`, `|x| ≤ 1/2` and the integer inequality `c² ∓ cd + d² ≥ 1`
  (`int_quad_ge_one`). Hence `Im (γτ) ≤ Im τ` for every `γ ∈ SL₂(ℤ)`.

* **Interior points** (`eq_of_interior`). If `τ` and `γτ` both lie in the interior
  `|Re| < 1/2, |τ| > 1`, then both heights are maximal, so they agree and `|cτ + d|² = 1`.
  With strict inequalities this forces `c = 0`; then `γ = ±T^b`, so `γτ = τ + n` with
  `|n| < 1`, i.e. `γτ = τ`.

So the interior of `F` maps injectively to the orbit space `SL₂(ℤ)\ℍ`. (The identifications
on the boundary — `τ ↦ τ + 1` on the vertical sides and `τ ↦ −1/τ` on the arc — and the
stabilisers of `i` and `ρ = e^{2πi/3}` are not treated here.)
-/

namespace Foundations.Langlands.Modular

open Foundations.Numbers Foundations.Algebra Foundations.Algebra.Group Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

namespace SL2Z

/-- **The interior of F.** `|Re τ| < 1/2` and `|τ|² > 1`. -/
def InFInterior (z : C) : Prop := OF.abs z.re < 1 / 2 ∧ 1 < C.normSq z

/-- An integer square is non-negative. -/
theorem int_mul_self_nonneg (c : Int) : 0 ≤ c * c := by
  rcases Int.le_total 0 c with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

/-- The square of a non-zero integer is positive. -/
theorem int_mul_self_pos {c : Int} (hc : c ≠ 0) : 0 < c * c := by
  rcases Int.lt_or_gt_of_ne hc with h | h
  · have := Int.mul_pos (Int.neg_pos_of_neg h) (Int.neg_pos_of_neg h)
    rwa [Int.neg_mul_neg] at this
  · exact Int.mul_pos h h

/-- For integers not both zero, `c² ± cd + d² ≥ 1`, in the form
`cd + 1 ≤ c² + d²` and `−cd + 1 ≤ c² + d²`. -/
theorem int_quad_ge_one {c d : Int} (h : c ≠ 0 ∨ d ≠ 0) :
    c * d + 1 ≤ c * c + d * d ∧ -(c * d) + 1 ≤ c * c + d * d := by
  have hc := int_mul_self_nonneg c
  have hd := int_mul_self_nonneg d
  have hm := int_mul_self_nonneg (c - d)
  have hp := int_mul_self_nonneg (c + d)
  have em : (c - d) * (c - d) = c * c + d * d - 2 * (c * d) := by grind
  have ep : (c + d) * (c + d) = c * c + d * d + 2 * (c * d) := by grind
  have hpos : 1 ≤ c * c + d * d := by
    rcases h with h | h
    · have : 0 < c * c := int_mul_self_pos h
      omega
    · have : 0 < d * d := int_mul_self_pos h
      omega
  generalize c * c = A at *
  generalize d * d = B at *
  generalize c * d = P at *
  generalize (c - d) * (c - d) = X at *
  generalize (c + d) * (c + d) = Y at *
  omega

/-- The bottom row of a matrix in SL₂(ℤ) is never `(0, 0)`. -/
theorem bottom_ne_zero (g : SL2Z) : g.c ≠ 0 ∨ g.d ≠ 0 := by
  apply Classical.byContradiction; intro h
  have hc : g.c = 0 := Classical.byContradiction fun hc => h (Or.inl hc)
  have hd : g.d = 0 := Classical.byContradiction fun hd => h (Or.inr hd)
  have := g.det; rw [hc, hd] at this; simp at this

/-- The expansion `|cτ + d|² = c²|τ|² + 2cd·Re τ + d²`. -/
theorem Q_expand (z : C) (c d : Int) :
    Q z c d = (c : R) * (c : R) * C.normSq z + 2 * ((c : R) * (d : R)) * z.re +
      (d : R) * (d : R) := by
  unfold Q C.normSq; grind

/-- The cross term is at least `−|cd|`: `2cd·x ≥ −cd` and `2cd·x ≥ cd` according to the sign
of `cd`, when `|x| ≤ 1/2`. -/
theorem cross_term {P x : R} (hx : OF.abs x ≤ 1 / 2) :
    (0 ≤ P → -P ≤ 2 * P * x) ∧ (P ≤ 0 → P ≤ 2 * P * x) := by
  obtain ⟨h1, h2⟩ := OF.abs_le.1 hx
  constructor
  · intro hP
    have := OrderedRing.mul_le_mul_of_nonneg_left h1 hP
    grind
  · intro hP
    have := OrderedRing.mul_le_mul_of_nonpos_left h2 hP
    grind

/-- **Lower bound for the automorphy factor on F.** For `τ ∈ F` and any `γ ∈ SL₂(ℤ)`,
`|cτ + d|² ≥ c² − |cd| + d² ≥ 1`. The first form is recorded with an extra term
`c²(|τ|² − 1)`. -/
theorem Q_lower (g : SL2Z) {z : C} (hF : OF.abs z.re ≤ 1 / 2) :
    1 + (g.c : R) * (g.c : R) * (C.normSq z - 1) ≤ Q z g.c g.d := by
  rw [Q_expand]
  obtain ⟨hq1, hq2⟩ := int_quad_ge_one (bottom_ne_zero g)
  have cast1 : ((g.c * g.d + 1 : Int) : R) ≤ ((g.c * g.c + g.d * g.d : Int) : R) :=
    intCast_le_of_le hq1
  have cast2 : ((-(g.c * g.d) + 1 : Int) : R) ≤ ((g.c * g.c + g.d * g.d : Int) : R) :=
    intCast_le_of_le hq2
  simp only [Ring.intCast_add, Ring.intCast_mul, Ring.intCast_neg, Ring.intCast_one] at cast1 cast2
  obtain ⟨hpos, hneg⟩ := cross_term (P := (g.c : R) * (g.d : R)) hF
  rcases Classical.em (0 ≤ (g.c : R) * (g.d : R)) with h | h
  · have := hpos h; grind
  · have := hneg (by grind); grind

/-- **Points of F have |cτ + d| ≥ 1.** -/
theorem one_le_Q_of_mem_F (g : SL2Z) {z : C} (hF : InF z) : 1 ≤ Q z g.c g.d := by
  have h := Q_lower g hF.1
  have h2 := hF.2
  have := OrderedRing.mul_nonneg (C.mul_self_nonneg (g.c : R)) (by grind : 0 ≤ C.normSq z - 1)
  grind

/-- **Height is maximal on F.** If `τ ∈ F` then `Im (γτ) ≤ Im τ` for every `γ ∈ SL₂(ℤ)`. -/
theorem im_smul_le_of_mem_F (g : SL2Z) {p : UHP} (hF : InF p.z) : (g • p).z.im ≤ p.z.im := by
  rw [im_smul, normSq_denom_eq_Q]
  have h := div_le_div_left p.pos (by grind : (0 : R) < 1) (one_le_Q_of_mem_F g hF)
  have e : p.z.im / 1 = p.z.im := by grind
  grind

/-- If `c ≠ 0` and `τ` is in the interior of `F`, then `|cτ + d|² > 1`. -/
theorem one_lt_Q_of_interior (g : SL2Z) (hc : g.c ≠ 0) {z : C} (hF : InFInterior z) :
    1 < Q z g.c g.d := by
  have h := Q_lower g (z := z) (by have := hF.1; grind)
  have hcc : (0 : R) < (g.c : R) * (g.c : R) := by
    have h1 : (0 : Int) < g.c * g.c := int_mul_self_pos hc
    have := (OF.intCast_lt (K := R)).2 h1
    rw [Ring.intCast_zero, Ring.intCast_mul] at this; exact this
  have := OrderedRing.mul_pos hcc (by have := hF.2; grind : (0 : R) < C.normSq z - 1)
  grind

/-- If `0 < y`, `0 < Q` and `y / Q = y` then `Q = 1`. -/
theorem eq_one_of_div_eq {y Q : R} (hy : 0 < y) (hQ : 0 < Q) (h : y / Q = y) : Q = 1 := by
  have hQ0 : Q ≠ 0 := by grind
  have hy0 : y ≠ 0 := by grind
  have : y = y * Q := by
    calc y = y / Q * Q := by grind
      _ = y * Q := by rw [h]
  have e : y * (Q - 1) = 0 := by grind
  rcases Classical.em (Q - 1 = 0) with h1 | h1
  · grind
  · exfalso
    have := Field.mul_inv_cancel hy0
    have : (y⁻¹ * y) * (Q - 1) = 0 := by grind
    grind

/-- A matrix with `c = 0` acts as an integer translation: `γτ = τ + n`. -/
theorem exists_translate_of_c_eq_zero {g : SL2Z} (hc : g.c = 0) (z : C) :
    ∃ n : Int, mob g z = mob (Tn n) z := by
  have hdet := g.det
  rw [hc, Int.mul_zero, Int.sub_zero] at hdet
  have hunit : g.d = 1 ∨ g.d = -1 := by
    have h2 : g.d.natAbs * g.a.natAbs = 1 := by rw [← Int.natAbs_mul, Int.mul_comm, hdet]; rfl
    have : g.d.natAbs = 1 := Nat.eq_one_of_mul_eq_one_right h2
    omega
  rcases hunit with hd | hd
  · have ha : g.a = 1 := by rw [hd] at hdet; omega
    have hg : g = Tn g.b := ext ha rfl hc hd
    refine ⟨g.b, ?_⟩
    generalize g.b = b at hg ⊢
    rw [hg]
  · have ha : g.a = -1 := by rw [hd] at hdet; omega
    have hg : g = neg (Tn (-g.b)) := ext (by simp [neg, Tn, ha]) (by simp [neg, Tn])
      (by simp [neg, Tn, hc]) (by simp [neg, Tn, hd])
    refine ⟨-g.b, ?_⟩
    generalize -g.b = b at hg ⊢
    rw [hg, mob_neg]

/-- **Interior points of F are inequivalent.** If `τ` and `γτ` both lie in the interior of
`F`, then `γτ = τ`. -/
theorem eq_of_interior (g : SL2Z) (p : UHP) (hp : InFInterior p.z)
    (hq : InFInterior (g • p).z) : g • p = p := by
  have hpF : InF p.z := ⟨by have := hp.1; grind, by have := hp.2; grind⟩
  have hqF : InF (g • p).z := ⟨by have := hq.1; grind, by have := hq.2; grind⟩
  have h1 := im_smul_le_of_mem_F g hpF
  have h2 := im_smul_le_of_mem_F g⁻¹ hqF
  rw [MulAction.inv_smul_smul] at h2
  have heq : (g • p).z.im = p.z.im := by grind
  rw [im_smul, normSq_denom_eq_Q] at heq
  have hQ := eq_one_of_div_eq p.pos (Q_pos g p.pos) heq
  have hc : g.c = 0 := by
    apply Classical.byContradiction; intro hc
    have := one_lt_Q_of_interior g hc hp; grind
  obtain ⟨n, hn⟩ := exists_translate_of_c_eq_zero hc p.z
  have hre : (g • p).z.re = p.z.re + (n : R) := by rw [smul_z, hn, re_mob_Tn]
  have hn0 : n = 0 := by
    obtain ⟨a1, a2⟩ := OF.abs_lt.1 hp.1
    obtain ⟨b1, b2⟩ := OF.abs_lt.1 hq.1
    have u1 : (n : R) < ((1 : Int) : R) := by rw [Ring.intCast_one]; grind
    have u2 : ((-1 : Int) : R) < (n : R) := by rw [Ring.intCast_neg, Ring.intCast_one]; grind
    have := (OF.intCast_lt (K := R)).1 u1
    have := (OF.intCast_lt (K := R)).1 u2
    omega
  apply UHP.ext
  rw [smul_z, hn, hn0, mob_Tn, Ring.intCast_zero]
  grind

end SL2Z

end Foundations.Langlands.Modular
