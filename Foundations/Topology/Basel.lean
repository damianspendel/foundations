import Foundations.Topology.Wallis

/-!
# The Basel problem: `Σ 1/n² = π²/6`

Pietro **Mengoli** asked in 1650 for the sum of the reciprocals of the squares; the Bernoullis in
Basel could not find it, and the question became known as the *Basel problem*. Leonhard **Euler**
solved it in 1734/35 — `1 + 1/4 + 1/9 + 1/16 + ⋯ = π²/6` — by treating `sin x / x` as an
"infinite polynomial" with roots `±π, ±2π, …`, a bold step justified only a century later.

We follow a short rigorous proof (Yuri Matsuoka, 1961) using only integrals. With

  `Aₙ = ∫₀^{π/2} cos^{2n} x dx`  and  `Bₙ = ∫₀^{π/2} x² cos^{2n} x dx`,

two integrations by parts give `A_{n+1} = (2n+1)/(2n+2) · Aₙ` (the Wallis recursion) and
`A_{n+1} = (n+1)(2n+1) Bₙ − 2(n+1)² B_{n+1}`. Dividing, the terms telescope:

  `1/(n+1)² = 2 Bₙ/Aₙ − 2 B_{n+1}/A_{n+1}`,  so  `Σ_{k=1}^{N} 1/k² = 2 B₀/A₀ − 2 B_N/A_N`,

and `2 B₀/A₀ = 2 (π/2)²/3 = π²/6`. Finally the error term vanishes: by **Jordan's inequality**
`x ≤ (π/2) sin x` on `[0, π/2]` (a consequence of the concavity of sine, proved with the mean value
theorem) we get `B_N ≤ (π/2)² (A_N − A_{N+1}) = (π/2)² A_N / (2N + 2)`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Wallis

/-- Cross-multiplication: `x/y = z/w` when `x w = z y` (for `y, w ≠ 0`). -/
theorem div_eq_div_of {x y z w : R} (hy : y ≠ 0) (hw : w ≠ 0) (h : x * w = z * y) : x / y = z / w := by
  have iy := Field.mul_inv_cancel hy
  have iw := Field.mul_inv_cancel hw
  rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]
  calc x * y⁻¹ = x * y⁻¹ * (w * w⁻¹) := by rw [iw, Semiring.mul_one]
    _ = (x * w) * y⁻¹ * w⁻¹ := by grind
    _ = (z * y) * y⁻¹ * w⁻¹ := by rw [h]
    _ = z * w⁻¹ * (y * y⁻¹) := by grind
    _ = z * w⁻¹ := by rw [iy, Semiring.mul_one]

/-! ## Jordan's inequality -/

/-- **Jordan's inequality**: `x ≤ (π/2) sin x` for `0 ≤ x ≤ π/2`. -/
theorem jordan {x : R} (h0 : 0 ≤ x) (h1 : x ≤ hpi) : x ≤ hpi * sin x := by
  have hp := hpi_pos
  have hpi_le : hpi ≤ pi := by unfold hpi; have := pi_pos; grind
  rcases (by grind : x = 0 ∨ x = hpi ∨ (0 < x ∧ x < hpi)) with e | e | ⟨e1, e2⟩
  · rw [e, sin_zero]; grind
  · rw [e, sin_hpi]; grind
  · apply Classical.byContradiction; intro hneg
    let g : R → R := fun t => hpi * sin t - t
    let g' : R → R := fun t => hpi * cos t - 1
    have hd : ∀ t, HasDerivAt g (g' t) t := fun t => by
      have := ((hasDerivAt_sin t).const_mul hpi).sub (hasDerivAt_id t)
      exact this
    obtain ⟨c₁, a1, a2, a3⟩ := mean_value (f := g) (f' := g') e1
      (fun t _ _ => (hd t).continuousAt) (fun t _ _ => hd t)
    obtain ⟨c₂, b1, b2, b3⟩ := mean_value (f := g) (f' := g') e2
      (fun t _ _ => (hd t).continuousAt) (fun t _ _ => hd t)
    have g0 : g 0 = 0 := by show hpi * sin 0 - 0 = 0; rw [sin_zero]; grind
    have gp : g hpi = 0 := by show hpi * sin hpi - hpi = 0; rw [sin_hpi]; grind
    have gx : g x < 0 := by show hpi * sin x - x < 0; grind
    rw [g0] at a3; rw [gp] at b3
    -- `g'(c₁) < 0 < g'(c₂)` but `g'` decreases.
    have k1 : g' c₁ < 0 := by
      apply Classical.byContradiction; intro h
      have := OrderedRing.mul_nonneg (by grind : 0 ≤ g' c₁) (by grind : (0 : R) ≤ x - 0); grind
    have k2 : 0 < g' c₂ := by
      apply Classical.byContradiction; intro h
      have := OrderedRing.mul_nonneg (by grind : 0 ≤ -g' c₂) (by grind : (0 : R) ≤ hpi - x); grind
    have k3 := cos_strictAnti (x := c₁) (y := c₂) (by grind) (by grind) (by grind)
    have k4 := OrderedRing.mul_lt_mul_of_pos_left k3 hp
    have : g' c₁ = hpi * cos c₁ - 1 := rfl
    have : g' c₂ = hpi * cos c₂ - 1 := rfl
    grind

/-! ## The integrals `Aₙ` and `Bₙ` -/

/-- `Aₙ = ∫₀^{π/2} cos^{2n} x dx`. -/
noncomputable def A (n : Nat) : R := I (2 * n)

/-- `Bₙ = ∫₀^{π/2} x² cos^{2n} x dx`. -/
noncomputable def B (n : Nat) : R := integral (fun x => x * x * cos x ^ (2 * n)) 0 hpi

/-- `x² cosᵏ x` is continuous. -/
theorem continuousAt_x2cos (k : Nat) (x : R) : R.ContinuousAt (fun y => y * y * cos y ^ k) x :=
  continuousAt_mul (continuousAt_mul (continuousAt_id x) (continuousAt_id x)) (continuousAt_cos_pow k x)

/-- The Wallis recursion for `A`: `(2n + 2) A_{n+1} = (2n + 1) Aₙ`. -/
theorem A_rec (n : Nat) : (2 * (n : R) + 2) * A (n + 1) = (2 * (n : R) + 1) * A n := by
  have := I_rec (2 * n)
  unfold A; rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  have c : ((2 * n : Nat) : R) = 2 * (n : R) := by grind
  rw [c] at this; grind

/-- `Aₙ > 0`. -/
theorem A_pos (n : Nat) : 0 < A n := I_pos _

/-- `A₀ = π/2`. -/
theorem A_zero : A 0 = hpi := I_zero

/-- `B₀ = (π/2)³/3`. -/
theorem B_zero : B 0 = hpi * hpi * hpi / 3 := by
  have hab := Std.le_of_lt hpi_pos
  unfold B
  rw [integral_eq_sub (F := fun x => 1 / 3 * (x * x * x)) hab (fun t _ _ => by
      have h := (((hasDerivAt_id t).mul (hasDerivAt_id t)).mul (hasDerivAt_id t)).const_mul (1 / 3)
      have e : 1 / 3 * ((1 * t + t * 1) * t + t * t * 1) = t * t * cos t ^ (2 * 0) := by
        show _ = t * t * 1; grind
      rw [e] at h; exact h) (fun t _ _ => continuousAt_x2cos _ t)]
  grind

/-- **The key identity** `A_{n+1} + 2(n+1)² B_{n+1} = (n+1)(2n+1) Bₙ` (two integrations by
parts, packaged as one application of the fundamental theorem of calculus). -/
theorem key (j : Nat) :
    A (j + 1) + 2 * ((j : R) + 1) * ((j : R) + 1) * B (j + 1) =
      ((j : R) + 1) * (2 * (j : R) + 1) * B j := by
  have hab := Std.le_of_lt hpi_pos
  let n1 : R := (j : R) + 1
  let g : R → R := fun x => cos x ^ (2 * j + 1 + 1) +
    (2 * n1 * n1 * (x * x * cos x ^ (2 * j + 1 + 1)) + (-(n1 * (2 * (j : R) + 1))) * (x * x * cos x ^ (2 * j)))
  let F : R → R := fun x => x * cos x ^ (2 * j + 1 + 1) + n1 * (x * x * (sin x * cos x ^ (2 * j + 1)))
  have hd : ∀ t, 0 ≤ t → t ≤ hpi → HasDerivAt F (g t) t := fun t _ _ => by
    have h := ((hasDerivAt_id t).mul (hasDerivAt_cos_pow (2 * j + 1) t)).add
      ((((hasDerivAt_id t).mul (hasDerivAt_id t)).mul
        ((hasDerivAt_sin t).mul (hasDerivAt_cos_pow (2 * j) t))).const_mul n1)
    have e : 1 * cos t ^ (2 * j + 1 + 1) + t * (((2 * j + 1 : Nat) + 1) * cos t ^ (2 * j + 1) * -sin t) +
        n1 * ((1 * t + t * 1) * (sin t * cos t ^ (2 * j + 1)) +
          t * t * (cos t * cos t ^ (2 * j + 1) + sin t * (((2 * j : Nat) + 1) * cos t ^ (2 * j) * -sin t)))
        = g t := by
      have p1 : cos t ^ (2 * j + 1) = cos t ^ (2 * j) * cos t := rfl
      have p2 : cos t ^ (2 * j + 1 + 1) = cos t ^ (2 * j) * cos t * cos t := rfl
      have py := sin_sq_add_cos_sq t
      have c1 : ((2 * j + 1 : Nat) : R) = 2 * (j : R) + 1 := by grind
      have c2 : ((2 * j : Nat) : R) = 2 * (j : R) := by grind
      show _ = cos t ^ (2 * j + 1 + 1) + (2 * n1 * n1 * (t * t * cos t ^ (2 * j + 1 + 1)) +
        (-(n1 * (2 * (j : R) + 1))) * (t * t * cos t ^ (2 * j)))
      rw [p1, p2, c1, c2]
      generalize cos t ^ (2 * j) = C
      show _ = _ + (2 * ((j : R) + 1) * ((j : R) + 1) * _ + -(((j : R) + 1) * _) * _)
      show _ + _ + ((j : R) + 1) * _ = _
      grind
    rw [e] at h; exact h
  have c3 : ∀ t, R.ContinuousAt (fun x => x * x * cos x ^ (2 * j + 1 + 1)) t := continuousAt_x2cos _
  have c4 : ∀ t, R.ContinuousAt (fun x => x * x * cos x ^ (2 * j)) t := continuousAt_x2cos _
  have hgc : ∀ t, R.ContinuousAt g t := fun t =>
    continuousAt_add (continuousAt_cos_pow _ t)
      (continuousAt_add (continuousAt_cmul _ (c3 t)) (continuousAt_cmul _ (c4 t)))
  have h1 := integral_eq_sub hab hd fun t _ _ => hgc t
  rw [integral_add' hab (continuousAt_cos_pow _) (fun t => continuousAt_add
      (continuousAt_cmul _ (c3 t)) (continuousAt_cmul _ (c4 t))),
    integral_add' hab (fun t => continuousAt_cmul _ (c3 t)) (fun t => continuousAt_cmul _ (c4 t)),
    integral_const_mul' _ hab c3, integral_const_mul' _ hab c4] at h1
  have hF0 : F 0 = 0 := by show 0 * _ + n1 * (0 * 0 * _) = 0; grind
  have hFp : F hpi = 0 := by
    show hpi * cos hpi ^ (2 * j + 1 + 1) + n1 * (hpi * hpi * (sin hpi * cos hpi ^ (2 * j + 1))) = 0
    rw [cos_hpi]
    have : (0 : R) ^ (2 * j + 1 + 1) = 0 := by show (0 : R) ^ (2 * j + 1) * 0 = 0; grind
    have : (0 : R) ^ (2 * j + 1) = 0 := by show (0 : R) ^ (2 * j) * 0 = 0; grind
    grind
  rw [hF0, hFp] at h1
  have eA : A (j + 1) = integral (fun x => cos x ^ (2 * j + 1 + 1)) 0 hpi := by
    unfold A I; rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
  have eB : B (j + 1) = integral (fun x => x * x * cos x ^ (2 * j + 1 + 1)) 0 hpi := by
    unfold B; rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
  have eB' : B j = integral (fun x => x * x * cos x ^ (2 * j)) 0 hpi := rfl
  rw [← eA, ← eB, ← eB'] at h1
  show _ = n1 * _ * _
  grind

/-- `Bₙ ≥ 0`. -/
theorem B_nonneg (n : Nat) : 0 ≤ B n := by
  have hab := Std.le_of_lt hpi_pos
  have := HasIntegral.mono hab (hasIntegral_const 0 hab)
    (hasIntegral_integral hab fun x _ _ => continuousAt_x2cos (2 * n) x) fun t h0 h1 => by
      have := pow_le_pow_left.pow_nonneg (cos_mem h0 h1).1 (2 * n)
      exact OrderedRing.mul_nonneg (OrderedRing.mul_nonneg h0 h0) this
  unfold B; grind

/-- **The error term is small**: `Bₙ ≤ (π/2)² Aₙ / (2n + 2)`. -/
theorem B_le (n : Nat) : B n ≤ hpi * hpi * (A n / (2 * (n : R) + 2)) := by
  have hab := Std.le_of_lt hpi_pos
  -- Pointwise: `x² cos^{2n} ≤ (π/2)² (cos^{2n} − cos^{2n+2})`.
  have hle := HasIntegral.mono hab
    (hasIntegral_integral hab fun x _ _ => continuousAt_x2cos (2 * n) x)
    (((hasIntegral_integral hab fun x _ _ => continuousAt_cos_pow (2 * n) x).const_mul (hpi * hpi)).add
      ((hasIntegral_integral hab fun x _ _ => continuousAt_cos_pow (2 * n + 1 + 1) x).const_mul
        (-(hpi * hpi)))) fun t h0 h1 => by
      have hj := jordan h0 h1
      have hsq : t * t ≤ hpi * sin t * (hpi * sin t) := by
        have := OrderedRing.mul_le_mul_of_nonneg_left hj h0
        have := OrderedRing.mul_le_mul_of_nonneg_right hj (Std.le_trans h0 hj)
        grind
      have hC := pow_le_pow_left.pow_nonneg (cos_mem h0 h1).1 (2 * n)
      have py := sin_sq_add_cos_sq t
      have k := OrderedRing.mul_le_mul_of_nonneg_right hsq hC
      show t * t * cos t ^ (2 * n) ≤ hpi * hpi * cos t ^ (2 * n) + -(hpi * hpi) * (cos t ^ (2 * n) * cos t * cos t)
      have ss : sin t * sin t = 1 - cos t * cos t := by grind
      have e : hpi * sin t * (hpi * sin t) * cos t ^ (2 * n) =
          hpi * hpi * cos t ^ (2 * n) + -(hpi * hpi) * (cos t ^ (2 * n) * cos t * cos t) := by
        rw [show hpi * sin t * (hpi * sin t) * cos t ^ (2 * n) =
          hpi * hpi * (sin t * sin t) * cos t ^ (2 * n) by grind, ss]
        grind
      rw [e] at k; exact k
  have eA : A (n + 1) = integral (fun x => cos x ^ (2 * n + 1 + 1)) 0 hpi := by
    unfold A I; rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
  have hr := A_rec n
  have hpos := A_pos n
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  unfold A at hr hpos ⊢; unfold B
  unfold A at eA
  rw [← eA] at hle
  have eI : integral (fun y => cos y ^ (2 * n)) 0 hpi = I (2 * n) := rfl
  rw [eI] at hle
  generalize I (2 * n) = a at *
  generalize I (2 * (n + 1)) = a' at *
  have h2 : (2 * (n : R) + 2) ≠ 0 := by grind
  have i := Field.mul_inv_cancel h2
  have ha' : a' = (2 * (n : R) + 1) * (2 * (n : R) + 2)⁻¹ * a := by
    calc a' = a' * ((2 * (n : R) + 2) * (2 * (n : R) + 2)⁻¹) := by rw [i, Semiring.mul_one]
      _ = ((2 * (n : R) + 2) * a') * (2 * (n : R) + 2)⁻¹ := by grind
      _ = ((2 * (n : R) + 1) * a) * (2 * (n : R) + 2)⁻¹ := by rw [hr]
      _ = _ := by grind
  rw [ha'] at hle
  rw [Field.div_eq_mul_inv]
  generalize (2 * (n : R) + 2)⁻¹ = J at *
  have hJ : 1 - (2 * (n : R) + 1) * J = J := by grind
  have e : hpi * hpi * a + -(hpi * hpi) * ((2 * (n : R) + 1) * J * a) = hpi * hpi * (a * J) := by
    rw [show hpi * hpi * a + -(hpi * hpi) * ((2 * (n : R) + 1) * J * a) =
      hpi * hpi * a * (1 - (2 * (n : R) + 1) * J) by grind, hJ]; grind
  rw [e] at hle; exact hle

/-- **Telescoping**: `Σ_{k<N} 1/(k+1)² = 2 B₀/A₀ − 2 B_N/A_N`. -/
theorem partial_sum (N : Nat) :
    fsum (fun k => 1 / (((k : R) + 1) * ((k : R) + 1))) N = 2 * (B 0 / A 0) - 2 * (B N / A N) := by
  induction N with
  | zero => rw [fsum_zero]; grind
  | succ N ih =>
    rw [fsum_succ, ih]
    have k := key N
    have r := A_rec N
    have p1 := A_pos N; have p2 := A_pos (N + 1)
    have : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg
    generalize A N = a at *
    generalize A (N + 1) = a' at *
    generalize B N = b at *
    generalize B (N + 1) = b' at *
    generalize B 0 / A 0 = s at *
    generalize (N : R) = n at *
    -- `1/(n+1)² = 2b/a − 2b'/a'`.
    have hP : (n + 1) * (n + 1) ≠ 0 := by
      have := OrderedRing.mul_pos (by grind : (0 : R) < n + 1) (by grind : (0 : R) < n + 1); grind
    have ha : a ≠ 0 := by grind
    have ha' : a' ≠ 0 := by grind
    have hY : (n + 1) * (n + 1) * a' ≠ 0 := by
      have := OrderedRing.mul_pos (OrderedRing.mul_pos (by grind : (0 : R) < n + 1)
        (by grind : (0 : R) < n + 1)) p2; grind
    have f1 : 2 * (b / a) = (2 * b) / a := by rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
    have r' := congrArg (· * (b * (n + 1))) r
    have k' := congrArg (· * a) k
    have f2 : (2 * b) / a = (a' + 2 * (n + 1) * (n + 1) * b') / ((n + 1) * (n + 1) * a') :=
      div_eq_div_of ha hY (by grind)
    have f3 : 1 / ((n + 1) * (n + 1)) = a' / ((n + 1) * (n + 1) * a') :=
      div_eq_div_of hP hY (by grind)
    have f4 : b' / a' = ((n + 1) * (n + 1) * b') / ((n + 1) * (n + 1) * a') :=
      div_eq_div_of ha' hY (by grind)
    have f5 : a' / ((n + 1) * (n + 1) * a') + 2 * (((n + 1) * (n + 1) * b') / ((n + 1) * (n + 1) * a'))
        = (a' + 2 * (n + 1) * (n + 1) * b') / ((n + 1) * (n + 1) * a') := by
      rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
    rw [← f3, ← f4] at f5
    have e : 1 / ((n + 1) * (n + 1)) = 2 * (b / a) - 2 * (b' / a') := by
      rw [f1, f2, ← f5]; grind
    rw [e]; grind

/-- **The Basel problem** (Mengoli 1650, Euler 1734/35). `Σ_{n ≥ 1} 1/n² = π²/6`. -/
theorem basel : HasSum (fun k => 1 / (((k : R) + 1) * ((k : R) + 1))) (pi * pi / 6) := by
  have h0 : 2 * (B 0 / A 0) = pi * pi / 6 := by
    rw [B_zero, A_zero]; have := hpi_pos; unfold hpi at *; grind
  intro ε hε
  have hp := hpi_pos
  obtain ⟨M, hM⟩ := eps_small (div_pos hε (OrderedRing.mul_pos hp hp))
  refine ⟨M, fun N hN => ?_⟩
  rw [partial_sum, h0]
  have hb := B_le N
  have hb0 := B_nonneg N
  have ha := A_pos N
  have : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg
  have k := hM N hN
  -- `0 ≤ 2 B_N/A_N ≤ (π/2)²/(N+1) < ε`.
  have q1 : 0 ≤ B N / A N := by
    rw [Field.div_eq_mul_inv]; exact OrderedRing.mul_nonneg hb0
      (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 ha))
  have q2 : 2 * (B N / A N) ≤ hpi * hpi * (1 / ((N : R) + 1)) := by
    have h2 : (2 * (N : R) + 2) ≠ 0 := by grind
    have t0 : B N ≤ hpi * hpi / (2 * (N : R) + 2) * A N := by
      have : hpi * hpi * (A N / (2 * (N : R) + 2)) = hpi * hpi / (2 * (N : R) + 2) * A N := by
        rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
      rw [← this]; exact hb
    have t1 : B N / A N ≤ hpi * hpi / (2 * (N : R) + 2) := by
      rw [Field.div_eq_mul_inv]
      apply Classical.byContradiction; intro hc
      have := (Field.IsOrdered.lt_mul_inv_iff_mul_lt (hpi * hpi / (2 * (N : R) + 2)) (B N) ha).1
        (by grind)
      grind
    have t2 : 2 * (1 / (2 * (N : R) + 2)) = 1 / ((N : R) + 1) := by
      rw [show 2 * (1 / (2 * (N : R) + 2)) = 2 / (2 * (N : R) + 2) by
        rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind]
      exact div_eq_div_of h2 (by grind) (by grind)
    have t3 : hpi * hpi / (2 * (N : R) + 2) = hpi * hpi * (1 / (2 * (N : R) + 2)) := by
      rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
    rw [t3] at t1
    rw [← t2]
    grind
  have q3 := OrderedRing.mul_lt_mul_of_pos_left k (OrderedRing.mul_pos hp hp)
  have e : hpi * hpi * (ε / (hpi * hpi)) = ε := by
    have := Field.mul_inv_cancel (show hpi * hpi ≠ 0 by have := OrderedRing.mul_pos hp hp; grind)
    rw [Field.div_eq_mul_inv]; grind
  exact abs_lt.2 ⟨by grind, by grind⟩

end Wallis

end Foundations.Topology
