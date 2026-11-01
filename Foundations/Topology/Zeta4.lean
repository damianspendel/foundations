import Foundations.Topology.Basel

/-!
# `ζ(4) = Σ 1/n⁴ = π⁴/90`

Euler's solution of the Basel problem (1734/35) gave at once the sums of all even powers:
`Σ 1/n⁴ = π⁴/90`, `Σ 1/n⁶ = π⁶/945`, and so on. We derive the first of these by pushing the
integral method of the previous file one step further. Besides `Aₙ = ∫₀^{π/2} cos^{2n}` and
`Bₙ = ∫₀^{π/2} x² cos^{2n}` we use

  `Cₙ = ∫₀^{π/2} x⁴ cos^{2n} x dx`.

The same integration by parts as before, applied to `2x³ cos^{2n+2} + (n+1) x⁴ sin cos^{2n+1}`,
gives `6 B_{n+1} + 2(n+1)² C_{n+1} = (n+1)(2n+1) Cₙ`. Writing `Hₙ = Σ_{k ≤ n} 1/k²` and
`Zₙ = Σ_{k ≤ n} 1/k⁴`, and using `Bₙ = Aₙ (π²/12 − Hₙ/2)` from the Basel computation, an
induction gives the closed form

  `Cₙ / Aₙ = π⁴/80 − (π²/4) Hₙ + (3/4) Hₙ² + (3/4) Zₙ`.

Since `x⁴ ≤ (π/2)² x²` on `[0, π/2]`, `0 ≤ Cₙ/Aₙ ≤ (π/2)² Bₙ/Aₙ → 0`; with `Hₙ → π²/6` the closed
form yields `(3/4) ζ(4) = π⁴/24 − π⁴/48 − π⁴/80 = π⁴/120`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Wallis

/-- Changing the stated derivative to an equal value. -/
theorem HasDerivAt.congr_deriv {f : R → R} {d d' x : R} (h : HasDerivAt f d x) (e : d = d') :
    HasDerivAt f d' x := e ▸ h

/-- Cancelling a non-zero factor. -/
theorem cancel_left {u x y : R} (hu : u ≠ 0) (h : u * x = u * y) : x = y := by
  have i := Field.mul_inv_cancel hu
  calc x = (u * u⁻¹) * x := by rw [i]; grind
    _ = u⁻¹ * (u * x) := by grind
    _ = u⁻¹ * (u * y) := by rw [h]
    _ = (u * u⁻¹) * y := by grind
    _ = y := by rw [i]; grind

/-- `Cₙ = ∫₀^{π/2} x⁴ cos^{2n} x dx`. -/
noncomputable def C (n : Nat) : R := integral (fun x => x * x * (x * x) * cos x ^ (2 * n)) 0 hpi

/-- `x⁴ cosᵏ x` is continuous. -/
theorem continuousAt_x4cos (k : Nat) (x : R) :
    R.ContinuousAt (fun y => y * y * (y * y) * cos y ^ k) x :=
  continuousAt_mul (continuousAt_mul (continuousAt_mul (continuousAt_id x) (continuousAt_id x))
    (continuousAt_mul (continuousAt_id x) (continuousAt_id x))) (continuousAt_cos_pow k x)

/-- `C₀ = (π/2)⁵/5`. -/
theorem C_zero : C 0 = hpi * hpi * (hpi * hpi) * hpi / 5 := by
  have hab := Std.le_of_lt hpi_pos
  unfold C
  rw [integral_eq_sub (F := fun x => 1 / 5 * (x * x * (x * x) * x)) hab (fun t _ _ => by
      refine HasDerivAt.congr_deriv (((((hasDerivAt_id t).mul (hasDerivAt_id t)).mul
        ((hasDerivAt_id t).mul (hasDerivAt_id t))).mul (hasDerivAt_id t)).const_mul (1 / 5)) ?_
      show _ = t * t * (t * t) * 1; grind) (fun t _ _ => continuousAt_x4cos _ t)]
  grind

/-- **The key identity** `6 B_{n+1} + 2(n+1)² C_{n+1} = (n+1)(2n+1) Cₙ`. -/
theorem key4 (j : Nat) :
    6 * B (j + 1) + 2 * ((j : R) + 1) * ((j : R) + 1) * C (j + 1) =
      ((j : R) + 1) * (2 * (j : R) + 1) * C j := by
  have hab := Std.le_of_lt hpi_pos
  let n1 : R := (j : R) + 1
  let g : R → R := fun x => 6 * (x * x * cos x ^ (2 * j + 1 + 1)) +
    (2 * n1 * n1 * (x * x * (x * x) * cos x ^ (2 * j + 1 + 1)) +
      (-(n1 * (2 * (j : R) + 1))) * (x * x * (x * x) * cos x ^ (2 * j)))
  let F : R → R := fun x => 2 * (x * x * x * cos x ^ (2 * j + 1 + 1)) +
    n1 * (x * x * (x * x) * (sin x * cos x ^ (2 * j + 1)))
  have hd : ∀ t, 0 ≤ t → t ≤ hpi → HasDerivAt F (g t) t := fun t _ _ => by
    have hA := (((((hasDerivAt_id t).mul (hasDerivAt_id t)).mul (hasDerivAt_id t)).mul
      (hasDerivAt_cos_pow (2 * j + 1) t)).const_mul 2)
    have hB := (((((hasDerivAt_id t).mul (hasDerivAt_id t)).mul ((hasDerivAt_id t).mul
      (hasDerivAt_id t))).mul ((hasDerivAt_sin t).mul (hasDerivAt_cos_pow (2 * j) t))).const_mul n1)
    refine HasDerivAt.congr_deriv (hA.add hB) ?_
    have p1 : cos t ^ (2 * j + 1) = cos t ^ (2 * j) * cos t := rfl
    have p2 : cos t ^ (2 * j + 1 + 1) = cos t ^ (2 * j) * cos t * cos t := rfl
    have py := sin_sq_add_cos_sq t
    have c1 : ((2 * j + 1 : Nat) : R) = 2 * (j : R) + 1 := by grind
    have c2 : ((2 * j : Nat) : R) = 2 * (j : R) := by grind
    show _ = 6 * (t * t * cos t ^ (2 * j + 1 + 1)) +
      (2 * n1 * n1 * (t * t * (t * t) * cos t ^ (2 * j + 1 + 1)) +
        (-(n1 * (2 * (j : R) + 1))) * (t * t * (t * t) * cos t ^ (2 * j)))
    rw [p1, p2, c1, c2]
    have ss : sin t * sin t = 1 - cos t * cos t := by grind
    generalize cos t ^ (2 * j) = Cc
    show _ = _ + (2 * ((j : R) + 1) * ((j : R) + 1) * _ + -(((j : R) + 1) * _) * _)
    show _ + ((j : R) + 1) * _ = _
    grind
  have c3 : ∀ t, R.ContinuousAt (fun x => x * x * cos x ^ (2 * j + 1 + 1)) t := continuousAt_x2cos _
  have c4 : ∀ t, R.ContinuousAt (fun x => x * x * (x * x) * cos x ^ (2 * j + 1 + 1)) t :=
    continuousAt_x4cos _
  have c5 : ∀ t, R.ContinuousAt (fun x => x * x * (x * x) * cos x ^ (2 * j)) t := continuousAt_x4cos _
  have hgc : ∀ t, R.ContinuousAt g t := fun t =>
    continuousAt_add (continuousAt_cmul _ (c3 t))
      (continuousAt_add (continuousAt_cmul _ (c4 t)) (continuousAt_cmul _ (c5 t)))
  have h1 := integral_eq_sub hab hd fun t _ _ => hgc t
  rw [integral_add' hab (fun t => continuousAt_cmul _ (c3 t)) (fun t => continuousAt_add
      (continuousAt_cmul _ (c4 t)) (continuousAt_cmul _ (c5 t))),
    integral_add' hab (fun t => continuousAt_cmul _ (c4 t)) (fun t => continuousAt_cmul _ (c5 t)),
    integral_const_mul' _ hab c3, integral_const_mul' _ hab c4, integral_const_mul' _ hab c5] at h1
  have hF0 : F 0 = 0 := by show 2 * (0 * 0 * 0 * _) + n1 * (0 * 0 * (0 * 0) * _) = 0; grind
  have hFp : F hpi = 0 := by
    show 2 * (hpi * hpi * hpi * cos hpi ^ (2 * j + 1 + 1)) +
      n1 * (hpi * hpi * (hpi * hpi) * (sin hpi * cos hpi ^ (2 * j + 1))) = 0
    rw [cos_hpi]
    have : (0 : R) ^ (2 * j + 1 + 1) = 0 := by show (0 : R) ^ (2 * j + 1) * 0 = 0; grind
    have : (0 : R) ^ (2 * j + 1) = 0 := by show (0 : R) ^ (2 * j) * 0 = 0; grind
    grind
  rw [hF0, hFp] at h1
  have eB : B (j + 1) = integral (fun x => x * x * cos x ^ (2 * j + 1 + 1)) 0 hpi := by
    unfold B; rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
  have eC : C (j + 1) = integral (fun x => x * x * (x * x) * cos x ^ (2 * j + 1 + 1)) 0 hpi := by
    unfold C; rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
  have eC' : C j = integral (fun x => x * x * (x * x) * cos x ^ (2 * j)) 0 hpi := rfl
  rw [← eB, ← eC, ← eC'] at h1
  show _ = n1 * _ * _
  grind

/-- `Cₙ ≥ 0`. -/
theorem C_nonneg (n : Nat) : 0 ≤ C n := by
  have hab := Std.le_of_lt hpi_pos
  have := HasIntegral.mono hab (hasIntegral_const 0 hab)
    (hasIntegral_integral hab fun x _ _ => continuousAt_x4cos (2 * n) x) fun t h0 h1 => by
      have := pow_le_pow_left.pow_nonneg (cos_mem h0 h1).1 (2 * n)
      exact OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg h0 h0)
        (OrderedRing.mul_nonneg h0 h0)) this
  unfold C; grind

/-- `Cₙ ≤ (π/2)² Bₙ`, since `x⁴ ≤ (π/2)² x²` on `[0, π/2]`. -/
theorem C_le (n : Nat) : C n ≤ hpi * hpi * B n := by
  have hab := Std.le_of_lt hpi_pos
  have := HasIntegral.mono hab
    (hasIntegral_integral hab fun x _ _ => continuousAt_x4cos (2 * n) x)
    ((hasIntegral_integral hab fun x _ _ => continuousAt_x2cos (2 * n) x).const_mul (hpi * hpi))
    fun t h0 h1 => by
      have hc := pow_le_pow_left.pow_nonneg (cos_mem h0 h1).1 (2 * n)
      have h2 : t * t ≤ hpi * hpi := by
        have := OrderedRing.mul_le_mul_of_nonneg_left h1 h0
        have := OrderedRing.mul_le_mul_of_nonneg_right h1 hab; grind
      have := OrderedRing.mul_le_mul_of_nonneg_right h2
        (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg h0 h0) hc)
      show t * t * (t * t) * cos t ^ (2 * n) ≤ hpi * hpi * (t * t * cos t ^ (2 * n))
      grind
  unfold C B; exact this

/-! ## The closed form -/

/-- The partial sums `Hₙ = Σ_{k<n} 1/(k+1)²`. -/
noncomputable def H (n : Nat) : R := fsum (fun k => 1 / (((k : R) + 1) * ((k : R) + 1))) n

/-- The partial sums `Zₙ = Σ_{k<n} 1/(k+1)⁴`. -/
noncomputable def Z (n : Nat) : R :=
  fsum (fun k => 1 / (((k : R) + 1) * ((k : R) + 1)) * (1 / (((k : R) + 1) * ((k : R) + 1)))) n

/-- `π² = 4 (π/2)²`. -/
theorem pi_sq : pi * pi = 4 * (hpi * hpi) := by unfold hpi; grind

/-- From the Basel computation: `Bₙ = Aₙ ((π/2)²/3 − Hₙ/2)`. -/
theorem B_eq (n : Nat) : B n = A n * (hpi * hpi / 3 - H n / 2) := by
  have h := partial_sum n
  rw [B_zero, A_zero] at h
  have hp := hpi_pos
  have ha := A_pos n
  have e : hpi * hpi * hpi / 3 / hpi = hpi * hpi / 3 := by grind
  rw [e] at h
  unfold H
  rw [h]
  have : B n / A n * A n = B n := by grind
  grind

/-- **Closed form**: `Cₙ = Aₙ ((π/2)⁴/5 − (π/2)² Hₙ + (3/4) Hₙ² + (3/4) Zₙ)`. -/
theorem C_eq (n : Nat) : C n = A n * (hpi * hpi * (hpi * hpi) / 5 - hpi * hpi * H n +
    3 / 4 * (H n * H n) + 3 / 4 * Z n) := by
  induction n with
  | zero =>
    rw [C_zero, A_zero]
    show _ = hpi * (hpi * hpi * (hpi * hpi) / 5 - hpi * hpi * 0 + 3 / 4 * (0 * 0) + 3 / 4 * 0)
    grind
  | succ n ih =>
    have k := key4 n
    have r := A_rec n
    have hb := B_eq (n + 1)
    have hn0 : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    let t : R := 1 / (((n : R) + 1) * ((n : R) + 1))
    have ht : ((n : R) + 1) * ((n : R) + 1) * t = 1 := by
      show _ * (1 / _) = 1
      have : ((n : R) + 1) * ((n : R) + 1) ≠ 0 := by
        have := OrderedRing.mul_pos (by grind : (0 : R) < (n : R) + 1) (by grind : (0 : R) < (n : R) + 1)
        grind
      grind
    have eH : H (n + 1) = H n + t := by unfold H; rw [fsum_succ]
    have eZ : Z (n + 1) = Z n + t * t := by unfold Z; rw [fsum_succ]
    rw [eH] at hb
    rw [eH, eZ]
    generalize hR : hpi * hpi * (hpi * hpi) / 5 - hpi * hpi * H n + 3 / 4 * (H n * H n) +
      3 / 4 * Z n = Rn at ih
    have hR' : hpi * hpi * (hpi * hpi) / 5 - hpi * hpi * (H n + t) + 3 / 4 * ((H n + t) * (H n + t)) +
        3 / 4 * (Z n + t * t) = Rn - 3 * (hpi * hpi / 3 - (H n + t) / 2) * t := by
      rw [← hR]; grind
    rw [hR']
    generalize hpi * hpi / 3 - (H n + t) / 2 = β at hb hR' ⊢
    rw [ih] at k
    rw [hb] at k
    -- `2(n+1)² C' = 2(n+1)² A' (Rn − 3βt)`.
    apply cancel_left (u := 2 * ((n : R) + 1) * ((n : R) + 1)) (by
      have := OrderedRing.mul_pos (by grind : (0 : R) < (n : R) + 1) (by grind : (0 : R) < (n : R) + 1)
      grind)
    have e1 := congrArg (· * (6 * (A (n + 1) * β))) ht
    have e2 := congrArg (· * (((n : R) + 1) * Rn)) r
    grind

/-- `Hₙ → π²/6` (the Basel problem). -/
theorem tendsto_H : Tendsto H (pi * pi / 6) := basel

/-- **Euler's `ζ(4) = π⁴/90`**: `Σ_{n ≥ 1} 1/n⁴ = π⁴/90`. -/
theorem zeta4 : HasSum (fun k => 1 / (((k : R) + 1) * ((k : R) + 1)) *
    (1 / (((k : R) + 1) * ((k : R) + 1)))) (pi * pi * (pi * pi) / 90) := by
  have hp := hpi_pos
  let Rn : Nat → R := fun n => hpi * hpi * (hpi * hpi) / 5 - hpi * hpi * H n + 3 / 4 * (H n * H n) +
    3 / 4 * Z n
  let β : Nat → R := fun n => hpi * hpi / 3 - H n / 2
  -- `0 ≤ Rₙ ≤ (π/2)² βₙ`.
  have hR : ∀ n, abs (Rn n - 0) ≤ hpi * hpi * β n := fun n => by
    have h1 := C_eq n; have h2 := B_eq n; have h3 := C_nonneg n; have h4 := C_le n
    have ha := A_pos n
    rw [h1] at h3 h4; rw [h2] at h4
    change 0 ≤ A n * Rn n at h3
    change A n * Rn n ≤ hpi * hpi * (A n * β n) at h4
    have r0 : 0 ≤ Rn n := by
      apply Classical.byContradiction; intro hc
      have := OrderedRing.mul_lt_mul_of_pos_left (by grind : Rn n < 0) ha; grind
    have r1 : Rn n ≤ hpi * hpi * β n := by
      apply Classical.byContradiction; intro hc
      have := OrderedRing.mul_lt_mul_of_pos_left (by grind : hpi * hpi * β n < Rn n) ha; grind
    rw [show Rn n - 0 = Rn n by grind, abs_of_nonneg r0]; exact r1
  have hH := tendsto_H
  have hβ : Tendsto β (hpi * hpi / 3 - 1 / 2 * (pi * pi / 6)) := by
    have h := Tendsto.sub (tendsto_const (hpi * hpi / 3)) (Tendsto.const_mul (1 / 2) hH)
    refine Tendsto.congr_eventually h 0 fun n _ => ?_
    show hpi * hpi / 3 - 1 / 2 * H n = hpi * hpi / 3 - H n / 2
    grind
  rw [show hpi * hpi / 3 - 1 / 2 * (pi * pi / 6) = 0 by rw [pi_sq]; grind] at hβ
  have hβ' := hβ.const_mul (hpi * hpi)
  rw [show hpi * hpi * 0 = 0 by grind] at hβ'
  have hRt : Tendsto Rn 0 := tendsto_of_abs_le hβ' hR
  -- `Zₙ = (4/3)(Rₙ − (π/2)⁴/5 + (π/2)² Hₙ − (3/4) Hₙ²)`.
  have h1 := Tendsto.sub hRt (tendsto_const (hpi * hpi * (hpi * hpi) / 5))
  have h2 := Tendsto.add h1 (Tendsto.const_mul (hpi * hpi) hH)
  have h3 := Tendsto.sub h2 (Tendsto.const_mul (3 / 4) (Tendsto.mul hH hH))
  have hZ := Tendsto.const_mul (4 / 3) h3
  have e : 4 / 3 * (0 - hpi * hpi * (hpi * hpi) / 5 + hpi * hpi * (pi * pi / 6) -
      3 / 4 * (pi * pi / 6 * (pi * pi / 6))) = pi * pi * (pi * pi) / 90 := by
    rw [pi_sq]; grind
  rw [e] at hZ
  refine Tendsto.congr_eventually hZ 0 fun n _ => ?_
  show 4 / 3 * (hpi * hpi * (hpi * hpi) / 5 - hpi * hpi * H n + 3 / 4 * (H n * H n) + 3 / 4 * Z n -
    hpi * hpi * (hpi * hpi) / 5 + hpi * hpi * H n - 3 / 4 * (H n * H n)) = Z n
  grind

end Wallis

end Foundations.Topology
