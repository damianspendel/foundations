import Foundations.Topology.Stirling

/-!
# The Leibniz series `π/4 = 1 − 1/3 + 1/5 − 1/7 + ⋯`

Found by Mādhava of Sangamagrāma (c. 1400) in Kerala, and rediscovered by James Gregory (1671)
and Gottfried Wilhelm **Leibniz** (1674), who was delighted that the circle "is to its
circumscribed square as `1 − 1/3 + 1/5 − ⋯` is to `1`".

The proof uses the integral `∫₀¹ dt/(1 + t²)`.

* It equals `π/4`. The function `G(x) = ∫₀ˣ dt/(1+t²)` (the arctangent, defined here as an
  integral) undoes the tangent: `θ ↦ G(tan θ) − θ` has derivative
  `tan'(θ)/(1 + tan² θ) − 1 = 0`, so it is constant on `[0, π/4]`; and `tan(π/4) = 1`.
* Summing the geometric series, `1/(1+t²) = Σ_{k<N} (−1)ᵏ t^{2k} + (−1)ᴺ t^{2N}/(1+t²)`. Integrating
  term by term, the `N`-th partial sum of the Leibniz series differs from `∫₀¹ dt/(1+t²)` by at most
  `∫₀¹ t^{2N} dt = 1/(2N+1)`.

The reciprocals `1/x` are written as `exp(−log x)` for `x > 0`, which makes them differentiable by
the chain rule.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Leibniz

open Wallis Stirling

/-- The integrand `f(t) = 1/(1 + t²)`, written as `exp(−log(1 + t²))`. -/
noncomputable def f (t : R) : R := exp (-log (1 + t * t))

/-- `1 + t² > 0`. -/
theorem one_add_sq_pos (t : R) : 0 < 1 + t * t := by have := C.mul_self_nonneg t; grind

/-- `f(t) (1 + t²) = 1`. -/
theorem f_mul (t : R) : f t * (1 + t * t) = 1 := by
  have := exp_mul_exp_neg (log (1 + t * t))
  rw [exp_log (one_add_sq_pos t)] at this
  unfold f; grind

/-- `0 < f(t) ≤ 1`. -/
theorem f_bounds (t : R) : 0 < f t ∧ f t ≤ 1 := by
  have h := f_mul t
  have hp := exp_pos (-log (1 + t * t))
  have := C.mul_self_nonneg t
  refine ⟨hp, ?_⟩
  have := OrderedRing.mul_nonneg (Std.le_of_lt hp) this
  change exp (-log (1 + t * t)) * (1 + t * t) = 1 at h
  show exp (-log (1 + t * t)) ≤ 1
  grind

/-- `f` is differentiable, hence continuous. -/
theorem continuousAt_f (t : R) : R.ContinuousAt f t := by
  have h1 : HasDerivAt (fun y => 1 + y * y) (0 + (1 * t + t * 1)) t :=
    (hasDerivAt_const 1 t).add ((hasDerivAt_id t).mul (hasDerivAt_id t))
  have h2 := (hasDerivAt_log (one_add_sq_pos t)).comp (f := fun y => 1 + y * y) h1
  have h3 := (hasDerivAt_exp _).comp h2.neg
  exact h3.continuousAt

/-! ## `∫₀¹ dt/(1+t²) = π/4` -/

/-- The arctangent as an integral: `G(x) = ∫_{−1}^{x} f`. -/
noncomputable def G (x : R) : R := integral f (-1) x

/-- `G' = f` on `(−1, 2)`. -/
theorem hasDerivAt_G {x : R} (h1 : -1 < x) (h2 : x < 2) : HasDerivAt G (f x) x :=
  ftc1 (b := 2) (fun y _ _ => continuousAt_f y) h1 h2

/-- `π/4`. -/
noncomputable def qpi : R := hpi / 2

/-- `cos > 0` on `[0, π/4]`. -/
theorem cos_pos {θ : R} (h0 : 0 ≤ θ) (h1 : θ ≤ qpi) : 0 < cos θ :=
  pi_div_two_spec.2.2.2 θ h0 (by
    have := hpi_pos; have e : hpi = pi / 2 := rfl; unfold qpi at h1; grind)

/-- The tangent `T(θ) = sin θ / cos θ`, written as `sin θ · exp(−log cos θ)`. -/
noncomputable def T (θ : R) : R := sin θ * exp (-log (cos θ))

/-- `cos θ · exp(−log cos θ) = 1` where `cos θ > 0`. -/
theorem cos_mul_E {θ : R} (h : 0 < cos θ) : cos θ * exp (-log (cos θ)) = 1 := by
  have := exp_mul_exp_neg (log (cos θ)); rw [exp_log h] at this; exact this

/-- **Derivative of the tangent**: `T' = 1 + T²` on `[0, π/4]`. -/
theorem hasDerivAt_T {θ : R} (h0 : 0 ≤ θ) (h1 : θ ≤ qpi) : HasDerivAt T (1 + T θ * T θ) θ := by
  have hc := cos_pos h0 h1
  have hE := (hasDerivAt_exp _).comp ((hasDerivAt_log hc).comp (hasDerivAt_cos θ)).neg
  refine HasDerivAt.congr_deriv ((hasDerivAt_sin θ).mul hE) ?_
  have k := cos_mul_E hc
  have py := sin_sq_add_cos_sq θ
  show cos θ * exp (-log (cos θ)) + sin θ * (exp (-log (cos θ)) * -(1 / cos θ * -sin θ)) =
    1 + sin θ * exp (-log (cos θ)) * (sin θ * exp (-log (cos θ)))
  have e : 1 / cos θ = exp (-log (cos θ)) := by
    have := Field.mul_inv_cancel (show cos θ ≠ 0 by grind)
    rw [Field.div_eq_mul_inv]
    exact cancel_left (u := cos θ) (by grind) (by grind)
  rw [e]
  generalize exp (-log (cos θ)) = E at k ⊢
  grind

/-- `sin (π/4) = cos (π/4)`. -/
theorem sin_qpi : sin qpi = cos qpi := by
  have := cos_add_pi_div_two (-qpi)
  rw [show -qpi + pi / 2 = qpi by unfold qpi hpi; grind, sin_neg] at this
  grind

/-- `tan (π/4) = 1`. -/
theorem T_qpi : T qpi = 1 := by
  have hq : 0 ≤ qpi := by unfold qpi; have := hpi_pos; grind
  unfold T; rw [sin_qpi]; exact cos_mul_E (cos_pos hq (Std.le_refl _))

/-- `tan 0 = 0`. -/
theorem T_zero : T 0 = 0 := by unfold T; rw [sin_zero]; grind

/-- The tangent increases on `[0, π/4]`, so `0 ≤ T θ ≤ 1` there. -/
theorem T_mem {θ : R} (h0 : 0 ≤ θ) (h1 : θ ≤ qpi) : 0 ≤ T θ ∧ T θ ≤ 1 := by
  have hpos : ∀ x, 0 ≤ x → x ≤ qpi → 0 ≤ 1 + T x * T x := fun x _ _ => by
    have := C.mul_self_nonneg (T x); grind
  have a := monotone_of_deriv_nonneg (a := 0) (b := qpi) (fun x h h' => hasDerivAt_T h h') hpos
    (Std.le_refl 0) h0 h1
  have b := monotone_of_deriv_nonneg (a := 0) (b := qpi) (fun x h h' => hasDerivAt_T h h') hpos
    h0 h1 (Std.le_refl qpi)
  rw [T_zero] at a; rw [T_qpi] at b
  exact ⟨a, b⟩

/-- **`∫₀¹ dt/(1 + t²) = π/4`.** -/
theorem integral_f : integral f 0 1 = qpi := by
  have hq : 0 ≤ qpi := by unfold qpi; have := hpi_pos; grind
  -- `θ ↦ G(T θ) − θ` is constant on `[0, π/4]`.
  have hd : ∀ θ, 0 ≤ θ → θ ≤ qpi → HasDerivAt (fun θ => G (T θ) - θ) (f (T θ) * (1 + T θ * T θ) - 1) θ :=
    fun θ h0 h1 => by
      have hm := T_mem h0 h1
      exact ((hasDerivAt_G (by grind) (by grind)).comp (hasDerivAt_T h0 h1)).sub (hasDerivAt_id θ)
  have hc := const_of_deriv_zero hd (fun θ _ _ => by rw [f_mul]; grind) hq (Std.le_refl qpi)
    (Std.le_refl 0) hq
  have hc : G (T qpi) - qpi = G (T 0) - 0 := hc
  rw [T_qpi, T_zero] at hc
  have := integral_add_interval (f := f) (a := -1) (u := 0) (v := 1) (by grind) (by grind)
    fun x _ _ => continuousAt_f x
  unfold G at hc
  grind

/-! ## The series -/

/-- The partial sums `Σ_{k<N} (−1)ᵏ/(2k+1)`. -/
noncomputable def S (N : Nat) : R := fsum (fun k => (-1 : R) ^ k / (2 * (k : R) + 1)) N

/-- The polynomial `p_N(t) = Σ_{k<N} (−1)ᵏ t^{2k}`. -/
noncomputable def p (N : Nat) (t : R) : R := fsum (fun k => (-1 : R) ^ k * t ^ (2 * k)) N

/-- Geometric sum: `p_N(t) (1 + t²) = 1 − (−1)ᴺ t^{2N}`. -/
theorem p_mul (N : Nat) (t : R) : p N t * (1 + t * t) = 1 - (-1 : R) ^ N * t ^ (2 * N) := by
  induction N with
  | zero => show (0 : R) * _ = 1 - 1 * 1; grind
  | succ N ih =>
    unfold p at ih ⊢
    rw [fsum_succ, pow_succ', show 2 * (N + 1) = 2 * N + 1 + 1 by omega, pow_succ', pow_succ']
    generalize fsum (fun k => (-1 : R) ^ k * t ^ (2 * k)) N = P at ih ⊢
    grind

/-- `p_N` is continuous. -/
theorem continuousAt_p (N : Nat) (t : R) : R.ContinuousAt (p N) t :=
  (hasDerivAt_fsum (fun k y => (-1 : R) ^ k * y ^ (2 * k)) _ N fun k _ =>
    (hasDerivAt_pow' (2 * k) t).const_mul _).continuousAt

/-- **Termwise integration**: `∫₀¹ p_N = S_N`. -/
theorem integral_p (N : Nat) : integral (p N) 0 1 = S N := by
  have hd : ∀ t, 0 ≤ t → t ≤ 1 → HasDerivAt
      (fun y => fsum (fun k => (-1 : R) ^ k / (2 * (k : R) + 1) * y ^ (2 * k + 1)) N) (p N t) t :=
    fun t _ _ => by
      refine HasDerivAt.congr_deriv (hasDerivAt_fsum _ _ N fun k _ =>
        (hasDerivAt_pow (2 * k) t).const_mul ((-1 : R) ^ k / (2 * (k : R) + 1))) ?_
      unfold p; apply fsum_congr; intro k _
      have : (0 : R) ≤ (k : R) := OrderedRing.natCast_nonneg
      have c : ((2 * k : Nat) : R) = 2 * (k : R) := by grind
      rw [c]; grind
  rw [integral_eq_sub (by grind) hd fun t _ _ => continuousAt_p N t]
  unfold S
  have h0 : fsum (fun k => (-1 : R) ^ k / (2 * (k : R) + 1) * (0 : R) ^ (2 * k + 1)) N = 0 :=
    fsum_zero' (f := fun (k : Nat) => (-1 : R) ^ k / (2 * (k : R) + 1) * (0 : R) ^ (2 * k + 1))
      (fun k => by show _ * ((0 : R) ^ (2 * k) * 0) = 0; grind) N
  rw [h0]
  rw [show (fun (k : Nat) => (-1 : R) ^ k / (2 * (k : R) + 1) * (1 : R) ^ (2 * k + 1)) =
    fun (k : Nat) => (-1 : R) ^ k / (2 * (k : R) + 1) from funext fun k => by rw [one_pow]; grind]
  grind

/-- **The Leibniz series** (Mādhava, Gregory, Leibniz).
`1 − 1/3 + 1/5 − 1/7 + ⋯ = π/4`. -/
theorem leibniz : HasSum (fun k => (-1 : R) ^ k / (2 * (k : R) + 1)) (pi / 4) := by
  have hab : (0 : R) ≤ 1 := by grind
  -- `|S_N − π/4| ≤ 1/(2N+1)`.
  have hb : ∀ N : Nat, abs (S N - qpi) ≤ 1 / (2 * (N : R) + 1) := fun N => by
    have hfI := hasIntegral_integral hab fun x _ _ => continuousAt_f x
    have hpI := hasIntegral_integral hab fun x _ _ => continuousAt_p N x
    have hD := hfI.add (hpI.const_mul (-1))
    have hwI := hasIntegral_integral hab fun x _ _ => continuousAt_pow (2 * N) x
    rw [integral_pow (2 * N) hab, one_pow, show (0 : R) ^ (2 * N + 1) = 0 by rw [pow_succ']; grind,
      show ((2 * N : Nat) : R) = 2 * (N : R) by grind] at hwI
    -- `|f − p_N| = t^{2N} f ≤ t^{2N}`.
    have hpt : ∀ t, 0 ≤ t → t ≤ 1 → abs (f t + -1 * p N t) ≤ t ^ (2 * N) := fun t h0 _ => by
      have h1 := p_mul N t
      have h2 := f_mul t
      have hfb := f_bounds t
      have e : f t + -1 * p N t = (-1 : R) ^ N * t ^ (2 * N) * f t := by
        have : p N t = p N t * ((1 + t * t) * f t) := by grind
        rw [this]
        generalize (1 + t * t) * f t = one at *
        grind
      rw [e, abs_mul, abs_mul, abs_pow, show abs (-1 : R) = 1 by
          rw [R.abs_neg, abs_of_nonneg (by grind)], one_pow,
        abs_of_nonneg (pow_le_pow_left.pow_nonneg h0 _), abs_of_nonneg (Std.le_of_lt hfb.1)]
      have := pow_le_pow_left.pow_nonneg h0 (2 * N)
      have := OrderedRing.mul_le_mul_of_nonneg_left hfb.2 this
      grind
    have up := HasIntegral.mono hab hD hwI fun t h0 h1 => (abs_le.1 (hpt t h0 h1)).2
    have lo := HasIntegral.mono hab (hwI.const_mul (-1)) hD fun t h0 h1 => by
      have := (abs_le.1 (hpt t h0 h1)).1; show -1 * t ^ (2 * N) ≤ _; grind
    rw [integral_f, integral_p] at up lo
    exact abs_le.2 ⟨by grind, by grind⟩
  intro ε hε
  obtain ⟨M, hM⟩ := eps_small hε
  refine ⟨M, fun N hN => ?_⟩
  have k := hM N hN
  have : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg
  have k2 := one_div_le_one_div (by grind : (0 : R) < (N : R) + 1)
    (by grind : (N : R) + 1 ≤ 2 * (N : R) + 1)
  have := hb N
  show abs (S N - pi / 4) < ε
  rw [show pi / 4 = qpi by unfold qpi hpi; grind]
  grind

end Leibniz

end Foundations.Topology
