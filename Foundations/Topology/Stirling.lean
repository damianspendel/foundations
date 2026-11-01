import Foundations.Topology.Zeta4

/-!
# Stirling's formula

Abraham de Moivre found (1730) that `n!` behaves like `C √n (n/e)ⁿ` for some constant `C`, and
James **Stirling** identified the constant in the same year: `C = √(2π)`. In modern notation

  `n! / (√(2πn) (n/e)ⁿ) → 1`.

The proof has two halves.

1. *Existence of the limit.* Put `dₙ = log n! + n − (n + ½) log n`. Then
   `dₙ − d_{n+1} = (n + ½) log(1 + 1/n) − 1`, and two elementary inequalities for the logarithm
   — proved, after the substitution `1 + x = eᵘ`, by differentiating twice — show
   `0 ≤ dₙ − d_{n+1} ≤ 1/(4n(n+1))`. So `dₙ` decreases and stays above `d₁ − 1/4`: it converges,
   to some `D` (monotone convergence).
2. *Identification of the constant.* The partial Wallis products are
   `wₙ = 16ⁿ (n!)⁴ / (((2n)!)² (2n + 1))`, so `log wₙ = 4dₙ − 2d_{2n} − log 2 − log((2n+1)/n)`.
   Letting `n → ∞` and using the **Wallis product** `wₙ → π/2`: `log(π/2) = 2D − 2 log 2`, i.e.
   `D = ½ log(2π)` and `e^D = √(2π)`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Stirling

open Wallis

/-! ## Two inequalities for the exponential -/

/-- `exp` is continuous. -/
theorem continuousAt_exp (x : R) : R.ContinuousAt exp x := (hasDerivAt_exp x).continuousAt

/-- `2 (eᵘ − 1) ≤ u (eᵘ + 1)` for `u ≥ 0` (equivalently `log(1+x) ≥ 2x/(2+x)`). -/
theorem exp_ineq1 {u : R} (hu : 0 ≤ u) : 2 * (exp u - 1) ≤ u * (exp u + 1) := by
  -- `j(v) = 1 − eᵛ + v eᵛ` has derivative `v eᵛ ≥ 0`, so `j ≥ j(0) = 0`.
  have hj : ∀ v, HasDerivAt (fun v => 1 - exp v + v * exp v) (v * exp v) v := fun v =>
    HasDerivAt.congr_deriv (((hasDerivAt_const 1 v).sub (hasDerivAt_exp v)).add
      ((hasDerivAt_id v).mul (hasDerivAt_exp v))) (by grind)
  have jpos : ∀ v, 0 ≤ v → 0 ≤ 1 - exp v + v * exp v := fun v hv => by
    have := monotone_of_deriv_nonneg (a := 0) (b := v) (fun t _ _ => hj t)
      (fun t h0 _ => OrderedRing.mul_nonneg h0 (Std.le_of_lt (exp_pos t))) (Std.le_refl 0) hv
      (Std.le_refl v)
    rw [exp_zero] at this; grind
  -- `k(v) = v(eᵛ + 1) − 2(eᵛ − 1)` has derivative `j(v) ≥ 0`.
  have hk : ∀ v, HasDerivAt (fun v => v * (exp v + 1) - 2 * (exp v - 1)) (1 - exp v + v * exp v) v :=
    fun v => HasDerivAt.congr_deriv (((hasDerivAt_id v).mul ((hasDerivAt_exp v).add
      (hasDerivAt_const 1 v))).sub (((hasDerivAt_exp v).sub (hasDerivAt_const 1 v)).const_mul 2))
      (by grind)
  have := monotone_of_deriv_nonneg (a := 0) (b := u) (fun t _ _ => hk t)
    (fun t h0 _ => jpos t h0) (Std.le_refl 0) hu (Std.le_refl u)
  rw [exp_zero] at this; grind

/-- `u (2 + 4eᵘ) ≤ (eᵘ − 1)(5 + eᵘ)` for `u ≥ 0` (equivalently
`log(1+x) ≤ x(6+x)/(6+4x)`). -/
theorem exp_ineq2 {u : R} (hu : 0 ≤ u) : u * (2 + 4 * exp u) ≤ (exp u - 1) * (5 + exp u) := by
  -- `m''(v) = 4eᵛ(eᵛ − 1 − v) ≥ 0`.
  have hj : ∀ v, HasDerivAt (fun v => 2 * (exp v * exp v) - 2 - 4 * (v * exp v))
      (4 * (exp v * exp v) - 4 * exp v - 4 * (v * exp v)) v := fun v =>
    HasDerivAt.congr_deriv (((((hasDerivAt_exp v).mul (hasDerivAt_exp v)).const_mul 2).sub
      (hasDerivAt_const 2 v)).sub (((hasDerivAt_id v).mul (hasDerivAt_exp v)).const_mul 4)) (by grind)
  have jpos : ∀ v, 0 ≤ v → 0 ≤ 2 * (exp v * exp v) - 2 - 4 * (v * exp v) := fun v hv => by
    have := monotone_of_deriv_nonneg (a := 0) (b := v) (fun t _ _ => hj t)
      (fun t h0 _ => by
        have := one_add_le_exp h0
        have := OrderedRing.mul_nonneg (Std.le_of_lt (exp_pos t)) (by grind : 0 ≤ exp t - 1 - t)
        grind) (Std.le_refl 0) hv (Std.le_refl v)
    rw [exp_zero] at this; grind
  have hk : ∀ v, HasDerivAt (fun v => (exp v - 1) * (5 + exp v) - v * (2 + 4 * exp v))
      (2 * (exp v * exp v) - 2 - 4 * (v * exp v)) v := fun v =>
    HasDerivAt.congr_deriv ((((hasDerivAt_exp v).sub (hasDerivAt_const 1 v)).mul
      ((hasDerivAt_const 5 v).add (hasDerivAt_exp v))).sub ((hasDerivAt_id v).mul
      ((hasDerivAt_const 2 v).add ((hasDerivAt_exp v).const_mul 4)))) (by grind)
  have := monotone_of_deriv_nonneg (a := 0) (b := u) (fun t _ _ => hk t)
    (fun t h0 _ => jpos t h0) (Std.le_refl 0) hu (Std.le_refl u)
  rw [exp_zero] at this; grind

/-! ## The sequence `dₙ` -/

/-- `dₘ = log m! + m − (m + ½) log m`. -/
noncomputable def d (m : Nat) : R := log (fact m : R) + (m : R) - ((m : R) + 1 / 2) * log (m : R)

/-- **The one-step bounds** `0 ≤ dₘ − d_{m+1} ≤ 1/(4m(m+1))` for `m ≥ 1`, in multiplied-out form. -/
theorem step_bounds (n : Nat) :
    0 ≤ d (n + 1) - d (n + 2) ∧
      4 * ((n : R) + 1) * ((n : R) + 2) * (d (n + 1) - d (n + 2)) ≤ 1 := by
  have hn0 : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  generalize hm : (n : R) + 1 = m
  have hm1 : 1 ≤ m := by grind
  have hmpos : 0 < m := by grind
  have c1 : ((n + 1 : Nat) : R) = m := by rw [← hm]; grind
  have c2 : ((n + 2 : Nat) : R) = m + 1 := by rw [← hm]; grind
  have hF : (fact (n + 2) : R) = (m + 1) * (fact (n + 1) : R) := by
    rw [fact_succ' (n + 1), c1]
  have hlogF : log (fact (n + 2) : R) = log (m + 1) + log (fact (n + 1) : R) := by
    rw [hF]; exact log_mul (by grind) (fact_pos' _)
  -- `dₘ − d_{m+1} = (m + ½) u − 1` with `u = log(m+1) − log m`.
  have hdiff : d (n + 1) - d (n + 2) = (m + 1 / 2) * (log (m + 1) - log m) - 1 := by
    unfold d; rw [c1, c2, hlogF]; grind
  rw [show (n : R) + 2 = m + 1 by rw [← hm]; grind, hdiff]
  generalize hu : log (m + 1) - log m = u
  -- `eᵘ = (m + 1)/m`, so with `w = 1/m`: `eᵘ = 1 + w`, `m w = 1`.
  have hmw : m * (1 / m) = 1 := by grind
  generalize hw : 1 / m = w at hmw
  have heu : exp u = 1 + w := by
    rw [← hu, show log (m + 1) - log m = log (m + 1) + -log m by grind, exp_add,
      exp_log (by grind)]
    have := exp_mul_exp_neg (log m); rw [exp_log hmpos] at this
    have e2 : exp (-log m) = w := by
      have := cancel_left (u := m) (by grind) (show m * exp (-log m) = m * w by grind); exact this
    rw [e2]; grind
  have hu0 : 0 ≤ u := by
    rw [← hu]
    have := log_strictMono hmpos (by grind : m < m + 1); grind
  have i1 := exp_ineq1 hu0
  have i2 := exp_ineq2 hu0
  rw [heu] at i1 i2
  constructor
  · -- `2w ≤ u(2 + w)`, times `m`: `2 ≤ u(2m + 1)`.
    have k := OrderedRing.mul_le_mul_of_nonneg_left i1 (Std.le_of_lt hmpos)
    have e := congrArg (· * u) hmw
    grind
  · -- `u(6 + 4w) ≤ w(6 + w)`, times `m²`: `u m (6m + 4) ≤ 6m + 1`.
    have k := OrderedRing.mul_le_mul_of_nonneg_left i2
      (Std.le_of_lt (OrderedRing.mul_pos hmpos hmpos))
    have e1 := congrArg (· * (u * m)) hmw
    have e2 := congrArg (· * m) hmw
    have e3 := congrArg (· * (m * w)) hmw
    have k2 : u * m * (6 * m + 4) ≤ 6 * m + 1 := by grind
    -- Then `(6m+4) · [4m(m+1)((m+½)u − 1) − 1] ≤ 0`.
    have k3 := OrderedRing.mul_le_mul_of_nonneg_left k2 (OrderedRing.mul_nonneg (by grind : (0 : R) ≤ 2 * (m + 1)) (by grind : (0 : R) ≤ 2 * m + 1))
    have k4 : (6 * m + 4) * (4 * m * (m + 1) * ((m + 1 / 2) * u - 1)) ≤ (6 * m + 4) * 1 := by
      grind
    apply Classical.byContradiction; intro hc
    have := OrderedRing.mul_lt_mul_of_pos_left (by grind : (1 : R) < 4 * m * (m + 1) *
      ((m + 1 / 2) * u - 1)) (by grind : (0 : R) < 6 * m + 4)
    grind

/-! ## Convergence of `dₙ` -/

/-- The shifted sequence `sₙ = d_{n+1}`. -/
noncomputable def s (n : Nat) : R := d (n + 1)

/-- `sₙ` decreases. -/
theorem s_anti (n : Nat) : s (n + 1) ≤ s n := by
  have := (step_bounds n).1; show d (n + 1 + 1) ≤ d (n + 1); grind

/-- `sₙ ≥ s₀ − 1/4`. -/
theorem s_lower (n : Nat) : s 0 - 1 / 4 ≤ s n := by
  -- `Tₙ = sₙ − 1/(4(n+1))` increases.
  let T : Nat → R := fun n => s n - 1 / (4 * ((n : R) + 1))
  have hT : ∀ n, T n ≤ T (n + 1) := fun n => by
    have hb := (step_bounds n).2
    have hn0 : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    show s n - 1 / (4 * ((n : R) + 1)) ≤ s (n + 1) - 1 / (4 * (((n + 1 : Nat) : R) + 1))
    rw [show (((n + 1 : Nat) : R) + 1) = (n : R) + 2 by grind]
    change 4 * ((n : R) + 1) * ((n : R) + 2) * (s n - s (n + 1)) ≤ 1 at hb
    have ha : 4 * ((n : R) + 1) * (1 / (4 * ((n : R) + 1))) = 1 := by grind
    have hb' : 4 * ((n : R) + 2) * (1 / (4 * ((n : R) + 2))) = 1 := by grind
    generalize 1 / (4 * ((n : R) + 1)) = a at ha ⊢
    generalize 1 / (4 * ((n : R) + 2)) = b at hb' ⊢
    have e1 := congrArg (· * ((n : R) + 2)) ha
    have e2 := congrArg (· * ((n : R) + 1)) hb'
    -- `4(n+1)(n+2)(a − b) = 1`.
    have key : 4 * ((n : R) + 1) * ((n : R) + 2) * (a - b) = 1 := by grind
    apply Classical.byContradiction; intro hc
    have := OrderedRing.mul_lt_mul_of_pos_left (by grind : a - b < s n - s (n + 1))
      (OrderedRing.mul_pos (OrderedRing.mul_pos (by grind : (0 : R) < 4 * ((n : R) + 1))
        (by grind : (0 : R) < (n : R) + 2)) (by grind : (0 : R) < 1) |> fun h => by
          have : (0 : R) < 4 * ((n : R) + 1) * ((n : R) + 2) := by
            have := OrderedRing.mul_pos (by grind : (0 : R) < 4 * ((n : R) + 1))
              (by grind : (0 : R) < (n : R) + 2)
            exact this
          exact this)
    grind
  have := mono_le hT (Nat.zero_le n)
  have hn : 0 < 1 / (4 * ((n : R) + 1)) := div_pos (by grind) (by
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg; grind)
  show s 0 - 1 / 4 ≤ s n
  change s 0 - 1 / (4 * (((0 : Nat) : R) + 1)) ≤ s n - 1 / (4 * ((n : R) + 1)) at this
  rw [show 1 / (4 * (((0 : Nat) : R) + 1)) = 1 / 4 by grind] at this
  grind

/-- **The sequence `dₙ` converges.** -/
theorem exists_lim : ∃ D, Tendsto s D := by
  obtain ⟨L, hL⟩ := monotone_convergence (a := fun n => -s n) (fun n => by
    have := s_anti n; show -s n ≤ -s (n + 1); grind) ⟨-(s 0 - 1 / 4), fun n => by
      have := s_lower n; show -s n ≤ _; grind⟩
  refine ⟨-L, ?_⟩
  have := hL.const_mul (-1)
  rw [show -1 * L = -L by grind] at this
  exact this.congr_eventually 0 fun n _ => by show -1 * -s n = s n; grind

/-! ## Identifying the limit with Wallis -/

/-- `log (xᵏ) = k log x` for `x > 0`. -/
theorem log_pow {x : R} (hx : 0 < x) (k : Nat) : log (x ^ k) = (k : R) * log x := by
  induction k with
  | zero => show log 1 = _; rw [log_one]; grind
  | succ k ih =>
    rw [pow_succ', log_mul (pow_pos' hx k) hx, ih]; grind

/-- The partial Wallis products in factorial form: `wₖ ((2k)!)² (2k+1) = 16ᵏ (k!)⁴`. -/
theorem wp_fact (k : Nat) : wp k * ((fact (2 * k) : R) * (fact (2 * k) : R) * (2 * (k : R) + 1)) =
    (16 : R) ^ k * ((fact k : R) * (fact k : R) * ((fact k : R) * (fact k : R))) := by
  induction k with
  | zero =>
    rw [show fact (2 * 0) = 1 from rfl]
    show (1 : R) * (((1 : Nat) : R) * ((1 : Nat) : R) * (2 * ((0 : Nat) : R) + 1)) = 1 * _; grind
  | succ k ih =>
    have hk0 : (0 : R) ≤ (k : R) := OrderedRing.natCast_nonneg
    have f1 : (fact (2 * (k + 1)) : R) = (2 * (k : R) + 2) * ((2 * (k : R) + 1) * (fact (2 * k) : R)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, fact_succ', fact_succ']; grind
    have f2 : (fact (k + 1) : R) = ((k : R) + 1) * (fact k : R) := fact_succ' k
    have w1 : wp (k + 1) = wp k * ((2 * (k : R) + 2) * (2 * (k : R) + 2) /
        ((2 * (k : R) + 1) * (2 * (k : R) + 3))) := rfl
    rw [f1, f2, w1, pow_succ']
    have c : ((k + 1 : Nat) : R) = (k : R) + 1 := by grind
    rw [c]
    have hq : (2 * (k : R) + 2) * (2 * (k : R) + 2) / ((2 * (k : R) + 1) * (2 * (k : R) + 3)) *
        ((2 * (k : R) + 1) * (2 * (k : R) + 3)) = (2 * (k : R) + 2) * (2 * (k : R) + 2) := by
      have : (2 * (k : R) + 1) * (2 * (k : R) + 3) ≠ 0 := by
        have := OrderedRing.mul_pos (by grind : (0 : R) < 2 * (k : R) + 1)
          (by grind : (0 : R) < 2 * (k : R) + 3); grind
      grind
    generalize (2 * (k : R) + 2) * (2 * (k : R) + 2) / ((2 * (k : R) + 1) * (2 * (k : R) + 3)) = q
      at hq ⊢
    generalize (fact (2 * k) : R) = F2 at ih ⊢
    generalize (fact k : R) = F at ih ⊢
    generalize wp k = W at ih ⊢
    generalize (16 : R) ^ k = P at ih ⊢
    have e := congrArg (· * (q * ((2 * (k : R) + 1) * (2 * (k : R) + 3)) - (2 * (k : R) + 2) *
      (2 * (k : R) + 2))) ih
    grind

/-- `wₖ > 0`. -/
theorem wp_pos (k : Nat) : 0 < wp k := by
  rw [wp_eq]
  exact div_pos (OrderedRing.mul_pos hpi_pos (I_pos _)) (I_pos _)

/-- `log m! = dₘ − m + (m + ½) log m`. -/
theorem log_fact (m : Nat) : log (fact m : R) = d m - (m : R) + ((m : R) + 1 / 2) * log (m : R) := by
  unfold d; grind

/-- `log 16 = 4 log 2`. -/
theorem log_16 : log (16 : R) = 4 * log 2 := by
  rw [show (16 : R) = 2 * 2 * (2 * 2) by grind, log_mul (by grind) (by grind),
    log_mul (by grind) (by grind)]; grind

/-- **The Wallis product in terms of `d`**:
`log w_{n+1} = 4 sₙ − 2 s_{2n+1} − log 2 − log(2 + 1/(n+1))`. -/
theorem log_wp (n : Nat) :
    log (wp (n + 1)) = 4 * s n - 2 * s (2 * n + 1) - log 2 - log (2 + 1 / ((n : R) + 1)) := by
  have hn0 : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  have h := congrArg log (wp_fact (n + 1))
  have ck : ((n + 1 : Nat) : R) = (n : R) + 1 := by grind
  have c2 : ((2 * (n + 1) : Nat) : R) = 2 * ((n : R) + 1) := by grind
  have pF := fact_pos' (n + 1); have pF2 := fact_pos' (2 * (n + 1))
  rw [ck] at h
  rw [log_mul (wp_pos _) (OrderedRing.mul_pos (OrderedRing.mul_pos pF2 pF2) (by grind)),
    log_mul (OrderedRing.mul_pos pF2 pF2) (by grind), log_mul pF2 pF2,
    log_mul (pow_pos' (by grind) _) (OrderedRing.mul_pos (OrderedRing.mul_pos pF pF)
      (OrderedRing.mul_pos pF pF)),
    log_mul (OrderedRing.mul_pos pF pF) (OrderedRing.mul_pos pF pF), log_mul pF pF,
    log_pow (by grind), log_16, log_fact, log_fact, ck, c2] at h
  rw [log_mul (by grind : (0 : R) < 2) (by grind : (0 : R) < (n : R) + 1)] at h
  have e3 : log (2 * ((n : R) + 1) + 1) = log ((n : R) + 1) + log (2 + 1 / ((n : R) + 1)) := by
    rw [← log_mul (by grind) (by
      have : 0 < 1 / ((n : R) + 1) := div_pos (by grind) (by grind); grind)]
    congr 1; grind
  rw [e3] at h
  have hs1 : s n = d (n + 1) := rfl
  have hs2 : s (2 * n + 1) = d (2 * (n + 1)) := by
    show d (2 * n + 1 + 1) = _; rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
  rw [hs1, hs2]
  grind

/-- Continuity of `log` at positive points. -/
theorem continuousAt_log {y : R} (hy : 0 < y) : R.ContinuousAt log y :=
  (hasDerivAt_log hy).continuousAt

/-- **The limit of `dₙ` is `½ log(2π)`.** -/
theorem tendsto_s : Tendsto s (log (2 * pi) / 2) := by
  obtain ⟨D, hD⟩ := exists_lim
  have hπ := pi_pos
  -- Left side: `log w_{n+1} → log(π/2)`.
  have hW : Tendsto (fun n => wp (n + 1)) (pi / 2) :=
    (wallis.shift 1).congr_eventually 0 fun n _ => by show wp (1 + n) = wp (n + 1); rw [Nat.add_comm]
  have h1 := tendsto_comp (continuousAt_log (by grind : (0 : R) < pi / 2)) hW
  -- Right side.
  have hD2 : Tendsto (fun n => s (2 * n + 1)) D := fun ε hε => by
    obtain ⟨N, hN⟩ := hD ε hε; exact ⟨N, fun n hn => hN _ (by omega)⟩
  have hinv : Tendsto (fun n => 2 + 1 / ((n : R) + 1)) 2 := fun ε hε => by
    obtain ⟨N, hN⟩ := eps_small hε
    refine ⟨N, fun n hn => ?_⟩
    have k := hN n hn; have := eps_pos n
    rw [show 2 + 1 / ((n : R) + 1) - 2 = 1 / ((n : R) + 1) by grind, abs_of_nonneg (by grind)]
    exact k
  have hl2 := tendsto_comp (continuousAt_log (by grind : (0 : R) < 2)) hinv
  have h2 := Tendsto.sub (Tendsto.sub (Tendsto.sub (hD.const_mul 4) (hD2.const_mul 2))
    (tendsto_const (log 2))) hl2
  have h1' : Tendsto (fun n => log (wp (n + 1)))
      (4 * D - 2 * D - log 2 - log 2) :=
    h2.congr_eventually 0 fun n _ => (log_wp n).symm
  have heq := tendsto_unique h1 h1'
  have e : log (2 * pi) = log (pi / 2) + 2 * log 2 := by
    rw [show 2 * pi = pi / 2 * (2 * 2) by grind, log_mul (by grind) (by grind),
      log_mul (by grind) (by grind)]; grind
  rw [e, show log (pi / 2) + 2 * log 2 = 2 * D by grind, show 2 * D / 2 = D by grind]
  exact hD

/-! ## Stirling's formula -/

/-- `xᵏ = exp(k log x)` for `x > 0`. -/
theorem pow_eq_exp {x : R} (hx : 0 < x) (k : Nat) : x ^ k = exp ((k : R) * log x) := by
  rw [← log_pow hx, exp_log (pow_pos' hx k)]

/-- The ratio in Stirling's formula equals `exp(sₙ − ½ log(2π))`. -/
theorem ratio_eq (n : Nat) :
    (fact (n + 1) : R) / (sqrt (2 * pi * ((n : R) + 1)) * (((n : R) + 1) / e) ^ (n + 1)) =
      exp (s n - log (2 * pi) / 2) := by
  have hn0 : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  have hπ := pi_pos
  have hm : (0 : R) < (n : R) + 1 := by grind
  have ck : ((n + 1 : Nat) : R) = (n : R) + 1 := by grind
  -- The pieces as exponentials.
  have hF : (fact (n + 1) : R) = exp (log (fact (n + 1) : R)) := (exp_log (fact_pos' _)).symm
  have h2π : 0 < 2 * pi * ((n : R) + 1) := OrderedRing.mul_pos (by grind) hm
  have hsq : sqrt (2 * pi * ((n : R) + 1)) = exp (log (2 * pi * ((n : R) + 1)) / 2) :=
    sqrt_eq (Std.le_of_lt (exp_pos _)) (by rw [← exp_add, show log (2 * pi * ((n : R) + 1)) / 2 +
      log (2 * pi * ((n : R) + 1)) / 2 = log (2 * pi * ((n : R) + 1)) by grind, exp_log h2π])
  have he : e = exp 1 := rfl
  have hq : 0 < ((n : R) + 1) / e := div_pos hm (exp_pos 1)
  have hlq : log (((n : R) + 1) / e) = log ((n : R) + 1) - 1 := by
    rw [Field.div_eq_mul_inv, he]
    have : (exp 1)⁻¹ = exp (-1) := by
      have := exp_mul_exp_neg 1
      have := Field.mul_inv_cancel (show exp 1 ≠ 0 by have := exp_pos 1; grind)
      exact cancel_left (u := exp 1) (by have := exp_pos 1; grind) (by grind)
    rw [this, log_mul hm (exp_pos _), log_exp]; grind
  rw [hF, hsq, pow_eq_exp hq, hlq, ← exp_add, log_fact, log_mul (by grind) hm, ck]
  -- `exp a / exp b = exp (a − b)`.
  generalize hA : d (n + 1) - ((n : R) + 1) + ((n : R) + 1 + 1 / 2) * log ((n : R) + 1) = A
  generalize hB : (log (2 * pi) + log ((n : R) + 1)) / 2 +
    ((n + 1 : Nat) : R) * (log ((n : R) + 1) - 1) = B
  have hAB : A - B = s n - log (2 * pi) / 2 := by
    rw [← hA, ← hB, ck]; show _ = d (n + 1) - _; grind
  rw [← hAB]
  have := exp_add (A - B) B
  rw [show A - B + B = A by grind] at this
  have hB0 := exp_pos B
  rw [this]; grind

/-- **Stirling's formula** (de Moivre and Stirling, 1730). `n! / (√(2πn) (n/e)ⁿ) → 1`. -/
theorem stirling : Tendsto (fun n => (fact (n + 1) : R) /
    (sqrt (2 * pi * ((n : R) + 1)) * (((n : R) + 1) / e) ^ (n + 1))) 1 := by
  have h := Tendsto.sub tendsto_s (tendsto_const (log (2 * pi) / 2))
  rw [show log (2 * pi) / 2 - log (2 * pi) / 2 = 0 by grind] at h
  have h2 := tendsto_comp (continuousAt_exp 0) h
  rw [exp_zero] at h2
  exact h2.congr_eventually 0 fun n _ => (ratio_eq n).symm

end Stirling

end Foundations.Topology
