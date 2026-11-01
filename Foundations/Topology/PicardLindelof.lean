import Foundations.Topology.UniformConvergence

/-!
# The Picard–Lindelöf theorem

When does a differential equation `y' = F(t, y)` with initial value `y(t₀) = y₀` have a solution,
and when is it unique? Émile **Picard** (1890) answered: when `F` is continuous and *Lipschitz* in
`y`, i.e. `|F(t, y) − F(t, z)| ≤ L |y − z|`; Ernst Lindelöf (1894) sharpened the statement.

The modern proof, which we follow, is Banach's: by the fundamental theorem of calculus the
differential equation is equivalent to the **integral equation**

  `y(t) = y₀ + ∫_{t₀}^{t} F(s, y(s)) ds`,

i.e. to `y` being a fixed point of the operator `T` on the right. On the complete metric space
`C[t₀, t₀ + h]` with the sup metric, `T` shrinks distances by the factor `L h`; for `h` small
(`L h ≤ 1/2`) it is a contraction, and **Banach's fixed-point theorem** produces the solution —
the limit of Picard's iterates `y₀, T y₀, T (T y₀), …`. Uniqueness among all differentiable
solutions follows from the mean value theorem: two solutions can never drift apart, since their
difference `w` satisfies `|w'| ≤ L |w|`.

For `y' = y`, `y(0) = 1` the unique solution is the exponential function of `Numbers/Exp`.

We work on the forward interval `[t₀, t₀ + h]`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

/-- A function continuous on `[a, b]` is bounded there. -/
theorem bound_on {u : R → R} {a b : R} (hab : a ≤ b)
    (hu : ∀ x, a ≤ x → x ≤ b → R.ContinuousAt u x) : ∃ M, ∀ x, a ≤ x → x ≤ b → abs (u x) ≤ M := by
  obtain ⟨c₁, -, -, h₁⟩ := extreme_value hab hu
  obtain ⟨c₂, -, -, h₂⟩ := extreme_value (f := fun x => 0 - u x) hab
    fun x h1 h2 => continuousAt_sub (continuousAt_const 0 x) (hu x h1 h2)
  refine ⟨abs (u c₁) + abs (0 - u c₂), fun x h1 h2 => ?_⟩
  have k1 := h₁ x h1 h2; have k2 := h₂ x h1 h2
  have := le_abs (u c₁); have := le_abs (0 - u c₂)
  have := abs_nonneg (u c₁); have := abs_nonneg (0 - u c₂)
  exact abs_le.2 ⟨by grind, by grind⟩

/-- Derivatives are local: a function agreeing with `f` near `x` has the same derivative. -/
theorem HasDerivAt.congr_nhds {f g : R → R} {d x δ : R} (hf : HasDerivAt f d x) (hδ : 0 < δ)
    (h : ∀ z, abs (z - x) < δ → g z = f z) : HasDerivAt g d x := fun ε hε => by
  obtain ⟨δ', hδ', k⟩ := hf ε hε
  obtain ⟨η, hη, e1, e2⟩ := exists_pos_le_both hδ hδ'
  refine ⟨η, hη, fun y hy => ?_⟩
  rw [h y (by grind), h x (by rw [show x - x = 0 by grind, R.abs_zero]; exact hδ)]
  exact k y (by grind)

section Picard

variable {F : R → R → R}

/-- `F` is **jointly continuous**. -/
def JointCont (F : R → R → R) : Prop :=
  ∀ t y, ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧ ∀ t' y', abs (t' - t) < δ → abs (y' - y) < δ →
    abs (F t' y' - F t y) < ε

/-- Composing a jointly continuous `F` with a continuous `y` gives a continuous `s ↦ F(s, y(s))`. -/
theorem JointCont.comp (hF : JointCont F) {y : R → R} (hy : ∀ s, R.ContinuousAt y s) (s : R) :
    R.ContinuousAt (fun s => F s (y s)) s := fun ε hε => by
  obtain ⟨δ, hδ, k⟩ := hF s (y s) ε hε
  obtain ⟨δ', hδ', k'⟩ := hy s δ hδ
  obtain ⟨η, hη, e1, e2⟩ := exists_pos_le_both hδ hδ'
  exact ⟨η, hη, fun t ht => k t (y t) (by grind) (k' t (by grind))⟩

/-- `∫_{t₀}^{t₀} φ = 0`. -/
theorem integral_self {φ : R → R} (hφ : ∀ s, R.ContinuousAt φ s) (t₀ : R) : integral φ t₀ t₀ = 0 := by
  have := integral_add_interval (f := φ) (a := t₀) (u := t₀) (v := t₀) (Std.le_refl _)
    (Std.le_refl _) fun x _ _ => hφ x
  grind

/-- Lipschitz bound for the integral: `|∫_{t₀}^v φ − ∫_{t₀}^u φ| ≤ M |v − u|` on `[t₀, b]`. -/
theorem integral_lipschitz {φ : R → R} (hφ : ∀ s, R.ContinuousAt φ s) {t₀ b M : R}
    (hM : ∀ s, t₀ ≤ s → s ≤ b → abs (φ s) ≤ M) {u v : R} (hu : t₀ ≤ u) (hu' : u ≤ b) (hv : t₀ ≤ v)
    (hv' : v ≤ b) : abs (integral φ t₀ v - integral φ t₀ u) ≤ M * abs (v - u) := by
  have key : ∀ p q, t₀ ≤ p → p ≤ q → q ≤ b →
      abs (integral φ t₀ q - integral φ t₀ p) ≤ M * (q - p) := fun p q h1 h2 h3 => by
    rw [integral_add_interval h1 h2 fun x _ _ => hφ x,
      show integral φ t₀ p + integral φ p q - integral φ t₀ p = integral φ p q by grind]
    have := (hasIntegral_integral h2 fun x _ _ => hφ x).abs_sub_le (c := 0) (ε := M) h2
      fun s hs1 hs2 => by rw [show φ s - 0 = φ s by grind]; exact hM s (by grind) (by grind)
    rw [show integral φ p q - 0 * (q - p) = integral φ p q by grind] at this; exact this
  rcases (by grind : u ≤ v ∨ v ≤ u) with h | h
  · rw [abs_of_nonneg (by grind : (0 : R) ≤ v - u)]; exact key u v hu h hv'
  · rw [abs_sub_comm, abs_sub_comm v, abs_of_nonneg (by grind : (0 : R) ≤ u - v)]
    exact key v u hv h hu'

/-- **Picard–Lindelöf theorem.** Let `F` be jointly continuous and globally Lipschitz in `y` with
constant `L`. Then for every initial value `y(t₀) = y₀` there is `h > 0` and a solution `y` of
`y' = F(t, y)` on the forward interval `[t₀, t₀ + h]` (differentiable inside, continuous
everywhere), and every other solution (continuous at every point of `[t₀, t₀ + h]`) coincides
with it on `[t₀, t₀ + h]`. -/
theorem picard_lindelof (hF : JointCont F) {L : R} (hL0 : 0 ≤ L)
    (hL : ∀ t y z, abs (F t y - F t z) ≤ L * abs (y - z)) (t₀ y₀ : R) :
    ∃ h : R, 0 < h ∧ ∃ y : R → R, y t₀ = y₀ ∧ (∀ t, R.ContinuousAt y t) ∧
      (∀ t, t₀ < t → t < t₀ + h → HasDerivAt y (F t (y t)) t) ∧
      ∀ z : R → R, z t₀ = y₀ → (∀ t, t₀ ≤ t → t ≤ t₀ + h → R.ContinuousAt z t) →
        (∀ t, t₀ < t → t < t₀ + h → HasDerivAt z (F t (z t)) t) →
        ∀ t, t₀ ≤ t → t ≤ t₀ + h → z t = y t := by
  let h : R := 1 / (2 * (L + 1))
  have hh : 0 < h := div_pos (by grind) (by grind)
  have hLh : L * h ≤ 1 / 2 := by
    have : (2 * (L + 1)) * h = 1 := by grind
    grind
  let b := t₀ + h
  have hab : t₀ ≤ b := by grind
  haveI : LeFact t₀ b := ⟨hab⟩
  -- The integral operator on `C[t₀, b]`.
  have hφ : ∀ y : CFun t₀ b, ∀ s, R.ContinuousAt (fun s => F s (y.1 s)) s :=
    fun y => hF.comp y.2.2
  let Tf : CFun t₀ b → R → R := fun y t => y₀ + integral (fun s => F s (y.1 s)) t₀ (clamp t₀ b t)
  have hTc : ∀ y t, R.ContinuousAt (Tf y) t := fun y t ε hε => by
    obtain ⟨M, hM⟩ := bound_on hab fun s _ _ => hφ y s
    have hM0 : 0 ≤ M := Std.le_trans (abs_nonneg _) (hM t₀ (Std.le_refl _) hab)
    refine ⟨ε / (M + 1), div_pos hε (by grind), fun t' ht' => ?_⟩
    have m := clamp_mem hab t; have m' := clamp_mem hab t'
    have k := integral_lipschitz (hφ y) hM m.1 m.2 m'.1 m'.2
    have k2 := abs_clamp_sub_le hab t' t
    show abs (y₀ + _ - (y₀ + _)) < ε
    rw [show ∀ p q : R, y₀ + p - (y₀ + q) = p - q from fun p q => by grind]
    have k3 := OrderedRing.mul_le_mul_of_nonneg_left k2 hM0
    have k4 := OrderedRing.mul_lt_mul_of_pos_left ht' (by grind : 0 < M + 1)
    have e : (M + 1) * (ε / (M + 1)) = ε := by grind
    have k5 : M * abs (t' - t) ≤ (M + 1) * abs (t' - t) := by have := abs_nonneg (t' - t); grind
    exact Std.lt_of_le_of_lt (Std.le_trans k (Std.le_trans k3 k5)) (by rw [← e]; exact k4)
  let T : CFun t₀ b → CFun t₀ b := fun y => ⟨Tf y, fun x => by
    show y₀ + _ = y₀ + _; rw [clamp_clamp hab], hTc y⟩
  -- `T` is a contraction with constant `1/2`.
  have hcontr : ∀ y z, dist (T y) (T z) ≤ 1 / 2 * dist y z := fun y z => by
    apply CFun.supDist_le
    intro t
    have m := clamp_mem hab t
    have hd : 0 ≤ dist y z := dist_nonneg y z
    change abs ((y₀ + integral (fun s => F s (y.1 s)) t₀ (clamp t₀ b t)) -
      (y₀ + integral (fun s => F s (z.1 s)) t₀ (clamp t₀ b t))) ≤ _
    generalize clamp t₀ b t = c at m ⊢
    have hy := hasIntegral_integral m.1 fun x _ _ => hφ y x
    have hz := hasIntegral_integral m.1 fun x _ _ => hφ z x
    have k := (hy.add (hz.const_mul (-1))).abs_sub_le (c := 0) (ε := L * dist y z) m.1
      fun s _ _ => by
        have k1 := hL s (y.1 s) (z.1 s)
        have k2 := OrderedRing.mul_le_mul_of_nonneg_left (CFun.le_supDist y z s) hL0
        have e : CFun.supDist y z = dist y z := rfl
        rw [e] at k2
        rw [show F s (y.1 s) + -1 * F s (z.1 s) - 0 = F s (y.1 s) - F s (z.1 s) by grind]
        exact Std.le_trans k1 k2
    have k2 := OrderedRing.mul_le_mul_of_nonneg_left (by grind : c - t₀ ≤ h)
      (OrderedRing.mul_nonneg hL0 hd)
    have k3 := OrderedRing.mul_le_mul_of_nonneg_right hLh hd
    have e : L * dist y z * h = L * h * dist y z := by grind
    grind
  let y0c : CFun t₀ b := ⟨fun _ => y₀, fun _ => rfl, fun x => continuousAt_const y₀ x⟩
  obtain ⟨y, hy, -, -⟩ := banach_fixed_point (CFun.complete (a := t₀) (b := b)) (q := 1 / 2)
    (by grind) (by grind) hcontr y0c
  have hfix : ∀ t, y.1 t = y₀ + integral (fun s => F s (y.1 s)) t₀ (clamp t₀ b t) :=
    fun t => (congrArg (fun w : CFun t₀ b => w.1 t) hy).symm
  -- The fixed point solves the differential equation.
  have hY0 : y.1 t₀ = y₀ := by
    rw [hfix, clamp_of_mem hab (Std.le_refl _) hab, integral_self (hφ y)]; grind
  have hYd : ∀ t, t₀ < t → t < b → HasDerivAt y.1 (F t (y.1 t)) t := fun t ht1 ht2 => by
    have hI := ftc1 (f := fun s => F s (y.1 s)) (a := t₀) (b := b) (fun x _ _ => hφ y x) ht1 ht2
    have h2 : HasDerivAt (fun v => y₀ + integral (fun s => F s (y.1 s)) t₀ v)
        (0 + F t (y.1 t)) t := (hasDerivAt_const y₀ t).add hI
    obtain ⟨δ, hδ, hδ'⟩ := nhds_of_interior ht1 ht2
    have h3 := HasDerivAt.congr_nhds (g := y.1) h2 hδ fun v hv => by
      obtain ⟨a1, a2⟩ := hδ' v hv
      show y.1 v = y₀ + _
      rw [hfix, clamp_of_mem hab (Std.le_of_lt a1) (Std.le_of_lt a2)]
    rw [show (0 : R) + F t (y.1 t) = F t (y.1 t) by grind] at h3
    exact h3
  refine ⟨h, hh, y.1, hY0, y.2.2, hYd, fun z hz0 hzc hzd => ?_⟩
  -- Uniqueness: the difference `w` of two solutions satisfies `|w'| ≤ L |w|`.
  let w : R → R := fun t => z t - y.1 t
  have hwc : ∀ t, t₀ ≤ t → t ≤ b → R.ContinuousAt w t := fun t h1 h2 =>
    continuousAt_sub (hzc t h1 h2) (y.2.2 t)
  have hwd : ∀ t, t₀ < t → t < b → HasDerivAt w (F t (z t) - F t (y.1 t)) t := fun t h1 h2 =>
    (hzd t h1 h2).sub (hYd t h1 h2)
  obtain ⟨Mw, hMw⟩ := bound_on hab hwc
  obtain ⟨B, hB1, hB2⟩ := exists_lub (fun s => ∃ t, t₀ ≤ t ∧ t ≤ b ∧ s = abs (w t))
    ⟨_, t₀, Std.le_refl _, hab, rfl⟩ ⟨Mw, fun s ⟨t, h1, h2, hs⟩ => hs ▸ hMw t h1 h2⟩
  have hwB : ∀ t, t₀ ≤ t → t ≤ b → abs (w t) ≤ B := fun t h1 h2 => hB1 _ ⟨t, h1, h2, rfl⟩
  have hw0 : w t₀ = 0 := by show z t₀ - y.1 t₀ = 0; rw [hz0, hY0]; grind
  have hB0 : 0 ≤ B := by have := hwB t₀ (Std.le_refl _) hab; have := abs_nonneg (w t₀); grind
  have half : ∀ t, t₀ ≤ t → t ≤ b → abs (w t) ≤ B / 2 := fun t h1 h2 => by
    rcases (by grind : t = t₀ ∨ t₀ < t) with e | e
    · rw [e, hw0, R.abs_zero]; grind
    · obtain ⟨c, hc1, hc2, hc3⟩ := mean_value (f := w) (f' := fun c => F c (z c) - F c (y.1 c)) e
        (fun s s1 s2 => hwc s s1 (by grind)) (fun s s1 s2 => hwd s s1 (by grind))
      rw [hw0] at hc3
      have k1 := hL c (z c) (y.1 c)
      have k2 := hwB c (by grind) (by grind)
      have hwt : abs (w t) = abs (F c (z c) - F c (y.1 c)) * (t - t₀) := by
        rw [show w t = w t - 0 by grind, hc3, abs_mul, abs_of_nonneg (by grind : (0 : R) ≤ t - t₀)]
      have k3 := OrderedRing.mul_le_mul_of_nonneg_left k2 hL0
      have k4 := OrderedRing.mul_le_mul_of_nonneg_right (Std.le_trans k1 (by
        show L * abs (z c - y.1 c) ≤ L * B; exact k3)) (by grind : (0 : R) ≤ t - t₀)
      have k5 := OrderedRing.mul_le_mul_of_nonneg_left (by grind : t - t₀ ≤ h)
        (OrderedRing.mul_nonneg hL0 hB0)
      have k6 := OrderedRing.mul_le_mul_of_nonneg_right hLh hB0
      grind
  have hBle : B ≤ B / 2 := hB2 _ fun s ⟨t, h1, h2, hs⟩ => hs ▸ half t h1 h2
  intro t h1 h2
  have := hwB t h1 h2
  have := eq_zero_of_abs_le (x := w t) (by grind)
  show z t = y.1 t
  grind

/-- **Example: `y' = y`, `y(0) = 1`.** On a small interval `[0, h]` every solution of this initial
value problem is the exponential function (`Numbers/Exp`). -/
theorem picard_exp : ∃ h : R, 0 < h ∧ ∀ z : R → R, z 0 = 1 →
    (∀ t, 0 ≤ t → t ≤ 0 + h → R.ContinuousAt z t) →
    (∀ t, 0 < t → t < 0 + h → HasDerivAt z (z t) t) → ∀ t, 0 ≤ t → t ≤ 0 + h → z t = exp t := by
  have hF : JointCont (fun _ y => y) := fun t y ε hε => ⟨ε, hε, fun _ _ _ h => h⟩
  obtain ⟨h, hh, y, -, -, -, huniq⟩ := picard_lindelof hF (L := 1) (by grind)
    (fun _ y z => by show _ ≤ 1 * _; grind) 0 1
  refine ⟨h, hh, fun z hz0 hzc hzd t h1 h2 => ?_⟩
  rw [huniq z hz0 hzc hzd t h1 h2, ← huniq exp exp_zero
    (fun t _ _ => (hasDerivAt_exp t).continuousAt) (fun t _ _ => hasDerivAt_exp t) t h1 h2]

end Picard

end Foundations.Topology
