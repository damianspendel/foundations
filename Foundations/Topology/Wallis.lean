import Foundations.Topology.ArzelaAscoli

/-!
# The Wallis product

John **Wallis** (*Arithmetica Infinitorum*, 1656), interpolating between areas he could compute,
found the first infinite product in mathematics:

  `π/2 = (2·2)/(1·3) · (4·4)/(3·5) · (6·6)/(5·7) ⋯ = Π_{n ≥ 1} (2n)² / ((2n − 1)(2n + 1))`.

With the calculus of the previous parts it follows from the integrals

  `Iₙ = ∫₀^{π/2} cosⁿ x dx`,  with `I₀ = π/2`, `I₁ = 1`, and `(n + 2) I_{n+2} = (n + 1) Iₙ`.

The recursion is an integration by parts, which we package as a single application of the
fundamental theorem of calculus to `F(x) = sin x · cos^{n+1} x`. Since `0 ≤ cos ≤ 1` on `[0, π/2]`,
the `Iₙ` decrease; hence `I_{2n+1}/I_{2n}` is squeezed between `(2n+1)/(2n+2)` and `1`, and tends to
`1`. Unwinding the recursion, the `n`-th partial Wallis product equals `(π/2) · I_{2n+1}/I_{2n}`.

The same integrals are the starting point of the solution of the Basel problem (next file).
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Wallis

/-- The number `π/2`. -/
noncomputable def hpi : R := pi / 2

/-- `π/2 > 0`. -/
theorem hpi_pos : 0 < hpi := pi_div_two_spec.1

/-- `cos (π/2) = 0`. -/
theorem cos_hpi : cos hpi = 0 := cos_pi_div_two

/-- `sin (π/2) = 1`. -/
theorem sin_hpi : sin hpi = 1 := sin_pi_div_two

/-- `0 ≤ cos x ≤ 1` on `[0, π/2]`. -/
theorem cos_mem {x : R} (h0 : 0 ≤ x) (h1 : x ≤ hpi) : 0 ≤ cos x ∧ cos x ≤ 1 := by
  refine ⟨?_, (abs_le.1 (abs_cos_le x)).2⟩
  rcases (by grind : x < hpi ∨ x = hpi) with e | e
  · exact Std.le_of_lt (pi_div_two_spec.2.2.2 x h0 e)
  · rw [e, cos_hpi]; exact Std.le_refl 0

/-- Sums of continuous functions are continuous. -/
theorem continuousAt_add {f g : R → R} {x : R} (hf : R.ContinuousAt f x) (hg : R.ContinuousAt g x) :
    R.ContinuousAt (fun y => f y + g y) x := by
  have := continuousAt_sub hf (continuousAt_sub (continuousAt_const 0 x) hg)
  intro ε hε; obtain ⟨δ, hδ, h⟩ := this ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have k : abs ((f y - (0 - g y)) - (f x - (0 - g x))) < ε := h y hy
  show abs (f y + g y - (f x + g x)) < ε
  rw [show f y + g y - (f x + g x) = (f y - (0 - g y)) - (f x - (0 - g x)) by grind]
  exact k

/-- Derivative of `cos^{k+1}`. -/
theorem hasDerivAt_cos_pow (k : Nat) (x : R) :
    HasDerivAt (fun y => cos y ^ (k + 1)) (((k : R) + 1) * cos x ^ k * -sin x) x :=
  (hasDerivAt_pow k (cos x)).comp (hasDerivAt_cos x)

/-- `cosⁿ` is continuous. -/
theorem continuousAt_cos_pow (n : Nat) (x : R) : R.ContinuousAt (fun y => cos y ^ n) x :=
  ((hasDerivAt_pow' n (cos x)).comp (hasDerivAt_cos x)).continuousAt

/-- Linearity: `∫ (f + g) = ∫ f + ∫ g` for continuous `f`, `g`. -/
theorem integral_add' {f g : R → R} {a b : R} (hab : a ≤ b) (hf : ∀ x, R.ContinuousAt f x)
    (hg : ∀ x, R.ContinuousAt g x) :
    integral (fun x => f x + g x) a b = integral f a b + integral g a b :=
  ((hasIntegral_integral hab fun x _ _ => hf x).add
    (hasIntegral_integral hab fun x _ _ => hg x)).integral_eq hab

/-- Linearity: `∫ c f = c ∫ f` for continuous `f`. -/
theorem integral_const_mul' (c : R) {f : R → R} {a b : R} (hab : a ≤ b)
    (hf : ∀ x, R.ContinuousAt f x) : integral (fun x => c * f x) a b = c * integral f a b :=
  ((hasIntegral_integral hab fun x _ _ => hf x).const_mul c).integral_eq hab

/-- Constant multiples of continuous functions are continuous. -/
theorem continuousAt_cmul (c : R) {f : R → R} {x : R} (hf : R.ContinuousAt f x) :
    R.ContinuousAt (fun y => c * f y) x := continuousAt_mul (continuousAt_const c x) hf

/-- **The Wallis integrals** `Iₙ = ∫₀^{π/2} cosⁿ x dx`. -/
noncomputable def I (n : Nat) : R := integral (fun x => cos x ^ n) 0 hpi

/-- `I₀ = π/2`. -/
theorem I_zero : I 0 = hpi := by
  have := (hasIntegral_const 1 (Std.le_of_lt hpi_pos)).integral_eq (Std.le_of_lt hpi_pos)
  unfold I; show integral (fun _ => (1 : R)) 0 hpi = hpi; rw [this]; grind

/-- `I₁ = 1`. -/
theorem I_one : I 1 = 1 := by
  unfold I
  rw [integral_eq_sub (F := sin) (Std.le_of_lt hpi_pos) (fun t _ _ => by
      have e : cos t ^ 1 = cos t := by show 1 * cos t = cos t; grind
      rw [e]; exact hasDerivAt_sin t) (fun t _ _ => continuousAt_cos_pow 1 t),
    sin_hpi, sin_zero]
  grind

/-- **The reduction formula** `(n + 2) I_{n+2} = (n + 1) Iₙ` (integration by parts). -/
theorem I_rec (m : Nat) : ((m : R) + 2) * I (m + 2) = ((m : R) + 1) * I m := by
  have hab := Std.le_of_lt hpi_pos
  -- `F = sin · cos^{m+1}` has derivative `(m+2) cos^{m+2} − (m+1) cos^m`.
  let g : R → R := fun x => ((m : R) + 2) * cos x ^ (m + 2) + (-((m : R) + 1)) * cos x ^ m
  have hd : ∀ t, 0 ≤ t → t ≤ hpi → HasDerivAt (fun x => sin x * cos x ^ (m + 1)) (g t) t :=
    fun t _ _ => by
      have h := (hasDerivAt_sin t).mul (hasDerivAt_cos_pow m t)
      have e : cos t * cos t ^ (m + 1) + sin t * (((m : R) + 1) * cos t ^ m * -sin t) = g t := by
        have p1 : cos t ^ (m + 1) = cos t ^ m * cos t := rfl
        have p2 : cos t ^ (m + 2) = cos t ^ m * cos t * cos t := rfl
        have py := sin_sq_add_cos_sq t
        show _ = ((m : R) + 2) * cos t ^ (m + 2) + (-((m : R) + 1)) * cos t ^ m
        rw [p1, p2]
        generalize cos t ^ m = C
        grind
      rw [e] at h; exact h
  have hgc : ∀ t, R.ContinuousAt g t := fun t =>
    continuousAt_add (continuousAt_cmul _ (continuousAt_cos_pow _ t))
      (continuousAt_cmul _ (continuousAt_cos_pow _ t))
  have h1 := integral_eq_sub hab hd fun t _ _ => hgc t
  have h2 : integral g 0 hpi = ((m : R) + 2) * I (m + 2) + (-((m : R) + 1)) * I m := by
    unfold I
    rw [integral_add' hab (fun t => continuousAt_cmul _ (continuousAt_cos_pow _ t))
      (fun t => continuousAt_cmul _ (continuousAt_cos_pow _ t)),
      integral_const_mul' _ hab (continuousAt_cos_pow _),
      integral_const_mul' _ hab (continuousAt_cos_pow _)]
  rw [h2, cos_hpi, sin_zero] at h1
  have : (0 : R) ^ (m + 1) = 0 := by show (0 : R) ^ m * 0 = 0; grind
  rw [this] at h1
  grind

/-- All `Iₙ` are positive. -/
theorem I_pos (n : Nat) : 0 < I n := by
  have key : ∀ n, 0 < I n ∧ 0 < I (n + 1) := by
    intro n
    induction n with
    | zero => rw [I_zero, show (0 : Nat) + 1 = 1 from rfl, I_one]; exact ⟨hpi_pos, by grind⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have := I_rec n
      have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
      have h3 := OrderedRing.mul_pos (by grind : (0 : R) < (n : R) + 1) ih.1
      rw [show n + 1 + 1 = n + 2 from rfl]
      apply Classical.byContradiction; intro hc
      have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : I (n + 2) ≤ 0)
        (by grind : (0 : R) ≤ (n : R) + 2)
      grind
  exact (key n).1

/-- The `Iₙ` decrease. -/
theorem I_anti (n : Nat) : I (n + 1) ≤ I n := by
  have hab := Std.le_of_lt hpi_pos
  exact HasIntegral.mono hab (hasIntegral_integral hab fun x _ _ => continuousAt_cos_pow _ x)
    (hasIntegral_integral hab fun x _ _ => continuousAt_cos_pow _ x) fun t h0 h1 => by
      obtain ⟨c0, c1⟩ := cos_mem h0 h1
      have hp : 0 ≤ cos t ^ n := pow_le_pow_left.pow_nonneg c0 n
      show cos t ^ n * cos t ≤ cos t ^ n
      have := OrderedRing.mul_le_mul_of_nonneg_left c1 hp
      grind

/-- The partial **Wallis products** `Π_{k=1}^{n} (2k)² / ((2k − 1)(2k + 1))`. -/
noncomputable def wp : Nat → R
  | 0 => 1
  | n + 1 => wp n * ((2 * (n : R) + 2) * (2 * (n : R) + 2) / ((2 * (n : R) + 1) * (2 * (n : R) + 3)))

/-- The partial product is `(π/2) · I_{2n+1} / I_{2n}`. -/
theorem wp_eq (n : Nat) : wp n = hpi * I (2 * n + 1) / I (2 * n) := by
  induction n with
  | zero =>
    show (1 : R) = hpi * I 1 / I 0
    rw [I_one, I_zero]; have := hpi_pos; grind
  | succ n ih =>
    show wp n * _ = _
    have r1 := I_rec (2 * n)
    have r2 := I_rec (2 * n + 1)
    have p1 := I_pos (2 * n); have p2 := I_pos (2 * n + 1)
    have p3 := I_pos (2 * n + 2); have p4 := I_pos (2 * n + 3)
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, show 2 * n + 2 + 1 = 2 * n + 3 by omega, ih]
    rw [show 2 * n + 1 + 2 = 2 * n + 3 by omega] at r2
    have c1 : ((2 * n : Nat) : R) = 2 * (n : R) := by grind
    have c2 : ((2 * n + 1 : Nat) : R) = 2 * (n : R) + 1 := by grind
    rw [c1] at r1; rw [c2] at r2
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    generalize I (2 * n) = a at *
    generalize I (2 * n + 1) = b at *
    generalize I (2 * n + 2) = c at *
    generalize I (2 * n + 3) = d at *
    generalize (n : R) = N at *
    have hc : c = (2 * N + 1) * a / (2 * N + 2) := by grind
    have hd : d = (2 * N + 2) * b / (2 * N + 3) := by grind
    rw [hc, hd]
    grind

/-- **The Wallis product** (Wallis 1656). `Π_{n ≥ 1} (2n)²/((2n − 1)(2n + 1)) = π/2`: the partial
products converge to `π/2`. -/
theorem wallis : Tendsto wp (pi / 2) := by
  have hb : ∀ n : Nat, abs (wp n - hpi) ≤ hpi * (1 / ((n : R) + 1)) := fun n => by
    rw [wp_eq]
    have r := I_rec (2 * n)
    have a1 := I_anti (2 * n); have a2 := I_anti (2 * n + 1)
    have p1 := I_pos (2 * n); have p3 := I_pos (2 * n + 2)
    have c1 : ((2 * n : Nat) : R) = 2 * (n : R) := by grind
    rw [c1] at r
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega] at a2
    have hp := hpi_pos
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    generalize I (2 * n) = a at *
    generalize I (2 * n + 1) = b at *
    generalize I (2 * n + 2) = c at *
    generalize (n : R) = N at *
    -- `(2N+1)/(2N+2) · a = c ≤ b ≤ a`.
    have hrb : b / a ≤ 1 := by
      have := OrderedRing.mul_le_mul_of_nonneg_right a1 (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 p1))
      rw [Field.div_eq_mul_inv]; grind
    have hrl : 1 - 1 / (N + 1) ≤ b / a := by
      have hc : c = (2 * N + 1) / (2 * N + 2) * a := by grind
      have k : (2 * N + 1) / (2 * N + 2) ≤ b / a := by
        have k1 := OrderedRing.mul_le_mul_of_nonneg_right (show c ≤ b from a2)
          (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 p1))
        have ia := Field.mul_inv_cancel (show a ≠ 0 by grind)
        have e : c * a⁻¹ = (2 * N + 1) / (2 * N + 2) := by
          rw [hc, Semiring.mul_assoc, ia, Semiring.mul_one]
        rw [e] at k1
        rw [Field.div_eq_mul_inv b]; exact k1
      have : 1 - 1 / (N + 1) ≤ (2 * N + 1) / (2 * N + 2) := by
        have e : (2 * N + 1) / (2 * N + 2) = 1 - 1 / (2 * N + 2) := by grind
        rw [e]
        have := one_div_le_one_div (by grind : 0 < N + 1) (by grind : N + 1 ≤ 2 * N + 2)
        grind
      grind
    have e : hpi * b / a - hpi = hpi * (b / a - 1) := by grind
    rw [e, abs_mul, abs_of_nonneg (Std.le_of_lt hp)]
    apply OrderedRing.mul_le_mul_of_nonneg_left _ (Std.le_of_lt hp)
    have : 0 < 1 / (N + 1) := div_pos (by grind) (by grind)
    exact abs_le.2 ⟨by grind, by grind⟩
  intro ε hε
  obtain ⟨N, hN⟩ := eps_small (div_pos hε hpi_pos)
  refine ⟨N, fun n hn => ?_⟩
  have k := hN n hn
  have k2 := OrderedRing.mul_lt_mul_of_pos_left k hpi_pos
  have e : hpi * (ε / hpi) = ε := by have := hpi_pos; grind
  show abs (wp n - pi / 2) < ε
  have := hb n
  unfold hpi at *
  grind

end Wallis

end Foundations.Topology
