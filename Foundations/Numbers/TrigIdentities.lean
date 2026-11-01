import Foundations.Numbers.Trig

/-!
# Analysis on the reals X: trigonometric identities and periodicity

With sine and cosine defined by power series and `π` as twice the first positive zero of cosine,
the familiar trigonometry has to be *proved*. The tool is the same "derivative-zero trick" that
gave the functional equation of `exp`: for fixed `y`, the function

  `t ↦ (sin (t + y) − sin t cos y − cos t sin y)² + (cos (t + y) − cos t cos y + sin t sin y)²`

has derivative `0` and vanishes at `t = 0`, so it vanishes identically — and a sum of two
squares vanishes only if both do. This gives the **addition formulas**. Putting `y = π/2` (where
`cos = 0`, `sin = 1`) gives `sin (x + π/2) = cos x` and `cos (x + π/2) = −sin x`; iterating,
`sin` and `cos` are **periodic with period `2π`**, `sin π = 0` and `cos π = −1`.

Finally we locate **all zeros**: `sin x = 0` exactly when `x` is an integer multiple of `π`, and
`cos x = 0` exactly when `x = π/2 + kπ`. The key is that `sin` is positive on `(0, π)`; any real
number can be moved into `[0, π)` by subtracting an integer multiple of `π` (integer parts exist
because ℝ is Archimedean).
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-- A sum of two squares vanishes only if both terms vanish. -/
theorem eq_zero_of_sq_add_sq {a b : R} (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by
  have ha := OrderedRing.sq_nonneg (a := a)
  have hb := OrderedRing.sq_nonneg (a := b)
  constructor
  · apply Classical.byContradiction; intro hne
    have := OrderedRing.sq_pos (a := a) hne; grind
  · apply Classical.byContradiction; intro hne
    have := OrderedRing.sq_pos (a := b) hne; grind

/-- Derivative of `t ↦ t + y`. -/
theorem hasDerivAt_add_const (y t : R) : HasDerivAt (fun t => t + y) (1 + 0) t :=
  (hasDerivAt_id t).add (hasDerivAt_const y t)

/-! ## The addition formulas -/

/-- **Addition formulas** for sine and cosine, proved together. -/
theorem sin_cos_add (x y : R) :
    sin (x + y) = sin x * cos y + cos x * sin y ∧ cos (x + y) = cos x * cos y - sin x * sin y := by
  -- `A t` and `B t` are the two errors; `(A² + B²)' = 2AB + 2B(−A) = 0`.
  have hA := fun t => ((hasDerivAt_sin (t + y)).comp (f := fun t => t + y)
      (hasDerivAt_add_const y t)).sub
    (((hasDerivAt_sin t).mul (hasDerivAt_const (cos y) t)).add
      ((hasDerivAt_cos t).mul (hasDerivAt_const (sin y) t)))
  have hB := fun t => (((hasDerivAt_cos (t + y)).comp (f := fun t => t + y)
      (hasDerivAt_add_const y t)).sub
    ((hasDerivAt_cos t).mul (hasDerivAt_const (cos y) t))).add
      ((hasDerivAt_sin t).mul (hasDerivAt_const (sin y) t))
  have hF := fun t => ((hA t).mul (hA t)).add ((hB t).mul (hB t))
  have := const_of_deriv_zero' hF (fun t => by grind) x 0
  rw [sin_zero, cos_zero, show (0 : R) + y = y by grind] at this
  have h := eq_zero_of_sq_add_sq (a := sin (x + y) - (sin x * cos y + cos x * sin y))
    (b := cos (x + y) - cos x * cos y + sin x * sin y) (by grind)
  exact ⟨by grind, by grind⟩

/-- **Addition formula for sine.** `sin (x + y) = sin x cos y + cos x sin y`. -/
theorem sin_add (x y : R) : sin (x + y) = sin x * cos y + cos x * sin y := (sin_cos_add x y).1

/-- **Addition formula for cosine.** `cos (x + y) = cos x cos y − sin x sin y`. -/
theorem cos_add (x y : R) : cos (x + y) = cos x * cos y - sin x * sin y := (sin_cos_add x y).2

/-! ## Periodicity -/

/-- `sin (x + π/2) = cos x`. -/
theorem sin_add_pi_div_two (x : R) : sin (x + pi / 2) = cos x := by
  rw [sin_add, cos_pi_div_two, sin_pi_div_two]; grind

/-- `cos (x + π/2) = −sin x`. -/
theorem cos_add_pi_div_two (x : R) : cos (x + pi / 2) = -sin x := by
  rw [cos_add, cos_pi_div_two, sin_pi_div_two]; grind

/-- `sin (x + π) = −sin x`. -/
theorem sin_add_pi (x : R) : sin (x + pi) = -sin x := by
  rw [show x + pi = x + pi / 2 + pi / 2 by grind, sin_add_pi_div_two, cos_add_pi_div_two]

/-- `cos (x + π) = −cos x`. -/
theorem cos_add_pi (x : R) : cos (x + pi) = -cos x := by
  rw [show x + pi = x + pi / 2 + pi / 2 by grind, cos_add_pi_div_two, sin_add_pi_div_two]

/-- **Sine has period `2π`.** -/
theorem sin_add_two_pi (x : R) : sin (x + 2 * pi) = sin x := by
  rw [show x + 2 * pi = x + pi + pi by grind, sin_add_pi, sin_add_pi]; grind

/-- **Cosine has period `2π`.** -/
theorem cos_add_two_pi (x : R) : cos (x + 2 * pi) = cos x := by
  rw [show x + 2 * pi = x + pi + pi by grind, cos_add_pi, cos_add_pi]; grind

/-- **`sin π = 0`.** -/
theorem sin_pi : sin pi = 0 := by
  have := sin_add_pi 0; rw [sin_zero, show (0 : R) + pi = pi by grind] at this; grind

/-- **`cos π = −1`.** -/
theorem cos_pi : cos pi = -1 := by
  have := cos_add_pi 0; rw [cos_zero, show (0 : R) + pi = pi by grind] at this; exact this

/-- `sin (2π) = 0`. -/
theorem sin_two_pi : sin (2 * pi) = 0 := by
  have := sin_add_two_pi 0; rw [sin_zero, show (0 : R) + 2 * pi = 2 * pi by grind] at this
  exact this

/-- `cos (2π) = 1`. -/
theorem cos_two_pi : cos (2 * pi) = 1 := by
  have := cos_add_two_pi 0; rw [cos_zero, show (0 : R) + 2 * pi = 2 * pi by grind] at this
  exact this

/-! ## The zeros of sine and cosine -/

/-- `π > 0`. -/
theorem pi_pos : 0 < pi := pi_pos_le_four.1

/-- **Sine is positive on `(0, π)`.** -/
theorem sin_pos_of_pos_of_lt_pi {x : R} (h0 : 0 < x) (hx : x < pi) : 0 < sin x := by
  obtain ⟨-, -, hcos, hpos⟩ := pi_div_two_spec
  have hnn : ∀ t, 0 ≤ t → t ≤ pi / 2 → 0 ≤ cos t := fun t h1 h2 => by
    rcases (by grind : t < pi / 2 ∨ t = pi / 2) with h | h
    · exact Std.le_of_lt (hpos t h1 h)
    · rw [h, hcos]; grind
  rcases (by grind : x ≤ pi / 2 ∨ pi / 2 < x) with h | h
  · have k1 : sin 0 < sin (x / 2) := strictMono_of_deriv_pos (a := 0) (b := x / 2)
      (fun t _ _ => hasDerivAt_sin t) (fun t h1 h2 => hpos t h1 (by grind))
      (Std.le_refl 0) (by grind) (Std.le_refl _)
    have k2 : sin (x / 2) ≤ sin x := monotone_of_deriv_nonneg (a := x / 2) (b := x)
      (fun t _ _ => hasDerivAt_sin t) (fun t h1 h2 => hnn t (by grind) (by grind))
      (Std.le_refl _) (by grind) (Std.le_refl _)
    rw [sin_zero] at k1; grind
  · rw [show x = (x - pi / 2) + pi / 2 by grind, sin_add_pi_div_two]
    exact hpos _ (by grind) (by grind)

/-- Shifting by an integer multiple of `π` preserves the zeros of sine. -/
theorem sin_add_int_mul_pi_eq_zero (x : R) (k : Int) : sin (x + (k : R) * pi) = 0 ↔ sin x = 0 := by
  have hnat : ∀ n : Nat, ∀ x : R, sin (x + (n : R) * pi) = 0 ↔ sin x = 0 := by
    intro n
    induction n with
    | zero => intro x; rw [show x + ((0 : Nat) : R) * pi = x by grind]
    | succ n ih =>
      intro x
      rw [show x + ((n + 1 : Nat) : R) * pi = x + (n : R) * pi + pi by grind, sin_add_pi, ← ih x]
      constructor <;> intro h <;> grind
  cases k with
  | ofNat n =>
    have : ((Int.ofNat n : Int) : R) = (n : R) := Ring.intCast_natCast n
    rw [this]; exact hnat n x
  | negSucc n =>
    have e : ((Int.negSucc n : Int) : R) = -((n + 1 : Nat) : R) := by
      rw [Int.negSucc_eq, Ring.intCast_neg]
      have : (((n : Int) + 1 : Int) : R) = (((n + 1 : Nat) : Int) : R) := rfl
      rw [this, Ring.intCast_natCast]
    rw [e]
    have := hnat (n + 1) (x + -((n + 1 : Nat) : R) * pi)
    rw [show x + -((n + 1 : Nat) : R) * pi + ((n + 1 : Nat) : R) * pi = x by grind] at this
    exact this.symm

/-- Every real number is an integer multiple of `π` plus a remainder in `[0, π)`. -/
theorem exists_int_mul_pi (x : R) : ∃ m : Int, (m : R) * pi ≤ x ∧ x < (m : R) * pi + pi := by
  obtain ⟨m, hm1, hm2⟩ := exists_floor (K := R) archimedean (x / pi)
  have hp := pi_pos
  have e : x / pi * pi = x := by grind
  refine ⟨m, ?_, ?_⟩
  · have := OrderedRing.mul_le_mul_of_nonneg_right hm1 (Std.le_of_lt hp); grind
  · have := OrderedRing.mul_lt_mul_of_pos_right hm2 hp; grind

/-- **Zeros of sine.** `sin x = 0` if and only if `x = kπ` for an integer `k`. -/
theorem sin_eq_zero_iff (x : R) : sin x = 0 ↔ ∃ k : Int, x = (k : R) * pi := by
  constructor
  · intro h
    obtain ⟨m, hm1, hm2⟩ := exists_int_mul_pi x
    have hy : sin (x - (m : R) * pi) = 0 := by
      rw [← sin_add_int_mul_pi_eq_zero _ m, show x - (m : R) * pi + (m : R) * pi = x by grind]
      exact h
    refine ⟨m, ?_⟩
    apply Classical.byContradiction; intro hne
    have := sin_pos_of_pos_of_lt_pi (x := x - (m : R) * pi) (by grind) (by grind)
    grind
  · rintro ⟨k, rfl⟩
    have := (sin_add_int_mul_pi_eq_zero 0 k).2 sin_zero
    rw [show (0 : R) + (k : R) * pi = (k : R) * pi by grind] at this
    exact this

/-- **Zeros of cosine.** `cos x = 0` if and only if `x = π/2 + kπ` for an integer `k`. -/
theorem cos_eq_zero_iff (x : R) : cos x = 0 ↔ ∃ k : Int, x = pi / 2 + (k : R) * pi := by
  rw [← sin_add_pi_div_two, sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    have : ((k - 1 : Int) : R) = (k : R) - 1 := by grind
    rw [this]; grind
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    have : ((k + 1 : Int) : R) = (k : R) + 1 := by grind
    rw [this]; grind

end R

end Foundations.Numbers
