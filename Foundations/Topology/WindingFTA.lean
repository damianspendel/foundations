import Foundations.Topology.NoRetraction

/-!
# The fundamental theorem of algebra, by winding numbers

Part II proved the fundamental theorem of algebra (`C.fta`) analytically, after d'Alembert and
Argand: `|p|` attains a minimum, and at a non-root one can always go further down. Here is the
other classical proof — in substance Gauss's (1799, 1849) — now in the language of the degree.

Let `p(z) = zⁿ + aₙ₋₁zⁿ⁻¹ + ⋯ + a₀` with `n ≥ 1`, and suppose `p` has no root. Choose
`ρ = 1 + Σ |aₖ|`.

* On the circle `|z| = ρ` the leading term dominates: `|Σ aₖ zᵏ| < ρⁿ = |zⁿ|`. Hence the loops
  `t ↦ zⁿ + u · Σ aₖ zᵏ` (`z = ρ cis 2πt`, `u ∈ [0, 1]`) never pass through `0`, and after
  normalisation they deform `t ↦ cis (2πnt)`, of degree `n`, into the loop `t ↦ p(ρ cis 2πt)/|·|`.
* That loop is the boundary loop of the map `z ↦ p(ρz)/|p(ρz)|` of the disc into the circle,
  so its degree is `0` (previous file).

Thus `n = 0`, a contradiction. Topologically: a polynomial of degree `n` winds a large circle `n`
times around the origin, and a loop that winds around the origin cannot be filled in without
hitting it.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind
open Foundations.Numbers.C (cabs normSq conj cis)

/-! ## Polynomials are continuous -/

variable {A B : Type} [MetricSpace A] [MetricSpace B]

/-- Complex addition is jointly continuous. -/
theorem cont2_cadd : Cont2 (fun z w : C => z + w) :=
  (Cont2.mkC (continuous_re.cont2_left.add continuous_re.cont2_right)
    (continuous_im.cont2_left.add continuous_im.cont2_right)).congr fun _ _ => C.ext rfl rfl

/-- Sums of jointly continuous complex functions. -/
theorem Cont2.cadd {F G : A → B → C} (hF : Cont2 F) (hG : Cont2 G) :
    Cont2 (fun a b => F a b + G a b) := cont2_cadd.comp2 hF hG

/-- Products of continuous complex functions. -/
theorem Continuous.cmul' {f g : A → C} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => f a * g a) := ((hf.cont2_left (B := R)).cmul hg.cont2_left).slice' 0

/-- Sums of continuous complex functions. -/
theorem Continuous.cadd' {f g : A → C} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => f a + g a) := ((hf.cont2_left (B := R)).cadd hg.cont2_left).slice' 0

/-- Powers `z ↦ zᵏ` are continuous. -/
theorem continuous_pow_C (k : Nat) : Continuous (fun z : C => z ^ k) := by
  induction k with
  | zero => exact (continuous_constant (1 : C)).congr fun _ => rfl
  | succ k ih => exact (ih.cmul' continuous_id_C).congr fun _ => rfl
where
  /-- The identity of `ℂ` is continuous. -/
  continuous_id_C : Continuous (fun z : C => z) := fun _ ε hε => ⟨ε, hε, fun _ h => h⟩

/-- The lower part `Σ_{k<n} aₖ zᵏ` of a polynomial. -/
noncomputable def lowerPart (a : Nat → C) (n : Nat) (z : C) : C := gsum (fun k => a k * z ^ k) n

/-- The lower part of a polynomial is continuous. -/
theorem continuous_lowerPart (a : Nat → C) (n : Nat) : Continuous (lowerPart a n) := by
  induction n with
  | zero => exact (continuous_constant (0 : C)).congr fun _ => rfl
  | succ n ih =>
    exact (ih.cadd' ((continuous_constant (a n)).cmul' (continuous_pow_C n))).congr fun _ => rfl

/-! ## The leading term dominates on a large circle -/

/-- The triangle inequality for finite sums. -/
theorem cabs_gsum_le (f : Nat → C) (n : Nat) : cabs (gsum f n) ≤ fsum (fun k => cabs (f k)) n := by
  induction n with
  | zero => show cabs 0 ≤ 0; rw [C.cabs_zero]; exact Std.le_refl 0
  | succ n ih =>
    show cabs (gsum f n + f n) ≤ fsum (fun k => cabs (f k)) n + cabs (f n)
    have := C.cabs_add (gsum f n) (f n); grind

/-- Finite sums are monotone. -/
theorem fsum_le_fsum {f g : Nat → R} {n : Nat} (h : ∀ k, k < n → f k ≤ g k) :
    fsum f n ≤ fsum g n := by
  induction n with
  | zero => exact Std.le_refl _
  | succ n ih =>
    show fsum f n + f n ≤ fsum g n + g n
    have := ih fun k hk => h k (by omega); have := h n (by omega); grind

/-- A finite sum of non-negative terms is non-negative. -/
theorem fsum_nonneg {f : Nat → R} {n : Nat} (h : ∀ k, k < n → 0 ≤ f k) : 0 ≤ fsum f n := by
  have := fsum_le_fsum (f := fun _ => 0) (g := f) (n := n) h
  rwa [fsum_eq_zero fun _ _ => rfl] at this

/-- A constant factor comes out of a finite sum. -/
theorem fsum_mul_const (f : Nat → R) (c : R) (n : Nat) :
    fsum (fun k => f k * c) n = fsum f n * c := by
  induction n with
  | zero => show (0 : R) = 0 * c; grind
  | succ n ih => show fsum (fun k => f k * c) n + f n * c = (fsum f n + f n) * c; rw [ih]; grind

/-- Powers of a number `≥ 1` increase. -/
theorem pow_mono {ρ : R} (h : 1 ≤ ρ) (k d : Nat) : ρ ^ k ≤ ρ ^ (k + d) := by
  induction d with
  | zero => exact Std.le_refl _
  | succ d ih =>
    show ρ ^ k ≤ ρ ^ (k + d) * ρ
    have := one_le_pow h (k + d)
    have := OrderedRing.mul_le_mul_of_nonneg_left h (show 0 ≤ ρ ^ (k + d) by grind)
    grind

/-- **The leading term dominates.** On the circle `|z| = 1 + Σ |aₖ|`, the lower part of a
polynomial of degree `n ≥ 1` is smaller than `|zⁿ|`. -/
theorem cabs_lowerPart_lt {a : Nat → C} {n : Nat} (hn : 1 ≤ n) {z : C}
    (hz : cabs z = 1 + fsum (fun k => cabs (a k)) n) : cabs (lowerPart a n z) < cabs z ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hS := fsum_nonneg (f := fun k => cabs (a k)) (n := m + 1) fun k _ => C.cabs_nonneg _
  have hρ : 1 ≤ cabs z := by grind
  have k1 := cabs_gsum_le (fun k => a k * z ^ k) (m + 1)
  have k2 : fsum (fun k => cabs (a k * z ^ k)) (m + 1) ≤
      fsum (fun k => cabs (a k) * cabs z ^ m) (m + 1) := fsum_le_fsum fun k hk => by
    rw [C.cabs_mul, C.cabs_pow]
    have := pow_mono hρ k (m - k); rw [show k + (m - k) = m by omega] at this
    exact OrderedRing.mul_le_mul_of_nonneg_left this (C.cabs_nonneg _)
  rw [fsum_mul_const] at k2
  have k3 := OrderedRing.mul_lt_mul_of_pos_right (show fsum (fun k => cabs (a k)) (m + 1) < cabs z
    by grind) (show 0 < cabs z ^ m by have := one_le_pow hρ m; grind)
  have e : cabs z ^ (m + 1) = cabs z ^ m * cabs z := rfl
  unfold lowerPart; grind

/-- Normalising a positive multiple of a point of the circle gives the point back. -/
theorem nrm_pos_mul {r : R} (hr : 0 < r) {u : C} (hu : normSq u = 1) : nrm (C.ofReal r * u) = u := by
  unfold nrm
  rw [C.cabs_mul, C.cabs_ofReal (Std.le_of_lt hr), (cabs_eq_one_iff u).2 hu]
  apply C.ext <;> simp only [C.mul_re, C.mul_im] <;> unfold C.ofReal <;> simp only <;> grind

/-- **The loop `t ↦ cis (2πnt)` has degree `n`** (for natural `n`). -/
theorem degree_cis_mul (n : Nat) : degree (fun t => C.cis ((n : R) * (2 * pi * t))) = (n : Int) := by
  have ec : ((n : Int) : R) = (n : R) := Lean.Grind.Ring.intCast_natCast n
  have hc : Continuous (fun t : R => (n : R) * (2 * pi * t)) :=
    (continuous_affine ((n : R) * (2 * pi)) 0).congr fun t => by grind
  refine degree_eq ⟨continuous_cis.comp hc, fun t _ _ => normSq_cis _, ?_⟩ ⟨hc, fun _ _ _ => rfl⟩
    (by grind)
  show C.cis ((n : R) * (2 * pi * 1)) = C.cis ((n : R) * (2 * pi * 0))
  rw [show (n : R) * (2 * pi * 1) = 2 * pi * ((n : Int) : R) by grind, cis_two_pi_int,
    show (n : R) * (2 * pi * 0) = 0 by grind, cis_zero]

/-! ## The fundamental theorem of algebra -/

/-- **Fundamental theorem of algebra, via winding numbers.** Every monic complex polynomial
`zⁿ + aₙ₋₁zⁿ⁻¹ + ⋯ + a₀` of degree `n ≥ 1` has a root. (Compare the analytic proof `C.fta` of
Part II.) -/
theorem fta_winding {n : Nat} (hn : 1 ≤ n) (a : Nat → C) :
    ∃ z, z ^ n + lowerPart a n z = 0 := by
  apply Classical.byContradiction; intro hno
  have hP : ∀ z, z ^ n + lowerPart a n z ≠ 0 := fun z h => hno ⟨z, h⟩
  let ρ : R := 1 + fsum (fun k => cabs (a k)) n
  have hS := fsum_nonneg (f := fun k => cabs (a k)) (n := n) fun k _ => C.cabs_nonneg _
  have hρ : 0 < ρ := by grind
  have hPc : Continuous (fun z : C => z ^ n + lowerPart a n z) :=
    (continuous_pow_C n).cadd' (continuous_lowerPart a n)
  have hscale : Continuous (fun z : Disc => C.ofReal ρ * z.1) :=
    (continuous_constant _).cmul' (continuous_val _)
  -- The boundary loop of `z ↦ p(ρz)/|p(ρz)|` has degree `0` …
  have h0 := degree_boundary_eq_zero
    (G := fun z => nrm ((C.ofReal ρ * z.1) ^ n + lowerPart a n (C.ofReal ρ * z.1)))
    ((hPc.comp hscale).comp_at fun z => continuousAt_nrm (hP _)) (fun z => normSq_nrm (hP _))
  -- … but it is homotopic to `t ↦ cis (2πnt)`, of degree `n`.
  have hw : ∀ t, cabs (C.ofReal ρ * (bd t).1) = ρ := fun t => by
    show cabs (C.ofReal ρ * C.cis (2 * pi * t)) = ρ
    rw [C.cabs_mul, C.cabs_ofReal (Std.le_of_lt hρ), cabs_cis]; grind
  have knz : ∀ u t, (C.ofReal ρ * (bd t).1) ^ n +
      C.ofReal (clamp01 u) * lowerPart a n (C.ofReal ρ * (bd t).1) ≠ 0 := fun u t h => by
    have mu := clamp01_mem u
    have lt := cabs_lowerPart_lt (a := a) hn (hw t)
    have e1 : (C.ofReal ρ * (bd t).1) ^ n =
        -(C.ofReal (clamp01 u) * lowerPart a n (C.ofReal ρ * (bd t).1)) := by grind
    have e2 := congrArg cabs e1
    rw [C.cabs_pow, hw t, C.cabs_neg, C.cabs_mul, C.cabs_ofReal mu.1] at e2
    rw [hw t] at lt
    have := OrderedRing.mul_le_mul_of_nonneg_right mu.2
      (C.cabs_nonneg (lowerPart a n (C.ofReal ρ * (bd t).1)))
    grind
  have hwc : Continuous (fun t => C.ofReal ρ * (bd t).1) :=
    (continuous_constant _).cmul' ((continuous_val _).comp continuous_bd)
  have hin : Cont2 (fun u t => (C.ofReal ρ * (bd t).1) ^ n +
      C.ofReal (clamp01 u) * lowerPart a n (C.ofReal ρ * (bd t).1)) :=
    ((continuous_pow_C n).comp hwc).cont2_right.cadd
      ((continuous_ofReal.comp continuous_clamp01).cont2_left.cmul
        ((continuous_lowerPart a n).comp hwc).cont2_right)
  have hK := hin.comp_left' fun u t => continuousAt_nrm (knz u t)
  have key := degree_homotopy hK (fun u t _ _ _ _ => normSq_nrm (knz u t))
    (fun u _ _ => by (try simp only); rw [bd_one])
  have k0 : (fun t => nrm ((C.ofReal ρ * (bd t).1) ^ n +
      C.ofReal (clamp01 0) * lowerPart a n (C.ofReal ρ * (bd t).1))) =
      fun t => C.cis ((n : R) * (2 * pi * t)) := funext fun t => by
    rw [clamp01_of_mem (Std.le_refl 0) (by grind)]
    rw [show ∀ x y : C, x + C.ofReal 0 * y = x from fun x y => by
      apply C.ext <;> simp only [C.add_re, C.add_im, C.mul_re, C.mul_im] <;> unfold C.ofReal <;>
        simp only <;> grind]
    show nrm ((C.ofReal ρ * C.cis (2 * pi * t)) ^ n) = _
    rw [C.mul_pow, C.ofReal_pow, C.cis_pow]
    exact nrm_pos_mul (by have := one_le_pow (show 1 ≤ ρ by grind) n; grind) (normSq_cis _)
  have k1 : (fun t => nrm ((C.ofReal ρ * (bd t).1) ^ n +
      C.ofReal (clamp01 1) * lowerPart a n (C.ofReal ρ * (bd t).1))) =
      fun t => nrm ((C.ofReal ρ * (bd t).1) ^ n + lowerPart a n (C.ofReal ρ * (bd t).1)) :=
    funext fun t => by
      rw [clamp01_of_mem (by grind) (Std.le_refl 1)]
      congr 2; apply C.ext <;> simp only [C.mul_re, C.mul_im] <;> unfold C.ofReal <;> simp only <;>
        grind
  (try simp only at key h0)
  rw [k0, k1, degree_cis_mul, h0] at key
  omega

end Foundations.Topology
