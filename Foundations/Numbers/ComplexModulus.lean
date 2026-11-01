import Foundations.Numbers.ComplexExp

/-!
# The modulus of a complex number, polar form, and `k`-th roots

This file prepares the fundamental theorem of algebra. We need to measure the size of a complex
number and to extract roots of complex numbers.

* The **square root** of a non-negative real (from the existence of `n`-th roots, i.e. from
  completeness), and the **modulus** `|z| = √(a² + b²)` of `z = a + bi`. It is multiplicative,
  `|z w| = |z| |w|` (Brahmagupta–Fibonacci), and satisfies the **triangle inequality**
  `|z + w| ≤ |z| + |w|` — whose proof is the Cauchy–Schwarz inequality in the plane,
  `(ac + bd)² ≤ (a² + b²)(c² + d²)`.
* The **parity** of sine and cosine, and **arguments**: every point `(x, y)` of the unit circle is
  `(cos θ, sin θ)` for some `θ` (intermediate value theorem for cosine on `[0, π]`).
* **De Moivre's formula** `(cos θ + i sin θ)ᵏ = cos kθ + i sin kθ`, so every non-zero complex number
  has **polar form** `u = r (cos θ + i sin θ)`, and hence **`k`-th roots**:
  `r^{1/k} (cos (θ/k) + i sin (θ/k))`.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-! ## Square roots -/

/-- For `0 ≤ r < s`, `r² < s²`. -/
theorem mul_self_lt_mul_self {r s : R} (hr : 0 ≤ r) (h : r < s) : r * r < s * s := by
  have h1 := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt h) hr
  have h2 := OrderedRing.mul_lt_mul_of_pos_right h (by grind : 0 < s)
  grind

/-- For `s ≥ 0`, `r² ≤ s²` implies `r ≤ s`. -/
theorem le_of_mul_self_le {r s : R} (hs : 0 ≤ s) (h : r * r ≤ s * s) : r ≤ s := by
  apply Classical.byContradiction; intro hlt
  have := mul_self_lt_mul_self hs (by grind : s < r); grind

/-- Non-negative numbers with equal squares are equal. -/
theorem eq_of_mul_self_eq {r s : R} (hr : 0 ≤ r) (hs : 0 ≤ s) (h : r * r = s * s) : r = s := by
  have := le_of_mul_self_le hs (by grind : r * r ≤ s * s)
  have := le_of_mul_self_le hr (by grind : s * s ≤ r * r)
  grind

/-- **The square root** `√x` of `x ≥ 0` (and `0` for `x < 0`, a value of no significance). -/
noncomputable def sqrt (x : R) : R :=
  open Classical in if h : 0 ≤ x then Classical.choose (exists_nth_root h (n := 2) (by omega)) else 0

/-- `√x ≥ 0` and `√x · √x = x` for `x ≥ 0`. -/
theorem sqrt_spec {x : R} (hx : 0 ≤ x) : 0 ≤ sqrt x ∧ sqrt x * sqrt x = x := by
  unfold sqrt
  rw [dite_eq_left_of_eq_true (eq_true hx)]
  have h := Classical.choose_spec (exists_nth_root hx (n := 2) (by omega))
  exact ⟨h.1, by have := h.2; grind⟩

/-- `√x ≥ 0`. -/
theorem sqrt_nonneg (x : R) : 0 ≤ sqrt x := by
  by_cases hx : 0 ≤ x
  · exact (sqrt_spec hx).1
  · unfold sqrt; rw [dite_eq_right_of_eq_false (eq_false hx)]; grind

/-- The square root is the unique non-negative number with the given square. -/
theorem sqrt_eq {x r : R} (hr : 0 ≤ r) (h : r * r = x) : sqrt x = r := by
  have hx : 0 ≤ x := by rw [← h]; exact C.mul_self_nonneg r
  exact eq_of_mul_self_eq (sqrt_spec hx).1 hr (by rw [(sqrt_spec hx).2, h])

/-! ## Parity of sine and cosine -/

/-- **Cosine is even, sine is odd**: `cos (−x) = cos x`, `sin (−x) = −sin x`. -/
theorem cos_neg_sin_neg (x : R) : cos (-x) = cos x ∧ sin (-x) = -sin x := by
  have h1 := sin_add x (-x)
  have h2 := cos_add x (-x)
  rw [show x + -x = 0 by grind, sin_zero] at h1
  rw [show x + -x = 0 by grind, cos_zero] at h2
  have h3 := sin_sq_add_cos_sq x
  -- Solve the linear system `sin x · c + cos x · s = 0`, `cos x · c − sin x · s = 1`.
  generalize cos (-x) = c at h1 h2 ⊢
  generalize sin (-x) = s at h1 h2 ⊢
  constructor
  · have : c = c * (sin x * sin x + cos x * cos x) := by rw [h3]; grind
    grind
  · have : s = s * (sin x * sin x + cos x * cos x) := by rw [h3]; grind
    grind

/-- `cos (−x) = cos x`. -/
theorem cos_neg (x : R) : cos (-x) = cos x := (cos_neg_sin_neg x).1

/-- `sin (−x) = −sin x`. -/
theorem sin_neg (x : R) : sin (-x) = -sin x := (cos_neg_sin_neg x).2

/-- Sine is non-negative on `[0, π]`. -/
theorem sin_nonneg_of_mem {θ : R} (h0 : 0 ≤ θ) (h1 : θ ≤ pi) : 0 ≤ sin θ := by
  rcases (by grind : θ = 0 ∨ θ = pi ∨ (0 < θ ∧ θ < pi)) with e | e | ⟨e1, e2⟩
  · rw [e, sin_zero]; grind
  · rw [e, sin_pi]; grind
  · exact Std.le_of_lt (sin_pos_of_pos_of_lt_pi e1 e2)

/-- `|x| ≤ 1` when `x² ≤ 1`. -/
theorem abs_le_one_of_sq {x : R} (h : x * x ≤ 1) : -1 ≤ x ∧ x ≤ 1 := by
  constructor
  · apply Classical.byContradiction; intro hlt
    have := mul_self_lt_mul_self (by grind : (0 : R) ≤ 1) (by grind : 1 < -x); grind
  · apply Classical.byContradiction; intro hlt
    have := mul_self_lt_mul_self (by grind : (0 : R) ≤ 1) (by grind : 1 < x); grind

/-- **Arguments.** Every point `(x, y)` with `x² + y² = 1` is `(cos θ, sin θ)` for some `θ`. -/
theorem exists_angle {x y : R} (h : x * x + y * y = 1) : ∃ θ, cos θ = x ∧ sin θ = y := by
  have hy2 := C.mul_self_nonneg y
  obtain ⟨hx1, hx2⟩ := abs_le_one_of_sq (x := x) (by grind)
  have hπ := pi_pos
  -- Cosine runs from `1` down to `−1` on `[0, π]`.
  obtain ⟨θ, h0, h1, hθ⟩ := intermediate_value' (f := fun t => 0 - cos t) (a := 0) (b := pi)
    (v := -x) (Std.le_of_lt hπ)
    (fun t _ _ => continuousAt_sub (continuousAt_const 0 t) (continuousAt_cos t))
    (by show 0 - cos 0 ≤ -x; rw [cos_zero]; grind)
    (by show -x ≤ 0 - cos pi; rw [cos_pi]; grind)
  have hc : cos θ = x := by have : 0 - cos θ = -x := hθ; grind
  have hs := sin_nonneg_of_mem h0 h1
  have hss : sin θ * sin θ = y * y := by have := sin_sq_add_cos_sq θ; rw [hc] at this; grind
  rcases (by grind : 0 ≤ y ∨ y < 0) with hy | hy
  · exact ⟨θ, hc, eq_of_mul_self_eq hs hy hss⟩
  · refine ⟨-θ, by rw [cos_neg, hc], ?_⟩
    rw [sin_neg, eq_of_mul_self_eq hs (by grind : 0 ≤ -y) (by grind)]; grind

end R

namespace C

open R

/-! ## The modulus -/

/-- `|z|² ≥ 0`. -/
theorem normSq_nonneg (z : C) : 0 ≤ normSq z := by
  have := mul_self_nonneg z.re; have := mul_self_nonneg z.im; unfold normSq; grind

/-- **The modulus** `|z| = √(a² + b²)` of `z = a + bi`. -/
noncomputable def cabs (z : C) : R := sqrt (normSq z)

/-- `|z| ≥ 0`. -/
theorem cabs_nonneg (z : C) : 0 ≤ cabs z := sqrt_nonneg _

/-- `|z|² = a² + b²`. -/
theorem cabs_mul_self (z : C) : cabs z * cabs z = normSq z := (sqrt_spec (normSq_nonneg z)).2

/-- `|z| = 0` only for `z = 0`. -/
theorem eq_zero_of_cabs {z : C} (h : cabs z = 0) : z = 0 := by
  apply normSq_eq_zero; rw [← cabs_mul_self, h]; grind

/-- `|z| > 0` for `z ≠ 0`. -/
theorem cabs_pos {z : C} (h : z ≠ 0) : 0 < cabs z := by
  rcases (by have := cabs_nonneg z; grind : cabs z = 0 ∨ 0 < cabs z) with e | e
  · exact absurd (eq_zero_of_cabs e) h
  · exact e

/-- `|0| = 0`. -/
theorem cabs_zero : cabs 0 = 0 := sqrt_eq (Std.le_refl 0) (by show (0 : R) * 0 = 0 * 0 + 0 * 0; grind)

/-- **The modulus is multiplicative.** `|z w| = |z| |w|`. -/
theorem cabs_mul (z w : C) : cabs (z * w) = cabs z * cabs w := by
  apply sqrt_eq (OrderedRing.mul_nonneg (cabs_nonneg z) (cabs_nonneg w))
  rw [normSq_mul, ← cabs_mul_self z, ← cabs_mul_self w]; grind

/-- `|x| = x` for a real `x ≥ 0`. -/
theorem cabs_ofReal {x : R} (hx : 0 ≤ x) : cabs (ofReal x) = x :=
  sqrt_eq hx (by show x * x = x * x + 0 * 0; grind)

/-- `|re z| ≤ |z|`. -/
theorem abs_re_le_cabs (z : C) : abs z.re ≤ cabs z := by
  apply le_of_mul_self_le (cabs_nonneg z)
  rw [cabs_mul_self, ← abs_mul]; unfold normSq
  have := mul_self_nonneg z.im
  rw [abs_of_nonneg (mul_self_nonneg z.re)]; grind

/-- `|im z| ≤ |z|`. -/
theorem abs_im_le_cabs (z : C) : abs z.im ≤ cabs z := by
  apply le_of_mul_self_le (cabs_nonneg z)
  rw [cabs_mul_self, ← abs_mul]; unfold normSq
  have := mul_self_nonneg z.re
  rw [abs_of_nonneg (mul_self_nonneg z.im)]; grind

/-- `|z| ≤ |re z| + |im z|`. -/
theorem cabs_le_nrm (z : C) : cabs z ≤ nrm z := by
  apply le_of_mul_self_le (nrm_nonneg z)
  rw [cabs_mul_self]; unfold normSq nrm
  have := OrderedRing.mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)
  have e1 : abs z.re * abs z.re = z.re * z.re := by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
  have e2 : abs z.im * abs z.im = z.im * z.im := by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
  grind

/-- **Triangle inequality** for the modulus: `|z + w| ≤ |z| + |w|`. -/
theorem cabs_add (z w : C) : cabs (z + w) ≤ cabs z + cabs w := by
  apply le_of_mul_self_le (by have := cabs_nonneg z; have := cabs_nonneg w; grind)
  have hz := cabs_mul_self z
  have hw := cabs_mul_self w
  -- Cauchy–Schwarz: `ac + bd ≤ |z| |w|`.
  have hcs : z.re * w.re + z.im * w.im ≤ cabs z * cabs w := by
    apply le_of_mul_self_le (OrderedRing.mul_nonneg (cabs_nonneg z) (cabs_nonneg w))
    have : cabs z * cabs w * (cabs z * cabs w) = normSq z * normSq w := by rw [← hz, ← hw]; grind
    rw [this]; unfold normSq
    have := mul_self_nonneg (z.re * w.im - z.im * w.re)
    grind
  rw [cabs_mul_self]
  unfold normSq at hz hw ⊢
  simp only [add_re, add_im]
  grind

/-- `|−z| = |z|`. -/
theorem cabs_neg (z : C) : cabs (-z) = cabs z := by
  unfold cabs normSq; rw [neg_re, neg_im]; congr 1; grind

/-- `|z − w| = |w − z|`. -/
theorem cabs_sub_comm (z w : C) : cabs (z - w) = cabs (w - z) := by
  rw [show z - w = -(w - z) by grind, cabs_neg]

/-- Reverse triangle inequality: `|z| − |w| ≤ |z − w|`. -/
theorem cabs_sub_le (z w : C) : cabs z - cabs w ≤ cabs (z - w) := by
  have := cabs_add (z - w) w
  rw [show z - w + w = z by grind] at this; grind

/-- `|zᵏ| = |z|ᵏ`. -/
theorem cabs_pow (z : C) (k : Nat) : cabs (z ^ k) = cabs z ^ k := by
  induction k with
  | zero => show cabs 1 = 1; exact cabs_ofReal (x := 1) (by grind)
  | succ k ih => show cabs (z ^ k * z) = cabs z ^ k * cabs z; rw [cabs_mul, ih]

/-- `(z w)ᵏ = zᵏ wᵏ`. -/
theorem mul_pow (z w : C) (k : Nat) : (z * w) ^ k = z ^ k * w ^ k := by
  induction k with
  | zero => show (1 : C) = 1 * 1; grind
  | succ k ih => show (z * w) ^ k * (z * w) = z ^ k * z * (w ^ k * w); rw [ih]; grind

/-! ## Polar form and `k`-th roots -/

/-- The point `cos θ + i sin θ` of the unit circle. -/
noncomputable def cis (θ : R) : C := ⟨cos θ, sin θ⟩

/-- `cis a · cis b = cis (a + b)` (the addition formulas). -/
theorem cis_add (a b : R) : cis a * cis b = cis (a + b) := by
  apply ext
  · show cos a * cos b - sin a * sin b = cos (a + b); rw [cos_add]
  · show cos a * sin b + sin a * cos b = sin (a + b); rw [sin_add]; grind

/-- **De Moivre's formula.** `(cos θ + i sin θ)ᵏ = cos kθ + i sin kθ`. -/
theorem cis_pow (θ : R) (k : Nat) : cis θ ^ k = cis ((k : R) * θ) := by
  induction k with
  | zero =>
    show (1 : C) = cis (((0 : Nat) : R) * θ)
    rw [show ((0 : Nat) : R) * θ = 0 by grind]
    apply ext
    · show (1 : R) = cos 0; rw [cos_zero]
    · show (0 : R) = sin 0; rw [sin_zero]
  | succ k ih =>
    show cis θ ^ k * cis θ = _
    rw [ih, cis_add]; congr 1; grind

/-- **Polar form.** Every non-zero complex number is `|u| (cos θ + i sin θ)`. -/
theorem exists_polar {u : C} (hu : u ≠ 0) : ∃ θ, u = ofReal (cabs u) * cis θ := by
  have hr := cabs_pos hu
  have hrr := cabs_mul_self u
  obtain ⟨θ, hc, hs⟩ := exists_angle (x := u.re / cabs u) (y := u.im / cabs u) (by
    unfold normSq at hrr
    have : cabs u ≠ 0 := by grind
    grind)
  refine ⟨θ, ext ?_ ?_⟩
  · show u.re = cabs u * cos θ - 0 * sin θ; rw [hc]; grind
  · show u.im = cabs u * sin θ + 0 * cos θ; rw [hs]; grind

/-- **`k`-th roots.** For every complex `u` and `k ≥ 1` there is `ω` with `ωᵏ = u`. -/
theorem exists_pow_eq (u : C) {k : Nat} (hk : 1 ≤ k) : ∃ ω : C, ω ^ k = u := by
  by_cases hu : u = 0
  · refine ⟨0, ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hu]; show (0 : C) ^ j * 0 = 0; grind
  · obtain ⟨θ, hθ⟩ := exists_polar hu
    obtain ⟨s, hs0, hs⟩ := exists_nth_root (cabs_nonneg u) hk
    refine ⟨ofReal s * cis (θ / (k : R)), ?_⟩
    have hk' : (0 : R) < (k : R) := OrderedRing.pos_natCast_of_pos _ (by omega)
    rw [mul_pow, ofReal_pow, cis_pow, hs, show (k : R) * (θ / (k : R)) = θ by grind]
    exact hθ.symm

end C

end Foundations.Numbers
