import Foundations.Langlands.Modular.Eisenstein

/-!
# The Eisenstein series are not identically zero

The transformation law alone is satisfied by the zero function, so `G_isModular` would be
empty if `G_k` vanished identically. This file shows that it does not: for every even `k ≥ 4`,

  **`G_k(9i) ≠ 0`** (`G_ne_zero`), indeed `Re G_k(9i) ≥ 2/9` (`re_G_ge`).

The idea is the one behind the classical limit `G_k(iy) → 2ζ(k)` as `y → ∞` (which we do not
prove): split the lattice sum at `τ = iy` into

* the row `m = 0`, which is `Σ_{0 < |n| ≤ N} n^{−k}`; for even `k` its terms are positive reals
  and the two terms `n = ±1` already give `2` (`re_row_ge_two`);
* the rest `m ≠ 0`, where `|miy + n|² = m²y² + n²` is at least `max(|m|, |n|)²` and at least `y²`,
  so `|miy + n|^{−k} · max(|m|, |n|)³ ≤ 1/y` (`rest_bound`) and, by the shell estimate, the
  whole rest has modulus at most `16/y` (`cabs_rest_le`).

At `y = 9` this leaves `Re ≥ 2 − 16/9 = 2/9` for every square partial sum, hence for the limit.
Combined with `G_i_eq_zero`, for `k ≡ 2 (mod 4)` (`k ≥ 6`) the function `G_k` is a non-zero
solution of the weight-`k` law that vanishes at `i` (`G_nonzero_but_vanishes_at_i`).
-/

namespace Foundations.Langlands.Modular

open Foundations.Numbers Foundations.Numbers.C Lean.Grind SL2Z

attribute [local instance] Semiring.natCast Ring.intCast

namespace Lattice

/-! ## Real-number preliminaries -/

/-- Powers of non-negative reals are non-negative. -/
theorem rpow_nonneg {x : R} (hx : 0 ≤ x) (n : Nat) : 0 ≤ x ^ n := by
  induction n with
  | zero => show (0 : R) ≤ 1; grind
  | succ n ih => rw [R.pow_succ']; exact OrderedRing.mul_nonneg ih hx

/-- `1ⁿ = 1` in ℝ. -/
theorem rone_pow (n : Nat) : (1 : R) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [R.pow_succ', ih]; grind

/-- `x^{2j} = (x²)^j` in ℝ. -/
theorem rpow_two_mul (x : R) (j : Nat) : x ^ (2 * j) = (x * x) ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, R.pow_succ', R.pow_succ', R.pow_succ', ih]
    grind

/-- Powers of a real number, viewed in ℂ, stay real: `(a + 0i)ⁿ = aⁿ + 0i`. -/
theorem ofReal_pow (a : R) (n : Nat) : (⟨a, 0⟩ : C) ^ n = ⟨a ^ n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (⟨a, 0⟩ : C) ^ n * ⟨a, 0⟩ = ⟨a ^ n * a, 0⟩
    rw [ih]; apply C.ext
    · show a ^ n * a - 0 * 0 = a ^ n * a; grind
    · show a ^ n * 0 + 0 * a = 0; grind

/-- An integer square is at least `1` in ℝ when the integer is non-zero. -/
theorem one_le_intCast_sq {m : Int} (hm : m ≠ 0) : (1 : R) ≤ (m : R) * (m : R) := by
  have h := int_mul_self_pos hm
  have := intCast_le_of_le (show (1 : Int) ≤ m * m by omega)
  rw [Ring.intCast_mul, Ring.intCast_one] at this; exact this

/-! ## The row `m = 0` -/

/-- Real parts of interval sums. -/
theorem isum_re (a : Int) (len : Nat) (h : Int → C) :
    (isum a len h).re = isum a len (fun n => (h n).re) := by
  unfold isum; rw [gsum_re, R.gsum_eq_fsum]

/-- The terms of the row `m = 0` are `n^{−k}`. -/
theorem eterm_zero_row (k : Nat) (z : C) (n : Int) :
    eterm k z 0 n = (⟨(n : R) ^ k, 0⟩ : C)⁻¹ := by
  unfold eterm lin
  rw [Ring.intCast_zero, show (0 : C) * z + (n : C) = ⟨(n : R), 0⟩ by
    apply C.ext
    · show 0 * z.re - 0 * z.im + (n : R) = (n : R); grind
    · show 0 * z.im + 0 * z.re + 0 = 0; grind, ofReal_pow]

/-- For even `k`, the terms `n^{−k}` have non-negative real part. -/
theorem re_eterm_zero_row_nonneg (j : Nat) (z : C) (n : Int) :
    0 ≤ (eterm (2 * j) z 0 n).re := by
  rw [eterm_zero_row, C.inv_re, rpow_two_mul]
  have ha := rpow_nonneg (C.mul_self_nonneg (n : R)) j
  generalize ((n : R) * (n : R)) ^ j = a at *
  show 0 ≤ a / (a * a + 0 * 0)
  rcases (by grind : a = 0 ∨ 0 < a) with h | h
  · rw [h]; show (0 : R) ≤ 0 * (0 * 0 + 0 * 0)⁻¹; grind
  · exact Std.le_of_lt (OF.div_pos h (by have := OrderedRing.mul_pos h h; grind))

/-- The terms `n = ±1` of the row `m = 0` equal `1`. -/
theorem re_eterm_zero_row_one (j : Nat) (z : C) {n : Int} (hn : n = 1 ∨ n = -1) :
    (eterm (2 * j) z 0 n).re = 1 := by
  rw [eterm_zero_row, C.inv_re, rpow_two_mul]
  have : (n : R) * (n : R) = 1 := by
    rcases hn with h | h <;> rw [h]
    · rw [Ring.intCast_one]; grind
    · rw [Ring.intCast_neg, Ring.intCast_one]; grind
  rw [this, rone_pow]
  show (1 : R) / (1 * 1 + 0 * 0) = 1; grind

/-- **The row `m = 0` has real part at least 2** (from `n = ±1`), for even `k` and `N ≥ 1`. -/
theorem re_row_ge_two (j : Nat) (z : C) {N : Nat} (hN : 1 ≤ N) :
    2 ≤ (isum (-(N : Int)) (2 * N + 1) (eterm (2 * j) z 0)).re := by
  rw [isum_re]
  have h1 := isum_single (b := -(N : Int)) (len := 2 * N + 1) (c := 1) (by omega) (by omega) (1 : R)
  have h2 := isum_single (b := -(N : Int)) (len := 2 * N + 1) (c := -1) (by omega) (by omega) (1 : R)
  have h3 := isum_add (-(N : Int)) (2 * N + 1) (fun n => if n = 1 then (1 : R) else 0)
    (fun n => if n = -1 then (1 : R) else 0)
  have h4 : isum (-(N : Int)) (2 * N + 1)
      (fun n => (if n = 1 then (1 : R) else 0) + (if n = -1 then (1 : R) else 0)) ≤
      isum (-(N : Int)) (2 * N + 1) (fun n => (eterm (2 * j) z 0 n).re) := by
    unfold isum; apply gsum_le; intro i _
    dsimp only
    generalize -(N : Int) + (i : Int) = n
    by_cases e1 : n = 1
    · rw [ite_t e1, ite_f (by omega), re_eterm_zero_row_one j z (Or.inl e1)]; grind
    · by_cases e2 : n = -1
      · rw [ite_f e1, ite_t e2, re_eterm_zero_row_one j z (Or.inr e2)]; grind
      · rw [ite_f e1, ite_f e2]; have := re_eterm_zero_row_nonneg j z n; grind
  grind

/-- The square sum of the row `m = 0` is the interval sum `Σ_{|n| ≤ N} n^{−k}`. -/
theorem sq_row (k : Nat) (z : C) (N : Nat) :
    sq N (fun m n => if m = 0 then eterm k z m n else 0) =
      isum (-(N : Int)) (2 * N + 1) (eterm k z 0) := by
  unfold sq
  rw [isum_congr (h' := fun m => if m = 0 then isum (-(N : Int)) (2 * N + 1) (eterm k z 0) else 0)
    fun m _ _ => by
      by_cases hm : m = 0
      · rw [ite_t hm]; subst hm; apply isum_congr; intro n _ _; rfl
      · rw [ite_f hm]; refine Eq.trans (isum_congr fun n _ _ => ?_) (isum_zero _ _)
        dsimp only; rw [ite_f hm]]
  exact isum_single (by omega) (by omega) _

/-! ## The rest `m ≠ 0` -/

/-- **The bound for `m ≠ 0` at `τ = iy`, `y ≥ 1`, `k ≥ 4`:**
`|miy + n|^{−k} · max(|m|, |n|)³ ≤ 1/y`. -/
theorem rest_bound {k : Nat} (hk : 4 ≤ k) {y : R} (hy : 0 < y) (hy1 : 1 ≤ y) (m n : Int) :
    cabs (if m = 0 then 0 else eterm k (iMul y hy).z m n) * ((supNorm m n : Nat) : R) ^ 3 ≤
      y⁻¹ := by
  by_cases hm : m = 0
  · rw [ite_t hm, cabs_zero]; have := inv_pos' hy; grind
  rw [ite_f hm, cabs_eterm]
  have hQ : normSq (lin (iMul y hy).z m n) = (n : R) * (n : R) + (m : R) * y * ((m : R) * y) := by
    rw [normSq_lin]; unfold SL2Z.Q; show ((m : R) * 0 + _) * ((m : R) * 0 + _) + (m : R) * y * ((m : R) * y) = _; grind
  have hm1 := one_le_intCast_sq hm
  have hyy : 1 ≤ y * y := by have := OrderedRing.mul_le_mul_of_nonneg_left hy1 (by grind : (0 : R) ≤ y); grind
  have hn := C.mul_self_nonneg (n : R)
  have hsup := supNorm_sq_le m n
  have hs0 : 0 ≤ ((supNorm m n : Nat) : R) := OrderedRing.natCast_nonneg
  generalize hc : cabs (lin (iMul y hy).z m n) = c
  have hcc : c * c = normSq (lin (iMul y hy).z m n) := by rw [← hc, cabs_mul_self]
  have hc0 : 0 ≤ c := by rw [← hc]; exact cabs_nonneg _
  generalize ((supNorm m n : Nat) : R) = s at *
  -- `c ≥ s` and `c ≥ y`
  have hmm := OrderedRing.mul_le_mul_of_nonneg_left hyy (C.mul_self_nonneg (m : R))
  have hcs : s ≤ c := R.le_of_mul_self_le hc0 (by rw [hcc, hQ]; grind)
  have hcy : y ≤ c := R.le_of_mul_self_le hc0 (by
    rw [hcc, hQ]
    have := OrderedRing.mul_le_mul_of_nonneg_right hm1 (by grind : (0 : R) ≤ y * y)
    grind)
  have hc1 : 1 ≤ c := Std.le_trans hy1 hcy
  have hck : c ^ 4 ≤ c ^ k := by
    have := pow_le_pow_add hc1 4 (k - 4); rwa [show 4 + (k - 4) = k by omega] at this
  have h4 : c ^ 4 = c * c * c * c := by show 1 * c * c * c * c = _; grind
  apply inv_mul_le_inv (rpow_pos (by grind) k) hy
  rw [pow_three]
  have q0 := OrderedRing.mul_le_mul_of_nonneg_left hcy
    (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hs0 hs0) hs0)
  have q1 := OrderedRing.mul_le_mul_of_nonneg_left hcs
    (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hs0 hs0) hc0)
  have q2 := OrderedRing.mul_le_mul_of_nonneg_left hcs
    (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hs0 hc0) hc0)
  have q3 := OrderedRing.mul_le_mul_of_nonneg_left hcs
    (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hc0 hc0) hc0)
  grind

/-- **The rest is small.** At `τ = iy` with `y ≥ 1` and `k ≥ 4`, the part `m ≠ 0` of every
square partial sum has modulus at most `16/y`. -/
theorem cabs_rest_le {k : Nat} (hk : 4 ≤ k) {y : R} (hy : 0 < y) (hy1 : 1 ≤ y) (N : Nat) :
    cabs (sq N (fun m n => if m = 0 then 0 else eterm k (iMul y hy).z m n)) ≤ 16 * y⁻¹ := by
  refine Std.le_trans (cabs_sq_le _ _) ?_
  have := sq_cabs_le _ (rest_bound hk hy hy1) N
  rw [ite_t rfl, cabs_zero] at this
  grind

/-- Splitting a partial sum into the row `m = 0` and the rest. -/
theorem partialG_split (k : Nat) (z : C) (N : Nat) :
    partialG k z N = isum (-(N : Int)) (2 * N + 1) (eterm k z 0) +
      sq N (fun m n => if m = 0 then 0 else eterm k z m n) := by
  unfold partialG; rw [← sq_row, ← sq_add]
  apply sq_congr; intro m n _ _ _ _
  by_cases hm : m = 0
  · rw [ite_t hm, ite_t hm]; grind
  · rw [ite_f hm, ite_f hm]; grind

/-- **Every square partial sum of `G_k(9i)` has real part at least `2/9`**, for even `k ≥ 4`
and `N ≥ 1`: the row `m = 0` contributes at least `2`, the rest at most `16/9` in modulus. -/
theorem re_partialG_ge {j : Nat} (hj : 2 ≤ j) {N : Nat} (hN : 1 ≤ N) :
    2 / 9 ≤ (partialG (2 * j) (iMul 9 (by grind)).z N).re := by
  rw [partialG_split, C.add_re]
  have h1 := re_row_ge_two j (iMul 9 (by grind)).z hN
  have h2 := cabs_rest_le (k := 2 * j) (by omega) (y := 9) (by grind) (by grind) N
  have h3 := abs_re_le_cabs (sq N (fun m n => if m = 0 then 0 else
    eterm (2 * j) (iMul 9 (by grind)).z m n))
  have h4 := (OF.abs_le.1 h3).1
  have : (16 : R) * 9⁻¹ = 16 / 9 := by grind
  grind

/-- **A lower bound for `G_k(9i)`.** For even `k ≥ 4`, `Re G_k(9i) ≥ 2/9`. -/
theorem re_G_ge {j : Nat} (hj : 2 ≤ j) : 2 / 9 ≤ (G (2 * j) (iMul 9 (by grind))).re := by
  apply Classical.byContradiction; intro hlt
  have hε : 0 < 2 / 9 - (G (2 * j) (iMul 9 (by grind))).re := by grind
  obtain ⟨N, hN⟩ := tendsto_G (k := 2 * j) (by omega) (iMul 9 (by grind)) _ hε
  have k1 := hN (max N 1) (by omega)
  have k2 := re_partialG_ge hj (N := max N 1) (by omega)
  have k3 := (OF.abs_lt.1 (Std.lt_of_le_of_lt (abs_re_le_cabs _) k1)).2
  have e : (partialG (2 * j) (iMul 9 (by grind)).z (max N 1) - G (2 * j) (iMul 9 (by grind))).re =
      (partialG (2 * j) (iMul 9 (by grind)).z (max N 1)).re - (G (2 * j) (iMul 9 (by grind))).re :=
    by show _ + -_ = _; grind
  rw [e] at k3
  grind

/-- **The Eisenstein series are not identically zero.** For every even `k ≥ 4`,
`G_k(9i) ≠ 0`. -/
theorem G_ne_zero {j : Nat} (hj : 2 ≤ j) : G (2 * j) (iMul 9 (by grind)) ≠ 0 := fun h => by
  have := re_G_ge hj
  rw [h, C.zero_re] at this; grind

/-- **A non-zero solution of the weight-`k` law vanishing at `i`.** For `k = 4j + 2 ≥ 6`, the
Eisenstein series `G_k` satisfies the weight-`k` law, is not identically zero, and vanishes at
`i`. -/
theorem G_nonzero_but_vanishes_at_i {j : Nat} (hj : 1 ≤ j) :
    IsModular (4 * j + 2) (G (4 * j + 2)) ∧ G (4 * j + 2) (iMul 9 (by grind)) ≠ 0 ∧
      G (4 * j + 2) (iMul 1 (by grind)) = 0 := by
  refine ⟨G_isModular (by omega), ?_, G_i_eq_zero j hj⟩
  have := G_ne_zero (j := 2 * j + 1) (by omega)
  rwa [show 2 * (2 * j + 1) = 4 * j + 2 by omega] at this

end Lattice

end Foundations.Langlands.Modular
