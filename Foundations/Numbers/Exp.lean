import Foundations.Numbers.Series

/-!
# Analysis on the reals V: the exponential function and the number `e`

Euler defined the exponential function by the power series

  `exp x = 1 + x + x²/2! + x³/3! + ⋯ = Σ xⁿ / n!`,

and we do the same. The ratio test of the previous file shows that the series converges for every
real `x` (the ratio of consecutive terms is `x/(n+1)`, eventually below `1/2`).

From the series alone we then prove:

* `exp` is its own derivative, `exp' = exp`. The proof estimates the series term by term: the
  `n`-th term of `exp y − exp x − (y − x) exp x` is at most `(y − x)²/2 · Mⁿ⁻²/(n−2)!`, so the
  whole difference is at most a constant times `(y − x)²`;
* the **functional equation** `exp (x + y) = exp x · exp y`. Instead of multiplying series we use
  the calculus of the previous files: `t ↦ exp t · exp (c − t)` has derivative `0`, so it is
  constant (a consequence of the mean value theorem);
* `exp` is **positive** and **strictly increasing**;
* Euler's number `e = exp 1 = Σ 1/n!` is **irrational** (Fourier's proof, 1815): if `e = p/q`,
  then `m! (e − Σ_{n ≤ m} 1/n!)` would be an integer strictly between `0` and `1` for `m = q + 1`.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-! ## Factorials -/

/-- The **factorial** `n! = 1 · 2 ⋯ n` (with `0! = 1`). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Factorials are positive. -/
theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => show 0 < 1; omega
  | succ n ih => show 0 < (n + 1) * fact n; exact Nat.mul_pos (by omega) ih

/-- Factorials are positive as reals. -/
theorem fact_pos' (n : Nat) : (0 : R) < (fact n : R) :=
  OrderedRing.pos_natCast_of_pos _ (fact_pos n)

/-- The recursion `(n+1)! = (n+1) · n!` as reals. -/
theorem fact_succ' (n : Nat) : (fact (n + 1) : R) = ((n : R) + 1) * (fact n : R) := by
  show (((n + 1) * fact n : Nat) : R) = _; grind

/-- `k! ∣ m!` for `k ≤ m`. -/
theorem fact_dvd_fact {k m : Nat} (h : k ≤ m) : fact k ∣ fact m := by
  induction m with
  | zero => rw [show k = 0 by omega]; exact Nat.dvd_refl _
  | succ m ih =>
    by_cases hk : k = m + 1
    · rw [hk]; exact Nat.dvd_refl _
    · exact Nat.dvd_trans (ih (by omega)) ⟨m + 1, by show (m + 1) * fact m = fact m * (m + 1); grind⟩

/-- `q ∣ m!` for `1 ≤ q ≤ m`. -/
theorem dvd_fact {q m : Nat} (h1 : 1 ≤ q) (h2 : q ≤ m) : q ∣ fact m := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  exact Nat.dvd_trans ⟨fact r, rfl⟩ (fact_dvd_fact h2)

/-! ## The exponential series -/

/-- The `n`-th term `xⁿ / n!` of the exponential series. -/
noncomputable def expTerm (x : R) (n : Nat) : R := x ^ n / (fact n : R)

/-- Consecutive terms of the exponential series: `xⁿ⁺¹/(n+1)! = xⁿ/n! · x/(n+1)`. -/
theorem expTerm_succ (x : R) (n : Nat) :
    expTerm x (n + 1) = expTerm x n * (x / ((n : R) + 1)) := by
  unfold expTerm
  rw [fact_succ', pow_succ']
  have := fact_pos' n
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  grind

/-- Terms of the exponential series at `x ≥ 0` are non-negative. -/
theorem expTerm_nonneg {x : R} (hx : 0 ≤ x) (n : Nat) : 0 ≤ expTerm x n := by
  induction n with
  | zero => unfold expTerm; show (0 : R) ≤ 1 / ((1 : Nat) : R); grind
  | succ n ih =>
    rw [expTerm_succ]
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    exact OrderedRing.mul_nonneg ih (div_pos' hx (by grind : (0 : R) < (n : R) + 1))
where
  /-- A non-negative number divided by a positive one is non-negative. -/
  div_pos' {a b : R} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
    rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg ha (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hb))

/-- For `b > 0`, `|x / b| = |x| · b⁻¹`. -/
theorem abs_div_pos {x b : R} (hb : 0 < b) : abs (x / b) = abs x * b⁻¹ := by
  rw [Field.div_eq_mul_inv, abs_mul, abs_of_nonneg (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hb))]

/-- **The exponential series converges absolutely** for every real `x` (ratio test). -/
theorem summable_expTerm_abs (x : R) : ∃ t, HasSum (fun n => abs (expTerm x n)) t := by
  obtain ⟨N, hN⟩ := archimedean (2 * abs x)
  refine ratio_test (q := 1 / 2) (by grind) (by grind) N fun n hn => ?_
  have hnN : (N : R) ≤ (n : R) := OrderedRing.natCast_le_natCast_of_le _ _ hn
  have hpos : (0 : R) < (n : R) + 1 := by
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg; grind
  rw [expTerm_succ, abs_mul, abs_div_pos hpos]
  -- `|x| / (n + 1) ≤ 1/2`.
  have k : abs x * ((n : R) + 1)⁻¹ ≤ 1 / 2 := by
    have := OrderedRing.mul_le_mul_of_nonneg_right (by grind : 2 * abs x ≤ (n : R) + 1)
      (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hpos))
    grind
  have := OrderedRing.mul_le_mul_of_nonneg_left k (abs_nonneg (expTerm x n))
  grind

/-- The exponential series converges. -/
theorem exists_hasSum_exp (x : R) : ∃ s, HasSum (expTerm x) s := by
  obtain ⟨t, ht⟩ := summable_expTerm_abs x
  obtain ⟨s, hs, -⟩ := summable_of_abs ht
  exact ⟨s, hs⟩

/-- **The exponential function** `exp x = Σ xⁿ / n!`. -/
noncomputable def exp (x : R) : R := Classical.choose (exists_hasSum_exp x)

/-- `exp x` is the sum of the exponential series. -/
theorem hasSum_exp (x : R) : HasSum (expTerm x) (exp x) :=
  Classical.choose_spec (exists_hasSum_exp x)

/-- `exp 0 = 1`. -/
theorem exp_zero : exp 0 = 1 := by
  have h : HasSum (expTerm 0) 1 := by
    apply (tendsto_const 1).congr_eventually 1
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    induction k with
    | zero => show (1 : R) = 0 + (0 : R) ^ 0 / ((fact 0 : Nat) : R); show (1 : R) = 0 + 1 / ((1 : Nat) : R); grind
    | succ k ih =>
      rw [fsum_succ, ← ih (by omega), expTerm_succ]; grind
  exact (hasSum_exp 0).unique h

/-- For `x ≥ 0`, `exp x ≥ 1 + x` (the first two terms of the series). -/
theorem one_add_le_exp {x : R} (hx : 0 ≤ x) : 1 + x ≤ exp x := by
  have := fsum_le_of_hasSum (expTerm_nonneg hx) (hasSum_exp x) 2
  have e : fsum (expTerm x) 2 = 1 + x := by
    rw [fsum_succ, fsum_succ, fsum_zero, expTerm_succ]
    show 0 + x ^ 0 / ((1 : Nat) : R) + x ^ 0 / ((1 : Nat) : R) * (x / (((0 : Nat) : R) + 1)) = 1 + x
    grind
  grind

/-! ## The derivative of `exp` -/

/-- The error term `yⁿ − xⁿ − n xⁿ⁻¹ (y − x)` of the linear approximation of `yⁿ`. -/
noncomputable def powErr (x y : R) (n : Nat) : R := y ^ n - x ^ n - (n : R) * x ^ (n - 1) * (y - x)

/-- Recursion for the error term: `E (n+1) = y · E n + n xⁿ⁻¹ (y − x)²`. -/
theorem powErr_succ (x y : R) (n : Nat) :
    powErr x y (n + 1) = y * powErr x y n + (n : R) * x ^ (n - 1) * ((y - x) * (y - x)) := by
  unfold powErr
  cases n with
  | zero => show y ^ 1 - x ^ 1 - ((0 + 1 : Nat) : R) * x ^ 0 * (y - x) = _
            show y ^ 0 * y - x ^ 0 * x - ((0 + 1 : Nat) : R) * x ^ 0 * (y - x) = _; grind
  | succ m =>
    rw [show m + 1 + 1 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega, pow_succ' y (m + 1),
      pow_succ' x (m + 1), pow_succ' x m]
    grind

/-- Powers are monotone on `[0, ∞)`. -/
theorem pow_le_pow_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) (n : Nat) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => show (1 : R) ≤ 1; grind
  | succ n ih =>
    rw [pow_succ', pow_succ']
    have hb : 0 ≤ b ^ n := Std.le_trans (pow_nonneg ha n) ih
    have := OrderedRing.mul_le_mul_of_nonneg_right ih ha
    have := OrderedRing.mul_le_mul_of_nonneg_left hab hb
    grind
where
  /-- Powers of a non-negative number are non-negative. -/
  pow_nonneg {a : R} (ha : 0 ≤ a) (n : Nat) : 0 ≤ a ^ n := by
    induction n with
    | zero => show (0 : R) ≤ 1; grind
    | succ n ih => rw [pow_succ']; exact OrderedRing.mul_nonneg ih ha

/-- Size of the error term: if `|x|, |y| ≤ M` then
`|E (n+2)| ≤ (n+2)(n+1)/2 · Mⁿ · |y − x|²`. -/
theorem abs_powErr_le {x y M : R} (hx : abs x ≤ M) (hy : abs y ≤ M) (n : Nat) :
    abs (powErr x y (n + 2)) ≤
      ((n : R) + 2) * ((n : R) + 1) / 2 * M ^ n * (abs (y - x) * abs (y - x)) := by
  have hM : 0 ≤ M := Std.le_trans (abs_nonneg x) hx
  have hk := OrderedRing.mul_nonneg (abs_nonneg (y - x)) (abs_nonneg (y - x))
  induction n with
  | zero =>
    have e : powErr x y (0 + 2) = (y - x) * (y - x) := by
      unfold powErr; show y ^ 2 - x ^ 2 - ((2 : Nat) : R) * x ^ 1 * (y - x) = _; grind
    rw [e, abs_mul]
    grind
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, powErr_succ, show n + 2 - 1 = n + 1 by omega]
    have hn : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    have t1 := abs_mul_le hy ih
    have t2 : abs (((n + 2 : Nat) : R) * x ^ (n + 1) * ((y - x) * (y - x))) ≤
        ((n : R) + 2) * M ^ (n + 1) * (abs (y - x) * abs (y - x)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (OrderedRing.natCast_nonneg)]
      have := pow_le_pow_left (abs_nonneg x) hx (n + 1)
      have := OrderedRing.mul_le_mul_of_nonneg_left this (by grind : (0 : R) ≤ (n : R) + 2)
      have := OrderedRing.mul_le_mul_of_nonneg_right this hk
      grind
    have t3 := abs_add (y * powErr x y (n + 2)) (((n + 2 : Nat) : R) * x ^ (n + 1) * ((y - x) * (y - x)))
    rw [pow_succ' M n] at t2 ⊢
    grind

/-- The auxiliary series `Σ n xⁿ⁻¹ / n!` (the termwise derivative of the exponential series). -/
noncomputable def derTerm (x : R) (n : Nat) : R := (n : R) * x ^ (n - 1) / (fact n : R)

/-- The termwise derivative of the exponential series sums to `exp x`. -/
theorem hasSum_derTerm (x : R) : HasSum (derTerm x) (exp x) := by
  apply hasSum_succ_iff.1
  have e0 : derTerm x 0 = 0 := by unfold derTerm; show ((0 : Nat) : R) * x ^ (0 - 1) / _ = 0; grind
  rw [e0, show exp x - 0 = exp x by grind]
  refine (hasSum_exp x).congr fun n => ?_
  unfold derTerm expTerm
  rw [fact_succ', show n + 1 - 1 = n by omega]
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  have := OrderedRing.mul_pos (by grind : (0 : R) < (n : R) + 1) (fact_pos' n)
  have := fact_pos' n
  grind

/-- Termwise estimate: `|E (n+2) / (n+2)!| ≤ |y − x|²/2 · Mⁿ/n!` when `|x|, |y| ≤ M`. -/
theorem abs_powErr_div_le {x y M : R} (hx : abs x ≤ M) (hy : abs y ≤ M) (n : Nat) :
    abs (powErr x y (2 + n) / (fact (2 + n) : R)) ≤
      abs (y - x) * abs (y - x) / 2 * expTerm M n := by
  rw [Nat.add_comm 2 n]
  have hF : (fact (n + 2) : R) = ((n : R) + 2) * ((n : R) + 1) * (fact n : R) := by
    rw [fact_succ', fact_succ']; grind
  have hFp := fact_pos' (n + 2)
  rw [abs_div_pos hFp]
  have k := OrderedRing.mul_le_mul_of_nonneg_right (abs_powErr_le hx hy n)
    (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hFp))
  have := fact_pos' n
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  unfold expTerm
  rw [hF] at k ⊢
  have hP := OrderedRing.mul_pos (OrderedRing.mul_pos (by grind : (0 : R) < (n : R) + 2)
    (by grind : (0 : R) < (n : R) + 1)) (fact_pos' n)
  have i1 := Field.mul_inv_cancel (show ((n : R) + 2) * ((n : R) + 1) * (fact n : R) ≠ 0 by grind)
  have i2 := Field.mul_inv_cancel (show (fact n : R) ≠ 0 by grind)
  have e : ((n : R) + 2) * ((n : R) + 1) / 2 * M ^ n * (abs (y - x) * abs (y - x)) *
      (((n : R) + 2) * ((n : R) + 1) * (fact n : R))⁻¹ =
      abs (y - x) * abs (y - x) / 2 * (M ^ n / (fact n : R)) := by grind
  rw [e] at k
  exact k

/-- **Quadratic estimate.** `|exp y − exp x − (y − x) exp x| ≤ |y − x|²/2 · exp (|x| + 1)` when
`|y − x| ≤ 1`. -/
theorem abs_exp_sub_le {x y : R} (hxy : abs (y - x) ≤ 1) :
    abs (exp y - exp x - (y - x) * exp x) ≤
      abs (y - x) * abs (y - x) / 2 * exp (abs x + 1) := by
  let M := abs x + 1
  have hx : abs x ≤ M := by grind
  have hy : abs y ≤ M := by
    have := abs_add (y - x) x; rw [show y - x + x = y by grind] at this; grind
  have hM : 0 ≤ M := by have := abs_nonneg x; grind
  -- The series of error terms `E n / n!` sums to the left-hand side…
  have h1 : HasSum (fun n => powErr x y n / (fact n : R))
      (exp y - exp x - (y - x) * exp x) := by
    refine (((hasSum_exp y).sub (hasSum_exp x)).sub ((hasSum_derTerm x).const_mul (y - x))).congr
      fun n => ?_
    unfold expTerm derTerm powErr
    have := fact_pos' n
    grind
  -- …and its first two terms vanish.
  have h2 : HasSum (fun n => powErr x y (2 + n) / (fact (2 + n) : R))
      (exp y - exp x - (y - x) * exp x) := by
    have := (hasSum_shift_iff (a := fun n => powErr x y n / (fact n : R)) 2).2 h1
    have e : fsum (fun n => powErr x y n / (fact n : R)) 2 = 0 := by
      rw [fsum_succ, fsum_succ, fsum_zero]; unfold powErr
      show 0 + (y ^ 0 - x ^ 0 - ((0 : Nat) : R) * x ^ (0 - 1) * (y - x)) / ((1 : Nat) : R) +
        (y ^ 1 - x ^ 1 - ((1 : Nat) : R) * x ^ (1 - 1) * (y - x)) / ((1 * 1 : Nat) : R) = 0
      show 0 + (y ^ 0 - x ^ 0 - ((0 : Nat) : R) * x ^ 0 * (y - x)) / ((1 : Nat) : R) +
        (y ^ 0 * y - x ^ 0 * x - ((1 : Nat) : R) * x ^ 0 * (y - x)) / ((1 * 1 : Nat) : R) = 0
      grind
    rw [e, show exp y - exp x - (y - x) * exp x - 0 = exp y - exp x - (y - x) * exp x by grind]
      at this
    exact this
  -- Each term is dominated by `|y − x|²/2 · Mⁿ/n!`.
  have h3 : ∀ n, abs (powErr x y (2 + n) / (fact (2 + n) : R)) ≤
      abs (y - x) * abs (y - x) / 2 * expTerm M n := abs_powErr_div_le hx hy
  have := abs_hasSum_le h3 h2 ((hasSum_exp M).const_mul (abs (y - x) * abs (y - x) / 2))
  exact this

/-- A quadratic error bound gives a derivative: if `|f y − f x − d (y − x)| ≤ C |y − x|²` for
`|y − x| ≤ 1`, then `f' (x) = d`. -/
theorem hasDerivAt_of_quadratic {f : R → R} {d x C : R} (hC : 0 ≤ C)
    (h : ∀ y, abs (y - x) ≤ 1 → abs (f y - f x - d * (y - x)) ≤ C * (abs (y - x) * abs (y - x))) :
    HasDerivAt f d x := fun ε hε => by
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both (by grind : (0 : R) < 1)
    (div_pos hε (by grind : 0 < C + 1))
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have k := h y (by grind)
  have hk := abs_nonneg (y - x)
  -- `|y − x| · C ≤ ε`.
  have k1 := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt hy) (by grind : 0 ≤ C + 1)
  have k2 := OrderedRing.mul_le_mul_of_nonneg_left hδ2 (by grind : 0 ≤ C + 1)
  have e : (C + 1) * (ε / (C + 1)) = ε := by grind
  have k3 : abs (y - x) * C ≤ ε := by
    have := OrderedRing.mul_nonneg hk hC
    grind
  have k4 := OrderedRing.mul_le_mul_of_nonneg_left k3 hk
  grind

/-- **`exp` is its own derivative**: `exp' = exp`. -/
theorem hasDerivAt_exp (x : R) : HasDerivAt exp (exp x) x := by
  have hE : 0 ≤ exp (abs x + 1) := by
    have := one_add_le_exp (by have := abs_nonneg x; grind : 0 ≤ abs x + 1)
    have := abs_nonneg x; grind
  refine hasDerivAt_of_quadratic (C := exp (abs x + 1) / 2) (by grind) fun y hy => ?_
  have k := abs_exp_sub_le (x := x) (y := y) hy
  rw [show exp y - exp x - (y - x) * exp x = exp y - exp x - exp x * (y - x) by grind] at k
  grind

/-! ## The functional equation -/

/-- **Functional equation of the exponential.** `exp (x + y) = exp x · exp y`. -/
theorem exp_add (x y : R) : exp (x + y) = exp x * exp y := by
  -- `g t = exp t · exp (c − t)` has derivative `0`, hence is constant.
  let c := x + y
  have hd : ∀ t, HasDerivAt (fun t => exp t * exp (c - t))
      (exp t * exp (c - t) + exp t * (exp (c - t) * (0 - 1))) t := fun t =>
    (hasDerivAt_exp t).mul ((hasDerivAt_exp (c - t)).comp (f := fun t => c - t)
      ((hasDerivAt_const c t).sub (hasDerivAt_id t)))
  have := const_of_deriv_zero' hd (fun t => by grind) x 0
  rw [exp_zero, show c - x = y by grind, show c - 0 = x + y by grind] at this
  grind

/-- `exp x · exp (−x) = 1`. -/
theorem exp_mul_exp_neg (x : R) : exp x * exp (-x) = 1 := by
  rw [← exp_add, show x + -x = 0 by grind, exp_zero]

/-- **The exponential is positive.** -/
theorem exp_pos (x : R) : 0 < exp x := by
  have h1 : 0 ≤ exp x := by
    rw [show x = x / 2 + x / 2 by grind, exp_add]
    have := OrderedRing.sq_nonneg (a := exp (x / 2)); grind
  have h2 := exp_mul_exp_neg x
  rcases (by grind : exp x = 0 ∨ 0 < exp x) with h | h
  · rw [h] at h2; grind
  · exact h

/-- **The exponential is strictly increasing.** -/
theorem exp_strictMono {x y : R} (h : x < y) : exp x < exp y :=
  strictMono_of_deriv_pos' hasDerivAt_exp exp_pos h

/-! ## Euler's number `e` is irrational -/

/-- **Euler's number** `e = exp 1 = 1 + 1 + 1/2! + 1/3! + ⋯`. -/
noncomputable def e : R := exp 1

/-- `1ⁿ = 1`. -/
theorem one_pow (n : Nat) : (1 : R) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', ih]; grind

/-- The terms of the series for `e`: `1/n!`. -/
theorem expTerm_one (n : Nat) : expTerm 1 n = 1 / (fact n : R) := by
  unfold expTerm; rw [one_pow]

/-- Taking reciprocals reverses the order of positive numbers. -/
theorem one_div_le_one_div {a b : R} (ha : 0 < a) (hab : a ≤ b) : 1 / b ≤ 1 / a := by
  have hb : 0 < b := by grind
  have i1 := Field.mul_inv_cancel (show a ≠ 0 by grind)
  have i2 := Field.mul_inv_cancel (show b ≠ 0 by grind)
  have := OrderedRing.mul_le_mul_of_nonneg_right hab
    (OrderedRing.mul_nonneg (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 ha))
      (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hb)))
  have e1 : a * (a⁻¹ * b⁻¹) = b⁻¹ := by rw [← Semiring.mul_assoc, i1, Semiring.one_mul]
  have e2 : b * (a⁻¹ * b⁻¹) = a⁻¹ := by
    rw [CommSemiring.mul_comm a⁻¹, ← Semiring.mul_assoc, i2, Semiring.one_mul]
  rw [e1, e2] at this
  rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv, Semiring.one_mul, Semiring.one_mul]
  exact this

/-- **Irrationality of `e`** (Fourier, 1815). There are no integers `p` and `q > 0` with
`e = p / q`. -/
theorem e_irrational : ¬ ∃ p : Int, ∃ q : Nat, 0 < q ∧ e = (p : R) / (q : R) := by
  rintro ⟨p, q, hq, he⟩
  let m := q + 1
  have hm : (2 : R) ≤ (m : R) := by
    have := OrderedRing.natCast_le_natCast_of_le (R := R) 2 m (by omega); grind
  -- `m! · e` is an integer, because `q ∣ m!`.
  obtain ⟨r, hr⟩ := dvd_fact (q := q) (m := m) hq (by omega)
  have hqpos : (0 : R) < (q : R) := OrderedRing.pos_natCast_of_pos _ hq
  have hme : (fact m : R) * e = (((r : Int) * p : Int) : R) := by
    rw [he, hr]
    have : (((q * r : Nat)) : R) = (q : R) * (r : R) := by grind
    rw [this]
    have : ((r : Int) : R) = (r : R) := Ring.intCast_natCast r
    grind
  -- `m! · (1/0! + ⋯ + 1/m!)` is a natural number.
  have hS : ∀ j, j ≤ m + 1 → ∃ N : Nat, (fact m : R) * fsum (expTerm 1) j = (N : R) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, by show (fact m : R) * 0 = ((0 : Nat) : R); grind⟩
    | succ j ih =>
      intro hj
      obtain ⟨N, hN⟩ := ih (by omega)
      obtain ⟨r', hr'⟩ := fact_dvd_fact (k := j) (m := m) (by omega)
      refine ⟨N + r', ?_⟩
      rw [fsum_succ, expTerm_one, hr']
      have := fact_pos' j
      have : (((fact j * r' : Nat)) : R) = (fact j : R) * (r' : R) := by grind
      rw [this]
      rw [hr'] at hN
      rw [this] at hN
      grind
  obtain ⟨N, hN⟩ := hS (m + 1) (Nat.le_refl _)
  -- The tail `m! · Σ_{n > m} 1/n!` …
  let T := (fact m : R) * (e - fsum (expTerm 1) (m + 1))
  have ht : HasSum (fun k => (fact m : R) * expTerm 1 (m + 1 + k)) T :=
    ((hasSum_shift_iff (a := expTerm 1) (s := e) (m + 1)).2 (hasSum_exp 1)).const_mul _
  let ρ : R := 1 / ((m : R) + 1)
  have hm0 : (0 : R) ≤ (m : R) := OrderedRing.natCast_nonneg
  have hρ : 0 < ρ := div_pos (by grind) (by grind)
  have hpos : ∀ k, 0 ≤ (fact m : R) * expTerm 1 (m + 1 + k) := fun k =>
    OrderedRing.mul_nonneg (Std.le_of_lt (fact_pos' m)) (expTerm_nonneg (by grind) _)
  have h0 : (fact m : R) * expTerm 1 (m + 1 + 0) = ρ := by
    rw [Nat.add_zero, expTerm_succ, expTerm_one]
    have := fact_pos' m
    grind
  -- … is positive (its first term is `1/(m+1)`) …
  have hTpos : 0 < T := by
    have := fsum_le_of_hasSum hpos ht 1
    rw [fsum_succ, fsum_zero, h0] at this
    grind
  -- … and at most `Σ_{k ≥ 1} (1/(m+1))ᵏ = 1/m ≤ 1/2`.
  have hdom : ∀ k, abs ((fact m : R) * expTerm 1 (m + 1 + k)) ≤ ρ * ρ ^ k := fun k => by
    rw [abs_of_nonneg (hpos k)]
    induction k with
    | zero => rw [h0]; show ρ ≤ ρ * 1; grind
    | succ k ih =>
      rw [← Nat.add_assoc, expTerm_succ, pow_succ']
      have hk : (0 : R) ≤ ((m + 1 + k : Nat) : R) := OrderedRing.natCast_nonneg
      have hle : 1 / (((m + 1 + k : Nat) : R) + 1) ≤ ρ :=
        one_div_le_one_div (by grind) (by
          have := OrderedRing.natCast_le_natCast_of_le (R := R) m (m + 1 + k) (by omega); grind)
      have k1 := OrderedRing.mul_le_mul_of_nonneg_right ih (Std.le_of_lt (div_pos
        (by grind : (0 : R) < 1) (by grind : (0 : R) < ((m + 1 + k : Nat) : R) + 1)))
      have k2 := OrderedRing.mul_le_mul_of_nonneg_left hle
        (OrderedRing.mul_nonneg (Std.le_of_lt hρ) (Std.le_trans (abs_nonneg _) (abs_le_pow ρ k hρ)))
      grind
  have hgeo := (hasSum_geometric (r := ρ) (by
    rw [abs_of_nonneg (Std.le_of_lt hρ)]
    have := one_div_le_one_div (by grind : (0 : R) < 2) (by grind : (2 : R) ≤ (m : R) + 1)
    grind)).const_mul ρ
  have hT := abs_hasSum_le hdom ht hgeo
  rw [abs_of_nonneg (Std.le_of_lt hTpos)] at hT
  have hval : ρ * (1 / (1 - ρ)) = 1 / (m : R) := by
    have i1 := Field.mul_inv_cancel (show (m : R) + 1 ≠ 0 by grind)
    have i2 := Field.mul_inv_cancel (show (m : R) ≠ 0 by grind)
    have i3 : 1 - ρ = (m : R) * ((m : R) + 1)⁻¹ := by grind
    rw [i3]
    have i4 := Field.mul_inv_cancel (show (m : R) * ((m : R) + 1)⁻¹ ≠ 0 by
      intro h
      have := OrderedRing.mul_pos (by grind : (0 : R) < (m : R))
        (Field.IsOrdered.inv_pos_iff.2 (by grind : (0 : R) < (m : R) + 1))
      grind)
    grind
  have hhalf := one_div_le_one_div (by grind : (0 : R) < 2) hm
  -- But `T = m! e − m! Σ_{n ≤ m} 1/n!` is an integer: contradiction.
  let z : Int := (r : Int) * p - (N : Int)
  have hz : (z : R) = T := by
    show (((r : Int) * p - (N : Int) : Int) : R) = (fact m : R) * (e - fsum (expTerm 1) (m + 1))
    have : ((N : Int) : R) = (N : R) := Ring.intCast_natCast N
    have : (((r : Int) * p - (N : Int) : Int) : R) = (((r : Int) * p : Int) : R) - ((N : Int) : R) := by
      grind
    grind
  have z1 : ((0 : Int) : R) < (z : R) := by rw [hz]; grind
  have z2 : (z : R) < ((1 : Int) : R) := by rw [hz]; grind
  have := (intCast_lt (K := R)).1 z1
  have := (intCast_lt (K := R)).1 z2
  omega
where
  /-- For `ρ > 0`, `|ρᵏ| ≤ ρᵏ`. -/
  abs_le_pow (ρ : R) (k : Nat) (hρ : 0 < ρ) : abs (ρ ^ k) ≤ ρ ^ k := by
    rw [abs_pow, abs_of_nonneg (Std.le_of_lt hρ)]; exact Std.le_refl _

end R

end Foundations.Numbers
