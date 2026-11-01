import Foundations.NumberTheory.Chebyshev

/-!
# Toward the prime number theorem I: finite sums and logarithms

The **prime number theorem** says that the number `π(x)` of primes up to `x` is asymptotic to
`x / log x`: the ratio `π(x) log x / x` tends to `1`. Gauss, as a teenager in 1792, noticed in
tables of primes that their density near `x` is about `1 / log x`; Legendre (1798, 1808) proposed
the similar formula `x / (log x − 1.08366)`. Chebyshev (1852) proved by elementary means that the
ratio stays between two positive constants (see `Chebyshev`), and Riemann's memoir of 1859
showed that the finer question is governed by the complex zeros of the zeta function. The
theorem was proved in 1896, independently by **Hadamard** and **de la Vallée Poussin**, using the
theory of functions of a complex variable — above all the fact that `ζ(s)` has no zeros on the
line `Re s = 1`.

For half a century it was believed that no proof could avoid complex analysis: the theorem
seemed to "know" about the zeros of `ζ`. In 1948 **Atle Selberg** found an elementary
"symmetry formula", and **Paul Erdős** and Selberg then derived the prime number theorem from it
without any complex analysis (Selberg's own paper and the joint use of Erdős's ideas led to a
well-known priority dispute; both published proofs in 1949, and Selberg's Fields Medal of 1950
cited this work). "Elementary" here does not mean easy — it means using only real numbers,
limits and the logarithm. Philosophically the result was a lesson about *purity of method*:
what a theorem is "about" does not dictate which tools are needed to prove it, and an apparently
deep dependence on one branch of mathematics can turn out to be an artefact of the first proof.

The files `PNT*` follow the elementary route as far as it goes in this development. This first
file only gathers tools: identities for finite sums `Σ_{k<n} a(k)` (exchanging a double sum,
picking out a single term, counting multiples), and inequalities for the logarithm
(`log y ≤ y − 1`, and the crude Stirling-type bounds `n log n − n ≤ log n! ≤ n log n`).
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.R Lean.Grind OF

/-! ## Finite sums -/

/-- The sum of zeros is zero. -/
theorem fsum_zeros (n : Nat) : fsum (fun _ => (0 : R)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fsum_succ, ih]; grind

/-- A sum of a constant: `Σ_{k<n} c = n · c`. -/
theorem fsum_const (c : R) (n : Nat) : fsum (fun _ => c) n = (n : R) * c := by
  induction n with
  | zero => show (0 : R) = ((0 : Nat) : R) * c; grind
  | succ n ih => rw [fsum_succ, ih]; grind

/-- Constant multiples on the right. -/
theorem fsum_mul_const (c : R) (a : Nat → R) (n : Nat) :
    fsum (fun k => a k * c) n = fsum a n * c := by
  have := fsum_const_mul c a n
  rw [← show (fun k => c * a k) = (fun k => a k * c) from funext fun k => by grind]
  grind

/-- **Exchanging the order of a double sum.**
`Σ_{i<n} Σ_{j<m} f(i,j) = Σ_{j<m} Σ_{i<n} f(i,j)`. -/
theorem fsum_swap (f : Nat → Nat → R) (m n : Nat) :
    fsum (fun i => fsum (fun j => f i j) m) n = fsum (fun j => fsum (fun i => f i j) n) m := by
  induction n with
  | zero => show (0 : R) = fsum (fun _ => (0 : R)) m; rw [fsum_zeros]
  | succ n ih =>
    rw [fsum_succ, ih]
    show _ = fsum (fun j => fsum (fun i => f i j) n + f n j) m
    rw [fsum_add]

/-- Sums are monotone in the terms (only the terms below the bound matter). -/
theorem fsum_le_fsum' {a b : Nat → R} {n : Nat} (h : ∀ k, k < n → a k ≤ b k) :
    fsum a n ≤ fsum b n := by
  induction n with
  | zero => show (0 : R) ≤ 0; grind
  | succ n ih =>
    rw [fsum_succ, fsum_succ]
    have := ih fun k hk => h k (by omega)
    have := h n (by omega); grind

/-- Sums of terms that are non-negative below the bound are non-negative. -/
theorem fsum_nonneg' {a : Nat → R} {n : Nat} (h : ∀ k, k < n → 0 ≤ a k) : 0 ≤ fsum a n := by
  have := fsum_le_fsum' (a := fun _ => (0 : R)) (b := a) h
  rw [fsum_zeros] at this; exact this

/-- **Picking out one term.** `Σ_{i<n} [i = c] a(i) = a(c)` if `c < n` (and `0` otherwise). -/
theorem fsum_ite_eq (c : Nat) (a : Nat → R) (n : Nat) :
    fsum (fun i => if i = c then a i else 0) n = if c < n then a c else 0 := by
  induction n with
  | zero => simp only [Nat.not_lt_zero, ↓reduceIte]; rfl
  | succ n ih =>
    rw [fsum_succ, ih]
    by_cases h1 : c < n
    · have h2 : c < n + 1 := by omega
      have h3 : ¬ n = c := by omega
      simp only [h1, h2, h3, ↓reduceIte]; grind
    · by_cases h3 : n = c
      · subst h3; simp only [h1, Nat.lt_add_one, ↓reduceIte]; grind
      · have h2 : ¬ c < n + 1 := by omega
        simp only [h1, h2, h3, ↓reduceIte]; grind

/-- If the terms vanish from `n` on, a longer sum equals the sum up to `n`. -/
theorem fsum_eq_of_vanish {a : Nat → R} {n m : Nat} (hnm : n ≤ m)
    (h : ∀ k, n ≤ k → k < m → a k = 0) : fsum a m = fsum a n := by
  induction m with
  | zero => obtain rfl : n = 0 := by omega
            rfl
  | succ m ih =>
    by_cases hm : n = m + 1
    · subst hm; rfl
    · rw [fsum_succ, ih (by omega) fun k h1 h2 => h k h1 (by omega), h m (by omega) (by omega)]
      grind

/-- Two sums with the same bound agree if their terms agree below the bound
(a version of `fsum_congr` for different bounds whose extra terms vanish). -/
theorem fsum_congr_bound {a : Nat → R} {n m : Nat} (hnm : n ≤ m)
    (h : ∀ k, n ≤ k → k < m → a k = 0) : fsum a n = fsum a m :=
  (fsum_eq_of_vanish hnm h).symm

/-- Splitting off the indicator of a condition. -/
theorem fsum_ite_add (P : Nat → Prop) [DecidablePred P] (a : Nat → R) (n : Nat) :
    fsum a n = fsum (fun k => if P k then a k else 0) n + fsum (fun k => if P k then 0 else a k) n := by
  rw [← fsum_add]
  apply fsum_congr; intro k _
  by_cases h : P k <;> simp only [h, ↓reduceIte] <;> grind

/-! ## Casting natural numbers into the reals -/

/-- `((a + b : ℕ) : R) = a + b`. -/
theorem natCast_add' (a b : Nat) : ((a + b : Nat) : R) = (a : R) + (b : R) := by grind

/-- `((a * b : ℕ) : R) = a · b`. -/
theorem natCast_mul' (a b : Nat) : ((a * b : Nat) : R) = (a : R) * (b : R) := by grind

/-- Natural numbers are non-negative reals. -/
theorem natCast_nonneg' (n : Nat) : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg

/-- The cast reflects order. -/
theorem natCast_le_iff {n m : Nat} : (n : R) ≤ (m : R) ↔ n ≤ m := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hnm
    have := natCast_le' (show m + 1 ≤ n by omega)
    have : ((m + 1 : Nat) : R) = (m : R) + 1 := by grind
    grind
  · exact natCast_le'

/-- `((a ^ k : ℕ) : R) = aᵏ`. -/
theorem natCast_pow' (a k : Nat) : ((a ^ k : Nat) : R) = (a : R) ^ k := by
  induction k with
  | zero => show ((1 : Nat) : R) = 1; grind
  | succ k ih =>
    rw [Nat.pow_succ]
    show ((a ^ k * a : Nat) : R) = (a : R) ^ k * (a : R)
    rw [natCast_mul', ih]

/-- **Counting multiples.** For `d ≥ 1`, the number of `m` with `1 ≤ m ≤ N` and `d ∣ m` is
`⌊N/d⌋`. -/
theorem fsum_count_multiples {d : Nat} (hd : 0 < d) (N : Nat) :
    fsum (fun m => if 1 ≤ m ∧ d ∣ m then (1 : R) else 0) (N + 1) = ((N / d : Nat) : R) := by
  induction N with
  | zero =>
    rw [fsum_succ]; simp only [Nat.le_zero, Nat.one_ne_zero, false_and, ↓reduceIte, Nat.zero_div]
    show (0 : R) + 0 = ((0 : Nat) : R); grind
  | succ N ih =>
    rw [fsum_succ, ih, succ_div_eq hd]
    by_cases h : d ∣ N + 1
    · simp only [h, and_true, show 1 ≤ N + 1 by omega, ↓reduceIte]; grind
    · simp only [h, and_false, ↓reduceIte]; grind

/-! ## Logarithms -/

/-- `log y ≤ y − 1` for `y ≥ 1` (from `exp t ≥ 1 + t`). -/
theorem log_le_sub_one {y : R} (hy : 1 ≤ y) : R.log y ≤ y - 1 := by
  have h1 := one_add_le_exp (show (0 : R) ≤ y - 1 by grind)
  have h2 : exp (R.log y) = y := exp_log (by grind)
  apply Classical.byContradiction; intro h
  have := exp_strictMono (show y - 1 < R.log y by grind)
  grind

/-- `log y ≥ 0` for `y ≥ 1`. -/
theorem log_nonneg' {y : R} (hy : 1 ≤ y) : 0 ≤ R.log y := by
  have := log_le_log (show (0 : R) < 1 by grind) hy
  rw [R.log_one] at this; exact this

/-- `log y > 0` for `y > 1`. -/
theorem log_pos' {y : R} (hy : 1 < y) : 0 < R.log y := by
  have := R.log_strictMono (show (0 : R) < 1 by grind) hy
  rw [R.log_one] at this; exact this

/-- `1 ≤ n` as reals for natural `n ≥ 1`. -/
theorem one_le_natCast {n : Nat} (hn : 1 ≤ n) : (1 : R) ≤ (n : R) := by
  have := natCast_le' hn
  have e : ((1 : Nat) : R) = 1 := by grind
  grind

/-- `log n ≥ 0` for natural `n ≥ 1`. -/
theorem log_natCast_nonneg {n : Nat} (hn : 1 ≤ n) : 0 ≤ R.log (n : R) :=
  log_nonneg' (one_le_natCast hn)

/-- `log (x / y) = log x − log y` for `x, y > 0`. -/
theorem log_div' {x y : R} (hx : 0 < x) (hy : 0 < y) : R.log (x / y) = R.log x - R.log y := by
  have hq : 0 < x / y := div_pos hx hy
  have := R.log_mul hq hy
  have hy0 : y ≠ 0 := by grind
  have e : x / y * y = x := by grind
  rw [e] at this
  grind

/-- `log (xᵏ) = k log x` for `x > 0`. -/
theorem log_pow' {x : R} (hx : 0 < x) (k : Nat) : R.log (x ^ k) = (k : R) * R.log x :=
  (pow_pos_and_log_pow hx k).2

/-- The logarithm of a product of positive natural numbers is the sum of the logarithms. -/
theorem log_bprod {f : Nat → Nat} (hf : ∀ i, 0 < f i) :
    ∀ B, R.log (bprod f B : R) = fsum (fun i => R.log (f i : R)) B
  | 0 => by show R.log ((1 : Nat) : R) = 0; rw [show ((1 : Nat) : R) = 1 by grind, R.log_one]
  | B + 1 => by
    rw [fsum_succ, ← log_bprod hf B]
    show R.log ((bprod f B * f B : Nat) : R) = _
    rw [natCast_mul', R.log_mul (natCast_pos' (bprod_pos hf B)) (natCast_pos' (hf B))]

/-- `log` of a natural number is at most the number itself. -/
theorem log_natCast_le {n : Nat} (hn : 1 ≤ n) : R.log (n : R) ≤ (n : R) := by
  have := log_le_sub_one (one_le_natCast hn)
  grind

/-! ## Crude Stirling bounds -/

/-- `n! ≤ nⁿ`. -/
theorem fact_le_pow (n : Nat) : Arith.fact n ≤ n ^ n := by
  have key : ∀ k, k ≤ n → Arith.fact k ≤ n ^ k := by
    intro k
    induction k with
    | zero => intro _; simp [Arith.fact]
    | succ k ih =>
      intro hk
      simp only [Arith.fact, Nat.pow_succ]
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul (ih (by omega)) hk
  exact key n (Nat.le_refl n)

/-- The two factorials of the development agree. -/
theorem arith_fact_eq (n : Nat) : Arith.fact n = R.fact n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Arith.fact, R.fact, ih]

/-- **Upper Stirling bound.** `log n! ≤ n log n`. -/
theorem log_fact_le (n : Nat) : R.log (Arith.fact n : R) ≤ (n : R) * R.log (n : R) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · show R.log ((1 : Nat) : R) ≤ _; rw [show ((1 : Nat) : R) = 1 by grind, R.log_one]; grind
  · have := log_ineq_of_pow_le (a := Arith.fact n) (b := n) (k := 1) (l := n) (Arith.fact_pos n) hn
      (by rw [Nat.pow_one]; exact fact_le_pow n)
    grind

/-- `nⁿ / n! ≤ eⁿ`: the `n`-th term of the series for `eⁿ` is at most its sum. -/
theorem pow_div_fact_le_exp (n : Nat) : (n : R) ^ n / (R.fact n : R) ≤ exp (n : R) := by
  have h := fsum_le_of_hasSum (fun k => expTerm_nonneg (natCast_nonneg' n) k) (hasSum_exp (n : R))
    (n + 1)
  have hle : expTerm (n : R) n ≤ fsum (expTerm (n : R)) (n + 1) := by
    rw [fsum_succ]
    have := fsum_nonneg (fun k => expTerm_nonneg (natCast_nonneg' n) k) n
    grind
  exact Std.le_trans hle h

/-- **Lower Stirling bound.** `n log n − n ≤ log n!`. -/
theorem log_fact_ge (n : Nat) : (n : R) * R.log (n : R) - (n : R) ≤ R.log (Arith.fact n : R) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · show _ ≤ R.log ((1 : Nat) : R)
    rw [show ((1 : Nat) : R) = 1 by grind, R.log_one]
    show ((0 : Nat) : R) * _ - ((0 : Nat) : R) ≤ 0; grind
  · have hf : (0 : R) < (Arith.fact n : R) := natCast_pos' (Arith.fact_pos n)
    have hp : (0 : R) < (n : R) ^ n := (pow_pos_and_log_pow (natCast_pos' hn) n).1
    have h := pow_div_fact_le_exp n
    rw [← arith_fact_eq] at h
    have hq : 0 < (n : R) ^ n / (Arith.fact n : R) := div_pos hp hf
    have := log_le_log hq h
    rw [log_exp, log_div' hp hf, log_pow' (natCast_pos' hn)] at this
    grind

end Foundations.NumberTheory.PNT
