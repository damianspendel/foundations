import Foundations.Numbers.Derivative

/-!
# Analysis on the reals IV: infinite series

An infinite sum `a₀ + a₁ + a₂ + ⋯` is not a sum at all but a *limit*: the limit of the partial
sums `a₀ + ⋯ + aₙ₋₁`. Zeno's paradox of Achilles and the tortoise — infinitely many steps
completed in finite time — dissolves once `1/2 + 1/4 + 1/8 + ⋯ = 1` is read in this way.

This file first records how limits interact with the field operations, then develops the basic
theory of series:

* the **geometric series** `Σ rⁿ = 1/(1 − r)` for `|r| < 1`;
* the **comparison test**: a series of non-negative terms dominated by a convergent one converges;
* **absolute convergence implies convergence** — this is where the completeness of ℝ (in the form
  "Cauchy sequences converge") enters;
* the **ratio test**: if eventually `|aₙ₊₁| ≤ q |aₙ|` with `q < 1`, the series converges
  absolutely.

These are exactly the tools needed in the next file to define the exponential function by its
power series.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-! ## Limits and the field operations -/

/-- A constant sequence converges to its value. -/
theorem tendsto_const (c : R) : Tendsto (fun _ => c) c := fun ε hε =>
  ⟨0, fun n _ => by simp only; rw [show c - c = 0 by grind, abs_zero]; exact hε⟩

/-- Changing finitely many terms does not affect convergence: if `a` and `b` agree from some
index on, they have the same limits. -/
theorem Tendsto.congr_eventually {a b : Nat → R} {L : R} (h : Tendsto a L) (N : Nat)
    (hab : ∀ n, N ≤ n → a n = b n) : Tendsto b L := fun ε hε => by
  obtain ⟨M, hM⟩ := h ε hε
  exact ⟨max M N, fun n hn => by rw [← hab n (by omega)]; exact hM n (by omega)⟩

/-- A sequence converges if one of its tails does. -/
theorem Tendsto.of_shift {a : Nat → R} {L : R} (N : Nat) (h : Tendsto (fun n => a (N + n)) L) :
    Tendsto a L := fun ε hε => by
  obtain ⟨M, hM⟩ := h ε hε
  refine ⟨N + M, fun n hn => ?_⟩
  have : abs (a (N + (n - N)) - L) < ε := hM (n - N) (by omega)
  rw [show N + (n - N) = n by omega] at this
  exact this

/-- Every tail of a convergent sequence converges to the same limit. -/
theorem Tendsto.shift {a : Nat → R} {L : R} (N : Nat) (h : Tendsto a L) :
    Tendsto (fun n => a (N + n)) L := fun ε hε => by
  obtain ⟨M, hM⟩ := h ε hε
  exact ⟨M, fun n hn => hM (N + n) (by omega)⟩

/-- **Limit of a sum** is the sum of the limits. -/
theorem Tendsto.add {a b : Nat → R} {L M : R} (ha : Tendsto a L) (hb : Tendsto b M) :
    Tendsto (fun n => a n + b n) (L + M) := fun ε hε => by
  obtain ⟨N₁, h₁⟩ := ha (ε / 2) (by grind)
  obtain ⟨N₂, h₂⟩ := hb (ε / 2) (by grind)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have k1 := h₁ n (by omega)
  have k2 := h₂ n (by omega)
  have k3 := abs_add (a n - L) (b n - M)
  rw [show a n - L + (b n - M) = a n + b n - (L + M) by grind] at k3
  grind

/-- **Limit of a constant multiple.** -/
theorem Tendsto.const_mul (c : R) {a : Nat → R} {L : R} (ha : Tendsto a L) :
    Tendsto (fun n => c * a n) (c * L) := fun ε hε => by
  obtain ⟨η, hη, hηc⟩ := exists_mul_le c (by grind : 0 < ε / 2)
  obtain ⟨N, hN⟩ := ha η hη
  refine ⟨N, fun n hn => ?_⟩
  rw [show c * a n - c * L = c * (a n - L) by grind, abs_mul]
  have := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt (hN n hn)) (abs_nonneg c)
  grind

/-- **Limit of a difference.** -/
theorem Tendsto.sub {a b : Nat → R} {L M : R} (ha : Tendsto a L) (hb : Tendsto b M) :
    Tendsto (fun n => a n - b n) (L - M) := by
  have := ha.add (hb.const_mul (-1))
  simp only [show ∀ s t : R, s + -1 * t = s - t from fun s t => by grind] at this
  exact this

/-- Limits preserve `≤` between sequences. -/
theorem le_of_tendsto_of_tendsto {a b : Nat → R} {L M : R} (ha : Tendsto a L) (hb : Tendsto b M)
    (h : ∀ n, a n ≤ b n) : L ≤ M := by
  have := le_of_tendsto (hb.sub ha) (c := 0) fun n => by have := h n; grind
  grind

/-- **Squeeze.** If `|aₙ − L| ≤ bₙ` and `bₙ → 0`, then `aₙ → L`. -/
theorem tendsto_of_abs_le {a b : Nat → R} {L : R} (hb : Tendsto b 0)
    (h : ∀ n, abs (a n - L) ≤ b n) : Tendsto a L := fun ε hε => by
  obtain ⟨N, hN⟩ := hb ε hε
  refine ⟨N, fun n hn => ?_⟩
  have := abs_lt.1 (hN n hn)
  have := h n
  grind

/-- The terms of an increasing sequence lie below its limit. -/
theorem le_lim_of_mono {a : Nat → R} {L : R} (hmono : ∀ n, a n ≤ a (n + 1)) (h : Tendsto a L)
    (n : Nat) : a n ≤ L :=
  le_of_tendsto (h.shift n) fun k => mono_le hmono (by omega)

/-! ## Finite sums -/

/-- Defining equation of finite sums. -/
theorem fsum_succ (a : Nat → R) (n : Nat) : fsum a (n + 1) = fsum a n + a n := rfl

/-- The empty sum is `0`. -/
theorem fsum_zero (a : Nat → R) : fsum a 0 = 0 := rfl

/-- Finite sums are additive. -/
theorem fsum_add (a b : Nat → R) (n : Nat) :
    fsum (fun k => a k + b k) n = fsum a n + fsum b n := by
  induction n with
  | zero => show (0 : R) = 0 + 0; grind
  | succ n ih => rw [fsum_succ, fsum_succ, fsum_succ, ih]; grind

/-- Finite sums commute with constant multiples. -/
theorem fsum_const_mul (c : R) (a : Nat → R) (n : Nat) :
    fsum (fun k => c * a k) n = c * fsum a n := by
  induction n with
  | zero => show (0 : R) = c * 0; grind
  | succ n ih => rw [fsum_succ, fsum_succ, ih]; grind

/-- Finite sums of differences. -/
theorem fsum_sub (a b : Nat → R) (n : Nat) :
    fsum (fun k => a k - b k) n = fsum a n - fsum b n := by
  induction n with
  | zero => show (0 : R) = 0 - 0; grind
  | succ n ih => rw [fsum_succ, fsum_succ, fsum_succ, ih]; grind

/-- Sums of termwise equal sequences agree. -/
theorem fsum_congr {a b : Nat → R} {n : Nat} (h : ∀ k, k < n → a k = b k) : fsum a n = fsum b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fsum_succ, fsum_succ, ih fun k hk => h k (by omega), h n (by omega)]

/-- Splitting off the first term: `Σ_{k<n+1} aₖ = a₀ + Σ_{k<n} aₖ₊₁`. -/
theorem fsum_succ' (a : Nat → R) (n : Nat) :
    fsum a (n + 1) = a 0 + fsum (fun k => a (k + 1)) n := by
  induction n with
  | zero => show (0 : R) + a 0 = a 0 + 0; grind
  | succ n ih => rw [fsum_succ, ih, fsum_succ]; grind

/-- Splitting a sum: `Σ_{k<m+n} aₖ = Σ_{k<m} aₖ + Σ_{k<n} aₘ₊ₖ`. -/
theorem fsum_split (a : Nat → R) (m n : Nat) :
    fsum a (m + n) = fsum a m + fsum (fun k => a (m + k)) n := by
  induction n with
  | zero => show fsum a m = fsum a m + 0; grind
  | succ n ih => rw [← Nat.add_assoc, fsum_succ, ih, fsum_succ]; grind

/-- Sums of non-negative terms are non-negative. -/
theorem fsum_nonneg {a : Nat → R} (h : ∀ k, 0 ≤ a k) (n : Nat) : 0 ≤ fsum a n := by
  induction n with
  | zero => show (0 : R) ≤ 0; grind
  | succ n ih => rw [fsum_succ]; have := h n; grind

/-- Sums are monotone in the terms. -/
theorem fsum_le_fsum {a b : Nat → R} (h : ∀ k, a k ≤ b k) (n : Nat) : fsum a n ≤ fsum b n := by
  induction n with
  | zero => show (0 : R) ≤ 0; grind
  | succ n ih => rw [fsum_succ, fsum_succ]; have := h n; grind

/-- **Triangle inequality for finite sums.** -/
theorem abs_fsum_le (a : Nat → R) (n : Nat) : abs (fsum a n) ≤ fsum (fun k => abs (a k)) n := by
  induction n with
  | zero => show abs (0 : R) ≤ 0; rw [abs_zero]; grind
  | succ n ih => rw [fsum_succ, fsum_succ]; have := abs_add (fsum a n) (a n); grind

/-- Partial sums of non-negative terms increase. -/
theorem fsum_mono {a : Nat → R} (h : ∀ k, 0 ≤ a k) {m n : Nat} (hmn : m ≤ n) :
    fsum a m ≤ fsum a n :=
  mono_le (a := fsum a) (fun n => by rw [fsum_succ]; have := h n; grind) hmn

/-! ## Series -/

/-- The series `Σ aₙ` **has sum `s`**: its partial sums `a₀ + ⋯ + aₙ₋₁` converge to `s`. -/
def HasSum (a : Nat → R) (s : R) : Prop := Tendsto (fsum a) s

/-- The series `Σ aₙ` **converges** (to some sum). -/
def Summable (a : Nat → R) : Prop := ∃ s, HasSum a s

/-- A series has at most one sum. -/
theorem HasSum.unique {a : Nat → R} {s t : R} (hs : HasSum a s) (ht : HasSum a t) : s = t :=
  tendsto_unique hs ht

/-- Sums of series add. -/
theorem HasSum.add {a b : Nat → R} {s t : R} (ha : HasSum a s) (hb : HasSum b t) :
    HasSum (fun n => a n + b n) (s + t) := by
  exact (Tendsto.add ha hb).congr_eventually 0 fun n _ => (fsum_add a b n).symm

/-- Sums of series subtract. -/
theorem HasSum.sub {a b : Nat → R} {s t : R} (ha : HasSum a s) (hb : HasSum b t) :
    HasSum (fun n => a n - b n) (s - t) := by
  exact (Tendsto.sub ha hb).congr_eventually 0 fun n _ => (fsum_sub a b n).symm

/-- Constant multiples of series. -/
theorem HasSum.const_mul (c : R) {a : Nat → R} {s : R} (ha : HasSum a s) :
    HasSum (fun n => c * a n) (c * s) := by
  exact (Tendsto.const_mul c ha).congr_eventually 0 fun n _ => (fsum_const_mul c a n).symm

/-- Termwise equal series have the same sums. -/
theorem HasSum.congr {a b : Nat → R} {s : R} (ha : HasSum a s) (h : ∀ n, a n = b n) :
    HasSum b s := by
  have : a = b := funext h
  exact this ▸ ha

/-- Dropping the first term: `Σ aₙ = s` iff `Σ aₙ₊₁ = s − a₀`. -/
theorem hasSum_succ_iff {a : Nat → R} {s : R} :
    HasSum (fun n => a (n + 1)) (s - a 0) ↔ HasSum a s := by
  constructor
  · intro h
    have h2 := (Tendsto.add (tendsto_const (a 0)) h).congr_eventually 0 (b := fun n => fsum a (n + 1))
      (fun n _ => (fsum_succ' a n).symm)
    rw [show a 0 + (s - a 0) = s by grind] at h2
    exact Tendsto.of_shift 1 (h2.congr_eventually 0 fun n _ => by rw [Nat.add_comm])
  · intro h
    have h2 := (Tendsto.sub (h.shift 1) (tendsto_const (a 0)))
    refine h2.congr_eventually 0 fun n _ => ?_
    show fsum a (1 + n) - a 0 = fsum (fun k => a (k + 1)) n
    rw [Nat.add_comm 1 n, fsum_succ']; grind

/-- Dropping the first `N` terms: `Σ aₙ = s` iff `Σ aₙ₊ₖ = s − (a₀ + ⋯ + a_{N−1})`. -/
theorem hasSum_shift_iff {a : Nat → R} {s : R} (N : Nat) :
    HasSum (fun n => a (N + n)) (s - fsum a N) ↔ HasSum a s := by
  constructor
  · intro h
    have h2 := Tendsto.add (tendsto_const (fsum a N)) h
    rw [show fsum a N + (s - fsum a N) = s by grind] at h2
    exact Tendsto.of_shift N (h2.congr_eventually 0 fun n _ => (fsum_split a N n).symm)
  · intro h
    exact (Tendsto.sub (h.shift N) (tendsto_const (fsum a N))).congr_eventually 0 fun n _ => by
      show fsum a (N + n) - fsum a N = fsum (fun k => a (N + k)) n
      rw [fsum_split]; grind

/-- The partial sums of a series of non-negative terms lie below its sum. -/
theorem fsum_le_of_hasSum {a : Nat → R} {s : R} (hpos : ∀ n, 0 ≤ a n) (h : HasSum a s)
    (n : Nat) : fsum a n ≤ s :=
  le_lim_of_mono (fun n => by rw [fsum_succ]; have := hpos n; grind) h n

/-- The sum of a series of non-negative terms is non-negative. -/
theorem hasSum_nonneg {a : Nat → R} {s : R} (hpos : ∀ n, 0 ≤ a n) (h : HasSum a s) : 0 ≤ s :=
  le_of_tendsto h (fsum_nonneg hpos)

/-- **Bounded series of non-negative terms converge** (monotone convergence for series). -/
theorem summable_of_bounded {a : Nat → R} (hpos : ∀ n, 0 ≤ a n) {B : R}
    (hB : ∀ n, fsum a n ≤ B) : ∃ s, HasSum a s ∧ s ≤ B := by
  obtain ⟨s, hs⟩ := monotone_convergence (a := fsum a)
    (fun n => by rw [fsum_succ]; have := hpos n; grind) ⟨B, hB⟩
  exact ⟨s, hs, tendsto_le hs hB⟩

/-- **Comparison test.** If `0 ≤ aₙ ≤ bₙ` and `Σ bₙ = t`, then `Σ aₙ` converges, to a sum
`≤ t`. -/
theorem comparison {a b : Nat → R} {t : R} (hpos : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n)
    (hb : HasSum b t) : ∃ s, HasSum a s ∧ s ≤ t :=
  summable_of_bounded hpos fun n =>
    Std.le_trans (fsum_le_fsum hab n) (fsum_le_of_hasSum (fun k => Std.le_trans (hpos k) (hab k)) hb n)

/-- Comparison of sums: `|aₙ| ≤ bₙ` gives `|Σ aₙ| ≤ Σ bₙ`. -/
theorem abs_hasSum_le {a b : Nat → R} {s t : R} (hab : ∀ n, abs (a n) ≤ b n) (ha : HasSum a s)
    (hb : HasSum b t) : abs s ≤ t := by
  have k : ∀ n, abs (fsum a n) ≤ fsum b n := fun n =>
    Std.le_trans (abs_fsum_le a n) (fsum_le_fsum hab n)
  have h1 := le_of_tendsto_of_tendsto ha hb fun n => (abs_le.1 (k n)).2
  have h2 := le_of_tendsto_of_tendsto (Tendsto.const_mul (-1) (hb : Tendsto (fsum b) t)) ha fun n => by
    have := (abs_le.1 (k n)).1; grind
  exact abs_le.2 ⟨by grind, h1⟩

/-- A convergent sequence is Cauchy. -/
theorem Tendsto.isCauchySeq {a : Nat → R} {L : R} (h : Tendsto a L) : IsCauchySeq a :=
  fun ε hε => by
  obtain ⟨N, hN⟩ := h (ε / 2) (by grind)
  refine ⟨N, fun m n hm hn => ?_⟩
  have k1 := hN m hm
  have k2 := hN n hn
  rw [abs_sub_comm] at k2
  have k3 := abs_add (a m - L) (L - a n)
  rw [show a m - L + (L - a n) = a m - a n by grind] at k3
  grind

/-- **Absolute convergence implies convergence.** If `Σ |aₙ|` converges, so does `Σ aₙ`, and
`|Σ aₙ| ≤ Σ |aₙ|`. -/
theorem summable_of_abs {a : Nat → R} {t : R} (h : HasSum (fun n => abs (a n)) t) :
    ∃ s, HasSum a s ∧ abs s ≤ t := by
  have hc := h.isCauchySeq
  have key : ∀ m k, abs (fsum a (m + k) - fsum a m) ≤
      fsum (fun n => abs (a n)) (m + k) - fsum (fun n => abs (a n)) m := fun m k => by
    rw [fsum_split, fsum_split (fun n => abs (a n))]
    have := abs_fsum_le (fun n => a (m + n)) k
    rw [show fsum a m + fsum (fun n => a (m + n)) k - fsum a m = fsum (fun n => a (m + n)) k by grind]
    grind
  have hcs : IsCauchySeq (fsum a) := fun ε hε => by
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    rcases (by omega : m ≤ n ∨ n ≤ m) with h' | h'
    · obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
      have := abs_le.1 (key m k)
      have := (abs_lt.1 (hN (m + k) m hn hm)).2
      rw [abs_sub_comm]
      exact abs_lt.2 ⟨by grind, by grind⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
      have := abs_le.1 (key n k)
      have := (abs_lt.1 (hN (n + k) n hm hn)).2
      exact abs_lt.2 ⟨by grind, by grind⟩
  obtain ⟨s, hs⟩ := cauchy_complete hcs
  exact ⟨s, hs, abs_hasSum_le (fun n => Std.le_refl _) hs h⟩

/-! ## The geometric series -/

/-- Powers of a number in `[0, 1)` tend to `0`. -/
theorem tendsto_pow_zero {r : R} (h0 : 0 ≤ r) (h1 : r < 1) : Tendsto (fun n => r ^ n) 0 := by
  -- The powers decrease and are bounded below, so they converge, say to `L`; then `L = r L`.
  have hnn : ∀ n : Nat, 0 ≤ r ^ n := by
    intro n
    induction n with
    | zero => show (0 : R) ≤ 1; grind
    | succ n ih => rw [pow_succ']; exact OrderedRing.mul_nonneg ih h0
  have hdec : ∀ n : Nat, r ^ (n + 1) ≤ r ^ n := fun n => by
    rw [pow_succ']
    have := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt h1) (hnn n)
    grind
  obtain ⟨L, hL⟩ := monotone_convergence (a := fun n => -r ^ n) (fun n => by
    have := hdec n; show -r ^ n ≤ -r ^ (n + 1); grind) ⟨0, fun n => by
      have := hnn n; show -r ^ n ≤ 0; grind⟩
  have hL' : Tendsto (fun n => r ^ n) (-L) := by
    have := hL.const_mul (-1)
    rw [show -1 * L = -L by grind] at this
    exact this.congr_eventually 0 fun n _ => by show -1 * -r ^ n = r ^ n; grind
  have h2 : Tendsto (fun n => r ^ (1 + n)) (r * -L) := by
    have := hL'.const_mul r
    exact this.congr_eventually 0 fun n _ => by
      show r * r ^ n = r ^ (1 + n); rw [Nat.add_comm, pow_succ']; grind
  have := tendsto_unique (hL'.shift 1) h2
  have : -L = 0 := by
    have hr : (1 - r) * -L = 0 := by grind
    have hne : 1 - r ≠ 0 := by grind
    have : (1 - r)⁻¹ * ((1 - r) * -L) = -L := by grind
    grind
  rw [this] at hL'; exact hL'

/-- `|xⁿ| = |x|ⁿ`. -/
theorem abs_pow (x : R) (n : Nat) : abs (x ^ n) = abs x ^ n := by
  induction n with
  | zero => show abs (1 : R) = 1; exact abs_of_nonneg (by grind)
  | succ n ih => rw [pow_succ', pow_succ', abs_mul, ih]

/-- **Geometric series.** For `|r| < 1`, `Σ rⁿ = 1 / (1 − r)`. -/
theorem hasSum_geometric {r : R} (hr : abs r < 1) : HasSum (fun n => r ^ n) (1 / (1 - r)) := by
  have hr' := abs_lt.1 hr
  have hne : 1 - r ≠ 0 := by grind
  have hsum : ∀ n : Nat, fsum (fun k => r ^ k) n = (1 - r ^ n) * (1 / (1 - r)) := by
    intro n
    induction n with
    | zero => show (0 : R) = (1 - 1) * (1 / (1 - r)); grind
    | succ n ih =>
      rw [fsum_succ, ih, pow_succ']
      have e : (1 - r) * (1 / (1 - r)) = 1 := by grind
      grind
  have hz : Tendsto (fun n => abs (r ^ n)) 0 := by
    have := tendsto_pow_zero (abs_nonneg r) hr
    exact this.congr_eventually 0 fun n _ => (abs_pow r n).symm
  have hz' : Tendsto (fun n => r ^ n) 0 := tendsto_of_abs_le hz fun n => by
    rw [show r ^ n - 0 = r ^ n by grind]; exact Std.le_refl _
  have := (Tendsto.sub (tendsto_const 1) hz').const_mul (1 / (1 - r))
  rw [show 1 / (1 - r) * (1 - 0) = 1 / (1 - r) by grind] at this
  refine this.congr_eventually 0 fun n _ => ?_
  show 1 / (1 - r) * (1 - r ^ n) = fsum (fun k => r ^ k) n
  rw [hsum]; grind

/-! ## The ratio test -/

/-- **Ratio test.** If from some index `N` on `|aₙ₊₁| ≤ q |aₙ|` with `0 ≤ q < 1`, then `Σ |aₙ|`
converges (and hence so does `Σ aₙ`). -/
theorem ratio_test {a : Nat → R} {q : R} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : Nat)
    (h : ∀ n, N ≤ n → abs (a (n + 1)) ≤ q * abs (a n)) :
    ∃ t, HasSum (fun n => abs (a n)) t := by
  -- The tail from `N` on is dominated by the geometric series `|a_N| · Σ qᵏ`.
  have hdom : ∀ k, abs (a (N + k)) ≤ abs (a N) * q ^ k := fun k => by
    induction k with
    | zero => show abs (a (N + 0)) ≤ abs (a N) * 1; grind
    | succ k ih =>
      rw [← Nat.add_assoc, pow_succ']
      have := h (N + k) (by omega)
      have := OrderedRing.mul_le_mul_of_nonneg_left ih hq0
      grind
  have hgeo := (hasSum_geometric (r := q) (by rw [abs_of_nonneg hq0]; exact hq1)).const_mul
    (abs (a N))
  obtain ⟨s, hs, -⟩ := comparison (a := fun k => abs (a (N + k))) (fun k => abs_nonneg _) hdom hgeo
  refine ⟨s + fsum (fun n => abs (a n)) N, ?_⟩
  apply (hasSum_shift_iff N).1
  rw [show s + fsum (fun n => abs (a n)) N - fsum (fun n => abs (a n)) N = s by grind]
  exact hs

end R

end Foundations.Numbers
