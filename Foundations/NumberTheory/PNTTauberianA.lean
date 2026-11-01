import Foundations.NumberTheory.PNTIterated

/-!
# Toward the prime number theorem XII: where the remainder is small

Write `V(n) = R(n)/n = ψ(n)/n − 1`; the prime number theorem says `V(n) → 0`. The tauberian
argument needs to know that `V` is small on *many* `n` — enough of them, measured
logarithmically, to pull the weighted average of the previous file strictly below its maximum.
This file proves the decisive qualitative fact:

  for every `ε > 0` there are `K` and `T` such that every interval `(y, Ky]` with `y` large
  contains an `m` with `|V(n)| ≤ ε/2` for **all** `n ∈ [m, m + m/T]`.

Three ingredients combine:

* **`V` changes sign.** The mean value `|Σ_{n ≤ N} R(n)/(n(n+1))| ≤ B` (in the form
  `Σ V(n)/(n+1)`) forbids `V > ε/4` throughout `(y, Ky]` once `log K` is large, because
  `Σ_{y < n ≤ Ky} 1/(n+1) ≈ log K`; likewise `V < −ε/4` is forbidden.
* **`V` moves in small steps.** `V(n+1) − V(n) = (Λ(n+1) − 1 − V(n))/(n+1)` is `O(log n / n)`,
  so a discrete intermediate value argument finds `m` with `|V(m)| ≤ ε/4`.
* **`V` is almost Lipschitz on the logarithmic scale.** By the short-interval bound,
  `|V(n) − V(m)| ≤ (5 + C₀)(n − m)/n + 2 KA / log m` for `m ≤ n ≤ 2m`; so `V` stays below `ε/2`
  on `[m, m + m/T]` when `T` is large.

This is the elementary substitute for the observation, in the analytic proofs, that `ζ` has no
zero on the line `Re s = 1`: the primes cannot conspire to keep `ψ(x)/x` away from `1` for long
stretches.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- The normalised remainder `V(n) = R(n)/n = ψ(n)/n − 1`. -/
noncomputable def vrem (n : Nat) : R := rem n / (n : R)

/-- The Chebyshev constant `C₀ = 1 + log 1024` bounding `|V|`. -/
noncomputable def C0 : R := 1 + R.log 1024

/-- `C₀ ≥ 1`. -/
theorem one_le_C0 : 1 ≤ C0 := by unfold C0; have := log1024_nonneg; grind

/-- `R(n) = n V(n)` for `n ≥ 1`. -/
theorem rem_eq_mul {n : Nat} (hn : 1 ≤ n) : rem n = (n : R) * vrem n := by
  unfold vrem
  have h0 : (0 : R) < (n : R) := natCast_pos' hn
  have : (n : R) ≠ 0 := by grind
  grind

/-- `|V(n)| ≤ C₀`. -/
theorem abs_vrem_le (n : Nat) : abs (vrem n) ≤ C0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold vrem; rw [rem_zero, show (0 : R) / ((0 : Nat) : R) = 0 by grind, abs_zero]
    have := one_le_C0; grind
  · have h := abs_rem_le n
    rw [rem_eq_mul hn, abs_mul, abs_of_nonneg (natCast_nonneg' n)] at h
    have hn0 : (0 : R) < (n : R) := natCast_pos' hn
    unfold C0
    exact le_of_mul_le_mul_right' (C := (n : R)) (by grind) hn0

/-- `Λ(n) ≤ log n` for `n ≥ 1` (a term of `Σ_{d ∣ n} Λ(d) = log n`). -/
theorem vonMangoldt_le_log {n : Nat} (hn : 1 ≤ n) : vonMangoldt n ≤ R.log (n : R) := by
  rw [← dsum_vonMangoldt hn]; unfold dsum
  rw [fsum_succ]; simp only [Nat.dvd_refl, ↓reduceIte]
  have h0 : ∀ d, 0 ≤ (if d ∣ n then vonMangoldt d else 0) := by
    intro d; split
    · exact vonMangoldt_nonneg d
    · grind
  have := fsum_nonneg h0 n
  grind

/-- `ψ` is non-decreasing. -/
theorem psi_mono {m n : Nat} (h : m ≤ n) : psi m ≤ psi n := by
  rw [psi_eq_sum_vonMangoldt, psi_eq_sum_vonMangoldt]
  exact fsum_mono vonMangoldt_nonneg (by omega)

/-- **Small steps.** `|V(n+1) − V(n)| · (n+1) ≤ log(n+1) + 1 + C₀` for `n ≥ 1`. -/
theorem vrem_step {n : Nat} (hn : 1 ≤ n) :
    abs (vrem (n + 1) - vrem n) * ((n : R) + 1) ≤ R.log ((n + 1 : Nat) : R) + 1 + C0 := by
  have hv : (0 : R) < (n : R) + 1 := by have := natCast_nonneg' n; grind
  have hr : rem (n + 1) = rem n + vonMangoldt (n + 1) - 1 := by
    unfold rem
    rw [psi_eq_sum_vonMangoldt, psi_eq_sum_vonMangoldt, fsum_succ (n := n + 1)]
    rw [show ((n + 1 : Nat) : R) = (n : R) + 1 by grind]; grind
  have e : (vrem (n + 1) - vrem n) * ((n : R) + 1) = vonMangoldt (n + 1) - 1 - vrem n := by
    have h1 := rem_eq_mul (n := n + 1) (by omega)
    have h2 := rem_eq_mul hn
    rw [show ((n + 1 : Nat) : R) = (n : R) + 1 by grind] at h1
    rw [h1, h2] at hr
    grind
  rw [show abs (vrem (n + 1) - vrem n) * ((n : R) + 1) =
    abs ((vrem (n + 1) - vrem n) * ((n : R) + 1)) by
      rw [abs_mul, abs_of_nonneg (Std.le_of_lt hv)], e]
  have h1 := vonMangoldt_le_log (n := n + 1) (by omega)
  have h2 := vonMangoldt_nonneg (n + 1)
  have h3 := abs_vrem_le n
  have h4 := log_natCast_nonneg (n := n + 1) (by omega)
  rw [abs_le] at h3 ⊢; constructor <;> grind

/-- Eventually the steps of `V` are at most `η`. -/
theorem vrem_step_small {η : R} (hη : 0 < η) :
    ∃ n₀, ∀ n, n₀ ≤ n → abs (vrem (n + 1) - vrem n) ≤ η := by
  obtain ⟨T, hT, hTη⟩ := exists_nat_mul_ge 4 hη
  obtain ⟨M, hM, hMη⟩ := exists_nat_mul_ge (2 * (1 + C0)) hη
  refine ⟨T * T + M + 1, fun n hn => ?_⟩
  have hv : (0 : R) < (n : R) + 1 := by have := natCast_nonneg' n; grind
  have h := vrem_step (n := n) (by omega)
  have hl := log_mul_le hT (show T * T ≤ n + 1 by omega)
  rw [show ((n + 1 : Nat) : R) = (n : R) + 1 by grind] at hl h
  have hT0 : (0 : R) < (T : R) := natCast_pos' hT
  -- `log(n+1) ≤ (η/2)(n+1)` and `1 + C₀ ≤ (η/2)(n+1)`.
  have k1 : R.log ((n : R) + 1) ≤ η / 2 * ((n : R) + 1) := by
    apply le_of_mul_le_mul_right' (C := (T : R)) _ hT0
    have := OrderedRing.mul_le_mul_of_nonneg_left hTη (Std.le_of_lt hv)
    grind
  have k2 : 1 + C0 ≤ η / 2 * ((n : R) + 1) := by
    have : (M : R) ≤ (n : R) + 1 := by
      have : (M : R) ≤ (n : R) := natCast_le' (show M ≤ n by omega)
      grind
    have := OrderedRing.mul_le_mul_of_nonneg_left this (Std.le_of_lt hη)
    grind
  exact le_of_mul_le_mul_right' (C := (n : R) + 1) (by grind) hv

/-- **Almost Lipschitz.** For `m ≤ n ≤ 2m` with `log m ≥ 1`:
`|V(n) − V(m)| ≤ (5 + C₀)(n − m)/n + 2 KA / log m`. -/
theorem vrem_lipschitz {m n : Nat} (hm : 1 ≤ m) (hlm : 1 ≤ R.log (m : R)) (hmn : m ≤ n)
    (hn2 : n ≤ 2 * m) :
    abs (vrem n - vrem m) ≤ (5 + C0) * (((n : R) - (m : R)) / (n : R)) +
      2 * KA / R.log (m : R) := by
  have hm0 : (0 : R) < (m : R) := natCast_pos' hm
  have hn0 : (0 : R) < (n : R) := natCast_pos' (by omega)
  have hl0 : (0 : R) < R.log (m : R) := by grind
  have hnm : (m : R) ≤ (n : R) := natCast_le' hmn
  -- `ψ(n) − ψ(m) ≤ 6(n − m) + 2 KA n / log m`.
  have hsi := psi_short_interval hm hmn
  have hln : R.log (n : R) ≤ R.log (m : R) + 1 := by
    have h1 := log_le_log hn0 (show (n : R) ≤ ((2 * m : Nat) : R) from natCast_le' hn2)
    rw [natCast_mul', R.log_mul (by grind) hm0] at h1
    have := log_le_sub_one (show (1 : R) ≤ ((2 : Nat) : R) by grind)
    grind
  have hD : psi n - psi m ≤ 6 * ((n : R) - (m : R)) + 2 * KA * (n : R) / R.log (m : R) := by
    apply le_of_mul_le_mul_right' (C := R.log (m : R)) _ hl0
    have e : (6 * ((n : R) - (m : R)) + 2 * KA * (n : R) / R.log (m : R)) * R.log (m : R) =
        6 * ((n : R) - (m : R)) * R.log (m : R) + 2 * KA * (n : R) := by
      have : R.log (m : R) ≠ 0 := by grind
      grind
    rw [e]
    have k1 := OrderedRing.mul_le_mul_of_nonneg_left hln (show 0 ≤ 2 * ((n : R) - (m : R)) by grind)
    have k2 := OrderedRing.mul_le_mul_of_nonneg_left hlm (show 0 ≤ 4 * ((n : R) - (m : R)) by grind)
    grind
  have hD0 := psi_mono hmn
  -- The identity `V(n) − V(m) = (D − (n − m) − (n − m) V(m))/n`.
  have e : vrem n - vrem m =
      ((psi n - psi m) - ((n : R) - (m : R)) - ((n : R) - (m : R)) * vrem m) / (n : R) := by
    unfold vrem rem
    have : (m : R) ≠ 0 := by grind
    have : (n : R) ≠ 0 := by grind
    grind
  rw [e]
  have hV := abs_vrem_le m
  have hk := OrderedRing.mul_le_mul_of_nonneg_left (show abs (vrem m) ≤ C0 from hV)
    (show 0 ≤ (n : R) - (m : R) by grind)
  have hX : 0 ≤ 2 * KA * (n : R) / R.log (m : R) := by
    have h1 := div_pos (show (0 : R) < 1 by grind) hl0
    have h2 : 0 ≤ 2 * KA * (n : R) :=
      OrderedRing.mul_nonneg (by have := KA_nonneg; grind) (Std.le_of_lt hn0)
    have := OrderedRing.mul_nonneg h2 (Std.le_of_lt h1)
    have e : 2 * KA * (n : R) / R.log (m : R) = 2 * KA * (n : R) * (1 / R.log (m : R)) := by grind
    rw [e]; exact this
  have hnum : abs ((psi n - psi m) - ((n : R) - (m : R)) - ((n : R) - (m : R)) * vrem m) ≤
      (5 + C0) * ((n : R) - (m : R)) + 2 * KA * (n : R) / R.log (m : R) := by
    have t1 := abs_add ((psi n - psi m) - ((n : R) - (m : R))) (-(((n : R) - (m : R)) * vrem m))
    rw [abs_neg, abs_mul, abs_of_nonneg (show 0 ≤ (n : R) - (m : R) by grind)] at t1
    have t2 : abs ((psi n - psi m) - ((n : R) - (m : R))) ≤
        5 * ((n : R) - (m : R)) + 2 * KA * (n : R) / R.log (m : R) := by
      rw [abs_le]; constructor <;> grind
    grind
  have hin : 0 < 1 / (n : R) := div_pos (by grind) hn0
  have e2 : ((psi n - psi m) - ((n : R) - (m : R)) - ((n : R) - (m : R)) * vrem m) / (n : R) =
      ((psi n - psi m) - ((n : R) - (m : R)) - ((n : R) - (m : R)) * vrem m) * (1 / (n : R)) := by
    grind
  rw [e2, abs_mul, abs_of_nonneg (Std.le_of_lt hin)]
  have := OrderedRing.mul_le_mul_of_nonneg_right hnum (Std.le_of_lt hin)
  have e3 : ((5 + C0) * ((n : R) - (m : R)) + 2 * KA * (n : R) / R.log (m : R)) * (1 / (n : R)) =
      (5 + C0) * (((n : R) - (m : R)) / (n : R)) + 2 * KA / R.log (m : R) := by
    have : (n : R) ≠ 0 := by grind
    have : R.log (m : R) ≠ 0 := by grind
    grind
  grind

/-! ## A discrete intermediate value theorem -/

/-- Upward crossing: if `f a < c ≤ f b` with `a ≤ b`, some `n ∈ (a, b]` has `f(n−1) < c ≤ f(n)`. -/
theorem ivt_up (f : Nat → R) (c : R) : ∀ b a, a ≤ b → f a < c → c ≤ f b →
    ∃ n, a < n ∧ n ≤ b ∧ f (n - 1) < c ∧ c ≤ f n
  | 0, a, hab, ha, hb => by obtain rfl : a = 0 := by omega
                            grind
  | b + 1, a, hab, ha, hb => by
    by_cases hab' : a = b + 1
    · subst hab'; grind
    · by_cases hfb : c ≤ f b
      · obtain ⟨n, h1, h2, h3, h4⟩ := ivt_up f c b a (by omega) ha hfb
        exact ⟨n, h1, by omega, h3, h4⟩
      · exact ⟨b + 1, by omega, Nat.le_refl _, by simp only [Nat.add_sub_cancel]; grind, hb⟩

/-- Downward crossing: if `c ≤ f a` and `f b < c` with `a ≤ b`, some `n ∈ [a, b)` has
`c ≤ f(n)` and `f(n+1) < c`. -/
theorem ivt_down (f : Nat → R) (c : R) : ∀ b a, a ≤ b → c ≤ f a → f b < c →
    ∃ n, a ≤ n ∧ n < b ∧ c ≤ f n ∧ f (n + 1) < c
  | 0, a, hab, ha, hb => by obtain rfl : a = 0 := by omega
                            grind
  | b + 1, a, hab, ha, hb => by
    by_cases hab' : a = b + 1
    · subst hab'; grind
    · by_cases hfb : f b < c
      · obtain ⟨n, h1, h2, h3, h4⟩ := ivt_down f c b a (by omega) ha hfb
        exact ⟨n, h1, by omega, h3, h4⟩
      · exact ⟨b, by omega, by omega, by grind, hb⟩

/-! ## `V` changes sign -/

/-- `R(n) · w(n) = V(n)/(n+1)` for `n ≥ 1`. -/
theorem rem_wt_eq {n : Nat} (hn : 1 ≤ n) : rem n * wt n = vrem n * (1 / ((n : R) + 1)) := by
  unfold wt vrem
  have h0 : (0 : R) < (n : R) := natCast_pos' hn
  have : (n : R) ≠ 0 := by grind
  have : (n : R) + 1 ≠ 0 := by grind
  grind

/-- The harmonic sum over `(y, Ky]` is at least `log K − 3` (for `y, K ≥ 1`). -/
theorem harmonic_block_ge {y K : Nat} (hy : 1 ≤ y) (hK : 1 ≤ K) :
    R.log (K : R) - 3 ≤ fsum (fun j => 1 / (((y + 1 + j : Nat) : R) + 1)) (K * y - y) := by
  have hKy : y ≤ K * y := Nat.le_mul_of_pos_left y (by omega)
  have e : fsum (fun j => 1 / (((y + 1 + j : Nat) : R) + 1)) (K * y - y) =
      harmonic (K * y + 1) - harmonic (y + 1) := by
    rw [harmonic_eq_shift, harmonic_eq_shift, show K * y + 1 = (y + 1) + (K * y - y) by omega,
      fsum_split]; grind
  rw [e]
  have h1 := harmonic_ge (N := K * y + 1) (by omega)
  have h2 := harmonic_le (N := y + 1) (by omega)
  have hy0 : (0 : R) < (y : R) := natCast_pos' hy
  have hK0 : (0 : R) < (K : R) := natCast_pos' hK
  have l1 : R.log (K : R) + R.log (y : R) ≤ R.log ((K * y + 1 : Nat) : R) := by
    rw [← R.log_mul hK0 hy0, ← natCast_mul']
    exact log_le_log (natCast_pos' (Nat.mul_pos hK hy)) (natCast_le' (by omega))
  have l2 : R.log ((y + 1 : Nat) : R) ≤ R.log (y : R) + 1 := by
    have := (log_succ_sub_bounds hy).1
    have := OrderedRing.mul_le_mul_of_nonneg_right (one_le_natCast hy)
      (show 0 ≤ R.log ((y + 1 : Nat) : R) - R.log (y : R) by
        have := log_le_log hy0 (natCast_le' (show y ≤ y + 1 by omega)); grind)
    grind
  grind

/-- **No long runs of one sign.** If `η (log K − 3) > 2B`, then for `y ≥ 1` the values `V(n)`,
`n ∈ (y, Ky]`, are neither all `> η` nor all `< −η`. -/
theorem no_sign_run {η : R} {K y : Nat} (hη : 0 < η) (hK : 1 ≤ K) (hy : 1 ≤ y)
    (hKη : 2 * Bm < η * (R.log (K : R) - 3)) :
    (∃ n, y < n ∧ n ≤ K * y ∧ vrem n ≤ η) ∧ (∃ n, y < n ∧ n ≤ K * y ∧ -η ≤ vrem n) := by
  have hKy : y ≤ K * y := Nat.le_mul_of_pos_left y (by omega)
  have hblock : fsum (fun n => rem n * wt n) (K * y + 1) - fsum (fun n => rem n * wt n) (y + 1) =
      fsum (fun j => vrem (y + 1 + j) * (1 / (((y + 1 + j : Nat) : R) + 1))) (K * y - y) := by
    rw [show K * y + 1 = (y + 1) + (K * y - y) by omega, fsum_split]
    rw [show fsum (fun n => rem n * wt n) (y + 1) +
      fsum (fun k => rem (y + 1 + k) * wt (y + 1 + k)) (K * y - y) -
      fsum (fun n => rem n * wt n) (y + 1) =
      fsum (fun k => rem (y + 1 + k) * wt (y + 1 + k)) (K * y - y) by grind]
    apply fsum_congr; intro j _; exact rem_wt_eq (by omega)
  have hB1 := abs_sum_rem_wt_le (K * y)
  have hB2 := abs_sum_rem_wt_le y
  rw [abs_le] at hB1 hB2
  have hH := harmonic_block_ge hy hK
  have hpos : ∀ j, 0 < 1 / (((y + 1 + j : Nat) : R) + 1) := fun j =>
    div_pos (by grind) (by have := natCast_nonneg' (y + 1 + j); grind)
  constructor
  · apply Classical.byContradiction; intro h
    have hall : ∀ j, j < K * y - y → η * (1 / (((y + 1 + j : Nat) : R) + 1)) ≤
        vrem (y + 1 + j) * (1 / (((y + 1 + j : Nat) : R) + 1)) := by
      intro j hj
      have : η < vrem (y + 1 + j) := by
        apply Classical.byContradiction; intro h'
        exact h ⟨y + 1 + j, by omega, by omega, by grind⟩
      exact OrderedRing.mul_le_mul_of_nonneg_right (Std.le_of_lt this) (Std.le_of_lt (hpos j))
    have hs := fsum_le_fsum' hall
    rw [fsum_const_mul, ← hblock] at hs
    have := OrderedRing.mul_le_mul_of_nonneg_left hH (Std.le_of_lt hη)
    grind
  · apply Classical.byContradiction; intro h
    have hall : ∀ j, j < K * y - y → vrem (y + 1 + j) * (1 / (((y + 1 + j : Nat) : R) + 1)) ≤
        -η * (1 / (((y + 1 + j : Nat) : R) + 1)) := by
      intro j hj
      have : vrem (y + 1 + j) < -η := by
        apply Classical.byContradiction; intro h'
        exact h ⟨y + 1 + j, by omega, by omega, by grind⟩
      exact OrderedRing.mul_le_mul_of_nonneg_right (Std.le_of_lt this) (Std.le_of_lt (hpos j))
    have hs := fsum_le_fsum' hall
    rw [fsum_const_mul, ← hblock] at hs
    have := OrderedRing.mul_le_mul_of_nonneg_left hH (Std.le_of_lt hη)
    grind

/-! ## Good intervals -/

/-- **Good intervals.** For every `ε > 0` there are `K, T ≥ 1` and `y₀` such that for every
`y ≥ y₀` some `m ∈ (y, Ky]` has `|V(n)| ≤ ε/2` for all `n ∈ [m, m + ⌊m/T⌋]`. -/
theorem good_interval {ε : R} (hε : 0 < ε) :
    ∃ K T y₀ : Nat, 1 ≤ K ∧ 1 ≤ T ∧ ∀ y, y₀ ≤ y → ∃ m, y < m ∧ m ≤ K * y ∧
      ∀ n, m ≤ n → n ≤ m + m / T → abs (vrem n) ≤ ε / 2 := by
  have hη : 0 < ε / 4 := by grind
  obtain ⟨T, hT, hTε⟩ := exists_nat_mul_ge (5 + C0) (show 0 < ε / 8 by grind)
  obtain ⟨K, hK, hKl⟩ := log_eventually_ge (2 * Bm / (ε / 4) + 4)
  obtain ⟨n₀, hn₀⟩ := vrem_step_small hη
  obtain ⟨L₁, hL₁, hL₁l⟩ := log_eventually_ge 1
  obtain ⟨L₂, hL₂, hL₂l⟩ := log_eventually_ge (2 * KA / (ε / 8))
  refine ⟨K, T, n₀ + L₁ + L₂ + 1, hK, hT, fun y hy => ?_⟩
  have hKη : 2 * Bm < ε / 4 * (R.log (K : R) - 3) := by
    have h1 := hKl K (Nat.le_refl K)
    have e : ε / 4 * (2 * Bm / (ε / 4)) = 2 * Bm := by
      have : ε / 4 ≠ 0 := by grind
      grind
    have := OrderedRing.mul_le_mul_of_nonneg_left (show 2 * Bm / (ε / 4) + 1 ≤
      R.log (K : R) - 3 by grind) (Std.le_of_lt hη)
    grind
  obtain ⟨⟨n₁, h11, h12, h13⟩, ⟨n₂, h21, h22, h23⟩⟩ :=
    no_sign_run hη hK (show 1 ≤ y by omega) hKη
  -- A point with `|V(m)| ≤ ε/4`.
  have hstep : ∀ n, y ≤ n → abs (vrem (n + 1) - vrem n) ≤ ε / 4 := fun n hn => hn₀ n (by omega)
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m, y < m ∧ m ≤ K * y ∧ abs (vrem m) ≤ ε / 4 := by
    by_cases hc : -(ε / 4) ≤ vrem n₁
    · exact ⟨n₁, h11, h12, by rw [abs_le]; constructor <;> grind⟩
    · rcases (by omega : n₁ < n₂ ∨ n₂ < n₁ ∨ n₁ = n₂) with h | h | h
      · obtain ⟨n, a1, a2, a3, a4⟩ := ivt_up vrem (-(ε / 4)) n₂ n₁ (by omega) (by grind) h23
        have := hstep (n - 1) (by omega)
        rw [show n - 1 + 1 = n by omega] at this
        refine ⟨n, by omega, by omega, ?_⟩
        rw [abs_le] at this ⊢; constructor <;> grind
      · obtain ⟨n, a1, a2, a3, a4⟩ := ivt_down vrem (-(ε / 4)) n₁ n₂ (by omega) h23 (by grind)
        have := hstep n (by omega)
        refine ⟨n, by omega, by omega, ?_⟩
        rw [abs_le] at this ⊢; constructor <;> grind
      · subst h; grind
  refine ⟨m, hm1, hm2, fun n hn1 hn2 => ?_⟩
  have hm0 : 1 ≤ m := by omega
  have hdiv : m / T ≤ m := Nat.div_le_self m T
  have hlm := hL₁l m (by omega)
  have hlip := vrem_lipschitz hm0 hlm hn1 (by omega)
  -- `(n − m)/n ≤ 1/T`.
  have hn0 : (0 : R) < (n : R) := natCast_pos' (by omega)
  have hT0 : (0 : R) < (T : R) := natCast_pos' hT
  have hq : ((n : R) - (m : R)) / (n : R) * (T : R) ≤ 1 := by
    have h1 : ((n - m : Nat) : R) * (T : R) ≤ (m : R) := by
      have : (n - m) * T ≤ m := by
        have := Nat.div_mul_le_self m T
        exact Nat.le_trans (Nat.mul_le_mul_right T (by omega)) this
      have h2 : (((n - m) * T : Nat) : R) ≤ (m : R) := natCast_le' this
      rw [natCast_mul'] at h2; exact h2
    have e : ((n - m : Nat) : R) = (n : R) - (m : R) := by
      have : ((n - m + m : Nat) : R) = ((n - m : Nat) : R) + (m : R) := natCast_add' _ _
      rw [show n - m + m = n by omega] at this; grind
    rw [e] at h1
    have hnm : (m : R) ≤ (n : R) := natCast_le' hn1
    have : (n : R) ≠ 0 := by grind
    have e2 : ((n : R) - (m : R)) / (n : R) * (T : R) * (n : R) = ((n : R) - (m : R)) * (T : R) := by
      grind
    apply le_of_mul_le_mul_right' (C := (n : R)) _ hn0
    rw [e2]; grind
  have hq0 : 0 ≤ ((n : R) - (m : R)) / (n : R) := by
    have hnm : (m : R) ≤ (n : R) := natCast_le' hn1
    have := div_pos (show (0 : R) < 1 by grind) hn0
    have e : ((n : R) - (m : R)) / (n : R) = ((n : R) - (m : R)) * (1 / (n : R)) := by grind
    rw [e]; exact OrderedRing.mul_nonneg (by grind) (Std.le_of_lt this)
  have k1 : (5 + C0) * (((n : R) - (m : R)) / (n : R)) ≤ ε / 8 := by
    apply le_of_mul_le_mul_right' (C := (T : R)) _ hT0
    have := OrderedRing.mul_le_mul_of_nonneg_left hq (show 0 ≤ 5 + C0 by have := one_le_C0; grind)
    grind
  have k2 : 2 * KA / R.log (m : R) ≤ ε / 8 := by
    have hl2 := hL₂l m (by omega)
    have hl0 : (0 : R) < R.log (m : R) := by grind
    apply le_of_mul_le_mul_right' (C := R.log (m : R)) _ hl0
    have e : 2 * KA / R.log (m : R) * R.log (m : R) = 2 * KA := by
      have : R.log (m : R) ≠ 0 := by grind
      grind
    rw [e]
    have := OrderedRing.mul_le_mul_of_nonneg_left hl2 (show 0 ≤ ε / 8 by grind)
    have e2 : ε / 8 * (2 * KA / (ε / 8)) = 2 * KA := by
      have : ε / 8 ≠ 0 := by grind
      grind
    grind
  have := abs_add (vrem n - vrem m) (vrem m)
  rw [show vrem n - vrem m + vrem m = vrem n by grind] at this
  grind

end Foundations.NumberTheory.PNT
