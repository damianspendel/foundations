import Foundations.NumberTheory.PNTRemainder

/-!
# Toward the prime number theorem XI: Selberg's formula iterated

Selberg's formula for the remainder, `R(x) log x + Σ_{n ≤ x} Λ(n) R(x/n) = O(x)`, expresses
`R(x)` through the values `R(x/n)` — but with the weights `Λ(n)`, whose total `ψ(x)` is the
unknown itself. The trick of the Erdős–Selberg argument is to apply the formula a second time,
to each `R(x/m)`, and combine:

  `R(x) log² x = −Σ_{k ≤ x} Λ(k) log k · R(x/k) + Σ_{k ≤ x} (Λ ∗ Λ)(k) R(x/k) + O(x log x)`.

Taking absolute values,

  `|R(x)| log² x ≤ Σ_{k ≤ x} a(k) |R(x/k)| + O(x log x)`,   `a(k) = Λ(k) log k + (Λ ∗ Λ)(k)`,

and now the weights `a(k)` are *known* on average: `Σ_{k ≤ y} a(k) = 2y log y + O(y)` is
Selberg's formula once more. After division by `x`, `|R(x)|/x` is bounded by a weighted average
of the values `|R(y)|/y` at `y = x/k`, with weights `a(k)/k` of total `log² x + O(log x)`. The
next files show that this average is strictly smaller than the largest value, unless that value
is `0`.

The proof is a bookkeeping exercise: multiply Selberg's formula at `N` by `log N`, subtract the
formula at each `⌊N/m⌋` weighted by `Λ(m)`, recognise the double sum
`Σ_m Λ(m) Σ_n Λ(n) R(⌊N/(mn)⌋)` as `Σ_k (Λ ∗ Λ)(k) R(⌊N/k⌋)` (hyperbola reindexing), and
control the rounding `log N − log ⌊N/m⌋ = log m + O(1/⌊N/m⌋)`.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- The left side of Selberg's formula for the remainder:
`S₁(M) = R(M) log M + Σ_{n ≤ M} Λ(n) R(⌊M/n⌋)`. -/
noncomputable def selS1 (M : Nat) : R :=
  rem M * R.log (M : R) + fsum (fun n => vonMangoldt n * rem (M / n)) (M + 1)

/-- The constant `K₁ = 31 + 3 log 1024` of Selberg's formula for the remainder. -/
noncomputable def K1 : R := 31 + 3 * R.log 1024

/-- `|S₁(M)| ≤ K₁ M` for every `M` (also `M = 0`). -/
theorem abs_selS1_le (M : Nat) : abs (selS1 M) ≤ K1 * (M : R) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · unfold selS1
    simp only [fsum_succ, fsum_zero, rem_zero, vonMangoldt_zero]
    rw [show (0 : R) * R.log ((0 : Nat) : R) + (0 + 0 * rem (0 / 0)) = 0 by grind, abs_zero]
    unfold K1; have := log1024_nonneg; grind
  · exact selberg_rem hM

/-- The double sum: `Σ_m Λ(m) Σ_{n ≤ N/m} Λ(n) R(⌊⌊N/m⌋/n⌋) = Σ_{k ≤ N} (Λ ∗ Λ)(k) R(⌊N/k⌋)`. -/
theorem double_sum_rem (N : Nat) :
    fsum (fun m => vonMangoldt m * fsum (fun n => vonMangoldt n * rem (N / m / n)) (N / m + 1))
      (N + 1) = fsum (fun k => vmConv k * rem (N / k)) (N + 1) := by
  have h := hyperbola N (fun d e => vonMangoldt d * vonMangoldt e * rem (N / (d * e)))
  have e1 : fsum (fun m => vonMangoldt m * fsum (fun n => vonMangoldt n * rem (N / m / n))
      (N / m + 1)) (N + 1) =
      fsum (fun d => if 1 ≤ d then fsum (fun e => if 1 ≤ e then
        vonMangoldt d * vonMangoldt e * rem (N / (d * e)) else 0) (N / d + 1) else 0) (N + 1) := by
    apply fsum_congr; intro d _
    by_cases hd : 1 ≤ d
    · simp only [hd, ↓reduceIte]
      rw [← fsum_const_mul]
      apply fsum_congr; intro e _
      by_cases he : 1 ≤ e
      · simp only [he, ↓reduceIte]; rw [Nat.div_div_eq_div_mul]; grind
      · obtain rfl : e = 0 := by omega
        simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte, vonMangoldt_zero]; grind
    · obtain rfl : d = 0 := by omega
      simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte, vonMangoldt_zero]; grind
  rw [e1, h]
  apply fsum_congr; intro k _
  by_cases hk : 1 ≤ k
  · simp only [hk, ↓reduceIte]
    unfold vmConv
    rw [show dsum (fun d => vonMangoldt d * vonMangoldt (k / d)) k * rem (N / k) =
      rem (N / k) * dsum (fun d => vonMangoldt d * vonMangoldt (k / d)) k by grind,
      dsum_const_mul]
    unfold dsum
    apply fsum_congr; intro d _
    by_cases hdk : d ∣ k
    · simp only [hdk, ↓reduceIte]; rw [Nat.mul_div_cancel' hdk]; grind
    · simp only [hdk, ↓reduceIte]
  · obtain rfl : k = 0 := by omega
    simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte]
    unfold vmConv dsum
    simp only [fsum_succ, fsum_zero, Nat.dvd_zero, ↓reduceIte, vonMangoldt_zero]; grind

/-- The rounding error `η_m = log N − log m − log ⌊N/m⌋` satisfies `0 ≤ η_m` and
`⌊N/m⌋ · η_m ≤ 1`, for `1 ≤ m ≤ N`. -/
theorem rounding_bounds {N m : Nat} (hm : 1 ≤ m) (hmN : m ≤ N) :
    0 ≤ R.log (N : R) - R.log (m : R) - R.log ((N / m : Nat) : R) ∧
      ((N / m : Nat) : R) * (R.log (N : R) - R.log (m : R) - R.log ((N / m : Nat) : R)) ≤ 1 := by
  have hQ : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).2 (by omega)
  have hm0 : (0 : R) < (m : R) := natCast_pos' hm
  have hN0 : (0 : R) < (N : R) := natCast_pos' (by omega)
  have hQ0 : (0 : R) < ((N / m : Nat) : R) := natCast_pos' hQ
  obtain ⟨f1, f2⟩ := div_sub_floor (N := N) hm
  rw [← log_div' hN0 hm0]
  have hy : (0 : R) < (N : R) / (m : R) := div_pos hN0 hm0
  have l1 := log_le_log hQ0 (show ((N / m : Nat) : R) ≤ (N : R) / (m : R) by grind)
  have l2 := log_le_log hy (show (N : R) / (m : R) ≤ ((N / m + 1 : Nat) : R) by
    rw [show ((N / m + 1 : Nat) : R) = ((N / m : Nat) : R) + 1 by grind]; grind)
  have b := (log_succ_sub_bounds hQ).1
  constructor
  · grind
  · have := OrderedRing.mul_le_mul_of_nonneg_left
      (show R.log ((N : R) / (m : R)) - R.log ((N / m : Nat) : R) ≤
        R.log ((N / m + 1 : Nat) : R) - R.log ((N / m : Nat) : R) by grind) (Std.le_of_lt hQ0)
    grind

/-- **Selberg's formula iterated.** For `N ≥ 1`,
`|R(N)| log² N ≤ Σ_{k ≤ N} a(k) |R(⌊N/k⌋)| + 2K₁ N log N + (1 + log 1024) log 1024 · N`. -/
theorem iterated_ineq {N : Nat} (hN : 1 ≤ N) :
    abs (rem N) * (R.log (N : R) * R.log (N : R)) ≤
      fsum (fun k => selA k * abs (rem (N / k))) (N + 1) +
        (2 * K1 * (N : R) * R.log (N : R) + (1 + R.log 1024) * R.log 1024 * (N : R)) := by
  have hc := log1024_nonneg
  have hlN := log_natCast_nonneg hN
  have hK1 : 0 ≤ K1 := by unfold K1; grind
  -- The exact identity.
  have hS1m : fsum (fun m => vonMangoldt m * selS1 (N / m)) (N + 1) =
      fsum (fun m => vonMangoldt m * rem (N / m) * R.log ((N / m : Nat) : R)) (N + 1) +
        fsum (fun k => vmConv k * rem (N / k)) (N + 1) := by
    rw [← double_sum_rem, ← fsum_add]
    apply fsum_congr; intro m _; unfold selS1; grind
  have hid : rem N * (R.log (N : R) * R.log (N : R)) =
      R.log (N : R) * selS1 N - fsum (fun m => vonMangoldt m * selS1 (N / m)) (N + 1) -
        fsum (fun m => vonMangoldt m * R.log (m : R) * rem (N / m)) (N + 1) -
        fsum (fun m => vonMangoldt m * rem (N / m) *
          (R.log (N : R) - R.log (m : R) - R.log ((N / m : Nat) : R))) (N + 1) +
        fsum (fun k => vmConv k * rem (N / k)) (N + 1) := by
    rw [hS1m]
    have e : R.log (N : R) * selS1 N = rem N * (R.log (N : R) * R.log (N : R)) +
        fsum (fun m => vonMangoldt m * rem (N / m) * R.log (N : R)) (N + 1) := by
      have hF : fsum (fun m => vonMangoldt m * rem (N / m) * R.log (N : R)) (N + 1) =
          fsum (fun m => vonMangoldt m * rem (N / m)) (N + 1) * R.log (N : R) :=
        fsum_mul_const _ _ _
      unfold selS1; rw [hF]
      generalize fsum (fun m => vonMangoldt m * rem (N / m)) (N + 1) = F
      grind
    rw [e]
    have e2 : fsum (fun m => vonMangoldt m * rem (N / m) * R.log (N : R)) (N + 1) =
        fsum (fun m => vonMangoldt m * rem (N / m) * R.log ((N / m : Nat) : R)) (N + 1) +
        fsum (fun m => vonMangoldt m * R.log (m : R) * rem (N / m)) (N + 1) +
        fsum (fun m => vonMangoldt m * rem (N / m) *
          (R.log (N : R) - R.log (m : R) - R.log ((N / m : Nat) : R))) (N + 1) := by
      rw [← fsum_add, ← fsum_add]; apply fsum_congr; intro m _; grind
    rw [e2]; grind
  -- Bounds.
  have b1 : abs (R.log (N : R) * selS1 N) ≤ K1 * (N : R) * R.log (N : R) := by
    rw [abs_mul, abs_of_nonneg hlN]
    have := OrderedRing.mul_le_mul_of_nonneg_left (abs_selS1_le N) hlN; grind
  have b2 : abs (fsum (fun m => vonMangoldt m * selS1 (N / m)) (N + 1)) ≤
      K1 * (N : R) * R.log (N : R) := by
    refine Std.le_trans (abs_fsum_le _ _) ?_
    have h1 : fsum (fun m => abs (vonMangoldt m * selS1 (N / m))) (N + 1) ≤
        K1 * fsum (fun n => vonMangoldt n * ((N / n : Nat) : R)) (N + 1) := by
      rw [← fsum_const_mul]; apply fsum_le_fsum'; intro m _
      rw [abs_mul, abs_of_nonneg (vonMangoldt_nonneg m)]
      have := OrderedRing.mul_le_mul_of_nonneg_left (abs_selS1_le (N / m)) (vonMangoldt_nonneg m)
      grind
    rw [sum_vonMangoldt_floor] at h1
    have := OrderedRing.mul_le_mul_of_nonneg_left (log_fact_le N) hK1
    grind
  have b3 : abs (fsum (fun m => vonMangoldt m * rem (N / m) *
      (R.log (N : R) - R.log (m : R) - R.log ((N / m : Nat) : R))) (N + 1)) ≤
      (1 + R.log 1024) * R.log 1024 * (N : R) := by
    refine Std.le_trans (abs_fsum_le _ _) ?_
    have h1 : fsum (fun m => abs (vonMangoldt m * rem (N / m) *
        (R.log (N : R) - R.log (m : R) - R.log ((N / m : Nat) : R)))) (N + 1) ≤
        (1 + R.log 1024) * fsum vonMangoldt (N + 1) := by
      rw [← fsum_const_mul]; apply fsum_le_fsum'; intro m hm
      rw [abs_mul, abs_mul, abs_of_nonneg (vonMangoldt_nonneg m)]
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · rw [vonMangoldt_zero]; grind
      · obtain ⟨r1, r2⟩ := rounding_bounds hm1 (show m ≤ N by omega)
        rw [abs_of_nonneg r1]
        have hr := abs_rem_le (N / m)
        have k1 := OrderedRing.mul_le_mul_of_nonneg_right hr r1
        have k2 : abs (rem (N / m)) * (R.log (N : R) - R.log (m : R) - R.log ((N / m : Nat) : R))
            ≤ 1 + R.log 1024 := by
          have := OrderedRing.mul_le_mul_of_nonneg_left r2 (show 0 ≤ 1 + R.log 1024 by grind)
          grind
        have := OrderedRing.mul_le_mul_of_nonneg_left k2 (vonMangoldt_nonneg m)
        grind
    rw [← psi_eq_sum_vonMangoldt] at h1
    have := OrderedRing.mul_le_mul_of_nonneg_left (psi_le N) (show 0 ≤ 1 + R.log 1024 by grind)
    grind
  -- Combine.
  have hk : abs (fsum (fun k => vmConv k * rem (N / k)) (N + 1) -
      fsum (fun m => vonMangoldt m * R.log (m : R) * rem (N / m)) (N + 1)) ≤
      fsum (fun k => selA k * abs (rem (N / k))) (N + 1) := by
    rw [← fsum_sub]
    refine Std.le_trans (abs_fsum_le _ _) (fsum_le_fsum' fun k _ => ?_)
    rw [show vmConv k * rem (N / k) - vonMangoldt k * R.log (k : R) * rem (N / k) =
      (vmConv k - vonMangoldt k * R.log (k : R)) * rem (N / k) by grind, abs_mul]
    apply OrderedRing.mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    unfold selA
    have := vmConv_nonneg k; have := vonMangoldt_log_nonneg k
    rw [abs_le]; constructor <;> grind
  have habs : abs (rem N * (R.log (N : R) * R.log (N : R))) =
      abs (rem N) * (R.log (N : R) * R.log (N : R)) := by
    rw [abs_mul, abs_of_nonneg (OrderedRing.mul_nonneg hlN hlN)]
  rw [← habs, hid]
  generalize R.log (N : R) * selS1 N = A1 at b1 ⊢
  generalize fsum (fun m => vonMangoldt m * selS1 (N / m)) (N + 1) = A2 at b2 ⊢
  generalize fsum (fun m => vonMangoldt m * rem (N / m) *
    (R.log (N : R) - R.log (m : R) - R.log ((N / m : Nat) : R))) (N + 1) = A3 at b3 ⊢
  generalize fsum (fun k => vmConv k * rem (N / k)) (N + 1) = A4 at hk ⊢
  generalize fsum (fun m => vonMangoldt m * R.log (m : R) * rem (N / m)) (N + 1) = A5 at hk ⊢
  rw [abs_le] at b1 b2 b3 hk ⊢
  constructor <;> grind

end Foundations.NumberTheory.PNT
