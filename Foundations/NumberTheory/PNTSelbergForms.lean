import Foundations.NumberTheory.PNTSelberg

/-!
# Toward the prime number theorem IX: Selberg's formula with `Λ ∗ Λ`

Selberg's formula is usually quoted in the form

  `Σ_{n ≤ x} Λ(n) log n + Σ_{mn ≤ x} Λ(m) Λ(n) = 2x log x + O(x)`,

in which the two kinds of "almost primes" — prime powers weighted by `log² p`, and products of
two prime powers weighted by `log p log q` — appear side by side. Writing
`(Λ ∗ Λ)(k) = Σ_{d ∣ k} Λ(d) Λ(k/d)` for the Dirichlet convolution, this file derives that form
from the `ψ`-form of the previous file. Two small steps are needed:

* `Σ_{n ≤ N} Λ(n) ψ(N/n) = Σ_{k ≤ N} (Λ ∗ Λ)(k)` — the hyperbola reindexing again;
* `0 ≤ ψ(N) log N − Σ_{n ≤ N} Λ(n) log n ≤ N log 1024` — by Abel summation the difference is
  `Σ_{j < N} ψ(j) (log(j+1) − log j)`, and each term is at most `j log 1024 · (1/j)`.

## From here to the prime number theorem

The prime number theorem `ψ(N)/N → 1` follows from Selberg's formula by the Erdős–Selberg
*tauberian* argument (in outline after Levinson's "motivated account", 1969). It is formalised in
the files that follow, using finite sums in place of integrals: `PNTRemainder` (Selberg's formula
for `R(N) = ψ(N) − N`), `PNTIterated` (`|R(N)| log² N ≤ Σ a(k) |R(N/k)| + O(N log N)`),
`PNTTauberianA`–`C` (sign changes, averaging, and the improvement lemma), and `PNTTheorem`
(`prime_number_theorem`). For comparison, the Isabelle formalisation of this proof by Avigad,
Donnelly, Gray and Raff (2007) ran to about 30 000 lines.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- The **Dirichlet convolution** `(Λ ∗ Λ)(k) = Σ_{d ∣ k} Λ(d) Λ(k/d)`. -/
noncomputable def vmConv (k : Nat) : R := dsum (fun d => vonMangoldt d * vonMangoldt (k / d)) k

/-- `Σ_{n ≤ N} Λ(n) ψ(⌊N/n⌋) = Σ_{k ≤ N} (Λ ∗ Λ)(k)`. -/
theorem sum_vonMangoldt_psi (N : Nat) :
    fsum (fun n => vonMangoldt n * psi (N / n)) (N + 1) = fsum vmConv (N + 1) := by
  have h := hyperbola N (fun d e => vonMangoldt d * vonMangoldt e)
  have e1 : fsum (fun n => vonMangoldt n * psi (N / n)) (N + 1) =
      fsum (fun d => if 1 ≤ d then fsum (fun e => if 1 ≤ e then vonMangoldt d * vonMangoldt e
        else 0) (N / d + 1) else 0) (N + 1) := by
    apply fsum_congr; intro d _
    by_cases hd : 1 ≤ d
    · simp only [hd, ↓reduceIte]
      rw [psi_eq_sum_vonMangoldt, ← fsum_const_mul]
      apply fsum_congr; intro e _
      by_cases he : 1 ≤ e
      · simp only [he, ↓reduceIte]
      · obtain rfl : e = 0 := by omega
        simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte, vonMangoldt_zero]; grind
    · obtain rfl : d = 0 := by omega
      simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte, vonMangoldt_zero]; grind
  rw [e1, h]
  apply fsum_congr; intro k _
  by_cases hk : 1 ≤ k
  · simp only [hk, ↓reduceIte]; rfl
  · obtain rfl : k = 0 := by omega
    simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte]
    unfold vmConv dsum
    simp only [fsum_succ, fsum_zero, Nat.dvd_zero, ↓reduceIte, vonMangoldt_zero]; grind

/-- **Abel summation for `Λ log`.** `D(N) = Σ_{n ≤ N} Λ(n) (log N − log n)` satisfies
`0 ≤ D(N) ≤ N log 1024`. -/
theorem psi_log_sub_bounds (N : Nat) :
    0 ≤ fsum (fun n => vonMangoldt n * (R.log (N : R) - R.log (n : R))) (N + 1) ∧
      fsum (fun n => vonMangoldt n * (R.log (N : R) - R.log (n : R))) (N + 1) ≤
        (N : R) * R.log 1024 := by
  have hc : 0 ≤ R.log 1024 := log_nonneg' (show (1 : R) ≤ 1024 by grind)
  induction N with
  | zero =>
    simp only [fsum_succ, fsum_zero, vonMangoldt_zero]
    constructor
    · grind
    · show _ ≤ ((0 : Nat) : R) * _; grind
  | succ N ih =>
    -- `D(N+1) = D(N) + ψ(N) (log(N+1) − log N)`.
    have hstep : fsum (fun n => vonMangoldt n * (R.log ((N + 1 : Nat) : R) - R.log (n : R)))
        (N + 1 + 1) =
        fsum (fun n => vonMangoldt n * (R.log (N : R) - R.log (n : R))) (N + 1) +
          psi N * (R.log ((N + 1 : Nat) : R) - R.log (N : R)) := by
      rw [fsum_succ, psi_eq_sum_vonMangoldt, ← fsum_mul_const, ← fsum_add]
      have : vonMangoldt (N + 1) * (R.log ((N + 1 : Nat) : R) - R.log ((N + 1 : Nat) : R)) = 0 := by
        grind
      rw [this]
      have e : fsum (fun n => vonMangoldt n * (R.log ((N + 1 : Nat) : R) - R.log (n : R))) (N + 1) =
          fsum (fun n => vonMangoldt n * (R.log (N : R) - R.log (n : R)) +
            vonMangoldt n * (R.log ((N + 1 : Nat) : R) - R.log (N : R))) (N + 1) := by
        apply fsum_congr; intro n _; grind
      rw [e]; grind
    rw [hstep]
    obtain ⟨ih1, ih2⟩ := ih
    -- `0 ≤ ψ(N) δ_N ≤ log 1024`.
    have hpsi0 := psi_nonneg N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have : psi 0 = 0 := by
        rw [psi_eq_sum_vonMangoldt]; simp only [fsum_succ, fsum_zero, vonMangoldt_zero]; grind
      rw [this]
      constructor
      · grind
      · have := natCast_nonneg' (0 + 1)
        have := OrderedRing.mul_nonneg this hc
        grind
    · obtain ⟨hδ1, hδ2⟩ := log_succ_sub_bounds hN
      have hδ0 : 0 ≤ R.log ((N + 1 : Nat) : R) - R.log (N : R) := by
        have := OrderedRing.mul_le_mul_of_nonneg_left hc (natCast_nonneg' N)
        apply Classical.byContradiction; intro h
        have := OrderedRing.mul_lt_mul_of_pos_left (show R.log ((N + 1 : Nat) : R) - R.log (N : R) < 0
          by grind) (show (0 : R) < (N : R) + 1 by have := natCast_nonneg' N; grind)
        grind
      have hpsi := psi_le N
      have k1 := OrderedRing.mul_le_mul_of_nonneg_right hpsi hδ0
      have k2 := OrderedRing.mul_le_mul_of_nonneg_left hδ1 hc
      have k3 := OrderedRing.mul_nonneg hpsi0 hδ0
      have e : ((N + 1 : Nat) : R) = (N : R) + 1 := by grind
      rw [e]
      constructor <;> grind

/-- **Selberg's symmetry formula, classical form.** For `N ≥ 1`,
`|Σ_{n ≤ N} Λ(n) log n + Σ_{k ≤ N} (Λ ∗ Λ)(k) − 2N log N| ≤ (30 + 4 log 1024) · N`,
i.e. `Σ_{n ≤ x} Λ(n) log n + Σ_{mn ≤ x} Λ(m) Λ(n) = 2x log x + O(x)`. -/
theorem selberg_symmetry_conv {N : Nat} (hN : 1 ≤ N) :
    abs (fsum (fun n => vonMangoldt n * R.log (n : R)) (N + 1) + fsum vmConv (N + 1) -
      2 * (N : R) * R.log (N : R)) ≤ (30 + 4 * R.log 1024) * (N : R) := by
  have hS := selberg_symmetry hN
  rw [sum_vonMangoldt_psi] at hS
  obtain ⟨h1, h2⟩ := psi_log_sub_bounds N
  have e : fsum (fun n => vonMangoldt n * (R.log (N : R) - R.log (n : R))) (N + 1) =
      psi N * R.log (N : R) - fsum (fun n => vonMangoldt n * R.log (n : R)) (N + 1) := by
    rw [psi_eq_sum_vonMangoldt, ← fsum_mul_const, ← fsum_sub]
    apply fsum_congr; intro n _; grind
  rw [e] at h1 h2
  rw [abs_le] at hS ⊢
  constructor <;> grind

end Foundations.NumberTheory.PNT
