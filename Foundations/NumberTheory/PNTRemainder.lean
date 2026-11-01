import Foundations.NumberTheory.PNTSelbergForms

/-!
# Toward the prime number theorem X: the remainder `R(N) = ψ(N) − N`

The prime number theorem says that the **remainder** `R(N) = ψ(N) − N` is `o(N)`. This file
rewrites Selberg's formula in terms of `R` and collects the auxiliary facts about `R` that the
Erdős–Selberg tauberian argument (next files) needs:

* **Selberg's formula for the remainder**:
  `R(N) log N + Σ_{n ≤ N} Λ(n) R(⌊N/n⌋) = O(N)` — the main terms `2N log N` cancel exactly
  against `N log N + Σ Λ(n) ⌊N/n⌋ = N log N + log N!`;
* the **Selberg weights** `a(k) = Λ(k) log k + (Λ ∗ Λ)(k) ≥ 0`, with summatory function
  `A(N) = 2N log N + O(N)`, and the logarithmic average `Σ_{k ≤ N} a(k)/k ≤ log² N + O(log N)`
  (by Abel summation and `Σ log j / j ≤ ½ log² N + ½`);
* a **short-interval bound** `(ψ(n) − ψ(m)) log m ≤ 2(n − m)(log n + 1) + O(n)`: primes cannot
  crowd into an interval more than twice as densely as expected (another consequence of Selberg's
  formula, since `a(k) ≥ Λ(k) log k`);
* the **mean value** `|Σ_{n ≤ N} R(n)/(n(n+1))| ≤ B`: on average `R` is neither positive nor
  negative, which will force it to change sign in every long multiplicative interval.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- The **remainder** `R(n) = ψ(n) − n` of the prime number theorem. -/
noncomputable def rem (n : Nat) : R := psi n - (n : R)

/-- The constant of Selberg's formula in its classical form. -/
noncomputable def KA : R := 30 + 4 * R.log 1024

/-- `log 1024 ≥ 0`. -/
theorem log1024_nonneg : 0 ≤ R.log 1024 := log_nonneg' (show (1 : R) ≤ 1024 by grind)

/-- `KA ≥ 0`. -/
theorem KA_nonneg : 0 ≤ KA := by unfold KA; have := log1024_nonneg; grind

/-- `ψ(0) = 0`. -/
theorem psi_zero : psi 0 = 0 := by
  rw [psi_eq_sum_vonMangoldt]; simp only [fsum_succ, fsum_zero, vonMangoldt_zero]; grind

/-- `R(0) = 0`. -/
theorem rem_zero : rem 0 = 0 := by unfold rem; rw [psi_zero]; grind

/-- `−n ≤ R(n) ≤ n (log 1024 − 1)`: Chebyshev's bounds for the remainder. -/
theorem rem_bounds (n : Nat) : -(n : R) ≤ rem n ∧ rem n ≤ (n : R) * R.log 1024 := by
  unfold rem
  have := psi_nonneg n; have := psi_le n; have := natCast_nonneg' n
  constructor <;> grind

/-- `|R(n)| ≤ C₀ n` with `C₀ = 1 + log 1024`. -/
theorem abs_rem_le (n : Nat) : abs (rem n) ≤ (1 + R.log 1024) * (n : R) := by
  obtain ⟨h1, h2⟩ := rem_bounds n
  have := OrderedRing.mul_nonneg log1024_nonneg (natCast_nonneg' n)
  rw [abs_le]; constructor <;> grind

/-! ## Selberg's formula for the remainder -/

/-- `Σ_{n ≤ N} Λ(n) ⌊N/n⌋ = log N!`. -/
theorem sum_vonMangoldt_floor (N : Nat) :
    fsum (fun n => vonMangoldt n * ((N / n : Nat) : R)) (N + 1) = R.log (Arith.fact N : R) := by
  rw [← ppSum_eq_sum_vonMangoldt, log_fact_eq]
  unfold ppSum
  apply fsum_congr; intro p _; apply fsum_congr; intro k _
  split <;> grind

/-- **Selberg's formula for the remainder.** For `N ≥ 1`,
`|R(N) log N + Σ_{n ≤ N} Λ(n) R(⌊N/n⌋)| ≤ (31 + 3 log 1024) N`. -/
theorem selberg_rem {N : Nat} (hN : 1 ≤ N) :
    abs (rem N * R.log (N : R) + fsum (fun n => vonMangoldt n * rem (N / n)) (N + 1)) ≤
      (31 + 3 * R.log 1024) * (N : R) := by
  have hS := selberg_symmetry hN
  have e : fsum (fun n => vonMangoldt n * rem (N / n)) (N + 1) =
      fsum (fun n => vonMangoldt n * psi (N / n)) (N + 1) - R.log (Arith.fact N : R) := by
    rw [← sum_vonMangoldt_floor, ← fsum_sub]
    apply fsum_congr; intro n _; unfold rem; grind
  rw [e]
  have h1 := log_fact_le N
  have h2 := log_fact_ge N
  unfold rem
  rw [abs_le] at hS ⊢
  constructor <;> grind

/-! ## The Selberg weights -/

/-- The **Selberg weights** `a(k) = Λ(k) log k + (Λ ∗ Λ)(k)`. -/
noncomputable def selA (k : Nat) : R := vonMangoldt k * R.log (k : R) + vmConv k

/-- `a(0) = 0`. -/
theorem selA_zero : selA 0 = 0 := by
  unfold selA vmConv dsum
  simp only [fsum_succ, fsum_zero, Nat.dvd_zero, ↓reduceIte, vonMangoldt_zero]; grind

/-- `Λ(k) log k ≥ 0`. -/
theorem vonMangoldt_log_nonneg (k : Nat) : 0 ≤ vonMangoldt k * R.log (k : R) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [vonMangoldt_zero]; grind
  · exact OrderedRing.mul_nonneg (vonMangoldt_nonneg k) (log_natCast_nonneg hk)

/-- `(Λ ∗ Λ)(k) ≥ 0`. -/
theorem vmConv_nonneg (k : Nat) : 0 ≤ vmConv k := by
  unfold vmConv dsum; apply fsum_nonneg; intro d; split
  · exact OrderedRing.mul_nonneg (vonMangoldt_nonneg _) (vonMangoldt_nonneg _)
  · grind

/-- `a(k) ≥ Λ(k) log k ≥ 0`. -/
theorem selA_ge (k : Nat) : vonMangoldt k * R.log (k : R) ≤ selA k := by
  unfold selA; have := vmConv_nonneg k; grind

/-- `a(k) ≥ 0`. -/
theorem selA_nonneg (k : Nat) : 0 ≤ selA k := by
  have := selA_ge k; have := vonMangoldt_log_nonneg k; grind

/-- The summatory function `A(N) = Σ_{k ≤ N} a(k)`. -/
noncomputable def bigA (N : Nat) : R := fsum selA (N + 1)

/-- **`A(N) = 2N log N + O(N)`** (Selberg's formula): `|A(N) − 2N log N| ≤ KA · N`
for all `N` (also `N = 0`). -/
theorem bigA_bounds (N : Nat) :
    abs (bigA N - 2 * (N : R) * R.log (N : R)) ≤ KA * (N : R) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · unfold bigA; simp only [fsum_succ, fsum_zero, selA_zero]
    rw [show ((0 : Nat) : R) = 0 by grind]
    rw [show (0 : R) + 0 - 2 * 0 * R.log 0 = 0 by grind, abs_zero]; grind
  · have := selberg_symmetry_conv hN
    unfold bigA selA; rw [fsum_add]; unfold KA; exact this

/-- `A` is non-decreasing. -/
theorem bigA_mono {m n : Nat} (h : m ≤ n) : bigA m ≤ bigA n := by
  unfold bigA; exact fsum_mono selA_nonneg (by omega)

/-- `A(n) − A(m) = Σ_{m < k ≤ n} a(k)`. -/
theorem bigA_sub {m n : Nat} (h : m ≤ n) :
    bigA n - bigA m = fsum (fun j => selA (m + 1 + j)) (n - m) := by
  unfold bigA
  rw [show n + 1 = (m + 1) + (n - m) by omega, fsum_split]; grind

/-! ## The short-interval bound -/

/-- **Primes are not too dense in short intervals.** For `1 ≤ m ≤ n`:
`(ψ(n) − ψ(m)) log m ≤ 2(n − m)(log n + 1) + 2 KA n`. -/
theorem psi_short_interval {m n : Nat} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (psi n - psi m) * R.log (m : R) ≤
      2 * ((n : R) - (m : R)) * (R.log (n : R) + 1) + 2 * KA * (n : R) := by
  have hlm := log_natCast_nonneg hm
  -- `log m · (ψ(n) − ψ(m)) ≤ A(n) − A(m)`.
  have h1 : (psi n - psi m) * R.log (m : R) ≤ bigA n - bigA m := by
    rw [bigA_sub hmn, psi_eq_sum_vonMangoldt, psi_eq_sum_vonMangoldt,
      show n + 1 = (m + 1) + (n - m) by omega, fsum_split]
    rw [show fsum vonMangoldt (m + 1) + fsum (fun k => vonMangoldt (m + 1 + k)) (n - m) -
      fsum vonMangoldt (m + 1) = fsum (fun k => vonMangoldt (m + 1 + k)) (n - m) by grind,
      ← fsum_mul_const]
    apply fsum_le_fsum'; intro j _
    have hl := log_le_log (natCast_pos' hm) (natCast_le' (show m ≤ m + 1 + j by omega))
    have := OrderedRing.mul_le_mul_of_nonneg_left hl (vonMangoldt_nonneg (m + 1 + j))
    have := selA_ge (m + 1 + j)
    grind
  -- `A(n) − A(m) ≤ 2n log n − 2m log m + KA (n + m)`.
  have hAn := bigA_bounds n
  have hAm := bigA_bounds m
  rw [abs_le] at hAn hAm
  -- `m (log n − log m) ≤ n − m`.
  have hm0 : (0 : R) < (m : R) := natCast_pos' hm
  have h2 : (m : R) * (R.log (n : R) - R.log (m : R)) ≤ (n : R) - (m : R) := by
    have hq : (1 : R) ≤ (n : R) / (m : R) := by
      have : (m : R) ≤ (n : R) := natCast_le' hmn
      have e : (m : R) / (m : R) = 1 := by have : (m : R) ≠ 0 := by grind
                                           grind
      have := OrderedRing.mul_le_mul_of_nonneg_right this
        (show 0 ≤ (m : R)⁻¹ by have := div_pos (show (0 : R) < 1 by grind) hm0; grind)
      grind
    have := log_le_sub_one hq
    rw [log_div' (natCast_pos' (by omega)) hm0] at this
    have := OrderedRing.mul_le_mul_of_nonneg_left this (Std.le_of_lt hm0)
    have e : (m : R) * ((n : R) / (m : R) - 1) = (n : R) - (m : R) := by
      have : (m : R) ≠ 0 := by grind
      grind
    grind
  have h3 : (m : R) ≤ (n : R) := natCast_le' hmn
  have hKA := KA_nonneg
  have k1 := OrderedRing.mul_le_mul_of_nonneg_left h3 hKA
  grind

/-! ## The logarithmic average of the weights -/

/-- `Σ_{1 ≤ j ≤ N} log j / j ≤ ½ log² N + ½ − 1/(2N)` for `N ≥ 1`. -/
theorem sum_log_div_le {N : Nat} (hN1 : 1 ≤ N) :
    fsum (fun j => if 1 ≤ j then R.log (j : R) * (1 / (j : R)) else 0) (N + 1) ≤
      R.log (N : R) * R.log (N : R) / 2 + 1 / 2 - 1 / (2 * (N : R)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  clear hN1
  induction n with
  | zero =>
    simp only [Nat.zero_add, fsum_succ, fsum_zero, show ¬ 1 ≤ 0 by omega, Nat.le_refl, ↓reduceIte]
    rw [show ((1 : Nat) : R) = 1 by grind, R.log_one]; grind
  | succ N' ih =>
    generalize hNd : N' + 1 = N at ih ⊢
    have hN : 1 ≤ N := by omega
    rw [fsum_succ]
    simp only [show 1 ≤ N + 1 by omega, ↓reduceIte]
    obtain ⟨b1, b2⟩ := log_succ_sub_bounds hN
    have hu : (0 : R) < (N : R) := natCast_pos' hN
    have ec : ((N + 1 : Nat) : R) = (N : R) + 1 := by grind
    rw [ec] at b1 b2 ⊢
    have hL0p : 0 ≤ R.log (N : R) := log_natCast_nonneg hN
    generalize R.log ((N : R) + 1) = L1 at *
    generalize R.log (N : R) = L0 at *
    have hD : 0 ≤ L1 - L0 := by
      apply Classical.byContradiction; intro h
      have := OrderedRing.mul_lt_mul_of_pos_left (show L1 - L0 < 0 by grind)
        (show (0 : R) < (N : R) + 1 by grind)
      grind
    have hv : (N : R) + 1 ≠ 0 := by grind
    have hn0 : (N : R) ≠ 0 := by grind
    have key : L1 * (1 / ((N : R) + 1)) + 1 / (2 * ((N : R) + 1)) ≤
        (L1 * L1 - L0 * L0) / 2 + 1 / (2 * (N : R)) := by
      apply le_of_mul_le_mul_right' (C := 2 * (N : R) * ((N : R) + 1)) _
        (by have := OrderedRing.mul_pos hu (show (0 : R) < (N : R) + 1 by grind); grind)
      have e1 : (L1 * (1 / ((N : R) + 1)) + 1 / (2 * ((N : R) + 1))) *
          (2 * (N : R) * ((N : R) + 1)) = 2 * (N : R) * L1 + (N : R) := by grind
      have e2 : ((L1 * L1 - L0 * L0) / 2 + 1 / (2 * (N : R))) * (2 * (N : R) * ((N : R) + 1)) =
          (N : R) * (((N : R) + 1) * (L1 - L0)) * (L1 + L0) + ((N : R) + 1) := by grind
      rw [e1, e2]
      have k1 := OrderedRing.mul_le_mul_of_nonneg_right b2 (show 0 ≤ (N : R) * (L1 + L0) by
        have := OrderedRing.mul_nonneg (Std.le_of_lt hu) (show 0 ≤ L1 + L0 by grind); grind)
      have k2 : (N : R) * (L1 - L0) ≤ 1 := b1
      grind
    grind

/-- The telescoping weight `w(k) = 1/(k(k+1))`. -/
noncomputable def wt (k : Nat) : R := 1 / ((k : R) * ((k : R) + 1))

/-- `w(k) ≥ 0`. -/
theorem wt_nonneg (k : Nat) : 0 ≤ wt k := by
  unfold wt
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [show ((0 : Nat) : R) = 0 by grind, show (0 : R) * (0 + 1) = 0 by grind]
    have : (1 : R) / 0 = 0 := by grind
    rw [this]; grind
  · have hk0 : (0 : R) < (k : R) := natCast_pos' hk
    exact Std.le_of_lt (div_pos (by grind)
      (OrderedRing.mul_pos hk0 (by grind)))

/-- **Abel summation for the weights.**
`Σ_{k ≤ N} a(k)/k = A(N)/N + Σ_{k < N} A(k)/(k(k+1))`. -/
theorem abel_selA (N : Nat) :
    fsum (fun k => selA k * (1 / (k : R))) (N + 1) =
      bigA N * (1 / (N : R)) + fsum (fun k => bigA k * wt k) N := by
  induction N with
  | zero =>
    simp only [fsum_succ, fsum_zero, selA_zero]
    unfold bigA; simp only [fsum_succ, fsum_zero, selA_zero]; grind
  | succ N ih =>
    rw [fsum_succ, ih, fsum_succ (n := N)]
    have hA : bigA (N + 1) = bigA N + selA (N + 1) := by unfold bigA; rw [fsum_succ (n := N + 1)]
    rw [hA]
    have ec : ((N + 1 : Nat) : R) = (N : R) + 1 := by grind
    rw [ec]; unfold wt
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have : bigA 0 = 0 := by unfold bigA; simp only [fsum_succ, fsum_zero, selA_zero]; grind
      rw [this]; grind
    · have hu : (N : R) ≠ 0 := by have : (0 : R) < (N : R) := natCast_pos' hN
                                  grind
      have hv : (N : R) + 1 ≠ 0 := by have := natCast_nonneg' N; grind
      grind

/-- `H(N) ≤ log N + 2` for `N ≥ 1`. -/
theorem harmonic_le {N : Nat} (hN : 1 ≤ N) : harmonic N ≤ R.log (N : R) + 2 := by
  obtain ⟨γ, _, hγ1, hγ⟩ := exists_euler_gamma
  obtain ⟨_, h2⟩ := hγ N hN
  have : harmonic N - R.log (N : R) - γ ≤ 1 := by
    have := OrderedRing.mul_le_mul_of_nonneg_right (one_le_natCast hN) (hγ N hN).1; grind
  grind

/-- `log N ≤ H(N)` for `N ≥ 1`. -/
theorem harmonic_ge {N : Nat} (hN : 1 ≤ N) : R.log (N : R) ≤ harmonic N := by
  obtain ⟨γ, hγ0, _, hγ⟩ := exists_euler_gamma
  have := (hγ N hN).1; grind

/-- `H(N) = Σ_{k < N} 1/(k+1)`. -/
theorem harmonic_eq_shift (N : Nat) : harmonic N = fsum (fun k => 1 / ((k : R) + 1)) N := by
  unfold harmonic; rw [fsum_succ']
  simp only [show ¬ 1 ≤ 0 by omega, show ∀ k : Nat, 1 ≤ k + 1 from fun k => by omega, ↓reduceIte]
  rw [show (0 : R) + fsum (fun k => 1 / ((k + 1 : Nat) : R)) N =
    fsum (fun k => 1 / ((k + 1 : Nat) : R)) N by grind]
  apply fsum_congr; intro k _; rw [show ((k + 1 : Nat) : R) = (k : R) + 1 by grind]

/-- **The logarithmic average of the Selberg weights.** For `N ≥ 1`,
`Σ_{k ≤ N} a(k)/k ≤ log² N + (2 + KA) log N + 3 KA + 1`. -/
theorem sum_selA_div_le {N : Nat} (hN : 1 ≤ N) :
    fsum (fun k => selA k * (1 / (k : R))) (N + 1) ≤
      R.log (N : R) * R.log (N : R) + (2 + KA) * R.log (N : R) + 3 * KA + 1 := by
  rw [abel_selA]
  have hKA := KA_nonneg
  have hN0 : (0 : R) < (N : R) := natCast_pos' hN
  have hl0 := log_natCast_nonneg hN
  -- The boundary term.
  have hb : bigA N * (1 / (N : R)) ≤ 2 * R.log (N : R) + KA := by
    have h := bigA_bounds N; rw [abs_le] at h
    apply le_of_mul_le_mul_right' (C := (N : R)) _ hN0
    have : (N : R) ≠ 0 := by grind
    have e : bigA N * (1 / (N : R)) * (N : R) = bigA N := by grind
    rw [e]; grind
  -- The sum term, compared termwise.
  have hs : fsum (fun k => bigA k * wt k) N ≤
      2 * fsum (fun k => if 1 ≤ k + 1 then R.log ((k + 1 : Nat) : R) * (1 / ((k + 1 : Nat) : R))
        else 0) N + KA * fsum (fun k => 1 / ((k : R) + 1)) N := by
    rw [← fsum_const_mul, ← fsum_const_mul, ← fsum_add]
    apply fsum_le_fsum'; intro k _
    simp only [show 1 ≤ k + 1 by omega, ↓reduceIte]
    have ec : ((k + 1 : Nat) : R) = (k : R) + 1 := by grind
    rw [ec]
    have hv : (0 : R) < (k : R) + 1 := by have := natCast_nonneg' k; grind
    have hlk : 0 ≤ R.log ((k : R) + 1) := by
      rw [← ec]; exact log_natCast_nonneg (by omega)
    have hterm : 0 ≤ R.log ((k : R) + 1) * (1 / ((k : R) + 1)) :=
      OrderedRing.mul_nonneg hlk (Std.le_of_lt (div_pos (by grind) hv))
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : bigA 0 = 0 := by unfold bigA; simp only [fsum_succ, fsum_zero, selA_zero]; grind
      rw [this]
      have := div_pos (show (0 : R) < 1 by grind) hv
      grind
    · have hk0 : (0 : R) < (k : R) := natCast_pos' hk
      have h := bigA_bounds k; rw [abs_le] at h
      have hlk' : R.log (k : R) ≤ R.log ((k : R) + 1) := log_le_log hk0 (by grind)
      have hw := wt_nonneg k
      have k1 : bigA k * wt k ≤ (2 * (k : R) * R.log (k : R) + KA * (k : R)) * wt k :=
        OrderedRing.mul_le_mul_of_nonneg_right (by grind) hw
      have e : (2 * (k : R) * R.log (k : R) + KA * (k : R)) * wt k =
          (2 * R.log (k : R) + KA) * (1 / ((k : R) + 1)) := by
        unfold wt; have : (k : R) ≠ 0 := by grind
        have : (k : R) + 1 ≠ 0 := by grind
        grind
      have k2 := OrderedRing.mul_le_mul_of_nonneg_right hlk'
        (Std.le_of_lt (div_pos (show (0 : R) < 1 by grind) hv))
      grind
  -- Evaluate the two sums.
  have h1 : fsum (fun k => if 1 ≤ k + 1 then R.log ((k + 1 : Nat) : R) * (1 / ((k + 1 : Nat) : R))
      else 0) N ≤ R.log (N : R) * R.log (N : R) / 2 + 1 / 2 := by
    have := sum_log_div_le hN
    rw [fsum_succ'] at this
    simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte] at this
    have : 0 ≤ 1 / (2 * (N : R)) := Std.le_of_lt (div_pos (by grind) (by grind))
    grind
  have h2 : fsum (fun k => 1 / ((k : R) + 1)) N ≤ R.log (N : R) + 2 := by
    rw [← harmonic_eq_shift]; exact harmonic_le hN
  have k3 := OrderedRing.mul_le_mul_of_nonneg_left h2 hKA
  grind

/-! ## The mean value of the remainder -/

/-- `Σ_{n ≤ N} ψ(n)/(n(n+1)) = Σ_{k ≤ N} Λ(k) (1/k − 1/(N+1))`. -/
theorem sum_psi_wt (N : Nat) :
    fsum (fun n => psi n * wt n) (N + 1) =
      fsum (fun k => vonMangoldt k * (1 / (k : R) - 1 / ((N : R) + 1))) (N + 1) := by
  induction N with
  | zero =>
    simp only [fsum_succ, fsum_zero, psi_zero, vonMangoldt_zero]; grind
  | succ N ih =>
    rw [fsum_succ, ih]
    have e : fsum (fun k => vonMangoldt k * (1 / (k : R) - 1 / (((N + 1 : Nat) : R) + 1))) (N + 1 + 1)
        = fsum (fun k => vonMangoldt k * (1 / (k : R) - 1 / ((N : R) + 1))) (N + 1) +
          psi N * (1 / ((N : R) + 1) - 1 / ((N : R) + 2)) +
          vonMangoldt (N + 1) * (1 / ((N : R) + 1) - 1 / ((N : R) + 2)) := by
      rw [fsum_succ, psi_eq_sum_vonMangoldt, ← fsum_mul_const, ← fsum_add]
      have ec : ((N + 1 : Nat) : R) = (N : R) + 1 := by grind
      rw [ec, show (N : R) + 1 + 1 = (N : R) + 2 by grind]
      congr 1
      apply fsum_congr; intro k _; grind
    rw [e]
    have hpsi : psi (N + 1) = psi N + vonMangoldt (N + 1) := by
      rw [psi_eq_sum_vonMangoldt, psi_eq_sum_vonMangoldt, fsum_succ (n := N + 1)]
    rw [hpsi]; unfold wt
    have ec : ((N + 1 : Nat) : R) = (N : R) + 1 := by grind
    rw [ec]
    have hv : (N : R) + 1 ≠ 0 := by have := natCast_nonneg' N; grind
    have hv2 : (N : R) + 2 ≠ 0 := by have := natCast_nonneg' N; grind
    have e2 : 1 / ((N : R) + 1) - 1 / ((N : R) + 2) = 1 / (((N : R) + 1) * ((N : R) + 1 + 1)) := by
      grind
    rw [e2]; grind

/-- `Σ_{n ≤ N} n/(n(n+1)) = H(N+1) − 1`. -/
theorem sum_id_wt (N : Nat) : fsum (fun n => (n : R) * wt n) (N + 1) = harmonic (N + 1) - 1 := by
  induction N with
  | zero =>
    simp only [fsum_succ, fsum_zero]
    rw [show (0 + 1 : Nat) = 1 from rfl, harmonic_one, show ((0 : Nat) : R) = 0 by grind]; grind
  | succ N ih =>
    rw [fsum_succ, ih, harmonic_succ (N + 1)]
    unfold wt
    have ec : ((N + 1 : Nat) : R) = (N : R) + 1 := by grind
    rw [ec]
    have hv : (N : R) + 1 ≠ 0 := by have := natCast_nonneg' N; grind
    have hv2 : (N : R) + 1 + 1 ≠ 0 := by have := natCast_nonneg' N; grind
    grind

/-- The mean-value constant `B = 3 + log 1024`. -/
noncomputable def Bm : R := 3 + R.log 1024

/-- **The remainder has mean value zero.** For every `N`,
`|Σ_{n ≤ N} R(n)/(n(n+1))| ≤ B`. -/
theorem abs_sum_rem_wt_le (N : Nat) : abs (fsum (fun n => rem n * wt n) (N + 1)) ≤ Bm := by
  have hc := log1024_nonneg
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [fsum_succ, fsum_zero, rem_zero]
    rw [show (0 : R) + 0 * wt 0 = 0 by grind, abs_zero]; unfold Bm; grind
  have e : fsum (fun n => rem n * wt n) (N + 1) =
      fsum (fun k => vonMangoldt k * (1 / (k : R))) (N + 1) - psi N * (1 / ((N : R) + 1)) -
        (harmonic (N + 1) - 1) := by
    rw [← sum_id_wt, show fsum (fun n => rem n * wt n) (N + 1) =
      fsum (fun n => psi n * wt n) (N + 1) - fsum (fun n => (n : R) * wt n) (N + 1) by
        rw [← fsum_sub]; apply fsum_congr; intro n _; unfold rem; grind, sum_psi_wt]
    congr 1
    rw [psi_eq_sum_vonMangoldt, ← fsum_mul_const, ← fsum_sub]
    apply fsum_congr; intro k _; grind
  rw [e]
  obtain ⟨m1, m2⟩ := mertens_vonMangoldt hN
  have hv : (0 : R) < (N : R) + 1 := by have := natCast_nonneg' N; grind
  have hP0 : 0 ≤ psi N * (1 / ((N : R) + 1)) :=
    OrderedRing.mul_nonneg (psi_nonneg N) (Std.le_of_lt (div_pos (by grind) hv))
  have hP1 : psi N * (1 / ((N : R) + 1)) ≤ R.log 1024 := by
    apply le_of_mul_le_mul_right' (C := (N : R) + 1) _ hv
    have : (N : R) + 1 ≠ 0 := by grind
    have e : psi N * (1 / ((N : R) + 1)) * ((N : R) + 1) = psi N := by grind
    rw [e]; have := psi_le N; grind
  have hH1 := harmonic_le (N := N + 1) (by omega)
  have hH2 := harmonic_ge (N := N + 1) (by omega)
  have hl1 : R.log (N : R) ≤ R.log ((N + 1 : Nat) : R) :=
    log_le_log (natCast_pos' hN) (natCast_le' (by omega))
  have hl2 := (log_succ_sub_bounds hN).1
  have hl3 : R.log ((N + 1 : Nat) : R) - R.log (N : R) ≤ 1 := by
    have := OrderedRing.mul_le_mul_of_nonneg_right (one_le_natCast hN) (show 0 ≤ R.log ((N + 1 : Nat) : R) - R.log (N : R) by grind)
    grind
  unfold Bm; rw [abs_le]; constructor <;> grind

end Foundations.NumberTheory.PNT
