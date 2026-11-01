import Foundations.NumberTheory.PNTSelbergEstimates

/-!
# Toward the prime number theorem VIII: Selberg's symmetry formula

In the spring of 1948 Atle Selberg, then at the Institute for Advanced Study, proved the asymptotic
formula

  `ψ(x) log x + Σ_{n ≤ x} Λ(n) ψ(x/n) = 2x log x + O(x)`,

equivalently `Σ_{p ≤ x} log² p + Σ_{pq ≤ x} log p log q = 2x log x + O(x)`. It is called a
*symmetry* formula because it weighs a prime `p` and the products `pq` symmetrically; heuristically
it says that the primes and the products of two primes together have exactly the density
`2 log x` they would have if `ψ(x) ∼ x`. Unlike `ψ(x) ∼ x` itself, it can be proved by
manipulating finite sums — and from it the prime number theorem follows by a delicate but purely
real-variable ("tauberian") argument. Erdős, learning of the formula, used it to prove that
`p_{n+1}/p_n → 1`; Selberg then completed a proof of the prime number theorem, and both published
elementary proofs in 1949 (Selberg in the *Annals of Mathematics*, Erdős in the *Proceedings of
the National Academy of Sciences*). How much each owed to the other became a bitter dispute,
documented in letters of the time; Selberg's Fields Medal (1950) cited this work, and Erdős
received the Cole Prize (1951) for his paper. We take no side.

Our proof follows the Tatuzawa–Iseki route (previous files). Apply the identity
`Σ_{d ≤ N} μ(d) Γ(d) = Φ(1) log N + Σ_{n ≤ N} Λ(n) Φ(n)` to

  `Φ(k) = ψ(⌊N/k⌋) − (N/k − c)`, with `c = γ + 1`.

On the right this gives `ψ(N) log N + Σ Λ(n) ψ(N/n)` minus
`(N − c) log N + N Σ Λ(n)/n − c ψ(N) = 2N log N + O(N)` (Mertens). On the left, with
`M = ⌊N/d⌋` and `y = N/d`, Chebyshev's identity gives
`Σ_{n ≤ M} Φ(dn) = log M! − y H(M) + cM`, and Stirling plus Euler's constant show this is
`O(log y)`; so `|Γ(d)| ≤ 4 log²(N/d) + 3`, and the logarithmic average
`Σ_{d ≤ N} log²(N/d) ≤ 6N` makes the whole left side `O(N)`.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- The test sequence `Φ(k) = ψ(⌊N/k⌋) − (N/k − c)` for the Tatuzawa–Iseki identity. -/
noncomputable def selbergPhi (c : R) (N k : Nat) : R := psi (N / k) - ((N : R) / (k : R) - c)

/-- `Σ_{1 ≤ n ≤ M} 1 = M`. -/
theorem fsum_one_count (M : Nat) : fsum (fun n => if 1 ≤ n then (1 : R) else 0) (M + 1) = (M : R) := by
  have := fsum_count_le_div (q := 1) (by omega) M
  rw [Nat.div_one] at this
  rw [← this]; apply fsum_congr; intro n hn
  simp only [Nat.one_mul, show n ≤ M by omega, and_true]

/-- The sum `Σ_{1 ≤ n ≤ M} 1/n · y − c` equals `y H(M) − c M`. -/
theorem fsum_harmonic_affine (y c : R) (M : Nat) :
    fsum (fun n => if 1 ≤ n then y * (1 / (n : R)) - c else 0) (M + 1) =
      y * harmonic M - c * (M : R) := by
  rw [← fsum_one_count M]; unfold harmonic
  rw [← fsum_const_mul, ← fsum_const_mul, ← fsum_sub]
  apply fsum_congr; intro n _; split <;> grind

/-- **The local estimate.** For `1 ≤ d ≤ N`, with `Γ(d) = log(N/d) · Σ_{n ≤ N/d} Φ(dn)`:
`|Γ(d)| ≤ 4 log²(N/d) + 3`. -/
theorem selberg_local {γ : R} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγ : ∀ M : Nat, 1 ≤ M → 0 ≤ harmonic M - R.log (M : R) - γ ∧
      (M : R) * (harmonic M - R.log (M : R) - γ) ≤ 1)
    {N d : Nat} (hd : 1 ≤ d) (hdN : d ≤ N) :
    abs (R.log ((N : R) / (d : R)) *
      fsum (fun n => if 1 ≤ n then selbergPhi (γ + 1) N (d * n) else 0) (N / d + 1)) ≤
      4 * (R.log ((N : R) / (d : R)) * R.log ((N : R) / (d : R))) + 3 := by
  have hd0 : (0 : R) < (d : R) := natCast_pos' hd
  have hdne : (d : R) ≠ 0 := by grind
  obtain ⟨M, hMd⟩ : ∃ M, M = N / d := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact (Nat.le_div_iff_mul_le hd).2 (by omega)
  have hM0 : (0 : R) < (M : R) := natCast_pos' hM1
  obtain ⟨y, hyd⟩ : ∃ y, y = (N : R) / (d : R) := ⟨_, rfl⟩
  rw [← hyd, ← hMd]
  -- `M ≤ y ≤ M + 1`.
  have hy := div_sub_floor (N := N) hd
  rw [← hyd, ← hMd] at hy
  -- The inner sum is `log M! − y H(M) + c M`.
  have hinner : fsum (fun n => if 1 ≤ n then selbergPhi (γ + 1) N (d * n) else 0) (M + 1) =
      R.log (Arith.fact M : R) - (y * harmonic M - (γ + 1) * (M : R)) := by
    rw [← sum_psi_div, ← fsum_harmonic_affine, ← fsum_sub]
    apply fsum_congr; intro n _
    by_cases hn : 1 ≤ n
    · simp only [hn, ↓reduceIte]
      unfold selbergPhi
      have hn0 : (0 : R) < (n : R) := natCast_pos' hn
      have e1 : N / (d * n) = M / n := by rw [hMd, Nat.div_div_eq_div_mul]
      have e2 : (N : R) / ((d * n : Nat) : R) = y * (1 / (n : R)) := by
        rw [natCast_mul', hyd]
        have : (n : R) ≠ 0 := by grind
        grind
      rw [e1, e2]
    · simp only [hn, ↓reduceIte]; grind
  rw [hinner]
  -- The ingredients.
  obtain ⟨hA1, hA2⟩ := stirling_bounds hM1
  obtain ⟨hB1, hB2⟩ := hγ M hM1
  have hL0 := log_natCast_nonneg hM1
  have hy1 : (1 : R) ≤ y := by have := one_le_natCast hM1; grind
  have hy0 : (0 : R) < y := by grind
  have hLY : R.log (M : R) ≤ R.log y := log_le_log hM0 (by grind)
  have hY0 : 0 ≤ R.log y := log_nonneg' hy1
  -- Name the error terms.
  obtain ⟨A, hAd⟩ : ∃ A, A = R.log (Arith.fact M : R) + (M : R) - ((M : R) + 1 / 2) * R.log (M : R) :=
    ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = harmonic M - R.log (M : R) - γ := ⟨_, rfl⟩
  rw [← hAd] at hA1 hA2; rw [← hBd] at hB1 hB2
  have hI : R.log (Arith.fact M : R) - (y * harmonic M - (γ + 1) * (M : R)) =
      -((y - (M : R)) * (R.log (M : R) + γ)) + R.log (M : R) / 2 + A - y * B := by
    rw [hAd, hBd]; grind
  rw [hI]
  -- Bounds on the pieces.
  have k1 := OrderedRing.mul_le_mul_of_nonneg_right (show y - (M : R) ≤ 1 by grind)
    (show 0 ≤ R.log (M : R) + γ by grind)
  have k1' := OrderedRing.mul_nonneg (show 0 ≤ y - (M : R) by grind)
    (show 0 ≤ R.log (M : R) + γ by grind)
  have hB1' : B ≤ 1 := by
    have := OrderedRing.mul_le_mul_of_nonneg_right (one_le_natCast hM1) hB1; grind
  have k2 := OrderedRing.mul_le_mul_of_nonneg_right (show y ≤ (M : R) + 1 by grind) hB1
  have k2' := OrderedRing.mul_nonneg (Std.le_of_lt hy0) hB1
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = R.log y := ⟨_, rfl⟩
  rw [← hYd] at hLY hY0 ⊢
  have hIb : abs (-((y - (M : R)) * (R.log (M : R) + γ)) + R.log (M : R) / 2 + A - y * B) ≤
      Y + 3 := by
    rw [abs_le]; constructor <;> grind
  generalize -((y - (M : R)) * (R.log (M : R) + γ)) + R.log (M : R) / 2 + A - y * B = I at hIb ⊢
  rw [abs_mul, abs_of_nonneg hY0]
  have k3 := OrderedRing.mul_le_mul_of_nonneg_left hIb hY0
  have k4 : 0 ≤ (Y - 1 / 2) * (Y - 1 / 2) := by
    rcases abs_cases (Y - 1 / 2) with h | h
    · exact OrderedRing.mul_nonneg h.1 h.1
    · have := OrderedRing.mul_pos (show 0 < -(Y - 1 / 2) by grind) (show 0 < -(Y - 1 / 2) by grind)
      grind
  grind

/-- **Selberg's symmetry formula.** For every `N ≥ 1`,
`|ψ(N) log N + Σ_{n ≤ N} Λ(n) ψ(⌊N/n⌋) − 2N log N| ≤ (30 + 3 log 1024) · N`,
i.e. `ψ(x) log x + Σ_{n ≤ x} Λ(n) ψ(x/n) = 2x log x + O(x)`. -/
theorem selberg_symmetry {N : Nat} (hN : 1 ≤ N) :
    abs (psi N * R.log (N : R) + fsum (fun n => vonMangoldt n * psi (N / n)) (N + 1) -
      2 * (N : R) * R.log (N : R)) ≤ (30 + 3 * R.log 1024) * (N : R) := by
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := exists_euler_gamma
  have hN0 : (0 : R) < (N : R) := natCast_pos' hN
  have hNn := Std.le_of_lt hN0
  have TI := tatuzawa_iseki hN (selbergPhi (γ + 1) N)
  -- The left side of the identity is `O(N)`.
  obtain ⟨E, hEd⟩ : ∃ E, E = fsum (fun d => if 1 ≤ d then mobius d * (R.log ((N : R) / (d : R)) *
      fsum (fun n => if 1 ≤ n then selbergPhi (γ + 1) N (d * n) else 0) (N / d + 1)) else 0)
      (N + 1) := ⟨_, rfl⟩
  rw [← hEd] at TI
  have hE : abs E ≤ 27 * (N : R) := by
    rw [hEd]
    refine Std.le_trans (abs_fsum_le _ _) ?_
    have h1 : fsum (fun d => abs (if 1 ≤ d then mobius d * (R.log ((N : R) / (d : R)) *
        fsum (fun n => if 1 ≤ n then selbergPhi (γ + 1) N (d * n) else 0) (N / d + 1)) else 0))
        (N + 1) ≤
        fsum (fun d => if 1 ≤ d then 4 * (R.log ((N : R) / (d : R)) * R.log ((N : R) / (d : R)))
          + 3 else 0) (N + 1) := by
      apply fsum_le_fsum'; intro d hd
      by_cases hd1 : 1 ≤ d
      · simp only [hd1, ↓reduceIte]
        rw [abs_mul]
        have hl := selberg_local hγ0 hγ1 hγ hd1 (show d ≤ N by omega)
        have hm := abs_mobius_le d
        have := OrderedRing.mul_le_mul_of_nonneg_right hm (abs_nonneg (R.log ((N : R) / (d : R)) *
          fsum (fun n => if 1 ≤ n then selbergPhi (γ + 1) N (d * n) else 0) (N / d + 1)))
        grind
      · simp only [hd1, ↓reduceIte]; rw [abs_zero]; grind
    have h2 : fsum (fun d => if 1 ≤ d then 4 * (R.log ((N : R) / (d : R)) *
        R.log ((N : R) / (d : R))) + 3 else 0) (N + 1) =
        4 * fsum (fun d => if 1 ≤ d then R.log ((N : R) / (d : R)) *
          R.log ((N : R) / (d : R)) else 0) (N + 1) +
        3 * fsum (fun d => if 1 ≤ d then (1 : R) else 0) (N + 1) := by
      rw [← fsum_const_mul, ← fsum_const_mul, ← fsum_add]
      apply fsum_congr; intro d _; split <;> grind
    have h3 : fsum (fun d => if 1 ≤ d then (1 : R) else 0) (N + 1) = (N : R) := fsum_one_count N
    have h4 := sum_log_sq_le hN
    refine Std.le_trans h1 ?_
    rw [h2, h3]
    generalize fsum (fun d => if 1 ≤ d then R.log ((N : R) / (d : R)) *
          R.log ((N : R) / (d : R)) else 0) (N + 1) = S2 at h4 ⊢
    grind
  -- The right side of the identity.
  have hphi1 : selbergPhi (γ + 1) N 1 = psi N - ((N : R) - (γ + 1)) := by
    unfold selbergPhi; rw [Nat.div_one, show ((1 : Nat) : R) = 1 by grind]; grind
  have hsum : fsum (fun n => vonMangoldt n * selbergPhi (γ + 1) N n) (N + 1) =
      fsum (fun n => vonMangoldt n * psi (N / n)) (N + 1) -
        (N : R) * fsum (fun n => vonMangoldt n * (1 / (n : R))) (N + 1) +
        (γ + 1) * fsum vonMangoldt (N + 1) := by
    rw [← fsum_const_mul, ← fsum_const_mul, ← fsum_sub, ← fsum_add]
    apply fsum_congr; intro n _
    unfold selbergPhi; grind
  rw [hphi1, hsum, ← psi_eq_sum_vonMangoldt] at TI
  -- Mertens and the Chebyshev bounds.
  obtain ⟨hT1, hT2⟩ := mertens_vonMangoldt hN
  obtain ⟨T, hTd⟩ : ∃ T, T = fsum (fun n => vonMangoldt n * (1 / (n : R))) (N + 1) := ⟨_, rfl⟩
  rw [← hTd] at TI hT1 hT2
  have hk1 := OrderedRing.mul_le_mul_of_nonneg_left hT1 hNn
  have hk2 := OrderedRing.mul_le_mul_of_nonneg_left hT2 hNn
  have hpsi := psi_le N
  have hpsi0 := psi_nonneg N
  have hlog := log_natCast_le hN
  have hlog0 := log_natCast_nonneg hN
  have hc1 := OrderedRing.mul_le_mul_of_nonneg_left hlog (show 0 ≤ γ + 1 by grind)
  have hc2 := OrderedRing.mul_le_mul_of_nonneg_right (show γ + 1 ≤ 2 by grind) hNn
  have hc3 := OrderedRing.mul_le_mul_of_nonneg_left hpsi (show 0 ≤ γ + 1 by grind)
  have hc4 := OrderedRing.mul_le_mul_of_nonneg_right (show γ + 1 ≤ 2 by grind)
    (OrderedRing.mul_nonneg hNn (log_nonneg' (show (1 : R) ≤ 1024 by grind)))
  have hc5 := OrderedRing.mul_nonneg (show 0 ≤ γ + 1 by grind) hlog0
  have hc6 := OrderedRing.mul_nonneg (show 0 ≤ γ + 1 by grind) hpsi0
  rw [abs_le] at hE ⊢
  constructor <;> grind

end Foundations.NumberTheory.PNT
