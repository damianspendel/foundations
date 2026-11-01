import Foundations.NumberTheory.PNTMobius

/-!
# Toward the prime number theorem VI: the Tatuzawa–Iseki identity

Selberg's own derivation of his formula (1949) inverted the function `Λ(n) log n + (Λ ∗ Λ)(n)`
with the Möbius function directly. A tidier route, due to **Tatuzawa and Iseki** (1951), packages
the inversion once and for all in an identity about arbitrary functions: if

  `G(x) = log x · Σ_{n ≤ x} F(x/n)`,

then

  `F(x) log x + Σ_{n ≤ x} Λ(n) F(x/n) = Σ_{d ≤ x} μ(d) G(x/d)`.

The left side is "Selberg-shaped"; the right side is a Möbius average of `G`. One applies it to
two functions `F₁ = ψ` and `F₂(x) = x − c` whose `G`'s nearly agree, so that the difference of the
right sides is small, and reads off the asymptotics of the left side.

We prove the identity for an integer `x = N`, with the values `F(N/n)` given as an arbitrary
sequence `Φ(n)` (this covers both `ψ(⌊N/n⌋)` and `N/n − c`): with
`Γ(d) = log(N/d) · Σ_{n ≤ N/d} Φ(dn)` (here `Φ(dn)` plays the role of `F(x/(dn))`),

  `Σ_{d ≤ N} μ(d) Γ(d) = Φ(1) log N + Σ_{n ≤ N} Λ(n) Φ(n)`.

The proof reorganises the double sum over `d·n ≤ N` as a sum over `m = dn` and its divisors
(the **hyperbola reindexing**), and then uses `Σ_{d ∣ m} μ(d) = [m = 1]` and
`Σ_{d ∣ m} μ(d) log d = −Λ(m)` from the previous file.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- `Λ(0) = 0`. -/
theorem vonMangoldt_zero : vonMangoldt 0 = 0 := by
  unfold vonMangoldt
  simp only [fsum_succ, fsum_zero]
  have : ¬ (Prime 0 ∧ 1 ≤ 0 ∧ 0 ^ 0 = 0) := fun h => by have := h.1.1; omega
  simp only [this, ↓reduceIte]; grind

/-- **The hyperbola reindexing.** `Σ_{d ≤ N} Σ_{n ≤ N/d} g(d, n) = Σ_{m ≤ N} Σ_{d ∣ m} g(d, m/d)`
(all indices `≥ 1`): both sides run over the pairs `(d, n)` with `dn ≤ N`. -/
theorem hyperbola (N : Nat) (g : Nat → Nat → R) :
    fsum (fun d => if 1 ≤ d then fsum (fun n => if 1 ≤ n then g d n else 0) (N / d + 1) else 0)
        (N + 1) =
      fsum (fun m => if 1 ≤ m then dsum (fun d => g d (m / d)) m else 0) (N + 1) := by
  -- Both sides equal `Σ_{d, n ≤ N} [1 ≤ d, 1 ≤ n, dn ≤ N] g(d, n)`.
  have lhs : ∀ d, d < N + 1 →
      (if 1 ≤ d then fsum (fun n => if 1 ≤ n then g d n else 0) (N / d + 1) else 0) =
        fsum (fun n => if 1 ≤ d ∧ 1 ≤ n ∧ d * n ≤ N then g d n else 0) (N + 1) := by
    intro d hd
    by_cases hd1 : 1 ≤ d
    · simp only [hd1, true_and, ↓reduceIte]
      rw [← fsum_congr_bound (a := fun n => if 1 ≤ n ∧ d * n ≤ N then g d n else 0)
        (show N / d + 1 ≤ N + 1 by have := Nat.div_le_self N d; omega) (fun n h1 _ => by
          have : ¬ (1 ≤ n ∧ d * n ≤ N) := fun h =>
            absurd ((Nat.le_div_iff_mul_le hd1).2 (by rw [Nat.mul_comm]; exact h.2)) (by omega)
          simp only [this, ↓reduceIte])]
      apply fsum_congr; intro n hn
      have : d * n ≤ N := by
        have := (Nat.le_div_iff_mul_le hd1).1 (show n ≤ N / d by omega)
        rw [Nat.mul_comm]; exact this
      simp only [this, and_true]
    · simp only [hd1, false_and, ↓reduceIte]; exact (fsum_zeros _).symm
  have rhs : ∀ m, m < N + 1 →
      (if 1 ≤ m then dsum (fun d => g d (m / d)) m else 0) =
        fsum (fun d => fsum (fun n => if m = d * n ∧ 1 ≤ d ∧ 1 ≤ n then g d n else 0) (N + 1))
          (N + 1) := by
    intro m hm
    by_cases hm1 : 1 ≤ m
    · simp only [hm1, ↓reduceIte]
      rw [dsum_eq_fsum hm1 (show m + 1 ≤ N + 1 by omega)]
      apply fsum_congr; intro d _
      by_cases hdm : d ∣ m
      · simp only [hdm, ↓reduceIte]
        have hd0 := pos_of_dvd' hm1 hdm
        have hq := one_le_div_of_dvd hm1 hdm
        rw [fsum_congr (b := fun n => if n = m / d then g d (m / d) else 0) (fun n _ => by
          by_cases hn : n = m / d
          · subst hn
            have : m = d * (m / d) := (Nat.mul_div_cancel' hdm).symm
            simp only [← this, show 1 ≤ d by omega, hq, ↓reduceIte, and_self]
          · have : ¬ (m = d * n ∧ 1 ≤ d ∧ 1 ≤ n) := fun h => hn (by
              rw [h.1, Nat.mul_div_cancel_left n hd0])
            simp only [this, hn, ↓reduceIte])]
        rw [fsum_ite_eq]
        have := Nat.div_le_self m d
        simp only [show m / d < N + 1 by omega, ↓reduceIte]
      · simp only [hdm, ↓reduceIte]
        rw [fsum_congr (b := fun _ => 0) (fun n _ => by
          have : ¬ (m = d * n ∧ 1 ≤ d ∧ 1 ≤ n) := fun h => hdm ⟨n, h.1⟩
          simp only [this, ↓reduceIte]), fsum_zeros]
    · simp only [hm1, ↓reduceIte]
      rw [fsum_congr (b := fun _ => 0) (fun d _ => by
        rw [fsum_congr (b := fun _ => 0) (fun n _ => by
          have : ¬ (m = d * n ∧ 1 ≤ d ∧ 1 ≤ n) := fun h => by
            have := Nat.mul_le_mul h.2.1 h.2.2; omega
          simp only [this, ↓reduceIte]), fsum_zeros]), fsum_zeros]
  rw [fsum_congr lhs, fsum_congr rhs]
  symm
  rw [fsum_swap]
  apply fsum_congr; intro d _
  rw [fsum_swap]
  apply fsum_congr; intro n _
  rw [fsum_congr (b := fun m => if m = d * n then
      (if 1 ≤ d ∧ 1 ≤ n then g d n else 0) else 0) (fun m _ => by
    by_cases h : m = d * n
    · subst h; by_cases h' : 1 ≤ d ∧ 1 ≤ n <;> simp [h']
    · simp only [h, false_and, ↓reduceIte])]
  rw [fsum_ite_eq]
  by_cases h1 : 1 ≤ d ∧ 1 ≤ n <;> by_cases h2 : d * n ≤ N <;>
    simp [h1, h2, show d * n < N + 1 ↔ d * n ≤ N by omega]

/-- **The Tatuzawa–Iseki identity** (integer form). For `N ≥ 1` and any `Φ : ℕ → ℝ`, with
`Γ(d) = log(N/d) · Σ_{1 ≤ n ≤ N/d} Φ(dn)`:
`Σ_{1 ≤ d ≤ N} μ(d) Γ(d) = Φ(1) log N + Σ_{n ≤ N} Λ(n) Φ(n)`. -/
theorem tatuzawa_iseki {N : Nat} (hN : 1 ≤ N) (Φ : Nat → R) :
    fsum (fun d => if 1 ≤ d then mobius d * (R.log ((N : R) / (d : R)) *
        fsum (fun n => if 1 ≤ n then Φ (d * n) else 0) (N / d + 1)) else 0) (N + 1) =
      Φ 1 * R.log (N : R) + fsum (fun n => vonMangoldt n * Φ n) (N + 1) := by
  have hN0 : (0 : R) < (N : R) := natCast_pos' hN
  -- Move the factors inside and apply the hyperbola reindexing.
  have e1 : fsum (fun d => if 1 ≤ d then mobius d * (R.log ((N : R) / (d : R)) *
        fsum (fun n => if 1 ≤ n then Φ (d * n) else 0) (N / d + 1)) else 0) (N + 1) =
      fsum (fun d => if 1 ≤ d then fsum (fun n => if 1 ≤ n then
        mobius d * R.log ((N : R) / (d : R)) * Φ (d * n) else 0) (N / d + 1) else 0) (N + 1) := by
    apply fsum_congr; intro d _
    split
    · rw [← fsum_const_mul, ← fsum_const_mul]
      apply fsum_congr; intro n _; split <;> grind
    · rfl
  rw [e1, hyperbola N (fun d n => mobius d * R.log ((N : R) / (d : R)) * Φ (d * n))]
  -- Evaluate the inner divisor sums.
  have e2 : ∀ m, m < N + 1 → (if 1 ≤ m then dsum (fun d => mobius d *
      R.log ((N : R) / (d : R)) * Φ (d * (m / d))) m else 0) =
      (if m = 1 then Φ 1 * R.log (N : R) else 0) + vonMangoldt m * Φ m := by
    intro m _
    by_cases hm : 1 ≤ m
    · simp only [hm, ↓reduceIte]
      have e3 : dsum (fun d => mobius d * R.log ((N : R) / (d : R)) * Φ (d * (m / d))) m =
          Φ m * (R.log (N : R) * dsum mobius m - dsum (fun d => mobius d * R.log (d : R)) m) := by
        rw [dsum_const_mul]; unfold dsum
        rw [← fsum_sub, ← fsum_const_mul]
        apply fsum_congr; intro d _
        by_cases hdm : d ∣ m
        · simp only [hdm, ↓reduceIte]
          have hd0 := pos_of_dvd' hm hdm
          rw [Nat.mul_div_cancel' hdm, log_div' hN0 (natCast_pos' hd0)]
          grind
        · simp only [hdm, ↓reduceIte]; grind
      rw [e3, dsum_mobius hm, vonMangoldt_eq_neg_dsum hm]
      by_cases h1 : m = 1
      · subst h1; simp only [↓reduceIte]; grind
      · simp only [h1, ↓reduceIte]; grind
    · obtain rfl : m = 0 := by omega
      simp only [show ¬ 1 ≤ 0 by omega, show (0 : Nat) ≠ 1 by omega, ↓reduceIte, vonMangoldt_zero]
      grind
  rw [fsum_congr e2, fsum_add, fsum_ite_eq]
  simp only [show 1 < N + 1 by omega, ↓reduceIte]

end Foundations.NumberTheory.PNT
