import Foundations.NumberTheory.LFunction

/-!
# Two small error terms: higher prime powers, and primes dividing `q`

The von Mangoldt function charges `log p` not only to the primes `p` but to all prime powers
`pᵏ`. When we finally count primes `p ≡ a (mod q)` we must check that the powers with `k ≥ 2`
contribute only a bounded amount to `Σ Λ(n)/n`:

  `Σ_{pᵏ ≤ N, k ≥ 2} log p / pᵏ ≤ 4`.

Summing the geometric series in `k` leaves `≤ 2 Σ_p log p / p²`, and `Σ_{n ≥ 1} log n / n² ≤ 2`
follows by telescoping against `(2 + log n)/n`, using `log (n+1) − log n ≤ 1/n`.

Similarly, the prime powers `pᵏ` with `p ∣ q` — exactly those `n` with `Λ(n) ≠ 0` that the
principal character modulo `q` discards — contribute at most `2q`, since
`Σ_{k ≥ 1} log p / pᵏ ≤ 2 log p / p ≤ 2` and there are at most `q` such primes.
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- A tail of the geometric series: `Σ_{k ≥ j} rᵏ ≤ 2 rʲ` for `0 ≤ r ≤ 1/2`. -/
theorem gsum_geom_tail_le {r : R} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (j K : Nat) :
    gsum (fun k => if j ≤ k then r ^ k else 0) K ≤ 2 * r ^ j := by
  have key : ∀ K, gsum (fun k => if j ≤ k then r ^ k else 0) K +
      (if j ≤ K then 2 * r ^ K else 2 * r ^ j) ≤ 2 * r ^ j := by
    intro K
    induction K with
    | zero =>
      rw [gsum_nil]
      by_cases h : j ≤ 0
      · rw [ite_eq_left h, show j = 0 by omega]; grind
      · rw [ite_eq_right h]; grind
    | succ K ih =>
      rw [gsum_succ]
      by_cases h : j ≤ K
      · rw [ite_eq_left h] at ih
        rw [ite_eq_left h, ite_eq_left (by omega)]
        have hp := pow_nonneg' hr0 K
        have : r ^ (K + 1) = r ^ K * r := rfl
        have := OrderedRing.mul_le_mul_of_nonneg_left hr hp
        grind
      · rw [ite_eq_right h] at ih
        rw [ite_eq_right h]
        by_cases h2 : j = K + 1
        · subst h2; rw [ite_eq_left (Nat.le_refl _)]; grind
        · rw [ite_eq_right (by omega)]; grind
  have := key K
  have : 0 ≤ (if j ≤ K then 2 * r ^ K else 2 * r ^ j) := by
    split
    · have := pow_nonneg' hr0 K; grind
    · have := pow_nonneg' hr0 j; grind
  grind

/-- `1 / pᵏ = (1/p)ᵏ`. -/
theorem one_div_pow_cast (p k : Nat) : 1 / ((p ^ k : Nat) : R) = (1 / (p : R)) ^ k := by
  induction k with
  | zero => show 1 / ((1 : Nat) : R) = 1; grind
  | succ k ih =>
    show 1 / ((p ^ k * p : Nat) : R) = (1 / (p : R)) ^ k * (1 / (p : R))
    rw [← ih]
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; rw [Nat.mul_zero, show ((0 : Nat) : R) = 0 by grind]
      rw [Field.div_eq_mul_inv, Field.inv_zero]
      grind
    · have h1 : ((p ^ k : Nat) : R) ≠ 0 := by have := natCast_pos' (Nat.pow_pos (n := k) h); grind
      have h2 : (p : R) ≠ 0 := by have := natCast_pos' h; grind
      rw [show ((p ^ k * p : Nat) : R) = ((p ^ k : Nat) : R) * (p : R) by grind]
      grind

/-- For a prime `p` and `j ≥ 0`: `Σ_{k ≥ j, pᵏ ≤ N} log p / pᵏ ≤ 2 log p / pʲ`. -/
theorem gsum_prime_pow_tail {p : Nat} (hp : Prime p) (j K : Nat) (P : Nat → Prop) [DecidablePred P] :
    gsum (fun k => if P k ∧ j ≤ k then lnat p / ((p ^ k : Nat) : R) else 0) K ≤
      2 * lnat p * (1 / (p : R)) ^ j := by
  have hp2 : 2 ≤ p := hp.1
  have hr0 : 0 ≤ 1 / (p : R) := one_div_nonneg' p
  have hr : 1 / (p : R) ≤ 1 / 2 := by
    have h1 := natCast_pos' (show 0 < p by omega)
    apply le_div_of_mul_le (show (0 : R) < 2 by grind)
    rw [show 1 / (p : R) * 2 = 2 / (p : R) by grind]
    apply div_le_of_le_mul h1
    have := natCast_le' hp2; rw [show ((2 : Nat) : R) = 2 by grind] at this; grind
  have h1 := gsum_le_gsum (n := K)
    (f := fun k => if P k ∧ j ≤ k then lnat p / ((p ^ k : Nat) : R) else 0)
    (g := fun k => lnat p * (if j ≤ k then (1 / (p : R)) ^ k else 0)) (fun k _ => by
      by_cases h : P k ∧ j ≤ k
      · rw [ite_eq_left h, ite_eq_left h.2, ← one_div_pow_cast]; grind
      · rw [ite_eq_right h]
        have := lnat_nonneg p
        split
        · exact OrderedRing.mul_nonneg this (pow_nonneg' hr0 k)
        · grind)
  rw [gsum_mul_left] at h1
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left (gsum_geom_tail_le hr0 hr j K) (lnat_nonneg p)
  grind

/-- **`Σ_{n ≤ K} log n / n² ≤ 2`** (telescoping against `(2 + log n)/n`). -/
theorem gsum_log_div_sq_le (K : Nat) :
    gsum (fun n => lnat n / ((n : R) * (n : R))) K ≤ 2 := by
  have key : ∀ m, 1 ≤ m → gsum (fun n => lnat n / ((n : R) * (n : R))) (m + 1) +
      (2 + lnat m) / (m : R) ≤ 2 := by
    intro m hm
    induction m, hm using Nat.le_induction' with
    | base =>
      rw [gsum_succ, gsum_succ, gsum_nil, lnat_one]; unfold lnat
      rw [ite_eq_left rfl]
      show 0 + 0 / (((0 : Nat) : R) * ((0 : Nat) : R)) + 0 / (((1 : Nat) : R) * ((1 : Nat) : R)) +
        (2 + 0) / ((1 : Nat) : R) ≤ 2
      rw [show ((0 : Nat) : R) = 0 by grind, show ((1 : Nat) : R) = 1 by grind]
      rw [Field.div_eq_mul_inv 0, Field.div_eq_mul_inv 0]; grind
    | succ m hm ih =>
      rw [gsum_succ]
      have hm0 := natCast_pos' (show 0 < m by omega)
      have hcast : ((m + 1 : Nat) : R) = (m : R) + 1 := by grind
      have hd := lnat_succ_sub_le hm
      have ha := lnat_nonneg m
      -- `m (b − a) ≤ 1`
      have hmd : (m : R) * (lnat (m + 1) - lnat m) ≤ 1 := by
        have h7 := OrderedRing.mul_le_mul_of_nonneg_left hd (Std.le_of_lt hm0)
        have : (m : R) ≠ 0 := by grind
        rw [show (m : R) * (1 / (m : R)) = 1 by grind] at h7; grind
      have hm2 := OrderedRing.mul_le_mul_of_nonneg_left hmd (show (0 : R) ≤ (m : R) + 2 by grind)
      -- the step `b/(m+1)² + (2+b)/(m+1) ≤ (2+a)/m`, after clearing denominators
      have step : lnat (m + 1) / (((m + 1 : Nat) : R) * ((m + 1 : Nat) : R)) +
          (2 + lnat (m + 1)) / ((m + 1 : Nat) : R) ≤ (2 + lnat m) / (m : R) := by
        rw [hcast]
        have hm1 : (0 : R) < (m : R) + 1 := by grind
        have hne : (m : R) ≠ 0 := by grind
        have hne1 : (m : R) + 1 ≠ 0 := by grind
        have hD : (0 : R) < (m : R) * (((m : R) + 1) * ((m : R) + 1)) :=
          OrderedRing.mul_pos hm0 (OrderedRing.mul_pos hm1 hm1)
        have lhs : lnat (m + 1) / (((m : R) + 1) * ((m : R) + 1)) + (2 + lnat (m + 1)) / ((m : R) + 1)
            = ((m : R) * lnat (m + 1) + (m : R) * ((m : R) + 1) * (2 + lnat (m + 1))) /
              ((m : R) * (((m : R) + 1) * ((m : R) + 1))) := by grind
        have rhs : (2 + lnat m) / (m : R) = (((m : R) + 1) * ((m : R) + 1) * (2 + lnat m)) /
              ((m : R) * (((m : R) + 1) * ((m : R) + 1))) := by grind
        rw [lhs, rhs]
        apply div_le_div_of_le _ hD
        grind
      grind
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h; show (0 : R) ≤ 2; grind
  · obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [gsum_succ, gsum_nil]; unfold lnat; rw [ite_eq_left rfl]
      show (0 : R) + 0 / (((0 : Nat) : R) * ((0 : Nat) : R)) ≤ 2
      rw [Field.div_eq_mul_inv 0]; grind
    · have := key m hm
      have : 0 ≤ (2 + lnat m) / (m : R) := by
        have := div_le_div_of_le (show (0 : R) ≤ 2 + lnat m by have := lnat_nonneg m; grind)
          (natCast_pos' hm)
        rw [show (0 : R) / (m : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this; exact this
      grind
where
  /-- Induction from `1`. -/
  Nat.le_induction' {P : (n : Nat) → 1 ≤ n → Prop} (base : P 1 (Nat.le_refl 1))
      (succ : ∀ n (hn : 1 ≤ n), P n hn → P (n + 1) (Nat.le_succ_of_le hn)) :
      ∀ n (hn : 1 ≤ n), P n hn := by
    intro n hn
    induction n with
    | zero => exact absurd hn (by omega)
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; exact base
      · exact succ n h (ih h)

/-- **Higher prime powers contribute boundedly.**
`Σ_{p ≤ N} Σ_{k ≤ N} [p prime, k ≥ 2, pᵏ ≤ N] log p / pᵏ ≤ 4`. -/
theorem prime_power_sum_le (N : Nat) :
    gsum (fun p => gsum (fun k => if Prime p ∧ 2 ≤ k ∧ p ^ k ≤ N then lnat p / ((p ^ k : Nat) : R)
      else 0) (N + 1)) (N + 1) ≤ 4 := by
  have h1 := gsum_le_gsum (n := N + 1)
    (f := fun p => gsum (fun k => if Prime p ∧ 2 ≤ k ∧ p ^ k ≤ N then lnat p / ((p ^ k : Nat) : R)
      else 0) (N + 1))
    (g := fun p => 2 * (lnat p / ((p : R) * (p : R)))) (fun p _ => by
      by_cases hp : Prime p
      · have := gsum_prime_pow_tail hp 2 (N + 1) (fun k => p ^ k ≤ N)
        have e : gsum (fun k => if Prime p ∧ 2 ≤ k ∧ p ^ k ≤ N then lnat p / ((p ^ k : Nat) : R)
            else 0) (N + 1) = gsum (fun k => if p ^ k ≤ N ∧ 2 ≤ k then lnat p / ((p ^ k : Nat) : R)
            else 0) (N + 1) := gsum_congr fun k _ => by
          by_cases h : p ^ k ≤ N ∧ 2 ≤ k
          · rw [ite_eq_left ⟨hp, h.2, h.1⟩, ite_eq_left h]
          · rw [ite_eq_right (fun h' => h ⟨h'.2.2, h'.2.1⟩), ite_eq_right h]
        rw [e]
        have e2 : 2 * lnat p * (1 / (p : R)) ^ 2 = 2 * (lnat p / ((p : R) * (p : R))) := by
          have : (p : R) ≠ 0 := by have := natCast_pos' (show 0 < p by have := hp.1; omega); grind
          show 2 * lnat p * (1 * (1 / (p : R)) * (1 / (p : R))) = _; grind
        rw [← e2]; exact this
      · rw [gsum_congr (g := fun _ => 0) (fun k _ => ite_eq_right (fun h => hp h.1)), gsum_zero']
        have : 0 ≤ lnat p / ((p : R) * (p : R)) := by
          rcases Nat.eq_zero_or_pos p with h | h
          · subst h; unfold lnat; rw [ite_eq_left rfl, Field.div_eq_mul_inv]; grind
          · have := div_le_div_of_le (lnat_nonneg p) (OrderedRing.mul_pos (natCast_pos' h) (natCast_pos' h))
            rw [show (0 : R) / ((p : R) * (p : R)) = 0 by rw [Field.div_eq_mul_inv]; grind] at this
            exact this
        grind)
  rw [gsum_mul_left] at h1
  have := gsum_log_div_sq_le (N + 1)
  grind

/-- Counting `1 ≤ p ≤ q` among `p < B`: at most `q`. -/
theorem gsum_count_le_q (q B : Nat) :
    gsum (fun p => if 1 ≤ p ∧ p ≤ q then (1 : R) else 0) B ≤ (q : R) := by
  by_cases h : q < B
  · rw [gsum_count_le q B h]; grind
  · rw [gsum_count_le_aux q B (by omega)]
    split
    · exact natCast_le' (Nat.zero_le q) |> fun h => by
        show (0 : R) ≤ (q : R); have := natCast_le' (Nat.zero_le q); grind
    · have := natCast_le' (show B ≤ q + 1 by omega)
      rw [show ((q + 1 : Nat) : R) = (q : R) + 1 by grind] at this; grind

/-- **Primes dividing `q` contribute boundedly.**
`Σ_{p ≤ N} Σ_{k ≤ N} [p prime, p ∣ q, k ≥ 1, pᵏ ≤ N] log p / pᵏ ≤ 2q` for `q ≥ 1`. -/
theorem prime_dvd_sum_le {q : Nat} (hq : 0 < q) (N : Nat) :
    gsum (fun p => gsum (fun k => if (Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N) ∧ p ∣ q then
      lnat p / ((p ^ k : Nat) : R) else 0) (N + 1)) (N + 1) ≤ 2 * (q : R) := by
  have h1 := gsum_le_gsum (n := N + 1)
    (f := fun p => gsum (fun k => if (Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N) ∧ p ∣ q then
      lnat p / ((p ^ k : Nat) : R) else 0) (N + 1))
    (g := fun p => 2 * (if 1 ≤ p ∧ p ≤ q then (1 : R) else 0)) (fun p _ => by
      by_cases hp : Prime p ∧ p ∣ q
      · have hp2 : 2 ≤ p := hp.1.1
        have := gsum_prime_pow_tail hp.1 1 (N + 1) (fun k => p ^ k ≤ N)
        have e : gsum (fun k => if (Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N) ∧ p ∣ q then
            lnat p / ((p ^ k : Nat) : R) else 0) (N + 1) = gsum (fun k => if p ^ k ≤ N ∧ 1 ≤ k then
            lnat p / ((p ^ k : Nat) : R) else 0) (N + 1) := gsum_congr fun k _ => by
          by_cases h : p ^ k ≤ N ∧ 1 ≤ k
          · rw [ite_eq_left ⟨⟨hp.1, h.2, h.1⟩, hp.2⟩, ite_eq_left h]
          · rw [ite_eq_right (fun h' => h ⟨h'.1.2.2, h'.1.2.1⟩), ite_eq_right h]
        rw [e, ite_eq_left ⟨by omega, Nat.le_of_dvd hq hp.2⟩]
        have h3 : lnat p * (1 / (p : R)) ^ 1 ≤ 1 := by
          have := lnat_div_le_one p
          show lnat p * (1 * (1 / (p : R))) ≤ 1
          have hne : (p : R) ≠ 0 := by have := natCast_pos' (show 0 < p by omega); grind
          grind
        grind
      · rw [gsum_congr (g := fun _ => 0) (fun k _ => ite_eq_right (fun h => hp ⟨h.1.1, h.2⟩)),
          gsum_zero']
        split <;> grind)
  rw [gsum_mul_left] at h1
  have := gsum_count_le_q q (N + 1)
  grind

end Foundations.NumberTheory
