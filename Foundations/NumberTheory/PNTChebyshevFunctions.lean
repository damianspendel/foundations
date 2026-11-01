import Foundations.NumberTheory.PNTSums

/-!
# Toward the prime number theorem II: Chebyshev's functions θ and ψ

Counting primes one by one, as `π(x)` does, turns out to be awkward. Chebyshev's insight (1850s)
was to *weight* each prime by its logarithm:

* `θ(x) = Σ_{p ≤ x} log p` — the logarithm of the primorial `x#`;
* `ψ(x) = Σ_{pᵏ ≤ x, k ≥ 1} log p` — the same, but every prime power `pᵏ` also counts, with
  weight `log p`.

The second is the more natural: `ψ(x) = Σ_{n ≤ x} Λ(n)`, where **von Mangoldt's function**
`Λ(n)` is `log p` if `n` is a power of the prime `p` and `0` otherwise. The point of the
weighting is that `Σ_{d ∣ n} Λ(d) = log n` — unique factorisation, written additively — so that
`log n! = Σ_{d ≤ n} Λ(d) ⌊n/d⌋`, the identity driving the next files. The prime number theorem
becomes the statement `ψ(x) ∼ x`: the primes, weighted by their logarithms, have density one.

In this file (for natural numbers `N`):

* `Λ`, `θ`, `ψ`, and the identity `ψ(N) = Σ_{n ≤ N} Λ(n)`;
* `θ(N) ≤ ψ(N) ≤ π(N) · log N ≤ N · log 1024`, and `θ(N) ≤ N · log 4` from Erdős's primorial
  bound — so θ and ψ are `O(N)`;
* `ψ(N) − θ(N) ≤ √N · log N`: higher prime powers are rare, since only primes `p ≤ √N` have a
  square below `N`.

Sums over prime powers are written as double sums over pairs `(p, k)`; for a prime `p` the
number of exponents `k ≥ 1` with `pᵏ ≤ N` is `ppCount p N`, the integer part of
`log N / log p`.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-! ## Counting sums -/

/-- A sum of a constant `c` over the indices satisfying `Q` is `(count) · c`. -/
theorem fsum_ite_const (Q : Nat → Prop) [DecidablePred Q] (c : R) :
    ∀ B, fsum (fun k => if Q k then c else 0) B = (countBelow Q B : R) * c
  | 0 => by show (0 : R) = ((0 : Nat) : R) * c; grind
  | B + 1 => by
    rw [fsum_succ, fsum_ite_const Q c B]
    simp only [countBelow]
    by_cases h : Q B <;> simp only [h, ↓reduceIte] <;> grind

/-- `countBelow Q B ≤ B`. -/
theorem countBelow_le_self (Q : Nat → Prop) [DecidablePred Q] : ∀ B, countBelow Q B ≤ B
  | 0 => Nat.le_refl 0
  | B + 1 => by
    have := countBelow_le_self Q B
    simp only [countBelow]; split <;> omega

/-! ## Prime power counts -/

/-- The number of exponents `1 ≤ k ≤ N` with `pᵏ ≤ N` (for a prime `p`, this is
`⌊log N / log p⌋`). -/
def ppCount (p N : Nat) : Nat := countBelow (fun k => 1 ≤ k ∧ p ^ k ≤ N) (N + 1)

/-- The counting invariant: below `B`, at most `B − 1` exponents qualify, and `p` to that power is
still at most `N`. -/
theorem ppCount_aux {p N : Nat} (hp : 1 ≤ p) (hN : 1 ≤ N) : ∀ B,
    (countBelow (fun k => 1 ≤ k ∧ p ^ k ≤ N) B < B ∨ B = 0) ∧
      p ^ countBelow (fun k => 1 ≤ k ∧ p ^ k ≤ N) B ≤ N
  | 0 => ⟨Or.inr rfl, by simp [countBelow]; omega⟩
  | B + 1 => by
    obtain ⟨h1, h2⟩ := ppCount_aux hp hN B
    simp only [countBelow]
    by_cases h : 1 ≤ B ∧ p ^ B ≤ N
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      have hc : countBelow (fun k => 1 ≤ k ∧ p ^ k ≤ N) B + 1 ≤ B := by omega
      exact ⟨Or.inl (by omega), Nat.le_trans (Nat.pow_le_pow_right hp hc) h.2⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      have := countBelow_le_self (fun k => 1 ≤ k ∧ p ^ k ≤ N) B
      exact ⟨Or.inl (by omega), h2⟩

/-- `p^(ppCount p N) ≤ N` for `N ≥ 1`. -/
theorem pow_ppCount_le {p N : Nat} (hp : 1 ≤ p) (hN : 1 ≤ N) : p ^ ppCount p N ≤ N :=
  (ppCount_aux hp hN (N + 1)).2

/-- If `p ≤ N` then at least the exponent `1` qualifies. -/
theorem one_le_ppCount {p N : Nat} (hp : 1 ≤ p) (hpN : p ≤ N) : 1 ≤ ppCount p N := by
  unfold ppCount
  have : ∀ B, 2 ≤ B → 1 ≤ countBelow (fun k => 1 ≤ k ∧ p ^ k ≤ N) B := by
    intro B hB
    induction B with
    | zero => omega
    | succ B ih =>
      simp only [countBelow]
      by_cases hB2 : B = 1
      · subst hB2; simp [countBelow, hpN]
      · have := ih (by omega); split <;> omega
  exact this (N + 1) (by omega)

/-- `ppCount p N · log p ≤ log N` for `p ≥ 1`, `N ≥ 1`. -/
theorem ppCount_mul_log_le {p N : Nat} (hp : 1 ≤ p) (hN : 1 ≤ N) :
    (ppCount p N : R) * R.log (p : R) ≤ R.log (N : R) := by
  have := log_ineq_of_pow_le (k := ppCount p N) (l := 1) hp hN
    (by rw [Nat.pow_one]; exact pow_ppCount_le hp hN)
  grind

/-- If `N < p²` (and `p ≥ 2`), only the exponent `1` can qualify. -/
theorem ppCount_le_one {p N : Nat} (hp : 2 ≤ p) (hN : 1 ≤ N) (hpN : N < p * p) :
    ppCount p N ≤ 1 := by
  apply Classical.byContradiction; intro h
  have h1 := pow_ppCount_le (by omega : 1 ≤ p) hN
  have h2 : p ^ 2 ≤ p ^ ppCount p N := Nat.pow_le_pow_right (by omega) (by omega)
  have : p ^ 2 = p * p := by rw [Nat.pow_two]
  omega

/-! ## The definitions -/

/-- The sum over prime powers `Σ_{pᵏ ≤ N, k ≥ 1} f(p, k)`, written as a double sum over
`p ≤ N`, `k ≤ N` (larger `p` or `k` cannot occur). -/
noncomputable def ppSum (f : Nat → Nat → R) (N : Nat) : R :=
  fsum (fun p => fsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then f p k else 0) (N + 1)) (N + 1)

/-- **Chebyshev's θ-function.** `θ(N) = Σ_{p ≤ N} log p`. -/
noncomputable def theta (N : Nat) : R := fsum (fun p => if Prime p then R.log (p : R) else 0) (N + 1)

/-- **Chebyshev's ψ-function.** `ψ(N) = Σ_{pᵏ ≤ N, k ≥ 1} log p`. -/
noncomputable def psi (N : Nat) : R := ppSum (fun p _ => R.log (p : R)) N

/-- **Von Mangoldt's function.** `Λ(n) = log p` if `n = pᵏ` with `p` prime and `k ≥ 1`, and
`Λ(n) = 0` otherwise. (Written as a sum over the — at most one — representation `n = pᵏ`.) -/
noncomputable def vonMangoldt (n : Nat) : R :=
  fsum (fun p => fsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k = n then R.log (p : R) else 0) (n + 1))
    (n + 1)

/-! ## Von Mangoldt's function -/

/-- `k < pᵏ` for `p ≥ 2`. -/
theorem lt_pow_self' {p : Nat} (hp : 2 ≤ p) (k : Nat) : k < p ^ k := lt_pow_self (by omega) k

/-- A prime dividing a power of a prime is that prime. -/
theorem prime_eq_of_dvd_pow {p q : Nat} (hp : Prime p) (hq : Prime q) :
    ∀ k, q ∣ p ^ k → q = p
  | 0, h => by
    rw [Nat.pow_zero] at h
    have := Nat.le_of_dvd (by omega) h; have := hq.1; omega
  | k + 1, h => by
    rw [Nat.pow_succ] at h
    rcases euclid_lemma hq h with h | h
    · exact prime_eq_of_dvd_pow hp hq k h
    · rcases hp.2 q h with h1 | h1
      · have := hq.1; omega
      · exact h1

/-- **Prime powers determine their base and exponent.** -/
theorem prime_pow_inj {p q j k : Nat} (hp : Prime p) (hq : Prime q) (hj : 1 ≤ j)
    (h : q ^ j = p ^ k) : q = p ∧ j = k := by
  have hqp : q = p := prime_eq_of_dvd_pow hp hq k
    (by rw [← h]; exact Nat.dvd_trans (by simp) (Nat.pow_dvd_pow q hj))
  subst hqp
  refine ⟨rfl, ?_⟩
  have e1 := vp_eq (p := q) (m := q ^ j) (e := j) (r := 1) hq.1 (by simp)
    (fun h => by have := Nat.le_of_dvd (by omega) h; have := hq.1; omega)
  have e2 := vp_eq (p := q) (m := q ^ k) (e := k) (r := 1) hq.1 (by simp)
    (fun h => by have := Nat.le_of_dvd (by omega) h; have := hq.1; omega)
  rw [h] at e1; omega

/-- The value of `Λ` at a prime power: **`Λ(pᵏ) = log p`** for `k ≥ 1`. -/
theorem vonMangoldt_prime_pow {p k : Nat} (hp : Prime p) (hk : 1 ≤ k) :
    vonMangoldt (p ^ k) = R.log (p : R) := by
  have hp2 := hp.1
  unfold vonMangoldt
  -- Only the pair `(p, k)` contributes.
  have inner : ∀ q, fsum (fun j => if Prime q ∧ 1 ≤ j ∧ q ^ j = p ^ k then R.log (q : R) else 0)
      (p ^ k + 1) = if q = p then R.log (p : R) else 0 := by
    intro q
    by_cases hq : q = p
    · subst hq
      rw [fsum_congr (b := fun j => if j = k then R.log (q : R) else 0) (fun j _ => by
        by_cases hj : j = k
        · subst hj; simp [hp, hk]
        · have : ¬ (Prime q ∧ 1 ≤ j ∧ q ^ j = q ^ k) := fun h =>
            hj (prime_pow_inj hp h.1 h.2.1 h.2.2).2
          simp only [this, hj, ↓reduceIte])]
      rw [fsum_ite_eq]
      have := lt_pow_self' hp2 k
      simp only [show k < q ^ k + 1 by omega, ↓reduceIte]
    · simp only [hq, ↓reduceIte]
      rw [fsum_congr (b := fun _ => 0) (fun j _ => by
        have : ¬ (Prime q ∧ 1 ≤ j ∧ q ^ j = p ^ k) := fun h =>
          hq (prime_pow_inj hp h.1 h.2.1 h.2.2).1
        simp only [this, ↓reduceIte])]
      exact fsum_zeros _
  rw [fsum_congr (fun q _ => inner q), fsum_ite_eq]
  have : p ≤ p ^ k := by
    have := Nat.pow_le_pow_right (show 0 < p by omega) hk; rwa [Nat.pow_one] at this
  simp only [show p < p ^ k + 1 by omega, ↓reduceIte]

/-- `Λ(p) = log p` for a prime `p`. -/
theorem vonMangoldt_prime {p : Nat} (hp : Prime p) : vonMangoldt p = R.log (p : R) := by
  have := vonMangoldt_prime_pow hp (Nat.le_refl 1); rwa [Nat.pow_one] at this

/-- `Λ ≥ 0`. -/
theorem vonMangoldt_nonneg (n : Nat) : 0 ≤ vonMangoldt n := by
  unfold vonMangoldt
  apply fsum_nonneg; intro p; apply fsum_nonneg; intro k
  split
  · next h => exact log_natCast_nonneg (by have := h.1.1; omega)
  · grind

/-- **`ψ` is the summatory function of `Λ`.** `ψ(N) = Σ_{n ≤ N} Λ(n)`. -/
theorem psi_eq_sum_vonMangoldt (N : Nat) :
    psi N = fsum vonMangoldt (N + 1) := by
  let g : Nat → Nat → Nat → R := fun n p k =>
    if Prime p ∧ 1 ≤ k ∧ p ^ k = n then R.log (p : R) else 0
  -- Extend the inner bounds of `Λ(n)` from `n + 1` to `N + 1`.
  have ext : ∀ n, n < N + 1 → vonMangoldt n =
      fsum (fun p => fsum (fun k => g n p k) (N + 1)) (N + 1) := by
    intro n hn
    unfold vonMangoldt
    have hvan : ∀ p k, n + 1 ≤ p ∨ n + 1 ≤ k → g n p k = 0 := by
      intro p k hpk
      simp only [g]
      split
      · next h =>
        exfalso
        have hp2 := h.1.1
        have h1 : p ≤ p ^ k := by
          have := Nat.pow_le_pow_right (show 0 < p by omega) h.2.1; rwa [Nat.pow_one] at this
        have := lt_pow_self' hp2 k
        omega
      · rfl
    rw [fsum_congr_bound (show n + 1 ≤ N + 1 by omega) (fun p h1 _ => by
      rw [fsum_congr (b := fun _ => 0) (fun k _ => hvan p k (Or.inl h1)), fsum_zeros])]
    apply fsum_congr; intro p _
    exact fsum_congr_bound (show n + 1 ≤ N + 1 by omega) (fun k h1 _ => hvan p k (Or.inr h1))
  rw [fsum_congr ext]
  -- Move the sum over `n` innermost and evaluate it.
  rw [fsum_swap]
  unfold psi ppSum
  apply fsum_congr; intro p _
  rw [fsum_swap]
  apply fsum_congr; intro k _
  rw [fsum_congr (b := fun n => if n = p ^ k then
      (if Prime p ∧ 1 ≤ k then R.log (p : R) else 0) else 0) (fun n _ => by
    simp only [g]
    by_cases h : n = p ^ k
    · subst h; by_cases h' : Prime p ∧ 1 ≤ k <;> simp [h']
    · have : ¬ (Prime p ∧ 1 ≤ k ∧ p ^ k = n) := fun h' => h h'.2.2.symm
      simp only [this, h, ↓reduceIte])]
  rw [fsum_ite_eq]
  by_cases h1 : Prime p ∧ 1 ≤ k <;> by_cases h2 : p ^ k ≤ N <;>
    simp [h1, h2, show (p ^ k < N + 1) ↔ p ^ k ≤ N by omega]

/-! ## ψ in terms of prime power counts -/

/-- `ψ(N) = Σ_{p ≤ N} ppCount(p, N) · log p`. -/
theorem psi_eq (N : Nat) :
    psi N = fsum (fun p => if Prime p then (ppCount p N : R) * R.log (p : R) else 0) (N + 1) := by
  unfold psi ppSum
  apply fsum_congr; intro p _
  by_cases hp : Prime p
  · simp only [hp, true_and, ↓reduceIte]
    exact fsum_ite_const _ _ _
  · simp only [hp, false_and, ↓reduceIte]; exact fsum_zeros _

/-- `θ ≥ 0`. -/
theorem theta_nonneg (N : Nat) : 0 ≤ theta N := by
  unfold theta; apply fsum_nonneg; intro p
  split
  · next h => exact log_natCast_nonneg (by have := h.1; omega)
  · grind

/-- `ψ ≥ 0`. -/
theorem psi_nonneg (N : Nat) : 0 ≤ psi N := by
  rw [psi_eq_sum_vonMangoldt]; exact fsum_nonneg vonMangoldt_nonneg _

/-- **`θ(N) ≤ ψ(N)`.** -/
theorem theta_le_psi (N : Nat) : theta N ≤ psi N := by
  rw [psi_eq]; unfold theta
  apply fsum_le_fsum'; intro p hp
  by_cases hpr : Prime p
  · simp only [hpr, ↓reduceIte]
    have h1 := one_le_ppCount (p := p) (N := N) (by have := hpr.1; omega) (by omega)
    have h2 := log_natCast_nonneg (n := p) (by have := hpr.1; omega)
    have h3 : ((1 : Nat) : R) ≤ (ppCount p N : R) := natCast_le' h1
    have := OrderedRing.mul_le_mul_of_nonneg_right h3 h2
    grind
  · simp only [hpr, ↓reduceIte]; grind

/-- The number of primes up to `N`, as a sum. -/
theorem fsum_prime_const (c : R) (N : Nat) :
    fsum (fun p => if Prime p then c else 0) (N + 1) = (primeCount N : R) * c :=
  fsum_ite_const Prime c (N + 1)

/-- **`ψ(N) ≤ π(N) · log N`**: each prime `p ≤ N` contributes `ppCount(p, N) · log p ≤ log N`. -/
theorem psi_le_primeCount_mul_log {N : Nat} (hN : 1 ≤ N) :
    psi N ≤ (primeCount N : R) * R.log (N : R) := by
  rw [psi_eq, ← fsum_prime_const]
  apply fsum_le_fsum'; intro p _
  by_cases hpr : Prime p
  · simp only [hpr, ↓reduceIte]
    exact ppCount_mul_log_le (by have := hpr.1; omega) hN
  · simp only [hpr, ↓reduceIte]; grind

/-- Chebyshev's upper bound in logarithmic form: `π(N) · log N ≤ N · log 1024` for `N ≥ 1`. -/
theorem primeCount_mul_log_le {N : Nat} (hN : 1 ≤ N) :
    (primeCount N : R) * R.log (N : R) ≤ (N : R) * R.log 1024 :=
  log_ineq_of_pow_le (a := N) (b := 1024) hN (by omega) (chebyshev_upper hN)

/-- **ψ is `O(N)`.** `ψ(N) ≤ N · log 1024`. -/
theorem psi_le (N : Nat) : psi N ≤ (N : R) * R.log 1024 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : psi 0 = 0 := by
      rw [psi_eq]; simp only [fsum_succ, fsum_zero]
      have : ¬ Prime 0 := fun h => by have := h.1; omega
      simp only [this, ↓reduceIte]; grind
    rw [this]; show (0 : R) ≤ ((0 : Nat) : R) * _; grind
  · exact Std.le_trans (psi_le_primeCount_mul_log hN) (primeCount_mul_log_le hN)

/-- **θ is `O(N)`** (from Erdős's primorial bound): `θ(N) ≤ N · log 4`. -/
theorem theta_le (N : Nat) : theta N ≤ (N : R) * R.log 4 := by
  have hpos : ∀ i, 0 < (fun i => if Prime i then i else 1) i := by
    intro i; simp only; split
    · next h => have := h.1; omega
    · omega
  have h1 : theta N = R.log (primorial N : R) := by
    unfold primorial; rw [log_bprod hpos]; unfold theta
    apply fsum_congr; intro i _
    by_cases h : Prime i <;> simp only [h, ↓reduceIte]
    rw [show ((1 : Nat) : R) = 1 by grind, R.log_one]
  rw [h1]
  have := log_ineq_of_pow_le (a := primorial N) (b := 4) (k := 1) (l := N) (primorial_pos N)
    (by omega)
    (by rw [Nat.pow_one]; exact primorial_le_four_pow N)
  grind

/-- **Higher prime powers are negligible.** If `s² ≤ N < (s + 1)²` (so `s = ⌊√N⌋`), then
`ψ(N) − θ(N) ≤ s · log N`. -/
theorem psi_sub_theta_le {N s : Nat} (hN : 1 ≤ N) (hs1 : s * s ≤ N)
    (hs : N < (s + 1) * (s + 1)) : psi N - theta N ≤ (s : R) * R.log (N : R) := by
  have hsN : s ≤ N := by
    rcases Nat.eq_zero_or_pos s with h | h
    · omega
    · have := Nat.le_mul_of_pos_right s h; omega
  have hlogN := log_natCast_nonneg hN
  -- Termwise: `(ppCount − 1) log p ≤ [p ≤ s] log N`.
  have key : psi N - theta N ≤
      fsum (fun p => if Prime p ∧ p ≤ s then R.log (N : R) else 0) (N + 1) := by
    rw [psi_eq]; unfold theta; rw [← fsum_sub]
    apply fsum_le_fsum'; intro p hp
    by_cases hpr : Prime p
    · have hp2 := hpr.1
      have hlp := log_natCast_nonneg (n := p) (by omega)
      have hc := ppCount_mul_log_le (p := p) (by omega) hN
      simp only [hpr, true_and, ↓reduceIte]
      by_cases hps : p ≤ s
      · simp only [hps, ↓reduceIte]; grind
      · simp only [hps, ↓reduceIte]
        have hpp : N < p * p := Nat.lt_of_lt_of_le hs (Nat.mul_le_mul (by omega) (by omega))
        have h1 := ppCount_le_one hp2 hN hpp
        have h2 := one_le_ppCount (p := p) (N := N) (by omega) (by omega)
        have : ppCount p N = 1 := by omega
        rw [this]; grind
    · simp only [hpr, false_and, ↓reduceIte]; grind
  -- The right side is `π(s) · log N ≤ s · log N`.
  have e : fsum (fun p => if Prime p ∧ p ≤ s then R.log (N : R) else 0) (N + 1) =
      (primeCount s : R) * R.log (N : R) := by
    rw [← fsum_congr_bound (show s + 1 ≤ N + 1 by omega) (fun p h1 _ => by
      have : ¬ (Prime p ∧ p ≤ s) := fun h => by omega
      simp only [this, ↓reduceIte])]
    rw [← fsum_prime_const]
    apply fsum_congr; intro p hp
    simp only [show p ≤ s by omega, and_true]
  rw [e] at key
  have := OrderedRing.mul_le_mul_of_nonneg_right
    (show (primeCount s : R) ≤ (s : R) from natCast_le' (primeCount_le s)) hlogN
  grind

end Foundations.NumberTheory.PNT
