import Foundations.NumberTheory.Chebyshev
import Foundations.Numbers.ComplexExp

/-!
# Arithmetic functions: divisor sums and the von Mangoldt function

Analytic number theory studies the primes through *arithmetic functions* — functions on the
positive integers — and their *divisor sums* `Σ_{d ∣ n} f(d)`. This file sets up the small amount
of such machinery that Dirichlet's theorem needs.

* **Finite-sum bookkeeping.** Interchanging double sums; summing over the multiples of `d` up
  to `N` (they are `d, 2d, …, ⌊N/d⌋ d`); and the identity behind every later estimate,

    `Σ_{n ≤ N} Σ_{d ∣ n} F(d, n/d) = Σ_{d ≤ N} Σ_{m ≤ N/d} F(d, m)`,

  which simply counts the pairs `(d, m)` with `d m ≤ N` in two ways (Dirichlet's *hyperbola*
  bookkeeping).
* **Multiplicativity of divisor sums.** If `p` is prime and `p ∤ m`, the divisors of `pᵃ m` are
  the `pⁱ e` with `i ≤ a`, `e ∣ m`; hence `Σ_{d ∣ pᵃm} f(d) = Σ_{i ≤ a} Σ_{e ∣ m} f(pⁱ e)`.
* **The von Mangoldt function** `Λ(n) = log p` if `n = pᵏ` (`k ≥ 1`), `0` otherwise, and the
  identity `Σ_{d ∣ n} Λ(d) = log n`, which is unique factorisation written additively. We define
  `Λ` as a double sum over pairs `(p, k)`; then sums `Σ_{n ≤ N} Λ(n) g(n)` regroup at once into
  sums over prime powers.

All sums are the finite sums `gsum f N = f 0 + ⋯ + f (N−1)` of Part II, over any field.
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-! ## Finite sums in a field -/

section Generic

variable {α : Type} [Field α]

/-- The empty sum is zero. -/
theorem gsum_nil (f : Nat → α) : gsum f 0 = 0 := rfl

/-- The sum of zeros is zero. -/
theorem gsum_zero' (n : Nat) : gsum (fun _ => (0 : α)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum_succ, ih]; grind

/-- Termwise equal summands, as functions. -/
theorem gsum_congr' {f g : Nat → α} (n : Nat) (h : ∀ k, k < n → f k = g k) :
    gsum f n = gsum g n := gsum_congr h

/-- **Interchanging a double finite sum.** -/
theorem gsum_comm (F : Nat → Nat → α) (A B : Nat) :
    gsum (fun i => gsum (fun j => F i j) B) A = gsum (fun j => gsum (fun i => F i j) A) B := by
  induction A with
  | zero => exact (gsum_zero' B).symm
  | succ A ih => rw [gsum_succ, ih, ← gsum_add]; rfl

/-- A sum in which only the term `n = m` survives. -/
theorem gsum_ite_eq (m N : Nat) (f : Nat → α) :
    gsum (fun n => if n = m then f n else 0) N = if m < N then f m else 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [gsum_succ, ih]
    by_cases h1 : m < N
    · rw [ite_eq_left h1, ite_eq_left (by omega : m < N + 1), ite_eq_right (by omega : ¬ N = m)]
      grind
    · rw [ite_eq_right h1]
      by_cases h2 : N = m
      · subst h2; rw [ite_eq_left rfl, ite_eq_left (by omega : N < N + 1)]; grind
      · rw [ite_eq_right h2, ite_eq_right (by omega : ¬ m < N + 1)]; grind

/-- Extending the range of a sum by terms that vanish. -/
theorem gsum_extend {f : Nat → α} {A B : Nat} (hAB : A ≤ B) (h : ∀ k, A ≤ k → k < B → f k = 0) :
    gsum f B = gsum f A := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hAB
  rw [gsum_split, gsum_congr (g := fun _ => 0) (fun k hk => h (A + k) (by omega) (by omega)),
    gsum_zero']
  grind

/-- **Summing over multiples.** For `d ≥ 1`, the multiples of `d` in `[0, N]` are `d m` with
`m ≤ N / d`: `Σ_{n ≤ N, d ∣ n} F(n) = Σ_{m ≤ N/d} F(d m)`. -/
theorem gsum_multiples {d : Nat} (hd : 0 < d) (F : Nat → α) (N : Nat) :
    gsum (fun n => if d ∣ n then F n else 0) (N + 1) = gsum (fun m => F (d * m)) (N / d + 1) := by
  induction N with
  | zero =>
    rw [Nat.zero_div, gsum_succ, gsum_succ, gsum_nil, gsum_nil, ite_eq_left (Nat.dvd_zero d),
      Nat.mul_zero]
  | succ N ih =>
    rw [gsum_succ, ih, succ_div_eq hd]
    by_cases h : d ∣ N + 1
    · rw [ite_eq_left h, ite_eq_left h, gsum_succ (fun m => F (d * m)) (N / d + 1)]
      have e : d * (N / d + 1) = N + 1 := by
        have := succ_div_eq hd (n := N)
        rw [ite_eq_left h] at this
        rw [← this, Nat.mul_div_cancel' h]
      rw [e]
    · rw [ite_eq_right h, ite_eq_right h, Nat.add_zero]; grind

/-- **Counting pairs `(d, m)` with `d m ≤ N` in two ways.** If `F(0, m) = F(d, 0) = 0`, then
`Σ_{n ≤ N} Σ_{d ∣ n} F(d, n/d) = Σ_{d ≤ N} Σ_{m ≤ N/d} F(d, m)`. -/
theorem gsum_divisors_eq (F : Nat → Nat → α) (h0 : ∀ m, F 0 m = 0) (h0' : ∀ d, F d 0 = 0)
    (N : Nat) :
    gsum (fun n => gsum (fun d => if d ∣ n then F d (n / d) else 0) (n + 1)) (N + 1) =
      gsum (fun d => gsum (fun m => F d m) (N / d + 1)) (N + 1) := by
  -- extend each inner sum to `d ≤ N`
  have e1 : ∀ n, n < N + 1 → gsum (fun d => if d ∣ n then F d (n / d) else 0) (n + 1) =
      gsum (fun d => if d ∣ n then F d (n / d) else 0) (N + 1) := by
    intro n hn
    symm; apply gsum_extend (by omega)
    intro k hk1 hk2
    by_cases hkn : k ∣ n
    · have : n = 0 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · exact h
        · exact absurd (Nat.le_of_dvd h hkn) (by omega)
      subst this; rw [ite_eq_left hkn, Nat.zero_div, h0']
    · rw [ite_eq_right hkn]
  rw [gsum_congr e1, gsum_comm]
  apply gsum_congr
  intro d _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    rw [gsum_congr (g := fun _ => 0) (fun n _ => by split <;> simp [h0]),
      gsum_congr (g := fun _ => 0) (fun m _ => h0 m), gsum_zero', gsum_zero']
  · rw [gsum_multiples hd (fun n => F d (n / d)) N]
    apply gsum_congr; intro m _; rw [Nat.mul_div_cancel_left m hd]

end Generic

/-! ## Divisor sums -/

section Divisors

variable {α : Type} [Field α]

/-- The **divisor sum** `Σ_{d ∣ n} f(d)` (for `n ≥ 1`; the range `d ≤ n` contains all divisors). -/
def dsum (f : Nat → α) (n : Nat) : α := gsum (fun d => if d ∣ n then f d else 0) (n + 1)

/-- `Σ_{d ∣ 1} f(d) = f(1)`. -/
theorem dsum_one (f : Nat → α) : dsum f 1 = f 1 := by
  unfold dsum
  rw [gsum_succ, gsum_succ, gsum_nil, ite_eq_right (by decide : ¬ (0 ∣ 1)),
    ite_eq_left (Nat.dvd_refl 1)]
  grind

/-- Divisor sums only depend on the values at divisors. -/
theorem dsum_congr {f g : Nat → α} {n : Nat} (h : ∀ d, d ∣ n → f d = g d) : dsum f n = dsum g n := by
  unfold dsum; apply gsum_congr; intro d _
  by_cases hd : d ∣ n
  · rw [ite_eq_left hd, ite_eq_left hd, h d hd]
  · rw [ite_eq_right hd, ite_eq_right hd]

/-- **The new divisors of `p^{a+1} m`.** For a prime `p ∤ m`: `d ∣ p^{a+1} m` but `d ∤ pᵃ m`
exactly when `d = p^{a+1} e` with `e ∣ m`. -/
theorem dvd_pow_succ_mul_iff {p m a d : Nat} (hp : Prime p) (hpm : ¬ p ∣ m) :
    (d ∣ p ^ (a + 1) * m ∧ ¬ d ∣ p ^ a * m) ↔ (p ^ (a + 1) ∣ d ∧ d / p ^ (a + 1) ∣ m) := by
  have hp1 : 1 < p := hp.1
  have hppos : 0 < p ^ (a + 1) := Nat.pow_pos (by omega)
  constructor
  · rintro ⟨h1, h2⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hpm (Nat.dvd_zero p))
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by
      rintro rfl; have := Nat.eq_zero_of_zero_dvd h1
      exact absurd this (Nat.pos_iff_ne_zero.1 (Nat.mul_pos hppos hm0)))
    obtain ⟨r, hr, hpr⟩ := vp_spec hp1 hd0
    have hcop : Nat.Coprime r p := by
      rcases hp.2 _ (Nat.gcd_dvd_right r p) with h | h
      · exact h
      · exact absurd (h ▸ Nat.gcd_dvd_left r p) hpr
    have hrm : r ∣ m := by
      have : r ∣ p ^ (a + 1) * m := Nat.dvd_trans ⟨p ^ vp p d, hr.trans (Nat.mul_comm _ _)⟩ h1
      exact (hcop.pow_right (a + 1)).dvd_of_dvd_mul_left this
    have hv : a + 1 ≤ vp p d := by
      apply Classical.byContradiction; intro hv
      apply h2; rw [hr]
      exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (by omega)) hrm
    have hdvd : p ^ (a + 1) ∣ d := (pow_dvd_iff_le_vp hp1 hd0).2 hv
    refine ⟨hdvd, ?_⟩
    obtain ⟨e, he⟩ := hdvd
    rw [he, Nat.mul_div_cancel_left e hppos]
    rw [he] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hppos h1
  · rintro ⟨⟨e, rfl⟩, h2⟩
    rw [Nat.mul_div_cancel_left e hppos] at h2
    refine ⟨Nat.mul_dvd_mul_left _ h2, fun h => hpm ?_⟩
    rw [Nat.pow_succ, Nat.mul_assoc] at h
    have := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (show 0 < p by omega)) h
    exact Nat.dvd_trans ⟨e, rfl⟩ this

/-- **Divisor sums over `pᵃ m`** (`p` prime, `p ∤ m`, `m ≥ 1`):
`Σ_{d ∣ pᵃ m} f(d) = Σ_{i ≤ a} Σ_{e ∣ m} f(pⁱ e)`. -/
theorem dsum_prime_pow_mul (f : Nat → α) {p m : Nat} (hp : Prime p) (hpm : ¬ p ∣ m) (hm : 0 < m) :
    ∀ a : Nat, dsum f (p ^ a * m) = gsum (fun i => dsum (fun e => f (p ^ i * e)) m) (a + 1)
  | 0 => by
    show dsum f (p ^ 0 * m) = 0 + dsum (fun e => f (p ^ 0 * e)) m
    simp only [Nat.pow_zero, Nat.one_mul]; grind
  | a + 1 => by
    rw [gsum_succ, ← dsum_prime_pow_mul f hp hpm hm a]
    have hp1 : 1 < p := hp.1
    have hppos : 0 < p ^ (a + 1) := Nat.pow_pos (by omega)
    have hn : 0 < p ^ a * m := Nat.mul_pos (Nat.pow_pos (by omega)) hm
    have hle : p ^ a * m ≤ p ^ (a + 1) * m :=
      Nat.mul_le_mul_right m (Nat.pow_le_pow_right (by omega) (by omega))
    unfold dsum
    -- split each term into old and new divisors
    have split : ∀ d, (if d ∣ p ^ (a + 1) * m then f d else 0) =
        (if d ∣ p ^ a * m then f d else 0) +
          (if p ^ (a + 1) ∣ d then (if d / p ^ (a + 1) ∣ m then f d else 0) else 0) := by
      intro d
      have key := dvd_pow_succ_mul_iff (d := d) (a := a) hp hpm
      by_cases h1 : d ∣ p ^ a * m
      · have h1' : d ∣ p ^ (a + 1) * m := Nat.dvd_trans h1 (Nat.mul_dvd_mul_right
          (Nat.pow_dvd_pow p (by omega)) m)
        have : ¬ (p ^ (a + 1) ∣ d ∧ d / p ^ (a + 1) ∣ m) := fun h => (key.2 h).2 h1
        rw [ite_eq_left h1', ite_eq_left h1]
        by_cases h3 : p ^ (a + 1) ∣ d
        · rw [ite_eq_left h3, ite_eq_right (fun h4 => this ⟨h3, h4⟩)]; grind
        · rw [ite_eq_right h3]; grind
      · rw [ite_eq_right h1]
        by_cases h2 : d ∣ p ^ (a + 1) * m
        · obtain ⟨h3, h4⟩ := key.1 ⟨h2, h1⟩
          rw [ite_eq_left h2, ite_eq_left h3, ite_eq_left h4]; grind
        · have : ¬ (p ^ (a + 1) ∣ d ∧ d / p ^ (a + 1) ∣ m) := fun h => h2 (key.2 h).1
          rw [ite_eq_right h2]
          by_cases h3 : p ^ (a + 1) ∣ d
          · rw [ite_eq_left h3, ite_eq_right (fun h4 => this ⟨h3, h4⟩)]; grind
          · rw [ite_eq_right h3]; grind
    rw [gsum_congr (fun d _ => split d), gsum_add]
    congr 1
    · apply gsum_extend (by omega)
      intro k hk _
      rw [ite_eq_right]; intro h; exact absurd (Nat.le_of_dvd hn h) (by omega)
    · obtain ⟨N, hN⟩ : ∃ N, p ^ (a + 1) * m + 1 = N + 1 := ⟨_, rfl⟩
      rw [hN, gsum_multiples hppos _ N]
      have hNm : N / p ^ (a + 1) = m := by
        rw [show N = p ^ (a + 1) * m by omega, Nat.mul_div_cancel_left m hppos]
      rw [hNm]; apply gsum_congr; intro e _
      rw [Nat.mul_div_cancel_left e hppos]

end Divisors

/-! ## Logarithms of natural numbers -/

/-- `log n` for a natural number `n ≥ 1`, with the convention `log 0 = 0`. -/
noncomputable def lnat (n : Nat) : R := if n = 0 then 0 else R.log n

/-- `log 1 = 0`. -/
theorem lnat_one : lnat 1 = 0 := by unfold lnat; rw [ite_eq_right (by omega)]; exact R.log_one

/-- `log n ≥ 0`. -/
theorem lnat_nonneg (n : Nat) : 0 ≤ lnat n := by
  unfold lnat
  split
  · grind
  · have h1 : (1 : R) ≤ (n : R) := by
      have := natCast_le' (show 1 ≤ n by omega); grind
    have := log_le_log (by grind) h1
    rw [R.log_one] at this; exact this

/-- `log (m n) = log m + log n` for `m, n ≥ 1`. -/
theorem lnat_mul {m n : Nat} (hm : 0 < m) (hn : 0 < n) : lnat (m * n) = lnat m + lnat n := by
  unfold lnat
  rw [ite_eq_right (Nat.pos_iff_ne_zero.1 (Nat.mul_pos hm hn)), ite_eq_right (by omega),
    ite_eq_right (by omega)]
  rw [show ((m * n : Nat) : R) = (m : R) * (n : R) by grind]
  exact R.log_mul (natCast_pos' hm) (natCast_pos' hn)

/-- `log (pᵏ) = k log p` for `p ≥ 1`. -/
theorem lnat_pow {p : Nat} (hp : 0 < p) (k : Nat) : lnat (p ^ k) = (k : R) * lnat p := by
  induction k with
  | zero => rw [Nat.pow_zero, lnat_one]; grind
  | succ k ih => rw [Nat.pow_succ, lnat_mul (Nat.pow_pos hp) hp, ih]; grind

/-! ## The von Mangoldt function -/

/-- The **von Mangoldt function** `Λ(n) = log p` if `n = pᵏ` with `p` prime and `k ≥ 1`, and
`0` otherwise — written as a sum over the pairs `(p, k)` with `p, k ≤ n`.

The `PNT*` files define the same function independently as `PNT.vonMangoldt` (with their own
`dsum` and `psi`); no bridging lemma between the two copies is stated. -/
noncomputable def vonMangoldt (n : Nat) : R :=
  gsum (fun p => gsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k = n then lnat p else 0) (n + 1)) (n + 1)

/-- `Λ(n) ≥ 0`. -/
theorem vonMangoldt_nonneg (n : Nat) : 0 ≤ vonMangoldt n := by
  unfold vonMangoldt
  apply fsum_nonneg' ; intro p
  apply fsum_nonneg'; intro k
  split
  · exact lnat_nonneg p
  · grind
where
  /-- Non-negative summands give a non-negative sum. -/
  fsum_nonneg' {f : Nat → R} {n : Nat} (h : ∀ k, 0 ≤ f k) : 0 ≤ gsum f n := by
    induction n with
    | zero => show (0 : R) ≤ 0; grind
    | succ n ih => rw [gsum_succ]; have := h n; grind

/-- If `pᵏ = n` with `p` prime and `k ≥ 1`, then `p ≤ n` and `k ≤ n`. -/
theorem le_of_prime_pow_eq {p k n : Nat} (hp : Prime p) (hk : 1 ≤ k) (h : p ^ k = n) :
    p ≤ n ∧ k ≤ n := by
  have hp2 : 2 ≤ p := hp.1
  constructor
  · rw [← h]; calc p = p ^ 1 := (Nat.pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  · rw [← h]
    have := Nat.lt_pow_self (n := k) (show 1 < p by omega)
    omega

/-- **Regrouping a `Λ`-weighted sum by prime powers.**
`Σ_{n ≤ N} Λ(n) g(n) = Σ_{p ≤ N} Σ_{k ≤ N} [p prime, k ≥ 1, pᵏ ≤ N] · log p · g(pᵏ)`. -/
theorem gsum_vonMangoldt_mul (g : Nat → R) (N : Nat) :
    gsum (fun n => vonMangoldt n * g n) (N + 1) =
      gsum (fun p => gsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then lnat p * g (p ^ k) else 0)
        (N + 1)) (N + 1) := by
  unfold vonMangoldt
  -- extend the inner ranges to `N`
  have e1 : ∀ n, n < N + 1 →
      gsum (fun p => gsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k = n then lnat p else 0) (n + 1))
        (n + 1) * g n =
      gsum (fun p => gsum (fun k => if n = p ^ k then
        (if Prime p ∧ 1 ≤ k then lnat p * g n else 0) else 0) (N + 1)) (N + 1) := by
    intro n hn
    rw [← gsum_mul_right]
    have inner : ∀ p, gsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k = n then lnat p else 0) (n + 1) * g n
        = gsum (fun k => if n = p ^ k then (if Prime p ∧ 1 ≤ k then lnat p * g n else 0) else 0)
          (N + 1) := by
      intro p
      rw [← gsum_mul_right]
      symm
      rw [gsum_extend (A := n + 1) (by omega)]
      · apply gsum_congr; intro k _
        by_cases h : Prime p ∧ 1 ≤ k ∧ p ^ k = n
        · rw [ite_eq_left h, ite_eq_left h.2.2.symm, ite_eq_left ⟨h.1, h.2.1⟩]
        · rw [ite_eq_right h]
          by_cases h2 : n = p ^ k
          · rw [ite_eq_left h2, ite_eq_right (fun h3 => h ⟨h3.1, h3.2, h2.symm⟩)]; grind
          · rw [ite_eq_right h2]; grind
      · intro k hk _
        by_cases h2 : n = p ^ k
        · rw [ite_eq_left h2]
          by_cases h3 : Prime p ∧ 1 ≤ k
          · exact absurd (le_of_prime_pow_eq h3.1 h3.2 h2.symm).2 (by omega)
          · rw [ite_eq_right h3]
        · rw [ite_eq_right h2]
    rw [gsum_congr (fun p _ => inner p)]
    symm
    rw [gsum_extend (A := n + 1) (by omega)]
    intro p hp _
    apply gsum_congr' (g := fun _ => 0) _ (fun k _ => ?_) |>.trans (gsum_zero' _)
    by_cases h2 : n = p ^ k
    · rw [ite_eq_left h2]
      by_cases h3 : Prime p ∧ 1 ≤ k
      · exact absurd (le_of_prime_pow_eq h3.1 h3.2 h2.symm).1 (by omega)
      · rw [ite_eq_right h3]
    · rw [ite_eq_right h2]
  rw [gsum_congr e1, gsum_comm]
  apply gsum_congr; intro p _
  rw [gsum_comm]
  apply gsum_congr; intro k _
  rw [gsum_ite_eq (p ^ k) (N + 1) (fun n => if Prime p ∧ 1 ≤ k then lnat p * g n else 0)]
  by_cases h : Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N
  · rw [ite_eq_left h, ite_eq_left (by omega), ite_eq_left ⟨h.1, h.2.1⟩]
  · rw [ite_eq_right h]
    by_cases h2 : p ^ k < N + 1
    · rw [ite_eq_left h2, ite_eq_right (fun h3 => h ⟨h3.1, h3.2, by omega⟩)]
    · rw [ite_eq_right h2]

end Foundations.NumberTheory
