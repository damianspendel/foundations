import Foundations.NumberTheory.Binomial

/-!
# The primorial bound: the product of the primes up to n is at most 4ⁿ

The **primorial** `n#` is the product of all primes `p ≤ n`: `1, 1, 2, 6, 6, 30, 30, 210, …`.
Its logarithm `θ(n) = Σ_{p ≤ n} log p` is *Chebyshev's function*, and the prime number theorem
is equivalent to `θ(n) ∼ n`. Here we prove the elementary upper bound

  `n# ≤ 4ⁿ`, i.e. `θ(n) ≤ n · log 4`,

which Erdős used in his 1932 proof of Bertrand's postulate. (Chebyshev had obtained bounds of
this kind in 1852 with more delicate estimates; the slick argument below is Erdős's.)

The proof is by induction. Even `n > 2` are not prime, so `n# = (n−1)#`. For odd `n = 2m + 1`,
every prime `p` with `m + 1 < p ≤ 2m + 1` divides `(2m+1)!` but neither `m!` nor `(m+1)!`, hence
divides `C(2m+1, m+1)`. Being distinct primes, their product divides it too, and
`C(2m+1, m+1) ≤ 4ᵐ` (it is half of `C(2m+2, m+1)`, which is at most `4^(m+1)/2`). So
`(2m+1)# ≤ (m+1)# · 4ᵐ ≤ 4^(m+1) · 4ᵐ = 4^(2m+1)`.

Along the way we set up finite products `∏_{i<B} f(i)` and a decision procedure for primality,
which the next file uses for Bertrand's postulate.
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Deciding primality -/

/-- Primality is decidable: it suffices to test the divisors `d ≤ p`. (A naive but honest
procedure; the kernel can run it on numbers in the thousands.) -/
instance decPrime : DecidablePred Prime := fun p =>
  decidable_of_iff (2 ≤ p ∧ ∀ d, d < p + 1 → d ∣ p → d = 1 ∨ d = p) (by
    constructor
    · rintro ⟨h2, h⟩
      exact ⟨h2, fun d hd => h d (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd)) hd⟩
    · rintro ⟨h2, h⟩
      exact ⟨h2, fun d _ hd => h d hd⟩)

/-- A prime dividing `k!` is at most `k`. -/
theorem prime_le_of_dvd_fact {p : Nat} (hp : Prime p) : ∀ {k : Nat}, p ∣ fact k → p ≤ k
  | 0, h => by
    simp only [fact] at h
    have := Nat.le_of_dvd (by omega) h; have := hp.1; omega
  | k + 1, h => by
    simp only [fact] at h
    rcases euclid_lemma hp h with h | h
    · exact Nat.le_of_dvd (by omega) h
    · have := prime_le_of_dvd_fact hp h; omega

/-! ## Finite products -/

/-- The finite product `∏_{i < B} f(i)`. -/
def bprod (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | B + 1 => bprod f B * f B

/-- A product of positive factors is positive. -/
theorem bprod_pos {f : Nat → Nat} (hf : ∀ i, 0 < f i) : ∀ B, 0 < bprod f B
  | 0 => Nat.one_pos
  | B + 1 => Nat.mul_pos (bprod_pos hf B) (hf B)

/-- The product of a pointwise product is the product of the products. -/
theorem bprod_mul (f g : Nat → Nat) : ∀ B, bprod (fun i => f i * g i) B = bprod f B * bprod g B
  | 0 => rfl
  | B + 1 => by simp only [bprod, bprod_mul f g B]; grind

/-- Products only depend on the factors below the bound. -/
theorem bprod_congr {f g : Nat → Nat} : ∀ {B}, (∀ i, i < B → f i = g i) → bprod f B = bprod g B
  | 0, _ => rfl
  | B + 1, h => by
    simp only [bprod]
    rw [bprod_congr (fun i hi => h i (by omega)), h B (by omega)]

/-- Products are monotone in the factors. -/
theorem bprod_le_bprod {f g : Nat → Nat} : ∀ {B}, (∀ i, i < B → f i ≤ g i) →
    bprod f B ≤ bprod g B
  | 0, _ => Nat.le_refl 1
  | B + 1, h => Nat.mul_le_mul (bprod_le_bprod (fun i hi => h i (by omega))) (h B (by omega))

/-- Factors equal to `1` beyond `A` do not change the product. -/
theorem bprod_eq_of_one {f : Nat → Nat} {A : Nat} (h : ∀ i, A ≤ i → f i = 1) :
    ∀ {B}, A ≤ B → bprod f B = bprod f A := by
  intro B hB
  induction B with
  | zero => obtain rfl : A = 0 := by omega
            rfl
  | succ B ih =>
    by_cases hAB : A = B + 1
    · rw [hAB]
    · simp only [bprod]; rw [h B (by omega), Nat.mul_one, ih (by omega)]

/-- Pulling one factor `f(p)` out of the product and replacing it by `1`. -/
theorem bprod_update (f : Nat → Nat) {p : Nat} : ∀ {B}, p < B →
    bprod f B = f p * bprod (fun i => if i = p then 1 else f i) B
  | 0, h => absurd h (Nat.not_lt_zero _)
  | B + 1, h => by
    simp only [bprod]
    by_cases hp : p = B
    · subst hp
      have hc : bprod (fun i => if i = p then 1 else f i) p = bprod f p :=
        bprod_congr (fun i hi => by simp [Nat.ne_of_lt hi])
      rw [hc]
      simp [Nat.mul_comm]
    · rw [bprod_update f (p := p) (show p < B by omega)]
      simp only [show ¬ B = p from fun h => hp h.symm, ↓reduceIte]
      exact Nat.mul_assoc _ _ _

/-- If the factors are at most `c` and equal `1` beyond `a`, the product is at most `c^(a+1)`. -/
theorem bprod_le_pow {g : Nat → Nat} {a c : Nat} (hc : 1 ≤ c) (h1 : ∀ i, a < i → g i = 1)
    (hle : ∀ i, g i ≤ c) (B : Nat) : bprod g B ≤ c ^ (a + 1) := by
  have key : ∀ B, bprod g B ≤ c ^ (min B (a + 1)) := by
    intro B
    induction B with
    | zero => simp [bprod]
    | succ B ih =>
      simp only [bprod]
      by_cases hB : B ≤ a
      · rw [show min (B + 1) (a + 1) = min B (a + 1) + 1 by omega, Nat.pow_succ]
        exact Nat.mul_le_mul ih (hle B)
      · rw [h1 B (by omega), Nat.mul_one, show min (B + 1) (a + 1) = min B (a + 1) by omega]
        exact ih
  exact Nat.le_trans (key B) (Nat.pow_le_pow_right hc (by omega))

/-- A prime dividing a product divides one of the factors. -/
theorem prime_dvd_bprod {q : Nat} (hq : Prime q) {f : Nat → Nat} :
    ∀ {B}, q ∣ bprod f B → ∃ i, i < B ∧ q ∣ f i
  | 0, h => by
    simp only [bprod] at h
    have := Nat.le_of_dvd (by omega) h; have := hq.1; omega
  | B + 1, h => by
    simp only [bprod] at h
    rcases euclid_lemma hq h with h | h
    · obtain ⟨i, hi, hd⟩ := prime_dvd_bprod hq h
      exact ⟨i, by omega, hd⟩
    · exact ⟨B, by omega, h⟩

/-- A product of distinct primes (those `p < B` satisfying `P`), each dividing `N`, divides `N`. -/
theorem bprod_primes_dvd (P : Nat → Prop) [DecidablePred P] {N : Nat} :
    ∀ {B}, (∀ p, p < B → Prime p → P p → p ∣ N) →
      bprod (fun i => if Prime i ∧ P i then i else 1) B ∣ N
  | 0, _ => Nat.one_dvd N
  | B + 1, h => by
    simp only [bprod]
    have ih := bprod_primes_dvd P (B := B) (fun p hp => h p (by omega))
    by_cases hB : Prime B ∧ P B
    · simp only [hB, and_self, ↓reduceIte]
      obtain ⟨t, ht⟩ := ih
      -- `B` does not divide the product of the smaller primes.
      have hnd : ¬ B ∣ bprod (fun i => if Prime i ∧ P i then i else 1) B := by
        intro hd
        obtain ⟨i, hi, hdi⟩ := prime_dvd_bprod hB.1 hd
        by_cases hi' : Prime i ∧ P i
        · simp only [hi', and_self, ↓reduceIte] at hdi
          have := Nat.le_of_dvd (by have := hi'.1.1; omega) hdi
          omega
        · simp only [hi', ↓reduceIte] at hdi
          have := Nat.le_of_dvd (by omega) hdi; have := hB.1.1; omega
      have hBN := h B (by omega) hB.1 hB.2
      rw [ht] at hBN
      rcases euclid_lemma hB.1 hBN with h' | h'
      · exact absurd h' hnd
      · obtain ⟨s, rfl⟩ := h'
        exact ⟨s, by rw [ht]; grind⟩
    · simp only [hB, ↓reduceIte, Nat.mul_one]
      exact ih

/-! ## The primorial -/

/-- The **primorial** `n# = ∏_{p ≤ n, p prime} p`. -/
def primorial (n : Nat) : Nat := bprod (fun i => if Prime i then i else 1) (n + 1)

/-- The primorial is positive. -/
theorem primorial_pos (n : Nat) : 0 < primorial n :=
  bprod_pos (fun i => by
    by_cases h : Prime i
    · simp only [h, ↓reduceIte]; have := h.1; omega
    · simp only [h, ↓reduceIte]; omega) _

/-- Splitting the primorial: `(2m+1)# = (m+1)# · ∏_{m+1 < p ≤ 2m+1} p`. -/
theorem primorial_split (m : Nat) :
    primorial (2 * m + 1) = primorial (m + 1) *
      bprod (fun i => if Prime i ∧ m + 1 < i then i else 1) (2 * m + 2) := by
  unfold primorial
  let f1 : Nat → Nat := fun i => if Prime i ∧ i ≤ m + 1 then i else 1
  have hsplit : bprod (fun i => if Prime i then i else 1) (2 * m + 1 + 1) =
      bprod (fun i => f1 i * (if Prime i ∧ m + 1 < i then i else 1)) (2 * m + 2) := by
    apply bprod_congr
    intro i _
    by_cases hp : Prime i <;> by_cases hi : i ≤ m + 1 <;> by_cases hi2 : m + 1 < i <;>
      simp [f1, hp, hi, hi2] <;> omega
  rw [hsplit, bprod_mul]
  congr 1
  rw [bprod_eq_of_one (A := m + 2) (fun i hi => by simp only [f1]; split <;> omega) (by omega)]
  apply bprod_congr
  intro i hi
  by_cases hp : Prime i <;> simp [f1, hp] <;> omega

/-- The primes in `(m+1, 2m+1]` all divide `C(2m+1, m+1)`, hence so does their product. -/
theorem bprod_dvd_choose (m : Nat) :
    bprod (fun i => if Prime i ∧ m + 1 < i then i else 1) (2 * m + 2) ∣ choose (2 * m + 1) (m + 1) := by
  apply bprod_primes_dvd
  intro p hp2 hp hpm
  have hid := choose_mul_fact (2 * m + 1) (m + 1) m (by omega)
  have h1 : p ∣ fact (2 * m + 1) := dvd_fact (by have := hp.1; omega) (by omega)
  rw [← hid] at h1
  rcases euclid_lemma hp h1 with h | h
  · rcases euclid_lemma hp h with h | h
    · exact h
    · have := prime_le_of_dvd_fact hp h; omega
  · have := prime_le_of_dvd_fact hp h; omega

/-- `C(2m+1, m+1) ≤ 4ᵐ`: it is half of `C(2m+2, m+1) ≤ 4^(m+1) / 2`. -/
theorem choose_odd_le (m : Nat) : choose (2 * m + 1) (m + 1) ≤ 4 ^ m := by
  have h1 := two_mul_centralBinom_le (m + 1) (by omega)
  have h2 : centralBinom (m + 1) = choose (2 * m + 1) m + choose (2 * m + 1) (m + 1) := by
    unfold centralBinom
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, choose_succ_succ]
  have h3 : choose (2 * m + 1) m = choose (2 * m + 1) (m + 1) := by
    have := choose_symm m (m + 1)
    rwa [show m + (m + 1) = 2 * m + 1 by omega] at this
  rw [h2, h3, Nat.pow_succ] at h1
  omega

/-- **Erdős's primorial bound.** The product of all primes `p ≤ n` is at most `4ⁿ`. -/
theorem primorial_le_four_pow : ∀ n, primorial n ≤ 4 ^ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases (by omega : n ≤ 2 ∨ (n % 2 = 0 ∧ 3 ≤ n) ∨ (n % 2 = 1 ∧ 3 ≤ n)) with h | ⟨he, h3⟩ | ⟨ho, h3⟩
    · rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> decide
    · -- Even `n ≥ 4` is not prime, so `n# = (n-1)#`.
      have hnp : ¬ Prime n := by
        intro hp
        rcases hp.2 2 (by omega) with h | h <;> omega
      have : primorial n = primorial (n - 1) := by
        unfold primorial
        rw [show n + 1 = (n - 1 + 1) + 1 by omega]
        simp only [bprod]
        rw [show n - 1 + 1 = n by omega]
        simp [hnp]
      rw [this]
      exact Nat.le_trans (ih (n - 1) (by omega)) (Nat.pow_le_pow_right (by omega) (by omega))
    · -- Odd `n = 2m + 1`: split off the primes in `(m+1, 2m+1]`.
      obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
      rw [primorial_split]
      have hb : bprod (fun i => if Prime i ∧ m + 1 < i then i else 1) (2 * m + 2) ≤ 4 ^ m := by
        have hpos : 0 < choose (2 * m + 1) (m + 1) := by
          have := choose_pos (m + 1) m
          rwa [show m + 1 + m = 2 * m + 1 by omega] at this
        exact Nat.le_trans (Nat.le_of_dvd hpos (bprod_dvd_choose m)) (choose_odd_le m)
      calc primorial (m + 1) * bprod (fun i => if Prime i ∧ m + 1 < i then i else 1) (2 * m + 2)
          ≤ 4 ^ (m + 1) * 4 ^ m := Nat.mul_le_mul (ih (m + 1) (by omega)) hb
        _ = 4 ^ (2 * m + 1) := by rw [← Nat.pow_add]; congr 1; omega

end Foundations.NumberTheory
