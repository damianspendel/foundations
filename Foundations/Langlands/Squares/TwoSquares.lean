import Foundations.Langlands.Squares.Identities
import Foundations.Langlands.Padic.LegendreBasic
import Foundations.NumberTheory.PrimesMod4
import Foundations.Algebra.TwoSquares

/-!
# Which numbers are sums of two squares?

Fermat's Christmas-day letter of 1640 contained more than the theorem on primes `p ≡ 1 (mod 4)`
(`Foundations.Algebra.fermat_two_squares`, Zagier's proof). Fermat also knew the complete
answer, made rigorous by Euler (1749–1758): a positive integer `n` is a sum of two squares if and
only if every prime `p ≡ 3 (mod 4)` divides `n` to an **even** power. Thus `45 = 3² · 5 = 6² + 3²`,
but `21 = 3 · 7` and `12 = 2² · 3` are not sums of two squares.

* **Sufficiency** is multiplicative: `2 = 1² + 1²`, primes `≡ 1 (mod 4)` are sums of two squares
  by Fermat, `p² = p² + 0²`, and the Brahmagupta identity multiplies representations.
* **Necessity** is a divisibility argument: if `p ≡ 3 (mod 4)` divides `a² + b²` then `p` divides
  both `a` and `b`, since otherwise `(b a⁻¹)² ≡ −1 (mod p)`, contradicting Fermat's criterion
  `neg_one_qr_iff` (the first supplement to quadratic reciprocity). Dividing by `p²` lowers the
  exponent of `p` by two, and an odd exponent eventually reaches `1`, which is impossible.

We phrase "`p` occurs to the exact power `k`" without a valuation function: `pᵏ ∣ n` and
`pᵏ⁺¹ ∤ n`. For `n = 0` the condition is vacuous, consistently with `0 = 0² + 0²`.
-/

namespace Foundations.Langlands.Squares

open Foundations.Numbers.Arith

/-- **Even exponents at primes `≡ 3 (mod 4)`.** Every prime `p ≡ 3 (mod 4)` divides `n` to an
even exact power: whenever `pᵏ ∣ n` but `pᵏ⁺¹ ∤ n`, the exponent `k` is even. -/
def ThreeModFourEven (n : Nat) : Prop :=
  ∀ p k : Nat, Prime p → p % 4 = 3 → p ^ k ∣ n → ¬ p ^ (k + 1) ∣ n → k % 2 = 0

/-! ## Necessity -/

/-- **A prime `p ≡ 3 (mod 4)` dividing `a² + b²` divides `a` and `b`.** Otherwise `−1` would be a
square modulo `p`. -/
theorem dvd_both_of_dvd_sum_sq {p a b : Nat} (hp : Prime p) (h3 : p % 4 = 3)
    (h : p ∣ a * a + b * b) : p ∣ a ∧ p ∣ b := by
  have hodd : p % 2 = 1 := by omega
  -- It suffices: `p ∣ x` for one of them forces `p ∣` the other.
  have key : ∀ {a b : Nat}, p ∣ a * a + b * b → p ∣ a := by
    intro a b h
    apply Classical.byContradiction
    intro ha
    have ha' : ¬ (p : Int) ∣ (a : Int) := fun h' => ha (Int.natCast_dvd_natCast.1 h')
    obtain ⟨u, hu⟩ := Foundations.Langlands.Padic.Legendre.exists_inv_mod
      (Foundations.Langlands.Padic.Legendre.coprime_prime hp ha').symm
    -- `(b u)² + 1 = u² (a² + b²) − (a u − 1)(a u + 1)` is divisible by `p`.
    have hI : (p : Int) ∣ (b * u) * (b * u) + 1 := by
      have h1 : (p : Int) ∣ u * u * ((a : Int) * a + (b : Int) * b) := by
        have : (p : Int) ∣ ((a * a + b * b : Nat) : Int) := Int.natCast_dvd_natCast.2 h
        push_cast at this
        rw [Int.mul_comm]
        exact Int.dvd_mul_of_dvd_left this
      have h2 : (p : Int) ∣ ((a : Int) * u - 1) * ((a : Int) * u + 1) :=
        Int.dvd_mul_of_dvd_left hu
      have e : (b * u) * (b * u) + 1 = u * u * ((a : Int) * a + (b : Int) * b) -
          ((a : Int) * u - 1) * ((a : Int) * u + 1) := by grind
      rw [e]; exact Int.dvd_sub h1 h2
    have hN : p ∣ (b * u).natAbs * (b * u).natAbs + 1 := by
      apply Int.natCast_dvd_natCast.1
      have := @Int.natAbs_mul_self (b * u)
      push_cast at this ⊢
      rw [this]; exact hI
    have hqr := Foundations.NumberTheory.neg_one_isQR_of_dvd hp.1 hN
    have := (Foundations.Algebra.neg_one_qr_iff (p := p) hp hodd).1 hqr
    omega
  exact ⟨key h, key (by rw [Nat.add_comm]; exact h)⟩

/-- Cancelling `p²` from an exact power: `p^(k+2) ∣ p² m ↔ p^k ∣ m`. -/
theorem pow_add_two_dvd_iff {p k m : Nat} (hp : 0 < p) :
    p ^ (k + 2) ∣ p * p * m ↔ p ^ k ∣ m := by
  rw [show p ^ (k + 2) = p * p * p ^ k by rw [Nat.pow_add]; grind]
  exact Nat.mul_dvd_mul_iff_left (Nat.mul_pos hp hp)

/-- **Necessity.** In a sum of two squares, every prime `p ≡ 3 (mod 4)` occurs to an even power. -/
theorem threeModFourEven_of_sum_sq {n a b : Nat} (h : a * a + b * b = n) : ThreeModFourEven n := by
  intro p k hp h3 hk hk1
  have hp0 : 0 < p := by have := hp.1; omega
  induction k using Nat.strongRecOn generalizing n a b with
  | _ k ih =>
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with h0 | h1 | h2
  · subst h0; rfl
  · subst h1
    exfalso
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := dvd_both_of_dvd_sum_sq hp h3 (by rw [h]; simpa using hk)
    apply hk1
    exact ⟨a' * a' + b' * b', by rw [← h]; grind⟩
  · have hpn : p ∣ n := Nat.dvd_trans (by simpa using Nat.pow_dvd_pow p (show 1 ≤ k by omega)) hk
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := dvd_both_of_dvd_sum_sq hp h3 (by rw [h]; exact hpn)
    have hn : n = p * p * (a' * a' + b' * b') := by rw [← h]; grind
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [hn] at hk hk1
    rw [pow_add_two_dvd_iff hp0] at hk
    rw [show j + 2 + 1 = (j + 1) + 2 by omega, pow_add_two_dvd_iff hp0] at hk1
    have := ih j (by omega) rfl hk hk1
    omega

/-! ## Sufficiency -/

/-- A prime `q` not dividing `p` does not affect divisibility by `q`-powers:
`qᵏ ∣ p c ↔ qᵏ ∣ c`. -/
theorem prime_pow_dvd_mul_iff {q p c : Nat} (hq : Prime q) (hqp : ¬ q ∣ p) :
    ∀ k, q ^ k ∣ p * c ↔ q ^ k ∣ c := by
  intro k
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    constructor
    · intro h
      have hq1 : q ∣ p * c := Nat.dvd_trans (by simpa using Nat.pow_dvd_pow q (show 1 ≤ k + 1 by omega)) h
      rcases euclid_lemma hq hq1 with h' | ⟨c', rfl⟩
      · exact absurd h' hqp
      · have hq0 : 0 < q := by have := hq.1; omega
        rw [Nat.pow_succ, Nat.mul_comm (q ^ k) q] at h ⊢
        rw [show p * (q * c') = q * (p * c') by grind] at h
        exact Nat.mul_dvd_mul_left q ((ih (c := c')).1 ((Nat.mul_dvd_mul_iff_left hq0).1 h))
    · intro h
      exact Nat.dvd_trans h (Nat.dvd_mul_left c p)

/-- Distinct primes do not divide each other. -/
theorem not_dvd_of_primes {q p : Nat} (hq : Prime q) (hp : Prime p) (hne : q ≠ p) : ¬ q ∣ p := by
  intro h
  rcases hp.2 q h with h1 | h1
  · have := hq.1; omega
  · exact hne h1

/-- If `n` satisfies the even-exponent condition, so does `n / p` for a prime `p ∣ n` with
`p ≢ 3 (mod 4)`. -/
theorem ThreeModFourEven.of_mul {p c : Nat} (hp : Prime p) (h3 : p % 4 ≠ 3)
    (h : ThreeModFourEven (p * c)) : ThreeModFourEven c := by
  intro q k hq hq3 hk hk1
  have hqp : ¬ q ∣ p := not_dvd_of_primes hq hp (by omega)
  exact h q k hq hq3 ((prime_pow_dvd_mul_iff hq hqp k).2 hk)
    (fun h' => hk1 ((prime_pow_dvd_mul_iff hq hqp (k + 1)).1 h'))

/-- If `p² d` satisfies the even-exponent condition, so does `d`. -/
theorem ThreeModFourEven.of_mul_sq {p d : Nat} (hp : Prime p)
    (h : ThreeModFourEven (p * p * d)) : ThreeModFourEven d := by
  intro q k hq hq3 hk hk1
  have hp0 : 0 < p := by have := hp.1; omega
  by_cases hqp : q = p
  · subst hqp
    have := h q (k + 2) hq hq3 ((pow_add_two_dvd_iff hp0).2 hk)
      (by rw [show k + 2 + 1 = (k + 1) + 2 by omega, pow_add_two_dvd_iff hp0]; exact hk1)
    omega
  · have hqp' : ¬ q ∣ p := not_dvd_of_primes hq hp hqp
    have e : ∀ j, q ^ j ∣ p * p * d ↔ q ^ j ∣ d := fun j => by
      rw [Nat.mul_assoc, prime_pow_dvd_mul_iff hq hqp' j, prime_pow_dvd_mul_iff hq hqp' j]
    exact h q k hq hq3 ((e k).2 hk) (fun h' => hk1 ((e (k + 1)).1 h'))

/-- `2` and the primes `≡ 1 (mod 4)` are sums of two squares (the latter by Fermat). -/
theorem isSum2_prime_ne_three {p : Nat} (hp : Prime p) (h3 : p % 4 ≠ 3) : IsSum2 (p : Int) := by
  by_cases h2 : p = 2
  · subst h2; exact ⟨1, 1, rfl⟩
  · have hodd : p % 2 = 1 := by
      apply Classical.byContradiction; intro he
      rcases hp.2 2 ⟨p / 2, by omega⟩ with h' | h' <;> omega
    obtain ⟨a, b, hab⟩ := Foundations.Algebra.fermat_two_squares (p := p) hp (by omega)
    exact isSum2_of_nat hab

/-- **Sufficiency.** If every prime `≡ 3 (mod 4)` occurs in `n` to an even power, then `n` is a sum
of two (integer) squares. -/
theorem isSum2_of_threeModFourEven (n : Nat) (h : ThreeModFourEven n) : IsSum2 (n : Int) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with h0 | h1 | h2
  · subst h0; exact ⟨0, 0, rfl⟩
  · subst h1; exact ⟨1, 0, rfl⟩
  obtain ⟨p, hp, c, rfl⟩ := exists_prime_dvd h2
  have hp2 := hp.1
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h2
    · exact h0
  by_cases h3 : p % 4 = 3
  · -- `p` must occur at least twice.
    have hpc : p ∣ c := by
      apply Classical.byContradiction
      intro hpc
      have := h p 1 hp h3 (by rw [Nat.pow_one]; exact Nat.dvd_mul_right p c) (by
        rw [Nat.pow_succ, Nat.pow_one]
        exact fun h' => hpc ((Nat.mul_dvd_mul_iff_left (by omega)).1 h'))
      omega
    obtain ⟨d, rfl⟩ := hpc
    rw [← Nat.mul_assoc] at h ⊢
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0; simp at hc0
      · exact h0
    have hlt : d < p * p * d := by
      have : 4 ≤ p * p := Nat.mul_le_mul hp2 hp2
      have := Nat.mul_lt_mul_of_pos_right (show 1 < p * p by omega) hd0
      omega
    obtain ⟨a, b, hab⟩ := ih d (by rw [← Nat.mul_assoc]; exact hlt) (h.of_mul_sq hp)
    refine ⟨(p : Int) * a, (p : Int) * b, ?_⟩
    push_cast
    rw [← hab]; grind
  · have hlt : c < p * c := by
      have := Nat.mul_lt_mul_of_pos_right (show 1 < p by omega) hc0
      omega
    have := (isSum2_prime_ne_three hp h3).mul (ih c hlt (h.of_mul hp h3))
    push_cast
    exact this

/-! ## The theorem -/

/-- **The two-squares theorem** (Fermat 1640, Euler 1749–58). A natural number `n` is a sum of two
squares if and only if every prime `p ≡ 3 (mod 4)` divides `n` to an even exact power. -/
theorem two_squares_iff (n : Nat) :
    (∃ a b : Nat, a * a + b * b = n) ↔ ThreeModFourEven n := by
  constructor
  · rintro ⟨a, b, h⟩
    exact threeModFourEven_of_sum_sq h
  · intro h
    exact nat_of_isSum2 (isSum2_of_threeModFourEven n h)

/-- Example: `21 = 3 · 7` is not a sum of two squares, because `3` occurs to the first power. -/
example : ¬ ∃ a b : Nat, a * a + b * b = 21 := by
  intro h
  have h3 : Prime 3 := ⟨by decide, fun d hd => by
    have := Nat.le_of_dvd (by decide) hd
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with h | h | h | h <;> subst h <;>
      first | (exact absurd hd (by decide)) | simp⟩
  have := (two_squares_iff 21).1 h 3 1 h3 rfl (by decide) (by decide)
  omega

end Foundations.Langlands.Squares
