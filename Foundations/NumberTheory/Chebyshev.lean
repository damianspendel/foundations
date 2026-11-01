import Foundations.NumberTheory.Bertrand
import Foundations.Numbers.Log

/-!
# Chebyshev's bounds: π(x) is of order x / log x

How many primes are there up to `x`? Write `π(x)` for their number. Gauss, aged fifteen, guessed
from tables (1792) that the density of primes near `x` is about `1 / log x`, so that
`π(x) ≈ x / log x`; Legendre made a similar conjecture in 1798. This is the **prime number
theorem**, `π(x) log x / x → 1`, proved only in 1896 (Hadamard, de la Vallée Poussin) with complex
analysis.

The first real progress was **Chebyshev's** (1852): with elementary means he showed that
`π(x) log x / x` stays between two positive constants (he got `0.92` and `1.11`), and deduced
Bertrand's postulate. We prove such bounds, with cruder constants, from the two facts about
`C(2n, n)` that already gave Bertrand:

* **Lower bound.** Every prime power dividing `C(2n, n)` is at most `2n`, and only primes `≤ 2n`
  occur, so `C(2n, n) ≤ (2n)^π(2n)`. With `C(2n, n) ≥ 4ⁿ / (2n + 1)` this gives
  `2ⁿ ≤ (2n)^π(2n)`, and for every `m ≥ 6`: `2^⌊m/2⌋ ≤ m^π(m)`.
* **Upper bound.** The primes in `(k, n]` each exceed `k` and their product is at most the
  primorial `n# ≤ 4ⁿ`; so `k^(π(n) − k − 1) ≤ 4ⁿ`. Choosing `k = ⌊√n⌋` yields `n^π(n) ≤ 1024ⁿ`.

Taking logarithms (the natural logarithm `log` constructed in Part II):

  `⌊m/2⌋ · log 2 ≤ π(m) · log m ≤ m · log 1024`,

i.e. `(log 2 / 2 − o(1)) · m / log m ≤ π(m) ≤ (10 log 2) · m / log m`: the order of magnitude
`m / log m` is established, though not the asymptotic constant `1`.
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Counting -/

/-- The number of `i < B` satisfying `P`. -/
def countBelow (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0 => 0
  | B + 1 => countBelow P B + if P B then 1 else 0

/-- The **prime counting function** `π(n)`: the number of primes `p ≤ n`. -/
def primeCount (n : Nat) : Nat := countBelow Prime (n + 1)

/-- A product of the constant `c` over the `i < B` with `P i` is `c^(count)`. -/
theorem bprod_const (P : Nat → Prop) [DecidablePred P] (c : Nat) :
    ∀ B, bprod (fun i => if P i then c else 1) B = c ^ countBelow P B
  | 0 => rfl
  | B + 1 => by
    simp only [bprod, countBelow, bprod_const P c B]
    by_cases h : P B
    · simp only [h, ↓reduceIte, Nat.pow_succ]
    · simp [h]

/-- Counting `P` below `B` is at most counting `P ∧ (k < ·)` plus `k + 1`. -/
theorem countBelow_le (P : Nat → Prop) [DecidablePred P] (k : Nat) : ∀ B,
    countBelow P B ≤ countBelow (fun i => P i ∧ k < i) B + min B (k + 1)
  | 0 => by simp [countBelow]
  | B + 1 => by
    have ih := countBelow_le P k B
    simp only [countBelow]
    by_cases h : P B <;> by_cases hk : k < B <;> simp [h, hk] <;> omega

/-- `π(n + 1) = π(n) + [n + 1 is prime]`. -/
theorem primeCount_succ (n : Nat) :
    primeCount (n + 1) = primeCount n + if Prime (n + 1) then 1 else 0 := rfl

/-- `π(n) ≤ n`. -/
theorem primeCount_le (n : Nat) : primeCount n ≤ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [primeCount_succ]
    split <;> omega

/-- `π` is monotone. -/
theorem primeCount_mono {m n : Nat} (h : m ≤ n) : primeCount m ≤ primeCount n := by
  induction n with
  | zero => obtain rfl : m = 0 := by omega
            exact Nat.le_refl _
  | succ n ih =>
    by_cases hm : m = n + 1
    · rw [hm]; exact Nat.le_refl _
    · have := ih (by omega)
      rw [primeCount_succ]
      omega

/-! ## Chebyshev's lower bound -/

/-- `C(2n, n) ≤ (2n)^π(2n)`: every prime power in `C(2n, n)` is at most `2n`. -/
theorem centralBinom_le_pow_primeCount {n : Nat} (hn : 1 ≤ n) :
    centralBinom n ≤ (2 * n) ^ primeCount (2 * n) := by
  unfold primeCount
  rw [← bprod_const]
  apply le_bprod_of_pow_dvd _ _ (centralBinom_pos n)
  · intro i; split <;> omega
  · intro p e hp hpe
    simp only [hp, ↓reduceIte]
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp; omega
    · exact pow_dvd_centralBinom_le hp he hpe
  · intro p hp hpC
    have := prime_dvd_centralBinom_le hp hpC; omega

/-- `4ⁿ ≤ (2n + 1) · (2n)^π(2n)`. -/
theorem four_pow_le_primeCount {n : Nat} (hn : 1 ≤ n) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ primeCount (2 * n) :=
  Nat.le_trans (four_pow_le_centralBinom n)
    (Nat.mul_le_mul_left _ (centralBinom_le_pow_primeCount hn))

/-- `2n + 1 ≤ 2ⁿ` for `n ≥ 3`. -/
theorem two_mul_add_one_le_two_pow : ∀ n, 3 ≤ n → 2 * n + 1 ≤ 2 ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 2
    · subst h; decide
    · have := ih (by omega); rw [Nat.pow_succ]; omega

/-- **Chebyshev's lower bound** (elementary form). For `m ≥ 6`: `2^⌊m/2⌋ ≤ m^π(m)`, i.e.
`π(m) ≥ ⌊m/2⌋ · log 2 / log m`. -/
theorem chebyshev_lower {m : Nat} (hm : 6 ≤ m) : 2 ^ (m / 2) ≤ m ^ primeCount m := by
  have hn : 3 ≤ m / 2 := by omega
  have h4 := four_pow_le_primeCount (n := m / 2) (by omega)
  have h2 := two_mul_add_one_le_two_pow (m / 2) hn
  have hpos : 0 < 2 ^ (m / 2) := Nat.pow_pos (by omega)
  have key : 2 ^ (m / 2) ≤ (2 * (m / 2)) ^ primeCount (2 * (m / 2)) := by
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ (m / 2)) _ hpos
    have e : 4 ^ (m / 2) = 2 ^ (m / 2) * 2 ^ (m / 2) := by
      rw [← Nat.pow_add, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]; congr 1; omega
    rw [← e]
    exact Nat.le_trans h4 (Nat.mul_le_mul_right _ h2)
  calc 2 ^ (m / 2) ≤ (2 * (m / 2)) ^ primeCount (2 * (m / 2)) := key
    _ ≤ m ^ primeCount (2 * (m / 2)) := Nat.pow_le_pow_left (by omega) _
    _ ≤ m ^ primeCount m := Nat.pow_le_pow_right (by omega) (primeCount_mono (by omega))

/-! ## Chebyshev's upper bound -/

/-- `k^(#primes in (k, n]) ≤ 4ⁿ`: these primes all exceed `k`, and their product is at most the
primorial. -/
theorem pow_count_le_four_pow (k n : Nat) :
    k ^ countBelow (fun i => Prime i ∧ k < i) (n + 1) ≤ 4 ^ n := by
  rw [← bprod_const]
  calc bprod (fun i => if Prime i ∧ k < i then k else 1) (n + 1)
      ≤ bprod (fun i => if Prime i then i else 1) (n + 1) := by
        apply bprod_le_bprod
        intro i _
        by_cases h : Prime i ∧ k < i
        · simp only [h.1, h.2, and_self, ↓reduceIte]; omega
        · simp only [h, ↓reduceIte]
          split
          · next hp => have := hp.1; omega
          · omega
    _ ≤ 4 ^ n := primorial_le_four_pow n

/-- `k^π(n) ≤ k^(k+1) · 4ⁿ` for `k ≥ 1`. -/
theorem pow_primeCount_le (k n : Nat) (hk : 1 ≤ k) : k ^ primeCount n ≤ k ^ (k + 1) * 4 ^ n := by
  have hc := countBelow_le Prime k (n + 1)
  calc k ^ primeCount n
      ≤ k ^ (countBelow (fun i => Prime i ∧ k < i) (n + 1) + (k + 1)) :=
        Nat.pow_le_pow_right hk (by unfold primeCount; omega)
    _ = k ^ (k + 1) * k ^ countBelow (fun i => Prime i ∧ k < i) (n + 1) := by
        rw [Nat.pow_add, Nat.mul_comm]
    _ ≤ k ^ (k + 1) * 4 ^ n := Nat.mul_le_mul_left _ (pow_count_le_four_pow k n)

/-- **Chebyshev's upper bound** (elementary form). For `n ≥ 1`: `n^π(n) ≤ 1024ⁿ`, i.e.
`π(n) ≤ 10 log 2 · n / log n`. (Apply the previous bound with `k = ⌊√n⌋`.) -/
theorem chebyshev_upper {n : Nat} (hn : 1 ≤ n) : n ^ primeCount n ≤ 1024 ^ n := by
  obtain ⟨k, hk1, hk2⟩ := exists_sqrt n
  have hk : 1 ≤ k := by
    apply Classical.byContradiction; intro h
    obtain rfl : k = 0 := by omega
    omega
  -- `k^(k+1) ≤ 4ⁿ`, since `k < 2ᵏ` and `k(k+1) ≤ 2n`.
  have hkk : k ^ (k + 1) ≤ 4 ^ n := by
    have h1 : k ≤ 2 ^ k := Nat.le_of_lt (lt_pow_self (by omega) k)
    have h2 : k * (k + 1) ≤ 2 * n := by
      have : k * (k + 1) = k * k + k := by grind
      have : k ≤ k * k := Nat.le_mul_of_pos_right k hk
      omega
    calc k ^ (k + 1) ≤ (2 ^ k) ^ (k + 1) := Nat.pow_le_pow_left h1 _
      _ = 2 ^ (k * (k + 1)) := by rw [← Nat.pow_mul]
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by omega) h2
      _ = 4 ^ n := by rw [Nat.pow_mul]
  have hkp : k ^ primeCount n ≤ 16 ^ n :=
    calc k ^ primeCount n ≤ k ^ (k + 1) * 4 ^ n := pow_primeCount_le k n hk
      _ ≤ 4 ^ n * 4 ^ n := Nat.mul_le_mul_right _ hkk
      _ = 16 ^ n := by rw [← Nat.mul_pow]
  -- `n ≤ 4k²`, since `n < (k+1)² ≤ (2k)²`.
  have hn4 : n ≤ 4 * (k * k) := by
    have : (k + 1) * (k + 1) ≤ (2 * k) * (2 * k) := Nat.mul_le_mul (by omega) (by omega)
    have : (2 * k) * (2 * k) = 4 * (k * k) := by grind
    omega
  have hpi := primeCount_le n
  calc n ^ primeCount n ≤ (4 * (k * k)) ^ primeCount n := Nat.pow_le_pow_left hn4 _
    _ = 4 ^ primeCount n * (k ^ primeCount n * k ^ primeCount n) := by
        rw [Nat.mul_pow, Nat.mul_pow]
    _ ≤ 4 ^ n * (16 ^ n * 16 ^ n) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hpi) (Nat.mul_le_mul hkp hkp)
    _ = 1024 ^ n := by rw [← Nat.mul_pow, ← Nat.mul_pow]

/-! ## The logarithmic form -/

/-- `xᵏ > 0` and `log (xᵏ) = k · log x` for `x > 0`. -/
theorem pow_pos_and_log_pow {x : R} (hx : 0 < x) :
    ∀ k : Nat, 0 < x ^ k ∧ R.log (x ^ k) = (k : R) * R.log x
  | 0 => by
    refine ⟨by show (0 : R) < 1; grind, ?_⟩
    show R.log 1 = _
    rw [R.log_one]; grind
  | k + 1 => by
    obtain ⟨h1, h2⟩ := pow_pos_and_log_pow hx k
    have e : x ^ (k + 1) = x ^ k * x := rfl
    rw [e]
    refine ⟨Lean.Grind.OrderedRing.mul_pos h1 hx, ?_⟩
    rw [R.log_mul h1 hx, h2]; grind

/-- `log` is monotone on the positive reals. -/
theorem log_le_log {x y : R} (hx : 0 < x) (h : x ≤ y) : R.log x ≤ R.log y := by
  by_cases he : x = y
  · subst he; grind
  · have hlt : x < y := by grind
    have := R.log_strictMono hx hlt
    grind

/-- Positive naturals are positive reals. -/
theorem natCast_pos' {n : Nat} (h : 0 < n) : (0 : R) < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have : ((k + 1 : Nat) : R) = k + 1 := by grind
  have : (0 : R) ≤ k := Lean.Grind.OrderedRing.natCast_nonneg
  grind

/-- The cast `ℕ → R` is monotone. -/
theorem natCast_le' {n m : Nat} (h : n ≤ m) : (n : R) ≤ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have : ((n + k : Nat) : R) = n + k := by grind
  have : (0 : R) ≤ k := Lean.Grind.OrderedRing.natCast_nonneg
  grind

/-- From `aᵏ ≤ bˡ` in `ℕ` (with `a, b > 0`) to `k log a ≤ l log b` in `R`. -/
theorem log_ineq_of_pow_le {a b k l : Nat} (ha : 0 < a) (hb : 0 < b) (h : a ^ k ≤ b ^ l) :
    (k : R) * R.log a ≤ (l : R) * R.log b := by
  have hcast : ((a ^ k : Nat) : R) ≤ ((b ^ l : Nat) : R) := natCast_le' h
  have ea : ((a ^ k : Nat) : R) = (a : R) ^ k := by grind
  have eb : ((b ^ l : Nat) : R) = (b : R) ^ l := by grind
  rw [ea, eb] at hcast
  obtain ⟨hpa, hla⟩ := pow_pos_and_log_pow (natCast_pos' ha) k
  obtain ⟨_, hlb⟩ := pow_pos_and_log_pow (natCast_pos' hb) l
  rw [← hla, ← hlb]
  exact log_le_log hpa hcast

/-- **Chebyshev's bounds.** For every `m ≥ 6`,
`⌊m/2⌋ · log 2 ≤ π(m) · log m ≤ m · log 1024`.
So `π(m)` is of order `m / log m`: bounded above and below by constant multiples of it. -/
theorem chebyshev_bounds {m : Nat} (hm : 6 ≤ m) :
    ((m / 2 : Nat) : R) * R.log 2 ≤ (primeCount m : R) * R.log m ∧
      (primeCount m : R) * R.log m ≤ (m : R) * R.log 1024 := by
  constructor
  · have := log_ineq_of_pow_le (by omega) (by omega) (chebyshev_lower hm)
    exact this
  · have := log_ineq_of_pow_le (by omega) (by omega) (chebyshev_upper (n := m) (by omega))
    exact this

end Foundations.NumberTheory
