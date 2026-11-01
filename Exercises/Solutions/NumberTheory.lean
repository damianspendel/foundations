import Foundations.NumberTheory.Bertrand

/-!
# Exercises IX: Number theory

Problems on elementary number theory, from Part II (`Numbers/Arithmetic.lean`: primes,
Euclid's lemma, factorials), Part IV (`Algebra/Lagrange.lean`: Fermat's little theorem) and
Part XII (`Foundations/NumberTheory`: binomial coefficients, primes modulo 4, Bertrand's
postulate).

All numbers are Lean's `Nat`. Congruences are written with `%`: `a ≡ b (mod n)` is
`a % n = b % n`. Two definitions of primality appear, `Arith.Prime` and `Algebra.IsPrime`;
they are literally the same formula (`2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`), so a proof of one
can be used where the other is expected.

*Tools.* `omega` decides linear arithmetic with `%` and `/` by numerals; the lemmas
`Nat.mul_mod`, `Nat.add_mod` and `Nat.pow_mod` move `% n` inside products, sums and powers.

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in
`Exercises/Problems/NumberTheory.lean`.
-/

namespace Exercises.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith Foundations.NumberTheory

/-! ## Congruences -/

/-- **Exercise 9.1 (★★) — Squares modulo 4.** Every square is `≡ 0` or `≡ 1 (mod 4)`.

*Hint:* the remainder of `n` mod 4 is one of `0, 1, 2, 3` (`omega` proves this
four-way split). In each case, `Nat.mul_mod` reduces `n * n % 4` to a computation on the
remainder.

*Uses:* `Nat.mul_mod`. -/
theorem sq_mod_four (n : Nat) : n * n % 4 = 0 ∨ n * n % 4 = 1 := by
  -- SOLUTION
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
    simp [Nat.mul_mod, h]
  -- END

/-- **Exercise 9.2 (★★) — Sums of two squares avoid 3 mod 4.** For all `x`, `y`,
`x² + y² ≢ 3 (mod 4)`. (So no prime `p ≡ 3 (mod 4)` is a sum of two squares.)

*Hint:* prove (or reuse) the fact about squares modulo 4 from the previous exercise for `x`
and `y`, then `Nat.add_mod` and `omega`.

*Uses:* `Nat.mul_mod`, `Nat.add_mod`. -/
theorem sum_two_sq_mod_four (x y : Nat) : (x * x + y * y) % 4 ≠ 3 := by
  -- SOLUTION
  have sq : ∀ n : Nat, n * n % 4 = 0 ∨ n * n % 4 = 1 := fun n => by
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
      simp [Nat.mul_mod, h]
  rw [Nat.add_mod]
  rcases sq x with hx | hx <;> rcases sq y with hy | hy <;> rw [hx, hy] <;> decide
  -- END

/-- **Exercise 9.3 (★★★) — Fermat's little theorem, second form.** For every prime `p` and
every `a`: `aᵖ ≡ a (mod p)`. (No coprimality assumption.)

The library proves `a^(p-1) % p = 1` when `p ∤ a`.

*Hint:* split on whether `p ∣ a`. Write `aᵖ = a^(p-1) * a` (valid since `p ≥ 1`).
If `p ∣ a`, both sides are `0 mod p`. Otherwise use `Nat.mul_mod` and the library's version.

*Uses:* `Algebra.fermat`, `Nat.mul_mod`, `Nat.pow_succ`, `Nat.mod_eq_zero_of_dvd`. -/
theorem pow_prime_mod (p a : Nat) (hp : Foundations.Algebra.IsPrime p) : a ^ p % p = a % p := by
  -- SOLUTION
  have hp2 := hp.1
  have e : a ^ p = a ^ (p - 1) * a := by
    rw [← Nat.pow_succ]; congr 1; omega
  rw [e]
  by_cases ha : p ∣ a
  · rw [Nat.mod_eq_zero_of_dvd ha, Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd ha _)]
  · rw [Nat.mul_mod, Foundations.Algebra.fermat p a hp ha, Nat.one_mul, Nat.mod_mod]
  -- END

/-! ## Primes -/

/-- **Exercise 9.4 (★★★) — `p` divides the middle binomial coefficients.** If `p` is prime and
`0 < k < p`, then `p ∣ C(p, k)`.

*Hint:* the library's factorial formula gives `C(p, k) · k! · (p−k)! = p!`, and `p ∣ p!`.
By Euclid's lemma `p` divides one of the three factors on the left. Show, by induction on
`m`, that `p ∤ m!` for `m < p` (again with Euclid's lemma, since `(m+1)! = (m+1)·m!`).

*Uses:* `choose_mul_fact`, `euclid_lemma`, `dvd_fact`, `fact`, `Nat.le_of_dvd`. -/
theorem prime_dvd_choose {p k : Nat} (hp : Prime p) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ choose p k := by
  -- SOLUTION
  have not_dvd_fact : ∀ m, m < p → ¬ p ∣ fact m := by
    intro m
    induction m with
    | zero =>
      intro _ h
      have h1 : p ≤ 1 := Nat.le_of_dvd (by decide) h
      have := hp.1
      omega
    | succ m ih =>
      intro hm h
      rcases euclid_lemma hp h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'; omega
      · exact ih (by omega) h'
  have hfact := choose_mul_fact p k (p - k) (by omega)
  have hdvd : p ∣ choose p k * fact k * fact (p - k) :=
    hfact ▸ dvd_fact (by have := hp.1; omega) (Nat.le_refl p)
  rcases euclid_lemma hp hdvd with h | h
  · rcases euclid_lemma hp h with h | h
    · exact h
    · exact absurd h (not_dvd_fact k hkp)
  · exact absurd h (not_dvd_fact (p - k) (by omega))
  -- END

/-- **Exercise 9.5 (★) — Primes ≡ 3 (mod 4) are unbounded.** There is no bound `N` below
which all primes `p ≡ 3 (mod 4)` lie.

*Hint:* the library's Euclid-style theorem produces such a prime above any given number.

*Uses:* `exists_prime_mod_four_eq_three`. -/
theorem primes_mod_four_unbounded : ¬ ∃ N, ∀ p, Prime p → p % 4 = 3 → p < N := by
  -- SOLUTION
  rintro ⟨N, hN⟩
  obtain ⟨p, hNp, hp, h3⟩ := exists_prime_mod_four_eq_three N
  have := hN p hp h3
  omega
  -- END

/-- **Exercise 9.6 (★) — A prime between 100 and 200.**

*Hint:* Bertrand's postulate.

*Uses:* `bertrand`. -/
theorem prime_between_100_200 : ∃ p, Prime p ∧ 100 < p ∧ p ≤ 200 := by
  -- SOLUTION
  exact bertrand 100 (by omega)
  -- END

/-- **Exercise 9.7 (★) — The gcd divides the sum.** The greatest common divisor of `a` and `b`,
computed by Euclid's algorithm, divides `a + b`.

*Hint:* the library tells you that `gcd a b` divides both `a` and `b`.

*Uses:* `Arith.gcd_dvd`, `Nat.dvd_add`. -/
theorem gcd_dvd_add (a b : Nat) : gcd a b ∣ a + b := by
  -- SOLUTION
  exact Nat.dvd_add (gcd_dvd a b).1 (gcd_dvd a b).2
  -- END

end Exercises.NumberTheory
