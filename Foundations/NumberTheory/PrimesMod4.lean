import Foundations.Numbers.Arithmetic
import Foundations.Algebra.QuadraticResidues

/-!
# Primes in the progressions 4k + 1 and 4k + 3

Euclid proved (Elements IX.20) that there are infinitely many primes: multiply the primes you
have, add one, and look at any prime factor of the result. Part II formalised that argument as
`Arith.exists_prime_ge`. This chapter opens Part XII by asking a finer question: if we sort the
odd primes by their remainder modulo 4, are there infinitely many of *each* kind?

* Primes `≡ 3 (mod 4)`: 3, 7, 11, 19, 23, 31, … Euclid's trick still works with one twist.
  A number `≡ 3 (mod 4)` cannot have only prime factors `≡ 1 (mod 4)`, since products of
  numbers `≡ 1` stay `≡ 1`. So `4·N! − 1` has a prime factor `≡ 3 (mod 4)`, and it is larger
  than `N` because every number up to `N` divides `N!`. (Textbooks use `4·p₁⋯pₖ − 1`; the
  factorial does the same job and saves us bookkeeping of a finite list of primes.)
* Primes `≡ 1 (mod 4)`: 5, 13, 17, 29, 37, … Here the naive trick fails (products of primes
  `≡ 3` can be `≡ 1`), and we need a genuinely new ingredient: the *first supplement* to
  quadratic reciprocity, proved in Part IV as `neg_one_qr_iff`. It says that `−1` is a square
  modulo an odd prime `q` exactly when `q ≡ 1 (mod 4)`. Any odd prime `q` dividing
  `(2·N!)² + 1` makes `−1` a square modulo `q`, hence `q ≡ 1 (mod 4)`, and again `q > N`.

These are the two simplest cases of **Dirichlet's theorem on primes in arithmetic progressions**
(1837): whenever `gcd(a, m) = 1`, there are infinitely many primes `≡ a (mod m)`. Dirichlet's
proof introduced characters and L-functions, i.e. analysis, into number theory; a Euclid-style
argument exists only for special progressions (those with `a² ≡ 1 mod m`, by a theorem of
Murty). Here we stop at the two progressions modulo 4; the general theorem is proved later in
this part, in `Dirichlet`, by Dirichlet's analytic method.
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Two small facts about primes -/

/-- A prime is at least 2. -/
theorem Prime.two_le {p : Nat} (hp : Prime p) : 2 ≤ p := hp.1

/-- A prime `p ≤ N` (in fact any `1 ≤ p ≤ N`) divides `N!`, so it cannot divide `N! · c + 1`
style numbers; this is the core of all Euclid-type arguments. Here: if `p ∣ a` and `p ∣ a + 1`
then `p = 1`. -/
theorem eq_one_of_dvd_succ {p a : Nat} (h1 : p ∣ a) (h2 : p ∣ a + 1) : p = 1 := by
  have := Nat.dvd_sub h2 h1
  rw [Nat.add_sub_cancel_left] at this
  exact Nat.dvd_one.1 this

/-- If every prime factor of a positive number `m` is `≡ 1 (mod 4)`, then so is `m`: the
residue class `1` is closed under multiplication. -/
theorem mod_four_eq_one_of_factors {m : Nat} (hm : 1 ≤ m)
    (h : ∀ p, Prime p → p ∣ m → p % 4 = 1) : m % 4 = 1 := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases h1 : m = 1
    · subst h1; rfl
    · obtain ⟨p, hp, k, rfl⟩ := exists_prime_dvd (n := m) (by omega)
      have hp2 := hp.1
      have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at hm
        · exact h0
      have hlt : k < p * k := by
        have : 2 * k ≤ p * k := Nat.mul_le_mul_right k hp2
        omega
      have hk4 := ih k hlt hk (fun q hq hqk => h q hq (Nat.dvd_mul_left_of_dvd hqk p))
      have hp4 := h p hp (Nat.dvd_mul_right p k)
      rw [Nat.mul_mod, hp4, hk4]

/-! ## Primes congruent to 3 modulo 4 -/

/-- **Infinitely many primes ≡ 3 (mod 4).** For every `N` there is a prime `p ≥ N` with
`p ≡ 3 (mod 4)`. Proof: a prime factor `≡ 3 (mod 4)` of `4·N! − 1` (Euclid's argument, with
the residue class tracked). -/
theorem exists_prime_mod_four_eq_three (N : Nat) : ∃ p, N ≤ p ∧ Prime p ∧ p % 4 = 3 := by
  have hf := fact_pos N
  -- `M = 4·N! − 1 ≡ 3 (mod 4)`, and `M ≥ 3`.
  let M := 4 * fact N - 1
  have hM4 : M % 4 = 3 := by omega
  -- Not all prime factors of `M` are `≡ 1 (mod 4)`.
  have : ∃ p, Prime p ∧ p ∣ M ∧ p % 4 ≠ 1 := by
    apply Classical.byContradiction
    intro hno
    have := mod_four_eq_one_of_factors (m := M) (by omega)
      (fun p hp hpM => Classical.byContradiction fun h => hno ⟨p, hp, hpM, h⟩)
    omega
  obtain ⟨p, hp, hpM, hp1⟩ := this
  have hp2 := hp.1
  -- `p` is odd, because `M` is odd.
  have hpodd : p % 2 = 1 := by
    apply Classical.byContradiction
    intro hev
    have h2p : 2 ∣ p := by omega
    have := Nat.dvd_trans h2p hpM
    omega
  refine ⟨p, ?_, hp, by omega⟩
  -- If `p < N` then `p ∣ N!`, so `p ∣ 4·N!` and `p ∣ M = 4·N! − 1`: impossible.
  apply Classical.byContradiction
  intro hlt
  have h1 : p ∣ 4 * fact N - 1 := hpM
  have h2 : p ∣ (4 * fact N - 1) + 1 := by
    have : (4 * fact N - 1) + 1 = 4 * fact N := by omega
    rw [this]
    exact Nat.dvd_mul_left_of_dvd (dvd_fact (by omega) (by omega)) 4
  have := eq_one_of_dvd_succ h1 h2
  omega

/-! ## Primes congruent to 1 modulo 4 -/

/-- If an odd prime `q` divides `x² + 1`, then `−1` (that is, `q − 1`) is a quadratic residue
modulo `q`. -/
theorem neg_one_isQR_of_dvd {q x : Nat} (hq : 2 ≤ q) (h : q ∣ x * x + 1) :
    Foundations.Algebra.IsQR (q - 1) q := by
  refine ⟨x, ?_⟩
  have h0 : (x * x + 1) % q = 0 := Nat.mod_eq_zero_of_dvd h
  have hlt : x * x % q < q := Nat.mod_lt _ (by omega)
  have hsum : (x * x % q + 1) % q = 0 := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; exact h0
  rw [Nat.mod_eq_of_lt (show q - 1 < q by omega)]
  -- `x² mod q + 1` is a multiple of `q` lying in `[1, q]`, hence equals `q`.
  have : x * x % q + 1 = q := by
    have hd : q ∣ x * x % q + 1 := Nat.dvd_of_mod_eq_zero hsum
    obtain ⟨c, hc⟩ := hd
    rcases c with _ | _ | c
    · omega
    · omega
    · have : q * (c + 1 + 1) ≥ q * 2 := Nat.mul_le_mul_left q (by omega)
      omega
  omega

/-- **Infinitely many primes ≡ 1 (mod 4).** For every `N` there is a prime `p ≥ N` with
`p ≡ 1 (mod 4)`. Proof: any prime factor `q` of `(2·N!)² + 1` is odd and larger than `N`, and
`−1` is a square modulo `q`; by the first supplement to quadratic reciprocity
(`neg_one_qr_iff`, Part IV), `q ≡ 1 (mod 4)`. -/
theorem exists_prime_mod_four_eq_one (N : Nat) : ∃ p, N ≤ p ∧ Prime p ∧ p % 4 = 1 := by
  have hf := fact_pos N
  let x := 2 * fact N
  obtain ⟨q, hq, hqM⟩ := exists_prime_dvd (n := x * x + 1) (by
    have : 1 ≤ x * x := Nat.mul_pos (by omega) (by omega)
    omega)
  have hq2 := hq.1
  -- `q` is odd, since `x² + 1` is odd.
  have hqodd : q % 2 = 1 := by
    apply Classical.byContradiction
    intro hev
    have h2q : 2 ∣ q := by omega
    have h2M := Nat.dvd_trans h2q hqM
    have : 2 ∣ x * x := Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right 2 (fact N)) x
    have := eq_one_of_dvd_succ this h2M
    omega
  refine ⟨q, ?_, hq, ?_⟩
  · apply Classical.byContradiction
    intro hlt
    have h1 : q ∣ x * x := Nat.dvd_mul_right_of_dvd
      (Nat.dvd_mul_left_of_dvd (dvd_fact (by omega) (by omega)) 2) x
    have := eq_one_of_dvd_succ h1 hqM
    omega
  · exact (Foundations.Algebra.neg_one_qr_iff (p := q) hq hqodd).1 (neg_one_isQR_of_dvd hq2 hqM)

end Foundations.NumberTheory
