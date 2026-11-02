import Foundations.NumberTheory.Corollaries

/-!
# Exercises X: Analytic number theory

Problems on the analytic half of Part XII (`Foundations/NumberTheory`): characters of finite
abelian groups and Dirichlet characters (`DualGroup`, `DirichletCharacters`), Mertens'
estimate (`Mertens`, `Unify`), Dirichlet's theorem (`Dirichlet`), Euler's divergence of
`Σ 1/p` and the prime number theorem (`Corollaries`, `PNT*`), and the Möbius function
(`Mobius`).

*Two blocks.* The part has two parallel developments: the **Dirichlet block** (namespace
`Foundations.NumberTheory`: `gsum`, `vonMangoldt`, `mobius`, `lnat n = log n`) and the
**PNT block** (namespace `Foundations.NumberTheory.PNT`: `fsum`, `PNT.theta`, `PNT.psi`,
`PNT.vonMangoldt`). `Unify` shows they agree; each exercise below stays inside one block.

*Tools.* The library's reals `R` are registered as an ordered field, so `grind` closes most
linear goals over `R`. `OF.abs_lt` unfolds `|x| < e` into `-e < x ∧ x < e`.
`Tendsto a L` means `∀ ε > 0, ∃ N, ∀ n ≥ N, |a n − L| < ε`.

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in
`Exercises/Problems/NumberTheory2.lean`.
-/

namespace Exercises.NumberTheory2

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Foundations.NumberTheory
open Foundations.Algebra Foundations.Algebra.FiniteType Lean.Grind OF

/-! ## Characters -/

/-- **Exercise 10.1 (★) — A non-trivial character sums to zero.** If `χ` is a character of a
finite abelian group `G` other than the trivial character, then `Σ_{x ∈ G} χ(x) = 0`.

*Hint:* the first orthogonality relation computes `Σ_x χ(x)` by cases on `χ = 1`.

*Uses:* `sum_character`, `ite_eq_right`. -/
theorem sum_nontrivial_character {G : Type} [CommGroup G] [FiniteType G] (χ : Character G)
    (hχ : χ ≠ Character.one) : sumOver χ.1 = 0 := by
  -- SOLUTION
  rw [sum_character, ite_eq_right hχ]
  -- END

/-! ## Primes in progressions and the sum of their reciprocals -/

/-- **Exercise 10.2 (★★) — Primes that are 3 mod 8 and 1 mod 3.** Above every bound there is
a prime `p` with `p ≡ 3 (mod 8)` and `p ≡ 1 (mod 3)`. (In particular there are infinitely many
primes `≡ 3 (mod 8)`.)

*Hint:* combine the two congruences into one modulo `24` (Chinese remainder theorem: which
residue mod 24 is `3` mod 8 and `1` mod 3?), check it is coprime to `24` with `decide`, and
apply Dirichlet's theorem. `omega` recovers the two congruences.

*Uses:* `dirichlet`. -/
theorem primes_three_mod_eight_one_mod_three (N : Nat) :
    ∃ p, N ≤ p ∧ Prime p ∧ p % 8 = 3 ∧ p % 3 = 1 := by
  -- SOLUTION
  obtain ⟨p, hNp, hp, h⟩ := dirichlet (q := 24) (by decide) (a := 19) (by decide) N
  exact ⟨p, hNp, hp, by omega, by omega⟩
  -- END

/-- **Exercise 10.3 (★★) — Eventually above every bound.** For every real `B`, the partial sums
`Σ_{p ≤ M} 1/p` are `≥ B` not just for one `M` but for all `M` from some point on.

*Hint:* Euler's theorem gives one `N`; the partial sums of a series with non-negative terms
increase.

*Uses:* `euler_sum_reciprocal_primes`, `R.fsum_mono`. -/
theorem eventually_sum_reciprocal_primes_ge (B : R) :
    ∃ N, ∀ M, N ≤ M → B ≤ fsum (fun p => if Prime p then 1 / (p : R) else 0) (M + 1) := by
  -- SOLUTION
  obtain ⟨N, hN⟩ := euler_sum_reciprocal_primes B
  refine ⟨N, fun M hM => ?_⟩
  have hnn : ∀ k, (0 : R) ≤ (fun p => if Prime p then 1 / (p : R) else 0) k := by
    intro k
    by_cases hk : Prime k
    · simp only [hk, ↓reduceIte]
      exact Std.le_of_lt (div_pos (by grind) (natCast_pos' (by have := hk.1; omega)))
    · simp only [hk, ↓reduceIte]; grind
  have := fsum_mono hnn (show N + 1 ≤ M + 1 by omega)
  grind
  -- END

/-! ## Mertens and Chebyshev -/

/-- **Exercise 10.4 (★★★) — `Σ_{n ≤ N} Λ(n)/n ∼ log N`.** Mertens' estimate says the sum differs
from `log N` by a bounded amount; deduce that the ratio of the two tends to `1`.

*Hint:* write `S(N)/log N − 1 = (S(N) − log N)/log N`. By Mertens' bounds the numerator lies in
`[−1, log 1024]`, so its absolute value is at most `c = 1 + log 1024`. Given `ε`, choose `N₀`
with `log N ≥ c/ε` for `N ≥ N₀`. Then `|S(N) − log N| ≤ c ≤ ε log N`; divide by `log N`
(`div_le_of_le_mul`, `PNT.abs_div_le_of_le` or a direct `OF.abs_lt` argument).

*Uses:* `mertens_both`, `PNT.log_eventually_ge`, `PNT.log_nonneg'` (for `log 1024 ≥ 0`),
`div_pos`. -/
theorem mertens_ratio_tendsto :
    Tendsto (fun N => gsum (fun d => vonMangoldt d / (d : R)) (N + 1) / R.log (N : R)) 1 := by
  -- SOLUTION
  intro ε hε
  have hc0 : 0 ≤ R.log 1024 := PNT.log_nonneg' (by grind)
  have hc : 0 < 1 + R.log 1024 := by grind
  obtain ⟨N₀, hN₀1, hN₀⟩ := PNT.log_eventually_ge (2 * (1 + R.log 1024) / ε)
  refine ⟨N₀, fun N hN => ?_⟩
  have hL := hN₀ N hN
  have hcε : 0 < 2 * (1 + R.log 1024) / ε := div_pos (by grind) hε
  obtain ⟨-, h1, h2⟩ := mertens_both (N := N) (by omega)
  show abs (gsum (fun d => vonMangoldt d / (d : R)) (N + 1) / R.log (N : R) - 1) < ε
  generalize gsum (fun d => vonMangoldt d / (d : R)) (N + 1) = S at h1 h2 ⊢
  generalize R.log (N : R) = L at hL h1 h2 ⊢
  generalize R.log 1024 = c at hc0 hc hL hcε h1 h2 ⊢
  have hL0 : 0 < L := by grind
  have hLε : 2 * (1 + c) ≤ ε * L := by
    have e : 2 * (1 + c) = 2 * (1 + c) / ε * ε := by
      rw [Field.div_eq_mul_inv]
      have : ε * ε⁻¹ = 1 := Field.mul_inv_cancel (by grind)
      grind
    have := OrderedRing.mul_le_mul_of_nonneg_left hL (Std.le_of_lt hε)
    grind
  have e : S / L - 1 = (S - L) * L⁻¹ := by
    rw [Field.div_eq_mul_inv]
    have : L * L⁻¹ = 1 := Field.mul_inv_cancel (by grind)
    grind
  have hinv : 0 < L⁻¹ := by
    have := div_pos (show (0 : R) < 1 by grind) hL0
    rw [Field.div_eq_mul_inv] at this; grind
  have hLL : L * L⁻¹ = 1 := Field.mul_inv_cancel (by grind)
  rw [e]
  apply OF.abs_lt.2
  have u1 := OrderedRing.mul_le_mul_of_nonneg_right h2 (Std.le_of_lt hinv)
  have u2 := OrderedRing.mul_le_mul_of_nonneg_right h1 (Std.le_of_lt hinv)
  have u3 := OrderedRing.mul_le_mul_of_nonneg_right hLε (Std.le_of_lt hinv)
  have u3' : 2 * (1 + c) * L⁻¹ ≤ ε := by
    have : ε * L * L⁻¹ = ε * (L * L⁻¹) := Semiring.mul_assoc _ _ _
    rw [this, hLL] at u3; grind
  have k1 : 2 * (1 + c) * L⁻¹ = 2 * L⁻¹ + 2 * (c * L⁻¹) := by grind
  have k2 : -1 * L⁻¹ = -L⁻¹ := by grind
  rw [k1] at u3'
  rw [k2] at u2
  have u6 : 0 ≤ c * L⁻¹ := OrderedRing.mul_nonneg hc0 (Std.le_of_lt hinv)
  generalize (S - L) * L⁻¹ = x at u1 u2 ⊢
  generalize c * L⁻¹ = z at u1 u3' u6
  generalize L⁻¹ = y at hinv u2 u3'
  constructor <;> grind
  -- END

/-- **Exercise 10.5 (★) — Chebyshev's bound for `θ`.** The sum `θ(N) = Σ_{p ≤ N} log p` is at
most `N · log 1024`.

(The library proves the sharper `θ(N) ≤ N log 4` directly; here go through `ψ`, the sum of
`log p` over prime powers `pᵏ ≤ N`.)

*Hint:* `θ ≤ ψ`, and Chebyshev's bound for `ψ`.

*Uses:* `PNT.theta_le_psi`, `PNT.psi_le`. -/
theorem theta_le_mul_log_1024 (N : Nat) : PNT.theta N ≤ (N : R) * R.log 1024 := by
  -- SOLUTION
  have := PNT.theta_le_psi N
  have := PNT.psi_le N
  grind
  -- END

/-! ## The prime number theorem -/

/-- **Exercise 10.6 (★) — `π(N) → ∞`.** For every `k`, from some point on there are at least
`k` primes up to `N`.

*Hint:* the library shows that `π` is unbounded and that it is monotone.

*Uses:* `primeCount_unbounded`, `primeCount_mono`. -/
theorem primeCount_tendsto_top (k : Nat) : ∃ N₀, ∀ N, N₀ ≤ N → k ≤ primeCount N := by
  -- SOLUTION
  obtain ⟨N₀, h⟩ := primeCount_unbounded k
  exact ⟨N₀, fun N hN => Nat.le_trans h (primeCount_mono hN)⟩
  -- END

/-- **Exercise 10.7 (★★) — A Chebyshev-type lower bound from the PNT.** For all large `N`,
`π(N) · log N ≥ N/2`.

*Hint:* apply the prime number theorem with `ε = 1/2`: from some point on,
`π(N) log N / N > 1/2`. Multiply by `N > 0` (`a / N · N = a` for `N ≠ 0`).

*Uses:* `PNT.prime_number_theorem` (unfold `PNT.PrimeNumberTheorem`), `OF.abs_lt`,
`OrderedRing.mul_lt_mul_of_pos_right`, `natCast_pos'`. -/
theorem primeCount_mul_log_ge_half :
    ∃ N₀, ∀ N : Nat, N₀ ≤ N → (N : R) / 2 ≤ (primeCount N : R) * R.log (N : R) := by
  -- SOLUTION
  obtain ⟨N₀, hN₀⟩ := PNT.prime_number_theorem (1 / 2) (by grind)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have h := (OF.abs_lt.1 (hN₀ N (by omega))).1
  simp only at h
  have hn : (0 : R) < (N : R) := natCast_pos' (by omega)
  generalize (primeCount N : R) * R.log (N : R) = a at h ⊢
  have e : a / (N : R) * (N : R) = a := by
    rw [Field.div_eq_mul_inv]
    have : (N : R) * (N : R)⁻¹ = 1 := Field.mul_inv_cancel (by grind)
    grind
  have := OrderedRing.mul_lt_mul_of_pos_right (show 1 / 2 < a / (N : R) by grind) hn
  rw [e] at this
  have e2 : (N : R) / 2 = 1 / 2 * (N : R) := by
    rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
  grind
  -- END

/-! ## The Möbius function -/

/-- **Exercise 10.8 (★★) — Möbius at 30.** `μ(30) = −1`, and the Möbius inversion identity
`Σ_{d ∣ n} μ(d) = [n = 1]` gives `Σ_{d ∣ 30} μ(d) = 0`.

*Hint:* `30 = 2 · (3 · (5 · 1))`; peel off one prime at a time with `μ(p e) = −μ(e)` (the side
conditions `¬ p ∣ e` are `decide`), and finish with `μ(1) = 1`. The sum is one application of
the library's identity.

*Uses:* `mobius_prime_mul`, `mobius_one`, `dsum_mobius`. Primality of small numbers is
decidable: `(by decide : Prime 5)`. -/
theorem mobius_thirty : mobius 30 = -1 ∧ dsum mobius 30 = 0 := by
  -- SOLUTION
  refine ⟨?_, by rw [dsum_mobius (by decide)]; rfl⟩
  have h5 : mobius (5 * 1) = -1 := by
    rw [mobius_prime_mul (by decide) (by decide) (by decide), mobius_one]
  have h3 : mobius (3 * 5) = 1 := by
    rw [mobius_prime_mul (by decide) (by decide) (by decide), h5]; grind
  rw [show (30 : Nat) = 2 * 15 from rfl, mobius_prime_mul (by decide) (by decide) (by decide),
    show (15 : Nat) = 3 * 5 from rfl, h3]
  -- END

end Exercises.NumberTheory2
