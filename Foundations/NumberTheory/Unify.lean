import Foundations.NumberTheory.Dirichlet
import Foundations.NumberTheory.PNTTheorem

/-!
# Unifying the Dirichlet and PNT blocks

This part of the library grew two independent towers on top of `Chebyshev`:

* the **Dirichlet block** (`ArithmeticFunctions` … `Dirichlet`, namespace
  `Foundations.NumberTheory`), which works with the generic field sum `gsum`, the logarithm
  `lnat n` of a natural number, its own von Mangoldt function `vonMangoldt` and Möbius function
  `mobius` (defined through squarefreeness and the number `ω(n)` of prime factors), and writes
  Chebyshev's function as `ψ(N) = gsum vonMangoldt (N + 1)`;
* the **PNT block** (`PNT*`, namespace `Foundations.NumberTheory.PNT`), which works with the real
  sum `fsum`, the logarithm `R.log (n : R)`, and its own `PNT.vonMangoldt`, `PNT.psi`,
  `PNT.mobius` (a product of local factors over the primes `q ≤ n`).

This file proves that the two towers talk about the same objects. First the sum operators
agree (`fsum_eq_gsum`), hence so do the two divisor sums (`dsum_eq`), and so do the two
logarithms on positive integers (`lnat_eq_log`). Then:

* `vonMangoldt_eq` — `PNT.vonMangoldt n = vonMangoldt n`;
* `mobius_eq` — `PNT.mobius n = mobius n` for `n ≥ 1`, by strong induction on `n`, peeling off
  one prime at a time with the multiplicativity rules proved separately on each side (at `n = 0`
  the two conventions differ, `mobius_zero_ne`, which is harmless since `μ(0)` never enters a
  divisor sum);
* `psi_eq_gsum` — `PNT.psi N = gsum vonMangoldt (N + 1)`;
* `mertens_sum_eq` — the sum `Σ_{n ≤ N} Λ(n)/n` of `mertens_lower`/`mertens_upper` is the sum of
  `PNT.mertens_vonMangoldt`, and as an illustration both pairs of bounds are restated about one
  common sum (`mertens_both`).

As a payoff, the prime number theorem can be stated in the Dirichlet block's language:
`gsum vonMangoldt (N + 1) / N → 1` (`psi_gsum_tendsto_one`).
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-! ## The sum operators and the logarithms -/

/-- **`fsum = gsum`.** The real finite sum `fsum` of the analysis library and the field sum
`gsum` (specialised to `R`) are the same function. -/
theorem fsum_eq_gsum (f : Nat → R) (n : Nat) : fsum f n = gsum f n := by
  induction n with
  | zero => rfl
  | succ n ih => show fsum f n + f n = gsum f n + f n; rw [ih]

/-- On positive integers the Dirichlet block's `lnat n` is the real logarithm `log n`. -/
theorem lnat_eq_log {n : Nat} (hn : n ≠ 0) : lnat n = R.log (n : R) := by
  unfold lnat; rw [ite_eq_right hn]

/-- On primes, `lnat p = log p`. -/
theorem lnat_prime {p : Nat} (hp : Prime p) : lnat p = R.log (p : R) :=
  lnat_eq_log (by have := hp.1; omega)

/-- **The two divisor sums agree.** `PNT.dsum f n = dsum f n`: both are `Σ_{d ∣ n} f(d)`. -/
theorem dsum_eq (f : Nat → R) (n : Nat) : PNT.dsum f n = dsum f n := by
  unfold PNT.dsum dsum; rw [fsum_eq_gsum]

/-! ## Von Mangoldt's function and ψ -/

/-- **The two von Mangoldt functions agree.** `PNT.vonMangoldt n = vonMangoldt n` for all `n`. -/
theorem vonMangoldt_eq (n : Nat) : PNT.vonMangoldt n = vonMangoldt n := by
  unfold PNT.vonMangoldt vonMangoldt
  rw [fsum_eq_gsum]
  apply gsum_congr; intro p _
  rw [fsum_eq_gsum]
  apply gsum_congr; intro k _
  by_cases h : Prime p ∧ 1 ≤ k ∧ p ^ k = n
  · rw [ite_eq_left h, ite_eq_left h, lnat_prime h.1]
  · rw [ite_eq_right h, ite_eq_right h]

/-- The two von Mangoldt functions are equal as functions. -/
theorem vonMangoldt_funext : PNT.vonMangoldt = vonMangoldt := funext vonMangoldt_eq

/-- **The two ψ-functions agree.** Chebyshev's `PNT.psi N` equals the Dirichlet block's
`ψ(N) = gsum vonMangoldt (N + 1)`. -/
theorem psi_eq_gsum (N : Nat) : PNT.psi N = gsum vonMangoldt (N + 1) := by
  rw [PNT.psi_eq_sum_vonMangoldt, fsum_eq_gsum, vonMangoldt_funext]

/-- **The prime number theorem in the Dirichlet block's language.**
`(Σ_{n ≤ N} Λ(n)) / N → 1`, with `Λ` and the sum those of `ArithmeticFunctions`. -/
theorem psi_gsum_tendsto_one : Tendsto (fun N => gsum vonMangoldt (N + 1) / (N : R)) 1 := by
  have h := PNT.psi_div_tendsto_one
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  exact ⟨N₀, fun N hN => by show abs (gsum vonMangoldt (N + 1) / (N : R) - 1) < ε
                            rw [← psi_eq_gsum]; exact hN₀ N hN⟩

/-- The Dirichlet block's Chebyshev bound `psi_le` and the PNT block's agree up to presentation:
both bound the same `ψ(N)` by `N log 1024`. -/
theorem psi_le_both {N : Nat} (hN : 0 < N) :
    gsum vonMangoldt (N + 1) ≤ (N : R) * chebC ∧ PNT.psi N ≤ (N : R) * R.log 1024 :=
  ⟨psi_le hN, PNT.psi_le N⟩

/-! ## Mertens' sum -/

/-- **The two Mertens sums agree.** The sum `Σ_{n ≤ N} Λ(n)/n` of `mertens_lower` and
`mertens_upper` equals the sum `Σ_{n ≤ N} Λ(n) · (1/n)` of `PNT.mertens_vonMangoldt`. -/
theorem mertens_sum_eq (N : Nat) :
    gsum (fun d => vonMangoldt d / (d : R)) (N + 1) =
      fsum (fun n => PNT.vonMangoldt n * (1 / (n : R))) (N + 1) := by
  rw [fsum_eq_gsum]
  apply gsum_congr; intro n _
  rw [vonMangoldt_eq, Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind

/-- `chebC` is `log 1024`. -/
theorem chebC_eq : chebC = R.log 1024 := by
  unfold chebC; congr 1

/-- **Mertens' first theorem, both versions at once.** For `N ≥ 1` the common sum
`S(N) = Σ_{n ≤ N} Λ(n)/n` satisfies the Dirichlet block's bounds `log N − 1 ≤ S(N) ≤ log N + log 1024`
and the PNT block's bounds `−1 ≤ S(N) − log N ≤ log 1024` — which are the same statement. -/
theorem mertens_both {N : Nat} (hN : 1 ≤ N) :
    (R.log (N : R) - 1 ≤ gsum (fun d => vonMangoldt d / (d : R)) (N + 1) ∧
      gsum (fun d => vonMangoldt d / (d : R)) (N + 1) ≤ R.log (N : R) + R.log 1024) ∧
    (-1 ≤ gsum (fun d => vonMangoldt d / (d : R)) (N + 1) - R.log (N : R) ∧
      gsum (fun d => vonMangoldt d / (d : R)) (N + 1) - R.log (N : R) ≤ R.log 1024) := by
  have h1 := mertens_lower (N := N) (by omega)
  have h2 := mertens_upper (N := N) (by omega)
  rw [lnat_eq_log (by omega)] at h1 h2
  rw [chebC_eq] at h2
  have h3 := PNT.mertens_vonMangoldt hN
  rw [← mertens_sum_eq] at h3
  exact ⟨⟨h1, h2⟩, h3⟩

/-! ## The Möbius function -/

/-- **The two Möbius functions agree.** `PNT.mobius n = mobius n` for every `n ≥ 1`: by strong
induction, writing `n = p · m` with `p` prime and using `μ(p m) = −μ(m)` for `p ∤ m` and
`μ(p² e) = 0` on both sides. (At `n = 0`, outside the range where `μ` is meaningful, the two
conventions differ: the empty-ish product gives `PNT.mobius 0 = 1`, while `mobius 0 = 0`.) -/
theorem mobius_eq : ∀ n, 1 ≤ n → PNT.mobius n = mobius n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro hn1
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [show n = 1 by omega, PNT.mobius_one, NumberTheory.mobius_one]
  · obtain ⟨p, hp, hpn⟩ := exists_prime_dvd hn
    obtain ⟨m, rfl⟩ := hpn
    have hp2 := hp.1
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · omega
    have hmlt : m < p * m := by
      have := Nat.mul_le_mul_right m hp2; omega
    by_cases hpm : p ∣ m
    · rw [PNT.mobius_mul_prime_dvd hp hm hpm]
      obtain ⟨e, rfl⟩ := hpm
      rw [show p * (p * e) = p ^ 2 * e by rw [Nat.pow_two, Nat.mul_assoc],
        NumberTheory.mobius_prime_pow_mul hp (Nat.le_refl 2)]
    · rw [PNT.mobius_mul_prime hp hm hpm, NumberTheory.mobius_prime_mul hp hpm (by omega),
        ih m hmlt hm]

/-- At `0` the two conventions differ: `PNT.mobius 0 = 1` but `mobius 0 = 0`. -/
theorem mobius_zero_ne : PNT.mobius 0 = 1 ∧ mobius 0 = 0 := by
  constructor
  · show PNT.fprod _ 0 * PNT.mobFactor 0 0 = 1
    unfold PNT.mobFactor
    have : ¬ Prime 0 := fun h => by have := h.1; omega
    rw [ite_eq_right this]; show (1 : R) * 1 = 1; grind
  · unfold mobius; rw [ite_eq_left rfl]

/-- **Möbius inversion data agree.** Since the Möbius functions agree on `n ≥ 1`, the divisor-sum
identity `Σ_{d ∣ n} μ(d) = [n = 1]` of either block is the same statement: here the PNT block's
version is derived for the Dirichlet block's `μ`, with the PNT block's divisor sum. -/
theorem dsum_mobius_cross {n : Nat} (hn : 1 ≤ n) :
    PNT.dsum mobius n = if n = 1 then 1 else 0 := by
  rw [← PNT.dsum_mobius hn]
  unfold PNT.dsum
  apply fsum_congr; intro d _
  by_cases hd : d ∣ n
  · rw [ite_eq_left hd, ite_eq_left hd, mobius_eq d (Nat.pos_of_dvd_of_pos hd (by omega))]
  · rw [ite_eq_right hd, ite_eq_right hd]

end Foundations.NumberTheory
