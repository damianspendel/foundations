import Foundations.NumberTheory.NonVanishingComplex
import Foundations.NumberTheory.NonVanishingReal

/-!
# Dirichlet's theorem on primes in arithmetic progressions

> **Theorem (Dirichlet, 1837).** If `a` and `q ≥ 1` are coprime, there are infinitely many
> primes `p ≡ a (mod q)`.

Euclid's argument gives infinitely many primes; variants of it (file `PrimesMod4`) handle a few
progressions such as `4k + 1` and `4k + 3`, but no purely algebraic trick is known that works for
every progression. Dirichlet's proof was the first to bring analysis — infinite series, limits,
and the group characters of `(ℤ/qℤ)ˣ` — to bear on a question about whole numbers, and it is
usually counted as the birth of **analytic number theory**. He was inspired by Euler's proof
(1737) that `Σ 1/p` diverges, which is the case `q = 1`. Our `mertens_lower`,
`Σ_{n ≤ N} Λ(n)/n ≥ log N − 1`, is the case `q = 1` of Dirichlet's theorem in Mertens' form;
it gives the divergence of `Σ log p / p`, which is weaker than Euler's `Σ 1/p = ∞`.

The proof formalised in this part follows the elementary route through the values `L(1, χ)`:

1. `Characters`, `DualGroup`, `DirichletCharacters` — characters of finite abelian groups,
   orthogonality, Dirichlet characters and the sieve for one residue class;
2. `ArithmeticFunctions`, `Mertens`, `PrimePowers` — divisor sums, the von Mangoldt function,
   Chebyshev's bound and Mertens' estimate;
3. `LFunction` — convergence of `L(1, χ) = Σ χ(n)/n` by Abel summation;
4. `ChebyshevSums`, `DirichletConditional` — the key identity, and the reduction of the theorem
   to `L(1, χ) ≠ 0`;
5. `Mobius`, `NonVanishingComplex` — `L(1, χ) ≠ 0` for non-real `χ` (by counting zeros);
6. `RealCharacters`, `NonVanishingReal` — `L(1, χ) ≠ 0` for real `χ` (positivity of
   `Σ_{d ∣ n} χ(d)` and the hyperbola method).

This file puts them together. Everything is proved from the axioms of Lean's logic, with reals
and complex numbers constructed from scratch in Part II.
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Numbers Foundations.Numbers.Arith Lean.Grind
open Foundations.Numbers.C (ofReal)

variable {q : Nat} [NeZero q]

/-- **`L(1, χ) ≠ 0` for real characters.** If `L(1, χ) = 0` for a real `χ ≠ χ₀`, then
`log (M + 1) ≤ T(M²) ≤ 16q + 2` for every `M ≥ 1`, which is absurd. -/
theorem Lone_ne_zero_of_real (χ : Character (ZModUnits q)) (hχ : χ ≠ Character.one)
    (hr : IsRealChar χ) : Lone χ ≠ 0 := by
  intro hL
  obtain ⟨M, hM, hlog⟩ := exists_lnat_gt (16 * (q : R) + 2)
  have h1 := Tsum_sq_le hr hχ hL (M := M) hM
  have h2 := Tsum_sq_ge hr M
  have h3 := lnat_le_lnat hM (show M ≤ M + 1 by omega)
  grind

/-- A character equal to its conjugate is real. -/
theorem isRealChar_of_conj_eq {χ : Character (ZModUnits q)} (h : Character.conj χ = χ) :
    IsRealChar χ := by
  intro n
  have := congrArg (fun ψ : Character (ZModUnits q) => (dchar ψ n).im) h
  simp only [dchar_conj, C.conj_im] at this
  grind

/-- **Dirichlet's non-vanishing theorem.** `L(1, χ) ≠ 0` for every non-principal Dirichlet
character `χ` modulo `q`. -/
theorem Lone_ne_zero (χ : Character (ZModUnits q)) (hχ : χ ≠ Character.one) : Lone χ ≠ 0 := by
  by_cases hc : Character.conj χ = χ
  · exact Lone_ne_zero_of_real χ hχ (isRealChar_of_conj_eq hc)
  · exact Lone_ne_zero_of_conj_ne χ hχ hc

end Foundations.NumberTheory

namespace Foundations.NumberTheory

open Foundations.Numbers.Arith

/-- **Dirichlet's theorem on primes in arithmetic progressions** (1837). If `q ≥ 1` and `a` is
coprime to `q`, then for every `N` there is a prime `p ≥ N` with `p ≡ a (mod q)`: the progression
`a, a + q, a + 2q, …` contains infinitely many primes. -/
theorem dirichlet {q : Nat} (hq : 0 < q) {a : Nat} (ha : Nat.Coprime a q) (N : Nat) :
    ∃ p, N ≤ p ∧ Prime p ∧ p % q = a % q := by
  haveI : NeZero q := ⟨by omega⟩
  exact dirichlet_of_nonvanishing (fun χ hχ => Lone_ne_zero χ hχ) a ha N

/-- **Infinitely many primes in each coprime residue class**, stated as: the primes `≡ a (mod q)`
are not bounded. -/
theorem not_bounded_primes_mod {q : Nat} (hq : 0 < q) {a : Nat} (ha : Nat.Coprime a q) :
    ¬ ∃ B, ∀ p, Prime p → p % q = a % q → p < B := by
  rintro ⟨B, hB⟩
  obtain ⟨p, hp1, hp2, hp3⟩ := dirichlet hq ha B
  have := hB p hp2 hp3
  omega

/-- Example: there are infinitely many primes ending in the digit `7` (`p ≡ 7 mod 10`). -/
example (N : Nat) : ∃ p, N ≤ p ∧ Prime p ∧ p % 10 = 7 :=
  dirichlet (q := 10) (by decide) (a := 7) (by decide) N

end Foundations.NumberTheory
