import Foundations.NumberTheory.PrimesMod4
import Foundations.NumberTheory.Binomial
import Foundations.NumberTheory.PrimorialBound
import Foundations.NumberTheory.Bertrand
import Foundations.NumberTheory.Chebyshev
import Foundations.NumberTheory.Characters
import Foundations.NumberTheory.DualGroup
import Foundations.NumberTheory.DirichletCharacters
import Foundations.NumberTheory.ArithmeticFunctions
import Foundations.NumberTheory.Mertens
import Foundations.NumberTheory.LFunction
import Foundations.NumberTheory.PrimePowers
import Foundations.NumberTheory.ChebyshevSums
import Foundations.NumberTheory.DirichletConditional
import Foundations.NumberTheory.Mobius
import Foundations.NumberTheory.NonVanishingComplex
import Foundations.NumberTheory.RealCharacters
import Foundations.NumberTheory.NonVanishingReal
import Foundations.NumberTheory.Dirichlet
import Foundations.NumberTheory.PNTSums
import Foundations.NumberTheory.PNTChebyshevFunctions
import Foundations.NumberTheory.PNTEquivalence
import Foundations.NumberTheory.PNTMertens
import Foundations.NumberTheory.PNTMobius
import Foundations.NumberTheory.PNTTatuzawaIseki
import Foundations.NumberTheory.PNTSelbergEstimates
import Foundations.NumberTheory.PNTSelberg
import Foundations.NumberTheory.PNTSelbergForms

/-!
# Part XII: Number theory — the distribution of the primes

Euclid showed that the primes never run out. This part asks the next questions: *how* are they
distributed, and how far apart can they be? It builds on the arithmetic of Part II (primes,
Euclid's lemma, unique factorisation, factorials, the real logarithm) and on the quadratic
residues of Part IV.

1. `PrimesMod4` — infinitely many primes `≡ 3 (mod 4)` (Euclid's argument with `4·N! − 1`) and
   infinitely many primes `≡ 1 (mod 4)` (via `(2·N!)² + 1` and the first supplement to quadratic
   reciprocity). These are the simplest cases of **Dirichlet's theorem** (1837) on primes in
   arithmetic progressions, whose general proof needs analysis (L-functions) and is given in
   items 6–19 below.
2. `Binomial` — binomial coefficients via Pascal's rule; the central binomial coefficient
   `C(2n, n)` with `4ⁿ/(2n+1) ≤ C(2n, n) ≤ 4ⁿ`; the `p`-adic valuation and **Legendre's
   formula** `vₚ(n!) = Σ ⌊n/pᵏ⌋`; prime powers dividing `C(2n, n)` are at most `2n`, and primes
   in `(2n/3, n]` do not divide it.
3. `PrimorialBound` — Erdős's bound: the product of the primes up to `n` is at most `4ⁿ`.
4. `Bertrand` — **Bertrand's postulate** (conjectured 1845, proved by Chebyshev 1852): for every
   `n ≥ 1` there is a prime in `(n, 2n]`. We follow Erdős's elementary proof of 1932, which
   simplified Ramanujan's of 1919; small `n` are settled by a chain of twelve primes up to 1259,
   checked by the kernel.
5. `Chebyshev` — **Chebyshev's bounds**: `⌊m/2⌋ · log 2 ≤ π(m) · log m ≤ m · log 1024` for
   `m ≥ 6`, so `π(m)` is of order `m / log m`.

The **prime number theorem**, `π(x) ∼ x / log x` (Hadamard and de la Vallée Poussin, 1896), is
**not proved here**. The `PNT*` files (namespace `Foundations.NumberTheory.PNT`) build the
elementary Erdős–Selberg route up to its last step: the Chebyshev functions θ and ψ, the
equivalence `PNT ⇔ θ(N)/N → 1 ⇔ ψ(N)/N → 1` (`pnt_iff_theta`, `pnt_iff_psi`), Mertens' theorems,
the Möbius function, the Tatuzawa–Iseki identity, and **Selberg's symmetry formula** with explicit
constants (`selberg_symmetry`). The missing piece is the tauberian argument from Selberg's formula
to `ψ(x) ∼ x` (about 30k lines in the Isabelle formalisation of Avigad et al., 2007). Nor is Fermat's Last Theorem: even its
case `n = 4` (Fermat's infinite descent) is not attempted here, while the full theorem was
formalised in Lean in 2026 (Anthropic, September 2026: about 13 million lines, built on Mathlib) — far outside the scope of a
from-scratch development.
-/
