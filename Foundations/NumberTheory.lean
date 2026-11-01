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
import Foundations.NumberTheory.PNTRemainder
import Foundations.NumberTheory.PNTIterated
import Foundations.NumberTheory.PNTTauberianA
import Foundations.NumberTheory.PNTTauberianB
import Foundations.NumberTheory.PNTTauberianC
import Foundations.NumberTheory.PNTTheorem

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
   the files `Characters` … `Dirichlet` (theorem `dirichlet`).
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

The **prime number theorem**, `π(x) ∼ x / log x`, is **proved** here
(`prime_number_theorem` in `PNTTheorem`, namespace `Foundations.NumberTheory.PNT`), by the
elementary method of Selberg and Erdős (1948/49) rather than the complex analysis of Hadamard and
de la Vallée Poussin (1896). The `PNT*` files run as follows:
* the Chebyshev functions θ and ψ, and the equivalence `PNT ⇔ θ(N)/N → 1 ⇔ ψ(N)/N → 1`
  (`pnt_iff_theta`, `pnt_iff_psi`);
* Mertens' theorems, the Möbius function, the Tatuzawa–Iseki identity, Euler's constant and
  Stirling's formula;
* **Selberg's symmetry formula** with explicit constants (`selberg_symmetry`,
  `selberg_symmetry_conv`);
* the tauberian argument: Selberg's formula for the remainder `R(N) = ψ(N) − N` and its
  iteration `|R(N)| log² N ≤ Σ a(k) |R(N/k)| + O(N log N)` (`PNTRemainder`, `PNTIterated`);
  good intervals where `ψ(n)/n − 1` is small, because it changes sign with small steps
  (`PNTTauberianA`); the averaging machinery (`PNTTauberianB`); and the improvement lemma that
  lowers any eventual bound on `|ψ(n)/n − 1|` by a fixed amount (`PNTTauberianC`);
* `PNTTheorem`: iterating that lemma gives `ψ(N)/N → 1`, hence `θ(N)/N → 1` and
  `π(N) log N / N → 1`.

Fermat's Last Theorem is out of scope: even its
case `n = 4` (Fermat's infinite descent) is not attempted here, while the full theorem was
formalised in Lean in 2026 (Anthropic, September 2026: about 13 million lines, built on Mathlib) — far outside the scope of a
from-scratch development.
-/
