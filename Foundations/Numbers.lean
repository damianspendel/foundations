import Foundations.Numbers.Peano
import Foundations.Numbers.Int
import Foundations.Numbers.Arithmetic
import Foundations.Numbers.Rat
import Foundations.Numbers.Cauchy
import Foundations.Numbers.Real
import Foundations.Numbers.RealOrder
import Foundations.Numbers.Bisection
import Foundations.Numbers.Completeness
import Foundations.Numbers.Uncountable
import Foundations.Numbers.Embeddings
import Foundations.Numbers.OrderedField
import Foundations.Numbers.CompleteOrderedField
import Foundations.Numbers.Dedekind
import Foundations.Numbers.DedekindField
import Foundations.Numbers.Analysis
import Foundations.Numbers.Continuity
import Foundations.Numbers.Complex
import Foundations.Numbers.Derivative
import Foundations.Numbers.Series
import Foundations.Numbers.Exp
import Foundations.Numbers.Log
import Foundations.Numbers.Integral
import Foundations.Numbers.FTC
import Foundations.Numbers.Trig
import Foundations.Numbers.TrigIdentities
import Foundations.Numbers.ComplexExp
import Foundations.Numbers.PiIrrational
import Foundations.Numbers.ComplexModulus
import Foundations.Numbers.Compactness2D
import Foundations.Numbers.FTA
import Foundations.Numbers.InverseTrig

/-!
# Part II: Number systems

The number systems built from scratch, each from the previous by a quotient construction:

1. `Peano` — the natural numbers `N` as an inductive type; arithmetic, order, well-ordering;
   bridge to Lean's `Nat`.
2. `Int` — the integers `Z` as classes of pairs of naturals (formal differences); commutative
   ring, linear order; bridge to Lean's `Int`.
3. `Arithmetic` — Euclid's algorithm, Bézout, Euclid's lemma, infinitude of primes, the
   fundamental theorem of arithmetic.
4. `Rat` — the rationals `Q` as classes of fractions; ordered field, Archimedean, density,
   irrationality of √2.
5. `Cauchy`, `Real`, `RealOrder` — the reals `R` as classes of Cauchy sequences of rationals;
   ordered field, Archimedean.
6. `Bisection`, `Completeness` — the least upper bound property; existence of √2.
7. `Uncountable` — Cantor: the reals are uncountable; the rationals are not complete.
8. `Embeddings` — the chain ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ of injective ring homomorphisms.
9. `OrderedField`, `CompleteOrderedField` — ordered fields in general; ℚ inside every ordered
   field; categoricity: any two complete ordered fields are uniquely isomorphic.
10. `Dedekind`, `DedekindField` — a second construction of the reals by Dedekind cuts; it is a
    complete ordered field, hence isomorphic to the Cauchy reals.
11. `Analysis`, `Continuity` — limits, monotone convergence, Bolzano–Weierstrass, Cauchy
    completeness, continuity, intermediate and extreme value theorems, `n`-th roots.
12. `Complex` — ℂ as pairs of reals; a field with `i² = −1`; conjugation; ℂ is not orderable.
13. `Derivative` — the derivative; sum, product and chain rules; polynomials; Fermat, Rolle,
    the mean value theorem and its consequences (monotonicity, constancy).
14. `Series` — infinite series; geometric series, comparison test, absolute convergence, ratio test.
15. `Exp` — the exponential function as a power series; `exp' = exp`, `exp (x + y) = exp x · exp y`,
    positivity and monotonicity; Euler's number `e` is irrational.
16. `Log` — the natural logarithm as the inverse of `exp`; `log (x y) = log x + log y`;
    `log' = 1/y`.
17. `Integral` — the Riemann integral; linearity, monotonicity, additivity; Heine–Cantor;
    continuous functions are integrable.
18. `FTC` — the fundamental theorem of calculus, both parts; `∫ tⁿ` and `∫ exp`.
19. `Trig` — power series with bounded coefficients and termwise differentiation; sine and
    cosine; `sin² + cos² = 1`; `π` as twice the first positive zero of cosine.
20. `TrigIdentities` — addition formulas; periodicity with period `2π`; `sin π = 0`, `cos π = −1`;
    all zeros of sine and cosine.
21. `ComplexExp` — the complex exponential as a power series; `exp (z + w) = exp z · exp w` via the
    Cauchy product; Euler's formula `exp (iθ) = cos θ + i sin θ`; Euler's identity `e^{iπ} + 1 = 0`.
22. `PiIrrational` — π is irrational (Niven's proof, via the fundamental theorem of calculus).
23. `ComplexModulus` — square roots; the modulus `|z|` (multiplicative, triangle inequality);
    parity of sine and cosine; arguments; de Moivre; polar form and `k`-th roots in ℂ.
24. `Compactness2D` — a continuous function attains its minimum on a closed square
    (Bolzano–Weierstrass on pairs).
25. `FTA` — the fundamental theorem of algebra: every non-constant complex polynomial has a root
    (d'Alembert–Argand minimum-modulus proof).
26. `InverseTrig` — cosine is strictly decreasing on `[0, π]`; the arc cosine.
-/
