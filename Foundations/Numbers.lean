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
-/
