import Foundations.Combinatorics.Pigeonhole
import Foundations.Combinatorics.Ramsey
import Foundations.Combinatorics.Konig
import Foundations.Combinatorics.Hall
import Foundations.Combinatorics.RamseyCompactness

/-!
# Part IX: Combinatorics

Finite and infinite combinatorics, built on Lean's core natural numbers and lists:
the pigeonhole principle (finite and infinite) and the Erdős–Szekeres theorem on
monotone subsequences; Ramsey's theorem — the finite version with the Erdős–Szekeres
recursion `R(s,t) ≤ R(s−1,t) + R(s,t−1)`, the exact value `R(3,3) = 6`, and the infinite
version for colourings of pairs of natural numbers; Kőnig's lemma on infinite
finitely branching trees, the combinatorial form of compactness; Hall's marriage
theorem (both directions); and finally the finite Ramsey theorem re-derived from the
infinite one by Kőnig's lemma — compactness at work, as in Part III.
-/
