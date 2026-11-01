import Foundations.Sets.PSet
import Foundations.Sets.ZFSet
import Foundations.Sets.Paradoxes
import Foundations.Sets.Omega
import Foundations.Sets.Pairs
import Foundations.Sets.SchroederBernstein
import Foundations.Sets.Ordinals
import Foundations.Sets.Recursion
import Foundations.Sets.OmegaArith
import Foundations.Sets.Cardinality
import Foundations.Sets.Choice
import Foundations.Sets.Transfinite
import Foundations.Sets.CardinalOrder
import Foundations.Sets.Infinite
import Foundations.Sets.CardinalArith
import Foundations.Sets.Hartogs
import Foundations.Sets.Koenig

/-!
# Part I: Sets

Aczel's model of Zermelo–Fraenkel set theory inside Lean's type theory:
pre-sets (`PSet`), their extensional quotient (`ZFSet`) with the ZF axioms as
theorems, the paradoxes of Russell and Cantor, the von Neumann naturals and the
Peano axioms for `ω` (with a bridge to Lean's `Nat`), Kuratowski pairs and
cartesian products, the Schröder–Bernstein theorem, and von Neumann ordinals
with the Burali-Forti paradox; Dedekind's recursion theorem and set-theoretic
arithmetic on `ω` (bridged to `Nat`); cardinality of types (ℕ × ℕ ≃ ℕ,
countable unions, Cantor's diagonal arguments); Zorn's lemma and Zermelo's
well-ordering theorem; successor/limit ordinals and transfinite induction.
Then the arithmetic of the infinite: comparability of cardinals (a total
preorder, with Schröder–Bernstein), the equivalence of "infinite",
"Dedekind-infinite" and "contains a copy of ℕ", Hessenberg's κ · κ = κ with its
consequences for sums and products, Hartogs' theorem, the tower
ℕ < 𝒫(ℕ) < 𝒫(𝒫(ℕ)) < ⋯, and Kőnig's theorem.
-/
