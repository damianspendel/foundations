import Foundations.Forcing.BooleanAlgebra
import Foundations.Forcing.RegularOpen
import Foundations.Forcing.BooleanSemantics
import Foundations.Forcing.BooleanSoundness
import Foundations.Forcing.BSet
import Foundations.Forcing.BSetModel
import Foundations.Forcing.BSetZF
import Foundations.Forcing.Cohen
import Foundations.Forcing.CohenReals

/-!
# Part: Forcing and Boolean-valued models (toward the independence of CH)

## The problem

Cantor's **Continuum Hypothesis** (1878) says that every infinite set of real numbers is
either countable or in bijection with ℝ; equivalently `2^ℵ₀ = ℵ₁`. Hilbert put it first on his
list of problems in 1900. The answer came in two halves:

* **Gödel (1938)**: CH cannot be *refuted* in ZF set theory with choice (ZFC). Inside any
  model of ZF Gödel built the **constructible universe** `L` of sets that are definable
  from earlier ones, stage by stage along the ordinals. In `L` both the axiom of choice and
  CH hold. So if ZF is consistent, so is ZFC + CH.
* **Cohen (1963)**: CH cannot be *proved* in ZFC either. His method, **forcing**, extends a
  countable model `M` by a "generic" object `G` that `M` cannot describe. The truth of a
  statement in `M[G]` is decided by finite pieces of information about `G` (the
  conditions). Adding `ℵ₂` generic reals makes `2^ℵ₀ ≥ ℵ₂`.

**Scott, Solovay and Vopěnka** (1965–67) recast forcing as **Boolean-valued model theory**:
instead of building `M[G]`, assign to each sentence `φ` a truth value `⟦φ⟧` in a complete
Boolean algebra `B`. Every axiom of ZFC gets value `⊤`, and for the Cohen algebra so does
`¬CH`. Soundness of first-order logic for such models then shows ZFC ⊬ CH. This is the route
taken here (route A of the plan), and it is also the route of the Lean 3 *flypitch* project
(Han and van Doorn, 2019), which completed the independence proof with Mathlib.

## What independence means

That CH is independent of ZFC is a *mathematical* theorem about formal provability. It
holds whatever one believes about sets. Its philosophical weight is contested. For a
formalist the question "is CH true?" has no further content once independence is known.
Gödel himself held the realist view: CH has a definite truth value, and he expected it to
be false. Independence then shows that the ZFC axioms are an incomplete description of the
universe of sets, and new axioms (large cardinals, forcing axioms) must be sought. Others,
such as Hamkins with his "multiverse", read forcing as revealing many equally legitimate set-theoretic
universes, in some of which CH holds and in others not. Boolean-valued models make the
technical core vivid: a statement may be neither true nor false but true *to a degree*, and
independence is the existence of a coherent assignment of degrees in which the axioms are
fully true and CH is not.

## Contents and status

The planned milestones, and what is proved:

1. **Complete Boolean algebras: done.** `BooleanAlgebra` gives the class
   `CompleteBooleanAlgebra`, implication and residuation (`le_himp_iff`) and infinite
   distributivity (`inf_iSup_le`). `RegularOpen` gives the regular-open algebra
   `RO P` of a forcing poset, a complete Boolean algebra (`RO.instCBA`). The regular-open
   algebra of a general topological space (and `Foundations/Topology`) is *not* used.
2. **Boolean-valued semantics and soundness: done.** `BooleanSemantics` defines `⟦φ⟧ₑ ∈ B` for
   the existing first-order syntax, with the substitution lemma and the congruence lemma
   (`envEq_inf_val_le`). `BooleanSoundness` proves soundness of the existing natural
   deduction calculus for all Boolean-valued structures (`BStructure.soundness`, and
   `val_eq_top_of_proves`: theorems have value `⊤`). It also recovers Tarskian soundness as
   the case `B = Prop` (`entails_of_proves`).
3. **The Boolean-valued universe: done, for all of ZF.** `BSet` defines `B`-valued
   pre-sets, Boolean equality (reflexive, symmetric, transitive) and membership. `BSetModel`
   proves that extensionality, empty set, pairing, union, the separation scheme and the
   ∈-induction scheme have value `⊤`. `BSetZF` adds power set, infinity and the collection
   scheme: `VB_models_ZF` shows that every axiom of ZF (Collection form) is `⊤` in `V^B` for
   every complete Boolean algebra `B : Type`, so every theorem of ZF is too
   (`VB_val_eq_top_of_ZF`). The **axiom of choice in `V^B` is not proved.**
4. **The Cohen algebra and ccc: done, in poset form.** `Cohen` defines `Cohen I` as the
   regular-open algebra of finite partial functions `I × ℕ ⇀ 2`, for an arbitrary index
   type `I`, and proves the countable chain condition (`cohen_ccc`) by an induction on the
   size of conditions. It also proves that suprema in ccc algebras are countable suprema
   (`ccc_iSup_countable`). The isomorphism with the regular open sets of the product space
   `2^(I×ω)` is not formalised, and no specific `I` of size `ℵ₂` is singled out.
5. **¬CH and independence: only first steps.** `CohenReals` defines the canonical names `ċ_α`
   of the Cohen reals and proves, by density arguments, that each is a subset of `ω̌`
   (`creal_subset_omega`), that they are pairwise distinct (`creal_ne`), and that none of
   them is a ground-model real (`creal_ne_ground`). All three hold with Boolean value `⊤`.

**What remains** for the independence of CH: choice in `V^B`; ordinals, cardinals and
functions inside `V^B` (check names of ordinals, `ℵ̌₁`, `ℵ̌₂`); the theorem that ccc forcing
preserves cardinals (whose algebraic core is `ccc_iSup_countable`); the internal statement
that `α ↦ ċ_α` is an injection of `ℵ̌₂` into `𝒫(ω̌)`, giving `⟦¬CH⟧ = ⊤` for `|I| = ℵ₂`; a
formula `CH` of the language `LSet`; and, for the other half, a Boolean-valued (or
constructible) model in which `⟦CH⟧ = ⊤`. With these, `BStructure.not_proves_of_val` applied
to a non-degenerate algebra (`⊤ ≠ ⊥`) would yield `¬ (ZFC ⊢₁ CH)` and `¬ (ZFC ⊢₁ ¬CH)`.
-/
