import Foundations.Forcing.BooleanAlgebra
import Foundations.Forcing.RegularOpen
import Foundations.Forcing.BooleanSemantics
import Foundations.Forcing.BooleanSoundness
import Foundations.Forcing.BSet
import Foundations.Forcing.BSetModel
import Foundations.Forcing.BSetZF
import Foundations.Forcing.Cohen
import Foundations.Forcing.CohenReals
import Foundations.Forcing.CheckNames
import Foundations.Forcing.Formulas
import Foundations.Forcing.CardinalPreservation
import Foundations.Forcing.NotCH
import Foundations.Forcing.CollapsePoset
import Foundations.Forcing.CollapseNames
import Foundations.Forcing.CollapseEnum
import Foundations.Forcing.CollapseReals
import Foundations.Forcing.CollapseCH
import Foundations.Forcing.SanityChecks
import Foundations.Forcing.Mixing
import Foundations.Forcing.AxiomOfChoice
import Foundations.Forcing.Independence

/-!
# Part: Forcing and Boolean-valued models: CH is independent of ZFC

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
Boolean algebra `B`. Every axiom of ZF(C) gets value `⊤`, and for the Cohen algebra so does
`¬CH`. Soundness of first-order logic for such models then shows that CH is not provable.
This is the route taken here. It is also the route of the Lean 3 *flypitch* project (Han
and van Doorn, 2019), which completed the independence proof (both halves, for ZFC) with
Mathlib. Here both halves are proved, for ZF and then for ZFC: Cohen's half with the Cohen algebra,
and Gödel's half with a collapse algebra instead of `L` (item 10), with choice verified in every
`V^B` (item 13); the conclusion is `CH_independent_ZFC` (item 14).

## What independence means

That CH is independent of ZFC is a *mathematical* theorem about formal provability. It
holds whatever one believes about sets. Its philosophical weight is contested. For a
formalist the question "is CH true?" has no further content once independence is known.
Gödel himself held the realist view: CH has a definite truth value, and he expected it to
be false. Independence then shows that the ZFC axioms are an incomplete description of the
universe of sets, and new axioms (large cardinals, forcing axioms) must be sought. Others,
such as Hamkins with his "multiverse", read forcing as revealing many equally legitimate
set-theoretic universes, in some of which CH holds and in others not. Boolean-valued models
make the technical core vivid: a statement may be neither true nor false but true *to a
degree*, and unprovability is the existence of a coherent assignment of degrees in which the
axioms are fully true and the statement is not.

## Contents and status

1. **Complete Boolean algebras** (`BooleanAlgebra`, `RegularOpen`). The class
   `CompleteBooleanAlgebra`, residuation (`le_himp_iff`), infinite distributivity
   (`inf_iSup_le`). The regular-open algebra `RO P` of a forcing poset is complete Boolean
   (`RO.instCBA`), and non-degenerate when `P` is inhabited (`RO.top_ne_bot`). Regular opens of
   general topological spaces are not treated.
2. **Boolean-valued semantics and soundness** (`BooleanSemantics`, `BooleanSoundness`). Truth
   values `⟦φ⟧ₑ ∈ B` for the existing first-order syntax, with the substitution and
   congruence lemmas. Soundness of the existing natural deduction calculus
   (`BStructure.soundness`, `not_proves_of_val`), and Tarskian soundness as the case
   `B = Prop` (`entails_of_proves`).
3. **`V^B` is a model of ZF** (`BSet`, `BSetModel`, `BSetZF`). Names, Boolean equality and
   membership. `VB_models_ZF`: every axiom of `ZF` has value `⊤` in `V^B` for every complete
   Boolean algebra `B : Type`. Here `ZF` is extensionality, empty set, pairing, union, power set,
   infinity, and the separation, collection and ∈-induction schemes, the scheme instances
   together with all their universal closures. Choice in `V^B` is item 13.
4. **Check names** (`CheckNames`). The ground model embeds into `V^B` faithfully and two-valuedly:
   `⟦x̌ = y̌⟧ = ⊤ ↔ x = y` and `⟦x̌ ∈ y̌⟧ = ⊤ ↔ x ∈ y` for non-degenerate `B`
   (`eq_zcheck_eq_top_iff`, `mem_zcheck_eq_top_iff`).
5. **The Cohen algebra and ccc** (`Cohen`). `Cohen I` is the regular-open algebra of finite
   partial functions `I × ℕ ⇀ 2`; it is ccc for every `I` (`cohen_ccc`) and non-degenerate
   (`cohen_top_ne_bot`); suprema in ccc algebras are countable suprema
   (`ccc_iSup_countable`). The identification with the regular opens of the space `2^(I×ω)`
   is not formalised.
6. **Cohen reals** (`CohenReals`). The canonical names `ċ_α` are subsets of `ω̌`, pairwise
   distinct, and not in the ground model, each with value `⊤`.
7. **CH as a sentence** (`Formulas`). Formula combinators for `⊆`, Kuratowski pairs,
   functions, injectivity, "`w = ω`" and "`p = 𝒫(w)`", with their truth values computed in
   `V^B`. `CH` is the `LSet` sentence "for `w = ω` and `p = 𝒫(w)`, every `x ⊆ p` injects into
   `w` or receives an injection from `p`".
8. **ccc preserves cardinals** (`CardinalPreservation`). For ccc `B`, if `T` does not inject
   into `U × ℕ`, then in `V^B` no function from `{h t}` (pairwise distinct) into `{k u}` is
   injective (`isFunc_inf_isInj_eq_bot`). The ground cardinals `ω₁`, `ω₂` come from Hartogs'
   theorem, with `ω₁ ↛ ℕ × ℕ` and `ω₂ ↛ ω₁ × ℕ`.
9. **¬CH and unprovability** (`NotCH`). For `B = Cohen(ω₂)`: `⟦¬CH⟧ = ⊤` (`VB_not_CH`). The
   witness is the name of the first `ℵ₁` Cohen reals, which is uncountable and smaller than
   `𝒫(ω)` in `V^B`. Hence
   **`ZF_not_proves_CH : ¬ (ZF ⊢₁ CH)`** and `ZF_notCH_consistent`.

10. **The collapse and CH** (`CollapsePoset`, `CollapseNames`, `CollapseEnum`, `CollapseReals`,
   `CollapseCH`). The other half of independence, by the forcing route instead of Gödel's `L`
   (1938): the Lévy-style collapse of `2^ℵ₀` onto `ℵ₁`. The poset `CCond I` of countable
   partial functions `I ⇀ 𝒫(ℕ)` is **σ-closed** (`CCond.sigma_closed`) and its regular-open
   algebra `Col I` is non-degenerate (`col_top_ne_bot`). σ-closure gives the deciding lemma
   `decide_countable` and hence **no new reals** (`mem_powersetB_le`). The generic function
   hits every ground real (`top_le_iSup_catom`). Graph names with a checkable injectivity
   criterion (`BSet.le_isFunc_inf_isInj`, using Boolean injectivity of Kuratowski pairs
   `BSet.eq_opair_le`) and an external Boolean enumeration of subsets of `ω₁` (`enumV`) build
   the needed injections. For every `ω₁`-like `I`, `⟦CH⟧ = ⊤` in `V^{Col I}`
   (`val_CH_eq_top`); for `I = W₁` this gives
   **`ZF_not_proves_notCH : ¬ (ZF ⊢₁ CH.neg)`**, `ZF_CH_consistent`, and
   **`CH_independent_ZF : ¬ (ZF ⊢₁ CH) ∧ ¬ (ZF ⊢₁ CH.neg)`**.
11. **Sanity checks** (`SanityChecks`). An audit that the CH encoding is not trivially false.
   Kuratowski pairs are injective in the Boolean sense (`Sanity.opair_inj`). Identity and empty
   injections have value `⊤`. In `V^{Cohen(ω₂)}`, `ω̌` injects into the witness `x`, and the matrix
   of `CH` has value `⊤` at `x := 𝒫(ω)` and at `x := ∅`. "`w = ω`" and "`p = 𝒫(w)`" determine
   their objects up to Boolean equality (`Sanity.isOmega_le_eq`, `Sanity.isPow_unique`).
12. **Mixing and fullness** (`Mixing`). Disjoint refinement of a family in `B` along a
   well-ordering of its index type (from Zermelo's theorem in `Sets/Choice`), the mixing lemma
   (`BSet.le_eq_mix`), and the maximum principle `⨆_y ⟦φ(y)⟧ ≤ ⟦φ(z)⟧` for some `z`
   (`VB_maximum_principle`).
13. **The axiom of choice in `V^B`** (`AxiomOfChoice`). `axChoice` is the choice-set form of AC:
   every set of nonempty, pairwise disjoint sets has a set meeting each member in exactly one
   element. `VB_choice`: `⟦axChoice⟧ = ⊤` in every `V^B`. With `ZFC := ZF ∪ {axChoice}`,
   `VB_models_ZFC`, **`ZFC_not_proves_CH`** and `ZFC_notCH_consistent`.
14. **Independence** (`Independence`). The collapse model also satisfies ZFC, so
   **`ZFC_not_proves_notCH`**, `ZFC_CH_consistent`, and
   **`CH_independent_ZFC : ¬ (ZFC ⊢₁ CH) ∧ ¬ (ZFC ⊢₁ CH.neg)`**.

**What is not done.** Gödel's `L` itself. A proof inside the calculus that `axChoice` is
ZF-equivalent to other forms of AC (choice functions, well-ordering); the choice-set form is a
standard formulation, used as stated. Internal names for the function `α ↦ ċ_α` of the Cohen
model, for the generic surjection `ω̌₁ → 𝒫(ω̌)` of the collapse model, and for `ω̌₁` itself:
both proofs work with external families of names and truth values instead. A separate theorem
that the collapse preserves `ω₁`; its content is used inside `enum_total`. A proof inside the
calculus that `CH` is ZF-equivalent to other textbook formulations of CH; the sentence is
simply the standard definition, written out in `LSet`. Both unprovability results are
unconditional (not relative to Con(ZF)) because Lean's metatheory proves that ZF (and ZFC) has models.
-/
