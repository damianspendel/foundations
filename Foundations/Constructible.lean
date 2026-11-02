import Foundations.Constructible.RelSat
import Foundations.Constructible.Definable
import Foundations.Constructible.Hierarchy
import Foundations.Constructible.Reflection
import Foundations.Constructible.LModel
import Foundations.Constructible.Absoluteness

/-!
# Part: The constructible universe `L`

## Gödel 1938

Part XIII proved that the Continuum Hypothesis is independent of ZFC, with *both* halves done by
forcing over Boolean-valued models. Historically the first half came a quarter of a century
before forcing. In 1938 Kurt Gödel showed that CH, and with it the axiom of choice and the
generalised continuum hypothesis, cannot be refuted from ZF. He did it by finding inside the
universe of sets a smaller universe, the **constructible universe** `L`, in which they all hold.

## The definability idea

`L` is built in stages along the ordinals, like the cumulative hierarchy `V_α`, but the power-set
step `V_{α+1} = 𝒫(V_α)` is replaced by the **definable power set**:

  `L₀ = ∅`,  `L_{α+1} = Def(L_α)`,  `L_λ = ⋃_{β<λ} L_β`,  `L = ⋃_α L_α`,

where `Def(X)` consists of the subsets of `X` that are first-order definable over `(X, ∈)` with
parameters from `X`. A set enters `L` only if it can be *described*, by a formula of set theory,
in terms of sets that are already there. Russell and Poincaré's demand that sets be defined
"predicatively" is made precise and then pushed through the whole transfinite.

## Why `L` matters

* **`L` is a model of ZF** (proved here: `L_models_ZF`). So whatever ZF proves is true in `L`, and
  `L` is a second universe of sets sitting inside the first one.
* **`V = L` holds in `L`.** The construction of `L` is *absolute*: computed inside `L`, it gives
  `L` again. So ZF + `V = L` is consistent if ZF is. From `V = L` Gödel derived a definable
  well-ordering of the universe (hence AC) and, through the *condensation lemma*, GCH. This route
  gives Con(ZF) → Con(ZFC + GCH).
* `V = L` settles many questions that ZFC leaves open (Suslin's problem, the Whitehead problem,
  projective-set regularity) and is the prototype of all **inner models** in modern set theory.

## Contrast with forcing

Forcing *adds* sets: the generic extension `M[G]` contains objects `M` cannot describe, and truth
in it is decided by conditions. Gödel's `L` *removes* sets: it keeps only the describable ones.
Forcing shows that statements are unprovable by making them false; `L` shows that statements are
irrefutable by making them true. Absoluteness is the tool on the `L` side, genericity on the
forcing side. In this library the forcing part proved both halves of the independence of CH
(Gödel's half with a σ-closed collapse instead of `L`). This part supplies the inner model itself,
as far as described below.

## Contents and status

**Milestone 1, definable power set: complete.**
1. **Relativised satisfaction** (`RelSat`). `RSat P e φ` is the relativisation `φ^P` of an `LSet`
   formula to a class `P`. It agrees with Tarskian satisfaction in the structure `(X, ∈)` on
   `Small X` (`sat_setStr_iff`) and with the `Prop`-valued Boolean semantics on the class structure
   `classStr P` (`val_classStr_iff`). It has a substitution lemma (`RSat_subst`) and a finite
   support lemma (`RSat_congr`).
2. **`Def(X)`** (`Definable`). `Def X` is defined with `Formula.Sat` on `setStr X`, and `mem_Def`
   characterises it. Closure: `Def X ⊆ 𝒫(X)`, `∅, X ∈ Def X`, pairs and singletons, all finite
   subsets (`finSet_mem_Def`), complements, binary unions and intersections. For transitive `X`,
   `X ⊆ Def X`.

**Milestone 2, the hierarchy: complete.**
3. **`L_α` and `L`** (`Hierarchy`). `Lev x = ⋃_{y∈x} Def(Lev y)` by `∈`-recursion. On ordinals:
   `L_recursion` (`L₀ = ∅`, `L_{α+1} = Def(L_α)`, `L_λ = ⋃_{β<λ} L_β`), `Lev_transitive_ord`
   (`L_α` is transitive), `Lev_mono_ord` (`L_α ⊆ L_β` for `α ≤ β`). The class `InL` is transitive
   (`InL.mem`). Any set of constructible sets lies in one stage (`exists_stage`). The ordinals of
   `L_α` are exactly the members of `α`, and every ordinal is constructible (`ordinals_Lev`).

**Milestone 3, `L ⊨ ZF`: complete, for every axiom of the theory `ZF` of Part XIII.**
4. **Reflection** (`Reflection`). The Tarski–Vaught criterion (`absolute_of_closed`) and the
   reflection principle for the `L`-hierarchy (`reflection_L`): every formula is absolute between
   `L` and arbitrarily large `L_α`. Consequence: `separation_L`.
5. **The model** (`LModel`). `LModel = classStr InL`, the structure `(L, ∈)` on the subtype of
   constructible sets. Extensionality, empty set, pairing, union, power set, infinity, and the
   schemes of separation, collection and `∈`-induction are true in `L` (`L_ext`, `L_empty`,
   `L_pair`, `L_union`, `L_pow`, `L_inf`, `L_sep`, `L_coll`, `L_ind`). Hence
   **`L_models_ZF : ∀ ψ, ZF ψ → LModel.val e ψ = ⊤`**, and by soundness `L_val_eq_top_of_ZF`,
   `L_relativises_ZF` and `ZF_consistent_via_L : ¬ (ZF ⊢₁ ⊥)`.
6. **Absoluteness** (`Absoluteness`). Bounded (`Δ₀`) formulas are absolute for transitive classes
   (`delta0_absolute`), and `L` recognises the ordinals correctly (`L_ordinal_iff`).

**Milestone 4 (stretch goals): not reached.** None of the following is proved:
* `V = L` in `L`. This needs a formula of `LSet` expressing "`x ∈ L_α`": a coding of formulas as
  sets, a set-theoretic definition of the satisfaction relation of `(X, ∈)` by recursion on codes,
  and a proof that the function `α ↦ L_α` so defined is absolute for `L`. None of this internal
  coding exists here.
* A definable well-ordering of `L`, and AC in `L`. These need the same internal satisfaction
  relation.
* The condensation lemma, and GCH (or CH) in `L`.

So Gödel's half of the independence of CH is **not** obtained via `L` here. The library's proof
of that half remains the forcing proof of Part XIII (`ZFC_not_proves_notCH`, collapse algebra).
The relativisation is an external one: `RSat InL` is a statement of the metatheory about the
class `InL`, not an `LSet` formula.
-/
