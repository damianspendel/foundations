import Foundations.Constructible.Reflection

/-!
# `L` is a model of ZF

## The theorem

Gödel's first main theorem about `L` (1938): **the constructible universe is a model of ZF.**
Here `L` is packaged as the two-valued structure `LModel = (L, ∈)` on the subtype
`{z : ZFSet // InL z}`. Every axiom of the theory `ZF` of Part XIII then has truth value `⊤`
(`L_models_ZF`). That theory consists of extensionality, empty set, pairing, union, power set,
infinity, and the separation, collection and `∈`-induction schemes, each with all its universal
closures.

## The proofs, axiom by axiom

* **Extensionality** and **`∈`-induction** hold because `L` is a transitive class
  (`InL.mem`): for constructible sets, "same constructible members" means "same members",
  and `∈`-induction in `ZFSet` restricts to `L`.
* **Empty set, pairing, union**: the required sets are separated out of a stage `L_α`
  that contains them, using `separation_L`.
* **Infinity**: the stage `L_ω` itself is a constructible set containing `∅` and closed under
  `x ↦ x ∪ {x}`.
* **Power set**: the constructible subsets of `x` all lie in one stage `L_β` (bounding), and
  `{z ∈ L_β | z ⊆ x}` is constructible by separation. It is the power set of `x` *in the sense
  of `L`*: it contains only the constructible subsets, which is the whole point.
* **Collection**: choose for each `x ∈ u` a constructible witness, bound all of them in one
  stage `L_β`, and take `v = L_β`.
* **Separation**: the reflection principle (`separation_L`, previous file).

The sets that `L` thinks are power sets are generally smaller than the real ones. This is
possible because "`p` is the power set of `x`" is *not* absolute. In contrast, the formulas used
for the empty set, pairs, unions and successors are absolute for transitive classes, so `L`
computes these operations correctly.

## Consequences

By soundness of the proof calculus for `Prop`-valued structures (`val_eq_top_of_theory`),
every theorem of ZF is true in `L` (`L_val_eq_top_of_ZF`). In particular ZF does not prove `⊥`
(`ZF_consistent_via_L`). That consequence was already available from the forcing models; here it
comes from an inner model, Gödel's route.
-/

namespace Foundations.Constructible

open Foundations.Logic.FO Foundations.Forcing Foundations.Sets Foundations.Sets.ZFSet
open CBA
open BStructure (liftBy allN val_allN_eq_top val_eq_top_of_theory not_proves_of_val)

/-- The constructible universe as a structure `(L, ∈)`: domain the constructible sets
(a subtype of `ZFSet`, in `Type 1`), genuine equality and membership. -/
abbrev LModel : BStructure.{0, 1} LSet Prop := classStr InL

/-- A formula is *true in `L`* if its relativisation to `L` holds for all constructible values
of its variables. -/
def TrueInL (φ : Formula LSet) : Prop := ∀ e : Nat → ZFSet, (∀ n, InL (e n)) → RSat InL e φ

/-- A formula true in `L` has truth value `⊤` in `LModel` under every environment. -/
theorem val_eq_top_of_TrueInL {φ : Formula LSet} (h : TrueInL φ) (e : Nat → LModel.Dom) :
    LModel.val e φ = ⊤ :=
  (val_classStr_eq_top_iff InL φ e).2 (h _ fun n => (e n).2)

/-- Recognising a separated set: if `S` has exactly the members `z ∈ a` with `φ^L(z, e)`, and
`a` and the parameters are constructible, then `S` is constructible. -/
theorem InL_of_sep_iff (φ : Formula LSet) {a S : ZFSet} (ha : InL a) {e : Nat → ZFSet}
    (he : ∀ n, InL (e n)) (hS : ∀ z, z ∈ S ↔ z ∈ a ∧ RSat InL (BEnv.cons z e) φ) : InL S := by
  have : S = sep (fun z => RSat InL (BEnv.cons z e) φ) a := ext fun z => by rw [hS, mem_sep]
  rw [this]; exact separation_L φ ha he

/-! ### Extensionality, empty set, pairing, union -/

/-- Extensionality holds in `L`. -/
theorem L_ext : TrueInL axExt := by
  intro e _
  simp only [axExt, RSat, RSat_iffF, RSat_memF, tv_var, cons_zero, cons_succ]
  intro x hx y hy h
  exact ext fun z => ⟨fun hz => (h z (hx.mem hz)).1 hz, fun hz => (h z (hy.mem hz)).2 hz⟩

/-- The empty-set axiom holds in `L`. -/
theorem L_empty : TrueInL axEmpty := by
  intro e _
  simp only [axEmpty, RSat, RSat_neg, RSat_memF, tv_var, cons_zero, cons_succ]
  exact ⟨∅, InL.empty, fun y _ => not_mem_empty y⟩

/-- Constructible sets are closed under pairs. -/
theorem InL.pair {x y : ZFSet} (hx : InL x) (hy : InL y) : InL ({x, y} : ZFSet) := by
  obtain ⟨α, hα, hS⟩ := exists_stage (S := {x, y}) fun z hz => by
    rcases mem_pair.1 hz with rfl | rfl <;> assumption
  refine InL_of_sep_iff (.disj (.eq (v 0) (v 1)) (.eq (v 0) (v 2))) (InL.stage hα)
    (e := fun n => if n = 0 then x else y) (fun n => ?_) fun z => ?_
  · by_cases h : n = 0
    · simp only [h, ↓reduceIte]; exact hx
    · simp only [h, ↓reduceIte]; exact hy
  · show z ∈ ({x, y} : ZFSet) ↔ z ∈ Lev α ∧ (z = x ∨ z = y)
    exact ⟨fun h => ⟨hS h, mem_pair.1 h⟩, fun h => mem_pair.2 h.2⟩

/-- The pairing axiom holds in `L`. -/
theorem L_pair : TrueInL axPair := by
  intro e _
  simp only [axPair, RSat, RSat_iffF, RSat_memF, tv_var, cons_zero, cons_succ]
  intro x hx y hy
  exact ⟨{x, y}, InL.pair hx hy, fun w _ => mem_pair⟩

/-- Constructible sets are closed under unions. -/
theorem InL.sUnion {x : ZFSet} (hx : InL x) : InL (⋃₀ x) := by
  have hT := Lev_transitive (lrank_ord x).1
  have hxα := mem_Lev_lrank hx
  refine InL_of_sep_iff (.ex (.conj (memF (v 0) (v 2)) (memF (v 1) (v 0))))
    (InL.stage (lrank_ord x)) (e := fun _ => x) (fun _ => hx) fun z => ?_
  show z ∈ ⋃₀ x ↔ z ∈ Lev (lrank x) ∧ ∃ y, InL y ∧ y ∈ x ∧ z ∈ y
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    exact ⟨hT y (hT x hxα hy) hz, y, hx.mem hy, hy, hz⟩
  · rintro ⟨_, y, _, hy, hz⟩
    exact ⟨y, hy, hz⟩

/-- The union axiom holds in `L`. -/
theorem L_union : TrueInL axUnion := by
  intro e _
  simp only [axUnion, RSat, RSat_iffF, RSat_memF, tv_var, cons_zero, cons_succ]
  intro x hx
  refine ⟨⋃₀ x, InL.sUnion hx, fun w _ => ?_⟩
  rw [mem_sUnion]
  exact ⟨fun ⟨y, hy, hw⟩ => ⟨y, hx.mem hy, hy, hw⟩, fun ⟨y, _, hy, hw⟩ => ⟨y, hy, hw⟩⟩

/-! ### Power set and infinity -/

/-- The power-set axiom holds in `L`. The witness is the set of constructible subsets
of `x`, separated from a stage that contains all of them. -/
theorem L_pow : TrueInL axPow := by
  intro e _
  simp only [axPow, RSat, RSat_iffF, RSat_memF, tv_var, cons_zero, cons_succ]
  intro x hx
  obtain ⟨β, hβ, hS⟩ := exists_stage (S := sep InL (powerset x)) fun z hz => (mem_sep.1 hz).2
  let p := sep (fun z => RSat InL (BEnv.cons z fun _ => x)
    (.all (.imp (memF (v 0) (v 1)) (memF (v 0) (v 2))))) (Lev β)
  refine ⟨p, separation_L _ (InL.stage hβ) fun _ => hx, fun z hz => ?_⟩
  show z ∈ p ↔ ∀ w, InL w → w ∈ z → w ∈ x
  constructor
  · intro h
    exact (mem_sep.1 h).2
  · intro h
    refine mem_sep.2 ⟨hS (mem_sep.2 ⟨mem_powerset.2 fun w hw => h w (hz.mem hw) hw, hz⟩), h⟩

/-- The successor `y ∪ {y}` of a member of `L_ω` is again in `L_ω`. -/
theorem succ_mem_Lev_omega {y : ZFSet} (hy : y ∈ Lev ω) : succ y ∈ Lev ω := by
  obtain ⟨m, hm, hym⟩ := mem_Lev.1 hy
  have hmo : IsOrdinal (succ m) := (isOrdinal_omega.mem hm).succ
  have hy' : y ∈ Lev (succ m) := Def_subset_Lev (mem_succ_self m) hym
  have hT := Lev_transitive hmo.1
  refine Def_subset_Lev (succ_mem_omega hm) (Def_intro (fun w hw => ?_)
    (.disj (memF (v 0) (v 1)) (.eq (v 0) (v 1))) (fun _ => y) (fun _ _ => hy') fun w _ => ?_)
  · rcases mem_succ.1 hw with rfl | hw
    · exact hy'
    · exact hT y hy' hw
  · show w ∈ succ y ↔ w ∈ y ∨ w = y
    rw [mem_succ, or_comm]

/-- The axiom of infinity holds in `L`, witnessed by the stage `L_ω`. -/
theorem L_inf : TrueInL axInf := by
  intro e _
  simp only [axInf, RSat, RSat_iffF, RSat_neg, RSat_memF, tv_var, cons_zero, cons_succ]
  refine ⟨Lev ω, InL.stage isOrdinal_omega, ⟨∅, InL.empty, empty_mem_Lev empty_mem_omega,
    fun z _ => not_mem_empty z⟩, fun y hy hyω => ?_⟩
  refine ⟨succ y, InL.of_mem_Lev isOrdinal_omega (succ_mem_Lev_omega hyω),
    succ_mem_Lev_omega hyω, fun w _ => ?_⟩
  rw [mem_succ, or_comm]

/-! ### The schemes: separation, collection, `∈`-induction -/

/-- The separation scheme holds in `L`, for every formula and all constructible
parameters. -/
theorem L_sep (φ : Formula LSet) : TrueInL (axSep φ) := by
  intro e he
  simp only [axSep, RSat, RSat_iffF, RSat_memF, tv_var, cons_zero, cons_succ]
  intro x hx
  refine ⟨sep (fun z => RSat InL (BEnv.cons z e) φ) x, separation_L φ hx he, fun z _ => ?_⟩
  rw [RSat_liftBy _ 2 φ z _ e (fun _ => rfl), mem_sep]

/-- The collection scheme holds in `L`. For each `x ∈ u` with a constructible witness,
choose one; all chosen witnesses lie in one stage `L_β`, which serves as the collecting set. -/
theorem L_coll (φ : Formula LSet) : TrueInL (axColl φ) := by
  classical
  intro e _
  simp only [axColl, RSat, RSat_memF, tv_var, cons_zero, cons_succ]
  intro u hu hyp
  have hyp' : ∀ x ∈ u, ∃ y, InL y ∧ RSat InL (BEnv.cons y (BEnv.cons x e)) φ := fun x hx => by
    obtain ⟨y, hy, h⟩ := hyp x (hu.mem hx) hx
    exact ⟨y, hy, (RSat_lift2By _ 1 φ y x _ e (fun _ => rfl)).1 h⟩
  let f : ZFSet → ZFSet := fun x =>
    if h : ∃ y, InL y ∧ RSat InL (BEnv.cons y (BEnv.cons x e)) φ then Classical.choose h else ∅
  have hf : ∀ x ∈ u, InL (f x) ∧ RSat InL (BEnv.cons (f x) (BEnv.cons x e)) φ := fun x hx => by
    simp only [f, hyp' x hx, ↓reduceDIte]
    exact Classical.choose_spec (hyp' x hx)
  obtain ⟨β, hβ, hS⟩ := exists_stage (S := image f u) fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact (hf x hx).1
  refine ⟨Lev β, InL.stage hβ, fun x _ hx => ⟨f x, (hf x hx).1, hS (mem_image.2 ⟨x, hx, rfl⟩), ?_⟩⟩
  exact (RSat_lift2By _ 2 φ (f x) x _ e (fun _ => rfl)).2 (hf x hx).2

/-- The `∈`-induction scheme holds in `L`, because `L` is transitive and `∈`-induction
holds in `ZFSet`. -/
theorem L_ind (φ : Formula LSet) : TrueInL (axInd φ) := by
  intro e _
  simp only [axInd, RSat, RSat_memF, tv_var, cons_zero, cons_succ]
  intro h
  have hl : ∀ x y, RSat InL (BEnv.cons y (BEnv.cons x e)) (liftBy 1 φ) ↔
      RSat InL (BEnv.cons y e) φ := fun x y => RSat_liftBy _ 1 φ y _ e (fun _ => rfl)
  refine mem_induction (fun x => InL x → RSat InL (BEnv.cons x e) φ) fun x ih hx => ?_
  exact h x hx fun y hy hyx => (hl x y).2 (ih y hyx hy)

/-! ### `L ⊨ ZF` -/

/-- **`L` is a model of ZF.** (Gödel 1938.) Every axiom of the theory `ZF` (extensionality,
empty set, pairing, union, power set, infinity, and all instances of separation, collection and
`∈`-induction together with their universal closures) has truth value `⊤` in the structure
`(L, ∈)`, under every environment of constructible sets. -/
theorem L_models_ZF (e : Nat → LModel.Dom) : ∀ ψ, ZF ψ → LModel.val e ψ = ⊤ := by
  rintro ψ ((rfl | rfl | rfl | rfl | ⟨φ, n, rfl⟩ | ⟨φ, n, rfl⟩) | rfl | rfl | ⟨φ, n, rfl⟩)
  · exact val_eq_top_of_TrueInL L_ext e
  · exact val_eq_top_of_TrueInL L_empty e
  · exact val_eq_top_of_TrueInL L_pair e
  · exact val_eq_top_of_TrueInL L_union e
  · exact val_allN_eq_top (M := LModel) (val_eq_top_of_TrueInL (L_sep φ)) n e
  · exact val_allN_eq_top (M := LModel) (val_eq_top_of_TrueInL (L_ind φ)) n e
  · exact val_eq_top_of_TrueInL L_pow e
  · exact val_eq_top_of_TrueInL L_inf e
  · exact val_allN_eq_top (M := LModel) (val_eq_top_of_TrueInL (L_coll φ)) n e

/-- **Every theorem of ZF is true in `L`.** If `ZF ⊢₁ φ`, then `φ` has value `⊤` in `(L, ∈)`
under every environment, by soundness. -/
theorem L_val_eq_top_of_ZF {φ : Formula LSet} (h : ZF ⊢₁ φ) (e : Nat → LModel.Dom) :
    LModel.val e φ = ⊤ :=
  val_eq_top_of_theory h LModel e (L_models_ZF e)

/-- Theorems of ZF hold relativised to `L`. If `ZF ⊢₁ φ`, then `φ^L` holds for every
assignment of constructible sets to its variables. -/
theorem L_relativises_ZF {φ : Formula LSet} (h : ZF ⊢₁ φ) (e : Nat → ZFSet)
    (he : ∀ n, InL (e n)) : RSat InL e φ :=
  (val_classStr_eq_top_iff InL φ fun n => ⟨e n, he n⟩).1 (L_val_eq_top_of_ZF h _)

/-- **Consistency of ZF via `L`.** ZF does not derive `⊥`, since `⊥` is false in `L`. -/
theorem ZF_consistent_via_L : ¬ (ZF ⊢₁ .bot) :=
  not_proves_of_val LModel (fun _ => ⟨∅, InL.empty⟩) (L_models_ZF _)
    fun h => ((prop_eq_top_iff _).1 h).elim

end Foundations.Constructible
