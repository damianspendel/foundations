import Foundations.Constructible.Definable
import Foundations.Sets.Transfinite

/-!
# The constructible hierarchy `L_α` and the class `L`

## Gödel's hierarchy

Gödel (1938) defined the constructible sets in stages:

  `L₀ = ∅`,  `L_{α+1} = Def(L_α)`,  `L_λ = ⋃_{β<λ} L_β` for limit `λ`,

and `L = ⋃_α L_α`. Compare the cumulative hierarchy `V_{α+1} = 𝒫(V_α)`: the only difference is
that the full power set is replaced by the definable one. That single change makes `L` a very
"thin" and very well-understood universe. Every constructible set has a description, a formula
together with finitely many earlier parameters, and this is what later yields a definable
well-ordering of `L` and the generalised continuum hypothesis in `L`. (Those consequences are
**not** formalised here; see the aggregator `Constructible` for the status.)

## How the recursion is set up

Ordinals in this library are von Neumann ordinals inside `ZFSet`, and there is no packaged
transfinite recursion for set-valued functions. We use the well-foundedness of `∈` on `ZFSet`
(from `∈`-induction) and Lean's `WellFounded.fix` to define, for *every* set `x`,

  `Lev x = ⋃_{y ∈ x} Def(Lev y)`.

This single uniform clause gives Gödel's three clauses on ordinals (`Lev_zero`, `Lev_succ`,
`Lev_limit`, gathered in `L_recursion`). It also makes monotonicity immediate: `x ⊆ y` gives
`Lev x ⊆ Lev y` (`Lev_mono`). For transitive `x` the stage `Lev x` is transitive
(`Lev_transitive`).

## The class `L`

`InL z` means `z ∈ L_α` for some ordinal `α`. The class is transitive (`InL.mem`). Any set of
constructible sets lies inside a single stage `L_α` (`exists_stage`); this uses replacement in
the ambient `ZFSet` universe. Every ordinal is constructible, and the ordinals of `L_α` are
exactly the members of `α` (`ordinals_Lev`).
-/

namespace Foundations.Constructible

open Foundations.Logic.FO Foundations.Forcing Foundations.Sets Foundations.Sets.ZFSet

/-- Membership is well-founded on `ZFSet`. This is the axiom of foundation, in the form
needed for recursion along `∈`. -/
theorem mem_wf : WellFounded (fun x y : ZFSet => x ∈ y) :=
  ⟨mem_induction (fun x => Acc _ x) fun x ih => Acc.intro x ih⟩

/-- **The constructible hierarchy.** `Lev x = ⋃_{y ∈ x} Def(Lev y)`, by `∈`-recursion. On
ordinals this is Gödel's `L_α`. -/
noncomputable def Lev : ZFSet → ZFSet :=
  mem_wf.fix fun x rec => ⋃₀ ofFamily fun i : x.Idx => Def (rec (x.elt i) (elt_mem x i))

/-- The defining equation of `Lev`. -/
theorem Lev_eq (x : ZFSet) : Lev x = ⋃₀ ofFamily fun i : x.Idx => Def (Lev (x.elt i)) :=
  mem_wf.fix_eq _ x

/-- Members of `L_x`. `z ∈ Lev x` iff `z` is definable over `Lev y` for some `y ∈ x`. -/
theorem mem_Lev {x z : ZFSet} : z ∈ Lev x ↔ ∃ y ∈ x, z ∈ Def (Lev y) := by
  rw [Lev_eq, mem_sUnion]
  constructor
  · rintro ⟨w, hw, hz⟩
    obtain ⟨i, rfl⟩ := mem_ofFamily.1 hw
    exact ⟨x.elt i, elt_mem x i, hz⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨i, rfl⟩ := mem_iff_elt.1 hy
    exact ⟨_, mem_ofFamily.2 ⟨i, rfl⟩, hz⟩

/-- For `y ∈ x`, every set definable over `Lev y` is in `Lev x`. -/
theorem Def_subset_Lev {x y : ZFSet} (hy : y ∈ x) : Def (Lev y) ⊆ Lev x :=
  fun _ hz => mem_Lev.2 ⟨y, hy, hz⟩

/-- Monotonicity. If `x ⊆ y` then `L_x ⊆ L_y`. In particular `L_α ⊆ L_β` for ordinals
`α ≤ β`. -/
theorem Lev_mono {x y : ZFSet} (h : x ⊆ y) : Lev x ⊆ Lev y := fun _ hz => by
  obtain ⟨w, hw, hz⟩ := mem_Lev.1 hz
  exact mem_Lev.2 ⟨w, h hw, hz⟩

/-- **Monotonicity of `L_α`.** `L_α ⊆ L_β` for ordinals `α ≤ β`, with `≤` the ordinal order
(`∈` or `=`). -/
theorem Lev_mono_ord {α β : ZFSet} (hβ : IsOrdinal β) (h : α ∈ β ∨ α = β) : Lev α ⊆ Lev β := by
  rcases h with h | rfl
  · exact Lev_mono (hβ.1 α h)
  · exact subset_refl _

/-- `L₀ = ∅`. -/
theorem Lev_zero : Lev ∅ = ∅ :=
  eq_empty_of_forall_not_mem fun _ hz => by
    obtain ⟨y, hy, _⟩ := mem_Lev.1 hz
    exact not_mem_empty y hy

/-- Stages over transitive sets are transitive. If `x` is transitive (for instance an
ordinal), so is `L_x`. -/
theorem Lev_transitive {x : ZFSet} (hx : IsTransitive x) : IsTransitive (Lev x) := by
  intro z hz w hw
  obtain ⟨y, hy, hzy⟩ := mem_Lev.1 hz
  exact Lev_mono (hx y hy) (subset_of_mem_Def hzy hw)

/-- **Transitivity of `L_α`.** `L_α` is a transitive set for every ordinal `α`. -/
theorem Lev_transitive_ord {α : ZFSet} (hα : IsOrdinal α) : IsTransitive (Lev α) :=
  Lev_transitive hα.1

/-- Earlier stages are members of later ones: `y ∈ x` gives `L_y ∈ L_x`. -/
theorem Lev_mem_Lev {x y : ZFSet} (h : y ∈ x) : Lev y ∈ Lev x :=
  Def_subset_Lev h (self_mem_Def _)

/-- Successor stages. For transitive `α` (in particular every ordinal),
`L_{α+1} = Def(L_α)`. -/
theorem Lev_succ {α : ZFSet} (hα : IsTransitive α) : Lev (succ α) = Def (Lev α) := by
  apply subset_antisymm
  · intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_Lev.1 hz
    rcases mem_succ.1 hy with rfl | hy
    · exact hzy
    · exact subset_Def_of_transitive (Lev_transitive hα) (Def_subset_Lev hy hzy)
  · exact Def_subset_Lev (mem_succ_self α)

/-- Limit stages. For a limit ordinal `λ`, `L_λ = ⋃_{β<λ} L_β`. -/
theorem Lev_limit {l z : ZFSet} (hl : IsLimitOrdinal l) : z ∈ Lev l ↔ ∃ β ∈ l, z ∈ Lev β := by
  constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := mem_Lev.1 hz
    rw [← hl.2.2] at hy
    obtain ⟨δ, hδ, hyδ⟩ := mem_sUnion.1 hy
    exact ⟨δ, hδ, Def_subset_Lev hyδ hzy⟩
  · rintro ⟨β, hβ, hz⟩
    exact Lev_mono (hl.1.1 β hβ) hz

/-- **Gödel's recursion for `L`.** On ordinals the hierarchy satisfies
`L₀ = ∅`, `L_{α+1} = Def(L_α)` and `L_λ = ⋃_{β<λ} L_β` for limits `λ`. -/
theorem L_recursion :
    Lev ∅ = ∅ ∧ (∀ α, IsOrdinal α → Lev (succ α) = Def (Lev α)) ∧
      (∀ l, IsLimitOrdinal l → ∀ z, z ∈ Lev l ↔ ∃ β ∈ l, z ∈ Lev β) :=
  ⟨Lev_zero, fun _ hα => Lev_succ hα.1, fun _ hl _ => Lev_limit hl⟩

/-- The empty set belongs to every stage `L_x` with `x` non-empty. -/
theorem empty_mem_Lev {x y : ZFSet} (hy : y ∈ x) : (∅ : ZFSet) ∈ Lev x :=
  Def_subset_Lev hy (empty_mem_Def _)

/-! ### The class `L` -/

/-- **The constructible universe `L`.** As a class: `InL z` iff `z ∈ L_α` for some ordinal
`α`. -/
def InL (z : ZFSet) : Prop := ∃ α, IsOrdinal α ∧ z ∈ Lev α

/-- Members of stages are constructible. -/
theorem InL.of_mem_Lev {α z : ZFSet} (hα : IsOrdinal α) (h : z ∈ Lev α) : InL z := ⟨α, hα, h⟩

/-- `L` is a transitive class. Members of constructible sets are constructible. -/
theorem InL.mem {y z : ZFSet} (hy : InL y) (hz : z ∈ y) : InL z := by
  obtain ⟨α, hα, h⟩ := hy
  exact ⟨α, hα, Lev_transitive hα.1 y h hz⟩

/-- Sets definable over a stage `L_α` are constructible (they lie in `L_{α+1}`). -/
theorem InL.of_mem_Def {α z : ZFSet} (hα : IsOrdinal α) (h : z ∈ Def (Lev α)) : InL z :=
  ⟨succ α, hα.succ, Def_subset_Lev (mem_succ_self α) h⟩

/-- Each stage is constructible. `L_α ∈ L_{α+1}`. -/
theorem InL.stage {α : ZFSet} (hα : IsOrdinal α) : InL (Lev α) :=
  InL.of_mem_Def hα (self_mem_Def _)

/-- The empty set is constructible. -/
theorem InL.empty : InL ∅ := InL.of_mem_Def isOrdinal_empty (empty_mem_Def _)

/-- A chosen stage containing a constructible set (`∅` for non-constructible sets). -/
noncomputable def lrank (z : ZFSet) : ZFSet :=
  open Classical in if h : InL z then Classical.choose h else ∅

/-- The chosen stage is an ordinal. -/
theorem lrank_ord (z : ZFSet) : IsOrdinal (lrank z) := by
  unfold lrank
  split
  · exact (Classical.choose_spec ‹InL z›).1
  · exact isOrdinal_empty

/-- A constructible set lies in its chosen stage. -/
theorem mem_Lev_lrank {z : ZFSet} (h : InL z) : z ∈ Lev (lrank z) := by
  unfold lrank
  simp only [h, ↓reduceDIte]
  exact (Classical.choose_spec h).2

/-- The supremum `α ∪ β` of two ordinals is an ordinal containing both. -/
theorem ord_max {α β : ZFSet} (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    IsOrdinal (α ∪ β) ∧ α ⊆ α ∪ β ∧ β ⊆ α ∪ β := by
  refine ⟨isOrdinal_sUnion fun x hx => ?_, fun z hz => mem_union.2 (Or.inl hz),
    fun z hz => mem_union.2 (Or.inr hz)⟩
  rcases mem_pair.1 hx with rfl | rfl
  · exact hα
  · exact hβ

/-- **Bounding.** Every set of constructible sets is contained in a single stage `L_α`. (The
ordinal is the supremum of chosen stages, a set by replacement in `ZFSet`.) -/
theorem exists_stage {S : ZFSet} (hS : ∀ y ∈ S, InL y) : ∃ α, IsOrdinal α ∧ S ⊆ Lev α := by
  refine ⟨⋃₀ image lrank S, isOrdinal_sUnion fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨z, _, rfl⟩ := mem_image.1 hx
    exact lrank_ord z
  · exact Lev_mono (subset_sUnion_of_mem (mem_image.2 ⟨y, hy, rfl⟩)) (mem_Lev_lrank (hS y hy))

/-- Bounding finitely many parameters. If `e n` is constructible for every `n < k`, all
these values lie in one stage `L_α`. -/
theorem exists_stage_env {e : Nat → ZFSet} {k : Nat} (he : ∀ n < k, InL (e n)) :
    ∃ α, IsOrdinal α ∧ ∀ n < k, e n ∈ Lev α := by
  obtain ⟨α, hα, hS⟩ := exists_stage (S := ofFamily fun i : Fin k => e i) fun y hy => by
    obtain ⟨i, rfl⟩ := mem_ofFamily.1 hy
    exact he i i.2
  exact ⟨α, hα, fun n hn => hS (mem_ofFamily.2 ⟨⟨n, hn⟩, rfl⟩)⟩

/-! ### Ordinals in `L` -/

/-- The formula "`v₀` is a transitive set": `∀y (y ∈ v₀ → ∀w (w ∈ y → w ∈ v₀))`. -/
def transF : Formula LSet :=
  .all (.imp (memF (v 0) (v 1)) (.all (.imp (memF (v 0) (v 1)) (memF (v 0) (v 2)))))

/-- The formula "`v₀` is an ordinal": a transitive set of transitive sets. -/
def ordF : Formula LSet := .conj transF (.all (.imp (memF (v 0) (v 1)) transF))

/-- In a transitive set `X`, `transF` expresses transitivity (it is absolute). -/
theorem RSat_transF {X x : ZFSet} (hX : IsTransitive X) (hx : x ∈ X) (e : Nat → ZFSet) :
    RSat (· ∈ X) (BEnv.cons x e) transF ↔ IsTransitive x := by
  simp only [transF, RSat, RSat_memF, tv_var, cons_zero, cons_succ]
  constructor
  · intro h y hy w hw
    exact h y (hX x hx hy) hy w (hX y (hX x hx hy) hw) hw
  · intro h y _ hy w _ hw
    exact h y hy hw

/-- In a transitive set `X`, `ordF` expresses being an ordinal (it is absolute). -/
theorem RSat_ordF {X x : ZFSet} (hX : IsTransitive X) (hx : x ∈ X) (e : Nat → ZFSet) :
    RSat (· ∈ X) (BEnv.cons x e) ordF ↔ IsOrdinal x := by
  show RSat _ _ transF ∧ (∀ y, y ∈ X → y ∈ x → RSat _ (BEnv.cons y (BEnv.cons x e)) transF) ↔ _
  rw [RSat_transF hX hx]
  refine and_congr Iff.rfl ⟨fun h y hy => ?_, fun h y hyX hy => ?_⟩
  · exact (RSat_transF hX (hX x hx hy) _).1 (h y (hX x hx hy) hy)
  · exact (RSat_transF hX hyX _).2 (h y hy)

/-- The ordinals of `L_α` are below `α`. Every ordinal in `L_α` is a member of `α`. -/
theorem ord_mem_of_mem_Lev : ∀ α, IsOrdinal α → ∀ z ∈ Lev α, IsOrdinal z → z ∈ α := by
  refine transfinite_induction _ fun α hα ih z hz hzo => ?_
  obtain ⟨β, hβ, hzβ⟩ := mem_Lev.1 hz
  have hsub : z ⊆ β := fun w hw =>
    ih β hβ w (subset_of_mem_Def hzβ hw) (hzo.mem hw)
  rcases ordinal_trichotomy hzo (hα.mem hβ) with h | rfl | h
  · exact hα.1 β hβ h
  · exact hβ
  · exact absurd (hsub h) (mem_irrefl β)

/-- Every ordinal is definable over its own stage: `α ∈ Def(L_α)`, defined as the set of
ordinals of `L_α`. Hence `α ∈ L_{α+1}`. -/
theorem ord_mem_Def_Lev : ∀ α, IsOrdinal α → α ∈ Def (Lev α) := by
  refine transfinite_induction _ fun α hα ih => ?_
  have hsub : α ⊆ Lev α := fun β hβ => Def_subset_Lev hβ (ih β hβ)
  have hb : bnd ordF = 1 := by simp [bnd, ordF, transF, memF, memArgs, tbnd, finMax]
  refine Def_intro hsub ordF (fun _ => ∅) (fun n hn => absurd hn (by omega)) fun y hy => ?_
  rw [RSat_ordF (Lev_transitive hα.1) hy]
  exact ⟨fun h => hα.mem h, fun h => ord_mem_of_mem_Lev α hα y hy h⟩

/-- **Ordinals in `L`.** The ordinals of `L_α` are exactly the members of `α`, and every
ordinal is constructible. -/
theorem ordinals_Lev {α : ZFSet} (hα : IsOrdinal α) :
    (∀ z, (z ∈ Lev α ∧ IsOrdinal z) ↔ z ∈ α) ∧ InL α := by
  refine ⟨fun z => ⟨fun h => ord_mem_of_mem_Lev α hα z h.1 h.2, fun h => ⟨?_, hα.mem h⟩⟩,
    InL.of_mem_Def hα (ord_mem_Def_Lev α hα)⟩
  exact Def_subset_Lev h (ord_mem_Def_Lev z (hα.mem h))

end Foundations.Constructible
