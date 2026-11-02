import Foundations.Forcing.CollapsePoset
import Foundations.Forcing.CollapseNames

/-!
# Boolean-valued enumeration of subsets of `ω₁`

The last step of the proof of CH in the collapse model is a fact of ZF: an uncountable subset
`A` of `ω₁` has cardinality `ℵ₁`, because its increasing enumeration `f : ω₁ → A`,

`f(α) = the least element of A above all f(β), β < α`,

is an injection. In the Boolean-valued universe `A` is given by truth values
`b ξ = ⟦ξ ∈ A⟧`, one for each ground ordinal `ξ < ω₁`, and `A` need not be in the ground
model. Rather than re-proving ordinal theory inside `V^B`, we define the enumeration
*externally*, by well-founded recursion on the ground ordinal `α`, as a family of truth
values `enumV b α ζ = ⟦f(α) = ζ⟧`:

`⟦f(α) = ζ⟧ = b ζ ⊓ ⨅_{η < ζ} (b η ⇨ ⨆_{β < α} ⟦f(β) = η⟧) ⊓ ⨅_{β < α} ⨆_{η < ζ} ⟦f(β) = η⟧`,

"`ζ ∈ A`, every element of `A` below `ζ` has already been enumerated, and every earlier value
lies below `ζ`". Everything in this file holds in every complete Boolean algebra, over every
`ω₁`-like order (in fact only the well-order is used):

* the **least-element principle** for Boolean families, `⨆ d ≤ ⨆_ξ (d ξ ⊓ ⨅_{η<ξ} (d η)ᶜ)`
  (`iSup_le_iSup_least`), the Boolean form of the well-ordering of the ground `ω₁`;
* `f` is **single-valued** (`enumV_disj`) and **injective** (`enumV_inj`);
* the **step**: if some element of `A` lies above all earlier values, then `f(α)` is defined
  (`enumV_step`).

Whether some element of `A` lies above all earlier values is the one place where σ-closure is
needed. That is done in `CollapseCH`.
-/

namespace Foundations.Forcing

open CBA

variable {I : Type} [Omega1Like I] {B : Type} [CompleteBooleanAlgebra B]

/-- **Least-element principle for Boolean families.** Over a well-order, for every family
`d : I → B`, `⨆_ξ d ξ ≤ ⨆_ξ (d ξ ⊓ ⨅_{η < ξ} (d η)ᶜ)`: in `V^B`, a nonempty set of ground
ordinals has a least element. -/
theorem iSup_le_iSup_least (d : I → B) :
    iSup d ≤ iSup fun ξ => d ξ ⊓ iInf fun η : {η // η < ξ} => (d η.1)ᶜ := by
  refine iSup_le fun ξ => Omega1Like.wf.induction ξ (C := fun ξ => d ξ ≤ _) fun ξ ih => ?_
  let m := iInf fun η : {η // η < ξ} => (d η.1)ᶜ
  calc d ξ ≤ d ξ ⊓ (m ⊔ mᶜ) := le_inf _ _ _ le_rfl (le_trans' le_top' top_le_sup_compl')
    _ ≤ (d ξ ⊓ m) ⊔ (d ξ ⊓ mᶜ) := inf_sup_le _ _ _
    _ ≤ _ := sup_le _ _ _ (le_iSup (fun ξ => d ξ ⊓ iInf fun η : {η // η < ξ} => (d η.1)ᶜ) ξ)
        (inf_le_of_right_le (le_trans' compl_iInf_le (iSup_le fun η => by
          rw [compl_compl]; exact ih η.1 η.2)))

/-- **The enumeration of a Boolean subset of `I`.** `enumV b α ζ` is the truth value of
"the `α`-th element of `A = {ξ | b ξ}` is `ζ`", defined by well-founded recursion on `α`. -/
noncomputable def enumV (b : I → B) : I → I → B :=
  Omega1Like.wf.fix (C := fun _ => I → B) fun α rec ζ =>
    b ζ ⊓ (iInf fun η : {η // η < ζ} => b η.1 ⇨ iSup fun β : {β // β < α} => rec β.1 β.2 η.1) ⊓
      (iInf fun β : {β // β < α} => iSup fun η : {η // η < ζ} => rec β.1 β.2 η.1)

variable (b : I → B)

/-- The defining equation of the enumeration. -/
theorem enumV_eq (α ζ : I) : enumV b α ζ =
    b ζ ⊓ (iInf fun η : {η // η < ζ} => b η.1 ⇨ iSup fun β : {β // β < α} => enumV b β.1 η.1) ⊓
      (iInf fun β : {β // β < α} => iSup fun η : {η // η < ζ} => enumV b β.1 η.1) := by
  unfold enumV; rw [WellFounded.fix_eq]

/-- Enumerated elements belong to `A`. -/
theorem enumV_le_b (α ζ : I) : enumV b α ζ ≤ b ζ := by
  rw [enumV_eq]; lattice_le

/-- Earlier values lie below later ones: `⟦f(α) = ζ⟧ ≤ ⨆_{η<ζ} ⟦f(β) = η⟧` for `β < α`. -/
theorem enumV_le_below {α β : I} (h : β < α) (ζ : I) :
    enumV b α ζ ≤ iSup fun η : {η // η < ζ} => enumV b β η.1 := by
  rw [enumV_eq]
  exact inf_le_of_right_le (iInf_le (fun β : {β // β < α} =>
    iSup fun η : {η // η < ζ} => enumV b β.1 η.1) ⟨β, h⟩)

/-- Elements of `A` below a value are enumerated earlier. -/
theorem enumV_le_fill {α ζ η : I} (h : η < ζ) :
    enumV b α ζ ⊓ b η ≤ iSup fun β : {β // β < α} => enumV b β.1 η := by
  rw [enumV_eq]
  exact le_trans' (inf_le_inf (inf_le_of_left_le (inf_le_of_right_le
    (iInf_le (fun η : {η // η < ζ} => b η.1 ⇨ iSup fun β : {β // β < α} => enumV b β.1 η.1)
      ⟨η, h⟩))) le_rfl) himp_inf_le

/-- Single-valuedness for comparable values, by induction on `α`. -/
theorem enumV_disj_lt (α : I) : ∀ η ζ : I, η < ζ → enumV b α η ⊓ enumV b α ζ ≤ ⊥ := by
  refine Omega1Like.wf.induction α (C := fun α => ∀ η ζ : I, η < ζ →
    enumV b α η ⊓ enumV b α ζ ≤ ⊥) fun α ih η ζ hηζ => ?_
  have h1 : enumV b α η ⊓ enumV b α ζ ≤ iSup fun β : {β // β < α} => enumV b β.1 η :=
    le_trans' (le_inf _ _ _ (inf_le_right _ _) (inf_le_of_left_le (enumV_le_b b α η)))
      (enumV_le_fill b hηζ)
  refine le_trans' (le_inf _ _ _ (inf_le_left _ _) h1) (BSet.inf_iSup_le_of fun β => ?_)
  refine le_trans' (inf_le_inf (enumV_le_below b β.2 η) le_rfl) ?_
  refine le_trans' iSup_inf_le (iSup_le fun θ => ?_)
  exact ih β.1 β.2 θ.1 η θ.2

/-- **The enumeration is single-valued.** `⟦f(α) = ζ⟧ ⊓ ⟦f(α) = ζ'⟧ = ⊥` for `ζ ≠ ζ'`. -/
theorem enumV_disj (α : I) {ζ ζ' : I} (h : ζ ≠ ζ') : enumV b α ζ ⊓ enumV b α ζ' ≤ ⊥ := by
  rcases Omega1Like.tri ζ ζ' with h' | h' | h'
  · exact enumV_disj_lt b α ζ ζ' h'
  · exact absurd h' h
  · rw [inf_comm]; exact enumV_disj_lt b α ζ' ζ h'

/-- Injectivity for comparable arguments. -/
theorem enumV_inj_lt {α β : I} (h : β < α) (ζ : I) : enumV b α ζ ⊓ enumV b β ζ ≤ ⊥ := by
  refine le_trans' (inf_le_inf (enumV_le_below b h ζ) le_rfl) ?_
  refine le_trans' iSup_inf_le (iSup_le fun η => ?_)
  exact enumV_disj_lt b β η.1 ζ η.2

/-- **The enumeration is injective.** `⟦f(α) = ζ⟧ ⊓ ⟦f(β) = ζ⟧ = ⊥` for `α ≠ β`. -/
theorem enumV_inj {α β : I} (h : α ≠ β) (ζ : I) : enumV b α ζ ⊓ enumV b β ζ ≤ ⊥ := by
  rcases Omega1Like.tri α β with h' | h' | h'
  · rw [inf_comm]; exact enumV_inj_lt b h' ζ
  · exact absurd h' h
  · exact enumV_inj_lt b h' ζ

/-- **The enumeration step.** If some `ζ ∈ A` lies above all values `f(β)`, `β < α`, then
`f(α)` is defined: `⨆_ζ (b ζ ⊓ ⨅_{β<α} ⨆_{η<ζ} ⟦f(β) = η⟧) ≤ ⨆_ζ ⟦f(α) = ζ⟧`. The value is
the least such `ζ`, by the least-element principle. -/
theorem enumV_step (α : I) :
    (iSup fun ζ => b ζ ⊓ iInf fun β : {β // β < α} => iSup fun η : {η // η < ζ} =>
      enumV b β.1 η.1) ≤ iSup fun ζ => enumV b α ζ := by
  let d : I → B := fun ζ => b ζ ⊓ iInf fun β : {β // β < α} => iSup fun η : {η // η < ζ} =>
    enumV b β.1 η.1
  refine le_trans' (iSup_le_iSup_least d) (iSup_mono fun ζ => ?_)
  rw [enumV_eq]
  refine le_inf _ _ _ (le_inf _ _ _ (inf_le_of_left_le (inf_le_left _ _))
    (le_iInf fun η => le_himp_iff.2 ?_)) (inf_le_of_left_le (inf_le_right _ _))
  -- the element `η < ζ` of `A` is not above all earlier values, so it is one of them
  let N : {β // β < α} → B := fun β => iSup fun θ : {θ // θ < η.1} => enumV b β.1 θ.1
  have hnot : (d η.1)ᶜ ⊓ b η.1 ≤ iSup fun β => (N β)ᶜ := by
    refine le_trans' (le_compl_iff.2 ?_) compl_iInf_le
    exact le_trans' (le_inf _ _ _ (by lattice_le)
      (le_inf _ _ _ (by lattice_le) (by lattice_le))) compl_inf_le
  have hD : d ζ ⊓ (iInf fun η : {η // η < ζ} => (d η.1)ᶜ) ⊓ b η.1 ≤
      (iSup fun β => (N β)ᶜ) ⊓ ((iInf fun β : {β // β < α} => iSup fun θ : {θ // θ < ζ} =>
        enumV b β.1 θ.1) ⊓ b η.1) :=
    le_inf _ _ _ (le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_right_le (iInf_le _ η)))
      (inf_le_right _ _)) hnot) (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le
        (inf_le_right _ _))) (inf_le_right _ _))
  refine le_trans' hD (le_trans' iSup_inf_le (iSup_le fun β => ?_))
  refine le_trans' (inf_le_inf le_rfl (inf_le_inf (iInf_le _ β) le_rfl)) ?_
  have : (N β)ᶜ ⊓ ((iSup fun θ : {θ // θ < ζ} => enumV b β.1 θ.1) ⊓ b η.1) ≤
      iSup fun θ : {θ // θ < ζ} => (N β)ᶜ ⊓ (enumV b β.1 θ.1 ⊓ b η.1) :=
    le_trans' (inf_le_inf le_rfl iSup_inf_le) inf_iSup_le
  refine le_trans' this (iSup_le fun θ => ?_)
  rcases Omega1Like.tri θ.1 η.1 with h | h | h
  · -- `θ < η`: excluded by `(N β)ᶜ`
    exact le_trans' (le_inf _ _ _ (inf_le_left _ _) (inf_le_of_right_le (inf_le_of_left_le
      (le_iSup (fun θ : {θ // θ < η.1} => enumV b β.1 θ.1) ⟨θ.1, h⟩)))) compl_inf_le
      |> le_trans' (le_rfl) |> fun h' => le_trans' h' bot_le'
  · -- `θ = η`
    refine inf_le_of_right_le (inf_le_of_left_le ?_)
    rw [h]; exact le_iSup (fun β : {β // β < α} => enumV b β.1 η.1) β
  · -- `η < θ`: then `η` was enumerated before `β`
    refine inf_le_of_right_le (le_trans' (enumV_le_fill b h) (iSup_le fun β' => ?_))
    exact le_iSup (fun β : {β // β < α} => enumV b β.1 η.1)
      ⟨β'.1, Omega1Like.lt_trans _ _ _ β'.2 β.2⟩

end Foundations.Forcing
