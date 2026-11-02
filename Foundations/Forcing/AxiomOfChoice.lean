import Foundations.Forcing.Mixing
import Foundations.Forcing.NotCH

/-!
# The axiom of choice in `V^B`, and ZFC ⊬ CH

`NotCH` showed `ZF ⊬ CH`. To upgrade this to Cohen's theorem in its usual form, `ZFC ⊬ CH`, we
verify that the axiom of choice has truth value `⊤` in `V^B` for **every** complete Boolean
algebra `B`. We use the **choice-set form** of AC (Zermelo 1908; Jech, *Set Theory*, ch. 5):

> for every set `x` whose members are nonempty and pairwise disjoint, there is a set `c` that
> meets every member of `x` in exactly one element.

Over the other axioms of ZF this is equivalent to the usual forms of AC (choice functions,
well-ordering, Zorn). That equivalence is textbook set theory and is not formalised here.

**The proof.** Let `x = {(Xᵢ, aᵢ)}` and assume the hypothesis of AC to degree `H`. Two choices
must be made coherently.

1. *Which listed members represent a member of `x`.* Different indices `i ≠ k` may list
   Boolean-equal members `Xᵢ`, `Xₖ`. A choice made separately for each would then violate
   uniqueness. So we well-order the index type in the metatheory and pass to the
   disjoint refinement `sᵢ = aᵢ ⊓ ¬⨆_{k<i} (aₖ ⊓ ⟦Xᵢ = Xₖ⟧)` of `Mixing`. Then
   `sᵢ ⊓ sₖ ⊓ ⟦Xᵢ = Xₖ⟧ = ⊥` for `i ≠ k`, and each `aᵢ` is still covered by
   `⨆ₖ (sₖ ⊓ ⟦Xᵢ = Xₖ⟧)`.
2. *An element of each `Xᵢ`.* By the maximum principle (`BSet.exists_mem_witness`) there is
   a single name `zᵢ` with `⟦zᵢ ∈ Xᵢ⟧ = ⟦Xᵢ ≠ ∅⟧`.

The choice set is the name `c = {(zᵢ, sᵢ)}`. Existence of an element of `Xᵢ ∩ c` is witnessed
by `zᵢ`. For uniqueness, an element `z'` of `Xᵢ ∩ c` equals some `zₖ`. Then `z'` lies in
`Xᵢ ∩ Xₖ`, so `Xᵢ = Xₖ` by disjointness, and so `k = i` by the separation of step 1. The
general member `y` of `x` is reduced to the listed ones by the congruence lemma.

Then `ZFC := ZF ∪ {AC}` holds in `V^B` (`VB_models_ZFC`), and the Cohen model of `NotCH` gives

> **`ZFC_not_proves_CH : ¬ (ZFC ⊢₁ CH)`** and `ZFC_notCH_consistent`.
-/

namespace Foundations.Forcing

open Foundations.Logic.FO CBA BStructure

attribute [local instance] Classical.propDecidable

variable {B : Type} [CompleteBooleanAlgebra B]

/-! ### The formula -/

/-- The hypothesis of AC about `x` (variable `0`): every member of `x` is nonempty, and members
of `x` with a common element are equal. In de Bruijn form,
`(∀y (y ∈ x → ∃z z ∈ y)) ∧ ∀y (y ∈ x → ∀y' (y' ∈ x → ∀z (z ∈ y ∧ z ∈ y' → y = y')))`. -/
def choiceHyp : Formula LSet :=
  .conj (.all (.imp (memF (v 0) (v 1)) (.ex (memF (v 0) (v 1)))))
    (.all (.imp (memF (v 0) (v 1)) (.all (.imp (memF (v 0) (v 2))
      (.all (.imp (.conj (memF (v 0) (v 2)) (memF (v 0) (v 1))) (.eq (v 2) (v 1))))))))

/-- The conclusion of AC about `y` (variable `0`) and `c` (variable `1`): `y ∩ c` has exactly
one element, `∃z ((z ∈ y ∧ z ∈ c) ∧ ∀z' (z' ∈ y ∧ z' ∈ c → z' = z))`. -/
def choiceBody : Formula LSet :=
  .ex (.conj (.conj (memF (v 0) (v 1)) (memF (v 0) (v 2)))
    (.all (.imp (.conj (memF (v 0) (v 2)) (memF (v 0) (v 3))) (.eq (v 0) (v 1)))))

/-- **The axiom of choice** (choice-set form), a sentence of `LSet`:
`∀x (choiceHyp(x) → ∃c ∀y (y ∈ x → choiceBody(y, c)))`. Written out:

`∀x [ (∀y (y ∈ x → ∃z z ∈ y)) ∧ (∀y (y ∈ x → ∀y' (y' ∈ x → ∀z (z ∈ y ∧ z ∈ y' → y = y'))))
  → ∃c ∀y (y ∈ x → ∃z ((z ∈ y ∧ z ∈ c) ∧ ∀z' (z' ∈ y ∧ z' ∈ c → z' = z))) ]`.

"Every set of nonempty, pairwise disjoint sets has a choice set": a set meeting each member in
exactly one element. -/
def axChoice : Formula LSet :=
  .all (.imp choiceHyp (.ex (.all (.imp (memF (v 0) (v 2)) choiceBody))))

/-- Truth value of the hypothesis of AC. -/
theorem val_choiceHyp (x : BSet B) (e : Nat → BSet B) :
    (VB B).val (BEnv.cons x e) choiceHyp =
      (iInf fun y => BSet.mem y x ⇨ iSup fun z => BSet.mem z y) ⊓
      (iInf fun y => BSet.mem y x ⇨ iInf fun y' => BSet.mem y' x ⇨
        iInf fun z => (BSet.mem z y ⊓ BSet.mem z y') ⇨ BSet.eq y y') := rfl

/-- Truth value of the conclusion of AC. -/
theorem val_choiceBody (y c : BSet B) (e : Nat → BSet B) :
    (VB B).val (BEnv.cons y (BEnv.cons c e)) choiceBody =
      iSup fun z => (BSet.mem z y ⊓ BSet.mem z c) ⊓
        iInf fun z' => (BSet.mem z' y ⊓ BSet.mem z' c) ⇨ BSet.eq z' z := rfl

/-- **Truth value of AC.** -/
theorem val_axChoice (e : Nat → BSet B) : (VB B).val e axChoice =
    iInf fun x => (VB B).val (BEnv.cons x e) choiceHyp ⇨
      iSup fun c => iInf fun y => BSet.mem y x ⇨
        (VB B).val (BEnv.cons y (BEnv.cons c (BEnv.cons x e))) choiceBody := rfl

/-! ### AC holds in `V^B` -/

/-- **The axiom of choice holds in `V^B`.** For every complete Boolean algebra `B` and every
environment, `⟦AC⟧ = ⊤`. -/
theorem VB_choice (e : Nat → BSet B) : (VB B).val e axChoice = ⊤ := by
  rw [val_axChoice]
  refine eq_top_iff.2 (le_iInf fun x => le_himp_iff.2 ?_)
  rw [top_inf, val_choiceHyp]
  cases x with
  | mk I X a =>
  -- notation
  let x : BSet B := .mk I X a
  let H := (iInf fun y => BSet.mem y x ⇨ iSup fun z => BSet.mem z y) ⊓
      (iInf fun y => BSet.mem y x ⇨ iInf fun y' => BSet.mem y' x ⇨
        iInf fun z => (BSet.mem z y ⊓ BSet.mem z y') ⇨ BSet.eq y y')
  show H ≤ _
  -- step 1: separate the listing of `x`
  obtain ⟨lt, _, htot, hwf⟩ := Foundations.Sets.WellOrdering.exists_wellOrder I
  let r : I → I → B := fun i k => BSet.eq (X i) (X k)
  let s : I → B := refine lt a r
  have hsep : ∀ i k, i ≠ k → s i ⊓ s k ⊓ BSet.eq (X i) (X k) ≤ ⊥ := fun i k h =>
    refine_disjoint (r := r) htot (fun _ _ => BSet.eq_symm _ _) h
  have hcov : ∀ i, a i ≤ iSup fun k => s k ⊓ BSet.eq (X i) (X k) := fun i =>
    refine_cover (r := r) hwf (fun _ => BSet.eq_self _) (fun _ _ _ => BSet.eq_trans _ _ _) i
  have hsx : ∀ k, s k ≤ BSet.mem (X k) x := fun k =>
    le_trans' (refine_le lt a r k) (BSet.bval_le_mem x k)
  -- step 2: an element of each member
  let z : I → BSet B := fun i => Classical.choose (X i).exists_mem_witness
  have hz : ∀ i, iSup (fun w => BSet.mem w (X i)) ≤ BSet.mem (z i) (X i) := fun i =>
    Classical.choose_spec (X i).exists_mem_witness
  let c : BSet B := .mk I z s
  have hsc : ∀ k, s k ≤ BSet.mem (z k) c := fun k => BSet.bval_le_mem c k
  have hne : ∀ k, H ⊓ s k ≤ BSet.mem (z k) (X k) := fun k =>
    le_trans' (le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (iInf_le _ (X k))))
      (inf_le_of_right_le (hsx k))) himp_inf_le) (hz k)
  have hdis : ∀ i k w, H ⊓ s i ⊓ s k ⊓ BSet.mem w (X i) ⊓ BSet.mem w (X k) ≤
      BSet.eq (X i) (X k) := by
    intro i k w
    have h1 : H ≤ BSet.mem (X i) x ⇨ BSet.mem (X k) x ⇨
        (BSet.mem w (X i) ⊓ BSet.mem w (X k)) ⇨ BSet.eq (X i) (X k) :=
      inf_le_of_right_le (le_trans' (iInf_le _ (X i)) (himp_le_himp le_rfl
        (le_trans' (iInf_le _ (X k)) (himp_le_himp le_rfl (iInf_le _ w)))))
    refine le_trans' (le_inf _ _ _ ?_ (le_inf _ _ _ (inf_le_of_left_le (inf_le_right _ _))
      (inf_le_right _ _))) himp_inf_le
    refine le_trans' (le_inf _ _ _ ?_ (inf_le_of_left_le (inf_le_of_left_le
      (inf_le_of_right_le (hsx k))))) himp_inf_le
    exact le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (inf_le_of_left_le
      (inf_le_of_left_le h1)))) (inf_le_of_left_le (inf_le_of_left_le (inf_le_of_left_le
        (inf_le_of_right_le (hsx i)))))) himp_inf_le
  -- the conclusion at a listed member `Xₖ`, with witness `zₖ`
  have hpt : ∀ k, H ⊓ s k ≤ (VB B).val (BEnv.cons (X k) (BEnv.cons c (BEnv.cons x e))) choiceBody := by
    intro k
    rw [val_choiceBody]
    refine le_iSup_of_le (z k) (le_inf _ _ _ (le_inf _ _ _ (hne k) (inf_le_of_right_le (hsc k)))
      (le_iInf fun z' => le_himp_iff.2 ?_))
    -- uniqueness: `z' ∈ c` means `z' = zₘ`, and `m = k` by separation
    refine le_trans' (le_inf _ _ _ (le_inf _ _ _ (inf_le_left _ _)
      (inf_le_of_right_le (inf_le_left _ _))) (inf_le_of_right_le (inf_le_right _ _))) ?_
    show (H ⊓ s k ⊓ BSet.mem z' (X k)) ⊓ (iSup fun m => s m ⊓ BSet.eq z' (z m)) ≤ _
    refine le_trans' inf_iSup_le (iSup_le fun m => ?_)
    by_cases hmk : m = k
    · subst hmk; exact inf_le_of_right_le (inf_le_right _ _)
    · refine le_trans' ?_ bot_le'
      have hzm : H ⊓ s k ⊓ BSet.mem z' (X k) ⊓ (s m ⊓ BSet.eq z' (z m)) ≤ BSet.mem z' (X m) :=
        le_trans' (le_inf _ _ _ (inf_le_of_right_le (le_trans' (inf_le_right _ _) (BSet.eq_symm _ _)))
          (le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le
            (inf_le_left _ _))) (inf_le_of_right_le (inf_le_left _ _))) (hne m)))
          (BSet.mem_congr_left _ _ _)
      have hXX : H ⊓ s k ⊓ BSet.mem z' (X k) ⊓ (s m ⊓ BSet.eq z' (z m)) ≤ BSet.eq (X k) (X m) :=
        le_trans' (le_inf _ _ _ (le_inf _ _ _ (le_inf _ _ _ (le_inf _ _ _
          (inf_le_of_left_le (inf_le_of_left_le (inf_le_left _ _)))
          (inf_le_of_left_le (inf_le_of_left_le (inf_le_right _ _))))
          (inf_le_of_right_le (inf_le_left _ _)))
          (inf_le_of_left_le (inf_le_right _ _))) hzm) (hdis k m z')
      refine le_trans' (le_inf _ _ _ (le_inf _ _ _
        (inf_le_of_left_le (inf_le_of_left_le (inf_le_right _ _)))
        (inf_le_of_right_le (inf_le_left _ _))) hXX) (hsep k m (Ne.symm hmk))
  -- an arbitrary member `y` of `x`
  refine le_iSup_of_le c (le_iInf fun y => le_himp_iff.2 ?_)
  show H ⊓ (iSup fun i => a i ⊓ BSet.eq y (X i)) ≤ _
  refine le_trans' inf_iSup_le (iSup_le fun i => ?_)
  refine le_trans' (le_inf _ _ _ (le_inf _ _ _ (inf_le_left _ _)
    (inf_le_of_right_le (inf_le_right _ _)))
    (inf_le_of_right_le (le_trans' (inf_le_left _ _) (hcov i)))) ?_
  refine le_trans' inf_iSup_le (iSup_le fun k => ?_)
  -- `H ⊓ ⟦y = Xᵢ⟧ ⊓ (sₖ ⊓ ⟦Xᵢ = Xₖ⟧) ≤ ⟦Xₖ = y⟧ ⊓ (H ⊓ sₖ)`, then congruence in `y`
  refine le_trans' (le_inf _ _ _ ?_ (le_inf _ _ _ (inf_le_of_left_le (inf_le_left _ _))
    (inf_le_of_right_le (inf_le_left _ _))))
    (le_trans' (inf_le_inf le_rfl (hpt k)) (eq_inf_val_cons_le (M := VB B) choiceBody _ (X k) y))
  exact le_trans' (le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_right _ _))
    (inf_le_of_right_le (inf_le_right _ _))) (BSet.eq_trans _ _ _)) (BSet.eq_symm _ _)

/-! ### ZFC and the unprovability of CH -/

/-- **The axioms of ZFC**: the axioms `ZF` of `BSetZF` together with the axiom of choice
`axChoice` (choice-set form). -/
def ZFC : Theory LSet := fun ψ => ZF ψ ∨ ψ = axChoice

/-- **`V^B` is a Boolean-valued model of ZFC.** For every complete Boolean algebra `B : Type`
and every environment, every axiom of ZFC has truth value `⊤` in `V^B`. -/
theorem VB_models_ZFC (e : Nat → BSet B) : ∀ ψ, ZFC ψ → (VB B).val e ψ = ⊤ := by
  rintro ψ (h | rfl)
  · exact VB_models_ZF e ψ h
  · exact VB_choice e

/-- **Every theorem of ZFC is true in `V^B`**, for every complete Boolean algebra `B`. -/
theorem VB_val_eq_top_of_ZFC {φ : Formula LSet} (h : ZFC ⊢₁ φ) (e : Nat → BSet B) :
    (VB B).val e φ = ⊤ :=
  val_eq_top_of_theory h (VB B) e (VB_models_ZFC e)

/-- **Cohen's theorem: ZFC does not prove CH.** No derivation of the sentence `CH` from the
axioms `ZFC` (ZF plus the axiom of choice) exists in the first-order natural deduction
calculus. -/
theorem ZFC_not_proves_CH : ¬ (ZFC ⊢₁ CH) :=
  not_proves_of_val (VB CohenB) (fun _ => BSet.empty) (VB_models_ZFC _)
    (by rw [val_CH_eq_bot]; exact (cohen_top_ne_bot W₂).symm)

/-- **ZFC + ¬CH is consistent**: it does not derive `⊥`. -/
theorem ZFC_notCH_consistent : ¬ (Theory.insert ZFC (Formula.neg CH) ⊢₁ Formula.bot) := by
  refine not_proves_of_val (VB CohenB) (fun _ => BSet.empty) ?_ (cohen_top_ne_bot W₂).symm
  rintro ψ (rfl | h)
  · exact VB_not_CH _
  · exact VB_models_ZFC _ ψ h

end Foundations.Forcing
