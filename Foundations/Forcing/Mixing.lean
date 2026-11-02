import Foundations.Forcing.BSetZF
import Foundations.Sets.Choice

/-!
# Disjoint refinements, the mixing lemma and the maximum principle

To verify the axiom of choice in `V^B` (next file, `AxiomOfChoice`) we need two classical
tools of Boolean-valued model theory (Bell, *Set Theory: Boolean-Valued Models and
Independence Proofs*, ch. 1).

* **Disjoint refinement.** In a complete Boolean algebra, a family `(f i)` indexed by a
  well-ordered type can be cut down to `g i = f i ⊓ ¬⨆_{k<i} f k`. The `g i` are pairwise
  disjoint and have the same supremum. We prove a relative version, with a "similarity"
  `r i k` (later: Boolean equality of names): `g i = f i ⊓ ¬⨆_{k<i} (f k ⊓ r i k)`. Then
  `g i ⊓ g k ⊓ r i k = ⊥` for `i ≠ k` (`refine_disjoint`), and every `f i` is covered by
  `⨆ₖ (g k ⊓ r i k)` (`refine_cover`, by well-founded induction). The well-ordering comes
  from Zermelo's theorem in the metatheory (`Sets/Choice`, proved from Zorn's lemma).
* **The mixing lemma.** Given names `y t` and pairwise disjoint weights `w t`, the name
  `mix w y`, which lists each member of `y t` with its degree cut down by `w t`, is equal to
  `y t` to degree at least `w t` (`le_eq_mix`). This needs no choice at all.

Together they give the **maximum principle** (Bell's fullness of `V^B`): every existential
truth value is attained by a single name. For any formula `φ` there is a name `z` with
`⨆_y ⟦φ(y)⟧ ≤ ⟦φ(z)⟧` (`VB_maximum_principle`). We only need the special case "every nonempty
name has a member" (`BSet.exists_mem_witness`): there is `z` with `⨆_w ⟦w ∈ Y⟧ ≤ ⟦z ∈ Y⟧`.
-/

namespace Foundations.Forcing

open Foundations.Logic.FO CBA BStructure

attribute [local instance] Classical.propDecidable

variable {B : Type} [CompleteBooleanAlgebra B]

/-! ### Disjoint refinement along a well-ordering -/

section Refine

variable {ι : Type} (lt : ι → ι → Prop) (f : ι → B) (r : ι → ι → B)

/-- The refinement of `f` along the order `lt`, relative to `r`:
`g i = f i ⊓ ¬⨆_{k < i} (f k ⊓ r i k)`. -/
def refine (i : ι) : B := f i ⊓ (iSup fun k : {k // lt k i} => f k.1 ⊓ r i k.1)ᶜ

/-- The refinement is below the original family. -/
theorem refine_le (i : ι) : refine lt f r i ≤ f i := inf_le_left _ _

variable {lt f r}

/-- **Disjointness of the refinement.** For a total order `lt` and symmetric `r`, distinct
indices have refined values that are disjoint relative to `r`: `g i ⊓ g k ⊓ r i k = ⊥`. -/
theorem refine_disjoint (htot : ∀ x y, lt x y ∨ x = y ∨ lt y x)
    (hsymm : ∀ i k, r i k ≤ r k i) {i k : ι} (hik : i ≠ k) :
    refine lt f r i ⊓ refine lt f r k ⊓ r i k ≤ ⊥ := by
  rcases htot i k with h | h | h
  · -- `i < k`: `g k` excludes `f i ⊓ r k i`
    have h1 : refine lt f r i ⊓ refine lt f r k ⊓ r i k ≤
        (iSup fun m : {m // lt m k} => f m.1 ⊓ r k m.1)ᶜ := inf_le_of_left_le (inf_le_of_right_le (inf_le_right _ _))
    have h2 : refine lt f r i ⊓ refine lt f r k ⊓ r i k ≤
        iSup fun m : {m // lt m k} => f m.1 ⊓ r k m.1 :=
      le_iSup_of_le ⟨i, h⟩ (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (refine_le _ _ _ _)))
        (inf_le_of_right_le (hsymm i k)))
    exact le_trans' (le_inf _ _ _ h1 h2) compl_inf_le
  · exact absurd h hik
  · -- `k < i`: `g i` excludes `f k ⊓ r i k`
    have h1 : refine lt f r i ⊓ refine lt f r k ⊓ r i k ≤
        (iSup fun m : {m // lt m i} => f m.1 ⊓ r i m.1)ᶜ := inf_le_of_left_le (inf_le_of_left_le (inf_le_right _ _))
    have h2 : refine lt f r i ⊓ refine lt f r k ⊓ r i k ≤
        iSup fun m : {m // lt m i} => f m.1 ⊓ r i m.1 :=
      le_iSup_of_le ⟨k, h⟩ (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_right_le (refine_le _ _ _ _)))
        (inf_le_right _ _))
    exact le_trans' (le_inf _ _ _ h1 h2) compl_inf_le

/-- **Covering by the refinement.** For a well-founded `lt` and a reflexive, transitive `r`,
every `f i` is covered by the refined family: `f i ≤ ⨆ₖ (g k ⊓ r i k)`. -/
theorem refine_cover (hwf : WellFounded lt) (hrefl : ∀ i, r i i = ⊤)
    (htrans : ∀ i k m, r i k ⊓ r k m ≤ r i m) (i : ι) :
    f i ≤ iSup fun k => refine lt f r k ⊓ r i k := by
  induction i using hwf.induction with
  | _ i ih =>
    let S := iSup fun k : {k // lt k i} => f k.1 ⊓ r i k.1
    have hsplit : f i ≤ (f i ⊓ S) ⊔ (f i ⊓ Sᶜ) :=
      le_trans' (le_inf _ _ _ le_rfl (le_trans' le_top' top_le_sup_compl')) (inf_sup_le _ _ _)
    refine le_trans' hsplit (sup_le _ _ _ ?_ ?_)
    · refine inf_le_of_right_le (iSup_le fun k => ?_)
      refine le_trans' (inf_le_inf (ih k.1 k.2) le_rfl) (le_trans' iSup_inf_le (iSup_mono fun m => ?_))
      exact le_inf _ _ _ (inf_le_of_left_le (inf_le_left _ _))
        (le_trans' (le_inf _ _ _ (inf_le_right _ _) (inf_le_of_left_le (inf_le_right _ _))) (htrans i k.1 m))
    · exact le_iSup_of_le i (le_inf _ _ _ le_rfl (by rw [hrefl]; exact le_top'))

/-- **Disjoint refinement.** Every family `f : ι → B` has a pairwise disjoint refinement `g ≤ f`
with the same supremum (each `f i` is below `⨆ g`). The index type is well-ordered by
Zermelo's theorem. -/
theorem exists_disjoint_refinement (f : ι → B) :
    ∃ g : ι → B, (∀ i, g i ≤ f i) ∧ (∀ i k, i ≠ k → g i ⊓ g k ≤ ⊥) ∧
      ∀ i, f i ≤ iSup g := by
  obtain ⟨lt, _, htot, hwf⟩ := Foundations.Sets.WellOrdering.exists_wellOrder ι
  refine ⟨refine lt f (fun _ _ => ⊤), refine_le lt f _, fun i k h => ?_, fun i => ?_⟩
  · have := refine_disjoint (f := f) (r := fun _ _ => (⊤ : B)) htot (fun _ _ => le_rfl) h
    rwa [inf_top] at this
  · refine le_trans' (refine_cover (r := fun _ _ => (⊤ : B)) hwf (fun _ => rfl)
      (fun _ _ _ => le_top') i) (iSup_mono fun k => ?_)
    rw [inf_top]; exact le_rfl

end Refine

/-! ### The mixing lemma -/

/-- The **mixture** of names `y t` with weights `w t`: it lists every member of every `y t`,
with degree cut down by `w t`. -/
def BSet.mix {T : Type} (w : T → B) (y : T → BSet B) : BSet B :=
  .mk (Σ t, (y t).type) (fun p => (y p.1).func p.2) (fun p => w p.1 ⊓ (y p.1).bval p.2)

/-- **The mixing lemma.** If the weights are pairwise disjoint, the mixture is equal to each
`y t` at least to degree `w t`: `w t ≤ ⟦mix w y = y t⟧`. -/
theorem BSet.le_eq_mix {T : Type} (w : T → B) (y : T → BSet B)
    (hw : ∀ s t, s ≠ t → w s ⊓ w t ≤ ⊥) (t : T) : w t ≤ BSet.eq (BSet.mix w y) (y t) := by
  apply BSet.le_eq_of
  · rintro ⟨s, l⟩
    show w t ⊓ (w s ⊓ (y s).bval l) ≤ iSup fun j => (y t).bval j ⊓ BSet.eq ((y s).func l) ((y t).func j)
    by_cases h : s = t
    · subst h
      exact le_iSup_of_le l (by rw [BSet.eq_self, inf_top]; exact inf_le_of_right_le (inf_le_right _ _))
    · exact le_trans' (le_trans' (le_inf _ _ _ (inf_le_of_right_le (inf_le_left _ _)) (inf_le_left _ _))
        (hw s t h)) bot_le'
  · intro j
    refine le_iSup_of_le (⟨t, j⟩ : Σ t, (y t).type) ?_
    show _ ≤ (w t ⊓ (y t).bval j) ⊓ BSet.eq ((y t).func j) ((y t).func j)
    rw [BSet.eq_self, inf_top]; exact le_rfl

/-! ### The maximum principle -/

/-- **Witnesses for nonemptiness.** Every name `Y` has a name `z` that is a member of `Y` to the
full degree to which `Y` is nonempty: `⨆_w ⟦w ∈ Y⟧ ≤ ⟦z ∈ Y⟧`. The witness is the mixture of the
listed members of `Y`, weighted by a disjoint refinement of their degrees. -/
theorem BSet.exists_mem_witness (Y : BSet B) :
    ∃ z : BSet B, iSup (fun w => BSet.mem w Y) ≤ BSet.mem z Y := by
  obtain ⟨d, hdle, hdis, hcov⟩ := exists_disjoint_refinement Y.bval
  refine ⟨BSet.mix d Y.func, iSup_le fun w => ?_⟩
  refine iSup_le fun j => inf_le_of_left_le (le_trans' (hcov j) (iSup_le fun k => ?_))
  -- `d k ≤ ⟦mix = Aₖ⟧ ⊓ ⟦Aₖ ∈ Y⟧ ≤ ⟦mix ∈ Y⟧`
  refine le_trans' (le_inf _ _ _ (le_trans' (BSet.le_eq_mix d Y.func hdis k) (BSet.eq_symm _ _))
    (le_trans' (hdle k) (BSet.bval_le_mem Y k))) (BSet.mem_congr_left _ _ _)

/-- **The maximum principle** (fullness of `V^B`). For every formula `φ` and environment `e`
there is a name `z` attaining the existential truth value: `⨆_y ⟦φ(y)⟧ ≤ ⟦φ(z)⟧`. The proof
chooses one witness for each attained truth value (a set, since `B` is), refines the values
to a disjoint family and mixes the witnesses. -/
theorem VB_maximum_principle (φ : Formula LSet) (e : Nat → BSet B) :
    ∃ z : BSet B, iSup (fun y : BSet B => (VB B).val (BEnv.cons y e) φ) ≤
      (VB B).val (BEnv.cons z e) φ := by
  let T := {b : B // ∃ y : BSet B, (VB B).val (BEnv.cons y e) φ = b}
  let wit : T → BSet B := fun t => Classical.choose t.2
  have hwit : ∀ t : T, (VB B).val (BEnv.cons (wit t) e) φ = t.1 := fun t => Classical.choose_spec t.2
  obtain ⟨d, hdle, hdis, hcov⟩ := exists_disjoint_refinement (fun t : T => t.1)
  refine ⟨BSet.mix d wit, iSup_le fun y => ?_⟩
  refine le_trans' (hcov ⟨_, y, rfl⟩) (iSup_le fun k => ?_)
  refine le_trans' (le_inf _ _ _ (le_trans' (BSet.le_eq_mix d wit hdis k) (BSet.eq_symm _ _))
    (le_trans' (hdle k) (hwit k ▸ le_rfl))) (eq_inf_val_cons_le (M := VB B) φ e _ _)

end Foundations.Forcing
