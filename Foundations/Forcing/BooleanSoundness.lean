import Foundations.Forcing.BooleanSemantics
import Foundations.Logic.FOSoundness
import Foundations.Logic.FOSemantics

/-!
# Soundness of natural deduction for Boolean-valued models

The first-order natural deduction calculus `Γ ⊢₁ φ` of `Logic/FOSoundness` was shown sound
for Tarskian (two-valued) structures. Here we prove that it is sound for **every
Boolean-valued structure**, over every complete Boolean algebra `B`:

`Γ ⊢₁ φ  →  ⨅_{ψ ∈ Γ} ⟦ψ⟧ₑ ≤ ⟦φ⟧ₑ`  for every `B`-valued structure and environment `e`.

In particular a formula derivable from no premises has truth value `⊤`. This is the hinge
of the Boolean-valued approach to independence. To show that a theory `T` does not prove
`φ`, it suffices to find a complete Boolean algebra `B` and a `B`-valued model in which
every axiom of `T` has value `⊤` but `⟦φ⟧ ≠ ⊤`. Scott and Solovay showed that for
`T = ZFC` and `φ = CH` such a model exists (`V^B` for the Cohen algebra `B`). Here this is
carried out for `T = ZF` in `NotCH` (`ZF_not_proves_CH`), and for `T = ZFC` in
`AxiomOfChoice` and `Independence` (`CH_independent_ZFC`).

Each rule is checked against the algebra:

* `→`-introduction is residuation `c ⊓ a ≤ b ↔ c ≤ a ⇨ b`;
* reductio ad absurdum is the Boolean law `c ⊓ aᶜ ≤ ⊥ → c ≤ a`;
* `∨`-elimination is finite distributivity, `∃`-elimination is *infinite*
  distributivity `c ⊓ ⨆ₓ aₓ ≤ ⨆ₓ (c ⊓ aₓ)`;
* the quantifier rules use the substitution lemma, and Leibniz's law uses the
  congruence lemma of the previous file.

Finally, `Prop` is itself a complete Boolean algebra (classically). Every Tarskian structure
is a `Prop`-valued structure whose truth values are exactly Tarskian satisfaction
(`val_ofStructure_iff`). So the soundness theorem of `Logic/FOSoundness` is recovered as the
special case `B = Prop` (`entails_of_proves`).
-/

namespace Foundations.Forcing

open Foundations.Logic.FO CBA

universe u w

variable {L : Signature} {B : Type u} [CompleteBooleanAlgebra B]

namespace BStructure

variable {M : BStructure.{u, w} L B}

variable (M) in
/-- The truth value of a theory: the meet of the values of its members. -/
def thVal (Γ : Theory L) (e : Nat → M.Dom) : B := iInf fun ψ : {ψ // Γ ψ} => M.val e ψ.1

/-- A member of a theory is at least as true as the whole theory. -/
theorem thVal_le {Γ : Theory L} {ψ : Formula L} (h : Γ ψ) (e : Nat → M.Dom) :
    M.thVal Γ e ≤ M.val e ψ := iInf_le (fun ψ : {ψ // Γ ψ} => M.val e ψ.1) ⟨ψ, h⟩

/-- Value of an extended theory. -/
theorem le_thVal_insert {Γ : Theory L} {φ : Formula L} (e : Nat → M.Dom) :
    M.thVal Γ e ⊓ M.val e φ ≤ M.thVal (Theory.insert Γ φ) e :=
  le_iInf fun ⟨ψ, hψ⟩ => by
    rcases hψ with rfl | hψ
    · exact inf_le_right _ _
    · exact inf_le_of_left_le (thVal_le hψ e)

/-- The value of a theory under `e` lies below the value of its shift under `x · e`. -/
theorem thVal_le_shift (Γ : Theory L) (e : Nat → M.Dom) (x : M.Dom) :
    M.thVal Γ e ≤ M.thVal (Theory.shift Γ) (BEnv.cons x e) :=
  le_iInf fun ⟨ψ, χ, hχ, hψ⟩ => by
    subst hψ; rw [val_shift]; exact thVal_le hχ e

/-- **Soundness of natural deduction for Boolean-valued models.** If `Γ ⊢₁ φ`, then in every
`B`-valued structure, under every environment, `⨅_{ψ ∈ Γ} ⟦ψ⟧ ≤ ⟦φ⟧`. -/
theorem soundness {Γ : Theory L} {φ : Formula L} (h : Γ ⊢₁ φ) :
    ∀ (M : BStructure.{u, w} L B) (e : Nat → M.Dom), M.thVal Γ e ≤ M.val e φ := by
  induction h with
  | hyp hφ => exact fun M e => thVal_le hφ e
  | impI _ ih =>
      exact fun M e => le_himp_iff.2 (le_trans' (le_thVal_insert e) (ih M e))
  | impE _ _ ih₁ ih₂ =>
      exact fun M e => le_trans' (le_inf _ _ _ (ih₁ M e) (ih₂ M e)) himp_inf_le
  | conjI _ _ ih₁ ih₂ => exact fun M e => le_inf _ _ _ (ih₁ M e) (ih₂ M e)
  | conjE₁ _ ih => exact fun M e => le_trans' (ih M e) (inf_le_left _ _)
  | conjE₂ _ ih => exact fun M e => le_trans' (ih M e) (inf_le_right _ _)
  | disjI₁ _ ih => exact fun M e => le_trans' (ih M e) (le_sup_left _ _)
  | disjI₂ _ ih => exact fun M e => le_trans' (ih M e) (le_sup_right _ _)
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
      intro M e
      calc M.thVal _ e ≤ M.thVal _ e ⊓ M.val e (.disj _ _) := le_inf _ _ _ le_rfl (ih₁ M e)
        _ ≤ (M.thVal _ e ⊓ M.val e _) ⊔ (M.thVal _ e ⊓ M.val e _) := inf_sup_le _ _ _
        _ ≤ _ := sup_le _ _ _ (le_trans' (le_thVal_insert e) (ih₂ M e))
                    (le_trans' (le_thVal_insert e) (ih₃ M e))
  | botE _ ih => exact fun M e => le_trans' (ih M e) bot_le'
  | @raa Γ φ _ ih =>
      intro M e
      apply le_of_inf_compl_le_bot
      have h := le_trans' (le_thVal_insert (M := M) (Γ := Γ) (φ := Formula.neg φ) e) (ih M e)
      have hv : M.val e (Formula.neg φ) = (M.val e φ)ᶜ := by
        show M.val e φ ⇨ ⊥ = _; rw [compl_eq_himp_bot]
      rwa [hv] at h
  | allI _ ih =>
      exact fun M e => le_iInf fun x => le_trans' (thVal_le_shift _ e x) (ih M _)
  | allE t _ ih =>
      intro M e
      rw [val_inst]
      exact le_trans' (ih M e) (iInf_le (fun x => M.val (BEnv.cons x e) _) _)
  | exI t _ ih =>
      intro M e
      have := ih M e
      rw [val_inst] at this
      exact le_trans' this (le_iSup (fun x => M.val (BEnv.cons x e) _) _)
  | @exE Γ φ ψ _ _ ih₁ ih₂ =>
      intro M e
      calc M.thVal Γ e ≤ M.thVal Γ e ⊓ iSup (fun x => M.val (BEnv.cons x e) φ) :=
            le_inf _ _ _ le_rfl (ih₁ M e)
        _ ≤ iSup (fun x => M.thVal Γ e ⊓ M.val (BEnv.cons x e) φ) := inf_iSup_le
        _ ≤ M.val e ψ := iSup_le fun x => by
            have h2 := ih₂ M (BEnv.cons x e)
            rw [val_shift] at h2
            exact le_trans' (inf_le_inf (thVal_le_shift Γ e x) le_rfl)
              (le_trans' (le_thVal_insert _) h2)
  | refl t =>
      intro M e
      show _ ≤ M.eq _ _
      rw [M.eq_refl]; exact le_top'
  | @subst Γ φ s t _ _ ih₁ ih₂ =>
      intro M e
      rw [val_inst]
      have h2 := ih₂ M e
      rw [val_inst] at h2
      have hd : M.eq (M.evalT e s) (M.evalT e t) ≤
          M.envEq (BEnv.cons (M.evalT e s) e) (BEnv.cons (M.evalT e t) e) :=
        le_iInf fun n => by
          cases n with
          | zero => exact le_rfl
          | succ k =>
              show _ ≤ M.eq (e k) (e k)
              rw [M.eq_refl]; exact le_top'
      exact le_trans' (le_inf _ _ _ (le_trans' (ih₁ M e) hd) h2) (envEq_inf_val_le φ _ _)

/-- **Validity of theorems.** A formula derivable from no premises has Boolean truth value
`⊤` in every Boolean-valued structure, under every environment. -/
theorem val_eq_top_of_proves {φ : Formula L} (h : (fun _ => False : Theory L) ⊢₁ φ)
    (M : BStructure.{u, w} L B) (e : Nat → M.Dom) : M.val e φ = ⊤ :=
  eq_top_iff.2 (le_trans' (le_iInf fun ⟨_, h⟩ => h.elim) (soundness h M e))

/-- **Truth of consequences.** If every axiom of `Γ` has value `⊤` and `Γ ⊢₁ φ`, then `φ`
has value `⊤`. This is the form in which soundness yields independence results. -/
theorem val_eq_top_of_theory {Γ : Theory L} {φ : Formula L} (h : Γ ⊢₁ φ)
    (M : BStructure.{u, w} L B) (e : Nat → M.Dom) (hΓ : ∀ ψ, Γ ψ → M.val e ψ = ⊤) :
    M.val e φ = ⊤ :=
  eq_top_iff.2 (le_trans' (le_iInf fun ⟨ψ, h⟩ => (eq_top_iff.1 (hΓ ψ h))) (soundness h M e))

/-- **Unprovability from a Boolean-valued model.** If every axiom of `Γ` is `⊤` in `M` but
`φ` is not, then `Γ` does not derive `φ`. -/
theorem not_proves_of_val {Γ : Theory L} {φ : Formula L} (M : BStructure.{u, w} L B)
    (e : Nat → M.Dom) (hΓ : ∀ ψ, Γ ψ → M.val e ψ = ⊤) (hφ : M.val e φ ≠ ⊤) : ¬ (Γ ⊢₁ φ) :=
  fun h => hφ (val_eq_top_of_theory h M e hΓ)


/-! ### The two-valued case: Tarski's semantics is the case `B = Prop` -/

/-- **`Prop` is a complete Boolean algebra** (classically): order is implication, meets and
joins are `∧`, `∨`, `∀`, `∃`, and the complement is negation. -/
instance propCBA : CompleteBooleanAlgebra Prop where
  le a b := a → b
  inf a b := a ∧ b
  sup a b := a ∨ b
  compl a := ¬ a
  top := True
  bot := False
  sSup S := ∃ a, S a ∧ a
  sInf S := ∀ a, S a → a
  le_refl _ h := h
  le_trans _ _ _ h₁ h₂ h := h₂ (h₁ h)
  le_antisymm _ _ h₁ h₂ := propext ⟨h₁, h₂⟩
  inf_le_left _ _ h := h.1
  inf_le_right _ _ h := h.2
  le_inf _ _ _ h₁ h₂ h := ⟨h₁ h, h₂ h⟩
  le_sup_left _ _ h := Or.inl h
  le_sup_right _ _ h := Or.inr h
  sup_le _ _ _ h₁ h₂ h := h.elim h₁ h₂
  le_top _ _ := trivial
  bot_le _ h := h.elim
  le_sSup _ _ hS h := ⟨_, hS, h⟩
  sSup_le _ _ h := fun ⟨b, hb, hb'⟩ => h b hb hb'
  sInf_le _ _ hS h := h _ hS
  le_sInf _ _ h ha b hb := h b hb ha
  inf_sup_le _ _ _ h := h.2.elim (fun h' => Or.inl ⟨h.1, h'⟩) (fun h' => Or.inr ⟨h.1, h'⟩)
  inf_compl_le_bot _ h := h.2 h.1
  top_le_sup_compl a _ := Classical.em a

/-- Meets in `Prop` are universal quantifiers. -/
theorem prop_iInf_iff {ι : Sort _} (f : ι → Prop) : iInf f ↔ ∀ i, f i :=
  ⟨fun h i => h _ ⟨i, rfl⟩, fun h _ ⟨i, hi⟩ => hi ▸ h i⟩

/-- Joins in `Prop` are existential quantifiers. -/
theorem prop_iSup_iff {ι : Sort _} (f : ι → Prop) : iSup f ↔ ∃ i, f i :=
  ⟨fun ⟨_, ⟨i, hi⟩, h⟩ => ⟨i, hi ▸ h⟩, fun ⟨i, h⟩ => ⟨_, ⟨i, rfl⟩, h⟩⟩

/-- A Tarskian structure, viewed as a `Prop`-valued structure with genuine equality. -/
abbrev ofStructure (M : Structure L) : BStructure.{0, 0} L Prop where
  Dom := M.Dom
  funcs := M.funcs
  rels := M.rels
  eq x y := x = y
  eq_refl x := propext ⟨fun _ => trivial, fun _ => rfl⟩
  eq_symm _ _ h := h.symm
  eq_trans _ _ _ h := h.1.trans h.2
  funcs_congr f a b h := congrArg (M.funcs f) (funext fun i => (prop_iInf_iff _).1 h i)
  rels_congr R a b h := by
    have e : a = b := funext fun i => (prop_iInf_iff _).1 h.1 i
    exact e ▸ h.2

/-- Term evaluation in `ofStructure M` is Tarskian term evaluation. -/
theorem evalT_ofStructure (M : Structure L) (e : Nat → M.Dom) :
    ∀ t : Term L, (ofStructure M).evalT e t = t.eval M e
  | .var _ => rfl
  | .func f ts => by
      show M.funcs f _ = M.funcs f _
      congr; funext i; exact evalT_ofStructure M e (ts i)

/-- The two ways of pushing a value onto an environment agree. -/
theorem benv_cons_eq {α : Type} (x : α) (e : Nat → α) : BEnv.cons x e = Env.cons x e := by
  funext n; cases n <;> rfl

/-- **Boolean-valued semantics generalises Tarski's.** For `B = Prop`, the Boolean truth value
of a formula in a structure is exactly Tarskian satisfaction. -/
theorem val_ofStructure_iff (M : Structure L) :
    ∀ (φ : Formula L) (e : Nat → M.Dom), (ofStructure M).val e φ ↔ Formula.Sat M e φ
  | .bot, _ => Iff.rfl
  | .eq t s, e => by
      show (ofStructure M).evalT e t = (ofStructure M).evalT e s ↔ _
      rw [evalT_ofStructure, evalT_ofStructure]; exact Iff.rfl
  | .rel R ts, e => by
      show M.rels R (fun i => (ofStructure M).evalT e (ts i)) ↔ _
      simp only [evalT_ofStructure]; exact Iff.rfl
  | .imp φ ψ, e => by
      show (¬ _ ∨ _) ↔ (_ → _)
      rw [val_ofStructure_iff M φ e, val_ofStructure_iff M ψ e]
      exact ⟨fun h hφ => h.elim (absurd hφ) id,
        fun h => (Classical.em (Formula.Sat M e φ)).elim (fun hφ => Or.inr (h hφ)) Or.inl⟩
  | .conj φ ψ, e => and_congr (val_ofStructure_iff M φ e) (val_ofStructure_iff M ψ e)
  | .disj φ ψ, e => or_congr (val_ofStructure_iff M φ e) (val_ofStructure_iff M ψ e)
  | .all φ, e => by
      refine (prop_iInf_iff _).trans (forall_congr' fun x => ?_)
      rw [val_ofStructure_iff M φ, benv_cons_eq]
  | .ex φ, e => by
      refine (prop_iSup_iff _).trans (exists_congr fun x => ?_)
      rw [val_ofStructure_iff M φ, benv_cons_eq]

/-- **Tarskian soundness recovered.** Specialising Boolean-valued soundness to `B = Prop`
gives back the soundness theorem of `Logic/FOSoundness`: `Γ ⊢₁ φ → Γ ⊨ φ`. -/
theorem entails_of_proves {Γ : Theory L} {φ : Formula L} (h : Γ ⊢₁ φ) : Entails Γ φ := by
  intro M e hΓ
  have hle := soundness h (ofStructure M) e
  refine (val_ofStructure_iff M φ e).1 (hle ?_)
  exact (prop_iInf_iff _).2 fun ⟨ψ, hψ⟩ => (val_ofStructure_iff M ψ e).2 (hΓ ψ hψ)

end BStructure

end Foundations.Forcing
