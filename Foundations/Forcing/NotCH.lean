import Foundations.Forcing.CardinalPreservation
import Foundations.Forcing.CohenReals

/-!
# The failure of CH in `V^{Cohen(ω₂)}`, and ZF ⊬ CH

We now put everything together, with the index set of the Cohen reals taken to be `W₂`, the
(small type of) members of the ground ordinal `ω₂`. Let `B = Cohen W₂`.

In `V^B`, `ω̌` is ω (`isOmega_omegaB`) and the name `P` of all Boolean subsets of `ω̌` is its
power set (`isPow_powersetB`). Consider the name `x = {ċ_ξ | ξ ∈ ω₁}` of the first `ℵ₁` Cohen
reals. It is a subset of `𝒫(ω)` (`subset_xName`). Moreover:

* `x` does not inject into `ω` (`no_inj_x_omega`). The `ċ_ξ` are pairwise distinct, and `ω₁`
  does not inject into `ℕ × ℕ`, so the ccc argument of `CardinalPreservation` applies.
* `𝒫(ω)` does not inject into `x` (`no_inj_P_x`). Otherwise the name `{ċ_α | α ∈ ω₂}`, a subset
  of `𝒫(ω)`, would inject into `x`. But `ω₂` does not inject into `ω₁ × ℕ`.

So `x` witnesses the failure of CH, and `⟦CH⟧ = ⊥` (`val_CH_eq_bot`), i.e. `⟦¬CH⟧ = ⊤`
(`VB_not_CH`). Since every axiom of ZF has value `⊤` in `V^B` and `⊤ ≠ ⊥` in the Cohen
algebra, soundness yields the main theorem:

> **`ZF_not_proves_CH`: `¬ (ZF ⊢₁ CH)`**, and in fact ZF + ¬CH is consistent
> (`ZF_notCH_consistent`).

**Scope.** This is Cohen's half of the independence of CH, for **ZF** (in the axiomatisation
`ZF` of `BSetZF`, which includes the universal closures of all scheme instances), with CH the
specific `LSet` sentence `CH` of `Formulas`. The axiom of choice is not used in this file. It is
verified in `V^B` in `AxiomOfChoice` (choice-set form), which upgrades the result to
`ZFC_not_proves_CH : ¬ (ZFC ⊢₁ CH)` with the same model. The other half (`ZF ⊬ ¬CH`) is proved
in `CollapseCH` by a collapse model rather than `L`, and both are combined in `Independence`. No Con(ZF) hypothesis is needed, because Lean's type theory (with universes and
choice), which is stronger than ZF, proves that ZF has models. Read from outside, the result is
relative to the consistency of Lean's logic.
-/

namespace Foundations.Forcing

open Foundations.Logic.FO Foundations.Sets CBA BStructure

attribute [local instance] Classical.propDecidable

/-! ### `ω̌` is ω and `P` is its power set (in any `V^B`) -/

section General

variable {B : Type} [CompleteBooleanAlgebra B]

/-- `ň`-numeral `0` has no members. -/
theorem mem_natB_zero (z : BSet B) : BSet.mem z (natB 0) = ⊥ := by
  rw [mem_natB]; exact eq_bot_iff.2 (iSup_le fun m => absurd m.2 (Nat.not_lt_zero _))

/-- Successor names: `⟦y = ň⟧ ≤ ⟦(n+1)ˇ = y ∪ {y}⟧`. -/
theorem eq_le_isSucc (y : BSet B) (n : Nat) : BSet.eq y (natB n) ≤ BSet.isSucc (natB (n + 1)) y := by
  refine le_iInf fun w => ?_
  rw [mem_natB_succ]
  have hs := BSet.eq_symm y (natB n)
  refine le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_)
  · refine le_trans' (inf_sup_le _ _ _) (sup_le_sup ?_ ?_)
    · exact le_trans' (inf_le_inf hs le_rfl) (BSet.mem_congr_right _ _ _)
    · exact le_trans' (by rw [inf_comm]; exact inf_le_inf le_rfl hs) (BSet.eq_trans w (natB n) y)
  · refine le_trans' (inf_sup_le _ _ _) (sup_le_sup ?_ ?_)
    · exact BSet.mem_congr_right _ _ _
    · rw [inf_comm]; exact BSet.eq_trans _ _ _

/-- `ω̌` is inductive (value `⊤`). -/
theorem isInductive_omegaB : BSet.isInductive (omegaB : BSet B) = ⊤ := by
  have hω : ∀ n, BSet.mem (natB n) (omegaB : BSet B) = ⊤ := mem_natB_family _
  refine eq_top_iff.2 (le_inf _ _ _ ?_ ?_)
  · refine le_iSup_of_le (natB 0) (le_inf _ _ _ (by rw [hω 0]; exact le_rfl) ?_)
    exact le_iInf fun z => le_himp_iff.2 (inf_le_of_right_le (by rw [mem_natB_zero]; exact le_rfl))
  · refine le_iInf fun y => le_himp_iff.2 ?_
    rw [top_inf]
    show (iSup fun n : Nat => ⊤ ⊓ BSet.eq y (natB n)) ≤ _
    refine iSup_le fun n => le_iSup_of_le (natB (n + 1)) ?_
    rw [top_inf, hω, top_inf]
    exact eq_le_isSucc y n

/-- An inductive name contains every numeral (to the degree of its inductiveness). -/
theorem isInductive_le_mem (v : BSet B) : ∀ n, BSet.isInductive v ≤ BSet.mem (natB n) v
  | 0 => by
      refine le_trans' (inf_le_left _ _) (iSup_le fun e => ?_)
      have he : BSet.isEmpty e ≤ BSet.eq e (natB 0) := by
        rw [BSet.eq_eq_iInf_biimp]
        refine le_iInf fun z => ?_
        rw [mem_natB_zero]
        exact le_inf _ _ _ (iInf_le _ z) (le_himp_iff.2 (inf_le_of_right_le bot_le'))
      exact le_trans' (by rw [inf_comm]; exact inf_le_inf he le_rfl) (BSet.mem_congr_left _ _ v)
  | n + 1 => by
      have ih := isInductive_le_mem v n
      have hstep : BSet.isInductive v ≤ iSup fun s => BSet.mem s v ⊓ BSet.isSucc s (natB n) :=
        le_trans' (le_inf _ _ _ (inf_le_of_right_le (iInf_le _ (natB n))) ih) himp_inf_le
      refine le_trans' hstep (iSup_le fun s => ?_)
      have hs : BSet.isSucc s (natB n) ≤ BSet.eq s (natB (n + 1)) := by
        rw [BSet.eq_eq_iInf_biimp]
        refine iInf_mono fun w => ?_
        rw [mem_natB_succ]; exact le_rfl
      exact le_trans' (by rw [inf_comm]; exact inf_le_inf hs le_rfl) (BSet.mem_congr_left _ _ v)

/-- **`ω̌` is ω in `V^B`**: `⟦ω̌ is the least inductive set⟧ = ⊤`. -/
theorem isOmega_omegaB : BSet.isOmega (omegaB : BSet B) = ⊤ := by
  refine eq_top_iff.2 (le_inf _ _ _ (eq_top_iff.1 isInductive_omegaB) ?_)
  refine le_iInf fun v => le_himp_iff.2 ?_
  rw [top_inf]
  refine le_iInf fun z => le_himp_iff.2 ?_
  show _ ⊓ (iSup fun n : Nat => ⊤ ⊓ BSet.eq z (natB n)) ≤ _
  refine le_trans' inf_iSup_le (iSup_le fun n => ?_)
  refine le_trans' (le_inf _ _ _ (inf_le_of_right_le (inf_le_of_right_le (BSet.eq_symm _ _)))
    (inf_le_of_left_le (isInductive_le_mem v n))) (BSet.mem_congr_left _ _ v)

/-- The power-set name of `ω̌`. -/
def powersetB : BSet B := BSet.powerset omegaB

/-- **`P` is the power set of `ω̌` in `V^B`**: `⟦P = 𝒫(ω̌)⟧ = ⊤`. -/
theorem isPow_powersetB : BSet.isPow (powersetB : BSet B) omegaB = ⊤ := by
  refine eq_top_iff.2 (le_iInf fun z => le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_))
  · rw [top_inf]
    refine iSup_le fun f => le_iInf fun w => le_himp_iff.2 ?_
    show ⊤ ⊓ BSet.eq z (omegaB.restrict f) ⊓ BSet.mem w z ≤ _
    exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
      (BSet.mem_congr_right w z _)) (BSet.mem_restrict_le _ f w)
  · rw [top_inf]
    refine le_iSup_of_le (fun i => BSet.mem (omegaB.func i) z) ?_
    show _ ≤ ⊤ ⊓ _
    rw [top_inf]; exact BSet.subset_le_eq_restrict omegaB z

/-- Membership in a name is bounded by membership in `P` when all listed members are in `P`. -/
theorem mem_le_powersetB {T : Type} (h : T → BSet B) (hP : ∀ t, BSet.mem (h t) powersetB = ⊤)
    (a : BSet B) : BSet.mem a (.mk T h fun _ => ⊤) ≤ BSet.mem a powersetB :=
  iSup_le fun t => le_trans' (le_inf _ _ _ (inf_le_of_right_le (BSet.eq_symm _ _))
    (le_trans' le_top' (eq_top_iff.1 (hP t)))) (BSet.mem_congr_left _ _ _)

/-- `⊤ ⇨ a ≤ a`, and more generally `(b ⇨ a) ≤ a` when `b = ⊤`. -/
theorem himp_le_of_eq_top {a b : B} (hb : b = ⊤) : (b ⇨ a) ≤ a :=
  le_trans' (le_inf _ _ _ le_rfl (by rw [hb]; exact le_top')) himp_inf_le

end General

/-! ### The Cohen model over `ω₂` -/

/-- The Boolean algebra of the model: the Cohen algebra adding `ℵ₂` reals. -/
abbrev CohenB : Type := Cohen W₂

/-- Each Cohen real is a member of `P = 𝒫(ω̌)` with value `⊤`. -/
theorem mem_creal_powersetB (α : W₂) : BSet.mem (creal α) (powersetB : BSet CohenB) = ⊤ := by
  refine eq_top_iff.2 (le_iSup_of_le (fun n : Nat => atom (α, n) true) ?_)
  have : omegaB.restrict (fun n : Nat => atom (α, n) true) = (creal α : BSet CohenB) := by
    show BSet.mk Nat natB (fun n => atom (α, n) true ⊓ ⊤) = BSet.mk Nat natB fun n => atom (α, n) true
    simp only [inf_top]
  show ⊤ ≤ ⊤ ⊓ BSet.eq (creal α) (omegaB.restrict fun n : Nat => atom (α, n) true)
  rw [this, BSet.eq_self, inf_top]; exact le_rfl

/-- The name `x = {ċ_ξ | ξ ∈ ω₁}` of the first `ℵ₁` Cohen reals. -/
noncomputable def xName : BSet CohenB := .mk W₁ (fun ξ => creal (W₁.incl ξ)) fun _ => ⊤

/-- The name `{ċ_α | α ∈ ω₂}` of all the Cohen reals. -/
def cName : BSet CohenB := .mk W₂ creal fun _ => ⊤

/-- `⟦x ⊆ 𝒫(ω̌)⟧ = ⊤`. -/
theorem subset_xName : BSet.subset xName (powersetB : BSet CohenB) = ⊤ :=
  eq_top_iff.2 (le_iInf fun a => le_himp_iff.2 (inf_le_of_right_le
    (mem_le_powersetB _ (fun _ => mem_creal_powersetB _) a)))

/-- **`x` is uncountable in `V^B`**: no `f` is an injective function from `x` into `ω̌`. -/
theorem no_inj_x_omega (f : BSet CohenB) :
    BSet.isFunc f xName omegaB ⊓ BSet.isInj f xName = ⊥ :=
  isFunc_inf_isInj_eq_bot (cohen_isCCC W₂) (fun ξ => creal (W₁.incl ξ)) natB
    (fun _ _ h => creal_ne fun e => h (W₁.incl_injective e)) W₁_not_inj f

/-- **`𝒫(ω)` does not inject into `x` in `V^B`.** -/
theorem no_inj_P_x (f : BSet CohenB) :
    BSet.isFunc f powersetB xName ⊓ BSet.isInj f powersetB = ⊥ := by
  have hsub : ∀ a, BSet.mem a cName ≤ BSet.mem a powersetB :=
    mem_le_powersetB _ mem_creal_powersetB
  apply eq_bot_iff.2
  refine le_trans' (inf_le_inf (BSet.isFunc_mono_dom hsub) (BSet.isInj_mono_dom hsub)) ?_
  exact eq_bot_iff.1 (isFunc_inf_isInj_eq_bot (cohen_isCCC W₂) creal (fun ξ => creal (W₁.incl ξ))
    (fun _ _ h => creal_ne h) W₂_not_inj f)

/-- **CH is false in `V^{Cohen(ω₂)}`**: `⟦CH⟧ = ⊥`. -/
theorem val_CH_eq_bot (e : Nat → BSet CohenB) : (VB CohenB).val e CH = ⊥ := by
  rw [val_CH]
  apply eq_bot_iff.2
  refine iInf_le_of_le omegaB (iInf_le_of_le powersetB ?_)
  refine le_trans' (himp_le_of_eq_top (by rw [isOmega_omegaB, isPow_powersetB, inf_top])) ?_
  refine iInf_le_of_le xName (le_trans' (himp_le_of_eq_top subset_xName) ?_)
  exact sup_le _ _ _ (iSup_le fun f => (no_inj_x_omega f) ▸ le_rfl)
    (iSup_le fun f => (no_inj_P_x f) ▸ le_rfl)

/-- **`V^{Cohen(ω₂)} ⊨ ¬CH`**: the negation of the Continuum Hypothesis has truth value `⊤`. -/
theorem VB_not_CH (e : Nat → BSet CohenB) : (VB CohenB).val e (Formula.neg CH) = ⊤ := by
  show (VB CohenB).val e CH ⇨ ⊥ = ⊤
  rw [val_CH_eq_bot, himp_eq_top_iff]; exact le_rfl

/-- **Cohen's theorem: ZF does not prove CH.** No derivation of the sentence `CH` from the
axioms `ZF` exists in the first-order natural deduction calculus. -/
theorem ZF_not_proves_CH : ¬ (ZF ⊢₁ CH) :=
  not_proves_of_val (VB CohenB) (fun _ => BSet.empty) (VB_models_ZF _)
    (by rw [val_CH_eq_bot]; exact (cohen_top_ne_bot W₂).symm)

/-- **ZF + ¬CH is consistent**: it does not derive `⊥`. -/
theorem ZF_notCH_consistent : ¬ (Theory.insert ZF (Formula.neg CH) ⊢₁ Formula.bot) := by
  refine not_proves_of_val (VB CohenB) (fun _ => BSet.empty) ?_ (cohen_top_ne_bot W₂).symm
  rintro ψ (rfl | h)
  · exact VB_not_CH _
  · exact VB_models_ZF _ ψ h

end Foundations.Forcing
