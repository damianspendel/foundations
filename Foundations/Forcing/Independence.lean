import Foundations.Forcing.AxiomOfChoice
import Foundations.Forcing.CollapseCH

/-!
# The independence of CH from ZFC

The two halves of the independence of the Continuum Hypothesis come from two different
Boolean-valued models, and choice holds in every Boolean-valued universe (`VB_choice`):

* the Cohen model `V^{Cohen(ω₂)}` has `⟦¬CH⟧ = ⊤` (`VB_not_CH`), giving `ZFC_not_proves_CH`;
* the collapse model `V^{Col(ω₁)}` has `⟦CH⟧ = ⊤` (`VB_CH`); with `VB_models_ZFC` this gives
  `ZFC ⊬ ¬CH` below.

Together they give **CH is independent of ZFC** (`CH_independent_ZFC`): Gödel (1938) and Cohen
(1963), here both by forcing. As everywhere in this part, `CH` is the fixed `LSet` sentence of
`Formulas`, `ZFC` is `ZF ∪ {axChoice}` with the choice-set form of AC, and the results are
unconditional because Lean's metatheory proves that ZFC has models (externally, they are
relative to the consistency of Lean's logic).
-/

namespace Foundations.Forcing

open Foundations.Logic.FO Foundations.Sets CBA BStructure

/-- **ZFC does not prove ¬CH** (Gödel's half, by forcing): the collapse model `V^{Col(ω₁)}`
satisfies every axiom of ZFC with value `⊤` and gives `CH` value `⊤`, so `¬CH` has value `⊥`. -/
theorem ZFC_not_proves_notCH : ¬ (ZFC ⊢₁ CH.neg) := by
  refine not_proves_of_val (VB (Col W₁)) (fun _ => BSet.empty) (VB_models_ZFC _) ?_
  show (VB (Col W₁)).val _ CH ⇨ ⊥ ≠ ⊤
  rw [VB_CH]
  intro h
  exact col_top_ne_bot W₁ (le_antisymm' (himp_eq_top_iff.1 h) bot_le')

/-- **ZFC + CH is consistent**: it does not derive `⊥`. -/
theorem ZFC_CH_consistent : ¬ (Theory.insert ZFC CH ⊢₁ Formula.bot) := by
  refine not_proves_of_val (VB (Col W₁)) (fun _ => BSet.empty) ?_ (col_top_ne_bot W₁).symm
  rintro ψ (rfl | h)
  · exact VB_CH _
  · exact VB_models_ZFC _ ψ h

/-- **The independence of the Continuum Hypothesis** (Gödel 1938, Cohen 1963; here both halves
by forcing): ZFC proves neither `CH` nor `¬CH`. -/
theorem CH_independent_ZFC : ¬ (ZFC ⊢₁ CH) ∧ ¬ (ZFC ⊢₁ CH.neg) :=
  ⟨ZFC_not_proves_CH, ZFC_not_proves_notCH⟩

end Foundations.Forcing
