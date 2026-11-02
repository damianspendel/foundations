import Foundations.Logic.GodelIITransfer

/-!
# Feferman's intensionality phenomenon, kernel-checked

Gödel (1931) stated his second theorem for "the" formula expressing the consistency of
the system; Hilbert and Bernays (1939) and Löb (1955) showed that what the proof really
uses are three properties of the provability formula, the derivability conditions
(D1)–(D3). Feferman (1960) drew the moral explicitly: a formula can *define* the set of
theorems of PA in the standard model `ℕ` — be extensionally correct — and yet have a
consistency statement that PA proves. Gödel II is a theorem about sentences, not about
the truth value "PA is consistent". (Feferman's own examples enumerate the axioms of PA
"only as long as they are consistent"; the simplest such example, used below, is a
folklore variant.)

**The example.** Put

  `provF(x) := provH(x) ∧ x ≠ ⌜⊥⌝`.

Because PA is consistent, `⌜⊥⌝` is never the code of a theorem, so in `ℕ` the extra
conjunct changes nothing: `provF` defines PA-provability exactly as `provH` does
(`sat_provF`). Yet the consistency statement `¬provF(⌜⊥⌝)` is outright provable in PA
(`PA_proves_conF_provF`), since `⌜⊥⌝ ≠ ⌜⊥⌝` is refutable.

**Which derivability condition breaks.** `provF` still satisfies (D1) (`provF_D1`) and
(D3) (`provF_D3`). By Gödel II in its abstract form, it cannot satisfy all three, and we
locate the failure precisely: (D2) — closure under modus ponens — fails already for the
instance `□(⊤ → ⊥) → (□⊤ → □⊥)` with `⊤ := ¬⊥` (`provF_not_D2`): proving that instance
in PA would amount to proving `Con_H`, contradicting `godel_second_PA_unconditional`.

**Moral for this library.** The example is why the caveat on
`godel_second_PA_unconditional` matters, and also why the theorem is *not* vacuous: `provH`
contains no consistency filter and satisfies all of (D1)–(D3) provably in PA, which is
exactly the property that `provF` lacks. The derivation predicate `provDP` of
`GodelIID3Main` also satisfies (D1)–(D3), with (D3) obtained by formalised
Σ₁-completeness, so Gödel II holds for it too (`godel_second_provDP`).
-/

namespace Foundations.Logic.FO

open Arith Formula Theory

namespace GodelII

/-- **Feferman-style provability formula.** `provF(x) := provH(x) ∧ ¬(x = ⌜⊥⌝)`
(free variable `0`). -/
noncomputable def provF : Formula Arith := conj provH (neg (eq (v 0) (numeral (fcode bot))))

/-- The formula `⊤ := ¬⊥`. -/
def top : Formula Arith := neg bot

/-- Meaning of `□_F φ = provF(⌜φ⌝)` in every model of PA: it is `□_H φ` together with the
*external* condition `φ ≠ ⊥`. -/
theorem sat_box_provF (N : PAModel) (e : Nat → N.Dom) (φ : Formula Arith) :
    Sat N.M e (box provF φ) ↔ Sat N.M e (box provH φ) ∧ φ ≠ bot := by
  have hv : ∀ x : N.Dom, Term.eval N.M (Env.cons x e) (v 0) = x := fun _ => rfl
  simp only [box, sat_inst, provF, neg, Sat, eval_numeral_M, hv]
  refine and_congr Iff.rfl ⟨fun h hφ => h ?_, fun h he => h (fcode_inj (numM_inj N.isQ he))⟩
  subst hφ; rfl

/-- `□_F φ` is never the formula `⊥` (it is a conjunction). -/
theorem box_provF_ne_bot (φ : Formula Arith) : box provF φ ≠ bot := by
  intro h
  have := congrArg fcode h
  simp only [box, provF, Formula.inst, Formula.subst, fcode_conj, fcode_bot] at this
  exact absurd this (by unfold Computability.pair; omega)

/-- `¬φ` is never the formula `⊥`. -/
theorem neg_ne_bot (φ : Formula Arith) : neg φ ≠ bot := by intro h; cases h

/-- **`provF` defines PA-provability in the standard model**, exactly like `provH`. -/
theorem sat_provF (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provF φ) ↔ PA ⊢₁ φ := by
  rw [sat_box_provF stdPA e φ, sat_provH]
  exact ⟨And.left, fun h => ⟨h, fun hφ => PA_consistent (hφ ▸ h)⟩⟩

/-- **`provF` and `provH` have the same extension in `ℕ`.** -/
theorem provF_std_iff_provH (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provF φ) ↔ Sat stdModel e (box provH φ) := by
  rw [sat_provF, sat_provH]

/-- **PA proves the Feferman consistency statement.** `PA ⊢ ¬provF(⌜⊥⌝)`. -/
theorem PA_proves_conF_provF : PA ⊢₁ conF provF :=
  PA_proves_of_models fun N e h => ((sat_box_provF N e bot).1 h).2 rfl

/-- **Condition (D1) holds for `provF`.** If `PA ⊢ φ` then `PA ⊢ provF(⌜φ⌝)`. -/
theorem provF_D1 {φ : Formula Arith} (h : PA ⊢₁ φ) : PA ⊢₁ box provF φ :=
  PA_proves_of_models fun N e => (sat_box_provF N e φ).2
    ⟨sat_of_PA_proves N (provH_D1 h) e, fun hφ => PA_consistent (hφ ▸ h)⟩

/-- For `φ ≠ ⊥`, the boxes of `provF` and `provH` are PA-provably equivalent; we need the
direction `□_H φ → □_F φ`. -/
theorem boxH_imp_boxF {φ : Formula Arith} (hφ : φ ≠ bot) : PA ⊢₁ imp (box provH φ) (box provF φ) :=
  PA_proves_of_models fun N e h => (sat_box_provF N e φ).2 ⟨h, hφ⟩

/-- **Condition (D3) holds for `provF`.** `PA ⊢ □_F φ → □_F □_F φ`. -/
theorem provF_D3 (φ : Formula Arith) : PA ⊢₁ imp (box provF φ) (box provF (box provF φ)) :=
  PA_proves_of_models fun N e h => by
    obtain ⟨hH, hφ⟩ := (sat_box_provF N e φ).1 h
    refine (sat_box_provF N e _).2 ⟨?_, box_provF_ne_bot φ⟩
    -- `□_H φ → □_H □_H φ` (D3 for `provH`), then `□_H(□_H φ → □_F φ)` by (D1) and (D2)
    have h₁ := sat_of_PA_proves N (provH_D3 φ) e hH
    have h₂ := sat_of_PA_proves N (provH_D1 (boxH_imp_boxF hφ)) e
    exact sat_of_PA_proves N (provH_D2 _ _) e h₂ h₁

/-- **Condition (D2) fails for `provF`**, already at the instance
`□_F(⊤ → ⊥) → (□_F ⊤ → □_F ⊥)`. If PA proved it, then — since a `provH`-proof of `⊥`
yields `provH`-proofs of `⊤ → ⊥` and of `⊤` — PA would prove `Con_H`, contradicting
`godel_second_PA_unconditional`. -/
theorem provF_not_D2 :
    ¬ PA ⊢₁ imp (box provF (imp top bot)) (imp (box provF top) (box provF bot)) := by
  intro hD2
  apply godel_second_PA_unconditional
  refine PA_proves_of_models fun N e hbot => ?_
  -- from `□_H ⊥` obtain `□_H X` for every `X`, by (D1) and (D2) for `provH`
  have ex : ∀ X, Sat N.M e (box provH X) := fun X =>
    sat_of_PA_proves N (provH_D2 bot X) e
      (sat_of_PA_proves N (provH_D1 (Proves.impI (Proves.botE (Proves.assume PA bot)))) e) hbot
  have h₁ : Sat N.M e (box provF (imp top bot)) :=
    (sat_box_provF N e _).2 ⟨ex _, neg_ne_bot top⟩
  have h₂ : Sat N.M e (box provF top) := (sat_box_provF N e _).2 ⟨ex _, neg_ne_bot bot⟩
  exact ((sat_box_provF N e bot).1 (sat_of_PA_proves N hD2 e h₁ h₂)).2 rfl

/-- **`provF` does not satisfy the derivability conditions over PA.** -/
theorem provF_not_derivability : ¬ Derivability PA provF :=
  fun hD => provF_not_D2 (hD.d2 _ _)

/-- **Feferman's intensionality theorem (example form).** There are two formulas `P`,
`P'` which define the same set in the standard model — namely the set of (codes of)
theorems of PA — such that PA proves the consistency statement `¬P'(⌜⊥⌝)` but not
`¬P(⌜⊥⌝)`. (Here `P = provH`, `P' = provF`.) Gödel's second theorem therefore depends on
the provability formula, not merely on its extension. -/
theorem godel_second_intensional : ∃ P P' : Formula Arith,
    (∀ φ e, Sat stdModel e (box P φ) ↔ PA ⊢₁ φ) ∧ (∀ φ e, Sat stdModel e (box P' φ) ↔ PA ⊢₁ φ) ∧
    ¬ PA ⊢₁ conF P ∧ PA ⊢₁ conF P' :=
  ⟨provH, provF, sat_provH, sat_provF, godel_second_PA_unconditional, PA_proves_conF_provF⟩

end GodelII

end Foundations.Logic.FO
