import Foundations.Logic.FOSemantics

/-!
# First-order natural deduction and its soundness

We extend Gentzen's natural deduction from propositional logic to first-order logic
with equality. Besides the propositional rules (copied from `NaturalDeduction`), the
quantifiers get their own introduction and elimination rules:

* **∀-introduction.** To prove `∀x φ(x)`, prove `φ(x)` for an *arbitrary* `x` — one
  about which the premises say nothing. With de Bruijn indices, "arbitrary" is
  expressed by shifting the premises: they are re-indexed so that they cannot mention
  the fresh variable `0`.
* **∀-elimination.** From `∀x φ(x)` infer `φ(t)` for any term `t`.
* **∃-introduction.** From `φ(t)` infer `∃x φ(x)`.
* **∃-elimination.** From `∃x φ(x)`, and a derivation of `ψ` from `φ(x)` for a fresh
  `x` (not occurring in `ψ` or the other premises), infer `ψ`.
* **Equality** (Leibniz's indiscernibility of identicals): `t = t` always, and from
  `s = t` and `φ(s)` infer `φ(t)`.

The usual side conditions on variables ("eigenvariable conditions"), notoriously
fiddly in textbook presentations, are here enforced automatically by the shifting.

**Soundness**: `Γ ⊢₁ φ → Γ ⊨ φ`. Each rule preserves satisfaction in every structure
under every environment; the quantifier cases rest on the substitution lemma of the
previous file.
-/

namespace Foundations.Logic.FO

variable {L : Signature}

open Formula Theory

/-- **First-order natural deduction.** `Proves Γ φ` (written `Γ ⊢₁ φ`) means that `φ`
has a derivation from premises in `Γ`. -/
inductive Proves : Theory L → Formula L → Prop where
  /-- Hypothesis. -/
  | hyp {Γ φ} : Γ φ → Proves Γ φ
  /-- `→`-introduction. -/
  | impI {Γ φ ψ} : Proves (insert Γ φ) ψ → Proves Γ (imp φ ψ)
  /-- `→`-elimination (modus ponens). -/
  | impE {Γ φ ψ} : Proves Γ (imp φ ψ) → Proves Γ φ → Proves Γ ψ
  /-- `∧`-introduction. -/
  | conjI {Γ φ ψ} : Proves Γ φ → Proves Γ ψ → Proves Γ (conj φ ψ)
  /-- `∧`-elimination, left. -/
  | conjE₁ {Γ φ ψ} : Proves Γ (conj φ ψ) → Proves Γ φ
  /-- `∧`-elimination, right. -/
  | conjE₂ {Γ φ ψ} : Proves Γ (conj φ ψ) → Proves Γ ψ
  /-- `∨`-introduction, left. -/
  | disjI₁ {Γ φ ψ} : Proves Γ φ → Proves Γ (disj φ ψ)
  /-- `∨`-introduction, right. -/
  | disjI₂ {Γ φ ψ} : Proves Γ ψ → Proves Γ (disj φ ψ)
  /-- `∨`-elimination. -/
  | disjE {Γ φ ψ χ} : Proves Γ (disj φ ψ) → Proves (insert Γ φ) χ →
      Proves (insert Γ ψ) χ → Proves Γ χ
  /-- Ex falso quodlibet. -/
  | botE {Γ φ} : Proves Γ bot → Proves Γ φ
  /-- Reductio ad absurdum (classical). -/
  | raa {Γ φ} : Proves (insert Γ (neg φ)) bot → Proves Γ φ
  /-- `∀`-introduction: prove the body for a fresh variable (premises shifted). -/
  | allI {Γ φ} : Proves (shift Γ) φ → Proves Γ (all φ)
  /-- `∀`-elimination: instantiate at any term. -/
  | allE {Γ : Theory L} {φ : Formula L} (t : Term L) : Proves Γ (all φ) → Proves Γ (φ.inst t)
  /-- `∃`-introduction: a witness term gives an existential. -/
  | exI {Γ : Theory L} {φ : Formula L} (t : Term L) : Proves Γ (φ.inst t) → Proves Γ (ex φ)
  /-- `∃`-elimination: reason from a fresh witness to a conclusion not mentioning it. -/
  | exE {Γ : Theory L} {φ ψ : Formula L} : Proves Γ (ex φ) → Proves (insert (shift Γ) φ) ψ.shift → Proves Γ ψ
  /-- Reflexivity of equality. -/
  | refl {Γ} (t : Term L) : Proves Γ (eq t t)
  /-- Substitutivity of equals (Leibniz's law). -/
  | subst {Γ : Theory L} {φ : Formula L} {s t : Term L} : Proves Γ (eq s t) → Proves Γ (φ.inst s) → Proves Γ (φ.inst t)

@[inherit_doc] infix:50 " ⊢₁ " => Proves

namespace Proves

/-- **Weakening** for first-order derivations. -/
theorem weaken {Γ : Theory L} {φ} (h : Γ ⊢₁ φ) : ∀ {Δ}, Γ.Subset Δ → Δ ⊢₁ φ := by
  induction h with
  | hyp hφ => exact fun hs => hyp (hs _ hφ)
  | impI _ ih => exact fun hs => impI (ih (insert_mono hs _))
  | impE _ _ ih₁ ih₂ => exact fun hs => impE (ih₁ hs) (ih₂ hs)
  | conjI _ _ ih₁ ih₂ => exact fun hs => conjI (ih₁ hs) (ih₂ hs)
  | conjE₁ _ ih => exact fun hs => conjE₁ (ih hs)
  | conjE₂ _ ih => exact fun hs => conjE₂ (ih hs)
  | disjI₁ _ ih => exact fun hs => disjI₁ (ih hs)
  | disjI₂ _ ih => exact fun hs => disjI₂ (ih hs)
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
      exact fun hs => disjE (ih₁ hs) (ih₂ (insert_mono hs _)) (ih₃ (insert_mono hs _))
  | botE _ ih => exact fun hs => botE (ih hs)
  | raa _ ih => exact fun hs => raa (ih (insert_mono hs _))
  | allI _ ih => exact fun hs => allI (ih (shift_mono hs))
  | allE t _ ih => exact fun hs => allE t (ih hs)
  | exI t _ ih => exact fun hs => exI t (ih hs)
  | exE _ _ ih₁ ih₂ => exact fun hs => exE (ih₁ hs) (ih₂ (insert_mono (shift_mono hs) _))
  | refl t => exact fun _ => refl t
  | subst _ _ ih₁ ih₂ => exact fun hs => subst (ih₁ hs) (ih₂ hs)

/-- Satisfying `Γ` under `e` gives satisfaction of `shift Γ` under any `x · e`. -/
theorem sat_shift_theory {M : Structure L} {Γ : Theory L} {e : Nat → M.Dom}
    (hΓ : ∀ ψ, Γ ψ → Sat M e ψ) (x : M.Dom) :
    ∀ ψ, shift Γ ψ → Sat M (Env.cons x e) ψ := by
  rintro _ ⟨χ, hχ, rfl⟩
  exact (sat_shift χ e x).2 (hΓ χ hχ)

/-- Satisfaction of an extended theory from satisfaction of its parts. -/
theorem sat_insert {M : Structure L} {Γ : Theory L} {e : Nat → M.Dom} {φ : Formula L}
    (hφ : Sat M e φ) (hΓ : ∀ ψ, Γ ψ → Sat M e ψ) : ∀ ψ, insert Γ φ ψ → Sat M e ψ := by
  rintro ψ (rfl | hψ)
  · exact hφ
  · exact hΓ ψ hψ

/-- **Soundness of first-order natural deduction.** Every derivable formula is a
semantic consequence: `Γ ⊢₁ φ → Γ ⊨ φ`. -/
theorem soundness {Γ : Theory L} {φ : Formula L} (h : Γ ⊢₁ φ) : Entails Γ φ := by
  induction h with
  | hyp hφ => exact fun M e hΓ => hΓ _ hφ
  | impI _ ih => exact fun M e hΓ hφ => ih M e (sat_insert hφ hΓ)
  | impE _ _ ih₁ ih₂ => exact fun M e hΓ => ih₁ M e hΓ (ih₂ M e hΓ)
  | conjI _ _ ih₁ ih₂ => exact fun M e hΓ => ⟨ih₁ M e hΓ, ih₂ M e hΓ⟩
  | conjE₁ _ ih => exact fun M e hΓ => (ih M e hΓ).1
  | conjE₂ _ ih => exact fun M e hΓ => (ih M e hΓ).2
  | disjI₁ _ ih => exact fun M e hΓ => Or.inl (ih M e hΓ)
  | disjI₂ _ ih => exact fun M e hΓ => Or.inr (ih M e hΓ)
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
      intro M e hΓ
      rcases ih₁ M e hΓ with h | h
      · exact ih₂ M e (sat_insert h hΓ)
      · exact ih₃ M e (sat_insert h hΓ)
  | botE _ ih => exact fun M e hΓ => (ih M e hΓ).elim
  | raa _ ih =>
      intro M e hΓ
      exact Classical.byContradiction fun hn => ih M e (sat_insert hn hΓ)
  | allI _ ih => exact fun M e hΓ x => ih M (Env.cons x e) (sat_shift_theory hΓ x)
  | allE t _ ih => exact fun M e hΓ => (sat_inst _ e t).2 (ih M e hΓ _)
  | exI t _ ih => exact fun M e hΓ => ⟨_, (sat_inst _ e t).1 (ih M e hΓ)⟩
  | @exE Γ φ ψ _ _ ih₁ ih₂ =>
      intro M e hΓ
      obtain ⟨x, hx⟩ := ih₁ M e hΓ
      exact (sat_shift ψ e x).1 (ih₂ M (Env.cons x e) (sat_insert hx (sat_shift_theory hΓ x)))
  | refl t => exact fun _ _ _ => rfl
  | @subst Γ φ s t _ _ ih₁ ih₂ =>
      intro M e hΓ
      have h₂ := (sat_inst φ e s).1 (ih₂ M e hΓ)
      rw [ih₁ M e hΓ] at h₂
      exact (sat_inst φ e t).2 h₂

/-- **Consistency of a theory with a model.** If a theory has a model, it does not
derive `⊥`. (Soundness turns the existence of a model into a syntactic fact.) -/
theorem consistent_of_model {Γ : Theory L} (M : Structure L) (e : Nat → M.Dom)
    (hM : IsModel M Γ) : ¬ (Γ ⊢₁ bot) :=
  fun h => soundness h M e (fun ψ hψ => hM ψ hψ e)

/-- Example derivation: `∀x φ(x) → ∃x φ(x)` is derivable for any `φ` (reflecting the
convention that domains are non-empty): instantiate the universal at the variable
`0` and use it as the existential witness. -/
theorem all_imp_ex (Γ : Theory L) (φ : Formula L) : Γ ⊢₁ imp (all φ) (ex φ) :=
  impI (exI (.var 0) (allE (.var 0) (hyp (Or.inl rfl))))

/-- Example derivation: symmetry of equality, `s = t ⊢₁ t = s`, obtained from Leibniz's
law applied to the formula `x = s` (with `s` shifted past the bound variable). -/
theorem eq_symm {Γ : Theory L} {s t : Term L} (h : Γ ⊢₁ eq s t) : Γ ⊢₁ eq t s := by
  have key : ∀ u : Term L,
      (eq (Term.var 0) (s.rename Nat.succ)).inst u = eq u s := by
    intro u
    simp only [Formula.inst, Formula.subst, Term.rename_eq_subst]
    congr 1
    rw [← Term.subst_var s]
    -- substituting into a shifted term composes to the identity
    have comp : ∀ r : Term L, ((r.subst fun n => Term.var (n + 1)).subst (Subst.single u)) = r.subst Term.var := by
      intro r
      induction r with
      | var n => rfl
      | func f ts ih => simp only [Term.subst]; congr; funext i; exact ih i
    rw [comp, Term.subst_var, Term.subst_var]
  have h₁ := Proves.subst (φ := eq (Term.var 0) (s.rename Nat.succ)) h (by rw [key]; exact refl s)
  rwa [key] at h₁

end Proves

end Foundations.Logic.FO
