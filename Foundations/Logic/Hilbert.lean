import Foundations.Logic.NaturalDeduction

/-!
# Hilbert-style axiomatics and its equivalence with natural deduction

Before Gentzen, the standard way to present logic — in Frege's *Begriffsschrift*
(1879), Russell and Whitehead's *Principia Mathematica* (1910–13), and the
Hilbert–Ackermann textbook (1928) — was *axiomatic*: a handful of axiom schemes and
a single rule of inference, *modus ponens*. Such "Hilbert systems" are very
economical (ideal for metatheory) but notoriously awkward to use, because there is
no way to make a temporary assumption.

Our axiom schemes are:
* **K**: `φ → (ψ → φ)` and **S**: `(φ → ψ → χ) → (φ → ψ) → (φ → χ)`
  (the names come from Schönfinkel's and Curry's combinators — a first glimpse of the
  Curry–Howard correspondence between proofs and programs);
* **DNE**: `¬¬φ → φ` (double-negation elimination, making the logic classical);
* three schemes for `∧` and three for `∨` describing their introduction and
  elimination behaviour.

The bridge between the two styles is the **deduction theorem** (Herbrand 1930,
Tarski): if `ψ` is derivable from `Γ ∪ {φ}` then `φ → ψ` is derivable from `Γ`. It
shows that the "make an assumption, then discharge it" step of natural deduction is
admissible in the Hilbert system. With it we prove that the two systems derive
**exactly the same** formulas from the same premises.
-/

namespace Foundations.Logic

open Formula Theory

/-- The axiom schemes of our Hilbert system. -/
inductive HAxiom : Formula → Prop where
  /-- Scheme K: `φ → (ψ → φ)`. -/
  | k (φ ψ) : HAxiom (imp φ (imp ψ φ))
  /-- Scheme S: `(φ → ψ → χ) → (φ → ψ) → φ → χ`. -/
  | s (φ ψ χ) : HAxiom (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  /-- Double-negation elimination: `¬¬φ → φ`. -/
  | dne (φ) : HAxiom (imp (neg (neg φ)) φ)
  /-- `φ ∧ ψ → φ`. -/
  | conjE₁ (φ ψ) : HAxiom (imp (conj φ ψ) φ)
  /-- `φ ∧ ψ → ψ`. -/
  | conjE₂ (φ ψ) : HAxiom (imp (conj φ ψ) ψ)
  /-- `φ → ψ → φ ∧ ψ`. -/
  | conjI (φ ψ) : HAxiom (imp φ (imp ψ (conj φ ψ)))
  /-- `φ → φ ∨ ψ`. -/
  | disjI₁ (φ ψ) : HAxiom (imp φ (disj φ ψ))
  /-- `ψ → φ ∨ ψ`. -/
  | disjI₂ (φ ψ) : HAxiom (imp ψ (disj φ ψ))
  /-- `(φ → χ) → (ψ → χ) → (φ ∨ ψ → χ)`. -/
  | disjE (φ ψ χ) : HAxiom (imp (imp φ χ) (imp (imp ψ χ) (imp (disj φ ψ) χ)))

/-- **Hilbert-style derivability.** `HDerives Γ φ` (written `Γ ⊢ₕ φ`) holds when `φ`
is obtained from premises in `Γ` and axioms by repeated modus ponens. -/
inductive HDerives (Γ : Theory) : Formula → Prop where
  /-- Premises are derivable. -/
  | hyp {φ} : Γ φ → HDerives Γ φ
  /-- Axioms are derivable. -/
  | ax {φ} : HAxiom φ → HDerives Γ φ
  /-- Modus ponens: from `φ → ψ` and `φ` infer `ψ`. -/
  | mp {φ ψ} : HDerives Γ (imp φ ψ) → HDerives Γ φ → HDerives Γ ψ

@[inherit_doc] infix:50 " ⊢ₕ " => HDerives

namespace HDerives

/-- The identity `φ → φ` is derivable in the Hilbert system: the classic five-line
proof `S K K`. -/
theorem identity (Γ : Theory) (φ : Formula) : Γ ⊢ₕ imp φ φ :=
  mp (mp (ax (.s φ (imp φ φ) φ)) (ax (.k φ (imp φ φ)))) (ax (.k φ φ))

/-- **Deduction theorem** (Herbrand, 1930). If `ψ` is derivable from `Γ ∪ {φ}` in the
Hilbert system then `φ → ψ` is derivable from `Γ`. -/
theorem deduction {Γ : Theory} {φ ψ : Formula} (h : insert Γ φ ⊢ₕ ψ) : Γ ⊢ₕ imp φ ψ := by
  induction h with
  | @hyp χ hχ =>
      rcases hχ with rfl | hχ
      · exact identity Γ _
      · exact mp (ax (.k χ φ)) (hyp hχ)
  | @ax χ hχ => exact mp (ax (.k χ φ)) (ax hχ)
  | @mp χ θ _ _ ih₁ ih₂ => exact mp (mp (ax (.s φ χ θ)) ih₁) ih₂

/-- Ex falso in the Hilbert system: from `⊥` derive anything (via K and DNE). -/
theorem botE {Γ : Theory} {φ : Formula} (h : Γ ⊢ₕ bot) : Γ ⊢ₕ φ :=
  mp (ax (.dne φ)) (mp (ax (.k bot (neg φ))) h)

end HDerives

/-- **From natural deduction to Hilbert.** Every natural-deduction derivation can be
translated into a Hilbert-style derivation. -/
theorem Derives.toHilbert {Γ : Theory} {φ : Formula} (h : Γ ⊢ φ) : Γ ⊢ₕ φ := by
  induction h with
  | hyp hφ => exact .hyp hφ
  | impI _ ih => exact HDerives.deduction ih
  | impE _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | conjI _ _ ih₁ ih₂ => exact .mp (.mp (.ax (.conjI _ _)) ih₁) ih₂
  | conjE₁ _ ih => exact .mp (.ax (.conjE₁ _ _)) ih
  | conjE₂ _ ih => exact .mp (.ax (.conjE₂ _ _)) ih
  | disjI₁ _ ih => exact .mp (.ax (.disjI₁ _ _)) ih
  | disjI₂ _ ih => exact .mp (.ax (.disjI₂ _ _)) ih
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
      exact .mp (.mp (.mp (.ax (.disjE _ _ _)) (HDerives.deduction ih₂))
        (HDerives.deduction ih₃)) ih₁
  | botE _ ih => exact HDerives.botE ih
  | raa _ ih => exact .mp (.ax (.dne _)) (HDerives.deduction ih)

/-- Every Hilbert axiom is derivable in natural deduction (from any premises). -/
theorem HAxiom.toND {φ : Formula} (h : HAxiom φ) (Γ : Theory) : Γ ⊢ φ := by
  cases h with
  | k φ ψ => exact Derives.impI (Derives.impI ((Derives.assume _ _).weaken₁ _))
  | s φ ψ χ =>
      refine Derives.impI (Derives.impI (Derives.impI ?_))
      have hφ : insert (insert (insert Γ (imp φ (imp ψ χ))) (imp φ ψ)) φ ⊢ φ := Derives.assume _ _
      have h₁ := ((Derives.assume Γ (imp φ (imp ψ χ))).weaken₁ (imp φ ψ)).weaken₁ φ
      have h₂ := (Derives.assume (insert Γ (imp φ (imp ψ χ))) (imp φ ψ)).weaken₁ φ
      exact Derives.impE (Derives.impE h₁ hφ) (Derives.impE h₂ hφ)
  | dne φ => exact Derives.impI (Derives.dne (Derives.assume _ _))
  | conjE₁ φ ψ => exact Derives.impI (Derives.conjE₁ (Derives.assume _ _))
  | conjE₂ φ ψ => exact Derives.impI (Derives.conjE₂ (Derives.assume _ _))
  | conjI φ ψ => exact Derives.impI (Derives.impI (Derives.conjI ((Derives.assume _ _).weaken₁ _) (Derives.assume _ _)))
  | disjI₁ φ ψ => exact Derives.impI (Derives.disjI₁ (Derives.assume _ _))
  | disjI₂ φ ψ => exact Derives.impI (Derives.disjI₂ (Derives.assume _ _))
  | disjE φ ψ χ =>
      refine Derives.impI (Derives.impI (Derives.impI (Derives.disjE (Derives.assume _ _) ?_ ?_)))
      · exact Derives.impE ((((Derives.assume _ _).weaken₁ _).weaken₁ _).weaken₁ _) (Derives.assume _ _)
      · exact Derives.impE (((Derives.assume _ _).weaken₁ _).weaken₁ _) (Derives.assume _ _)

/-- **From Hilbert to natural deduction.** Every Hilbert-style derivation can be
translated into a natural-deduction derivation. -/
theorem HDerives.toND {Γ : Theory} {φ : Formula} (h : Γ ⊢ₕ φ) : Γ ⊢ φ := by
  induction h with
  | hyp hφ => exact .hyp hφ
  | ax hφ => exact hφ.toND Γ
  | mp _ _ ih₁ ih₂ => exact .impE ih₁ ih₂

/-- **Equivalence of Hilbert and natural deduction.** The two proof systems derive
exactly the same formulas from the same premises. -/
theorem hilbert_iff_nd (Γ : Theory) (φ : Formula) : Γ ⊢ₕ φ ↔ Γ ⊢ φ :=
  ⟨HDerives.toND, Derives.toHilbert⟩

/-- **Soundness of the Hilbert system**, inherited from natural deduction. -/
theorem HDerives.soundness {Γ : Theory} {φ : Formula} (h : Γ ⊢ₕ φ) : Γ ⊨ φ :=
  h.toND.soundness

end Foundations.Logic
