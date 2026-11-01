import Foundations.Logic.PropSemantics

/-!
# Gentzen's sequent calculus LK

In *Untersuchungen über das logische Schließen* (1934/35) Gerhard Gentzen introduced
two proof systems. The first, **natural deduction** (file `NaturalDeduction`), was
designed to look like actual mathematical reasoning. The second, the **sequent
calculus** `LK` (*L* for *logistisch*, *K* for *klassisch*), was designed for a
different purpose: to make the *structure of proofs themselves* a tractable
mathematical object. It was the instrument with which Gentzen proved his
*Hauptsatz* ("main theorem"), the cut-elimination theorem of the next file.

**Sequents.** A *sequent* `Γ ⊢ Δ` is a pair of finite lists of formulas. It is read:
*if every formula in `Γ` is true, then at least one formula in `Δ` is true* — the
antecedent is read conjunctively, the succedent disjunctively. The empty succedent
is "absurdity"; the empty sequent `⊢` asserts outright contradiction.

**Rules.** Every connective has exactly two rules: one introducing it on the *left*
(how a hypothesis of this form is used) and one introducing it on the *right* (how a
conclusion of this form is established). This perfect left/right symmetry — which
in natural deduction appears as the asymmetry of introduction and elimination — is
the source of the calculus's metamathematical power. We present the rules as a
*table*: for each formula `A`, `leftPremises A` lists the premises (as additions to
the two sides of the sequent) of the left rule for `A`, and `rightPremises A` those
of the right rule (`none` where there is no rule: atoms, and `⊥` on the right).
For example, the left rule for `A → B` has two premises, `Γ ⊢ A, Δ` and
`B, Γ ⊢ Δ`; the left rule for `⊥` has *no* premises at all (`⊥` on the left is an
axiom).

**Formulation.** We follow Kleene's variant (*Introduction to Metamathematics*,
1952) in which the principal formula is *kept* in the premises. Together with
reading sequents up to membership this makes the structural rules of exchange and
contraction invisible, and weakening becomes *admissible* (provable, rather than
postulated) in the cut-free system `CutFree`. The full calculus `LK` adds two rules:
an explicit structural rule of weakening (which, via `⊆`, also covers exchange and
contraction), and the rule of **cut**,

`Γ ⊢ A, Δ    A, Γ ⊢ Δ`
`―――――――――――――――――――`
`      Γ ⊢ Δ`

the sequent-calculus form of using a lemma: prove `A`, then use `A`. Cut is the only
rule whose premises contain a formula (`A`) that has disappeared from the
conclusion. Every other rule is *analytic*: its premises consist of subformulas of
its conclusion.

The main result here is **soundness** of `LK` for the truth-table semantics: every
derivable sequent is valid.
-/

namespace Foundations.Logic.Sequent

open Formula

/-- The premises of the **left rule** for a formula `A`, as a list of pairs
`(L, R)`: each pair stands for the premise `L ++ Γ ⊢ R ++ Δ` of a conclusion
`Γ ⊢ Δ` with `A ∈ Γ`. The value is `none` when there is no left rule (atoms).
`⊥` has a left rule with *no* premises. -/
def leftPremises : Formula → Option (List (List Formula × List Formula))
  | bot => some []
  | var _ => none
  | imp A B => some [([], [A]), ([B], [])]
  | conj A B => some [([A, B], [])]
  | disj A B => some [([A], []), ([B], [])]

/-- The premises of the **right rule** for a formula `A`, as a list of pairs
`(L, R)`: each pair stands for the premise `L ++ Γ ⊢ R ++ Δ` of a conclusion
`Γ ⊢ Δ` with `A ∈ Δ`. The value is `none` when there is no right rule (atoms and
`⊥`). -/
def rightPremises : Formula → Option (List (List Formula × List Formula))
  | bot => none
  | var _ => none
  | imp A B => some [([A], [B])]
  | conj A B => some [([], [A]), ([], [B])]
  | disj A B => some [([], [A, B])]

/-- **The cut-free sequent calculus.** `CutFree Γ Δ` holds when the sequent `Γ ⊢ Δ`
has a derivation using only the identity axiom and the left and right rules of the
connectives — no cut, and no structural rules. -/
inductive CutFree : List Formula → List Formula → Prop where
  /-- Identity: `Γ ⊢ Δ` whenever some formula occurs on both sides. -/
  | ax {Γ Δ : List Formula} {A : Formula} : A ∈ Γ → A ∈ Δ → CutFree Γ Δ
  /-- The left rule for a formula `A` occurring in the antecedent. -/
  | left {Γ Δ : List Formula} {A : Formula} {ps : List (List Formula × List Formula)} :
      A ∈ Γ → leftPremises A = some ps →
      (∀ p ∈ ps, CutFree (p.1 ++ Γ) (p.2 ++ Δ)) → CutFree Γ Δ
  /-- The right rule for a formula `A` occurring in the succedent. -/
  | right {Γ Δ : List Formula} {A : Formula} {ps : List (List Formula × List Formula)} :
      A ∈ Δ → rightPremises A = some ps →
      (∀ p ∈ ps, CutFree (p.1 ++ Γ) (p.2 ++ Δ)) → CutFree Γ Δ

/-- **The sequent calculus LK.** `LK Γ Δ` holds when `Γ ⊢ Δ` is derivable with the
identity axiom, the logical rules, the structural rule (weakening, which also
absorbs exchange and contraction since sequents are compared by `⊆`), and **cut**. -/
inductive LK : List Formula → List Formula → Prop where
  /-- Identity: `Γ ⊢ Δ` whenever some formula occurs on both sides. -/
  | ax {Γ Δ : List Formula} {A : Formula} : A ∈ Γ → A ∈ Δ → LK Γ Δ
  /-- The left rule for a formula `A` occurring in the antecedent. -/
  | left {Γ Δ : List Formula} {A : Formula} {ps : List (List Formula × List Formula)} :
      A ∈ Γ → leftPremises A = some ps → (∀ p ∈ ps, LK (p.1 ++ Γ) (p.2 ++ Δ)) → LK Γ Δ
  /-- The right rule for a formula `A` occurring in the succedent. -/
  | right {Γ Δ : List Formula} {A : Formula} {ps : List (List Formula × List Formula)} :
      A ∈ Δ → rightPremises A = some ps → (∀ p ∈ ps, LK (p.1 ++ Γ) (p.2 ++ Δ)) → LK Γ Δ
  /-- Structural rule: weakening (and, implicitly, exchange and contraction). -/
  | weak {Γ Δ Γ' Δ' : List Formula} : LK Γ Δ → Γ ⊆ Γ' → Δ ⊆ Δ' → LK Γ' Δ'
  /-- **Cut**: from `Γ ⊢ A, Δ` and `A, Γ ⊢ Δ` infer `Γ ⊢ Δ`. -/
  | cut {Γ Δ : List Formula} (A : Formula) : LK Γ (A :: Δ) → LK (A :: Γ) Δ → LK Γ Δ

/-! ## The familiar rules, one by one

The table-driven constructors are convenient for uniform proofs; here are the rules
in their textbook shape (with the principal formula kept, Kleene-style). -/

namespace CutFree

/-- `⊥`-left: a sequent with `⊥` in the antecedent is an axiom. -/
theorem botL {Γ Δ} (h : bot ∈ Γ) : CutFree Γ Δ := left h rfl (by simp)

/-- `→`-left: from `Γ ⊢ A, Δ` and `B, Γ ⊢ Δ` infer `Γ ⊢ Δ` when `A → B ∈ Γ`. -/
theorem impL {Γ Δ A B} (h : imp A B ∈ Γ) (h₁ : CutFree Γ (A :: Δ))
    (h₂ : CutFree (B :: Γ) Δ) : CutFree Γ Δ :=
  left h rfl (by simp [h₁, h₂])

/-- `→`-right: from `A, Γ ⊢ B, Δ` infer `Γ ⊢ Δ` when `A → B ∈ Δ`. -/
theorem impR {Γ Δ A B} (h : imp A B ∈ Δ) (h₁ : CutFree (A :: Γ) (B :: Δ)) :
    CutFree Γ Δ :=
  right h rfl (by simp [h₁])

/-- `∧`-left: from `A, B, Γ ⊢ Δ` infer `Γ ⊢ Δ` when `A ∧ B ∈ Γ`. -/
theorem conjL {Γ Δ A B} (h : conj A B ∈ Γ) (h₁ : CutFree (A :: B :: Γ) Δ) :
    CutFree Γ Δ :=
  left h rfl (by simp [h₁])

/-- `∧`-right: from `Γ ⊢ A, Δ` and `Γ ⊢ B, Δ` infer `Γ ⊢ Δ` when `A ∧ B ∈ Δ`. -/
theorem conjR {Γ Δ A B} (h : conj A B ∈ Δ) (h₁ : CutFree Γ (A :: Δ))
    (h₂ : CutFree Γ (B :: Δ)) : CutFree Γ Δ :=
  right h rfl (by simp [h₁, h₂])

/-- `∨`-left: from `A, Γ ⊢ Δ` and `B, Γ ⊢ Δ` infer `Γ ⊢ Δ` when `A ∨ B ∈ Γ`. -/
theorem disjL {Γ Δ A B} (h : disj A B ∈ Γ) (h₁ : CutFree (A :: Γ) Δ)
    (h₂ : CutFree (B :: Γ) Δ) : CutFree Γ Δ :=
  left h rfl (by simp [h₁, h₂])

/-- `∨`-right: from `Γ ⊢ A, B, Δ` infer `Γ ⊢ Δ` when `A ∨ B ∈ Δ`. -/
theorem disjR {Γ Δ A B} (h : disj A B ∈ Δ) (h₁ : CutFree Γ (A :: B :: Δ)) :
    CutFree Γ Δ :=
  right h rfl (by simp [h₁])

/-- **Admissibility of weakening** (and of exchange and contraction). If `Γ ⊢ Δ` has
a cut-free derivation, so does every `Γ' ⊢ Δ'` with `Γ ⊆ Γ'` and `Δ ⊆ Δ'`: the
same derivation tree works, with larger contexts throughout. -/
theorem weaken {Γ Δ} (h : CutFree Γ Δ) : ∀ {Γ' Δ'}, Γ ⊆ Γ' → Δ ⊆ Δ' → CutFree Γ' Δ' := by
  induction h with
  | ax h₁ h₂ => exact fun hΓ hΔ => ax (hΓ h₁) (hΔ h₂)
  | left hA hps _ ih =>
      exact fun hΓ hΔ => left (hΓ hA) hps (fun p hp => ih p hp (by grind) (by grind))
  | right hA hps _ ih =>
      exact fun hΓ hΔ => right (hΔ hA) hps (fun p hp => ih p hp (by grind) (by grind))

/-- Every cut-free derivation is an `LK` derivation. -/
theorem toLK {Γ Δ} (h : CutFree Γ Δ) : LK Γ Δ := by
  induction h with
  | ax h₁ h₂ => exact .ax h₁ h₂
  | left hA hps _ ih => exact .left hA hps ih
  | right hA hps _ ih => exact .right hA hps ih

end CutFree

namespace LK

/-- `⊥`-left in `LK`. -/
theorem botL {Γ Δ} (h : bot ∈ Γ) : LK Γ Δ := (CutFree.botL h).toLK

/-- `→`-left in `LK`. -/
theorem impL {Γ Δ A B} (h : imp A B ∈ Γ) (h₁ : LK Γ (A :: Δ)) (h₂ : LK (B :: Γ) Δ) :
    LK Γ Δ :=
  left h rfl (by simp [h₁, h₂])

/-- `→`-right in `LK`. -/
theorem impR {Γ Δ A B} (h : imp A B ∈ Δ) (h₁ : LK (A :: Γ) (B :: Δ)) : LK Γ Δ :=
  right h rfl (by simp [h₁])

/-- `∧`-left in `LK`. -/
theorem conjL {Γ Δ A B} (h : conj A B ∈ Γ) (h₁ : LK (A :: B :: Γ) Δ) : LK Γ Δ :=
  left h rfl (by simp [h₁])

/-- `∧`-right in `LK`. -/
theorem conjR {Γ Δ A B} (h : conj A B ∈ Δ) (h₁ : LK Γ (A :: Δ)) (h₂ : LK Γ (B :: Δ)) :
    LK Γ Δ :=
  right h rfl (by simp [h₁, h₂])

/-- `∨`-left in `LK`. -/
theorem disjL {Γ Δ A B} (h : disj A B ∈ Γ) (h₁ : LK (A :: Γ) Δ) (h₂ : LK (B :: Γ) Δ) :
    LK Γ Δ :=
  left h rfl (by simp [h₁, h₂])

/-- `∨`-right in `LK`. -/
theorem disjR {Γ Δ A B} (h : disj A B ∈ Δ) (h₁ : LK Γ (A :: B :: Δ)) : LK Γ Δ :=
  right h rfl (by simp [h₁])

/-- Identity on a formula: `A ⊢ A`. -/
theorem id (A : Formula) : LK [A] [A] := ax (A := A) (by simp) (by simp)

end LK

/-! ## Semantics and soundness -/

/-- **Validity of a sequent.** `Γ ⊢ Δ` is valid when every valuation making all
formulas of `Γ` true makes some formula of `Δ` true. -/
def Valid (Γ Δ : List Formula) : Prop :=
  ∀ v : Valuation, (∀ A ∈ Γ, A.eval v = true) → ∃ B ∈ Δ, B.eval v = true

/-- **Meaning of the left rules.** If `A` has a left rule with premises `ps`, then
`A` is true under `v` exactly when some premise `(L, R)` is "selected" by `v`: all of
`L` true and all of `R` false. -/
theorem left_sem {A : Formula} {ps} (h : leftPremises A = some ps) (v : Valuation) :
    A.eval v = true ↔
      ∃ p ∈ ps, (∀ B ∈ p.1, B.eval v = true) ∧ (∀ B ∈ p.2, B.eval v = false) := by
  cases A <;> simp [leftPremises] at h <;> subst h <;> simp [eval]

/-- **Meaning of the right rules.** If `A` has a right rule with premises `ps`, then
`A` is false under `v` exactly when some premise `(L, R)` is selected by `v`: all of
`L` true and all of `R` false. -/
theorem right_sem {A : Formula} {ps} (h : rightPremises A = some ps) (v : Valuation) :
    A.eval v = false ↔
      ∃ p ∈ ps, (∀ B ∈ p.1, B.eval v = true) ∧ (∀ B ∈ p.2, B.eval v = false) := by
  cases A <;> simp [rightPremises] at h <;> subst h <;> simp [eval] <;>
    cases eval v _ <;> simp

/-- **Soundness of LK.** Every sequent derivable in `LK` (with cut) is valid. -/
theorem LK.sound {Γ Δ} (h : LK Γ Δ) : Valid Γ Δ := by
  induction h with
  | ax h₁ h₂ => exact fun v hv => ⟨_, h₂, hv _ h₁⟩
  | @left Γ Δ A ps hA hps _ ih =>
      intro v hv
      obtain ⟨p, hp, hL, hR⟩ := (left_sem hps v).1 (hv A hA)
      obtain ⟨B, hB, hBv⟩ := ih p hp v (by
        intro C hC
        rcases List.mem_append.1 hC with hC | hC
        · exact hL C hC
        · exact hv C hC)
      rcases List.mem_append.1 hB with hB' | hB'
      · simp [hR B hB'] at hBv
      · exact ⟨B, hB', hBv⟩
  | @right Γ Δ A ps hA hps _ ih =>
      intro v hv
      cases hAv : A.eval v with
      | true => exact ⟨A, hA, hAv⟩
      | false =>
          obtain ⟨p, hp, hL, hR⟩ := (right_sem hps v).1 hAv
          obtain ⟨B, hB, hBv⟩ := ih p hp v (by
            intro C hC
            rcases List.mem_append.1 hC with hC | hC
            · exact hL C hC
            · exact hv C hC)
          rcases List.mem_append.1 hB with hB' | hB'
          · simp [hR B hB'] at hBv
          · exact ⟨B, hB', hBv⟩
  | weak _ hΓ hΔ ih =>
      intro v hv
      obtain ⟨B, hB, hBv⟩ := ih v (fun C hC => hv C (hΓ hC))
      exact ⟨B, hΔ hB, hBv⟩
  | @cut Γ Δ A _ _ ih₁ ih₂ =>
      intro v hv
      cases hAv : A.eval v with
      | true =>
          exact ih₂ v (fun C hC => by
            rcases List.mem_cons.1 hC with rfl | hC
            · exact hAv
            · exact hv C hC)
      | false =>
          obtain ⟨B, hB, hBv⟩ := ih₁ v hv
          rcases List.mem_cons.1 hB with rfl | hB
          · simp [hAv] at hBv
          · exact ⟨B, hB, hBv⟩

/-- Soundness for cut-free derivations. -/
theorem CutFree.sound {Γ Δ} (h : CutFree Γ Δ) : Valid Γ Δ := h.toLK.sound

/-- A formula provable in `LK` (as the sequent `⊢ A`) is a tautology. -/
theorem LK.tautology_of_proves {A : Formula} (h : LK [] [A]) : A.Tautology := by
  intro v
  obtain ⟨B, hB, hBv⟩ := h.sound v (by simp)
  simp at hB
  exact hB ▸ hBv

/-- The empty sequent is not valid. -/
theorem not_valid_empty : ¬ Valid [] [] := by
  intro h
  obtain ⟨_, hB, _⟩ := h (fun _ => false) (by simp)
  simp at hB

/-! ## Examples -/

/-- The law of excluded middle `⊢ p ∨ ¬p`, by a cut-free derivation: `∨`-right,
then `→`-right, then identity on `p`. -/
example : CutFree [] [disj (var 0) (neg (var 0))] :=
  CutFree.disjR (List.mem_singleton_self _)
    (CutFree.impR (A := var 0) (B := bot) (by simp [neg])
      (CutFree.ax (A := var 0) (by simp) (by simp)))

/-- Peirce's law `⊢ ((p → q) → p) → p`, a cut-free derivation: the multiple
succedent is what lets classical laws be proved without any special rule. -/
example : CutFree [] [imp (imp (imp (var 0) (var 1)) (var 0)) (var 0)] := by
  refine CutFree.impR (List.mem_singleton_self _) ?_
  refine CutFree.impL (A := imp (var 0) (var 1)) (B := var 0) (by simp) ?_ ?_
  · refine CutFree.impR (A := var 0) (B := var 1) (by simp) ?_
    exact CutFree.ax (A := var 0) (by simp) (by simp)
  · exact CutFree.ax (A := var 0) (by simp) (by simp)

end Foundations.Logic.Sequent
