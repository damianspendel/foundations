import Foundations.Logic.PropSemantics

/-!
# Natural deduction and its soundness

Semantics defines "follows from" by quantifying over all valuations; a *proof
system* defines it by finite, checkable chains of inference. Gerhard Gentzen
(*Untersuchungen über das logische Schließen*, 1934–35), and independently
Stanisław Jaśkowski, introduced **natural deduction**, designed to mirror how
mathematicians actually reason: each connective comes with *introduction* rules
(how to prove it) and *elimination* rules (how to use it), and hypotheses can be
assumed temporarily and then *discharged* (as in "assume φ … hence φ → ψ").

We formalise derivability as an inductive predicate `Γ ⊢ φ` ("φ is derivable from
premises Γ"): a derivation is literally a finite tree of rule applications. The
rules are intuitionistic natural deduction (intro/elim rules plus *ex falso
quodlibet*) together with one classical rule, *reductio ad absurdum*: if assuming
`¬φ` leads to `⊥`, conclude `φ`.

The main result is **soundness**: `Γ ⊢ φ → Γ ⊨ φ`. Every derivable formula is a
semantic consequence — the rules never lead from truths to falsehoods. (The converse,
completeness, is much deeper and is proved in `PropCompleteness`.) We also prove
weakening, a few derived rules, and the *finiteness* of derivations: any derivation
uses only finitely many premises, the syntactic root of compactness.
-/

namespace Foundations.Logic

open Formula Theory

/-- **Natural deduction.** `Derives Γ φ` (written `Γ ⊢ φ`) holds when there is a
natural-deduction derivation of `φ` whose undischarged hypotheses all lie in `Γ`. -/
inductive Derives : Theory → Formula → Prop where
  /-- Hypothesis: any premise may be used. -/
  | hyp {Γ φ} : Γ φ → Derives Γ φ
  /-- `→`-introduction (conditional proof): discharge the assumption `φ`. -/
  | impI {Γ φ ψ} : Derives (insert Γ φ) ψ → Derives Γ (imp φ ψ)
  /-- `→`-elimination (modus ponens). -/
  | impE {Γ φ ψ} : Derives Γ (imp φ ψ) → Derives Γ φ → Derives Γ ψ
  /-- `∧`-introduction. -/
  | conjI {Γ φ ψ} : Derives Γ φ → Derives Γ ψ → Derives Γ (conj φ ψ)
  /-- `∧`-elimination, left. -/
  | conjE₁ {Γ φ ψ} : Derives Γ (conj φ ψ) → Derives Γ φ
  /-- `∧`-elimination, right. -/
  | conjE₂ {Γ φ ψ} : Derives Γ (conj φ ψ) → Derives Γ ψ
  /-- `∨`-introduction, left. -/
  | disjI₁ {Γ φ ψ} : Derives Γ φ → Derives Γ (disj φ ψ)
  /-- `∨`-introduction, right. -/
  | disjI₂ {Γ φ ψ} : Derives Γ ψ → Derives Γ (disj φ ψ)
  /-- `∨`-elimination (proof by cases), discharging `φ` resp. `ψ`. -/
  | disjE {Γ φ ψ χ} : Derives Γ (disj φ ψ) → Derives (insert Γ φ) χ →
      Derives (insert Γ ψ) χ → Derives Γ χ
  /-- Ex falso quodlibet: from absurdity, anything. -/
  | botE {Γ φ} : Derives Γ bot → Derives Γ φ
  /-- Reductio ad absurdum (the classical rule): if `¬φ` leads to `⊥`, infer `φ`. -/
  | raa {Γ φ} : Derives (insert Γ (neg φ)) bot → Derives Γ φ

@[inherit_doc] infix:50 " ⊢ " => Derives

namespace Derives

/-- **Weakening.** Adding premises never destroys a derivation. -/
theorem weaken {Γ φ} (h : Γ ⊢ φ) : ∀ {Δ}, Γ.Subset Δ → Δ ⊢ φ := by
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

/-- The newly added premise is derivable. -/
theorem assume (Γ : Theory) (φ : Formula) : insert Γ φ ⊢ φ := hyp (Or.inl rfl)

/-- Weakening by a single extra premise. -/
theorem weaken₁ {Γ φ} (h : Γ ⊢ φ) (ψ : Formula) : insert Γ ψ ⊢ φ :=
  h.weaken (subset_insert Γ ψ)

/-- Cut: a derived formula may be used as a lemma. -/
theorem cut {Γ φ ψ} (h₁ : Γ ⊢ φ) (h₂ : insert Γ φ ⊢ ψ) : Γ ⊢ ψ := impE (impI h₂) h₁

/-- `¬`-elimination: `φ` and `¬φ` together give `⊥`. -/
theorem negE {Γ φ} (h₁ : Γ ⊢ neg φ) (h₂ : Γ ⊢ φ) : Γ ⊢ bot := impE h₁ h₂

/-- `¬`-introduction: if `φ` leads to `⊥`, infer `¬φ`. -/
theorem negI {Γ φ} (h : insert Γ φ ⊢ bot) : Γ ⊢ neg φ := impI h

/-- Double-negation elimination, derived from reductio. -/
theorem dne {Γ φ} (h : Γ ⊢ neg (neg φ)) : Γ ⊢ φ :=
  raa (negE (h.weaken₁ _) (assume _ _))

/-- The law of excluded middle `φ ∨ ¬φ` is derivable (classically). -/
theorem lem (Γ : Theory) (φ : Formula) : Γ ⊢ disj φ (neg φ) := by
  apply raa
  apply negE (assume _ _)
  apply disjI₂
  apply negI
  apply negE ((assume _ _).weaken₁ _)
  exact disjI₁ (assume _ _)

/-- Proof by cases on `φ`: if `χ` follows both from `φ` and from `¬φ`, it follows
outright. -/
theorem byCases {Γ φ χ} (h₁ : insert Γ φ ⊢ χ) (h₂ : insert Γ (neg φ) ⊢ χ) : Γ ⊢ χ :=
  disjE (lem Γ φ) h₁ h₂

/-- From `¬φ` infer `φ → ψ` (a false antecedent makes an implication true). -/
theorem imp_of_neg {Γ φ ψ} (h : Γ ⊢ neg φ) : Γ ⊢ imp φ ψ :=
  impI (botE (negE (h.weaken₁ _) (assume _ _)))

/-- From `ψ` infer `φ → ψ`. -/
theorem imp_of_right {Γ φ ψ} (h : Γ ⊢ ψ) : Γ ⊢ imp φ ψ := impI (h.weaken₁ _)

/-- From `φ` and `¬ψ` infer `¬(φ → ψ)`. -/
theorem neg_imp {Γ φ ψ} (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ neg ψ) : Γ ⊢ neg (imp φ ψ) :=
  negI (negE (h₂.weaken₁ _) (impE (assume _ _) (h₁.weaken₁ _)))

/-- From `¬φ` infer `¬(φ ∧ ψ)`. -/
theorem neg_conj₁ {Γ φ ψ} (h : Γ ⊢ neg φ) : Γ ⊢ neg (conj φ ψ) :=
  negI (negE (h.weaken₁ _) (conjE₁ (assume _ _)))

/-- From `¬ψ` infer `¬(φ ∧ ψ)`. -/
theorem neg_conj₂ {Γ φ ψ} (h : Γ ⊢ neg ψ) : Γ ⊢ neg (conj φ ψ) :=
  negI (negE (h.weaken₁ _) (conjE₂ (assume _ _)))

/-- From `¬φ` and `¬ψ` infer `¬(φ ∨ ψ)`. -/
theorem neg_disj {Γ φ ψ} (h₁ : Γ ⊢ neg φ) (h₂ : Γ ⊢ neg ψ) : Γ ⊢ neg (disj φ ψ) :=
  negI (disjE (assume _ _)
    (negE ((h₁.weaken₁ _).weaken₁ _) (assume _ _))
    (negE ((h₂.weaken₁ _).weaken₁ _) (assume _ _)))

/-- `¬⊥` is derivable from no premises. -/
theorem neg_bot (Γ : Theory) : Γ ⊢ neg bot := negI (assume _ _)

/-- **Deduction theorem (natural deduction form).** `Γ ∪ {φ} ⊢ ψ` iff `Γ ⊢ φ → ψ`. -/
theorem deduction {Γ φ ψ} : insert Γ φ ⊢ ψ ↔ Γ ⊢ imp φ ψ :=
  ⟨impI, fun h => impE (h.weaken₁ _) (assume _ _)⟩

/-- **Soundness of natural deduction.** Every formula derivable from `Γ` is a
semantic consequence of `Γ`: `Γ ⊢ φ → Γ ⊨ φ`. The proof checks that each rule
preserves truth under any valuation satisfying the open hypotheses. -/
theorem soundness {Γ φ} (h : Γ ⊢ φ) : Γ ⊨ φ := by
  induction h with
  | hyp hφ => exact fun v hv => hv _ hφ
  | @impI Γ φ ψ _ ih =>
      intro v hv
      cases hφ : eval v φ with
      | false => simp [eval, hφ]
      | true =>
          have := ih v (fun χ hχ => by
            rcases hχ with rfl | hχ
            · exact hφ
            · exact hv χ hχ)
          simp [eval, this]
  | impE _ _ ih₁ ih₂ =>
      intro v hv
      have h₁ := ih₁ v hv
      have h₂ := ih₂ v hv
      simp only [eval, h₂, Bool.not_true, Bool.false_or] at h₁
      exact h₁
  | conjI _ _ ih₁ ih₂ => intro v hv; simp [eval, ih₁ v hv, ih₂ v hv]
  | conjE₁ _ ih =>
      intro v hv; have := ih v hv; simp only [eval, Bool.and_eq_true] at this; exact this.1
  | conjE₂ _ ih =>
      intro v hv; have := ih v hv; simp only [eval, Bool.and_eq_true] at this; exact this.2
  | disjI₁ _ ih => intro v hv; simp [eval, ih v hv]
  | disjI₂ _ ih => intro v hv; simp [eval, ih v hv]
  | @disjE Γ φ ψ χ _ _ _ ih₁ ih₂ ih₃ =>
      intro v hv
      have h₁ := ih₁ v hv
      simp only [eval, Bool.or_eq_true] at h₁
      rcases h₁ with h₁ | h₁
      · exact ih₂ v (fun θ hθ => by rcases hθ with rfl | hθ; exact h₁; exact hv θ hθ)
      · exact ih₃ v (fun θ hθ => by rcases hθ with rfl | hθ; exact h₁; exact hv θ hθ)
  | botE _ ih => intro v hv; exact absurd (ih v hv) (by simp [eval])
  | @raa Γ φ _ ih =>
      intro v hv
      cases hφ : eval v φ with
      | true => rfl
      | false =>
          have := ih v (fun χ hχ => by
            rcases hχ with rfl | hχ
            · simp [hφ]
            · exact hv χ hχ)
          simp [eval] at this

/-- **Finiteness of derivations.** Any derivation from `Γ` uses only finitely many
premises: there is a finite list `L` of premises of `Γ` with `L ⊢ φ`. -/
theorem finite_premises {Γ φ} (h : Γ ⊢ φ) :
    ∃ L : List Formula, (∀ ψ ∈ L, Γ ψ) ∧ ofList L ⊢ φ := by
  -- Helper: discharge a hypothesis `θ` from a finite list of premises of `insert Γ θ`.
  have drop : ∀ {Γ : Theory} {θ : Formula} (L : List Formula), (∀ ψ ∈ L, insert Γ θ ψ) →
      (∀ ψ ∈ L.filter (· ≠ θ), Γ ψ) ∧ (ofList L).Subset (insert (ofList (L.filter (· ≠ θ))) θ) := by
    intro Γ θ L hL
    constructor
    · intro ψ hψ
      simp only [List.mem_filter, decide_eq_true_eq] at hψ
      rcases hL ψ hψ.1 with h | h
      · exact absurd h hψ.2
      · exact h
    · intro ψ hψ
      by_cases e : ψ = θ
      · exact Or.inl e
      · exact Or.inr (by simp [ofList, List.mem_filter]; exact ⟨hψ, e⟩)
  have sub_append_l : ∀ L₁ L₂ : List Formula, (ofList L₁).Subset (ofList (L₁ ++ L₂)) :=
    fun L₁ L₂ ψ hψ => List.mem_append_left L₂ hψ
  have sub_append_r : ∀ L₁ L₂ : List Formula, (ofList L₂).Subset (ofList (L₁ ++ L₂)) :=
    fun L₁ L₂ ψ hψ => List.mem_append_right L₁ hψ
  have all_append : ∀ {Γ : Theory} (L₁ L₂ : List Formula), (∀ ψ ∈ L₁, Γ ψ) →
      (∀ ψ ∈ L₂, Γ ψ) → ∀ ψ ∈ L₁ ++ L₂, Γ ψ := by
    intro Γ L₁ L₂ h₁ h₂ ψ hψ
    rcases List.mem_append.1 hψ with h | h
    · exact h₁ ψ h
    · exact h₂ ψ h
  induction h with
  | @hyp Γ φ hφ => exact ⟨[φ], by simpa using hφ, hyp (by simp [ofList])⟩
  | @impI Γ φ ψ _ ih =>
      obtain ⟨L, hL, hd⟩ := ih
      obtain ⟨h₁, h₂⟩ := drop L hL
      exact ⟨_, h₁, impI (hd.weaken h₂)⟩
  | impE _ _ ih₁ ih₂ =>
      obtain ⟨L₁, hL₁, hd₁⟩ := ih₁
      obtain ⟨L₂, hL₂, hd₂⟩ := ih₂
      exact ⟨L₁ ++ L₂, all_append _ _ hL₁ hL₂,
        impE (hd₁.weaken (sub_append_l _ _)) (hd₂.weaken (sub_append_r _ _))⟩
  | conjI _ _ ih₁ ih₂ =>
      obtain ⟨L₁, hL₁, hd₁⟩ := ih₁
      obtain ⟨L₂, hL₂, hd₂⟩ := ih₂
      exact ⟨L₁ ++ L₂, all_append _ _ hL₁ hL₂,
        conjI (hd₁.weaken (sub_append_l _ _)) (hd₂.weaken (sub_append_r _ _))⟩
  | conjE₁ _ ih => obtain ⟨L, hL, hd⟩ := ih; exact ⟨L, hL, conjE₁ hd⟩
  | conjE₂ _ ih => obtain ⟨L, hL, hd⟩ := ih; exact ⟨L, hL, conjE₂ hd⟩
  | disjI₁ _ ih => obtain ⟨L, hL, hd⟩ := ih; exact ⟨L, hL, disjI₁ hd⟩
  | disjI₂ _ ih => obtain ⟨L, hL, hd⟩ := ih; exact ⟨L, hL, disjI₂ hd⟩
  | @disjE Γ φ ψ χ _ _ _ ih₁ ih₂ ih₃ =>
      obtain ⟨L₁, hL₁, hd₁⟩ := ih₁
      obtain ⟨L₂, hL₂, hd₂⟩ := ih₂
      obtain ⟨L₃, hL₃, hd₃⟩ := ih₃
      obtain ⟨h₂a, h₂b⟩ := drop L₂ hL₂
      obtain ⟨h₃a, h₃b⟩ := drop L₃ hL₃
      refine ⟨L₁ ++ (L₂.filter (· ≠ φ) ++ L₃.filter (· ≠ ψ)),
        all_append _ _ hL₁ (all_append _ _ h₂a h₃a), ?_⟩
      refine disjE (hd₁.weaken (sub_append_l _ _)) (hd₂.weaken ?_) (hd₃.weaken ?_)
      · exact h₂b.trans (insert_mono ((sub_append_l _ _).trans (sub_append_r _ _)) _)
      · exact h₃b.trans (insert_mono ((sub_append_r _ _).trans (sub_append_r _ _)) _)
  | botE _ ih => obtain ⟨L, hL, hd⟩ := ih; exact ⟨L, hL, botE hd⟩
  | @raa Γ φ _ ih =>
      obtain ⟨L, hL, hd⟩ := ih
      obtain ⟨h₁, h₂⟩ := drop L hL
      exact ⟨_, h₁, raa (hd.weaken h₂)⟩

end Derives

end Foundations.Logic
