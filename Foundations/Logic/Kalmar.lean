import Foundations.Logic.PropCompleteness

/-!
# Kalmár's proof of completeness for finitely many premises

`PropCompleteness` proved strong completeness abstractly, via maximal consistent
sets and Lindenbaum's lemma. László Kalmár (1935) found a more concrete argument
for the finite case, which literally *turns a truth table into a proof*:

1. **Kalmár's lemma.** Fix a valuation `v` and a list `L` of atoms covering those of
   `φ`. Let `Δ_v` be the "row hypotheses": `p` for each atom `p ∈ L` true under `v`,
   and `¬p` for each false one. Then `Δ_v ⊢ φ` if `φ` is true under `v`, and
   `Δ_v ⊢ ¬φ` otherwise. (Each row of the truth table becomes a derivation.)
2. **Eliminating hypotheses.** If `φ` is a tautology, then `Δ_v ⊢ φ` for *every* row.
   Rows differing only at atom `p` can be merged by the excluded middle `p ∨ ¬p`;
   doing this atom by atom removes all row hypotheses, leaving `⊢ φ`.
3. **Finitely many premises** `γ₁, …, γₙ` are absorbed into the formula
   `γ₁ → ⋯ → γₙ → φ`, which is a tautology whenever `γ₁, …, γₙ ⊨ φ`.

This independent proof of (weak and finite) completeness is a good illustration of
how semantic information (one truth-table row) is converted into syntactic objects
(derivations).
-/

namespace Foundations.Logic

open Formula Theory

/-- `signed b φ` is `φ` if `b` is true and `¬φ` if `b` is false. -/
def signed : Bool → Formula → Formula
  | true, φ => φ
  | false, φ => neg φ

/-- The row hypotheses for valuation `v` over the atoms `L`: the literal `p` or `¬p`
for each `p ∈ L`, according to the value of `p` under `v`. -/
def rowHyps (v : Valuation) (L : List Nat) : Theory :=
  fun ψ => ∃ p ∈ L, ψ = signed (v p) (var p)

/-- The union of two theories. -/
def Theory.union (Γ Δ : Theory) : Theory := fun ψ => Γ ψ ∨ Δ ψ

/-- **Kalmár's lemma.** If the atoms of `φ` lie in `L`, then the row hypotheses for
`v` derive `φ` or `¬φ`, according to whether `φ` is true or false under `v`. -/
theorem kalmar_lemma (v : Valuation) (L : List Nat) :
    ∀ φ : Formula, (∀ a ∈ atoms φ, a ∈ L) → rowHyps v L ⊢ signed (eval v φ) φ
  | bot, _ => Derives.neg_bot _
  | var p, h => Derives.hyp ⟨p, h p (by simp [atoms]), rfl⟩
  | imp a b, h => by
      have ha := kalmar_lemma v L a (fun x hx => h x (by simp [atoms, hx]))
      have hb := kalmar_lemma v L b (fun x hx => h x (by simp [atoms, hx]))
      cases ea : eval v a <;> cases eb : eval v b <;>
        simp only [ea, eb, signed] at ha hb <;> simp only [eval, ea, eb, signed]
      · exact Derives.imp_of_neg ha
      · exact Derives.imp_of_right hb
      · exact Derives.neg_imp ha hb
      · exact Derives.imp_of_right hb
  | conj a b, h => by
      have ha := kalmar_lemma v L a (fun x hx => h x (by simp [atoms, hx]))
      have hb := kalmar_lemma v L b (fun x hx => h x (by simp [atoms, hx]))
      cases ea : eval v a <;> cases eb : eval v b <;>
        simp only [ea, eb, signed] at ha hb <;> simp only [eval, ea, eb, signed]
      · exact Derives.neg_conj₁ ha
      · exact Derives.neg_conj₁ ha
      · exact Derives.neg_conj₂ hb
      · exact Derives.conjI ha hb
  | disj a b, h => by
      have ha := kalmar_lemma v L a (fun x hx => h x (by simp [atoms, hx]))
      have hb := kalmar_lemma v L b (fun x hx => h x (by simp [atoms, hx]))
      cases ea : eval v a <;> cases eb : eval v b <;>
        simp only [ea, eb, signed] at ha hb <;> simp only [eval, ea, eb, signed]
      · exact Derives.neg_disj ha hb
      · exact Derives.disjI₂ hb
      · exact Derives.disjI₁ ha
      · exact Derives.disjI₁ ha

/-- **Eliminating row hypotheses.** If `φ` is derivable from `Γ` together with the
row hypotheses for every valuation, it is derivable from `Γ` alone. Proved by
removing one atom at a time with the excluded middle. -/
theorem eliminate_rows {Γ : Theory} {φ : Formula} :
    ∀ L : List Nat, (∀ v, Γ.union (rowHyps v L) ⊢ φ) → Γ ⊢ φ
  | [], h => (h fun _ => false).weaken fun ψ hψ => by
      rcases hψ with hψ | ⟨p, hp, _⟩
      · exact hψ
      · simp at hp
  | p :: L, h => by
      apply eliminate_rows L
      intro v
      -- Merge the two rows differing only at `p`.
      have key : ∀ b : Bool, (Γ.union (rowHyps v L)).insert (signed b (var p)) ⊢ φ := by
        intro b
        refine (h (Valuation.update v p b)).weaken ?_
        rintro ψ (hψ | ⟨q, hq, rfl⟩)
        · exact Or.inr (Or.inl hψ)
        · by_cases hqp : q = p
          · subst hqp; left; simp [Valuation.update]
          · rcases List.mem_cons.1 hq with rfl | hq
            · exact absurd rfl hqp
            · right; right; exact ⟨q, hq, by simp [Valuation.update, hqp]⟩
      exact Derives.byCases (key true) (key false)

/-- **Weak completeness (Kalmár).** Every tautology is derivable from no premises. -/
theorem kalmar_completeness {φ : Formula} (h : φ.Tautology) : Theory.empty ⊢ φ := by
  apply eliminate_rows (atoms φ)
  intro v
  have := kalmar_lemma v (atoms φ) φ (fun _ ha => ha)
  rw [h v] at this
  exact this.weaken fun ψ hψ => Or.inr hψ

/-- The formula `γ₁ → ⋯ → γₙ → φ` built from a list of premises. -/
def impChain (l : List Formula) (φ : Formula) : Formula := l.foldr imp φ

/-- `γ₁ → ⋯ → γₙ → φ` is true iff `φ` is true whenever all `γᵢ` are. -/
theorem eval_impChain (v : Valuation) (φ : Formula) :
    ∀ l : List Formula, eval v (impChain l φ) = true ↔
      ((∀ ψ ∈ l, eval v ψ = true) → eval v φ = true)
  | [] => by simp [impChain]
  | a :: l => by
      have ih := eval_impChain v φ l
      simp only [impChain, List.foldr_cons] at ih ⊢
      simp only [eval, Bool.or_eq_true, Bool.not_eq_true', ih, List.mem_cons,
        forall_eq_or_imp]
      cases eval v a <;> simp

/-- From `γ₁ → ⋯ → γₙ → φ` and the premises `γᵢ`, modus ponens yields `φ`. -/
theorem derives_of_impChain {φ : Formula} :
    ∀ (l : List Formula) {Δ : Theory}, (∀ ψ ∈ l, Δ ψ) → Δ ⊢ impChain l φ → Δ ⊢ φ
  | [], _, _, h => h
  | a :: l, Δ, hl, h =>
      derives_of_impChain l (fun ψ hψ => hl ψ (by simp [hψ]))
        (Derives.impE h (Derives.hyp (hl a (by simp))))

/-- **Completeness for finitely many premises (Kalmár's method).** If `φ` follows
semantically from the finite list of premises `l`, then it is derivable from them. -/
theorem kalmar_finite_completeness {l : List Formula} {φ : Formula}
    (h : ofList l ⊨ φ) : ofList l ⊢ φ := by
  have taut : (impChain l φ).Tautology := fun v =>
    (eval_impChain v φ l).2 fun hl => h v hl
  exact derives_of_impChain l (fun _ hψ => hψ)
    ((kalmar_completeness taut).weaken (empty_subset _))

end Foundations.Logic
