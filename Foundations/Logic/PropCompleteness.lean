import Foundations.Logic.Hilbert

/-!
# Completeness and compactness of propositional logic

Soundness says the rules prove nothing false. **Completeness** is the converse:
whatever follows semantically can actually be *proved* — `Γ ⊨ φ → Γ ⊢ φ`. For
propositional logic this was first established by Paul Bernays (1918, in his
Habilitationsschrift) and Emil Post (1921); László Kalmár (1935) gave the elegant
truth-table-based proof for finitely many premises. Here we prove the *strong*
form, for arbitrary (even infinite) sets of premises, by the method that Leon
Henkin (1949) devised for first-order logic, resting on **Lindenbaum's lemma**
(reported by Tarski, 1930):

1. A theory is *consistent* if it does not derive `⊥`.
2. **Lindenbaum's lemma.** Every consistent theory extends to a *maximal*
   consistent one, which "decides" every formula. We enumerate all formulas
   (via the finite lists `allUpTo n`, which exhaust the formulas) and add each in
   turn whenever this keeps the theory consistent.
3. **Truth lemma.** A maximal consistent theory `M` describes a valuation: make an
   atom true iff it belongs to `M`. Then *every* formula is true iff it belongs to `M`.
4. Hence every consistent theory is satisfiable (*model existence*), and
   completeness follows by reductio: if `Γ ⊬ φ` then `Γ ∪ {¬φ}` is consistent,
   hence satisfiable, so `Γ ⊭ φ`.

Combined with the finiteness of derivations, completeness yields **compactness**:
if every finite subset of `Γ` is satisfiable, so is `Γ` — a purely semantic fact
proved by a detour through syntax. Finally, since tautologyhood is decidable by truth
tables, so is provability from no premises.
-/

namespace Foundations.Logic

open Formula Theory

/-- A theory is **consistent** if it does not derive `⊥`. -/
def Consistent (Γ : Theory) : Prop := ¬ (Γ ⊢ bot)

/-- A theory is **maximal consistent** if it is consistent and cannot be consistently
extended by any formula it does not already contain. -/
def MaximalConsistent (M : Theory) : Prop :=
  Consistent M ∧ ∀ φ, M φ ∨ ¬ Consistent (insert M φ)

/-! ## Enumerating all formulas -/

/-- A finite list of formulas: those of depth `≤ n` built from atoms `< n`. As `n`
grows these lists exhaust all formulas, giving an enumeration of the (countable)
set of formulas. -/
def allUpTo : Nat → List Formula
  | 0 => [bot]
  | n + 1 =>
      bot :: ((List.range (n + 1)).map var ++
        (allUpTo n).flatMap fun a => (allUpTo n).flatMap fun b => [imp a b, conj a b, disj a b])

/-- Membership in the next enumeration list, unfolded one level. -/
theorem mem_allUpTo_succ {φ : Formula} {n : Nat} : φ ∈ allUpTo (n + 1) ↔
    φ = bot ∨ (∃ k, k < n + 1 ∧ var k = φ) ∨
      ∃ a ∈ allUpTo n, ∃ b ∈ allUpTo n, φ ∈ [imp a b, conj a b, disj a b] := by
  rw [allUpTo]
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap]

/-- The enumeration lists are cumulative. -/
theorem allUpTo_succ {φ : Formula} : ∀ {n}, φ ∈ allUpTo n → φ ∈ allUpTo (n + 1)
  | 0, h => by simp [allUpTo] at h; simp [allUpTo, h]
  | n + 1, h => by
      rw [mem_allUpTo_succ] at h ⊢
      rcases h with h | ⟨k, hk, rfl⟩ | ⟨a, ha, b, hb, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨a, allUpTo_succ ha, b, allUpTo_succ hb, h⟩)

/-- The enumeration lists are cumulative (general form). -/
theorem allUpTo_mono {φ : Formula} {m n : Nat} (hmn : m ≤ n) (h : φ ∈ allUpTo m) :
    φ ∈ allUpTo n := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact allUpTo_succ ih

/-- Every formula occurs in some list `allUpTo n`. -/
theorem exists_mem_allUpTo : ∀ φ : Formula, ∃ n, φ ∈ allUpTo n
  | bot => ⟨0, by simp [allUpTo]⟩
  | var k => ⟨k + 1, by simp [allUpTo]⟩
  | imp a b | conj a b | disj a b => by
      obtain ⟨n₁, h₁⟩ := exists_mem_allUpTo a
      obtain ⟨n₂, h₂⟩ := exists_mem_allUpTo b
      refine ⟨max n₁ n₂ + 1, ?_⟩
      rw [mem_allUpTo_succ]
      refine Or.inr (Or.inr ⟨a, allUpTo_mono (Nat.le_max_left _ _) h₁,
        b, allUpTo_mono (Nat.le_max_right _ _) h₂, by simp⟩)

/-! ## Lindenbaum's lemma -/

open Classical in
/-- Process a list of formulas, adding each one to the theory whenever the result
stays consistent. -/
noncomputable def extend : Theory → List Formula → Theory
  | Δ, [] => Δ
  | Δ, φ :: l => extend (if Consistent (insert Δ φ) then insert Δ φ else Δ) l

/-- Extending only adds formulas. -/
theorem subset_extend : ∀ (l : List Formula) (Δ : Theory), Δ.Subset (extend Δ l)
  | [], _ => Subset.refl _
  | φ :: l, Δ => by
      unfold extend
      split
      · exact (subset_insert Δ φ).trans (subset_extend l _)
      · exact subset_extend l _

/-- Extending preserves consistency. -/
theorem consistent_extend : ∀ (l : List Formula) (Δ : Theory), Consistent Δ →
    Consistent (extend Δ l)
  | [], _, h => h
  | φ :: l, Δ, h => by
      unfold extend
      split
      · exact consistent_extend l _ (by assumption)
      · exact consistent_extend l _ h

/-- After processing `l`, each formula of `l` has either been added, or was rejected
because it is inconsistent with a sub-theory of the result. -/
theorem extend_decides : ∀ (l : List Formula) (Δ : Theory) (φ : Formula), φ ∈ l →
    extend Δ l φ ∨ ∃ Δ', Δ'.Subset (extend Δ l) ∧ ¬ Consistent (insert Δ' φ)
  | [], _, _, h => by simp at h
  | ψ :: l, Δ, φ, h => by
      rcases List.mem_cons.1 h with rfl | h
      · unfold extend
        split
        · exact Or.inl (subset_extend l _ φ (Or.inl rfl))
        · exact Or.inr ⟨Δ, subset_extend l _, by assumption⟩
      · unfold extend
        exact extend_decides l _ φ h

/-- The `n`-th stage of the Lindenbaum construction starting from `Γ`. -/
noncomputable def stage (Γ : Theory) : Nat → Theory
  | 0 => Γ
  | n + 1 => extend (stage Γ n) (allUpTo n)

/-- The stages form an increasing chain. -/
theorem stage_mono (Γ : Theory) {m n : Nat} (h : m ≤ n) : (stage Γ m).Subset (stage Γ n) := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact ih.trans (subset_extend _ _)

/-- Every stage is consistent if `Γ` is. -/
theorem consistent_stage {Γ : Theory} (hΓ : Consistent Γ) : ∀ n, Consistent (stage Γ n)
  | 0 => hΓ
  | n + 1 => consistent_extend _ _ (consistent_stage hΓ n)

/-- The Lindenbaum completion of `Γ`: the union of all stages. -/
noncomputable def lindenbaum (Γ : Theory) : Theory := fun ψ => ∃ n, stage Γ n ψ

/-- Any finite list of members of the union lies in a single stage. -/
theorem lindenbaum_finite (Γ : Theory) :
    ∀ L : List Formula, (∀ ψ ∈ L, lindenbaum Γ ψ) → ∃ n, ∀ ψ ∈ L, stage Γ n ψ
  | [], _ => ⟨0, by simp⟩
  | ψ :: L, h => by
      obtain ⟨m, hm⟩ := h ψ (by simp)
      obtain ⟨n, hn⟩ := lindenbaum_finite Γ L (fun χ hχ => h χ (by simp [hχ]))
      refine ⟨max m n, fun χ hχ => ?_⟩
      rcases List.mem_cons.1 hχ with rfl | hχ
      · exact stage_mono Γ (Nat.le_max_left _ _) _ hm
      · exact stage_mono Γ (Nat.le_max_right _ _) _ (hn χ hχ)

/-- **Lindenbaum's lemma.** Every consistent theory is contained in a maximal
consistent theory. -/
theorem lindenbaum_lemma {Γ : Theory} (hΓ : Consistent Γ) :
    ∃ M, Γ.Subset M ∧ MaximalConsistent M := by
  refine ⟨lindenbaum Γ, fun ψ h => ⟨0, h⟩, ?_, ?_⟩
  · intro hbot
    obtain ⟨L, hL, hd⟩ := hbot.finite_premises
    obtain ⟨n, hn⟩ := lindenbaum_finite Γ L hL
    exact consistent_stage hΓ n (hd.weaken hn)
  · intro φ
    obtain ⟨n, hn⟩ := exists_mem_allUpTo φ
    rcases extend_decides (allUpTo n) (stage Γ n) φ hn with h | ⟨Δ', hsub, hinc⟩
    · exact Or.inl ⟨n + 1, h⟩
    · refine Or.inr fun hc => hc ?_
      refine Classical.byContradiction fun hc' => ?_
      exact hinc (fun hb => hc' (hb.weaken (insert_mono
        (hsub.trans fun ψ h => ⟨n + 1, h⟩) φ)))

/-! ## The truth lemma -/

namespace MaximalConsistent

variable {M : Theory} (hM : MaximalConsistent M)
include hM

/-- A maximal consistent theory is deductively closed. -/
theorem closed {φ : Formula} (h : M ⊢ φ) : M φ := by
  rcases hM.2 φ with h' | h'
  · exact h'
  · exact absurd (Derives.cut h (by refine Classical.byContradiction fun hc => ?_; exact h' hc)) hM.1

/-- A maximal consistent theory contains `¬φ` exactly when it does not contain `φ`. -/
theorem neg_iff (φ : Formula) : M (neg φ) ↔ ¬ M φ := by
  constructor
  · intro h₁ h₂
    exact hM.1 (Derives.negE (.hyp h₁) (.hyp h₂))
  · intro h
    rcases hM.2 φ with h' | h'
    · exact absurd h' h
    · exact hM.closed (Derives.negI (by refine Classical.byContradiction fun hc => ?_; exact h' hc))

/-- The valuation determined by a maximal consistent theory: an atom is true iff it
belongs to the theory. -/
noncomputable def valuation (M : Theory) : Valuation :=
  open Classical in fun n => decide (M (var n))

/-- **Truth lemma.** Under the valuation determined by a maximal consistent theory
`M`, a formula is true exactly when it belongs to `M`. -/
theorem truth : ∀ φ : Formula, φ.eval (valuation M) = true ↔ M φ
  | bot => by simp only [eval]; exact ⟨nofun, fun h => absurd (Derives.hyp h) hM.1⟩
  | var n => by simp [eval, valuation]
  | imp a b => by
      have ia := truth a
      have ib := truth b
      simp only [eval, Bool.or_eq_true, Bool.not_eq_true']
      constructor
      · rintro (h | h)
        · have : ¬ M a := fun h' => by rw [← ia] at h'; simp_all
          exact hM.closed (Derives.imp_of_neg (.hyp ((hM.neg_iff a).2 this)))
        · exact hM.closed (Derives.imp_of_right (.hyp (ib.1 h)))
      · intro h
        by_cases ha : M a
        · exact Or.inr (ib.2 (hM.closed (Derives.impE (.hyp h) (.hyp ha))))
        · left
          cases e : eval (valuation M) a
          · rfl
          · exact absurd (ia.1 e) ha
  | conj a b => by
      simp only [eval, Bool.and_eq_true, truth a, truth b]
      exact ⟨fun h => hM.closed (Derives.conjI (.hyp h.1) (.hyp h.2)),
        fun h => ⟨hM.closed (Derives.conjE₁ (.hyp h)), hM.closed (Derives.conjE₂ (.hyp h))⟩⟩
  | disj a b => by
      simp only [eval, Bool.or_eq_true, truth a, truth b]
      constructor
      · rintro (h | h)
        · exact hM.closed (Derives.disjI₁ (.hyp h))
        · exact hM.closed (Derives.disjI₂ (.hyp h))
      · intro h
        refine Classical.byContradiction fun hc => ?_
        simp only [not_or] at hc
        exact (hM.neg_iff _).1 (hM.closed (Derives.neg_disj
          (.hyp ((hM.neg_iff a).2 hc.1)) (.hyp ((hM.neg_iff b).2 hc.2)))) h

end MaximalConsistent

/-! ## Completeness and compactness -/

/-- **Model existence.** Every consistent theory is satisfiable. -/
theorem satisfiable_of_consistent {Γ : Theory} (h : Consistent Γ) : Γ.Satisfiable := by
  obtain ⟨M, hsub, hM⟩ := lindenbaum_lemma h
  exact ⟨MaximalConsistent.valuation M, fun ψ hψ => (hM.truth ψ).2 (hsub ψ hψ)⟩

/-- **Completeness theorem** (strong form, for arbitrary sets of premises).
If `φ` is a semantic consequence of `Γ`, then `φ` is derivable from `Γ` in natural
deduction: `Γ ⊨ φ → Γ ⊢ φ`. -/
theorem completeness {Γ : Theory} {φ : Formula} (h : Γ ⊨ φ) : Γ ⊢ φ := by
  refine Classical.byContradiction fun hn => ?_
  have hc : Consistent (insert Γ (neg φ)) := fun hb => hn (Derives.raa hb)
  obtain ⟨v, hv⟩ := satisfiable_of_consistent hc
  have h₁ := h v (fun ψ hψ => hv ψ (Or.inr hψ))
  have h₂ := hv (neg φ) (Or.inl rfl)
  simp [h₁] at h₂

/-- **Soundness and completeness.** Derivability and semantic consequence coincide. -/
theorem derives_iff_entails (Γ : Theory) (φ : Formula) : Γ ⊢ φ ↔ Γ ⊨ φ :=
  ⟨Derives.soundness, completeness⟩

/-- **Completeness of the Hilbert system.** `Γ ⊨ φ → Γ ⊢ₕ φ`. -/
theorem hilbert_completeness {Γ : Theory} {φ : Formula} (h : Γ ⊨ φ) : Γ ⊢ₕ φ :=
  (completeness h).toHilbert

/-- **Weak completeness.** Every tautology is derivable from no premises. -/
theorem tautology_iff_derivable (φ : Formula) : φ.Tautology ↔ Theory.empty ⊢ φ := by
  rw [tautology_iff_entails_empty, derives_iff_entails]

/-- **Decidability of provability.** Whether `φ` is derivable from no premises is
decidable — by truth tables, thanks to soundness and completeness. -/
instance decDerivable (φ : Formula) : Decidable (Theory.empty ⊢ φ) :=
  decidable_of_iff _ (tautology_iff_derivable φ)

/-- **Compactness theorem (consequence form).** If `Γ ⊨ φ` then already some finite
list of premises from `Γ` entails `φ`. -/
theorem compactness_entails {Γ : Theory} {φ : Formula} (h : Γ ⊨ φ) :
    ∃ L : List Formula, (∀ ψ ∈ L, Γ ψ) ∧ ofList L ⊨ φ := by
  obtain ⟨L, hL, hd⟩ := (completeness h).finite_premises
  exact ⟨L, hL, hd.soundness⟩

/-- **Compactness theorem.** A set of formulas is satisfiable if every finite subset
of it is satisfiable. -/
theorem compactness {Γ : Theory}
    (h : ∀ L : List Formula, (∀ ψ ∈ L, Γ ψ) → (ofList L).Satisfiable) : Γ.Satisfiable := by
  refine Classical.byContradiction fun hn => ?_
  have hbot : Γ ⊨ bot := fun v hv => absurd ⟨v, hv⟩ hn
  obtain ⟨L, hL, hLbot⟩ := compactness_entails hbot
  obtain ⟨v, hv⟩ := h L hL
  simpa [eval] using hLbot v hv

end Foundations.Logic
