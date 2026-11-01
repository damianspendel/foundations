import Foundations.Logic.SequentCalculus

/-!
# Gentzen's Hauptsatz: cut elimination

**The theorem.** Every sequent derivable in `LK` — with cut and structural rules —
has a derivation using neither (`cut_elimination`). Gentzen called this his
*Hauptsatz* (1934/35), and it is arguably the founding theorem of structural proof
theory.

**Why it matters: analyticity.** A cut-free derivation never introduces a formula
that is not already a subformula of its end-sequent (the **subformula property**,
`subformula_property` below). It is *analytic* in an old philosophical sense: its
content is unfolded from what is to be proved, with no detours through foreign
lemmas. Cut, by contrast, is the rule of *synthetic* reasoning — of invention — in
which some formula `A`, possibly far more complex than anything in the conclusion,
is proved and then used. The Hauptsatz says that, in pure logic, such detours can
always be eliminated: everything provable is provable analytically. (The price,
famously, is size: cut elimination may blow up proofs super-exponentially, so lemmas
are dispensable in principle but not in practice.) In natural deduction the
corresponding result is Prawitz's **normalisation theorem** (1965): every
derivation can be brought into a normal form without "detours" in which a formula
is introduced and immediately eliminated; normal derivations likewise enjoy the
subformula property.

**Why it matters: consistency.** Hilbert's programme asked for *finitary*
consistency proofs: proofs, by elementary combinatorial reasoning about proofs as
finite objects, that no formal derivation ends in a contradiction. For pure logic
cut elimination delivers exactly this. The empty sequent `⊢` has no cut-free
derivation — trivially, since every rule needs a formula in its conclusion to act
on — hence no derivation at all (`LK.consistent`). Unlike the soundness argument,
this consistency proof never mentions truth or valuations: it is purely
syntactic. Gentzen's 1936 consistency proof of Peano arithmetic extends this idea to
arithmetic, where cut cannot be fully eliminated and transfinite induction up to
the ordinal ε₀ is needed (see `GentzenConsistency`).

**The proof.** We prove that cut is *admissible* in the cut-free calculus: if
`Γ ⊢ A, Δ` and `A, Γ ⊢ Δ` have cut-free derivations, so does `Γ ⊢ Δ`. The proof is by
induction on the cut formula `A` — its complexity, Gentzen's "grade" — and within
that by induction on a derivation:

* If `A` is an atom or `⊥` (no right rule), we trace the occurrences of `A` in the
  derivation of `Γ ⊢ A, Δ` up to the axioms where it was introduced, and replace each
  such axiom `A ∈ Γ'` by the derivation of `A, Γ ⊢ Δ` (suitably weakened).
* If `A` is compound, every rule is **invertible**: from a derivation of the
  conclusion we extract derivations of the premises, with `A` itself removed
  (`inv_left`, `inv_right`). The cut on `A` is then replaced by cuts on its
  immediate subformulas, which are smaller.

Elimination of all cuts from an `LK` derivation then follows by induction on the
derivation, eliminating topmost cuts first.
-/

namespace Foundations.Logic.Sequent

open Formula

/-! ## Interaction of left and right rules -/

/-- A formula with a non-empty left rule also has a right rule. -/
theorem right_of_left {X : Formula} {qs q} (hqs : leftPremises X = some qs) (hq : q ∈ qs) :
    ∃ ps, rightPremises X = some ps := by
  cases X <;> simp [leftPremises, rightPremises] at hqs ⊢
  subst hqs; simp at hq

/-- A formula with a right rule also has a left rule. -/
theorem left_of_right {X : Formula} {ps} (hps : rightPremises X = some ps) :
    ∃ qs, leftPremises X = some qs := by
  cases X <;> simp [leftPremises, rightPremises] at hps ⊢

/-- **Duality of left and right rules.** For a formula with both rules, combining any
left premise with any right premise yields an axiom: some formula is added on both
sides. This is the combinatorial heart of the identity `A ⊢ A`. -/
theorem dual {X : Formula} {qs ps q p} (hqs : leftPremises X = some qs)
    (hps : rightPremises X = some ps) (hq : q ∈ qs) (hp : p ∈ ps) :
    ∃ Y, Y ∈ q.1 ++ p.1 ∧ Y ∈ q.2 ++ p.2 := by
  cases X <;> simp [leftPremises, rightPremises] at hqs hps <;> subst hqs hps <;>
    simp at hq hp <;> rcases hq with rfl | rfl <;> try rcases hp with rfl | rfl
  all_goals simp

/-- If `X` occurs in the antecedent, each premise of the right rule for `X` is
cut-free derivable (by the left rule for `X` and duality). -/
theorem close_right {X : Formula} {ps p Γ Δ} (hX : X ∈ Γ) (hps : rightPremises X = some ps)
    (hp : p ∈ ps) : CutFree (p.1 ++ Γ) (p.2 ++ Δ) := by
  obtain ⟨qs, hqs⟩ := left_of_right hps
  refine CutFree.left (List.mem_append_right _ hX) hqs (fun q hq => ?_)
  obtain ⟨Y, h₁, h₂⟩ := dual hqs hps hq hp
  exact CutFree.ax (A := Y) (by grind) (by grind)

/-- If `X` occurs in the succedent, each premise of the left rule for `X` is cut-free
derivable (by the right rule for `X` and duality). -/
theorem close_left {X : Formula} {qs q Γ Δ} (hX : X ∈ Δ) (hqs : leftPremises X = some qs)
    (hq : q ∈ qs) : CutFree (q.1 ++ Γ) (q.2 ++ Δ) := by
  obtain ⟨ps, hps⟩ := right_of_left hqs hq
  refine CutFree.right (List.mem_append_right _ hX) hps (fun p hp => ?_)
  obtain ⟨Y, h₁, h₂⟩ := dual hqs hps hq hp
  exact CutFree.ax (A := Y) (by grind) (by grind)

/-! ## Inversion -/

/-- **Inversion of the right rules.** If `Γ ⊢ X, Δ` is cut-free derivable, then so
is each premise of the right rule for `X`, with `X` itself removed. (Stated with
inclusions `⊆`, so that the induction goes through.) -/
theorem inv_right {X : Formula} {ps p} (hps : rightPremises X = some ps) (hp : p ∈ ps)
    {Γ Δ} (h : CutFree Γ Δ) :
    ∀ {Γ' Δ'}, Γ ⊆ Γ' → Δ ⊆ X :: Δ' → CutFree (p.1 ++ Γ') (p.2 ++ Δ') := by
  induction h with
  | @ax Γ Δ A h₁ h₂ =>
      intro Γ' Δ' hΓ hΔ
      rcases List.mem_cons.1 (hΔ h₂) with rfl | h
      · exact close_right (hΓ h₁) hps hp
      · exact .ax (A := A) (List.mem_append_right _ (hΓ h₁)) (List.mem_append_right _ h)
  | @left Γ Δ A qs hA hqs _ ih =>
      intro Γ' Δ' hΓ hΔ
      refine .left (A := A) (List.mem_append_right _ (hΓ hA)) hqs (fun q hq => ?_)
      exact (@ih q hq (q.1 ++ Γ') (q.2 ++ Δ') (by grind) (by grind)).weaken
        (by grind) (by grind)
  | @right Γ Δ A qs hA hqs _ ih =>
      intro Γ' Δ' hΓ hΔ
      rcases List.mem_cons.1 (hΔ hA) with rfl | hA'
      · obtain rfl : ps = qs := Option.some.inj (hps.symm.trans hqs)
        exact (@ih p hp (p.1 ++ Γ') (p.2 ++ Δ') (by grind) (by grind)).weaken
          (by grind) (by grind)
      · refine .right (A := A) (List.mem_append_right _ hA') hqs (fun q hq => ?_)
        exact (@ih q hq (q.1 ++ Γ') (q.2 ++ Δ') (by grind) (by grind)).weaken
          (by grind) (by grind)

/-- **Inversion of the left rules.** If `X, Γ ⊢ Δ` is cut-free derivable, then so is
each premise of the left rule for `X`, with `X` itself removed. -/
theorem inv_left {X : Formula} {qs q} (hqs : leftPremises X = some qs) (hq : q ∈ qs)
    {Γ Δ} (h : CutFree Γ Δ) :
    ∀ {Γ' Δ'}, Γ ⊆ X :: Γ' → Δ ⊆ Δ' → CutFree (q.1 ++ Γ') (q.2 ++ Δ') := by
  induction h with
  | @ax Γ Δ A h₁ h₂ =>
      intro Γ' Δ' hΓ hΔ
      rcases List.mem_cons.1 (hΓ h₁) with rfl | h
      · exact close_left (hΔ h₂) hqs hq
      · exact .ax (A := A) (List.mem_append_right _ h) (List.mem_append_right _ (hΔ h₂))
  | @left Γ Δ A ps hA hps _ ih =>
      intro Γ' Δ' hΓ hΔ
      rcases List.mem_cons.1 (hΓ hA) with rfl | hA'
      · obtain rfl : qs = ps := Option.some.inj (hqs.symm.trans hps)
        exact (@ih q hq (q.1 ++ Γ') (q.2 ++ Δ') (by grind) (by grind)).weaken
          (by grind) (by grind)
      · refine .left (A := A) (List.mem_append_right _ hA') hps (fun p hp => ?_)
        exact (@ih p hp (p.1 ++ Γ') (p.2 ++ Δ') (by grind) (by grind)).weaken
          (by grind) (by grind)
  | @right Γ Δ A ps hA hps _ ih =>
      intro Γ' Δ' hΓ hΔ
      refine .right (A := A) (List.mem_append_right _ (hΔ hA)) hps (fun p hp => ?_)
      exact (@ih p hp (p.1 ++ Γ') (p.2 ++ Δ') (by grind) (by grind)).weaken
        (by grind) (by grind)

/-! ## Cut admissibility -/

/-- **Cut on a formula without right rule** (an atom or `⊥`). If `Γ ⊢ X, Δ` and
`X, Γ ⊢ Δ` are cut-free derivable then so is `Γ ⊢ Δ`: the occurrences of `X` on the
right can only stem from axioms, which become instances of the second derivation. -/
theorem cut_noRight {X : Formula} (hX : rightPremises X = none) {Γ Δ} (h : CutFree Γ Δ) :
    ∀ {Γ' Δ'}, Γ ⊆ Γ' → Δ ⊆ X :: Δ' → CutFree (X :: Γ') Δ' → CutFree Γ' Δ' := by
  induction h with
  | @ax Γ Δ A h₁ h₂ =>
      intro Γ' Δ' hΓ hΔ h'
      rcases List.mem_cons.1 (hΔ h₂) with rfl | h
      · exact h'.weaken (by grind) (List.Subset.refl _)
      · exact .ax (hΓ h₁) h
  | @left Γ Δ A qs hA hqs _ ih =>
      intro Γ' Δ' hΓ hΔ h'
      refine .left (hΓ hA) hqs (fun q hq => ?_)
      exact @ih q hq (q.1 ++ Γ') (q.2 ++ Δ') (by grind) (by grind)
        (h'.weaken (by grind) (by grind))
  | @right Γ Δ A qs hA hqs _ ih =>
      intro Γ' Δ' hΓ hΔ h'
      rcases List.mem_cons.1 (hΔ hA) with rfl | hA'
      · rw [hX] at hqs; cases hqs
      · refine .right hA' hqs (fun q hq => ?_)
        exact @ih q hq (q.1 ++ Γ') (q.2 ++ Δ') (by grind) (by grind)
          (h'.weaken (by grind) (by grind))

/-- **Admissibility of cut.** If `Γ ⊢ A, Δ` and `A, Γ ⊢ Δ` have cut-free derivations,
then so does `Γ ⊢ Δ`. By induction on the cut formula `A`: atoms and `⊥` are handled
by `cut_noRight`; for compound `A` both premises are inverted and the cut is
replaced by cuts on the immediate subformulas of `A`. -/
theorem cut_admissible : ∀ (A : Formula) {Γ Δ : List Formula},
    CutFree Γ (A :: Δ) → CutFree (A :: Γ) Δ → CutFree Γ Δ
  | bot, _, _, h₁, h₂ => cut_noRight rfl h₁ (List.Subset.refl _) (List.Subset.refl _) h₂
  | var _, _, _, h₁, h₂ => cut_noRight rfl h₁ (List.Subset.refl _) (List.Subset.refl _) h₂
  | imp A B, Γ, Δ, h₁, h₂ => by
      -- `A, Γ ⊢ B, Δ`, `Γ ⊢ A, Δ` and `B, Γ ⊢ Δ`
      have r : CutFree (A :: Γ) (B :: Δ) :=
        inv_right (X := imp A B) (p := ([A], [B])) rfl (by simp) h₁
          (List.Subset.refl _) (List.Subset.refl _)
      have l₁ : CutFree Γ (A :: Δ) :=
        inv_left (X := imp A B) (q := ([], [A])) rfl (by simp) h₂
          (List.Subset.refl _) (List.Subset.refl _)
      have l₂ : CutFree (B :: Γ) Δ :=
        inv_left (X := imp A B) (q := ([B], [])) rfl (by simp) h₂
          (List.Subset.refl _) (List.Subset.refl _)
      have hB : CutFree Γ (B :: Δ) := cut_admissible A (l₁.weaken (by grind) (by grind)) r
      exact cut_admissible B hB l₂
  | conj A B, Γ, Δ, h₁, h₂ => by
      -- `Γ ⊢ A, Δ`, `Γ ⊢ B, Δ` and `A, B, Γ ⊢ Δ`
      have r₁ : CutFree Γ (A :: Δ) :=
        inv_right (X := conj A B) (p := ([], [A])) rfl (by simp) h₁
          (List.Subset.refl _) (List.Subset.refl _)
      have r₂ : CutFree Γ (B :: Δ) :=
        inv_right (X := conj A B) (p := ([], [B])) rfl (by simp) h₁
          (List.Subset.refl _) (List.Subset.refl _)
      have l : CutFree (A :: B :: Γ) Δ :=
        inv_left (X := conj A B) (q := ([A, B], [])) rfl (by simp) h₂
          (List.Subset.refl _) (List.Subset.refl _)
      have hB : CutFree (B :: Γ) Δ := cut_admissible A (r₁.weaken (by grind) (by grind)) l
      exact cut_admissible B r₂ hB
  | disj A B, Γ, Δ, h₁, h₂ => by
      -- `Γ ⊢ A, B, Δ`, `A, Γ ⊢ Δ` and `B, Γ ⊢ Δ`
      have r : CutFree Γ (A :: B :: Δ) :=
        inv_right (X := disj A B) (p := ([], [A, B])) rfl (by simp) h₁
          (List.Subset.refl _) (List.Subset.refl _)
      have l₁ : CutFree (A :: Γ) Δ :=
        inv_left (X := disj A B) (q := ([A], [])) rfl (by simp) h₂
          (List.Subset.refl _) (List.Subset.refl _)
      have l₂ : CutFree (B :: Γ) Δ :=
        inv_left (X := disj A B) (q := ([B], [])) rfl (by simp) h₂
          (List.Subset.refl _) (List.Subset.refl _)
      have hB : CutFree Γ (B :: Δ) := cut_admissible A r (l₁.weaken (by grind) (by grind))
      exact cut_admissible B hB l₂

/-- **Gentzen's Hauptsatz (cut elimination).** Every sequent derivable in `LK`, with
cut and the structural rules, has a cut-free derivation. -/
theorem cut_elimination {Γ Δ : List Formula} (h : LK Γ Δ) : CutFree Γ Δ := by
  induction h with
  | ax h₁ h₂ => exact .ax h₁ h₂
  | left hA hps _ ih => exact .left hA hps ih
  | right hA hps _ ih => exact .right hA hps ih
  | weak _ hΓ hΔ ih => exact ih.weaken hΓ hΔ
  | cut A _ _ ih₁ ih₂ => exact cut_admissible A ih₁ ih₂

/-- `LK` and its cut-free fragment derive exactly the same sequents. -/
theorem LK_iff_cutFree (Γ Δ : List Formula) : LK Γ Δ ↔ CutFree Γ Δ :=
  ⟨cut_elimination, CutFree.toLK⟩

/-! ## The subformula property -/

/-- The list of all subformulas of a formula (including itself). -/
def subformulas : Formula → List Formula
  | bot => [bot]
  | var n => [var n]
  | imp A B => imp A B :: (subformulas A ++ subformulas B)
  | conj A B => conj A B :: (subformulas A ++ subformulas B)
  | disj A B => disj A B :: (subformulas A ++ subformulas B)

/-- Every formula is a subformula of itself. -/
theorem mem_subformulas_self (A : Formula) : A ∈ subformulas A := by
  cases A <;> simp [subformulas]

/-- Being a subformula is transitive. -/
theorem subformulas_trans {A B : Formula} (hAB : A ∈ subformulas B) :
    ∀ {C : Formula}, B ∈ subformulas C → A ∈ subformulas C
  | bot, h => by simp [subformulas] at h; subst h; exact hAB
  | var _, h => by simp [subformulas] at h; subst h; exact hAB
  | imp C D, h => by
      simp only [subformulas, List.mem_cons, List.mem_append] at h ⊢
      rcases h with rfl | h | h
      · simpa [subformulas] using hAB
      · exact Or.inr (Or.inl (subformulas_trans hAB h))
      · exact Or.inr (Or.inr (subformulas_trans hAB h))
  | conj C D, h => by
      simp only [subformulas, List.mem_cons, List.mem_append] at h ⊢
      rcases h with rfl | h | h
      · simpa [subformulas] using hAB
      · exact Or.inr (Or.inl (subformulas_trans hAB h))
      · exact Or.inr (Or.inr (subformulas_trans hAB h))
  | disj C D, h => by
      simp only [subformulas, List.mem_cons, List.mem_append] at h ⊢
      rcases h with rfl | h | h
      · simpa [subformulas] using hAB
      · exact Or.inr (Or.inl (subformulas_trans hAB h))
      · exact Or.inr (Or.inr (subformulas_trans hAB h))

/-- The formulas added by a left rule are subformulas of its principal formula. -/
theorem left_premise_sub {A : Formula} {ps p B} (h : leftPremises A = some ps)
    (hp : p ∈ ps) (hB : B ∈ p.1 ++ p.2) : B ∈ subformulas A := by
  cases A <;> simp [leftPremises] at h <;> subst h <;> simp at hp <;>
    rcases hp with rfl | rfl <;> simp at hB <;>
    rcases hB with rfl | rfl <;> simp [subformulas, mem_subformulas_self]

/-- The formulas added by a right rule are subformulas of its principal formula. -/
theorem right_premise_sub {A : Formula} {ps p B} (h : rightPremises A = some ps)
    (hp : p ∈ ps) (hB : B ∈ p.1 ++ p.2) : B ∈ subformulas A := by
  cases A <;> simp [rightPremises] at h <;> subst h <;> simp at hp <;>
    try rcases hp with rfl | rfl
  all_goals (simp at hB; try rcases hB with rfl | rfl)
  all_goals simp [subformulas, mem_subformulas_self]

/-- Cut-free derivations **within** a set `S` of formulas: like `CutFree`, but every
sequent occurring anywhere in the derivation consists of formulas from `S`. -/
inductive Within (S : Formula → Prop) : List Formula → List Formula → Prop where
  /-- Identity, with all formulas in `S`. -/
  | ax {Γ Δ : List Formula} {A : Formula} : (∀ B ∈ Γ ++ Δ, S B) →
      A ∈ Γ → A ∈ Δ → Within S Γ Δ
  /-- A left rule, with all formulas of the conclusion in `S`. -/
  | left {Γ Δ : List Formula} {A : Formula} {ps : List (List Formula × List Formula)} :
      (∀ B ∈ Γ ++ Δ, S B) → A ∈ Γ → leftPremises A = some ps →
      (∀ p ∈ ps, Within S (p.1 ++ Γ) (p.2 ++ Δ)) → Within S Γ Δ
  /-- A right rule, with all formulas of the conclusion in `S`. -/
  | right {Γ Δ : List Formula} {A : Formula} {ps : List (List Formula × List Formula)} :
      (∀ B ∈ Γ ++ Δ, S B) → A ∈ Δ → rightPremises A = some ps →
      (∀ p ∈ ps, Within S (p.1 ++ Γ) (p.2 ++ Δ)) → Within S Γ Δ

/-- A derivation within `S` is in particular a cut-free derivation. -/
theorem Within.cutFree {S Γ Δ} (h : Within S Γ Δ) : CutFree Γ Δ := by
  induction h with
  | ax _ h₁ h₂ => exact .ax h₁ h₂
  | left _ hA hps _ ih => exact .left hA hps ih
  | right _ hA hps _ ih => exact .right hA hps ih

/-- Auxiliary form of the subformula property, for an arbitrary end-sequent `E`. -/
theorem within_of_cutFree (E : List Formula) {Γ Δ} (h : CutFree Γ Δ) :
    (∀ B ∈ Γ ++ Δ, ∃ C ∈ E, B ∈ subformulas C) →
      Within (fun B => ∃ C ∈ E, B ∈ subformulas C) Γ Δ := by
  induction h with
  | ax h₁ h₂ => exact fun hS => .ax hS h₁ h₂
  | @left Γ Δ A ps hA hps _ ih =>
      intro hS
      refine .left hS hA hps (fun p hp => ih p hp ?_)
      intro B hB
      obtain ⟨C, hC, hAC⟩ := hS A (List.mem_append_left _ hA)
      simp only [List.mem_append] at hB
      rcases hB with (hB | hB) | (hB | hB)
      · exact ⟨C, hC, subformulas_trans (left_premise_sub hps hp (by simp [hB])) hAC⟩
      · exact hS B (by simp [hB])
      · exact ⟨C, hC, subformulas_trans (left_premise_sub hps hp (by simp [hB])) hAC⟩
      · exact hS B (by simp [hB])
  | @right Γ Δ A ps hA hps _ ih =>
      intro hS
      refine .right hS hA hps (fun p hp => ih p hp ?_)
      intro B hB
      obtain ⟨C, hC, hAC⟩ := hS A (List.mem_append_right _ hA)
      simp only [List.mem_append] at hB
      rcases hB with (hB | hB) | (hB | hB)
      · exact ⟨C, hC, subformulas_trans (right_premise_sub hps hp (by simp [hB])) hAC⟩
      · exact hS B (by simp [hB])
      · exact ⟨C, hC, subformulas_trans (right_premise_sub hps hp (by simp [hB])) hAC⟩
      · exact hS B (by simp [hB])

/-- **Subformula property.** Every cut-free derivable sequent `Γ ⊢ Δ` has a cut-free
derivation in which every formula of every sequent is a subformula of a formula of
the end-sequent `Γ ⊢ Δ`. -/
theorem subformula_property {Γ Δ : List Formula} (h : CutFree Γ Δ) :
    Within (fun B => ∃ C ∈ Γ ++ Δ, B ∈ subformulas C) Γ Δ :=
  within_of_cutFree (Γ ++ Δ) h (fun B hB => ⟨B, hB, mem_subformulas_self B⟩)

/-- **Analyticity of LK.** Every sequent derivable in `LK` (even using cut) has a
derivation in which only subformulas of the end-sequent occur. -/
theorem LK.analytic {Γ Δ : List Formula} (h : LK Γ Δ) :
    Within (fun B => ∃ C ∈ Γ ++ Δ, B ∈ subformulas C) Γ Δ :=
  subformula_property (cut_elimination h)

/-! ## Syntactic consistency -/

/-- The empty sequent has no cut-free derivation: every rule needs a formula in its
conclusion to act on. -/
theorem CutFree.not_empty : ¬ CutFree [] [] := by
  intro h
  cases h <;> simp_all

/-- **Consistency of LK, syntactically.** The empty sequent `⊢` is not derivable in
`LK`. The proof is purely combinatorial — cut elimination plus `CutFree.not_empty` —
and mentions neither truth nor valuations: a consistency proof of the kind
demanded by Hilbert's programme, for pure propositional logic. -/
theorem LK.consistent : ¬ LK [] [] := fun h => CutFree.not_empty (cut_elimination h)

/-- `⊥` is not provable in `LK`: a cut-free proof of `⊢ ⊥` would have to end with a
right rule for `⊥`, and there is none. -/
theorem LK.not_proves_bot : ¬ LK [] [bot] := by
  intro h
  cases cut_elimination h with
  | ax h₁ _ => simp at h₁
  | left h₁ _ _ => simp at h₁
  | right h₁ h₂ _ => simp at h₁; subst h₁; simp [rightPremises] at h₂

/-- No atom is provable in `LK`. -/
theorem LK.not_proves_var (n : Nat) : ¬ LK [] [var n] := by
  intro h
  cases cut_elimination h with
  | ax h₁ _ => simp at h₁
  | left h₁ _ _ => simp at h₁
  | right h₁ h₂ _ => simp at h₁; subst h₁; simp [rightPremises] at h₂

end Foundations.Logic.Sequent
