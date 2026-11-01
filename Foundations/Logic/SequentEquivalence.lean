import Foundations.Logic.CutElimination
import Foundations.Logic.NaturalDeduction

/-!
# Cut-free completeness, proof search, and natural deduction

The previous file showed that cut can be eliminated. This file shows that the
cut-free calculus is, nevertheless, *complete*: every valid sequent has a cut-free
derivation. Together with soundness, a sequent is derivable (with or without cut)
exactly when it is valid.

**Proof search.** In a cut-free derivation, read from the bottom up, each rule
*decomposes* its principal formula into its immediate subformulas, and every rule of
our calculus is semantically **invertible**: the premises are valid as soon as the
conclusion is. So one may search for a derivation mechanically: decompose any
compound formula, branch where the rule has several premises, and stop when only
atoms remain — at which point the sequent is derivable iff some atom occurs on both
sides. Since each step strictly reduces a size measure, the search terminates. This is
the method of Gentzen's 1934/35 decision procedure for intuitionistic and classical
propositional logic, and the ancestor of Beth's semantic tableaux (1955) and of
much of modern automated theorem proving.

`search` implements this procedure as a program, `search_sound` shows that a
successful search yields a cut-free derivation, and `search_complete` shows that a
valid sequent always leads to success. As corollaries:

* **Cut-free completeness**: `CutFree Γ Δ ↔ Valid Γ Δ`;
* a *second*, purely syntactic **decision procedure for tautologies** (alongside the
  truth tables of `PropSemantics`): `⊢ A` is cut-free derivable iff `A` is a
  tautology, and derivability is computably decidable by proof search;
* a second, *semantic* proof of cut elimination: `LK Γ Δ → Valid Γ Δ → CutFree Γ Δ`.
  This short route is available only because propositional validity is so well
  behaved; Gentzen's syntactic proof (previous file) is the one that generalises,
  for example to settings like arithmetic where no completeness theorem is at hand.

**Natural deduction.** Finally we translate in both directions, purely
syntactically, between `LK` and Gentzen's other calculus, natural deduction
(`Derives`). A sequent `Γ ⊢ Δ` corresponds to the natural-deduction judgement that
`Γ` together with the negations of `Δ` is contradictory. The translation from
natural deduction into `LK` uses cut essentially (modus ponens *is* a cut); composing
it with cut elimination turns every natural-deduction derivation into an analytic,
cut-free sequent derivation — a sequent-calculus counterpart of Prawitz's
normalisation theorem (1965).
-/

namespace Foundations.Logic.Sequent

open Formula

/-! ## Proof search -/

/-- The weight of a list of formulas: the sum of `2 · size + 1` over its members. Every
step of proof search strictly decreases the weight of the unprocessed formulas. -/
def weight (l : List Formula) : Nat := (l.map fun A => 2 * A.size + 1).sum

/-- Weight of a cons. -/
theorem weight_cons (A : Formula) (l : List Formula) :
    weight (A :: l) = 2 * A.size + 1 + weight l := by
  simp [weight]

/-- Weight of an append. -/
theorem weight_append (l₁ l₂ : List Formula) : weight (l₁ ++ l₂) = weight l₁ + weight l₂ := by
  simp [weight]

/-- The premises of a left rule weigh less than its principal formula. -/
theorem weight_left {A : Formula} {ps p} (h : leftPremises A = some ps) (hp : p ∈ ps) :
    weight p.1 + weight p.2 < 2 * A.size + 1 := by
  cases A <;> simp [leftPremises] at h <;> subst h <;> simp at hp <;>
    try rcases hp with rfl | rfl
  all_goals simp [weight, size]; omega

/-- The premises of a right rule weigh less than its principal formula. -/
theorem weight_right {A : Formula} {ps p} (h : rightPremises A = some ps) (hp : p ∈ ps) :
    weight p.1 + weight p.2 < 2 * A.size + 1 := by
  cases A <;> simp [rightPremises] at h <;> subst h <;> simp at hp <;>
    try rcases hp with rfl | rfl
  all_goals simp [weight, size]; omega

/-- **Proof search** with fuel `n`. `search n Γ Δ L R` tries to derive
`Γ ++ L ⊢ Δ ++ R`, where `Γ, Δ` are still to be decomposed and `L, R` hold the
already processed formulas that admit no rule (atoms; atoms and `⊥`). It decomposes
the first unprocessed formula by its rule, branching over the premises, and at the
end checks whether some processed formula occurs on both sides. -/
def search : Nat → List Formula → List Formula → List Formula → List Formula → Bool
  | 0, _, _, _, _ => false
  | n + 1, A :: Γ, Δ, L, R =>
      match leftPremises A with
      | some ps => ps.all fun p => search n (p.1 ++ Γ) (p.2 ++ Δ) L R
      | none => search n Γ Δ (A :: L) R
  | n + 1, [], A :: Δ, L, R =>
      match rightPremises A with
      | some ps => ps.all fun p => search n p.1 (p.2 ++ Δ) L R
      | none => search n [] Δ L (A :: R)
  | _ + 1, [], [], L, R => L.any fun A => decide (A ∈ R)

/-- **Soundness of proof search.** A successful search produces a cut-free derivation. -/
theorem search_sound : ∀ (n : Nat) (Γ Δ L R : List Formula),
    search n Γ Δ L R = true → CutFree (Γ ++ L) (Δ ++ R)
  | 0, _, _, _, _, h => by simp [search] at h
  | n + 1, A :: Γ, Δ, L, R, h => by
      cases hA : leftPremises A with
      | some ps =>
          simp only [search, hA, List.all_eq_true] at h
          refine CutFree.left (A := A) (by simp) hA (fun p hp => ?_)
          exact (search_sound n _ _ L R (h p hp)).weaken (by grind) (by grind)
      | none =>
          simp only [search, hA] at h
          exact (search_sound n Γ Δ (A :: L) R h).weaken (by grind) (by grind)
  | n + 1, [], A :: Δ, L, R, h => by
      cases hA : rightPremises A with
      | some ps =>
          simp only [search, hA, List.all_eq_true] at h
          refine CutFree.right (A := A) (by simp) hA (fun p hp => ?_)
          exact (search_sound n _ _ L R (h p hp)).weaken (by grind) (by grind)
      | none =>
          simp only [search, hA] at h
          exact (search_sound n [] Δ L (A :: R) h).weaken (by grind) (by grind)
  | n + 1, [], [], L, R, h => by
      simp only [search, List.any_eq_true, decide_eq_true_eq] at h
      obtain ⟨A, h₁, h₂⟩ := h
      exact CutFree.ax (A := A) (by simpa using h₁) (by simpa using h₂)

/-- A formula without left rule is an atom. -/
theorem eq_var_of_left_none {A : Formula} (h : leftPremises A = none) : ∃ k, A = var k := by
  cases A <;> simp [leftPremises] at h ⊢

/-- A formula without right rule is `⊥` or an atom. -/
theorem eq_of_right_none {A : Formula} (h : rightPremises A = none) :
    A = bot ∨ ∃ k, A = var k := by
  cases A <;> simp [rightPremises] at h ⊢

/-- **Completeness of proof search.** If `Γ ++ L ⊢ Δ ++ R` is valid (with `L, R`
fully processed) and the fuel exceeds the weight of `Γ, Δ`, the search succeeds. -/
theorem search_complete : ∀ (n : Nat) (Γ Δ L R : List Formula),
    weight Γ + weight Δ < n → (∀ A ∈ L, leftPremises A = none) →
    (∀ A ∈ R, rightPremises A = none) → Valid (Γ ++ L) (Δ ++ R) →
    search n Γ Δ L R = true
  | 0, _, _, _, _, hw, _, _, _ => by omega
  | n + 1, A :: Γ, Δ, L, R, hw, hL, hR, hv => by
      rw [weight_cons] at hw
      cases hA : leftPremises A with
      | some ps =>
          simp only [search, hA, List.all_eq_true]
          intro p hp
          have := weight_left hA hp
          refine search_complete n _ _ L R ?_ hL hR ?_
          · rw [weight_append, weight_append]; omega
          · intro v hv'
            by_cases hq : ∃ B ∈ p.2, B.eval v = true
            · obtain ⟨B, hB, hBv⟩ := hq
              exact ⟨B, by simp [hB], hBv⟩
            · have hAv : A.eval v = true := (left_sem hA v).2
                ⟨p, hp, fun B hB => hv' B (by simp [hB]), fun B hB => by
                  simpa using fun h => hq ⟨B, hB, h⟩⟩
              obtain ⟨B, hB, hBv⟩ := hv v (by
                intro C hC
                simp only [List.cons_append, List.mem_cons] at hC
                rcases hC with rfl | hC
                · exact hAv
                · exact hv' C (by simp at hC ⊢; grind))
              exact ⟨B, by simp at hB ⊢; grind, hBv⟩
      | none =>
          simp only [search, hA]
          refine search_complete n Γ Δ (A :: L) R (by omega) ?_ hR ?_
          · intro B hB
            rcases List.mem_cons.1 hB with rfl | hB
            · exact hA
            · exact hL B hB
          · intro v hv'
            exact hv v (fun C hC => hv' C (by simp at hC ⊢; grind))
  | n + 1, [], A :: Δ, L, R, hw, hL, hR, hv => by
      rw [weight_cons] at hw
      simp only [weight, List.map_nil, List.sum_nil] at hw
      cases hA : rightPremises A with
      | some ps =>
          simp only [search, hA, List.all_eq_true]
          intro p hp
          have := weight_right hA hp
          refine search_complete n _ _ L R ?_ hL hR ?_
          · rw [weight_append]; simp only [weight] at this ⊢; omega
          · intro v hv'
            by_cases hq : ∃ B ∈ p.2, B.eval v = true
            · obtain ⟨B, hB, hBv⟩ := hq
              exact ⟨B, by simp [hB], hBv⟩
            · have hAv : A.eval v = false := (right_sem hA v).2
                ⟨p, hp, fun B hB => hv' B (by simp [hB]), fun B hB => by
                  simpa using fun h => hq ⟨B, hB, h⟩⟩
              obtain ⟨B, hB, hBv⟩ := hv v (fun C hC => hv' C (by simp at hC ⊢; grind))
              simp only [List.cons_append, List.mem_cons] at hB
              rcases hB with rfl | hB
              · simp [hAv] at hBv
              · exact ⟨B, by simp at hB ⊢; grind, hBv⟩
      | none =>
          simp only [search, hA]
          refine search_complete n [] Δ L (A :: R) (by simp only [weight, List.map_nil, List.sum_nil] at *; omega) hL ?_ ?_
          · intro B hB
            rcases List.mem_cons.1 hB with rfl | hB
            · exact hA
            · exact hR B hB
          · intro v hv'
            obtain ⟨B, hB, hBv⟩ := hv v hv'
            exact ⟨B, by simp at hB ⊢; grind, hBv⟩
  | n + 1, [], [], L, R, _, hL, hR, hv => by
      simp only [search, List.any_eq_true, decide_eq_true_eq]
      -- the countervaluation: make exactly the atoms of `L` true
      let v : Valuation := fun k => decide (var k ∈ L)
      obtain ⟨B, hB, hBv⟩ := hv v (by
        intro C hC
        obtain ⟨k, rfl⟩ := eq_var_of_left_none (hL C (by simpa using hC))
        simpa [v, eval] using hC)
      have hB' : B ∈ R := by simpa using hB
      rcases eq_of_right_none (hR B hB') with rfl | ⟨k, rfl⟩
      · simp [eval] at hBv
      · exact ⟨var k, by simpa [v, eval] using hBv, hB'⟩

/-- Proof search with sufficient fuel, starting from nothing processed. -/
def proofSearch (Γ Δ : List Formula) : Bool := search (weight Γ + weight Δ + 1) Γ Δ [] []

/-- **Cut-free completeness.** Every valid sequent has a cut-free derivation. -/
theorem cutFree_complete {Γ Δ : List Formula} (h : Valid Γ Δ) : CutFree Γ Δ := by
  have := search_sound _ Γ Δ [] []
    (search_complete (weight Γ + weight Δ + 1) Γ Δ [] [] (by omega) (by simp) (by simp)
      (by simpa using h))
  simpa using this

/-- **Soundness and cut-free completeness.** A sequent has a cut-free derivation iff
it is valid. -/
theorem cutFree_iff_valid (Γ Δ : List Formula) : CutFree Γ Δ ↔ Valid Γ Δ :=
  ⟨CutFree.sound, cutFree_complete⟩

/-- **Completeness of LK.** A sequent is derivable in `LK` iff it is valid. -/
theorem LK_iff_valid (Γ Δ : List Formula) : LK Γ Δ ↔ Valid Γ Δ :=
  ⟨LK.sound, fun h => (cutFree_complete h).toLK⟩

/-- **Correctness of proof search.** `proofSearch Γ Δ` succeeds iff `Γ ⊢ Δ` has a
cut-free derivation. -/
theorem proofSearch_iff (Γ Δ : List Formula) : proofSearch Γ Δ = true ↔ CutFree Γ Δ := by
  constructor
  · intro h; simpa using search_sound _ Γ Δ [] [] h
  · intro h
    exact search_complete _ Γ Δ [] [] (by omega) (by simp) (by simp) (by simpa using h.sound)

/-- **A syntactic decision procedure.** Cut-free derivability is decidable, by proof
search. -/
instance decCutFree (Γ Δ : List Formula) : Decidable (CutFree Γ Δ) :=
  decidable_of_iff _ (proofSearch_iff Γ Δ)

/-- Derivability in `LK` is decidable (by cut elimination and proof search). -/
instance decLK (Γ Δ : List Formula) : Decidable (LK Γ Δ) :=
  decidable_of_iff _ (LK_iff_cutFree Γ Δ).symm

/-- **Cut-free LK proves exactly the tautologies.** -/
theorem cutFree_iff_tautology (A : Formula) : CutFree [] [A] ↔ A.Tautology := by
  rw [cutFree_iff_valid]
  constructor
  · intro h v
    obtain ⟨B, hB, hBv⟩ := h v (by simp)
    simp at hB; exact hB ▸ hBv
  · intro h v _
    exact ⟨A, by simp, h v⟩

/-- **Semantic cut elimination.** A second proof of the Hauptsatz for propositional
logic: by soundness an `LK`-derivable sequent is valid, and by cut-free completeness
every valid sequent is cut-free derivable. -/
theorem cut_elimination_semantic {Γ Δ : List Formula} (h : LK Γ Δ) : CutFree Γ Δ :=
  cutFree_complete h.sound

/-- Proof search at work: Peirce's law has a cut-free derivation, found by the
decision procedure. -/
example : CutFree [] [imp (imp (imp (var 0) (var 1)) (var 0)) (var 0)] := by decide

/-- Proof search at work: `p → q ⊢ ¬q → ¬p` (contraposition). -/
example : CutFree [imp (var 0) (var 1)] [imp (neg (var 1)) (neg (var 0))] := by decide

/-- Proof search at work: `⊢ p → q` is not derivable. -/
example : ¬ LK [] [imp (var 0) (var 1)] := by decide

/-! ## From LK to natural deduction -/

open Theory in
/-- The natural-deduction reading of a sequent `Γ ⊢ Δ`: the premises are `Γ`
together with the negations of the formulas in `Δ`. -/
def ctx (Γ Δ : List Formula) : Theory := fun ψ => ψ ∈ Γ ∨ ∃ B ∈ Δ, ψ = neg B

/-- Extending a theory `T` by a rule premise `(L, R)`: add `L` and the negations
of `R`. -/
def ext (T : Theory) (p : List Formula × List Formula) : Theory :=
  fun ψ => T ψ ∨ ψ ∈ p.1 ∨ ∃ B ∈ p.2, ψ = neg B

/-- The left rules are valid in natural deduction: if `T ⊢ A` and every premise
extension of `T` is contradictory, then so is `T`. -/
theorem left_nd {A : Formula} {ps} (h : leftPremises A = some ps) {T : Theory}
    (hA : T ⊢ A) (hp : ∀ p ∈ ps, ext T p ⊢ bot) : T ⊢ bot := by
  cases A <;> simp [leftPremises] at h <;> subst h
  case bot => exact hA
  case imp A B =>
    have h₁ := hp ([], [A]) (by simp)
    have h₂ := hp ([B], []) (by simp)
    have hA' : T ⊢ A := Derives.raa (h₁.weaken (by intro ψ; simp [ext, Theory.insert]; grind))
    exact Derives.cut (Derives.impE hA hA')
      (h₂.weaken (by intro ψ; simp [ext, Theory.insert]; grind))
  case conj A B =>
    have h₁ := hp ([A, B], []) (by simp)
    have h₂ : Theory.insert (Theory.insert T A) B ⊢ bot :=
      h₁.weaken (by intro ψ; simp [ext, Theory.insert]; grind)
    exact Derives.cut (Derives.conjE₁ hA)
      (Derives.cut ((Derives.conjE₂ hA).weaken₁ _) h₂)
  case disj A B =>
    have h₁ := hp ([A], []) (by simp)
    have h₂ := hp ([B], []) (by simp)
    exact Derives.disjE hA (h₁.weaken (by intro ψ; simp [ext, Theory.insert]; grind))
      (h₂.weaken (by intro ψ; simp [ext, Theory.insert]; grind))

/-- The right rules are valid in natural deduction: if `T ⊢ ¬A` and every premise
extension of `T` is contradictory, then so is `T`. -/
theorem right_nd {A : Formula} {ps} (h : rightPremises A = some ps) {T : Theory}
    (hA : T ⊢ neg A) (hp : ∀ p ∈ ps, ext T p ⊢ bot) : T ⊢ bot := by
  cases A <;> simp [rightPremises] at h <;> subst h
  case imp A B =>
    have h₁ := hp ([A], [B]) (by simp)
    have : Theory.insert T A ⊢ B :=
      Derives.raa (h₁.weaken (by intro ψ; simp [ext, Theory.insert]; grind))
    exact Derives.negE hA (Derives.impI this)
  case conj A B =>
    have h₁ := hp ([], [A]) (by simp)
    have h₂ := hp ([], [B]) (by simp)
    have hA' : T ⊢ A := Derives.raa (h₁.weaken (by intro ψ; simp [ext, Theory.insert]; grind))
    have hB' : T ⊢ B := Derives.raa (h₂.weaken (by intro ψ; simp [ext, Theory.insert]; grind))
    exact Derives.negE hA (Derives.conjI hA' hB')
  case disj A B =>
    have h₁ := hp ([], [A, B]) (by simp)
    have hB : Theory.insert T (neg A) ⊢ B :=
      Derives.raa (h₁.weaken (by intro ψ; simp [ext, Theory.insert]; grind))
    have hAB : T ⊢ disj A B :=
      Derives.byCases (Derives.disjI₁ (Derives.assume _ _)) (Derives.disjI₂ hB)
    exact Derives.negE hA hAB

/-- **From LK to natural deduction.** If `Γ ⊢ Δ` is derivable in `LK`, then `Γ`
together with the negations of `Δ` derives `⊥` in natural deduction. -/
theorem LK.toDerives {Γ Δ : List Formula} (h : LK Γ Δ) : ctx Γ Δ ⊢ bot := by
  induction h with
  | @ax Γ Δ A h₁ h₂ =>
      exact Derives.negE (Derives.hyp (Or.inr ⟨A, h₂, rfl⟩)) (Derives.hyp (Or.inl h₁))
  | @left Γ Δ A ps hA hps _ ih =>
      refine left_nd hps (Derives.hyp (Or.inl hA)) (fun p hp => (ih p hp).weaken ?_)
      intro ψ hψ
      simp only [ctx, ext, List.mem_append] at hψ ⊢
      grind
  | @right Γ Δ A ps hA hps _ ih =>
      refine right_nd hps (Derives.hyp (Or.inr ⟨A, hA, rfl⟩)) (fun p hp => (ih p hp).weaken ?_)
      intro ψ hψ
      simp only [ctx, ext, List.mem_append] at hψ ⊢
      grind
  | weak _ hΓ hΔ ih =>
      refine ih.weaken ?_
      intro ψ hψ
      rcases hψ with hψ | ⟨B, hB, rfl⟩
      · exact Or.inl (hΓ hψ)
      · exact Or.inr ⟨B, hΔ hB, rfl⟩
  | @cut Γ Δ A _ _ ih₁ ih₂ =>
      have hA : ctx Γ Δ ⊢ A := Derives.raa (ih₁.weaken (by
        intro ψ hψ; simp only [ctx, Theory.insert, List.mem_cons] at hψ ⊢; grind))
      exact Derives.cut hA (ih₂.weaken (by
        intro ψ hψ; simp only [ctx, Theory.insert, List.mem_cons] at hψ ⊢; grind))

/-- An `LK`-derivation of `Γ ⊢ φ` yields a natural-deduction derivation of `φ` from
the premises `Γ`. -/
theorem LK.toDerives_single {Γ : List Formula} {φ : Formula} (h : LK Γ [φ]) :
    Theory.ofList Γ ⊢ φ :=
  Derives.raa (h.toDerives.weaken (by
    intro ψ hψ; simp only [ctx, Theory.insert, Theory.ofList, List.mem_singleton] at hψ ⊢
    grind))

/-! ## From natural deduction to LK -/

/-- **From natural deduction to LK.** If `φ` is derivable from premises `Γ` and all
of these premises are listed in `L`, then `L ⊢ φ` is derivable in `LK`. Each
elimination rule becomes a cut against a left rule. -/
theorem _root_.Foundations.Logic.Derives.toLK {Γ : Theory} {φ : Formula} (h : Γ ⊢ φ) :
    ∀ L : List Formula, (∀ ψ, Γ ψ → ψ ∈ L) → LK L [φ] := by
  induction h with
  | hyp hφ => exact fun L hL => LK.ax (hL _ hφ) (by simp)
  | @impI Γ φ ψ _ ih =>
      intro L hL
      have := ih (φ :: L) (by intro χ hχ; rcases hχ with rfl | hχ <;> simp [hL _, *])
      exact LK.impR (A := φ) (B := ψ) (by simp) (LK.weak this (by grind) (by grind))
  | @impE Γ φ ψ _ _ ih₁ ih₂ =>
      intro L hL
      refine LK.cut (imp φ ψ) (LK.weak (ih₁ L hL) (by grind) (by grind)) ?_
      exact LK.impL (A := φ) (B := ψ) (by simp)
        (LK.weak (ih₂ L hL) (by grind) (by grind)) (LK.ax (A := ψ) (by simp) (by simp))
  | @conjI Γ φ ψ _ _ ih₁ ih₂ =>
      intro L hL
      exact LK.conjR (A := φ) (B := ψ) (by simp)
        (LK.weak (ih₁ L hL) (by grind) (by grind)) (LK.weak (ih₂ L hL) (by grind) (by grind))
  | @conjE₁ Γ φ ψ _ ih =>
      intro L hL
      refine LK.cut (conj φ ψ) (LK.weak (ih L hL) (by grind) (by grind)) ?_
      exact LK.conjL (A := φ) (B := ψ) (by simp) (LK.ax (A := φ) (by simp) (by simp))
  | @conjE₂ Γ φ ψ _ ih =>
      intro L hL
      refine LK.cut (conj φ ψ) (LK.weak (ih L hL) (by grind) (by grind)) ?_
      exact LK.conjL (A := φ) (B := ψ) (by simp) (LK.ax (A := ψ) (by simp) (by simp))
  | @disjI₁ Γ φ ψ _ ih =>
      intro L hL
      exact LK.disjR (A := φ) (B := ψ) (by simp) (LK.weak (ih L hL) (by grind) (by grind))
  | @disjI₂ Γ φ ψ _ ih =>
      intro L hL
      exact LK.disjR (A := φ) (B := ψ) (by simp) (LK.weak (ih L hL) (by grind) (by grind))
  | @disjE Γ φ ψ χ _ _ _ ih₁ ih₂ ih₃ =>
      intro L hL
      have h₂ := ih₂ (φ :: L) (by intro θ hθ; rcases hθ with rfl | hθ <;> simp [hL _, *])
      have h₃ := ih₃ (ψ :: L) (by intro θ hθ; rcases hθ with rfl | hθ <;> simp [hL _, *])
      refine LK.cut (disj φ ψ) (LK.weak (ih₁ L hL) (by grind) (by grind)) ?_
      exact LK.disjL (A := φ) (B := ψ) (by simp)
        (LK.weak h₂ (by grind) (by grind)) (LK.weak h₃ (by grind) (by grind))
  | @botE Γ φ _ ih =>
      intro L hL
      exact LK.cut bot (LK.weak (ih L hL) (by grind) (by grind)) (LK.botL (by simp))
  | @raa Γ φ _ ih =>
      intro L hL
      have h₁ := ih (neg φ :: L) (by intro θ hθ; rcases hθ with rfl | hθ <;> simp [hL _, *])
      -- `L ⊢ ¬φ, φ`
      have h₂ : LK L [neg φ, φ] :=
        LK.impR (A := φ) (B := bot) (by simp [neg]) (LK.ax (A := φ) (by simp) (by simp))
      refine LK.cut (neg φ) h₂ ?_
      exact LK.cut bot (LK.weak h₁ (by grind) (by grind)) (LK.botL (by simp))

/-- **LK and natural deduction agree** on finite sets of premises:
`Γ ⊢ φ` is derivable in `LK` iff `φ` is derivable from `Γ` by natural deduction. -/
theorem LK_iff_derives (Γ : List Formula) (φ : Formula) :
    LK Γ [φ] ↔ Theory.ofList Γ ⊢ φ :=
  ⟨LK.toDerives_single, fun h => h.toLK Γ (fun _ hψ => hψ)⟩

/-- **LK and natural deduction prove the same formulas.** -/
theorem LK_iff_derives_empty (φ : Formula) : LK [] [φ] ↔ Theory.empty ⊢ φ := by
  rw [LK_iff_derives]
  exact ⟨fun h => h.weaken (fun _ h => by simp [Theory.ofList] at h),
    fun h => h.weaken (fun _ h => h.elim)⟩

/-- **Analytic proofs for natural deduction.** `φ` is derivable by natural deduction
from a (possibly infinite) theory `Γ` iff some finite list `L` of premises from `Γ`
gives a *cut-free* sequent derivation of `L ⊢ φ` — which by the subformula property
mentions only subformulas of `L` and `φ`. -/
theorem derives_iff_cutFree {Γ : Theory} {φ : Formula} :
    Γ ⊢ φ ↔ ∃ L : List Formula, (∀ ψ ∈ L, Γ ψ) ∧ CutFree L [φ] := by
  constructor
  · intro h
    obtain ⟨L, hL, hd⟩ := h.finite_premises
    exact ⟨L, hL, cut_elimination ((LK_iff_derives L φ).2 hd)⟩
  · rintro ⟨L, hL, hd⟩
    exact (LK.toDerives_single hd.toLK).weaken (fun ψ hψ => hL ψ hψ)

end Foundations.Logic.Sequent
