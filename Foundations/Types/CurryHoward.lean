import Foundations.Types.Normalization

/-!
# Propositions as types: the Curry–Howard correspondence

Read the simple types as *formulas* of propositional logic: an atom is a
propositional variable, `A → B` is implication, `A × B` conjunction, `A + B`
disjunction, `⊥` falsity (and `¬A` abbreviates `A → ⊥`). Then the typing rules
of the simply typed λ-calculus are, letter for letter, the rules of Gentzen's
**natural deduction** (1934) for intuitionistic propositional logic, once the
terms are erased: `λ` is implication introduction, application is *modus
ponens*, pairing and projections are the rules for `∧`, injections and case
analysis the rules for `∨`, and `absurd` is *ex falso quodlibet*.

So a term of type `A` *is* a proof of `A`. This is the **Curry–Howard
correspondence**, observed by Curry (1934, for combinators and Hilbert-style
axioms) and made precise by Howard (1969, circulated as a manuscript, published
1980) for natural deduction. It gives formal content to the
**Brouwer–Heyting–Kolmogorov** explanation of the intuitionistic connectives: a
proof of `A → B` is a construction transforming proofs of `A` into proofs of
`B`; a proof of `A ∨ B` is a proof of one of them *together with the
information which one*; there is no proof of `⊥`.

The correspondence goes deeper than provability. **Computation is proof
simplification**: a β-redex `(λx. t) u` is an introduction immediately followed
by an elimination — a detour, or *cut*, in the proof — and contracting it is
Prawitz's (1965) step of normalization of natural deduction proofs. A normal
term is a *normal* (cut-free) proof, which has the *subformula property*. So
the normalization theorem of `Normalization.lean` *is* the cut-elimination (or
normalization) theorem for intuitionistic natural deduction.

We prove:

* **Curry–Howard**: `Γ ⊢ A` in natural deduction iff some term has type `A` in
  context `Γ` (erasing terms in one direction, extracting them in the other).
* **Normal terms ↔ normal proofs**: normal well-typed terms correspond to
  derivations in the *intercalation calculus* (`Nf`/`Ne`): introductions applied
  on top of chains of eliminations from hypotheses.
* **Cut elimination**: every provable formula has a normal proof — via
  normalization of terms.
* Consequences read off from the shape of normal proofs: intuitionistic logic
  is consistent and does not prove the **law of excluded middle** `A ∨ ¬A`,
  **Peirce's law** `((A → B) → A) → A` (for distinct atoms `A`, `B`), or
  **double-negation elimination** `¬¬A → A` (here the normal-form analysis is
  combined with soundness for classical truth tables) — although it does prove
  `¬¬(A ∨ ¬A)`, for which we exhibit the term.
  Brouwer's rejection of excluded middle thus becomes a theorem about a formal
  system.

Lean itself rests on the same idea, scaled up: in its dependent type theory
(a descendant of Martin-Löf's and of Coquand–Huet's calculus of constructions)
propositions are types and proofs are terms, and the kernel checks a proof by
type-checking a term. Unlike this file's system, Lean's logic also includes the
axiom `Classical.choice`, from which excluded middle is derived.
-/

namespace Foundations.Types

namespace STLC

open Term

/-! ## Formulas and natural deduction -/

/-- **Formulas** of intuitionistic propositional logic are simple types. -/
abbrev Formula := Ty

/-- Negation `¬A := A → ⊥`. -/
abbrev neg (A : Formula) : Formula := .arr A .bot

/-- **Natural deduction** for intuitionistic propositional logic: `ND Γ A` means
`A` is derivable from the hypotheses `Γ`. -/
inductive ND : List Formula → Formula → Prop
  /-- Use a hypothesis. -/
  | hyp {Γ : List Formula} {n : Nat} {A : Formula} : Γ[n]? = some A → ND Γ A
  /-- `→`-introduction (discharging a hypothesis). -/
  | impI {Γ : List Formula} {A B : Formula} : ND (A :: Γ) B → ND Γ (.arr A B)
  /-- `→`-elimination (modus ponens). -/
  | impE {Γ : List Formula} {A B : Formula} : ND Γ (.arr A B) → ND Γ A → ND Γ B
  /-- `∧`-introduction. -/
  | andI {Γ : List Formula} {A B : Formula} : ND Γ A → ND Γ B → ND Γ (.prod A B)
  /-- `∧`-elimination, left. -/
  | andE₁ {Γ : List Formula} {A B : Formula} : ND Γ (.prod A B) → ND Γ A
  /-- `∧`-elimination, right. -/
  | andE₂ {Γ : List Formula} {A B : Formula} : ND Γ (.prod A B) → ND Γ B
  /-- `∨`-introduction, left. -/
  | orI₁ {Γ : List Formula} {A B : Formula} : ND Γ A → ND Γ (.sum A B)
  /-- `∨`-introduction, right. -/
  | orI₂ {Γ : List Formula} {A B : Formula} : ND Γ B → ND Γ (.sum A B)
  /-- `∨`-elimination (proof by cases). -/
  | orE {Γ : List Formula} {A B C : Formula} :
      ND Γ (.sum A B) → ND (A :: Γ) C → ND (B :: Γ) C → ND Γ C
  /-- `⊥`-elimination (ex falso quodlibet). -/
  | botE {Γ : List Formula} {C : Formula} : ND Γ .bot → ND Γ C

/-- **Terms are proofs**: erasing the term from a typing derivation leaves a
natural deduction derivation. -/
theorem HasType.toND {Γ : Ctx} {t : Term} {A : Ty} (h : HasType Γ t A) : ND Γ A := by
  induction h with
  | var hn => exact .hyp hn
  | lam _ ih => exact .impI ih
  | app _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | fst _ ih => exact .andE₁ ih
  | snd _ ih => exact .andE₂ ih
  | inl _ ih => exact .orI₁ ih
  | inr _ ih => exact .orI₂ ih
  | case _ _ _ ih ih₁ ih₂ => exact .orE ih ih₁ ih₂
  | absurd _ ih => exact .botE ih

/-- **Proofs are terms**: every natural deduction derivation can be decorated with
a λ-term. -/
theorem ND.toTerm {Γ : List Formula} {A : Formula} (h : ND Γ A) : ∃ t, HasType Γ t A := by
  induction h with
  | hyp hn => exact ⟨_, .var hn⟩
  | impI _ ih => obtain ⟨t, ht⟩ := ih; exact ⟨_, .lam ht⟩
  | impE _ _ ih₁ ih₂ =>
    obtain ⟨t, ht⟩ := ih₁; obtain ⟨u, hu⟩ := ih₂; exact ⟨_, .app ht hu⟩
  | andI _ _ ih₁ ih₂ =>
    obtain ⟨t, ht⟩ := ih₁; obtain ⟨u, hu⟩ := ih₂; exact ⟨_, .pair ht hu⟩
  | andE₁ _ ih => obtain ⟨t, ht⟩ := ih; exact ⟨_, .fst ht⟩
  | andE₂ _ ih => obtain ⟨t, ht⟩ := ih; exact ⟨_, .snd ht⟩
  | orI₁ _ ih => obtain ⟨t, ht⟩ := ih; exact ⟨_, .inl ht⟩
  | orI₂ _ ih => obtain ⟨t, ht⟩ := ih; exact ⟨_, .inr ht⟩
  | orE _ _ _ ih ih₁ ih₂ =>
    obtain ⟨t, ht⟩ := ih; obtain ⟨u₁, hu₁⟩ := ih₁; obtain ⟨u₂, hu₂⟩ := ih₂
    exact ⟨_, .case ht hu₁ hu₂⟩
  | botE _ ih => obtain ⟨t, ht⟩ := ih; exact ⟨_, .absurd ht⟩

/-- **The Curry–Howard correspondence.** A formula is provable in intuitionistic
natural deduction from hypotheses `Γ` exactly when the corresponding type is
inhabited in context `Γ`. -/
theorem curry_howard {Γ : List Formula} {A : Formula} : ND Γ A ↔ ∃ t, HasType Γ t A :=
  ⟨ND.toTerm, fun ⟨_, h⟩ => h.toND⟩

/-! ## Normal proofs -/

mutual
/-- **Neutral derivations**: a chain of eliminations starting from a hypothesis
(the major premises run down the main branch). -/
inductive Ne : List Formula → Formula → Prop
  | hyp {Γ : List Formula} {n : Nat} {A : Formula} : Γ[n]? = some A → Ne Γ A
  | impE {Γ : List Formula} {A B : Formula} : Ne Γ (.arr A B) → Nf Γ A → Ne Γ B
  | andE₁ {Γ : List Formula} {A B : Formula} : Ne Γ (.prod A B) → Ne Γ A
  | andE₂ {Γ : List Formula} {A B : Formula} : Ne Γ (.prod A B) → Ne Γ B
  | orE {Γ : List Formula} {A B C : Formula} :
      Ne Γ (.sum A B) → Nf (A :: Γ) C → Nf (B :: Γ) C → Ne Γ C
  | botE {Γ : List Formula} {C : Formula} : Ne Γ .bot → Ne Γ C

/-- **Normal derivations**: introductions on top of neutral derivations — no
introduction is ever immediately followed by an elimination of the same
connective (no *cuts*, no detours). -/
inductive Nf : List Formula → Formula → Prop
  | ne {Γ : List Formula} {A : Formula} : Ne Γ A → Nf Γ A
  | impI {Γ : List Formula} {A B : Formula} : Nf (A :: Γ) B → Nf Γ (.arr A B)
  | andI {Γ : List Formula} {A B : Formula} : Nf Γ A → Nf Γ B → Nf Γ (.prod A B)
  | orI₁ {Γ : List Formula} {A B : Formula} : Nf Γ A → Nf Γ (.sum A B)
  | orI₂ {Γ : List Formula} {A B : Formula} : Nf Γ B → Nf Γ (.sum A B)
end

mutual
/-- Neutral derivations are derivations. -/
theorem Ne.toND {Γ : List Formula} {A : Formula} : Ne Γ A → ND Γ A
  | .hyp h => .hyp h
  | .impE h₁ h₂ => .impE (Ne.toND h₁) (Nf.toND h₂)
  | .andE₁ h => .andE₁ (Ne.toND h)
  | .andE₂ h => .andE₂ (Ne.toND h)
  | .orE h h₁ h₂ => .orE (Ne.toND h) (Nf.toND h₁) (Nf.toND h₂)
  | .botE h => .botE (Ne.toND h)

/-- Normal derivations are derivations. -/
theorem Nf.toND {Γ : List Formula} {A : Formula} : Nf Γ A → ND Γ A
  | .ne h => Ne.toND h
  | .impI h => .impI (Nf.toND h)
  | .andI h₁ h₂ => .andI (Nf.toND h₁) (Nf.toND h₂)
  | .orI₁ h => .orI₁ (Nf.toND h)
  | .orI₂ h => .orI₂ (Nf.toND h)
end

/-- A typed term that is not an introduction form of the "wrong" shape: a term of
function type that is not a `λ` is neutral. -/
theorem neutral_of_arr {Γ : Ctx} {t : Term} {A B : Ty} (h : HasType Γ t (.arr A B))
    (hl : ∀ s, t ≠ lam s) : Neutral t := by
  cases t with
  | lam s => exact absurd rfl (hl s)
  | pair => cases h
  | inl => cases h
  | inr => cases h
  | _ => exact trivial

/-- A term of product type that is not a pair is neutral. -/
theorem neutral_of_prod {Γ : Ctx} {t : Term} {A B : Ty} (h : HasType Γ t (.prod A B))
    (hp : ∀ a b, t ≠ pair a b) : Neutral t := by
  cases t with
  | pair a b => exact absurd rfl (hp a b)
  | lam => cases h
  | inl => cases h
  | inr => cases h
  | _ => exact trivial

/-- A term of sum type that is not an injection is neutral. -/
theorem neutral_of_sum {Γ : Ctx} {t : Term} {A B : Ty} (h : HasType Γ t (.sum A B))
    (hl : ∀ a, t ≠ inl a) (hr : ∀ a, t ≠ inr a) : Neutral t := by
  cases t with
  | inl a => exact absurd rfl (hl a)
  | inr a => exact absurd rfl (hr a)
  | lam => cases h
  | pair => cases h
  | _ => exact trivial

/-- Every term of the empty type is neutral. -/
theorem neutral_of_bot {Γ : Ctx} {t : Term} (h : HasType Γ t .bot) : Neutral t := by
  cases t with
  | lam => cases h
  | pair => cases h
  | inl => cases h
  | inr => cases h
  | _ => exact trivial

/-- **Normal terms are normal proofs.** A normal well-typed term yields a normal
derivation of its type, and a neutral one a neutral derivation. -/
theorem HasType.toNf {Γ : Ctx} {t : Term} {A : Ty} (h : HasType Γ t A) (hn : Normal t) :
    Nf Γ A ∧ (Neutral t → Ne Γ A) := by
  induction h with
  | var hx => exact ⟨.ne (.hyp hx), fun _ => .hyp hx⟩
  | lam _ ih =>
    exact ⟨.impI (ih fun t' h => hn _ (Step.lam h)).1, fun h => h.elim⟩
  | @app Γ t u A B h₁ _ ih₁ ih₂ =>
    have hneu : Neutral t := neutral_of_arr h₁ (by rintro s rfl; exact hn _ (Step.beta s u))
    have hne := (ih₁ fun t' h => hn _ (Step.appL h)).2 hneu
    have hne' : Ne Γ B := .impE hne (ih₂ fun t' h => hn _ (Step.appR h)).1
    exact ⟨.ne hne', fun _ => hne'⟩
  | pair _ _ ih₁ ih₂ =>
    exact ⟨.andI (ih₁ fun t' h => hn _ (Step.pairL h)).1 (ih₂ fun t' h => hn _ (Step.pairR h)).1,
      fun h => h.elim⟩
  | @fst Γ t A B h ih =>
    have hneu : Neutral t := neutral_of_prod h (by rintro a b rfl; exact hn _ (Step.fstPair a b))
    have hne : Ne Γ A := .andE₁ ((ih fun t' h => hn _ (Step.fst h)).2 hneu)
    exact ⟨.ne hne, fun _ => hne⟩
  | @snd Γ t A B h ih =>
    have hneu : Neutral t := neutral_of_prod h (by rintro a b rfl; exact hn _ (Step.sndPair a b))
    have hne : Ne Γ B := .andE₂ ((ih fun t' h => hn _ (Step.snd h)).2 hneu)
    exact ⟨.ne hne, fun _ => hne⟩
  | inl _ ih => exact ⟨.orI₁ (ih fun t' h => hn _ (Step.inl h)).1, fun h => h.elim⟩
  | inr _ ih => exact ⟨.orI₂ (ih fun t' h => hn _ (Step.inr h)).1, fun h => h.elim⟩
  | @case Γ t u₁ u₂ A B C h _ _ ih ih₁ ih₂ =>
    have hneu : Neutral t := neutral_of_sum h
      (by rintro a rfl; exact hn _ (Step.caseInl a u₁ u₂))
      (by rintro a rfl; exact hn _ (Step.caseInr a u₁ u₂))
    have hne : Ne Γ C := .orE ((ih fun t' h => hn _ (Step.case₀ h)).2 hneu)
      (ih₁ fun t' h => hn _ (Step.case₁ h)).1 (ih₂ fun t' h => hn _ (Step.case₂ h)).1
    exact ⟨.ne hne, fun _ => hne⟩
  | @absurd Γ t C h ih =>
    have hne : Ne Γ C := .botE ((ih fun t' h => hn _ (Step.absurd h)).2 (neutral_of_bot h))
    exact ⟨.ne hne, fun _ => hne⟩

mutual
/-- **Normal proofs are normal terms** (neutral case): a neutral derivation is
decorated by a normal, neutral, well-typed term. -/
theorem Ne.toTerm {Γ : List Formula} {A : Formula} :
    Ne Γ A → ∃ t, HasType Γ t A ∧ Normal t ∧ Neutral t
  | .hyp h => ⟨.var _, .var h, ⟨fun x (hs : Step (.var _) x) => (by cases hs), trivial⟩⟩
  | .impE h₁ h₂ => by
    obtain ⟨t, ht, hn, hneu⟩ := Ne.toTerm h₁
    obtain ⟨u, hu, hnu⟩ := Nf.toTerm h₂
    refine ⟨.app t u, .app ht hu, fun x hx => ?_, trivial⟩
    cases hx with
    | beta => exact hneu
    | appL h => exact hn _ h
    | appR h => exact hnu _ h
  | .andE₁ h => by
    obtain ⟨t, ht, hn, hneu⟩ := Ne.toTerm h
    refine ⟨.fst t, .fst ht, fun x hx => ?_, trivial⟩
    cases hx with
    | fstPair => exact hneu
    | fst h => exact hn _ h
  | .andE₂ h => by
    obtain ⟨t, ht, hn, hneu⟩ := Ne.toTerm h
    refine ⟨.snd t, .snd ht, fun x hx => ?_, trivial⟩
    cases hx with
    | sndPair => exact hneu
    | snd h => exact hn _ h
  | .orE h h₁ h₂ => by
    obtain ⟨t, ht, hn, hneu⟩ := Ne.toTerm h
    obtain ⟨u₁, hu₁, hn₁⟩ := Nf.toTerm h₁
    obtain ⟨u₂, hu₂, hn₂⟩ := Nf.toTerm h₂
    refine ⟨.case t u₁ u₂, .case ht hu₁ hu₂, fun x hx => ?_, trivial⟩
    cases hx with
    | caseInl => exact hneu
    | caseInr => exact hneu
    | case₀ h => exact hn _ h
    | case₁ h => exact hn₁ _ h
    | case₂ h => exact hn₂ _ h
  | .botE h => by
    obtain ⟨t, ht, hn, _⟩ := Ne.toTerm h
    refine ⟨.absurd t, .absurd ht, fun x hx => ?_, trivial⟩
    cases hx with
    | absurd h => exact hn _ h

/-- **Normal proofs are normal terms**: a normal derivation is decorated by a
normal well-typed term. -/
theorem Nf.toTerm {Γ : List Formula} {A : Formula} : Nf Γ A → ∃ t, HasType Γ t A ∧ Normal t
  | .ne h => by
    obtain ⟨t, ht, hn, _⟩ := Ne.toTerm h
    exact ⟨t, ht, hn⟩
  | .impI h => by
    obtain ⟨t, ht, hn⟩ := Nf.toTerm h
    refine ⟨.lam t, .lam ht, fun x hx => ?_⟩
    cases hx with
    | lam h => exact hn _ h
  | .andI h₁ h₂ => by
    obtain ⟨a, ha, hna⟩ := Nf.toTerm h₁
    obtain ⟨b, hb, hnb⟩ := Nf.toTerm h₂
    refine ⟨.pair a b, .pair ha hb, fun x hx => ?_⟩
    cases hx with
    | pairL h => exact hna _ h
    | pairR h => exact hnb _ h
  | .orI₁ h => by
    obtain ⟨a, ha, hna⟩ := Nf.toTerm h
    refine ⟨.inl a, .inl ha, fun x hx => ?_⟩
    cases hx with
    | inl h => exact hna _ h
  | .orI₂ h => by
    obtain ⟨a, ha, hna⟩ := Nf.toTerm h
    refine ⟨.inr a, .inr ha, fun x hx => ?_⟩
    cases hx with
    | inr h => exact hna _ h
end

/-- **Normal terms ↔ normal proofs.** A formula has a normal derivation from `Γ`
exactly when the corresponding type has a normal inhabitant in context `Γ`. -/
theorem nf_iff_normal_term {Γ : List Formula} {A : Formula} :
    Nf Γ A ↔ ∃ t, HasType Γ t A ∧ Normal t :=
  ⟨Nf.toTerm, fun ⟨_, ht, hn⟩ => (ht.toNf hn).1⟩

/-- **Cut elimination** (normalization of natural deduction, Prawitz 1965),
obtained from the normalization of λ-terms: every derivable formula has a normal
derivation. -/
theorem cut_elimination {Γ : List Formula} {A : Formula} (h : ND Γ A) : Nf Γ A := by
  obtain ⟨t, ht⟩ := h.toTerm
  obtain ⟨n, _, hn, hnt⟩ := weak_normalization ht
  exact (hnt.toNf hn).1

/-! ## What intuitionistic logic does not prove -/

/-- With no hypotheses there is no neutral derivation: it would have to start from a
hypothesis. -/
theorem no_closed_ne' : ∀ {Γ : List Formula} {A : Formula}, Ne Γ A → Γ = [] → False
  | _, _, .hyp h, hΓ => by subst hΓ; simp at h
  | _, _, .impE h _, hΓ => no_closed_ne' h hΓ
  | _, _, .andE₁ h, hΓ => no_closed_ne' h hΓ
  | _, _, .andE₂ h, hΓ => no_closed_ne' h hΓ
  | _, _, .orE h _ _, hΓ => no_closed_ne' h hΓ
  | _, _, .botE h, hΓ => no_closed_ne' h hΓ

/-- With no hypotheses there is no neutral derivation. -/
theorem no_closed_ne {A : Formula} (h : Ne [] A) : False := no_closed_ne' h rfl

/-- **Consistency of intuitionistic propositional logic**: `⊥` is not provable. -/
theorem nd_consistent : ¬ ND [] .bot := fun h => by
  cases cut_elimination h with
  | ne h => exact no_closed_ne h

/-- From a single atomic hypothesis only that atom can be derived neutrally. -/
theorem ne_atom_ctx' {k : Nat} : ∀ {Γ : List Formula} {C : Formula},
    Ne Γ C → Γ = [.atom k] → C = .atom k
  | _, _, @Ne.hyp _ n _ h, hΓ => by
    subst hΓ
    cases n with
    | zero => simp at h; exact h.symm
    | succ n => simp at h
  | _, _, .impE h _, hΓ => by have := ne_atom_ctx' h hΓ; cases this
  | _, _, .andE₁ h, hΓ => by have := ne_atom_ctx' h hΓ; cases this
  | _, _, .andE₂ h, hΓ => by have := ne_atom_ctx' h hΓ; cases this
  | _, _, .orE h _ _, hΓ => by have := ne_atom_ctx' h hΓ; cases this
  | _, _, .botE h, hΓ => by have := ne_atom_ctx' h hΓ; cases this

/-- From a single atomic hypothesis only that atom can be derived neutrally. -/
theorem ne_atom_ctx {k : Nat} {C : Formula} (h : Ne [.atom k] C) : C = .atom k :=
  ne_atom_ctx' h rfl

/-- There is no normal proof of excluded middle `A ∨ ¬A` for an atom `A`. -/
theorem no_nf_lem (k : Nat) : ¬ Nf [] (.sum (.atom k) (neg (.atom k))) := by
  intro h
  cases h with
  | ne h => exact no_closed_ne h
  | orI₁ h => cases h with
    | ne h => exact no_closed_ne h
  | orI₂ h => cases h with
    | ne h => exact no_closed_ne h
    | impI h => cases h with
      | ne h => have := ne_atom_ctx h; cases this

/-- **Intuitionistic logic does not prove the law of excluded middle.** For an atom
`A`, the formula `A ∨ ¬A` is not derivable in natural deduction. (Its normal
proof would have to end with `∨`-introduction, and neither `A` nor `¬A` is
provable outright.) -/
theorem lem_unprovable (k : Nat) : ¬ ND [] (.sum (.atom k) (neg (.atom k))) :=
  fun h => no_nf_lem k (cut_elimination h)

/-- Equivalently: the type `A + (A → ⊥)` has no closed inhabitant. -/
theorem no_closed_lem_term (k : Nat) : ¬ ∃ t, HasType [] t (.sum (.atom k) (neg (.atom k))) :=
  fun ⟨_, h⟩ => lem_unprovable k h.toND

/-- But the **double negation of excluded middle** is provable, by the term
`λk. k (inr (λa. k (inl a)))`: intuitionistic logic cannot refute excluded middle. -/
theorem nn_lem (A : Formula) :
    HasType [] (lam (app (var 0) (inr (lam (app (var 1) (inl (var 0)))))))
      (neg (neg (.sum A (neg A)))) :=
  .lam (.app (.var rfl) (.inr (.lam (.app (.var rfl) (.inl (.var rfl))))))

/-- Neutral derivations from the single hypothesis `(A → B) → A`. -/
theorem ne_peirce_ctx' {i j : Nat} : ∀ {Γ : List Formula} {C : Formula}, Ne Γ C →
    Γ = [.arr (.arr (.atom i) (.atom j)) (.atom i)] →
      C = .arr (.arr (.atom i) (.atom j)) (.atom i) ∨
      (C = .atom i ∧ Nf Γ (.arr (.atom i) (.atom j)))
  | _, _, @Ne.hyp _ n _ h, hΓ => by
    subst hΓ
    cases n with
    | zero => simp at h; exact Or.inl h.symm
    | succ n => simp at h
  | _, _, .impE h hu, hΓ => by
    rcases ne_peirce_ctx' h hΓ with he | ⟨he, _⟩
    · cases he; exact Or.inr ⟨rfl, hu⟩
    · cases he
  | _, _, .andE₁ h, hΓ => by rcases ne_peirce_ctx' h hΓ with he | ⟨he, _⟩ <;> cases he
  | _, _, .andE₂ h, hΓ => by rcases ne_peirce_ctx' h hΓ with he | ⟨he, _⟩ <;> cases he
  | _, _, .orE h _ _, hΓ => by rcases ne_peirce_ctx' h hΓ with he | ⟨he, _⟩ <;> cases he
  | _, _, .botE h, hΓ => by rcases ne_peirce_ctx' h hΓ with he | ⟨he, _⟩ <;> cases he

/-- Neutral derivations from the single hypothesis `(A → B) → A`. -/
theorem ne_peirce_ctx {i j : Nat} {C : Formula}
    (h : Ne [.arr (.arr (.atom i) (.atom j)) (.atom i)] C) :
      C = .arr (.arr (.atom i) (.atom j)) (.atom i) ∨
      (C = .atom i ∧ Nf [.arr (.arr (.atom i) (.atom j)) (.atom i)] (.arr (.atom i) (.atom j))) :=
  ne_peirce_ctx' h rfl

/-- Neutral derivations from the hypotheses `A` and `(A → B) → A`. -/
theorem ne_peirce_ctx₂' {i j : Nat} : ∀ {Γ : List Formula} {C : Formula}, Ne Γ C →
    Γ = [.atom i, .arr (.arr (.atom i) (.atom j)) (.atom i)] →
      C = .atom i ∨ C = .arr (.arr (.atom i) (.atom j)) (.atom i)
  | _, _, @Ne.hyp _ n _ h, hΓ => by
    subst hΓ
    match n, h with
    | 0, h => simp at h; exact Or.inl h.symm
    | 1, h => simp at h; exact Or.inr h.symm
    | n + 2, h => simp at h
  | _, _, .impE h _, hΓ => by
    rcases ne_peirce_ctx₂' h hΓ with he | he
    · cases he
    · cases he; exact Or.inl rfl
  | _, _, .andE₁ h, hΓ => by rcases ne_peirce_ctx₂' h hΓ with he | he <;> cases he
  | _, _, .andE₂ h, hΓ => by rcases ne_peirce_ctx₂' h hΓ with he | he <;> cases he
  | _, _, .orE h _ _, hΓ => by rcases ne_peirce_ctx₂' h hΓ with he | he <;> cases he
  | _, _, .botE h, hΓ => by rcases ne_peirce_ctx₂' h hΓ with he | he <;> cases he

/-- Neutral derivations from the hypotheses `A` and `(A → B) → A`. -/
theorem ne_peirce_ctx₂ {i j : Nat} {C : Formula}
    (h : Ne [.atom i, .arr (.arr (.atom i) (.atom j)) (.atom i)] C) :
    C = .atom i ∨ C = .arr (.arr (.atom i) (.atom j)) (.atom i) :=
  ne_peirce_ctx₂' h rfl

/-- **Intuitionistic logic does not prove Peirce's law** `((A → B) → A) → A`, for
distinct atoms `A` and `B`. -/
theorem peirce_unprovable {i j : Nat} (hij : i ≠ j) :
    ¬ ND [] (.arr (.arr (.arr (.atom i) (.atom j)) (.atom i)) (.atom i)) := by
  intro h
  cases cut_elimination h with
  | ne h => exact no_closed_ne h
  | impI h =>
    cases h with
    | ne h =>
      rcases ne_peirce_ctx h with he | ⟨_, hnf⟩
      · cases he
      · cases hnf with
        | ne h' => rcases ne_peirce_ctx h' with he | ⟨he, _⟩ <;> cases he
        | impI h' => cases h' with
          | ne h'' =>
            rcases ne_peirce_ctx₂ h'' with he | he
            · cases he; exact hij rfl
            · cases he

/-- **Truth-table semantics**: the classical truth value of a formula under a
valuation of the atoms. -/
def Holds (v : Nat → Bool) : Formula → Prop
  | .atom n => v n = true
  | .bot => False
  | .arr A B => Holds v A → Holds v B
  | .prod A B => Holds v A ∧ Holds v B
  | .sum A B => Holds v A ∨ Holds v B

/-- **Soundness for truth tables.** Whatever is derivable from true hypotheses is true. -/
theorem ND.sound {Γ : List Formula} {A : Formula} (h : ND Γ A) (v : Nat → Bool) :
    (∀ B ∈ Γ, Holds v B) → Holds v A := by
  induction h with
  | hyp hn => intro hΓ; exact hΓ _ (List.mem_of_getElem? hn)
  | impI _ ih =>
    intro hΓ ha
    exact ih fun B hB => by
      rcases List.mem_cons.1 hB with rfl | hB
      · exact ha
      · exact hΓ B hB
  | impE _ _ ih₁ ih₂ => intro hΓ; exact ih₁ hΓ (ih₂ hΓ)
  | andI _ _ ih₁ ih₂ => intro hΓ; exact ⟨ih₁ hΓ, ih₂ hΓ⟩
  | andE₁ _ ih => intro hΓ; exact (ih hΓ).1
  | andE₂ _ ih => intro hΓ; exact (ih hΓ).2
  | orI₁ _ ih => intro hΓ; exact Or.inl (ih hΓ)
  | orI₂ _ ih => intro hΓ; exact Or.inr (ih hΓ)
  | orE _ _ _ ih ih₁ ih₂ =>
    intro hΓ
    rcases ih hΓ with ha | hb
    · exact ih₁ fun B hB => by
        rcases List.mem_cons.1 hB with rfl | hB
        · exact ha
        · exact hΓ B hB
    · exact ih₂ fun B hB => by
        rcases List.mem_cons.1 hB with rfl | hB
        · exact hb
        · exact hΓ B hB
  | botE _ ih => intro hΓ; exact (ih hΓ).elim

/-- Neutral derivations from the single hypothesis `¬¬A`: either the hypothesis
itself, or the derivation passed through a proof of `¬A`. -/
theorem ne_dne_ctx' {k : Nat} : ∀ {Γ : List Formula} {C : Formula}, Ne Γ C →
    Γ = [neg (neg (.atom k))] → C = neg (neg (.atom k)) ∨ ND Γ (neg (.atom k))
  | _, _, @Ne.hyp _ n _ h, hΓ => by
    subst hΓ
    cases n with
    | zero => simp at h; exact Or.inl h.symm
    | succ n => simp at h
  | _, _, .impE h hu, hΓ => by
    rcases ne_dne_ctx' h hΓ with he | hnd
    · cases he; exact Or.inr hu.toND
    · exact Or.inr hnd
  | _, _, .andE₁ h, hΓ => by
    rcases ne_dne_ctx' h hΓ with he | hnd
    · cases he
    · exact Or.inr hnd
  | _, _, .andE₂ h, hΓ => by
    rcases ne_dne_ctx' h hΓ with he | hnd
    · cases he
    · exact Or.inr hnd
  | _, _, .orE h _ _, hΓ => by
    rcases ne_dne_ctx' h hΓ with he | hnd
    · cases he
    · exact Or.inr hnd
  | _, _, .botE h, hΓ => by
    rcases ne_dne_ctx' h hΓ with he | hnd
    · cases he
    · exact Or.inr hnd

/-- **Intuitionistic logic does not prove double-negation elimination** `¬¬A → A`.
A normal proof would derive `A` from `¬¬A` by eliminations, which forces a proof of
`¬A` from `¬¬A` — impossible, since making `A` true makes `¬¬A` true and `¬A`
false. (Here cut elimination and truth tables work together.) -/
theorem dne_unprovable (k : Nat) : ¬ ND [] (.arr (neg (neg (.atom k))) (.atom k)) := by
  intro h
  cases cut_elimination h with
  | ne h => exact no_closed_ne h
  | impI h =>
    cases h with
    | ne h =>
      rcases ne_dne_ctx' h rfl with he | hnd
      · cases he
      · exact hnd.sound (fun _ => true) (fun B hB => by
          simp only [List.mem_singleton] at hB
          subst hB
          exact fun hna => hna rfl) rfl

end STLC

end Foundations.Types
