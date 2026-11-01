import Foundations.Types.Lambda

/-!
# The simply typed λ-calculus

The untyped λ-calculus is too liberal to serve as a logic: Curry's paradox
(1942) and the Kleene–Rosser paradox (1935) showed that Church's original
system, which combined λ-terms with logical constants, was inconsistent, and
`Ω` shows that computation need not end. Church's remedy (1940) was to add
**types**, in the spirit of Russell's theory of types: every term gets a type,
and a function of type `A → B` may only be applied to an argument of type `A`.
Self-application `x x` becomes ill-typed, and with it `Ω`.

Here we study the **simply typed λ-calculus** with function types `A → B`,
products `A × B` (pairs, with projections), sums `A + B` (tagged alternatives,
with case analysis) and the empty type `⊥` (with "ex falso" elimination), over
a supply of atomic types. We present it *à la Curry*: terms are untyped (with
de Bruijn indices, as in `Lambda.lean`), and a separate judgement
`Γ ⊢ t : A` assigns types, where the context `Γ` lists the types of the free
variables `0, 1, 2, …`.

The two basic metatheorems, the slogan of which is Milner's *well-typed
programs cannot go wrong*, are:

* **Subject reduction (preservation).** Reduction preserves types: if
  `Γ ⊢ t : A` and `t ⟶ t'` then `Γ ⊢ t' : A`. The heart of the proof is the
  *substitution lemma*: substituting well-typed terms for variables preserves
  typing.
* **Progress.** A closed well-typed term is either a *value* (an introduction
  form: a `λ`, a pair, or an injection) or can take a step. A closed term never
  gets "stuck" in a meaningless state such as applying a pair to an argument.

Lean's own kernel is a vastly extended relative of this system — dependent
types, universes and inductive types — and its soundness rests on metatheorems
of exactly this kind.
-/

namespace Foundations.Types

namespace STLC

/-! ## Types and terms -/

/-- **Simple types**: atoms, the empty type, functions, products and sums. -/
inductive Ty where
  /-- An atomic type (a propositional variable, under Curry–Howard). -/
  | atom (n : Nat)
  /-- The empty type `⊥`. -/
  | bot
  /-- Function type `A → B`. -/
  | arr (A B : Ty)
  /-- Product type `A × B`. -/
  | prod (A B : Ty)
  /-- Sum type `A + B`. -/
  | sum (A B : Ty)
  deriving DecidableEq, Repr

/-- **Terms** of the simply typed λ-calculus (untyped syntax, de Bruijn indices). -/
inductive Term where
  /-- Variable. -/
  | var (n : Nat)
  /-- Application `t u`. -/
  | app (t u : Term)
  /-- Abstraction `λ. t` (binds variable `0` in `t`). -/
  | lam (t : Term)
  /-- Pair `⟨a, b⟩`. -/
  | pair (a b : Term)
  /-- First projection. -/
  | fst (t : Term)
  /-- Second projection. -/
  | snd (t : Term)
  /-- Left injection. -/
  | inl (t : Term)
  /-- Right injection. -/
  | inr (t : Term)
  /-- Case analysis `case t of inl ⇒ u₁ | inr ⇒ u₂` (each branch binds variable `0`). -/
  | case (t u₁ u₂ : Term)
  /-- Ex falso: from a term of the empty type, anything. -/
  | absurd (t : Term)
  deriving DecidableEq, Repr

open Term

/-! ## Renaming and substitution -/

/-- Lifting a renaming under a binder. -/
def upRen (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

/-- Renaming free variables. -/
def rename (ξ : Nat → Nat) : Term → Term
  | var n => var (ξ n)
  | app t u => app (rename ξ t) (rename ξ u)
  | lam t => lam (rename (upRen ξ) t)
  | pair a b => pair (rename ξ a) (rename ξ b)
  | fst t => fst (rename ξ t)
  | snd t => snd (rename ξ t)
  | inl t => inl (rename ξ t)
  | inr t => inr (rename ξ t)
  | case t u₁ u₂ => case (rename ξ t) (rename (upRen ξ) u₁) (rename (upRen ξ) u₂)
  | .absurd t => .absurd (rename ξ t)

/-- Lifting a substitution under a binder. -/
def up (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Simultaneous substitution. -/
def subst (σ : Nat → Term) : Term → Term
  | var n => σ n
  | app t u => app (subst σ t) (subst σ u)
  | lam t => lam (subst (up σ) t)
  | pair a b => pair (subst σ a) (subst σ b)
  | fst t => fst (subst σ t)
  | snd t => snd (subst σ t)
  | inl t => inl (subst σ t)
  | inr t => inr (subst σ t)
  | case t u₁ u₂ => case (subst σ t) (subst (up σ) u₁) (subst (up σ) u₂)
  | .absurd t => .absurd (subst σ t)

/-- Extending a substitution: `0 ↦ u`, `n + 1 ↦ σ n`. -/
def cons (u : Term) (σ : Nat → Term) : Nat → Term
  | 0 => u
  | n + 1 => σ n

/-- Single substitution `t[u]` for variable `0`. -/
def inst (t u : Term) : Term := subst (cons u var) t

/-- Lifting commutes with composition of renamings. -/
theorem upRen_comp (ξ ζ : Nat → Nat) : upRen ξ ∘ upRen ζ = upRen (ξ ∘ ζ) := by
  funext n; cases n <;> rfl

/-- Renamings compose. -/
theorem rename_rename (t : Term) : ∀ ξ ζ, rename ξ (rename ζ t) = rename (ξ ∘ ζ) t := by
  induction t <;> intros <;> simp only [rename, upRen_comp, Function.comp_apply, *]

/-- Lifting a substitution after a lifted renaming. -/
theorem up_upRen (σ : Nat → Term) (ξ : Nat → Nat) : up σ ∘ upRen ξ = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

/-- Substitution after renaming. -/
theorem subst_rename (t : Term) : ∀ σ ξ, subst σ (rename ξ t) = subst (σ ∘ ξ) t := by
  induction t <;> intros <;> simp only [rename, subst, up_upRen, *] <;> rfl

/-- A lifted renaming after a lifted substitution. -/
theorem rename_up (ξ : Nat → Nat) (σ : Nat → Term) :
    rename (upRen ξ) ∘ up σ = up (rename ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Function.comp, up, rename_rename]; rfl

/-- Renaming after substitution. -/
theorem rename_subst (t : Term) : ∀ ξ σ, rename ξ (subst σ t) = subst (rename ξ ∘ σ) t := by
  induction t <;> intros <;> simp only [rename, subst, rename_up, *] <;> rfl

/-- Lifting commutes with composition of substitutions. -/
theorem up_comp (τ σ : Nat → Term) : subst (up τ) ∘ up σ = up (subst τ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Function.comp, up, subst_rename, rename_subst]; rfl

/-- Substitutions compose. -/
theorem subst_subst (t : Term) : ∀ τ σ, subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  induction t <;> intros <;> simp only [subst, up_comp, *] <;> rfl

/-- Lifting the identity substitution gives the identity. -/
theorem up_var : up var = var := by
  funext n; cases n <;> rfl

/-- The identity substitution does nothing. -/
theorem subst_var (t : Term) : subst var t = t := by
  induction t <;> simp only [subst, up_var, *]

/-- Substitution commutes with single substitution. -/
theorem subst_inst (σ : Nat → Term) (t u : Term) :
    subst σ (inst t u) = inst (subst (up σ) t) (subst σ u) := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, cons, subst_rename]
    exact (subst_var _).symm

/-- Substituting for variable `0` after going under a binder: `(t (up σ))[u] = t (u · σ)`. -/
theorem inst_up (σ : Nat → Term) (t u : Term) : inst (subst (up σ) t) u = subst (cons u σ) t := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, cons, subst_rename]
    exact subst_var _

/-! ## Typing -/

/-- A **context**: the types of the free variables `0, 1, 2, …`. -/
abbrev Ctx := List Ty

/-- The **typing judgement** `Γ ⊢ t : A`. -/
inductive HasType : Ctx → Term → Ty → Prop
  | var {Γ : Ctx} {n : Nat} {A : Ty} : Γ[n]? = some A → HasType Γ (var n) A
  | lam {Γ : Ctx} {t : Term} {A B : Ty} : HasType (A :: Γ) t B → HasType Γ (lam t) (.arr A B)
  | app {Γ : Ctx} {t u : Term} {A B : Ty} :
      HasType Γ t (.arr A B) → HasType Γ u A → HasType Γ (app t u) B
  | pair {Γ : Ctx} {a b : Term} {A B : Ty} :
      HasType Γ a A → HasType Γ b B → HasType Γ (pair a b) (.prod A B)
  | fst {Γ : Ctx} {t : Term} {A B : Ty} : HasType Γ t (.prod A B) → HasType Γ (fst t) A
  | snd {Γ : Ctx} {t : Term} {A B : Ty} : HasType Γ t (.prod A B) → HasType Γ (snd t) B
  | inl {Γ : Ctx} {t : Term} {A B : Ty} : HasType Γ t A → HasType Γ (inl t) (.sum A B)
  | inr {Γ : Ctx} {t : Term} {A B : Ty} : HasType Γ t B → HasType Γ (inr t) (.sum A B)
  | case {Γ : Ctx} {t u₁ u₂ : Term} {A B C : Ty} :
      HasType Γ t (.sum A B) → HasType (A :: Γ) u₁ C → HasType (B :: Γ) u₂ C →
      HasType Γ (case t u₁ u₂) C
  | absurd {Γ : Ctx} {t : Term} {C : Ty} : HasType Γ t .bot → HasType Γ (absurd t) C

/-- **Weakening / renaming lemma.** Typing is preserved by renamings that respect
the types of variables. -/
theorem HasType.rename {Γ : Ctx} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ {Δ : Ctx} (ξ : Nat → Nat), (∀ n B, Γ[n]? = some B → Δ[ξ n]? = some B) →
      HasType Δ (STLC.rename ξ t) A := by
  have hup : ∀ {Γ Δ : Ctx} {A : Ty} (ξ : Nat → Nat),
      (∀ n B, Γ[n]? = some B → Δ[ξ n]? = some B) →
      ∀ n B, (A :: Γ)[n]? = some B → (A :: Δ)[upRen ξ n]? = some B := by
    intro Γ Δ A ξ hξ n B hn
    cases n with
    | zero => exact hn
    | succ n => simpa [upRen] using hξ n B (by simpa using hn)
  induction h with
  | var hn => intro Δ ξ hξ; exact .var (hξ _ _ hn)
  | lam _ ih => intro Δ ξ hξ; exact .lam (ih _ (hup ξ hξ))
  | app _ _ ih₁ ih₂ => intro Δ ξ hξ; exact .app (ih₁ ξ hξ) (ih₂ ξ hξ)
  | pair _ _ ih₁ ih₂ => intro Δ ξ hξ; exact .pair (ih₁ ξ hξ) (ih₂ ξ hξ)
  | fst _ ih => intro Δ ξ hξ; exact .fst (ih ξ hξ)
  | snd _ ih => intro Δ ξ hξ; exact .snd (ih ξ hξ)
  | inl _ ih => intro Δ ξ hξ; exact .inl (ih ξ hξ)
  | inr _ ih => intro Δ ξ hξ; exact .inr (ih ξ hξ)
  | case _ _ _ ih ih₁ ih₂ =>
    intro Δ ξ hξ; exact .case (ih ξ hξ) (ih₁ _ (hup ξ hξ)) (ih₂ _ (hup ξ hξ))
  | absurd _ ih => intro Δ ξ hξ; exact .absurd (ih ξ hξ)

/-- **Substitution lemma.** Substituting well-typed terms for variables preserves typing. -/
theorem HasType.subst {Γ : Ctx} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ {Δ : Ctx} (σ : Nat → Term), (∀ n B, Γ[n]? = some B → HasType Δ (σ n) B) →
      HasType Δ (STLC.subst σ t) A := by
  have hup : ∀ {Γ Δ : Ctx} {A : Ty} (σ : Nat → Term),
      (∀ n B, Γ[n]? = some B → HasType Δ (σ n) B) →
      ∀ n B, (A :: Γ)[n]? = some B → HasType (A :: Δ) (up σ n) B := by
    intro Γ Δ A σ hσ n B hn
    cases n with
    | zero => exact .var hn
    | succ n =>
      exact (hσ n B (by simpa using hn)).rename Nat.succ (fun m C hm => by simpa using hm)
  induction h with
  | var hn => intro Δ σ hσ; exact hσ _ _ hn
  | lam _ ih => intro Δ σ hσ; exact .lam (ih _ (hup σ hσ))
  | app _ _ ih₁ ih₂ => intro Δ σ hσ; exact .app (ih₁ σ hσ) (ih₂ σ hσ)
  | pair _ _ ih₁ ih₂ => intro Δ σ hσ; exact .pair (ih₁ σ hσ) (ih₂ σ hσ)
  | fst _ ih => intro Δ σ hσ; exact .fst (ih σ hσ)
  | snd _ ih => intro Δ σ hσ; exact .snd (ih σ hσ)
  | inl _ ih => intro Δ σ hσ; exact .inl (ih σ hσ)
  | inr _ ih => intro Δ σ hσ; exact .inr (ih σ hσ)
  | case _ _ _ ih ih₁ ih₂ =>
    intro Δ σ hσ; exact .case (ih σ hσ) (ih₁ _ (hup σ hσ)) (ih₂ _ (hup σ hσ))
  | absurd _ ih => intro Δ σ hσ; exact .absurd (ih σ hσ)

/-- Typing of a single substitution. -/
theorem HasType.inst {Γ : Ctx} {t u : Term} {A B : Ty} (ht : HasType (A :: Γ) t B)
    (hu : HasType Γ u A) : HasType Γ (STLC.inst t u) B :=
  ht.subst _ (fun n C hn => by
    cases n with
    | zero => simp at hn; subst hn; exact hu
    | succ n => exact .var (by simpa using hn))

/-! ## Reduction -/

/-- **One-step reduction**: the β-rule for functions, the projection rules for
pairs, the case rules for sums — anywhere inside a term. -/
inductive Step : Term → Term → Prop
  | beta (t u : Term) : Step (app (lam t) u) (inst t u)
  | fstPair (a b : Term) : Step (fst (pair a b)) a
  | sndPair (a b : Term) : Step (snd (pair a b)) b
  | caseInl (t u₁ u₂ : Term) : Step (case (inl t) u₁ u₂) (inst u₁ t)
  | caseInr (t u₁ u₂ : Term) : Step (case (inr t) u₁ u₂) (inst u₂ t)
  | appL {t t' u : Term} : Step t t' → Step (app t u) (app t' u)
  | appR {t u u' : Term} : Step u u' → Step (app t u) (app t u')
  | lam {t t' : Term} : Step t t' → Step (lam t) (lam t')
  | pairL {a a' b : Term} : Step a a' → Step (pair a b) (pair a' b)
  | pairR {a b b' : Term} : Step b b' → Step (pair a b) (pair a b')
  | fst {t t' : Term} : Step t t' → Step (fst t) (fst t')
  | snd {t t' : Term} : Step t t' → Step (snd t) (snd t')
  | inl {t t' : Term} : Step t t' → Step (inl t) (inl t')
  | inr {t t' : Term} : Step t t' → Step (inr t) (inr t')
  | case₀ {t t' u₁ u₂ : Term} : Step t t' → Step (case t u₁ u₂) (case t' u₁ u₂)
  | case₁ {t u₁ u₁' u₂ : Term} : Step u₁ u₁' → Step (case t u₁ u₂) (case t u₁' u₂)
  | case₂ {t u₁ u₂ u₂' : Term} : Step u₂ u₂' → Step (case t u₁ u₂) (case t u₁ u₂')
  | absurd {t t' : Term} : Step t t' → Step (absurd t) (absurd t')

/-- Many-step reduction. -/
abbrev Red : Term → Term → Prop := Star Step

/-- A term is **normal** when no reduction step applies. -/
def Normal (t : Term) : Prop := ∀ t', ¬ Step t t'

/-! ## Deciding whether a term can step

To normalize terms *constructively* — without appeal to excluded middle — we
need to be able to tell, effectively, whether a term is normal. The function
`step?` searches a term for a redex (leftmost-outermost first) and returns the
contracted term, or `none` if there is no redex. -/

/-- The body of an abstraction, if the term is one. -/
def lamBody : Term → Option Term
  | lam s => some s
  | _ => none

/-- The first component of a pair, if the term is one. -/
def pairFst : Term → Option Term
  | pair a _ => some a
  | _ => none

/-- The second component of a pair, if the term is one. -/
def pairSnd : Term → Option Term
  | pair _ b => some b
  | _ => none

/-- The contractum of a case analysis on an injection, if the scrutinee is one. -/
def caseRedex (u₁ u₂ : Term) : Term → Option Term
  | inl a => some (inst u₁ a)
  | inr b => some (inst u₂ b)
  | _ => none

/-- **One step of reduction, computed**: some one-step reduct of the term, if it has one. -/
def step? : Term → Option Term
  | var _ => none
  | app t u => firstSome ((lamBody t).map (fun s => inst s u))
      (firstSome ((step? t).map (fun t' => app t' u)) ((step? u).map (app t)))
  | lam t => (step? t).map lam
  | pair a b => firstSome ((step? a).map (fun a' => pair a' b)) ((step? b).map (pair a))
  | fst t => firstSome (pairFst t) ((step? t).map fst)
  | snd t => firstSome (pairSnd t) ((step? t).map snd)
  | inl t => (step? t).map inl
  | inr t => (step? t).map inr
  | case t u₁ u₂ => firstSome (caseRedex u₁ u₂ t)
      (firstSome ((step? t).map (fun t' => case t' u₁ u₂))
        (firstSome ((step? u₁).map (fun u => case t u u₂)) ((step? u₂).map (case t u₁))))
  | .absurd t => (step? t).map .absurd

/-- `step?` only returns genuine reducts. -/
theorem step?_sound : ∀ (t t' : Term), step? t = some t' → Step t t' := by
  intro t
  induction t with
  | var n => intro t' h; simp [step?] at h
  | app t u iht ihu =>
    intro x h
    simp only [step?] at h
    rcases firstSome_eq_some h with h | h
    · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
      cases t <;> simp [lamBody] at hs
      subst hs
      exact Step.beta _ _
    rcases firstSome_eq_some h with h | h
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.appL (iht _ ht)
    · obtain ⟨u', hu, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.appR (ihu _ hu)
  | lam t ih =>
    intro x h
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.lam (ih _ ht)
  | pair a b iha ihb =>
    intro x h
    simp only [step?] at h
    rcases firstSome_eq_some h with h | h
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.pairL (iha _ ha)
    · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.pairR (ihb _ hb)
  | fst t ih =>
    intro x h
    simp only [step?] at h
    rcases firstSome_eq_some h with h | h
    · cases t <;> simp [pairFst] at h
      subst h; exact Step.fstPair _ _
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.fst (ih _ ht)
  | snd t ih =>
    intro x h
    simp only [step?] at h
    rcases firstSome_eq_some h with h | h
    · cases t <;> simp [pairSnd] at h
      subst h; exact Step.sndPair _ _
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.snd (ih _ ht)
  | inl t ih =>
    intro x h
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.inl (ih _ ht)
  | inr t ih =>
    intro x h
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.inr (ih _ ht)
  | case t u₁ u₂ iht ih₁ ih₂ =>
    intro x h
    simp only [step?] at h
    rcases firstSome_eq_some h with h | h
    · cases t <;> simp [caseRedex] at h
      · subst h; exact Step.caseInl _ _ _
      · subst h; exact Step.caseInr _ _ _
    rcases firstSome_eq_some h with h | h
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.case₀ (iht _ ht)
    rcases firstSome_eq_some h with h | h
    · obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.case₁ (ih₁ _ hu)
    · obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.case₂ (ih₂ _ hu)
  | absurd t ih =>
    intro x h
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.absurd (ih _ ht)

/-- `step?` finds a reduct whenever there is one. -/
theorem step?_complete {t t' : Term} (h : Step t t') : (step? t).isSome := by
  induction h with
  | beta => simp [step?, lamBody, firstSome]
  | fstPair => simp [step?, pairFst, firstSome]
  | sndPair => simp [step?, pairSnd, firstSome]
  | caseInl => simp [step?, caseRedex, firstSome]
  | caseInr => simp [step?, caseRedex, firstSome]
  | appL _ ih => exact firstSome_isSome_right (firstSome_isSome_left (by simpa using ih))
  | appR _ ih => exact firstSome_isSome_right (firstSome_isSome_right (by simpa using ih))
  | lam _ ih => simpa [step?] using ih
  | pairL _ ih => exact firstSome_isSome_left (by simpa using ih)
  | pairR _ ih => exact firstSome_isSome_right (by simpa using ih)
  | fst _ ih => exact firstSome_isSome_right (by simpa using ih)
  | snd _ ih => exact firstSome_isSome_right (by simpa using ih)
  | inl _ ih => simpa [step?] using ih
  | inr _ ih => simpa [step?] using ih
  | case₀ _ ih => exact firstSome_isSome_right (firstSome_isSome_left (by simpa using ih))
  | case₁ _ ih =>
    exact firstSome_isSome_right (firstSome_isSome_right (firstSome_isSome_left (by simpa using ih)))
  | case₂ _ ih =>
    exact firstSome_isSome_right (firstSome_isSome_right (firstSome_isSome_right (by simpa using ih)))
  | absurd _ ih => simpa [step?] using ih

/-- **Normality is decidable**: `step?` returns `none` exactly on normal terms. -/
theorem normal_iff_step?_none (t : Term) : Normal t ↔ step? t = none := by
  constructor
  · intro hn
    cases hs : step? t with
    | none => rfl
    | some t' => exact absurd (step?_sound _ _ hs) (hn t')
  · intro hs t' h
    have := step?_complete h
    rw [hs] at this
    exact absurd this (by simp)

/-- Reduction is stable under renaming. -/
theorem Step.rename {t t' : Term} (h : Step t t') : ∀ ξ, Step (STLC.rename ξ t) (STLC.rename ξ t') := by
  have hinst : ∀ ξ t u, STLC.rename ξ (STLC.inst t u) =
      STLC.inst (STLC.rename (upRen ξ) t) (STLC.rename ξ u) := by
    intro ξ t u
    simp only [STLC.inst, rename_subst, subst_rename]
    congr 1
    funext n; cases n <;> rfl
  induction h <;> intro ξ <;> simp only [STLC.rename, hinst] <;> constructor <;> apply_assumption

/-- **Reduction is stable under substitution.** -/
theorem Step.subst {t t' : Term} (h : Step t t') : ∀ σ, Step (STLC.subst σ t) (STLC.subst σ t') := by
  induction h <;> intro σ <;> simp only [STLC.subst, subst_inst] <;> constructor <;> apply_assumption

/-! ## Subject reduction and progress -/

/-- **Subject reduction (preservation).** Reduction preserves types. -/
theorem subject_reduction {Γ : Ctx} {t t' : Term} {A : Ty} (h : Step t t') (ht : HasType Γ t A) :
    HasType Γ t' A := by
  induction h generalizing Γ A with
  | beta t u =>
    cases ht with
    | app h₁ h₂ => cases h₁ with
      | lam h₁ => exact h₁.inst h₂
  | fstPair a b => cases ht with
    | fst h => cases h with
      | pair h₁ _ => exact h₁
  | sndPair a b => cases ht with
    | snd h => cases h with
      | pair _ h₂ => exact h₂
  | caseInl t u₁ u₂ => cases ht with
    | case h h₁ _ => cases h with
      | inl h => exact h₁.inst h
  | caseInr t u₁ u₂ => cases ht with
    | case h _ h₂ => cases h with
      | inr h => exact h₂.inst h
  | appL _ ih => cases ht with
    | app h₁ h₂ => exact .app (ih h₁) h₂
  | appR _ ih => cases ht with
    | app h₁ h₂ => exact .app h₁ (ih h₂)
  | lam _ ih => cases ht with
    | lam h => exact .lam (ih h)
  | pairL _ ih => cases ht with
    | pair h₁ h₂ => exact .pair (ih h₁) h₂
  | pairR _ ih => cases ht with
    | pair h₁ h₂ => exact .pair h₁ (ih h₂)
  | fst _ ih => cases ht with
    | fst h => exact .fst (ih h)
  | snd _ ih => cases ht with
    | snd h => exact .snd (ih h)
  | inl _ ih => cases ht with
    | inl h => exact .inl (ih h)
  | inr _ ih => cases ht with
    | inr h => exact .inr (ih h)
  | case₀ _ ih => cases ht with
    | case h h₁ h₂ => exact .case (ih h) h₁ h₂
  | case₁ _ ih => cases ht with
    | case h h₁ h₂ => exact .case h (ih h₁) h₂
  | case₂ _ ih => cases ht with
    | case h h₁ h₂ => exact .case h h₁ (ih h₂)
  | absurd _ ih => cases ht with
    | absurd h => exact .absurd (ih h)

/-- Subject reduction for many steps. -/
theorem subject_reduction_red {Γ : Ctx} {t t' : Term} {A : Ty} (h : Red t t')
    (ht : HasType Γ t A) : HasType Γ t' A := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact subject_reduction hs ih

/-- **Values**: the introduction forms. -/
def IsValue : Term → Prop
  | lam _ => True
  | pair _ _ => True
  | inl _ => True
  | inr _ => True
  | _ => False

/-- **Progress.** A closed well-typed term is a value or can take a step. -/
theorem progress {t : Term} {A : Ty} (ht : HasType [] t A) : IsValue t ∨ ∃ t', Step t t' := by
  generalize hΓ : ([] : Ctx) = Γ at ht
  induction ht with
  | var hn => subst hΓ; simp at hn
  | lam _ _ => exact Or.inl trivial
  | pair _ _ _ _ => exact Or.inl trivial
  | inl _ _ => exact Or.inl trivial
  | inr _ _ => exact Or.inl trivial
  | @app Γ t u A B h₁ _ ih₁ _ =>
    rcases ih₁ hΓ with hv | ⟨t', ht'⟩
    · cases h₁ <;> simp [IsValue] at hv
      exact Or.inr ⟨_, Step.beta _ _⟩
    · exact Or.inr ⟨_, Step.appL ht'⟩
  | fst h ih =>
    rcases ih hΓ with hv | ⟨t', ht'⟩
    · cases h <;> simp [IsValue] at hv
      exact Or.inr ⟨_, Step.fstPair _ _⟩
    · exact Or.inr ⟨_, Step.fst ht'⟩
  | snd h ih =>
    rcases ih hΓ with hv | ⟨t', ht'⟩
    · cases h <;> simp [IsValue] at hv
      exact Or.inr ⟨_, Step.sndPair _ _⟩
    · exact Or.inr ⟨_, Step.snd ht'⟩
  | case h _ _ ih _ _ =>
    rcases ih hΓ with hv | ⟨t', ht'⟩
    · cases h <;> simp [IsValue] at hv
      · exact Or.inr ⟨_, Step.caseInl _ _ _⟩
      · exact Or.inr ⟨_, Step.caseInr _ _ _⟩
    · exact Or.inr ⟨_, Step.case₀ ht'⟩
  | absurd h ih =>
    rcases ih hΓ with hv | ⟨t', ht'⟩
    · cases h <;> simp [IsValue] at hv
    · exact Or.inr ⟨_, Step.absurd ht'⟩

/-- **Type safety** ("well-typed programs cannot go wrong"): a closed well-typed
term that has finished computing is a value. -/
theorem normal_closed_isValue {t : Term} {A : Ty} (ht : HasType [] t A) (hn : Normal t) :
    IsValue t :=
  (progress ht).resolve_right fun ⟨t', h⟩ => hn t' h

end STLC

end Foundations.Types
