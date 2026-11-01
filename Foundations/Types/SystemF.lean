import Foundations.Types.Lambda

/-!
# System F: polymorphism, and why `Type : Type` fails

In the simply typed λ-calculus the identity function must be written once for
every type: `λx. x : A → A`, `λx. x : B → B`, … **System F**, discovered
independently by Jean-Yves Girard (1972, as a proof-theoretic tool for
second-order arithmetic) and John Reynolds (1974, as a theory of polymorphic
programs), lets terms abstract over *types*: the polymorphic identity
`Λα. λx. x` has type `∀α. α → α`, and can be instantiated at any type, including
`∀α. α → α` itself. This *impredicativity* — a quantifier over all types that
itself denotes a type — makes the system immensely expressive: natural numbers
(`∀α. (α → α) → α → α`), pairs, sums, lists and every function provably total in
second-order arithmetic are definable.

Under Curry–Howard, System F is second-order intuitionistic propositional logic,
and Girard proved its normalization by extending Tait's method with
*reducibility candidates*: since `∀α. A` quantifies over all types, its
reducibility must quantify over all *possible* reducibility predicates. (We do
not formalize that proof here; it needs the impredicative quantification that
Lean's `Prop` happens to offer.)

Here we set up System F à la Church-for-types (explicit type abstraction `Λ.`
and type application `t [B]`, with de Bruijn indices for both term and type
variables) and prove **subject reduction** and **progress**. Two layers of
substitution interact: substituting a type for a type variable inside a typing
derivation (`HasType.tySubst`) requires that type substitution commute with
the shifting of contexts under a `Λ`.

**Why not `Type : Type`?** One might go further and let types be terms of a type
of all types, `Type : Type` (Martin-Löf's first, 1971, version of his type
theory did exactly this). Girard showed in 1972 that this is inconsistent —
every type, including the empty type, becomes inhabited — by encoding the
Burali-Forti paradox of the ordinal of all ordinals; Hurkens (1995) simplified
the paradox to a short term. The proof is a type-theoretic shadow of Russell's
and Burali-Forti's paradoxes (cf. `Paradoxes.lean`, `Ordinals.lean` in Part I),
and it is the reason why Lean, like Martin-Löf's later theories and Coq, has an
infinite hierarchy of *universes* `Type 0 : Type 1 : Type 2 : ⋯` instead of a
single type of all types, with impredicativity confined to `Prop`. (We state the
paradox here only informally; a formal derivation is beyond this part.)
-/

namespace Foundations.Types

namespace SystemF

/-! ## Types -/

/-- **Types of System F**: type variables (de Bruijn indices), functions, and
universal quantification `∀. A` (binding type variable `0` in `A`). -/
inductive Ty where
  /-- A type variable. -/
  | tvar (n : Nat)
  /-- Function type. -/
  | arr (A B : Ty)
  /-- Universal type `∀α. A`. -/
  | all (A : Ty)
  deriving DecidableEq, Repr

namespace Ty

/-- Lifting a renaming under a binder. -/
def upRen (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

/-- Renaming type variables. -/
def rename (ξ : Nat → Nat) : Ty → Ty
  | tvar n => tvar (ξ n)
  | arr A B => arr (rename ξ A) (rename ξ B)
  | all A => all (rename (upRen ξ) A)

/-- Lifting a type substitution under a binder. -/
def up (σ : Nat → Ty) : Nat → Ty
  | 0 => tvar 0
  | n + 1 => rename Nat.succ (σ n)

/-- Simultaneous substitution of types for type variables. -/
def subst (σ : Nat → Ty) : Ty → Ty
  | tvar n => σ n
  | arr A B => arr (subst σ A) (subst σ B)
  | all A => all (subst (up σ) A)

/-- Extending a type substitution: `0 ↦ B`, `n + 1 ↦ σ n`. -/
def cons (B : Ty) (σ : Nat → Ty) : Nat → Ty
  | 0 => B
  | n + 1 => σ n

/-- Instantiating the bound variable: `A[B]`. -/
def inst (A B : Ty) : Ty := subst (cons B tvar) A

/-- Shifting all free type variables up by one (going under a `Λ`). -/
abbrev shift : Ty → Ty := rename Nat.succ

/-- Lifting commutes with composition of renamings. -/
theorem upRen_comp (ξ ζ : Nat → Nat) : upRen ξ ∘ upRen ζ = upRen (ξ ∘ ζ) := by
  funext n; cases n <;> rfl

/-- Renamings compose. -/
theorem rename_rename (A : Ty) : ∀ ξ ζ, rename ξ (rename ζ A) = rename (ξ ∘ ζ) A := by
  induction A <;> intros <;> simp only [rename, upRen_comp, Function.comp_apply, *]

/-- Lifting a substitution after a lifted renaming. -/
theorem up_upRen (σ : Nat → Ty) (ξ : Nat → Nat) : up σ ∘ upRen ξ = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

/-- Substitution after renaming. -/
theorem subst_rename (A : Ty) : ∀ σ ξ, subst σ (rename ξ A) = subst (σ ∘ ξ) A := by
  induction A <;> intros <;> simp only [rename, subst, up_upRen, *] <;> rfl

/-- A lifted renaming after a lifted substitution. -/
theorem rename_up (ξ : Nat → Nat) (σ : Nat → Ty) :
    rename (upRen ξ) ∘ up σ = up (rename ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Function.comp, up, rename_rename]; rfl

/-- Renaming after substitution. -/
theorem rename_subst (A : Ty) : ∀ ξ σ, rename ξ (subst σ A) = subst (rename ξ ∘ σ) A := by
  induction A <;> intros <;> simp only [rename, subst, rename_up, *] <;> rfl

/-- Lifting commutes with composition of substitutions. -/
theorem up_comp (τ σ : Nat → Ty) : subst (up τ) ∘ up σ = up (subst τ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Function.comp, up, subst_rename, rename_subst]; rfl

/-- Substitutions compose. -/
theorem subst_subst (A : Ty) : ∀ τ σ, subst τ (subst σ A) = subst (subst τ ∘ σ) A := by
  induction A <;> intros <;> simp only [subst, up_comp, *] <;> rfl

/-- Lifting the identity substitution gives the identity. -/
theorem up_tvar : up tvar = tvar := by
  funext n; cases n <;> rfl

/-- The identity substitution does nothing. -/
theorem subst_tvar (A : Ty) : subst tvar A = A := by
  induction A <;> simp only [subst, up_tvar, *]

/-- Renaming commutes with instantiation. -/
theorem rename_inst (ξ : Nat → Nat) (A B : Ty) :
    rename ξ (inst A B) = inst (rename (upRen ξ) A) (rename ξ B) := by
  simp only [inst, rename_subst, subst_rename]
  congr 1
  funext n; cases n <;> rfl

/-- Substitution commutes with instantiation. -/
theorem subst_inst (σ : Nat → Ty) (A B : Ty) :
    subst σ (inst A B) = inst (subst (up σ) A) (subst σ B) := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, cons, subst_rename]
    exact (subst_tvar _).symm

/-- Shifting commutes with lifted renamings. -/
theorem rename_shift (ξ : Nat → Nat) : rename (upRen ξ) ∘ shift = shift ∘ rename ξ := by
  funext A
  simp only [Function.comp, shift, rename_rename]
  rfl

/-- Shifting commutes with lifted substitutions. -/
theorem subst_shift (σ : Nat → Ty) : subst (up σ) ∘ shift = shift ∘ subst σ := by
  funext A
  simp only [Function.comp, shift, subst_rename, rename_subst]
  rfl

/-- Instantiating a shifted type gives it back. -/
theorem inst_shift (B : Ty) : (fun A => subst (cons B tvar) (shift A)) = id := by
  funext A
  simp only [shift, subst_rename]
  exact subst_tvar A

end Ty

/-! ## Terms -/

/-- **Terms of System F**: variables, application, abstraction, type abstraction
`Λ. t`, and type application `t [B]`. -/
inductive Term where
  /-- A term variable. -/
  | var (n : Nat)
  /-- Application. -/
  | app (t u : Term)
  /-- Abstraction (binds term variable `0`). -/
  | lam (t : Term)
  /-- Type abstraction `Λ. t` (binds type variable `0`). -/
  | tlam (t : Term)
  /-- Type application `t [B]`. -/
  | tapp (t : Term) (B : Ty)
  deriving DecidableEq, Repr

namespace Term

/-- Renaming the type variables occurring in a term. -/
def tyRename (ξ : Nat → Nat) : Term → Term
  | var n => var n
  | app t u => app (tyRename ξ t) (tyRename ξ u)
  | lam t => lam (tyRename ξ t)
  | tlam t => tlam (tyRename (Ty.upRen ξ) t)
  | tapp t B => tapp (tyRename ξ t) (B.rename ξ)

/-- Substituting types for the type variables occurring in a term. -/
def tySubst (τ : Nat → Ty) : Term → Term
  | var n => var n
  | app t u => app (tySubst τ t) (tySubst τ u)
  | lam t => lam (tySubst τ t)
  | tlam t => tlam (tySubst (Ty.up τ) t)
  | tapp t B => tapp (tySubst τ t) (B.subst τ)

/-- Renaming term variables. -/
def rename (ξ : Nat → Nat) : Term → Term
  | var n => var (ξ n)
  | app t u => app (rename ξ t) (rename ξ u)
  | lam t => lam (rename (Ty.upRen ξ) t)
  | tlam t => tlam (rename ξ t)
  | tapp t B => tapp (rename ξ t) B

/-- Lifting a term substitution under a term binder. -/
def up (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Simultaneous substitution of terms for term variables (under a `Λ`, the
substituted terms have their type variables shifted). -/
def subst (σ : Nat → Term) : Term → Term
  | var n => σ n
  | app t u => app (subst σ t) (subst σ u)
  | lam t => lam (subst (up σ) t)
  | tlam t => tlam (subst (fun n => tyRename Nat.succ (σ n)) t)
  | tapp t B => tapp (subst σ t) B

/-- Extending a term substitution. -/
def cons (u : Term) (σ : Nat → Term) : Nat → Term
  | 0 => u
  | n + 1 => σ n

/-- Single substitution `t[u]` of a term for term variable `0`. -/
def inst (t u : Term) : Term := subst (cons u var) t

/-- Single substitution `t[B]` of a type for type variable `0`. -/
def tyInst (t : Term) (B : Ty) : Term := tySubst (Ty.cons B Ty.tvar) t

end Term

open Term

/-! ## Typing -/

/-- The **typing judgement** of System F. Under a type abstraction the context is
shifted, since a new type variable `0` is introduced. -/
inductive HasType : List Ty → Term → Ty → Prop
  | var {Γ : List Ty} {n : Nat} {A : Ty} : Γ[n]? = some A → HasType Γ (var n) A
  | lam {Γ : List Ty} {t : Term} {A B : Ty} : HasType (A :: Γ) t B → HasType Γ (lam t) (.arr A B)
  | app {Γ : List Ty} {t u : Term} {A B : Ty} :
      HasType Γ t (.arr A B) → HasType Γ u A → HasType Γ (app t u) B
  | tlam {Γ : List Ty} {t : Term} {A : Ty} :
      HasType (Γ.map Ty.shift) t A → HasType Γ (tlam t) (.all A)
  | tapp {Γ : List Ty} {t : Term} {A B : Ty} :
      HasType Γ t (.all A) → HasType Γ (tapp t B) (A.inst B)

/-- The **polymorphic identity** `Λα. λx. x : ∀α. α → α`. -/
theorem id_typed : HasType [] (tlam (lam (var 0))) (.all (.arr (.tvar 0) (.tvar 0))) :=
  .tlam (.lam (.var rfl))

/-- Typing is preserved by renaming term variables. -/
theorem HasType.rename {Γ : List Ty} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ {Δ : List Ty} (ξ : Nat → Nat), (∀ n B, Γ[n]? = some B → Δ[ξ n]? = some B) →
      HasType Δ (Term.rename ξ t) A := by
  induction h with
  | var hn => intro Δ ξ hξ; exact .var (hξ _ _ hn)
  | lam _ ih =>
    intro Δ ξ hξ
    refine .lam (ih _ fun n B hn => ?_)
    cases n with
    | zero => exact hn
    | succ n => simpa [Ty.upRen] using hξ n B (by simpa using hn)
  | app _ _ ih₁ ih₂ => intro Δ ξ hξ; exact .app (ih₁ ξ hξ) (ih₂ ξ hξ)
  | tlam _ ih =>
    intro Δ ξ hξ
    refine .tlam (ih ξ fun n B hn => ?_)
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn ⊢
    obtain ⟨B₀, hB₀, rfl⟩ := hn
    exact ⟨B₀, hξ n B₀ hB₀, rfl⟩
  | tapp _ ih => intro Δ ξ hξ; exact .tapp (ih ξ hξ)

/-- Typing is preserved by renaming type variables (in the context, term and type). -/
theorem HasType.tyRename {Γ : List Ty} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ ξ, HasType (Γ.map (Ty.rename ξ)) (Term.tyRename ξ t) (A.rename ξ) := by
  induction h with
  | var hn => intro ξ; exact .var (by simp [hn])
  | lam _ ih => intro ξ; exact .lam (ih ξ)
  | app _ _ ih₁ ih₂ => intro ξ; exact .app (ih₁ ξ) (ih₂ ξ)
  | @tlam Γ t A _ ih =>
    intro ξ
    have := ih (Ty.upRen ξ)
    rw [List.map_map, Ty.rename_shift, ← List.map_map] at this
    exact .tlam this
  | tapp _ ih =>
    intro ξ
    rw [Ty.rename_inst]
    exact .tapp (ih ξ)

/-- **Type substitution lemma**: typing is preserved by substituting types for
type variables. -/
theorem HasType.tySubst {Γ : List Ty} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ τ, HasType (Γ.map (Ty.subst τ)) (Term.tySubst τ t) (A.subst τ) := by
  induction h with
  | var hn => intro τ; exact .var (by simp [hn])
  | lam _ ih => intro τ; exact .lam (ih τ)
  | app _ _ ih₁ ih₂ => intro τ; exact .app (ih₁ τ) (ih₂ τ)
  | @tlam Γ t A _ ih =>
    intro τ
    have := ih (Ty.up τ)
    rw [List.map_map, Ty.subst_shift, ← List.map_map] at this
    exact .tlam this
  | tapp _ ih =>
    intro τ
    rw [Ty.subst_inst]
    exact .tapp (ih τ)

/-- **Term substitution lemma.** -/
theorem HasType.subst {Γ : List Ty} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ {Δ : List Ty} (σ : Nat → Term), (∀ n B, Γ[n]? = some B → HasType Δ (σ n) B) →
      HasType Δ (Term.subst σ t) A := by
  induction h with
  | var hn => intro Δ σ hσ; exact hσ _ _ hn
  | lam _ ih =>
    intro Δ σ hσ
    refine .lam (ih _ fun n B hn => ?_)
    cases n with
    | zero => exact .var hn
    | succ n =>
      exact (hσ n B (by simpa using hn)).rename Nat.succ (fun m C hm => by simpa using hm)
  | app _ _ ih₁ ih₂ => intro Δ σ hσ; exact .app (ih₁ σ hσ) (ih₂ σ hσ)
  | tlam _ ih =>
    intro Δ σ hσ
    refine .tlam (ih _ fun n B hn => ?_)
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
    obtain ⟨B₀, hB₀, rfl⟩ := hn
    exact (hσ n B₀ hB₀).tyRename Nat.succ
  | tapp _ ih => intro Δ σ hσ; exact .tapp (ih σ hσ)

/-! ## Reduction, subject reduction and progress -/

/-- **One-step reduction** of System F: term β, type β (`(Λ. t) [B] ⟶ t[B]`), and
congruences. -/
inductive Step : Term → Term → Prop
  | beta (t u : Term) : Step (app (lam t) u) (inst t u)
  | tbeta (t : Term) (B : Ty) : Step (tapp (tlam t) B) (tyInst t B)
  | appL {t t' u : Term} : Step t t' → Step (app t u) (app t' u)
  | appR {t u u' : Term} : Step u u' → Step (app t u) (app t u')
  | lam {t t' : Term} : Step t t' → Step (lam t) (lam t')
  | tlam {t t' : Term} : Step t t' → Step (tlam t) (tlam t')
  | tapp {t t' : Term} {B : Ty} : Step t t' → Step (tapp t B) (tapp t' B)

/-- **Subject reduction for System F.** -/
theorem subject_reduction {Γ : List Ty} {t t' : Term} {A : Ty} (h : Step t t')
    (ht : HasType Γ t A) : HasType Γ t' A := by
  induction h generalizing Γ A with
  | beta t u =>
    cases ht with
    | app h₁ h₂ => cases h₁ with
      | lam h₁ =>
        exact h₁.subst _ fun n C hn => by
          cases n with
          | zero => simp at hn; subst hn; exact h₂
          | succ n => exact .var (by simpa using hn)
  | tbeta t B =>
    cases ht with
    | tapp h => cases h with
      | tlam h =>
        have := h.tySubst (Ty.cons B Ty.tvar)
        rw [List.map_map] at this
        have hid : Ty.subst (Ty.cons B Ty.tvar) ∘ Ty.shift = id := Ty.inst_shift B
        rw [hid, List.map_id] at this
        exact this
  | appL _ ih => cases ht with
    | app h₁ h₂ => exact .app (ih h₁) h₂
  | appR _ ih => cases ht with
    | app h₁ h₂ => exact .app h₁ (ih h₂)
  | lam _ ih => cases ht with
    | lam h => exact .lam (ih h)
  | tlam _ ih => cases ht with
    | tlam h => exact .tlam (ih h)
  | tapp _ ih => cases ht with
    | tapp h => exact .tapp (ih h)

/-- Values of System F: abstractions and type abstractions. -/
def IsValue : Term → Prop
  | lam _ => True
  | tlam _ => True
  | _ => False

/-- **Progress for System F.** A closed well-typed term is a value or can step. -/
theorem progress {t : Term} {A : Ty} (ht : HasType [] t A) : IsValue t ∨ ∃ t', Step t t' := by
  generalize hΓ : ([] : List Ty) = Γ at ht
  induction ht with
  | var hn => subst hΓ; simp at hn
  | lam _ _ => exact Or.inl trivial
  | tlam _ _ => exact Or.inl trivial
  | @app Γ t u A B h₁ _ ih₁ _ =>
    rcases ih₁ hΓ with hv | ⟨t', ht'⟩
    ·       cases t with
      | lam s => exact Or.inr ⟨_, Step.beta _ _⟩
      | tlam s => cases h₁
      | _ => simp [IsValue] at hv
    · exact Or.inr ⟨_, Step.appL ht'⟩
  | @tapp Γ t A B h ih =>
    rcases ih hΓ with hv | ⟨t', ht'⟩
    ·       cases t with
      | tlam s => exact Or.inr ⟨_, Step.tbeta _ _⟩
      | lam s => cases h
      | _ => simp [IsValue] at hv
    · exact Or.inr ⟨_, Step.tapp ht'⟩

end SystemF

end Foundations.Types
