import Foundations.Types.SystemF

/-!
# System F: the algebra of two substitutions

System F has two kinds of variables — for terms and for types — and therefore
two substitution operations, which interact: substituting a term under a type
abstraction `Λ` must shift the type variables of the substituted term, and
substituting a type into a term must commute with substituting terms. This file
proves the necessary laws (the "σ-calculus" of de Bruijn substitutions, twice
over), shows that reduction is stable under both substitutions, and gives a
*decision procedure* `step?` for whether a term can reduce. These are the tools
for Girard's normalization proof in `SystemFNormalization.lean`.

None of this has philosophical content of its own; it is the bookkeeping that
pen-and-paper proofs dismiss with "by the usual properties of substitution" —
and which a proof assistant insists on seeing.
-/

namespace Foundations.Types

namespace SystemF

namespace Term

/-! ## Type operations on terms -/

/-- Type renamings compose on terms. -/
theorem tyRename_tyRename (t : Term) :
    ∀ ξ ζ, tyRename ξ (tyRename ζ t) = tyRename (ξ ∘ ζ) t := by
  induction t <;> intros <;> simp only [tyRename, Ty.upRen_comp, Ty.rename_rename, *]

/-- Type substitution after type renaming. -/
theorem tySubst_tyRename (t : Term) :
    ∀ τ ξ, tySubst τ (tyRename ξ t) = tySubst (τ ∘ ξ) t := by
  induction t <;> intros <;> simp only [tyRename, tySubst, Ty.up_upRen, Ty.subst_rename, *]

/-- Type renaming after type substitution. -/
theorem tyRename_tySubst (t : Term) :
    ∀ ξ τ, tyRename ξ (tySubst τ t) = tySubst (Ty.rename ξ ∘ τ) t := by
  induction t <;> intros <;> simp only [tyRename, tySubst, Ty.rename_up, Ty.rename_subst, *]

/-- Type substitutions compose on terms. -/
theorem tySubst_tySubst (t : Term) :
    ∀ τ τ', tySubst τ (tySubst τ' t) = tySubst (Ty.subst τ ∘ τ') t := by
  induction t <;> intros <;> simp only [tySubst, Ty.up_comp, Ty.subst_subst, *]

/-- The identity type substitution does nothing to a term. -/
theorem tySubst_tvar (t : Term) : tySubst Ty.tvar t = t := by
  induction t <;> simp only [tySubst, Ty.up_tvar, Ty.subst_tvar, *]

/-- Instantiating a type-shifted term gives it back. -/
theorem tySubst_cons_tyRename_succ (B : Ty) (s : Term) :
    tySubst (Ty.cons B Ty.tvar) (tyRename Nat.succ s) = s := by
  rw [tySubst_tyRename]
  exact tySubst_tvar s

/-- Shifting type variables commutes with a lifted type renaming. -/
theorem tyRename_upRen_succ (ξ : Nat → Nat) (s : Term) :
    tyRename (Ty.upRen ξ) (tyRename Nat.succ s) = tyRename Nat.succ (tyRename ξ s) := by
  rw [tyRename_tyRename, tyRename_tyRename]; rfl

/-- Shifting type variables commutes with a lifted type substitution. -/
theorem tySubst_up_succ (τ : Nat → Ty) (s : Term) :
    tySubst (Ty.up τ) (tyRename Nat.succ s) = tyRename Nat.succ (tySubst τ s) := by
  rw [tySubst_tyRename, tyRename_tySubst]; rfl

/-! ## Term renaming -/

/-- Term renaming commutes with type renaming. -/
theorem rename_tyRename (t : Term) :
    ∀ ξ ζ, rename ξ (tyRename ζ t) = tyRename ζ (rename ξ t) := by
  induction t <;> intros <;> simp only [rename, tyRename, *]

/-- Term renaming commutes with type substitution. -/
theorem rename_tySubst (t : Term) :
    ∀ ξ τ, rename ξ (tySubst τ t) = tySubst τ (rename ξ t) := by
  induction t <;> intros <;> simp only [rename, tySubst, *]

/-- Term renamings compose. -/
theorem rename_rename (t : Term) : ∀ ξ ζ, rename ξ (rename ζ t) = rename (ξ ∘ ζ) t := by
  induction t <;> intros <;> simp only [rename, Ty.upRen_comp, Function.comp_apply, *]

/-- Lifting a substitution after a lifted renaming. -/
theorem up_upRen (σ : Nat → Term) (ξ : Nat → Nat) : up σ ∘ Ty.upRen ξ = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

/-- Term substitution after term renaming. -/
theorem subst_rename (t : Term) : ∀ σ ξ, subst σ (rename ξ t) = subst (σ ∘ ξ) t := by
  induction t <;> intros <;> simp only [rename, subst, up_upRen, *] <;> rfl

/-- A lifted renaming after a lifted substitution. -/
theorem rename_up (ξ : Nat → Nat) (σ : Nat → Term) :
    rename (Ty.upRen ξ) ∘ up σ = up (rename ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Function.comp, up, rename_rename]; rfl

/-- Term renaming after term substitution. -/
theorem rename_subst (t : Term) : ∀ ξ σ, rename ξ (subst σ t) = subst (rename ξ ∘ σ) t := by
  induction t with
  | var n => intros; rfl
  | app t u iht ihu => intros; simp only [subst, rename, iht, ihu]
  | lam t ih => intro ξ σ; simp only [subst, rename, ih, rename_up]
  | tlam t ih =>
    intro ξ σ
    simp only [subst, rename, ih]
    congr 2
    funext n
    exact rename_tyRename _ _ _
  | tapp t B ih => intros; simp only [subst, rename, ih]

/-- Type renaming of a term substitution. -/
theorem tyRename_subst (t : Term) :
    ∀ ξ σ, tyRename ξ (subst σ t) = subst (tyRename ξ ∘ σ) (tyRename ξ t) := by
  induction t with
  | var n => intros; rfl
  | app t u iht ihu => intros; simp only [subst, tyRename, iht, ihu]
  | lam t ih =>
    intro ξ σ
    simp only [subst, tyRename, ih]
    congr 2
    funext n
    cases n with
    | zero => rfl
    | succ n => simp only [Function.comp, up, rename_tyRename]
  | tlam t ih =>
    intro ξ σ
    simp only [subst, tyRename, ih]
    congr 2
    funext n
    exact tyRename_upRen_succ _ _
  | tapp t B ih => intros; simp only [subst, tyRename, ih]

/-- **Type substitution of a term substitution**:
`(t σ) τ = (t τ) (σ τ)`. -/
theorem tySubst_subst (t : Term) :
    ∀ τ σ, tySubst τ (subst σ t) = subst (tySubst τ ∘ σ) (tySubst τ t) := by
  induction t with
  | var n => intros; rfl
  | app t u iht ihu => intros; simp only [subst, tySubst, iht, ihu]
  | lam t ih =>
    intro τ σ
    simp only [subst, tySubst, ih]
    congr 2
    funext n
    cases n with
    | zero => rfl
    | succ n => simp only [Function.comp, up, rename_tySubst]
  | tlam t ih =>
    intro τ σ
    simp only [subst, tySubst, ih]
    congr 2
    funext n
    exact tySubst_up_succ _ _
  | tapp t B ih => intros; simp only [subst, tySubst, ih]

/-- Lifting commutes with composition of substitutions. -/
theorem up_comp (τ σ : Nat → Term) : subst (up τ) ∘ up σ = up (subst τ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Function.comp, up, subst_rename, rename_subst]; rfl

/-- **Term substitutions compose.** -/
theorem subst_subst (t : Term) : ∀ τ σ, subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  induction t with
  | var n => intros; rfl
  | app t u iht ihu => intros; simp only [subst, iht, ihu]
  | lam t ih => intro τ σ; simp only [subst, ih, up_comp]
  | tlam t ih =>
    intro τ σ
    simp only [subst, ih]
    congr 2
    funext n
    exact (tyRename_subst _ _ _).symm
  | tapp t B ih => intros; simp only [subst, ih]

/-- Lifting the identity substitution gives the identity. -/
theorem up_var : up var = var := by
  funext n; cases n <;> rfl

/-- The identity substitution does nothing. -/
theorem subst_var (t : Term) : subst var t = t := by
  induction t with
  | var n => rfl
  | app t u iht ihu => simp only [subst, iht, ihu]
  | lam t ih => simp only [subst, up_var, ih]
  | tlam t ih =>
    have : (fun n => tyRename Nat.succ (var n)) = var := rfl
    simp only [subst, this, ih]
  | tapp t B ih => simp only [subst, ih]

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

/-- `(t (up σ))[u] = t (u · σ)`. -/
theorem inst_up (σ : Nat → Term) (t u : Term) : inst (subst (up σ) t) u = subst (cons u σ) t := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, cons, subst_rename]
    exact subst_var _

/-- Type substitution commutes with single term substitution. -/
theorem tySubst_inst (τ : Nat → Ty) (t u : Term) :
    tySubst τ (inst t u) = inst (tySubst τ t) (tySubst τ u) := by
  simp only [inst, tySubst_subst]
  congr 1
  funext n; cases n <;> rfl

/-- Type substitution commutes with single type substitution. -/
theorem tySubst_tyInst (τ : Nat → Ty) (t : Term) (B : Ty) :
    tySubst τ (tyInst t B) = tyInst (tySubst (Ty.up τ) t) (B.subst τ) := by
  simp only [tyInst, tySubst_tySubst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, Ty.up, Ty.cons, Ty.subst_rename]
    exact (Ty.subst_tvar _).symm

/-- Term substitution commutes with single type substitution. -/
theorem subst_tyInst (σ : Nat → Term) (t : Term) (B : Ty) :
    subst σ (tyInst t B) = tyInst (subst (fun n => tyRename Nat.succ (σ n)) t) B := by
  simp only [tyInst, tySubst_subst]
  congr 1
  funext n
  exact (tySubst_cons_tyRename_succ B (σ n)).symm

/-- Instantiating the type abstraction produced by substitution under a `Λ`. -/
theorem tyInst_subst_tySubst (σ : Nat → Term) (τ : Nat → Ty) (t : Term) (B : Ty) :
    tyInst (subst (fun n => tyRename Nat.succ (σ n)) (tySubst (Ty.up τ) t)) B =
      subst σ (tySubst (Ty.subst (Ty.cons B Ty.tvar) ∘ Ty.up τ) t) := by
  simp only [tyInst, tySubst_subst, tySubst_tySubst]
  congr 1
  funext n
  exact tySubst_cons_tyRename_succ B (σ n)

end Term

open Term

/-! ## Reduction under substitution -/

/-- **Reduction is stable under term substitution.** -/
theorem Step.subst {t t' : Term} (h : Step t t') : ∀ σ, Step (Term.subst σ t) (Term.subst σ t') := by
  induction h <;> intro σ <;> simp only [Term.subst, subst_inst, subst_tyInst] <;>
    constructor <;> apply_assumption

/-- **Reduction is stable under type substitution.** -/
theorem Step.tySubst {t t' : Term} (h : Step t t') :
    ∀ τ, Step (Term.tySubst τ t) (Term.tySubst τ t') := by
  induction h <;> intro τ <;> simp only [Term.tySubst, tySubst_inst, tySubst_tyInst] <;>
    constructor <;> apply_assumption

/-! ## Deciding whether a term can step -/

/-- A term is **normal** when no reduction step applies. -/
def Normal (t : Term) : Prop := ∀ t', ¬ Step t t'

/-- The body of an abstraction, if the term is one. -/
def lamBody : Term → Option Term
  | lam s => some s
  | _ => none

/-- The body of a type abstraction, if the term is one. -/
def tlamBody : Term → Option Term
  | tlam s => some s
  | _ => none

/-- **One step of reduction, computed**: some one-step reduct, if there is one. -/
def step? : Term → Option Term
  | var _ => none
  | app t u => firstSome ((lamBody t).map (fun s => inst s u))
      (firstSome ((step? t).map (fun t' => app t' u)) ((step? u).map (app t)))
  | lam t => (step? t).map lam
  | tlam t => (step? t).map tlam
  | tapp t B => firstSome ((tlamBody t).map (fun s => tyInst s B)) ((step? t).map (fun t' => tapp t' B))

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
  | tlam t ih =>
    intro x h
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.tlam (ih _ ht)
  | tapp t B ih =>
    intro x h
    simp only [step?] at h
    rcases firstSome_eq_some h with h | h
    · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
      cases t <;> simp [tlamBody] at hs
      subst hs
      exact Step.tbeta _ _
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h; exact Step.tapp (ih _ ht)

/-- `step?` finds a reduct whenever there is one. -/
theorem step?_complete {t t' : Term} (h : Step t t') : (step? t).isSome := by
  induction h with
  | beta => simp [step?, lamBody, firstSome]
  | tbeta => simp [step?, tlamBody, firstSome]
  | appL _ ih => exact firstSome_isSome_right (firstSome_isSome_left (by simpa using ih))
  | appR _ ih => exact firstSome_isSome_right (firstSome_isSome_right (by simpa using ih))
  | lam _ ih => simpa [step?] using ih
  | tlam _ ih => simpa [step?] using ih
  | tapp _ ih => exact firstSome_isSome_right (by simpa using ih)

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

end SystemF

end Foundations.Types
