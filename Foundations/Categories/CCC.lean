import Foundations.Categories.Monads
import Foundations.Types.STLC

/-!
# Cartesian closed categories and the λ-calculus

A **cartesian closed category** (CCC) has a terminal object `1`, binary products
`X × Y`, and for any two objects `A`, `B` an **exponential** `A ⇒ B` — an object of
"arrows from `A` to `B`" — characterised by the currying bijection

  `(X × A ⟶ B)  ≅  (X ⟶ (A ⇒ B))`,

natural in `X`: the functor `− × A` is left adjoint to `A ⇒ −`. The category of types
is cartesian closed (`Adjunctions.lean`); so are the categories of sets, of
presheaves, of Scott domains, every topos (next file), and the Heyting algebras of
intuitionistic logic regarded as thin categories.

**Lambek's correspondence** (1970s, *Introduction to Higher-Order Categorical Logic*
with P. Scott, 1986) says that cartesian closed categories *are* the simply typed
λ-calculus, seen structurally:

| λ-calculus (Part V)              | cartesian closed category         |
|----------------------------------|-----------------------------------|
| type `A`                         | object `⟦A⟧`                      |
| context `x₁ : A₁, …, xₙ : Aₙ`     | product `1 × ⟦A₁⟧ × ⋯ × ⟦Aₙ⟧`      |
| term `Γ ⊢ t : B`                 | arrow `⟦Γ⟧ ⟶ ⟦B⟧`                  |
| variable                         | projection                        |
| `λx. t`                          | currying `curry ⟦t⟧`              |
| application `t u`                | `⟨⟦t⟧, ⟦u⟧⟩ ≫ eval`                 |
| substitution                     | composition                       |
| β-reduction / η-expansion        | equality of arrows                |

This file defines CCCs in general (with the exponential presented as a universal
arrow, and repackaged as an adjunction), shows that types form one, and then
**interprets the simply typed λ-calculus in an arbitrary CCC**: types become
objects, well-typed terms become arrows, and we prove **soundness** — β-reduction
(and the projection rules for pairs, and η) become equations between arrows. The key
lemma is that *substitution is composition*.

*Technical choice.* Part V presents the λ-calculus à la Curry: untyped de Bruijn terms
with a separate typing relation `Γ ⊢ t : A` (a proposition). Interpreting a term needs
recursion over its typing *derivation*, which must therefore be data. So we use the
equivalent **intrinsically typed** presentation (à la Church) of the `→, ×` fragment:
`Tm Γ A` is the type of terms of type `A` in context `Γ`, and ill-typed terms cannot
even be written. An **erasure** map sends each intrinsic term to a Part V term, which
is well typed there; erasure commutes with substitution, so every intrinsic reduction
step erases to a Part V reduction step. Thus the interpretation is genuinely a
semantics of Part V's calculus (for its `→, ×` fragment over atomic types).
-/

namespace Foundations.Categories

universe v u

open Category

/-- A **cartesian closed category**: a terminal object, chosen binary products and chosen
exponentials. The exponential `exp A B` (“`A ⇒ B`”) comes with an evaluation arrow
`eval : (A ⇒ B) × A ⟶ B` through which every arrow `X × A ⟶ B` factors uniquely, as
`(curry f) × 𝟙 ≫ eval`. -/
class CartesianClosed (C : Type u) [Category.{v} C] where
  /-- The terminal object. -/
  one : C
  /-- It is terminal. -/
  terminal : IsTerminal one
  /-- The product object. -/
  prod : C → C → C
  /-- The first projection. -/
  fst : {X Y : C} → (prod X Y ⟶ X)
  /-- The second projection. -/
  snd : {X Y : C} → (prod X Y ⟶ Y)
  /-- The product is a product. -/
  isProd : ∀ X Y : C, IsProduct X Y (prod X Y) fst snd
  /-- The exponential `A ⇒ B`. -/
  exp : C → C → C
  /-- Evaluation `(A ⇒ B) × A ⟶ B`. -/
  eval : {A B : C} → (prod (exp A B) A ⟶ B)
  /-- Currying: `X × A ⟶ B` gives `X ⟶ (A ⇒ B)`. -/
  curry : {X A B : C} → (prod X A ⟶ B) → (X ⟶ exp A B)
  /-- `(curry f × 𝟙) ≫ eval = f`. -/
  curry_eval : ∀ {X A B : C} (f : prod X A ⟶ B),
    (isProd (exp A B) A).lift (fst ≫ curry f) snd ≫ eval = f
  /-- `curry f` is the only arrow with this property. -/
  curry_uniq : ∀ {X A B : C} (f : prod X A ⟶ B) (g : X ⟶ exp A B),
    (isProd (exp A B) A).lift (fst ≫ g) snd ≫ eval = f → g = curry f

namespace CartesianClosed

variable {C : Type u} [Category.{v} C] [CartesianClosed C]

/-- The pairing `⟨f, g⟩ : W ⟶ X × Y`. -/
abbrev pair {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ prod X Y := (isProd X Y).lift f g

/-- The unique arrow to the terminal object. -/
def toOne (X : C) : X ⟶ one := terminal.lift X

/-- Arrows to the terminal object are all equal. -/
theorem toOne_uniq {X : C} (f g : X ⟶ (one : C)) : f = g := terminal.uniq f g

/-- The uniqueness of currying, in terms of `pair`. -/
theorem curry_uniq' {X A B : C} (f : prod X A ⟶ B) (g : X ⟶ exp A B)
    (h : pair (fst ≫ g) snd ≫ eval = f) : g = curry f := curry_uniq f g h

/-- `⟨f, g⟩ ≫ π₁ = f`. -/
@[simp] theorem pair_fst {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) : pair f g ≫ fst = f :=
  (isProd X Y).fac₁ f g

/-- `⟨f, g⟩ ≫ π₂ = g`. -/
@[simp] theorem pair_snd {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) : pair f g ≫ snd = g :=
  (isProd X Y).fac₂ f g

/-- Arrows into a product are determined by their components. -/
theorem hom_ext {W X Y : C} {h k : W ⟶ prod X Y} (h₁ : h ≫ fst = k ≫ fst)
    (h₂ : h ≫ snd = k ≫ snd) : h = k := (isProd X Y).hom_ext h₁ h₂

/-- `a ≫ ⟨f, g⟩ = ⟨a ≫ f, a ≫ g⟩`. -/
theorem comp_pair {V W X Y : C} (a : V ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
    a ≫ pair f g = pair (a ≫ f) (a ≫ g) := (isProd X Y).comp_lift a f g

/-- `⟨π₁, π₂⟩ = 𝟙`. -/
theorem pair_fst_snd {X Y : C} : pair (fst : prod X Y ⟶ X) snd = 𝟙 (prod X Y) :=
  hom_ext (by rw [pair_fst, id_comp]) (by rw [pair_snd, id_comp])

/-- `⟨f, g⟩ ≫ (h × 𝟙) = ⟨f ≫ h, g⟩`. -/
theorem pair_comp_prodMap {W X X' Y : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ X') :
    pair f g ≫ pair (fst ≫ h) snd = pair (f ≫ h) g :=
  hom_ext (by rw [assoc, pair_fst, ← assoc, pair_fst, pair_fst])
    (by rw [assoc, pair_snd, pair_snd, pair_snd])

/-- The defining equation of currying, in terms of `pair`. -/
@[simp] theorem curry_eval' {X A B : C} (f : prod X A ⟶ B) :
    pair (fst ≫ curry f) snd ≫ eval = f := curry_eval f

/-- **Naturality of currying**: `curry ((g × 𝟙) ≫ f) = g ≫ curry f`. -/
theorem curry_natural {X' X A B : C} (g : X' ⟶ X) (f : prod X A ⟶ B) :
    curry (pair (fst ≫ g) snd ≫ f) = g ≫ curry f :=
  (curry_uniq _ _ (by
    show pair (fst ≫ g ≫ curry f) snd ≫ eval = pair (fst ≫ g) snd ≫ f
    rw [← assoc, ← pair_comp_prodMap, assoc, curry_eval'])).symm

/-- `curry` of `(g × 𝟙) ≫ eval` is `g` (the η-law). -/
theorem curry_eval_eta {X A B : C} (g : X ⟶ exp A B) : curry (pair (fst ≫ g) snd ≫ eval) = g :=
  (curry_uniq _ g rfl).symm

/-- Currying a composite: `curry (g ≫ h) = curry g ≫ curry (eval ≫ h)`. -/
theorem curry_comp {X A B B' : C} (g : prod X A ⟶ B) (h : B ⟶ B') :
    curry (g ≫ h) = curry g ≫ curry (eval ≫ h) := by
  refine (curry_uniq' _ _ ?_).symm
  have e : pair (fst ≫ curry g ≫ curry (eval ≫ h)) (snd : prod X A ⟶ A) =
      pair (fst ≫ curry g) (snd : prod X A ⟶ A) ≫ pair (fst ≫ curry (eval ≫ h)) snd := by
    rw [pair_comp_prodMap, assoc]
  rw [e, assoc, curry_eval', ← assoc, curry_eval']

/-- `curry eval = 𝟙`. -/
theorem curry_eval_id {A B : C} : curry (eval : prod (exp A B) A ⟶ B) = 𝟙 _ :=
  (curry_uniq' _ _ (by rw [comp_id, pair_fst_snd, id_comp])).symm

/-- The functor `− × A`. -/
def prodFunctor (A : C) : C ⥤ C where
  obj X := prod X A
  map f := pair (fst ≫ f) snd
  map_id _ := by rw [comp_id, pair_fst_snd]
  map_comp f g := by rw [pair_comp_prodMap, assoc]

/-- The functor `A ⇒ −`. -/
def expFunctor (A : C) : C ⥤ C where
  obj B := exp A B
  map g := curry (eval ≫ g)
  map_id _ := by rw [comp_id]; exact curry_eval_id
  map_comp f g := by rw [← assoc]; exact curry_comp _ _

/-- **Exponentials as an adjunction**: in a CCC, `(− × A) ⊣ (A ⇒ −)`, the bijection being
currying. -/
def expAdjunction (A : C) : Adjunction (prodFunctor A) (expFunctor A) where
  homEquiv _ _ :=
    { toFun := fun f => curry f
      invFun := fun g => pair (fst ≫ g) snd ≫ eval
      left_inv := fun f => curry_eval' f
      right_inv := fun g => curry_eval_eta g }
  natural_left f g := curry_natural f g
  natural_right g h := curry_comp g h


end CartesianClosed

/-- **The category of types is cartesian closed**: one-point type, cartesian product, and
the function type `A → B` with evaluation `(g, a) ↦ g a` and currying. -/
instance typesCCC : CartesianClosed (Type u) where
  one := PUnit
  terminal := types_terminal
  prod X Y := X × Y
  fst := fun p => p.1
  snd := fun p => p.2
  isProd X Y := types_product X Y
  exp A B := A → B
  eval := fun p => p.1 p.2
  curry f := fun x a => f (x, a)
  curry_eval _ := rfl
  curry_uniq _ _ h := funext fun x => funext fun a => congrFun h (x, a)

/-! ## The `→, ×` fragment of the simply typed λ-calculus, intrinsically typed -/

namespace Lambek

open Foundations.Types.STLC (Ty Term HasType Step)

/-- Simple types of the `→, ×` fragment, over atoms indexed by natural numbers. -/
inductive FTy where
  /-- An atomic type. -/
  | atom (n : Nat)
  /-- Function type `A → B`. -/
  | arr (A B : FTy)
  /-- Product type `A × B`. -/
  | prod (A B : FTy)

/-- The inclusion of fragment types into the types of Part V. -/
def FTy.toTy : FTy → Ty
  | .atom n => .atom n
  | .arr A B => .arr A.toTy B.toTy
  | .prod A B => .prod A.toTy B.toTy

/-- A variable of type `A` in context `Γ`: a typed de Bruijn index (the most recently bound
variable is `here`). -/
inductive Mem : FTy → List FTy → Type where
  /-- The last variable of the context. -/
  | here {A : FTy} {Γ : List FTy} : Mem A (A :: Γ)
  /-- A variable further out. -/
  | there {A B : FTy} {Γ : List FTy} : Mem A Γ → Mem A (B :: Γ)

/-- The de Bruijn index of a variable. -/
def Mem.idx : {A : FTy} → {Γ : List FTy} → Mem A Γ → Nat
  | _, _, .here => 0
  | _, _, .there v => v.idx + 1

/-- **Intrinsically typed terms**: `Tm Γ A` is the type of terms of type `A` in context `Γ`.
Only well-typed terms can be formed. -/
inductive Tm : List FTy → FTy → Type where
  /-- A variable. -/
  | var {Γ : List FTy} {A : FTy} : Mem A Γ → Tm Γ A
  /-- λ-abstraction. -/
  | lam {Γ : List FTy} {A B : FTy} : Tm (A :: Γ) B → Tm Γ (.arr A B)
  /-- Application. -/
  | app {Γ : List FTy} {A B : FTy} : Tm Γ (.arr A B) → Tm Γ A → Tm Γ B
  /-- Pairing. -/
  | pair {Γ : List FTy} {A B : FTy} : Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  /-- First projection. -/
  | fst {Γ : List FTy} {A B : FTy} : Tm Γ (.prod A B) → Tm Γ A
  /-- Second projection. -/
  | snd {Γ : List FTy} {A B : FTy} : Tm Γ (.prod A B) → Tm Γ B

/-- A **renaming** from `Γ` to `Δ`: every variable of `Γ` becomes a variable of `Δ` of the
same type. -/
abbrev Ren (Γ Δ : List FTy) : Type := ∀ {A : FTy}, Mem A Γ → Mem A Δ

/-- Extending a renaming under a binder. -/
def Ren.lift {Γ Δ : List FTy} {B : FTy} (ρ : Ren Γ Δ) : Ren (B :: Γ) (B :: Δ) := fun v =>
  match v with
  | .here => .here
  | .there w => .there (ρ w)

/-- Renaming a term. -/
def rename : {Γ Δ : List FTy} → {A : FTy} → Ren Γ Δ → Tm Γ A → Tm Δ A
  | _, _, _, ρ, .var v => .var (ρ v)
  | _, _, _, ρ, .lam t => .lam (rename ρ.lift t)
  | _, _, _, ρ, .app t u => .app (rename ρ t) (rename ρ u)
  | _, _, _, ρ, .pair a b => .pair (rename ρ a) (rename ρ b)
  | _, _, _, ρ, .fst t => .fst (rename ρ t)
  | _, _, _, ρ, .snd t => .snd (rename ρ t)

/-- A **substitution** from `Γ` to `Δ`: a term in context `Δ` for every variable of `Γ`. -/
abbrev Sub (Γ Δ : List FTy) : Type := ∀ {A : FTy}, Mem A Γ → Tm Δ A

/-- Extending a substitution under a binder. -/
def Sub.lift {Γ Δ : List FTy} {B : FTy} (σ : Sub Γ Δ) : Sub (B :: Γ) (B :: Δ) := fun v =>
  match v with
  | .here => .var .here
  | .there w => rename (fun x => .there x) (σ w)

/-- Applying a substitution to a term. -/
def subst : {Γ Δ : List FTy} → {A : FTy} → Sub Γ Δ → Tm Γ A → Tm Δ A
  | _, _, _, σ, .var v => σ v
  | _, _, _, σ, .lam t => .lam (subst σ.lift t)
  | _, _, _, σ, .app t u => .app (subst σ t) (subst σ u)
  | _, _, _, σ, .pair a b => .pair (subst σ a) (subst σ b)
  | _, _, _, σ, .fst t => .fst (subst σ t)
  | _, _, _, σ, .snd t => .snd (subst σ t)

/-- The substitution replacing the last variable by `u` and leaving the others alone. -/
def Sub.single {Γ : List FTy} {A : FTy} (u : Tm Γ A) : Sub (A :: Γ) Γ := fun v =>
  match v with
  | .here => u
  | .there w => .var w

/-- Substituting `u` for the bound variable of `t`: `t[u/x]`. -/
def inst {Γ : List FTy} {A B : FTy} (t : Tm (A :: Γ) B) (u : Tm Γ A) : Tm Γ B :=
  subst (Sub.single u) t

/-- **One-step reduction** of intrinsic terms: β for functions, projections of pairs, and
congruence under every constructor. -/
inductive TStep : {Γ : List FTy} → {A : FTy} → Tm Γ A → Tm Γ A → Prop where
  /-- `(λx. t) u ⟶ t[u/x]`. -/
  | beta {Γ : List FTy} {A B : FTy} (t : Tm (A :: Γ) B) (u : Tm Γ A) :
      TStep (.app (.lam t) u) (inst t u)
  /-- `π₁ ⟨a, b⟩ ⟶ a`. -/
  | fstPair {Γ : List FTy} {A B : FTy} (a : Tm Γ A) (b : Tm Γ B) : TStep (.fst (.pair a b)) a
  /-- `π₂ ⟨a, b⟩ ⟶ b`. -/
  | sndPair {Γ : List FTy} {A B : FTy} (a : Tm Γ A) (b : Tm Γ B) : TStep (.snd (.pair a b)) b
  /-- Reduce the function of an application. -/
  | appL {Γ : List FTy} {A B : FTy} {t t' : Tm Γ (.arr A B)} (u : Tm Γ A) :
      TStep t t' → TStep (.app t u) (.app t' u)
  /-- Reduce the argument of an application. -/
  | appR {Γ : List FTy} {A B : FTy} (t : Tm Γ (.arr A B)) {u u' : Tm Γ A} :
      TStep u u' → TStep (.app t u) (.app t u')
  /-- Reduce under a λ. -/
  | lam {Γ : List FTy} {A B : FTy} {t t' : Tm (A :: Γ) B} : TStep t t' → TStep (.lam t) (.lam t')
  /-- Reduce the first component of a pair. -/
  | pairL {Γ : List FTy} {A B : FTy} {a a' : Tm Γ A} (b : Tm Γ B) :
      TStep a a' → TStep (.pair a b) (.pair a' b)
  /-- Reduce the second component of a pair. -/
  | pairR {Γ : List FTy} {A B : FTy} (a : Tm Γ A) {b b' : Tm Γ B} :
      TStep b b' → TStep (.pair a b) (.pair a b')
  /-- Reduce under a first projection. -/
  | fst {Γ : List FTy} {A B : FTy} {t t' : Tm Γ (.prod A B)} : TStep t t' → TStep (.fst t) (.fst t')
  /-- Reduce under a second projection. -/
  | snd {Γ : List FTy} {A B : FTy} {t t' : Tm Γ (.prod A B)} : TStep t t' → TStep (.snd t) (.snd t')

/-! ## Erasure to Part V -/

/-- **Erasure**: forget the types, obtaining a Part V term (with de Bruijn indices). -/
def erase : {Γ : List FTy} → {A : FTy} → Tm Γ A → Term
  | _, _, .var v => .var v.idx
  | _, _, .lam t => .lam (erase t)
  | _, _, .app t u => .app (erase t) (erase u)
  | _, _, .pair a b => .pair (erase a) (erase b)
  | _, _, .fst t => .fst (erase t)
  | _, _, .snd t => .snd (erase t)

/-- The index of a variable points to its type in the erased context. -/
theorem Mem.lookup {A : FTy} {Γ : List FTy} (v : Mem A Γ) :
    (Γ.map FTy.toTy)[v.idx]? = some A.toTy := by
  induction v with
  | here => rfl
  | there w ih => simpa [Mem.idx] using ih

/-- **Erased terms are well typed in Part V**: if `t : Tm Γ A` then `Γ ⊢ erase t : A`. -/
theorem erase_hasType {Γ : List FTy} {A : FTy} (t : Tm Γ A) :
    HasType (Γ.map FTy.toTy) (erase t) A.toTy := by
  induction t with
  | var v => exact .var v.lookup
  | lam _ ih => exact .lam ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

/-- Erasure commutes with renaming (for a renaming tracked by an index map `ξ`). -/
theorem erase_rename {Γ Δ : List FTy} {A : FTy} (t : Tm Γ A) (ρ : Ren Γ Δ) (ξ : Nat → Nat)
    (h : ∀ {B : FTy} (v : Mem B Γ), (ρ v).idx = ξ v.idx) :
    erase (rename ρ t) = Foundations.Types.STLC.rename ξ (erase t) := by
  induction t generalizing Δ ξ with
  | var v => exact congrArg Term.var (h v)
  | lam t ih =>
    refine congrArg Term.lam (ih ρ.lift _ fun v => ?_)
    cases v with
    | here => rfl
    | there w => exact congrArg (· + 1) (h w)
  | app _ _ ih₁ ih₂ =>
    show Term.app _ _ = Term.app _ _
    rw [ih₁ ρ ξ h, ih₂ ρ ξ h]
  | pair _ _ ih₁ ih₂ =>
    show Term.pair _ _ = Term.pair _ _
    rw [ih₁ ρ ξ h, ih₂ ρ ξ h]
  | fst _ ih => exact congrArg Term.fst (ih ρ ξ h)
  | snd _ ih => exact congrArg Term.snd (ih ρ ξ h)

/-- Erasure commutes with substitution (for a substitution tracked by `τ`). -/
theorem erase_subst {Γ Δ : List FTy} {A : FTy} (t : Tm Γ A) (σ : Sub Γ Δ) (τ : Nat → Term)
    (h : ∀ {B : FTy} (v : Mem B Γ), erase (σ v) = τ v.idx) :
    erase (subst σ t) = Foundations.Types.STLC.subst τ (erase t) := by
  induction t generalizing Δ τ with
  | var v => exact h v
  | lam t ih =>
    refine congrArg Term.lam (ih σ.lift _ fun v => ?_)
    cases v with
    | here => rfl
    | there w =>
      show erase (rename _ (σ w)) = Foundations.Types.STLC.rename Nat.succ (τ w.idx)
      rw [erase_rename (σ w) _ Nat.succ (fun _ => rfl), h w]
  | app _ _ ih₁ ih₂ =>
    show Term.app _ _ = Term.app _ _
    rw [ih₁ σ τ h, ih₂ σ τ h]
  | pair _ _ ih₁ ih₂ =>
    show Term.pair _ _ = Term.pair _ _
    rw [ih₁ σ τ h, ih₂ σ τ h]
  | fst _ ih => exact congrArg Term.fst (ih σ τ h)
  | snd _ ih => exact congrArg Term.snd (ih σ τ h)

/-- Erasure commutes with single substitution: `erase (t[u/x]) = (erase t)[erase u/x]`. -/
theorem erase_inst {Γ : List FTy} {A B : FTy} (t : Tm (A :: Γ) B) (u : Tm Γ A) :
    erase (inst t u) = Foundations.Types.STLC.inst (erase t) (erase u) :=
  erase_subst t _ _ fun v => by cases v <;> rfl

/-- **Intrinsic reduction is Part V reduction**: every step of intrinsic terms erases to a
step of Part V's reduction relation. -/
theorem TStep.erase {Γ : List FTy} {A : FTy} {t t' : Tm Γ A} (h : TStep t t') :
    Step (Lambek.erase t) (Lambek.erase t') := by
  induction h with
  | beta t u =>
    show Step (.app (.lam _) _) _
    rw [erase_inst]; exact .beta _ _
  | fstPair a b => exact .fstPair _ _
  | sndPair a b => exact .sndPair _ _
  | appL _ _ ih => exact .appL ih
  | appR _ _ ih => exact .appR ih
  | lam _ ih => exact .lam ih
  | pairL _ _ ih => exact .pairL ih
  | pairR _ _ ih => exact .pairR ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

/-! ## Interpretation in an arbitrary cartesian closed category -/

section Semantics

open CartesianClosed

variable {C : Type u} [Category.{v} C] [CartesianClosed C] (ι : Nat → C)

/-- **Types are objects**: the interpretation of a type, given objects `ι n` for the atoms;
`→` becomes the exponential and `×` the product. -/
@[reducible] def semTy : FTy → C
  | .atom n => ι n
  | .arr A B => exp (semTy A) (semTy B)
  | .prod A B => prod (semTy A) (semTy B)

/-- **Contexts are products**: `⟦A₁, …, Aₙ⟧ = (⋯(1 × ⟦Aₙ⟧) × ⋯) × ⟦A₁⟧` (the most recent
variable on the right). -/
@[reducible] def semCtx : List FTy → C
  | [] => one
  | A :: Γ => prod (semCtx Γ) (semTy ι A)

/-- **Variables are projections.** -/
def semVar : {A : FTy} → {Γ : List FTy} → Mem A Γ → (semCtx ι Γ ⟶ semTy ι A)
  | _, _, .here => snd
  | _, _, .there v => fst ≫ semVar v

/-- **Terms are arrows**: the interpretation of `Γ ⊢ t : A` as an arrow `⟦Γ⟧ ⟶ ⟦A⟧`.
Abstraction is currying, application is pairing followed by evaluation. -/
def semTm : {Γ : List FTy} → {A : FTy} → Tm Γ A → (semCtx ι Γ ⟶ semTy ι A)
  | _, _, .var v => semVar ι v
  | _, _, .lam t => curry (semTm t)
  | _, _, .app t u => pair (semTm t) (semTm u) ≫ eval
  | _, _, .pair a b => pair (semTm a) (semTm b)
  | _, _, .fst t => semTm t ≫ fst
  | _, _, .snd t => semTm t ≫ snd

/-- **Substitutions are arrows** `⟦Δ⟧ ⟶ ⟦Γ⟧`, tupling the interpretations of the
substituted terms. -/
def semSub {Δ : List FTy} : {Γ : List FTy} → Sub Γ Δ → (semCtx ι Δ ⟶ semCtx ι Γ)
  | [], _ => toOne _
  | _ :: _, σ => pair (semSub fun v => σ (.there v)) (semTm ι (σ .here))

/-- A substituted variable is interpreted by composing with the substitution. -/
theorem semVar_sub {Δ Γ : List FTy} {A : FTy} (σ : Sub Γ Δ) (v : Mem A Γ) :
    semTm ι (σ v) = semSub ι σ ≫ semVar ι v := by
  induction v with
  | here => exact (pair_snd _ _).symm
  | there w ih =>
    have e : semSub ι σ ≫ fst = semSub ι (fun v => σ (.there v)) := pair_fst _ _
    show _ = semSub ι σ ≫ fst ≫ semVar ι w
    rw [← assoc, e]
    exact ih (fun v => σ (.there v))

/-- If every `σ' v` is `f ≫ σ v` semantically, then `⟦σ'⟧ = f ≫ ⟦σ⟧`. -/
theorem semSub_comp {Δ Δ' Γ : List FTy} (σ : Sub Γ Δ) (σ' : Sub Γ Δ')
    (f : semCtx ι Δ' ⟶ semCtx ι Δ)
    (h : ∀ {A : FTy} (v : Mem A Γ), semTm ι (σ' v) = f ≫ semTm ι (σ v)) :
    semSub ι σ' = f ≫ semSub ι σ := by
  induction Γ with
  | nil => exact toOne_uniq _ _
  | cons B Γ ih =>
    show pair _ _ = f ≫ pair _ _
    rw [comp_pair, ih (fun v => σ (.there v)) (fun v => σ' (.there v)) (fun v => h (.there v)),
      h .here]

/-- The identity substitution is interpreted by the identity. -/
theorem semSub_id {Γ : List FTy} : semSub ι (Γ := Γ) (fun v => .var v) = 𝟙 _ := by
  induction Γ with
  | nil => exact toOne_uniq _ _
  | cons B Γ ih =>
    show pair (semSub ι fun v => Tm.var (Mem.there v)) snd = 𝟙 _
    rw [semSub_comp ι (fun v => Tm.var v) _ fst (fun _ => rfl), ih, comp_id, pair_fst_snd]

/-- The interpretation of a lifted substitution is `⟦σ⟧ × 𝟙`, provided weakening is
interpreted by the first projection. -/
theorem semSub_lift_aux {Δ Γ : List FTy} {B : FTy} (σ : Sub Γ Δ) (σ' : Sub (B :: Γ) (B :: Δ))
    (h₀ : semTm ι (σ' .here) = snd)
    (h : ∀ {A : FTy} (v : Mem A Γ), semTm ι (σ' (.there v)) = fst ≫ semTm ι (σ v)) :
    semSub ι σ' = pair (fst ≫ semSub ι σ) snd := by
  show pair _ _ = _
  rw [h₀, semSub_comp ι σ (fun v => σ' (.there v)) fst h]

/-- **Renaming is composition**: `⟦rename ρ t⟧ = ⟦ρ⟧ ≫ ⟦t⟧`. -/
theorem sem_rename {Γ Δ : List FTy} {A : FTy} (t : Tm Γ A) (ρ : Ren Γ Δ) :
    semTm ι (rename ρ t) = semSub ι (fun v => .var (ρ v)) ≫ semTm ι t := by
  induction t generalizing Δ with
  | var v => exact semVar_sub ι (fun v => .var (ρ v)) v
  | lam t ih =>
    show curry _ = _ ≫ curry _
    rw [ih ρ.lift, semSub_lift_aux ι (fun v => .var (ρ v)) _ rfl (fun _ => rfl), curry_natural]
  | app t u iht ihu =>
    show pair _ _ ≫ eval = _ ≫ pair _ _ ≫ eval
    rw [iht ρ, ihu ρ, ← assoc, comp_pair]
  | pair a b iha ihb =>
    show pair _ _ = _ ≫ pair _ _
    rw [iha ρ, ihb ρ, comp_pair]
  | fst t ih =>
    show _ ≫ fst = _ ≫ _ ≫ fst
    rw [ih ρ, assoc]
  | snd t ih =>
    show _ ≫ snd = _ ≫ _ ≫ snd
    rw [ih ρ, assoc]

/-- **Weakening is the first projection**: `⟦t⟧` in an extended context is `π₁ ≫ ⟦t⟧`. -/
theorem sem_weaken {Γ : List FTy} {A B : FTy} (t : Tm Γ A) :
    semTm ι (rename (fun x => Mem.there (B := B) x) t) = fst ≫ semTm ι t := by
  rw [sem_rename, semSub_comp ι (fun v => .var v) _ fst (fun _ => rfl), semSub_id, comp_id]

/-- **The substitution lemma: substitution is composition**,
`⟦t[σ]⟧ = ⟦σ⟧ ≫ ⟦t⟧`. -/
theorem sem_subst {Γ Δ : List FTy} {A : FTy} (t : Tm Γ A) (σ : Sub Γ Δ) :
    semTm ι (subst σ t) = semSub ι σ ≫ semTm ι t := by
  induction t generalizing Δ with
  | var v => exact semVar_sub ι σ v
  | lam t ih =>
    show curry _ = _ ≫ curry _
    rw [ih σ.lift, semSub_lift_aux ι σ _ rfl (fun v => sem_weaken ι (σ v)), curry_natural]
  | app t u iht ihu =>
    show pair _ _ ≫ eval = _ ≫ pair _ _ ≫ eval
    rw [iht σ, ihu σ, ← assoc, comp_pair]
  | pair a b iha ihb =>
    show pair _ _ = _ ≫ pair _ _
    rw [iha σ, ihb σ, comp_pair]
  | fst t ih =>
    show _ ≫ fst = _ ≫ _ ≫ fst
    rw [ih σ, assoc]
  | snd t ih =>
    show _ ≫ snd = _ ≫ _ ≫ snd
    rw [ih σ, assoc]

/-- **Soundness of β**: `⟦(λx. t) u⟧ = ⟦t[u/x]⟧` in every cartesian closed category. -/
theorem sem_beta {Γ : List FTy} {A B : FTy} (t : Tm (A :: Γ) B) (u : Tm Γ A) :
    semTm ι (.app (.lam t) u) = semTm ι (inst t u) := by
  show pair (curry (semTm ι t)) (semTm ι u) ≫ eval = semTm ι (subst (Sub.single u) t)
  rw [sem_subst]
  show _ = pair (semSub ι fun v => Tm.var v) (semTm ι u) ≫ semTm ι t
  rw [semSub_id]
  have : pair (curry (semTm ι t)) (semTm ι u) =
      pair (𝟙 _) (semTm ι u) ≫ pair (fst ≫ curry (semTm ι t)) snd := by
    rw [pair_comp_prodMap, id_comp]
  rw [this, assoc, curry_eval']

/-- **Soundness of η**: `⟦λx. t x⟧ = ⟦t⟧` (where `t` is weakened past `x`). -/
theorem sem_eta {Γ : List FTy} {A B : FTy} (t : Tm Γ (.arr A B)) :
    semTm ι (.lam (.app (rename (fun x => Mem.there x) t) (.var .here))) = semTm ι t := by
  show curry (pair _ snd ≫ eval) = _
  rw [sem_weaken]
  exact curry_eval_eta _

/-- **Soundness of the product rules**: `⟦π₁ ⟨a, b⟩⟧ = ⟦a⟧`, `⟦π₂ ⟨a, b⟩⟧ = ⟦b⟧` and
`⟦⟨π₁ t, π₂ t⟩⟧ = ⟦t⟧` (surjective pairing). -/
theorem sem_pair_rules {Γ : List FTy} {A B : FTy} (a : Tm Γ A) (b : Tm Γ B)
    (t : Tm Γ (.prod A B)) :
    semTm ι (.fst (.pair a b)) = semTm ι a ∧ semTm ι (.snd (.pair a b)) = semTm ι b ∧
      semTm ι (.pair (.fst t) (.snd t)) = semTm ι t :=
  ⟨pair_fst _ _, pair_snd _ _, hom_ext (pair_fst _ _) (pair_snd _ _)⟩

/-- **Soundness of reduction (Lambek)**: if `t` reduces to `t'` in one step, then `t` and
`t'` denote the same arrow in every cartesian closed category, under every interpretation
of the atomic types. Computation is invisible to the semantics: β-reduction *is*
equality of arrows. -/
theorem sem_sound {Γ : List FTy} {A : FTy} {t t' : Tm Γ A} (h : TStep t t') :
    semTm ι t = semTm ι t' := by
  induction h with
  | beta t u => exact sem_beta ι t u
  | fstPair a b => exact pair_fst _ _
  | sndPair a b => exact pair_snd _ _
  | appL u _ ih =>
    show pair _ _ ≫ eval = pair _ _ ≫ eval
    rw [ih]
  | appR t _ ih =>
    show pair _ _ ≫ eval = pair _ _ ≫ eval
    rw [ih]
  | lam _ ih =>
    show curry _ = curry _
    rw [ih]
  | pairL b _ ih =>
    show pair _ _ = pair _ _
    rw [ih]
  | pairR a _ ih =>
    show pair _ _ = pair _ _
    rw [ih]
  | fst _ ih =>
    show _ ≫ fst = _ ≫ fst
    rw [ih]
  | snd _ ih =>
    show _ ≫ snd = _ ≫ snd
    rw [ih]

end Semantics

/-! ## Example: the set-theoretic semantics -/

/-- In the CCC of types, the interpretation is the familiar "standard semantics": for
instance the closed term `λx. λy. x` (the K combinator) denotes the function returning
constant functions. -/
theorem types_sem_K (ι : Nat → Type u) (a b : ι 0) :
    (semTm ι (Γ := []) (A := .arr (.atom 0) (.arr (.atom 0) (.atom 0)))
      (.lam (.lam (.var (.there .here)))) : PUnit → (ι 0 → ι 0 → ι 0)) PUnit.unit a b = a :=
  rfl

end Lambek

end Foundations.Categories
