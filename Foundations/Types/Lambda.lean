/-!
# The untyped λ-calculus and the Church–Rosser theorem

In the 1930s Alonzo Church proposed the **λ-calculus** as a foundation for
logic and as an analysis of the notion of an *effectively calculable function*.
It has just three kinds of expression: variables, *application* `t u` ("apply
the function `t` to `u`"), and *abstraction* `λx. t` ("the function sending `x`
to `t`"). Computation is a single rule, **β-reduction**: `(λx. t) u ⟶ t[x := u]`,
substitute the argument for the parameter. Everything else — numbers,
booleans, pairs, recursion — can be *encoded* (Church numerals below).

Two things make the calculus delicate.

* **Variables and substitution.** Substituting must not capture free
  variables. Following N. G. de Bruijn (1972) we avoid names altogether: a
  variable is a number `n`, pointing to the `n`-th enclosing `λ`. So `λx. λy. x`
  is written `λ λ 1`. Substitution then becomes a purely mechanical operation
  on these numbers, with a small algebra of laws (`subst_subst` etc.).
* **Order of evaluation.** A term may contain several redexes; does the choice
  matter? The **Church–Rosser theorem** (1936) says no: if `t` reduces to `u`
  and to `v`, then `u` and `v` reduce to a common term. Hence normal forms, when
  they exist, are unique: a λ-term has at most one "value". We give the elegant
  proof of Tait and Martin-Löf, through *parallel reduction*, in the streamlined
  form of Takahashi: every term `t` has a *complete development* `cd t`
  (contract all its redexes at once), and any parallel step from `t` can be
  completed to `cd t` (the "triangle property").

Not every term has a normal form: `Ω = (λx. x x)(λx. x x)` reduces only to
itself. Computation can run forever — the price of the calculus' expressive
power (it is Turing-complete), and the reason why *typed* calculi, studied in
the following files, are needed when λ-terms are to serve as proofs.
-/

namespace Foundations.Types

/-! ## Reflexive–transitive closure -/

/-- The **reflexive–transitive closure** `R*` of a relation: finitely many `R`-steps. -/
inductive Star {α : Type _} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star R a a
  | tail {a b c : α} : Star R a b → R b c → Star R a c

namespace Star

variable {α : Type _} {R : α → α → Prop}

/-- A single step is a reduction sequence. -/
theorem single {a b : α} (h : R a b) : Star R a b := tail (refl a) h

/-- Reduction sequences compose. -/
theorem trans {a b c : α} (h₁ : Star R a b) (h₂ : Star R b c) : Star R a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact tail ih h

/-- A step followed by a reduction sequence. -/
theorem head {a b c : α} (h₁ : R a b) (h₂ : Star R b c) : Star R a c := trans (single h₁) h₂

/-- A map that turns `R`-steps into `S`-steps turns `R*` into `S*`. -/
theorem map {β : Type _} {S : β → β → Prop} (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b))
    {a b : α} (h : Star R a b) : Star S (f a) (f b) := by
  induction h with
  | refl => exact refl _
  | tail _ h ih => exact tail ih (hf _ _ h)

/-- Analysing a reduction sequence by its first step: either it is empty, or it
begins with a step. -/
theorem cases_head {a c : α} (h : Star R a c) : a = c ∨ ∃ b, R a b ∧ Star R b c := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
    rcases ih with rfl | ⟨x, hx, hxb⟩
    · exact Or.inr ⟨c, hbc, refl c⟩
    · exact Or.inr ⟨x, hx, tail hxb hbc⟩

/-- Monotonicity: if `R ⊆ S*` then `R* ⊆ S*`. -/
theorem flatten {S : α → α → Prop} (hRS : ∀ a b, R a b → Star S a b) {a b : α}
    (h : Star R a b) : Star S a b := by
  induction h with
  | refl => exact refl _
  | tail _ h ih => exact trans ih (hRS _ _ h)

end Star

namespace Lambda

/-! ## Terms with de Bruijn indices -/

/-- **Untyped λ-terms** with de Bruijn indices: `var n` refers to the `n`-th
enclosing binder. -/
inductive Term where
  /-- A variable (de Bruijn index). -/
  | var (n : Nat)
  /-- Application `t u`. -/
  | app (t u : Term)
  /-- Abstraction `λ. t`. -/
  | lam (t : Term)
  deriving DecidableEq, Repr

open Term

/-! ## Renaming and substitution -/

/-- Lifting a renaming under a binder: index `0` stays, others shift. -/
def upRen (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

/-- Renaming the free variables of a term by `ξ`. -/
def rename (ξ : Nat → Nat) : Term → Term
  | var n => var (ξ n)
  | app t u => app (rename ξ t) (rename ξ u)
  | lam t => lam (rename (upRen ξ) t)

/-- Lifting a substitution under a binder. -/
def up (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

/-- **Simultaneous substitution**: replace each free variable `n` by `σ n`. -/
def subst (σ : Nat → Term) : Term → Term
  | var n => σ n
  | app t u => app (subst σ t) (subst σ u)
  | lam t => lam (subst (up σ) t)

/-- Extending a substitution: `0 ↦ u`, `n + 1 ↦ σ n`. -/
def cons (u : Term) (σ : Nat → Term) : Nat → Term
  | 0 => u
  | n + 1 => σ n

/-- **Single substitution** `t[u]`: substitute `u` for variable `0` in `t` (and
lower the other free variables by one), as β-reduction requires. -/
def inst (t u : Term) : Term := subst (cons u var) t

/-- Lifting commutes with composition of renamings. -/
theorem upRen_comp (ξ ζ : Nat → Nat) : upRen ξ ∘ upRen ζ = upRen (ξ ∘ ζ) := by
  funext n; cases n <;> rfl

/-- Renamings compose. -/
theorem rename_rename (t : Term) : ∀ ξ ζ, rename ξ (rename ζ t) = rename (ξ ∘ ζ) t := by
  induction t with
  | var n => intros; rfl
  | app t u iht ihu => intros; simp only [rename, iht, ihu]
  | lam t ih => intro ξ ζ; simp only [rename, ih, upRen_comp]

/-- Lifting a substitution after a lifted renaming. -/
theorem up_upRen (σ : Nat → Term) (ξ : Nat → Nat) : up σ ∘ upRen ξ = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

/-- Substitution after renaming. -/
theorem subst_rename (t : Term) : ∀ σ ξ, subst σ (rename ξ t) = subst (σ ∘ ξ) t := by
  induction t with
  | var n => intros; rfl
  | app t u iht ihu => intros; simp only [rename, subst, iht, ihu]
  | lam t ih => intro σ ξ; simp only [rename, subst, ih, up_upRen]

/-- A lifted renaming after a lifted substitution. -/
theorem rename_up (ξ : Nat → Nat) (σ : Nat → Term) :
    rename (upRen ξ) ∘ up σ = up (rename ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, rename_rename]
    rfl

/-- Renaming after substitution. -/
theorem rename_subst (t : Term) : ∀ ξ σ, rename ξ (subst σ t) = subst (rename ξ ∘ σ) t := by
  induction t with
  | var n => intros; rfl
  | app t u iht ihu => intros; simp only [rename, subst, iht, ihu]
  | lam t ih => intro ξ σ; simp only [rename, subst, ih, rename_up]

/-- Lifting commutes with composition of substitutions. -/
theorem up_comp (τ σ : Nat → Term) : subst (up τ) ∘ up σ = up (subst τ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, subst_rename, rename_subst]
    rfl

/-- **Substitutions compose**: substituting `σ` then `τ` is substituting `τ ∘ σ`. -/
theorem subst_subst (t : Term) : ∀ τ σ, subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  induction t with
  | var n => intros; rfl
  | app t u iht ihu => intros; simp only [subst, iht, ihu]
  | lam t ih => intro τ σ; simp only [subst, ih, up_comp]

/-- Lifting the identity substitution gives the identity. -/
theorem up_var : up var = var := by
  funext n; cases n <;> rfl

/-- The identity substitution does nothing. -/
theorem subst_var (t : Term) : subst var t = t := by
  induction t with
  | var n => rfl
  | app t u iht ihu => simp only [subst, iht, ihu]
  | lam t ih => simp only [subst, up_var, ih]

/-- Renaming commutes with single substitution. -/
theorem rename_inst (ξ : Nat → Nat) (t u : Term) :
    rename ξ (inst t u) = inst (rename (upRen ξ) t) (rename ξ u) := by
  simp only [inst, rename_subst, subst_rename]
  congr 1
  funext n; cases n <;> rfl

/-- Substitution commutes with single substitution:
`(t[u])σ = (t (up σ))[u σ]`. -/
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

/-! ## β-reduction -/

/-- **One-step β-reduction**, anywhere inside a term. -/
inductive Step : Term → Term → Prop
  /-- The β-rule `(λ. t) u ⟶ t[u]`. -/
  | beta (t u : Term) : Step (app (lam t) u) (inst t u)
  /-- Reduce in the function part. -/
  | appL {t t' u : Term} : Step t t' → Step (app t u) (app t' u)
  /-- Reduce in the argument. -/
  | appR {t u u' : Term} : Step u u' → Step (app t u) (app t u')
  /-- Reduce under a binder. -/
  | lam {t t' : Term} : Step t t' → Step (lam t) (lam t')

/-- Many-step β-reduction `t ⟶* u`. -/
abbrev Red : Term → Term → Prop := Star Step

/-- A term is in **normal form** when no β-step applies. -/
def Normal (t : Term) : Prop := ∀ t', ¬ Step t t'

/-- A term **has a normal form** when it reduces to one. -/
def HasNF (t : Term) : Prop := ∃ n, Red t n ∧ Normal n

/-- Reduction in the function part of an application. -/
theorem Red.appL {t t' u : Term} (h : Red t t') : Red (app t u) (app t' u) :=
  Star.map (fun t => app t u) (fun _ _ => Step.appL) h
/-- Reduction in the argument of an application. -/
theorem Red.appR {t u u' : Term} (h : Red u u') : Red (app t u) (app t u') :=
  Star.map (fun u => app t u) (fun _ _ => Step.appR) h
/-- Reduction under a binder. -/
theorem Red.lam {t t' : Term} (h : Red t t') : Red (lam t) (lam t') :=
  Star.map Term.lam (fun _ _ => Step.lam) h

/-! ## Parallel reduction (Tait–Martin-Löf) -/

/-- **Parallel reduction**: contract any set of redexes present in the term,
all at once. -/
inductive Par : Term → Term → Prop
  | var (n : Nat) : Par (var n) (var n)
  | app {t t' u u' : Term} : Par t t' → Par u u' → Par (app t u) (app t' u')
  | lam {t t' : Term} : Par t t' → Par (lam t) (lam t')
  | beta {t t' u u' : Term} : Par t t' → Par u u' → Par (app (lam t) u) (inst t' u')

/-- Parallel reduction is reflexive. -/
theorem Par.refl : ∀ t, Par t t
  | .var n => Par.var n
  | .app t u => Par.app (Par.refl t) (Par.refl u)
  | .lam t => Par.lam (Par.refl t)

/-- A β-step is a parallel step. -/
theorem Step.par {t u : Term} (h : Step t u) : Par t u := by
  induction h with
  | beta t u => exact Par.beta (Par.refl t) (Par.refl u)
  | appL _ ih => exact Par.app ih (Par.refl _)
  | appR _ ih => exact Par.app (Par.refl _) ih
  | lam _ ih => exact Par.lam ih

/-- A parallel step is a β-reduction sequence. -/
theorem Par.red {t u : Term} (h : Par t u) : Red t u := by
  induction h with
  | var n => exact Star.refl _
  | app _ _ iht ihu => exact (Red.appL iht).trans (Red.appR ihu)
  | lam _ ih => exact Red.lam ih
  | beta _ _ iht ihu =>
    exact ((Red.lam iht).appL.trans (Red.appR ihu)).trans (Star.single (Step.beta _ _))

/-- Parallel reduction is stable under renaming. -/
theorem Par.rename {t t' : Term} (h : Par t t') : ∀ ξ, Par (rename ξ t) (rename ξ t') := by
  induction h with
  | var n => intro ξ; exact Par.var _
  | app _ _ iht ihu => intro ξ; exact Par.app (iht ξ) (ihu ξ)
  | lam _ ih => intro ξ; exact Par.lam (ih _)
  | beta _ _ iht ihu =>
    intro ξ
    rw [rename_inst]
    exact Par.beta (iht _) (ihu ξ)

/-- **Substitution lemma for parallel reduction.** -/
theorem Par.subst {t t' : Term} (h : Par t t') :
    ∀ σ τ, (∀ n, Par (σ n) (τ n)) → Par (subst σ t) (subst τ t') := by
  have hup : ∀ σ τ : Nat → Term, (∀ n, Par (σ n) (τ n)) → ∀ n, Par (up σ n) (up τ n) := by
    intro σ τ hστ n
    cases n with
    | zero => exact Par.var 0
    | succ n => exact (hστ n).rename _
  induction h with
  | var n => intro σ τ h; exact h n
  | app _ _ iht ihu => intro σ τ h; exact Par.app (iht σ τ h) (ihu σ τ h)
  | lam _ ih => intro σ τ h; exact Par.lam (ih _ _ (hup σ τ h))
  | beta _ _ iht ihu =>
    intro σ τ h
    rw [subst_inst]
    exact Par.beta (iht _ _ (hup σ τ h)) (ihu σ τ h)

/-- Parallel reduction of a single substitution. -/
theorem Par.inst {t t' u u' : Term} (ht : Par t t') (hu : Par u u') :
    Par (Lambda.inst t u) (Lambda.inst t' u') :=
  ht.subst _ _ (fun n => by cases n with
    | zero => exact hu
    | succ n => exact Par.var n)

/-- The **complete development** of a term: contract all of its redexes at once. -/
def cd : Term → Term
  | var n => var n
  | lam t => lam (cd t)
  | app (lam t) u => Lambda.inst (cd t) (cd u)
  | app t u => app (cd t) (cd u)

/-- Inverting a parallel step from an abstraction. -/
theorem Par.lam_inv {t x : Term} (h : Par (Term.lam t) x) : ∃ t', x = Term.lam t' ∧ Par t t' := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

/-- **The triangle property** (Takahashi): every parallel step from `t` can be
completed, by another parallel step, to the complete development `cd t`. -/
theorem Par.triangle {t u : Term} (h : Par t u) : Par u (cd t) := by
  induction h with
  | var n => exact Par.var n
  | lam _ ih => exact Par.lam ih
  | @app t t' u u' ht _ iht ihu =>
    cases t with
    | lam s =>
      obtain ⟨s', rfl, _⟩ := ht.lam_inv
      cases iht with
      | lam hs => exact Par.beta hs ihu
    | var n => exact Par.app iht ihu
    | app a b => exact Par.app iht ihu
  | beta _ _ iht ihu => exact Par.inst iht ihu

/-- **Diamond property of parallel reduction.** -/
theorem Par.diamond {t u v : Term} (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w :=
  ⟨cd t, hu.triangle, hv.triangle⟩

/-- The strip lemma: one parallel step against many. -/
theorem Par.strip {t u v : Term} (hu : Par t u) (hv : Star Par t v) :
    ∃ w, Star Par u w ∧ Par v w := by
  induction hv with
  | refl => exact ⟨u, Star.refl u, hu⟩
  | tail _ hstep ih =>
    obtain ⟨w₀, hw₀, hv₀⟩ := ih
    obtain ⟨w, h₁, h₂⟩ := Par.diamond hv₀ hstep
    exact ⟨w, hw₀.tail h₁, h₂⟩

/-- Many parallel steps are confluent. -/
theorem Par.confluent {t u v : Term} (hu : Star Par t u) (hv : Star Par t v) :
    ∃ w, Star Par u w ∧ Star Par v w := by
  induction hu with
  | refl => exact ⟨v, hv, Star.refl v⟩
  | tail _ hstep ih =>
    obtain ⟨w₀, hu₀, hvw₀⟩ := ih
    obtain ⟨w, hw, hw₀⟩ := Par.strip hstep hu₀
    exact ⟨w, hw, hvw₀.tail hw₀⟩

/-- **The Church–Rosser theorem.** β-reduction is confluent: if `t ⟶* u` and
`t ⟶* v`, then `u` and `v` have a common reduct. -/
theorem church_rosser {t u v : Term} (hu : Red t u) (hv : Red t v) :
    ∃ w, Red u w ∧ Red v w := by
  have toPar : ∀ {a b}, Red a b → Star Par a b :=
    fun h => Star.flatten (fun _ _ h => Star.single h.par) h
  have ofPar : ∀ {a b}, Star Par a b → Red a b :=
    fun h => Star.flatten (fun _ _ h => h.red) h
  obtain ⟨w, h₁, h₂⟩ := Par.confluent (toPar hu) (toPar hv)
  exact ⟨w, ofPar h₁, ofPar h₂⟩

/-- A normal form has no non-trivial reducts. -/
theorem Normal.red_eq {n m : Term} (hn : Normal n) (h : Red n m) : m = n := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (hn _)

/-- **Uniqueness of normal forms.** A term has at most one normal form. -/
theorem nf_unique {t n m : Term} (hn : Red t n) (hm : Red t m) (hn' : Normal n)
    (hm' : Normal m) : n = m := by
  obtain ⟨w, h₁, h₂⟩ := church_rosser hn hm
  rw [← hn'.red_eq h₁, ← hm'.red_eq h₂]

/-! ## Church numerals -/

/-- `iterApp f a n = f (f (⋯ (f a)))` with `n` applications of `f`. -/
def iterApp (f a : Term) : Nat → Term
  | 0 => a
  | n + 1 => app f (iterApp f a n)

/-- The **Church numeral** `n̄ = λf. λx. fⁿ x`: the number `n` as the operation of
iterating a function `n` times. -/
def church (n : Nat) : Term := lam (lam (iterApp (var 1) (var 0) n))

/-- The **successor** `λn. λf. λx. f (n f x)`. -/
def csucc : Term := lam (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

/-- Substitution distributes over iterated application. -/
theorem subst_iterApp (σ : Nat → Term) (f a : Term) (n : Nat) :
    subst σ (iterApp f a n) = iterApp (subst σ f) (subst σ a) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterApp, subst, ih]

/-- Renaming distributes over iterated application. -/
theorem rename_iterApp (ξ : Nat → Nat) (f a : Term) (n : Nat) :
    rename ξ (iterApp f a n) = iterApp (rename ξ f) (rename ξ a) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterApp, rename, ih]

/-- Church numerals are closed: renaming leaves them unchanged. -/
theorem rename_church (ξ : Nat → Nat) (n : Nat) : rename ξ (church n) = church n := by
  simp only [church, rename, rename_iterApp]; rfl

/-- **The successor computes**: `csucc n̄ ⟶* (n+1)‾`. -/
theorem csucc_church (n : Nat) : Red (app csucc (church n)) (church (n + 1)) := by
  -- first β-step: substitute the numeral for the parameter
  have h₁ : Step (app csucc (church n))
      (lam (lam (app (var 1) (app (app (church n) (var 1)) (var 0))))) := by
    have := Step.beta (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0))))) (church n)
    simp only [inst, subst, up, cons, rename_church] at this
    exact this
  -- second β-step: feed `f`
  have h₂ : Step (app (church n) (var 1)) (lam (iterApp (var 2) (var 0) n)) := by
    have := Step.beta (lam (iterApp (var 1) (var 0) n)) (var 1)
    simp only [inst, subst, subst_iterApp, up, cons, rename] at this
    exact this
  -- third β-step: feed `x`
  have h₃ : Step (app (lam (iterApp (var 2) (var 0) n)) (var 0)) (iterApp (var 1) (var 0) n) := by
    have := Step.beta (iterApp (var 2) (var 0) n) (var 0)
    simp only [inst, subst_iterApp, subst, cons] at this
    exact this
  refine Star.head h₁ (Red.lam (Red.lam (Red.appR ?_)))
  exact (Star.single (Step.appL h₂)).tail h₃

/-- Church numerals are in normal form. -/
theorem church_normal (n : Nat) : Normal (church n) := by
  have hit : ∀ k t, ¬ Step (iterApp (var 1) (var 0) k) t := by
    intro k
    induction k with
    | zero => intro t h; cases h
    | succ k ih =>
      intro t h
      cases h with
      | appL h => cases h
      | appR h => exact ih _ h
  intro t h
  cases h with
  | lam h => cases h with
    | lam h => exact hit n _ h

/-- Distinct numbers give distinct numerals. -/
theorem church_injective : Function.Injective church := by
  have : ∀ m n, iterApp (var 1) (var 0) m = iterApp (var 1) (var 0) n → m = n := by
    intro m
    induction m with
    | zero => intro n h; cases n with
      | zero => rfl
      | succ n => simp [iterApp] at h
    | succ m ih => intro n h; cases n with
      | zero => simp [iterApp] at h
      | succ n => simp only [iterApp, app.injEq, true_and] at h; rw [ih n h]
  intro m n h
  simp only [church, lam.injEq] at h
  exact this m n h

/-! ## A term without normal form -/

/-- The self-application `ω = λx. x x`. -/
def omegaT : Term := lam (app (var 0) (var 0))

/-- `Ω = ω ω`, the simplest non-terminating program. -/
def Omega : Term := app omegaT omegaT

/-- `Ω` reduces in one step only to itself. -/
theorem Omega_step {t : Term} (h : Step Omega t) : t = Omega := by
  cases h with
  | beta => rfl
  | appL h => cases h with
    | lam h => cases h with
      | appL h => cases h
      | appR h => cases h
  | appR h => cases h with
    | lam h => cases h with
      | appL h => cases h
      | appR h => cases h

/-- **Ω has no normal form**: it reduces only to itself, and it is not normal. -/
theorem Omega_no_nf : ¬ HasNF Omega := by
  rintro ⟨n, hred, hn⟩
  have : ∀ t, Red Omega t → t = Omega := by
    intro t h
    induction h with
    | refl => rfl
    | tail _ hs ih => subst ih; exact Omega_step hs
  rw [this n hred] at hn
  exact hn _ (Step.beta _ _)

end Lambda

end Foundations.Types
