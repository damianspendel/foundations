import Foundations.Types.SystemFSubst

/-!
# Impredicativity at work: Church encodings in System F

In System F the data types of programming need not be added: they can be
*defined*, by the same trick Church used in the untyped calculus, now with
types. The idea (due to Böhm–Berarducci and Girard) is that a data type *is* its
own iteration principle:

* `Bool := ∀α. α → α → α` — a boolean is a way of choosing between two
  alternatives of any type; `true := Λα. λx. λy. x`, `false := Λα. λx. λy. y`.
* `Nat := ∀α. (α → α) → α → α` — a natural number `n` is the operation of
  iterating any function `n` times: `n̄ := Λα. λf. λx. fⁿ x`.
* `A × B := ∀α. (A → B → α) → α` — a pair is something that can feed its two
  components to any two-argument consumer.

The quantifier `∀α` ranges over *all* types, including `Nat` itself. That is
what makes these definitions work — `n̄ [Nat]` iterates a function on numbers,
which is how addition and multiplication are defined — and also what makes them
philosophically striking: the type `Nat` is defined by quantifying over a
totality to which it belongs. Poincaré and Russell regarded such *impredicative*
definitions as viciously circular; Ramsey and Gödel defended them on the ground
that they merely single out an object that already exists. Girard's
normalization theorem (`SystemFNormalization.lean`) shows that, at least, they
cannot lead to non-terminating computation or to a proof of falsity.

We give the encodings with their typing derivations, and check that they
compute: the successor of `n̄` reduces to the numeral of `n + 1`, iteration
unfolds to `fⁿ x`, the conditional selects the right branch, and projections
recover the components of a pair.
-/

namespace Foundations.Types

namespace SystemF

open Term

/-! ## Reduction sequences -/

/-- Many-step reduction in System F. -/
abbrev Red : Term → Term → Prop := Star Step

/-- Reduction in the function part. -/
theorem Red.appL {t t' u : Term} (h : Red t t') : Red (app t u) (app t' u) :=
  Star.map (fun t => app t u) (fun _ _ => Step.appL) h
/-- Reduction in the argument. -/
theorem Red.appR {t u u' : Term} (h : Red u u') : Red (app t u) (app t u') :=
  Star.map (fun u => app t u) (fun _ _ => Step.appR) h
/-- Reduction under a `λ`. -/
theorem Red.lam {t t' : Term} (h : Red t t') : Red (lam t) (lam t') :=
  Star.map Term.lam (fun _ _ => Step.lam) h
/-- Reduction under a `Λ`. -/
theorem Red.tlam {t t' : Term} (h : Red t t') : Red (tlam t) (tlam t') :=
  Star.map Term.tlam (fun _ _ => Step.tlam) h

/-- Instantiating a shifted type gives it back. -/
theorem Ty.subst_cons_shift (B X : Ty) : Ty.subst (Ty.cons B Ty.tvar) (Ty.shift X) = X :=
  congrFun (Ty.inst_shift B) X

/-- A substitution `cons b var` after a shift gives back the term. -/
theorem subst_cons_rename_succ (b s : Term) : subst (cons b var) (rename Nat.succ s) = s := by
  rw [subst_rename]; exact subst_var s

/-- Type application with the instantiated type given explicitly (convenient when
`A[B]` should be computed). -/
theorem HasType.tapp' {Γ : List Ty} {t : Term} {A B C : Ty} (h : HasType Γ t (.all A))
    (he : A.inst B = C) : HasType Γ (Term.tapp t B) C := he ▸ HasType.tapp h

/-! ## Types -/

/-- `Bool := ∀α. α → α → α`. -/
def boolT : Ty := .all (.arr (.tvar 0) (.arr (.tvar 0) (.tvar 0)))

/-- `Nat := ∀α. (α → α) → α → α`. -/
def natT : Ty := .all (.arr (.arr (.tvar 0) (.tvar 0)) (.arr (.tvar 0) (.tvar 0)))

/-- `A × B := ∀α. (A → B → α) → α`. -/
def prodT (A B : Ty) : Ty := .all (.arr (.arr (Ty.shift A) (.arr (Ty.shift B) (.tvar 0))) (.tvar 0))

/-! ## Booleans -/

/-- `true := Λα. λx. λy. x`. -/
def tru : Term := tlam (lam (lam (var 1)))
/-- `false := Λα. λx. λy. y`. -/
def fls : Term := tlam (lam (lam (var 0)))
/-- The conditional at type `A`: `λb. λx. λy. b [A] x y`. -/
def cond (A : Ty) : Term := lam (lam (lam (app (app (tapp (var 2) A) (var 1)) (var 0))))

/-- `true : Bool`. -/
theorem tru_typed : HasType [] tru boolT := .tlam (.lam (.lam (.var rfl)))
/-- `false : Bool`. -/
theorem fls_typed : HasType [] fls boolT := .tlam (.lam (.lam (.var rfl)))
/-- `cond A : Bool → A → A → A`. -/
theorem cond_typed (A : Ty) : HasType [] (cond A) (.arr boolT (.arr A (.arr A A))) :=
  .lam (.lam (.lam (.app (.app (.tapp' (.var rfl) rfl) (.var rfl)) (.var rfl))))

/-- **The conditional computes**: `true [A] a b ⟶* a`. -/
theorem tru_red (A : Ty) (a b : Term) : Red (app (app (tapp tru A) a) b) a := by
  have h₁ : Step (tapp tru A) (lam (lam (var 1))) := Step.tbeta _ _
  have h₂ : Step (app (lam (lam (var 1))) a) (lam (rename Nat.succ a)) := by
    have := Step.beta (lam (var 1)) a
    simpa [inst, subst, up, cons] using this
  have h₃ : Step (app (lam (rename Nat.succ a)) b) a := by
    have := Step.beta (rename Nat.succ a) b
    rwa [inst, subst_cons_rename_succ] at this
  exact ((Star.single (Step.appL (Step.appL h₁))).tail (Step.appL h₂)).tail h₃

/-- **The conditional computes**: `false [A] a b ⟶* b`. -/
theorem fls_red (A : Ty) (a b : Term) : Red (app (app (tapp fls A) a) b) b := by
  have h₁ : Step (tapp fls A) (lam (lam (var 0))) := Step.tbeta _ _
  have h₂ : Step (app (lam (lam (var 0))) a) (lam (var 0)) := Step.beta _ _
  have h₃ : Step (app (lam (var 0)) b) b := Step.beta _ _
  exact ((Star.single (Step.appL (Step.appL h₁))).tail (Step.appL h₂)).tail h₃

/-! ## Natural numbers -/

/-- `iterApp f a n = f (f (⋯ (f a)))` with `n` applications. -/
def iterApp (f a : Term) : Nat → Term
  | 0 => a
  | n + 1 => app f (iterApp f a n)

/-- The **Church numeral** `n̄ := Λα. λf. λx. fⁿ x`. -/
def num (n : Nat) : Term := tlam (lam (lam (iterApp (var 1) (var 0) n)))

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

/-- Type renaming distributes over iterated application. -/
theorem tyRename_iterApp (ξ : Nat → Nat) (f a : Term) (n : Nat) :
    tyRename ξ (iterApp f a n) = iterApp (tyRename ξ f) (tyRename ξ a) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterApp, tyRename, ih]

/-- Type substitution distributes over iterated application. -/
theorem tySubst_iterApp (τ : Nat → Ty) (f a : Term) (n : Nat) :
    tySubst τ (iterApp f a n) = iterApp (tySubst τ f) (tySubst τ a) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterApp, tySubst, ih]

/-- Numerals are closed: renaming leaves them unchanged. -/
theorem rename_num (ξ : Nat → Nat) (n : Nat) : rename ξ (num n) = num n := by
  simp only [num, rename, rename_iterApp]; rfl

/-- Numerals are closed: substitution leaves them unchanged. -/
theorem subst_num (σ : Nat → Term) (n : Nat) : subst σ (num n) = num n := by
  simp only [num, subst, subst_iterApp]; rfl

/-- Numerals contain no type variables. -/
theorem tyRename_num (ξ : Nat → Nat) (n : Nat) : tyRename ξ (num n) = num n := by
  simp only [num, tyRename, tyRename_iterApp]

/-- Typing of iterated application. -/
theorem iterApp_typed {Γ : List Ty} {f a : Term} {A : Ty} (hf : HasType Γ f (.arr A A))
    (ha : HasType Γ a A) (n : Nat) : HasType Γ (iterApp f a n) A := by
  induction n with
  | zero => exact ha
  | succ n ih => exact .app hf ih

/-- **Every numeral has type `Nat`.** -/
theorem num_typed (n : Nat) : HasType [] (num n) natT :=
  .tlam (.lam (.lam (iterApp_typed (.var rfl) (.var rfl) n)))

/-- The **successor** `λn. Λα. λf. λx. f (n [α] f x)`. -/
def succT : Term :=
  lam (tlam (lam (lam (app (var 1) (app (app (tapp (var 2) (.tvar 0)) (var 1)) (var 0))))))

/-- `succ : Nat → Nat`. -/
theorem succT_typed : HasType [] succT (.arr natT natT) :=
  .lam (.tlam (.lam (.lam (.app (.var rfl) (.app (.app (.tapp' (.var rfl) rfl) (.var rfl)) (.var rfl))))))

/-- **Addition** `λm. λn. Λα. λf. λx. m [α] f (n [α] f x)`. -/
def addT : Term :=
  lam (lam (tlam (lam (lam (app (app (tapp (var 3) (.tvar 0)) (var 1))
    (app (app (tapp (var 2) (.tvar 0)) (var 1)) (var 0)))))))

/-- `add : Nat → Nat → Nat`. -/
theorem addT_typed : HasType [] addT (.arr natT (.arr natT natT)) :=
  .lam (.lam (.tlam (.lam (.lam (.app (.app (.tapp' (.var rfl) rfl) (.var rfl))
    (.app (.app (.tapp' (.var rfl) rfl) (.var rfl)) (.var rfl)))))))

/-- **Iteration** at type `A`: `λn. λf. λx. n [A] f x : Nat → (A → A) → A → A`. -/
def iterT (A : Ty) : Term := lam (lam (lam (app (app (tapp (var 2) A) (var 1)) (var 0))))

/-- `iter A : Nat → (A → A) → A → A`. -/
theorem iterT_typed (A : Ty) : HasType [] (iterT A) (.arr natT (.arr (.arr A A) (.arr A A))) :=
  .lam (.lam (.lam (.app (.app (.tapp' (.var rfl) rfl) (.var rfl)) (.var rfl))))

/-- Instantiating a numeral and feeding it `f` and `x`: `n̄ [A] f x ⟶* fⁿ x`. -/
theorem num_apply (n : Nat) (A : Ty) (f x : Term) :
    Red (app (app (tapp (num n) A) f) x) (iterApp f x n) := by
  have h₁ : Step (tapp (num n) A) (lam (lam (iterApp (var 1) (var 0) n))) := by
    have := Step.tbeta (lam (lam (iterApp (var 1) (var 0) n))) A
    unfold num
    simpa [tyInst, tySubst, tySubst_iterApp] using this
  have h₂ : Step (app (lam (lam (iterApp (var 1) (var 0) n))) f)
      (lam (iterApp (rename Nat.succ f) (var 0) n)) := by
    have := Step.beta (lam (iterApp (var 1) (var 0) n)) f
    simpa [inst, subst, subst_iterApp, up, cons] using this
  have h₃ : Step (app (lam (iterApp (rename Nat.succ f) (var 0) n)) x) (iterApp f x n) := by
    have := Step.beta (iterApp (rename Nat.succ f) (var 0) n) x
    simpa [inst, subst_iterApp, subst, cons, subst_cons_rename_succ] using this
  exact ((Star.single (Step.appL (Step.appL h₁))).tail (Step.appL h₂)).tail h₃

/-- **Iteration computes**: `iter A n̄ f x ⟶* fⁿ x`. -/
theorem iterT_red (A : Ty) (n : Nat) (f x : Term) :
    Red (app (app (app (iterT A) (num n)) f) x) (iterApp f x n) := by
  have h₁ : Step (app (iterT A) (num n))
      (lam (lam (app (app (tapp (num n) A) (var 1)) (var 0)))) := by
    have := Step.beta (lam (lam (app (app (tapp (var 2) A) (var 1)) (var 0)))) (num n)
    unfold iterT
    simpa [inst, subst, up, cons, rename, rename_num] using this
  have h₂ : Step (app (lam (lam (app (app (tapp (num n) A) (var 1)) (var 0)))) f)
      (lam (app (app (tapp (num n) A) (rename Nat.succ f)) (var 0))) := by
    have := Step.beta (lam (app (app (tapp (num n) A) (var 1)) (var 0))) f
    simpa [inst, subst, up, cons, rename, subst_num] using this
  have h₃ : Step (app (lam (app (app (tapp (num n) A) (rename Nat.succ f)) (var 0))) x)
      (app (app (tapp (num n) A) f) x) := by
    have := Step.beta (app (app (tapp (num n) A) (rename Nat.succ f)) (var 0)) x
    simp only [inst, subst, cons, subst_cons_rename_succ] at this
    rwa [subst_num] at this
  exact (((Star.single (Step.appL (Step.appL h₁))).tail (Step.appL h₂)).tail h₃).trans
    (num_apply n A f x)

/-- **The successor computes**: `succ n̄ ⟶* (n+1)‾`. -/
theorem succT_red (n : Nat) : Red (app succT (num n)) (num (n + 1)) := by
  have h₁ : Step (app succT (num n))
      (tlam (lam (lam (app (var 1) (app (app (tapp (num n) (.tvar 0)) (var 1)) (var 0)))))) := by
    have := Step.beta (tlam (lam (lam (app (var 1) (app (app (tapp (var 2) (.tvar 0)) (var 1))
      (var 0)))))) (num n)
    unfold succT
    simpa [inst, subst, up, cons, rename, tyRename, rename_num, tyRename_num] using this
  refine Star.head h₁ (Red.tlam (Red.lam (Red.lam (Red.appR ?_))))
  exact num_apply n (.tvar 0) (var 1) (var 0)

/-! ## Pairs -/

/-- The pair value `⟨a, b⟩ := Λα. λk. k a b` (with `a`, `b` shifted past the binders). -/
def pairV (a b : Term) : Term :=
  tlam (lam (app (app (var 0) (rename Nat.succ (tyRename Nat.succ a)))
    (rename Nat.succ (tyRename Nat.succ b))))

/-- Pairing as a function: `λx. λy. Λα. λk. k x y : A → B → A × B`. -/
def pairT : Term := lam (lam (tlam (lam (app (app (var 0) (var 2)) (var 1)))))

/-- `pair : A → B → A × B`. -/
theorem pairT_typed (A B : Ty) : HasType [] pairT (.arr A (.arr B (prodT A B))) :=
  .lam (.lam (.tlam (.lam (.app (.app (.var rfl) (.var rfl)) (.var rfl)))))

/-- First projection at types `A`, `B`: `λp. p [A] (λx. λy. x)`. -/
def fstT (A : Ty) : Term := lam (app (tapp (var 0) A) (lam (lam (var 1))))

/-- Second projection at types `A`, `B`: `λp. p [B] (λx. λy. y)`. -/
def sndT (B : Ty) : Term := lam (app (tapp (var 0) B) (lam (lam (var 0))))

/-- `fst : A × B → A`. -/
theorem fstT_typed (A B : Ty) : HasType [] (fstT A) (.arr (prodT A B) A) := by
  have hk : HasType [prodT A B] (lam (lam (var 1))) (.arr A (.arr B A)) := .lam (.lam (.var rfl))
  have hp : HasType [prodT A B] (tapp (var 0) A) (.arr (.arr A (.arr B A)) A) := by
    refine HasType.tapp' (A := .arr (.arr (Ty.shift A) (.arr (Ty.shift B) (.tvar 0))) (.tvar 0))
      (.var rfl) ?_
    simp [Ty.inst, Ty.subst, Ty.cons, Ty.subst_cons_shift]
  exact .lam (.app hp hk)

/-- `snd : A × B → B`. -/
theorem sndT_typed (A B : Ty) : HasType [] (sndT B) (.arr (prodT A B) B) := by
  have hk : HasType [prodT A B] (lam (lam (var 0))) (.arr A (.arr B B)) := .lam (.lam (.var rfl))
  have hp : HasType [prodT A B] (tapp (var 0) B) (.arr (.arr A (.arr B B)) B) := by
    refine HasType.tapp' (A := .arr (.arr (Ty.shift A) (.arr (Ty.shift B) (.tvar 0))) (.tvar 0))
      (.var rfl) ?_
    simp [Ty.inst, Ty.subst, Ty.cons, Ty.subst_cons_shift]
  exact .lam (.app hp hk)

/-- Instantiating a pair value and feeding it a consumer `k`. -/
theorem pairV_apply (a b k : Term) (C : Ty) : Red (app (tapp (pairV a b) C) k) (app (app k a) b) := by
  have h₁ : Step (tapp (pairV a b) C)
      (lam (app (app (var 0) (rename Nat.succ a)) (rename Nat.succ b))) := by
    have := Step.tbeta (lam (app (app (var 0) (rename Nat.succ (tyRename Nat.succ a)))
      (rename Nat.succ (tyRename Nat.succ b)))) C
    unfold pairV
    simpa [tyInst, tySubst, ← rename_tySubst, tySubst_cons_tyRename_succ] using this
  have h₂ : Step (app (lam (app (app (var 0) (rename Nat.succ a)) (rename Nat.succ b))) k)
      (app (app k a) b) := by
    have := Step.beta (app (app (var 0) (rename Nat.succ a)) (rename Nat.succ b)) k
    simpa [inst, subst, cons, subst_cons_rename_succ] using this
  exact (Star.single (Step.appL h₁)).tail h₂

/-- **Projections compute**: `fst ⟨a, b⟩ ⟶* a`. -/
theorem fstT_red (A : Ty) (a b : Term) : Red (app (fstT A) (pairV a b)) a := by
  have h₁ : Step (app (fstT A) (pairV a b)) (app (tapp (pairV a b) A) (lam (lam (var 1)))) :=
    Step.beta _ _
  refine (Star.head h₁ (pairV_apply a b _ A)).trans ?_
  have h₂ : Step (app (lam (lam (var 1))) a) (lam (rename Nat.succ a)) := by
    have := Step.beta (lam (var 1)) a
    simpa [inst, subst, up, cons] using this
  have h₃ : Step (app (lam (rename Nat.succ a)) b) a := by
    have := Step.beta (rename Nat.succ a) b
    rwa [inst, subst_cons_rename_succ] at this
  exact (Star.single (Step.appL h₂)).tail h₃

/-- **Projections compute**: `snd ⟨a, b⟩ ⟶* b`. -/
theorem sndT_red (B : Ty) (a b : Term) : Red (app (sndT B) (pairV a b)) b := by
  have h₁ : Step (app (sndT B) (pairV a b)) (app (tapp (pairV a b) B) (lam (lam (var 0)))) :=
    Step.beta _ _
  refine (Star.head h₁ (pairV_apply a b _ B)).trans ?_
  have h₂ : Step (app (lam (lam (var 0))) a) (lam (var 0)) := Step.beta _ _
  have h₃ : Step (app (lam (var 0)) b) b := Step.beta _ _
  exact (Star.single (Step.appL h₂)).tail h₃

end SystemF

end Foundations.Types
