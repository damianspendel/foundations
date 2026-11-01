import Foundations.Logic.FOSyntax

/-!
# First-order logic: structures, satisfaction, and the substitution lemma

The semantics of first-order logic is Tarski's (*The Concept of Truth in Formalized
Languages*, 1933; model theory proper, with Vaught, 1957). A **structure** for a
signature consists of a non-empty domain of individuals together with an
interpretation of every function symbol as a function and every relation symbol as
a relation on the domain. A formula is then true or false in a structure *relative
to an environment* `e : ℕ → domain` assigning individuals to the free variables.

Tarski's key insight was that truth for complex formulas must be defined via
*satisfaction* of open formulas by assignments: `∀x φ` is satisfied by `e` if `φ`
is satisfied by every modification of `e` at `x`. With de Bruijn indices this
modification is simply *pushing* a new value onto the front of the environment
(`Env.cons x e`), because the bound variable has index `0` and all others move up.

The central technical result is the **substitution lemma**: substituting terms
syntactically has the same effect as evaluating those terms and updating the
environment semantically,
`M, e ⊨ φ[σ]  ↔  M, (n ↦ ⟦σ n⟧ₑ) ⊨ φ`.
It is the precise sense in which our capture-avoiding substitution is *correct*,
and it is exactly what the soundness of the quantifier rules needs.
-/

namespace Foundations.Logic.FO

variable {L : Signature}

/-- **First-order structure** for a signature `L`: a domain together with
interpretations of the function and relation symbols. (Non-emptiness of the domain
is implicit: we always evaluate under an environment, which supplies elements.) -/
structure Structure (L : Signature) where
  /-- The domain of individuals. -/
  Dom : Type
  /-- Interpretation of each `n`-ary function symbol as an `n`-ary function. -/
  funcs : {n : Nat} → L.Func n → (Fin n → Dom) → Dom
  /-- Interpretation of each `n`-ary relation symbol as an `n`-ary relation. -/
  rels : {n : Nat} → L.Rel n → (Fin n → Dom) → Prop

/-- Push a new value `x` onto an environment: `x` becomes the value of index `0`,
and the old value of index `n` becomes the value of `n + 1`. -/
def Env.cons {α : Type} (x : α) (e : Nat → α) : Nat → α
  | 0 => x
  | n + 1 => e n

variable (M : Structure L)

namespace Term

/-- The value of a term in a structure under an environment. -/
def eval (e : Nat → M.Dom) : Term L → M.Dom
  | var n => e n
  | func f ts => M.funcs f fun i => eval e (ts i)

variable {M}

/-- Evaluating a renamed term is evaluating the original term in the re-indexed
environment. -/
theorem eval_rename (e : Nat → M.Dom) (ρ : Nat → Nat) :
    ∀ t : Term L, (t.rename ρ).eval M e = t.eval M (fun n => e (ρ n))
  | var _ => rfl
  | func f ts => by simp only [rename, eval]; congr; funext i; exact eval_rename e ρ (ts i)

/-- **Substitution lemma for terms.** Evaluating `t[σ]` under `e` equals evaluating `t`
under the environment `n ↦ ⟦σ n⟧ₑ`. -/
theorem eval_subst (e : Nat → M.Dom) (σ : Nat → Term L) :
    ∀ t : Term L, (t.subst σ).eval M e = t.eval M (fun n => (σ n).eval M e)
  | var _ => rfl
  | func f ts => by simp only [subst, eval]; congr; funext i; exact eval_subst e σ (ts i)

end Term

namespace Formula

/-- **Tarski's satisfaction relation.** `Sat M e φ` holds when the structure `M`
satisfies `φ` under the environment `e`. -/
def Sat : (Nat → M.Dom) → Formula L → Prop
  | _, bot => False
  | e, eq t s => t.eval M e = s.eval M e
  | e, rel R ts => M.rels R fun i => (ts i).eval M e
  | e, imp φ ψ => Sat e φ → Sat e ψ
  | e, conj φ ψ => Sat e φ ∧ Sat e ψ
  | e, disj φ ψ => Sat e φ ∨ Sat e ψ
  | e, all φ => ∀ x : M.Dom, Sat (Env.cons x e) φ
  | e, ex φ => ∃ x : M.Dom, Sat (Env.cons x e) φ

variable {M}

/-- Evaluating under a lifted substitution after pushing `x` is the same as pushing
`x` onto the evaluated substitution. -/
theorem lift_eval (e : Nat → M.Dom) (σ : Nat → Term L) (x : M.Dom) :
    (fun n => (Subst.lift σ n).eval M (Env.cons x e)) =
      Env.cons x (fun n => (σ n).eval M e) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Subst.lift, Term.eval_rename]; rfl

/-- **Substitution lemma.** `M, e ⊨ φ[σ]` iff `M, (n ↦ ⟦σ n⟧ₑ) ⊨ φ`: syntactic
substitution corresponds exactly to semantic re-assignment of variables. -/
theorem sat_subst : ∀ (φ : Formula L) (e : Nat → M.Dom) (σ : Nat → Term L),
    Sat M e (φ.subst σ) ↔ Sat M (fun n => (σ n).eval M e) φ
  | bot, _, _ => Iff.rfl
  | eq t s, e, σ => by simp only [subst, Sat, Term.eval_subst]
  | rel R ts, e, σ => by simp only [subst, Sat, Term.eval_subst]
  | imp φ ψ, e, σ => by simp only [subst, Sat, sat_subst φ, sat_subst ψ]
  | conj φ ψ, e, σ => by simp only [subst, Sat, sat_subst φ, sat_subst ψ]
  | disj φ ψ, e, σ => by simp only [subst, Sat, sat_subst φ, sat_subst ψ]
  | all φ, e, σ => by simp only [subst, Sat, sat_subst φ, lift_eval]
  | ex φ, e, σ => by simp only [subst, Sat, sat_subst φ, lift_eval]

/-- Shifting a formula and pushing a value onto the environment cancel out:
`M, x·e ⊨ φ↑` iff `M, e ⊨ φ`. -/
theorem sat_shift (φ : Formula L) (e : Nat → M.Dom) (x : M.Dom) :
    Sat M (Env.cons x e) φ.shift ↔ Sat M e φ := by
  simp only [shift, sat_subst]; rfl

/-- Instantiating the bound variable by `t` is satisfied under `e` iff the body is
satisfied when the bound variable is given the value of `t`. -/
theorem sat_inst (φ : Formula L) (e : Nat → M.Dom) (t : Term L) :
    Sat M e (φ.inst t) ↔ Sat M (Env.cons (t.eval M e) e) φ := by
  simp only [inst, sat_subst]
  have : (fun n => (Subst.single t n).eval M e) = Env.cons (t.eval M e) e := by
    funext n; cases n <;> rfl
  rw [this]

/-- Negation is satisfied exactly when the formula is not. -/
theorem sat_neg (φ : Formula L) (e : Nat → M.Dom) : Sat M e φ.neg ↔ ¬ Sat M e φ := Iff.rfl

end Formula

/-- A structure `M` is a *model* of a theory `Γ` if it satisfies every formula of `Γ`
under every environment (free variables are read universally). -/
def IsModel (M : Structure L) (Γ : Theory L) : Prop :=
  ∀ φ, Γ φ → ∀ e : Nat → M.Dom, Formula.Sat M e φ

/-- **First-order semantic consequence** `Γ ⊨ φ`: in every structure, every
environment satisfying all formulas of `Γ` also satisfies `φ`. -/
def Entails (Γ : Theory L) (φ : Formula L) : Prop :=
  ∀ (M : Structure L) (e : Nat → M.Dom), (∀ ψ, Γ ψ → Formula.Sat M e ψ) → Formula.Sat M e φ

end Foundations.Logic.FO
