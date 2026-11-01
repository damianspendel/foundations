import Foundations.Logic.FOSoundness

/-!
# Peano arithmetic as a first-order theory, and its consistency relative to Lean

Dedekind (*Was sind und was sollen die Zahlen?*, 1888) and Peano (1889)
characterised the natural numbers by a few axioms about zero, successor and
induction. Read inside first-order logic — with addition and multiplication given
by their recursion equations, and induction as an infinite *schema*, one axiom for
each formula — these become **Peano Arithmetic (PA)**, the standard first-order
theory of arithmetic and the setting of Gödel's incompleteness theorems (1931).

Here we
1. define the signature `{0, S, +, ×}` of arithmetic,
2. state the axioms of PA in our de Bruijn syntax,
3. define the **standard model** `ℕ` (Lean's natural numbers; the Numbers part of
   this project proves them isomorphic to a from-scratch Peano construction), and
4. prove that `ℕ` satisfies every axiom of PA, including every instance of the
   induction schema.

By the soundness theorem, PA therefore **cannot derive a contradiction**. This is a
*relative* consistency proof: it shows PA is consistent provided Lean's own logic
is. Hilbert hoped for a "finitary" consistency proof of arithmetic; Gödel's second
incompleteness theorem shows PA cannot prove its own consistency, and Gentzen (1936)
gave a proof using transfinite induction up to the ordinal ε₀. Our proof uses the
(much stronger) set-theoretic strength of Lean's type theory instead.
-/

namespace Foundations.Logic.FO

/-- The function symbols of arithmetic, indexed by arity: the constant `0`, the unary
successor `S`, and binary `+` and `×`. -/
inductive ArithFunc : Nat → Type where
  /-- The constant zero. -/
  | zero : ArithFunc 0
  /-- The successor function. -/
  | succ : ArithFunc 1
  /-- Addition. -/
  | add : ArithFunc 2
  /-- Multiplication. -/
  | mul : ArithFunc 2

/-- **The language of arithmetic**: function symbols `0, S, +, ×` and no relation
symbols besides the logical equality. -/
def Arith : Signature where
  Func := ArithFunc
  Rel := fun _ => Empty

namespace Arith

/-- Package two terms as the argument tuple of a binary function symbol. -/
def args₂ (t s : Term Arith) : Fin 2 → Term Arith := fun i => if i.val = 0 then t else s

/-- The term `0`. -/
def zero : Term Arith := .func (L := Arith) ArithFunc.zero Fin.elim0

/-- The term `S t`. -/
def succ (t : Term Arith) : Term Arith := .func (L := Arith) ArithFunc.succ fun _ => t

/-- The term `t + s`. -/
def add (t s : Term Arith) : Term Arith := .func (L := Arith) ArithFunc.add (args₂ t s)

/-- The term `t × s`. -/
def mul (t s : Term Arith) : Term Arith := .func (L := Arith) ArithFunc.mul (args₂ t s)

/-- Shorthand for the variable with de Bruijn index `n`. -/
abbrev v (n : Nat) : Term Arith := .var n

/-- The substitution used in the induction step: the bound variable `x` (index `0`)
is replaced by `S x`, all other variables are left alone. -/
def succSubst : Nat → Term Arith
  | 0 => succ (v 0)
  | n + 1 => v (n + 1)

end Arith

open Arith Formula

/-- **The axioms of Peano Arithmetic.** Six closed axioms for successor, addition and
multiplication, plus the induction schema
`φ(0) ∧ ∀x (φ(x) → φ(Sx)) → ∀x φ(x)` for *every* formula `φ` (whose other free
variables act as parameters). -/
inductive PA : Theory Arith where
  /-- `∀x. S x ≠ 0`: zero is not a successor. -/
  | succ_ne_zero : PA (all (neg (eq (succ (v 0)) zero)))
  /-- `∀x ∀y. S x = S y → x = y`: successor is injective. -/
  | succ_inj : PA (all (all (imp (eq (succ (v 1)) (succ (v 0))) (eq (v 1) (v 0)))))
  /-- `∀x. x + 0 = x`. -/
  | add_zero : PA (all (eq (add (v 0) zero) (v 0)))
  /-- `∀x ∀y. x + S y = S (x + y)`. -/
  | add_succ : PA (all (all (eq (add (v 1) (succ (v 0))) (succ (add (v 1) (v 0))))))
  /-- `∀x. x × 0 = 0`. -/
  | mul_zero : PA (all (eq (mul (v 0) zero) zero))
  /-- `∀x ∀y. x × S y = x × y + x`. -/
  | mul_succ : PA (all (all (eq (mul (v 1) (succ (v 0))) (add (mul (v 1) (v 0)) (v 1)))))
  /-- The induction schema, one axiom for each formula `φ`. -/
  | induction (φ : Formula Arith) :
      PA (imp (conj (φ.inst zero) (all (imp φ (φ.subst succSubst)))) (all φ))

/-- **The standard model of arithmetic**: the natural numbers with their usual zero,
successor, addition and multiplication. -/
abbrev stdModel : Structure Arith where
  Dom := Nat
  funcs := fun {n} f a =>
    match n, f with
    | _, ArithFunc.zero => 0
    | _, ArithFunc.succ => a 0 + 1
    | _, ArithFunc.add => a 0 + a 1
    | _, ArithFunc.mul => a 0 * a 1
  rels := fun R _ => nomatch R

namespace Arith

variable (e : Nat → Nat)

/-- `0` denotes zero in the standard model. -/
@[simp] theorem eval_zero : zero.eval stdModel e = (0 : Nat) := rfl

/-- `S t` denotes the successor of the value of `t`. -/
@[simp] theorem eval_succ (t : Term Arith) :
    (succ t).eval stdModel e = (t.eval stdModel e : Nat) + 1 := rfl

/-- `t + s` denotes the sum of the values. -/
@[simp] theorem eval_add (t s : Term Arith) :
    (add t s).eval stdModel e = (t.eval stdModel e : Nat) + s.eval stdModel e := rfl

/-- `t × s` denotes the product of the values. -/
@[simp] theorem eval_mul (t s : Term Arith) :
    (mul t s).eval stdModel e = (t.eval stdModel e : Nat) * s.eval stdModel e := rfl

end Arith

/-- **The standard model satisfies PA.** Every axiom of Peano arithmetic — including
every instance of the induction schema — is true in `(ℕ, 0, S, +, ×)` under every
assignment of the free variables. -/
theorem stdModel_isModel : IsModel stdModel PA := by
  refine ⟨⟨(0 : Nat)⟩, ?_⟩
  intro φ hφ e
  cases hφ with
  | succ_ne_zero => intro (x : Nat) (h : x + 1 = 0); exact Nat.succ_ne_zero x h
  | succ_inj => intro (x : Nat) (y : Nat) (h : x + 1 = y + 1); exact Nat.succ.inj h
  | add_zero => intro (x : Nat); show x + 0 = x; rfl
  | add_succ => intro (x : Nat) (y : Nat); show x + (y + 1) = x + y + 1; rfl
  | mul_zero => intro (x : Nat); show x * 0 = 0; rfl
  | mul_succ => intro (x : Nat) (y : Nat); show x * (y + 1) = x * y + x; exact Nat.mul_succ x y
  | induction φ =>
      rintro ⟨h0, hstep⟩ n
      have h0' : Sat stdModel (Env.cons (0 : Nat) e) φ := (sat_inst φ e zero).1 h0
      have hstep' : ∀ x : Nat, Sat stdModel (Env.cons x e) φ →
          Sat stdModel (Env.cons (x + 1) e) φ := by
        intro x hx
        have := (sat_subst φ (Env.cons x e) succSubst).1 (hstep x hx)
        have henv : (fun n => (succSubst n).eval stdModel (Env.cons x e)) =
            Env.cons (x + 1) e := by
          funext n; cases n <;> rfl
        rwa [henv] at this
      induction n with
      | zero => exact h0'
      | succ n ih => exact hstep' n ih

/-- **Consistency of Peano Arithmetic (relative to Lean).** PA does not derive `⊥`:
by soundness, a derivation of `⊥` would have to be true in the standard model. -/
theorem PA_consistent : ¬ (PA ⊢₁ bot) :=
  Proves.consistent_of_model stdModel (fun _ => (0 : Nat)) stdModel_isModel

/-- **Every theorem of PA is true in ℕ.** If PA derives `φ`, then `φ` holds in the
standard model under every assignment. -/
theorem PA_sound {φ : Formula Arith} (h : PA ⊢₁ φ) (e : Nat → Nat) : Sat stdModel e φ :=
  Proves.soundness h stdModel e (fun ψ hψ => stdModel_isModel.2 ψ hψ e)

/-- `0` is unchanged by any substitution (it has no variables). -/
theorem Arith.zero_subst (σ : Nat → Term Arith) : zero.subst σ = zero := by
  simp only [zero, Term.subst]; congr; funext i; exact i.elim0

/-- Example derivation in PA: `⊢ 0 + 0 = 0`, by instantiating the axiom
`∀x. x + 0 = x` at `x := 0`. -/
theorem PA_proves_zero_add_zero : PA ⊢₁ eq (add zero zero) zero := by
  have h := Proves.allE zero (Proves.hyp PA.add_zero)
  have e : (eq (add (v 0) zero) (v 0)).inst zero = eq (add zero zero) zero := by
    simp only [Formula.inst, Formula.subst, add, Term.subst]
    congr 2
    funext i
    simp only [args₂]
    split <;> simp [Term.subst, Subst.single, zero_subst]
  rwa [e] at h

end Foundations.Logic.FO
