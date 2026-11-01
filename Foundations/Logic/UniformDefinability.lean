import Foundations.Logic.PASequences
import Foundations.Logic.PACompleteness

/-!
# Uniform definability: one formula for all models of PA

The definability calculus of `PAModels` (`Dfn`) works inside one fixed model: it says
that *some* formula defines a property there. To state a theorem *of PA* about a
property, however, we need a *single* formula that defines it in *every* model at
once. This file repeats the calculus in that uniform form.

* `UDefT f` packages a term together with the proof that, in every model `N` of PA and
  under every environment, it denotes `f N e`;
* `UDef P` packages a formula together with the proof that, in every model, it
  defines `P N`.

Both are *data* (structures, not propositions), so a formula assembled by the
calculus is a concrete, inspectable formula of arithmetic — not one picked by the
axiom of choice. The tactic `udfn` decomposes a property syntactically (connectives,
quantifiers, `=`, `≤`, `<`, `+`, `·`, numerals, variables and Gödel's β-relation) and
builds the defining formula automatically; further atoms can be added with
`macro_rules`.
-/

namespace Foundations.Logic.FO

open Arith Formula

namespace PAModel

/-- **A uniformly definable function.** A term that denotes `f N e` in every model `N`
of PA under every environment `e`. -/
structure UDefT (f : ∀ N : PAModel, (Nat → N.Dom) → N.Dom) where
  /-- The defining term. -/
  t : Term Arith
  /-- It denotes `f`. -/
  spec : ∀ (N : PAModel) (e : Nat → N.Dom), t.eval N.M e = f N e

/-- **A uniformly definable property.** A formula that defines `P N` in every model `N`
of PA. -/
structure UDef (P : ∀ N : PAModel, (Nat → N.Dom) → Prop) where
  /-- The defining formula. -/
  φ : Formula Arith
  /-- It defines `P`. -/
  spec : ∀ (N : PAModel) (e : Nat → N.Dom), Sat N.M e φ ↔ P N e

/-- Variables are uniformly definable. -/
def UDefT.var (n : Nat) : UDefT fun _ e => e n := ⟨v n, fun _ _ => rfl⟩

/-- Numerals are uniformly definable. -/
def UDefT.ofNat (k : Nat) : UDefT fun N _ => (OfNat.ofNat k : N.Dom) :=
  ⟨numeral k, fun _ e => eval_numeral_M e k⟩

/-- Sums are uniformly definable. -/
def UDefT.add {f g : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f) (hg : UDefT g) :
    UDefT fun N e => f N e + g N e :=
  ⟨Arith.add hf.t hg.t, fun N e => by rw [eval_add_M, hf.spec, hg.spec]; rfl⟩

/-- Products are uniformly definable. -/
def UDefT.mul {f g : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f) (hg : UDefT g) :
    UDefT fun N e => f N e * g N e :=
  ⟨Arith.mul hf.t hg.t, fun N e => by rw [eval_mul_M, hf.spec, hg.spec]; rfl⟩

/-- Equations are uniformly definable. -/
def UDef.eq {f g : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f) (hg : UDefT g) :
    UDef fun N e => f N e = g N e :=
  ⟨Formula.eq hf.t hg.t, fun N e => by simp only [Sat, hf.spec, hg.spec]⟩

/-- Conjunction. -/
def UDef.and {P Q : ∀ N : PAModel, (Nat → N.Dom) → Prop} (hP : UDef P) (hQ : UDef Q) :
    UDef fun N e => P N e ∧ Q N e :=
  ⟨conj hP.φ hQ.φ, fun N e => by simp only [Sat, hP.spec, hQ.spec]⟩

/-- Disjunction. -/
def UDef.or {P Q : ∀ N : PAModel, (Nat → N.Dom) → Prop} (hP : UDef P) (hQ : UDef Q) :
    UDef fun N e => P N e ∨ Q N e :=
  ⟨disj hP.φ hQ.φ, fun N e => by simp only [Sat, hP.spec, hQ.spec]⟩

/-- Implication. -/
def UDef.imp {P Q : ∀ N : PAModel, (Nat → N.Dom) → Prop} (hP : UDef P) (hQ : UDef Q) :
    UDef fun N e => P N e → Q N e :=
  ⟨Formula.imp hP.φ hQ.φ, fun N e => by simp only [Sat, hP.spec, hQ.spec]⟩

/-- Negation. -/
def UDef.not {P : ∀ N : PAModel, (Nat → N.Dom) → Prop} (hP : UDef P) :
    UDef fun N e => ¬ P N e :=
  ⟨neg hP.φ, fun N e => by simp only [neg, Sat, hP.spec]⟩

/-- Existential quantification over the variable `0`. -/
def UDef.ex {Q : ∀ N : PAModel, N.Dom → (Nat → N.Dom) → Prop}
    (h : UDef fun N e => Q N (e 0) (fun n => e (n + 1))) : UDef fun N e => ∃ x, Q N x e :=
  ⟨Formula.ex h.φ, fun N e => exists_congr fun x => h.spec N (Env.cons x e)⟩

/-- Universal quantification over the variable `0`. -/
def UDef.all {Q : ∀ N : PAModel, N.Dom → (Nat → N.Dom) → Prop}
    (h : UDef fun N e => Q N (e 0) (fun n => e (n + 1))) : UDef fun N e => ∀ x, Q N x e :=
  ⟨Formula.all h.φ, fun N e => forall_congr' fun x => h.spec N (Env.cons x e)⟩

/-- `≤` is uniformly definable. -/
def UDef.le {f g : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f) (hg : UDefT g) :
    UDef fun N e => f N e ≤ g N e :=
  ⟨Formula.ex (Formula.eq (Arith.add (hf.t.rename Nat.succ) (v 0)) (hg.t.rename Nat.succ)),
    fun N e => by
      simp only [Sat, eval_add_M, Term.eval_rename, eval_var_M]
      exact exists_congr fun z => by
        rw [show (fun n => Env.cons z e (n + 1)) = e from rfl, hf.spec, hg.spec]; rfl⟩

/-- `<` is uniformly definable. -/
def UDef.lt {f g : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f) (hg : UDefT g) :
    UDef fun N e => f N e < g N e :=
  UDef.le (UDefT.add hf (UDefT.ofNat 1)) hg

/-- **Uniformly definable properties are closed under substitution of uniformly
definable functions.** -/
def UDef.subst {P : ∀ N : PAModel, (Nat → N.Dom) → Prop} (hP : UDef P)
    {σ : Nat → ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hσ : ∀ n, UDefT (σ n)) :
    UDef fun N e => P N (fun n => σ n N e) :=
  ⟨hP.φ.subst fun n => (hσ n).t, fun N e => by
    rw [sat_subst, hP.spec]
    have : (fun n => ((hσ n).t).eval N.M e) = fun n => σ n N e := funext fun n => (hσ n).spec N e
    rw [this]⟩

/-- Gödel's β-relation is uniformly definable (at variables). -/
def UDef.betaM_var : UDef fun N e => BetaM (N := N) (e 0) (e 1) (e 2) (e 3) :=
  ⟨Formula.ex (conj
      (Formula.eq (v 1) (Arith.add (Arith.mul (v 0)
        (Arith.add (numeral 1) (Arith.mul (Arith.add (v 3) (numeral 1)) (v 2)))) (v 4)))
      (Formula.ex (Formula.eq (Arith.add (Arith.add (v 5) (numeral 1)) (v 0))
        (Arith.add (numeral 1) (Arith.mul (Arith.add (v 4) (numeral 1)) (v 3)))))),
    fun N e => by
      simp only [Sat, eval_add_M, eval_mul_M, eval_var_M, eval_numeral_M]
      rfl⟩

/-- **Gödel's β-relation is uniformly definable**, at any uniformly definable
arguments. -/
def UDef.betaM {fc fd fi fy : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hc : UDefT fc)
    (hd : UDefT fd) (hi : UDefT fi) (hy : UDefT fy) :
    UDef fun N e => BetaM (fc N e) (fd N e) (fi N e) (fy N e) :=
  UDef.betaM_var.subst (σ := fun n => match n with | 0 => fc | 1 => fd | 2 => fi | _ => fy)
    (fun n => match n with | 0 => hc | 1 => hd | 2 => hi | _ + 3 => hy)

/-- One step of the `udfn` tactic (extensible by further `macro_rules`). -/
syntax "udfn_step" : tactic
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.and)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.or)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.imp)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.not)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.ex)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.all)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.eq)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDefT.add)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDefT.mul)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDefT.ofNat)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDefT.var)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.le)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.lt)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.betaM)

/-- `udfn` builds uniform definitions `UDef P` by decomposing `P` syntactically. -/
macro "udfn" : tactic => `(tactic| repeat' udfn_step)

end PAModel

end Foundations.Logic.FO
