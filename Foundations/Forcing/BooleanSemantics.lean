import Foundations.Forcing.BooleanAlgebra
import Foundations.Logic.FOSyntax

/-!
# Boolean-valued semantics for first-order logic

Tarski's semantics (`Logic/FOSemantics`) assigns to every formula, under an environment, a
truth value in `Prop`. Scott and Solovay's idea is to let truth values range over an
arbitrary complete Boolean algebra `B`:

* `⟦⊥⟧ = ⊥`, `⟦φ ∧ ψ⟧ = ⟦φ⟧ ⊓ ⟦ψ⟧`, `⟦φ ∨ ψ⟧ = ⟦φ⟧ ⊔ ⟦ψ⟧`, `⟦φ → ψ⟧ = ⟦φ⟧ ⇨ ⟦ψ⟧`;
* `⟦∀x φ⟧ = ⨅ₓ ⟦φ⟧[x]` and `⟦∃x φ⟧ = ⨆ₓ ⟦φ⟧[x]`, infinite meets and joins over the domain.

Equality is no longer two-valued either: a **Boolean-valued structure** (`BStructure`)
carries a `B`-valued equality `⟦x = y⟧`. It must be reflexive, symmetric and transitive in
the Boolean sense, and function and relation symbols must respect it (for instance
`⟦a = b⟧ ⊓ ⟦R a⟧ ≤ ⟦R b⟧`). In the Boolean-valued universe of set theory two distinct
names may denote "partly the same" set, so this generality is essential.

This file defines the truth value `val M e φ ∈ B` for the existing de Bruijn syntax and
proves the two technical lemmas that make the semantics behave:

* the **substitution lemma** `val_subst`, as in the Tarskian case;
* the **congruence lemma** `envEq_inf_val_le`: if two environments agree to degree
  `d = ⨅ₙ ⟦e n = e' n⟧`, then `d ⊓ ⟦φ⟧ₑ ≤ ⟦φ⟧ₑ'`. Every formula is extensional with
  respect to Boolean equality. This needs the *infinite* meet over all variables, which
  exists because `B` is complete.

Soundness of the proof calculus is proved in the next file.

Domains may live in any universe (`Type w`), because the Boolean-valued universe of sets
built later lives in `Type 1`. For this reason term evaluation and environments are
redefined here rather than borrowed from the `Prop`-valued development, whose domains live
in `Type`.
-/

namespace Foundations.Forcing

open Foundations.Logic.FO CBA

universe u w

/-- Push a value onto an environment (universe-polymorphic version of `Env.cons`). -/
def BEnv.cons {α : Type w} (x : α) (e : Nat → α) : Nat → α
  | 0 => x
  | n + 1 => e n

/-- **Boolean-valued structure.** A domain with genuine functions for the function
symbols, `B`-valued relations for the relation symbols, and a `B`-valued equality that is
an equivalence relation in the Boolean sense and is respected by all symbols. -/
structure BStructure (L : Signature) (B : Type u) [CompleteBooleanAlgebra B] where
  /-- The domain ("names"). -/
  Dom : Type w
  /-- Interpretation of `n`-ary function symbols. -/
  funcs : {n : Nat} → L.Func n → (Fin n → Dom) → Dom
  /-- Boolean truth value of an atomic relational statement. -/
  rels : {n : Nat} → L.Rel n → (Fin n → Dom) → B
  /-- Boolean truth value of an equation. -/
  eq : Dom → Dom → B
  /-- `⟦x = x⟧ = ⊤`. -/
  eq_refl : ∀ x, eq x x = ⊤
  /-- `⟦x = y⟧ ≤ ⟦y = x⟧`. -/
  eq_symm : ∀ x y, eq x y ≤ eq y x
  /-- `⟦x = y⟧ ⊓ ⟦y = z⟧ ≤ ⟦x = z⟧`. -/
  eq_trans : ∀ x y z, eq x y ⊓ eq y z ≤ eq x z
  /-- Function symbols respect Boolean equality. -/
  funcs_congr : ∀ {n} (f : L.Func n) (a b : Fin n → Dom),
    iInf (fun i => eq (a i) (b i)) ≤ eq (funcs f a) (funcs f b)
  /-- Relation symbols respect Boolean equality. -/
  rels_congr : ∀ {n} (R : L.Rel n) (a b : Fin n → Dom),
    iInf (fun i => eq (a i) (b i)) ⊓ rels R a ≤ rels R b

variable {L : Signature} {B : Type u} [CompleteBooleanAlgebra B]

namespace BStructure

variable (M : BStructure.{u, w} L B)

/-- The value of a term under an environment. -/
def evalT (e : Nat → M.Dom) : Term L → M.Dom
  | .var n => e n
  | .func f ts => M.funcs f fun i => evalT e (ts i)

variable {M}

/-- Evaluating a renamed term. -/
theorem evalT_rename (e : Nat → M.Dom) (ρ : Nat → Nat) :
    ∀ t : Term L, M.evalT e (t.rename ρ) = M.evalT (fun n => e (ρ n)) t
  | .var _ => rfl
  | .func f ts => by
      simp only [Term.rename, evalT]; congr; funext i; exact evalT_rename e ρ (ts i)

/-- Substitution lemma for terms. -/
theorem evalT_subst (e : Nat → M.Dom) (σ : Nat → Term L) :
    ∀ t : Term L, M.evalT e (t.subst σ) = M.evalT (fun n => M.evalT e (σ n)) t
  | .var _ => rfl
  | .func f ts => by
      simp only [Term.subst, evalT]; congr; funext i; exact evalT_subst e σ (ts i)

variable (M)

/-- **Boolean truth value** `⟦φ⟧ₑ ∈ B` of a formula under an environment. Quantifiers are
interpreted by infinite meets and joins over the domain. -/
def val : (Nat → M.Dom) → Formula L → B
  | _, .bot => ⊥
  | e, .eq t s => M.eq (M.evalT e t) (M.evalT e s)
  | e, .rel R ts => M.rels R fun i => M.evalT e (ts i)
  | e, .imp φ ψ => val e φ ⇨ val e ψ
  | e, .conj φ ψ => val e φ ⊓ val e ψ
  | e, .disj φ ψ => val e φ ⊔ val e ψ
  | e, .all φ => iInf fun x => val (BEnv.cons x e) φ
  | e, .ex φ => iSup fun x => val (BEnv.cons x e) φ

variable {M}

/-- Evaluating under a lifted substitution after pushing `x`. -/
theorem lift_evalT (e : Nat → M.Dom) (σ : Nat → Term L) (x : M.Dom) :
    (fun n => M.evalT (BEnv.cons x e) (Subst.lift σ n)) =
      BEnv.cons x (fun n => M.evalT e (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Subst.lift, evalT_rename]; rfl

/-- **Substitution lemma (Boolean-valued).** `⟦φ[σ]⟧ₑ = ⟦φ⟧_{n ↦ ⟦σ n⟧ₑ}`. -/
theorem val_subst : ∀ (φ : Formula L) (e : Nat → M.Dom) (σ : Nat → Term L),
    M.val e (φ.subst σ) = M.val (fun n => M.evalT e (σ n)) φ
  | .bot, _, _ => rfl
  | .eq t s, e, σ => by simp only [Formula.subst, val, evalT_subst]
  | .rel R ts, e, σ => by simp only [Formula.subst, val, evalT_subst]
  | .imp φ ψ, e, σ => by simp only [Formula.subst, val, val_subst φ, val_subst ψ]
  | .conj φ ψ, e, σ => by simp only [Formula.subst, val, val_subst φ, val_subst ψ]
  | .disj φ ψ, e, σ => by simp only [Formula.subst, val, val_subst φ, val_subst ψ]
  | .all φ, e, σ => by simp only [Formula.subst, val, val_subst φ, lift_evalT]
  | .ex φ, e, σ => by simp only [Formula.subst, val, val_subst φ, lift_evalT]

/-- Shifting a formula and pushing a value cancel: `⟦φ↑⟧_{x·e} = ⟦φ⟧ₑ`. -/
theorem val_shift (φ : Formula L) (e : Nat → M.Dom) (x : M.Dom) :
    M.val (BEnv.cons x e) φ.shift = M.val e φ := by
  simp only [Formula.shift, val_subst]; rfl

/-- Instantiation: `⟦φ(t)⟧ₑ = ⟦φ⟧_{⟦t⟧ₑ · e}`. -/
theorem val_inst (φ : Formula L) (e : Nat → M.Dom) (t : Term L) :
    M.val e (φ.inst t) = M.val (BEnv.cons (M.evalT e t) e) φ := by
  simp only [Formula.inst, val_subst]
  have : (fun n => M.evalT e (Subst.single t n)) = BEnv.cons (M.evalT e t) e := by
    funext n; cases n <;> rfl
  rw [this]

/-! ### Extensionality of formulas with respect to Boolean equality -/

/-- Symmetry of Boolean equality as an equation. -/
theorem eq_comm' (x y : M.Dom) : M.eq x y = M.eq y x :=
  le_antisymm' (M.eq_symm x y) (M.eq_symm y x)

/-- The degree `⨅ₙ ⟦e n = e' n⟧` to which two environments agree. -/
def envEq (M : BStructure.{u, w} L B) (e e' : Nat → M.Dom) : B :=
  iInf fun n => M.eq (e n) (e' n)

/-- Agreement of environments is symmetric. -/
theorem envEq_symm (e e' : Nat → M.Dom) : M.envEq e e' ≤ M.envEq e' e :=
  iInf_mono fun _ => M.eq_symm _ _

/-- Pushing the same value onto two environments does not decrease their agreement. -/
theorem envEq_cons (e e' : Nat → M.Dom) (x : M.Dom) :
    M.envEq e e' ≤ M.envEq (BEnv.cons x e) (BEnv.cons x e') :=
  le_iInf fun n => by
    cases n with
    | zero => exact le_trans' le_top' (by rw [show BEnv.cons x e 0 = x from rfl,
                show BEnv.cons x e' 0 = x from rfl, M.eq_refl x]; exact le_rfl)
    | succ k => exact iInf_le (fun n => M.eq (e n) (e' n)) k

/-- Terms respect agreement of environments. -/
theorem envEq_le_evalT (e e' : Nat → M.Dom) :
    ∀ t : Term L, M.envEq e e' ≤ M.eq (M.evalT e t) (M.evalT e' t)
  | .var n => iInf_le _ n
  | .func f ts => le_trans' (le_iInf fun i => envEq_le_evalT e e' (ts i)) (M.funcs_congr f _ _)

/-- **Congruence lemma.** Every formula is extensional for Boolean equality: if the
environments `e`, `e'` agree to degree `d`, then `d ⊓ ⟦φ⟧ₑ ≤ ⟦φ⟧ₑ'`. -/
theorem envEq_inf_val_le : ∀ (φ : Formula L) (e e' : Nat → M.Dom),
    M.envEq e e' ⊓ M.val e φ ≤ M.val e' φ
  | .bot, _, _ => inf_le_right _ _
  | .eq t s, e, e' => by
      show M.envEq e e' ⊓ M.eq (M.evalT e t) (M.evalT e s) ≤ M.eq (M.evalT e' t) (M.evalT e' s)
      have ht := envEq_le_evalT e e' t
      have hs := envEq_le_evalT e e' s
      calc M.envEq e e' ⊓ M.eq (M.evalT e t) (M.evalT e s)
          ≤ M.eq (M.evalT e' t) (M.evalT e t) ⊓ M.eq (M.evalT e t) (M.evalT e s) ⊓
              M.eq (M.evalT e s) (M.evalT e' s) :=
            le_inf _ _ _ (inf_le_inf (le_trans' ht (M.eq_symm _ _)) le_rfl)
              (inf_le_of_left_le hs)
        _ ≤ M.eq (M.evalT e' t) (M.evalT e s) ⊓ M.eq (M.evalT e s) (M.evalT e' s) :=
            inf_le_inf (M.eq_trans _ _ _) le_rfl
        _ ≤ _ := M.eq_trans _ _ _
  | .rel R ts, e, e' =>
      le_trans' (inf_le_inf (le_iInf fun i => envEq_le_evalT e e' (ts i)) le_rfl)
        (M.rels_congr R _ _)
  | .imp φ ψ, e, e' => by
      show M.envEq e e' ⊓ (M.val e φ ⇨ M.val e ψ) ≤ M.val e' φ ⇨ M.val e' ψ
      rw [le_himp_iff]
      have h1 := envEq_inf_val_le φ e' e
      have h2 := envEq_inf_val_le ψ e e'
      calc M.envEq e e' ⊓ (M.val e φ ⇨ M.val e ψ) ⊓ M.val e' φ
          ≤ M.envEq e e' ⊓ ((M.val e φ ⇨ M.val e ψ) ⊓ M.val e φ) :=
            le_inf _ _ _ (inf_le_of_left_le (inf_le_left _ _))
              (le_inf _ _ _ (inf_le_of_left_le (inf_le_right _ _))
                (le_trans' (inf_le_inf (inf_le_of_left_le (envEq_symm e e')) le_rfl) h1))
        _ ≤ M.envEq e e' ⊓ M.val e ψ := inf_le_inf le_rfl himp_inf_le
        _ ≤ M.val e' ψ := h2
  | .conj φ ψ, e, e' =>
      le_inf _ _ _
        (le_trans' (inf_le_inf le_rfl (inf_le_left _ _)) (envEq_inf_val_le φ e e'))
        (le_trans' (inf_le_inf le_rfl (inf_le_right _ _)) (envEq_inf_val_le ψ e e'))
  | .disj φ ψ, e, e' =>
      le_trans' (inf_sup_le _ _ _)
        (sup_le_sup (envEq_inf_val_le φ e e') (envEq_inf_val_le ψ e e'))
  | .all φ, e, e' =>
      le_iInf fun x => le_trans' (inf_le_inf (envEq_cons e e' x) (iInf_le _ x))
        (envEq_inf_val_le φ _ _)
  | .ex φ, e, e' =>
      le_trans' inf_iSup_le (iSup_mono fun x =>
        le_trans' (inf_le_inf (envEq_cons e e' x) le_rfl) (envEq_inf_val_le φ _ _))

/-- **Leibniz's law for truth values.** `⟦x = y⟧ ⊓ ⟦φ(x)⟧ ≤ ⟦φ(y)⟧`, where `φ(x)` means `φ`
evaluated with `x` pushed onto the environment. -/
theorem eq_inf_val_cons_le (φ : Formula L) (e : Nat → M.Dom) (x y : M.Dom) :
    M.eq x y ⊓ M.val (BEnv.cons x e) φ ≤ M.val (BEnv.cons y e) φ := by
  have hd : M.eq x y ≤ M.envEq (BEnv.cons x e) (BEnv.cons y e) :=
    le_iInf fun n => by
      cases n with
      | zero => exact le_rfl
      | succ k =>
          show _ ≤ M.eq (e k) (e k)
          rw [M.eq_refl]; exact le_top'
  exact le_trans' (inf_le_inf hd le_rfl) (envEq_inf_val_le φ _ _)

/-- Lifting a formula past `k` new binders (keeping its variable `0`): the substitution
`0 ↦ 0`, `n + 1 ↦ n + 1 + k`. Used to state axiom schemes with parameters. -/
def liftBy (k : Nat) (φ : Formula L) : Formula L := φ.subst (Subst.lift fun n => .var (n + k))

/-- Truth value of a lifted formula: if the environment `env` has the parameters `e` sitting
`k` places down, then `⟦liftBy k φ⟧_{z·env} = ⟦φ⟧_{z·e}`. -/
theorem val_liftBy (k : Nat) (φ : Formula L) (z : M.Dom) (env e : Nat → M.Dom)
    (h : ∀ n, env (n + k) = e n) :
    M.val (BEnv.cons z env) (liftBy k φ) = M.val (BEnv.cons z e) φ := by
  simp only [liftBy, val_subst, lift_evalT]
  have : (fun n => M.evalT env (Term.var (n + k) : Term L)) = e := funext h
  rw [this]

end BStructure

end Foundations.Forcing
