import Foundations.Forcing.CardinalPreservation
import Foundations.Forcing.BSetZF

/-!
# Relativised satisfaction: formulas of set theory read inside a class

## Gödel's idea

In 1938 Kurt Gödel showed that the axiom of choice and the generalised continuum
hypothesis cannot be refuted from the axioms of Zermelo–Fraenkel set theory. His method was
to find, inside any universe of sets, a smaller universe `L` of **constructible** sets in
which these statements are true. The sets of `L` are built in stages along the ordinals, and
at each stage one adds exactly those subsets of the previous stage that can be **defined**
over it by a first-order formula of set theory. Everything in this part rests on that one
notion: a formula `φ` of the language `LSet` (one binary relation symbol `∈`) can be read
inside a structure `(X, ∈)`, with its quantifiers ranging only over `X`.

## What this file does

For a predicate `P : ZFSet → Prop` (a "class") we define `RSat P e φ`: the formula `φ` holds
when its quantifiers range over the sets satisfying `P`, membership is real membership and the
free variables take the values `e n`. This is the familiar **relativisation** `φ^P` of set
theory. Two special cases connect it with the library's existing semantics:

* for a set `X`, the Tarskian structure `setStr X` with domain `Small X` (a small type of the
  members of `X`, from the forcing part) satisfies `φ` exactly when `RSat (· ∈ X)` does
  (`sat_setStr_iff`);
* for a class `P`, the two-valued Boolean structure `classStr P` with domain the subtype
  `{z // P z}` (which lives in `Type 1`) gives `φ` the truth value `⊤` exactly when
  `RSat P` holds (`val_classStr_iff`). This is the form in which soundness
  (`not_proves_of_val`) applies.

We prove the substitution lemma for `RSat` and a **finite support** lemma: the truth of `φ`
depends only on the values of the variables below a syntactic bound `bnd φ`. The latter lets
us replace an environment of infinitely many parameters by one with finitely many, which is
needed in the reflection argument later.

## The contrast with forcing

Part XIII proved both halves of the independence of CH by *enlarging* the universe: a
Boolean-valued model `V^B` adds new, generic sets. Gödel's method goes the other way: it
*shrinks* the universe to the sets that are explicitly definable from earlier ones. Here
the truth values are two-valued again (`B = Prop`), and the domain is a subclass of the
ordinary universe `ZFSet`.
-/

namespace Foundations.Constructible

open Foundations.Logic.FO Foundations.Forcing Foundations.Sets Foundations.Sets.ZFSet
open CBA
open BStructure (liftBy allN)

/-! ### Terms and relativised satisfaction -/

/-- The value of an `LSet` term under an environment of sets. `LSet` has no function
symbols, so every term is a variable. -/
def tv (e : Nat → ZFSet) : Term LSet → ZFSet
  | .var n => e n
  | .func f _ => nomatch f

/-- A variable evaluates to its value in the environment. -/
@[simp] theorem tv_var (e : Nat → ZFSet) (n : Nat) : tv e (.var n) = e n := rfl

/-- **Relativised satisfaction.** `RSat P e φ` is the relativisation `φ^P`: it holds when
`φ` is true with its quantifiers restricted to the class `P`, membership read as membership
of `ZFSet`, and the free variable `n` given the value `e n`. -/
def RSat (P : ZFSet → Prop) : (Nat → ZFSet) → Formula LSet → Prop
  | _, .bot => False
  | e, .eq t s => tv e t = tv e s
  | e, .rel R ts => tv e (ts ⟨0, by have := R.down; omega⟩) ∈ tv e (ts ⟨1, by have := R.down; omega⟩)
  | e, .imp φ ψ => RSat P e φ → RSat P e ψ
  | e, .conj φ ψ => RSat P e φ ∧ RSat P e ψ
  | e, .disj φ ψ => RSat P e φ ∨ RSat P e ψ
  | e, .all φ => ∀ x, P x → RSat P (BEnv.cons x e) φ
  | e, .ex φ => ∃ x, P x ∧ RSat P (BEnv.cons x e) φ

/-- Pushing `x` and reading index `0` gives `x`. -/
@[simp] theorem cons_zero (x : ZFSet) (e : Nat → ZFSet) : BEnv.cons x e 0 = x := rfl

/-- Pushing `x` and reading index `n + 1` gives the old value of `n`. -/
@[simp] theorem cons_succ (x : ZFSet) (e : Nat → ZFSet) (n : Nat) :
    BEnv.cons x e (n + 1) = e n := rfl

/-- The atomic formula `t ∈ s` holds iff the values are members. -/
@[simp] theorem RSat_memF (P : ZFSet → Prop) (e : Nat → ZFSet) (t s : Term LSet) :
    RSat P e (memF t s) ↔ tv e t ∈ tv e s := Iff.rfl

/-- The biconditional `φ ↔ ψ` holds iff the two sides are equivalent. -/
@[simp] theorem RSat_iffF (P : ZFSet → Prop) (e : Nat → ZFSet) (φ ψ : Formula LSet) :
    RSat P e (iffF φ ψ) ↔ (RSat P e φ ↔ RSat P e ψ) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Negation holds iff the formula fails. -/
@[simp] theorem RSat_neg (P : ZFSet → Prop) (e : Nat → ZFSet) (φ : Formula LSet) :
    RSat P e φ.neg ↔ ¬ RSat P e φ := Iff.rfl

/-! ### Substitution -/

/-- Evaluating a substituted term. -/
theorem tv_subst (e : Nat → ZFSet) (σ : Nat → Term LSet) :
    ∀ t : Term LSet, tv e (t.subst σ) = tv (fun n => tv e (σ n)) t
  | .var _ => rfl
  | .func f _ => nomatch f

/-- Evaluating a renamed term. -/
theorem tv_rename (e : Nat → ZFSet) (ρ : Nat → Nat) :
    ∀ t : Term LSet, tv e (t.rename ρ) = tv (fun n => e (ρ n)) t
  | .var _ => rfl
  | .func f _ => nomatch f

/-- Evaluating under a lifted substitution after pushing `x`. -/
theorem tv_lift (e : Nat → ZFSet) (σ : Nat → Term LSet) (x : ZFSet) :
    (fun n => tv (BEnv.cons x e) (Subst.lift σ n)) = BEnv.cons x (fun n => tv e (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Subst.lift, tv_rename]; rfl

/-- Substitution lemma for relativised satisfaction. `φ[σ]` holds under `e` iff `φ`
holds under `n ↦ ⟦σ n⟧ₑ`. -/
theorem RSat_subst (P : ZFSet → Prop) : ∀ (φ : Formula LSet) (e : Nat → ZFSet)
    (σ : Nat → Term LSet), RSat P e (φ.subst σ) ↔ RSat P (fun n => tv e (σ n)) φ
  | .bot, _, _ => Iff.rfl
  | .eq t s, e, σ => by simp only [Formula.subst, RSat, tv_subst]
  | .rel R ts, e, σ => by simp only [Formula.subst, RSat, tv_subst]
  | .imp φ ψ, e, σ => by simp only [Formula.subst, RSat, RSat_subst P φ, RSat_subst P ψ]
  | .conj φ ψ, e, σ => by simp only [Formula.subst, RSat, RSat_subst P φ, RSat_subst P ψ]
  | .disj φ ψ, e, σ => by simp only [Formula.subst, RSat, RSat_subst P φ, RSat_subst P ψ]
  | .all φ, e, σ => by simp only [Formula.subst, RSat, RSat_subst P φ, tv_lift]
  | .ex φ, e, σ => by simp only [Formula.subst, RSat, RSat_subst P φ, tv_lift]

/-- Relativised satisfaction of `liftBy k φ` (the formula `φ` moved past `k` new binders,
keeping its variable `0`): if `env` is `e` shifted `k` places, it is satisfaction of `φ`. -/
theorem RSat_liftBy (P : ZFSet → Prop) (k : Nat) (φ : Formula LSet) (z : ZFSet)
    (env e : Nat → ZFSet) (h : ∀ n, env (n + k) = e n) :
    RSat P (BEnv.cons z env) (liftBy k φ) ↔ RSat P (BEnv.cons z e) φ := by
  simp only [liftBy, RSat_subst, tv_lift]
  have : (fun n => tv env (Term.var (n + k) : Term LSet)) = e := funext h
  rw [this]

/-- Relativised satisfaction of `lift2By k φ` (keeping variables `0` and `1`). -/
theorem RSat_lift2By (P : ZFSet → Prop) (k : Nat) (φ : Formula LSet) (y x : ZFSet)
    (env e : Nat → ZFSet) (h : ∀ n, env (n + k) = e n) :
    RSat P (BEnv.cons y (BEnv.cons x env)) (lift2By k φ) ↔
      RSat P (BEnv.cons y (BEnv.cons x e)) φ := by
  simp only [lift2By, RSat_subst, tv_lift]
  have : (fun n => tv env (Term.var (n + k) : Term LSet)) = e := funext h
  rw [this]

/-! ### Finite support -/

/-- The largest value of a finite family of natural numbers (`0` for the empty family). -/
def finMax : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => max (f 0) (finMax n fun i => f i.succ)

/-- Every member of a finite family is at most its maximum. -/
theorem le_finMax : ∀ (n : Nat) (f : Fin n → Nat) (i : Fin n), f i ≤ finMax n f
  | 0, _, i => i.elim0
  | n + 1, f, i => by
      cases i using Fin.cases with
      | zero => exact Nat.le_max_left _ _
      | succ j => exact Nat.le_trans (le_finMax n (fun i => f i.succ) j) (Nat.le_max_right _ _)

/-- A bound on the free variables of a term: `n + 1` for the variable `n`. -/
def tbnd : Term LSet → Nat
  | .var n => n + 1
  | .func _ _ => 0

/-- Variable bound of a formula. Every free variable of `φ` has index below `bnd φ`. -/
def bnd : Formula LSet → Nat
  | .bot => 0
  | .eq t s => max (tbnd t) (tbnd s)
  | .rel (n := n) _ ts => finMax n fun i => tbnd (ts i)
  | .imp φ ψ => max (bnd φ) (bnd ψ)
  | .conj φ ψ => max (bnd φ) (bnd ψ)
  | .disj φ ψ => max (bnd φ) (bnd ψ)
  | .all φ => bnd φ - 1
  | .ex φ => bnd φ - 1

/-- Terms depend only on the variables below their bound. -/
theorem tv_congr {e e' : Nat → ZFSet} : ∀ (t : Term LSet), (∀ n < tbnd t, e n = e' n) →
    tv e t = tv e' t
  | .var n, h => h n (Nat.lt_succ_self n)
  | .func f _, _ => nomatch f

/-- Agreement below `k + 1` after pushing the same value follows from agreement below `k`. -/
theorem cons_agree {e e' : Nat → ZFSet} {k : Nat} (x : ZFSet) (h : ∀ n < k - 1, e n = e' n) :
    ∀ n < k, BEnv.cons x e n = BEnv.cons x e' n
  | 0, _ => rfl
  | n + 1, hn => h n (by omega)

/-- Finite support. If two environments agree on every variable below `bnd φ`, they
satisfy `φ` alike. -/
theorem RSat_congr (P : ZFSet → Prop) : ∀ (φ : Formula LSet) {e e' : Nat → ZFSet},
    (∀ n < bnd φ, e n = e' n) → (RSat P e φ ↔ RSat P e' φ)
  | .bot, _, _, _ => Iff.rfl
  | .eq t s, e, e', h => by
      show tv e t = tv e s ↔ tv e' t = tv e' s
      rw [tv_congr t (fun n hn => h n (Nat.lt_of_lt_of_le hn (Nat.le_max_left _ _))),
        tv_congr s (fun n hn => h n (Nat.lt_of_lt_of_le hn (Nat.le_max_right _ _)))]
  | .rel (n := m) R ts, e, e', h => by
      have hc : ∀ i, tv e (ts i) = tv e' (ts i) := fun i =>
        tv_congr (ts i) fun n hn => h n (Nat.lt_of_lt_of_le hn (le_finMax m (fun i => tbnd (ts i)) i))
      show tv e (ts _) ∈ tv e (ts _) ↔ tv e' (ts _) ∈ tv e' (ts _)
      rw [hc, hc]
  | .imp φ ψ, e, e', h => by
      have h1 := RSat_congr P φ (fun n hn => h n (Nat.lt_of_lt_of_le hn (Nat.le_max_left _ _)))
      have h2 := RSat_congr P ψ (fun n hn => h n (Nat.lt_of_lt_of_le hn (Nat.le_max_right _ _)))
      exact imp_congr h1 h2
  | .conj φ ψ, e, e', h => by
      have h1 := RSat_congr P φ (fun n hn => h n (Nat.lt_of_lt_of_le hn (Nat.le_max_left _ _)))
      have h2 := RSat_congr P ψ (fun n hn => h n (Nat.lt_of_lt_of_le hn (Nat.le_max_right _ _)))
      exact and_congr h1 h2
  | .disj φ ψ, e, e', h => by
      have h1 := RSat_congr P φ (fun n hn => h n (Nat.lt_of_lt_of_le hn (Nat.le_max_left _ _)))
      have h2 := RSat_congr P ψ (fun n hn => h n (Nat.lt_of_lt_of_le hn (Nat.le_max_right _ _)))
      exact or_congr h1 h2
  | .all φ, e, e', h =>
      forall_congr' fun x => imp_congr Iff.rfl (RSat_congr P φ (cons_agree x h))
  | .ex φ, e, e', h =>
      exists_congr fun x => and_congr Iff.rfl (RSat_congr P φ (cons_agree x h))

/-- Satisfaction depends on the class only through its extension: two predicates that
agree everywhere give the same satisfaction relation. -/
theorem RSat_class_congr {P Q : ZFSet → Prop} (hPQ : ∀ x, P x ↔ Q x) :
    ∀ (φ : Formula LSet) (e : Nat → ZFSet), RSat P e φ ↔ RSat Q e φ
  | .bot, _ => Iff.rfl
  | .eq _ _, _ => Iff.rfl
  | .rel _ _, _ => Iff.rfl
  | .imp φ ψ, e => imp_congr (RSat_class_congr hPQ φ e) (RSat_class_congr hPQ ψ e)
  | .conj φ ψ, e => and_congr (RSat_class_congr hPQ φ e) (RSat_class_congr hPQ ψ e)
  | .disj φ ψ, e => or_congr (RSat_class_congr hPQ φ e) (RSat_class_congr hPQ ψ e)
  | .all φ, _ => forall_congr' fun x => imp_congr (hPQ x) (RSat_class_congr hPQ φ _)
  | .ex φ, _ => exists_congr fun x => and_congr (hPQ x) (RSat_class_congr hPQ φ _)

/-! ### The Tarskian structure `(X, ∈)` on a set -/

/-- The structure `(X, ∈)`. For a set `X`, the Tarskian `LSet`-structure whose domain is
the small type `Small X` of members of `X` and whose relation symbol is membership. -/
noncomputable abbrev setStr (X : ZFSet) : Structure LSet where
  Dom := Small X
  funcs f _ := nomatch f
  rels R a := (a ⟨0, by have := R.down; omega⟩).val ∈ (a ⟨1, by have := R.down; omega⟩).val

/-- Term values in `setStr X` name the corresponding sets. -/
theorem eval_setStr (X : ZFSet) (e : Nat → Small X) :
    ∀ t : Term LSet, (t.eval (setStr X) e).val = tv (fun n => (e n).val) t
  | .var _ => rfl
  | .func f _ => nomatch f

/-- Reading `Env.cons` through `Small.val`. -/
theorem val_env_cons {X : ZFSet} (q : Small X) (e : Nat → Small X) :
    (fun n => (Env.cons q e n).val) = BEnv.cons q.val (fun n => (e n).val) := by
  funext n; cases n <;> rfl

/-- **Tarskian satisfaction in `(X, ∈)` is relativisation to `X`.** -/
theorem sat_setStr_iff (X : ZFSet) : ∀ (φ : Formula LSet) (e : Nat → Small X),
    Formula.Sat (setStr X) e φ ↔ RSat (· ∈ X) (fun n => (e n).val) φ
  | .bot, _ => Iff.rfl
  | .eq t s, e => by
      show t.eval (setStr X) e = s.eval (setStr X) e ↔ tv _ t = tv _ s
      rw [← eval_setStr X e t, ← eval_setStr X e s]
      exact ⟨fun h => h ▸ rfl, fun h => Small.val_injective h⟩
  | .rel R ts, e => by
      show (setStr X).rels R _ ↔ _
      show (Term.eval (setStr X) e (ts _)).val ∈ (Term.eval (setStr X) e (ts _)).val ↔ _
      rw [eval_setStr, eval_setStr]; exact Iff.rfl
  | .imp φ ψ, e => imp_congr (sat_setStr_iff X φ e) (sat_setStr_iff X ψ e)
  | .conj φ ψ, e => and_congr (sat_setStr_iff X φ e) (sat_setStr_iff X ψ e)
  | .disj φ ψ, e => or_congr (sat_setStr_iff X φ e) (sat_setStr_iff X ψ e)
  | .all φ, e => by
      show (∀ q : Small X, Formula.Sat (setStr X) (Env.cons q e) φ) ↔ _
      constructor
      · intro h x hx
        have := (sat_setStr_iff X φ _).1 (h (Small.ofMem x hx))
        rwa [val_env_cons, Small.val_ofMem] at this
      · intro h q
        rw [sat_setStr_iff X φ, val_env_cons]
        exact h q.val q.val_mem
  | .ex φ, e => by
      show (∃ q : Small X, Formula.Sat (setStr X) (Env.cons q e) φ) ↔ _
      constructor
      · rintro ⟨q, hq⟩
        rw [sat_setStr_iff X φ, val_env_cons] at hq
        exact ⟨q.val, q.val_mem, hq⟩
      · rintro ⟨x, hx, h⟩
        refine ⟨Small.ofMem x hx, ?_⟩
        rw [sat_setStr_iff X φ, val_env_cons, Small.val_ofMem]
        exact h

/-! ### The two-valued structure `(P, ∈)` on a class -/

/-- The structure `(P, ∈)` on a class. For a predicate `P`, the two-valued (`Prop`-valued)
Boolean structure whose domain is the subtype `{z // P z}` (in `Type 1`), with genuine equality
and membership. This is a Tarskian structure in all but name: the `Prop`-valued semantics of
`BStructure` is Tarski's (`val_ofStructure_iff`), but `Structure` itself requires a domain in
`Type`, while a proper class of sets needs `Type 1`. -/
abbrev classStr (P : ZFSet → Prop) : BStructure.{0, 1} LSet Prop where
  Dom := {z : ZFSet // P z}
  funcs f _ := nomatch f
  rels R a := (a ⟨0, by have := R.down; omega⟩).1 ∈ (a ⟨1, by have := R.down; omega⟩).1
  eq x y := x = y
  eq_refl x := propext ⟨fun _ => trivial, fun _ => rfl⟩
  eq_symm _ _ h := h.symm
  eq_trans _ _ _ h := h.1.trans h.2
  funcs_congr f _ _ := nomatch f
  rels_congr R a b h := by
    have e : a = b := funext fun i => (BStructure.prop_iInf_iff _).1 h.1 i
    exact e ▸ h.2

/-- Term values in `classStr P`. -/
theorem evalT_classStr (P : ZFSet → Prop) (e : Nat → {z // P z}) :
    ∀ t : Term LSet, ((classStr P).evalT e t).1 = tv (fun n => (e n).1) t
  | .var _ => rfl
  | .func f _ => nomatch f

/-- Reading `BEnv.cons` through the subtype projection. -/
theorem val_benv_cons {P : ZFSet → Prop} (q : {z // P z}) (e : Nat → {z // P z}) :
    (fun n => (BEnv.cons q e n).1) = BEnv.cons q.1 (fun n => (e n).1) := by
  funext n; cases n <;> rfl

/-- **Truth in `(P, ∈)` is relativisation to `P`.** -/
theorem val_classStr_iff (P : ZFSet → Prop) : ∀ (φ : Formula LSet) (e : Nat → {z // P z}),
    (classStr P).val e φ ↔ RSat P (fun n => (e n).1) φ
  | .bot, _ => Iff.rfl
  | .eq t s, e => by
      show (classStr P).evalT e t = (classStr P).evalT e s ↔ tv _ t = tv _ s
      rw [← evalT_classStr P e t, ← evalT_classStr P e s]
      exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
  | .rel R ts, e => by
      show ((classStr P).evalT e (ts _)).1 ∈ ((classStr P).evalT e (ts _)).1 ↔ _
      rw [evalT_classStr, evalT_classStr]; exact Iff.rfl
  | .imp φ ψ, e => by
      show (¬ _ ∨ _) ↔ (_ → _)
      rw [val_classStr_iff P φ e, val_classStr_iff P ψ e]
      exact ⟨fun h hφ => h.elim (absurd hφ) id,
        fun h => (Classical.em (RSat P _ φ)).elim (fun hφ => Or.inr (h hφ)) Or.inl⟩
  | .conj φ ψ, e => and_congr (val_classStr_iff P φ e) (val_classStr_iff P ψ e)
  | .disj φ ψ, e => or_congr (val_classStr_iff P φ e) (val_classStr_iff P ψ e)
  | .all φ, e => by
      refine (BStructure.prop_iInf_iff _).trans ?_
      constructor
      · intro h x hx
        have := (val_classStr_iff P φ _).1 (h ⟨x, hx⟩)
        rwa [val_benv_cons] at this
      · intro h q
        rw [val_classStr_iff P φ, val_benv_cons]
        exact h q.1 q.2
  | .ex φ, e => by
      refine (BStructure.prop_iSup_iff _).trans ?_
      constructor
      · rintro ⟨q, hq⟩
        rw [val_classStr_iff P φ, val_benv_cons] at hq
        exact ⟨q.1, q.2, hq⟩
      · rintro ⟨x, hx, h⟩
        refine ⟨⟨x, hx⟩, ?_⟩
        rw [val_classStr_iff P φ, val_benv_cons]
        exact h

/-- In `Prop`, a truth value equals `⊤` iff it holds. -/
theorem prop_eq_top_iff (p : Prop) : p = (⊤ : Prop) ↔ p :=
  ⟨fun h => h ▸ trivial, fun h => propext ⟨fun _ => trivial, fun _ => h⟩⟩

/-- Truth value `⊤` in `(P, ∈)`. A formula has value `⊤` in `classStr P` under `e` iff
its relativisation to `P` holds. -/
theorem val_classStr_eq_top_iff (P : ZFSet → Prop) (φ : Formula LSet) (e : Nat → {z // P z}) :
    (classStr P).val e φ = ⊤ ↔ RSat P (fun n => (e n).1) φ :=
  (prop_eq_top_iff _).trans (val_classStr_iff P φ e)

end Foundations.Constructible
