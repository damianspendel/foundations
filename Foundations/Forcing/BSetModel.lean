import Foundations.Forcing.BSet
import Foundations.Forcing.BooleanSoundness

/-!
# `V^B` as a Boolean-valued model of set theory

The previous file built names and their Boolean equality and membership. Here we package
them as a Boolean-valued structure `VB B` for the first-order **language of set theory**
`LSet` (one binary relation symbol `∈`, no function symbols), so that the general
Boolean-valued semantics of `BooleanSemantics` applies to arbitrary set-theoretic
formulas. We then verify that the following axioms of ZF have truth value `⊤` in `V^B`, for
**every** complete Boolean algebra `B`:

* **Extensionality** `∀x ∀y (∀z (z ∈ x ↔ z ∈ y) → x = y)`;
* **Empty set** `∃x ∀y ¬(y ∈ x)`;
* **Pairing** `∀x ∀y ∃z ∀w (w ∈ z ↔ w = x ∨ w = y)`;
* **Union** `∀x ∃u ∀w (w ∈ u ↔ ∃y (y ∈ x ∧ w ∈ y))`;
* the **Separation scheme** `∀x ∃s ∀z (z ∈ s ↔ z ∈ x ∧ φ(z))`, for every formula `φ`, with
  arbitrary parameters;
* the **∈-induction scheme** `∀x ((∀y ∈ x) φ(y) → φ(x)) → ∀x φ(x)`, for every formula `φ`
  (the form of Foundation used in ZF without choice).

Separation and ∈-induction hold for *all* formulas because of the congruence lemma of
`BooleanSemantics`: every formula is extensional for Boolean equality. The witness for
separation is the name `{(Aᵢ, bᵢ ⊓ ⟦φ(Aᵢ)⟧)}`, a direct Boolean analogue of
`{a ∈ x | φ(a)}`.

Combined with soundness, every first-order consequence of these axioms has value `⊤` in
`V^B` (`VB_val_eq_top_of_proves`). The remaining ZF axioms (power set, infinity and
collection) are verified in the next file, `BSetZF`. The axiom of choice is not treated.
-/

namespace Foundations.Forcing

open Foundations.Logic.FO CBA BStructure

/-- **The language of set theory**: no function symbols and a single binary relation
symbol `∈` (a relation symbol of arity `n` is a proof that `n = 2`). -/
def LSet : Signature where
  Func _ := Empty
  Rel n := PLift (n = 2)

/-- The argument list `[t, s]`. -/
def memArgs (t s : Term LSet) : Fin 2 → Term LSet := fun i => if i.val = 0 then t else s

/-- The atomic formula `t ∈ s`. -/
def memF (t s : Term LSet) : Formula LSet := .rel (n := 2) ⟨rfl⟩ (memArgs t s)

/-- The biconditional `φ ↔ ψ`, as `(φ → ψ) ∧ (ψ → φ)`. -/
def iffF {L : Signature} (φ ψ : Formula L) : Formula L := .conj (.imp φ ψ) (.imp ψ φ)

/-- Shorthand for the de Bruijn variable `n`. -/
abbrev v (n : Nat) : Term LSet := .var n

variable {B : Type} [CompleteBooleanAlgebra B]

/-- **The Boolean-valued universe as a structure.** Domain: the names `BSet B`; equality and
membership: their Boolean values. -/
abbrev VB (B : Type) [CompleteBooleanAlgebra B] : BStructure.{0, 1} LSet B where
  Dom := BSet B
  funcs f _ := nomatch f
  rels R a := BSet.mem (a ⟨0, by have := R.down; omega⟩) (a ⟨1, by have := R.down; omega⟩)
  eq := BSet.eq
  eq_refl := BSet.eq_self
  eq_symm := BSet.eq_symm
  eq_trans := BSet.eq_trans
  funcs_congr f _ _ := nomatch f
  rels_congr R a b := le_trans'
    (le_inf _ _ _ (le_inf _ _ _ (inf_le_of_left_le (iInf_le _ _)) (inf_le_of_left_le (iInf_le _ _)))
      (inf_le_right _ _))
    (BSet.mem_congr _ _ _ _)

/-- The truth value of `t ∈ s` in `V^B` is Boolean membership of the values. -/
theorem val_memF (e : Nat → BSet B) (t s : Term LSet) :
    (VB B).val e (memF t s) = BSet.mem ((VB B).evalT e t) ((VB B).evalT e s) := rfl

/-- The truth value of `φ ↔ ψ` is the biimplication of the truth values. -/
theorem val_iffF (e : Nat → BSet B) (φ ψ : Formula LSet) :
    (VB B).val e (iffF φ ψ) = ((VB B).val e φ ⇔ (VB B).val e ψ) := rfl

/-! ### Extensionality, empty set, pairing, union -/

/-- The axiom of extensionality `∀x ∀y (∀z (z ∈ x ↔ z ∈ y) → x = y)`. -/
def axExt : Formula LSet :=
  .all (.all (.imp (.all (iffF (memF (v 0) (v 2)) (memF (v 0) (v 1)))) (.eq (v 1) (v 0))))

/-- **Extensionality holds in `V^B`.** `⟦Extensionality⟧ = ⊤`. -/
theorem VB_ext (e : Nat → BSet B) : (VB B).val e axExt = ⊤ :=
  eq_top_iff.2 <| le_iInf fun x => le_iInf fun y => le_himp_iff.2 <|
    inf_le_of_right_le (BSet.iInf_biimp_le_eq x y)

/-- The empty name, with no members. -/
def BSet.empty : BSet B := .mk Empty Empty.elim Empty.elim

/-- Nothing belongs to the empty name. -/
theorem BSet.mem_empty (y : BSet B) : BSet.mem y BSet.empty = ⊥ :=
  eq_bot_iff.2 (iSup_le fun i => i.elim)

/-- The empty-set axiom `∃x ∀y ¬(y ∈ x)`. -/
def axEmpty : Formula LSet := .ex (.all (Formula.neg (memF (v 0) (v 1))))

/-- **The empty-set axiom holds in `V^B`.** -/
theorem VB_empty (e : Nat → BSet B) : (VB B).val e axEmpty = ⊤ :=
  eq_top_iff.2 <| le_iSup_of_le BSet.empty <| le_iInf fun y => le_himp_iff.2 <|
    inf_le_of_right_le (by
      show BSet.mem y BSet.empty ≤ ⊥
      rw [BSet.mem_empty]; exact le_rfl)

/-- The unordered pair `{x, y}` of names, both members with degree `⊤`. -/
def BSet.pair (x y : BSet B) : BSet B := .mk Bool (fun b => cond b x y) (fun _ => ⊤)

/-- Membership in a pair: `⟦w ∈ {x, y}⟧ = ⟦w = x⟧ ⊔ ⟦w = y⟧`. -/
theorem BSet.mem_pair (w x y : BSet B) : BSet.mem w (BSet.pair x y) = BSet.eq w x ⊔ BSet.eq w y :=
  le_antisymm'
    (iSup_le fun b => by
      cases b
      · exact inf_le_of_right_le (le_sup_right _ _)
      · exact inf_le_of_right_le (le_sup_left _ _))
    (sup_le _ _ _ (le_iSup_of_le true (by show _ ≤ ⊤ ⊓ _; rw [top_inf]; exact le_rfl))
      (le_iSup_of_le false (by show _ ≤ ⊤ ⊓ _; rw [top_inf]; exact le_rfl)))

/-- The pairing axiom `∀x ∀y ∃z ∀w (w ∈ z ↔ w = x ∨ w = y)`. -/
def axPair : Formula LSet :=
  .all (.all (.ex (.all (iffF (memF (v 0) (v 1)) (.disj (.eq (v 0) (v 3)) (.eq (v 0) (v 2)))))))

/-- A biimplication between equal truth values is `⊤`. -/
theorem top_le_biimp_self (a : B) : ⊤ ≤ (a ⇔ a) :=
  le_inf _ _ _ (le_himp_iff.2 (inf_le_right _ _)) (le_himp_iff.2 (inf_le_right _ _))

/-- **The pairing axiom holds in `V^B`.** -/
theorem VB_pair (e : Nat → BSet B) : (VB B).val e axPair = ⊤ :=
  eq_top_iff.2 <| le_iInf fun x => le_iInf fun y => le_iSup_of_le (BSet.pair x y) <|
    le_iInf fun w => by
      show ⊤ ≤ (BSet.mem w (BSet.pair x y) ⇔ BSet.eq w x ⊔ BSet.eq w y)
      rw [BSet.mem_pair]; exact top_le_biimp_self _

/-- The union `⋃x` of a name: indexed by pairs (member of `x`, member of that member), with
degree the meet of the two degrees. -/
def BSet.sUnion (x : BSet B) : BSet B :=
  .mk (Σ i : x.type, (x.func i).type) (fun p => (x.func p.1).func p.2)
    (fun p => x.bval p.1 ⊓ (x.func p.1).bval p.2)

/-- Membership in a union: `⟦w ∈ ⋃x⟧ = ⨆_y (⟦y ∈ x⟧ ⊓ ⟦w ∈ y⟧)`. -/
theorem BSet.mem_sUnion (w x : BSet B) :
    BSet.mem w (BSet.sUnion x) = iSup fun y => BSet.mem y x ⊓ BSet.mem w y := by
  apply le_antisymm'
  · refine iSup_le fun ⟨i, j⟩ => le_iSup_of_le (x.func i) (le_inf _ _ _ ?_ ?_)
    · exact le_trans' (by show _ ≤ x.bval i; lattice_le) (BSet.bval_le_mem x i)
    · exact le_iSup_of_le j (by show _ ⊓ _ ⊓ _ ≤ _; lattice_le)
  · refine iSup_le fun y => le_trans' iSup_inf_le (iSup_le fun i => ?_)
    calc x.bval i ⊓ BSet.eq y (x.func i) ⊓ BSet.mem w y
        ≤ x.bval i ⊓ (BSet.eq y (x.func i) ⊓ BSet.mem w y) := by lattice_le
      _ ≤ x.bval i ⊓ BSet.mem w (x.func i) := inf_le_inf le_rfl (BSet.mem_congr_right _ _ _)
      _ ≤ iSup (fun j => x.bval i ⊓ ((x.func i).bval j ⊓ BSet.eq w ((x.func i).func j))) :=
          inf_iSup_le
      _ ≤ _ := iSup_le fun j => le_iSup_of_le (⟨i, j⟩ : Σ i : x.type, (x.func i).type)
          (by show _ ≤ (x.bval i ⊓ (x.func i).bval j) ⊓ _; lattice_le)

/-- The union axiom `∀x ∃u ∀w (w ∈ u ↔ ∃y (y ∈ x ∧ w ∈ y))`. -/
def axUnion : Formula LSet :=
  .all (.ex (.all (iffF (memF (v 0) (v 1)) (.ex (.conj (memF (v 0) (v 3)) (memF (v 1) (v 0)))))))

/-- **The union axiom holds in `V^B`.** -/
theorem VB_union (e : Nat → BSet B) : (VB B).val e axUnion = ⊤ :=
  eq_top_iff.2 <| le_iInf fun x => le_iSup_of_le (BSet.sUnion x) <| le_iInf fun w => by
    show ⊤ ≤ (BSet.mem w (BSet.sUnion x) ⇔ iSup fun y => BSet.mem y x ⊓ BSet.mem w y)
    rw [BSet.mem_sUnion]; exact top_le_biimp_self _

/-! ### The separation and ∈-induction schemes -/

/-- The separation axiom for `φ` (whose variable `0` is the element tested and whose other
free variables are parameters): `∀x ∃s ∀z (z ∈ s ↔ z ∈ x ∧ φ(z))`. -/
def axSep (φ : Formula LSet) : Formula LSet :=
  .all (.ex (.all (iffF (memF (v 0) (v 1)) (.conj (memF (v 0) (v 2)) (liftBy 2 φ)))))

/-- The separated name `{(Aᵢ, bᵢ ⊓ ⟦φ(Aᵢ)⟧)}`, a Boolean analogue of `{a ∈ x | φ(a)}`. -/
def BSet.sep (φ : Formula LSet) (e : Nat → BSet B) (x : BSet B) : BSet B :=
  .mk x.type x.func (fun i => x.bval i ⊓ (VB B).val (BEnv.cons (x.func i) e) φ)

/-- Membership in a separated name: `⟦z ∈ {a ∈ x | φ(a)}⟧ = ⟦z ∈ x⟧ ⊓ ⟦φ(z)⟧`. -/
theorem BSet.mem_sep (φ : Formula LSet) (e : Nat → BSet B) (x z : BSet B) :
    BSet.mem z (BSet.sep φ e x) = BSet.mem z x ⊓ (VB B).val (BEnv.cons z e) φ := by
  have leib := fun (a b : BSet B) => eq_inf_val_cons_le (M := VB B) φ e a b
  apply le_antisymm'
  · refine iSup_le fun i => le_inf _ _ _ (le_iSup_of_le i (by show _ ⊓ _ ⊓ _ ≤ _; lattice_le)) ?_
    show (x.bval i ⊓ _) ⊓ BSet.eq z (x.func i) ≤ _
    refine le_trans' ?_ (leib (x.func i) z)
    exact le_inf _ _ _ (inf_le_of_right_le (BSet.eq_symm _ _)) (by lattice_le)
  · refine le_trans' iSup_inf_le (iSup_mono fun i => ?_)
    show _ ≤ (x.bval i ⊓ _) ⊓ BSet.eq z (x.func i)
    refine le_inf _ _ _ (le_inf _ _ _ (by lattice_le) ?_) (by lattice_le)
    exact le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (leib z (x.func i))

/-- **The separation scheme holds in `V^B`**, for every formula `φ` and every choice of
parameters `e`. -/
theorem VB_sep (φ : Formula LSet) (e : Nat → BSet B) : (VB B).val e (axSep φ) = ⊤ :=
  eq_top_iff.2 <| le_iInf fun x => le_iSup_of_le (BSet.sep φ e x) <| le_iInf fun z => by
    show ⊤ ≤ (BSet.mem z (BSet.sep φ e x) ⇔ BSet.mem z x ⊓ (VB B).val _ (liftBy 2 φ))
    rw [val_liftBy 2 φ z _ e (fun _ => rfl), BSet.mem_sep]; exact top_le_biimp_self _

/-- The ∈-induction axiom for `φ` (variable `0` distinguished, other variables parameters):
`∀x (∀y (y ∈ x → φ(y)) → φ(x)) → ∀x φ(x)`. -/
def axInd (φ : Formula LSet) : Formula LSet :=
  .imp (.all (.imp (.all (.imp (memF (v 0) (v 1)) (liftBy 1 φ))) φ)) (.all φ)

/-- **The ∈-induction scheme holds in `V^B`**, for every formula `φ` and parameters `e`.
The proof is by induction on names: if `a` is the value of the hypothesis and `a ≤ ⟦φ(Aᵢ)⟧`
for every listed member `Aᵢ` of `x`, then `a ≤ ⟦∀y ∈ x φ(y)⟧` by the congruence lemma, so
`a ≤ ⟦φ(x)⟧`. -/
theorem VB_ind (φ : Formula LSet) (e : Nat → BSet B) : (VB B).val e (axInd φ) = ⊤ := by
  apply eq_top_iff.2
  apply le_himp_iff.2
  rw [top_inf]
  let a : B := iInf fun x : BSet B =>
    iInf (fun y : BSet B => BSet.mem y x ⇨ (VB B).val (BEnv.cons y e) φ) ⇨
      (VB B).val (BEnv.cons x e) φ
  have ha : (VB B).val e (.all (.imp (.all (.imp (memF (v 0) (v 1)) (liftBy 1 φ))) φ)) = a := by
    show iInf (fun x : BSet B => iInf (fun y : BSet B => BSet.mem y x ⇨
      (VB B).val (BEnv.cons y (BEnv.cons x e)) (liftBy 1 φ)) ⇨ _) = a
    have hl : ∀ x y : BSet B, (VB B).val (BEnv.cons y (BEnv.cons x e)) (liftBy 1 φ) =
        (VB B).val (BEnv.cons y e) φ := fun x y => val_liftBy (M := VB B) 1 φ y (BEnv.cons x e) e (fun _ => rfl)
    simp only [hl]; rfl
  rw [ha]
  refine le_iInf fun x => ?_
  induction x with
  | mk α A b ih =>
    have hall : a ≤ iInf fun y : BSet B => BSet.mem y (.mk α A b) ⇨ (VB B).val (BEnv.cons y e) φ :=
      le_iInf fun y => le_himp_iff.2 <| by
        refine le_trans' inf_iSup_le (iSup_le fun i => ?_)
        show a ⊓ (b i ⊓ BSet.eq y (A i)) ≤ _
        refine le_trans' ?_ (eq_inf_val_cons_le (M := VB B) φ e (A i) y)
        exact le_inf _ _ _ (inf_le_of_right_le (inf_le_of_right_le (BSet.eq_symm _ _)))
          (inf_le_of_left_le (ih i))
    exact le_trans' (le_inf _ _ _ (iInf_le _ (BSet.mk α A b)) hall) himp_inf_le

/-! ### The fragment of ZF verified in `V^B` -/

/-- The fragment of ZF verified here: extensionality, empty set, pairing, union, and all
instances of separation and of ∈-induction. The scheme instances are open formulas (their
free variables are parameters); their universal closures `∀ⁿ` are included as well, so that
derivability from `ZFFrag` is at least as strong as from the textbook closed axioms. -/
def ZFFrag : Theory LSet := fun ψ =>
  ψ = axExt ∨ ψ = axEmpty ∨ ψ = axPair ∨ ψ = axUnion ∨ (∃ φ n, ψ = allN (axSep φ) n) ∨
    (∃ φ n, ψ = allN (axInd φ) n)

/-- **`V^B` is a Boolean-valued model of the fragment `ZFFrag`.** For every complete Boolean
algebra `B` and every environment, each axiom of `ZFFrag` has truth value `⊤` in `V^B`. -/
theorem VB_models_ZFFrag (e : Nat → BSet B) : ∀ ψ, ZFFrag ψ → (VB B).val e ψ = ⊤ := by
  rintro ψ (rfl | rfl | rfl | rfl | ⟨φ, n, rfl⟩ | ⟨φ, n, rfl⟩)
  · exact VB_ext e
  · exact VB_empty e
  · exact VB_pair e
  · exact VB_union e
  · exact val_allN_eq_top (M := VB B) (VB_sep φ) n e
  · exact val_allN_eq_top (M := VB B) (VB_ind φ) n e

/-- **Every consequence of `ZFFrag` is true in `V^B`.** By Boolean soundness, anything
derivable from extensionality, empty set, pairing, union, separation and ∈-induction has
truth value `⊤` in `V^B`, for every complete Boolean algebra `B`. -/
theorem VB_val_eq_top_of_proves {φ : Formula LSet} (h : ZFFrag ⊢₁ φ) (e : Nat → BSet B) :
    (VB B).val e φ = ⊤ :=
  val_eq_top_of_theory h (VB B) e (VB_models_ZFFrag e)

end Foundations.Forcing
