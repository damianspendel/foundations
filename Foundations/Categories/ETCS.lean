import Foundations.Categories.Topos
import Foundations.Numbers.Peano

/-!
# ETCS: the elementary theory of the category of sets

In *An elementary theory of the category of sets* (1964) F. William Lawvere proposed
a foundation for mathematics that speaks not of membership but of functions. Its
axioms describe a category, and say that it looks like "the" category of sets:

1. it is a **topos** — finite limits, exponentials (function sets), a subobject
   classifier `Ω` (power sets);
2. it is **well-pointed** — arrows are determined by their effect on *elements*,
   where an element of `X` is an arrow `1 ⟶ X` (extensionality); and it is
   non-degenerate (`Ω` has two distinct elements);
3. it has a **natural numbers object** — an object `N` with `0 : 1 ⟶ N` and
   `s : N ⟶ N` through which every "sequence" `x : 1 ⟶ X`, `f : X ⟶ X` is defined by a
   unique recursion `h(0) = x`, `h(n+1) = f(h(n))` (infinity);
4. **choice** — every epimorphism (surjection) has a section.

In ETCS a set has no "internal" structure at all: an element is just an arrow from the
one-point set, and two sets with the same number of elements are indistinguishable.
What a set *is* is exhausted by its place in the web of functions. This is the
**structuralist** foundation par excellence (Lawvere, McLarty, Awodey), and the result
is mathematically robust: ETCS is equiconsistent with a modest fragment of ZF (bounded
Zermelo set theory with choice); adding a replacement schema brings it up to ZFC.

**Contrast with Part I.** In Part I we built a model of ZF inside Lean following Aczel:
a set is a well-founded *tree* (`PSet`: an index type and a family of members) taken up
to extensional equivalence. There, membership `x ∈ y` is a global relation between any
two sets, and the von Neumann numeral `2 = {∅, {∅}}` has members with properties
irrelevant to arithmetic ("`∅ ∈ 2`"). Paul Benacerraf (*What numbers could not be*,
1965) took such accidents to show that numbers cannot be sets at all. ETCS answers him:
the natural numbers are *any* natural numbers object, and we prove below that **any two
natural numbers objects are isomorphic by a unique isomorphism respecting zero and
successor** — a categorical form of Dedekind's categoricity theorem. In particular the
Peano numbers built from scratch in Part II and Lean's own `Nat` are both natural
numbers objects in the topos of types, and hence canonically the same.

Here we state the ETCS axioms as a structure on a topos and show that the **category of
Lean types is a model**. (Choice and the subobject classifier use `Classical.choice`.)
-/

namespace Foundations.Categories

universe v u

open Category CartesianClosed

/-- An **epimorphism**: an arrow that can be cancelled on the right of composites (the
categorical notion of surjectivity). -/
structure Epi {C : Type u} [Category.{v} C] {X Y : C} (e : X ⟶ Y) : Prop where
  /-- Right cancellation. -/
  cancel : ∀ {Z : C} (g h : Y ⟶ Z), e ≫ g = e ≫ h → g = h

/-! ## Natural numbers objects -/

section NNO

variable {C : Type u} [Category.{v} C]

/-- A **natural numbers object** (Lawvere): `z : T ⟶ N` and `s : N ⟶ N` such that for every
`x : T ⟶ X` and `f : X ⟶ X` there is exactly one `h : N ⟶ X` with `z ≫ h = x` and
`s ≫ h = h ≫ f` — definition by primitive recursion. -/
structure IsNNO (T N : C) (z : T ⟶ N) (s : N ⟶ N) where
  /-- The arrow defined by recursion. -/
  ind : {X : C} → (T ⟶ X) → (X ⟶ X) → (N ⟶ X)
  /-- `h(0) = x`. -/
  ind_zero : ∀ {X : C} (x : T ⟶ X) (f : X ⟶ X), z ≫ ind x f = x
  /-- `h(n + 1) = f(h(n))`. -/
  ind_succ : ∀ {X : C} (x : T ⟶ X) (f : X ⟶ X), s ≫ ind x f = ind x f ≫ f
  /-- Uniqueness of the recursively defined arrow. -/
  uniq : ∀ {X : C} (x : T ⟶ X) (f : X ⟶ X) (h : N ⟶ X), z ≫ h = x → s ≫ h = h ≫ f →
    h = ind x f

namespace IsNNO

variable {T N N' : C} {z : T ⟶ N} {s : N ⟶ N} {z' : T ⟶ N'} {s' : N' ⟶ N'}

/-- **Proof by induction**, categorically: two arrows out of `N` that satisfy the same
recursion equations are equal. -/
theorem hom_ext (hN : IsNNO T N z s) {X : C} (f : X ⟶ X) {h k : N ⟶ X} (h₀ : z ≫ h = z ≫ k)
    (hh : s ≫ h = h ≫ f) (hk : s ≫ k = k ≫ f) : h = k :=
  (hN.uniq _ f h h₀ hh).trans (hN.uniq _ f k rfl hk).symm

/-- **Natural numbers objects are unique up to isomorphism** (Dedekind's categoricity
theorem, categorically): the comparison maps are defined by recursion. -/
def uniqueIso (hN : IsNNO T N z s) (hN' : IsNNO T N' z' s') : N ≅ N' where
  hom := hN.ind z' s'
  inv := hN'.ind z s
  hom_inv_id := hN.hom_ext s
    (by rw [← assoc, hN.ind_zero, hN'.ind_zero, comp_id])
    (by rw [← assoc, hN.ind_succ, assoc, hN'.ind_succ, assoc])
    (by rw [comp_id, id_comp])
  inv_hom_id := hN'.hom_ext s'
    (by rw [← assoc, hN'.ind_zero, hN.ind_zero, comp_id])
    (by rw [← assoc, hN'.ind_succ, assoc, hN.ind_succ, assoc])
    (by rw [comp_id, id_comp])

/-- The comparison isomorphism preserves zero and successor. -/
theorem uniqueIso_hom (hN : IsNNO T N z s) (hN' : IsNNO T N' z' s') :
    z ≫ (uniqueIso hN hN').hom = z' ∧ s ≫ (uniqueIso hN hN').hom = (uniqueIso hN hN').hom ≫ s' :=
  ⟨hN.ind_zero _ _, hN.ind_succ _ _⟩

/-- **…and it is the only arrow `N ⟶ N'` preserving zero and successor.** -/
theorem uniqueIso_unique (hN : IsNNO T N z s) (hN' : IsNNO T N' z' s') (h : N ⟶ N')
    (h₀ : z ≫ h = z') (h₁ : s ≫ h = h ≫ s') : h = (uniqueIso hN hN').hom :=
  hN.uniq _ _ h h₀ h₁

end IsNNO

end NNO

/-! ## The axioms of ETCS -/

/-- **Lawvere's elementary theory of the category of sets** (ETCS), as a structure on a
topos: well-pointedness, non-degeneracy, a natural numbers object, and the axiom of choice
(every epimorphism splits). -/
structure ETCS (C : Type u) [Category.{v} C] [Topos C] where
  /-- **Well-pointedness** (extensionality): arrows agreeing on all elements `1 ⟶ X` are
  equal. -/
  wellPointed : ∀ {X Y : C} (f g : X ⟶ Y), (∀ x : (one : C) ⟶ X, x ≫ f = x ≫ g) → f = g
  /-- **Non-degeneracy**: there are two distinct truth values. -/
  nondegenerate : ∃ p q : (one : C) ⟶ Topos.Ω, p ≠ q
  /-- The natural numbers. -/
  N : C
  /-- Zero. -/
  zero : (one : C) ⟶ N
  /-- Successor. -/
  succ : N ⟶ N
  /-- **Infinity**: `N` is a natural numbers object. -/
  nno : IsNNO one N zero succ
  /-- **Choice**: every epimorphism has a section. -/
  choice : ∀ {X Y : C} (e : X ⟶ Y), Epi e → ∃ s : Y ⟶ X, s ≫ e = 𝟙 Y

/-! ## The category of types is a model of ETCS -/

/-- Iterating `f` `n` times on `x`. -/
def iterNat {X : Type} (x : X) (f : X → X) : Nat → X
  | 0 => x
  | n + 1 => f (iterNat x f n)

/-- **Lean's `Nat` is a natural numbers object** in the topos of types. -/
def natNNO : IsNNO (C := Type) PUnit Nat (fun _ => 0) Nat.succ where
  ind x f := iterNat (x PUnit.unit) f
  ind_zero _ _ := funext fun u => by cases u; rfl
  ind_succ _ _ := rfl
  uniq x f h h₀ h₁ := funext fun n => by
    induction n with
    | zero => exact congrFun h₀ PUnit.unit
    | succ n ih =>
      show h (n + 1) = f (iterNat (x PUnit.unit) f n)
      rw [← ih]; exact congrFun h₁ n

/-- In the category of types, an epimorphism is surjective (test it against the two maps
`y ↦ True` and `y ↦ (y is in the image)` into `Prop`). -/
theorem types_epi_surjective {X Y : Type} {e : X ⟶ Y} (he : Epi e) (y : Y) : ∃ x, e x = y := by
  have := he.cancel (Z := Prop) (fun _ => True) (fun y => ∃ x, e x = y)
    (funext fun x => (eq_true ⟨x, rfl⟩).symm)
  exact of_eq_true (congrFun this y).symm

/-- **The category of types is a model of ETCS**: it is a topos, well-pointed (functions
are determined by their values), non-degenerate (`True ≠ False`), has `Nat` as natural
numbers object, and satisfies choice (surjections have sections, by `Classical.choice`). -/
noncomputable def typesETCS : ETCS Type where
  wellPointed f g h := funext fun a => congrFun (h fun _ => a) PUnit.unit
  nondegenerate := ⟨Topos.truth, typesFalse, fun h => by
    have := congrFun h PUnit.unit
    change True = False at this
    exact this ▸ trivial⟩
  N := Nat
  zero := fun _ => 0
  succ := Nat.succ
  nno := natNNO
  choice e he := ⟨fun y => Classical.choose (types_epi_surjective he y),
    funext fun y => Classical.choose_spec (types_epi_surjective he y)⟩

/-! ## Benacerraf's problem, dissolved -/

open Foundations.Numbers in
/-- Iterating `f` along the from-scratch Peano numbers of Part II. -/
def iterN {X : Type} (x : X) (f : X → X) : N → X
  | .zero => x
  | .succ n => f (iterN x f n)

open Foundations.Numbers in
/-- **The from-scratch Peano numbers of Part II form a natural numbers object** in the
topos of types. -/
def peanoNNO : IsNNO (C := Type) PUnit N (fun _ => .zero) N.succ where
  ind x f := iterN (x PUnit.unit) f
  ind_zero _ _ := funext fun u => by cases u; rfl
  ind_succ _ _ := rfl
  uniq x f h h₀ h₁ := funext fun n => by
    induction n with
    | zero => exact congrFun h₀ PUnit.unit
    | succ n ih =>
      show h (.succ n) = f (iterN (x PUnit.unit) f n)
      rw [← ih]; exact congrFun h₁ n

open Foundations.Numbers in
/-- **The Peano numbers and Lean's `Nat` are canonically isomorphic**, as natural numbers
objects: the comparison map, defined by recursion, sends `zero` to `0` and commutes with
successor, and it is the only map doing so. For the structuralist this is the whole truth
about "which objects the natural numbers are": any NNO will do, and all are uniquely
identified. -/
def peanoNatIso : (N : Type) ≅ Nat := IsNNO.uniqueIso peanoNNO natNNO

open Foundations.Numbers in
/-- The canonical isomorphism sends `zero` to `0` and `succ n` to its image plus one. -/
theorem peanoNatIso_spec (n : N) :
    peanoNatIso.hom N.zero = 0 ∧ peanoNatIso.hom (N.succ n) = peanoNatIso.hom n + 1 :=
  ⟨rfl, rfl⟩

end Foundations.Categories
