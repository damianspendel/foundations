import Foundations.Algebra.Group

/-!
# Categories, functors and natural transformations

Category theory was introduced by Samuel Eilenberg and Saunders Mac Lane in
*General Theory of Natural Equivalences* (1945). They wanted to say precisely
what it means for an isomorphism to be *natural* — like the isomorphism between
a finite-dimensional vector space and its double dual, which (unlike the one
with its dual) needs no choice of basis. To define "natural transformation" they
needed "functor", and to define functor, "category". Grothendieck then made
categories the working language of algebraic geometry, and Lawvere proposed them
as a *foundation* for mathematics, rivalling set theory.

A **category** consists of objects and, for any two objects `X`, `Y`, a
collection of *morphisms* (arrows) `X ⟶ Y`, with identities `𝟙 X` and an
associative composition `f ≫ g` ("first `f`, then `g`"). That is all.
Nothing is said about what objects *are*: there is no membership relation, no
looking inside. An object is characterized only by its arrows to and from other
objects. This is the **structuralist** reading of mathematics (Benacerraf, Shapiro,
Awodey): mathematical objects are positions in structures, known through their
relations. In set-theoretic foundations, by contrast, the natural number `2` is a
particular set (`{∅, {∅}}` in von Neumann's coding of Part I), with "accidental"
properties such as `∅ ∈ 2`; categorically, `2` is known only up to unique
isomorphism, through its universal property.

A **functor** `F : C ⥤ D` maps objects to objects and arrows to arrows,
preserving identities and composition — a structure-preserving map of
structures. A **natural transformation** `α : F ⟶ G` is a family of arrows
`α_X : F X ⟶ G X` compatible with every arrow of `C`.

Examples in this file: the category of types and functions (Lean's own
"sets"); any preorder (at most one arrow `a ⟶ b`, namely the fact `a ≤ b`);
any monoid, and in particular any group, as a category with *one* object (the
arrows are the elements); the category of groups and homomorphisms from Part IV;
and the opposite of any category.
-/

namespace Foundations.Categories

universe v v₁ v₂ v₃ u u₁ u₂ u₃

/-- A **category**: objects (the type `C`), morphisms `Hom X Y` between any two objects,
identities and an associative composition `comp f g` ("first `f`, then `g`") with the
identities as units. -/
class Category (C : Type u) where
  /-- The morphisms from `X` to `Y`. -/
  Hom : C → C → Type v
  /-- The identity morphism of `X`. -/
  id : (X : C) → Hom X X
  /-- Composition in diagrammatic order: `comp f g` is "first `f`, then `g`". -/
  comp : {X Y Z : C} → Hom X Y → Hom Y Z → Hom X Z
  /-- The identity is a left unit. -/
  id_comp : ∀ {X Y : C} (f : Hom X Y), comp (id X) f = f
  /-- The identity is a right unit. -/
  comp_id : ∀ {X Y : C} (f : Hom X Y), comp f (id Y) = f
  /-- Composition is associative. -/
  assoc : ∀ {W X Y Z : C} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

/-- `X ⟶ Y`: the morphisms from `X` to `Y`. -/
scoped infixr:10 " ⟶ " => Category.Hom
/-- `f ≫ g`: first `f`, then `g`. -/
scoped infixr:80 " ≫ " => Category.comp
/-- `𝟙 X`: the identity morphism. -/
scoped notation "𝟙" => Category.id

attribute [simp] Category.id_comp Category.comp_id Category.assoc

open Category

/-! ## Isomorphisms -/

section Iso

variable {C : Type u} [Category.{v} C]

/-- An **isomorphism** between `X` and `Y`: arrows both ways composing to the identities. -/
structure Iso (X Y : C) where
  /-- The forward arrow. -/
  hom : X ⟶ Y
  /-- The backward arrow. -/
  inv : Y ⟶ X
  /-- Forward then backward is the identity. -/
  hom_inv_id : hom ≫ inv = 𝟙 X
  /-- Backward then forward is the identity. -/
  inv_hom_id : inv ≫ hom = 𝟙 Y

/-- `X ≅ Y`: the isomorphisms from `X` to `Y`. -/
scoped infixr:10 " ≅ " => Iso

/-- Isomorphisms with the same forward arrow are equal (the inverse is determined). -/
theorem Iso.ext {X Y : C} {i j : X ≅ Y} (h : i.hom = j.hom) : i = j := by
  cases i with
  | mk f g hfg hgf =>
    cases j with
    | mk f' g' hfg' hgf' =>
      simp only at h
      subst h
      have : g = g' := by
        calc g = g ≫ 𝟙 X := by simp
          _ = g ≫ (f ≫ g') := by rw [hfg']
          _ = (g ≫ f) ≫ g' := by simp
          _ = g' := by rw [hgf]; simp
      subst this
      rfl

/-- The identity isomorphism. -/
def Iso.refl (X : C) : X ≅ X := ⟨𝟙 X, 𝟙 X, by simp, by simp⟩

/-- The inverse isomorphism. -/
def Iso.symm {X Y : C} (i : X ≅ Y) : Y ≅ X := ⟨i.inv, i.hom, i.inv_hom_id, i.hom_inv_id⟩

/-- The composite of isomorphisms. -/
def Iso.trans {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) : X ≅ Z where
  hom := i.hom ≫ j.hom
  inv := j.inv ≫ i.inv
  hom_inv_id := by
    rw [assoc, ← assoc j.hom, j.hom_inv_id, id_comp, i.hom_inv_id]
  inv_hom_id := by
    rw [assoc, ← assoc i.inv, i.inv_hom_id, id_comp, j.inv_hom_id]

end Iso

/-! ## Functors and natural transformations -/

/-- A **functor** from `C` to `D`: a map on objects and on arrows preserving identities
and composition. -/
structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] where
  /-- The action on objects. -/
  obj : C → D
  /-- The action on morphisms. -/
  map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y)
  /-- Identities are preserved. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)
  /-- Composition is preserved. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- `C ⥤ D`: the functors from `C` to `D`. -/
scoped infixr:26 " ⥤ " => Functor

attribute [simp] Functor.map_id Functor.map_comp

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- The identity functor. -/
def id (C : Type u₁) [Category.{v₁} C] : C ⥤ C where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The composite of two functors: first `F`, then `G`. -/
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  map_id X := by simp
  map_comp f g := by simp

/-- **Functors preserve isomorphisms.** -/
def mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  hom := F.map i.hom
  inv := F.map i.inv
  hom_inv_id := by rw [← F.map_comp, i.hom_inv_id, F.map_id]
  inv_hom_id := by rw [← F.map_comp, i.inv_hom_id, F.map_id]

end Functor

/-- A **natural transformation** `α : F ⟶ G` between functors `C ⥤ D`: arrows
`α_X : F X ⟶ G X` such that `F f ≫ α_Y = α_X ≫ G f` for every `f : X ⟶ Y`. -/
structure NatTrans {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F G : C ⥤ D) where
  /-- The component at `X`. -/
  app : (X : C) → (F.obj X ⟶ G.obj X)
  /-- The naturality square commutes. -/
  naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

namespace NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Natural transformations with the same components are equal. -/
theorem ext {F G : C ⥤ D} {α β : NatTrans F G} (h : ∀ X, α.app X = β.app X) : α = β := by
  cases α with
  | mk a na =>
    cases β with
    | mk b nb =>
      have : a = b := funext h
      subst this
      rfl

/-- The identity natural transformation. -/
def id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality f := by simp

/-- **Vertical composition** of natural transformations. -/
def vcomp {F G H : C ⥤ D} (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality f := by
    rw [← assoc, α.naturality, assoc, β.naturality, assoc]

end NatTrans

/-- A **natural isomorphism**: natural transformations both ways, inverse to each other. -/
structure NatIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F G : C ⥤ D) where
  /-- The forward transformation. -/
  hom : NatTrans F G
  /-- The backward transformation. -/
  inv : NatTrans G F
  /-- Forward then backward is the identity, componentwise. -/
  hom_inv_id : ∀ X, hom.app X ≫ inv.app X = 𝟙 (F.obj X)
  /-- Backward then forward is the identity, componentwise. -/
  inv_hom_id : ∀ X, inv.app X ≫ hom.app X = 𝟙 (G.obj X)

/-! ## Example: types and functions -/

/-- **The category of types**: objects are types, morphisms are functions. This is the
type-theoretic counterpart of the category of sets. -/
instance types : Category.{u} (Type u) where
  Hom X Y := X → Y
  id _ := fun x => x
  comp f g := fun x => g (f x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- In the category of types, composition is composition of functions. -/
theorem types_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := rfl

/-- In the category of types, the identity is the identity function. -/
theorem types_id_apply {X : Type u} (x : X) : (𝟙 X : X ⟶ X) x = x := rfl

/-- In the category of types, the isomorphisms are the bijections with given inverse. -/
def typesIsoOfInverse {X Y : Type u} (f : X → Y) (g : Y → X) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) : X ≅ Y :=
  ⟨f, g, funext hgf, funext hfg⟩

/-! ## Example: a preorder as a category -/

/-- A **preorder**: a reflexive and transitive relation. -/
class Preorder' (α : Type u) extends LE α where
  /-- Reflexivity. -/
  le_refl : ∀ a : α, a ≤ a
  /-- Transitivity. -/
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c

/-- A type synonym carrying the category structure of a preorder. -/
def PreCat (α : Type u) : Type u := α

/-- **A preorder is a category** with at most one arrow `a ⟶ b`, the proof of `a ≤ b`;
composition is transitivity. In such a *thin* category all diagrams commute. -/
instance PreCat.category (α : Type u) [Preorder' α] : Category.{0} (PreCat α) where
  Hom a b := PLift (@LE.le α _ a b)
  id a := ⟨Preorder'.le_refl (α := α) a⟩
  comp f g := ⟨Preorder'.le_trans (α := α) _ _ _ f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- In a preorder category, any two parallel arrows are equal. -/
theorem PreCat.hom_eq {α : Type u} [Preorder' α] {a b : PreCat α} (f g : a ⟶ b) : f = g := by
  cases f; cases g; rfl

/-- The natural numbers with `≤` form a preorder. -/
instance : Preorder' Nat where
  le_refl := Nat.le_refl
  le_trans _ _ _ := Nat.le_trans

/-- In a preorder category, isomorphic objects are mutually below each other. -/
theorem PreCat.iso_iff {α : Type u} [Preorder' α] (a b : PreCat α) :
    Nonempty (a ≅ b) ↔ (@LE.le α _ a b ∧ @LE.le α _ b a) :=
  ⟨fun ⟨i⟩ => ⟨i.hom.down, i.inv.down⟩,
   fun ⟨h₁, h₂⟩ => ⟨⟨⟨h₁⟩, ⟨h₂⟩, PreCat.hom_eq _ _, PreCat.hom_eq _ _⟩⟩⟩

/-! ## Example: a monoid as a one-object category -/

/-- A **monoid**: an associative multiplication with a two-sided unit. -/
class Monoid' (M : Type u) extends Mul M, One M where
  /-- Associativity. -/
  mul_assoc : ∀ a b c : M, a * b * c = a * (b * c)
  /-- `1` is a left unit. -/
  one_mul : ∀ a : M, 1 * a = a
  /-- `1` is a right unit. -/
  mul_one : ∀ a : M, a * 1 = a

/-- The one-object category of a monoid: a single object `⋆`. -/
structure SingleObj (M : Type u) where
  /-- The unique object. -/
  star ::

/-- **A monoid is a category with one object**: the arrows `⋆ ⟶ ⋆` are the elements, and
composition is multiplication (`f ≫ g = g * f`, as for composing functions). -/
instance SingleObj.category (M : Type u) [Monoid' M] : Category.{u} (SingleObj M) where
  Hom _ _ := M
  id _ := (1 : M)
  comp f g := (g * f : M)
  id_comp f := Monoid'.mul_one f
  comp_id f := Monoid'.one_mul f
  assoc f g h := (Monoid'.mul_assoc h g f).symm

/-- Every group is a monoid. -/
instance Monoid'.ofGroup (G : Type u) [Foundations.Algebra.Group G] : Monoid' G where
  mul_assoc := Foundations.Algebra.Group.mul_assoc
  one_mul := Foundations.Algebra.Group.one_mul
  mul_one := Foundations.Algebra.Group.mul_one

/-- **A group is a one-object category in which every arrow is an isomorphism** (a
*groupoid* with one object). -/
def SingleObj.isoOfGroup {G : Type u} [Foundations.Algebra.Group G]
    (g : (SingleObj.star : SingleObj G) ⟶ SingleObj.star) :
    (SingleObj.star : SingleObj G) ≅ SingleObj.star where
  hom := g
  inv := (g : G)⁻¹
  hom_inv_id := Foundations.Algebra.Group.inv_mul_cancel (g : G)
  inv_hom_id := Foundations.Algebra.Group.mul_inv_cancel (g : G)

/-! ## Example: the category of groups -/

open Foundations.Algebra in
/-- A **bundled group**: a type together with a group structure. -/
structure GroupCat where
  /-- The underlying type. -/
  carrier : Type u
  /-- The group structure. -/
  [str : Group carrier]

attribute [instance] GroupCat.str

open Foundations.Algebra in
/-- **The category of groups**, with group homomorphisms (Part IV) as arrows. -/
instance GroupCat.category : Category.{u} GroupCat.{u} where
  Hom G H := Foundations.Algebra.Hom G.carrier H.carrier
  id G := Foundations.Algebra.Hom.id G.carrier
  comp f g := Foundations.Algebra.Hom.comp g f
  id_comp _ := Foundations.Algebra.Hom.ext fun _ => rfl
  comp_id _ := Foundations.Algebra.Hom.ext fun _ => rfl
  assoc _ _ _ := Foundations.Algebra.Hom.ext fun _ => rfl

/-- The **forgetful functor** from groups to types: forget the multiplication. -/
def GroupCat.forget : GroupCat.{u} ⥤ Type u where
  obj G := G.carrier
  map f := fun x => f.toFun x
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## The opposite category -/

/-- The objects of the **opposite category** `Cᵒᵖ`: a copy of the objects of `C`. -/
structure Op (C : Type u) where
  /-- The underlying object of `C`. -/
  unop : C

/-- **The opposite category**: the same objects, with all arrows reversed. Every
categorical notion has a *dual*, obtained by passing to `Cᵒᵖ`. -/
instance Op.category (C : Type u) [Category.{v} C] : Category.{v} (Op C) where
  Hom X Y := Y.unop ⟶ X.unop
  id X := 𝟙 X.unop
  comp f g := g ≫ f
  id_comp _ := comp_id _
  comp_id _ := id_comp _
  assoc _ _ _ := (assoc _ _ _).symm

/-- Isomorphic objects of `C` are isomorphic in `Cᵒᵖ`. -/
def Iso.op {C : Type u} [Category.{v} C] {X Y : C} (i : X ≅ Y) : Op.mk X ≅ Op.mk Y where
  hom := i.inv
  inv := i.hom
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

end Foundations.Categories
