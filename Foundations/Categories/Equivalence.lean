import Foundations.Categories.GeneralLimits
import Foundations.Combinatorics.Pigeonhole

/-!
# Equivalences of categories

When are two categories "the same"? Asking for an *isomorphism* of categories —
functors `F : C ⥤ D` and `G : D ⥤ C` with `G ∘ F = id` and `F ∘ G = id` on the
nose — is too strict, because it compares objects by *equality*, and equality of
objects is exactly what category theory teaches us not to care about. The right
notion, the one mathematicians actually use, is an **equivalence**: functors `F`
and `G` with `G ∘ F` and `F ∘ G` merely *naturally isomorphic* to the identities.

Example. The category `FinSet` of finite types and all functions is huge: it has a
separate object for every finite type that can be written down, and many of them are
isomorphic (a two-element type of colours, the booleans, `Fin 2`, …). The category
`FinOrd` whose objects are just the natural numbers `0, 1, 2, …`, with the functions
`Fin m → Fin n` as arrows, is tiny by comparison. Yet the two are **equivalent**: the
inclusion `n ↦ Fin n` loses nothing that can be expressed in categorical terms.
`FinOrd` is a **skeleton** of `FinSet` — isomorphic objects in it are already equal
(we prove this with the pigeonhole principle of Part IX) — and it keeps exactly one
representative of each isomorphism class.

The characterisation theorem proved here says that a functor is (part of) an
equivalence **if and only if** it is

* **faithful** — it does not identify distinct arrows,
* **full** — every arrow between images is the image of an arrow, and
* **essentially surjective** — every object of the target is *isomorphic* to an
  image (not necessarily equal to one).

The converse direction must *choose*, for every object `Y` of `D`, some `X` with
`F X ≅ Y`, so it uses the axiom of choice (`Classical.choice`). This is a nice
illustration of how choice enters structural mathematics.

For a structuralist this is the precise sense in which only structure matters: any
property stated in the language of categories (objects, arrows, composition,
treated up to isomorphism) is invariant under equivalence. Notably, Lean's type
theory cannot prove that `Bool` and `Fin 2` are *different* types; it only knows
that they are isomorphic, which is all that matters categorically.
-/

namespace Foundations.Categories

universe v₁ v₂ u₁ u₂

open Category

section Lemmas

variable {C : Type u₁} [Category.{v₁} C]

/-- Cancelling an isomorphism inside a composite: `i.hom ≫ i.inv ≫ h = h`. -/
@[simp] theorem Iso.hom_inv_id_assoc {X Y Z : C} (i : X ≅ Y) (h : X ⟶ Z) :
    i.hom ≫ i.inv ≫ h = h := by rw [← assoc, i.hom_inv_id, id_comp]

/-- Cancelling an isomorphism inside a composite: `i.inv ≫ i.hom ≫ h = h`. -/
@[simp] theorem Iso.inv_hom_id_assoc {X Y Z : C} (i : X ≅ Y) (h : Y ⟶ Z) :
    i.inv ≫ i.hom ≫ h = h := by rw [← assoc, i.inv_hom_id, id_comp]

attribute [simp] Iso.hom_inv_id Iso.inv_hom_id

end Lemmas

/-- The inverse of a natural isomorphism. -/
def NatIso.symm {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : NatIso F G) : NatIso G F :=
  ⟨e.inv, e.hom, e.inv_hom_id, e.hom_inv_id⟩

/-- The component of a natural isomorphism at `X`, as an isomorphism. -/
def NatIso.app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : NatIso F G) (X : C) : F.obj X ≅ G.obj X :=
  ⟨e.hom.app X, e.inv.app X, e.hom_inv_id X, e.inv_hom_id X⟩

section Defs

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- An **equivalence of categories**: functors `F : C ⥤ D` and `G : D ⥤ C` together with
natural isomorphisms `X ≅ G (F X)` (the unit) and `F (G Y) ≅ Y` (the counit). (We list the
components and their naturality directly; `unitIso` and `counitIso` below repackage them
as natural isomorphisms `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭`.) -/
structure Equivalence (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] where
  /-- The forward functor. -/
  functor : C ⥤ D
  /-- The functor back. -/
  inverse : D ⥤ C
  /-- The unit isomorphisms `X ≅ G (F X)`. -/
  unit : (X : C) → (X ≅ inverse.obj (functor.obj X))
  /-- The counit isomorphisms `F (G Y) ≅ Y`. -/
  counit : (Y : D) → (functor.obj (inverse.obj Y) ≅ Y)
  /-- Naturality of the unit. -/
  unit_nat : ∀ {X X' : C} (f : X ⟶ X'),
    f ≫ (unit X').hom = (unit X).hom ≫ inverse.map (functor.map f)
  /-- Naturality of the counit. -/
  counit_nat : ∀ {Y Y' : D} (g : Y ⟶ Y'),
    functor.map (inverse.map g) ≫ (counit Y').hom = (counit Y).hom ≫ g

/-- A functor is **faithful** if it is injective on each hom-set. -/
structure Faithful (F : C ⥤ D) : Prop where
  /-- `F.map` is injective. -/
  map_injective : ∀ {X Y : C} {f g : X ⟶ Y}, F.map f = F.map g → f = g

/-- A functor is **full** if it is surjective on each hom-set; we record a chosen
preimage of every arrow. -/
structure Full (F : C ⥤ D) where
  /-- A preimage of `h : F X ⟶ F Y`. -/
  preimage : {X Y : C} → (F.obj X ⟶ F.obj Y) → (X ⟶ Y)
  /-- It is a preimage. -/
  map_preimage : ∀ {X Y : C} (h : F.obj X ⟶ F.obj Y), F.map (preimage h) = h

/-- A functor is **essentially surjective** if every object of the target is isomorphic
to the image of some object. -/
def EssSurj (F : C ⥤ D) : Prop :=
  ∀ Y : D, ∃ X : C, Nonempty (F.obj X ≅ Y)

attribute [simp] Full.map_preimage

/-- If `X ≅ G (F X)` naturally, then `F` is faithful: `f` can be recovered from
`G (F f)` by conjugating with the isomorphisms. -/
theorem faithful_of_unit {F : C ⥤ D} {G : D ⥤ C} (η : (X : C) → (X ≅ G.obj (F.obj X)))
    (nat : ∀ {X X' : C} (f : X ⟶ X'), f ≫ (η X').hom = (η X).hom ≫ G.map (F.map f)) :
    Faithful F := by
  constructor
  intro X Y f g h
  have key : ∀ k : X ⟶ Y, k = (η X).hom ≫ G.map (F.map k) ≫ (η Y).inv := fun k => by
    rw [← assoc, ← nat k, assoc, (η Y).hom_inv_id, comp_id]
  rw [key f, key g, h]

end Defs

namespace Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The unit, packaged as a natural isomorphism `𝟭 ≅ F ⋙ G`. -/
def unitIso (e : Equivalence C D) : NatIso (Functor.id C) (e.functor.comp e.inverse) where
  hom := ⟨fun X => (e.unit X).hom, fun f => e.unit_nat f⟩
  inv := ⟨fun X => (e.unit X).inv, fun {X X'} f => by
    show e.inverse.map (e.functor.map f) ≫ (e.unit X').inv = (e.unit X).inv ≫ f
    rw [← Iso.inv_hom_id_assoc (e.unit X) (e.inverse.map (e.functor.map f) ≫ _),
      ← assoc (e.unit X).hom, ← e.unit_nat f, assoc, Iso.hom_inv_id, comp_id]⟩
  hom_inv_id X := (e.unit X).hom_inv_id
  inv_hom_id X := (e.unit X).inv_hom_id

/-- The counit, packaged as a natural isomorphism `G ⋙ F ≅ 𝟭`. -/
def counitIso (e : Equivalence C D) : NatIso (e.inverse.comp e.functor) (Functor.id D) where
  hom := ⟨fun Y => (e.counit Y).hom, fun g => e.counit_nat g⟩
  inv := ⟨fun Y => (e.counit Y).inv, fun {Y Y'} g => by
    show g ≫ (e.counit Y').inv = (e.counit Y).inv ≫ e.functor.map (e.inverse.map g)
    rw [← Iso.inv_hom_id_assoc (e.counit Y) (g ≫ _), ← assoc (e.counit Y).hom,
      ← e.counit_nat g, assoc, Iso.hom_inv_id, comp_id]⟩
  hom_inv_id Y := (e.counit Y).hom_inv_id
  inv_hom_id Y := (e.counit Y).inv_hom_id

/-- The identity equivalence of a category with itself. -/
def refl (C : Type u₁) [Category.{v₁} C] : Equivalence C C where
  functor := Functor.id C
  inverse := Functor.id C
  unit X := Iso.refl X
  counit X := Iso.refl X
  unit_nat f := (comp_id f).trans (id_comp f).symm
  counit_nat f := (comp_id f).trans (id_comp f).symm

/-- **Equivalence is symmetric**: swap the functors and invert the isomorphisms. -/
def symm (e : Equivalence C D) : Equivalence D C where
  functor := e.inverse
  inverse := e.functor
  unit Y := (e.counit Y).symm
  counit X := (e.unit X).symm
  unit_nat g := (e.counitIso.inv.naturality g)
  counit_nat f := (e.unitIso.inv.naturality f)

/-- The forward functor of an equivalence is faithful. -/
theorem faithful_functor (e : Equivalence C D) : Faithful e.functor :=
  faithful_of_unit e.unit e.unit_nat

/-- The backward functor of an equivalence is faithful. -/
theorem faithful_inverse (e : Equivalence C D) : Faithful e.inverse :=
  faithful_of_unit e.symm.unit e.symm.unit_nat

/-- The forward functor of an equivalence is full: the preimage of `h : F X ⟶ F Y` is
`η_X ≫ G h ≫ η_Y⁻¹`. -/
def full_functor (e : Equivalence C D) : Full e.functor where
  preimage {X Y} h := (e.unit X).hom ≫ e.inverse.map h ≫ (e.unit Y).inv
  map_preimage {X Y} h := by
    apply e.faithful_inverse.map_injective
    have nat := e.unit_nat ((e.unit X).hom ≫ e.inverse.map h ≫ (e.unit Y).inv)
    rw [assoc, assoc, Iso.inv_hom_id, comp_id] at nat
    have := congrArg ((e.unit X).inv ≫ ·) nat
    simp only [Iso.inv_hom_id_assoc] at this
    exact this.symm

/-- The forward functor of an equivalence is essentially surjective: `Y ≅ F (G Y)`. -/
theorem essSurj_functor (e : Equivalence C D) : EssSurj e.functor :=
  fun Y => ⟨e.inverse.obj Y, ⟨e.counit Y⟩⟩

/-- **An equivalence is fully faithful and essentially surjective.** -/
theorem fullyFaithful_essSurj (e : Equivalence C D) :
    Nonempty (Full e.functor) ∧ Faithful e.functor ∧ EssSurj e.functor :=
  ⟨⟨e.full_functor⟩, e.faithful_functor, e.essSurj_functor⟩

end Equivalence

/-! ## The converse, using choice -/

section Converse

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (hfull : Full F) (hfaith : Faithful F) (hess : EssSurj F)

/-- The chosen preimage object of `Y` (by the axiom of choice). -/
noncomputable def essPre (Y : D) : C := Classical.choose (hess Y)

/-- The chosen isomorphism `F (essPre Y) ≅ Y`. -/
noncomputable def essIso (Y : D) : F.obj (essPre F hess Y) ≅ Y :=
  Classical.choice (Classical.choose_spec (hess Y))

/-- The inverse functor built from a fully faithful, essentially surjective functor:
`Y ↦ essPre Y`, and an arrow `g : Y ⟶ Y'` goes to the unique preimage of
`e_Y ≫ g ≫ e_Y'⁻¹`. -/
noncomputable def invFunctor : D ⥤ C where
  obj Y := essPre F hess Y
  map {Y Y'} g := hfull.preimage ((essIso F hess Y).hom ≫ g ≫ (essIso F hess Y').inv)
  map_id Y := hfaith.map_injective (by simp)
  map_comp {Y Y' Y''} f g := hfaith.map_injective (by simp)

/-- The unit isomorphism `X ≅ essPre (F X)`: the preimage of `e_{F X}⁻¹`. -/
noncomputable def unitAt (X : C) : X ≅ essPre F hess (F.obj X) where
  hom := hfull.preimage (essIso F hess (F.obj X)).inv
  inv := hfull.preimage (essIso F hess (F.obj X)).hom
  hom_inv_id := hfaith.map_injective (by
    rw [F.map_comp, hfull.map_preimage, hfull.map_preimage, Iso.inv_hom_id, F.map_id])
  inv_hom_id := hfaith.map_injective (by
    rw [F.map_comp, hfull.map_preimage, hfull.map_preimage, Iso.hom_inv_id, F.map_id])

/-- **A fully faithful, essentially surjective functor is an equivalence** (using the axiom
of choice to pick the inverse on objects). -/
noncomputable def Equivalence.ofFullyFaithfulEssSurj : Equivalence C D where
  functor := F
  inverse := invFunctor F hfull hfaith hess
  unit X := unitAt F hfull hfaith hess X
  counit Y := essIso F hess Y
  unit_nat {X X'} f := hfaith.map_injective (by
    change F.map (f ≫ hfull.preimage (essIso F hess (F.obj X')).inv) =
      F.map (hfull.preimage (essIso F hess (F.obj X)).inv ≫ hfull.preimage
        ((essIso F hess (F.obj X)).hom ≫ F.map f ≫ (essIso F hess (F.obj X')).inv))
    rw [F.map_comp, F.map_comp, hfull.map_preimage, hfull.map_preimage, hfull.map_preimage,
      Iso.inv_hom_id_assoc])
  counit_nat {Y Y'} g := by
    change F.map (hfull.preimage ((essIso F hess Y).hom ≫ g ≫ (essIso F hess Y').inv)) ≫ _ = _ ≫ g
    rw [hfull.map_preimage, assoc, assoc, Iso.inv_hom_id, comp_id]

end Converse

/-! ## Example: finite sets and their skeleton -/

/-- The objects of `FinOrd`: natural numbers, `n` standing for the standard `n`-element
set `{0, …, n − 1}`. -/
structure FinOrd where
  /-- The number of elements. -/
  n : Nat

/-- **The category `FinOrd`**: objects are natural numbers, arrows `m ⟶ n` are functions
`Fin m → Fin n`. -/
instance FinOrd.category : Category.{0} FinOrd where
  Hom m n := Fin m.n → Fin n.n
  id _ := fun x => x
  comp f g := fun x => g (f x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A **finite type**: a type in bijection with some `Fin n` (the bijection is not part of
the data — only its existence). -/
structure FinSet where
  /-- The underlying type. -/
  carrier : Type
  /-- It is finite. -/
  finite : ∃ n : Nat, Nonempty (Bij carrier (Fin n))

/-- **The category `FinSet`** of finite types and all functions. -/
instance FinSet.category : Category.{0} FinSet where
  Hom X Y := X.carrier → Y.carrier
  id _ := fun x => x
  comp f g := fun x => g (f x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The identity bijection of a type. -/
def Bij.refl (α : Type) : Bij α α := ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- The inclusion `FinOrd ⥤ FinSet`, `n ↦ Fin n`. -/
def finInclusion : FinOrd ⥤ FinSet where
  obj m := ⟨Fin m.n, ⟨m.n, ⟨Bij.refl _⟩⟩⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion is full (every function `Fin m → Fin n` is an arrow of `FinOrd`). -/
def finInclusion_full : Full finInclusion where
  preimage h := h
  map_preimage _ := rfl

/-- The inclusion is faithful. -/
theorem finInclusion_faithful : Faithful finInclusion := ⟨fun h => h⟩

/-- The inclusion is essentially surjective: every finite type is isomorphic to some
`Fin n`. -/
theorem finInclusion_essSurj : EssSurj finInclusion := by
  intro X
  obtain ⟨n, ⟨e⟩⟩ := X.finite
  exact ⟨⟨n⟩, ⟨⟨e.invFun, e.toFun, funext e.right_inv, funext e.left_inv⟩⟩⟩

/-- **Finite sets are equivalent to their skeleton**: the category of all finite types is
equivalent to the category with one object `n` for each natural number. -/
noncomputable def finSetEquivFinOrd : Equivalence FinOrd FinSet :=
  Equivalence.ofFullyFaithfulEssSurj finInclusion finInclusion_full finInclusion_faithful
    finInclusion_essSurj

/-- An injection `Fin m → Fin n` forces `m ≤ n` (pigeonhole). -/
theorem le_of_fin_injection {m n : Nat} (f : Fin m → Fin n)
    (hf : ∀ a b, f a = f b → a = b) : m ≤ n := by
  refine Nat.le_of_not_lt fun h => ?_
  obtain ⟨i, j, hij, he⟩ := Foundations.Combinatorics.pigeonhole_fin h f
  exact hij (hf i j he)

/-- **`FinOrd` is skeletal**: isomorphic objects are equal. -/
theorem FinOrd.skeletal {m n : FinOrd} (i : m ≅ n) : m = n := by
  have h₁ : ∀ x, i.inv (i.hom x) = x := congrFun i.hom_inv_id
  have h₂ : ∀ y, i.hom (i.inv y) = y := congrFun i.inv_hom_id
  have a := le_of_fin_injection i.hom fun a b h => by rw [← h₁ a, h, h₁]
  have b := le_of_fin_injection i.inv fun a b h => by rw [← h₂ a, h, h₂]
  cases m; cases n
  congr
  exact Nat.le_antisymm a b

end Foundations.Categories
