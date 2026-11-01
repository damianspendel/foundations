import Foundations.Categories.Category

/-!
# The Yoneda lemma

*"Tell me who your friends are, and I will tell you who you are."* The Yoneda
lemma (Nobuo Yoneda, communicated to Mac Lane in a Paris railway station in
1954) is the precise form of the structuralist slogan that an object is
determined by its relations to all other objects.

To each object `A` of a category `C` corresponds its **hom-functor**
`Hom(A, −) : C ⥤ Type`, sending `X` to the type of arrows `A ⟶ X` — the
"view of the category from `A`". The lemma says that for every functor
`F : C ⥤ Type`,

  `Nat(Hom(A, −), F) ≅ F A`,

naturally in `A` and `F`: a natural transformation out of a hom-functor is
completely determined by where it sends the single element `𝟙 A`, and any element
of `F A` arises this way. The proof is almost nothing — yet the consequences are
everywhere:

* taking `F = Hom(B, −)` gives `Nat(Hom(B, −), Hom(A, −)) ≅ (A ⟶ B)`: the **Yoneda
  embedding** `A ↦ Hom(A, −)` is *fully faithful*; a category embeds faithfully into a
  category of functors (of "presheaves") without loss of information;
* hence **objects with naturally isomorphic hom-functors are isomorphic**: an object
  is determined, up to isomorphism, by the pattern of arrows out of it. Nothing
  "internal" remains to be known.

Grothendieck built on this the idea that a geometric space *is* the functor of
its points with values in all test spaces; universal properties, limits and
adjoints (the next files) are all instances of representability.

We also make functors and natural transformations into a category (the
**functor category**), so that the Yoneda embedding is itself a functor.
-/

namespace Foundations.Categories

universe v v₁ v₂ u u₁ u₂ w w'

open Category

/-- A **bijection** between two types, given with its inverse. -/
structure Bij (α : Type w) (β : Type w') where
  /-- The forward map. -/
  toFun : α → β
  /-- The inverse map. -/
  invFun : β → α
  /-- The inverse undoes the forward map. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- The forward map undoes the inverse. -/
  right_inv : ∀ b, toFun (invFun b) = b

/-- The inverse bijection. -/
def Bij.symm {α : Type w} {β : Type w'} (e : Bij α β) : Bij β α :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

/-- A bijection is injective. -/
theorem Bij.injective {α : Type w} {β : Type w'} (e : Bij α β) {a b : α}
    (h : e.toFun a = e.toFun b) : a = b := by
  rw [← e.left_inv a, ← e.left_inv b, h]

/-! ## The functor category -/

/-- **The functor category** `C ⥤ D`: functors as objects, natural transformations as
arrows. -/
instance functorCategory (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] :
    Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := NatTrans.vcomp α β
  id_comp _ := NatTrans.ext fun _ => id_comp _
  comp_id _ := NatTrans.ext fun _ => comp_id _
  assoc _ _ _ := NatTrans.ext fun _ => assoc _ _ _

section Yoneda

variable {C : Type u} [Category.{v} C]

/-- The **hom-functor** `Hom(A, −) : C ⥤ Type`, sending `X` to the arrows `A ⟶ X` and
acting on arrows by post-composition. -/
def homFunctor (A : C) : C ⥤ Type v where
  obj X := A ⟶ X
  map f := fun g => g ≫ f
  map_id _ := funext fun g => comp_id g
  map_comp f g := funext fun h => (assoc h f g).symm

/-- Pre-composition with `f : A ⟶ B` is a natural transformation `Hom(B, −) ⟶ Hom(A, −)`. -/
def homPre {A B : C} (f : A ⟶ B) : NatTrans (homFunctor B) (homFunctor A) where
  app _ := fun g => f ≫ g
  naturality g := funext fun h => (assoc f h g).symm

/-- **The key computation**: a natural transformation out of `Hom(A, −)` is determined by
its value on `𝟙 A`: `α_X(h) = F(h)(α_A(𝟙 A))`. -/
theorem app_eq_map {F : C ⥤ Type v} {A : C} (α : NatTrans (homFunctor A) F) {X : C}
    (h : A ⟶ X) : α.app X h = F.map h (α.app A (𝟙 A)) := by
  have := congrFun (α.naturality h) (𝟙 A)
  change α.app X (𝟙 A ≫ h) = F.map h (α.app A (𝟙 A)) at this
  rw [id_comp] at this
  exact this

/-- The natural transformation `Hom(A, −) ⟶ F` determined by an element `x : F A`:
`h ↦ F(h)(x)`. -/
def yonedaInv (F : C ⥤ Type v) (A : C) (x : F.obj A) : NatTrans (homFunctor A) F where
  app _ := fun h => F.map h x
  naturality f := funext fun g => congrFun (F.map_comp g f) x

/-- **The Yoneda lemma.** For every functor `F : C ⥤ Type` and object `A`, natural
transformations `Hom(A, −) ⟶ F` correspond bijectively to elements of `F A`, via
`α ↦ α_A(𝟙 A)`. -/
def yoneda (F : C ⥤ Type v) (A : C) : Bij (NatTrans (homFunctor A) F) (F.obj A) where
  toFun α := α.app A (𝟙 A)
  invFun x := yonedaInv F A x
  left_inv α := NatTrans.ext fun _ => funext fun h => (app_eq_map α h).symm
  right_inv x := congrFun (F.map_id A) x

/-- **Naturality of the Yoneda bijection in `F`**: for `θ : F ⟶ G`,
`yoneda (α ≫ θ) = θ_A (yoneda α)`. -/
theorem yoneda_natural_F {F G : C ⥤ Type v} (θ : NatTrans F G) (A : C)
    (α : NatTrans (homFunctor A) F) :
    (yoneda G A).toFun (α.vcomp θ) = θ.app A ((yoneda F A).toFun α) := rfl

/-- **Naturality of the Yoneda bijection in `A`**: for `f : A ⟶ B`,
`yoneda (Hom(f, −) ≫ α) = F(f)(yoneda α)`. -/
theorem yoneda_natural_A (F : C ⥤ Type v) {A B : C} (f : A ⟶ B)
    (α : NatTrans (homFunctor A) F) :
    (yoneda F B).toFun ((homPre f).vcomp α) = F.map f ((yoneda F A).toFun α) := by
  change α.app B (f ≫ 𝟙 B) = F.map f (α.app A (𝟙 A))
  rw [comp_id]
  exact app_eq_map α f

/-- **The Yoneda embedding is fully faithful**: arrows `A ⟶ B` correspond bijectively to
natural transformations `Hom(B, −) ⟶ Hom(A, −)`, via pre-composition. -/
def yonedaFullyFaithful (A B : C) : Bij (A ⟶ B) (NatTrans (homFunctor B) (homFunctor A)) :=
  (yoneda (homFunctor A) B).symm

/-- The bijection of `yonedaFullyFaithful` is pre-composition. -/
theorem yonedaFullyFaithful_apply {A B : C} (f : A ⟶ B) :
    (yonedaFullyFaithful A B).toFun f = homPre f := rfl

/-- **Faithfulness**: distinct arrows induce distinct natural transformations. -/
theorem homPre_injective {A B : C} {f g : A ⟶ B} (h : homPre f = homPre g) : f = g :=
  (yonedaFullyFaithful A B).injective h

/-- **The Yoneda embedding** as a functor `Cᵒᵖ ⥤ (C ⥤ Type)`, `A ↦ Hom(A, −)`. -/
def yonedaEmbedding : Op C ⥤ (C ⥤ Type v) where
  obj A := homFunctor A.unop
  map f := homPre f
  map_id _ := NatTrans.ext fun _ => funext fun g => id_comp g
  map_comp f g := NatTrans.ext fun _ => funext fun h => assoc (C := C) g f h

/-- **Objects are determined by their hom-functors.** If `Hom(A, −)` and `Hom(B, −)` are
naturally isomorphic, then `A ≅ B`. -/
def isoOfHomIso {A B : C} (e : NatIso (homFunctor A) (homFunctor B)) : A ≅ B where
  hom := e.inv.app B (𝟙 B)
  inv := e.hom.app A (𝟙 A)
  hom_inv_id := by
    have h := congrFun (e.hom_inv_id A) (𝟙 A)
    exact (app_eq_map e.inv (e.hom.app A (𝟙 A))).symm.trans h
  inv_hom_id := by
    have h := congrFun (e.inv_hom_id B) (𝟙 B)
    exact (app_eq_map e.hom (e.inv.app B (𝟙 B))).symm.trans h

end Yoneda

end Foundations.Categories
