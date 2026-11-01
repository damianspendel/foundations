import Foundations.Categories.Limits

/-!
# Adjunctions

*"Adjoint functors arise everywhere"* (Mac Lane). Daniel Kan introduced them in
1958; Lawvere made them the organising principle of logic and foundations. A
functor `F : C ⥤ D` is **left adjoint** to `G : D ⥤ C`, written `F ⊣ G`, when
arrows `F X ⟶ Y` in `D` correspond bijectively and naturally to arrows
`X ⟶ G Y` in `C`. Typically `G` forgets structure and `F` freely creates it:

* the **free monoid** on a type `α` is the type of lists `List α` under
  concatenation; a monoid homomorphism `List α ⟶ M` is the same thing as an
  arbitrary function `α → M` (its values on one-letter words). So
  *free ⊣ forgetful*;
* in the category of types, `(− × A) ⊣ (A → −)`: a function of two arguments is
  the same as a function returning functions — **currying** (Schönfinkel 1924,
  Curry). A category with products and such exponentials is **cartesian closed**;
  cartesian closed categories are the semantics of the simply typed λ-calculus of
  Part V (Lambek), another face of Curry–Howard.

Lawvere observed that the quantifiers of logic are adjoints too (`∃ ⊣ weakening ⊣ ∀`)
and that so is comprehension in set theory: adjunctions are where logic and
structure meet.

Every adjunction has a **unit** `η : 𝟭 ⟶ G F` and **counit** `ε : F G ⟶ 𝟭`
satisfying the *triangle identities*, and **right adjoints preserve limits** —
we prove it for terminal objects and binary products: the forgetful functor from
any algebraic category preserves products because it has a left adjoint.
-/

namespace Foundations.Categories

universe v₁ v₂ u₁ u₂ u

open Category

section General

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- An **adjunction** `F ⊣ G`: a bijection between arrows `F X ⟶ Y` and `X ⟶ G Y`,
natural in `X` and `Y`. -/
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  /-- The bijection `(F X ⟶ Y) ≅ (X ⟶ G Y)`. -/
  homEquiv : (X : C) → (Y : D) → Bij (F.obj X ⟶ Y) (X ⟶ G.obj Y)
  /-- Naturality in `X`. -/
  natural_left : ∀ {X' X : C} {Y : D} (f : X' ⟶ X) (g : F.obj X ⟶ Y),
    (homEquiv X' Y).toFun (F.map f ≫ g) = f ≫ (homEquiv X Y).toFun g
  /-- Naturality in `Y`. -/
  natural_right : ∀ {X : C} {Y Y' : D} (g : F.obj X ⟶ Y) (h : Y ⟶ Y'),
    (homEquiv X Y').toFun (g ≫ h) = (homEquiv X Y).toFun g ≫ G.map h

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : Adjunction F G)

/-- Naturality of the inverse bijection in `X`. -/
theorem inv_natural_left {X' X : C} {Y : D} (f : X' ⟶ X) (k : X ⟶ G.obj Y) :
    (adj.homEquiv X' Y).invFun (f ≫ k) = F.map f ≫ (adj.homEquiv X Y).invFun k := by
  apply (adj.homEquiv X' Y).injective
  rw [(adj.homEquiv X' Y).right_inv, adj.natural_left, (adj.homEquiv X Y).right_inv]

/-- Naturality of the inverse bijection in `Y`. -/
theorem inv_natural_right {X : C} {Y Y' : D} (k : X ⟶ G.obj Y) (h : Y ⟶ Y') :
    (adj.homEquiv X Y').invFun (k ≫ G.map h) = (adj.homEquiv X Y).invFun k ≫ h := by
  apply (adj.homEquiv X Y').injective
  rw [(adj.homEquiv X Y').right_inv, adj.natural_right, (adj.homEquiv X Y).right_inv]

/-- The **unit** `η_X : X ⟶ G (F X)`, the transpose of `𝟙 (F X)`. -/
def unit : NatTrans (Functor.id C) (F.comp G) where
  app X := (adj.homEquiv X (F.obj X)).toFun (𝟙 (F.obj X))
  naturality {X Y} f := by
    change f ≫ (adj.homEquiv Y (F.obj Y)).toFun (𝟙 (F.obj Y)) =
      (adj.homEquiv X (F.obj X)).toFun (𝟙 (F.obj X)) ≫ G.map (F.map f)
    rw [← adj.natural_left, ← adj.natural_right, comp_id, id_comp]

/-- The **counit** `ε_Y : F (G Y) ⟶ Y`, the transpose of `𝟙 (G Y)`. -/
def counit : NatTrans (G.comp F) (Functor.id D) where
  app Y := (adj.homEquiv (G.obj Y) Y).invFun (𝟙 (G.obj Y))
  naturality {X Y} h := by
    change F.map (G.map h) ≫ (adj.homEquiv (G.obj Y) Y).invFun (𝟙 (G.obj Y)) =
      (adj.homEquiv (G.obj X) X).invFun (𝟙 (G.obj X)) ≫ h
    rw [← adj.inv_natural_left, ← adj.inv_natural_right, comp_id, id_comp]

/-- **First triangle identity**: `F η_X ≫ ε_{F X} = 𝟙 (F X)`. -/
theorem left_triangle (X : C) :
    F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) := by
  change F.map ((adj.homEquiv X (F.obj X)).toFun (𝟙 (F.obj X))) ≫
    (adj.homEquiv (G.obj (F.obj X)) (F.obj X)).invFun (𝟙 (G.obj (F.obj X))) = 𝟙 (F.obj X)
  rw [← adj.inv_natural_left, comp_id, (adj.homEquiv X (F.obj X)).left_inv]

/-- **Second triangle identity**: `η_{G Y} ≫ G ε_Y = 𝟙 (G Y)`. -/
theorem right_triangle (Y : D) :
    adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) := by
  change (adj.homEquiv (G.obj Y) (F.obj (G.obj Y))).toFun (𝟙 (F.obj (G.obj Y))) ≫
    G.map ((adj.homEquiv (G.obj Y) Y).invFun (𝟙 (G.obj Y))) = 𝟙 (G.obj Y)
  rw [← adj.natural_right, id_comp, (adj.homEquiv (G.obj Y) Y).right_inv]

/-- **Right adjoints preserve terminal objects.** -/
def preservesTerminal {T : D} (hT : IsTerminal T) : IsTerminal (G.obj T) where
  lift X := (adj.homEquiv X T).toFun (hT.lift (F.obj X))
  uniq {X} f g := by
    rw [← (adj.homEquiv X T).right_inv f, ← (adj.homEquiv X T).right_inv g,
      hT.uniq ((adj.homEquiv X T).invFun f) ((adj.homEquiv X T).invFun g)]

/-- **Right adjoints preserve binary products.** -/
def preservesProduct {X Y P : D} {π₁ : P ⟶ X} {π₂ : P ⟶ Y} (hP : IsProduct X Y P π₁ π₂) :
    IsProduct (G.obj X) (G.obj Y) (G.obj P) (G.map π₁) (G.map π₂) where
  lift {W} f g := (adj.homEquiv W P).toFun
    (hP.lift ((adj.homEquiv W X).invFun f) ((adj.homEquiv W Y).invFun g))
  fac₁ {W} f g := by rw [← adj.natural_right, hP.fac₁, (adj.homEquiv W X).right_inv]
  fac₂ {W} f g := by rw [← adj.natural_right, hP.fac₂, (adj.homEquiv W Y).right_inv]
  uniq {W} f g h h₁ h₂ := by
    rw [← (adj.homEquiv W P).right_inv h]
    congr 1
    apply hP.uniq
    · rw [← adj.inv_natural_right, h₁]
    · rw [← adj.inv_natural_right, h₂]

end Adjunction

end General

/-! ## The free monoid -/

/-- A **monoid homomorphism**. -/
structure MonHom (M : Type u) (N : Type u) [Monoid' M] [Monoid' N] where
  /-- The underlying function. -/
  toFun : M → N
  /-- The unit is preserved. -/
  map_one : toFun 1 = 1
  /-- Products are preserved. -/
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b

/-- Monoid homomorphisms with the same values are equal. -/
theorem MonHom.ext {M N : Type u} [Monoid' M] [Monoid' N] {f g : MonHom M N}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk f _ _ =>
    cases g with
    | mk g _ _ =>
      have : f = g := funext h
      subst this
      rfl

/-- A **bundled monoid**. -/
structure MonCat where
  /-- The underlying type. -/
  carrier : Type u
  /-- The monoid structure. -/
  [str : Monoid' carrier]

attribute [instance] MonCat.str

/-- **The category of monoids** and monoid homomorphisms. -/
instance MonCat.category : Category.{u} MonCat.{u} where
  Hom M N := MonHom M.carrier N.carrier
  id M := ⟨fun x => x, rfl, fun _ _ => rfl⟩
  comp f g := ⟨fun x => g.toFun (f.toFun x), by rw [f.map_one, g.map_one],
    fun a b => by rw [f.map_mul, g.map_mul]⟩
  id_comp _ := MonHom.ext fun _ => rfl
  comp_id _ := MonHom.ext fun _ => rfl
  assoc _ _ _ := MonHom.ext fun _ => rfl

/-- The **forgetful functor** from monoids to types. -/
def MonCat.forget : MonCat.{u} ⥤ Type u where
  obj M := M.carrier
  map f := fun x => f.toFun x
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Lists under concatenation form a monoid: the **free monoid** (words over an alphabet). -/
instance listMonoid (α : Type u) : Monoid' (List α) where
  mul := List.append
  one := []
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

/-- The product of a list of monoid elements, `[a₁, …, aₙ] ↦ a₁ ⋯ aₙ`. -/
def listProd {M : Type u} [Monoid' M] : List M → M
  | [] => 1
  | a :: l => a * listProd l

/-- The product of a concatenation is the product of the products. -/
theorem listProd_append {M : Type u} [Monoid' M] (l₁ l₂ : List M) :
    listProd (l₁ ++ l₂) = listProd l₁ * listProd l₂ := by
  induction l₁ with
  | nil => exact (Monoid'.one_mul _).symm
  | cons a l ih => simp only [List.cons_append, listProd, ih, Monoid'.mul_assoc]

/-- The **free monoid functor** `Type ⥤ Mon`, `α ↦ List α`. -/
def MonCat.free : Type u ⥤ MonCat.{u} where
  obj α := MonCat.mk (List α)
  map f := (⟨List.map f, rfl, fun a b => List.map_append⟩ : MonHom (List _) (List _))
  map_id _ := MonHom.ext fun l => List.map_id l
  map_comp f g := MonHom.ext fun l => by
    show List.map (fun x => g (f x)) l = List.map g (List.map f l)
    rw [List.map_map]; rfl

/-- The monoid homomorphism `List α ⟶ M` extending a function `g : α → M`. -/
def extendHom {α : Type u} (M : MonCat.{u}) (g : α → M.carrier) :
    MonHom (List α) M.carrier where
  toFun l := listProd (l.map g)
  map_one := rfl
  map_mul a b := by
    show listProd ((a ++ b).map g) = listProd (a.map g) * listProd (b.map g)
    rw [List.map_append, listProd_append]

/-- **The free monoid is left adjoint to the forgetful functor**: monoid homomorphisms
`List α ⟶ M` correspond to functions `α → M`. -/
def freeForgetAdjunction : Adjunction MonCat.free.{u} MonCat.forget.{u} where
  homEquiv α M :=
    { toFun := fun (φ : MonHom (List α) M.carrier) => fun a => φ.toFun [a]
      invFun := fun (g : α → M.carrier) => (extendHom M g : MonHom (List α) M.carrier)
      left_inv := fun (φ : MonHom (List α) M.carrier) => MonHom.ext fun (l : List α) => by
        induction l with
        | nil => exact φ.map_one.symm
        | cons a l ih =>
          show φ.toFun [a] * listProd (l.map fun a => φ.toFun [a]) = φ.toFun (a :: l)
          have := φ.map_mul [a] l
          change φ.toFun ([a] ++ l) = _ at this
          rw [List.singleton_append] at this
          rw [this]
          exact congrArg _ ih
      right_inv := fun (g : α → M.carrier) => funext fun a => Monoid'.mul_one (M := M.carrier) (g a) }
  natural_left _ _ := rfl
  natural_right _ _ := rfl

/-- **Consequence**: the forgetful functor from monoids preserves products — because it
is a right adjoint. -/
def MonCat.forget_preservesProduct {X Y P : MonCat.{u}} {π₁ : P ⟶ X} {π₂ : P ⟶ Y}
    (hP : IsProduct X Y P π₁ π₂) :
    IsProduct (MonCat.forget.obj X) (MonCat.forget.obj Y) (MonCat.forget.obj P)
      (MonCat.forget.map π₁) (MonCat.forget.map π₂) :=
  freeForgetAdjunction.preservesProduct hP

/-! ## Types are cartesian closed -/

/-- The functor `− × A` on types. -/
def prodFunctor (A : Type u) : Type u ⥤ Type u where
  obj X := X × A
  map f := fun p => (f p.1, p.2)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `A → −` on types (exponentiation). -/
def expFunctor (A : Type u) : Type u ⥤ Type u where
  obj Y := A → Y
  map f := fun g a => f (g a)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The category of types is cartesian closed**: `(− × A) ⊣ (A → −)`, the adjunction
being *currying*: functions `X × A → Y` correspond to functions `X → (A → Y)`. -/
def curryAdjunction (A : Type u) : Adjunction (prodFunctor A) (expFunctor A) where
  homEquiv _ _ :=
    { toFun := fun f x a => f (x, a)
      invFun := fun g p => g p.1 p.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  natural_left _ _ := rfl
  natural_right _ _ := rfl

/-- The counit of the currying adjunction is **evaluation** `(A → Y) × A → Y`. -/
theorem curryAdjunction_counit (A Y : Type u) (g : A → Y) (a : A) :
    (curryAdjunction A).counit.app Y (g, a) = g a := rfl

end Foundations.Categories
