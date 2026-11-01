import Foundations.Categories.Adjunctions

/-!
# Limits and colimits of arbitrary diagrams

The previous files treated products, terminal objects, equalisers and pullbacks one
at a time, each with its own universal property. They are all instances of one
notion. A **diagram** of shape `J` in a category `C` is simply a functor
`F : J ⥤ C`: the index category `J` is the "shape" (two points for a product, no
points for a terminal object, two parallel arrows for an equaliser, a cospan for a
pullback), and `F` draws that shape inside `C`.

A **cone** over `F` is an object `X` (the *apex*) with an arrow `π_j : X ⟶ F j` to
every vertex of the diagram, such that every triangle commutes:
`π_i ≫ F f = π_j` for `f : i ⟶ j`. A **limit** is a *universal* cone: every other
cone factors through it by exactly one arrow. Dually a **cocone** has arrows
`ι_j : F j ⟶ X` *into* the apex, and a **colimit** is a universal cocone — sums,
quotients and gluings are colimits.

The philosophical point already made for products holds in full generality: a
limit is characterised not by what it is *made of* but by how it *relates* to all
other cones, and this characterisation pins it down **up to a unique isomorphism**
compatible with the cones (proved below). In Yoneda's terms, a limit of `F` is a
representing object for the functor "cones over `F` with apex `−`".

In the category of types every small diagram has a limit and a colimit, and both
have a familiar set-theoretic description:

* the limit of `F` is the type of **compatible families** — elements
  `x_j ∈ F j`, one for each vertex, with `F f (x_i) = x_j` — a subtype of the
  product `∏_j F j`;
* the colimit of `F` is the **disjoint sum** `Σ_j F j` divided by the relation that
  identifies `x ∈ F i` with its image `F f x ∈ F j`; Lean's built-in quotient `Quot`
  provides exactly this (it uses the axiom `Quot.sound`).

Finally we prove **RAPL** — *right adjoints preserve limits* — in full generality,
together with its dual (left adjoints preserve colimits), and the special case that
each hom-functor `Hom(A, −)` carries limits to limits of types: "a map into a limit
is a compatible family of maps".
-/

namespace Foundations.Categories

universe v v₁ v₂ u u₁ u₂ w

open Category

section Cones

variable {J : Type u₁} [Category.{v₁} J] {C : Type u} [Category.{v} C]

/-- A **cone** over a diagram `F : J ⥤ C`: an apex `pt` with an arrow to every vertex
`F j`, making all triangles over arrows of `J` commute. -/
structure Cone (F : J ⥤ C) where
  /-- The apex of the cone. -/
  pt : C
  /-- The leg of the cone at `j`. -/
  π : (j : J) → (pt ⟶ F.obj j)
  /-- The triangles commute: `π_i ≫ F f = π_j`. -/
  w : ∀ {i j : J} (f : i ⟶ j), π i ≫ F.map f = π j

/-- A **cocone** under a diagram `F : J ⥤ C`: an apex `pt` with an arrow from every
vertex `F j`, making all triangles commute. -/
structure Cocone (F : J ⥤ C) where
  /-- The apex of the cocone. -/
  pt : C
  /-- The leg of the cocone at `j`. -/
  ι : (j : J) → (F.obj j ⟶ pt)
  /-- The triangles commute: `F f ≫ ι_j = ι_i`. -/
  w : ∀ {i j : J} (f : i ⟶ j), F.map f ≫ ι j = ι i

/-- A cone `c` is a **limit** of `F`: every cone `s` factors through `c` by exactly one
arrow `s.pt ⟶ c.pt` commuting with the legs. -/
structure IsLimit {F : J ⥤ C} (c : Cone F) where
  /-- The induced arrow from the apex of another cone. -/
  lift : (s : Cone F) → (s.pt ⟶ c.pt)
  /-- The induced arrow commutes with the legs. -/
  fac : ∀ (s : Cone F) (j : J), lift s ≫ c.π j = s.π j
  /-- The induced arrow is unique. -/
  uniq : ∀ (s : Cone F) (m : s.pt ⟶ c.pt), (∀ j, m ≫ c.π j = s.π j) → m = lift s

/-- A cocone `c` is a **colimit** of `F`: every cocone `s` is reached from `c` by exactly
one arrow `c.pt ⟶ s.pt` commuting with the legs. -/
structure IsColimit {F : J ⥤ C} (c : Cocone F) where
  /-- The induced arrow to the apex of another cocone. -/
  desc : (s : Cocone F) → (c.pt ⟶ s.pt)
  /-- The induced arrow commutes with the legs. -/
  fac : ∀ (s : Cocone F) (j : J), c.ι j ≫ desc s = s.ι j
  /-- The induced arrow is unique. -/
  uniq : ∀ (s : Cocone F) (m : c.pt ⟶ s.pt), (∀ j, c.ι j ≫ m = s.ι j) → m = desc s

namespace IsLimit

variable {F : J ⥤ C} {c d : Cone F}

/-- Arrows into the apex of a limit are determined by their composites with the legs. -/
theorem hom_ext (hc : IsLimit c) {W : C} {f g : W ⟶ c.pt}
    (h : ∀ j, f ≫ c.π j = g ≫ c.π j) : f = g := by
  let s : Cone F := ⟨W, fun j => g ≫ c.π j, fun f' => by rw [assoc, c.w]⟩
  exact (hc.uniq s f h).trans (hc.uniq s g fun _ => rfl).symm

/-- The cone itself factors through itself by the identity. -/
theorem lift_self (hc : IsLimit c) : hc.lift c = 𝟙 c.pt :=
  (hc.uniq c (𝟙 c.pt) fun _ => id_comp _).symm

/-- **Limits are unique up to isomorphism**: two limit cones of the same diagram have
isomorphic apexes. -/
def uniqueIso (hc : IsLimit c) (hd : IsLimit d) : c.pt ≅ d.pt where
  hom := hd.lift c
  inv := hc.lift d
  hom_inv_id := hc.hom_ext fun j => by rw [assoc, hc.fac, hd.fac, id_comp]
  inv_hom_id := hd.hom_ext fun j => by rw [assoc, hd.fac, hc.fac, id_comp]

/-- The comparison isomorphism commutes with the legs. -/
theorem uniqueIso_hom_comp (hc : IsLimit c) (hd : IsLimit d) (j : J) :
    (uniqueIso hc hd).hom ≫ d.π j = c.π j := hd.fac c j

/-- **…and it is the only isomorphism commuting with the legs.** -/
theorem iso_unique (hc : IsLimit c) (hd : IsLimit d) (i : c.pt ≅ d.pt)
    (h : ∀ j, i.hom ≫ d.π j = c.π j) : i = uniqueIso hc hd :=
  Iso.ext (hd.uniq c i.hom h)

/-- Transport of a limit along an isomorphism of apexes: if `c` is a limit and
`i : X ≅ c.pt`, the cone with apex `X` and legs `i.hom ≫ π_j` is again a limit. -/
def ofIso (hc : IsLimit c) {X : C} (i : X ≅ c.pt) :
    IsLimit (⟨X, fun j => i.hom ≫ c.π j, fun f => by rw [assoc, c.w]⟩ : Cone F) where
  lift s := hc.lift s ≫ i.inv
  fac s j := by
    show (hc.lift s ≫ i.inv) ≫ (i.hom ≫ c.π j) = s.π j
    rw [assoc, ← assoc i.inv, i.inv_hom_id, id_comp, hc.fac]
  uniq s m hm := by
    have : m ≫ i.hom = hc.lift s := hc.uniq s _ fun j => by rw [assoc]; exact hm j
    rw [← this, assoc, i.hom_inv_id, comp_id]

end IsLimit

namespace IsColimit

variable {F : J ⥤ C} {c d : Cocone F}

/-- Arrows out of the apex of a colimit are determined by their composites with the legs. -/
theorem hom_ext (hc : IsColimit c) {W : C} {f g : c.pt ⟶ W}
    (h : ∀ j, c.ι j ≫ f = c.ι j ≫ g) : f = g := by
  let s : Cocone F := ⟨W, fun j => c.ι j ≫ g, fun f' => by rw [← assoc, c.w]⟩
  exact (hc.uniq s f h).trans (hc.uniq s g fun _ => rfl).symm

/-- **Colimits are unique up to isomorphism.** -/
def uniqueIso (hc : IsColimit c) (hd : IsColimit d) : c.pt ≅ d.pt where
  hom := hc.desc d
  inv := hd.desc c
  hom_inv_id := hc.hom_ext fun j => by rw [← assoc, hc.fac, hd.fac, comp_id]
  inv_hom_id := hd.hom_ext fun j => by rw [← assoc, hd.fac, hc.fac, comp_id]

/-- **…and the isomorphism is the only one commuting with the legs.** -/
theorem iso_unique (hc : IsColimit c) (hd : IsColimit d) (i : c.pt ≅ d.pt)
    (h : ∀ j, c.ι j ≫ i.hom = d.ι j) : i = uniqueIso hc hd :=
  Iso.ext (hc.uniq d i.hom h)

end IsColimit

/-! ## Special shapes: the empty diagram -/

/-- The empty type, as an index category with no objects. -/
instance emptyCategory : Category.{0} PEmpty.{u₁ + 1} where
  Hom a _ := nomatch a
  id a := nomatch a
  comp {a} := nomatch a
  id_comp {a} := nomatch a
  comp_id {a} := nomatch a
  assoc {a} := nomatch a

/-- The empty diagram in `C`. -/
def emptyDiagram (C : Type u) [Category.{v} C] : PEmpty.{u₁ + 1} ⥤ C where
  obj a := nomatch a
  map {a} := nomatch a
  map_id a := nomatch a
  map_comp {a} := nomatch a

/-- **A limit of the empty diagram is a terminal object**: a cone over nothing is just
an object, so the universal property says exactly "one arrow from everywhere". -/
def IsLimit.isTerminal {c : Cone (emptyDiagram.{v, u, u₁} C)} (hc : IsLimit c) :
    IsTerminal c.pt where
  lift X := hc.lift ⟨X, fun a => (nomatch a), fun {a} => (nomatch a)⟩
  uniq _ _ := hc.hom_ext fun a => nomatch a

end Cones

/-! ## Functors acting on cones -/

section MapCone

variable {J : Type u₁} [Category.{v₁} J] {C : Type u} [Category.{v} C]
  {D : Type u₂} [Category.{v₂} D]

/-- The image of a cone under a functor `G`: apply `G` to the apex and all legs. -/
def Cone.map {F : J ⥤ C} (c : Cone F) (G : C ⥤ D) : Cone (F.comp G) where
  pt := G.obj c.pt
  π j := G.map (c.π j)
  w f := by
    show G.map (c.π _) ≫ G.map (F.map f) = G.map (c.π _)
    rw [← G.map_comp, c.w]

/-- The image of a cocone under a functor `G`. -/
def Cocone.map {F : J ⥤ C} (c : Cocone F) (G : C ⥤ D) : Cocone (F.comp G) where
  pt := G.obj c.pt
  ι j := G.map (c.ι j)
  w f := by
    show G.map (F.map f) ≫ G.map (c.ι _) = G.map (c.ι _)
    rw [← G.map_comp, c.w]

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : Adjunction F G)

/-- Transposing a cone over `K ⋙ G` across the adjunction gives a cone over `K`, with
apex `F W`. -/
def transposeCone {K : J ⥤ D} (s : Cone (K.comp G)) : Cone K where
  pt := F.obj s.pt
  π j := (adj.homEquiv s.pt (K.obj j)).invFun (s.π j : s.pt ⟶ G.obj (K.obj j))
  w f := (adj.inv_natural_right _ (K.map f)).symm.trans
    (congrArg (adj.homEquiv _ _).invFun (s.w f))

/-- Transposing a cocone under `K ⋙ F` across the adjunction gives a cocone under `K`,
with apex `G W`. -/
def transposeCocone {K : J ⥤ C} (s : Cocone (K.comp F)) : Cocone K where
  pt := G.obj s.pt
  ι j := (adj.homEquiv (K.obj j) s.pt).toFun (s.ι j : F.obj (K.obj j) ⟶ s.pt)
  w f := (adj.natural_left (K.map f) _).symm.trans
    (congrArg (adj.homEquiv _ _).toFun (s.w f))

/-- **RAPL: right adjoints preserve limits.** If `G` has a left adjoint `F` and `c` is a
limit of a diagram `K : J ⥤ D`, then `G c` is a limit of `K ⋙ G`. The proof transposes
a cone `W ⟶ G (K j)` across the adjunction to a cone `F W ⟶ K j`, factors that through
`c`, and transposes back. -/
def preservesLimit {K : J ⥤ D} {c : Cone K} (hc : IsLimit c) : IsLimit (c.map G) where
  lift s := (adj.homEquiv s.pt c.pt).toFun (hc.lift (adj.transposeCone s))
  fac s j :=
    (adj.natural_right (X := s.pt) (hc.lift (adj.transposeCone s)) (c.π j)).symm.trans
      ((congrArg (adj.homEquiv s.pt (K.obj j)).toFun (hc.fac (adj.transposeCone s) j)).trans
        ((adj.homEquiv s.pt (K.obj j)).right_inv _))
  uniq s m hm := by
    have key : (adj.homEquiv s.pt c.pt).invFun m = hc.lift (adj.transposeCone s) :=
      hc.uniq (adj.transposeCone s) _ fun j =>
        (adj.inv_natural_right m (c.π j)).symm.trans (congrArg (adj.homEquiv _ _).invFun (hm j))
    exact ((adj.homEquiv s.pt c.pt).right_inv m).symm.trans (congrArg _ key)

/-- **Dually: left adjoints preserve colimits.** If `F ⊣ G` and `c` is a colimit of
`K : J ⥤ C`, then `F c` is a colimit of `K ⋙ F`. -/
def preservesColimit {K : J ⥤ C} {c : Cocone K} (hc : IsColimit c) : IsColimit (c.map F) where
  desc s := (adj.homEquiv c.pt s.pt).invFun (hc.desc (adj.transposeCocone s))
  fac s j :=
    (adj.inv_natural_left (Y := s.pt) (c.ι j) (hc.desc (adj.transposeCocone s))).symm.trans
      ((congrArg (adj.homEquiv (K.obj j) s.pt).invFun (hc.fac (adj.transposeCocone s) j)).trans
        ((adj.homEquiv (K.obj j) s.pt).left_inv _))
  uniq s m hm := by
    have key : (adj.homEquiv c.pt s.pt).toFun m = hc.desc (adj.transposeCocone s) :=
      hc.uniq (adj.transposeCocone s) _ fun j =>
        (adj.natural_left (c.ι j) m).symm.trans (congrArg (adj.homEquiv _ _).toFun (hm j))
    exact ((adj.homEquiv c.pt s.pt).left_inv m).symm.trans (congrArg _ key)

end Adjunction

end MapCone

/-! ## All small limits and colimits of types -/

section Types

variable {J : Type u} [Category.{u} J] (F : J ⥤ Type u)

/-- The **limit type** of a diagram of types: compatible families `(x_j)_j` with
`F f (x_i) = x_j` for every arrow `f : i ⟶ j` — a subtype of the product `∏_j F j`. -/
def typesLimit : Type u := {x : (j : J) → F.obj j // ∀ {i j : J} (f : i ⟶ j), F.map f (x i) = x j}

/-- The limit cone of types: the legs are the projections. -/
def typesLimitCone : Cone F where
  pt := typesLimit F
  π j := fun x => x.1 j
  w f := funext fun x => x.2 f

/-- **The category of types has all small limits**: the type of compatible families is a
limit of any diagram `F : J ⥤ Type u` with `J` small. -/
def typesLimitConeIsLimit : IsLimit (typesLimitCone F) where
  lift s := fun x => ⟨fun j => s.π j x, fun f => congrFun (s.w f) x⟩
  fac _ _ := rfl
  uniq _ _ hm := funext fun x => Subtype.ext (funext fun j => congrFun (hm j) x)

/-- The relation generating the colimit: `x ∈ F i` is identified with `F f x ∈ F j`. -/
def ColimRel : (Σ j, F.obj j) → (Σ j, F.obj j) → Prop
  | ⟨i, x⟩, ⟨j, y⟩ => ∃ f : i ⟶ j, F.map f x = y

/-- The **colimit type** of a diagram of types: the disjoint sum `Σ_j F j` divided by the
equivalence relation generated by `x ∼ F f x`. -/
def typesColimit : Type u := Quot (ColimRel F)

/-- The colimit cocone of types: the legs are the injections into the quotient. -/
def typesColimitCocone : Cocone F where
  pt := typesColimit F
  ι j := fun x => Quot.mk _ ⟨j, x⟩
  w {i _} f := funext fun x => (Quot.sound ⟨f, rfl⟩ : Quot.mk (ColimRel F) ⟨i, x⟩ = _).symm

/-- **The category of types has all small colimits**: the quotient of the disjoint sum is
a colimit of any small diagram of types. -/
def typesColimitCoconeIsColimit : IsColimit (typesColimitCocone F) where
  desc s := Quot.lift (fun p => s.ι p.1 p.2) (by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨f, rfl⟩
    exact (congrFun (s.w f) x).symm)
  fac _ _ := rfl
  uniq s m hm := funext fun q => by
    induction q using Quot.ind with
    | mk p => exact congrFun (hm p.1) p.2

end Types

/-! ## Hom-functors preserve limits -/

section HomPreserves

variable {J : Type u₁} [Category.{v₁} J] {C : Type u} [Category.{v} C]

/-- **Hom-functors preserve limits.** For a limit cone `c` of `K : J ⥤ C` and any object
`A`, the arrows `A ⟶ c.pt` form a limit of the diagram of types `j ↦ (A ⟶ K j)`: an arrow
into a limit is the same thing as a compatible family of arrows into the diagram. -/
def homPreservesLimit (A : C) {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) :
    IsLimit (c.map (homFunctor A)) where
  lift s := fun x => hc.lift ⟨A, fun j => s.π j x, fun f => congrFun (s.w f) x⟩
  fac _ j := funext fun _ => hc.fac _ j
  uniq s m hm := funext fun x =>
    hc.uniq ⟨A, fun j => s.π j x, fun f => congrFun (s.w f) x⟩ (m x) fun j => congrFun (hm j) x

end HomPreserves

end Foundations.Categories
