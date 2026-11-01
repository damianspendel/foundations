import Foundations.Categories.Yoneda

/-!
# Limits: products, terminal objects, equalisers, pullbacks

In set theory the cartesian product `X × Y` is a specific set of Kuratowski
pairs (Part I). Category theory replaces such constructions by **universal
properties**: a product of `X` and `Y` is *any* object `P` with arrows
`π₁ : P ⟶ X`, `π₂ : P ⟶ Y` through which every other such pair factors uniquely.
This says nothing about what `P` is made of — and that is the point. The
universal property determines `P` **up to unique isomorphism** (proved below for
each construction), which is exactly the degree of determinacy that mathematical
practice needs. Whether `(a, b)` "is" `{{a}, {a, b}}` becomes a non-question.

The same pattern gives:

* a **terminal object**: an object with exactly one arrow from every object (in
  types, the one-point type; in groups, the trivial group);
* the **equaliser** of two parallel arrows `f, g : X ⟶ Y`: the universal arrow
  `e : E ⟶ X` with `e ≫ f = e ≫ g` (in types, the subtype `{x | f x = g x}`);
* the **pullback** of a cospan `X ⟶ Z ⟵ Y`: the universal commutative square (in
  types, `{(x, y) | f x = g y}`, the fibre product).

All are instances of the general notion of a *limit* of a diagram, and by the
Yoneda philosophy a limit is a *representing object* for cones. We prove the
uniqueness theorems, and construct products, terminal objects, equalisers and
pullbacks of types, and products and terminal objects of groups.
-/

namespace Foundations.Categories

universe v u

open Category

section Universal

variable {C : Type u} [Category.{v} C]

/-! ## Terminal objects -/

/-- `T` is a **terminal object**: from every object there is exactly one arrow to `T`. -/
structure IsTerminal (T : C) where
  /-- The arrow from `X` to `T`. -/
  lift : (X : C) → (X ⟶ T)
  /-- Any two arrows into `T` are equal. -/
  uniq : ∀ {X : C} (f g : X ⟶ T), f = g

/-- **Terminal objects are unique up to isomorphism.** -/
def IsTerminal.uniqueIso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' :=
  ⟨hT'.lift T, hT.lift T', hT.uniq _ _, hT'.uniq _ _⟩

/-- **…and the isomorphism is unique.** -/
theorem IsTerminal.iso_unique {T T' : C} (hT' : IsTerminal T') (i j : T ≅ T') : i = j :=
  Iso.ext (hT'.uniq _ _)

/-! ## Binary products -/

/-- `P` with projections `π₁, π₂` is a **product** of `X` and `Y`: every pair of arrows
`W ⟶ X`, `W ⟶ Y` factors uniquely through `P`. -/
structure IsProduct (X Y P : C) (π₁ : P ⟶ X) (π₂ : P ⟶ Y) where
  /-- The induced arrow `⟨f, g⟩ : W ⟶ P`. -/
  lift : {W : C} → (W ⟶ X) → (W ⟶ Y) → (W ⟶ P)
  /-- `⟨f, g⟩ ≫ π₁ = f`. -/
  fac₁ : ∀ {W : C} (f : W ⟶ X) (g : W ⟶ Y), lift f g ≫ π₁ = f
  /-- `⟨f, g⟩ ≫ π₂ = g`. -/
  fac₂ : ∀ {W : C} (f : W ⟶ X) (g : W ⟶ Y), lift f g ≫ π₂ = g
  /-- The induced arrow is the only one with these properties. -/
  uniq : ∀ {W : C} (f : W ⟶ X) (g : W ⟶ Y) (h : W ⟶ P), h ≫ π₁ = f → h ≫ π₂ = g →
    h = lift f g

namespace IsProduct

variable {X Y P Q : C} {π₁ : P ⟶ X} {π₂ : P ⟶ Y} {ρ₁ : Q ⟶ X} {ρ₂ : Q ⟶ Y}

/-- Arrows into a product are determined by their components. -/
theorem hom_ext (hP : IsProduct X Y P π₁ π₂) {W : C} {h k : W ⟶ P} (h₁ : h ≫ π₁ = k ≫ π₁)
    (h₂ : h ≫ π₂ = k ≫ π₂) : h = k :=
  (hP.uniq _ _ h h₁ h₂).trans (hP.uniq _ _ k rfl rfl).symm

/-- Pre-composing a pairing: `a ≫ ⟨f, g⟩ = ⟨a ≫ f, a ≫ g⟩`. -/
theorem comp_lift (hP : IsProduct X Y P π₁ π₂) {V W : C} (a : V ⟶ W) (f : W ⟶ X)
    (g : W ⟶ Y) : a ≫ hP.lift f g = hP.lift (a ≫ f) (a ≫ g) :=
  hP.uniq _ _ _ (by rw [assoc, hP.fac₁]) (by rw [assoc, hP.fac₂])

/-- **Products are unique up to isomorphism**, compatible with the projections. -/
def uniqueIso (hP : IsProduct X Y P π₁ π₂) (hQ : IsProduct X Y Q ρ₁ ρ₂) : P ≅ Q where
  hom := hQ.lift π₁ π₂
  inv := hP.lift ρ₁ ρ₂
  hom_inv_id := hP.hom_ext (by rw [assoc, hP.fac₁, hQ.fac₁, id_comp])
    (by rw [assoc, hP.fac₂, hQ.fac₂, id_comp])
  inv_hom_id := hQ.hom_ext (by rw [assoc, hQ.fac₁, hP.fac₁, id_comp])
    (by rw [assoc, hQ.fac₂, hP.fac₂, id_comp])

/-- The comparison isomorphism respects the projections. -/
theorem uniqueIso_hom_fac (hP : IsProduct X Y P π₁ π₂) (hQ : IsProduct X Y Q ρ₁ ρ₂) :
    (uniqueIso hP hQ).hom ≫ ρ₁ = π₁ ∧ (uniqueIso hP hQ).hom ≫ ρ₂ = π₂ :=
  ⟨hQ.fac₁ _ _, hQ.fac₂ _ _⟩

/-- **…and it is the unique isomorphism respecting the projections.** -/
theorem iso_unique (hP : IsProduct X Y P π₁ π₂) (hQ : IsProduct X Y Q ρ₁ ρ₂) (i : P ≅ Q)
    (h₁ : i.hom ≫ ρ₁ = π₁) (h₂ : i.hom ≫ ρ₂ = π₂) : i = uniqueIso hP hQ :=
  Iso.ext (hQ.hom_ext (by rw [h₁]; exact (hQ.fac₁ _ _).symm) (by rw [h₂]; exact (hQ.fac₂ _ _).symm))

end IsProduct

/-! ## Equalisers -/

/-- `e : E ⟶ X` is an **equaliser** of `f, g : X ⟶ Y`: `e ≫ f = e ≫ g`, and every arrow
equalising `f` and `g` factors uniquely through `e`. -/
structure IsEqualizer {X Y : C} (f g : X ⟶ Y) (E : C) (e : E ⟶ X) where
  /-- `e` equalises `f` and `g`. -/
  w : e ≫ f = e ≫ g
  /-- The factorisation of an equalising arrow. -/
  lift : {W : C} → (k : W ⟶ X) → k ≫ f = k ≫ g → (W ⟶ E)
  /-- The factorisation is a factorisation. -/
  fac : ∀ {W : C} (k : W ⟶ X) (hk : k ≫ f = k ≫ g), lift k hk ≫ e = k
  /-- The factorisation is unique. -/
  uniq : ∀ {W : C} (k : W ⟶ X) (hk : k ≫ f = k ≫ g) (h : W ⟶ E), h ≫ e = k → h = lift k hk

namespace IsEqualizer

variable {X Y E E' : C} {f g : X ⟶ Y} {e : E ⟶ X} {e' : E' ⟶ X}

/-- **Equalisers are monomorphisms.** -/
theorem mono (hE : IsEqualizer f g E e) {W : C} {h k : W ⟶ E} (hk : h ≫ e = k ≫ e) : h = k := by
  have hw : (k ≫ e) ≫ f = (k ≫ e) ≫ g := by rw [assoc, hE.w, assoc]
  exact (hE.uniq _ hw h hk).trans (hE.uniq _ hw k rfl).symm

/-- **Equalisers are unique up to isomorphism.** -/
def uniqueIso (hE : IsEqualizer f g E e) (hE' : IsEqualizer f g E' e') : E ≅ E' where
  hom := hE'.lift e hE.w
  inv := hE.lift e' hE'.w
  hom_inv_id := hE.mono (by rw [assoc, hE.fac, hE'.fac, id_comp])
  inv_hom_id := hE'.mono (by rw [assoc, hE'.fac, hE.fac, id_comp])

/-- **…uniquely so**, among isomorphisms compatible with the equalising arrows. -/
theorem iso_unique (hE : IsEqualizer f g E e) (hE' : IsEqualizer f g E' e') (i : E ≅ E')
    (h : i.hom ≫ e' = e) : i = uniqueIso hE hE' :=
  Iso.ext (hE'.mono (by rw [h]; exact (hE'.fac _ _).symm))

end IsEqualizer

/-! ## Pullbacks -/

/-- A commutative square `p₁ ≫ f = p₂ ≫ g` is a **pullback** of the cospan
`X ⟶ Z ⟵ Y` when every other commutative square over the cospan factors uniquely
through it. -/
structure IsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (P : C) (p₁ : P ⟶ X) (p₂ : P ⟶ Y) where
  /-- The square commutes. -/
  w : p₁ ≫ f = p₂ ≫ g
  /-- The factorisation of another commutative square. -/
  lift : {W : C} → (k₁ : W ⟶ X) → (k₂ : W ⟶ Y) → k₁ ≫ f = k₂ ≫ g → (W ⟶ P)
  /-- First component of the factorisation. -/
  fac₁ : ∀ {W : C} (k₁ : W ⟶ X) (k₂ : W ⟶ Y) (hk : k₁ ≫ f = k₂ ≫ g), lift k₁ k₂ hk ≫ p₁ = k₁
  /-- Second component of the factorisation. -/
  fac₂ : ∀ {W : C} (k₁ : W ⟶ X) (k₂ : W ⟶ Y) (hk : k₁ ≫ f = k₂ ≫ g), lift k₁ k₂ hk ≫ p₂ = k₂
  /-- Uniqueness of the factorisation. -/
  uniq : ∀ {W : C} (k₁ : W ⟶ X) (k₂ : W ⟶ Y) (hk : k₁ ≫ f = k₂ ≫ g) (h : W ⟶ P),
    h ≫ p₁ = k₁ → h ≫ p₂ = k₂ → h = lift k₁ k₂ hk

namespace IsPullback

variable {X Y Z P Q : C} {f : X ⟶ Z} {g : Y ⟶ Z} {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
  {q₁ : Q ⟶ X} {q₂ : Q ⟶ Y}

/-- Arrows into a pullback are determined by their two components. -/
theorem hom_ext (hP : IsPullback f g P p₁ p₂) {W : C} {h k : W ⟶ P} (h₁ : h ≫ p₁ = k ≫ p₁)
    (h₂ : h ≫ p₂ = k ≫ p₂) : h = k := by
  have hw : (k ≫ p₁) ≫ f = (k ≫ p₂) ≫ g := by rw [assoc, hP.w, assoc]
  exact (hP.uniq _ _ hw h h₁ h₂).trans (hP.uniq _ _ hw k rfl rfl).symm

/-- **Pullbacks are unique up to isomorphism.** -/
def uniqueIso (hP : IsPullback f g P p₁ p₂) (hQ : IsPullback f g Q q₁ q₂) : P ≅ Q where
  hom := hQ.lift p₁ p₂ hP.w
  inv := hP.lift q₁ q₂ hQ.w
  hom_inv_id := hP.hom_ext (by rw [assoc, hP.fac₁, hQ.fac₁, id_comp])
    (by rw [assoc, hP.fac₂, hQ.fac₂, id_comp])
  inv_hom_id := hQ.hom_ext (by rw [assoc, hQ.fac₁, hP.fac₁, id_comp])
    (by rw [assoc, hQ.fac₂, hP.fac₂, id_comp])

/-- **…uniquely so**, among isomorphisms compatible with the projections. -/
theorem iso_unique (hP : IsPullback f g P p₁ p₂) (hQ : IsPullback f g Q q₁ q₂) (i : P ≅ Q)
    (h₁ : i.hom ≫ q₁ = p₁) (h₂ : i.hom ≫ q₂ = p₂) : i = uniqueIso hP hQ :=
  Iso.ext (hQ.hom_ext (by rw [h₁]; exact (hQ.fac₁ _ _ _).symm)
    (by rw [h₂]; exact (hQ.fac₂ _ _ _).symm))

end IsPullback

end Universal

/-! ## Limits of types -/

/-- **The one-point type is terminal** in the category of types. -/
def types_terminal : IsTerminal (PUnit.{u + 1} : Type u) where
  lift _ := fun _ => PUnit.unit
  uniq _ _ := funext fun _ => rfl

/-- **The cartesian product is a product** in the category of types. -/
def types_product (X Y : Type u) :
    IsProduct X Y (X × Y) (fun p : X × Y => p.1) (fun p : X × Y => p.2) where
  lift f g := fun w => (f w, g w)
  fac₁ _ _ := rfl
  fac₂ _ _ := rfl
  uniq f g h h₁ h₂ := funext fun w => by
    subst h₁ h₂
    rfl

/-- **The subtype `{x | f x = g x}` is an equaliser** in the category of types. -/
def types_equalizer {X Y : Type u} (f g : X ⟶ Y) :
    IsEqualizer f g {x : X // f x = g x} (fun x => x.1) where
  w := funext fun x => x.2
  lift k hk := fun w => ⟨k w, congrFun hk w⟩
  fac _ _ := rfl
  uniq _ _ _ hh := funext fun w => Subtype.ext (congrFun hh w)

/-- **The fibre product `{(x, y) | f x = g y}` is a pullback** in the category of types. -/
def types_pullback {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback f g {p : X × Y // f p.1 = g p.2} (fun p => p.1.1) (fun p => p.1.2) where
  w := funext fun p => p.2
  lift k₁ k₂ hk := fun w => ⟨(k₁ w, k₂ w), congrFun hk w⟩
  fac₁ _ _ _ := rfl
  fac₂ _ _ _ := rfl
  uniq k₁ k₂ hk h h₁ h₂ := funext fun w => Subtype.ext (by
    subst h₁ h₂
    rfl)

/-! ## Limits of groups -/

open Foundations.Algebra

/-- The **direct product** of two groups, with componentwise operations. -/
instance prodGroup (G H : Type u) [Group G] [Group H] : Group (G × H) where
  mul a b := (a.1 * b.1, a.2 * b.2)
  one := (1, 1)
  inv a := (a.1⁻¹, a.2⁻¹)
  mul_assoc a b c := by
    show (a.1 * b.1 * c.1, a.2 * b.2 * c.2) = (a.1 * (b.1 * c.1), a.2 * (b.2 * c.2))
    rw [Group.mul_assoc, Group.mul_assoc]
  one_mul a := by
    show ((1 : G) * a.1, (1 : H) * a.2) = a
    rw [Group.one_mul, Group.one_mul]
  inv_mul_cancel a := by
    show (a.1⁻¹ * a.1, a.2⁻¹ * a.2) = ((1 : G), (1 : H))
    rw [Group.inv_mul_cancel, Group.inv_mul_cancel]

/-- The trivial group on the one-point type (in any universe). -/
instance punitGroup : Group PUnit.{u + 1} where
  mul _ _ := PUnit.unit
  one := PUnit.unit
  inv _ := PUnit.unit
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  inv_mul_cancel _ := rfl

/-- **The trivial group is terminal** in the category of groups. -/
def groups_terminal : IsTerminal (GroupCat.mk PUnit.{u + 1}) where
  lift G :=
    (⟨fun _ => PUnit.unit, fun _ _ => rfl⟩ : Foundations.Algebra.Hom G.carrier PUnit.{u + 1})
  uniq _ _ := Foundations.Algebra.Hom.ext fun _ => rfl

/-- The first projection of a direct product, as a homomorphism. -/
def fstHom (G H : Type u) [Group G] [Group H] : Foundations.Algebra.Hom (G × H) G :=
  ⟨fun p => p.1, fun _ _ => rfl⟩

/-- The second projection of a direct product, as a homomorphism. -/
def sndHom (G H : Type u) [Group G] [Group H] : Foundations.Algebra.Hom (G × H) H :=
  ⟨fun p => p.2, fun _ _ => rfl⟩

/-- **The direct product is a product** in the category of groups. -/
def groups_product (G H : GroupCat.{u}) :
    IsProduct G H (GroupCat.mk (G.carrier × H.carrier)) (fstHom G.carrier H.carrier)
      (sndHom G.carrier H.carrier) where
  lift f g := (⟨fun w => (f.toFun w, g.toFun w), fun a b => by
    show (f.toFun (a * b), g.toFun (a * b)) = (f.toFun a * f.toFun b, g.toFun a * g.toFun b)
    rw [f.map_mul, g.map_mul]⟩ : Foundations.Algebra.Hom _ (G.carrier × H.carrier))
  fac₁ _ _ := Foundations.Algebra.Hom.ext fun _ => rfl
  fac₂ _ _ := Foundations.Algebra.Hom.ext fun _ => rfl
  uniq f g h h₁ h₂ := Foundations.Algebra.Hom.ext fun w => by
    subst h₁ h₂
    rfl

end Foundations.Categories
