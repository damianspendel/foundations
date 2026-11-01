import Foundations.Categories.Equivalence

/-!
# Monads

A **monad** on a category `C` is an endofunctor `T : C ⥤ C` with two natural
transformations, a *unit* `η_X : X ⟶ T X` and a *multiplication*
`μ_X : T (T X) ⟶ T X`, satisfying associativity and unit laws — formally the same
shape as a monoid, but with composition of functors in place of multiplication of
elements ("a monad is a monoid in the category of endofunctors"). Monads were
discovered in algebraic topology (Godement's "standard constructions", 1958);
Eilenberg–Moore and Kleisli (1965) showed that **every adjunction yields a monad and
every monad arises from an adjunction**, in two extremal ways.

Monads are the categorical theory of *algebraic structure*. For the list monad
`T X = List X` (formal words), an algebra `List A → A` is precisely a way of
multiplying out words — and the laws of a monad algebra turn out to be precisely the
laws of a monoid. In this sense the monad *is* the theory of monoids, presented
without choosing generators and relations: a structuralist presentation of an
algebraic theory. We prove this correspondence in both directions below.

Through Eugenio Moggi (1989) and Philip Wadler, monads also became the standard way
of describing **computational effects** in functional programming: `Option X`
(computations that may fail), `List X` (non-deterministic computations),
`S → X × S` (computations with a mutable state `S`). The arrows of the **Kleisli
category**, `X ⟶ T Y`, are exactly "effectful functions", and Kleisli composition is
the sequencing of effects. Lean's own `do`-notation is built on this idea.

Contents: monads; the monad of an adjunction (and the list monad as the monad of the
free-monoid adjunction); the list, option and state monads on types; the Kleisli
category; Eilenberg–Moore algebras and their category; and algebras of the list
monad versus monoids.
-/

namespace Foundations.Categories

universe v u u₁ u₂ v₁ v₂

open Category

/-- A **monad** on `C`: an endofunctor `T` with unit `η_X : X ⟶ T X` and multiplication
`μ_X : T (T X) ⟶ T X`, both natural, such that `μ` is associative and `η` is a two-sided
unit for it. -/
structure Monad' (C : Type u) [Category.{v} C] where
  /-- The underlying endofunctor. -/
  T : C ⥤ C
  /-- The unit. -/
  η : (X : C) → (X ⟶ T.obj X)
  /-- The multiplication. -/
  μ : (X : C) → (T.obj (T.obj X) ⟶ T.obj X)
  /-- Naturality of the unit. -/
  η_nat : ∀ {X Y : C} (f : X ⟶ Y), f ≫ η Y = η X ≫ T.map f
  /-- Naturality of the multiplication. -/
  μ_nat : ∀ {X Y : C} (f : X ⟶ Y), T.map (T.map f) ≫ μ Y = μ X ≫ T.map f
  /-- Associativity: the two ways of flattening `T T T X` agree. -/
  assoc : ∀ X : C, T.map (μ X) ≫ μ X = μ (T.obj X) ≫ μ X
  /-- Left unit law. -/
  left_unit : ∀ X : C, η (T.obj X) ≫ μ X = 𝟙 (T.obj X)
  /-- Right unit law. -/
  right_unit : ∀ X : C, T.map (η X) ≫ μ X = 𝟙 (T.obj X)

/-! ## The monad of an adjunction -/

namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : Adjunction F G)

/-- The unit of an adjunction, with its type written as `X ⟶ G (F X)`. -/
def η' (X : C) : X ⟶ G.obj (F.obj X) := adj.unit.app X

/-- The counit of an adjunction, with its type written as `F (G Y) ⟶ Y`. -/
def ε' (Y : D) : F.obj (G.obj Y) ⟶ Y := adj.counit.app Y

/-- Naturality of the unit. -/
theorem η'_nat {X Y : C} (f : X ⟶ Y) : f ≫ adj.η' Y = adj.η' X ≫ G.map (F.map f) :=
  adj.unit.naturality f

/-- Naturality of the counit. -/
theorem ε'_nat {X Y : D} (h : X ⟶ Y) : F.map (G.map h) ≫ adj.ε' Y = adj.ε' X ≫ h :=
  adj.counit.naturality h

/-- **Every adjunction yields a monad**: `T = G ∘ F`, with the unit of the adjunction as
unit and `μ = G ε F` as multiplication. The monad laws follow from the triangle
identities and the naturality of the counit. -/
def toMonad : Monad' C where
  T := F.comp G
  η X := adj.η' X
  μ X := G.map (adj.ε' (F.obj X))
  η_nat f := adj.η'_nat f
  μ_nat {X Y} f := by
    show G.map (F.map (G.map (F.map f))) ≫ G.map (adj.ε' (F.obj Y)) =
      G.map (adj.ε' (F.obj X)) ≫ G.map (F.map f)
    rw [← G.map_comp, ← G.map_comp, adj.ε'_nat]
  assoc X := by
    show G.map (F.map (G.map (adj.ε' (F.obj X)))) ≫ G.map (adj.ε' (F.obj X)) =
      G.map (adj.ε' (F.obj (G.obj (F.obj X)))) ≫ G.map (adj.ε' (F.obj X))
    rw [← G.map_comp, ← G.map_comp, adj.ε'_nat]
  left_unit X := adj.right_triangle (F.obj X)
  right_unit X := by
    show G.map (F.map (adj.η' X)) ≫ G.map (adj.ε' (F.obj X)) = 𝟙 (G.obj (F.obj X))
    rw [← G.map_comp]
    have := adj.left_triangle X
    change F.map (adj.η' X) ≫ adj.ε' (F.obj X) = 𝟙 (F.obj X) at this
    rw [this, G.map_id]

end Adjunction

/-! ## Monads on types: lists, options, states -/

/-- The **list functor** `X ↦ List X`. -/
def listFunctor : Type u ⥤ Type u where
  obj X := List X
  map f := List.map f
  map_id _ := funext List.map_id
  map_comp f g := funext fun l => (List.map_map (f := f) (g := g) (l := l)).symm

/-- Mapping commutes with flattening. -/
theorem map_flatten {X Y : Type u} (f : X → Y) (L : List (List X)) :
    List.map f L.flatten = (L.map (List.map f)).flatten := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [List.flatten_cons, List.map_append, ih]

/-- Flattening is associative. -/
theorem flatten_flatten {X : Type u} (L : List (List (List X))) :
    (L.map List.flatten).flatten = L.flatten.flatten := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [List.flatten_cons, List.flatten_append, ih]

/-- **The list monad**: unit `x ↦ [x]`, multiplication `flatten` (concatenation of a list
of lists). Its algebras are the monoids. -/
def listMonad : Monad' (Type u) where
  T := listFunctor
  η _ := fun x => [x]
  μ _ := List.flatten
  η_nat _ := rfl
  μ_nat f := funext fun L => (map_flatten f L).symm
  assoc _ := funext fun L => flatten_flatten L
  left_unit _ := funext fun l => List.append_nil l
  right_unit _ := funext fun l => by
    show (l.map fun x => [x]).flatten = l
    induction l with
    | nil => rfl
    | cons a l ih =>
      show [a] ++ (l.map fun x => [x]).flatten = a :: l
      rw [ih]; rfl

/-- The **option functor** `X ↦ Option X` (adjoin a point "undefined"). -/
def optionFunctor : Type u ⥤ Type u where
  obj X := Option X
  map f := Option.map f
  map_id _ := funext fun o => by cases o <;> rfl
  map_comp _ _ := funext fun o => by cases o <;> rfl

/-- Flattening a nested option. -/
def optionJoin {X : Type u} : Option (Option X) → Option X
  | none => none
  | some o => o

/-- **The option (maybe) monad**: unit `some`, multiplication "flatten the nested option".
Its Kleisli arrows `X → Option Y` are the **partial functions**. -/
def optionMonad : Monad' (Type u) where
  T := optionFunctor
  η _ := some
  μ _ := optionJoin
  η_nat _ := rfl
  μ_nat _ := funext fun o => by cases o <;> rfl
  assoc _ := funext fun o => by cases o <;> rfl
  left_unit _ := rfl
  right_unit _ := funext fun o => by cases o <;> rfl

/-- The **state functor** `X ↦ (S → X × S)`: state transformers producing a value. -/
def stateFunctor (S : Type u) : Type u ⥤ Type u where
  obj X := S → X × S
  map f := fun g s => (f (g s).1, (g s).2)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The state monad**: unit returns a value without touching the state; multiplication
runs a state transformer and then the transformer it produced, on the new state. -/
def stateMonad (S : Type u) : Monad' (Type u) where
  T := stateFunctor S
  η _ := fun x s => (x, s)
  μ _ := fun m s => (m s).1 (m s).2
  η_nat _ := rfl
  μ_nat _ := rfl
  assoc _ := rfl
  left_unit _ := rfl
  right_unit _ := rfl

/-- **The list monad comes from the free-monoid adjunction**: its functor is
`forget ∘ free`, which is `List` on objects… -/
theorem freeForget_monad_obj (α : Type u) : freeForgetAdjunction.toMonad.T.obj α = List α :=
  rfl

/-- **…and its multiplication is flattening**: the counit multiplies out a word of words
in the free monoid, which is concatenation. -/
theorem freeForget_monad_μ (α : Type u) (L : List (List α)) :
    freeForgetAdjunction.toMonad.μ α L = L.flatten := by
  show listProd (L.map fun l => l) = L.flatten
  induction L with
  | nil => rfl
  | cons l L ih =>
    show l ++ listProd (L.map fun l => l) = (l :: L).flatten
    rw [ih, List.flatten_cons]

/-! ## The Kleisli category -/

section Kleisli

variable {C : Type u} [Category.{v} C]

/-- The objects of the **Kleisli category** of a monad: the objects of `C`. -/
structure Kleisli (M : Monad' C) where
  /-- The underlying object. -/
  of : C

/-- **The Kleisli category** of a monad `M`: arrows `X ⟶ Y` are arrows `X ⟶ T Y` of `C`
("effectful maps"), composed by `f ≫ T g ≫ μ` and with the unit `η` as identities. -/
instance Kleisli.category (M : Monad' C) : Category.{v} (Kleisli M) where
  Hom X Y := X.of ⟶ M.T.obj Y.of
  id X := M.η X.of
  comp f g := f ≫ M.T.map g ≫ M.μ _
  id_comp f := by
    show M.η _ ≫ M.T.map f ≫ M.μ _ = f
    rw [← Category.assoc, ← M.η_nat, Category.assoc, M.left_unit, comp_id]
  comp_id f := by
    show f ≫ M.T.map (M.η _) ≫ M.μ _ = f
    rw [M.right_unit, comp_id]
  assoc f g h := by
    show (f ≫ M.T.map g ≫ M.μ _) ≫ M.T.map h ≫ M.μ _ =
      f ≫ M.T.map (g ≫ M.T.map h ≫ M.μ _) ≫ M.μ _
    simp only [M.T.map_comp, Category.assoc]
    rw [M.assoc, ← Category.assoc (M.T.map (M.T.map h)), M.μ_nat h, Category.assoc]

/-- In the Kleisli category of the option monad, composition is composition of partial
functions: `g` is applied only if `f` was defined. -/
theorem kleisli_option_comp {X Y Z : Type u} (f : X → Option Y) (g : Y → Option Z) (x : X) :
    (show X → Option Z from
      @Category.comp (Kleisli optionMonad.{u}) _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g) x =
      (match f x with | none => none | some y => g y) := by
  show optionJoin (Option.map g (f x)) = _
  cases f x <;> rfl

end Kleisli

/-! ## Eilenberg–Moore algebras -/

section Algebras

variable {C : Type u} [Category.{v} C] (M : Monad' C)

/-- An **Eilenberg–Moore algebra** of a monad: an object `A` with a structure map
`a : T A ⟶ A` ("evaluate a formal expression") compatible with unit and multiplication. -/
structure Algebra where
  /-- The carrier. -/
  A : C
  /-- The structure map. -/
  a : M.T.obj A ⟶ A
  /-- Evaluating a generator gives the generator. -/
  unit : M.η A ≫ a = 𝟙 A
  /-- Evaluating in two stages is evaluating the flattened expression. -/
  assoc : M.T.map a ≫ a = M.μ A ≫ a

/-- A **homomorphism of algebras**: an arrow commuting with the structure maps. -/
structure AlgHom (X Y : Algebra M) where
  /-- The underlying arrow. -/
  f : X.A ⟶ Y.A
  /-- It commutes with evaluation. -/
  comm : M.T.map f ≫ Y.a = X.a ≫ f

/-- Algebra homomorphisms with equal underlying arrows are equal. -/
theorem AlgHom.ext {X Y : Algebra M} {g h : AlgHom M X Y} (e : g.f = h.f) : g = h := by
  cases g; cases h; cases e; rfl

/-- **The Eilenberg–Moore category** of algebras of a monad. -/
instance Algebra.category : Category.{v} (Algebra M) where
  Hom X Y := AlgHom M X Y
  id X := ⟨𝟙 X.A, by rw [M.T.map_id, id_comp, comp_id]⟩
  comp g h := ⟨g.f ≫ h.f, by
    rw [M.T.map_comp, Category.assoc, h.comm, ← Category.assoc, g.comm, Category.assoc]⟩
  id_comp _ := AlgHom.ext M (id_comp _)
  comp_id _ := AlgHom.ext M (comp_id _)
  assoc _ _ _ := AlgHom.ext M (Category.assoc _ _ _)

/-- **The free algebra** on `X`: carrier `T X`, structure map `μ_X`. -/
def Algebra.free (X : C) : Algebra M where
  A := M.T.obj X
  a := M.μ X
  unit := M.left_unit X
  assoc := M.assoc X

/-- The free algebra is free: any arrow `X ⟶ A` into the carrier of an algebra extends to
the algebra homomorphism `T X ⟶ A`, `T f ≫ a`. -/
def Algebra.freeLift {X : C} (B : Algebra M) (f : X ⟶ B.A) : AlgHom M (Algebra.free M X) B where
  f := M.T.map f ≫ B.a
  comm := by
    show M.T.map (M.T.map f ≫ B.a) ≫ B.a = M.μ X ≫ M.T.map f ≫ B.a
    rw [M.T.map_comp, Category.assoc, B.assoc, ← Category.assoc, M.μ_nat, Category.assoc]

end Algebras

/-! ## Algebras of the list monad are monoids -/

section ListAlgebras

/-- Multiplying out the products of a list of words is multiplying out their
concatenation. -/
theorem listProd_map_listProd {M : Type u} [Monoid' M] (L : List (List M)) :
    listProd (L.map listProd) = listProd L.flatten := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    show listProd l * listProd (L.map listProd) = listProd (l ++ L.flatten)
    rw [ih, listProd_append]

/-- **Every monoid is an algebra of the list monad**, the structure map multiplying out a
word: `[a₁, …, aₙ] ↦ a₁ ⋯ aₙ`. -/
def monoidAlgebra (M : Type u) [Monoid' M] : Algebra listMonad.{u} where
  A := M
  a := listProd
  unit := funext fun x => Monoid'.mul_one x
  assoc := funext fun L => listProd_map_listProd L

variable (X : Algebra listMonad.{u})

/-- Evaluating a one-letter word gives the letter. -/
theorem Algebra.a_single (x : X.A) : X.a [x] = x := congrFun X.unit x

/-- Evaluating the evaluations is evaluating the concatenation. -/
theorem Algebra.a_flatten (L : List (List X.A)) : X.a (L.map X.a) = X.a L.flatten :=
  congrFun X.assoc L

/-- The multiplication of a list algebra: evaluate the two-letter word. -/
def Algebra.mul (x y : X.A) : X.A := X.a [x, y]

/-- The unit of a list algebra: evaluate the empty word. -/
def Algebra.one : X.A := X.a []

/-- **Every algebra of the list monad is a monoid**, with `x * y = a [x, y]` and
`1 = a []`; associativity and the unit laws follow from the algebra laws. -/
@[instance_reducible] def Algebra.toMonoid : Monoid' X.A where
  mul := X.mul
  one := X.one
  mul_assoc x y z := by
    show X.a [X.a [x, y], z] = X.a [x, X.a [y, z]]
    have h₁ := X.a_flatten [[x, y], [z]]
    have h₂ := X.a_flatten [[x], [y, z]]
    simp only [List.map, List.flatten_cons, List.flatten_nil, X.a_single] at h₁ h₂
    rw [h₁, h₂]; rfl
  one_mul x := by
    show X.a [X.a [], x] = x
    have h := X.a_flatten [[], [x]]
    simp only [List.map, List.flatten_cons, List.flatten_nil, X.a_single] at h
    rw [h]; exact X.a_single x
  mul_one x := by
    show X.a [x, X.a []] = x
    have h := X.a_flatten [[x], []]
    simp only [List.map, List.flatten_cons, List.flatten_nil, X.a_single] at h
    rw [h]; exact X.a_single x

/-- **Round trip, monoid → algebra → monoid**: the multiplication recovered from the algebra
of a monoid is the original multiplication. -/
theorem monoidAlgebra_mul (M : Type u) [Monoid' M] (x y : M) :
    (monoidAlgebra M).mul x y = x * y := by
  show x * (y * 1) = x * y
  rw [Monoid'.mul_one]

/-- **Round trip, algebra → monoid → algebra**: multiplying out a word in the monoid of an
algebra is the algebra's structure map. Together with `monoidAlgebra_mul`: the algebras of
the list monad are exactly the monoids. -/
theorem listProd_toMonoid (l : List X.A) : @listProd X.A X.toMonoid l = X.a l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show X.a [x, @listProd X.A X.toMonoid l] = X.a (x :: l)
    rw [ih]
    have h := X.a_flatten [[x], l]
    simp only [List.map, List.flatten_cons, List.flatten_nil, X.a_single, List.append_nil,
      List.singleton_append] at h
    rw [h]

end ListAlgebras

end Foundations.Categories
