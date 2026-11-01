import Foundations.Categories.Adjunctions

/-!
# Lawvere's fixed-point theorem: the diagonal argument, once and for all

Cantor's theorem (no set maps onto its power set), Russell's paradox (there is
no set of all sets not containing themselves), Gödel's diagonal lemma (every
property of sentences has a "fixed point" sentence asserting it of itself),
Tarski's undefinability of truth, and Turing's unsolvability of the halting
problem — all are proved by a **diagonal argument**. In *Diagonal arguments and
cartesian closed categories* (1969) F. William Lawvere showed that they are all
instances of a single, almost trivial, theorem about categories with products:

> **Lawvere's fixed-point theorem.** If `φ : A × A ⟶ B` is *point-surjective* —
> every arrow `g : A ⟶ B` is `φ(a, −)` for some point `a` of `A` — then every
> endomorphism `t : B ⟶ B` has a fixed point.

Proof: apply the hypothesis to `g = t ∘ φ ∘ Δ` (where `Δ` is the diagonal
`x ↦ (x, x)`), obtaining a point `a` with `φ(a, x) = t(φ(x, x))` for all `x`;
then `b = φ(a, a)` satisfies `b = t(b)`. Read *contrapositively*, it is the
diagonal argument: if some `t` has **no** fixed point — negation on truth values,
`P ↦ ¬P`, or `b ↦ !b` on booleans — then **no** `φ` can be point-surjective:

* with `B = Prop` and `t = ¬`: no type surjects onto its power type `A → Prop`
  (**Cantor's theorem**; with `A` the "universe" and `φ = ∈` it is **Russell's
  paradox**, already met in `Paradoxes.lean` of Part I);
* with `B` the sentences of arithmetic and `φ` substitution: some sentence is
  equivalent to the negation of its own provability (**Gödel**; here `t` *does*
  have a fixed point, which is the content of the diagonal lemma);
* with `B = Bool` and `φ` the universal program: no program decides halting
  (**Turing**).

The paradoxes of self-reference are thus not about sets, sentences or machines as
such, but about the *structure* of self-application — a vindication of the
categorical point of view. We prove the theorem in an arbitrary category (with
"points" generalised to arrows out of any object `T`; classically `T` is the
terminal object), and derive Cantor's theorem for types from it.
-/

namespace Foundations.Categories

universe v u

open Category

section General

variable {C : Type u} [Category.{v} C]

/-- **Lawvere's fixed-point theorem.** Let `A × A` be a product (projections `p₁, p₂`)
and `φ : A × A ⟶ B` be point-surjective with respect to `T`-points: for every
`g : A ⟶ B` there is `a : T ⟶ A` with `φ ∘ ⟨a, x⟩ = g ∘ x` for all `x : T ⟶ A`. Then every
`t : B ⟶ B` has a fixed `T`-point `b : T ⟶ B`, `b ≫ t = b`. -/
theorem lawvere_fixed_point {A B AA T : C} {p₁ p₂ : AA ⟶ A} (hP : IsProduct A A AA p₁ p₂)
    (φ : AA ⟶ B)
    (hφ : ∀ g : A ⟶ B, ∃ a : T ⟶ A, ∀ x : T ⟶ A, hP.lift a x ≫ φ = x ≫ g)
    (t : B ⟶ B) : ∃ b : T ⟶ B, b ≫ t = b := by
  obtain ⟨a, ha⟩ := hφ (hP.lift (𝟙 A) (𝟙 A) ≫ φ ≫ t)
  refine ⟨hP.lift a a ≫ φ, ?_⟩
  have h₁ := ha a
  have h₂ : a ≫ hP.lift (𝟙 A) (𝟙 A) = hP.lift a a := by rw [hP.comp_lift, comp_id]
  calc (hP.lift a a ≫ φ) ≫ t = (a ≫ hP.lift (𝟙 A) (𝟙 A)) ≫ φ ≫ t := by rw [h₂, assoc]
    _ = a ≫ (hP.lift (𝟙 A) (𝟙 A) ≫ φ ≫ t) := by rw [assoc]
    _ = hP.lift a a ≫ φ := h₁.symm

/-- **Contrapositive form (the diagonal argument).** If some `t : B ⟶ B` has no fixed
`T`-point, then no `φ : A × A ⟶ B` is point-surjective. -/
theorem no_point_surjective {A B AA T : C} {p₁ p₂ : AA ⟶ A} (hP : IsProduct A A AA p₁ p₂)
    (t : B ⟶ B) (ht : ∀ b : T ⟶ B, b ≫ t ≠ b) (φ : AA ⟶ B) :
    ¬ ∀ g : A ⟶ B, ∃ a : T ⟶ A, ∀ x : T ⟶ A, hP.lift a x ≫ φ = x ≫ g := fun hφ =>
  let ⟨b, hb⟩ := lawvere_fixed_point hP φ hφ t
  ht b hb

end General

/-! ## The case of types -/

/-- **Lawvere's theorem for types.** If `f : A → (A → B)` is surjective, every function
`t : B → B` has a fixed point. (Derived from the categorical theorem, with points
`PUnit ⟶ A` and the cartesian product of types.) -/
theorem lawvere_types {A B : Type u} (f : A → A → B) (hf : Function.Surjective f) (t : B → B) :
    ∃ b, t b = b := by
  obtain ⟨b, hb⟩ := lawvere_fixed_point (T := PUnit.{u + 1}) (types_product A A)
    (fun p : A × A => f p.1 p.2)
    (fun g => by
      obtain ⟨a, ha⟩ := hf g
      exact ⟨fun _ => a, fun x => funext fun u => by
        change f a (x u) = g (x u)
        rw [ha]⟩)
    t
  exact ⟨b PUnit.unit, congrFun hb PUnit.unit⟩

/-- **Cantor's theorem from Lawvere's**: no type surjects onto its power type
`A → Prop`, because negation has no fixed point (`P = ¬P` is impossible). This is
the theorem `Sets.cantor_type` of Part I, now as a corollary of a fact about
categories. -/
theorem cantor_via_lawvere {A : Type} : ¬ ∃ f : A → (A → Prop), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨P, hP⟩ := lawvere_types f hf Not
  have hn : ¬ P := fun h => cast hP.symm h h
  exact hn (cast hP hn)

/-- **No surjection onto binary sequences**: `A → Bool` is never the image of `A`, because
boolean negation has no fixed point (Cantor's diagonal argument for `{0,1}`-sequences). -/
theorem no_surjection_bool {A : Type} : ¬ ∃ f : A → (A → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨b, hb⟩ := lawvere_types f hf (fun b => !b)
  cases b <;> simp at hb

/-- **Russell's paradox, Lawvere-style**: for any type `U` and any relation `mem` on it,
not every predicate on `U` is of the form `mem u` — in particular "`x` is not a member of
itself" is not. -/
theorem russell_via_lawvere {U : Type} (mem : U → U → Prop) :
    ¬ ∀ P : U → Prop, ∃ u, mem u = P := fun h =>
  cantor_via_lawvere ⟨mem, h⟩

/-- **Fixed points are unavoidable**: if some type `A` surjects onto `A → B`, then every
function on `B` has a fixed point — so `B` has at most one element. -/
theorem subsingleton_of_surjective {A B : Type u} (f : A → A → B) (hf : Function.Surjective f)
    (b₁ b₂ : B) : b₁ = b₂ := by
  apply Classical.byContradiction
  intro hne
  open Classical in
  obtain ⟨b, hb⟩ := lawvere_types f hf (fun b => if b = b₁ then b₂ else b₁)
  by_cases h : b = b₁
  · simp only [h, ↓reduceIte] at hb; exact hne hb.symm
  · simp only [h, ↓reduceIte] at hb; exact h hb.symm

end Foundations.Categories
