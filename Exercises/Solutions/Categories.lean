import Foundations.Categories.Lawvere

/-!
# Exercises VII: Categories

Problems on Part VII (`Foundations/Categories`): isomorphisms, the Yoneda lemma and its
consequences, and Lawvere's fixed-point theorem.

Composition is written in diagrammatic order: `f ≫ g` is "first `f`, then `g`". The
hom-functor `homFunctor A : C ⥤ Type` sends `X` to `A ⟶ X`, and `homPre f` is the natural
transformation `Hom(B, −) ⟶ Hom(A, −)` given by pre-composition with `f : A ⟶ B`. In the
category of types, `≫` is function composition and `𝟙` the identity
(`types_comp_apply`, `types_id_apply`).

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in `Exercises/Problems/Categories.lean`.
-/

namespace Exercises.Categories

open Foundations.Categories Foundations.Categories.Category

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Isomorphisms -/

/-- **Exercise 7.1 (★★) — Inverses are unique.** If `g` is a right inverse of `f`
(`f ≫ g = 𝟙`) and `h` is a left inverse (`h ≫ f = 𝟙`), then `g = h`.

*Hint:* compute `h ≫ f ≫ g` in two ways, using associativity and the unit laws.

*Uses:* `Category.assoc`, `Category.id_comp`, `Category.comp_id`. -/
theorem inverse_unique {X Y : C} {f : X ⟶ Y} {g h : Y ⟶ X} (hg : f ≫ g = 𝟙 X)
    (hh : h ≫ f = 𝟙 Y) : g = h := by
  -- SOLUTION
  calc g = 𝟙 Y ≫ g := (id_comp g).symm
    _ = (h ≫ f) ≫ g := by rw [hh]
    _ = h ≫ (f ≫ g) := assoc h f g
    _ = h := by rw [hg, comp_id]
  -- END

/-- **Exercise 7.2 (★★) — Isomorphisms can be cancelled.** If `i : X ≅ Y` and
`i.hom ≫ a = i.hom ≫ b`, then `a = b` (every isomorphism is a monomorphism).

*Hint:* compose with `i.inv` on the left.

*Uses:* `Iso.inv_hom_id`, `Category.assoc`, `Category.id_comp`. -/
theorem iso_cancel_left {X Y Z : C} (i : X ≅ Y) {a b : Y ⟶ Z} (h : i.hom ≫ a = i.hom ≫ b) :
    a = b := by
  -- SOLUTION
  calc a = (i.inv ≫ i.hom) ≫ a := by rw [i.inv_hom_id, id_comp]
    _ = i.inv ≫ (i.hom ≫ a) := assoc _ _ _
    _ = i.inv ≫ (i.hom ≫ b) := by rw [h]
    _ = b := by rw [← assoc, i.inv_hom_id, id_comp]
  -- END

/-! ## The Yoneda lemma -/

/-- **Exercise 7.3 (★) — Endo-transformations of a hom-functor.** Every natural transformation
`α : Hom(A, −) ⟶ Hom(A, −)` is pre-composition with the single arrow `α_A(𝟙 A) : A ⟶ A`,
i.e. `α_X(h) = α_A(𝟙 A) ≫ h`.

*Hint:* the key computation behind the Yoneda lemma, for `F = Hom(A, −)`.

*Uses:* `app_eq_map`. -/
theorem homFunctor_endo {A X : C} (α : NatTrans (homFunctor A) (homFunctor A)) (h : A ⟶ X) :
    α.app X h = α.app A (𝟙 A) ≫ h := by
  -- SOLUTION
  exact app_eq_map α h
  -- END

/-- **Exercise 7.4 (★) — A transformation is determined by one element.** Two natural
transformations `Hom(A, −) ⟶ F` that agree on `𝟙 A` are equal.

*Hint:* the Yoneda bijection `α ↦ α_A(𝟙 A)` is injective.

*Uses:* `yoneda`, `Bij.injective`. -/
theorem nat_trans_ext_id {F : C ⥤ Type v} {A : C} {α β : NatTrans (homFunctor A) F}
    (h : α.app A (𝟙 A) = β.app A (𝟙 A)) : α = β := by
  -- SOLUTION
  exact (yoneda F A).injective h
  -- END

/-- **Exercise 7.5 (★★) — The Yoneda principle, pointwise.** If `f, g : A ⟶ B` satisfy
`f ≫ h = g ≫ h` for every arrow `h` out of `B`, then `f = g`.

*Hint:* the hypothesis says `homPre f` and `homPre g` have the same components; the Yoneda
embedding is faithful. (Alternatively: test with a single, well-chosen `h`.)

*Uses:* `homPre_injective`, `NatTrans.ext`. -/
theorem eq_of_comp_eq {A B : C} {f g : A ⟶ B} (h : ∀ (X : C) (k : B ⟶ X), f ≫ k = g ≫ k) :
    f = g := by
  -- SOLUTION
  exact homPre_injective (NatTrans.ext fun X => funext fun k => h X k)
  -- END

/-- **Exercise 7.6 (★★★) — Isomorphic objects have isomorphic hom-functors.** If `A ≅ B`, then
`Hom(A, −)` and `Hom(B, −)` are naturally isomorphic. (This is the converse of the library's
`isoOfHomIso`; together they say an object is determined up to isomorphism by its
hom-functor.)

*Hint:* for `i : A ≅ B`, pre-composition with `i.inv : B ⟶ A` turns arrows out of `A` into
arrows out of `B`, and `homPre i.hom` goes back. The two inverse laws are equalities of
functions; prove them with `funext` and the inverse laws of `i`.

*Uses:* `homPre`, `NatIso`, `Iso.hom_inv_id`, `Iso.inv_hom_id`, `Category.assoc`. -/
theorem homFunctor_iso_of_iso {A B : C} (i : A ≅ B) :
    Nonempty (NatIso (homFunctor A) (homFunctor B)) := by
  -- SOLUTION
  refine ⟨⟨homPre i.inv, homPre i.hom, fun X => ?_, fun X => ?_⟩⟩
  · funext (g : A ⟶ X)
    show i.hom ≫ (i.inv ≫ g) = g
    rw [← assoc, i.hom_inv_id, id_comp]
  · funext (g : B ⟶ X)
    show i.inv ≫ (i.hom ≫ g) = g
    rw [← assoc, i.inv_hom_id, id_comp]
  -- END

/-! ## Lawvere's fixed-point theorem -/

/-- **Exercise 7.7 (★★) — Cantor for number-valued functions.** No function
`f : A → (A → ℕ)` is surjective.

*Hint:* by Lawvere's theorem, a surjection would give every map `ℕ → ℕ` a fixed point.
Which map has none?

*Uses:* `lawvere_types`. -/
theorem no_surjection_nat {A : Type} : ¬ ∃ f : A → (A → Nat), Function.Surjective f := by
  -- SOLUTION
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ := lawvere_types f hf (fun n => n + 1)
  omega
  -- END

end Exercises.Categories
