import Foundations.Langlands.Rep.Induced
import Foundations.Langlands.Rep.S3

/-!
# The standard representation of `S₃` is induced

The smallest example of an irreducible induced representation of a non-abelian group: the
2-dimensional irreducible representation of `S₃` is induced from a character of the rotation
subgroup `C₃ = ⟨r⟩`. In the model `S₃ = C₃ ⋊ C₂` of `S3`, the rotations are the elements
`⟨a, 0⟩ = r^a`; they form a subgroup `S3.rot` of order 3 (index 2), and `λ(r^a) = ω^a`, with `ω`
the primitive cube root of unity of `Monomial`, is a non-trivial character of it
(`S3.lam_r`, `S3.lam_r_ne_one`).

By `character_indRep` the character of `Ind^{S₃}_{C₃} λ` is the induced class function
`Ind λ(g) = (1/3) Σ_x λ°(x g x⁻¹)`. Conjugating a rotation `r^a` gives `r^a` or `r^{-a}`, three
times each, and conjugating a reflection gives a reflection, outside `C₃`; hence
`Ind λ(r^a) = ω^a + ω^{-a}` and `Ind λ(r^a s) = 0`, which is the character of `std`
(`S3.indFun_lam`). By `iso_of_character_eq`, equal characters force an isomorphism:
`Ind^{S₃}_{C₃} λ ≅ std` (`S3.std_iso_induced`). As a by-product the induced representation is
irreducible (`S3.induced_irreducible`).

In Langlands' language this is the simplest instance of *automorphic induction*: a character of
a subgroup of index 2 produces an irreducible 2-dimensional representation of the big group,
just as Hecke characters of an imaginary quadratic field induce to 2-dimensional Galois
representations of `ℚ` attached to CM modular forms.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

namespace S3

/-- **The rotation subgroup** `C₃ = {1, r, r²}` of `S₃`: the elements `⟨a, 0⟩`. -/
def rot : Subgroup S3 where
  carrier x := x.b = 0
  one_mem := rfl
  mul_mem := by
    intro x y hx hy
    show x.b + y.b = 0
    rw [hx, hy]; rfl
  inv_mem := by intro x hx; exact hx

/-- Membership in the rotation subgroup is decidable. -/
instance (x : S3) : Decidable (x ∈ rot) := inferInstanceAs (Decidable (x.b = 0))

/-- `|C₃| = 3`. -/
theorem card_rot : card rot = 3 := by
  rw [card_subtype, count_eq_countP]; rfl

/-- **A non-trivial character of `C₃`**: `λ(r^a) = ω^a`. -/
noncomputable def lam (h : rot) : C := cpow omega3 h.1.a.val

/-- `λ` is multiplicative. -/
theorem lam_mul (x y : rot) : lam (x * y) = lam x * lam y := by
  have e : (x * y).1.a = x.1.a + y.1.a := by
    show x.1.a + (if x.1.b = 0 then y.1.a else -y.1.a) = _
    simp only [show x.1.b = 0 from x.2, ↓reduceIte]
  unfold lam
  rw [e, cpow_fin_add omega3_cube]

/-- The character `λ` as a 1-dimensional representation of `C₃`. -/
noncomputable def chiRot : Rep rot C Unit := Rep.ofHom lam rfl lam_mul

/-- The character of `chiRot` is `λ`. -/
theorem character_chiRot : character chiRot = lam := by
  funext h; exact Rep.isum_unit _

/-- `λ(r) = ω`. -/
theorem lam_r : lam ⟨r, rfl⟩ = omega3 := Ring.one_mul _

/-- **`λ` is non-trivial**: `λ(r) = ω ≠ 1`. -/
theorem lam_r_ne_one : lam ⟨r, rfl⟩ ≠ 1 := by
  rw [lam_r]
  intro h
  apply three_ne_zero_C
  have hs := omega3_spec
  rw [h] at hs
  grind

/-- `λ°(x) = ω^a` at `x = r^a`, and `0` at reflections. -/
theorem ext0_lam (x : S3) : ext0 rot lam x = if x.b = 0 then cpow omega3 x.a.val else 0 := by
  by_cases hx : x.b = 0
  · rw [ext0_mem rot lam (show x ∈ rot from hx)]; simp only [hx, ↓reduceIte]; rfl
  · rw [ext0_not_mem rot lam (show x ∉ rot from hx)]; simp only [hx, ↓reduceIte]

/-- Conjugates of a rotation: `x r^a x⁻¹ = r^a` if `x` is a rotation, `r^{-a}` otherwise. -/
theorem conj_rot (x : S3) (a : Fin 3) :
    x * ⟨a, 0⟩ * x⁻¹ = ⟨if x.b = 0 then a else -a, 0⟩ := by
  obtain ⟨c, d⟩ := x
  show mul (mul _ _) (inv _) = _
  revert a c d; decide

/-- Conjugates of a reflection are reflections. -/
theorem conj_refl (x : S3) (a : Fin 3) : (x * ⟨a, 1⟩ * x⁻¹).b = 1 := by
  obtain ⟨c, d⟩ := x
  show (mul (mul _ _) (inv _)).b = _
  revert a c d; decide

/-- **The induced character.** `Ind^{S₃}_{C₃} λ = χ_std`: both are `ω^a + ω^{2a}` at `r^a` and
`0` at reflections. -/
theorem indFun_lam (g : S3) : indFun rot lam g = character std g := by
  obtain ⟨a, b⟩ := g
  have hn : (ncast 3 : C) * natInv 3 = 1 := ncast_mul_natInv (by decide)
  have h3 : (ncast 3 : C) = 1 + 1 + 1 := rfl
  rw [indFun, card_rot, character_std]
  match b with
  | 0 =>
    have ha : -a = a + a := by revert a; decide
    have hx : ∀ x : S3, ext0 rot lam (x * ⟨a, 0⟩ * x⁻¹) =
        if x.b = 0 then cpow omega3 a.val else cpow omega3 (-a).val := fun x => by
      rw [conj_rot, ext0_lam]
      by_cases hb : x.b = 0
      · simp only [hb, ↓reduceIte]
      · simp only [hb, ↓reduceIte]
    rw [isum_congr hx, isum_S3]
    simp (config := { decide := true }) only [↓reduceIte]
    rw [ha]
    grind
  | 1 =>
    rw [isum_eq_zero (fun x => by
      rw [ext0_lam]; simp only [conj_refl]; simp (config := { decide := true }) only [↓reduceIte])]
    simp (config := { decide := true }) only [↓reduceIte]
    exact Ring.mul_zero _

/-- **`std` is induced from `C₃`.** The 2-dimensional standard representation of `S₃` is
isomorphic to the representation `Ind^{S₃}_{C₃} λ` induced from the non-trivial character
`λ(r^a) = ω^a` of the rotation subgroup. -/
theorem std_iso_induced : Iso (indRep rot chiRot) std := by
  apply iso_of_character_eq
  rw [character_indRep, character_chiRot]
  funext g; exact indFun_lam g

/-- The induced representation `Ind^{S₃}_{C₃} λ` is irreducible. -/
theorem induced_irreducible : Irreducible (indRep rot chiRot) := by
  rw [irreducible_iff_pairing, character_eq_of_iso std_iso_induced]
  exact (irreducible_iff_pairing std).1 std_irreducible

end S3

end Foundations.Langlands
