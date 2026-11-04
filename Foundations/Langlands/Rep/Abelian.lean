import Foundations.Langlands.Rep.Multiplicity
import Foundations.NumberTheory.DualGroup

/-!
# Abelian groups: irreducible representations are characters

For a finite **abelian** group the theory collapses to the one built in
`NumberTheory/DualGroup`. Each `ρ(g)` commutes with every `ρ(h)`, so it is a `G`-map from `ρ`
to itself, and by Schur's lemma over `ℂ` it is a scalar. Then *every* line is invariant, so an
irreducible representation has degree one, and its character `g ↦ ρ(g)` is a homomorphism
`G → ℂ^×`: an element of the dual group `Ĝ = Character G`. Conversely every element of `Ĝ` is
a one-dimensional, hence irreducible, representation.

This is the bridge between Part XV and the character theory of Dirichlet: the irreducible
characters of a finite abelian group in the sense of Frobenius are exactly the characters
`IsChar` used for Dirichlet's theorem on primes in progressions. In Langlands' language it is the
case `n = 1`, where "Galois representations" are characters and the reciprocity laws of class
field theory take over; the non-abelian groups, whose irreducibles have higher degree, are
where the programme proper begins.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)
open Foundations.NumberTheory (IsChar Character)

set_option linter.unusedSectionVars false

universe u v w

variable {G : Type u} [CommGroup G] [FiniteType G] {ι : Type v} [FiniteType ι]

/-- In an abelian group every `ρ(g)` is a `G`-map from `ρ` to itself. -/
theorem isGMap_of_comm {K : Type w} [CommRing K] (ρ : Rep G K ι) (g : G) : IsGMap ρ ρ (ρ g) :=
  fun h => by
    show ρ.toFun g * ρ.toFun h = ρ.toFun h * ρ.toFun g
    rw [← ρ.map_mul, ← ρ.map_mul, CommGroup.mul_comm]

/-- The line `K · v` spanned by a vector. -/
def line {K : Type w} [CommRing K] (v : Vec ι K) : Subspace ι K where
  carrier x := ∃ c : K, x = c • v
  zero_mem := ⟨0, (VectorSpace.zero_smul v).symm⟩
  add_mem := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, (VectorSpace.add_smul a b v).symm⟩
  smul_mem c := by
    rintro _ ⟨a, rfl⟩; exact ⟨c * a, (VectorSpace.mul_smul c a v).symm⟩

/-- **Irreducible representations of abelian groups are one-dimensional** (over `ℂ`). -/
theorem card_eq_one_of_irreducible {ρ : Rep G C ι} (hρ : Irreducible ρ) : card ι = 1 := by
  obtain ⟨i0⟩ := hρ.1
  have hsc : ∀ g, ∃ z : C, ρ g = z • (1 : Mat ι ι C) := fun g =>
    schur_complex hρ (isGMap_of_comm ρ g)
  have hinv : Invariant ρ (line (Vec.basisVec i0)) := by
    rintro g _ ⟨c, rfl⟩
    obtain ⟨z, hz⟩ := hsc g
    refine ⟨z * c, ?_⟩
    rw [hz, smul_mulVec, one_mulVec, VectorSpace.mul_smul]
  have hall : ∀ j : ι, j = i0 := by
    intro j
    rcases hρ.2 _ hinv with h0 | htop
    · exfalso
      have := congrFun (h0 _ ⟨1, (VectorSpace.one_smul _).symm⟩) i0
      exact C.isField.1 (by rw [← kd_self (K := C) i0]; exact this.symm)
    · apply Classical.byContradiction; intro hj
      obtain ⟨c, hc⟩ := htop (Vec.basisVec j)
      have := congrFun hc j
      change kd j j = c * kd j i0 at this
      rw [kd_self, kd_ne hj, Ring.mul_zero] at this
      exact C.isField.1 this.symm
  rw [← count_true, count_congr (Q := fun x => x = i0) (fun x => ⟨fun _ => hall x, fun _ => trivial⟩),
    count_eq_self]

/-- **The character of an irreducible representation of an abelian group is a homomorphism**
`G → ℂ` (an element of the dual group). -/
theorem isChar_of_irreducible {ρ : Rep G C ι} (hρ : Irreducible ρ) : IsChar (character ρ) := by
  have hsc : ∀ g, ∃ z : C, ρ g = z • (1 : Mat ι ι C) := fun g =>
    schur_complex hρ (isGMap_of_comm ρ g)
  let z : G → C := fun g => Classical.choose (hsc g)
  have hz : ∀ g, ρ g = z g • (1 : Mat ι ι C) := fun g => Classical.choose_spec (hsc g)
  have hcard := card_eq_one_of_irreducible hρ
  have hχ : ∀ g, character ρ g = z g := fun g => by
    show trace (ρ g) = z g
    rw [hz, trace_smul, trace_one, hcard]; exact Ring.mul_one _
  obtain ⟨i0⟩ := hρ.1
  refine ⟨?_, fun a b => ?_⟩
  · rw [character_one, hcard]; rfl
  · rw [hχ, hχ, hχ]
    have e : ρ (a * b) *ᵥ Vec.basisVec i0 = ρ a *ᵥ (ρ b *ᵥ Vec.basisVec i0) := ρ.act_mul a b _
    rw [hz, hz, hz] at e
    simp only [smul_mulVec, one_mulVec] at e
    have := congrFun e i0
    change z (a * b) * kd i0 i0 = z a * (z b * kd i0 i0) at this
    rw [kd_self, Ring.mul_one, Ring.mul_one] at this
    exact this

/-- **One-dimensional representations are irreducible** (over any field). -/
theorem irreducible_of_unit {K : Type w} [CommRing K] (hF : IsField K) (ρ : Rep G K Unit) :
    Irreducible ρ := by
  refine ⟨⟨()⟩, fun W _ => ?_⟩
  by_cases h : W.IsZero
  · exact Or.inl h
  · right; intro y
    have : ∃ x, x ∈ W ∧ x ≠ 0 :=
      Classical.byContradiction fun hno => h fun x hx =>
        Classical.byContradiction fun hx0 => hno ⟨x, hx, hx0⟩
    obtain ⟨x, hx, hx0⟩ := this
    have hx0' : x () ≠ 0 := fun e => hx0 (Vec.ext fun u => by cases u; exact e)
    obtain ⟨t, ht⟩ := hF.2 _ hx0'
    have := W.smul_mem (y () * t) hx
    have e : (y () * t) • x = y := Vec.ext fun u => by
      cases u; show y () * t * x () = y ()
      rw [Ring.mul_assoc, CommRing.mul_comm t, ht, Ring.mul_one]
    rwa [e] at this

/-- The character of the one-dimensional representation attached to a homomorphism `χ` is `χ`. -/
theorem character_ofHom {K : Type w} [CommRing K] (χ : G → K) (h1 : χ 1 = 1)
    (hmul : ∀ g h, χ (g * h) = χ g * χ h) : character (Rep.ofHom χ h1 hmul) = χ :=
  funext fun _ => Rep.isum_unit _

/-- **Bridge to the dual group.** For a finite abelian group `G`, a function `ψ : G → ℂ` is
the character of an irreducible complex representation if and only if it is a character
`IsChar ψ` in the sense of `NumberTheory/DualGroup`, i.e. an element of `Ĝ = Character G`. -/
theorem irreducible_character_iff_isChar (ψ : G → C) :
    (∃ (ι : Type) (_ : FiniteType ι) (ρ : Rep G C ι), Irreducible ρ ∧ character ρ = ψ) ↔
      IsChar ψ := by
  constructor
  · rintro ⟨ι, _, ρ, hρ, rfl⟩; exact isChar_of_irreducible hρ
  · intro hψ
    refine ⟨Unit, inferInstance, Rep.ofHom ψ hψ.map_one hψ.map_mul,
      irreducible_of_unit C.isField _, character_ofHom _ _ _⟩

/-- Every element of the dual group `Ĝ` is the character of an irreducible representation. -/
noncomputable def Character.toRep (χ : Character G) : Rep G C Unit :=
  Rep.ofHom χ.1 χ.2.map_one χ.2.map_mul

/-- The representation attached to `χ ∈ Ĝ` is irreducible with character `χ`. -/
theorem Character.toRep_spec (χ : Character G) :
    Irreducible (Character.toRep χ) ∧ character (Character.toRep χ) = χ.1 :=
  ⟨irreducible_of_unit C.isField _, character_ofHom _ _ _⟩

end Foundations.Langlands
