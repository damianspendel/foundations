import Foundations.Langlands.Rep.CharacterIso
import Foundations.Langlands.Rep.ClassFunctions
import Foundations.Algebra.Lagrange

/-!
# Restriction, induction of class functions, and Frobenius reciprocity

A representation of a group `G` restricts to every subgroup `H`; this is trivial. Going the
other way, from `H` up to `G`, is the operation of **induction**, introduced by Frobenius in
1898 (*Über Relationen zwischen den Charakteren einer Gruppe und denen ihrer Untergruppen*).
Frobenius discovered that the two operations are adjoint: the multiplicity of `ψ` in an induced
character equals the multiplicity of the induced-from character in the restriction of `ψ`. This
is **Frobenius reciprocity**, and it is a main computational tool of character theory:
irreducible characters are routinely found by decomposing induced characters.

Induction is also the prototype of **Langlands functoriality**. Functoriality predicts that a
homomorphism of `L`-groups `ᴸH → ᴸG` transfers automorphic representations of `H` to
automorphic representations of `G`. For a finite extension `E/F`, *automorphic induction*
from `GL_n` over `E` to `GL_{n[E:F]}` over `F` is the case corresponding, on the Galois side,
to inducing representations from the subgroup `Gal(F̄/E)` to `Gal(F̄/F)`.

This file works at the level of class functions over `ℂ`:

* subgroups are those of `Algebra/Group` (`Subgroup G`, used as the type `{x // x ∈ H}` with
  the inherited group structure, as in Lagrange's and Sylow's theorems);
* the **restriction** `Res^G_H ρ` of a representation (`Rep.res`), whose character is the
  restriction of the character (`character_res`);
* `natInv n`, the inverse of `n ≠ 0` in `ℂ`;
* the **induced class function** `Ind f(g) = (1/|H|) Σ_{x ∈ G, x g x⁻¹ ∈ H} f(x g x⁻¹)`
  (`indFun`), with `f` extended by zero off `H` (`ext0`); it is a class function
  (`indFun_isClassFunction`);
* **Frobenius reciprocity** (`frobenius_reciprocity`): for every `f : H → ℂ` and every class
  function `ψ` on `G`, `⟨Ind f, ψ⟩_G = ⟨f, Res ψ⟩_H`, where `⟨χ, ψ⟩_G = (1/|G|) Σ_g χ(g) ψ(g⁻¹)`
  is the library's pairing `pairing` divided by the order of the group.

The induced *representation*, whose character is `Ind χ_σ`, is constructed in `Induced`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u v w

/-! ## Restriction -/

namespace Rep

variable {G : Type u} [Group G] {K : Type w} [CommRing K] {ι : Type v} [FiniteType ι]

/-- **Restriction** `Res^G_H ρ`: a representation of `G` restricted to a subgroup `H`, acting on
the same space, `h ↦ ρ(h)`. -/
def res (H : Subgroup G) (ρ : Rep G K ι) : Rep H K ι where
  toFun h := ρ h.1
  map_one := ρ.map_one
  map_mul a b := ρ.map_mul a.1 b.1

end Rep

variable {G : Type u} [Group G]

/-- The restriction `f|_H` of a function on `G` to a subgroup `H`. -/
def resFun {α : Type w} (H : Subgroup G) (f : G → α) : H → α := fun h => f h.1

/-- **Character of a restriction.** `χ_{Res ρ} = (χ_ρ)|_H`. -/
theorem character_res {K : Type w} [CommRing K] {ι : Type v} [FiniteType ι] (H : Subgroup G)
    (ρ : Rep G K ι) : character (ρ.res H) = resFun H (character ρ) := rfl

/-- The restriction of a class function is a class function. -/
theorem resFun_isClassFunction {α : Type w} (H : Subgroup G) {f : G → α}
    (hf : IsClassFunction f) : IsClassFunction (resFun H f) := fun g h => hf g.1 h.1

/-! ## Inverses of natural numbers in `ℂ` -/

/-- The inverse `1/n` in `ℂ` (and `0` for `n = 0`). -/
noncomputable def natInv (n : Nat) : C := by
  classical exact if h : (ncast n : C) = 0 then 0 else Classical.choose (C.isField.2 _ h)

/-- `n · (1/n) = 1` for `n > 0`. -/
theorem ncast_mul_natInv {n : Nat} (hn : 0 < n) : (ncast n : C) * natInv n = 1 := by
  have h := ncast_ne_zero_complex hn
  unfold natInv
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec (C.isField.2 _ h)

/-! ## Sums over a subgroup -/

/-- A sum over `G` of a function vanishing off `H` is the sum over `H`. -/
theorem isum_subgroup [FiniteType G] (H : Subgroup G) (F : G → C)
    (hF : ∀ g, g ∉ H → F g = 0) : isum F = isum (fun h : H => F h.1) := by
  let e : H ⊕ {x : G // x ∉ H} → G := Sum.elim Subtype.val Subtype.val
  have einj : ∀ a b, e a = e b → a = b := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (Subtype.ext hab)
    · have e' : a.1 = b.1 := hab
      exact absurd (e' ▸ a.2) b.2
    · have e' : a.1 = b.1 := hab
      exact absurd (e' ▸ b.2) a.2
    · exact congrArg Sum.inr (Subtype.ext hab)
  have esurj : ∀ y, ∃ x, e x = y := fun y => by
    by_cases hy : y ∈ H
    · exact ⟨.inl ⟨y, hy⟩, rfl⟩
    · exact ⟨.inr ⟨y, hy⟩, rfl⟩
  rw [← isum_comp_bij e einj esurj F, isum_sum]
  show isum (fun i : H => F i.1) + isum (fun k : {x : G // x ∉ H} => F k.1) = _
  rw [isum_eq_zero (fun x : {x : G // x ∉ H} => hF x.1 x.2), AddAbGroup.add_zero]

/-! ## Induced class functions -/

/-- The extension `f°` of a function `f : H → ℂ` by zero: `f°(g) = f(g)` for `g ∈ H` and `0`
otherwise. -/
noncomputable def ext0 (H : Subgroup G) (f : H → C) (g : G) : C := by
  classical exact if h : g ∈ H then f ⟨g, h⟩ else 0

/-- `f°(h) = f(h)` on `H`. -/
theorem ext0_mem (H : Subgroup G) (f : H → C) {g : G} (hg : g ∈ H) : ext0 H f g = f ⟨g, hg⟩ := by
  unfold ext0; simp only [hg, ↓reduceDIte]

/-- `f°(g) = 0` off `H`. -/
theorem ext0_not_mem (H : Subgroup G) (f : H → C) {g : G} (hg : g ∉ H) : ext0 H f g = 0 := by
  unfold ext0; simp only [hg, ↓reduceDIte]

variable [FiniteType G]

/-- **Induced class function** (Frobenius 1898). For `f : H → ℂ`,
`Ind f(g) = (1/|H|) Σ_{x ∈ G} f°(x g x⁻¹)`, where `f°` is `f` extended by zero: the sum runs over
those `x` with `x g x⁻¹ ∈ H`. -/
noncomputable def indFun (H : Subgroup G) (f : H → C) (g : G) : C :=
  natInv (card H) * isum (fun x : G => ext0 H f (x * g * x⁻¹))

/-- Reindexing a sum over `G` by right multiplication `x ↦ x y`. -/
theorem isum_mul_right_reindex {A : Type} [AddAbGroup A] (y : G) (F : G → A) :
    isum (fun x => F (x * y)) = isum F :=
  isum_comp_bij (fun x => x * y) (fun _ _ e => Group.mul_right_cancel e)
    (fun z => ⟨z * y⁻¹, Group.inv_mul_cancel_right z y⟩) F

/-- **Induced class functions are class functions.** -/
theorem indFun_isClassFunction (H : Subgroup G) (f : H → C) :
    IsClassFunction (indFun H f) := by
  intro g y
  unfold indFun
  congr 1
  rw [← isum_mul_right_reindex y (fun x => ext0 H f (x * g * x⁻¹))]
  apply isum_congr; intro x
  congr 1
  rw [Group.mul_inv_rev]
  simp only [Group.mul_assoc]

/-- The pairing is invariant under conjugating the first argument, for a class function `ψ`:
`Σ_g F(x g x⁻¹) ψ(g⁻¹) = Σ_g F(g) ψ(g⁻¹)`. -/
theorem isum_conj_pairing (F ψ : G → C) (hψ : IsClassFunction ψ) (x : G) :
    isum (fun g => F (x * g * x⁻¹) * ψ g⁻¹) = isum (fun g => F g * ψ g⁻¹) := by
  rw [← isum_conj_reindex x (fun g => F g * ψ g⁻¹)]
  apply isum_congr; intro g
  congr 1
  rw [← hψ g⁻¹ x, Group.mul_inv_rev, Group.mul_inv_rev, Group.inv_inv, Group.mul_assoc]

/-- Frobenius reciprocity, unnormalised: `Σ_g Ind f(g) ψ(g⁻¹) = (|G|/|H|) Σ_h f(h) ψ(h⁻¹)`. -/
theorem pairing_indFun (H : Subgroup G) (f : H → C) (ψ : G → C) (hψ : IsClassFunction ψ) :
    pairing (indFun H f) ψ = ncast (card G) * natInv (card H) * pairing f (resFun H ψ) := by
  unfold pairing indFun
  have step1 : isum (fun g => natInv (card H) * isum (fun x : G => ext0 H f (x * g * x⁻¹)) *
      ψ g⁻¹) = natInv (card H) *
        isum (fun x : G => isum (fun g => ext0 H f (x * g * x⁻¹) * ψ g⁻¹)) := by
    rw [isum_congr (fun g => by rw [Ring.mul_assoc, isum_mul_right]), ← isum_mul_left,
      isum_comm]
  rw [step1]
  rw [isum_congr (fun x => isum_conj_pairing (ext0 H f) ψ hψ x), isum_const]
  have step2 : isum (fun g => ext0 H f g * ψ g⁻¹) = isum (fun h : H => f h * resFun H ψ h⁻¹) := by
    rw [isum_subgroup H _ (fun g hg => by rw [ext0_not_mem H f hg, Ring.zero_mul])]
    apply isum_congr; intro h
    rw [ext0_mem H f h.2]
    rfl
  rw [step2]
  grind

/-- **Frobenius reciprocity** (Frobenius 1898). For a subgroup `H` of a finite group `G`, a
function `f : H → ℂ` and a class function `ψ` on `G`,
`⟨Ind f, ψ⟩_G = ⟨f, Res ψ⟩_H`, where `⟨χ, ψ⟩_G = (1/|G|) Σ_{g ∈ G} χ(g) ψ(g⁻¹)`. -/
theorem frobenius_reciprocity (H : Subgroup G) (f : H → C) (ψ : G → C)
    (hψ : IsClassFunction ψ) :
    natInv (card G) * pairing (indFun H f) ψ = natInv (card H) * pairing f (resFun H ψ) := by
  rw [pairing_indFun H f ψ hψ]
  have h := ncast_mul_natInv (card_group_pos (G := G))
  grind

/-- **Frobenius reciprocity for characters.** For a representation `σ` of `H` and a
representation `ρ` of `G`, `⟨Ind χ_σ, χ_ρ⟩_G = ⟨χ_σ, χ_{Res ρ}⟩_H`. -/
theorem frobenius_reciprocity_character {ι κ : Type} [FiniteType ι] [FiniteType κ]
    (H : Subgroup G) (σ : Rep H C ι) (ρ : Rep G C κ) :
    natInv (card G) * pairing (indFun H (character σ)) (character ρ) =
      natInv (card H) * pairing (character σ) (character (ρ.res H)) :=
  frobenius_reciprocity H _ _ (character_isClassFunction ρ)

end Foundations.Langlands
