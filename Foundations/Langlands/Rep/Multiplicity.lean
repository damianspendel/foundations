import Foundations.Langlands.Rep.Orthogonality

/-!
# Multiplicities are read off from characters

By Maschke's theorem a representation of a finite group over `ℂ` breaks into irreducible
pieces, and its character is then the sum of their characters, each counted with its
multiplicity (`character_dsum`). Frobenius' orthogonality relations turn this around: the
multiplicity of an irreducible `ρⱼ` in a character `χ = Σ_k m_k χ_k` is the inner product

  `m_j = ⟨χ, χ_j⟩ = |G|⁻¹ Σ_g χ(g) χ_j(g⁻¹)`.

In particular the multiplicities are **uniquely determined** by the character: two
decompositions of the same character into pairwise non-isomorphic irreducibles have the same
multiplicities (as elements of the field). This is the precise sense in which "the character
determines the representation", and it is the finite model of a principle that runs through
the Langlands programme, where representations are identified through their traces (Frobenius
traces on the Galois side, the trace formula on the automorphic side).

What is proved here is stated for characters: we assume `χ = Σ_k m_k χ_k` as functions on `G`.
That every representation is isomorphic to a direct sum of irreducibles (iterating
`split_of_not_irreducible` with a change of basis) is not formalised in this chapter.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u v w

variable {G : Type u} [Group G] [FiniteType G] {K : Type w} [CommRing K]

/-- The pairing is additive in its first argument, over finite sums. -/
theorem pairing_isum_left {α : Type v} [FiniteType α] (f : α → G → K) (ψ : G → K) :
    pairing (fun g => isum (fun a => f a g)) ψ = isum (fun a => pairing (f a) ψ) := by
  unfold pairing
  simp only [isum_mul_right]
  exact isum_comm _

/-- The pairing is homogeneous in its first argument. -/
theorem pairing_smul_left (c : K) (χ ψ : G → K) :
    pairing (fun g => c * χ g) ψ = c * pairing χ ψ := by
  unfold pairing
  rw [isum_mul_left]
  exact isum_congr fun g => Ring.mul_assoc _ _ _

variable {r : Nat} {ιs : Fin r → Type v} [∀ k, FiniteType (ιs k)]

/-- **Multiplicities from characters.** Let `ρ₀, …, ρ_{r−1}` be pairwise non-isomorphic
irreducible representations over an algebraically closed field in which their degrees are
non-zero. If `χ = Σ_k m_k χ_{ρ_k}` then `Σ_g χ(g) χ_{ρⱼ}(g⁻¹) = m_j |G|`. -/
theorem multiplicity_eq (hF : IsField K) (hK : AlgClosed K) (ρs : ∀ k, Rep G K (ιs k))
    (hirr : ∀ k, Irreducible (ρs k)) (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k'))
    (hdeg : ∀ k, (ncast (card (ιs k)) : K) ≠ 0) (m : Fin r → Nat) (χ : G → K)
    (hχ : ∀ g, χ g = isum (fun k => ncast (m k) * character (ρs k) g)) (j : Fin r) :
    pairing χ (character (ρs j)) = ncast (m j) * ncast (card G) := by
  rw [show χ = fun g => isum (fun k => ncast (m k) * character (ρs k) g) from funext hχ,
    pairing_isum_left]
  simp only [pairing_smul_left]
  rw [isum_single' _ j]
  · rw [orthogonality hF hK (hirr j) (hirr j) (hdeg j)]
    simp only [Iso.refl, ↓reduceIte]
  · intro k hk
    rw [orthogonality hF hK (hirr j) (hirr k) (hdeg j)]
    simp only [hdist j k (Ne.symm hk), ↓reduceIte, Ring.mul_zero]

/-- **Multiplicity as an inner product.** Under the hypotheses of `multiplicity_eq`, with
`t = |G|⁻¹`: `m_j = ⟨χ, χ_j⟩ = t · Σ_g χ(g) χ_j(g⁻¹)`. -/
theorem multiplicity_eq_inner (hF : IsField K) (hK : AlgClosed K) (ρs : ∀ k, Rep G K (ιs k))
    (hirr : ∀ k, Irreducible (ρs k)) (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k'))
    (hdeg : ∀ k, (ncast (card (ιs k)) : K) ≠ 0) (m : Fin r → Nat) (χ : G → K)
    (hχ : ∀ g, χ g = isum (fun k => ncast (m k) * character (ρs k) g)) (j : Fin r)
    {t : K} (ht : ncast (card G) * t = 1) :
    t * pairing χ (character (ρs j)) = ncast (m j) := by
  rw [multiplicity_eq hF hK ρs hirr hdist hdeg m χ hχ j, CommRing.mul_comm, Ring.mul_assoc, ht,
    Ring.mul_one]

/-- **Uniqueness of multiplicities.** Two decompositions `Σ_k m_k χ_k = Σ_k m'_k χ_k` of the
same function into pairwise non-isomorphic irreducible characters have the same multiplicities
(in `K`), provided `|G| ≠ 0` in `K`. -/
theorem multiplicity_unique (hF : IsField K) (hK : AlgClosed K) (ρs : ∀ k, Rep G K (ιs k))
    (hirr : ∀ k, Irreducible (ρs k)) (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k'))
    (hdeg : ∀ k, (ncast (card (ιs k)) : K) ≠ 0) (hG : (ncast (card G) : K) ≠ 0)
    (m m' : Fin r → Nat)
    (h : ∀ g, isum (fun k => ncast (m k) * character (ρs k) g) =
      isum (fun k => ncast (m' k) * character (ρs k) g)) (j : Fin r) :
    (ncast (m j) : K) = ncast (m' j) := by
  obtain ⟨t, ht⟩ := hF.2 _ hG
  rw [← multiplicity_eq_inner hF hK ρs hirr hdist hdeg m _ (fun _ => rfl) j ht,
    ← multiplicity_eq_inner hF hK ρs hirr hdist hdeg m' _ (fun _ => rfl) j ht]
  congr 2; exact funext h

/-- **Multiplicities over `ℂ`.** For pairwise non-isomorphic irreducible complex
representations `ρ_k` of a finite group and `χ = Σ_k m_k χ_{ρ_k}`:
`Σ_g χ(g) χ_{ρⱼ}(g⁻¹) = m_j |G|`. -/
theorem multiplicity_eq_complex (ρs : ∀ k, Rep G C (ιs k)) (hirr : ∀ k, Irreducible (ρs k))
    (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k')) (m : Fin r → Nat) (χ : G → C)
    (hχ : ∀ g, χ g = isum (fun k => ncast (m k) * character (ρs k) g)) (j : Fin r) :
    pairing χ (character (ρs j)) = ncast (m j) * ncast (card G) :=
  multiplicity_eq C.isField algClosed_complex ρs hirr hdist
    (fun k => ncast_ne_zero_complex (card_pos_of_irreducible (hirr k))) m χ hχ j

end Foundations.Langlands
