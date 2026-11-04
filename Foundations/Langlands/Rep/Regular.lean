import Foundations.Langlands.Rep.Decompose

/-!
# The irreducibility criterion and the regular representation

With complete reducibility in hand, characters control representations completely. Two
classical consequences, both due to Frobenius (1896–97), are proved here over `ℂ`.

* **The irreducibility criterion.** `ρ` is irreducible if and only if
  `Σ_g χ(g) χ(g⁻¹) = |G|`. One direction is orthogonality. Conversely, if `ρ` is reducible then
  `ρ ≅ σ₁ ⊕ σ₂` with both `σᵢ` sums of irreducibles, and expanding the pairing gives at least
  `2|G|`, because every pairing of sums of irreducibles is a non-negative multiple of `|G|`.
* **The regular representation**, `G` acting on `ℂ^G` by left translation, the permutation
  representation of `G` on itself. Its character is `|G|` at `1` and `0` elsewhere, so every
  irreducible `ρ` occurs in it with multiplicity `dim ρ`. Evaluating at `1` then gives
  **Burnside's formula** `Σᵢ (dim ρᵢ)² = |G|` over a complete list of pairwise non-isomorphic
  irreducibles.

The regular representation is, in Langlands' world, the space of functions on `G`. Its infinite
analogue, `L²(Γ\G)` for an arithmetic group `Γ`, is where automorphic representations live.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u

variable {G : Type u} [Group G] [FiniteType G]

/-! ## Natural numbers in `ℂ` -/

/-- `ncast` is additive. -/
theorem ncast_add_C (a b : Nat) : (ncast (a + b) : C) = ncast a + ncast b := by
  induction b with
  | zero => exact (Ring.add_zero _).symm
  | succ b ih => rw [← Nat.add_assoc, ncast_succ, ncast_succ, ih, Ring.add_assoc]

/-- `ncast` is multiplicative. -/
theorem ncast_mul_C (a b : Nat) : (ncast (a * b) : C) = ncast a * ncast b := by
  induction b with
  | zero => exact (Ring.mul_zero _).symm
  | succ b ih => rw [Nat.mul_succ, ncast_add_C, ih, ncast_succ, Ring.left_distrib, Ring.mul_one]

/-- **`ℕ → ℂ` is injective.** -/
theorem ncast_inj_C {a b : Nat} (h : (ncast a : C) = ncast b) : a = b := by
  have key : ∀ a k : Nat, (ncast a : C) ≠ ncast (a + (k + 1)) := fun a k e => by
    rw [ncast_add_C] at e
    have : (ncast (k + 1) : C) = 0 :=
      (Ring.add_left_cancel (e.symm.trans (Ring.add_zero _).symm))
    exact C.ncast_succ_ne_zero k this
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
    exact absurd h (key a k)
  · exact hab
  · obtain ⟨k, rfl⟩ : ∃ k, a = b + (k + 1) := ⟨a - b - 1, by omega⟩
    exact absurd h.symm (key b k)

/-- Cancelling `|G|` in `ℂ`. -/
theorem cancel_card {x y : C} (h : x * ncast (card G) = y * ncast (card G)) : x = y := by
  obtain ⟨t, ht⟩ := C.isField.2 _ (ncast_ne_zero_complex (card_group_pos (G := G)))
  have := congrArg (· * t) h
  simp only [Ring.mul_assoc, ht, Ring.mul_one] at this
  exact this

/-! ## Pairings of sums of irreducibles -/

/-- The pairing is additive in the first argument. -/
theorem pairing_add_left (χ₁ χ₂ ψ : G → C) :
    pairing (fun g => χ₁ g + χ₂ g) ψ = pairing χ₁ ψ + pairing χ₂ ψ := by
  unfold pairing; rw [← isum_add]; exact isum_congr fun _ => Ring.right_distrib _ _ _

/-- The pairing is additive in the second argument. -/
theorem pairing_add_right (χ ψ₁ ψ₂ : G → C) :
    pairing χ (fun g => ψ₁ g + ψ₂ g) = pairing χ ψ₁ + pairing χ ψ₂ := by
  unfold pairing; rw [← isum_add]; exact isum_congr fun _ => Ring.left_distrib _ _ _

/-- The character of a direct sum, as a function. -/
theorem character_dsum' {ι κ : Type} [FiniteType ι] [FiniteType κ] (ρ : Rep G C ι)
    (σ : Rep G C κ) : character (ρ.dsum σ) = fun g => character ρ g + character σ g :=
  funext (character_dsum ρ σ)

/-- **Pairings of sums of irreducibles are natural multiples of `|G|`.** -/
theorem sumIrr_pairing {κ : Type} [FiniteType κ] {σ : Rep G C κ} (hs : SumIrr κ σ) :
    ∀ {κ' : Type} [FiniteType κ'] {σ' : Rep G C κ'}, SumIrr κ' σ' →
      ∃ N : Nat, pairing (character σ) (character σ') = ncast N * ncast (card G) := by
  induction hs with
  | irr σ hσ =>
    intro κ' _ σ' hs'
    induction hs' with
    | irr τ hτ =>
      classical
      rw [orthogonality_complex hτ hσ]
      by_cases h : Iso τ σ
      · exact ⟨1, by simp only [h, ↓reduceIte]; exact (Ring.one_mul _).symm⟩
      · exact ⟨0, by simp only [h, ↓reduceIte]; exact (Ring.zero_mul _).symm⟩
    | sum τ₁ τ₂ _ _ ih₁ ih₂ =>
      obtain ⟨N₁, h₁⟩ := ih₁
      obtain ⟨N₂, h₂⟩ := ih₂
      refine ⟨N₁ + N₂, ?_⟩
      rw [character_dsum', pairing_add_right, h₁, h₂, ncast_add_C, Ring.right_distrib]
  | sum σ₁ σ₂ _ _ ih₁ ih₂ =>
    intro κ' _ σ' hs'
    obtain ⟨N₁, h₁⟩ := ih₁ hs'
    obtain ⟨N₂, h₂⟩ := ih₂ hs'
    refine ⟨N₁ + N₂, ?_⟩
    rw [character_dsum', pairing_add_left, h₁, h₂, ncast_add_C, Ring.right_distrib]

/-- A sum of irreducibles pairs with itself to a positive multiple of `|G|`. -/
theorem sumIrr_pairing_self {κ : Type} [FiniteType κ] {σ : Rep G C κ} (hs : SumIrr κ σ) :
    ∃ N : Nat, 1 ≤ N ∧ pairing (character σ) (character σ) = ncast N * ncast (card G) := by
  induction hs with
  | irr σ hσ =>
    refine ⟨1, Nat.le_refl 1, ?_⟩
    rw [orthogonality_complex hσ hσ]
    simp only [Iso.refl, ↓reduceIte]; exact (Ring.one_mul _).symm
  | sum σ₁ σ₂ hs₁ hs₂ ih₁ ih₂ =>
    obtain ⟨N₁, hN₁, h₁⟩ := ih₁
    obtain ⟨N₂, hN₂, h₂⟩ := ih₂
    obtain ⟨M₁, k₁⟩ := sumIrr_pairing hs₁ hs₂
    obtain ⟨M₂, k₂⟩ := sumIrr_pairing hs₂ hs₁
    refine ⟨N₁ + M₁ + (M₂ + N₂), by omega, ?_⟩
    rw [character_dsum', pairing_add_left, pairing_add_right, pairing_add_right, h₁, h₂, k₁, k₂,
      ncast_add_C, ncast_add_C, ncast_add_C, Ring.right_distrib, Ring.right_distrib,
      Ring.right_distrib]

/-! ## The irreducibility criterion -/

/-- **Irreducibility criterion** (Frobenius). A complex representation `ρ` of a finite group is
irreducible if and only if `Σ_g χ_ρ(g) χ_ρ(g⁻¹) = |G|`. -/
theorem irreducible_iff_pairing {ι : Type} [FiniteType ι] (ρ : Rep G C ι) :
    Irreducible ρ ↔ pairing (character ρ) (character ρ) = ncast (card G) := by
  constructor
  · intro h
    rw [orthogonality_complex h h]; simp only [Iso.refl, ↓reduceIte]
  · intro h
    apply Classical.byContradiction; intro hirr
    have hG := ncast_ne_zero_complex (card_group_pos (G := G))
    by_cases hne : Nonempty ι
    · obtain ⟨W, W', hW, hW', hc, h0, h0'⟩ :=
        split_of_not_irreducible C.isField hG ρ hne hirr
      obtain ⟨d, e, hd, he, _, ρ₁, ρ₂, hiso⟩ := iso_dsum_of_compl C.isField ρ hW hW' hc h0 h0'
      obtain ⟨κ₁, _, σ₁, hs₁, hi₁⟩ := complete_reducibility C.isField hG ρ₁ ⟨⟨0, hd⟩⟩
      obtain ⟨κ₂, _, σ₂, hs₂, hi₂⟩ := complete_reducibility C.isField hG ρ₂ ⟨⟨0, he⟩⟩
      have hs := SumIrr.sum σ₁ σ₂ hs₁ hs₂
      obtain ⟨N, hN, hp⟩ := sumIrr_pairing_self hs
      obtain ⟨N₁, hN₁, h₁⟩ := sumIrr_pairing_self hs₁
      obtain ⟨N₂, hN₂, h₂⟩ := sumIrr_pairing_self hs₂
      obtain ⟨M₁, k₁⟩ := sumIrr_pairing hs₁ hs₂
      obtain ⟨M₂, k₂⟩ := sumIrr_pairing hs₂ hs₁
      have hχ : character ρ = character (σ₁.dsum σ₂) :=
        character_eq_of_iso (hiso.trans (hi₁.dsum hi₂))
      rw [hχ, character_dsum', pairing_add_left, pairing_add_right, pairing_add_right, h₁, h₂,
        k₁, k₂, ← Ring.right_distrib, ← Ring.right_distrib, ← Ring.right_distrib,
        ← ncast_add_C, ← ncast_add_C, ← ncast_add_C] at h
      have h' : _ = (ncast 1 : C) * ncast (card G) := h.trans (Ring.one_mul _).symm
      have := ncast_inj_C (cancel_card h')
      omega
    · have hz : character ρ = fun _ => 0 := funext fun g => by
        show isum (fun i => ρ g i i) = 0
        exact isum_eq_zero fun i => absurd ⟨i⟩ hne
      rw [hz] at h
      exact hG (h.symm.trans (isum_eq_zero fun _ => Ring.zero_mul _))

/-! ## The regular representation -/

/-- A group acts on itself by left multiplication. -/
@[instance_reducible] def selfAction (G : Type u) [Group G] : MulAction G G where
  smul g x := g * x
  one_smul := Group.one_mul
  mul_smul := Group.mul_assoc

/-- The **regular representation** of `G` over `K`: the permutation representation of `G` on
itself by left multiplication, on the space `K^G` of functions on `G`. -/
noncomputable def regularRep (G : Type u) [Group G] [FiniteType G] (K : Type) [CommRing K] :
    Rep G K G :=
  @permRep G _ K _ G _ (selfAction G)

open Classical in
/-- **The regular character**: `χ_reg(g) = |G|` if `g = 1`, and `0` otherwise. -/
theorem character_regularRep (g : G) :
    character (regularRep G C) g = if g = 1 then (ncast (card G) : C) else 0 := by
  rw [regularRep, @character_permRep G _ G _ (selfAction G)]
  by_cases h : g = 1
  · subst h; rw [if_pos rfl]
    congr 1; rw [← count_true]
    exact count_congr fun x => ⟨fun _ => trivial, fun _ => Group.one_mul x⟩
  · simp only [h, ↓reduceIte]
    have h0 : count (fun x : G => @HSMul.hSMul G G G (@instHSMul G G (selfAction G).toSMul) g x = x)
        = 0 := count_eq_zero.2 fun x hx => h (Group.eq_one_of_mul_left hx)
    rw [h0]; rfl

/-- **Every irreducible occurs in the regular representation `dim ρ` times**, in the form
`Σ_g χ_reg(g) χ_ρ(g⁻¹) = dim ρ · |G|`. -/
theorem pairing_regular {ι : Type} [FiniteType ι] (ρ : Rep G C ι) :
    pairing (character (regularRep G C)) (character ρ) = ncast (card ι) * ncast (card G) := by
  unfold pairing
  have hz : ∀ g, g ≠ 1 → character (regularRep G C) g * character ρ g⁻¹ = 0 := fun g hg => by
    rw [character_regularRep, if_neg hg]; exact Ring.zero_mul _
  rw [isum_single' _ 1 hz, character_regularRep, if_pos rfl, Group.inv_one, character_one, CommRing.mul_comm]

variable {r : Nat} {ιs : Fin r → Type} [∀ k, FiniteType (ιs k)]

/-- **Multiplicity of an irreducible in the regular representation.** If the regular character
is `Σ_k m_k χ_k` for pairwise non-isomorphic irreducibles `ρ_k`, then `m_k = dim ρ_k`. -/
theorem regular_multiplicity (ρs : ∀ k, Rep G C (ιs k)) (hirr : ∀ k, Irreducible (ρs k))
    (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k')) (m : Fin r → Nat)
    (hχ : ∀ g, character (regularRep G C) g = isum (fun k => ncast (m k) * character (ρs k) g))
    (j : Fin r) : m j = card (ιs j) := by
  have := multiplicity_eq_complex ρs hirr hdist m _ hχ j
  rw [pairing_regular] at this
  exact ncast_inj_C (cancel_card this.symm)

/-- A sum of natural numbers indexed by `Fin r`. -/
def natSum : {r : Nat} → (Fin r → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => f 0 + natSum (fun i => f i.succ)

/-- `ncast` turns `natSum` into a sum in `ℂ`. -/
theorem ncast_natSum : ∀ {r : Nat} (f : Fin r → Nat),
    (ncast (natSum f) : C) = isum (fun k => (ncast (f k) : C))
  | 0, _ => rfl
  | _ + 1, f => by rw [isum_fin_succ, natSum, ncast_add_C, ncast_natSum]

/-- The character of a sum of irreducibles is a natural combination of the characters in a
complete list of irreducibles. -/
theorem sumIrr_character_expansion (ρs : ∀ k, Rep G C (ιs k))
    (hcomplete : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k))
    {κ : Type} [FiniteType κ] {σ : Rep G C κ} (hs : SumIrr κ σ) :
    ∃ m : Fin r → Nat, ∀ g, character σ g = isum (fun k => ncast (m k) * character (ρs k) g) := by
  classical
  induction hs with
  | irr σ hσ =>
    obtain ⟨k, hk⟩ := hcomplete σ hσ
    refine ⟨fun k' => if k' = k then 1 else 0, fun g => ?_⟩
    rw [isum_single' _ k (fun k' hk' => by simp only [hk', ↓reduceIte]; exact Ring.zero_mul _)]
    simp only [↓reduceIte]
    rw [character_eq_of_iso hk]; exact (Ring.one_mul _).symm
  | sum σ₁ σ₂ _ _ ih₁ ih₂ =>
    obtain ⟨m₁, h₁⟩ := ih₁
    obtain ⟨m₂, h₂⟩ := ih₂
    refine ⟨fun k => m₁ k + m₂ k, fun g => ?_⟩
    rw [character_dsum, h₁, h₂, ← isum_add]
    exact isum_congr fun k => by rw [ncast_add_C, Ring.right_distrib]

/-- **Burnside's formula** `Σᵢ (dim ρᵢ)² = |G|`. If `ρ₀, …, ρ_{r−1}` are pairwise
non-isomorphic irreducible complex representations of a finite group `G`, and every irreducible
representation is isomorphic to one of them, then the squares of their degrees add up to `|G|`. -/
theorem sum_sq_degrees {G : Type} [Group G] [FiniteType G] {r : Nat} {ιs : Fin r → Type}
    [∀ k, FiniteType (ιs k)] (ρs : ∀ k, Rep G C (ιs k)) (hirr : ∀ k, Irreducible (ρs k))
    (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k'))
    (hcomplete : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k)) :
    natSum (fun k => card (ιs k) * card (ιs k)) = card G := by
  have hG := ncast_ne_zero_complex (card_group_pos (G := G))
  obtain ⟨κ, _, σ, hs, hiso⟩ :=
    complete_reducibility C.isField hG (regularRep G C) ⟨1⟩
  obtain ⟨m, hm⟩ := sumIrr_character_expansion ρs hcomplete hs
  have hχ : ∀ g, character (regularRep G C) g =
      isum (fun k => ncast (m k) * character (ρs k) g) := fun g => by
    rw [character_eq_of_iso hiso]; exact hm g
  have hmk := regular_multiplicity ρs hirr hdist m hχ
  have h1 := hχ 1
  rw [character_regularRep, if_pos rfl] at h1
  apply ncast_inj_C
  rw [ncast_natSum, h1]
  exact isum_congr fun k => by rw [hmk k, character_one, ncast_mul_C]

end Foundations.Langlands
