import Foundations.Langlands.Rep.Completeness

/-!
# Characters determine representations

Frobenius' character was designed to forget almost everything about a representation; the
fundamental fact that makes it useful is that, over `ℂ`, it forgets nothing up to
isomorphism. This file proves it: **two complex representations of a finite group with the same
character are isomorphic** (`iso_of_character_eq`, and `iso_iff_character_eq` with the easy
converse `character_eq_of_iso` from `Basic`).

The proof combines complete reducibility with the multiplicity count of first orthogonality:

* reindexing a representation along a bijection of its index type gives an isomorphic
  representation (`iso_of_reindex`); hence direct sums are associative and commutative up to
  isomorphism (`Iso.dsum_assoc`, `Iso.dsum_comm`), adding the zero representation changes
  nothing (`iso_dsum_empty`), and any two representations of degree `0` are isomorphic
  (`iso_of_card_zero`);
* a sum of irreducibles `S` contains some irreducible `τ` with `⟨χ_S, χ_τ⟩ ≠ 0`
  (`sumIrr_exists_irr`), and whenever `⟨χ_S, χ_τ⟩ ≠ 0` the irreducible `τ` splits off:
  `S ≅ τ ⊕ S'` (`sumIrr_split`);
* if `χ_ρ = χ_σ`, decompose both, split off a common irreducible `τ`, cancel `χ_τ` from both
  characters, and induct on the degree.

This is the tool with which the next files identify induced representations: to show
`Ind^G_H σ ≅ ρ` it suffices to compare characters.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u

/-! ## Reindexing -/

section Reindex

variable {G : Type u} [Group G] {K : Type} [CommRing K]

/-- **Reindexing gives an isomorphic representation.** If `f : κ → ι` is a bijection (with
inverse `f'`) and `σ(g)_{ab} = ρ(g)_{f a, f b}` for all `g`, then `ρ ≅ σ`. -/
theorem iso_of_reindex {ι κ : Type} [FiniteType ι] [FiniteType κ] (ρ : Rep G K ι)
    (σ : Rep G K κ) (f : κ → ι) (f' : ι → κ) (h1 : ∀ a, f' (f a) = a) (h2 : ∀ i, f (f' i) = i)
    (h : ∀ g a b, σ g a b = ρ g (f a) (f b)) : Iso ρ σ := by
  have finj : ∀ a b, f a = f b → a = b := fun a b e => by rw [← h1 a, e, h1]
  have fsurj : ∀ i, ∃ a, f a = i := fun i => ⟨f' i, h2 i⟩
  refine ⟨fun a i => kd (f a) i, fun i a => kd i (f a), fun g => ?_, ?_, ?_⟩
  · apply ext; intro a j
    show isum (fun i => kd (f a) i * ρ g i j) = isum (fun b => σ g a b * kd (f b) j)
    rw [isum_kd_mul' (f a) (fun i => ρ g i j)]
    rw [isum_congr (fun b => by rw [h g a b]),
      isum_comp_bij f finj fsurj (fun i => ρ g (f a) i * kd i j), isum_mul_kd]
  · apply ext; intro i j
    show isum (fun a => kd i (f a) * kd (f a) j) = kd i j
    rw [isum_comp_bij f finj fsurj (fun i' => kd i i' * kd i' j), isum_kd_mul' i (fun a => kd a j)]
  · apply ext; intro a b
    show isum (fun i => kd (f a) i * kd i (f b)) = kd a b
    rw [isum_kd_mul' (f a) (fun i => kd i (f b)), kd_map f finj]

variable {ι κ μ : Type} [FiniteType ι] [FiniteType κ] [FiniteType μ]

/-- **Direct sums are associative** up to isomorphism: `(ρ ⊕ σ) ⊕ τ ≅ ρ ⊕ (σ ⊕ τ)`. -/
theorem Iso.dsum_assoc (ρ : Rep G K ι) (σ : Rep G K κ) (τ : Rep G K μ) :
    Iso ((ρ.dsum σ).dsum τ) (ρ.dsum (σ.dsum τ)) :=
  iso_of_reindex _ _ (Sum.elim (fun i => .inl (.inl i)) (Sum.elim (fun k => .inl (.inr k)) .inr))
    (Sum.elim (Sum.elim .inl (fun k => .inr (.inl k))) (fun m => .inr (.inr m)))
    (fun a => by rcases a with i | k | m <;> rfl) (fun a => by rcases a with (i | k) | m <;> rfl)
    (fun g a b => by rcases a with i | k | m <;> rcases b with j | l | n <;> rfl)

/-- **Direct sums are commutative** up to isomorphism: `ρ ⊕ σ ≅ σ ⊕ ρ`. -/
theorem Iso.dsum_comm (ρ : Rep G K ι) (σ : Rep G K κ) : Iso (ρ.dsum σ) (σ.dsum ρ) :=
  iso_of_reindex _ _ (Sum.elim .inr .inl) (Sum.elim .inr .inl)
    (fun a => by rcases a with k | i <;> rfl) (fun a => by rcases a with i | k <;> rfl)
    (fun g a b => by rcases a with k | i <;> rcases b with l | j <;> rfl)

/-- **Adding the zero representation.** `ρ ≅ ρ ⊕ 0`, with `0` the representation on
`K^(Fin 0)`. -/
theorem iso_dsum_empty (ρ : Rep G K ι) : Iso ρ (ρ.dsum (Rep.trivial G K (Fin 0))) :=
  iso_of_reindex _ _ (Sum.elim id (fun k => k.elim0)) .inl
    (fun a => match a with | .inl _ => rfl | .inr k => k.elim0) (fun _ => rfl)
    (fun g a b => by
      rcases a with i | k
      · rcases b with j | l
        · rfl
        · exact l.elim0
      · exact k.elim0)

/-- A type with `card ι = 0` has no elements. -/
theorem not_of_card_zero (h : card ι = 0) (x : ι) : False := by
  have := List.length_pos_of_mem (complete x)
  unfold card at h; omega

/-- **Representations of degree zero** are all isomorphic. -/
theorem iso_of_card_zero (ρ : Rep G K ι) (σ : Rep G K κ) (hι : card ι = 0) (hκ : card κ = 0) :
    Iso ρ σ :=
  ⟨0, 0, fun _ => ext fun k _ => (not_of_card_zero hκ k).elim,
    ext fun i _ => (not_of_card_zero hι i).elim, ext fun k _ => (not_of_card_zero hκ k).elim⟩

end Reindex

/-! ## Splitting an irreducible off a sum of irreducibles -/

variable {G : Type u} [Group G] [FiniteType G]

/-- `ncast N · ncast |G| ≠ 0` in `ℂ` for `N ≥ 1`. -/
theorem ncast_mul_card_ne_zero {N : Nat} (hN : 1 ≤ N) :
    (ncast N : C) * ncast (card G) ≠ 0 := by
  rw [← ncast_mul_C]
  exact ncast_ne_zero_complex (Nat.mul_pos hN (card_group_pos (G := G)))

/-- **Every sum of irreducibles contains an irreducible.** If `SumIrr S`, there is an
irreducible `τ` with `Σ_g χ_S(g) χ_τ(g⁻¹) = N · |G|` for some `N ≥ 1`. -/
theorem sumIrr_exists_irr {κ : Type} [FiniteType κ] {S : Rep G C κ} (hS : SumIrr κ S) :
    ∃ (μ : Type) (_ : FiniteType μ) (τ : Rep G C μ), Irreducible τ ∧
      ∃ N : Nat, 1 ≤ N ∧ pairing (character S) (character τ) = ncast N * ncast (card G) := by
  induction hS with
  | irr σ hσ =>
    obtain ⟨N, hN, h⟩ := sumIrr_pairing_self (SumIrr.irr σ hσ)
    exact ⟨_, inferInstance, σ, hσ, N, hN, h⟩
  | sum σ₁ σ₂ _ hs₂ ih₁ _ =>
    obtain ⟨μ, _, τ, hτ, N, hN, h⟩ := ih₁
    obtain ⟨M, hM⟩ := sumIrr_pairing hs₂ (SumIrr.irr τ hτ)
    refine ⟨μ, inferInstance, τ, hτ, N + M, by omega, ?_⟩
    rw [character_dsum', pairing_add_left, h, hM, ncast_add_C, Ring.right_distrib]

/-- **Splitting off an irreducible.** If `S` is a sum of irreducibles and `τ` is an irreducible
with `Σ_g χ_S(g) χ_τ(g⁻¹) ≠ 0`, then `S ≅ τ ⊕ S'` for some representation `S'`. -/
theorem sumIrr_split {κ : Type} [FiniteType κ] {S : Rep G C κ} (hS : SumIrr κ S)
    {μ : Type} [FiniteType μ] {τ : Rep G C μ} (hτ : Irreducible τ)
    (hp : pairing (character S) (character τ) ≠ 0) :
    ∃ (κ' : Type) (_ : FiniteType κ') (S' : Rep G C κ'), Iso S (τ.dsum S') := by
  revert hp
  induction hS with
  | irr σ hσ =>
    intro hp
    have hiso : Iso τ σ := Classical.byContradiction fun hn =>
      hp (by rw [orthogonality_complex hτ hσ]; simp only [hn, ↓reduceIte])
    exact ⟨Fin 0, inferInstance, Rep.trivial G C (Fin 0), hiso.symm.trans (iso_dsum_empty τ)⟩
  | sum σ₁ σ₂ _ _ ih₁ ih₂ =>
    intro hp
    rw [character_dsum', pairing_add_left] at hp
    by_cases h₁ : pairing (character σ₁) (character τ) = 0
    · rw [h₁, Ring.zero_add] at hp
      obtain ⟨κ', _, S', hi⟩ := ih₂ hp
      refine ⟨_ ⊕ κ', inferInstance, σ₁.dsum S', ?_⟩
      exact ((Iso.refl σ₁).dsum hi).trans ((Iso.dsum_assoc σ₁ τ S').symm.trans
        (((Iso.dsum_comm σ₁ τ).dsum (Iso.refl S')).trans (Iso.dsum_assoc τ σ₁ S')))
    · obtain ⟨κ', _, S', hi⟩ := ih₁ h₁
      exact ⟨κ' ⊕ _, inferInstance, S'.dsum σ₂,
        (hi.dsum (Iso.refl σ₂)).trans (Iso.dsum_assoc τ S' σ₂)⟩

/-- A type of positive size is non-empty. -/
theorem nonempty_of_card_pos {ι : Type} [FiniteType ι] (h : 0 < card ι) : Nonempty ι := by
  obtain ⟨x, _⟩ := List.exists_mem_of_length_pos h
  exact ⟨x⟩

/-- Equal characters, by induction on the degree `n`. -/
theorem iso_of_character_eq_aux : ∀ (n : Nat) {ι κ : Type} [FiniteType ι] [FiniteType κ]
    (ρ : Rep G C ι) (σ : Rep G C κ), card ι = n → character ρ = character σ → Iso ρ σ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro ι κ _ _ ρ σ hn hχ
    have hcard : card ι = card κ := by
      have e := congrFun hχ 1
      rw [character_one, character_one] at e
      exact ncast_inj_C e
    by_cases h0 : n = 0
    · exact iso_of_card_zero ρ σ (hn.trans h0) (hcard.symm.trans (hn.trans h0))
    have hG := ncast_ne_zero_complex (card_group_pos (G := G))
    obtain ⟨κ₁, _, S₁, hs₁, i₁⟩ :=
      complete_reducibility C.isField hG ρ (nonempty_of_card_pos (by omega))
    obtain ⟨κ₂, _, S₂, hs₂, i₂⟩ :=
      complete_reducibility C.isField hG σ (nonempty_of_card_pos (by omega))
    obtain ⟨μ, _, τ, hτ, N, hN, hp⟩ := sumIrr_exists_irr hs₁
    have hp0 : pairing (character S₁) (character τ) ≠ 0 := by
      rw [hp]; exact ncast_mul_card_ne_zero hN
    have hS : character S₂ = character S₁ :=
      (character_eq_of_iso i₂).symm.trans (hχ.symm.trans (character_eq_of_iso i₁))
    obtain ⟨κ', _, S', j₁⟩ := sumIrr_split hs₁ hτ hp0
    obtain ⟨κ'', _, S'', j₂⟩ := sumIrr_split hs₂ hτ (by rw [hS]; exact hp0)
    have hχ' : character S' = character S'' := by
      funext g
      have e := congrFun ((character_eq_of_iso j₁).symm.trans
        (hS.symm.trans (character_eq_of_iso j₂))) g
      rw [character_dsum, character_dsum] at e
      exact Ring.add_left_cancel e
    have hc : card ι = card μ + card κ' := by
      rw [(i₁.trans j₁).card_eq, card_sum]
    have hμ := card_pos_of_irreducible hτ
    have ih' := ih (card κ') (by omega) S' S'' rfl hχ'
    exact i₁.trans (j₁.trans (((Iso.refl τ).dsum ih').trans (j₂.symm.trans i₂.symm)))

/-- **Characters determine representations.** Two complex representations of a finite group
with the same character are isomorphic. -/
theorem iso_of_character_eq {ι κ : Type} [FiniteType ι] [FiniteType κ] {ρ : Rep G C ι}
    {σ : Rep G C κ} (h : character ρ = character σ) : Iso ρ σ :=
  iso_of_character_eq_aux _ ρ σ rfl h

/-- **Isomorphism is equality of characters.** Complex representations `ρ`, `σ` of a finite
group are isomorphic if and only if `χ_ρ = χ_σ`. -/
theorem iso_iff_character_eq {ι κ : Type} [FiniteType ι] [FiniteType κ] (ρ : Rep G C ι)
    (σ : Rep G C κ) : Iso ρ σ ↔ character ρ = character σ :=
  ⟨character_eq_of_iso, iso_of_character_eq⟩

end Foundations.Langlands
