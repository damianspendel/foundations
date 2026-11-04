import Foundations.Langlands.Rep.Regular

/-!
# A completeness criterion for lists of irreducibles

Burnside's formula `Σ_k (dim ρ_k)² = |G|` (`sum_sq_degrees`) was proved for a list of
irreducible complex representations that is already known to be complete. This file proves
the converse direction, which is what one uses in practice to certify that a list found by hand
is the full list of irreducibles.

* Isomorphic representations have equal degree (`Iso.card_eq`), by comparing characters at `1`.
* For **any** list `ρ₀, …, ρ_{r−1}` of pairwise non-isomorphic irreducible complex
  representations, `Σ_k (dim ρ_k)² ≤ |G|` (`sum_sq_le`). The regular representation is a sum of
  irreducibles; in that sum, each `ρ_k` occurs `dim ρ_k` times (its multiplicity is read off by
  `pairing_regular`), and summands isomorphic to different `ρ_k` are different summands.
  Evaluating at `1` gives the inequality.
* **Completeness criterion** (`complete_of_sum_sq`): if equality `Σ_k (dim ρ_k)² = |G|` holds,
  every irreducible representation is isomorphic to some `ρ_k`. Otherwise a missing
  irreducible `τ` could be added to the list, and the inequality for the longer list would
  give `|G| + (dim τ)² ≤ |G|`. Together with `sum_sq_degrees` this gives
  `complete_iff_sum_sq`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u

/-! ## Degrees of isomorphic representations -/

/-- **Isomorphic representations have equal degree.** Their characters agree, in particular
at `1`, where the character is the degree. -/
theorem Iso.card_eq {G : Type u} [Group G] {ι κ : Type} [FiniteType ι] [FiniteType κ]
    {ρ : Rep G C ι} {σ : Rep G C κ} (h : Iso ρ σ) : card ι = card κ := by
  have e := congrFun (character_eq_of_iso h) 1
  rw [character_one, character_one] at e
  exact ncast_inj_C e

/-! ## Finite sums of natural numbers -/

/-- A `natSum` of zeros is zero. -/
theorem natSum_eq_zero : ∀ {r : Nat} {f : Fin r → Nat}, (∀ k, f k = 0) → natSum f = 0
  | 0, _, _ => rfl
  | _ + 1, f, h => by
    show f 0 + natSum (fun i => f i.succ) = 0
    rw [h 0, natSum_eq_zero (fun i => h i.succ)]

/-- `natSum` is additive. -/
theorem natSum_add : ∀ {r : Nat} (f g : Fin r → Nat),
    natSum (fun k => f k + g k) = natSum f + natSum g
  | 0, _, _ => rfl
  | _ + 1, f, g => by
    show f 0 + g 0 + natSum (fun i => f i.succ + g i.succ) =
      (f 0 + natSum (fun i => f i.succ)) + (g 0 + natSum (fun i => g i.succ))
    rw [natSum_add]; omega

/-- A `natSum` with a single non-zero term is that term. -/
theorem natSum_single : ∀ {r : Nat} {f : Fin r → Nat} (k₀ : Fin r),
    (∀ k, k ≠ k₀ → f k = 0) → natSum f = f k₀
  | 0, _, k₀, _ => k₀.elim0
  | _ + 1, f, k₀, h => by
    show f 0 + natSum (fun i => f i.succ) = f k₀
    cases k₀ using Fin.cases with
    | zero =>
      rw [natSum_eq_zero (fun i => h i.succ (Fin.succ_ne_zero i)), Nat.add_zero]
    | succ j =>
      rw [h 0 (Fin.succ_ne_zero j).symm, Nat.zero_add,
        natSum_single (f := fun i => f i.succ) j
          (fun i hi => h i.succ (fun e => hi (Fin.succ_inj.1 e)))]

/-! ## Counting summands isomorphic to a given irreducible -/

variable {G : Type u} [Group G] [FiniteType G]
variable {r : Nat} {ιs : Fin r → Type} [∀ k, FiniteType (ιs k)]

/-- **Counting the summands of a sum of irreducibles.** Let `ρ₀, …, ρ_{r−1}` be pairwise
non-isomorphic irreducibles and `σ` a sum of irreducibles. There are natural numbers `n_k` (the
numbers of summands of `σ` isomorphic to `ρ_k`) with `Σ_g χ_σ(g) χ_k(g⁻¹) = n_k |G|` and
`Σ_k n_k dim ρ_k ≤ dim σ`. -/
theorem sumIrr_count (ρs : ∀ k, Rep G C (ιs k)) (hirr : ∀ k, Irreducible (ρs k))
    (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k')) {κ : Type} [FiniteType κ]
    {σ : Rep G C κ} (hs : SumIrr κ σ) :
    ∃ n : Fin r → Nat,
      (∀ k, pairing (character σ) (character (ρs k)) = ncast (n k) * ncast (card G)) ∧
      natSum (fun k => n k * card (ιs k)) ≤ card κ := by
  classical
  induction hs with
  | irr σ hσ =>
    by_cases hex : ∃ k, Iso (ρs k) σ
    · obtain ⟨k₀, hk₀⟩ := hex
      have hne : ∀ k, k ≠ k₀ → ¬ Iso (ρs k) σ := fun k hk h =>
        hdist k k₀ hk (h.trans hk₀.symm)
      refine ⟨fun k => if k = k₀ then 1 else 0, fun k => ?_, ?_⟩
      · rw [orthogonality_complex (hirr k) hσ]
        by_cases hk : k = k₀
        · subst hk; simp only [hk₀, ↓reduceIte]; exact (Ring.one_mul _).symm
        · simp only [hne k hk, hk, ↓reduceIte]; exact (Ring.zero_mul _).symm
      · rw [natSum_single k₀ (fun k hk => by simp only [hk, ↓reduceIte, Nat.zero_mul])]
        simp only [↓reduceIte, Nat.one_mul]
        exact Nat.le_of_eq hk₀.card_eq
    · refine ⟨fun _ => 0, fun k => ?_, ?_⟩
      · rw [orthogonality_complex (hirr k) hσ]
        rw [ite_eq_right (fun h => hex ⟨k, h⟩)]; exact (Ring.zero_mul _).symm
      · rw [natSum_eq_zero (fun k => Nat.zero_mul _)]; exact Nat.zero_le _
  | sum σ₁ σ₂ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁, b₁⟩ := ih₁
    obtain ⟨n₂, h₂, b₂⟩ := ih₂
    refine ⟨fun k => n₁ k + n₂ k, fun k => ?_, ?_⟩
    · rw [character_dsum', pairing_add_left, h₁, h₂, ncast_add_C, Ring.right_distrib]
    · rw [card_sum]
      have e : natSum (fun k => (n₁ k + n₂ k) * card (ιs k)) =
          natSum (fun k => n₁ k * card (ιs k)) + natSum (fun k => n₂ k * card (ιs k)) := by
        rw [← natSum_add]; congr 1; funext k; exact Nat.add_mul _ _ _
      rw [e]; omega

/-! ## The inequality and the completeness criterion -/

/-- **Burnside's inequality.** For any list `ρ₀, …, ρ_{r−1}` of pairwise non-isomorphic
irreducible complex representations of a finite group `G`, `Σ_k (dim ρ_k)² ≤ |G|`. -/
theorem sum_sq_le {G : Type} [Group G] [FiniteType G] {r : Nat} {ιs : Fin r → Type}
    [∀ k, FiniteType (ιs k)] (ρs : ∀ k, Rep G C (ιs k)) (hirr : ∀ k, Irreducible (ρs k))
    (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k')) :
    natSum (fun k => card (ιs k) * card (ιs k)) ≤ card G := by
  have hG := ncast_ne_zero_complex (card_group_pos (G := G))
  obtain ⟨κ, _, σ, hs, hiso⟩ := complete_reducibility C.isField hG (regularRep G C) ⟨1⟩
  obtain ⟨n, hn, hb⟩ := sumIrr_count ρs hirr hdist hs
  have hnk : ∀ k, n k = card (ιs k) := fun k => by
    have e := hn k
    rw [← character_eq_of_iso hiso, pairing_regular] at e
    exact ncast_inj_C (cancel_card e.symm)
  have e : natSum (fun k => card (ιs k) * card (ιs k)) = natSum (fun k => n k * card (ιs k)) := by
    congr 1; funext k; rw [hnk k]
  rw [← hiso.card_eq] at hb
  rw [e]; exact hb

/-! ### Adding one representation to a list -/

/-- The index types of the list `τ, ρ₀, …, ρ_{r−1}`. -/
def consIdx (κ : Type) (ιs : Fin r → Type) : Fin (r + 1) → Type :=
  fun k => Fin.cases κ ιs k

/-- The index types of an extended list are finite. -/
instance consIdx.instFinite (κ : Type) [FiniteType κ] (ιs : Fin r → Type)
    [∀ k, FiniteType (ιs k)] (k : Fin (r + 1)) : FiniteType (consIdx κ ιs k) :=
  Fin.cases (motive := fun k => FiniteType (consIdx κ ιs k)) (inferInstanceAs (FiniteType κ))
    (fun i => inferInstanceAs (FiniteType (ιs i))) k

/-- The extended list `τ, ρ₀, …, ρ_{r−1}`. -/
def consRep {κ : Type} [FiniteType κ] (τ : Rep G C κ) (ρs : ∀ k, Rep G C (ιs k)) :
    ∀ k : Fin (r + 1), Rep G C (consIdx κ ιs k) :=
  fun k => Fin.cases (motive := fun k => Rep G C (consIdx κ ιs k)) τ ρs k

/-- Adding an irreducible `τ` to a list of irreducibles gives a list of irreducibles. -/
theorem consRep_irreducible {κ : Type} [FiniteType κ] (τ : Rep G C κ) (ρs : ∀ k, Rep G C (ιs k))
    (hτ : Irreducible τ) (hirr : ∀ k, Irreducible (ρs k)) : ∀ k, Irreducible (consRep τ ρs k) :=
  fun k => by
    cases k using Fin.cases with
    | zero => exact hτ
    | succ j => exact hirr j

/-- Adding to a pairwise non-isomorphic list a representation `τ` isomorphic to none of its
members keeps it pairwise non-isomorphic. -/
theorem consRep_distinct {κ : Type} [FiniteType κ] (τ : Rep G C κ) (ρs : ∀ k, Rep G C (ιs k))
    (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k')) (hno : ∀ k, ¬ Iso τ (ρs k)) :
    ∀ k k', k ≠ k' → ¬ Iso (consRep τ ρs k) (consRep τ ρs k') := by
  intro k k' hkk'
  cases k using Fin.cases with
  | zero =>
    cases k' using Fin.cases with
    | zero => exact absurd rfl hkk'
    | succ j => exact hno j
  | succ i =>
    cases k' using Fin.cases with
    | zero => exact fun h => hno i h.symm
    | succ j => exact hdist i j (fun e => hkk' (congrArg Fin.succ e))

/-- **Completeness criterion.** If `ρ₀, …, ρ_{r−1}` are pairwise non-isomorphic irreducible
complex representations of a finite group `G` with `Σ_k (dim ρ_k)² = |G|`, then every
irreducible complex representation of `G` is isomorphic to one of them. -/
theorem complete_of_sum_sq {G : Type} [Group G] [FiniteType G] {r : Nat} {ιs : Fin r → Type}
    [∀ k, FiniteType (ιs k)] (ρs : ∀ k, Rep G C (ιs k)) (hirr : ∀ k, Irreducible (ρs k))
    (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k'))
    (hsum : natSum (fun k => card (ιs k) * card (ιs k)) = card G)
    {κ : Type} [FiniteType κ] (τ : Rep G C κ) (hτ : Irreducible τ) : ∃ k, Iso τ (ρs k) := by
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ k, ¬ Iso τ (ρs k) := fun k h => hno ⟨k, h⟩
  have hirr' := consRep_irreducible τ ρs hτ hirr
  have hdist' := consRep_distinct τ ρs hdist hno'
  have hle := sum_sq_le (consRep τ ρs) hirr' hdist'
  have hpos := card_pos_of_irreducible hτ
  have e : natSum (fun k => card (consIdx κ ιs k) * card (consIdx κ ιs k)) =
      card κ * card κ + natSum (fun k => card (ιs k) * card (ιs k)) := rfl
  rw [e, hsum] at hle
  have : 0 < card κ * card κ := Nat.mul_pos hpos hpos
  omega

/-- **Completeness is equivalent to Burnside's formula.** A list of pairwise non-isomorphic
irreducible complex representations of a finite group `G` is complete (every irreducible
representation is isomorphic to a member) if and only if `Σ_k (dim ρ_k)² = |G|`. -/
theorem complete_iff_sum_sq {G : Type} [Group G] [FiniteType G] {r : Nat} {ιs : Fin r → Type}
    [∀ k, FiniteType (ιs k)] (ρs : ∀ k, Rep G C (ιs k)) (hirr : ∀ k, Irreducible (ρs k))
    (hdist : ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k')) :
    (∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k)) ↔
      natSum (fun k => card (ιs k) * card (ιs k)) = card G :=
  ⟨fun h => sum_sq_degrees ρs hirr hdist h, fun h _ _ τ hτ => complete_of_sum_sq ρs hirr hdist h τ hτ⟩

end Foundations.Langlands
