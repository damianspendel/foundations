import Foundations.Langlands.Rep.Completeness

/-!
# Existence of a complete list of irreducibles

`sum_sq_degrees` assumes a complete list of irreducible representations. Here such a list is
shown to exist for every finite group, so Burnside's formula holds unconditionally
(`exists_sum_sq_degrees`).

The argument uses Burnside's inequality `sum_sq_le`. Every pairwise non-isomorphic list of
irreducibles has `r ≤ Σ_k (dim ρ_k)² ≤ |G|` members. If no list were complete, any list could
be extended by an irreducible isomorphic to none of its members (`consRep`), and starting from
the empty list one would obtain lists of every length, in particular of length `|G| + 1`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

/-- A `natSum` of terms that are all at least `1` is at least the number of terms. -/
theorem le_natSum : ∀ {r : Nat} {f : Fin r → Nat}, (∀ k, 1 ≤ f k) → r ≤ natSum f
  | 0, _, _ => Nat.le_refl 0
  | _ + 1, f, h => by
    show _ ≤ f 0 + natSum (fun i => f i.succ)
    have := le_natSum (f := fun i => f i.succ) (fun i => h i.succ)
    have := h 0
    omega

variable {G : Type} [Group G] [FiniteType G]

/-- `IsIrrList r ρs`: the representations `ρ₀, …, ρ_{r−1}` are irreducible and pairwise
non-isomorphic. -/
def IsIrrList (r : Nat) {ιs : Fin r → Type} [∀ k, FiniteType (ιs k)]
    (ρs : ∀ k, Rep G C (ιs k)) : Prop :=
  (∀ k, Irreducible (ρs k)) ∧ ∀ k k', k ≠ k' → ¬ Iso (ρs k) (ρs k')

/-- A list of `r` pairwise non-isomorphic irreducibles has `r ≤ |G|`. -/
theorem IsIrrList.le_card {r : Nat} {ιs : Fin r → Type} [∀ k, FiniteType (ιs k)]
    {ρs : ∀ k, Rep G C (ιs k)} (h : IsIrrList r ρs) : r ≤ card G := by
  have h1 := sum_sq_le ρs h.1 h.2
  have h2 : r ≤ natSum (fun k => card (ιs k) * card (ιs k)) := le_natSum fun k => by
    have := card_pos_of_irreducible (h.1 k)
    exact Nat.mul_pos this this
  omega

/-- **A complete list of irreducibles exists.** Every finite group `G` has finitely many
pairwise non-isomorphic irreducible complex representations `ρ₀, …, ρ_{r−1}` such that every
irreducible complex representation of `G` (on an index type in `Type`) is isomorphic to one of
them. -/
theorem exists_complete_irrList :
    ∃ (r : Nat) (ιs : Fin r → Type) (_ : ∀ k, FiniteType (ιs k)) (ρs : ∀ k, Rep G C (ιs k)),
      IsIrrList r ρs ∧
      ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k) := by
  apply Classical.byContradiction
  intro hno
  have grow : ∀ n : Nat, ∃ (ιs : Fin n → Type) (_ : ∀ k, FiniteType (ιs k))
      (ρs : ∀ k, Rep G C (ιs k)), IsIrrList n ρs := by
    intro n
    induction n with
    | zero => exact ⟨fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
        fun k => k.elim0, fun k => k.elim0⟩
    | succ n ih =>
      obtain ⟨ιs, inst, ρs, hl⟩ := ih
      have hnc : ¬ ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ →
          ∃ k, Iso τ (ρs k) := fun hc => hno ⟨n, ιs, inst, ρs, hl, hc⟩
      obtain ⟨κ, instκ, τ, hτ, hτn⟩ : ∃ (κ : Type) (_ : FiniteType κ) (τ : Rep G C κ),
          Irreducible τ ∧ ∀ k, ¬ Iso τ (ρs k) := by
        apply Classical.byContradiction
        intro h
        apply hnc
        intro κ _ τ hτ
        apply Classical.byContradiction
        intro hk
        exact h ⟨κ, inferInstance, τ, hτ, fun k hi => hk ⟨k, hi⟩⟩
      exact ⟨consIdx κ ιs, inferInstance, consRep τ ρs,
        consRep_irreducible τ ρs hτ hl.1, consRep_distinct τ ρs hl.2 hτn⟩
  obtain ⟨ιs, _, ρs, hl⟩ := grow (card G + 1)
  have := hl.le_card
  omega

/-- **Burnside's formula, unconditionally.** Every finite group `G` has a list
`ρ₀, …, ρ_{r−1}` of pairwise non-isomorphic irreducible complex representations which is
complete (every irreducible is isomorphic to a member) and satisfies
`Σ_k (dim ρ_k)² = |G|`. -/
theorem exists_sum_sq_degrees :
    ∃ (r : Nat) (ιs : Fin r → Type) (_ : ∀ k, FiniteType (ιs k)) (ρs : ∀ k, Rep G C (ιs k)),
      IsIrrList r ρs ∧
      (∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k)) ∧
      natSum (fun k => card (ιs k) * card (ιs k)) = card G := by
  obtain ⟨r, ιs, _, ρs, hl, hc⟩ := exists_complete_irrList (G := G)
  exact ⟨r, ιs, inferInstance, ρs, hl, hc, sum_sq_degrees ρs hl.1 hl.2 hc⟩

end Foundations.Langlands
