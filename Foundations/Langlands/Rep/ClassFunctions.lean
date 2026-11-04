import Foundations.Langlands.Rep.Existence

/-!
# Characters detect class functions

A **class function** is a function `f : G → ℂ` constant on conjugacy classes. The characters
of the irreducible representations are class functions; this file proves the key fact behind
the statement that they *span* the class functions:

**If a class function `f` satisfies `Σ_g f(g) χ(g) = 0` for every irreducible character `χ`,
then `f = 0`** (`classFunction_eq_zero`).

The proof is the standard one. For a representation `ρ`, the operator
`T_f(ρ) = Σ_g f(g) ρ(g)` commutes with every `ρ(h)` because `f` is a class function
(`classOp_isGMap`). If `ρ` is irreducible, Schur's lemma makes `T_f(ρ)` a scalar `z`, and its
trace `z · dim ρ = Σ_g f(g) χ_ρ(g)` vanishes, so `T_f(ρ) = 0`. The vanishing passes to direct
sums and to isomorphic representations, hence (by complete reducibility) to the regular
representation. There, `T_f` applied to the basis vector `e_1` is `Σ_g f(g) e_g`, the vector
`f` itself.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u

variable {G : Type u} [Group G] [FiniteType G]

/-! ## The operator `Σ_g f(g) ρ(g)` -/

/-- The operator `T_f(ρ) = Σ_g f(g) ρ(g)` of a function `f : G → ℂ` on a representation. -/
noncomputable def classOp {ι : Type} [FiniteType ι] (f : G → C) (ρ : Rep G C ι) :
    Mat ι ι C :=
  isum (fun g => f g • ρ g)

/-- `T_f(ρ) x = Σ_g f(g) ρ(g) x`. -/
theorem classOp_mulVec {ι : Type} [FiniteType ι] (f : G → C) (ρ : Rep G C ι) (x : Vec ι C) :
    classOp f ρ *ᵥ x = isum (fun g => f g • (ρ g *ᵥ x)) := by
  rw [classOp, isum_mulVec]; exact isum_congr fun g => smul_mulVec _ _ _

/-- Reindexing a sum over `G` by conjugation `g ↦ h g h⁻¹`. -/
theorem isum_conj_reindex {A : Type} [AddAbGroup A] (h : G) (F : G → A) :
    isum (fun g => F (h * g * h⁻¹)) = isum F :=
  isum_comp_bij (fun g => h * g * h⁻¹)
    (fun a b e => by
      have e' := Group.mul_right_cancel e
      exact Group.mul_left_cancel e')
    (fun y => ⟨h⁻¹ * y * h, by
      simp only [Group.mul_assoc, Group.mul_inv_cancel, Group.mul_one,
        Group.mul_inv_cancel_left]⟩) F

/-- **`T_f(ρ)` is a `G`-map when `f` is a class function.** -/
theorem classOp_isGMap {ι : Type} [FiniteType ι] {f : G → C} (hf : IsClassFunction f)
    (ρ : Rep G C ι) : IsGMap ρ ρ (classOp f ρ) := by
  apply IsGMap.of_act; intro h x
  rw [classOp_mulVec, classOp_mulVec, mulVec_isum, ← isum_conj_reindex h]
  apply isum_congr; intro g
  rw [hf, mulVec_smul, ← ρ.act_mul, ← ρ.act_mul]
  congr 3
  rw [Group.mul_assoc, Group.inv_mul_cancel, Group.mul_one]

/-- The trace of `T_f(ρ)` is `Σ_g f(g) χ_ρ(g)`. -/
theorem trace_classOp {ι : Type} [FiniteType ι] (f : G → C) (ρ : Rep G C ι) :
    trace (classOp f ρ) = isum (fun g => f g * character ρ g) := by
  rw [classOp, trace_isum]; exact isum_congr fun g => trace_smul _ _

/-- `T_f(ρ)` **kills** every vector: `Σ_g f(g) ρ(g) x = 0` for all `x`. -/
def Kills {ι : Type} [FiniteType ι] (f : G → C) (ρ : Rep G C ι) : Prop :=
  ∀ x, isum (fun g => f g • (ρ g *ᵥ x)) = 0

/-- **Schur step.** If `ρ` is irreducible, `f` a class function and
`Σ_g f(g) χ_ρ(g) = 0`, then `T_f(ρ) = 0`. -/
theorem kills_of_irreducible {ι : Type} [FiniteType ι] {f : G → C} (hf : IsClassFunction f)
    {ρ : Rep G C ι} (hρ : Irreducible ρ) (h0 : isum (fun g => f g * character ρ g) = 0) :
    Kills f ρ := by
  obtain ⟨z, hz⟩ := schur_complex hρ (classOp_isGMap hf ρ)
  have htr := trace_classOp f ρ
  rw [hz, trace_smul, trace_one, h0] at htr
  obtain ⟨t, ht⟩ := C.isField.2 _ (ncast_ne_zero_complex (card_pos_of_irreducible hρ))
  have hz0 : z = 0 := by
    calc z = z * (ncast (card ι) * t) := by rw [ht, Ring.mul_one]
      _ = z * ncast (card ι) * t := (Ring.mul_assoc _ _ _).symm
      _ = 0 := by rw [htr, Ring.zero_mul]
  intro x
  rw [← classOp_mulVec, hz, hz0, smul_mulVec]
  exact Vec.ext fun i => Ring.zero_mul _

/-- Killing passes to direct sums. -/
theorem kills_dsum {ι κ : Type} [FiniteType ι] [FiniteType κ] {f : G → C} {ρ : Rep G C ι}
    {σ : Rep G C κ} (h₁ : Kills f ρ) (h₂ : Kills f σ) : Kills f (ρ.dsum σ) := by
  intro x
  apply Vec.ext; intro a
  rw [Vec.isum_apply]
  cases a with
  | inl i =>
    have e := congrFun (h₁ (fun j => x (.inl j))) i
    rw [Vec.isum_apply] at e
    refine Eq.trans (isum_congr fun g => ?_) e
    show f g * (blockDiag (ρ g) (σ g) *ᵥ x) (.inl i) = f g * (ρ g *ᵥ fun j => x (.inl j)) i
    rw [blockDiag_mulVec_inl]; rfl
  | inr k =>
    have e := congrFun (h₂ (fun j => x (.inr j))) k
    rw [Vec.isum_apply] at e
    refine Eq.trans (isum_congr fun g => ?_) e
    show f g * (blockDiag (ρ g) (σ g) *ᵥ x) (.inr k) = f g * (σ g *ᵥ fun j => x (.inr j)) k
    rw [blockDiag_mulVec_inr]; rfl

/-- Killing passes along isomorphisms. -/
theorem kills_of_iso {ι κ : Type} [FiniteType ι] [FiniteType κ] {f : G → C} {ρ : Rep G C ι}
    {σ : Rep G C κ} (hi : Iso ρ σ) (h : Kills f σ) : Kills f ρ := by
  obtain ⟨T, S, hT, hST, _⟩ := hi
  intro x
  have e : ∀ g, f g • (ρ g *ᵥ x) = S *ᵥ (f g • (σ g *ᵥ (T *ᵥ x))) := fun g => by
    rw [mulVec_smul, ← hT.act, mulVec_mulVec, hST, one_mulVec]
  rw [isum_congr e, ← mulVec_isum, h, mulVec_zero]

/-- A sum of irreducibles is killed when every irreducible character is orthogonal to `f`. -/
theorem kills_sumIrr {f : G → C} (hf : IsClassFunction f)
    (H : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ →
      isum (fun g => f g * character τ g) = 0)
    {κ : Type} [FiniteType κ] {σ : Rep G C κ} (hs : SumIrr κ σ) : Kills f σ := by
  induction hs with
  | irr σ hσ => exact kills_of_irreducible hf hσ (H σ hσ)
  | sum σ₁ σ₂ _ _ ih₁ ih₂ => exact kills_dsum ih₁ ih₂

/-- **Characters detect class functions.** If `f : G → ℂ` is a class function on a finite
group with `Σ_g f(g) χ(g) = 0` for the character `χ` of every irreducible complex
representation (on an index type in `Type`), then `f = 0`. -/
theorem classFunction_eq_zero {G : Type} [Group G] [FiniteType G] {f : G → C}
    (hf : IsClassFunction f)
    (H : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ →
      isum (fun g => f g * character τ g) = 0) (g : G) : f g = 0 := by
  have hG := ncast_ne_zero_complex (card_group_pos (G := G))
  obtain ⟨κ, _, σ, hs, hiso⟩ := complete_reducibility C.isField hG (regularRep G C) ⟨1⟩
  have hk := kills_of_iso hiso (kills_sumIrr hf H hs) (Vec.basisVec 1)
  have e := congrFun hk g
  rw [Vec.isum_apply] at e
  have e2 : ∀ h : G, (f h • (regularRep G C h *ᵥ Vec.basisVec 1)) g = f h * kd h g := fun h => by
    show f h * (regularRep G C h *ᵥ Vec.basisVec 1) g = _
    rw [mulVec_basisVec]
    show f h * kd g (h * 1) = _
    rw [Group.mul_one, kd_comm]
  rw [isum_congr e2, isum_mul_kd] at e
  exact e

end Foundations.Langlands
