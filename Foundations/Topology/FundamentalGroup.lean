import Foundations.Topology.Paths

/-!
# The fundamental group

Concatenation of paths is not associative: `(γ ⬝ δ) ⬝ ε` spends half of the time on `γ`, while
`γ ⬝ (δ ⬝ ε)` spends only a quarter on it. The two paths trace out the same points in the same
order, only at different speeds — and speed is precisely what a homotopy can change. The same is
true of the constant path as an identity and of the reverse path as an inverse. Each of these
laws is an instance of the **reparametrisation lemma** of the previous file: both sides are one
path composed with two reparametrisations of `[0, 1]` that agree at the endpoints.

Passing to homotopy classes of **loops** (paths from `x₀` back to `x₀`) the laws become
equations, and Poincaré's **fundamental group** `π₁(X, x₀)` appears: an instance of the
project's `Group` class from Part IV (associativity, a left identity and left inverses suffice
there; the right-handed laws are theorems).

This is the characteristic move of algebraic topology: a space is replaced by an algebraic object
which forgets almost everything — distances, shapes, even the dimension — but keeps exactly what
survives continuous deformation.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

variable {X Y : Type} [MetricSpace X] [MetricSpace Y]

/-- Constant maps are continuous. -/
theorem continuous_constant (c : Y) : Continuous (fun _ : X => c) :=
  fun _ _ hε => ⟨1, by grind, fun _ _ => by rw [dist_self]; exact hε⟩

/-- `t ↦ t + c` is continuous. -/
theorem continuous_add_const (c : R) : Continuous (fun t : R => t + c) :=
  (continuous_affine 1 c).congr fun t => by grind

/-- `t ↦ (t + 1)/2` is continuous. -/
theorem continuous_half_add : Continuous (fun t : R => (t + 1) / 2) :=
  (continuous_affine (1 / 2) (1 / 2)).congr fun t => by grind

/-- The identity of the line is continuous. -/
theorem continuous_id_R : Continuous (fun t : R => t) :=
  (continuous_affine 1 0).congr fun t => by grind

namespace Path

variable {x y z w : X}

/-- Close goals produced by unfolding piecewise reparametrisations. -/
macro "reparam_tac" : tactic => `(tactic| (
  repeat' split
  all_goals first
    | rfl
    | (exfalso; grind)
    | (congr 1 <;> grind)
    | (simp only [Path.source, Path.target])
    | (rw [show (2 : R) * 0 = 0 by grind]; simp only [Path.source, Path.target])))

/-- The reparametrisation turning `γ ⬝ (δ ⬝ ε)` into `(γ ⬝ δ) ⬝ ε`. -/
noncomputable def assocParam (t : R) : R :=
  open Classical in if t ≤ 1 / 4 then 2 * t else if t ≤ 1 / 2 then t + 1 / 4 else (t + 1) / 2

/-- The associativity reparametrisation is continuous. -/
theorem continuous_assocParam : Continuous assocParam :=
  Continuous.paste continuous_two_mul
    (Continuous.paste (continuous_add_const (1 / 4)) continuous_half_add (by grind))
    (by rw [ite_eq_left (by grind)]; grind)

/-- **Associativity up to homotopy.** `(γ ⬝ δ) ⬝ ε ≃ γ ⬝ (δ ⬝ ε)`. -/
theorem trans_assoc (γ : Path x y) (δ : Path y z) (ε : Path z w) :
    Homotopic ((γ.trans δ).trans ε) (γ.trans (δ.trans ε)) :=
  homotopic_of_reparam (γ.trans (δ.trans ε)).cont continuous_assocParam continuous_id_R
    (by unfold assocParam; rw [ite_eq_left (by grind)]; grind)
    (by unfold assocParam; rw [ite_eq_right (by grind), ite_eq_right (by grind)]; grind) _ _
    (fun t _ _ => by
      simp only [trans_apply]
      by_cases h1 : t ≤ 1 / 4
      · rw [show assocParam t = 2 * t by unfold assocParam; rw [ite_eq_left h1]]; reparam_tac
      by_cases h2 : t ≤ 1 / 2
      · rw [show assocParam t = t + 1 / 4 by
          unfold assocParam; rw [ite_eq_right h1, ite_eq_left h2]]; reparam_tac
      · rw [show assocParam t = (t + 1) / 2 by
          unfold assocParam; rw [ite_eq_right h1, ite_eq_right h2]]; reparam_tac)
    (fun _ _ _ => rfl)

/-- **Left identity up to homotopy.** `const ⬝ γ ≃ γ`. -/
theorem const_trans (γ : Path x y) : Homotopic ((const x).trans γ) γ :=
  homotopic_of_reparam (φ := fun t => open Classical in if t ≤ 1 / 2 then 0 else 2 * t - 1)
    γ.cont (Continuous.paste (continuous_constant 0) continuous_two_mul_sub_one (by grind))
    continuous_id_R (by rw [ite_eq_left (by grind)]) (by rw [ite_eq_right (by grind)]; grind) _ _
    (fun t _ _ => by simp only [trans_apply, const]; reparam_tac)
    (fun _ _ _ => rfl)

/-- **Right identity up to homotopy.** `γ ⬝ const ≃ γ`. -/
theorem trans_const (γ : Path x y) : Homotopic (γ.trans (const y)) γ :=
  homotopic_of_reparam (φ := fun t => open Classical in if t ≤ 1 / 2 then 2 * t else 1)
    γ.cont (Continuous.paste continuous_two_mul (continuous_constant 1) (by grind))
    continuous_id_R (by rw [ite_eq_left (by grind)]; grind) (by rw [ite_eq_right (by grind)]) _ _
    (fun t _ _ => by simp only [trans_apply, const]; reparam_tac)
    (fun _ _ _ => rfl)

/-- **Left inverse up to homotopy.** `γ⁻¹ ⬝ γ ≃ const`. -/
theorem symm_trans (γ : Path x y) : Homotopic (γ.symm.trans γ) (const y) :=
  homotopic_of_reparam (φ := fun t => open Classical in if t ≤ 1 / 2 then 1 - 2 * t else 2 * t - 1)
    (ψ := fun _ => 1) γ.cont
    (Continuous.paste ((continuous_affine (-2) 1).congr fun t => by grind)
      continuous_two_mul_sub_one (by grind))
    (continuous_constant 1) (by rw [ite_eq_left (by grind)]; grind)
    (by rw [ite_eq_right (by grind)]; grind) _ _
    (fun t _ _ => by simp only [trans_apply, symm]; reparam_tac)
    (fun _ _ _ => by simp only [const, γ.target])

end Path

/-! ## The fundamental group -/

/-- Homotopy rel endpoints as a `Setoid` on paths from `x` to `y`. -/
def homotopySetoid (x y : X) : Setoid (Path x y) where
  r := Path.Homotopic
  iseqv := ⟨Path.Homotopic.refl, Path.Homotopic.symm, Path.Homotopic.trans⟩

/-- **Fundamental group.** `π₁(X, x₀)` (Poincaré 1895) is the set of homotopy classes rel
endpoints of loops at `x₀`. -/
def FundamentalGroup (X : Type) [MetricSpace X] (x₀ : X) : Type := Quotient (homotopySetoid x₀ x₀)

namespace FundamentalGroup

variable {x₀ : X}

/-- The class `[γ]` of a loop. -/
def mk (γ : Path x₀ x₀) : FundamentalGroup X x₀ := Quotient.mk _ γ

/-- Two loops have the same class exactly when they are homotopic. -/
theorem mk_eq_mk {γ δ : Path x₀ x₀} : mk γ = mk δ ↔ Path.Homotopic γ δ :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every element of `π₁` is the class of a loop. -/
theorem exists_mk (a : FundamentalGroup X x₀) : ∃ γ, mk γ = a := Quotient.exists_rep a

/-- **The fundamental group is a group.** Multiplication is `[γ][δ] = [γ ⬝ δ]`, identity the
class of the constant loop and inverse `[γ]⁻¹ = [γ⁻¹]`. -/
noncomputable instance instGroup : Foundations.Algebra.Group (FundamentalGroup X x₀) where
  mul := Quotient.lift₂ (fun γ δ => mk (γ.trans δ))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (Path.Homotopic.trans_congr h₁ h₂))
  one := mk (Path.const x₀)
  inv := Quotient.lift (fun γ => mk γ.symm) (fun _ _ h => Quotient.sound (Path.Homotopic.symm_congr h))
  mul_assoc a b c := by
    obtain ⟨γ, rfl⟩ := exists_mk a; obtain ⟨δ, rfl⟩ := exists_mk b; obtain ⟨ε, rfl⟩ := exists_mk c
    exact Quotient.sound (Path.trans_assoc γ δ ε)
  one_mul a := by
    obtain ⟨γ, rfl⟩ := exists_mk a
    exact Quotient.sound (Path.const_trans γ)
  inv_mul_cancel a := by
    obtain ⟨γ, rfl⟩ := exists_mk a
    exact Quotient.sound (Path.symm_trans γ)

/-- Multiplication of classes is concatenation of loops. -/
theorem mk_mul (γ δ : Path x₀ x₀) : mk γ * mk δ = mk (γ.trans δ) := rfl

/-- The identity is the class of the constant loop. -/
theorem one_def : (1 : FundamentalGroup X x₀) = mk (Path.const x₀) := rfl

/-- Inversion of classes is reversal of loops. -/
theorem mk_inv (γ : Path x₀ x₀) : (mk γ)⁻¹ = mk γ.symm := rfl

end FundamentalGroup

end Foundations.Topology
