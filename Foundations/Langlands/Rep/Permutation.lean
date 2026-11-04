import Foundations.Langlands.Rep.Abelian

/-!
# Permutation representations

The first representations anyone meets are permutation representations: a group acting on a
finite set `X` acts on the space `K^X` of functions (or formal combinations) by permuting the
basis vectors, `ρ(g) e_x = e_{g·x}`. Burnside's *Theory of Groups of Finite Order* (second
edition, 1911), which brought Frobenius' characters to a wide audience, makes them central: the
character of a permutation representation counts **fixed points**,

  `χ(g) = #{x ∈ X : g · x = x}`,

which is how characters were first computed in practice, and the sum `e_X = Σ_x e_x` spans a
copy of the trivial representation inside every permutation representation. By Maschke's
theorem it has an invariant complement.

In the Langlands programme the permutation representation of `G` on `G/H` is the *induced
representation* from the trivial character of `H`; induction from subgroups (Frobenius 1898)
is the mechanism behind the construction of Galois representations from Hecke characters and
behind Langlands' functoriality conjectures. Induction in general is not formalised here.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace

set_option linter.unusedSectionVars false

universe u v w

variable {G : Type u} [Group G] {X : Type v} [FiniteType X] [MulAction G X]
  {K : Type w} [CommRing K]

/-- **Permutation representation** of `G` on `K^X` for an action of `G` on a finite set `X`:
`ρ(g)` is the permutation matrix `(δ_{x, g·y})`, sending `e_y` to `e_{g·y}`. -/
noncomputable def permRep (G : Type u) [Group G] (K : Type w) [CommRing K] (X : Type v)
    [FiniteType X] [MulAction G X] : Rep G K X where
  toFun g := fun x y => kd x (g • y)
  map_one := ext fun x y => by
    show kd x ((1 : G) • y) = kd x y; rw [MulAction.one_smul]
  map_mul g h := ext fun x y => by
    show kd x ((g * h) • y) = isum (fun z => kd x (g • z) * kd z (h • y))
    rw [isum_mul_kd (h • y) (fun z => kd x (g • z)), MulAction.mul_smul]

/-- A sum of Kronecker deltas counts: `Σ_x δ_{x, f(x)} = #{x : x = f(x)}`. -/
theorem isum_kd_eq_count (f : X → X) :
    isum (fun x => (kd x (f x) : K)) = ncast (count (fun x => x = f x)) := by
  classical
  rw [count_eq_countP]
  unfold isum
  induction (elems : List X) with
  | nil => rfl
  | cons a l ih =>
    show kd a (f a) + lsum (l.map _) = _
    rw [ih, List.countP_cons]
    by_cases h : a = f a
    · have h1 : (kd a (f a) : K) = 1 := by rw [← h, kd_self]
      rw [h1, if_pos (decide_eq_true h), ncast_succ, Ring.add_comm]
    · rw [kd_ne h, if_neg (by simpa using h), Nat.add_zero]
      exact Ring.zero_add _

/-- **The character of a permutation representation counts fixed points**:
`χ(g) = #{x : g · x = x}`. -/
theorem character_permRep (g : G) :
    character (permRep G K X) g = ncast (count (fun x : X => g • x = x)) := by
  show isum (fun x => (kd x (g • x) : K)) = _
  rw [isum_kd_eq_count (g • ·)]
  congr 1; exact count_congr fun x => ⟨Eq.symm, Eq.symm⟩

/-- The vector `e_X = Σ_x e_x`, all of whose entries are `1`. -/
def onesVec (X : Type v) (K : Type w) [CommRing K] : Vec X K := fun _ => 1

/-- **`e_X` is fixed** by every permutation matrix. -/
theorem permRep_onesVec (g : G) : permRep G K X g *ᵥ onesVec X K = onesVec X K := by
  apply Vec.ext; intro x
  show isum (fun y => kd x (g • y) * (1 : K)) = 1
  rw [isum_single' _ (g⁻¹ • x)]
  · rw [MulAction.smul_inv_smul, kd_self, Ring.mul_one]
  · intro y hy
    have : x ≠ g • y := fun e => hy (by rw [e, MulAction.inv_smul_smul])
    rw [kd_ne this, Ring.zero_mul]

/-- **Every permutation representation contains the trivial representation**: the line
spanned by `e_X` is a subrepresentation on which `G` acts trivially. -/
theorem trivial_sub_permRep :
    Invariant (permRep G K X) (line (onesVec X K)) ∧
      ∀ g, ∀ v, v ∈ line (onesVec X K) → permRep G K X g *ᵥ v = v := by
  have hfix : ∀ g, ∀ v, v ∈ line (onesVec X K) → permRep G K X g *ᵥ v = v := by
    rintro g _ ⟨c, rfl⟩
    rw [mulVec_smul, permRep_onesVec]
  exact ⟨fun g v hv => by rw [hfix g v hv]; exact hv, hfix⟩

/-- **Splitting off the trivial summand.** Over a field with `|G| ≠ 0`, the line `K e_X` has
a `G`-invariant complement in every permutation representation (Maschke). -/
theorem permRep_splits [FiniteType G] (hF : IsField K) (hG : (ncast (card G) : K) ≠ 0) :
    ∃ W' : Subspace X K, Invariant (permRep G K X) W' ∧ IsCompl (line (onesVec X K)) W' :=
  maschke hF hG _ _ trivial_sub_permRep.1

end Foundations.Langlands
