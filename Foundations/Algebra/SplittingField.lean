import Foundations.Algebra.QuinticRoots
import Foundations.Algebra.Constructible

/-!
# The splitting field of `x⁵ - 6x + 3` and its automorphisms

Let `β₀, …, β₄` be the five complex roots of `f = x⁵ - 6x + 3` (previous file). The **splitting
field** is the subfield `L = ℚ(β₀, …, β₄)` of `ℂ`, built here as a tower of simple extensions
`ℚ = T₀ ⊆ T₁ ⊆ ⋯ ⊆ T₅ = L` with `T_{n+1} = Tₙ(βₙ)` (`tower`). Each step is finite, so `L` is a
finite extension of `ℚ` (`L_finite`), and `L` lies in every subfield containing `ℚ` and the five
roots (`L_le`).

This file produces the automorphisms of `L` that the Galois-group computation needs.

* **Embeddings become automorphisms** (`autOfEmbedding`). A ring homomorphism `τ : L → ℂ` sends
  roots of `f` to roots of `f`, because `f` has rational coefficients. So it maps `L` into
  itself, since the elements of `L` sent into `L` form a subfield containing `ℚ` and all `βᵢ`.
  An injective endomorphism of the finite extension `L/ℚ` is onto, so `τ` is an automorphism.
* **Complex conjugation** restricts to an automorphism of `L` (`conjAut`).
* **Transitivity** (`exists_aut_root`). For every root `βⱼ` there is an automorphism of `L`
  sending `β₀` to `βⱼ`. Because `f` is irreducible over `ℚ`, the minimal polynomial of `β₀` is
  `f` up to a unit, so `id_ℚ` extends to `ℚ(β₀) → ℂ` with `β₀ ↦ βⱼ`. The fundamental theorem of
  algebra extends it further along the tower to `L → ℂ`, and the first point makes it an
  automorphism.
-/

namespace Foundations.Algebra

open Polynomial Subfield

universe u

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Roots and their behaviour under homomorphisms -/

/-- The five complex roots of `x⁵ - 6x + 3`, as chosen in `exists_quintic_roots`. -/
noncomputable def qβ : Fin 5 → ℂ := Classical.choose exists_quintic_roots

/-- The defining properties of the chosen roots. -/
theorem qβ_spec : (∀ i j, qβ i = qβ j → i = j) ∧
    (∀ i, eval (qβ i) (quinticPoly ℂ) = 0) ∧ (qβ 0).im = 0 ∧ (qβ 1).im = 0 ∧ (qβ 2).im = 0 ∧
    (qβ 3).im ≠ 0 ∧ qβ 4 = Foundations.Numbers.C.conj (qβ 3) :=
  Classical.choose_spec exists_quintic_roots

/-- Every complex root of `x⁵ - 6x + 3` is one of the `qβ i`. -/
theorem qβ_enum (w : ℂ) (hw : eval w (quinticPoly ℂ) = 0) : ∃ i, qβ i = w :=
  quintic_root_enum qβ_spec.1 qβ_spec.2.1 w hw

/-- **Ring homomorphisms send roots to roots.** Since `x⁵ - 6x + 3` has integer coefficients, a
ring homomorphism maps its roots to its roots. -/
theorem RingHom.map_quintic_root {A B : Type u} [CommRing A] [CommRing B] (σ : RingHom A B) {x : A}
    (h : eval x (quinticPoly A) = 0) : eval (σ.toFun x) (quinticPoly B) = 0 := by
  rw [← mapPoly_quinticPoly σ, ← RingHom.map_eval, h, σ.map_zero]

/-- `x⁵ - 6x + 3` is non-zero over any field. -/
theorem quinticPoly_ne_zero {A : Type _} [CommRing A] (h01 : (0 : A) ≠ 1) : quinticPoly A ≠ 0 := by
  intro h; have := natDegree_quinticPoly (R := A) h01; rw [h] at this
  unfold natDegree at this; rw [len_eq_zero.2 rfl] at this; exact absurd this (by decide)

/-- `f(z)` computed over a subfield equals `f(z)` computed in `ℂ`. -/
theorem aeval_quinticPoly (F : Subfield ℂ) (z : ℂ) :
    aeval F z (quinticPoly F) = eval z (quinticPoly ℂ) := by
  unfold aeval; rw [mapPoly_quinticPoly]

/-- A root of `x⁵ - 6x + 3` is algebraic over every subfield of `ℂ`. -/
theorem quintic_isAlgebraic (F : Subfield ℂ) {z : ℂ} (hz : eval z (quinticPoly ℂ) = 0) :
    IsAlgebraic F z :=
  ⟨quinticPoly F, quinticPoly_ne_zero (F.isField C.isField).1, by rw [aeval_quinticPoly, hz]⟩

/-- The roots indexed by natural numbers (`qβ 0` beyond `4`). -/
noncomputable def qβn (n : Nat) : ℂ := if h : n < 5 then qβ ⟨n, h⟩ else qβ 0

/-- Each `qβn n` is a root. -/
theorem qβn_root (n : Nat) : eval (qβn n) (quinticPoly ℂ) = 0 := by
  unfold qβn; split
  · exact qβ_spec.2.1 _
  · exact qβ_spec.2.1 _

/-! ## The tower `ℚ ⊆ ℚ(β₀) ⊆ ⋯ ⊆ L` -/

/-- The tower `T₀ = ℚ`, `T_{n+1} = Tₙ(βₙ)`. -/
noncomputable def tower : Nat → Subfield ℂ
  | 0 => Qc
  | n + 1 => adjoin C.isField (tower n) (qβn n) (quintic_isAlgebraic _ (qβn_root n))

/-- **The splitting field** `L = ℚ(β₀, β₁, β₂, β₃, β₄)` of `x⁵ - 6x + 3` inside `ℂ`. -/
noncomputable def L : Subfield ℂ := tower 5

/-- Each step of the tower is an extension. -/
theorem tower_le_succ (n : Nat) : (tower n).le (tower (n + 1)) := le_adjoin _ _ _ _

/-- The tower increases. -/
theorem tower_mono {m : Nat} : ∀ n, m ≤ n → (tower m).le (tower n)
  | 0, h => by rw [Nat.le_zero.1 h]; exact le_refl _
  | n + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · exact le_trans (tower_mono n (by omega)) (tower_le_succ n)
    · rw [h']; exact le_refl _

/-- `ℚ ⊆ Tₙ`. -/
theorem Qc_le_tower (n : Nat) : Qc.le (tower n) := tower_mono (m := 0) n (Nat.zero_le n)

/-- `ℚ ⊆ L`. -/
theorem Qc_le_L : Qc.le L := Qc_le_tower 5

/-- `βₙ ∈ T_{n+1}`. -/
theorem qβn_mem (n : Nat) : qβn n ∈ tower (n + 1) := mem_adjoin_self _ _ _ _

/-- `β₀ ∈ Tₙ` for `n ≥ 1`. -/
theorem qβ0_mem_tower {n : Nat} (hn : 1 ≤ n) : qβ 0 ∈ tower n :=
  tower_mono n hn _ (qβn_mem 0)

/-- Every root lies in `L`. -/
theorem qβ_mem (i : Fin 5) : qβ i ∈ L := by
  have : qβn i.val = qβ i := by unfold qβn; rw [dite_eq_left i.isLt]
  rw [← this]; exact tower_mono 5 (by have := i.isLt; omega) _ (qβn_mem i.val)

/-- **`L/ℚ` is a finite extension.** -/
theorem tower_finite : ∀ n, FiniteExt Qc (tower n) (Qc_le_tower n)
  | 0 => (deg_self C.isField Qc).1
  | n + 1 => (tower_law C.isField (Qc_le_tower n) (tower_le_succ n) (tower_finite n)
      (adjoin_finite C.isField (tower n) (qβn n) _)).1

/-- **`L/ℚ` is a finite extension.** -/
theorem L_finite : FiniteExt Qc L Qc_le_L := tower_finite 5

/-- **`L` is generated by the roots**: it lies in every subfield containing `ℚ` and `β₀, …, β₄`. -/
theorem L_le {M : Subfield ℂ} (hQ : Qc.le M) (hβ : ∀ i, qβ i ∈ M) : L.le M := by
  have : ∀ n, n ≤ 5 → (tower n).le M := by
    intro n
    induction n with
    | zero => intro _; exact hQ
    | succ n ih =>
      intro hn
      apply adjoin_le _ _ _ _ (ih (by omega))
      have : qβn n = qβ ⟨n, by omega⟩ := by unfold qβn; rw [dite_eq_left (by omega)]
      rw [this]; exact hβ _
  exact this 5 (Nat.le_refl 5)

/-! ## Embeddings of `L` are automorphisms -/

/-- Ring homomorphisms from a subfield containing `ℚ` into the ambient field fix the
rationals. -/
theorem ringHom_fix_ratField' {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω) (hc : CharZero Ω)
    {F : Subfield Ω} (τ : RingHom F Ω) (x : F) (hx : x.1 ∈ ratField hΩ hc) : τ.toFun x = x.1 := by
  obtain ⟨a, b, hb, hab⟩ := hx
  have e : x * Int.cast b = Int.cast a := Subtype.ext (by
    rw [Subfield.coe_mul, Subfield.coe_intCast, Subfield.coe_intCast]; exact hab)
  have e' : τ.toFun x * Int.cast b = Int.cast a := by
    rw [← RingHom.map_intCast τ b, ← τ.map_mul, e, RingHom.map_intCast]
  have hb' : (Int.cast b : Ω) ≠ 0 := fun h => hb (hc b h)
  have : (τ.toFun x + -x.1) * Int.cast b = 0 := by grind
  rcases hΩ.isDomain.2 _ _ this with h | h
  · grind
  · exact absurd h hb'

/-- Ring homomorphisms from a subfield containing `ℚ` into `ℂ` fix the rationals. -/
theorem ringHom_fix_Qc {F : Subfield ℂ} (τ : RingHom F ℂ) (x : F) (hx : x.1 ∈ Qc) :
    τ.toFun x = x.1 :=
  ringHom_fix_ratField' C.isField C.charZero τ x hx

/-- An element `x ∈ L` is a root of `f` over `L` exactly when it is a root in `ℂ`. -/
theorem root_in_L {x : L} (h : eval x.1 (quinticPoly ℂ) = 0) : eval x (quinticPoly L) = 0 := by
  have := RingHom.map_eval L.incl x (quinticPoly L)
  rw [mapPoly_quinticPoly] at this
  apply RingHom.eq_zero_of_isField (L.isField C.isField) C.isField.1 L.incl
  rw [this]; exact h

/-- **An embedding of `L` into `ℂ` maps `L` into itself.** -/
theorem embedding_maps_L (τ : RingHom L ℂ) (x : L) : τ.toFun x ∈ L := by
  -- the elements of `L` sent into `L` form a subfield
  have hFL := L.isField C.isField
  let P : Subfield ℂ :=
    { carrier := fun y => ∃ h : y ∈ L, τ.toFun ⟨y, h⟩ ∈ L
      zero_mem := ⟨L.zero_mem, by
        show τ.toFun 0 ∈ L; rw [τ.map_zero]; exact L.zero_mem⟩
      one_mem := ⟨L.one_mem, by
        show τ.toFun 1 ∈ L; rw [τ.map_one]; exact L.one_mem⟩
      add_mem := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨L.add_mem ha hb, by
        show τ.toFun (⟨_, ha⟩ + ⟨_, hb⟩) ∈ L; rw [τ.map_add]; exact L.add_mem ha' hb'⟩
      neg_mem := fun ⟨ha, ha'⟩ => ⟨L.neg_mem ha, by
        show τ.toFun (-⟨_, ha⟩) ∈ L; rw [τ.map_neg]; exact L.neg_mem ha'⟩
      mul_mem := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨L.mul_mem ha hb, by
        show τ.toFun (⟨_, ha⟩ * ⟨_, hb⟩) ∈ L; rw [τ.map_mul]; exact L.mul_mem ha' hb'⟩
      inv_mem := by
        intro a ⟨ha, ha'⟩ ha0
        obtain ⟨b, hb, hab⟩ := L.inv_mem ha ha0
        refine ⟨b, ⟨hb, ?_⟩, hab⟩
        have h1 : τ.toFun ⟨a, ha⟩ * τ.toFun ⟨b, hb⟩ = 1 := by
          rw [← τ.map_mul]
          have : (⟨a, ha⟩ : L) * ⟨b, hb⟩ = 1 := Subtype.ext hab
          rw [this, τ.map_one]
        have hne : τ.toFun ⟨a, ha⟩ ≠ 0 := fun h => by rw [h, Ring.zero_mul] at h1; exact C.isField.1 h1
        obtain ⟨w, hw, hw1⟩ := L.inv_mem ha' hne
        have : τ.toFun ⟨b, hb⟩ = w := by
          calc τ.toFun ⟨b, hb⟩ = τ.toFun ⟨b, hb⟩ * (τ.toFun ⟨a, ha⟩ * w) := by rw [hw1, Ring.mul_one]
            _ = (τ.toFun ⟨a, ha⟩ * τ.toFun ⟨b, hb⟩) * w := by ac_rfl
            _ = w := by rw [h1, Ring.one_mul]
        rw [this]; exact hw }
  have hQ : Qc.le P := fun y hy => ⟨Qc_le_L y hy, by
    rw [ringHom_fix_Qc τ ⟨y, Qc_le_L y hy⟩ hy]; exact Qc_le_L y hy⟩
  have hβ : ∀ i, qβ i ∈ P := fun i => ⟨qβ_mem i, by
    have hr := RingHom.map_quintic_root τ (root_in_L (x := ⟨qβ i, qβ_mem i⟩) (qβ_spec.2.1 i))
    obtain ⟨j, hj⟩ := qβ_enum _ hr
    rw [← hj]; exact qβ_mem j⟩
  obtain ⟨_, h⟩ := L_le hQ hβ x.1 x.2
  exact h

/-- An embedding `L → ℂ`, viewed as a ring homomorphism `L → L`. -/
def restrictL (τ : RingHom L ℂ) : RingHom L L where
  toFun x := ⟨τ.toFun x, embedding_maps_L τ x⟩
  map_add a b := Subtype.ext (τ.map_add a b)
  map_mul a b := Subtype.ext (τ.map_mul a b)
  map_one := Subtype.ext τ.map_one

/-- **Embeddings are automorphisms.** Every ring homomorphism `L → ℂ` is (the restriction of)
an automorphism of `L` over `ℚ`. -/
noncomputable def autOfEmbedding (τ : RingHom L ℂ) : FieldAut Qc L :=
  autOfRingHom C.isField Qc_le_L L_finite (restrictL τ)
    (fun x hx => Subtype.ext (ringHom_fix_Qc τ x hx))

/-- The automorphism built from `τ` acts as `τ`. -/
theorem autOfEmbedding_apply (τ : RingHom L ℂ) (x : L) :
    ((autOfEmbedding τ).toFun x).1 = τ.toFun x := rfl

/-- **Complex conjugation restricted to `L`**, an automorphism of `L` over `ℚ`. -/
noncomputable def conjAut : FieldAut Qc L := autOfEmbedding (RingHom.comp conjHom L.incl)

/-- `conjAut` acts as complex conjugation. -/
theorem conjAut_apply (x : L) : ((conjAut).toFun x).1 = Foundations.Numbers.C.conj x.1 := rfl

/-! ## Transitivity on the roots -/

/-- **`f` is the minimal polynomial of each root.** Since `x⁵ - 6x + 3` is irreducible over
`ℚ`, any rational polynomial vanishing at one root vanishes at every root. -/
theorem minpoly_roots {z w : ℂ} (hz : eval z (quinticPoly ℂ) = 0) (hw : eval w (quinticPoly ℂ) = 0)
    (q : Polynomial Qc) (hq : aeval Qc z q = 0) : aeval Qc w q = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_minpoly Qc z C.isField (quintic_isAlgebraic Qc hz)
  have hf : aeval Qc z (quinticPoly Qc) = 0 := by rw [aeval_quinticPoly]; exact hz
  obtain ⟨c, hc⟩ := (hm _).1 hf
  have hmz : aeval Qc z m = 0 := (hm m).2 ⟨1, (Ring.mul_one m).symm⟩
  have hirr : Irreducible (quinticPoly Qc) := quinticPoly_irreducible C.isField C.charZero
  rcases hirr.2.2 m c hc with ⟨m', hm'⟩ | ⟨c', hc'⟩
  · exfalso
    have := congrArg (aeval Qc z) hm'
    rw [aeval_mul, hmz, Ring.zero_mul, aeval_one] at this
    exact C.isField.1 this
  · have hmw : aeval Qc w m = 0 := by
      have e : m = quinticPoly Qc * c' := by
        calc m = m * (c * c') := by rw [hc', Ring.mul_one]
          _ = (m * c) * c' := by ac_rfl
          _ = quinticPoly Qc * c' := by rw [← hc]
      rw [e, aeval_mul, aeval_quinticPoly, hw, Ring.zero_mul]
    obtain ⟨d, rfl⟩ := (hm q).1 hq
    rw [aeval_mul, hmw, Ring.zero_mul]

/-- **Transitivity.** For every root `βⱼ` there is an embedding `L → ℂ` sending `β₀` to `βⱼ`. -/
theorem exists_embedding (j : Fin 5) :
    ∃ τ : RingHom L ℂ, τ.toFun ⟨qβ 0, qβ_mem 0⟩ = qβ j := by
  have key : ∀ n (hn : 1 ≤ n), ∃ σ : RingHom (tower n) ℂ,
      σ.toFun ⟨qβ 0, qβ0_mem_tower hn⟩ = qβ j := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases h0 : n = 0
      · subst h0
        have h00 : qβn 0 = qβ 0 := by unfold qβn; rw [dite_eq_left (by decide)]; rfl
        obtain ⟨τ, _, hτγ, _⟩ := extend C.isField (tower 0) (qβn 0) (quintic_isAlgebraic _ (qβn_root 0)) Qc.incl (qβ j)
          (fun q hq => minpoly_roots (qβn_root 0) (qβ_spec.2.1 j) q hq)
        refine ⟨τ, ?_⟩
        have : (⟨qβ 0, qβ0_mem_tower (n := 1) (by omega)⟩ : tower 1) = ⟨qβn 0, qβn_mem 0⟩ :=
          Subtype.ext h00.symm
        rw [this]; exact hτγ
      · obtain ⟨σ, hσ⟩ := ih (by omega)
        obtain ⟨δ, hδ⟩ := exists_root_C C.isField (tower n) (qβn n) (quintic_isAlgebraic _ (qβn_root n)) σ
        obtain ⟨τ, hτF, _, _⟩ := extend C.isField (tower n) (qβn n) (quintic_isAlgebraic _ (qβn_root n)) σ δ hδ
        refine ⟨τ, ?_⟩
        rw [← hσ]
        exact hτF ⟨qβ 0, qβ0_mem_tower (n := n) (by omega)⟩
  exact key 5 (by decide)

/-- **Transitivity, for automorphisms.** For every root `βⱼ` some automorphism of `L` over `ℚ`
sends `β₀` to `βⱼ`. -/
theorem exists_aut_root (j : Fin 5) :
    ∃ σ : FieldAut Qc L, (σ.toFun ⟨qβ 0, qβ_mem 0⟩).1 = qβ j := by
  obtain ⟨τ, hτ⟩ := exists_embedding j
  exact ⟨autOfEmbedding τ, hτ⟩

end Foundations.Algebra
