import Foundations.Langlands.Padic.HilbertBilinear

/-!
# Primitive solutions of `z² = a x² + b y²`

A non-trivial solution over ℚₚ of `z² = a x² + b y²` with `a, b ∈ ℤₚ` can be rescaled into a
**primitive** one: `x, y, z ∈ ℤₚ`, not all divisible by `p` (`Qp.exists_primitive`). This is
the usual first step of every local computation of the Hilbert symbol, and it is used at `p = 2`
in `Hilbert2`.

* *Clearing denominators*: every `x ∈ ℚₚ` is `X / pᵏ` with `X ∈ ℤₚ`; multiplying the three
  coordinates by a common `pᴷ` gives a solution in ℤₚ.
* *Descent*: if `p` divides `x`, `y` and `z`, then `(x/p, y/p, z/p)` is again a solution
  (cancel `p²` in the domain ℤₚ), and the sum of the valuations of the coordinates drops. By
  induction on that sum we reach a primitive solution.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

namespace Zp

variable {p : Nat}

/-- `1` is a unit of ℤₚ. -/
theorem isPUnit_one (hp : Prime p) : IsPUnit (1 : Zp p) := (isUnit_iff hp 1).1 ⟨1, by grind⟩

/-- An element `≡ 0 (mod p)` is `p` times an element of ℤₚ. -/
theorem exists_eq_p_mul (hp : Prime p) {X : Zp p} (h : ModPow 1 X 0) : ∃ X', X = (p : Zp p) * X' := by
  by_cases hX : X = 0
  · exact ⟨0, by rw [hX]; grind⟩
  obtain ⟨v, w, hw, rfl⟩ := eq_pow_mul_unit hp hX
  have h1 := (modPow_zero_iff hp hX).1 h
  rw [val_pow_mul hp v hw] at h1
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  exact ⟨(p : Zp p) ^ v' * w, by rw [Semiring.pow_succ]; grind⟩

/-- `v(p X) = v(X) + 1` for `X ≠ 0`. -/
theorem val_p_mul (hp : Prime p) {X : Zp p} (hX : X ≠ 0) : val hp ((p : Zp p) * X) = val hp X + 1 := by
  obtain ⟨v, w, hw, rfl⟩ := eq_pow_mul_unit hp hX
  rw [val_pow_mul hp v hw, show (p : Zp p) * ((p : Zp p) ^ v * w) = (p : Zp p) ^ (v + 1) * w by
    rw [Semiring.pow_succ]; grind, val_pow_mul hp _ hw]

/-- Dividing by `p` does not increase the valuation, and decreases it for non-zero elements
(with the convention `v(0) = 0`). -/
theorem val_lt_of_eq_p_mul (hp : Prime p) {X X' : Zp p} (h : X = (p : Zp p) * X') :
    val hp X' ≤ val hp X ∧ (X ≠ 0 → val hp X' < val hp X) := by
  by_cases hX' : X' = 0
  · have h0 : val hp X' = 0 := by unfold val; simp [hX']
    rw [h0]
    exact ⟨Nat.zero_le _, fun hX => absurd (by rw [h, hX']; grind) hX⟩
  · rw [h, val_p_mul hp hX']; omega

end Zp

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- A triple in ℤₚ is **primitive** if `p` does not divide all three coordinates. -/
def Primitive (X Y Z : Zp p) : Prop :=
  ¬ (Zp.ModPow 1 X 0 ∧ Zp.ModPow 1 Y 0 ∧ Zp.ModPow 1 Z 0)

/-- **Descent in ℤₚ.** A non-trivial solution in ℤₚ of `Z² = a X² + b Y²` yields a primitive
one. -/
theorem exists_primitive_zp {a b : Zp p} :
    ∀ n : Nat, ∀ X Y Z : Zp p, Zp.val hP.prime X + Zp.val hP.prime Y + Zp.val hP.prime Z ≤ n →
      (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) → Z * Z = a * (X * X) + b * (Y * Y) →
      ∃ X Y Z : Zp p, Primitive X Y Z ∧ Z * Z = a * (X * X) + b * (Y * Y) := by
  have hp := hP.prime
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro X Y Z hn hne h
    by_cases hprim : Primitive X Y Z
    · exact ⟨X, Y, Z, hprim, h⟩
    unfold Primitive at hprim
    have hall := Classical.not_not.1 hprim
    obtain ⟨X', rfl⟩ := Zp.exists_eq_p_mul hp hall.1
    obtain ⟨Y', rfl⟩ := Zp.exists_eq_p_mul hp hall.2.1
    obtain ⟨Z', rfl⟩ := Zp.exists_eq_p_mul hp hall.2.2
    have hX := Zp.val_lt_of_eq_p_mul hp (X := (p : Zp p) * X') rfl
    have hY := Zp.val_lt_of_eq_p_mul hp (X := (p : Zp p) * Y') rfl
    have hZ := Zp.val_lt_of_eq_p_mul hp (X := (p : Zp p) * Z') rfl
    have hlt : Zp.val hp X' + Zp.val hp Y' + Zp.val hp Z' <
        Zp.val hp ((p : Zp p) * X') + Zp.val hp ((p : Zp p) * Y') +
          Zp.val hp ((p : Zp p) * Z') := by
      rcases hne with h' | h' | h'
      · have := hX.2 h'; omega
      · have := hY.2 h'; omega
      · have := hZ.2 h'; omega
  · omega
  · have hp0 := zp_p_ne_zero (p := p)
    have h0 : (p : Zp p) * ((p : Zp p) * (Z' * Z' - (a * (X' * X') + b * (Y' * Y')))) = 0 := by
      have := h; grind
    have h1 : Z' * Z' = a * (X' * X') + b * (Y' * Y') := by
      rcases Zp.eq_zero_or_eq_zero hp h0 with h2 | h2
      · exact absurd h2 hp0
      · rcases Zp.eq_zero_or_eq_zero hp h2 with h3 | h3
        · exact absurd h3 hp0
        · grind
    have hne' : X' ≠ 0 ∨ Y' ≠ 0 ∨ Z' ≠ 0 := by
      rcases hne with h' | h' | h'
      · exact Or.inl fun h0 => h' (by rw [h0]; grind)
      · exact Or.inr (Or.inl fun h0 => h' (by rw [h0]; grind))
      · exact Or.inr (Or.inr fun h0 => h' (by rw [h0]; grind))
    exact ih X' Y' Z' (by omega) hne' h1

/-- Every element of ℚₚ times a suitable power `pᵏ` lies in ℤₚ. -/
theorem exists_mul_pow_eq_ofZp (x : Qp p) : ∃ k : Nat, ∃ X : Zp p, x * ofZp ((p : Zp p) ^ k) = ofZp X := by
  induction x using ind with | h X k => ?_
  have hK : ofZp ((p : Zp p) ^ k) ≠ 0 := fun h => pow_ne_zero (p := p) k (mk_eq_zero.1 h)
  have hKi := Field.mul_inv_cancel hK
  refine ⟨k, X, ?_⟩
  rw [mk_eq_div]
  show ofZp X * (ofZp ((p : Zp p) ^ k))⁻¹ * _ = _
  rw [show ofZp X * (ofZp ((p : Zp p) ^ k))⁻¹ * ofZp ((p : Zp p) ^ k) =
    ofZp X * (ofZp ((p : Zp p) ^ k) * (ofZp ((p : Zp p) ^ k))⁻¹) by grind, hKi]
  grind

/-- Raising the power: `x pᵏ = X` gives `x p^(k+j) = X pʲ`. -/
theorem mul_pow_add {x : Qp p} {k : Nat} {X : Zp p} (h : x * ofZp ((p : Zp p) ^ k) = ofZp X)
    (j : Nat) : x * ofZp ((p : Zp p) ^ (k + j)) = ofZp (X * (p : Zp p) ^ j) := by
  rw [Semiring.pow_add, ofZp_mul, ofZp_mul, ← h]; grind

/-- **Primitive solutions.** If `z² = a x² + b y²` (`a, b ∈ ℤₚ`) has a non-trivial solution
in ℚₚ, it has a primitive solution in ℤₚ: `X, Y, Z ∈ ℤₚ`, not all divisible by `p`. -/
theorem exists_primitive {a b : Zp p} (h : HilbertSolvable (ofZp a) (ofZp b)) :
    ∃ X Y Z : Zp p, Primitive X Y Z ∧ Z * Z = a * (X * X) + b * (Y * Y) := by
  obtain ⟨x, y, z, hne, h⟩ := h
  obtain ⟨kx, X, hX⟩ := exists_mul_pow_eq_ofZp x
  obtain ⟨ky, Y, hY⟩ := exists_mul_pow_eq_ofZp y
  obtain ⟨kz, Z, hZ⟩ := exists_mul_pow_eq_ofZp z
  let K := kx + ky + kz
  have hX' := mul_pow_add hX (ky + kz)
  have hY' := mul_pow_add hY (kx + kz)
  have hZ' := mul_pow_add hZ (kx + ky)
  rw [show kx + (ky + kz) = K by omega] at hX'
  rw [show ky + (kx + kz) = K by omega] at hY'
  rw [show kz + (kx + ky) = K by omega] at hZ'
  have hK : ofZp ((p : Zp p) ^ K) ≠ 0 := fun h => pow_ne_zero (p := p) K (mk_eq_zero.1 h)
  have heq : Z * (p : Zp p) ^ (kx + ky) * (Z * (p : Zp p) ^ (kx + ky)) =
      a * (X * (p : Zp p) ^ (ky + kz) * (X * (p : Zp p) ^ (ky + kz))) +
        b * (Y * (p : Zp p) ^ (kx + kz) * (Y * (p : Zp p) ^ (kx + kz))) := by
    apply ofZp_injective
    simp only [ofZp_add, ofZp_mul] at hX' hY' hZ' ⊢
    rw [← hX', ← hY', ← hZ']
    generalize ofZp ((p : Zp p) ^ K) = k at *
    rw [show z * k * (z * k) = (z * z) * (k * k) by grind, h]; grind
  have nz : ∀ {w : Qp p} {W : Zp p}, w ≠ 0 → w * ofZp ((p : Zp p) ^ K) = ofZp W → W ≠ 0 :=
    fun hw hW h0 => mul_ne_zero' hw hK (by rw [hW, h0]; rfl)
  refine exists_primitive_zp _ _ _ _ (Nat.le_refl _) ?_ heq
  rcases hne with h' | h' | h'
  · exact Or.inl (nz h' hX')
  · exact Or.inr (Or.inl (nz h' hY'))
  · exact Or.inr (Or.inr (nz h' hZ'))

end Qp

end Foundations.Langlands.Padic
