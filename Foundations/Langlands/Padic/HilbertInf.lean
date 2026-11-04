import Foundations.Langlands.Padic.HilbertBilinear
import Foundations.Numbers.ComplexModulus

/-!
# The Hilbert symbol at the infinite place

The real numbers are the completion of ℚ at the place `∞`, and the Hilbert symbol makes sense
there with the same definition: `(a, b)_∞ = 1` if `z² = a x² + b y²` has a non-trivial real
solution, `−1` otherwise. Over ℝ the answer depends only on signs: **`(a, b)_∞ = −1` iff
`a < 0` and `b < 0`** (`hilbertInf_eq_neg_one_iff`). If `a ≥ 0` then `(1, 0, √a)` is a point;
if `a, b < 0` then `a x² + b y² ≤ 0 ≤ z²` forces `x = y = z = 0`.

`hilbertInfQ a b` is the symbol of two rationals viewed in ℝ; it is used in the product formula
(`HilbertProduct`).
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- The conic `z² = a x² + b y²` has a **non-trivial real point**. -/
def HilbertSolvableR (a b : R) : Prop :=
  ∃ x y z : R, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ z * z = a * (x * x) + b * (y * y)

/-- The **Hilbert symbol at `∞`**: `1` if `z² = a x² + b y²` has a non-trivial real solution,
`−1` otherwise. -/
noncomputable def hilbertInf (a b : R) : Int := by
  classical exact if HilbertSolvableR a b then 1 else -1

/-- Over ℝ, the conic has a non-trivial point unless both coefficients are negative. -/
theorem hilbertSolvableR_iff (a b : R) : HilbertSolvableR a b ↔ ¬ (a < 0 ∧ b < 0) := by
  have h10 : (1 : R) ≠ 0 := fun h => R.zero_ne_one h.symm
  constructor
  · rintro ⟨x, y, z, hne, h⟩ ⟨ha, hb⟩
    have hx := C.mul_self_nonneg x
    have hy := C.mul_self_nonneg y
    have hz := C.mul_self_nonneg z
    have h1 := OrderedRing.mul_nonpos_of_nonpos_of_nonneg (Std.le_of_lt ha) hx
    have h2 := OrderedRing.mul_nonpos_of_nonpos_of_nonneg (Std.le_of_lt hb) hy
    have e1 : a * (x * x) = 0 := by grind
    have e2 : b * (y * y) = 0 := by grind
    have e3 : z * z = 0 := by grind
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha; exact R.lt_irrefl 0 ha
    have hb0 : b ≠ 0 := fun h => by rw [h] at hb; exact R.lt_irrefl 0 hb
    have sq0 : ∀ t : R, t * t = 0 → t = 0 := fun t ht => by
      rcases Field.of_mul_eq_zero ht with h | h <;> exact h
    have hx0 : x = 0 := by
      rcases Field.of_mul_eq_zero e1 with h | h
      · exact absurd h ha0
      · exact sq0 x h
    have hy0 : y = 0 := by
      rcases Field.of_mul_eq_zero e2 with h | h
      · exact absurd h hb0
      · exact sq0 y h
    rcases hne with h | h | h
    · exact h hx0
    · exact h hy0
    · exact h (sq0 z e3)
  · intro h
    by_cases ha : a < 0
    · have hb : 0 ≤ b := by
        rcases R.lt_trichotomy b 0 with h' | h' | h'
        · exact absurd ⟨ha, h'⟩ h
        · rw [h']; exact Std.le_refl _
        · exact Std.le_of_lt h'
      obtain ⟨hs, hs2⟩ := R.sqrt_spec hb
      exact ⟨0, 1, R.sqrt b, Or.inr (Or.inl h10), by rw [hs2]; grind⟩
    · have ha' : 0 ≤ a := by
        rcases R.lt_trichotomy a 0 with h' | h' | h'
        · exact absurd h' ha
        · rw [h']; exact Std.le_refl _
        · exact Std.le_of_lt h'
      obtain ⟨hs, hs2⟩ := R.sqrt_spec ha'
      exact ⟨1, 0, R.sqrt a, Or.inl h10, by rw [hs2]; grind⟩

/-- **The Hilbert symbol at `∞`.** `(a, b)_∞ = −1` iff `a < 0` and `b < 0`. -/
theorem hilbertInf_eq_neg_one_iff (a b : R) : hilbertInf a b = -1 ↔ a < 0 ∧ b < 0 := by
  unfold hilbertInf
  by_cases h : HilbertSolvableR a b
  · simp only [h, ite_true]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' ((hilbertSolvableR_iff a b).1 h)⟩
  · simp only [h, ite_false, true_iff]
    exact Classical.byContradiction fun h' => h ((hilbertSolvableR_iff a b).2 h')

/-- `(a, b)_∞ = 1` iff `a ≥ 0` or `b ≥ 0`, i.e. not both negative. -/
theorem hilbertInf_eq_one_iff (a b : R) : hilbertInf a b = 1 ↔ ¬ (a < 0 ∧ b < 0) := by
  unfold hilbertInf
  by_cases h : HilbertSolvableR a b
  · simp only [h, ite_true, true_iff]; exact (hilbertSolvableR_iff a b).1 h
  · simp only [h, ite_false]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd ((hilbertSolvableR_iff a b).2 h') h⟩

/-- The Hilbert symbol at `∞` of two rationals. -/
noncomputable def hilbertInfQ (a b : Q) : Int := hilbertInf (R.ofQ a) (R.ofQ b)

/-- `(a, b)_∞ = 1` for a positive rational `a`. -/
theorem hilbertInfQ_of_pos {a : Q} (ha : 0 < a) (b : Q) : hilbertInfQ a b = 1 :=
  (hilbertInf_eq_one_iff _ _).2 fun ⟨h, _⟩ => by
    have := R.ofQ_lt.2 ha
    exact R.lt_asymm h this

end Foundations.Langlands.Padic
