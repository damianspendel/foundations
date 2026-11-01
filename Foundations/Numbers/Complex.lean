import Foundations.Numbers.RealOrder

/-!
# The complex numbers

The last extension in the classical sequence is of a different kind. ℕ → ℤ → ℚ → ℝ each
repaired a defect while keeping the order; the passage to ℂ adds a solution of `x² = −1`, which
no ordered field can contain (a square is never negative). Following Hamilton (1835), who wanted
to dispel the mystery of "imaginary" numbers, a complex number is simply a **pair of reals**
`(a, b)`, written `a + b·i`, with

  `(a, b) + (c, d) = (a + c, b + d)`,  `(a, b) · (c, d) = (ac − bd, ad + bc)`.

Nothing imaginary is involved: `i` is the pair `(0, 1)`, and `i · i = (−1, 0) = −1` is a
calculation. We prove that `C` is a **field** (registered with Lean's automation), that
`i² = −1`, the basic laws of **conjugation** `a + bi ↦ a − bi`, that `z · z̄ = |z|²` with
`|z|² = a² + b²`, the multiplicativity of `|z|²`, and finally that **ℂ cannot be ordered**: no
linear order compatible with `+` and `×` exists on it.
-/

namespace Foundations.Numbers

open Lean.Grind

/-- **The complex numbers**: pairs `(re, im)` of real numbers, standing for `re + im·i`. -/
structure C where
  /-- The real part. -/
  re : R
  /-- The imaginary part. -/
  im : R

namespace C

/-- Complex numbers with the same real and imaginary parts are equal. -/
theorem ext {z w : C} (h1 : z.re = w.re) (h2 : z.im = w.im) : z = w := by
  cases z; cases w; simp only at h1 h2; rw [h1, h2]

/-- Addition, componentwise. -/
instance : Add C := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
/-- Negation, componentwise. -/
instance : Neg C := ⟨fun z => ⟨-z.re, -z.im⟩⟩
/-- Subtraction. -/
instance : Sub C := ⟨fun z w => z + -w⟩
/-- Multiplication: `(a + bi)(c + di) = (ac − bd) + (ad + bc)i`. -/
instance : Mul C := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
/-- Numerals are real. -/
instance (n : Nat) : OfNat C n := ⟨⟨OfNat.ofNat n, 0⟩⟩
/-- The canonical map from `Nat`. -/
instance : NatCast C := ⟨fun n => ⟨n, 0⟩⟩
/-- The canonical map from `Int`. -/
instance : IntCast C := ⟨fun i => ⟨i, 0⟩⟩

/-- The imaginary unit `i = (0, 1)`. -/
def I : C := ⟨0, 1⟩

/-- Complex conjugation: `a + bi ↦ a − bi`. -/
def conj (z : C) : C := ⟨z.re, -z.im⟩

/-- The squared modulus `|z|² = a² + b²`. -/
def normSq (z : C) : R := z.re * z.re + z.im * z.im

/-- The inverse: `(a + bi)⁻¹ = (a − bi)/(a² + b²)` (and `0⁻¹ = 0`). -/
noncomputable instance : Inv C := ⟨fun z => ⟨z.re / normSq z, -z.im / normSq z⟩⟩
/-- Division. -/
noncomputable instance : Div C := ⟨fun z w => z * w⁻¹⟩

/-- Real part of a sum. -/
@[simp] theorem add_re (z w : C) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : C) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : C) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : C) : (-z).im = -z.im := rfl
@[simp] theorem mul_re (z w : C) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : C) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem inv_re (z : C) : z⁻¹.re = z.re / normSq z := rfl
@[simp] theorem inv_im (z : C) : z⁻¹.im = -z.im / normSq z := rfl
@[simp] theorem zero_re : (0 : C).re = 0 := rfl
@[simp] theorem zero_im : (0 : C).im = 0 := rfl
@[simp] theorem one_re : (1 : C).re = 1 := rfl
@[simp] theorem one_im : (1 : C).im = 0 := rfl
@[simp] theorem conj_re (z : C) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : C) : (conj z).im = -z.im := rfl
@[simp] theorem I_re : I.re = 0 := rfl
@[simp] theorem I_im : I.im = 1 := rfl

/-- Prove an identity of complex numbers by comparing real and imaginary parts. -/
macro "cpx" : tactic => `(tactic| (apply ext <;> simp only [add_re, add_im, neg_re, neg_im,
  mul_re, mul_im, zero_re, zero_im, one_re, one_im, conj_re, conj_im, I_re, I_im, normSq] <;>
  grind))

/-- Addition is associative. -/
theorem add_assoc (x y z : C) : x + y + z = x + (y + z) := by cpx
/-- Addition is commutative. -/
theorem add_comm (x y : C) : x + y = y + x := by cpx
/-- Zero is the additive identity. -/
theorem add_zero (x : C) : x + 0 = x := by cpx
/-- `-x` is an additive inverse of `x`. -/
theorem neg_add_cancel (x : C) : -x + x = 0 := by cpx
/-- Multiplication is associative. -/
theorem mul_assoc (x y z : C) : x * y * z = x * (y * z) := by cpx
/-- Multiplication is commutative. -/
theorem mul_comm (x y : C) : x * y = y * x := by cpx
/-- One is the multiplicative identity. -/
theorem mul_one (x : C) : x * 1 = x := by cpx
/-- One is a left identity. -/
theorem one_mul (x : C) : 1 * x = x := by cpx
/-- Zero times anything is zero. -/
theorem zero_mul (x : C) : 0 * x = 0 := by cpx
/-- Anything times zero is zero. -/
theorem mul_zero (x : C) : x * 0 = 0 := by cpx
/-- Multiplication distributes over addition (left). -/
theorem left_distrib (x y z : C) : x * (y + z) = x * y + x * z := by cpx
/-- Multiplication distributes over addition (right). -/
theorem right_distrib (x y z : C) : (x + y) * z = x * z + y * z := by cpx
/-- `(-x) · y = -(x · y)`. -/
theorem neg_mul (x y : C) : -x * y = -(x * y) := by cpx

/-- Zero is different from one. -/
theorem zero_ne_one : (0 : C) ≠ 1 := fun h => by
  have := congrArg C.re h; simp only [zero_re, one_re] at this; grind

/-- A real square is non-negative. -/
theorem mul_self_nonneg (a : R) : 0 ≤ a * a := by
  rcases (by grind : 0 ≤ a ∨ a ≤ 0) with h | h
  · exact OrderedRing.mul_nonneg h h
  · exact OrderedRing.mul_nonneg_of_nonpos_of_nonpos h h

/-- `|z|² = 0` only for `z = 0`. -/
theorem normSq_eq_zero {z : C} (h : normSq z = 0) : z = 0 := by
  have h1 := mul_self_nonneg z.re
  have h2 := mul_self_nonneg z.im
  unfold normSq at h
  have e1 : z.re * z.re = 0 := by grind
  have e2 : z.im * z.im = 0 := by grind
  apply ext
  · show z.re = 0; grind
  · show z.im = 0; grind

/-- **Inverses in ℂ.** Every non-zero complex number has an inverse. -/
theorem mul_inv_cancel {z : C} (hz : z ≠ 0) : z * z⁻¹ = 1 := by
  have hn : normSq z ≠ 0 := fun h => hz (normSq_eq_zero h)
  unfold normSq at hn
  apply ext
  · simp only [mul_re, inv_re, inv_im, one_re, normSq]; grind
  · simp only [mul_im, inv_re, inv_im, one_im, normSq]; grind

/-- The junk-value convention `0⁻¹ = 0`. -/
theorem inv_zero : (0 : C)⁻¹ = 0 := by
  apply ext <;> simp only [inv_re, inv_im, zero_re, zero_im, normSq] <;> grind

/-- Inversion is an involution. -/
theorem inv_inv (z : C) : z⁻¹⁻¹ = z := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, inv_zero]
  · have h1 := mul_inv_cancel hz
    have hz' : z⁻¹ ≠ 0 := by intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
    have h2 := mul_inv_cancel hz'
    calc z⁻¹⁻¹ = (z * z⁻¹) * z⁻¹⁻¹ := by rw [h1, one_mul]
      _ = z * (z⁻¹ * z⁻¹⁻¹) := mul_assoc _ _ _
      _ = z := by rw [h2, mul_one]

/-- The inverse of one is one. -/
theorem inv_one : (1 : C)⁻¹ = 1 := by
  have h := mul_inv_cancel (Ne.symm zero_ne_one); rw [one_mul] at h; exact h

/-- Natural-number powers. -/
def npow (z : C) : Nat → C
  | 0 => 1
  | n + 1 => npow z n * z

/-- Powers. -/
instance : HPow C Nat C := ⟨npow⟩

/-- Integer powers. -/
noncomputable def zpow (z : C) : Int → C
  | .ofNat n => z ^ n
  | .negSucc n => (z ^ (n + 1))⁻¹

/-- Powers. -/
noncomputable instance : HPow C Int C := ⟨zpow⟩

/-- **ℂ is a field.** Registered with Lean's automation as a `Lean.Grind.Field`. -/
noncomputable instance instField : Field C where
  nsmul := ⟨fun n z => (n : C) * z⟩
  zsmul := ⟨fun i z => (i : C) * z⟩
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    apply ext
    · exact Semiring.ofNat_succ (α := R) n
    · show (0 : R) = 0 + 0; grind
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i z := by
    apply ext
    · show ((-i : Int) : R) * z.re - 0 * z.im = -(((i : Int) : R) * z.re - 0 * z.im)
      rw [Ring.intCast_neg]; grind
    · show ((-i : Int) : R) * z.im + 0 * z.re = -(((i : Int) : R) * z.im + 0 * z.re)
      rw [Ring.intCast_neg]; grind
  intCast_neg i := by
    apply ext
    · exact Ring.intCast_neg (α := R) i
    · show (0 : R) = -0; grind
  intCast_ofNat n := by
    apply ext
    · exact Ring.intCast_ofNat (α := R) n
    · rfl
  mul_comm := mul_comm
  div_eq_mul_inv _ _ := rfl
  zero_ne_one := zero_ne_one
  inv_zero := inv_zero
  mul_inv_cancel := mul_inv_cancel
  zpow_zero _ := rfl
  zpow_succ _ _ := rfl
  zpow_neg a n := by
    cases n with
    | ofNat n =>
      cases n with
      | zero => show (1 : C) = 1⁻¹; rw [inv_one]
      | succ n => rfl
    | negSucc n => show a ^ (n + 1) = ((a ^ (n + 1))⁻¹)⁻¹; rw [inv_inv]

/-- **`i² = −1`.** -/
theorem I_sq : I * I = -1 := by cpx

/-- Conjugation is an involution. -/
theorem conj_conj (z : C) : conj (conj z) = z := by cpx

/-- Conjugation preserves addition. -/
theorem conj_add (z w : C) : conj (z + w) = conj z + conj w := by cpx

/-- Conjugation preserves multiplication. -/
theorem conj_mul (z w : C) : conj (z * w) = conj z * conj w := by cpx

/-- **`z · z̄ = |z|²`.** The product of a complex number with its conjugate is the real number
`a² + b²`. -/
theorem mul_conj (z : C) : z * conj z = ⟨normSq z, 0⟩ := by cpx

/-- `|z w|² = |z|² |w|²` (Brahmagupta–Fibonacci identity). -/
theorem normSq_mul (z w : C) : normSq (z * w) = normSq z * normSq w := by
  simp only [normSq, mul_re, mul_im]; grind

/-- **ℂ is not orderable.** There is no total relation `≤` on `C` that is compatible with
addition, makes products of non-negatives non-negative, and has `0 < 1`. (In any such order
`i² = −1` would be a non-negative square.) -/
theorem not_orderable :
    ¬ ∃ le : C → C → Prop, (∀ a b, le a b ∨ le b a) ∧ (∀ a b c, le a b → le (a + c) (b + c)) ∧
      (∀ a b, le 0 a → le 0 b → le 0 (a * b)) ∧ ¬ le 1 0 := by
  rintro ⟨le, htot, hadd, hmul, h10⟩
  have hneg : ¬ le 0 (-1) := fun h => by
    have := hadd 0 (-1) 1 h
    rw [show (0 : C) + 1 = 1 by grind, show (-1 : C) + 1 = 0 by grind] at this
    exact h10 this
  rcases htot 0 I with h | h
  · have := hmul I I h h; rw [I_sq] at this; exact hneg this
  · have h' := hadd I 0 (-I) h
    rw [show I + -I = 0 by grind, show (0 : C) + -I = -I by grind] at h'
    have := hmul (-I) (-I) h' h'
    rw [show -I * -I = I * I by grind, I_sq] at this
    exact hneg this

end C

end Foundations.Numbers
