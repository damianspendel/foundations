import Foundations.Numbers.Arithmetic

/-!
# Composition identities for sums of squares

Diophantus of Alexandria (*Arithmetica* III.19, c. 250 AD) already knew that the product of
two sums of two squares is again a sum of two squares: `65 = 5 · 13 = 1² + 8² = 4² + 7²`.
In modern terms this is the multiplicativity of the norm on the Gaussian integers, and it
was written down as an algebraic identity by Brahmagupta (628) and by Fibonacci (1225):

  `(a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²`.

Euler, in a letter to Goldbach of 4 May 1748, found the analogous identity for **four**
squares — the multiplicativity of the norm on Hamilton's quaternions, a century before
quaternions existed. Both identities are the reason why the question "which numbers are sums
of `k` squares?" reduces, for `k = 2` and `k = 4`, to the question for primes. (For three
squares there is no such identity; this is one reason the three-square theorem is so much
harder: `3 = 1² + 1² + 1²` and `5 = 2² + 1² + 0²` are sums of three squares, but `15 = 3 · 5` is
not.)

This file proves both identities over `ℤ` (by `grind`'s ring normaliser), packages them as
closure properties of the predicates `IsSum2` and `IsSum4`, and bridges between integer and
natural-number representations (`a² = |a|²`).
-/

namespace Foundations.Langlands.Squares

/-! ## The identities -/

/-- **Brahmagupta–Fibonacci identity.** `(a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²`. -/
theorem brahmagupta_identity (a b c d : Int) :
    (a * a + b * b) * (c * c + d * d) =
      (a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c) := by
  grind

/-- **Euler's four-square identity** (1748). The product of two sums of four squares is a sum of
four squares, with the explicit (quaternionic) bilinear expressions below. -/
theorem euler_four_square_identity (a1 a2 a3 a4 b1 b2 b3 b4 : Int) :
    (a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4) * (b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4) =
      (a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4) * (a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4)
      + (a1 * b2 - a2 * b1 + a3 * b4 - a4 * b3) * (a1 * b2 - a2 * b1 + a3 * b4 - a4 * b3)
      + (a1 * b3 - a3 * b1 + a4 * b2 - a2 * b4) * (a1 * b3 - a3 * b1 + a4 * b2 - a2 * b4)
      + (a1 * b4 - a4 * b1 + a2 * b3 - a3 * b2) * (a1 * b4 - a4 * b1 + a2 * b3 - a3 * b2) := by
  grind

/-! ## Squares are non-negative -/

/-- A square of an integer is non-negative. -/
theorem sq_nonneg' (t : Int) : 0 ≤ t * t := by
  rcases Int.le_total 0 t with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rw [Int.neg_mul_neg] at this
    exact this

/-- An integer square is zero only for zero. -/
theorem eq_zero_of_sq_eq_zero {t : Int} (h : t * t = 0) : t = 0 := by
  rcases Int.mul_eq_zero.1 h with h | h <;> exact h

/-- For `0 ≤ s ≤ M`, `s² ≤ M²`. -/
theorem sq_le_sq_of_nonneg {s M : Int} (h0 : 0 ≤ s) (h : s ≤ M) : s * s ≤ M * M := by
  have h1 := Int.mul_le_mul_of_nonneg_left h h0
  have h2 := Int.mul_le_mul_of_nonneg_right h (by omega : (0 : Int) ≤ M)
  omega

/-- For `0 ≤ s < M`, `s² < M²`. -/
theorem sq_lt_sq_of_nonneg {s M : Int} (h0 : 0 ≤ s) (h : s < M) : s * s < M * M := by
  have h1 := Int.mul_le_mul_of_nonneg_left (Int.le_of_lt h) h0
  have h2 := Int.mul_lt_mul_of_pos_right h (by omega : (0 : Int) < M)
  omega

/-- If `|t| ≤ M` then `t² ≤ M²`. -/
theorem sq_le_sq_of_abs_le {t M : Int} (h1 : -M ≤ t) (h2 : t ≤ M) : t * t ≤ M * M := by
  rcases Int.le_total 0 t with h | h
  · exact sq_le_sq_of_nonneg h h2
  · have := sq_le_sq_of_nonneg (s := -t) (M := M) (by omega) (by omega)
    rwa [Int.neg_mul_neg] at this

/-- If `|t| < M` then `t² < M²`. -/
theorem sq_lt_sq_of_abs_lt {t M : Int} (h1 : -M < t) (h2 : t < M) : t * t < M * M := by
  rcases Int.le_total 0 t with h | h
  · exact sq_lt_sq_of_nonneg h h2
  · have := sq_lt_sq_of_nonneg (s := -t) (M := M) (by omega) (by omega)
    rwa [Int.neg_mul_neg] at this

/-! ## The predicates -/

/-- An integer is a **sum of two squares** of integers. -/
def IsSum2 (n : Int) : Prop := ∃ a b : Int, a * a + b * b = n

/-- An integer is a **sum of four squares** of integers. -/
def IsSum4 (n : Int) : Prop := ∃ a b c d : Int, a * a + b * b + c * c + d * d = n

/-- Sums of two squares are closed under multiplication (Brahmagupta). -/
theorem IsSum2.mul {m n : Int} (hm : IsSum2 m) (hn : IsSum2 n) : IsSum2 (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨_, _, (brahmagupta_identity a b c d).symm⟩

/-- Sums of four squares are closed under multiplication (Euler). -/
theorem IsSum4.mul {m n : Int} (hm : IsSum4 m) (hn : IsSum4 n) : IsSum4 (m * n) := by
  obtain ⟨a1, a2, a3, a4, rfl⟩ := hm
  obtain ⟨b1, b2, b3, b4, rfl⟩ := hn
  exact ⟨_, _, _, _, (euler_four_square_identity a1 a2 a3 a4 b1 b2 b3 b4).symm⟩

/-- `0` is a sum of four squares. -/
theorem isSum4_zero : IsSum4 0 := ⟨0, 0, 0, 0, rfl⟩

/-- `1` is a sum of four squares. -/
theorem isSum4_one : IsSum4 1 := ⟨1, 0, 0, 0, rfl⟩

/-- A sum of two squares is a sum of four squares. -/
theorem IsSum2.isSum4 {n : Int} (h : IsSum2 n) : IsSum4 n := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨a, b, 0, 0, by grind⟩

/-! ## From integers to natural numbers -/

/-- A natural number that is a sum of two integer squares is a sum of two natural squares. -/
theorem nat_of_isSum2 {n : Nat} (h : IsSum2 (n : Int)) : ∃ a b : Nat, a * a + b * b = n := by
  obtain ⟨a, b, h⟩ := h
  refine ⟨a.natAbs, b.natAbs, ?_⟩
  have ha := @Int.natAbs_mul_self a
  have hb := @Int.natAbs_mul_self b
  omega

/-- A natural number that is a sum of four integer squares is a sum of four natural squares. -/
theorem nat_of_isSum4 {n : Nat} (h : IsSum4 (n : Int)) :
    ∃ a b c d : Nat, a * a + b * b + c * c + d * d = n := by
  obtain ⟨a, b, c, d, h⟩ := h
  refine ⟨a.natAbs, b.natAbs, c.natAbs, d.natAbs, ?_⟩
  have ha := @Int.natAbs_mul_self a
  have hb := @Int.natAbs_mul_self b
  have hc := @Int.natAbs_mul_self c
  have hd := @Int.natAbs_mul_self d
  omega

/-- A sum of two natural squares is a sum of two integer squares. -/
theorem isSum2_of_nat {n a b : Nat} (h : a * a + b * b = n) : IsSum2 (n : Int) :=
  ⟨a, b, by rw [← h]; push_cast; rfl⟩

/-- **Diophantus' example.** `65 = 1² + 8² = 4² + 7²`, and Brahmagupta's identity produces
both representations from `5 = 1² + 2²` and `13 = 2² + 3²`. -/
example : (1 * 2 - 2 * 3 : Int) * (1 * 2 - 2 * 3) + (1 * 3 + 2 * 2) * (1 * 3 + 2 * 2) = 65 ∧
    (1 * 2 + 2 * 3 : Int) * (1 * 2 + 2 * 3) + (1 * 3 - 2 * 2) * (1 * 3 - 2 * 2) = 65 := by
  decide

end Foundations.Langlands.Squares
