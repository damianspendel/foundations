import Foundations.Algebra.UFD

/-!
# The Gaussian integers

In his second memoir on biquadratic residues (1832) Gauss enlarged the integers to the
numbers `a + bi` with `a, b ∈ ℤ` and `i² = -1`, and showed that arithmetic there is as
well-behaved as in `ℤ`: there is division with small remainder, hence a Euclidean algorithm,
hence unique factorisation. It was the first time a "number system" had been invented to
illuminate questions about the ordinary integers — here, which primes are sums of two
squares, since `a² + b² = (a + bi)(a - bi)` — and it opened the road to algebraic number
theory.

The key quantity is the **norm** `N(a + bi) = a² + b²`, which is multiplicative. To divide
`α` by `β ≠ 0`, compute the exact quotient `α β̄ / N(β)` and round each coordinate to the
nearest integer; the rounding errors are at most `1/2`, so the remainder `ρ` satisfies
`N(ρ) ≤ N(β)/2 < N(β)`. Thus **`ℤ[i]` is a Euclidean domain**, and by the previous files a
PID with unique factorisation.
-/

namespace Foundations.Algebra

open Ring

/-- **Gaussian integer** `re + im·i`. -/
structure GaussInt where
  /-- Real part. -/
  re : Int
  /-- Imaginary part. -/
  im : Int

namespace GaussInt

/-- Gaussian integers are equal when their parts are. -/
theorem ext {z w : GaussInt} (h1 : z.re = w.re) (h2 : z.im = w.im) : z = w := by
  cases z; cases w; simp only at h1 h2; subst h1; subst h2; rfl

/-- Addition of Gaussian integers. -/
instance : Add GaussInt := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

/-- Multiplication: `(a + bi)(c + di) = (ac - bd) + (ad + bc)i`. -/
instance : Mul GaussInt := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

/-- Negation of Gaussian integers. -/
instance : Neg GaussInt := ⟨fun z => ⟨-z.re, -z.im⟩⟩

/-- The Gaussian integer `0`. -/
instance : Zero GaussInt := ⟨⟨0, 0⟩⟩

/-- The Gaussian integer `1`. -/
instance : One GaussInt := ⟨⟨1, 0⟩⟩

/-- Real part of a product. -/
@[simp] theorem mul_re (z w : GaussInt) : (z * w).re = z.re * w.re - z.im * w.im := rfl

/-- Imaginary part of a product. -/
@[simp] theorem mul_im (z w : GaussInt) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- Real part of a sum. -/
@[simp] theorem add_re (z w : GaussInt) : (z + w).re = z.re + w.re := rfl

/-- Imaginary part of a sum. -/
@[simp] theorem add_im (z w : GaussInt) : (z + w).im = z.im + w.im := rfl

/-- Real part of a negation. -/
@[simp] theorem neg_re (z : GaussInt) : (-z).re = -z.re := rfl

/-- Imaginary part of a negation. -/
@[simp] theorem neg_im (z : GaussInt) : (-z).im = -z.im := rfl

/-- Parts of `0`. -/
@[simp] theorem zero_re : (0 : GaussInt).re = 0 := rfl

/-- Parts of `0`. -/
@[simp] theorem zero_im : (0 : GaussInt).im = 0 := rfl

/-- Parts of `1`. -/
@[simp] theorem one_re : (1 : GaussInt).re = 1 := rfl

/-- Parts of `1`. -/
@[simp] theorem one_im : (1 : GaussInt).im = 0 := rfl

/-- **The ring `ℤ[i]`.** -/
instance : CommRing GaussInt where
  add_assoc _ _ _ := ext (by simp <;> grind) (by simp <;> grind)
  add_comm _ _ := ext (by simp <;> grind) (by simp <;> grind)
  zero_add _ := ext (by simp) (by simp)
  neg_add_cancel _ := ext (by simp <;> omega) (by simp <;> omega)
  mul_assoc _ _ _ := ext (by simp <;> grind) (by simp <;> grind)
  one_mul _ := ext (by simp) (by simp)
  mul_one _ := ext (by simp) (by simp)
  left_distrib _ _ _ := ext (by simp <;> grind) (by simp <;> grind)
  right_distrib _ _ _ := ext (by simp <;> grind) (by simp <;> grind)
  mul_comm _ _ := ext (by simp <;> grind) (by simp <;> grind)

/-- The imaginary unit satisfies `i² = -1`. -/
example : (⟨0, 1⟩ * ⟨0, 1⟩ : GaussInt) = -1 := rfl

/-- The **norm** `N(a + bi) = a² + b²`. -/
def norm (z : GaussInt) : Int := z.re * z.re + z.im * z.im

/-- Squares of integers are non-negative. -/
theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · rw [← Int.neg_mul_neg]; exact Int.mul_nonneg (by omega) (by omega)

/-- The norm is non-negative. -/
theorem norm_nonneg (z : GaussInt) : 0 ≤ norm z :=
  Int.add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The norm is multiplicative**: `N(zw) = N(z) N(w)` (Brahmagupta–Fibonacci identity). -/
theorem norm_mul (z w : GaussInt) : norm (z * w) = norm z * norm w := by
  unfold norm; simp only [mul_re, mul_im]; grind

/-- Only `0` has norm `0`. -/
theorem norm_eq_zero {z : GaussInt} : norm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold norm at h
    have h1 := sq_nonneg z.re
    have h2 := sq_nonneg z.im
    have e1 : z.re * z.re = 0 := by omega
    have e2 : z.im * z.im = 0 := by omega
    exact ext (by rcases Int.mul_eq_zero.1 e1 with h | h <;> exact h)
      (by rcases Int.mul_eq_zero.1 e2 with h | h <;> exact h)
  · intro h; rw [h]; rfl

/-- **`ℤ[i]` is an integral domain.** -/
theorem isDomain : IsDomain GaussInt := by
  refine ⟨fun h => absurd (congrArg GaussInt.re h) (by decide), fun z w h => ?_⟩
  have := congrArg norm h
  rw [norm_mul, show norm (0 : GaussInt) = 0 from rfl] at this
  rcases Int.mul_eq_zero.1 this with h | h
  · exact Or.inl (norm_eq_zero.1 h)
  · exact Or.inr (norm_eq_zero.1 h)

/-- Rounding: for `N > 0` there is `q` with `-N ≤ 2(x - qN) < N`. -/
theorem exists_round (x N : Int) (hN : 0 < N) : ∃ q : Int, -N ≤ 2 * (x - q * N) ∧ 2 * (x - q * N) < N := by
  refine ⟨(2 * x + N) / (2 * N), ?_⟩
  have h1 := Int.emod_add_mul_ediv (2 * x + N) (2 * N)
  have h2 := Int.emod_nonneg (2 * x + N) (b := 2 * N) (by omega)
  have h3 := Int.emod_lt_of_pos (2 * x + N) (b := 2 * N) (by omega)
  have e : 2 * N * ((2 * x + N) / (2 * N)) = 2 * ((2 * x + N) / (2 * N) * N) := by
    rw [Int.mul_comm ((2 * x + N) / (2 * N)) N, Int.mul_assoc]
  rw [e] at h1
  constructor <;> omega

/-- If `-N ≤ a ≤ N` then `a² ≤ N²`. -/
theorem sq_le_sq_of_abs_le {a N : Int} (h1 : -N ≤ a) (h2 : a ≤ N) : a * a ≤ N * N := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_self_le_mul_self h h2
  · rw [← Int.neg_mul_neg]; exact Int.mul_self_le_mul_self (by omega) (by omega)

/-- **Division with small remainder in `ℤ[i]`.** For `β ≠ 0` and any `α` there are `q`, `ρ`
with `α = qβ + ρ` and `N(ρ) < N(β)`. -/
theorem div_small (a b : GaussInt) (hb : b ≠ 0) :
    ∃ q r : GaussInt, a = q * b + r ∧ norm r < norm b := by
  have hN : 0 < norm b := by
    have := norm_nonneg b
    have : norm b ≠ 0 := fun h => hb (norm_eq_zero.1 h)
    omega
  let N := norm b
  let u := a.re * b.re + a.im * b.im
  let v := a.im * b.re - a.re * b.im
  obtain ⟨q1, hq1, hq1'⟩ := exists_round u N hN
  obtain ⟨q2, hq2, hq2'⟩ := exists_round v N hN
  let q : GaussInt := ⟨q1, q2⟩
  refine ⟨q, a + -(q * b), ?_, ?_⟩
  · rw [Ring.add_comm a, ← Ring.add_assoc, add_neg_cancel, Ring.zero_add]
  · -- `N(ρ) · N(β) = (u - q₁N)² + (v - q₂N)²`.
    have key : norm (a + -(q * b)) * N = (u - q1 * N) * (u - q1 * N) + (v - q2 * N) * (v - q2 * N) := by
      show norm (a + -(q * b)) * norm b = _
      unfold norm
      simp only [add_re, add_im, neg_re, neg_im, mul_re, mul_im]
      show _ = (a.re * b.re + a.im * b.im - q1 * (b.re * b.re + b.im * b.im)) *
          (a.re * b.re + a.im * b.im - q1 * (b.re * b.re + b.im * b.im)) +
        (a.im * b.re - a.re * b.im - q2 * (b.re * b.re + b.im * b.im)) *
          (a.im * b.re - a.re * b.im - q2 * (b.re * b.re + b.im * b.im))
      grind
    have s1 := sq_le_sq_of_abs_le hq1 (Int.le_of_lt hq1')
    have s2 := sq_le_sq_of_abs_le hq2 (Int.le_of_lt hq2')
    have e1 : 2 * (u - q1 * N) * (2 * (u - q1 * N)) = 4 * ((u - q1 * N) * (u - q1 * N)) := by grind
    have e2 : 2 * (v - q2 * N) * (2 * (v - q2 * N)) = 4 * ((v - q2 * N) * (v - q2 * N)) := by grind
    have hlt : norm (a + -(q * b)) * N < N * N := by
      have hNN : 0 < N * N := Int.mul_pos hN hN
      omega
    exact Int.lt_of_mul_lt_mul_right hlt (Int.le_of_lt hN)

/-- **`ℤ[i]` is a Euclidean domain** (Gauss), with the norm as size. -/
theorem isEuclidean : IsEuclidean GaussInt := by
  refine ⟨isDomain, fun z => (norm z).toNat, fun a b hb => ?_⟩
  obtain ⟨q, r, h, hr⟩ := div_small a b hb
  refine ⟨q, r, h, Or.inr ?_⟩
  show (norm r).toNat < (norm b).toNat
  have := norm_nonneg r
  omega

/-- **`ℤ[i]` is a principal ideal domain**, and so has unique factorisation. -/
theorem isPID : IsPID GaussInt := isEuclidean.isPID

end GaussInt

end Foundations.Algebra
