import Foundations.Langlands.Squares.FourSquares

/-!
# The Davenport–Cassels lemma for three squares

If a number is a sum of three *rational* squares, is it a sum of three *integer* squares? For the
form `x² + y² + z²` the answer is yes, by a beautiful geometric descent usually attributed to
Davenport and Cassels (it is the route taken in Serre's *Cours d'arithmétique*, 1970), although
the argument was found earlier by L. Aubry (1912).

Write the rational point as `X / t` with `X ∈ ℤ³`, `t ≥ 1`, `|X|² = k t²`. Round it to the nearest
lattice point `Y`, so every coordinate of `X − tY` is at most `t/2` in absolute value, hence
`|X − tY|² ≤ 3t²/4 < t²`. If `X = tY` we are done. Otherwise the line through `Y` and `X / t`
meets the sphere `|v|² = k` in a second rational point, and a short computation shows that its
denominator is

  `t' = |X − tY|² / t = k t − 2 X·Y + t |Y|²`, with `0 < t' < t`;

the new numerator is `X' = t' Y + (|Y|² − k)(X − tY)`, and `|X'|² = k t'²` is a polynomial
identity. Strong induction on `t` finishes the proof (`davenport_cassels`).

The Euclidean property used here — every point of `ℚ³` is at squared distance `< 1` from a point
of `ℤ³` — is what the lemma needs in general; it holds for sums of two, three or four squares but
fails for most positive forms, for which rational and integral representability differ.
-/

namespace Foundations.Langlands.Squares

/-- **Davenport–Cassels for three squares.** If `k t²` is a sum of three integer squares for some
`t ≥ 1`, then `k` itself is a sum of three integer squares. -/
theorem davenport_cassels (k : Int) :
    ∀ t : Nat, 0 < t → ∀ x1 x2 x3 : Int, x1 * x1 + x2 * x2 + x3 * x3 = k * ((t : Int) * t) →
      ∃ a b c : Int, a * a + b * b + c * c = k := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
  intro ht x1 x2 x3 hx
  have hT : (0 : Int) < (t : Int) := by omega
  obtain ⟨r1, y1, e1, a1, b1⟩ := exists_symm_residue x1 t hT
  obtain ⟨r2, y2, e2, a2, b2⟩ := exists_symm_residue x2 t hT
  obtain ⟨r3, y3, e3, a3, b3⟩ := exists_symm_residue x3 t hT
  generalize hTdef : (t : Int) = T at *
  -- `X = r + T Y` with `|rᵢ| ≤ T/2`.
  have q1 := four_sq_le a1 b1
  have q2 := four_sq_le a2 b2
  have q3 := four_sq_le a3 b3
  have s1 := sq_nonneg' r1
  have s2 := sq_nonneg' r2
  have s3 := sq_nonneg' r3
  by_cases h0 : r1 * r1 + r2 * r2 + r3 * r3 = 0
  · -- `X = T Y`, so `|Y|² = k`.
    have z1 := eq_zero_of_sq_eq_zero (t := r1) (by omega)
    have z2 := eq_zero_of_sq_eq_zero (t := r2) (by omega)
    have z3 := eq_zero_of_sq_eq_zero (t := r3) (by omega)
    subst z1 z2 z3
    refine ⟨y1, y2, y3, ?_⟩
    have hTT : T * T ≠ 0 := by
      intro h; rcases Int.mul_eq_zero.1 h with h | h <;> omega
    apply Int.eq_of_mul_eq_mul_left hTT
    subst e1 e2 e3
    grind
  · -- The second intersection point has denominator `T' = |r|² / T`.
    let T' : Int := k * T - 2 * (x1 * y1 + x2 * y2 + x3 * y3) + T * (y1 * y1 + y2 * y2 + y3 * y3)
    have hTT' : T * T' = r1 * r1 + r2 * r2 + r3 * r3 := by
      subst e1 e2 e3; grind
    have hpos : 0 < T * T' := by omega
    have hT'0 : 0 < T' := by
      apply Classical.byContradiction; intro hn
      have := Int.mul_le_mul_of_nonneg_left (show T' ≤ 0 by omega) (Int.le_of_lt hT)
      omega
    have hT'T : T' < T := by
      apply Classical.byContradiction; intro hn
      have := Int.mul_le_mul_of_nonneg_left (show T ≤ T' by omega) (Int.le_of_lt hT)
      omega
    have hlt : T'.toNat < t := by omega
    let N : Int := y1 * y1 + y2 * y2 + y3 * y3 - k
    apply ih T'.toNat hlt (by omega) (T' * y1 + N * r1) (T' * y2 + N * r2) (T' * y3 + N * r3)
    rw [Int.toNat_of_nonneg (Int.le_of_lt hT'0)]
    -- The identity `|X'|² = k T'²`, after multiplying by `T ≠ 0`.
    apply Int.eq_of_mul_eq_mul_left (show T ≠ 0 by omega)
    subst e1 e2 e3
    grind

/-- Integer form of the Davenport–Cassels lemma with a non-zero integer denominator. -/
theorem davenport_cassels_int {k z : Int} (hz : z ≠ 0) {x1 x2 x3 : Int}
    (h : x1 * x1 + x2 * x2 + x3 * x3 = k * (z * z)) : ∃ a b c : Int, a * a + b * b + c * c = k := by
  have hz' : ((z.natAbs : Nat) : Int) * (z.natAbs : Nat) = z * z := Int.natAbs_mul_self
  exact davenport_cassels k z.natAbs (by omega) x1 x2 x3 (by rw [hz']; exact h)

end Foundations.Langlands.Squares
