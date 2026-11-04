import Foundations.Langlands.Squares.Identities

/-!
# Three squares: the necessary condition

That numbers of the form `8b + 7` are never sums of three squares was known in the seventeenth
century (it is stated by Descartes and by Fermat), and **Legendre** (*Essai sur la théorie des nombres*, 1798) stated the full theorem, with a proof resting on the then-unproved Dirichlet theorem:

> a natural number is a sum of three squares if and only if it is not of the form `4ᵃ(8b + 7)`.

Legendre's proof of sufficiency had a gap (it used Dirichlet's theorem on primes in progressions
before Dirichlet proved it); **Gauss** gave a complete proof in the *Disquisitiones* (1801, art. 291–292),
via his theory of ternary quadratic forms, and also counted the representations in terms of class
numbers of binary forms. The easy half, formalised here, is a congruence argument:

* a square is `≡ 0, 1` or `4 (mod 8)`, so a sum of three squares is never `≡ 7 (mod 8)`;
* if `x² + y² + z² ≡ 0 (mod 4)` then `x, y, z` are all even (odd squares are `≡ 1 (mod 4)`), so
  `4ᵃ⁺¹(8b + 7)` is a sum of three squares only if `4ᵃ(8b + 7)` is.

In the language of the Hasse principle, `8b + 7` is the obstruction at the prime `2`: the form
`x² + y² + z²` does not represent `7` over `ℚ₂`. The sufficiency direction (every other number *is*
a sum of three squares) is the content of `ThreeSquaresSuff`, which combines both halves into
`three_squares_iff`.
-/

namespace Foundations.Langlands.Squares

/-- **Squares modulo 8.** An even square is `≡ 0` or `4 (mod 8)`; an odd square is `≡ 1 (mod 8)`. -/
theorem sq_mod_eight (x : Nat) :
    (x % 2 = 0 ∧ (x * x % 8 = 0 ∨ x * x % 8 = 4)) ∨ (x % 2 = 1 ∧ x * x % 8 = 1) := by
  have h : x * x % 8 = (x % 8) * (x % 8) % 8 := Nat.mul_mod x x 8
  have h2 : x % 2 = x % 8 % 2 := (Nat.mod_mod_of_dvd x (by decide : 2 ∣ 8)).symm
  rw [h, h2]
  have : x % 8 < 8 := Nat.mod_lt x (by decide)
  generalize x % 8 = r at this ⊢
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- A sum of three squares is never `≡ 7 (mod 8)`. -/
theorem sum_three_sq_mod_eight_ne_seven (x y z : Nat) : (x * x + y * y + z * z) % 8 ≠ 7 := by
  have := sq_mod_eight x
  have := sq_mod_eight y
  have := sq_mod_eight z
  omega

/-- If `x² + y² + z² ≡ 0 (mod 4)` then `x`, `y`, `z` are all even. -/
theorem even_of_sum_three_sq_mod_four {x y z : Nat} (h : (x * x + y * y + z * z) % 4 = 0) :
    x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 := by
  have := sq_mod_eight x
  have := sq_mod_eight y
  have := sq_mod_eight z
  omega

/-- **Necessity in Legendre's three-square theorem.** No number of the form `4ᵃ(8b + 7)` is a
sum of three squares of natural numbers. -/
theorem not_sum_three_squares (a b : Nat) :
    ¬ ∃ x y z : Nat, x * x + y * y + z * z = 4 ^ a * (8 * b + 7) := by
  induction a with
  | zero =>
    rintro ⟨x, y, z, h⟩
    apply sum_three_sq_mod_eight_ne_seven x y z
    rw [h]; omega
  | succ a ih =>
    rintro ⟨x, y, z, h⟩
    have h4 : (x * x + y * y + z * z) % 4 = 0 := by
      rw [h, Nat.pow_succ]
      exact Nat.mod_eq_zero_of_dvd ⟨4 ^ a * (8 * b + 7), by grind⟩
    obtain ⟨hx, hy, hz⟩ := even_of_sum_three_sq_mod_four h4
    obtain ⟨x', rfl⟩ : ∃ x', x = 2 * x' := ⟨x / 2, by omega⟩
    obtain ⟨y', rfl⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
    obtain ⟨z', rfl⟩ : ∃ z', z = 2 * z' := ⟨z / 2, by omega⟩
    apply ih
    refine ⟨x', y', z', ?_⟩
    rw [Nat.pow_succ] at h
    have : 4 * (x' * x' + y' * y' + z' * z') = 4 * (4 ^ a * (8 * b + 7)) := by grind
    omega

/-- **Legendre's obstruction**, restated: a sum of three squares is not of the form
`4ᵃ(8b + 7)`. -/
theorem sum_three_squares_not_form {n x y z : Nat} (h : x * x + y * y + z * z = n) :
    ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7) := by
  rintro ⟨a, b, rfl⟩
  exact not_sum_three_squares a b ⟨x, y, z, h⟩

/-- Examples: `7`, `15`, `28 = 4 · 7` and `60 = 4 · 15` are not sums of three squares. -/
example : (¬ ∃ x y z : Nat, x * x + y * y + z * z = 7) ∧
    (¬ ∃ x y z : Nat, x * x + y * y + z * z = 15) ∧
    (¬ ∃ x y z : Nat, x * x + y * y + z * z = 28) ∧
    (¬ ∃ x y z : Nat, x * x + y * y + z * z = 60) :=
  ⟨not_sum_three_squares 0 0, not_sum_three_squares 0 1, not_sum_three_squares 1 0,
    not_sum_three_squares 1 1⟩

end Foundations.Langlands.Squares
