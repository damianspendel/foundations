import Foundations.Algebra.Group

/-!
# Exercises IV: Algebra

Problems on group theory from Part IV (`Foundations/Algebra/Group.lean`): computations from
the group axioms, powers, homomorphisms and kernels, permutations and the cyclic groups
`ℤ/nℤ`.

The axioms are one-sided (associativity, `1 * a = a`, `a⁻¹ * a = 1`); the library derives the
other side (`Group.mul_one`, `Group.mul_inv_cancel`) and the usual cancellation rules. Powers
are `a ^ 0 = 1`, `a ^ (n + 1) = a ^ n * a` (`Group.pow_succ`).

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in `Exercises/Problems/Algebra.lean`.
-/

namespace Exercises.Algebra

open Foundations.Algebra Foundations.Algebra.Group

universe u v

variable {G : Type u} [Group G]

/-- **Exercise 4.1 (★) — Socks and shoes, three times.** `(a b c)⁻¹ = c⁻¹ b⁻¹ a⁻¹`.

*Hint:* the library has the two-factor rule; apply it twice.

*Uses:* `Group.mul_inv_rev`, `Group.mul_assoc`. -/
theorem mul_inv_rev3 (a b c : G) : (a * b * c)⁻¹ = c⁻¹ * b⁻¹ * a⁻¹ := by
  -- SOLUTION
  rw [mul_inv_rev, mul_inv_rev, mul_assoc]
  -- END

/-- **Exercise 4.2 (★★) — Exponent two forces commutativity.** If `x * x = 1` for every `x`,
then the group is commutative.

*Hint:* each element is its own inverse. Apply this to `a`, `b` and `a * b`, and compare
`(a b)⁻¹ = b⁻¹ a⁻¹`.

*Uses:* `Group.inv_eq_of_mul_eq_one`, `Group.mul_inv_rev`. -/
theorem comm_of_sq_eq_one (h : ∀ x : G, x * x = 1) (a b : G) : a * b = b * a := by
  -- SOLUTION
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one (h a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one (h b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one (h (a * b))
  rw [← hab, mul_inv_rev, ha, hb]
  -- END

/-- **Exercise 4.3 (★★) — Conjugation commutes with powers.** `(g a g⁻¹)ⁿ = g aⁿ g⁻¹`.

*Hint:* induction on `n`. In the step, the middle `g⁻¹ * g` cancels: rewrite with
`pow_succ` and reassociate (`mul_assoc`, `inv_mul_cancel_left`).

*Uses:* `Group.pow_succ`, `Group.mul_assoc`, `Group.inv_mul_cancel_left`,
`Group.mul_inv_cancel`. -/
theorem conj_pow (g a : G) (n : Nat) : (g * a * g⁻¹) ^ n = g * a ^ n * g⁻¹ := by
  -- SOLUTION
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one, mul_inv_cancel]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, inv_mul_cancel_left]
  -- END

/-- **Exercise 4.4 (★★★) — `ab` and `ba` have the same order.** If `(a b)ⁿ = 1` then
`(b a)ⁿ = 1`.

*Hint:* `b a` is a conjugate of `a b`: `b a = a⁻¹ (a b) a`. Prove the conjugation-power rule
of the previous exercise (as a `have`, by induction) and apply it with `g = a⁻¹`.

*Uses:* `Group.pow_succ`, `Group.inv_inv`, `Group.inv_mul_cancel_left`, `Group.mul_one`. -/
theorem pow_mul_comm_eq_one {a b : G} {n : Nat} (h : (a * b) ^ n = 1) : (b * a) ^ n = 1 := by
  -- SOLUTION
  have conj : ∀ (g x : G) (m : Nat), (g * x * g⁻¹) ^ m = g * x ^ m * g⁻¹ := by
    intro g x m
    induction m with
    | zero => rw [pow_zero, pow_zero, mul_one, mul_inv_cancel]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc, inv_mul_cancel_left]
  have hba : b * a = a⁻¹ * (a * b) * a⁻¹⁻¹ := by
    rw [inv_inv, inv_mul_cancel_left]
  rw [hba, conj, h, mul_one, inv_inv, inv_mul_cancel]
  -- END

/-- **Exercise 4.5 (★) — Equal images, kernel quotient.** If a homomorphism `f` takes the
same value at `a` and `b`, then `a⁻¹ b` lies in the kernel of `f`.

*Hint:* the library characterises equality of images through the kernel.

*Uses:* `Hom.eq_iff_inv_mul_mem_ker`. -/
theorem inv_mul_mem_ker {H : Type v} [Group H] (f : G →* H) {a b : G} (h : f a = f b) :
    a⁻¹ * b ∈ f.ker := by
  -- SOLUTION
  exact (Hom.eq_iff_inv_mul_mem_ker f).1 h
  -- END

/-- **Exercise 4.6 (★★) — A transposition is an involution.** In the symmetric group,
`swap a b * swap a b = 1`.

*Hint:* two permutations are equal if they agree at every point (`Perm.ext`). Evaluate both
sides at `x` (`Perm.mul_apply`, `Perm.one_apply`), unfold `swap` and split into the cases
`x = a`, `x = b` and neither.

*Uses:* `Perm.ext`, `Perm.mul_apply`, `Perm.swap`. -/
theorem swap_mul_self {α : Type u} [DecidableEq α] (a b : α) :
    Perm.swap a b * Perm.swap a b = 1 := by
  -- SOLUTION
  apply Perm.ext
  intro x
  simp only [Perm.mul_apply, Perm.one_apply]
  show (if (if x = a then b else if x = b then a else x) = a then b
      else if (if x = a then b else if x = b then a else x) = b then a
      else (if x = a then b else if x = b then a else x)) = x
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> simp_all
  -- END

/-- **Exercise 4.7 (★) — The generator of `ℤ/nℤ` has order dividing `n`.** In `ZMod n`
(written multiplicatively), `genⁿ = 1`.

*Hint:* two residues are equal when their values are (`Fin.ext`); compute the value of
`genⁿ` with the library and use `n % n = 0`.

*Uses:* `ZMod.pow_gen`, `Nat.mod_self`. -/
theorem gen_pow_n (n : Nat) [NeZero n] : (ZMod.gen ^ n : ZMod n) = 1 := by
  -- SOLUTION
  apply Fin.ext
  show (ZMod.val (ZMod.gen ^ n : ZMod n)).val = (0 : Fin n).val
  rw [ZMod.pow_gen, Nat.mod_self]
  rfl
  -- END

end Exercises.Algebra
