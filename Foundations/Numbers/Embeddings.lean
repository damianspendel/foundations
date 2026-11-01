import Foundations.Numbers.Uncountable

/-!
# ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ

Strictly speaking, our constructions do not make the natural numbers a *subset* of the integers:
an integer is a class of pairs of naturals, not a natural number. What is true is that each
system contains a faithful *copy* of the previous one: there is an injective map preserving
`0`, `1`, `+` and `×` (and the order). This is how the familiar chain `ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ` is to be
understood in a construction-based foundation: "`3` is a real number" means that the real number
represented by the constant sequence `3, 3, 3, …` plays, among the reals, exactly the role that
the natural number `3` plays among the naturals.

* `ℕ → ℤ` sends `n` to the class of the pair `(n, 0)`;
* `ℤ → ℚ` sends an integer `i` to the class of the fraction `i/1`;
* `ℚ → ℝ` sends `q` to the class of the constant sequence `q, q, q, …`.
-/

namespace Foundations.Numbers

open Lean.Grind

/-- The natural number `n` as an integer: the class of `(n, 0)`. -/
def natToZ (n : Nat) : Z := Z.mk n 0

/-- The integer `x` as a rational: the class of the fraction `x/1`. -/
def zToQ (x : Z) : Q := Q.mk (Z.toInt x) 1 Int.one_pos

/-- **ℕ embeds in ℤ.** `natToZ` is injective and preserves `0`, `1`, `+`, `×` and `≤`. -/
theorem natToZ_embedding :
    natToZ 0 = 0 ∧ natToZ 1 = 1 ∧ (∀ a b, natToZ (a + b) = natToZ a + natToZ b) ∧
    (∀ a b, natToZ (a * b) = natToZ a * natToZ b) ∧ (∀ a b, a ≤ b ↔ natToZ a ≤ natToZ b) ∧
    (∀ a b, natToZ a = natToZ b → a = b) := by
  refine ⟨rfl, rfl, fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a b h => ?_⟩
  · simp only [natToZ, Z.mk_add]
  · simp only [natToZ, Z.mk_mul, Z.mk_eq_mk]; simp
  · simp only [natToZ, Z.mk_le]; omega
  · simp only [natToZ, Z.mk_eq_mk] at h; omega

/-- `Z.toInt` is injective. -/
theorem Z.toInt_inj {x y : Z} (h : Z.toInt x = Z.toInt y) : x = y := by
  rw [← Z.equivInt.left_inv x, ← Z.equivInt.left_inv y]
  exact congrArg Z.ofInt h

/-- **ℤ embeds in ℚ.** `zToQ` is injective and preserves `0`, `1`, `+`, `×` and `≤`. -/
theorem zToQ_embedding :
    zToQ 0 = 0 ∧ zToQ 1 = 1 ∧ (∀ x y, zToQ (x + y) = zToQ x + zToQ y) ∧
    (∀ x y, zToQ (x * y) = zToQ x * zToQ y) ∧ (∀ x y, x ≤ y ↔ zToQ x ≤ zToQ y) ∧
    (∀ x y, zToQ x = zToQ y → x = y) := by
  refine ⟨rfl, rfl, fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y h => ?_⟩
  · simp only [zToQ, Q.mk_add, Q.mk_eq_mk, Z.toInt_add]; omega
  · simp only [zToQ, Q.mk_mul, Q.mk_eq_mk, Z.toInt_mul]; omega
  · simp only [zToQ, Q.mk_le, Z.toInt_le]; omega
  · simp only [zToQ, Q.mk_eq_mk] at h; exact Z.toInt_inj (by omega)

/-- **ℚ embeds in ℝ.** `ofQ` is injective and preserves `0`, `1`, `+`, `×` and `≤`. -/
theorem ofQ_embedding :
    R.ofQ 0 = 0 ∧ R.ofQ 1 = 1 ∧ (∀ p q, R.ofQ (p + q) = R.ofQ p + R.ofQ q) ∧
    (∀ p q, R.ofQ (p * q) = R.ofQ p * R.ofQ q) ∧ (∀ p q, p ≤ q ↔ R.ofQ p ≤ R.ofQ q) ∧
    (∀ p q, R.ofQ p = R.ofQ q → p = q) := by
  refine ⟨rfl, rfl, R.ofQ_add, R.ofQ_mul, fun p q => R.ofQ_le.symm, fun p q h => ?_⟩
  have h1 := R.ofQ_le.1 (le_of_eq h : R.ofQ p ≤ R.ofQ q)
  have h2 := R.ofQ_le.1 (le_of_eq h.symm : R.ofQ q ≤ R.ofQ p)
  exact Q.le_antisymm h1 h2
where
  le_of_eq {x y : R} (h : x = y) : x ≤ y := Or.inr h

/-- **The chain ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ.** The composite embedding of the natural numbers into the reals
is injective and preserves addition and multiplication. -/
theorem nat_to_real_embedding :
    let ι : Nat → R := fun n => R.ofQ (zToQ (natToZ n))
    (∀ a b, ι (a + b) = ι a + ι b) ∧ (∀ a b, ι (a * b) = ι a * ι b) ∧
    (∀ a b, ι a = ι b → a = b) := by
  intro ι
  obtain ⟨_, _, hz1, hz2, _, hz3⟩ := natToZ_embedding
  obtain ⟨_, _, hq1, hq2, _, hq3⟩ := zToQ_embedding
  obtain ⟨_, _, hr1, hr2, _, hr3⟩ := ofQ_embedding
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b h => hz3 _ _ (hq3 _ _ (hr3 _ _ h))⟩
  · show R.ofQ (zToQ (natToZ (a + b))) = _
    rw [hz1, hq1, hr1]
  · show R.ofQ (zToQ (natToZ (a * b))) = _
    rw [hz2, hq2, hr2]

end Foundations.Numbers
