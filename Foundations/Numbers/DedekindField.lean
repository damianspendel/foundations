import Foundations.Numbers.Dedekind

/-!
# The Dedekind reals form a complete ordered field

We now harvest the bridge of `Dedekind.lean`. The map `ofR : R → Cut` is a bijection that carries
the Cauchy-real `+`, `−`, `×` and `≤` to the operations defined directly on cuts. Hence every
algebraic law satisfied by `R` is also satisfied by cuts: to check, say, `A · (B + C) = A·B + A·C`
for cuts, write `A, B, C` as `ofR x, ofR y, ofR z` and use the law in `R`. With inverses defined
(as for `R`) by "the `B` with `A · B = 1`", cuts form an ordered field, and their least upper
bound property was proved directly. So the cuts are a **complete ordered field**, and by
categoricity there is exactly one isomorphism between Dedekind's reals and Cantor's.
-/

namespace Foundations.Numbers

open Lean.Grind

namespace Cut

/-- The order of reals corresponds to the order of cuts (strict version). -/
theorem ofR_lt (x y : R) : x < y ↔ ofR x < ofR y := by
  have h1 := ofR_le x y; have h2 := ofR_le y x
  constructor
  · intro h; exact ⟨h1.1 (by grind), fun h' => by have := h2.2 h'; grind⟩
  · intro ⟨h, h'⟩; have := h1.2 h; have : ¬ y ≤ x := fun h'' => h' (h2.1 h''); grind

/-- Zero as the cut of the real zero. -/
theorem zero_eq : (0 : Cut) = ofR 0 := ofR_zero.symm
/-- One as the cut of the real one. -/
theorem one_eq : (1 : Cut) = ofR 1 := (ofR_ofNat 1).symm
/-- Subtraction of cuts unfolded. -/
theorem sub_eq (A B : Cut) : A - B = A + -B := rfl

/-- Transport an equation between cuts to the corresponding equation between reals. -/
macro "transport" : tactic => `(tactic| (
  simp only [sub_eq, zero_eq, one_eq, ← ofR_add, ← ofR_neg, ← ofR_mul]
  try (congr 1; grind)))

/-- Addition is associative. -/
theorem add_assoc (A B C : Cut) : A + B + C = A + (B + C) := by
  obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; obtain ⟨z, rfl⟩ := surj C; transport
/-- Addition is commutative. -/
theorem add_comm (A B : Cut) : A + B = B + A := by
  obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; transport
/-- Zero is the additive identity. -/
theorem add_zero (A : Cut) : A + 0 = A := by
  obtain ⟨x, rfl⟩ := surj A; transport
/-- `-x` is an additive inverse of `x`. -/
theorem neg_add_cancel (A : Cut) : -A + A = 0 := by
  obtain ⟨x, rfl⟩ := surj A; transport
/-- Multiplication is associative. -/
theorem mul_assoc (A B C : Cut) : A * B * C = A * (B * C) := by
  obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; obtain ⟨z, rfl⟩ := surj C; transport
/-- Multiplication is commutative. -/
theorem mul_comm (A B : Cut) : A * B = B * A := by
  obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; transport
/-- One is the multiplicative identity. -/
theorem mul_one (A : Cut) : A * 1 = A := by
  obtain ⟨x, rfl⟩ := surj A; transport
/-- One is a left identity. -/
theorem one_mul (A : Cut) : 1 * A = A := by
  obtain ⟨x, rfl⟩ := surj A; transport
/-- Zero times anything is zero. -/
theorem zero_mul (A : Cut) : 0 * A = 0 := by
  obtain ⟨x, rfl⟩ := surj A; transport
/-- Anything times zero is zero. -/
theorem mul_zero (A : Cut) : A * 0 = 0 := by
  obtain ⟨x, rfl⟩ := surj A; transport
/-- Multiplication distributes over addition (left). -/
theorem left_distrib (A B C : Cut) : A * (B + C) = A * B + A * C := by
  obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; obtain ⟨z, rfl⟩ := surj C; transport
/-- Multiplication distributes over addition (right). -/
theorem right_distrib (A B C : Cut) : (A + B) * C = A * C + B * C := by
  obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; obtain ⟨z, rfl⟩ := surj C; transport
/-- `(-x) · y = -(x · y)`. -/
theorem neg_mul (A B : Cut) : -A * B = -(A * B) := by
  obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; transport

/-- Zero is different from one. -/
theorem zero_ne_one : (0 : Cut) ≠ 1 := by
  rw [zero_eq, one_eq]; intro h; have := ofR_inj h; grind

/-- Natural-number powers of cuts. -/
noncomputable def npow (A : Cut) : Nat → Cut
  | 0 => 1
  | n + 1 => npow A n * A

/-- Powers. -/
noncomputable instance : HPow Cut Nat Cut := ⟨npow⟩

/-- The inverse of a cut: the `B` with `A · B = 1` if there is one, `0` otherwise. -/
noncomputable def inv (A : Cut) : Cut :=
  open Classical in if h : ∃ B, A * B = 1 then Classical.choose h else 0

/-- Inversion. -/
noncomputable instance : Inv Cut := ⟨inv⟩
/-- Division. -/
noncomputable instance : Div Cut := ⟨fun A B => A * inv B⟩

/-- A non-zero element times its inverse is one. -/
theorem mul_inv_cancel {A : Cut} (hA : A ≠ 0) : A * A⁻¹ = 1 := by
  have h : ∃ B, A * B = 1 := by
    obtain ⟨x, rfl⟩ := surj A
    have hx : x ≠ 0 := fun h => hA (by rw [h, ofR_zero])
    refine ⟨ofR x⁻¹, ?_⟩
    rw [← ofR_mul, one_eq]; congr 1; grind
  show A * inv A = 1
  unfold inv; rw [dite_eq_left h]; exact Classical.choose_spec h

/-- The junk-value convention `0⁻¹ = 0`. -/
theorem inv_zero : (0 : Cut)⁻¹ = 0 := by
  show inv 0 = 0
  unfold inv; rw [dite_eq_right]
  rintro ⟨B, hB⟩; rw [zero_mul] at hB; exact zero_ne_one hB

/-- Inversion is an involution. -/
theorem inv_inv (A : Cut) : A⁻¹⁻¹ = A := by
  by_cases hA : A = 0
  · rw [hA, inv_zero, inv_zero]
  · have h1 := mul_inv_cancel hA
    have hA' : A⁻¹ ≠ 0 := by intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
    have h2 := mul_inv_cancel hA'
    calc A⁻¹⁻¹ = (A * A⁻¹) * A⁻¹⁻¹ := by rw [h1, one_mul]
      _ = A * (A⁻¹ * A⁻¹⁻¹) := mul_assoc _ _ _
      _ = A := by rw [h2, mul_one]

/-- The inverse of one is one. -/
theorem inv_one : (1 : Cut)⁻¹ = 1 := by
  have h := mul_inv_cancel (Ne.symm zero_ne_one); rw [one_mul] at h; exact h

/-- Integer powers of cuts. -/
noncomputable def zpow (A : Cut) : Int → Cut
  | .ofNat n => A ^ n
  | .negSucc n => (A ^ (n + 1))⁻¹

/-- Powers. -/
noncomputable instance : HPow Cut Int Cut := ⟨zpow⟩

/-- Rational cuts add like rationals. -/
theorem ratCut_add (p q : Q) : ratCut (p + q) = ratCut p + ratCut q := by
  rw [← ofR_ofQ, ← ofR_ofQ, ← ofR_ofQ, R.ofQ_add, ofR_add]

/-- Rational cuts negate like rationals. -/
theorem ratCut_neg (p : Q) : ratCut (-p) = -ratCut p := by
  rw [← ofR_ofQ, ← ofR_ofQ, R.ofQ_neg, ofR_neg]

/-- **The Dedekind reals form a field.** -/
noncomputable instance instField : Field Cut where
  nsmul := ⟨fun n A => (n : Cut) * A⟩
  zsmul := ⟨fun i A => (i : Cut) * A⟩
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
    show ratCut _ = ratCut _ + ratCut _
    rw [← ratCut_add]; congr 1; exact Semiring.ofNat_succ n
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i A := by
    show ratCut ((-i : Int) : Q) * A = -(ratCut (i : Q) * A)
    rw [← neg_mul, ← ratCut_neg]; rfl
  intCast_neg i := by
    show ratCut ((-i : Int) : Q) = -ratCut (i : Q)
    rw [← ratCut_neg]; rfl
  mul_comm := mul_comm
  inv := inv
  div := fun A B => A * inv B
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
      | zero => show (1 : Cut) = 1⁻¹; rw [inv_one]
      | succ n => rfl
    | negSucc n => show a ^ (n + 1) = ((a ^ (n + 1))⁻¹)⁻¹; rw [inv_inv]

/-- Addition of cuts respects the order. -/
noncomputable instance : OrderedAdd Cut where
  add_le_left_iff {A B} C := by
    obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; obtain ⟨z, rfl⟩ := surj C
    rw [← ofR_add, ← ofR_add, ← ofR_le, ← ofR_le]
    exact OrderedAdd.add_le_left_iff z

/-- **The Dedekind reals form an ordered field.** -/
noncomputable instance instOrderedRing : OrderedRing Cut where
  zero_lt_one := by rw [zero_eq, one_eq, ← ofR_lt]; exact OrderedRing.zero_lt_one
  mul_lt_mul_of_pos_left {A B C} h hC := by
    obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; obtain ⟨z, rfl⟩ := surj C
    rw [zero_eq, ← ofR_lt] at hC
    rw [← ofR_lt] at h
    rw [← ofR_mul, ← ofR_mul, ← ofR_lt]
    exact OrderedRing.mul_lt_mul_of_pos_left h hC
  mul_lt_mul_of_pos_right {A B C} h hC := by
    obtain ⟨x, rfl⟩ := surj A; obtain ⟨y, rfl⟩ := surj B; obtain ⟨z, rfl⟩ := surj C
    rw [zero_eq, ← ofR_lt] at hC
    rw [← ofR_lt] at h
    rw [← ofR_mul, ← ofR_mul, ← ofR_lt]
    exact OrderedRing.mul_lt_mul_of_pos_right h hC

/-- **The Dedekind reals form a complete ordered field.** -/
instance instComplete : CompleteOrderedField Cut := ⟨lub⟩

/-- **Dedekind reals ≅ Cauchy reals, explicitly.** The map `x ↦ {q | q < x}` is an isomorphism
of ordered fields from the Cauchy reals to the Dedekind reals. -/
noncomputable def isoR : OrderedFieldIso R Cut where
  toFun := ofR
  invFun := toR
  left_inv := toR_ofR
  right_inv := ofR_toR
  map_add := ofR_add
  map_mul := ofR_mul
  map_le := ofR_le

/-- **Dedekind reals ≅ Cauchy reals, by categoricity.** There is an isomorphism of ordered fields
between the Dedekind cuts and the Cauchy reals, and it is unique. -/
theorem dedekind_iso_cauchy :
    Nonempty (OrderedFieldIso Cut R) ∧
      ∀ e₁ e₂ : OrderedFieldIso Cut R, ∀ x, e₁.toFun x = e₂.toFun x :=
  categoricity

end Cut

end Foundations.Numbers
