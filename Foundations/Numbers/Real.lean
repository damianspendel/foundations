import Foundations.Numbers.Cauchy

/-!
# The real numbers as classes of Cauchy sequences

We now take the decisive step of the Cantor–Méray construction. A **real number** is an
equivalence class of Cauchy sequences of rationals, two sequences being identified when their
difference tends to zero. The number `√2`, for instance, *is* the class of all rational sequences
that close in on it — `1, 1.4, 1.41, 1.414, …` and every other sequence equivalent to that one.

This may look like a sleight of hand: we wanted a *point* filling the gap and we were handed a
*process* instead. But this is the same move as before. The integer `−2` was the class of pairs
with difference `−2`, the rational `½` was the class of fractions equal to `½`; the real `√2` is
the class of rational processes converging to `√2`. In each case the new object is constituted
by everything that "points at it", and no prior existence of the object is presupposed.

In this file we define the real numbers `R`, the embedding `ofQ : Q → R` of the rationals as
constant sequences, and addition, negation and multiplication (computed term by term). The ring
laws are inherited directly from those of `Q`, because they hold term by term. We register `R`
with Lean's automation as a commutative ring. The order, the inverse, and the field structure
follow in `RealOrder.lean`.
-/

namespace Foundations.Numbers

/-- **The real numbers.** A real number is an equivalence class of Cauchy sequences of
rationals, where two sequences are equivalent when their difference tends to zero. -/
def R : Type := Quotient CauSeq.setoid

namespace R

open CauSeq

/-- The real number determined by a Cauchy sequence of rationals. -/
def mk (a : CauSeq) : R := Quotient.mk CauSeq.setoid a

/-- Two Cauchy sequences define the same real number iff they are equivalent. -/
theorem mk_eq_mk {a b : CauSeq} : mk a = mk b ↔ a ≈ b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every real number is given by some Cauchy sequence. -/
@[elab_as_elim]
theorem ind {P : R → Prop} (h : ∀ a, P (mk a)) (x : R) : P x := Quotient.ind h x

/-- The rational number `q`, viewed as a real number (the class of the constant sequence). -/
def ofQ (q : Q) : R := mk (const q)

/-- Numerals in `R` are the images of rational numerals. -/
instance instOfNat (n : Nat) : OfNat R n := ⟨ofQ (OfNat.ofNat n)⟩
/-- The canonical map from `Nat` to the reals. -/
instance : NatCast R := ⟨fun n => ofQ n⟩
/-- The canonical map from `Int` to the reals. -/
instance : IntCast R := ⟨fun i => ofQ i⟩

/-- Addition of reals: add representing sequences term by term. -/
def add : R → R → R :=
  Quotient.lift₂ (fun a b => mk (CauSeq.add a b))
    (fun _ _ _ _ h₁ h₂ => mk_eq_mk.2 (add_equiv h₁ h₂))

/-- Negation of reals: negate representing sequences term by term. -/
def neg : R → R :=
  Quotient.lift (fun a => mk (CauSeq.neg a)) (fun _ _ h => mk_eq_mk.2 (neg_equiv h))

/-- Multiplication of reals: multiply representing sequences term by term. -/
def mul : R → R → R :=
  Quotient.lift₂ (fun a b => mk (CauSeq.mul a b))
    (fun _ _ _ _ h₁ h₂ => mk_eq_mk.2 (mul_equiv h₁ h₂))

/-- Addition on the reals. -/
instance : Add R := ⟨add⟩
/-- Negation on the reals. -/
instance : Neg R := ⟨neg⟩
/-- Subtraction on the reals: `x − y = x + (−y)`. -/
instance : Sub R := ⟨fun x y => add x (neg y)⟩
/-- Multiplication on the reals. -/
instance : Mul R := ⟨mul⟩

/-- Natural-number powers by repeated multiplication. -/
def npow (x : R) : Nat → R
  | 0 => 1
  | n + 1 => npow x n * x

/-- Powers on the reals. -/
instance : HPow R Nat R := ⟨npow⟩

/-- Computation rule: addition on representatives. -/
@[simp] theorem mk_add (a b : CauSeq) : mk a + mk b = mk (CauSeq.add a b) := rfl
/-- Computation rule: negation on representatives. -/
@[simp] theorem mk_neg (a : CauSeq) : -mk a = mk (CauSeq.neg a) := rfl
/-- Computation rule: subtraction on representatives. -/
@[simp] theorem mk_sub (a b : CauSeq) : mk a - mk b = mk (CauSeq.add a (CauSeq.neg b)) := rfl
/-- Computation rule: multiplication on representatives. -/
@[simp] theorem mk_mul (a b : CauSeq) : mk a * mk b = mk (CauSeq.mul a b) := rfl
/-- Numerals, unfolded to a representative. -/
theorem ofNat_def (n : Nat) : (OfNat.ofNat n : R) = ofQ (OfNat.ofNat n) := rfl
/-- Zero, unfolded to a representative. -/
theorem zero_def : (0 : R) = mk (const 0) := rfl
/-- One, unfolded to a representative. -/
theorem one_def : (1 : R) = mk (const 1) := rfl

/-! ## `ofQ` is a ring homomorphism -/

/-- The embedding of the rationals preserves addition. -/
theorem ofQ_add (p q : Q) : ofQ (p + q) = ofQ p + ofQ q := rfl
/-- The embedding of the rationals preserves negation. -/
theorem ofQ_neg (p : Q) : ofQ (-p) = -ofQ p := rfl
/-- The embedding of the rationals preserves subtraction. -/
theorem ofQ_sub (p q : Q) : ofQ (p - q) = ofQ p - ofQ q := rfl
/-- The embedding of the rationals preserves multiplication. -/
theorem ofQ_mul (p q : Q) : ofQ (p * q) = ofQ p * ofQ q := rfl

/-! ## The ring laws (inherited term by term from `Q`) -/

/-- Addition of reals is associative. -/
theorem add_assoc (x y z : R) : x + y + z = x + (y + z) := by
  induction x using ind; induction y using ind; induction z using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- Addition of reals is commutative. -/
theorem add_comm (x y : R) : x + y = y + x := by
  induction x using ind; induction y using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- Zero is the additive identity of the reals. -/
theorem add_zero (x : R) : x + 0 = x := by
  induction x using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- `-x` is an additive inverse of `x` in the reals. -/
theorem neg_add_cancel (x : R) : -x + x = 0 := by
  induction x using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- Multiplication of reals is associative. -/
theorem mul_assoc (x y z : R) : x * y * z = x * (y * z) := by
  induction x using ind; induction y using ind; induction z using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- Multiplication of reals is commutative. -/
theorem mul_comm (x y : R) : x * y = y * x := by
  induction x using ind; induction y using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- One is the multiplicative identity of the reals. -/
theorem mul_one (x : R) : x * 1 = x := by
  induction x using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- One is also a left identity for multiplication of reals. -/
theorem one_mul (x : R) : 1 * x = x := by rw [mul_comm, mul_one]

/-- Zero times anything is zero, in the reals. -/
theorem zero_mul (x : R) : 0 * x = 0 := by
  induction x using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- Anything times zero is zero, in the reals. -/
theorem mul_zero (x : R) : x * 0 = 0 := by rw [mul_comm, zero_mul]

/-- Multiplication of reals distributes over addition (on the left). -/
theorem left_distrib (x y z : R) : x * (y + z) = x * y + x * z := by
  induction x using ind; induction y using ind; induction z using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- Multiplication of reals distributes over addition (on the right). -/
theorem right_distrib (x y z : R) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, left_distrib, mul_comm z x, mul_comm z y]

/-- `(-x) · y = -(x · y)`. -/
theorem neg_mul (x y : R) : -x * y = -(x * y) := by
  induction x using ind; induction y using ind
  exact mk_eq_mk.2 (equiv_of_eq fun n => by simp; grind)

/-- **ℝ is a commutative ring.** Registered with Lean's automation as a `Lean.Grind.CommRing`
(the field structure is added in `RealOrder.lean`). -/
instance instCommRing : Lean.Grind.CommRing R where
  nsmul := ⟨fun n x => (n : R) * x⟩
  zsmul := ⟨fun i x => (i : R) * x⟩
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
    show ofQ _ = ofQ _ + ofQ _
    rw [← ofQ_add]; congr 1; exact Lean.Grind.Semiring.ofNat_succ n
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i a := by
    show ofQ ((-i : Int) : Q) * a = -(ofQ (i : Q) * a)
    rw [← neg_mul, ← ofQ_neg]; congr 2
  intCast_neg i := by
    show ofQ ((-i : Int) : Q) = -ofQ (i : Q)
    rw [← ofQ_neg]; congr 1
  mul_comm := mul_comm

end R

end Foundations.Numbers
