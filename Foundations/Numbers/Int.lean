import Foundations.Numbers.Peano

/-!
# The integers as classes of pairs of naturals

In the natural numbers we can add but not always subtract: `3 - 5` has no answer. The integers
repair this, and the construction shows how mathematicians *create* new objects out of old ones
by an act of abstraction.

Think of a pair of natural numbers `(a, b)` as a *formal difference* "`a` minus `b`". Many pairs
describe the same difference: `(5, 3)`, `(7, 5)`, `(2, 0)` all mean "two". We declare two pairs
equivalent when they describe the same difference,

  `(a, b) ~ (c, d)  ↔  a + d = c + b`

(note that this definition only uses *addition* of naturals, so it makes sense before negative
numbers exist). An integer is then, by definition, an *equivalence class* of pairs: the integer
`-2` **is** the collection of all pairs `(0, 2), (1, 3), (2, 4), …`. This is Frege's and
Russell's method of *definition by abstraction*: rather than postulating a mysterious new entity
"minus two", we identify it with the class of all its representatives. In Lean this is a
`Quotient` type.

We define `0`, `1`, `+`, `−`, `×` and `≤` on representatives, check that the choice of
representative does not matter, and then prove the laws of a **commutative ring** and that `≤` is
a **linear order** compatible with addition and with multiplication by positive numbers.
Finally a **bridge theorem** identifies our integers with Lean's built-in `Int`, so that later
files may use `Int` (and the arithmetic decision procedures `omega` and `grind`) freely.

From here on we use Lean's `Nat` in place of the home-made `N` of the previous file, as licensed by
the bridge theorem `N.bridge_nat`.
-/

namespace Foundations.Numbers

/-- Two pairs of naturals are *equivalent* when they represent the same difference:
`(a, b) ~ (c, d)` iff `a + d = c + b`. -/
def IntRel (p q : Nat × Nat) : Prop := p.1 + q.2 = q.1 + p.2

/-- The relation `IntRel` is an equivalence relation (reflexive, symmetric, transitive),
so we may form the quotient. -/
instance intSetoid : Setoid (Nat × Nat) where
  r := IntRel
  iseqv := {
    refl := fun p => by simp [IntRel]
    symm := fun {p q} h => by simp only [IntRel] at *; omega
    trans := fun {p q r} h₁ h₂ => by simp only [IntRel] at *; omega }

/-- **The integers.** An integer is an equivalence class of pairs `(a, b)` of natural numbers
under "same difference"; the class of `(a, b)` stands for `a − b`. -/
def Z : Type := Quotient intSetoid

/-- Unfolding the equivalence of pairs. -/
theorem rel_iff {p q : Nat × Nat} : p ≈ q ↔ p.1 + q.2 = q.1 + p.2 := Iff.rfl

namespace Z

/-- The integer represented by the formal difference `a − b`. -/
def mk (a b : Nat) : Z := Quotient.mk intSetoid (a, b)

/-- Two formal differences give the same integer exactly when they are equivalent. -/
theorem mk_eq_mk {a b c d : Nat} : mk a b = mk c d ↔ a + d = c + b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every integer is of the form `mk a b` (induction principle for the quotient). -/
@[elab_as_elim]
theorem ind {P : Z → Prop} (h : ∀ a b, P (mk a b)) (x : Z) : P x :=
  Quotient.ind (fun p => h p.1 p.2) x

/-- Zero is the class of `(0, 0)`. -/
instance : OfNat Z 0 := ⟨mk 0 0⟩
/-- One is the class of `(1, 0)`. -/
instance : OfNat Z 1 := ⟨mk 1 0⟩

/-- Addition: `(a − b) + (c − d) = (a + c) − (b + d)`. -/
def add : Z → Z → Z :=
  Quotient.lift₂ (fun p q => mk (p.1 + q.1) (p.2 + q.2))
    (fun _ _ _ _ h₁ h₂ => by
      apply Quotient.sound
      simp only [rel_iff] at *; omega)

/-- Negation swaps the two components: `−(a − b) = b − a`. -/
def neg : Z → Z :=
  Quotient.lift (fun p => mk p.2 p.1)
    (fun _ _ h => by
      apply Quotient.sound
      simp only [rel_iff] at *; omega)

/-- Multiplication: `(a − b)(c − d) = (ac + bd) − (ad + bc)`. -/
def mul : Z → Z → Z :=
  Quotient.lift₂ (fun p q => mk (p.1 * q.1 + p.2 * q.2) (p.1 * q.2 + p.2 * q.1))
    (fun _ _ _ _ h₁ h₂ => by
      apply Quotient.sound
      simp only [rel_iff] at *; grind)

/-- Addition on the integers. -/
instance : Add Z := ⟨add⟩
/-- Negation on the integers. -/
instance : Neg Z := ⟨neg⟩
/-- Subtraction on the integers: `x − y = x + (−y)`. -/
instance : Sub Z := ⟨fun x y => add x (neg y)⟩
/-- Multiplication on the integers. -/
instance : Mul Z := ⟨mul⟩

/-- Order: `a − b ≤ c − d` iff `a + d ≤ c + b`. -/
def le : Z → Z → Prop :=
  Quotient.lift₂ (fun p q => p.1 + q.2 ≤ q.1 + p.2)
    (fun _ _ _ _ h₁ h₂ => by
      simp only [rel_iff] at *
      apply propext; omega)

/-- The order `≤` on the integers. -/
instance : LE Z := ⟨le⟩
/-- The strict order on the integers: `x < y` iff `x ≤ y` and not `y ≤ x`. -/
instance : LT Z := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩

/-- Computation rule: addition on representatives. -/
@[simp] theorem mk_add (a b c d : Nat) : mk a b + mk c d = mk (a + c) (b + d) := rfl
/-- Computation rule: negation on representatives. -/
@[simp] theorem mk_neg (a b : Nat) : -mk a b = mk b a := rfl
/-- Computation rule: subtraction on representatives. -/
@[simp] theorem mk_sub (a b c d : Nat) : mk a b - mk c d = mk (a + d) (b + c) := rfl
/-- Computation rule: multiplication on representatives. -/
@[simp] theorem mk_mul (a b c d : Nat) :
    mk a b * mk c d = mk (a * c + b * d) (a * d + b * c) := rfl
/-- Computation rule: the order on representatives. -/
@[simp] theorem mk_le (a b c d : Nat) : mk a b ≤ mk c d ↔ a + d ≤ c + b := Iff.rfl
/-- Zero, unfolded to a representative. -/
@[simp] theorem zero_def : (0 : Z) = mk 0 0 := rfl
/-- One, unfolded to a representative. -/
@[simp] theorem one_def : (1 : Z) = mk 1 0 := rfl

/-! ## The commutative ring laws -/

/-- Addition is associative. -/
theorem add_assoc (x y z : Z) : x + y + z = x + (y + z) := by
  induction x using ind; induction y using ind; induction z using ind
  simp only [mk_add, mk_eq_mk]; omega

/-- Addition is commutative. -/
theorem add_comm (x y : Z) : x + y = y + x := by
  induction x using ind; induction y using ind
  simp only [mk_add, mk_eq_mk]; omega

/-- Zero is the additive identity. -/
theorem add_zero (x : Z) : x + 0 = x := by
  induction x using ind
  simp only [zero_def, mk_add, mk_eq_mk]; omega

/-- `−x` is an additive inverse of `x`. -/
theorem neg_add_cancel (x : Z) : -x + x = 0 := by
  induction x using ind
  simp only [zero_def, mk_neg, mk_add, mk_eq_mk]; omega

/-- Subtraction is adding the negative. -/
theorem sub_eq_add_neg (x y : Z) : x - y = x + -y := rfl

/-- Multiplication is associative. -/
theorem mul_assoc (x y z : Z) : x * y * z = x * (y * z) := by
  induction x using ind; induction y using ind; induction z using ind
  simp only [mk_mul, mk_eq_mk]; grind

/-- Multiplication is commutative. -/
theorem mul_comm (x y : Z) : x * y = y * x := by
  induction x using ind; induction y using ind
  simp only [mk_mul, mk_eq_mk]; grind

/-- One is the multiplicative identity. -/
theorem mul_one (x : Z) : x * 1 = x := by
  induction x using ind
  simp only [one_def, mk_mul, mk_eq_mk]; omega

/-- Multiplication distributes over addition. -/
theorem mul_add (x y z : Z) : x * (y + z) = x * y + x * z := by
  induction x using ind; induction y using ind; induction z using ind
  simp only [mk_mul, mk_add, mk_eq_mk]; grind

/-- Zero is different from one: the ring is not trivial. -/
theorem zero_ne_one : (0 : Z) ≠ 1 := by
  simp only [zero_def, one_def, ne_eq, mk_eq_mk]; omega

/-- **ℤ is a commutative ring.** The integers satisfy all the axioms of a commutative ring
with `0 ≠ 1`. -/
theorem comm_ring :
    (∀ x y z : Z, x + y + z = x + (y + z)) ∧ (∀ x y : Z, x + y = y + x) ∧
    (∀ x : Z, x + 0 = x) ∧ (∀ x : Z, -x + x = 0) ∧
    (∀ x y z : Z, x * y * z = x * (y * z)) ∧ (∀ x y : Z, x * y = y * x) ∧
    (∀ x : Z, x * 1 = x) ∧ (∀ x y z : Z, x * (y + z) = x * y + x * z) ∧ (0 : Z) ≠ 1 :=
  ⟨add_assoc, add_comm, add_zero, neg_add_cancel, mul_assoc, mul_comm, mul_one, mul_add,
    zero_ne_one⟩

/-! ## The order -/

/-- `≤` is reflexive. -/
theorem le_refl (x : Z) : x ≤ x := by
  induction x using ind; simp

/-- `≤` is transitive. -/
theorem le_trans {x y z : Z} : x ≤ y → y ≤ z → x ≤ z := by
  induction x using ind; induction y using ind; induction z using ind
  simp only [mk_le]; omega

/-- `≤` is antisymmetric. -/
theorem le_antisymm {x y : Z} : x ≤ y → y ≤ x → x = y := by
  induction x using ind; induction y using ind
  simp only [mk_le, mk_eq_mk]; omega

/-- `≤` is total. -/
theorem le_total (x y : Z) : x ≤ y ∨ y ≤ x := by
  induction x using ind; induction y using ind
  simp only [mk_le]; omega

/-- **`≤` on ℤ is a linear order.** -/
theorem le_linear_order :
    (∀ a : Z, a ≤ a) ∧ (∀ a b c : Z, a ≤ b → b ≤ c → a ≤ c) ∧
    (∀ a b : Z, a ≤ b → b ≤ a → a = b) ∧ (∀ a b : Z, a ≤ b ∨ b ≤ a) :=
  ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩

/-- **Order is compatible with addition.** `x ≤ y → x + z ≤ y + z`. -/
theorem add_le_add_right {x y : Z} (z : Z) : x ≤ y → x + z ≤ y + z := by
  induction x using ind; induction y using ind; induction z using ind
  simp only [mk_add, mk_le]; omega

/-- **Order is compatible with multiplication by positives.**
If `0 < z` and `x ≤ y` then `z * x ≤ z * y`. -/
theorem mul_le_mul_of_pos {x y z : Z} (hz : 0 < z) : x ≤ y → z * x ≤ z * y := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  induction z using ind with | h e f => ?_
  simp only [LT.lt, zero_def, mk_le, mk_mul] at *
  intro h
  obtain ⟨k, rfl⟩ : ∃ k, e = f + k := ⟨e - f, by omega⟩
  have := Nat.mul_le_mul_left k h
  simp only [Nat.mul_add, Nat.add_mul] at *
  omega

/-! ## The bridge to Lean's `Int` -/

/-- Read off the integer `a − b` in Lean's built-in `Int`. -/
def toInt : Z → Int :=
  Quotient.lift (fun p => (p.1 : Int) - p.2)
    (fun _ _ h => by simp only [rel_iff] at h; omega)

/-- Represent a Lean integer `i` as a formal difference of two naturals. -/
def ofInt (i : Int) : Z := mk i.toNat (-i).toNat

/-- Computation rule for `toInt` on a representative. -/
@[simp] theorem toInt_mk (a b : Nat) : toInt (mk a b) = (a : Int) - b := rfl

/-- The two translations are mutually inverse. -/
def equivInt : Equiv Z Int where
  toFun := toInt
  invFun := ofInt
  left_inv := by
    intro x
    induction x using ind
    simp only [ofInt, toInt_mk, mk_eq_mk]; omega
  right_inv := by
    intro i
    simp only [ofInt, toInt_mk]; omega

/-- `toInt` preserves addition. -/
theorem toInt_add (x y : Z) : toInt (x + y) = toInt x + toInt y := by
  induction x using ind; induction y using ind
  simp only [mk_add, toInt_mk]; omega

/-- `toInt` preserves negation. -/
theorem toInt_neg (x : Z) : toInt (-x) = -toInt x := by
  induction x using ind
  simp only [mk_neg, toInt_mk]; omega

/-- `toInt` preserves multiplication. -/
theorem toInt_mul (x y : Z) : toInt (x * y) = toInt x * toInt y := by
  induction x using ind; induction y using ind
  simp only [mk_mul, toInt_mk, Int.natCast_add, Int.natCast_mul]; grind

/-- `toInt` preserves and reflects the order. -/
theorem toInt_le (x y : Z) : x ≤ y ↔ toInt x ≤ toInt y := by
  induction x using ind; induction y using ind
  simp only [mk_le, toInt_mk]; omega

/-- **Bridge theorem (ℤ).** The equivalence `Z ≃ Int` preserves `0`, `1`, addition, negation,
multiplication and order. So the integers built from pairs of naturals are the same structure as
Lean's `Int`, and we use `Int` from now on. -/
theorem bridge_int :
    equivInt.toFun 0 = 0 ∧ equivInt.toFun 1 = 1 ∧
    (∀ x y, equivInt.toFun (x + y) = equivInt.toFun x + equivInt.toFun y) ∧
    (∀ x, equivInt.toFun (-x) = -equivInt.toFun x) ∧
    (∀ x y, equivInt.toFun (x * y) = equivInt.toFun x * equivInt.toFun y) ∧
    (∀ x y, x ≤ y ↔ equivInt.toFun x ≤ equivInt.toFun y) :=
  ⟨rfl, rfl, toInt_add, toInt_neg, toInt_mul, toInt_le⟩

end Z

end Foundations.Numbers
