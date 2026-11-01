import Foundations.Numbers.Int

/-!
# The rational numbers as classes of fractions

The integers let us subtract; the rationals let us *divide*. The construction repeats the trick
used for the integers, one level up. A *fraction* is a pair `(n, d)` of integers with `d > 0`,
read as "`n` divided by `d`". Different fractions can name the same quantity — `1/2`, `2/4`,
`(-3)/(-6)` — and we declare

  `n/d ~ n'/d'  ↔  n · d' = n' · d`  ("cross-multiplication"),

which again only uses operations (here: multiplication of integers) that already exist. A
rational number **is** the class of all fractions equivalent to a given one: the number one-half
*is* the collection `{1/2, 2/4, 3/6, …}`. Every operation is defined on representatives and shown
not to depend on the choice of representative.

We prove that `Q` is an **ordered field**: the field axioms (including inverses of non-zero
elements) and an order compatible with `+` and with multiplication by positives. Having done so,
we *register* these facts with Lean's automation (`Lean.Grind.Field`, `Lean.Grind.OrderedRing`,
…), so that from then on the `grind` tactic can do routine algebra and linear inequalities in `Q`
for us. We then prove:

* the **Archimedean property**: every rational is below some natural number;
* **density**: between two rationals there is always a third;
* the **irrationality of √2**: no rational `q` satisfies `q · q = 2`.

The last fact is the ancient discovery, attributed to the Pythagoreans, that the rationals have
*gaps*. Filling those gaps is the task of the real numbers, constructed in the following files.

We use Lean's `Int` freely, as licensed by `Z.bridge_int`.
-/

namespace Foundations.Numbers

/-- A *fraction*: an integer numerator together with a positive integer denominator. -/
structure Frac where
  /-- The numerator. -/
  num : Int
  /-- The denominator. -/
  den : Int
  /-- The denominator is positive. -/
  den_pos : 0 < den

/-- Cancelling a positive factor in an equation of integers. -/
theorem int_cancel_pos {x y k : Int} (hk : 0 < k) (h : x * k = y * k) : x = y :=
  Int.eq_of_mul_eq_mul_right (by omega) h

/-- Cancelling a positive factor in an inequality of integers. -/
theorem int_le_cancel_pos {x y k : Int} (hk : 0 < k) : x * k ≤ y * k ↔ x ≤ y :=
  Int.mul_le_mul_right hk

/-- Cancelling a positive factor in a strict inequality of integers. -/
theorem int_lt_cancel_pos {x y k : Int} (hk : 0 < k) : x * k < y * k ↔ x < y :=
  ⟨fun h => Int.lt_of_mul_lt_mul_right h (by omega),
   fun h => Int.mul_lt_mul_of_pos_right h hk⟩

/-- Fractions are equivalent when they cross-multiply to the same integer:
`n/d ~ n'/d'` iff `n · d' = n' · d`. This is an equivalence relation. -/
instance fracSetoid : Setoid Frac where
  r p q := p.num * q.den = q.num * p.den
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun {p q r} h₁ h₂ => by
      apply int_cancel_pos q.den_pos
      have h₁ : p.num * q.den = q.num * p.den := h₁
      have h₂ : q.num * r.den = r.num * q.den := h₂
      grind }

/-- Unfolding the equivalence of fractions. -/
theorem frac_rel_iff {p q : Frac} : p ≈ q ↔ p.num * q.den = q.num * p.den := Iff.rfl

/-- **The rational numbers.** A rational number is an equivalence class of fractions under
cross-multiplication; the class of `n/d` is the number `n ÷ d`. -/
def Q : Type := Quotient fracSetoid

namespace Q

/-- The rational number represented by the fraction `n/d` (with `d > 0`). -/
def mk (n d : Int) (h : 0 < d) : Q := Quotient.mk fracSetoid ⟨n, d, h⟩

/-- Two fractions give the same rational number iff they cross-multiply equally. -/
theorem mk_eq_mk {a b c d : Int} {hb : 0 < b} {hd : 0 < d} :
    mk a b hb = mk c d hd ↔ a * d = c * b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every rational number is represented by some fraction. -/
@[elab_as_elim]
theorem ind {P : Q → Prop} (h : ∀ n d (hd : 0 < d), P (mk n d hd)) (x : Q) : P x :=
  Quotient.ind (fun p => h p.num p.den p.den_pos) x

/-! ## Operations -/

/-- Numerals: the natural number `n` as the fraction `n/1`. -/
instance instOfNat (n : Nat) : OfNat Q n := ⟨mk (n : Int) 1 Int.one_pos⟩
/-- The canonical map `Nat → Q`. -/
instance : NatCast Q := ⟨fun n => mk (n : Int) 1 Int.one_pos⟩
/-- The canonical map `Int → Q`, sending `i` to `i/1`. -/
instance : IntCast Q := ⟨fun i => mk i 1 Int.one_pos⟩

/-- Addition: `a/b + c/d = (a·d + c·b)/(b·d)`. -/
def add : Q → Q → Q :=
  Quotient.lift₂
    (fun p q => mk (p.num * q.den + q.num * p.den) (p.den * q.den) (Int.mul_pos p.den_pos q.den_pos))
    (fun _ _ _ _ h₁ h₂ => by
      apply Quotient.sound
      simp only [frac_rel_iff] at *; grind)

/-- Negation: `-(a/b) = (-a)/b`. -/
def neg : Q → Q :=
  Quotient.lift (fun p => mk (-p.num) p.den p.den_pos)
    (fun _ _ h => by
      apply Quotient.sound
      simp only [frac_rel_iff] at *; grind)

/-- Multiplication: `(a/b)(c/d) = (a·c)/(b·d)`. -/
def mul : Q → Q → Q :=
  Quotient.lift₂
    (fun p q => mk (p.num * q.num) (p.den * q.den) (Int.mul_pos p.den_pos q.den_pos))
    (fun _ _ _ _ h₁ h₂ => by
      apply Quotient.sound
      simp only [frac_rel_iff] at *; grind)

/-- The sign of a numerator does not depend on the representative. -/
theorem num_pos_iff {p q : Frac} (h : p ≈ q) : 0 < p.num ↔ 0 < q.num := by
  have e1 := int_lt_cancel_pos (x := 0) (y := p.num) q.den_pos
  have e2 := int_lt_cancel_pos (x := 0) (y := q.num) p.den_pos
  simp only [frac_rel_iff, Int.zero_mul] at *
  rw [← e1, ← e2, h]

/-- The inverse of a fraction: `(a/b)⁻¹ = b/a` (moving the sign to the numerator), and the
"junk value" `0⁻¹ = 0`. -/
def invFrac (p : Frac) : Q :=
  if h : 0 < p.num then mk p.den p.num h
  else if h' : p.num < 0 then mk (-p.den) (-p.num) (by omega)
  else mk 0 1 Int.one_pos

/-- Inversion of rationals, well defined on classes. -/
def inv : Q → Q :=
  Quotient.lift invFrac (fun p q h => by
    have hp := num_pos_iff h
    have hn : p.num < 0 ↔ q.num < 0 := by
      have := num_pos_iff (p := ⟨-p.num, p.den, p.den_pos⟩) (q := ⟨-q.num, q.den, q.den_pos⟩)
        (by simp only [frac_rel_iff] at *; grind)
      simp only at this; omega
    have h' : p.num * q.den = q.num * p.den := h
    unfold invFrac
    by_cases h1 : 0 < p.num
    · have h2 := hp.1 h1
      simp only [h1, h2, dite_true, mk_eq_mk]; grind
    · have h2 : ¬ 0 < q.num := fun h => h1 (hp.2 h)
      by_cases h3 : p.num < 0
      · have h4 := hn.1 h3
        simp only [h1, h2, h3, h4, dite_true, dite_false, mk_eq_mk]; grind
      · have h4 : ¬ q.num < 0 := fun h => h3 (hn.2 h)
        simp only [h1, h2, h3, h4, dite_false])

/-- Addition on the rationals. -/
instance : Add Q := ⟨add⟩
/-- Negation on the rationals. -/
instance : Neg Q := ⟨neg⟩
/-- Subtraction on the rationals: `x − y = x + (−y)`. -/
instance : Sub Q := ⟨fun x y => add x (neg y)⟩
/-- Multiplication on the rationals. -/
instance : Mul Q := ⟨mul⟩
/-- Inversion on the rationals. -/
instance : Inv Q := ⟨inv⟩
/-- Division on the rationals: `x / y = x · y⁻¹`. -/
instance : Div Q := ⟨fun x y => mul x (inv y)⟩

/-- Order: `a/b ≤ c/d` iff `a·d ≤ c·b` (denominators being positive). -/
def le : Q → Q → Prop :=
  Quotient.lift₂ (fun p q => p.num * q.den ≤ q.num * p.den)
    (fun p₁ q₁ p₂ q₂ h₁ h₂ => by
      simp only [frac_rel_iff] at *
      apply propext
      have k1 := int_le_cancel_pos (x := p₁.num * q₁.den) (y := q₁.num * p₁.den)
        (Int.mul_pos p₂.den_pos q₂.den_pos)
      have k2 := int_le_cancel_pos (x := p₂.num * q₂.den) (y := q₂.num * p₂.den)
        (Int.mul_pos p₁.den_pos q₁.den_pos)
      rw [← k1, ← k2]
      have e1 : p₁.num * q₁.den * (p₂.den * q₂.den) = p₂.num * q₂.den * (p₁.den * q₁.den) := by
        grind
      have e2 : q₁.num * p₁.den * (p₂.den * q₂.den) = q₂.num * p₂.den * (p₁.den * q₁.den) := by
        grind
      rw [e1, e2])

/-- The order `≤` on the rationals. -/
instance : LE Q := ⟨le⟩
/-- Strict order: `x < y` iff `x ≤ y` and not `y ≤ x`. -/
instance : LT Q := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩

/-- The order on `Q` is decidable (compare cross-products of representatives). -/
instance decLe : DecidableRel (fun x y : Q => x ≤ y) := fun x y =>
  Quotient.recOnSubsingleton₂ x y (fun p q =>
    inferInstanceAs (Decidable (p.num * q.den ≤ q.num * p.den)))

/-- The strict order on the rationals is decidable. -/
instance decLt : DecidableRel (fun x y : Q => x < y) := fun x y =>
  inferInstanceAs (Decidable (x ≤ y ∧ ¬ y ≤ x))

/-! ## Computation rules on representatives -/

/-- Computation rule: addition on representatives. -/
@[simp] theorem mk_add (a b c d : Int) (hb : 0 < b) (hd : 0 < d) :
    mk a b hb + mk c d hd = mk (a * d + c * b) (b * d) (Int.mul_pos hb hd) := rfl
/-- Computation rule: negation on representatives. -/
@[simp] theorem mk_neg (a b : Int) (hb : 0 < b) : -mk a b hb = mk (-a) b hb := rfl
/-- Computation rule: subtraction on representatives. -/
@[simp] theorem mk_sub (a b c d : Int) (hb : 0 < b) (hd : 0 < d) :
    mk a b hb - mk c d hd = mk (a * d + -c * b) (b * d) (Int.mul_pos hb hd) := rfl
/-- Computation rule: multiplication on representatives. -/
@[simp] theorem mk_mul (a b c d : Int) (hb : 0 < b) (hd : 0 < d) :
    mk a b hb * mk c d hd = mk (a * c) (b * d) (Int.mul_pos hb hd) := rfl
/-- Computation rule: the order on representatives. -/
@[simp] theorem mk_le (a b c d : Int) (hb : 0 < b) (hd : 0 < d) :
    mk a b hb ≤ mk c d hd ↔ a * d ≤ c * b := Iff.rfl
/-- Computation rule: the strict order on representatives. -/
@[simp] theorem mk_lt (a b c d : Int) (hb : 0 < b) (hd : 0 < d) :
    mk a b hb < mk c d hd ↔ a * d < c * b := by
  show (_ ∧ ¬ _) ↔ _
  simp only [mk_le]; omega
/-- Numerals, unfolded to a representative. -/
theorem ofNat_def (n : Nat) : (OfNat.ofNat n : Q) = mk (n : Int) 1 Int.one_pos := rfl
/-- The cast of a natural number, unfolded to a representative. -/
theorem natCast_def (n : Nat) : (n : Q) = mk (n : Int) 1 Int.one_pos := rfl
/-- The cast of an integer, unfolded to a representative. -/
theorem intCast_def (i : Int) : (i : Q) = mk i 1 Int.one_pos := rfl

/-- Unfolding the inverse on a representative. -/
theorem mk_inv (a b : Int) (hb : 0 < b) : (mk a b hb)⁻¹ = invFrac ⟨a, b, hb⟩ := rfl

/-! ## The field laws -/

/-- Addition of rationals is associative. -/
theorem add_assoc (x y z : Q) : x + y + z = x + (y + z) := by
  induction x using ind; induction y using ind; induction z using ind
  simp only [mk_add, mk_eq_mk]; grind

/-- Addition of rationals is commutative. -/
theorem add_comm (x y : Q) : x + y = y + x := by
  induction x using ind; induction y using ind
  simp only [mk_add, mk_eq_mk]; grind

/-- Zero is the additive identity of the rationals. -/
theorem add_zero (x : Q) : x + 0 = x := by
  induction x using ind
  simp only [ofNat_def, mk_add, mk_eq_mk]; grind

/-- `-x` is an additive inverse of `x` in the rationals. -/
theorem neg_add_cancel (x : Q) : -x + x = 0 := by
  induction x using ind
  simp only [ofNat_def, mk_neg, mk_add, mk_eq_mk]; grind

/-- Multiplication of rationals is associative. -/
theorem mul_assoc (x y z : Q) : x * y * z = x * (y * z) := by
  induction x using ind; induction y using ind; induction z using ind
  simp only [mk_mul, mk_eq_mk]; grind

/-- Multiplication of rationals is commutative. -/
theorem mul_comm (x y : Q) : x * y = y * x := by
  induction x using ind; induction y using ind
  simp only [mk_mul, mk_eq_mk]; grind

/-- One is the multiplicative identity of the rationals. -/
theorem mul_one (x : Q) : x * 1 = x := by
  induction x using ind
  simp only [ofNat_def, mk_mul, mk_eq_mk]; grind

/-- One is also a left identity for multiplication of rationals. -/
theorem one_mul (x : Q) : 1 * x = x := by rw [mul_comm, mul_one]

/-- Zero times anything is zero, in the rationals. -/
theorem zero_mul (x : Q) : 0 * x = 0 := by
  induction x using ind
  simp only [ofNat_def, mk_mul, mk_eq_mk]; grind

/-- Anything times zero is zero, in the rationals. -/
theorem mul_zero (x : Q) : x * 0 = 0 := by rw [mul_comm, zero_mul]

/-- Multiplication of rationals distributes over addition (on the left). -/
theorem left_distrib (x y z : Q) : x * (y + z) = x * y + x * z := by
  induction x using ind; induction y using ind; induction z using ind
  simp only [mk_mul, mk_add, mk_eq_mk]; grind

/-- Multiplication of rationals distributes over addition (on the right). -/
theorem right_distrib (x y z : Q) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, left_distrib, mul_comm z x, mul_comm z y]

/-- Zero and one are different rationals: the structure is not trivial. -/
theorem zero_ne_one : (0 : Q) ≠ 1 := by
  simp only [ofNat_def, ne_eq, mk_eq_mk]; omega

/-- The junk-value convention: the inverse of zero is zero. -/
theorem inv_zero : (0 : Q)⁻¹ = 0 := by
  simp only [ofNat_def, mk_inv, invFrac]; rfl

/-- **Inverses.** Every non-zero rational has a multiplicative inverse: `x ≠ 0 → x · x⁻¹ = 1`. -/
theorem mul_inv_cancel {x : Q} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  induction x using ind with | h n d hd => ?_
  have hn : n ≠ 0 := by
    intro h; apply hx; subst h; simp only [ofNat_def, mk_eq_mk]; omega
  rw [mk_inv]; unfold invFrac
  by_cases h1 : 0 < n
  · simp only [h1, dite_true, mk_mul, ofNat_def, mk_eq_mk]; grind
  · have h2 : n < 0 := by omega
    simp only [h1, h2, dite_true, dite_false, mk_mul, ofNat_def, mk_eq_mk]; grind

/-- The inverse of one is one. -/
theorem inv_one : (1 : Q)⁻¹ = 1 := by
  simp only [ofNat_def, mk_inv, invFrac]; rfl

/-- Inversion is an involution: `(x⁻¹)⁻¹ = x`. -/
theorem inv_inv (x : Q) : x⁻¹⁻¹ = x := by
  by_cases hx : x = 0
  · rw [hx, inv_zero, inv_zero]
  · have h1 := mul_inv_cancel hx
    have hx' : x⁻¹ ≠ 0 := by
      intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
    have h2 := mul_inv_cancel hx'
    calc x⁻¹⁻¹ = (x * x⁻¹) * x⁻¹⁻¹ := by rw [h1, one_mul]
      _ = x * (x⁻¹ * x⁻¹⁻¹) := mul_assoc _ _ _
      _ = x := by rw [h2, mul_one]

/-- `(-x) · y = -(x · y)`. -/
theorem neg_mul (x y : Q) : -x * y = -(x * y) := by
  induction x using ind; induction y using ind
  simp only [mk_mul, mk_neg, mk_eq_mk]; grind

/-- Natural-number powers, by repeated multiplication. -/
def npow (x : Q) : Nat → Q
  | 0 => 1
  | n + 1 => npow x n * x

/-- Powers on the rationals. -/
instance : HPow Q Nat Q := ⟨npow⟩

/-- Integer powers (negative powers are inverses of positive ones). -/
def zpow (x : Q) : Int → Q
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

/-- Powers on the rationals. -/
instance : HPow Q Int Q := ⟨zpow⟩

/-- **`Q` is a field.** Registered with Lean's automation as a `Lean.Grind.Field`. -/
instance instField : Lean.Grind.Field Q where
  nsmul := ⟨fun n x => (n : Q) * x⟩
  zsmul := ⟨fun i x => (i : Q) * x⟩
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
    simp only [ofNat_def, mk_add, mk_eq_mk]; omega
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i a := by
    show ((-i : Int) : Q) * a = -((i : Q) * a)
    rw [← neg_mul]; rfl
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
      | zero => show (1 : Q) = 1⁻¹; rw [inv_one]
      | succ n => rfl
    | negSucc n => show a ^ (n + 1) = ((a ^ (n + 1))⁻¹)⁻¹; rw [inv_inv]

/-! ## The order laws -/

/-- `≤` on the rationals is reflexive. -/
theorem le_refl (x : Q) : x ≤ x := by
  induction x using ind; simp

/-- `≤` on the rationals is transitive. -/
theorem le_trans {x y z : Q} : x ≤ y → y ≤ z → x ≤ z := by
  induction x using ind with | h a b hb => ?_
  induction y using ind with | h c d hd => ?_
  induction z using ind with | h e f hf => ?_
  simp only [mk_le]
  intro h1 h2
  rw [← int_le_cancel_pos hd]
  have h1' := Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hf)
  have h2' := Int.mul_le_mul_of_nonneg_right h2 (Int.le_of_lt hb)
  grind

/-- `≤` on the rationals is antisymmetric. -/
theorem le_antisymm {x y : Q} : x ≤ y → y ≤ x → x = y := by
  induction x using ind; induction y using ind
  simp only [mk_le, mk_eq_mk]; omega

/-- `≤` on the rationals is total: any two elements are comparable. -/
theorem le_total (x y : Q) : x ≤ y ∨ y ≤ x := by
  induction x using ind; induction y using ind
  simp only [mk_le]; omega

/-- Order on the rationals is compatible with addition: `x ≤ y ↔ x + z ≤ y + z`. -/
theorem add_le_add_iff {x y : Q} (z : Q) : x ≤ y ↔ x + z ≤ y + z := by
  induction x using ind with | h a b hb => ?_
  induction y using ind with | h c d hd => ?_
  induction z using ind with | h e f hf => ?_
  simp only [mk_add, mk_le]
  rw [← int_le_cancel_pos (k := f * f) (Int.mul_pos hf hf)]
  have e1 : (a * f + e * b) * (d * f) = a * d * (f * f) + e * b * d * f := by grind
  have e2 : (c * f + e * d) * (b * f) = c * b * (f * f) + e * b * d * f := by grind
  rw [e1, e2]; omega

/-- `0 < 1` in the rationals. -/
theorem zero_lt_one : (0 : Q) < 1 := by
  simp only [ofNat_def, mk_lt]; omega

/-- Multiplying a strict inequality by a positive element preserves it. -/
theorem mul_lt_mul_of_pos_left {x y z : Q} : x < y → 0 < z → z * x < z * y := by
  induction x using ind with | h a b hb => ?_
  induction y using ind with | h c d hd => ?_
  induction z using ind with | h e f hf => ?_
  simp only [ofNat_def, mk_mul, mk_lt]
  intro h1 h2
  have h3 := Int.mul_lt_mul_of_pos_right h1 (Int.mul_pos (by omega : 0 < e) hf)
  grind

/-- `≤` on the rationals is a linear order (registered for automation). -/
instance : Std.IsLinearOrder Q where
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total

/-- `<` on the rationals agrees with `≤` (registered for automation). -/
instance : Std.LawfulOrderLT Q where
  lt_iff _ _ := Iff.rfl

/-- The order on the rationals is compatible with addition (registered for automation). -/
instance : Lean.Grind.OrderedAdd Q where
  add_le_left_iff := add_le_add_iff

/-- **`Q` is an ordered field.** Registered with Lean's automation as a strict ordered ring
(together with the field instance above): addition and multiplication by positives preserve
the order, and `0 < 1`. -/
instance instOrderedRing : Lean.Grind.OrderedRing Q where
  zero_lt_one := zero_lt_one
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right {a b c} h hz := by
    have := mul_lt_mul_of_pos_left h hz
    rwa [mul_comm c a, mul_comm c b] at this

/-- **`Q` is an ordered field (summary).** The field laws hold, and `≤` is a linear order
compatible with addition and with multiplication by positive elements. -/
theorem ordered_field :
    (∀ x y z : Q, x + y + z = x + (y + z)) ∧ (∀ x y : Q, x + y = y + x) ∧
    (∀ x : Q, x + 0 = x) ∧ (∀ x : Q, -x + x = 0) ∧
    (∀ x y z : Q, x * y * z = x * (y * z)) ∧ (∀ x y : Q, x * y = y * x) ∧
    (∀ x : Q, x * 1 = x) ∧ (∀ x y z : Q, x * (y + z) = x * y + x * z) ∧ (0 : Q) ≠ 1 ∧
    (∀ x : Q, x ≠ 0 → x * x⁻¹ = 1) ∧
    (∀ x y z : Q, x ≤ y → y ≤ z → x ≤ z) ∧ (∀ x y : Q, x ≤ y → y ≤ x → x = y) ∧
    (∀ x y : Q, x ≤ y ∨ y ≤ x) ∧ (∀ x y z : Q, x ≤ y → x + z ≤ y + z) ∧
    (∀ x y z : Q, x < y → 0 < z → z * x < z * y) :=
  ⟨add_assoc, add_comm, add_zero, neg_add_cancel, mul_assoc, mul_comm, mul_one, left_distrib,
    zero_ne_one, fun _ => mul_inv_cancel, fun _ _ _ => le_trans, fun _ _ => le_antisymm,
    le_total, fun _ _ z => (add_le_add_iff z).1, fun _ _ _ => mul_lt_mul_of_pos_left⟩

/-! ## Archimedes, density, and the irrationality of √2 -/

/-- **Archimedean property of ℚ.** Every rational number is smaller than some natural number. -/
theorem archimedean (x : Q) : ∃ n : Nat, x < (n : Q) := by
  induction x using ind with | h a b hb => ?_
  refine ⟨a.toNat + 1, ?_⟩
  simp only [natCast_def, mk_lt]
  have : ((a.toNat + 1 : Nat) : Int) * 1 ≤ ((a.toNat + 1 : Nat) : Int) * b :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  omega

/-- **Density of ℚ.** Between any two distinct rationals lies a third. -/
theorem density {x y : Q} (h : x < y) : ∃ z, x < z ∧ z < y :=
  ⟨(x + y) / 2, by grind, by grind⟩

/-- No natural number squared is twice a positive square (the arithmetic heart of the
irrationality of √2, proved by Fermat's infinite descent). -/
theorem nat_sq_ne_two_sq : ∀ b : Nat, 0 < b → ∀ a : Nat, a * a ≠ 2 * (b * b) := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro hb a h
    obtain ⟨c, hc | hc⟩ : ∃ c, a = 2 * c ∨ a = 2 * c + 1 := ⟨a / 2, by omega⟩
    · subst hc
      have h' : b * b = 2 * (c * c) := by grind
      obtain ⟨e, he | he⟩ : ∃ e, b = 2 * e ∨ b = 2 * e + 1 := ⟨b / 2, by omega⟩
      · subst he
        exact ih e (by omega) (by omega) c (by grind)
      · subst he; grind
    · subst hc; grind

/-- **Irrationality of √2.** There is no rational number whose square is `2`. -/
theorem sqrt_two_irrational : ¬ ∃ q : Q, q * q = 2 := by
  rintro ⟨q, hq⟩
  induction q using ind with | h n d hd => ?_
  simp only [mk_mul, ofNat_def, mk_eq_mk] at hq
  have hq' : n * n = 2 * (d * d) := by grind
  have h1 : (n * n).natAbs = (2 * (d * d)).natAbs := by rw [hq']
  simp only [Int.natAbs_mul] at h1
  exact nat_sq_ne_two_sq d.natAbs (by omega) n.natAbs h1

end Q

end Foundations.Numbers
