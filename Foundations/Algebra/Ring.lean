import Foundations.Algebra.Quotient

/-!
# Rings, ideals and quotient rings

A group has one operation; the integers have two, addition and multiplication, linked by
the distributive law. The abstract notion capturing this is the **ring**, a word
introduced by David Hilbert (*Zahlring*, 1897) for systems of algebraic integers; the
axiomatic definition was given by Abraham Fraenkel (1914) and the theory was recast in
its modern form by Emmy Noether in her 1921 paper *Idealtheorie in Ringbereichen*.

The central notion of ring theory is the **ideal**, introduced by Richard Dedekind (1871)
to rescue unique factorisation in rings of algebraic integers where it fails for
elements. Kummer had spoken of "ideal numbers" — numbers that ought to exist but do not;
Dedekind's philosophical masterstroke was to replace each such phantom by a set of
actual numbers (those it would divide), just as he had replaced each real number by a
cut of rationals. An ideal plays for a ring the role a normal subgroup plays for a group:
it is exactly what one can divide out by, forming the **quotient ring** `R ⧸ I`.

We define rings and commutative rings (written additively and multiplicatively), show
that the additive structure of a ring is a commutative group in the sense of the previous
files, give the examples `ℤ` and `ℤ/nℤ = Fin n`, construct quotient rings, and prove two
landmark facts:

* `R ⧸ I` is a field if and only if `I` is a maximal ideal;
* `ℤ/nℤ` is a field if and only if `n` is prime (using Fermat's little theorem from
  `Lagrange.lean` to manufacture inverses).
-/

namespace Foundations.Algebra

universe u v

/-- **Ring.** A ring is a type with addition, multiplication, negation, `0` and `1` such
that addition makes it a commutative group, multiplication is associative with identity
`1`, and multiplication distributes over addition on both sides. -/
class Ring (R : Type u) extends Add R, Mul R, Neg R, Zero R, One R where
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  /-- Addition is commutative. -/
  add_comm : ∀ a b : R, a + b = b + a
  /-- `0` is an additive identity. -/
  zero_add : ∀ a : R, 0 + a = a
  /-- `-a` is an additive inverse of `a`. -/
  neg_add_cancel : ∀ a : R, -a + a = 0
  /-- Multiplication is associative. -/
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  /-- `1` is a left multiplicative identity. -/
  one_mul : ∀ a : R, 1 * a = a
  /-- `1` is a right multiplicative identity. -/
  mul_one : ∀ a : R, a * 1 = a
  /-- Left distributivity. -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Right distributivity. -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- **Commutative ring.** A ring in which multiplication is commutative, like `ℤ`. -/
class CommRing (R : Type u) extends Ring R where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ a b : R, a * b = b * a

namespace Ring

variable {R : Type u} [Ring R]

/-- Addition in a ring is associative (registered for the `ac_rfl` tactic). -/
instance : Std.Associative (α := R) (· + ·) := ⟨Ring.add_assoc⟩

/-- Addition in a ring is commutative (registered for the `ac_rfl` tactic). -/
instance : Std.Commutative (α := R) (· + ·) := ⟨Ring.add_comm⟩

/-- `a + 0 = a`. -/
theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

/-- `a + -a = 0`. -/
theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

/-- `-a + (a + b) = b`. -/
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

/-- `a + (-a + b) = b`. -/
theorem add_neg_cancel_left (a b : R) : a + (-a + b) = b := by
  rw [← add_assoc, add_neg_cancel, zero_add]

/-- Additive cancellation: `a + b = a + c` implies `b = c`. -/
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

/-- Uniqueness of additive inverses: if `a + b = 0` then `-a = b`. -/
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

/-- `-(-a) = a`. -/
theorem neg_neg (a : R) : -(-a) = a := neg_eq_of_add_eq_zero (neg_add_cancel a)

/-- `-0 = 0`. -/
theorem neg_zero : -(0 : R) = 0 := neg_eq_of_add_eq_zero (add_zero 0)

/-- `-(a + b) = -a + -b`. -/
theorem neg_add (a b : R) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  have : a + b + (-a + -b) = (a + -a) + (b + -b) := by ac_rfl
  rw [this, add_neg_cancel, add_neg_cancel, add_zero]

/-- `a * 0 = 0`. -/
theorem mul_zero (a : R) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← left_distrib, add_zero, add_zero]

/-- `0 * a = 0`. -/
theorem zero_mul (a : R) : 0 * a = 0 := by
  apply add_left_cancel (a := 0 * a)
  rw [← right_distrib, add_zero, add_zero]

/-- `(-a) * b = -(a * b)`. -/
theorem neg_mul (a b : R) : -a * b = -(a * b) := by
  symm; apply neg_eq_of_add_eq_zero
  rw [← right_distrib, add_neg_cancel, zero_mul]

/-- `a * (-b) = -(a * b)`. -/
theorem mul_neg (a b : R) : a * -b = -(a * b) := by
  symm; apply neg_eq_of_add_eq_zero
  rw [← left_distrib, add_neg_cancel, mul_zero]

end Ring

/-- Multiplication in a commutative ring is associative (registered for `ac_rfl`). -/
instance CommRing.instAssocMul {R : Type u} [CommRing R] : Std.Associative (α := R) (· * ·) :=
  ⟨Ring.mul_assoc⟩

/-- Multiplication in a commutative ring is commutative (registered for `ac_rfl`). -/
instance CommRing.instCommMul {R : Type u} [CommRing R] : Std.Commutative (α := R) (· * ·) :=
  ⟨CommRing.mul_comm⟩

open Ring

/-! ## The additive group of a ring -/

/-- The additive group of a ring `R`, as a type synonym so that its group operation
(written `*` in group theory) can be the ring's addition. -/
def AddGroupOf (R : Type u) : Type u := R

/-- **The additive group of a ring.** Under addition, every ring is a commutative group:
rings are groups with extra structure. -/
instance {R : Type u} [Ring R] : CommGroup (AddGroupOf R) where
  mul := fun (a b : R) => (a + b : R)
  one := (0 : R)
  inv := fun (a : R) => (-a : R)
  mul_assoc := Ring.add_assoc (R := R)
  one_mul := Ring.zero_add (R := R)
  inv_mul_cancel := Ring.neg_add_cancel (R := R)
  mul_comm := Ring.add_comm (R := R)

/-! ## Examples -/

/-- **The ring of integers** `ℤ`. -/
instance : CommRing Int where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_comm := Int.mul_comm

/-- **The ring `ℤ/nℤ`**, realised on `Fin n` with addition and multiplication modulo `n`. -/
instance instCommRingFin (n : Nat) [NeZero n] : CommRing (Fin n) where
  zero := Fin.ofNat n 0
  one := Fin.ofNat n 1
  add_assoc a b c := by grind
  add_comm a b := by grind
  zero_add a := by show Fin.ofNat n 0 + a = a; grind
  neg_add_cancel a := by show -a + a = Fin.ofNat n 0; grind
  mul_assoc a b c := by grind
  one_mul a := by
    show Fin.ofNat n 1 * a = a
    apply Fin.ext
    rw [Fin.val_mul, Fin.val_ofNat, Nat.mod_mul_mod, Nat.one_mul, Nat.mod_eq_of_lt a.isLt]
  mul_one a := by
    show a * Fin.ofNat n 1 = a
    apply Fin.ext
    rw [Fin.val_mul, Fin.val_ofNat, Nat.mul_mod_mod, Nat.mul_one, Nat.mod_eq_of_lt a.isLt]
  left_distrib a b c := by grind
  right_distrib a b c := by grind
  mul_comm a b := by grind

/-! ## Ideals -/

/-- **Ideal** (Dedekind). An ideal of a commutative ring `R` is a set containing `0`, closed
under addition and negation (so an additive subgroup), and closed under multiplication by
*arbitrary* elements of `R`: it "absorbs" multiplication. -/
structure Ideal (R : Type u) [CommRing R] where
  /-- The elements of the ideal. -/
  carrier : R → Prop
  /-- `0` is in the ideal. -/
  zero_mem : carrier 0
  /-- Closure under addition. -/
  add_mem : ∀ {a b : R}, carrier a → carrier b → carrier (a + b)
  /-- Closure under negation. -/
  neg_mem : ∀ {a : R}, carrier a → carrier (-a)
  /-- Absorption: multiples of members are members. -/
  mul_mem : ∀ (r : R) {a : R}, carrier a → carrier (r * a)

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Membership in an ideal. -/
instance : Membership R (Ideal R) := ⟨fun I x => I.carrier x⟩

/-- `-a ∈ I` iff `a ∈ I`. -/
theorem neg_mem_iff (I : Ideal R) {a : R} : -a ∈ I ↔ a ∈ I :=
  ⟨fun h => by have := I.neg_mem h; rwa [neg_neg] at this, I.neg_mem⟩

/-- Absorption on the right: `a ∈ I` implies `a * r ∈ I`. -/
theorem mul_mem_right (I : Ideal R) (r : R) {a : R} (h : a ∈ I) : a * r ∈ I := by
  rw [CommRing.mul_comm]; exact I.mul_mem r h

/-- **An ideal containing `1` is everything.** -/
theorem eq_top_of_one_mem (I : Ideal R) (h : (1 : R) ∈ I) (x : R) : x ∈ I := by
  have := I.mul_mem x h
  rwa [Ring.mul_one] at this

/-- The **zero ideal** `{0}`. -/
def bot : Ideal R where
  carrier x := x = 0
  zero_mem := rfl
  add_mem := by intro a b ha hb; show a + b = 0; rw [ha, hb, add_zero]
  neg_mem := by intro a ha; show -a = 0; rw [ha, neg_zero]
  mul_mem := by intro r a ha; show r * a = 0; rw [ha, mul_zero]

/-- The **unit ideal**: the whole ring. -/
def top : Ideal R where
  carrier _ := True
  zero_mem := trivial
  add_mem _ _ := trivial
  neg_mem _ := trivial
  mul_mem _ _ _ := trivial

/-- The **principal ideal** `(a) = {r * a | r ∈ R}` of multiples of `a`. -/
def span (a : R) : Ideal R where
  carrier x := ∃ r, x = r * a
  zero_mem := ⟨0, by rw [zero_mul]⟩
  add_mem := by
    intro x y ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by rw [hr, hs, right_distrib]⟩
  neg_mem := by
    intro x ⟨r, hr⟩
    exact ⟨-r, by rw [hr, neg_mul]⟩
  mul_mem := by
    intro s x ⟨r, hr⟩
    exact ⟨s * r, by rw [hr, Ring.mul_assoc]⟩

/-- The ideal generated by `I` together with one more element `a`:
`I + (a) = {i + r * a | i ∈ I, r ∈ R}`. -/
def adjoin (I : Ideal R) (a : R) : Ideal R where
  carrier x := ∃ i r, i ∈ I ∧ x = i + r * a
  zero_mem := ⟨0, 0, I.zero_mem, by rw [zero_mul, add_zero]⟩
  add_mem := by
    intro x y ⟨i, r, hi, hx⟩ ⟨j, s, hj, hy⟩
    refine ⟨i + j, r + s, I.add_mem hi hj, ?_⟩
    rw [hx, hy, right_distrib]; ac_rfl
  neg_mem := by
    intro x ⟨i, r, hi, hx⟩
    exact ⟨-i, -r, I.neg_mem hi, by rw [hx, neg_add, neg_mul]⟩
  mul_mem := by
    intro s x ⟨i, r, hi, hx⟩
    exact ⟨s * i, s * r, I.mul_mem s hi, by rw [hx, left_distrib, Ring.mul_assoc]⟩

/-- `I ⊆ I + (a)`. -/
theorem le_adjoin (I : Ideal R) (a : R) {x : R} (hx : x ∈ I) : x ∈ adjoin I a :=
  ⟨x, 0, hx, by rw [zero_mul, add_zero]⟩

/-- `a ∈ I + (a)`. -/
theorem mem_adjoin_self (I : Ideal R) (a : R) : a ∈ adjoin I a :=
  ⟨0, 1, I.zero_mem, by rw [Ring.one_mul, zero_add]⟩

/-- An ideal is **maximal** if it is proper (does not contain `1`) and no ideal lies strictly
between it and the whole ring: any ideal containing it and some element outside it
contains `1`. -/
def IsMaximal (I : Ideal R) : Prop :=
  (1 : R) ∉ I ∧ ∀ J : Ideal R, (∀ x, x ∈ I → x ∈ J) → (∃ a, a ∈ J ∧ a ∉ I) → (1 : R) ∈ J

end Ideal

/-- **Ring homomorphism.** A map between rings preserving addition, multiplication and `1`. -/
structure RingHom (R : Type u) (S : Type v) [Ring R] [Ring S] where
  /-- The underlying function. -/
  toFun : R → S
  /-- Preserves addition. -/
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  /-- Preserves multiplication. -/
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  /-- Preserves the identity. -/
  map_one : toFun 1 = 1

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [Ring S]

/-- A ring homomorphism sends `0` to `0`. -/
theorem map_zero (f : RingHom R S) : f.toFun 0 = 0 := by
  apply add_left_cancel (a := f.toFun 0)
  rw [← f.map_add, add_zero, add_zero]

/-- A ring homomorphism preserves negation. -/
theorem map_neg (f : RingHom R S) (a : R) : f.toFun (-a) = -(f.toFun a) := by
  symm; apply neg_eq_of_add_eq_zero
  rw [← f.map_add, add_neg_cancel, f.map_zero]

/-- **Kernels of ring homomorphisms are ideals.** -/
def ker (f : RingHom R S) : Ideal R where
  carrier x := f.toFun x = 0
  zero_mem := f.map_zero
  add_mem := by intro a b ha hb; show f.toFun (a + b) = 0; rw [f.map_add, ha, hb, add_zero]
  neg_mem := by intro a ha; show f.toFun (-a) = 0; rw [f.map_neg, ha, neg_zero]
  mul_mem := by intro r a ha; show f.toFun (r * a) = 0; rw [f.map_mul, ha, mul_zero]

end RingHom

/-! ## Quotient rings -/

section QuotientRing

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Congruence modulo an ideal: `a ≡ b (mod I)` iff `-a + b ∈ I`. An equivalence relation. -/
def Ideal.setoid : Setoid R where
  r a b := -a + b ∈ I
  iseqv := {
    refl := fun a => by show -a + a ∈ I; rw [neg_add_cancel]; exact I.zero_mem
    symm := fun {a b} h => by
      show -b + a ∈ I
      have := I.neg_mem h
      rwa [neg_add, neg_neg, Ring.add_comm] at this
    trans := fun {a b c} h1 h2 => by
      show -a + c ∈ I
      have := I.add_mem h1 h2
      rwa [Ring.add_assoc, add_neg_cancel_left] at this }

/-- **Quotient ring.** `R ⧸ I`: the classes of elements of `R` modulo the ideal `I`. -/
def QuotientRing : Type u := Quotient I.setoid

namespace QuotientRing

/-- The class of `a` modulo `I`. -/
def mk (a : R) : QuotientRing I := Quotient.mk I.setoid a

variable {I}

/-- Two classes are equal iff the difference of representatives lies in `I`. -/
theorem mk_eq_mk {a b : R} : mk I a = mk I b ↔ -a + b ∈ I :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- Addition respects congruence modulo `I`. -/
theorem add_wd {a a' b b' : R} (ha : -a + a' ∈ I) (hb : -b + b' ∈ I) :
    -(a + b) + (a' + b') ∈ I := by
  have e : -(a + b) + (a' + b') = (-a + a') + (-b + b') := by rw [neg_add]; ac_rfl
  rw [e]; exact I.add_mem ha hb

/-- Negation respects congruence modulo `I`. -/
theorem neg_wd {a a' : R} (ha : -a + a' ∈ I) : -(-a) + -a' ∈ I := by
  rw [← neg_add]; exact I.neg_mem ha

/-- Multiplication respects congruence modulo `I`: `ab ≡ a'b ≡ a'b'`. -/
theorem mul_wd {a a' b b' : R} (ha : -a + a' ∈ I) (hb : -b + b' ∈ I) :
    -(a * b) + (a' * b') ∈ I := by
  have h1 : -(a * b) + a' * b ∈ I := by
    have := I.mul_mem_right b ha
    rwa [right_distrib, neg_mul] at this
  have h2 : -(a' * b) + a' * b' ∈ I := by
    have := I.mul_mem a' hb
    rwa [left_distrib, mul_neg] at this
  have := I.add_mem h1 h2
  rwa [Ring.add_assoc, add_neg_cancel_left] at this

/-- **The quotient ring** `R ⧸ I` is a commutative ring, with operations on representatives. -/
instance : CommRing (QuotientRing I) where
  add := Quotient.lift₂ (fun a b => mk I (a + b))
    (fun _ _ _ _ ha hb => Quotient.sound (add_wd ha hb))
  mul := Quotient.lift₂ (fun a b => mk I (a * b))
    (fun _ _ _ _ ha hb => Quotient.sound (mul_wd ha hb))
  neg := Quotient.lift (fun a => mk I (-a)) (fun _ _ ha => Quotient.sound (neg_wd ha))
  zero := mk I 0
  one := mk I 1
  add_assoc a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.add_assoc _ _ _)
  add_comm a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.add_comm _ _)
  zero_add a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.zero_add _)
  neg_add_cancel a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.neg_add_cancel _)
  mul_assoc a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.mul_assoc _ _ _)
  one_mul a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.one_mul _)
  mul_one a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.mul_one _)
  left_distrib a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.left_distrib _ _ _)
  right_distrib a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Ring.right_distrib _ _ _)
  mul_comm a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact congrArg (Quotient.mk _) (CommRing.mul_comm _ _)

/-- Classes multiply representative-wise. -/
theorem mk_mul (a b : R) : mk I a * mk I b = mk I (a * b) := rfl

/-- The class of `1` is the identity. -/
theorem mk_one : mk I (1 : R) = 1 := rfl

/-- The class of `0` is zero. -/
theorem mk_zero : mk I (0 : R) = 0 := rfl

/-- The class of `a` is zero iff `a ∈ I`: the ideal is what has been "set to zero". -/
theorem mk_eq_zero {a : R} : mk I a = 0 ↔ a ∈ I := by
  rw [← mk_zero, mk_eq_mk, add_zero, Ideal.neg_mem_iff]

/-- The canonical projection `R → R ⧸ I` is a ring homomorphism with kernel `I`. -/
def proj (I : Ideal R) : RingHom R (QuotientRing I) where
  toFun := mk I
  map_add _ _ := rfl
  map_mul _ _ := rfl
  map_one := rfl

/-- **Every ideal is a kernel**: `I` is the kernel of `R → R ⧸ I`. -/
theorem ker_proj (a : R) : a ∈ (proj I).ker ↔ a ∈ I := mk_eq_zero

end QuotientRing

end QuotientRing

/-! ## Fields -/

/-- **Field.** A commutative ring is a field if `0 ≠ 1` and every non-zero element has a
multiplicative inverse. -/
def IsField (R : Type u) [CommRing R] : Prop :=
  (0 : R) ≠ 1 ∧ ∀ a : R, a ≠ 0 → ∃ b, a * b = 1

open QuotientRing in
/-- **Maximal ideals and fields.** For an ideal `I` of a commutative ring `R`, the quotient
`R ⧸ I` is a field if and only if `I` is a maximal ideal. -/
theorem quotient_isField_iff_maximal {R : Type u} [CommRing R] (I : Ideal R) :
    IsField (QuotientRing I) ↔ I.IsMaximal := by
  constructor
  · intro ⟨h01, hinv⟩
    refine ⟨fun h1 => h01 ?_, ?_⟩
    · rw [← mk_one, mk_eq_zero.2 h1]
    · intro J hIJ ⟨a, haJ, haI⟩
      have hne : mk I a ≠ 0 := fun h => haI (mk_eq_zero.1 h)
      obtain ⟨q, hq⟩ := hinv _ hne
      obtain ⟨b, rfl⟩ := Quotient.exists_rep q
      have hab : mk I (a * b) = mk I 1 := hq
      have h1 := hIJ _ (mk_eq_mk.1 hab)
      have h2 : a * b ∈ J := J.mul_mem_right b haJ
      have := J.add_mem h2 h1
      rwa [add_neg_cancel_left] at this
  · intro ⟨h1, hmax⟩
    refine ⟨fun h => h1 ?_, ?_⟩
    · have : mk I (0 : R) = mk I 1 := h
      have := mk_eq_mk.1 this
      rwa [neg_zero, zero_add] at this
    · intro q hq
      obtain ⟨a, rfl⟩ := Quotient.exists_rep q
      have haI : a ∉ I := fun h => hq (mk_eq_zero.2 h)
      have hJ := hmax (Ideal.adjoin I a) (fun x hx => Ideal.le_adjoin I a hx)
        ⟨a, Ideal.mem_adjoin_self I a, haI⟩
      obtain ⟨i, r, hi, h1eq⟩ := hJ
      refine ⟨mk I r, ?_⟩
      show mk I (a * r) = mk I 1
      apply mk_eq_mk.2
      rw [h1eq, CommRing.mul_comm a r, Ring.add_comm i, neg_add_cancel_left]
      exact hi

/-! ## `ℤ/nℤ` is a field exactly when `n` is prime -/

/-- **`ℤ/nℤ` is a field iff `n` is prime.** In `Fin n` (with arithmetic modulo `n`), every
non-zero element is invertible exactly when `n` is a prime number. For primes, the inverse
of `a` is `a ^ (p - 2)`, by Fermat's little theorem; for composite `n = d * e`, the
residue `d` is a zero divisor and cannot be invertible. -/
theorem fin_isField_iff_prime (n : Nat) [NeZero n] : IsField (Fin n) ↔ IsPrime n := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have zero_val : ((0 : Fin n)).val = 0 := Fin.val_ofNat n 0 ▸ Nat.zero_mod n
  have one_val : ((1 : Fin n)).val = 1 % n := Fin.val_ofNat n 1
  constructor
  · intro ⟨h01, hinv⟩
    have h2 : 2 ≤ n := by
      apply Classical.byContradiction
      intro hlt
      have hn1 : n = 1 := by omega
      apply h01
      apply Fin.ext
      rw [zero_val, one_val, hn1]
    refine ⟨h2, ?_⟩
    intro d hd
    apply Classical.byContradiction
    intro hne
    have hd0 : d ≠ 0 := by intro h; rw [h] at hd; exact hn0 (Nat.eq_zero_of_zero_dvd hd)
    have hdle := Nat.le_of_dvd (by omega) hd
    obtain ⟨e, he⟩ := hd
    have hd2 : 2 ≤ d := by omega
    have hdn : d < n := by omega
    have he0 : 0 < e := by
      apply Nat.pos_of_ne_zero; intro h; rw [h, Nat.mul_zero] at he; exact hn0 he
    have hen : e < n := by
      have : 2 * e ≤ d * e := Nat.mul_le_mul_right e hd2
      omega
    let a : Fin n := ⟨d, hdn⟩
    let x : Fin n := ⟨e, hen⟩
    have ha0 : a ≠ 0 := by
      intro h; have := congrArg Fin.val h; rw [zero_val] at this; exact hd0 this
    obtain ⟨b, hb⟩ := hinv a ha0
    have hxa : x * a = 0 := by
      apply Fin.ext
      rw [Fin.val_mul, zero_val]
      show e * d % n = 0
      rw [Nat.mul_comm, ← he, Nat.mod_self]
    have hx : x = 0 := by
      calc x = x * 1 := (Ring.mul_one x).symm
        _ = x * (a * b) := by rw [hb]
        _ = x * a * b := (Ring.mul_assoc x a b).symm
        _ = 0 * b := by rw [hxa]
        _ = 0 := Ring.zero_mul b
    have := congrArg Fin.val hx
    rw [zero_val] at this
    exact absurd this (by show e ≠ 0; omega)
  · intro hp
    have h2 := hp.1
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      rw [zero_val, one_val, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by omega)
    · intro a ha
      have ha0 : a.val ≠ 0 := by
        intro h; apply ha; apply Fin.ext; rw [h, zero_val]
      have hndvd : ¬ n ∣ a.val := fun h => ha0 (Nat.eq_zero_of_dvd_of_lt h a.isLt)
      refine ⟨Fin.ofNat n (a.val ^ (n - 2)), ?_⟩
      apply Fin.ext
      rw [Fin.val_mul, Fin.val_ofNat, Nat.mul_mod_mod, one_val, Nat.mod_eq_of_lt (by omega : 1 < n)]
      have : a.val * a.val ^ (n - 2) = a.val ^ (n - 1) := by
        rw [Nat.mul_comm, ← Nat.pow_succ]; congr 1; omega
      rw [this]
      exact fermat n a.val hp hndvd

end Foundations.Algebra
