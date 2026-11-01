import Foundations.Algebra.QuinticIrreducible
import Foundations.Numbers.FTA

/-!
# The complex numbers as an ambient field

The Galois theory of this Part works inside one ambient field `Ω`. To compute the Galois group
of `x⁵ - 6x + 3` we take `Ω = ℂ`, the complex numbers built in Part II. Its two key features
are the **fundamental theorem of algebra** (every non-constant polynomial has a root, so the
splitting field can be built inside `ℂ`) and **complex conjugation**, a field automorphism that
fixes exactly the real numbers.

This file connects the two parts.

* `ℂ` is a commutative ring (`C.instAlgCommRing`) and a field of characteristic zero in the sense
  of the algebra part, so its prime field `ℚ = ratField` is available.
* `C.fta'`: a polynomial of `ℂ[x]` with a non-zero coefficient beyond the constant term has a
  root. This is `C.fta` of Part II, transported from coefficient lists to polynomials.
* `conjHom`: complex conjugation is a ring homomorphism.
* `quinticPoly_eval_ofReal`: at a real number `x`, the complex polynomial `x⁵ - 6x + 3` takes
  the real value `quinticR x` of the previous files.
-/

namespace Foundations.Algebra

open Foundations.Numbers Polynomial

/-- **`ℂ` is a commutative ring** in the sense of the algebra part, with its usual operations. -/
instance C.instAlgCommRing : CommRing C where
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  zero := 0
  one := 1
  add_assoc := C.add_assoc
  add_comm := C.add_comm
  zero_add x := by rw [C.add_comm]; exact C.add_zero x
  neg_add_cancel := C.neg_add_cancel
  mul_assoc := C.mul_assoc
  one_mul := C.one_mul
  mul_one := C.mul_one
  left_distrib := C.left_distrib
  right_distrib := C.right_distrib
  mul_comm := C.mul_comm

/-- The image of a natural number in `ℂ` is the real number `n`. -/
theorem C.ncast_eq : ∀ n : Nat, (ncast n : C) = ⟨(n : R), 0⟩
  | 0 => C.ext (by show (0 : R) = ((0 : Nat) : R); grind) rfl
  | 1 => C.ext (by show (1 : R) = ((1 : Nat) : R); grind) rfl
  | n + 2 => by
    show (ncast (n + 1) : C) + 1 = _
    rw [C.ncast_eq (n + 1)]
    apply C.ext
    · show ((n + 1 : Nat) : R) + 1 = ((n + 2 : Nat) : R); grind
    · show (0 : R) + 0 = 0; grind

/-- **`ℂ` is a field.** -/
theorem C.isField : IsField C :=
  ⟨C.zero_ne_one, fun a ha => ⟨a⁻¹, C.mul_inv_cancel ha⟩⟩

/-- The image of a natural number `n + 1` in `ℂ` is non-zero. -/
theorem C.ncast_succ_ne_zero (n : Nat) : (ncast (n + 1) : C) ≠ 0 := by
  rw [C.ncast_eq]; intro h
  have : ((n + 1 : Nat) : R) = 0 := congrArg C.re h
  have : (0 : R) < ((n + 1 : Nat) : R) := by grind
  grind

/-- **`ℂ` has characteristic zero.** -/
theorem C.charZero : CharZero C := by
  intro z hz
  change (icast z : C) = 0 at hz
  match z, hz with
  | .ofNat 0, _ => rfl
  | .ofNat (n + 1), hz => exact absurd hz (C.ncast_succ_ne_zero n)
  | .negSucc n, hz =>
    change -(ncast (n + 1) : C) = 0 at hz
    exact absurd (by rw [← Ring.neg_neg (ncast (n + 1) : C), hz, Ring.neg_zero]) (C.ncast_succ_ne_zero n)

/-- The image of `3` in `ℂ`. -/
theorem C.icast_three : (@Int.cast C CommRing.toIntCast 3) = ⟨3, 0⟩ := by
  show (ncast 3 : C) = _; rw [C.ncast_eq]; apply C.ext
  · show ((3 : Nat) : R) = 3; grind
  · rfl

/-- The image of `-6` in `ℂ`. -/
theorem C.icast_neg_six : (@Int.cast C CommRing.toIntCast (-6)) = ⟨-6, 0⟩ := by
  show -(ncast 6 : C) = _; rw [C.ncast_eq]; apply C.ext
  · show -((6 : Nat) : R) = -6; grind
  · show -(0 : R) = 0; grind

/-- The prime field `ℚ ⊆ ℂ`. -/
def Qc : Subfield C := ratField C.isField C.charZero

/-! ## The fundamental theorem of algebra for `ℂ[x]` -/

/-- Horner evaluation of coefficient lists agrees in the two parts of the project. -/
theorem evalList_eq_C.peval (z : C) : ∀ l : List C, evalList z l = C.peval l z
  | [] => rfl
  | a :: l => by
    show a + z * evalList z l = a + z * C.peval l z
    rw [evalList_eq_C.peval z l]

/-- A non-zero coefficient of a list is one of its entries. -/
theorem nonZero_of_coeff {l : List C} {n : Nat} (h : PolyList.coeff l n ≠ 0) : C.NonZero l := by
  induction l generalizing n with
  | nil => exact absurd (PolyList.coeff_nil n) h
  | cons a l ih =>
    cases n with
    | zero => exact ⟨a, List.mem_cons_self, h⟩
    | succ n =>
      obtain ⟨b, hb, hb0⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem a hb, hb0⟩

/-- **The fundamental theorem of algebra, polynomial form.** A polynomial over `ℂ` with a
non-zero coefficient at some index `n ≥ 1` has a complex root. -/
theorem C.fta' (p : Polynomial C) {n : Nat} (hn : 1 ≤ n) (hp : coeff p n ≠ 0) :
    ∃ z, eval z p = 0 := by
  induction p using Quotient.ind with
  | _ l =>
    match l, n, hn, hp with
    | [], n, _, hp => exact absurd (PolyList.coeff_nil n) hp
    | c :: t, n + 1, _, hp =>
      obtain ⟨z, hz⟩ := C.fta c t (nonZero_of_coeff (l := t) (n := n) hp)
      exact ⟨z, by show evalList z (c :: t) = 0; rw [evalList_eq_C.peval]; exact hz⟩

/-! ## Complex conjugation -/

/-- **Complex conjugation is a ring homomorphism** `ℂ → ℂ`. -/
def conjHom : RingHom C C where
  toFun := C.conj
  map_add := C.conj_add
  map_mul := C.conj_mul
  map_one := by
    apply C.ext
    · rfl
    · show -(0 : R) = 0; grind

/-- Conjugation is an involution. -/
theorem conjHom_conjHom (z : C) : conjHom.toFun (conjHom.toFun z) = z := C.conj_conj z

/-- A complex number is fixed by conjugation exactly when it is real. -/
theorem conj_eq_self_iff (z : C) : C.conj z = z ↔ z.im = 0 := by
  constructor
  · intro h; have := congrArg C.im h; change -z.im = z.im at this; grind
  · intro h; apply C.ext
    · rfl
    · show -z.im = z.im; rw [h]; grind

/-! ## The quintic at real arguments -/

/-- Evaluating `x⁵ - 6x + 3` in any commutative ring. -/
theorem eval_quinticPoly {A : Type _} [CommRing A] (x : A) :
    eval x (quinticPoly A) = x * x * x * x * x + Int.cast (-6) * x + Int.cast 3 := by
  show evalList x [Int.cast 3, Int.cast (-6), 0, 0, 0, 1] = _
  simp only [evalList]
  grind

/-- **The quintic at a real argument.** For real `x`, the complex value of `x⁵ - 6x + 3` at
`x` is the real number `quinticR x`. -/
theorem quinticPoly_eval_ofReal (x : R) :
    eval (⟨x, 0⟩ : C) (quinticPoly C) = ⟨quinticR x, 0⟩ := by
  rw [eval_quinticPoly, C.icast_three, C.icast_neg_six]
  unfold quinticR
  cpx

end Foundations.Algebra
