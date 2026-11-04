import Foundations.Langlands.Padic.Units

/-!
# The field ℚₚ of `p`-adic numbers

Since every nonzero `p`-adic integer is `pᵛ · u` with `u` a unit (`Units`), the only element of
ℤₚ that needs inverting to obtain a field is `p` itself. So we build

  `ℚₚ = ℤₚ[1/p]`,

the `p`-adic numbers, as formal quotients `x / pᵏ` (`x ∈ ℤₚ`, `k ∈ ℕ`), identifying `x / pᵏ`
with `y / pˡ` when `pˡ x = pᵏ y`. This is the same construction as ℚ from ℤ (fractions modulo
cross-multiplication), with denominators restricted to powers of `p`; transitivity of the
identification uses that ℤₚ has no zero divisors. A `p`-adic number is thus a "Laurent series in
`p`" with finitely many negative powers — Hensel's analogue of a meromorphic function germ.

We prove that ℚₚ is a commutative ring and then a **field**, registered with `grind` as a
`Lean.Grind.Field`. The inverse of `pᵛ u / pᵏ` is `pᵏ u⁻¹ / pᵛ`.

Primality of `p` is supplied by the class `PrimeP p`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- The hypothesis that `p` is prime, as a class (so that `ℚₚ` can be a type with instances). -/
class PrimeP (p : Nat) : Prop where
  /-- `p` is prime. -/
  prime : Prime p

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- Powers of `p` are nonzero in `ℤₚ`. -/
theorem pow_ne_zero (k : Nat) : (p : Zp p) ^ k ≠ 0 := by
  have h := Zp.pow_mul_unit_ne_zero hP.prime k (u := 1) (fun h0 => by
    have := Zp.modPow_mk.1 h0
    change (p : Int) ^ 1 ∣ 1 - 0 at this
    rw [Int.pow_one, Int.sub_zero] at this
    have := Int.eq_one_of_dvd_one (by omega) this; have := hP.prime.1; omega)
  rwa [Semiring.mul_one] at h

/-- Cancelling a power of `p` in `ℤₚ`. -/
theorem cancel_pow {k : Nat} {a b : Zp p} (h : (p : Zp p) ^ k * a = (p : Zp p) ^ k * b) :
    a = b := Zp.mul_left_cancel hP.prime (pow_ne_zero k) h

/-- `x / pᵏ ~ y / pˡ` iff `pˡ x = pᵏ y`. -/
instance setoid (p : Nat) [PrimeP p] : Setoid (Zp p × Nat) where
  r a b := (p : Zp p) ^ b.2 * a.1 = (p : Zp p) ^ a.2 * b.1
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun {a b c} h₁ h₂ => by
      apply cancel_pow (k := b.2)
      have h₁ : (p : Zp p) ^ b.2 * a.1 = (p : Zp p) ^ a.2 * b.1 := h₁
      have h₂ : (p : Zp p) ^ c.2 * b.1 = (p : Zp p) ^ b.2 * c.1 := h₂
      grind }

end Qp

/-- **The `p`-adic numbers** `ℚₚ = ℤₚ[1/p]`: classes of formal quotients `x / pᵏ`. -/
def Qp (p : Nat) [PrimeP p] : Type := Quotient (Qp.setoid p)

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- The `p`-adic number `x / pᵏ`. -/
def mk (x : Zp p) (k : Nat) : Qp p := Quotient.mk _ (x, k)

/-- Every `p`-adic number is some `x / pᵏ`. -/
@[elab_as_elim]
theorem ind {P : Qp p → Prop} (h : ∀ x k, P (mk x k)) (q : Qp p) : P q :=
  Quotient.ind (fun a => h a.1 a.2) q

/-- Equality of quotients. -/
theorem mk_eq_mk {x y : Zp p} {k l : Nat} :
    mk x k = mk y l ↔ (p : Zp p) ^ l * x = (p : Zp p) ^ k * y :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

instance : Zero (Qp p) := ⟨mk 0 0⟩
instance : One (Qp p) := ⟨mk 1 0⟩
instance : NatCast (Qp p) := ⟨fun n => mk n 0⟩
instance : IntCast (Qp p) := ⟨fun i => mk i 0⟩
instance (n : Nat) : OfNat (Qp p) n := ⟨mk n 0⟩

/-- Addition: `x/pᵏ + y/pˡ = (pˡ x + pᵏ y) / pᵏ⁺ˡ`. -/
instance : Add (Qp p) := ⟨Quotient.lift₂
  (fun a b => mk ((p : Zp p) ^ b.2 * a.1 + (p : Zp p) ^ a.2 * b.1) (a.2 + b.2))
  fun a₁ b₁ a₂ b₂ (h₁ : (p : Zp p) ^ a₂.2 * a₁.1 = (p : Zp p) ^ a₁.2 * a₂.1)
    (h₂ : (p : Zp p) ^ b₂.2 * b₁.1 = (p : Zp p) ^ b₁.2 * b₂.1) => mk_eq_mk.2 (by
    simp only [Semiring.pow_add]; grind)⟩

/-- Negation. -/
instance : Neg (Qp p) := ⟨Quotient.lift (fun a => mk (-a.1) a.2)
  fun a b (h : (p : Zp p) ^ b.2 * a.1 = (p : Zp p) ^ a.2 * b.1) => mk_eq_mk.2 (by grind)⟩

/-- Subtraction. -/
instance : Sub (Qp p) := ⟨fun x y => x + -y⟩

/-- Multiplication: `(x/pᵏ)(y/pˡ) = xy / pᵏ⁺ˡ`. -/
instance : Mul (Qp p) := ⟨Quotient.lift₂ (fun a b => mk (a.1 * b.1) (a.2 + b.2))
  fun a₁ b₁ a₂ b₂ (h₁ : (p : Zp p) ^ a₂.2 * a₁.1 = (p : Zp p) ^ a₁.2 * a₂.1)
    (h₂ : (p : Zp p) ^ b₂.2 * b₁.1 = (p : Zp p) ^ b₁.2 * b₂.1) => mk_eq_mk.2 (by
    simp only [Semiring.pow_add]; grind)⟩

/-- Natural powers. -/
def npow (x : Qp p) : Nat → Qp p
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow (Qp p) Nat (Qp p) := ⟨npow⟩

/-- Computation rule for addition. -/
theorem mk_add (x y : Zp p) (k l : Nat) :
    mk x k + mk y l = mk ((p : Zp p) ^ l * x + (p : Zp p) ^ k * y) (k + l) := rfl
/-- Computation rule for negation. -/
theorem mk_neg (x : Zp p) (k : Nat) : -mk x k = mk (-x) k := rfl
/-- Computation rule for multiplication. -/
theorem mk_mul (x y : Zp p) (k l : Nat) : mk x k * mk y l = mk (x * y) (k + l) := rfl

/-- Proving an equation of representatives after expanding powers of sums. -/
macro "qp_ring" : tactic =>
  `(tactic| (apply mk_eq_mk.2; (try simp only [Semiring.pow_add, Semiring.pow_zero]); grind))

/-- **ℚₚ is a commutative ring**, registered as a `Lean.Grind.CommRing`. -/
instance instCommRing : Lean.Grind.CommRing (Qp p) where
  nsmul := ⟨fun n x => (n : Qp p) * x⟩
  zsmul := ⟨fun i x => (i : Qp p) * x⟩
  add_zero x := by induction x using ind; show mk _ _ = _; qp_ring
  add_comm x y := by induction x using ind; induction y using ind; show mk _ _ = mk _ _; qp_ring
  add_assoc x y z := by
    induction x using ind; induction y using ind; induction z using ind
    show mk _ _ = mk _ _; qp_ring
  mul_assoc x y z := by
    induction x using ind; induction y using ind; induction z using ind
    show mk _ _ = mk _ _; qp_ring
  mul_one x := by induction x using ind; show mk _ _ = _; qp_ring
  one_mul x := by induction x using ind; show mk _ _ = _; qp_ring
  left_distrib x y z := by
    induction x using ind; induction y using ind; induction z using ind
    show mk _ _ = mk _ _; qp_ring
  right_distrib x y z := by
    induction x using ind; induction y using ind; induction z using ind
    show mk _ _ = mk _ _; qp_ring
  zero_mul x := by induction x using ind; show mk _ _ = _; qp_ring
  mul_zero x := by induction x using ind; show mk _ _ = _; qp_ring
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    show mk _ 0 = mk _ (0 + 0)
    apply mk_eq_mk.2
    show (p : Zp p) ^ (0 + 0) * ((n + 1 : Nat) : Zp p) = (p : Zp p) ^ 0 *
      ((p : Zp p) ^ 0 * (n : Zp p) + (p : Zp p) ^ 0 * 1)
    simp only [Semiring.pow_zero]; grind
  neg_add_cancel x := by induction x using ind; show mk _ _ = _; qp_ring
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i x := by
    induction x using ind
    show mk _ _ = mk _ _
    apply mk_eq_mk.2
    rw [Lean.Grind.Ring.intCast_neg]; grind
  intCast_neg i := by
    show mk _ 0 = mk _ 0
    rw [Lean.Grind.Ring.intCast_neg]
  mul_comm x y := by induction x using ind; induction y using ind; show mk _ _ = mk _ _; qp_ring

/-- `x / pᵏ = 0` iff `x = 0`. -/
theorem mk_eq_zero {x : Zp p} {k : Nat} : mk x k = 0 ↔ x = 0 := by
  show mk x k = mk 0 0 ↔ _
  rw [mk_eq_mk]; simp only [Semiring.pow_zero, Semiring.one_mul, Semiring.mul_zero]

/-- `0 ≠ 1` in `ℚₚ`. -/
theorem zero_ne_one : (0 : Qp p) ≠ 1 := fun h => by
  have := mk_eq_mk.1 h
  simp only [Semiring.pow_zero, Semiring.one_mul] at this
  exact Zp.one_ne_zero hP.prime.1 this.symm

/-- Every nonzero `p`-adic number has an inverse. -/
theorem exists_inv {q : Qp p} (hq : q ≠ 0) : ∃ r, q * r = 1 := by
  induction q using ind with | h x k => ?_
  have hx : x ≠ 0 := fun h => hq (mk_eq_zero.2 h)
  obtain ⟨v, u, hu, rfl⟩ := Zp.eq_pow_mul_unit hP.prime hx
  obtain ⟨u', hu'⟩ := (Zp.isUnit_iff hP.prime u).2 hu
  refine ⟨mk ((p : Zp p) ^ k * u') v, ?_⟩
  show mk _ _ = mk 1 0
  apply mk_eq_mk.2
  simp only [Semiring.pow_add, Semiring.pow_zero]
  grind

/-- The inverse: a choice of `r` with `q r = 1` (and `0⁻¹ = 0`). -/
noncomputable def inv (q : Qp p) : Qp p :=
  open Classical in if h : ∃ r, q * r = 1 then Classical.choose h else 0

noncomputable instance : Inv (Qp p) := ⟨inv⟩
noncomputable instance : Div (Qp p) := ⟨fun x y => x * y⁻¹⟩

/-- `q · q⁻¹ = 1` for `q ≠ 0`. -/
theorem mul_inv_cancel {q : Qp p} (hq : q ≠ 0) : q * q⁻¹ = 1 := by
  have h := exists_inv hq
  show q * inv q = 1
  unfold inv; rw [dite_eq_left_of_eq_true (eq_true h)]; exact Classical.choose_spec h

/-- `0⁻¹ = 0`. -/
theorem inv_zero : (0 : Qp p)⁻¹ = 0 := by
  show inv 0 = 0
  unfold inv
  have h : ¬ ∃ r, (0 : Qp p) * r = 1 := by
    rintro ⟨r, hr⟩
    exact zero_ne_one (by rw [← hr]; grind)
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- `(q⁻¹)⁻¹ = q`. -/
theorem inv_inv (q : Qp p) : q⁻¹⁻¹ = q := by
  by_cases hq : q = 0
  · rw [hq, inv_zero, inv_zero]
  · have h1 := mul_inv_cancel hq
    have hq' : q⁻¹ ≠ 0 := fun h => zero_ne_one (by rw [← h1, h]; grind)
    have h2 := mul_inv_cancel hq'
    calc q⁻¹⁻¹ = (q * q⁻¹) * q⁻¹⁻¹ := by rw [h1]; grind
      _ = q * (q⁻¹ * q⁻¹⁻¹) := by grind
      _ = q := by rw [h2]; grind

/-- `1⁻¹ = 1`. -/
theorem inv_one : (1 : Qp p)⁻¹ = 1 := by
  have h := mul_inv_cancel (q := (1 : Qp p)) (fun h => zero_ne_one h.symm)
  grind

/-- Integer powers on `ℚₚ`. -/
noncomputable def zpow (x : Qp p) : Int → Qp p
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

noncomputable instance : HPow (Qp p) Int (Qp p) := ⟨zpow⟩

/-- **ℚₚ is a field.** Registered with Lean's automation as a `Lean.Grind.Field`. -/
noncomputable instance instField : Field (Qp p) :=
  { instCommRing with
    inv := inv
    div := fun x y => x * inv y
    div_eq_mul_inv := fun _ _ => rfl
    zero_ne_one := zero_ne_one
    inv_zero := inv_zero
    mul_inv_cancel := mul_inv_cancel
    zpow_zero := fun _ => rfl
    zpow_succ := fun _ _ => rfl
    zpow_neg := fun a n => by
      cases n with
      | ofNat n =>
        cases n with
        | zero => show (1 : Qp p) = 1⁻¹; rw [inv_one]
        | succ n => rfl
      | negSucc n => show a ^ (n + 1) = ((a ^ (n + 1))⁻¹)⁻¹; rw [inv_inv] }

/-! ## ℤₚ inside ℚₚ -/

/-- The inclusion `ℤₚ → ℚₚ`, `x ↦ x / 1`. -/
def ofZp (x : Zp p) : Qp p := mk x 0

/-- The inclusion `ℤₚ → ℚₚ` is injective. -/
theorem ofZp_injective {x y : Zp p} (h : ofZp x = ofZp y) : x = y := by
  have := mk_eq_mk.1 h; simp only [Semiring.pow_zero, Semiring.one_mul] at this; exact this

/-- The inclusion `ℤₚ → ℚₚ` preserves addition. -/
theorem ofZp_add (x y : Zp p) : ofZp (x + y) = ofZp x + ofZp y := by
  unfold ofZp; rw [mk_add]; qp_ring

/-- The inclusion `ℤₚ → ℚₚ` preserves multiplication. -/
theorem ofZp_mul (x y : Zp p) : ofZp (x * y) = ofZp x * ofZp y := by
  unfold ofZp; rw [mk_mul]

/-- `x / pᵏ = x · (1/p)ᵏ`: every `p`-adic number is a `p`-adic integer divided by a power
of `p`. -/
theorem mk_eq_div (x : Zp p) (k : Nat) : mk x k = ofZp x / ofZp ((p : Zp p) ^ k) := by
  have hne : ofZp ((p : Zp p) ^ k) ≠ 0 := fun h => pow_ne_zero (p := p) k (mk_eq_zero.1 h)
  have : mk x k * ofZp ((p : Zp p) ^ k) = ofZp x := by
    unfold ofZp; rw [mk_mul]; qp_ring
  rw [← this]
  have := Field.mul_inv_cancel hne
  show _ = _ * _⁻¹
  grind

end Qp

end Foundations.Langlands.Padic
