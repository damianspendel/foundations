import Foundations.Algebra.Lagrange

/-!
# The prime field `𝔽_p` as a `Lean.Grind.Field`

To speak of an elliptic curve *over* `𝔽_p` we need `𝔽_p = ℤ/pℤ` as a field in the sense used by
`Weierstrass` (a `Lean.Grind.Field`). Lean's core library already makes `Fin n` a
`Lean.Grind.CommRing` (arithmetic modulo `n`); the algebra part of this library proves
**Fermat's little theorem** (`Foundations.Algebra.fermat`). Here we combine the two: for a
prime `p`, the inverse of `a ≠ 0` is `a ^ (p − 2)`, and `a · a^(p−2) = a^(p−1) = 1`.

The type `Fp p` is `Fin p` with this extra structure; its arithmetic is computable, so finite
questions about curves over `𝔽_p` can be settled by `decide` (see `PointCount`).
-/

namespace Foundations.Langlands.Elliptic

open Foundations.Algebra

/-- A natural number `p` together with a proof that it is prime, as a type-class argument. -/
class PrimeNat (p : Nat) : Prop where
  /-- The proof that `p` is prime. -/
  prime : IsPrime p

/-- **The prime field `𝔽_p`.** The residues `0, 1, …, p − 1` modulo `p`, i.e. `Fin p`. -/
def Fp (p : Nat) : Type := Fin p

namespace Fp

variable {p : Nat} [hp : PrimeNat p]

/-- A prime is nonzero, so `Fin p` is inhabited and carries Lean's `CommRing` structure. -/
instance instNeZero : NeZero p := ⟨by have := hp.prime.1; omega⟩

/-- `𝔽_p` is a commutative ring (inherited from Lean's ring structure on `Fin p`). -/
instance instCommRing : Lean.Grind.CommRing (Fp p) := inferInstanceAs (Lean.Grind.CommRing (Fin p))

/-- Equality in `𝔽_p` is decidable. -/
instance instDecEq : DecidableEq (Fp p) := inferInstanceAs (DecidableEq (Fin p))

/-- The residue of a natural number modulo `p`. -/
def ofNat (n : Nat) : Fp p := Fin.ofNat p n

/-- The underlying residue `0 ≤ a < p`. -/
def val (a : Fp p) : Nat := Fin.val (n := p) a

/-- Inversion in `𝔽_p`: `0⁻¹ = 0` and `a⁻¹ = a^(p−2)` otherwise. -/
instance instInv : Inv (Fp p) := ⟨fun a => if a = 0 then 0 else a ^ (p - 2)⟩

/-- Division in `𝔽_p` is multiplication by the inverse. -/
instance instDiv : Div (Fp p) := ⟨fun a b => a * b⁻¹⟩

/-- Unfolding the inverse. -/
theorem inv_def (a : Fp p) : a⁻¹ = if a = 0 then 0 else a ^ (p - 2) := rfl

/-- The inverse of zero is zero. -/
theorem inv_zero : (0 : Fp p)⁻¹ = 0 := by rw [inv_def]; simp

/-- `0 ≠ 1` in `𝔽_p`, since `p ≥ 2`. -/
theorem zero_ne_one : (0 : Fp p) ≠ 1 := by
  intro h
  have h2 := hp.prime.1
  have := congrArg (Fin.val (n := p)) h
  have e0 : Fin.val (n := p) (0 : Fin p) = 0 := Fin.val_ofNat p 0 ▸ Nat.zero_mod p
  have e1' : Fin.val (n := p) (1 : Fin p) = 1 % p := Fin.val_ofNat p 1
  have e1 : Fin.val (n := p) (1 : Fin p) = 1 := by
    rw [e1']; exact Nat.mod_eq_of_lt (by omega)
  change Fin.val (n := p) (0 : Fin p) = Fin.val (n := p) (1 : Fin p) at this
  omega

/-- Fermat's little theorem in `Fin p`: `a · a^(p−2) = 1` for `a ≠ 0`. -/
theorem fin_mul_pow {a : Fin p} (ha : a ≠ 0) : a * a ^ (p - 2) = 1 := by
  have h2 := hp.prime.1
  have hval : (Fin.val (n := p) a) ≠ 0 := by
    intro h; apply ha; exact Fin.ext (by rw [h]; rfl)
  have hnd : ¬ p ∣ Fin.val (n := p) a := fun h =>
    hval (Nat.eq_zero_of_dvd_of_lt h (Fin.isLt (n := p) a))
  have hf := fermat p (Fin.val (n := p) a) hp.prime hnd
  have e1' : Fin.val (n := p) (1 : Fin p) = 1 % p := Fin.val_ofNat p 1
  apply Fin.ext
  rw [Fin.val_mul, Fin.val_pow, Nat.mul_mod_mod, e1', Nat.mod_eq_of_lt (by omega : 1 < p)]
  rw [← Nat.pow_succ', show (p - 2).succ = p - 1 by omega, hf]

/-- **Inverses in `𝔽_p`, by Fermat's little theorem.** If `a ≠ 0` then `a · a^(p−2) = 1`. -/
theorem mul_inv_cancel {a : Fp p} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_def]; simp only [ha, ite_false]
  exact fin_mul_pow (p := p) ha

/-- Inverses are unique, so inversion is an involution. -/
theorem inv_inv (a : Fp p) : a⁻¹⁻¹ = a := by
  by_cases ha : a = 0
  · rw [ha, inv_zero, inv_zero]
  · have h1 := mul_inv_cancel ha
    have ha' : a⁻¹ ≠ 0 := by
      intro h; rw [h, Lean.Grind.Semiring.mul_zero] at h1; exact zero_ne_one h1
    have h2 := mul_inv_cancel ha'
    calc a⁻¹⁻¹ = (a * a⁻¹) * a⁻¹⁻¹ := by rw [h1, Lean.Grind.Semiring.one_mul]
      _ = a * (a⁻¹ * a⁻¹⁻¹) := Lean.Grind.Semiring.mul_assoc _ _ _
      _ = a := by rw [h2, Lean.Grind.Semiring.mul_one]

/-- The inverse of one is one. -/
theorem inv_one : (1 : Fp p)⁻¹ = 1 := by
  have h := mul_inv_cancel (zero_ne_one (p := p)).symm
  rwa [Lean.Grind.Semiring.one_mul] at h

/-- Integer powers in `𝔽_p` (negative powers are inverses of positive ones). -/
def zpow (a : Fp p) : Int → Fp p
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

/-- Integer powers in `𝔽_p`. -/
instance instZPow : HPow (Fp p) Int (Fp p) := ⟨zpow⟩

/-- **`𝔽_p` is a field.** Registered with Lean's automation as a `Lean.Grind.Field`. -/
instance instField : Lean.Grind.Field (Fp p) where
  div_eq_mul_inv _ _ := rfl
  zero_ne_one := zero_ne_one
  inv_zero := inv_zero
  mul_inv_cancel := mul_inv_cancel
  zpow_zero a := Lean.Grind.Semiring.pow_zero (α := Fp p) a
  zpow_succ a n := Lean.Grind.Semiring.pow_succ (α := Fp p) a n
  zpow_neg a n := by
    cases n with
    | ofNat n =>
      cases n with
      | zero =>
        show (a ^ (0 : Nat) : Fp p) = (a ^ (0 : Nat))⁻¹
        rw [Lean.Grind.Semiring.pow_zero, inv_one]
      | succ n => rfl
    | negSucc n => show a ^ (n + 1) = ((a ^ (n + 1))⁻¹)⁻¹; rw [inv_inv]

end Fp

end Foundations.Langlands.Elliptic
