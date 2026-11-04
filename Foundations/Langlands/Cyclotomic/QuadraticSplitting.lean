import Foundations.Langlands.Cyclotomic.QuadraticFixed

/-!
# Frobenius in the quadratic subfield `ℚ(√p*)`: the Galois side of splitting

For an odd prime `p` the cyclotomic field `ℚ(ζ_p)` contains exactly one quadratic field,
`ℚ(√p*)` with `p* = (-1)^((p-1)/2) p` (`Quadratic.lean`, `QuadraticFixed.lean`). For a prime
`q ≠ p`, the restriction of the Frobenius `σ_q` to `ℚ(√p*)` is either the identity or the
non-trivial automorphism `√p* ↦ -√p*`. In the language of prime ideals, `q` *splits* in
`ℚ(√p*)` exactly when this restriction is trivial, and is *inert* otherwise; and, for odd `q`,
`q` splits exactly when `p*` is a square modulo `q`.

**Prime ideals are not formalised in this library.** We therefore state everything through
Frobenius: "`q` splits in `ℚ(√p*)`" is replaced by "`σ_q` fixes `ℚ(√p*)` pointwise", where
`σ_q : ζ_p ↦ ζ_p^q` is the automorphism shown to reduce to the `q`-th power map modulo `q` in
`Frobenius.lean`. The identification of this condition with splitting of the prime ideal `(q)`
is classical but is **not** proved here.

The two descriptions of the condition are:

* **Galois side, read in `(ℤ/p)ˣ`.** `σ_q` fixes `ℚ(√p*)` iff `q` is a square mod `p`, i.e.
  `(q/p) = 1` (`galAut_fixes_sqrtField_iff`): `ℚ(√p*)` is the fixed field of the squares.
* **Arithmetic side, read modulo `q`.** By Gauss's congruence `(q/p) ≡ (p*)^((q-1)/2) (mod q)`
  (`legendre_eq_pstar_pow_mod`, which is quadratic reciprocity) and Euler's criterion modulo `q`,
  `(q/p) = 1` iff `p*` is a square modulo `q`.

Together (`frobenius_fixes_sqrtField_iff_pstar_sq`): **`σ_q` fixes `ℚ(√p*)` iff `p*` is a square
modulo `q`**, for distinct odd primes `p, q`. This is the decomposition law of the quadratic field
`ℚ(√p*)`, phrased via Frobenius. In the language of the `GL(1)` dictionary (said here in prose
only): the quadratic character `(·/p)` of `(ℤ/p)ˣ` corresponds to the character of
`Gal(ℚ(ζ_p)/ℚ)` whose kernel is the subgroup fixing `ℚ(√p*)`, and its value at `σ_q` is `(q/p)`.
The prime `q = 2` is excluded: every integer is a square modulo
`2`, while `2` splits in `ℚ(√p*)` only when `p* ≡ 1 (mod 8)`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Squares modulo `q`, for integers -/

/-- An integer `a` is **a square modulo `q`**: `a ≡ x² (mod q)` for some integer `x`. -/
def IsSqMod (a : Int) (q : Nat) : Prop := ∃ x : Int, (q : Int) ∣ x * x - a

/-- Natural-number congruence is integer divisibility of the difference. -/
theorem natMod_eq_iff_dvd (m k q : Nat) : m % q = k % q ↔ (q : Int) ∣ (m : Int) - k := by
  rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.natCast_emod,
    ← Int.natCast_emod]
  exact Int.ofNat_inj.symm

/-- Congruent integers have congruent powers: `q ∣ a - b → q ∣ aᵏ - bᵏ`. -/
theorem dvd_pow_sub_pow {q a b : Int} (h : q ∣ a - b) : ∀ k : Nat, q ∣ a ^ k - b ^ k
  | 0 => ⟨0, by grind⟩
  | k + 1 => by
    obtain ⟨c, hc⟩ := h
    obtain ⟨d, hd⟩ := dvd_pow_sub_pow ⟨c, hc⟩ k
    exact ⟨a * d + b ^ k * c, by rw [Int.pow_succ, Int.pow_succ]; grind⟩

/-- Being a square modulo `q` depends only on the class modulo `q`. -/
theorem isSqMod_congr {a b : Int} {q : Nat} (h : (q : Int) ∣ a - b) :
    IsSqMod a q ↔ IsSqMod b q := by
  obtain ⟨c, hc⟩ := h
  constructor
  · rintro ⟨x, d, hd⟩; exact ⟨x, d + c, by grind⟩
  · rintro ⟨x, d, hd⟩; exact ⟨x, d - c, by grind⟩

/-- For a natural number `m`, `IsQR m q` (a square of a natural number, mod `q`) is the same as
being a square modulo `q` in the integers. -/
theorem isQR_iff_isSqMod {m q : Nat} (hq : 0 < q) : IsQR m q ↔ IsSqMod m q := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have := (natMod_eq_iff_dvd (x * x) m q).1 hx
    rwa [Int.natCast_mul] at this
  · rintro ⟨x, hx⟩
    have hq0 : (q : Int) ≠ 0 := by omega
    let y : Nat := (x % q).toNat
    have hy : (y : Int) = x % q := Int.toNat_of_nonneg (Int.emod_nonneg x hq0)
    obtain ⟨c, hc⟩ : (q : Int) ∣ x - y := by rw [hy]; exact Int.dvd_self_sub_emod
    obtain ⟨d, hd⟩ := hx
    refine ⟨y, (natMod_eq_iff_dvd (y * y) m q).2 ⟨d - c * (x + y), ?_⟩⟩
    rw [Int.natCast_mul]
    grind

/-- **Euler's criterion for integers.** For an odd prime `q` and an integer `a` not divisible by
`q`, `a^((q-1)/2) ≡ 1 (mod q)` iff `a` is a square modulo `q`. -/
theorem euler_criterion_int {q : Nat} (hq : IsPrime q) (hqo : q % 2 = 1) {a : Int}
    (ha : ¬ (q : Int) ∣ a) : (q : Int) ∣ a ^ half q - 1 ↔ IsSqMod a q := by
  classical
  have hq2 := hq.1
  have hq0 : (q : Int) ≠ 0 := by omega
  let r : Nat := (a % q).toNat
  have hr : (r : Int) = a % q := Int.toNat_of_nonneg (Int.emod_nonneg a hq0)
  have har : (q : Int) ∣ a - r := by rw [hr]; exact Int.dvd_self_sub_emod
  have hrq : ¬ q ∣ r := by
    intro h
    obtain ⟨c, hc⟩ := Int.ofNat_dvd.2 h
    obtain ⟨d, hd⟩ := har
    exact ha ⟨d + c, by grind⟩
  -- move from `a` to its residue `r`
  have hpow : (q : Int) ∣ a ^ half q - (r : Int) ^ half q := dvd_pow_sub_pow har _
  have step1 : (q : Int) ∣ a ^ half q - 1 ↔ (q : Int) ∣ (r : Int) ^ half q - 1 := by
    obtain ⟨c, hc⟩ := hpow
    constructor
    · rintro ⟨d, hd⟩; exact ⟨d - c, by grind⟩
    · rintro ⟨d, hd⟩; exact ⟨d + c, by grind⟩
  have step2 : (q : Int) ∣ (r : Int) ^ half q - 1 ↔ r ^ half q % q = 1 := by
    rw [← Int.natCast_pow, ← Int.ofNat_one, ← natMod_eq_iff_dvd,
      Nat.mod_eq_of_lt (show 1 < q by omega)]
  have step3 : r ^ half q % q = 1 ↔ IsQR r q := by
    have he := euler_criterion hq hqo hrq
    by_cases hQR : IsQR r q
    · simp only [hQR, ↓reduceIte] at he; exact ⟨fun _ => hQR, fun _ => he⟩
    · simp only [hQR, ↓reduceIte] at he; exact ⟨fun h => by omega, fun h => absurd h hQR⟩
  rw [step1, step2, step3, isQR_iff_isSqMod (by omega), isSqMod_congr har]

/-! ## Quadratic reciprocity as a statement about squares -/

section Reciprocity

variable {p q : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) (hq : IsPrime q) (hqo : q % 2 = 1)
  (hpq : p ≠ q)

include hp hq hpq in
/-- An odd prime `q ≠ p` does not divide `p* = ±p`. -/
theorem not_dvd_pstar : ¬ (q : Int) ∣ pstar p := by
  intro hd
  have : (q : Int) ∣ (p : Int) := by
    unfold pstar at hd
    rw [neg_one_pow_int] at hd
    split at hd
    · rw [Int.one_mul] at hd; exact hd
    · rw [Int.neg_one_mul] at hd; exact Int.dvd_neg.1 hd
  rcases hp.2 q (Int.ofNat_dvd.1 this) with h1 | h1
  · have := hq.1; omega
  · exact hpq h1.symm

include hp hodd hq hqo hpq in
/-- `(q/p) = 1` iff `(p*)^((q-1)/2) ≡ 1 (mod q)`, from Gauss's congruence
`(q/p) ≡ (p*)^((q-1)/2) (mod q)`. -/
theorem legendre_eq_one_iff_pstar_pow (hpq' : ¬ p ∣ q) :
    legendre q p = 1 ↔ (q : Int) ∣ (pstar p) ^ half q - 1 := by
  obtain ⟨c, hc⟩ := legendre_eq_pstar_pow_mod hp hodd hq hqo hpq
  have hq3 : 3 ≤ q := by have := hq.1; omega
  rcases legendre_cases hp hodd hpq' with ⟨hL, _⟩ | ⟨hL, _⟩
  · rw [hL] at hc
    exact ⟨fun _ => ⟨-c, by grind⟩, fun _ => hL⟩
  · rw [hL] at hc
    refine ⟨fun h => by rw [hL] at h; exact absurd h (by decide), fun ⟨d, hd⟩ => ?_⟩
    have h2 : (q : Int) ∣ ((2 : Nat) : Int) := ⟨-(c + d), by grind⟩
    have : q ≤ 2 := Nat.le_of_dvd (by decide) (Int.ofNat_dvd.1 h2)
    omega

include hp hodd hq hqo hpq in
/-- **Quadratic reciprocity, squares form.** For distinct odd primes `p, q`: `q` is a square
modulo `p` iff `p* = (-1)^((p-1)/2) p` is a square modulo `q`. -/
theorem isQR_iff_pstar_isSqMod (hpq' : ¬ p ∣ q) : IsQR q p ↔ IsSqMod (pstar p) q := by
  rw [← legendre_eq_one_iff hpq', legendre_eq_one_iff_pstar_pow hp hodd hq hqo hpq hpq',
    euler_criterion_int hq hqo (not_dvd_pstar hp hq hpq)]

/-! ## The splitting law, via Frobenius -/

include hq hqo hpq in
/-- **The decomposition law of `ℚ(√p*)`, via Frobenius.** Let `p, q` be distinct odd primes and
`σ_q : ζ_p ↦ ζ_p^q` the Frobenius automorphism of `ℚ(ζ_p)` at `q`. Then `σ_q` fixes the quadratic
subfield `ℚ(√p*)` pointwise if and only if `p* = (-1)^((p-1)/2) p` is a square modulo `q`.
(Classically: `q` splits in `ℚ(√p*)` iff `p*` is a square mod `q`. Prime ideals are not
formalised in this library, so splitting is expressed here only through `σ_q`.) -/
theorem frobenius_fixes_sqrtField_iff_pstar_sq (hpq' : ¬ p ∣ q) :
    (∀ x : cycloField hp, x.1 ∈ sqrtField hp hodd → (galAut hp hpq').toFun x = x) ↔
      IsSqMod (pstar p) q := by
  rw [galAut_fixes_sqrtField_iff hp hodd hpq', isQR_iff_pstar_isSqMod hp hodd hq hqo hpq hpq']

include hq hqo hpq in
/-- **Three faces of one condition.** For distinct odd primes `p, q`, the following are
equivalent: (i) the Frobenius `σ_q` fixes `ℚ(√p*)` pointwise; (ii) `(q/p) = 1`, i.e. `q` is a
square modulo `p`; (iii) `p*` is a square modulo `q`. Condition (i) is the Galois-side form of
"`q` splits in `ℚ(√p*)`" (prime ideals are not formalised here); (i) ⇔ (ii) is Galois theory of
`ℚ(ζ_p)`, and (ii) ⇔ (iii) is quadratic reciprocity. -/
theorem frobenius_sqrtField_tfae (hpq' : ¬ p ∣ q) :
    ((∀ x : cycloField hp, x.1 ∈ sqrtField hp hodd → (galAut hp hpq').toFun x = x) ↔
      legendre q p = 1) ∧
    (legendre q p = 1 ↔ IsSqMod (pstar p) q) := by
  refine ⟨?_, ?_⟩
  · rw [galAut_fixes_sqrtField_iff hp hodd hpq', legendre_eq_one_iff hpq']
  · rw [legendre_eq_one_iff hpq']; exact isQR_iff_pstar_isSqMod hp hodd hq hqo hpq hpq'

end Reciprocity

end Foundations.Langlands
