import Foundations.Langlands.Padic.Hilbert2Bilinear

/-!
# Local Hilbert symbols of rational numbers

This file collects, for rational arguments, the local facts needed for Hilbert's product
formula, at every place `v` of ℚ (the primes, through `hilbertAt`, and `∞`, through
`hilbertInfQ`):

* **bilinearity** at every place: `hilbertAt_mul_left` (odd primes by `Qp.hilbert_mul_left`,
  `ℓ = 2` by `Qp.hilbert_mul_left_two`) and `hilbertInfQ_mul_left` (signs), for non-zero
  arguments; symmetry and invariance under square classes;
* `(a, a)_v = (a, −1)_v` (`hilbertAt_self`, `hilbertInfQ_self`), from `(a, b) = (a, −ab)`;
* the values on the generators `−1`, `2`, `p` of ℚˣ:
  - at an odd prime `ℓ`, two integers prime to `ℓ` have symbol `1` (`hilbertAt_int_units`);
  - at an odd prime `p`, `(−1, p)ₚ = (−1)^((p−1)/2)` (`hilbertAt_neg_one_self`, first
    supplement) and `(2, p)ₚ = (2/p) = (−1)^((p²−1)/8)` (`hilbertAt_two_self`, second
    supplement);
  - at `2`, the symbols of odd integers and of `2` from the table `table2`
    (`hilbertAt_two_units_int`, `hilbertAt_two_int_two`).
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-! ## Rationals in ℚₚ -/

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- `ofQ 0 = 0`. -/
theorem ofQ_zero : ofQ (p := p) 0 = 0 := by
  have h := ofQ_add (p := p) 0 0
  rw [show (0 : Q) + 0 = 0 by grind] at h
  grind

/-- A non-zero rational is non-zero in ℚₚ. -/
theorem ofQ_ne_zero {x : Q} (hx : x ≠ 0) : ofQ (p := p) x ≠ 0 := fun h =>
  hx (ofQ_injective (h.trans ofQ_zero.symm))

/-- An integer, viewed in ℚₚ through ℚ, is the image of the corresponding element of ℤₚ. -/
theorem ofQ_intCast (n : Int) : ofQ (p := p) (n : Q) = ofZp ((n : Int) : Zp p) := by
  show ofQ (Q.mk n 1 Int.one_pos) = _
  rw [ofQ_mk, show ((1 : Int) : Qp p) = 1 from rfl, Field.inv_one]
  show ofZp _ * 1 = _; grind

/-- `−1 ∈ ℚ` maps to `−1 ∈ ℤₚ`. -/
theorem ofQ_neg_one : ofQ (p := p) (-1) = ofZp (-1) := by
  rw [show (-1 : Q) = ((-1 : Int) : Q) from Ring.intCast_neg_one.symm, ofQ_intCast,
    Ring.intCast_neg_one]

omit hP in
/-- An integer prime to `p` is a unit of ℤₚ. -/
theorem isPUnit_intCast {n : Int} (hn : ¬ (p : Int) ∣ n) : Zp.IsPUnit ((n : Int) : Zp p) :=
  fun h => hn (by
    have h := Zp.modPow_intCast.1 (show Zp.ModPow 1 ((n : Int) : Zp p) ((0 : Int) : Zp p) from h)
    rwa [Int.pow_one, Int.sub_zero] at h)

end Qp

/-! ## General properties at a prime -/

/-- At a non-prime `ℓ` the symbol is `1` by convention. -/
theorem hilbertAt_of_not_prime {ℓ : Nat} (h : ¬ Prime ℓ) (a b : Q) : hilbertAt ℓ a b = 1 := by
  unfold hilbertAt; simp [h]

/-- **Symmetry** `(a, b)_ℓ = (b, a)_ℓ`. -/
theorem hilbertAt_comm (ℓ : Nat) (a b : Q) : hilbertAt ℓ a b = hilbertAt ℓ b a := by
  by_cases hℓ : Prime ℓ
  · haveI : PrimeP ℓ := ⟨hℓ⟩
    rw [hilbertAt_eq, hilbertAt_eq, Qp.hilbert_comm]
  · rw [hilbertAt_of_not_prime hℓ, hilbertAt_of_not_prime hℓ]

/-- **Bilinearity at every prime.** For non-zero rationals, `(a a', b)_ℓ = (a, b)_ℓ (a', b)_ℓ`
(for `ℓ = 2` by `Qp.hilbert_mul_left_two`, for odd `ℓ` by `Qp.hilbert_mul_left`). -/
theorem hilbertAt_mul_left (ℓ : Nat) {a a' b : Q} (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertAt ℓ (a * a') b = hilbertAt ℓ a b * hilbertAt ℓ a' b := by
  by_cases hℓ : Prime ℓ
  · haveI : PrimeP ℓ := ⟨hℓ⟩
    rw [hilbertAt_eq, hilbertAt_eq, hilbertAt_eq, Qp.ofQ_mul]
    by_cases h2 : ℓ = 2
    · subst h2
      exact Qp.hilbert_mul_left_two (Qp.ofQ_ne_zero ha) (Qp.ofQ_ne_zero ha') (Qp.ofQ_ne_zero hb)
    · exact Qp.hilbert_mul_left (prime_odd_of_ne_two hℓ h2) (Qp.ofQ_ne_zero ha)
        (Qp.ofQ_ne_zero ha') (Qp.ofQ_ne_zero hb)
  · rw [hilbertAt_of_not_prime hℓ, hilbertAt_of_not_prime hℓ, hilbertAt_of_not_prime hℓ]; rfl

/-- **Square classes at a prime.** `(c² a, b)_ℓ = (a, b)_ℓ` for `c ≠ 0`. -/
theorem hilbertAt_mul_sq_left (ℓ : Nat) {c : Q} (hc : c ≠ 0) (a b : Q) :
    hilbertAt ℓ (c * c * a) b = hilbertAt ℓ a b := by
  by_cases hℓ : Prime ℓ
  · haveI : PrimeP ℓ := ⟨hℓ⟩
    rw [hilbertAt_eq, hilbertAt_eq, Qp.ofQ_mul, Qp.ofQ_mul]
    exact Qp.hilbert_mul_sq_left (Qp.ofQ_ne_zero hc)
  · rw [hilbertAt_of_not_prime hℓ, hilbertAt_of_not_prime hℓ]

/-- `(1, b)_ℓ = 1`. -/
theorem hilbertAt_one_left (ℓ : Nat) (b : Q) : hilbertAt ℓ 1 b = 1 := by
  by_cases hℓ : Prime ℓ
  · haveI : PrimeP ℓ := ⟨hℓ⟩
    rw [hilbertAt_eq, Qp.ofQ_one]
    exact Qp.hilbert_of_eq_sq (c := 1) (by grind)
  · exact hilbertAt_of_not_prime hℓ _ _

/-- **`(a, a)_ℓ = (a, −1)_ℓ`** for `a ≠ 0`, from `(a, b) = (a, −ab)` and `−a² ∼ −1`. -/
theorem hilbertAt_self (ℓ : Nat) {a : Q} (ha : a ≠ 0) : hilbertAt ℓ a a = hilbertAt ℓ a (-1) := by
  by_cases hℓ : Prime ℓ
  · haveI : PrimeP ℓ := ⟨hℓ⟩
    rw [hilbertAt_eq, hilbertAt_eq, Qp.ofQ_neg_one, show Qp.ofZp (-1 : Zp ℓ) = -1 from rfl,
      Qp.hilbert_neg_mul (Qp.ofQ_ne_zero ha),
      show -(Qp.ofQ a * Qp.ofQ a) = Qp.ofQ (p := ℓ) a * Qp.ofQ a * (-1) by grind,
      Qp.hilbert_mul_sq_right (Qp.ofQ_ne_zero ha)]
  · rw [hilbertAt_of_not_prime hℓ, hilbertAt_of_not_prime hℓ]

/-! ## At infinity -/

/-- `(a, b)_∞` for rationals: `−1` iff `a < 0` and `b < 0`. -/
theorem hilbertInfQ_eq (a b : Q) : hilbertInfQ a b = if a < 0 ∧ b < 0 then -1 else 1 := by
  by_cases h : a < 0 ∧ b < 0
  · simp only [h, and_self, ite_true]
    exact (hilbertInf_eq_neg_one_iff _ _).2 ⟨R.ofQ_lt.2 h.1, R.ofQ_lt.2 h.2⟩
  · simp only [h, ite_false]
    exact (hilbertInf_eq_one_iff _ _).2 fun ⟨h1, h2⟩ => h ⟨R.ofQ_lt.1 h1, R.ofQ_lt.1 h2⟩

/-- Symmetry at `∞`. -/
theorem hilbertInfQ_comm (a b : Q) : hilbertInfQ a b = hilbertInfQ b a := by
  rw [hilbertInfQ_eq, hilbertInfQ_eq]
  by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;> simp [h1, h2]

/-- A non-zero rational is negative or positive. -/
theorem Q_neg_or_pos {a : Q} (ha : a ≠ 0) : (a < 0 ∧ ¬ 0 < a) ∨ (¬ a < 0 ∧ 0 < a) := by
  rcases Std.lt_trichotomy a 0 with h | h | h
  · exact Or.inl ⟨h, fun h' => by grind⟩
  · exact absurd h ha
  · exact Or.inr ⟨fun h' => by grind, h⟩

/-- The sign of a product of non-zero rationals. -/
theorem Q_mul_neg_iff {a a' : Q} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    a * a' < 0 ↔ ¬ (a < 0 ↔ a' < 0) := by
  rcases Q_neg_or_pos ha with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases Q_neg_or_pos ha' with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
  · have := OrderedRing.mul_pos_of_neg_of_neg h1 h2; grind
  · have := OrderedRing.mul_neg_of_neg_of_pos h1 h2'; grind
  · have := OrderedRing.mul_neg_of_pos_of_neg h1' h2; grind
  · have := OrderedRing.mul_pos h1' h2'; grind

/-- **Bilinearity at `∞`.** For non-zero rationals, `(a a', b)_∞ = (a, b)_∞ (a', b)_∞`. -/
theorem hilbertInfQ_mul_left {a a' : Q} (ha : a ≠ 0) (ha' : a' ≠ 0) (b : Q) :
    hilbertInfQ (a * a') b = hilbertInfQ a b * hilbertInfQ a' b := by
  rw [hilbertInfQ_eq, hilbertInfQ_eq, hilbertInfQ_eq]
  have hs := Q_mul_neg_iff ha ha'
  by_cases h1 : a < 0 <;> by_cases h2 : a' < 0 <;> by_cases h3 : b < 0 <;> simp_all

/-- **Square classes at `∞`.** `(c² a, b)_∞ = (a, b)_∞` for `c ≠ 0`. -/
theorem hilbertInfQ_mul_sq_left {c : Q} (hc : c ≠ 0) (a b : Q) :
    hilbertInfQ (c * c * a) b = hilbertInfQ a b := by
  by_cases ha : a = 0
  · subst ha; rw [show c * c * 0 = 0 by grind]
  · have hcc : c * c ≠ 0 := fun h => by
      rcases Field.of_mul_eq_zero h with h | h <;> exact hc h
    rw [hilbertInfQ_mul_left hcc ha, hilbertInfQ_mul_left hc hc,
      show hilbertInfQ c b * hilbertInfQ c b = 1 by
        rw [hilbertInfQ_eq]; split <;> decide]
    grind

/-- `(1, b)_∞ = 1`. -/
theorem hilbertInfQ_one_left (b : Q) : hilbertInfQ 1 b = 1 :=
  hilbertInfQ_of_pos (by grind) b

/-- **`(a, a)_∞ = (a, −1)_∞`.** -/
theorem hilbertInfQ_self (a : Q) : hilbertInfQ a a = hilbertInfQ a (-1) := by
  rw [hilbertInfQ_eq, hilbertInfQ_eq]
  have : (-1 : Q) < 0 := by grind
  by_cases h : a < 0 <;> simp [h, this]

/-! ## Values on generators -/

/-- **Units at odd primes.** For an odd prime `ℓ` and integers `m, n` prime to `ℓ`,
`(m, n)_ℓ = 1`. -/
theorem hilbertAt_int_units {ℓ : Nat} (hℓ : Prime ℓ) (h2 : ℓ ≠ 2) {m n : Int}
    (hm : ¬ (ℓ : Int) ∣ m) (hn : ¬ (ℓ : Int) ∣ n) : hilbertAt ℓ (m : Q) (n : Q) = 1 := by
  haveI : PrimeP ℓ := ⟨hℓ⟩
  rw [hilbertAt_eq, Qp.ofQ_intCast, Qp.ofQ_intCast]
  exact Qp.hilbert_units (prime_odd_of_ne_two hℓ h2) (Qp.isPUnit_intCast hm)
    (Qp.isPUnit_intCast hn)

/-- `−1` is the rational cast of the integer `−1`. -/
theorem Q_neg_one_eq : (-1 : Q) = ((-1 : Int) : Q) := Ring.intCast_neg_one.symm

/-- A natural number is the rational cast of the corresponding integer. -/
theorem Q_natCast_eq (n : Nat) : (n : Q) = ((n : Int) : Q) := rfl

/-- `ofZp p = std true 1` in ℚₚ. -/
theorem Qp.ofZp_p_eq_std {p : Nat} [PrimeP p] :
    Qp.ofZp ((p : Int) : Zp p) = Qp.std true (1 : Zp p) := by
  show _ = Qp.ofZp ((p : Zp p) * 1)
  rw [Semiring.mul_one]; rfl

/-- **First supplement, locally.** For an odd prime `p`, `(−1, p)ₚ = (−1)^((p−1)/2)`. -/
theorem hilbertAt_neg_one_self {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) :
    hilbertAt p (-1) (p : Q) = (-1) ^ Foundations.Algebra.half p := by
  haveI : PrimeP p := ⟨hp⟩
  rw [hilbertAt_eq, Qp.ofQ_neg_one, Qp.ofQ_natCast, Qp.ofZp_p_eq_std,
    show Qp.ofZp (-1 : Zp p) = Qp.std false (-1) from rfl,
    Qp.hilbert_std hodd false true Zp.isPUnit_neg_one (Zp.isPUnit_one hp)]
  exact Zp.chi_neg_one hodd

/-- **Second supplement, locally.** For an odd prime `p`, `(2, p)ₚ = (2/p) = (−1)^((p²−1)/8)`. -/
theorem hilbertAt_two_self {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) :
    hilbertAt p 2 (p : Q) = (-1) ^ ((p * p - 1) / 8) := by
  haveI : PrimeP p := ⟨hp⟩
  have hnd : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by decide) h
    have := hp.1; omega
  rw [hilbertAt_eq, show (2 : Q) = ((2 : Nat) : Q) from rfl, Qp.ofQ_natCast, Qp.ofQ_natCast,
    ← Foundations.Algebra.legendre_two hp hodd]
  exact Qp.hilbert_p hodd hnd

/-- The residue modulo `8` of an integer, as a natural number. -/
theorem res8_intCast_toNat (n : Int) : Zp.res8 (n : Zp 2) = (n % 8).toNat := by
  have := Zp.res8_intCast n
  omega

/-- An odd integer is a unit of ℤ₂. -/
theorem isPUnit_two_of_odd {m : Int} (hm : m % 2 = 1) : Zp.IsPUnit (m : Zp 2) :=
  Qp.isPUnit_intCast (fun h => by have := Int.emod_eq_zero_of_dvd h; omega)

/-- **`(m, n)₂` for odd integers**, from the table: `table2 false false (m mod 8) (n mod 8)`. -/
theorem hilbertAt_two_units_int {m n : Int} (hm : m % 2 = 1) (hn : n % 2 = 1) :
    hilbertAt 2 (m : Q) (n : Q) = table2 false false (m % 8).toNat (n % 8).toNat := by
  rw [hilbertAt_eq, Qp.ofQ_intCast, Qp.ofQ_intCast, ← res8_intCast_toNat,
    ← res8_intCast_toNat]
  exact Qp.hilbert_std_two false false (isPUnit_two_of_odd hm) (isPUnit_two_of_odd hn)

/-- **`(m, 2)₂` for an odd integer `m`**: `table2 false true (m mod 8) 1`. -/
theorem hilbertAt_two_int_two {m : Int} (hm : m % 2 = 1) :
    hilbertAt 2 (m : Q) 2 = table2 false true (m % 8).toNat 1 := by
  rw [hilbertAt_eq, Qp.ofQ_intCast, show (2 : Q) = ((2 : Nat) : Q) from rfl, Qp.ofQ_natCast,
    show Qp.ofZp (((2 : Nat) : Int) : Zp 2) = Qp.std true (1 : Zp 2) from Qp.ofZp_p_eq_std,
    show Qp.ofZp ((m : Int) : Zp 2) = Qp.std false ((m : Int) : Zp 2) from rfl,
    Qp.hilbert_std_two false true (isPUnit_two_of_odd hm) (Zp.isPUnit_one prime_two),
    res8_intCast_toNat, Zp.res8_one]

end Foundations.Langlands.Padic
