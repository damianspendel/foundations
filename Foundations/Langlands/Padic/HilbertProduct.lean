import Foundations.Langlands.Padic.Hilbert2
import Foundations.Langlands.Padic.HilbertInf
import Foundations.Langlands.Padic.ProductFormula
import Foundations.Algebra.Reciprocity

/-!
# Hilbert's product formula for two odd primes

Hilbert's reformulation of quadratic reciprocity: for non-zero rationals `a, b`, the local
symbols `(a, b)_v` are `1` for all but finitely many places `v`, and
`∏_v (a, b)_v = 1`, the product running over `∞` and all primes. We prove it for `a = p`,
`b = q` **distinct odd primes** (`hilbert_product_formula_primes`, and the finite-product form
`hilbert_product_formula_primes'` in the style of `product_formula`). The local symbols are:

* `(p, q)_∞ = 1`, since `p > 0` (`hilbertInfQ_of_pos`);
* `(p, q)_ℓ = 1` for odd `ℓ ∉ {p, q}`, as `p, q` are `ℓ`-adic units (`Qp.hilbert_units`);
* `(p, q)_p = (q/p)` and `(p, q)_q = (p/q)` (`Qp.hilbert_p`);
* `(p, q)_2 = (−1)^(((p−1)/2)((q−1)/2))` (`Qp.hilbert_two_units`).

So the product formula is exactly the law of quadratic reciprocity
`(q/p)(p/q) = (−1)^(((p−1)/2)((q−1)/2))` (`Algebra.quadratic_reciprocity`). The general case
(arbitrary non-zero rationals, which needs the full symbol at `2` including the factor `2` and
the second supplement) is `hilbert_product_formula` in `HilbertReciprocity`.

The symbol at a natural number `ℓ` is `hilbertAt ℓ a b`, defined as the Hilbert symbol in ℚ_ℓ
of `a, b ∈ ℚ` when `ℓ` is prime (and `1` otherwise).
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- The **local Hilbert symbol** `(a, b)_ℓ` of two rationals at a prime `ℓ`, computed in ℚ_ℓ;
by convention `1` when `ℓ` is not prime. -/
noncomputable def hilbertAt (ℓ : Nat) (a b : Q) : Int := by
  classical exact if h : Prime ℓ then
    @Qp.hilbert ℓ ⟨h⟩ (@Qp.ofQ ℓ ⟨h⟩ a) (@Qp.ofQ ℓ ⟨h⟩ b) else 1

/-- At a prime, `hilbertAt` is the Hilbert symbol of ℚ_ℓ. -/
theorem hilbertAt_eq (ℓ : Nat) [hP : PrimeP ℓ] (a b : Q) :
    hilbertAt ℓ a b = Qp.hilbert (Qp.ofQ (p := ℓ) a) (Qp.ofQ b) := by
  unfold hilbertAt; simp only [hP.prime, dite_true]

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- A natural number, viewed in ℚₚ through ℚ, is the image of the corresponding integer of ℤₚ. -/
theorem ofQ_natCast (n : Nat) : ofQ (p := p) (n : Q) = ofZp ((n : Int) : Zp p) := by
  show ofQ (Q.mk (n : Int) 1 Int.one_pos) = _
  rw [ofQ_mk, show ((1 : Int) : Qp p) = 1 from rfl, Field.inv_one]
  show ofZp _ * 1 = _; grind

omit hP in
/-- An integer prime to `p` is a unit of ℤₚ. -/
theorem isPUnit_natCast {n : Nat} (hn : ¬ p ∣ n) : Zp.IsPUnit ((n : Int) : Zp p) := fun h => hn (by
  have h := Zp.modPow_intCast.1 (show Zp.ModPow 1 ((n : Int) : Zp p) ((0 : Int) : Zp p) from h)
  rw [Int.pow_one, Int.sub_zero] at h
  exact Int.ofNat_dvd.1 h)

end Qp

/-- A prime `ℓ` does not divide a different prime `p`. -/
theorem prime_not_dvd {ℓ p : Nat} (hℓ : Prime ℓ) (hp : Prime p) (h : ℓ ≠ p) : ¬ ℓ ∣ p := fun hd => by
  rcases hp.2 ℓ hd with h1 | h1
  · have := hℓ.1; omega
  · exact h h1

/-- An odd prime is not `2`, and a prime other than `2` is odd. -/
theorem prime_odd_of_ne_two {ℓ : Nat} (hℓ : Prime ℓ) (h : ℓ ≠ 2) : ℓ % 2 = 1 := by
  apply Classical.byContradiction; intro h'
  rcases hℓ.2 2 (Nat.dvd_of_mod_eq_zero (by omega)) with h1 | h1 <;> omega

/-- `(−1)^n · (−1)^n = 1`. -/
theorem neg_one_pow_mul_self (n : Nat) : (-1 : Int) ^ n * (-1) ^ n = 1 := by
  rw [Foundations.Algebra.neg_one_pow_int]; split <;> decide

/-- For odd `p`, `q`: `(−1)^(((p−1)/2)((q−1)/2)) = −1` iff `p ≡ q ≡ 3 (mod 4)`. -/
theorem neg_one_pow_half_mul {p q : Nat} (hp : p % 2 = 1) (hq : q % 2 = 1) :
    (-1 : Int) ^ (Foundations.Algebra.half p * Foundations.Algebra.half q) =
      if p % 4 = 3 ∧ q % 4 = 3 then -1 else 1 := by
  rw [Foundations.Algebra.neg_one_pow_int, Nat.mul_mod]
  unfold Foundations.Algebra.half
  rcases (by omega : (p - 1) / 2 % 2 = 0 ∧ p % 4 = 1 ∨ (p - 1) / 2 % 2 = 1 ∧ p % 4 = 3) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases (by omega : (q - 1) / 2 % 2 = 0 ∧ q % 4 = 1 ∨ (q - 1) / 2 % 2 = 1 ∧ q % 4 = 3) with
    ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp [h1, h2, h3, h4]

/-- In ℤ₂, a natural number `n` is `≡ 3 (mod 4)` iff `n % 4 = 3`. -/
theorem modPow_two_three_iff (n : Nat) :
    Zp.ModPow 2 ((n : Int) : Zp 2) ((3 : Int) : Zp 2) ↔ n % 4 = 3 := by
  rw [Zp.modPow_intCast]
  show (4 : Int) ∣ (n : Int) - 3 ↔ _
  constructor
  · intro h; have := Int.emod_eq_zero_of_dvd h; omega
  · intro h; exact Int.dvd_of_emod_eq_zero (by omega)

/-- The local symbols of two distinct odd primes `p, q`: `(p, q)_ℓ = 1` at every odd prime
`ℓ ∉ {p, q}`. -/
theorem hilbertAt_primes_other {p q ℓ : Nat} (hp : Prime p) (hq : Prime q) (hℓ : Prime ℓ)
    (h2 : ℓ ≠ 2) (hlp : ℓ ≠ p) (hlq : ℓ ≠ q) : hilbertAt ℓ p q = 1 := by
  haveI : PrimeP ℓ := ⟨hℓ⟩
  rw [hilbertAt_eq, Qp.ofQ_natCast, Qp.ofQ_natCast]
  exact Qp.hilbert_units (prime_odd_of_ne_two hℓ h2)
    (Qp.isPUnit_natCast (prime_not_dvd hℓ hp hlp)) (Qp.isPUnit_natCast (prime_not_dvd hℓ hq hlq))

/-- `(p, q)_2 = (−1)^(((p−1)/2)((q−1)/2))` for odd primes `p, q`. -/
theorem hilbertAt_two_primes {p q : Nat} (hpo : p % 2 = 1) (hqo : q % 2 = 1) :
    hilbertAt 2 p q = (-1) ^ (Foundations.Algebra.half p * Foundations.Algebra.half q) := by
  have h2p : ¬ 2 ∣ p := fun h => by have := Nat.mod_eq_zero_of_dvd h; omega
  have h2q : ¬ 2 ∣ q := fun h => by have := Nat.mod_eq_zero_of_dvd h; omega
  rw [hilbertAt_eq, Qp.ofQ_natCast, Qp.ofQ_natCast,
    Qp.hilbert_two_units (Qp.isPUnit_natCast h2p) (Qp.isPUnit_natCast h2q),
    neg_one_pow_half_mul hpo hqo]
  by_cases h : p % 4 = 3 ∧ q % 4 = 3
  · have h' : Zp.ModPow 2 ((p : Int) : Zp 2) ((3 : Int) : Zp 2) ∧
        Zp.ModPow 2 ((q : Int) : Zp 2) ((3 : Int) : Zp 2) :=
      ⟨(modPow_two_three_iff p).2 h.1, (modPow_two_three_iff q).2 h.2⟩
    simp only [h, h', and_self, ite_true]
  · have h' : ¬ (Zp.ModPow 2 ((p : Int) : Zp 2) ((3 : Int) : Zp 2) ∧
        Zp.ModPow 2 ((q : Int) : Zp 2) ((3 : Int) : Zp 2)) := fun h' =>
      h ⟨(modPow_two_three_iff p).1 h'.1, (modPow_two_three_iff q).1 h'.2⟩
    simp only [h, h', ite_false]

/-- `(p, q)_q = (p/q)` for distinct odd primes. -/
theorem hilbertAt_primes_right {p q : Nat} (hp : Prime p) (hq : Prime q) (hqo : q % 2 = 1)
    (hpq : p ≠ q) : hilbertAt q p q = Foundations.Algebra.legendre p q := by
  haveI : PrimeP q := ⟨hq⟩
  rw [hilbertAt_eq, Qp.ofQ_natCast, Qp.ofQ_natCast]
  exact Qp.hilbert_p hqo (prime_not_dvd hq hp (Ne.symm hpq))

/-- `(p, q)_p = (q/p)` for distinct odd primes. -/
theorem hilbertAt_primes_left {p q : Nat} (hp : Prime p) (hq : Prime q) (hpo : p % 2 = 1)
    (hpq : p ≠ q) : hilbertAt p p q = Foundations.Algebra.legendre q p := by
  haveI : PrimeP p := ⟨hp⟩
  rw [hilbertAt_eq, Qp.ofQ_natCast, Qp.ofQ_natCast, Qp.hilbert_comm]
  exact Qp.hilbert_p hpo (prime_not_dvd hp hq hpq)

/-- `(p, q)_∞ = 1` for primes (indeed for any positive `p`). -/
theorem hilbertInfQ_primes {p : Nat} (hp : Prime p) (q : Q) : hilbertInfQ (p : Q) q = 1 :=
  hilbertInfQ_of_pos (OrderedRing.pos_natCast_of_pos (R := Q) _ (by have := hp.1; omega)) q

/-- **Hilbert's product formula for two odd primes.** For distinct odd primes `p, q`, the local
Hilbert symbols `(p, q)_ℓ` are `1` at every prime `ℓ ∉ {2, p, q}`, and
`(p, q)_∞ · (p, q)_2 · (p, q)_p · (p, q)_q = 1`; that is, `∏_v (p, q)_v = 1`. -/
theorem hilbert_product_formula_primes {p q : Nat} (hp : Prime p) (hq : Prime q)
    (hpo : p % 2 = 1) (hqo : q % 2 = 1) (hpq : p ≠ q) :
    (∀ ℓ, Prime ℓ → ℓ ≠ 2 → ℓ ≠ p → ℓ ≠ q → hilbertAt ℓ p q = 1) ∧
      hilbertInfQ p q * hilbertAt 2 p q * hilbertAt p p q * hilbertAt q p q = 1 := by
  refine ⟨fun ℓ hℓ h2 hlp hlq => hilbertAt_primes_other hp hq hℓ h2 hlp hlq, ?_⟩
  rw [hilbertInfQ_primes hp, hilbertAt_two_primes hpo hqo, hilbertAt_primes_left hp hq hpo hpq,
    hilbertAt_primes_right hp hq hqo hpq]
  have hr := Foundations.Algebra.quadratic_reciprocity hp hq hpo hqo hpq
  rw [show (1 : Int) * (-1) ^ (Foundations.Algebra.half p * Foundations.Algebra.half q) *
      Foundations.Algebra.legendre q p * Foundations.Algebra.legendre p q =
      (-1) ^ (Foundations.Algebra.half p * Foundations.Algebra.half q) *
      (Foundations.Algebra.legendre q p * Foundations.Algebra.legendre p q) by grind, hr]
  exact neg_one_pow_mul_self _

/-- **Hilbert's product formula, finite-product form.** For distinct odd primes `p, q` and every
`M > max(p, q)`, `(∏_{ℓ < M prime} (p, q)_ℓ) · (p, q)_∞ = 1` (values in ℚ). -/
theorem hilbert_product_formula_primes' {p q : Nat} (hp : Prime p) (hq : Prime q)
    (hpo : p % 2 = 1) (hqo : q % 2 = 1) (hpq : p ≠ q) {M : Nat} (hpM : p < M) (hqM : q < M) :
    primeProd (fun ℓ => ((hilbertAt ℓ p q : Int) : Q)) M * ((hilbertInfQ p q : Int) : Q) = 1 := by
  obtain ⟨hother, hprod⟩ := hilbert_product_formula_primes hp hq hpo hqo hpq
  have hp2 : p ≠ 2 := fun h => by omega
  have hq2 : q ≠ 2 := fun h => by omega
  have h2M : 2 < M := by have := hp.1; omega
  let c2 : Q := ((hilbertAt 2 p q : Int) : Q)
  let cp : Q := ((hilbertAt p p q : Int) : Q)
  let cq : Q := ((hilbertAt q p q : Int) : Q)
  have hcongr := primeProd_congr (N := M) (g := fun ℓ => ((hilbertAt ℓ p q : Int) : Q))
    (h := fun ℓ => (open Classical in if ℓ = 2 then c2 else 1) *
      (open Classical in if ℓ = p then cp else 1) * (open Classical in if ℓ = q then cq else 1))
    (fun ℓ hℓ _ => by
      by_cases e2 : ℓ = 2
      · subst e2; simp [hp2.symm, hq2.symm, c2]; grind
      · by_cases ep : ℓ = p
        · subst ep; simp [e2, hpq, cp]; grind
        · by_cases eq : ℓ = q
          · subst eq; simp [e2, ep, cq]; grind
          · simp only [e2, ep, eq, ite_false]
            rw [hother ℓ hℓ e2 ep eq]; grind)
  rw [hcongr, primeProd_mul, primeProd_mul, primeProd_single prime_two c2 h2M,
    primeProd_single hp cp hpM, primeProd_single hq cq hqM]
  have := congrArg (fun n : Int => (n : Q)) hprod
  simp only [Ring.intCast_mul, Ring.intCast_one] at this
  show c2 * cp * cq * _ = 1
  rw [← this]; grind

end Foundations.Langlands.Padic
