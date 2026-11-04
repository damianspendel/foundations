import Foundations.Algebra.Reciprocity
import Foundations.Algebra.GaussLemma
import Foundations.Numbers.Arithmetic

/-!
# Legendre symbols of odd numbers modulo a prime

The sufficiency proof of the three-square theorem (`ThreeSquaresSuff`) chooses an auxiliary prime
`q ≡ 1 (mod 4)` by Dirichlet's theorem and then needs to know that a given squarefree `k` is a
square modulo `q`. By quadratic reciprocity, `(p/q) = (q/p)` for every odd prime `p ∣ k`, and the
right-hand side is controlled by the residue of `q` modulo `p`. Multiplying over the prime factors
of `k` produces the value of a *character of `k` modulo 4 or 8*:

* if `q ≡ −1 (mod p)` then `(p/q) = (−1/p) = χ₄(p)`, so `(k/q) = χ₄(k)`, where
  `χ₄(m) = ±1` according as `m ≡ ±1 (mod 4)`;
* if `2q ≡ −1 (mod p)` then `(p/q) = (−2/p) = χ₈(p)`, so `(k/q) = χ₈(k)`, where
  `χ₈(m) = 1` exactly for `m ≡ 1, 3 (mod 8)`.

This is the Jacobi-symbol calculus in the special case needed, without defining the Jacobi
symbol: `legendre_eq_char` is the multiplicativity statement that a completely multiplicative
`χ` (on odd numbers) agreeing with `(·/q)` at all prime factors of `m` agrees at `m`. It is the
point at which Legendre's `4ᵃ(8b + 7)` condition enters: `χ₄(k) = 1` for `k ≡ 1 (mod 4)` and
`χ₈(k) = 1` for `k ≡ 3 (mod 8)`, but neither helps for `k ≡ 7 (mod 8)`.
-/

namespace Foundations.Langlands.Squares

open Foundations.Numbers.Arith

/-- The Legendre symbol `(a/p)` of Part IV (`Foundations.Algebra.legendre`). -/
local notation "ls" => Foundations.Algebra.legendre

/-! ## Two characters of odd numbers -/

/-- **The character `χ₄`** of odd numbers: `1` on `m ≡ 1 (mod 4)` and `−1` otherwise. -/
def chi4 (m : Nat) : Int := if m % 4 = 1 then 1 else -1

/-- **The character `χ₈`** of odd numbers: `1` on `m ≡ 1, 3 (mod 8)` and `−1` otherwise; it is
`m ↦ (−2/m)`. -/
def chi8 (m : Nat) : Int := if m % 8 = 1 ∨ m % 8 = 3 then 1 else -1

/-- `χ₄` is multiplicative on odd numbers. -/
theorem chi4_mul {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) : chi4 (a * b) = chi4 a * chi4 b := by
  unfold chi4
  rw [Nat.mul_mod]
  have h1 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have h2 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]

/-- `χ₈` is multiplicative on odd numbers. -/
theorem chi8_mul {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) : chi8 (a * b) = chi8 a * chi8 b := by
  unfold chi8
  rw [Nat.mul_mod]
  have h1 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  have h2 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by omega
  rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;> simp [h1, h2]

/-! ## Basic values of the Legendre symbol -/

/-- The Legendre symbol depends only on the residue of `a` modulo `p`. -/
theorem ls_congr {p a b : Nat} (h : a % p = b % p) : ls a p = ls b p := by
  classical
  have h1 : p ∣ a ↔ p ∣ b := by rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, h]
  have h2 : Foundations.Algebra.IsQR a p ↔ Foundations.Algebra.IsQR b p := by
    unfold Foundations.Algebra.IsQR; rw [h]
  unfold Foundations.Algebra.legendre
  simp only [h1, h2]

/-- `(1/p) = 1`. -/
theorem ls_one {p : Nat} (hp : Prime p) : ls 1 p = 1 := by
  classical
  have h2 := hp.1
  have hnd : ¬ p ∣ 1 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
  have hqr : Foundations.Algebra.IsQR 1 p := ⟨1, rfl⟩
  unfold Foundations.Algebra.legendre
  simp [hnd, hqr]

/-- **First supplement.** `(−1/p) = χ₄(p)` for an odd prime `p` (with `−1` written `p − 1`). -/
theorem ls_neg_one {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) : ls (p - 1) p = chi4 p := by
  classical
  have h2 := hp.1
  have hnd : ¬ p ∣ p - 1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hiff := Foundations.Algebra.neg_one_qr_iff (p := p) hp hodd
  unfold Foundations.Algebra.legendre chi4
  by_cases h4 : p % 4 = 1
  · simp [hnd, hiff.2 h4, h4]
  · have : ¬ Foundations.Algebra.IsQR (p - 1) p := fun h => h4 (hiff.1 h)
    simp [hnd, this, h4]

/-- **Second supplement**, as a value: `(2/p) = 1` if `p ≡ ±1 (mod 8)` and `−1` otherwise. -/
theorem ls_two {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) :
    ls 2 p = if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1 := by
  have h2 := hp.1
  have hnd : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by decide) h
    omega
  have hiff := Foundations.Algebra.two_qr_iff (p := p) hp hodd
  rcases Foundations.Algebra.legendre_cases hp hodd hnd with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; simp only [hiff.1 h, ↓reduceIte]
  · have : ¬ (p % 8 = 1 ∨ p % 8 = 7) := fun h' => by have := hiff.2 h'; omega
    rw [h]; simp only [this, ↓reduceIte]

/-- **Multiplicativity in the top argument, against a character.** Let `q` be an odd prime and
`χ` a function on odd numbers with `χ(1) = 1` and `χ(ab) = χ(a)χ(b)`. If `(p/q) = χ(p)` for every
prime factor `p` of the odd number `m`, then `(m/q) = χ(m)`. -/
theorem legendre_eq_char {q : Nat} (hq : Prime q) (hqo : q % 2 = 1) (χ : Nat → Int)
    (h1 : χ 1 = 1) (hmul : ∀ a b, a % 2 = 1 → b % 2 = 1 → χ (a * b) = χ a * χ b) :
    ∀ m, m % 2 = 1 → (∀ p, Prime p → p ∣ m → ls p q = χ p) → ls m q = χ m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro hm hp
  by_cases hm1 : m = 1
  · subst hm1; rw [ls_one hq, h1]
  obtain ⟨p, hpp, c, rfl⟩ := exists_prime_dvd (n := m) (by omega)
  have hp2 := hpp.1
  have hpo : p % 2 = 1 := by
    rw [Nat.mul_mod] at hm
    rcases Nat.mod_two_eq_zero_or_one p with h | h
    · rw [h] at hm; simp at hm
    · exact h
  have hco : c % 2 = 1 := by
    rw [Nat.mul_mod] at hm
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · rw [h] at hm; simp at hm
    · exact h
  have hc0 : 0 < c := by omega
  have hlt : c < p * c := by
    have := Nat.mul_lt_mul_of_pos_right (show 1 < p by omega) hc0
    omega
  rw [Foundations.Algebra.legendre_mul hq hqo, hmul p c hpo hco,
    hp p hpp (Nat.dvd_mul_right p c),
    ih c hlt hco (fun r hr hrc => hp r hr (Nat.dvd_trans hrc (Nat.dvd_mul_left c p)))]

/-! ## The two situations of the three-square proof -/

/-- Reciprocity for an odd prime `p` against a prime `q ≡ 1 (mod 4)`: `(p/q) = (q/p)`. -/
theorem ls_flip {p q : Nat} (hp : Prime p) (hq : Prime q) (hpo : p % 2 = 1) (hq4 : q % 4 = 1)
    (hpq : p ≠ q) : ls p q = ls q p :=
  (Foundations.Algebra.quadratic_reciprocity' hp hq hpo (by omega) hpq).1 (Or.inr hq4)

/-- **Situation A.** If `q ≡ 1 (mod 4)` is a prime with `q > k`, `k` is odd and `k ∣ q + 1`, then
`(k/q) = χ₄(k)`. -/
theorem ls_eq_chi4 {k q : Nat} (hq : Prime q) (hq4 : q % 4 = 1) (hko : k % 2 = 1) (hqk : k < q)
    (hd : k ∣ q + 1) : ls k q = chi4 k := by
  apply legendre_eq_char hq (by omega) chi4 rfl (fun a b ha hb => chi4_mul ha hb) k hko
  intro p hp hpk
  have hp2 := hp.1
  have hpo : p % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one p with h | h
    · exfalso
      have : 2 ∣ k := Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h) hpk
      omega
    · exact h
  have hpk' := Nat.le_of_dvd (by omega) hpk
  rw [ls_flip hp hq hpo hq4 (by omega), ← ls_neg_one hp hpo]
  apply ls_congr
  -- `q ≡ −1 (mod p)`.
  obtain ⟨j, hj⟩ := Nat.dvd_trans hpk hd
  have hj0 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp at hj
    · exact h
  have e : q = p * (j - 1) + (p - 1) := by
    have : p * j = p * (j - 1) + p := by
      rw [show p * j = p * ((j - 1) + 1) by rw [Nat.sub_add_cancel hj0], Nat.mul_succ]
    omega
  rw [e, Nat.mul_add_mod]

/-- **Situation B.** If `q ≡ 1 (mod 4)` is a prime with `q > k`, `k` is odd and `k ∣ 2q + 1`,
then `(k/q) = χ₈(k)`. -/
theorem ls_eq_chi8 {k q : Nat} (hq : Prime q) (hq4 : q % 4 = 1) (hko : k % 2 = 1) (hqk : k < q)
    (hd : k ∣ 2 * q + 1) : ls k q = chi8 k := by
  apply legendre_eq_char hq (by omega) chi8 rfl (fun a b ha hb => chi8_mul ha hb) k hko
  intro p hp hpk
  have hp2 := hp.1
  have hpo : p % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one p with h | h
    · exfalso
      have : 2 ∣ k := Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h) hpk
      omega
    · exact h
  have hpk' := Nat.le_of_dvd (by omega) hpk
  rw [ls_flip hp hq hpo hq4 (by omega)]
  -- `(2/p)(q/p) = (2q/p) = (−1/p)`.
  have h2q : ls (2 * q) p = chi4 p := by
    rw [← ls_neg_one hp hpo]
    apply ls_congr
    obtain ⟨j, hj⟩ := Nat.dvd_trans hpk hd
    have hj0 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at hj
      · exact h
    have e : 2 * q = p * (j - 1) + (p - 1) := by
      have : p * j = p * (j - 1) + p := by
        rw [show p * j = p * ((j - 1) + 1) by rw [Nat.sub_add_cancel hj0], Nat.mul_succ]
      omega
    rw [e, Nat.mul_add_mod]
  rw [Foundations.Algebra.legendre_mul hp hpo, ls_two hp hpo] at h2q
  unfold chi4 at h2q
  unfold chi8
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h8 | h8 | h8 | h8 <;>
    simp only [h8, show p % 4 = p % 8 % 4 from (Nat.mod_mod_of_dvd p (by decide)).symm] at h2q ⊢ <;>
    simp at h2q ⊢ <;> omega

end Foundations.Langlands.Squares
