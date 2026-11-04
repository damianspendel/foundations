import Foundations.Numbers.Arithmetic
import Foundations.Combinatorics.Pigeonhole

/-!
# Arithmetic toolkit for Legendre's theorem on conics

Legendre's theorem (*Essai sur la théorie des nombres*, 1785/1798) decides when the conic
`a x² + b y² + c z² = 0` has a non-trivial integer point: for squarefree, pairwise coprime,
non-zero `a, b, c` not all of the same sign, this happens iff `−bc`, `−ca`, `−ab` are squares
modulo `|a|`, `|b|`, `|c|` respectively. Hasse (1921) recast the statement as the first
*local–global principle*: the congruence conditions are exactly solvability over the `p`-adic
fields ℚₚ, and the sign condition is solvability over ℝ (see `HasseConic`).

This file sets up the elementary vocabulary over Lean's `Int` (licensed by the bridge theorems
of `Numbers`):

* `Legendre.Squarefree n` — no square of a prime divides `n`;
* `Legendre.Coprime m n` — `gcd(|m|, |n|) = 1`;
* `Legendre.IsSqMod m n` — `m ≡ t² (mod n)` for some integer `t`;

and the facts about them needed later: Bézout's identity over ℤ (`bezout_int`, from Euclid's
algorithm `Arith.bezout`), inverses modulo `n`, coprime divisibility, the **Chinese remainder
theorem for squares** (`IsSqMod.mul`), squarefree numbers are products of distinct primes
(`Squarefree.glue`: being a square modulo every prime factor implies being a square modulo
`n`), a squarefree positive square is `1`, products of coprime squarefree numbers are
squarefree, and integer square roots (`exists_isqrt`).
-/

namespace Foundations.Langlands.Padic

namespace Legendre

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Definitions -/

/-- An integer is **squarefree** if the square of no prime divides it. -/
def Squarefree (n : Int) : Prop := ∀ p : Nat, Prime p → ¬ ((p : Int) * p ∣ n)

/-- Two integers are **coprime** if `gcd(|m|, |n|) = 1`. -/
def Coprime (m n : Int) : Prop := Nat.Coprime m.natAbs n.natAbs

/-- `m` is a **square modulo `n`**: `n ∣ t² − m` for some integer `t`. (Divisibility by `n`
and by `|n|` are the same, so this is "a square mod `|n|`".) -/
def IsSqMod (m n : Int) : Prop := ∃ t : Int, n ∣ t * t - m

/-! ## Bézout, inverses and coprime divisibility -/

/-- Euclid's `Arith.gcd` is Lean's `Nat.gcd`. -/
theorem arith_gcd_eq (a b : Nat) : Arith.gcd a b = Nat.gcd a b :=
  Nat.dvd_antisymm (Nat.dvd_gcd (gcd_dvd a b).1 (gcd_dvd a b).2)
    (dvd_gcd (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b))

/-- `|m| = ± m` as integers, in a form convenient for rewriting. -/
theorem natAbs_cases (m : Int) : ((m.natAbs : Int) = m) ∨ ((m.natAbs : Int) = -m) := by
  rcases Int.le_total 0 m with h | h
  · exact Or.inl (Int.natAbs_of_nonneg h)
  · exact Or.inr (Int.ofNat_natAbs_of_nonpos h)

/-- **Bézout's identity over ℤ.** Coprime integers `m, n` satisfy `m u + n v = 1`. -/
theorem bezout_int {m n : Int} (h : Coprime m n) : ∃ u v : Int, m * u + n * v = 1 := by
  obtain ⟨x, y, hxy⟩ := Arith.bezout m.natAbs n.natAbs
  rw [arith_gcd_eq, Nat.Coprime.gcd_eq_one h] at hxy
  rcases natAbs_cases m with hm | hm <;> rcases natAbs_cases n with hn | hn <;>
    rw [hm, hn] at hxy
  · exact ⟨x, y, hxy.symm⟩
  · exact ⟨x, -y, by rw [Int.mul_neg, ← Int.neg_mul]; exact hxy.symm⟩
  · exact ⟨-x, y, by rw [Int.mul_neg, ← Int.neg_mul]; exact hxy.symm⟩
  · exact ⟨-x, -y, by rw [Int.mul_neg, Int.mul_neg, ← Int.neg_mul, ← Int.neg_mul]; exact hxy.symm⟩

/-- An integer coprime to `n` is invertible modulo `n`. -/
theorem exists_inv_mod {z n : Int} (h : Coprime z n) : ∃ w : Int, n ∣ z * w - 1 := by
  obtain ⟨u, v, huv⟩ := bezout_int h
  exact ⟨u, ⟨-v, by rw [show z * u - 1 = z * u + n * v - 1 - n * v by omega, huv]; grind⟩⟩

/-- Symmetry of coprimality. -/
theorem Coprime.symm {m n : Int} (h : Coprime m n) : Coprime n m := Nat.Coprime.symm h

/-- Coprimality is insensitive to signs. -/
theorem Coprime.neg_left {m n : Int} (h : Coprime m n) : Coprime (-m) n := by
  unfold Coprime; rw [Int.natAbs_neg]; exact h

/-- Coprimality is insensitive to signs. -/
theorem Coprime.neg_right {m n : Int} (h : Coprime m n) : Coprime m (-n) := by
  unfold Coprime; rw [Int.natAbs_neg]; exact h

/-- If `m` is coprime to `n` and `m ∣ n k`, then `m ∣ k`. -/
theorem Coprime.dvd_of_dvd_mul {m n k : Int} (h : Coprime m n) (hd : m ∣ n * k) : m ∣ k := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul] at hd
  exact Int.natAbs_dvd_natAbs.1 (Nat.Coprime.dvd_of_dvd_mul_left h hd)

/-- If coprime `m, n` both divide `k`, so does `m n`. -/
theorem Coprime.mul_dvd {m n k : Int} (h : Coprime m n) (hm : m ∣ k) (hn : n ∣ k) :
    m * n ∣ k := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h (Int.natAbs_dvd_natAbs.2 hm)
    (Int.natAbs_dvd_natAbs.2 hn)

/-- A divisor of an integer coprime to `n` is coprime to `n`. -/
theorem Coprime.of_dvd_left {d m n : Int} (hd : d ∣ m) (h : Coprime m n) : Coprime d n :=
  Nat.Coprime.coprime_dvd_left (Int.natAbs_dvd_natAbs.2 hd) h

/-- A prime dividing a product of integers divides a factor. -/
theorem prime_dvd_mul {p : Nat} (hp : Prime p) {a b : Int} (h : (p : Int) ∣ a * b) :
    (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  rcases euclid_lemma hp h with h | h
  · exact Or.inl (Int.ofNat_dvd_left.2 h)
  · exact Or.inr (Int.ofNat_dvd_left.2 h)

/-- A prime dividing a square divides the base. -/
theorem prime_dvd_of_dvd_sq {p : Nat} (hp : Prime p) {a : Int} (h : (p : Int) ∣ a * a) :
    (p : Int) ∣ a := by
  rcases prime_dvd_mul hp h with h | h <;> exact h

/-- An integer `n` with `|n| ≠ 1` and `n ≠ 0` has a prime factor. -/
theorem exists_prime_dvd_int {n : Int} (h0 : n ≠ 0) (h1 : n.natAbs ≠ 1) :
    ∃ p, Prime p ∧ (p : Int) ∣ n := by
  have : 2 ≤ n.natAbs := by have := Int.natAbs_pos.2 h0; omega
  obtain ⟨p, hp, hd⟩ := exists_prime_dvd this
  exact ⟨p, hp, Int.ofNat_dvd_left.2 hd⟩

/-- If no prime divides both `m` and `n`, and `m ≠ 0`, then `m` and `n` are coprime. -/
theorem coprime_of_no_prime {m n : Int} (hm : m ≠ 0)
    (h : ∀ p, Prime p → (p : Int) ∣ m → (p : Int) ∣ n → False) : Coprime m n := by
  unfold Coprime Nat.Coprime
  apply Classical.byContradiction; intro hg
  have hg0 : Nat.gcd m.natAbs n.natAbs ≠ 0 := fun h0 =>
    hm (Int.natAbs_eq_zero.1 (Nat.gcd_eq_zero_iff.1 h0).1)
  obtain ⟨p, hp, hd⟩ := exists_prime_dvd (show 2 ≤ Nat.gcd m.natAbs n.natAbs by omega)
  exact h p hp (Int.ofNat_dvd_left.2 (Nat.dvd_trans hd (Nat.gcd_dvd_left _ _)))
    (Int.ofNat_dvd_left.2 (Nat.dvd_trans hd (Nat.gcd_dvd_right _ _)))

/-- A prime not dividing `n` is coprime to `n`. -/
theorem coprime_prime {p : Nat} (hp : Prime p) {n : Int} (h : ¬ (p : Int) ∣ n) :
    Coprime p n := by
  apply coprime_of_no_prime (by have := hp.1; omega)
  intro q hq hqp hqn
  have hqp' : q ∣ p := Int.ofNat_dvd.1 hqp
  rcases hp.2 q hqp' with h1 | h1
  · have := hq.1; omega
  · subst h1; exact h hqn

/-- A prime dividing one of two coprime integers does not divide the other. -/
theorem Coprime.not_dvd {m n : Int} (h : Coprime m n) {p : Nat} (hp : Prime p)
    (hm : (p : Int) ∣ m) (hn : (p : Int) ∣ n) : False := by
  have h1 : p ∣ Nat.gcd m.natAbs n.natAbs :=
    Nat.dvd_gcd (Int.ofNat_dvd_left.1 hm) (Int.ofNat_dvd_left.1 hn)
  rw [Nat.Coprime.gcd_eq_one h] at h1
  have := Nat.le_of_dvd (by decide) h1; have := hp.1; omega

/-! ## Squares modulo `n` and the Chinese remainder theorem -/

/-- **Chinese remainder theorem for squares.** If `m` is a square modulo each of two coprime
integers, it is a square modulo their product. -/
theorem IsSqMod.mul {m n₁ n₂ : Int} (h : Coprime n₁ n₂) (h₁ : IsSqMod m n₁)
    (h₂ : IsSqMod m n₂) : IsSqMod m (n₁ * n₂) := by
  obtain ⟨u, v, huv⟩ := bezout_int h
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  let t := t₁ * (n₂ * v) + t₂ * (n₁ * u)
  have e₁ : n₁ ∣ t - t₁ := ⟨u * (t₂ - t₁), by
    show t₁ * (n₂ * v) + t₂ * (n₁ * u) - t₁ = _
    rw [show n₂ * v = 1 - n₁ * u by omega]; grind⟩
  have e₂ : n₂ ∣ t - t₂ := ⟨v * (t₁ - t₂), by
    show t₁ * (n₂ * v) + t₂ * (n₁ * u) - t₂ = _
    rw [show n₁ * u = 1 - n₂ * v by omega]; grind⟩
  refine ⟨t, h.mul_dvd ?_ ?_⟩
  · rw [show t * t - m = (t - t₁) * (t + t₁) + (t₁ * t₁ - m) by grind]
    exact Int.dvd_add (Int.dvd_trans e₁ (Int.dvd_mul_right _ _)) ht₁
  · rw [show t * t - m = (t - t₂) * (t + t₂) + (t₂ * t₂ - m) by grind]
    exact Int.dvd_add (Int.dvd_trans e₂ (Int.dvd_mul_right _ _)) ht₂

/-- Every integer is a square modulo a unit `±1`. -/
theorem isSqMod_of_natAbs_one {m n : Int} (h : n.natAbs = 1) : IsSqMod m n :=
  ⟨0, by
    rcases natAbs_cases n with e | e
    · rw [← e, h]; exact Int.one_dvd _
    · rw [show n = -1 by omega]; exact ⟨-(0 * 0 - m), by grind⟩⟩

/-- Every integer is a square modulo `2`: `m² − m = m (m − 1)` is even. -/
theorem isSqMod_two (m : Int) : IsSqMod m 2 := by
  refine ⟨m, ?_⟩
  rcases Int.emod_two_eq m with h | h
  · obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    exact ⟨k * (2 * k - 1), by rw [hk]; grind⟩
  · obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    exact ⟨k * (2 * k + 1), by rw [hk]; grind⟩

/-- Being a square modulo `n` depends only on `n` up to sign. -/
theorem IsSqMod.neg_mod {m n : Int} (h : IsSqMod m n) : IsSqMod m (-n) := by
  obtain ⟨t, ht⟩ := h; exact ⟨t, Int.neg_dvd.2 ht⟩

/-- Being a square modulo `n` depends only on the class of `m` modulo `n`. -/
theorem IsSqMod.congr {m m' n : Int} (h : IsSqMod m n) (e : n ∣ m - m') : IsSqMod m' n := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [show t * t - m' = (t * t - m) + (m - m') by omega]; exact Int.dvd_add ht e⟩

/-- Being a square modulo `n` passes to divisors of `n`. -/
theorem IsSqMod.of_dvd {m n d : Int} (h : IsSqMod m n) (hd : d ∣ n) : IsSqMod m d := by
  obtain ⟨t, ht⟩ := h; exact ⟨t, Int.dvd_trans hd ht⟩

/-! ## Squarefree integers -/

/-- Squarefreeness is insensitive to sign. -/
theorem Squarefree.neg {n : Int} (h : Squarefree n) : Squarefree (-n) :=
  fun p hp hd => h p hp (Int.dvd_neg.1 hd)

/-- Divisors of squarefree integers are squarefree. -/
theorem Squarefree.of_dvd {n d : Int} (h : Squarefree n) (hd : d ∣ n) : Squarefree d :=
  fun p hp hpd => h p hp (Int.dvd_trans hpd hd)

/-- If `p` divides the squarefree `n = p m`, then `p ∤ m`. -/
theorem Squarefree.not_dvd_cofactor {n m : Int} {p : Nat} (h : Squarefree n) (hp : Prime p)
    (e : n = p * m) : ¬ (p : Int) ∣ m := fun hm =>
  h p hp (e ▸ Int.mul_dvd_mul (Int.dvd_refl _) hm)

/-- A positive squarefree perfect square is `1`. -/
theorem Squarefree.eq_one_of_sq {n z : Int} (h : Squarefree n) (hn : 0 < n) (e : n = z * z) :
    n = 1 := by
  have hz : z.natAbs ≤ 1 := by
    apply Classical.byContradiction; intro hz
    have hz0 : z ≠ 0 := by intro h0; subst h0; omega
    obtain ⟨p, hp, hd⟩ := exists_prime_dvd_int hz0 (by omega)
    exact h p hp (e ▸ Int.mul_dvd_mul hd hd)
  have : z = 0 ∨ z = 1 ∨ z = -1 := by omega
  rcases this with h0 | h0 | h0 <;> subst h0 <;> simp_all

/-- **Products of coprime squarefree integers are squarefree.** -/
theorem Squarefree.mul {a b : Int} (hab : Coprime a b) (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (a * b) := by
  intro p hp hd
  have hp0 : (p : Int) ≠ 0 := by have := hp.1; omega
  have hpab : (p : Int) ∣ a * b := Int.dvd_trans (Int.dvd_mul_right _ _) hd
  rcases prime_dvd_mul hp hpab with hpa | hpb
  · obtain ⟨a₁, rfl⟩ := hpa
    have hnb : ¬ (p : Int) ∣ b := fun hpb => hab.not_dvd hp (Int.dvd_mul_right _ _) hpb
    rw [Int.mul_assoc] at hd
    have h1 := Int.dvd_of_mul_dvd_mul_left hp0 hd
    rcases prime_dvd_mul hp h1 with h2 | h2
    · exact ha p hp (Int.mul_dvd_mul (Int.dvd_refl _) h2)
    · exact hnb h2
  · obtain ⟨b₁, rfl⟩ := hpb
    have hna : ¬ (p : Int) ∣ a := fun hpa => hab.not_dvd hp hpa (Int.dvd_mul_right _ _)
    rw [show a * (↑p * b₁) = ↑p * (a * b₁) by grind] at hd
    have h1 := Int.dvd_of_mul_dvd_mul_left hp0 hd
    rcases prime_dvd_mul hp h1 with h2 | h2
    · exact hna h2
    · exact hb p hp (Int.mul_dvd_mul (Int.dvd_refl _) h2)

/-- **Gluing squares along the prime factors of a squarefree integer.** If `n ≠ 0` is
squarefree and `m` is a square modulo every prime factor of `n`, then `m` is a square modulo
`n` (the Chinese remainder theorem, by induction on `|n|`). -/
theorem Squarefree.glue {m : Int} : ∀ (k : Nat) {n : Int}, n.natAbs = k → n ≠ 0 →
    Squarefree n → (∀ p, Prime p → (p : Int) ∣ n → IsSqMod m p) → IsSqMod m n := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro n hk hn0 hsq hloc
    by_cases h1 : n.natAbs = 1
    · exact isSqMod_of_natAbs_one h1
    obtain ⟨p, hp, n₁, rfl⟩ := exists_prime_dvd_int hn0 h1
    have hp1 : 1 < p := hp.1
    have hn₁0 : n₁ ≠ 0 := by intro h; subst h; simp at hn0
    have hlt : n₁.natAbs < k := by
      rw [← hk, Int.natAbs_mul]
      have := Int.natAbs_pos.2 hn₁0
      simp only [Int.natAbs_natCast]
      exact Nat.lt_of_lt_of_le (by omega : n₁.natAbs < 2 * n₁.natAbs)
        (Nat.mul_le_mul_right _ (by omega))
    have hcop : Coprime p n₁ := coprime_prime hp (hsq.not_dvd_cofactor hp rfl)
    refine IsSqMod.mul hcop (hloc p hp (Int.dvd_mul_right _ _)) ?_
    exact ih _ hlt rfl hn₁0 (hsq.of_dvd (Int.dvd_mul_left _ _))
      (fun q hq hqd => hloc q hq (Int.dvd_trans hqd (Int.dvd_mul_left _ _)))

/-! ## Integer square roots -/

/-- **Integer square roots.** Every `n` lies between consecutive squares:
`X² ≤ n < (X + 1)²`. -/
theorem exists_isqrt (n : Nat) : ∃ X : Nat, X * X ≤ n ∧ n < (X + 1) * (X + 1) := by
  induction n with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨X, h1, h2⟩ := ih
    by_cases h : (X + 1) * (X + 1) ≤ n + 1
    · refine ⟨X + 1, h, ?_⟩
      have : (X + 1 + 1) * (X + 1 + 1) = (X + 1) * (X + 1) + 2 * X + 3 := by grind
      omega
    · exact ⟨X, by omega, by omega⟩

/-- The integer square root `⌊√n⌋`, chosen by `exists_isqrt`. -/
noncomputable def isqrt (n : Nat) : Nat := Classical.choose (exists_isqrt n)

/-- `⌊√n⌋² ≤ n < (⌊√n⌋ + 1)²`. -/
theorem isqrt_spec (n : Nat) : isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) :=
  Classical.choose_spec (exists_isqrt n)

end Legendre

end Foundations.Langlands.Padic
