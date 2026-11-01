import Foundations.NumberTheory.PNTMertens

/-!
# Toward the prime number theorem V: the Möbius function and divisor sums

Selberg's formula needs one more classical tool: **Möbius inversion** (Möbius, 1832; the
function `μ` already appears implicitly in Euler). The **Möbius function** is

  `μ(n) = (−1)ᵏ` if `n` is a product of `k` distinct primes, and `μ(n) = 0` if `p² ∣ n` for
  some prime `p`.

Its defining property is `Σ_{d ∣ n} μ(d) = [n = 1]`: summing `μ` over the divisors of any
`n > 1` gives zero, because the divisors with and without a given prime `p` cancel in pairs
`d ↔ p d`. This makes `μ` the inverse of the constant function `1` under *Dirichlet convolution*
`(f ∗ g)(n) = Σ_{d ∣ n} f(d) g(n/d)`, so that `F = f ∗ 1` can be solved for `f = F ∗ μ`.

Applied to `log = Λ ∗ 1` (unique factorisation: `Σ_{d ∣ n} Λ(d) = log n`), inversion gives

  `Λ(n) = Σ_{d ∣ n} μ(d) log(n/d) = −Σ_{d ∣ n} μ(d) log d`,

the identity that will feed the Tatuzawa–Iseki form of Selberg's argument.

We define `μ(n)` as a product of local factors `∏_{q ≤ n prime} m_q(n)` with `m_q(n) = 1, −1, 0`
according as `v_q(n) = 0, 1, ≥ 2`; then `μ(pm) = −μ(m)` for `p ∤ m` and `μ(pm) = 0` for `p ∣ m`
are factor-by-factor computations with the valuations of the `Binomial` file.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-! ## Finite products of reals -/

/-- The finite product `∏_{i < n} a(i)` of reals. -/
noncomputable def fprod (a : Nat → R) : Nat → R
  | 0 => 1
  | n + 1 => fprod a n * a n

/-- Products of pointwise products. -/
theorem fprod_mul (a b : Nat → R) : ∀ n, fprod (fun i => a i * b i) n = fprod a n * fprod b n
  | 0 => by show (1 : R) = 1 * 1; grind
  | n + 1 => by
    show fprod (fun i => a i * b i) n * (a n * b n) = fprod a n * a n * (fprod b n * b n)
    rw [fprod_mul a b n]; grind

/-- Products only depend on the factors below the bound. -/
theorem fprod_congr {a b : Nat → R} : ∀ {n}, (∀ i, i < n → a i = b i) → fprod a n = fprod b n
  | 0, _ => rfl
  | n + 1, h => by
    show fprod a n * a n = fprod b n * b n
    rw [fprod_congr (fun i hi => h i (by omega)), h n (by omega)]

/-- Sums of negatives. -/
theorem fsum_neg (a : Nat → R) (n : Nat) : fsum (fun i => -a i) n = -fsum a n := by
  have := fsum_const_mul (-1) a n
  rw [show (fun k => -1 * a k) = (fun k => -a k) from funext fun k => by grind] at this
  grind

/-- A product of `1`s is `1`. -/
theorem fprod_ones : ∀ n, fprod (fun _ => (1 : R)) n = 1
  | 0 => rfl
  | n + 1 => by show fprod _ n * 1 = 1; rw [fprod_ones n]; grind

/-- `∏_{i < n} (if i = c then x else 1) = x` if `c < n`. -/
theorem fprod_ite_eq (c : Nat) (x : R) : ∀ n, c < n →
    fprod (fun i => if i = c then x else 1) n = x
  | 0, h => absurd h (Nat.not_lt_zero c)
  | n + 1, h => by
    show fprod _ n * (if n = c then x else 1) = x
    by_cases hc : n = c
    · subst hc
      rw [fprod_congr (b := fun _ => 1) (fun i hi => by simp only [show i ≠ n by omega,
        ↓reduceIte]), fprod_ones]
      simp only [↓reduceIte]; grind
    · rw [fprod_ite_eq c x n (by omega)]; simp only [hc, ↓reduceIte]; grind

/-- A product with a zero factor vanishes. -/
theorem fprod_eq_zero {a : Nat → R} {c : Nat} (hc : a c = 0) : ∀ n, c < n → fprod a n = 0
  | 0, h => absurd h (Nat.not_lt_zero c)
  | n + 1, h => by
    show fprod a n * a n = 0
    by_cases hn : n = c
    · subst hn; rw [hc]; grind
    · rw [fprod_eq_zero hc n (by omega)]; grind

/-- If the factors equal `1` from `n` on, a longer product is the same. -/
theorem fprod_eq_of_one {a : Nat → R} {n m : Nat} (hnm : n ≤ m)
    (h : ∀ k, n ≤ k → k < m → a k = 1) : fprod a m = fprod a n := by
  induction m with
  | zero => obtain rfl : n = 0 := by omega
            rfl
  | succ m ih =>
    by_cases hm : n = m + 1
    · subst hm; rfl
    · show fprod a m * a m = _
      rw [ih (by omega) fun k h1 h2 => h k h1 (by omega), h m (by omega) (by omega)]; grind

/-- A product of factors of absolute value at most `1` has absolute value at most `1`. -/
theorem abs_fprod_le_one {a : Nat → R} (h : ∀ i, abs (a i) ≤ 1) : ∀ n, abs (fprod a n) ≤ 1
  | 0 => by show abs (1 : R) ≤ 1; rw [abs_of_nonneg (by grind)]; grind
  | n + 1 => by
    show abs (fprod a n * a n) ≤ 1
    rw [abs_mul]
    have h1 := abs_fprod_le_one h n
    have := OrderedRing.mul_le_mul_of_nonneg_left (h n) (abs_nonneg (fprod a n))
    grind

/-! ## The Möbius function -/

/-- The local factor of `μ` at `q`: `1, −1, 0` according as `v_q(n) = 0, 1, ≥ 2` (and `1` if
`q` is not prime). -/
noncomputable def mobFactor (q n : Nat) : R :=
  if Prime q then (if vp q n = 0 then 1 else if vp q n = 1 then -1 else 0) else 1

/-- **The Möbius function** `μ(n) = ∏_{q ≤ n} m_q(n)`: `(−1)ᵏ` for a product of `k` distinct
primes, `0` if `n` has a square factor. -/
noncomputable def mobius (n : Nat) : R := fprod (fun q => mobFactor q n) (n + 1)

/-- `v_q(n) = 0` for `q > n`. -/
theorem vp_eq_zero_of_lt {q n : Nat} (h : n < q) : vp q n = 0 := by
  unfold vp
  split
  · next hh => have := Nat.le_of_dvd hh.2.1 hh.2.2; omega
  · rfl

/-- The product defining `μ(n)` may be taken over any range `q < B` with `B > n`. -/
theorem mobius_eq_fprod {n B : Nat} (hB : n + 1 ≤ B) :
    mobius n = fprod (fun q => mobFactor q n) B := by
  unfold mobius
  refine (fprod_eq_of_one hB fun k hk _ => ?_).symm
  unfold mobFactor; rw [vp_eq_zero_of_lt (by omega)]; simp

/-- **`μ(1) = 1`.** -/
theorem mobius_one : mobius 1 = 1 := by
  unfold mobius
  rw [fprod_congr (b := fun _ => 1) (fun q _ => by
    unfold mobFactor
    split
    · next hq => rw [vp_one hq.1]; simp
    · rfl), fprod_ones]

/-- **`μ(pm) = −μ(m)`** for a prime `p ∤ m`. -/
theorem mobius_mul_prime {p m : Nat} (hp : Prime p) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    mobius (p * m) = -mobius m := by
  have hp1 := hp.1
  have hB : m + 1 ≤ p * m + 1 := by have := Nat.le_mul_of_pos_left m (show 0 < p by omega); omega
  rw [mobius_eq_fprod (Nat.le_refl _), mobius_eq_fprod hB]
  have hvpm : vp p m = 0 := by
    apply Classical.byContradiction; intro h
    have := (pow_dvd_iff_le_vp (e := 1) hp1 (show 0 < m by omega)).2 (by omega)
    rw [Nat.pow_one] at this; exact hpm this
  rw [fprod_congr (b := fun q => (if q = p then (-1 : R) else 1) * mobFactor q m) (fun q _ => by
    unfold mobFactor
    by_cases hq : Prime q
    · rw [vp_mul hq (by omega) hm, vp_prime hq hp]
      by_cases hqp : q = p
      · subst hqp; simp [hq, hvpm] <;> grind
      · simp only [hq, hqp, ↓reduceIte, Nat.zero_add]; grind
    · have : q ≠ p := fun h => hq (h ▸ hp)
      simp only [hq, this, ↓reduceIte]; grind)]
  rw [fprod_mul, fprod_ite_eq p (-1) _ (by
    have := Nat.le_mul_of_pos_right p (show 0 < m by omega); omega)]
  grind

/-- **`μ(pm) = 0`** for a prime `p ∣ m`. -/
theorem mobius_mul_prime_dvd {p m : Nat} (hp : Prime p) (hm : 1 ≤ m) (hpm : p ∣ m) :
    mobius (p * m) = 0 := by
  have hp1 := hp.1
  unfold mobius
  apply fprod_eq_zero (c := p)
  · unfold mobFactor
    rw [vp_mul hp (by omega) hm, vp_prime hp hp]
    have := (pow_dvd_iff_le_vp (e := 1) hp1 (show 0 < m by omega)).1 (by rw [Nat.pow_one]; exact hpm)
    simp only [hp, ↓reduceIte]
    rw [ite_eq_right_iff.2 (by omega), ite_eq_right_iff.2 (by omega)]
  · have := Nat.le_mul_of_pos_right p (show 0 < m by omega); omega

/-- **`|μ(n)| ≤ 1`.** -/
theorem abs_mobius_le (n : Nat) : abs (mobius n) ≤ 1 := by
  unfold mobius
  apply abs_fprod_le_one; intro q
  unfold mobFactor
  have h1 : abs (1 : R) = 1 := abs_of_nonneg (by grind)
  have h2 : abs (-1 : R) = 1 := by rw [abs_neg, h1]
  have h3 : abs (0 : R) = 0 := abs_zero
  split
  · split
    · grind
    · split <;> grind
  · grind

/-! ## Divisor sums -/

/-- The divisor sum `Σ_{d ∣ n} f(d)` (for `n ≥ 1`; all divisors are at most `n`). -/
noncomputable def dsum (f : Nat → R) (n : Nat) : R := fsum (fun d => if d ∣ n then f d else 0) (n + 1)

/-- Divisor sums may be taken over any range `d < B` with `B > n` (for `n ≥ 1`). -/
theorem dsum_eq_fsum {f : Nat → R} {n B : Nat} (hn : 1 ≤ n) (hB : n + 1 ≤ B) :
    dsum f n = fsum (fun d => if d ∣ n then f d else 0) B := by
  unfold dsum
  refine fsum_congr_bound hB fun d h1 _ => ?_
  have : ¬ d ∣ n := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  simp only [this, ↓reduceIte]

/-- **Coprimality.** If a prime `p` does not divide `d`, and `d ∣ p k`, then `d ∣ k`. -/
theorem dvd_of_dvd_prime_mul {p d k : Nat} (hp : Prime p) (hpd : ¬ p ∣ d) (h : d ∣ p * k) :
    d ∣ k := by
  have hg : gcd d p = 1 := by
    obtain ⟨g1, g2⟩ := gcd_dvd d p
    rcases hp.2 _ g2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ g1) hpd
  obtain ⟨x, y, hxy⟩ := bezout d p
  rw [hg] at hxy
  obtain ⟨c, hc⟩ := h
  have : (k : Int) = d * (k * x + c * y) := by
    have e : (k : Int) = k * (d * x + p * y) := by rw [← hxy]; simp
    have hc' : ((p * k : Nat) : Int) = ((d * c : Nat) : Int) := by rw [hc]
    push_cast at hc'
    rw [e]; grind
  exact Int.natCast_dvd_natCast.1 ⟨_, this⟩

/-- **Reindexing the multiples of `p`.** `Σ_{d ≤ pk, p ∣ d} f(d) = Σ_{e ≤ k} f(pe)`. -/
theorem fsum_multiples {p : Nat} (hp : 1 ≤ p) (f : Nat → R) : ∀ k,
    fsum (fun d => if p ∣ d then f d else 0) (p * k + 1) = fsum (fun e => f (p * e)) (k + 1)
  | 0 => by
    simp only [Nat.mul_zero, Nat.zero_add, fsum_succ, fsum_zero, Nat.dvd_zero, ↓reduceIte]
  | k + 1 => by
    rw [show p * (k + 1) + 1 = (p * k + 1) + p by grind, fsum_split, fsum_multiples hp f k,
      fsum_succ (n := k + 1)]
    congr 1
    rw [fsum_congr (b := fun j => if j = p - 1 then f (p * (k + 1)) else 0) (fun j hj => by
      by_cases hjp : j = p - 1
      · subst hjp
        have e : p * k + 1 + (p - 1) = p * (k + 1) := by grind
        simp only [e, Nat.dvd_mul_right, ↓reduceIte]
      · have : ¬ p ∣ p * k + 1 + j := by
          intro hd
          have h2 : p ∣ 1 + j := by
            have e : p * k + 1 + j = p * k + (1 + j) := by omega
            rw [e] at hd; exact (Nat.dvd_add_right (Nat.dvd_mul_right p k)).1 hd
          have := Nat.le_of_dvd (by omega) h2
          omega
        simp only [this, hjp, ↓reduceIte])]
    rw [fsum_ite_eq]; simp only [show p - 1 < p by omega, ↓reduceIte]

/-- **The fundamental property of `μ`.** `Σ_{d ∣ n} μ(d) = 1` if `n = 1`, and `0` if `n > 1`. -/
theorem dsum_mobius {n : Nat} (hn : 1 ≤ n) : dsum mobius n = if n = 1 then 1 else 0 := by
  by_cases h1 : n = 1
  · subst h1
    simp only [↓reduceIte, dsum, fsum_succ, fsum_zero]
    rw [mobius_one]; grind
  · simp only [h1, ↓reduceIte]
    obtain ⟨p, hp, ⟨k, rfl⟩⟩ := exists_prime_dvd (show 2 ≤ n by omega)
    have hp1 := hp.1
    have hk : 1 ≤ k := by rcases Nat.eq_zero_or_pos k with h | h
                          · subst h; omega
                          · exact h
    have hkpk : k + 1 ≤ p * k + 1 := by have := Nat.le_mul_of_pos_left k (show 0 < p by omega); omega
    -- The divisors not divisible by `p` are the divisors of `k` not divisible by `p`.
    obtain ⟨A, hAd⟩ : ∃ A, A = fsum (fun d => if d ∣ k ∧ ¬ p ∣ d then mobius d else 0) (k + 1) :=
      ⟨_, rfl⟩
    have hA : fsum (fun d => if p ∣ d then 0 else (if d ∣ p * k then mobius d else 0)) (p * k + 1)
        = A := by
      rw [hAd, fsum_congr_bound (a := fun d => if d ∣ k ∧ ¬ p ∣ d then mobius d else 0) hkpk
        (fun d h1 _ => by
        have : ¬ (d ∣ k ∧ ¬ p ∣ d) := fun h => by have := Nat.le_of_dvd (by omega) h.1; omega
        simp only [this, ↓reduceIte])]
      apply fsum_congr; intro d _
      by_cases hpd : p ∣ d
      · simp [hpd]
      · simp only [hpd, ↓reduceIte, not_false_eq_true, and_true]
        by_cases hdk : d ∣ k
        · simp [hdk, Nat.dvd_trans hdk (Nat.dvd_mul_left k p)]
        · have : ¬ d ∣ p * k := fun h => hdk (dvd_of_dvd_prime_mul hp hpd h)
          simp [this, hdk]
    -- The divisors divisible by `p` contribute `−A`.
    have hB : fsum (fun d => if p ∣ d then (if d ∣ p * k then mobius d else 0) else 0) (p * k + 1)
        = -A := by
      rw [fsum_multiples (by omega) (fun d => if d ∣ p * k then mobius d else 0) k]
      rw [hAd, ← fsum_neg]
      apply fsum_congr; intro e _
      by_cases hek : e ∣ k
      · have : p * e ∣ p * k := Nat.mul_dvd_mul_left p hek
        have he : 1 ≤ e := by
          rcases Nat.eq_zero_or_pos e with h | h
          · subst h; obtain ⟨c, hc⟩ := hek; omega
          · exact h
        simp only [this, hek, true_and, ↓reduceIte]
        by_cases hpe : p ∣ e
        · simp only [hpe, not_true_eq_false, ↓reduceIte, mobius_mul_prime_dvd hp he hpe]; grind
        · simp only [hpe, not_false_eq_true, ↓reduceIte, mobius_mul_prime hp he hpe]
      · have : ¬ p * e ∣ p * k := fun h => hek (Nat.dvd_of_mul_dvd_mul_left (by omega) h)
        simp only [this, hek, false_and, ↓reduceIte]; grind
    unfold dsum
    rw [fsum_ite_add (fun d => p ∣ d), hB, hA]; grind

/-! ## Möbius inversion of `log = Λ ∗ 1` -/

/-- A divisor of a positive number is positive. -/
theorem pos_of_dvd' {d m : Nat} (hm : 1 ≤ m) (h : d ∣ m) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0; obtain ⟨c, hc⟩ := h; omega
  · exact h0

/-- The cofactor of a divisor of a positive number is positive. -/
theorem one_le_div_of_dvd {d m : Nat} (hm : 1 ≤ m) (h : d ∣ m) : 1 ≤ m / d := by
  have hd0 := pos_of_dvd' hm h
  obtain ⟨c, hc⟩ := h
  rw [hc, Nat.mul_div_cancel_left c hd0]
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · subst h0; omega
  · exact h0

/-- Multiplying a divisor sum by a constant. -/
theorem dsum_const_mul (c : R) (f : Nat → R) (n : Nat) :
    c * dsum f n = dsum (fun d => c * f d) n := by
  unfold dsum; rw [← fsum_const_mul]
  apply fsum_congr; intro d _; split <;> grind

/-- `Λ(n)` as a double sum over any range `p, k < B` with `B > n`. -/
theorem vonMangoldt_eq_ext {n B : Nat} (hB : n + 1 ≤ B) :
    vonMangoldt n = fsum (fun p => fsum (fun k =>
      if Prime p ∧ 1 ≤ k ∧ p ^ k = n then R.log (p : R) else 0) B) B := by
  unfold vonMangoldt
  have hvan : ∀ p k, n + 1 ≤ p ∨ n + 1 ≤ k →
      (if Prime p ∧ 1 ≤ k ∧ p ^ k = n then R.log (p : R) else 0) = 0 := by
    intro p k hpk
    split
    · next h =>
      exfalso
      have hp2 := h.1.1
      have h1 : p ≤ p ^ k := by
        have := Nat.pow_le_pow_right (show 0 < p by omega) h.2.1; rwa [Nat.pow_one] at this
      have := lt_pow_self' hp2 k
      omega
    · rfl
  rw [fsum_congr_bound hB (fun p h1 _ => by
    rw [fsum_congr (b := fun _ => 0) (fun k _ => hvan p k (Or.inl h1)), fsum_zeros])]
  apply fsum_congr; intro p _
  exact fsum_congr_bound hB (fun k h1 _ => hvan p k (Or.inr h1))

/-- Counting an initial segment: `#{1 ≤ k < B : k ≤ v} = v` when `v < B`. -/
theorem countBelow_initial (v : Nat) : ∀ B, v < B → countBelow (fun k => 1 ≤ k ∧ k ≤ v) B = v
  | 0, h => absurd h (Nat.not_lt_zero v)
  | B + 1, h => by
    simp only [countBelow]
    by_cases hv : v = B
    · subst hv
      have : countBelow (fun k => 1 ≤ k ∧ k ≤ v) v = v - 1 ∨ v = 0 := by
        rcases Nat.eq_zero_or_pos v with h0 | h0
        · exact Or.inr h0
        · left
          have key : ∀ B, B ≤ v → countBelow (fun k => 1 ≤ k ∧ k ≤ v) B = B - 1 ∨ B = 0 := by
            intro B
            induction B with
            | zero => intro _; exact Or.inr rfl
            | succ B ih =>
              intro hB
              simp only [countBelow]
              rcases ih (by omega) with h1 | h1
              · left; rw [h1]; split <;> omega
              · subst h1; left; simp [countBelow]
          rcases key v (Nat.le_refl v) with h1 | h1
          · exact h1
          · omega
      rcases this with h1 | h1
      · rw [h1]; split <;> omega
      · subst h1; rfl
    · rw [countBelow_initial v B (by omega)]
      split <;> omega

/-- **`Σ_{d ∣ m} Λ(d) = log m`** — unique factorisation, additively (`log = Λ ∗ 1`). -/
theorem dsum_vonMangoldt {m : Nat} (hm : 1 ≤ m) : dsum vonMangoldt m = R.log (m : R) := by
  rw [log_eq_sum_vp (m + 1) m hm (by omega)]
  unfold dsum
  rw [fsum_congr (b := fun d => fsum (fun p => fsum (fun k =>
      if d ∣ m then (if Prime p ∧ 1 ≤ k ∧ p ^ k = d then R.log (p : R) else 0) else 0) (m + 1))
      (m + 1)) (fun d hd => by
    by_cases hdm : d ∣ m
    · simp only [hdm, ↓reduceIte]; exact vonMangoldt_eq_ext (by omega)
    · simp only [hdm, ↓reduceIte]
      rw [fsum_congr (b := fun _ => 0) (fun p _ => fsum_zeros _), fsum_zeros])]
  rw [fsum_swap]
  apply fsum_congr; intro p _
  rw [fsum_swap]
  by_cases hp : Prime p
  · simp only [hp, true_and, ↓reduceIte]
    have hp1 := hp.1
    rw [fsum_congr (b := fun k => if 1 ≤ k ∧ k ≤ vp p m then R.log (p : R) else 0) (fun k _ => by
      rw [fsum_congr (b := fun d => if d = p ^ k then
          (if 1 ≤ k ∧ p ^ k ∣ m then R.log (p : R) else 0) else 0) (fun d _ => by
        by_cases h : d = p ^ k
        · subst h; by_cases h' : 1 ≤ k ∧ p ^ k ∣ m
          · simp [h']
          · by_cases h2 : 1 ≤ k
            · have : ¬ p ^ k ∣ m := fun h3 => h' ⟨h2, h3⟩
              simp [this]
            · simp [h2]
        · have : ¬ (1 ≤ k ∧ p ^ k = d) := fun h' => h h'.2.symm
          simp only [this, h, ↓reduceIte, ite_self])]
      rw [fsum_ite_eq]
      have hiff := pow_dvd_iff_le_vp (e := k) hp1 (show 0 < m by omega)
      by_cases h1 : 1 ≤ k ∧ k ≤ vp p m
      · have hd : p ^ k ∣ m := hiff.2 h1.2
        have := Nat.le_of_dvd (by omega) hd
        simp [h1, hd, show p ^ k < m + 1 by omega]
      · have : ¬ (1 ≤ k ∧ p ^ k ∣ m) := fun h => h1 ⟨h.1, hiff.1 h.2⟩
        simp [this, h1])]
    rw [fsum_ite_const, countBelow_initial]
    have hd := (pow_dvd_iff_le_vp (e := vp p m) hp1 (show 0 < m by omega)).2 (Nat.le_refl _)
    have := Nat.le_of_dvd (by omega) hd
    have := lt_pow_self' hp1 (vp p m)
    omega
  · simp only [hp, false_and, ↓reduceIte, ite_self]
    rw [fsum_congr (b := fun _ => 0) (fun k _ => fsum_zeros _), fsum_zeros]

/-- For `d ∣ m`, `m ≥ 1`: `e ∣ m/d ↔ d e ∣ m`. -/
theorem dvd_div_iff_mul_dvd {d e m : Nat} (hm : 1 ≤ m) (hd : d ∣ m) : e ∣ m / d ↔ d * e ∣ m := by
  have hd0 := pos_of_dvd' hm hd
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left c hd0]
  constructor
  · exact Nat.mul_dvd_mul_left d
  · exact Nat.dvd_of_mul_dvd_mul_left hd0

/-- A divisor double sum written over pairs: `Σ_{d ∣ m} Σ_{e ∣ m/d} h(d,e) = Σ_{d,e ≤ m, de ∣ m} h(d,e)`. -/
theorem dsum_dsum_eq {m : Nat} (hm : 1 ≤ m) (h : Nat → Nat → R) :
    dsum (fun d => dsum (fun e => h d e) (m / d)) m =
      fsum (fun d => fsum (fun e => if d * e ∣ m then h d e else 0) (m + 1)) (m + 1) := by
  unfold dsum
  apply fsum_congr; intro d hd
  by_cases hdm : d ∣ m
  · simp only [hdm, ↓reduceIte]
    have hmd : 1 ≤ m / d := one_le_div_of_dvd hm hdm
    have hle : m / d + 1 ≤ m + 1 := by have := Nat.div_le_self m d; omega
    rw [show fsum (fun e => if e ∣ m / d then h d e else 0) (m / d + 1) = dsum (fun e => h d e) (m / d)
      from rfl, dsum_eq_fsum hmd hle]
    apply fsum_congr; intro e _
    by_cases he : d * e ∣ m
    · simp only [he, (dvd_div_iff_mul_dvd hm hdm).2 he, ↓reduceIte]
    · have : ¬ e ∣ m / d := fun h' => he ((dvd_div_iff_mul_dvd hm hdm).1 h')
      simp only [he, this, ↓reduceIte]
  · simp only [hdm, ↓reduceIte]
    rw [fsum_congr (b := fun _ => 0) (fun e _ => by
      have : ¬ d * e ∣ m := fun h => hdm (Nat.dvd_trans (Nat.dvd_mul_right d e) h)
      simp only [this, ↓reduceIte]), fsum_zeros]

/-- **Exchanging a divisor double sum.**
`Σ_{d ∣ m} Σ_{e ∣ m/d} h(d,e) = Σ_{e ∣ m} Σ_{d ∣ m/e} h(d,e)`. -/
theorem dsum_dsum_swap {m : Nat} (hm : 1 ≤ m) (h : Nat → Nat → R) :
    dsum (fun d => dsum (fun e => h d e) (m / d)) m =
      dsum (fun e => dsum (fun d => h d e) (m / e)) m := by
  rw [dsum_dsum_eq hm, dsum_dsum_eq hm (fun e d => h d e), fsum_swap]
  apply fsum_congr; intro d _; apply fsum_congr; intro e _
  rw [Nat.mul_comm]

/-- **Möbius inversion of `log = Λ ∗ 1`.** `Σ_{d ∣ m} μ(d) log(m/d) = Λ(m)` for `m ≥ 1`. -/
theorem dsum_mobius_log {m : Nat} (hm : 1 ≤ m) :
    dsum (fun d => mobius d * R.log ((m / d : Nat) : R)) m = vonMangoldt m := by
  have step1 : dsum (fun d => mobius d * R.log ((m / d : Nat) : R)) m =
      dsum (fun d => dsum (fun e => mobius d * vonMangoldt e) (m / d)) m := by
    unfold dsum
    apply fsum_congr; intro d _
    by_cases hdm : d ∣ m
    · simp only [hdm, ↓reduceIte]
      have hmd : 1 ≤ m / d := one_le_div_of_dvd hm hdm
      rw [← dsum_vonMangoldt hmd, dsum_const_mul]; rfl
    · simp only [hdm, ↓reduceIte]
  rw [step1, dsum_dsum_swap hm]
  unfold dsum
  rw [fsum_congr (b := fun e => if e = m then vonMangoldt m else 0) (fun e he => by
    by_cases hem : e ∣ m
    · simp only [hem, ↓reduceIte]
      have hme : 1 ≤ m / e := one_le_div_of_dvd hm hem
      have e1 : fsum (fun d => if d ∣ m / e then mobius d * vonMangoldt e else 0) (m / e + 1) =
          vonMangoldt e * dsum mobius (m / e) := by
        rw [dsum_const_mul]; unfold dsum
        apply fsum_congr; intro d _; split <;> grind
      rw [e1, dsum_mobius hme]
      by_cases hq : m / e = 1
      · have : e = m := by
          have he0 := pos_of_dvd' hm hem
          obtain ⟨c, hc⟩ := hem
          rw [hc, Nat.mul_div_cancel_left c he0] at hq
          rw [hc, hq, Nat.mul_one]
        subst this; simp only [hq, ↓reduceIte]; grind
      · have : e ≠ m := fun h => hq (by subst h; exact Nat.div_self (by omega))
        simp only [hq, this, ↓reduceIte]; grind
    · have : e ≠ m := fun h => hem (h ▸ Nat.dvd_refl m)
      simp only [hem, this, ↓reduceIte])]
  rw [fsum_ite_eq]; simp

/-- **`Λ(m) = −Σ_{d ∣ m} μ(d) log d`** for `m ≥ 1`. -/
theorem vonMangoldt_eq_neg_dsum {m : Nat} (hm : 1 ≤ m) :
    vonMangoldt m = -dsum (fun d => mobius d * R.log (d : R)) m := by
  rw [← dsum_mobius_log hm]
  have hsplit : dsum (fun d => mobius d * R.log ((m / d : Nat) : R)) m =
      R.log (m : R) * dsum mobius m - dsum (fun d => mobius d * R.log (d : R)) m := by
    rw [dsum_const_mul]; unfold dsum; rw [← fsum_sub]
    apply fsum_congr; intro d _
    by_cases hdm : d ∣ m
    · simp only [hdm, ↓reduceIte]
      have hd0 := pos_of_dvd' hm hdm
      have hc0 : 0 < m / d := by have := one_le_div_of_dvd hm hdm; omega
      obtain ⟨c, hc⟩ := hdm
      rw [hc, Nat.mul_div_cancel_left c hd0] at hc0
      rw [hc, Nat.mul_div_cancel_left c hd0, natCast_mul',
        R.log_mul (natCast_pos' hd0) (natCast_pos' hc0)]
      grind
    · simp only [hdm, ↓reduceIte]; grind
  rw [hsplit, dsum_mobius hm]
  by_cases h1 : m = 1
  · subst h1; simp only [↓reduceIte]
    rw [show ((1 : Nat) : R) = 1 by grind, R.log_one]; grind
  · simp only [h1, ↓reduceIte]; grind

end Foundations.NumberTheory.PNT
