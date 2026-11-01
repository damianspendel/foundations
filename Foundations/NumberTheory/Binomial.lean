import Foundations.NumberTheory.PrimesMod4

/-!
# Binomial coefficients and Legendre's formula

The proof of Bertrand's postulate that Paul Erdős found in 1932, aged nineteen, is a study of
one number: the **central binomial coefficient** `C(2n, n) = (2n)! / (n!)²`, the number of ways
to choose `n` things out of `2n`. Two opposite pressures act on it.

* It is **big**: `C(2n, n)` is the largest of the `2n + 1` numbers `C(2n, k)`, which add up to
  `2²ⁿ = 4ⁿ`, so `4ⁿ / (2n + 1) ≤ C(2n, n) ≤ 4ⁿ`. We prove both bounds directly from the
  recurrence `(n + 1) · C(2n+2, n+1) = 2(2n + 1) · C(2n, n)`.
* Its **prime factors are constrained**. Writing `vₚ(m)` for the exponent of `p` in `m`,
  *Legendre's formula* (1808) computes `vₚ(n!) = ⌊n/p⌋ + ⌊n/p²⌋ + ⌊n/p³⌋ + ⋯`: among `1, …, n`
  there are `⌊n/p⌋` multiples of `p`, each contributing one factor `p`, then `⌊n/p²⌋` multiples
  of `p²` contributing one more, and so on. Hence
  `vₚ(C(2n, n)) = Σₖ (⌊2n/pᵏ⌋ − 2⌊n/pᵏ⌋)`, and each summand is `0` or `1`, and is `0` once
  `pᵏ > 2n`. Consequently **every prime power dividing `C(2n, n)` is at most `2n`**, and a prime
  `p` with `2n/3 < p ≤ n` does **not** divide `C(2n, n)` at all: it occurs twice in `(2n)!`
  (as `p` and `2p`) and once in each `n!`.

Bertrand's postulate will follow by playing these facts against each other (file `Bertrand`).

Since core Lean has no binomial coefficients, we define them by Pascal's rule and prove the
factorial formula `C(a + b, a) · a! · b! = (a + b)!`. The valuation `vₚ` is defined by repeated
division.
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Binomial coefficients -/

/-- The **binomial coefficient** `C(n, k)`, defined by Pascal's rule:
`C(n, 0) = 1`, `C(0, k+1) = 0`, `C(n+1, k+1) = C(n, k) + C(n, k+1)`. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- `C(n, 0) = 1`. -/
theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

/-- Pascal's rule `C(n+1, k+1) = C(n, k) + C(n, k+1)`. -/
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) :=
  rfl

/-- `C(n, k) = 0` when `k > n`. -/
theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_eq_zero_of_lt (by omega : n < k),
      choose_eq_zero_of_lt (by omega : n < k + 1)]

/-- `C(n, n) = 1`. -/
theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt (Nat.lt_succ_self n)]

/-- **The factorial formula for binomial coefficients.** `C(a + b, a) · a! · b! = (a + b)!`. -/
theorem choose_mul_fact : ∀ n a b, a + b = n → choose n a * fact a * fact b = fact n := by
  intro n
  induction n with
  | zero => intro a b h; obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
            rfl
  | succ n ih =>
    intro a b h
    cases a with
    | zero => obtain rfl : b = n + 1 := by omega
              simp [choose_zero_right, fact]
    | succ a =>
      cases b with
      | zero => obtain rfl : a = n := by omega
                simp [choose_self, fact]
      | succ b =>
        have h1 := ih a (b + 1) (by omega)
        have h2 := ih (a + 1) b (by omega)
        rw [choose_succ_succ]
        simp only [fact] at h1 h2 ⊢
        have hn : n + 1 = (a + 1) + (b + 1) := by omega
        rw [hn]
        grind

/-- Binomial coefficients of the form `C(a + b, a)` are positive. -/
theorem choose_pos (a b : Nat) : 0 < choose (a + b) a := by
  have h := choose_mul_fact (a + b) a b rfl
  have := fact_pos (a + b)
  apply Nat.pos_of_ne_zero
  intro h0
  rw [h0] at h
  simp at h
  omega

/-- **Symmetry** `C(a + b, a) = C(a + b, b)`. -/
theorem choose_symm (a b : Nat) : choose (a + b) a = choose (a + b) b := by
  have h1 := choose_mul_fact (a + b) a b rfl
  have h2 := choose_mul_fact (a + b) b a (Nat.add_comm b a)
  have hpos : 0 < fact a * fact b := Nat.mul_pos (fact_pos a) (fact_pos b)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← Nat.mul_assoc, h1, Nat.mul_comm (fact a), ← Nat.mul_assoc, h2]

/-! ## The central binomial coefficient -/

/-- The **central binomial coefficient** `C(2n, n)`. -/
def centralBinom (n : Nat) : Nat := choose (2 * n) n

/-- `C(2n, n) · n! · n! = (2n)!`. -/
theorem centralBinom_mul_fact (n : Nat) : centralBinom n * fact n * fact n = fact (2 * n) :=
  choose_mul_fact (2 * n) n n (by omega)

/-- `C(2n, n) > 0`. -/
theorem centralBinom_pos (n : Nat) : 0 < centralBinom n := by
  have := choose_pos n n
  unfold centralBinom
  rwa [show 2 * n = n + n by omega]

/-- The **recurrence** `(n + 1) · C(2n+2, n+1) = 2(2n + 1) · C(2n, n)`. -/
theorem succ_mul_centralBinom_succ (n : Nat) :
    (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n := by
  have h1 := centralBinom_mul_fact (n + 1)
  have h2 := centralBinom_mul_fact n
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega] at h1
  simp only [fact] at h1
  have hpos : 0 < (n + 1) * (fact n * fact n) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (fact_pos n) (fact_pos n))
  apply Nat.eq_of_mul_eq_mul_right hpos
  grind

/-- `C(2n+2, n+1) ≤ 4 · C(2n, n)`. -/
theorem centralBinom_succ_le (n : Nat) : centralBinom (n + 1) ≤ 4 * centralBinom n := by
  have h := succ_mul_centralBinom_succ n
  apply Nat.le_of_mul_le_mul_left (c := n + 1) _ (by omega)
  rw [h]
  have : 2 * (2 * n + 1) ≤ (n + 1) * 4 := by omega
  calc 2 * (2 * n + 1) * centralBinom n ≤ (n + 1) * 4 * centralBinom n :=
        Nat.mul_le_mul_right _ this
    _ = (n + 1) * (4 * centralBinom n) := Nat.mul_assoc _ _ _

/-- **Upper bound** `C(2n, n) ≤ 4ⁿ`. -/
theorem centralBinom_le_four_pow (n : Nat) : centralBinom n ≤ 4 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc centralBinom (n + 1) ≤ 4 * centralBinom n := centralBinom_succ_le n
      _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- A sharper upper bound used for the primorial: `2 · C(2n, n) ≤ 4ⁿ` for `n ≥ 1`. -/
theorem two_mul_centralBinom_le (n : Nat) (hn : 1 ≤ n) : 2 * centralBinom n ≤ 4 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; decide
    · calc 2 * centralBinom (n + 1) ≤ 2 * (4 * centralBinom n) :=
            Nat.mul_le_mul_left 2 (centralBinom_succ_le n)
        _ = 4 * (2 * centralBinom n) := by omega
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 (ih h0)
        _ = 4 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- **Lower bound** `4ⁿ ≤ (2n + 1) · C(2n, n)`, i.e. `C(2n, n) ≥ 4ⁿ / (2n + 1)`. -/
theorem four_pow_le_centralBinom (n : Nat) : 4 ^ n ≤ (2 * n + 1) * centralBinom n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := succ_mul_centralBinom_succ n
    apply Nat.le_of_mul_le_mul_left (c := n + 1) _ (by omega)
    have e1 : (n + 1) * ((2 * (n + 1) + 1) * centralBinom (n + 1))
        = (2 * n + 3) * (2 * (2 * n + 1) * centralBinom n) := by
      rw [← h]; grind
    rw [e1, Nat.pow_succ]
    calc (n + 1) * (4 ^ n * 4) = (4 * (n + 1)) * 4 ^ n := by grind
      _ ≤ (4 * (n + 1)) * ((2 * n + 1) * centralBinom n) := Nat.mul_le_mul_left _ ih
      _ ≤ (2 * (2 * n + 3)) * ((2 * n + 1) * centralBinom n) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (2 * n + 3) * (2 * (2 * n + 1) * centralBinom n) := by grind

/-! ## The `p`-adic valuation -/

/-- The **`p`-adic valuation** `vₚ(m)`: how many times `p` divides `m`, computed by repeated
division (`0` if `p ≤ 1` or `m = 0`). -/
def vp (p m : Nat) : Nat :=
  if h : 1 < p ∧ 0 < m ∧ p ∣ m then vp p (m / p) + 1 else 0
termination_by m
decreasing_by exact Nat.div_lt_self h.2.1 h.1

/-- `m = p^(vₚ m) · r` with `p ∤ r`. -/
theorem vp_spec {p : Nat} (hp : 1 < p) : ∀ {m : Nat}, 0 < m → ∃ r, m = p ^ vp p m * r ∧ ¬ p ∣ r := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm
    rw [vp]
    split
    · next hd =>
      obtain ⟨k, rfl⟩ := hd.2.2
      have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
      rw [Nat.mul_div_cancel_left k (by omega)]
      have hlt : k < p * k := by
        have : 2 * k ≤ p * k := Nat.mul_le_mul_right k hp
        omega
      obtain ⟨r, hr, hpr⟩ := ih k hlt hk
      refine ⟨r, ?_, hpr⟩
      rw [Nat.pow_succ]
      conv => lhs; rw [hr]
      grind
    · next hd => exact ⟨m, by simp, fun h => hd ⟨hp, hm, h⟩⟩

/-- **Characterisation of `vₚ`.** For `m > 0`: `pᵉ ∣ m ↔ e ≤ vₚ(m)`. -/
theorem pow_dvd_iff_le_vp {p m e : Nat} (hp : 1 < p) (hm : 0 < m) : p ^ e ∣ m ↔ e ≤ vp p m := by
  obtain ⟨r, hr, hpr⟩ := vp_spec hp hm
  constructor
  · intro h
    apply Classical.byContradiction
    intro hlt
    have h1 : p ^ (vp p m + 1) ∣ m := Nat.dvd_trans (Nat.pow_dvd_pow p (by omega)) h
    have h2 : p ^ vp p m * p ∣ p ^ vp p m * r := by rw [← Nat.pow_succ, ← hr]; exact h1
    exact hpr (Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (show 0 < p by omega)) h2)
  · intro h
    exact Nat.dvd_trans (Nat.pow_dvd_pow p h) ⟨r, hr⟩

/-- If `m = pᵉ · r` with `p ∤ r`, then `vₚ(m) = e`. -/
theorem vp_eq {p m e r : Nat} (hp : 1 < p) (hm : m = p ^ e * r) (hr : ¬ p ∣ r) : vp p m = e := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; exact hr (Nat.dvd_zero p))
  have hm0 : 0 < m := by rw [hm]; exact Nat.mul_pos (Nat.pow_pos (by omega)) hr0
  have h1 : e ≤ vp p m := (pow_dvd_iff_le_vp hp hm0).1 ⟨r, hm⟩
  have h2 : ¬ e + 1 ≤ vp p m := by
    intro h
    have := (pow_dvd_iff_le_vp hp hm0).2 h
    rw [hm, Nat.pow_succ] at this
    exact hr (Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (show 0 < p by omega)) this)
  omega

/-- `vₚ(1) = 0`. -/
theorem vp_one {p : Nat} (hp : 1 < p) : vp p 1 = 0 :=
  vp_eq (e := 0) (r := 1) hp (by simp) (fun h => by have := Nat.le_of_dvd (by omega) h; omega)

/-- **`vₚ` is additive** for a prime `p`: `vₚ(a b) = vₚ(a) + vₚ(b)` (this is where Euclid's lemma
enters). -/
theorem vp_mul {p a b : Nat} (hp : Prime p) (ha : 0 < a) (hb : 0 < b) :
    vp p (a * b) = vp p a + vp p b := by
  have hp1 : 1 < p := hp.1
  obtain ⟨r, hr, hpr⟩ := vp_spec hp1 ha
  obtain ⟨s, hs, hps⟩ := vp_spec hp1 hb
  apply vp_eq hp1 (r := r * s)
  · conv => lhs; rw [hr, hs]
    rw [Nat.pow_add]; grind
  · intro h
    rcases euclid_lemma hp h with h | h
    · exact hpr h
    · exact hps h

/-- `vₚ((n+1)!) = vₚ(n+1) + vₚ(n!)`. -/
theorem vp_fact_succ {p : Nat} (hp : Prime p) (n : Nat) :
    vp p (fact (n + 1)) = vp p (n + 1) + vp p (fact n) := by
  simp only [fact]
  exact vp_mul hp (by omega) (fact_pos n)

/-! ## Legendre's formula -/

/-- The Legendre sum `⌊n/p⌋ + ⌊n/p²⌋ + ⋯ + ⌊n/pᴷ⌋`. -/
def legendreSum (p n : Nat) : Nat → Nat
  | 0 => 0
  | K + 1 => legendreSum p n K + n / p ^ (K + 1)

/-- Dividing `n + 1` instead of `n` by `q` raises the quotient by one exactly when `q ∣ n + 1`. -/
theorem succ_div_eq {n q : Nat} (hq : 0 < q) :
    (n + 1) / q = n / q + (if q ∣ n + 1 then 1 else 0) := by
  have hdm := Nat.div_add_mod n q
  have hlt := Nat.mod_lt n hq
  by_cases hr : n % q + 1 = q
  · have he : n + 1 = q * (n / q + 1) := by grind
    have hd : q ∣ n + 1 := ⟨_, he⟩
    simp only [hd, ↓reduceIte]; rw [he, Nat.mul_div_cancel_left _ hq]
  · have he : n + 1 = q * (n / q) + (n % q + 1) := by omega
    have hnd : ¬ q ∣ n + 1 := by
      intro h
      have := Nat.mod_eq_zero_of_dvd h
      rw [he, Nat.mul_add_mod, Nat.mod_eq_of_lt (show n % q + 1 < q by omega)] at this
      omega
    simp only [hnd, ↓reduceIte]; rw [he, Nat.mul_add_div hq, Nat.div_eq_of_lt (show n % q + 1 < q by omega)]

/-- How the Legendre sum changes from `n` to `n + 1`: by `min K (vₚ(n+1))`, the number of
`k ≤ K` with `pᵏ ∣ n + 1`. -/
theorem legendreSum_succ {p : Nat} (hp : 1 < p) (n : Nat) :
    ∀ K, legendreSum p (n + 1) K = legendreSum p n K + min K (vp p (n + 1)) := by
  intro K
  induction K with
  | zero => simp [legendreSum]
  | succ K ih =>
    simp only [legendreSum]
    rw [succ_div_eq (Nat.pow_pos (by omega)), ih]
    have hiff := pow_dvd_iff_le_vp (e := K + 1) hp (show 0 < n + 1 by omega)
    by_cases h : p ^ (K + 1) ∣ n + 1
    · simp only [h, ↓reduceIte]; have := hiff.1 h; omega
    · simp only [h, ↓reduceIte]; have := mt hiff.2 h; omega

/-- The Legendre sum of `0` vanishes. -/
theorem legendreSum_zero (p : Nat) : ∀ K, legendreSum p 0 K = 0
  | 0 => rfl
  | K + 1 => by simp [legendreSum, legendreSum_zero p K]

/-- **Legendre's formula** (1808). For a prime `p` and any `K` with `n < pᴷ`,
`vₚ(n!) = ⌊n/p⌋ + ⌊n/p²⌋ + ⋯ + ⌊n/pᴷ⌋`. -/
theorem legendre {p : Nat} (hp : Prime p) : ∀ n K, n < p ^ K → vp p (fact n) = legendreSum p n K := by
  have hp1 : 1 < p := hp.1
  intro n
  induction n with
  | zero => intro K _; rw [legendreSum_zero]; exact vp_one hp1
  | succ n ih =>
    intro K hK
    rw [vp_fact_succ hp, ih K (by omega), legendreSum_succ hp1]
    have hv : vp p (n + 1) < K := by
      have hd := (pow_dvd_iff_le_vp (e := vp p (n + 1)) hp1 (show 0 < n + 1 by omega)).2 (Nat.le_refl _)
      have := Nat.le_of_dvd (Nat.succ_pos n) hd
      exact (Nat.pow_lt_pow_iff_right hp1).1 (by omega)
    omega

/-- `n < 2ⁿ ≤ pⁿ`: enough terms for Legendre's formula. -/
theorem lt_pow_self {p : Nat} (hp : 1 < p) : ∀ n, n < p ^ n
  | 0 => by simp
  | n + 1 => by
    have := lt_pow_self hp n
    rw [Nat.pow_succ]
    have : p ^ n * 2 ≤ p ^ n * p := Nat.mul_le_mul_left _ hp
    omega

/-- **Legendre's formula**, standard form: `vₚ(n!) = Σ_{k=1}^{n} ⌊n/pᵏ⌋`. -/
theorem legendre' {p : Nat} (hp : Prime p) (n : Nat) : vp p (fact n) = legendreSum p n n :=
  legendre hp n n (lt_pow_self hp.1 n)

/-! ## Prime factors of the central binomial coefficient -/

/-- `vₚ(C(2n, n)) + 2 · (Legendre sum of n) = Legendre sum of 2n`, for `2n < pᴷ`. -/
theorem vp_centralBinom {p n K : Nat} (hp : Prime p) (hK : 2 * n < p ^ K) :
    vp p (centralBinom n) + 2 * legendreSum p n K = legendreSum p (2 * n) K := by
  have h := centralBinom_mul_fact n
  have hc := centralBinom_pos n
  have hf := fact_pos n
  rw [← legendre hp _ K hK, ← legendre hp n K (by omega), ← h,
    vp_mul hp (Nat.mul_pos hc hf) hf, vp_mul hp hc hf]
  omega

/-- `⌊2n/q⌋ − 2⌊n/q⌋` is `0` or `1`. -/
theorem two_mul_div {n q : Nat} (hq : 0 < q) :
    2 * n / q = 2 * (n / q) ∨ 2 * n / q = 2 * (n / q) + 1 := by
  have hdm := Nat.div_add_mod n q
  have hlt := Nat.mod_lt n hq
  by_cases h : 2 * (n % q) < q
  · left
    have he : 2 * n = q * (2 * (n / q)) + 2 * (n % q) := by grind
    rw [he, Nat.mul_add_div hq, Nat.div_eq_of_lt h, Nat.add_zero]
  · right
    have he : 2 * n = q * (2 * (n / q) + 1) + (2 * (n % q) - q) := by grind
    rw [he, Nat.mul_add_div hq, Nat.div_eq_of_lt (show 2 * (n % q) - q < q by omega)]

/-- Each Legendre summand of `C(2n, n)` is `0` or `1`, and is `0` once `pᵏ > 2n`; so the
partial sums `D` satisfy `D ≤ K` and `p^D ≤ 2n` (unless `D = 0`). -/
theorem legendreSum_two_mul {p n : Nat} (hp : 1 < p) : ∀ K, ∃ D,
    legendreSum p (2 * n) K = 2 * legendreSum p n K + D ∧ D ≤ K ∧ (D = 0 ∨ p ^ D ≤ 2 * n) := by
  intro K
  induction K with
  | zero => exact ⟨0, rfl, Nat.le_refl 0, Or.inl rfl⟩
  | succ K ih =>
    obtain ⟨D, hD, hDK, hDp⟩ := ih
    simp only [legendreSum]
    have hq : 0 < p ^ (K + 1) := Nat.pow_pos (by omega)
    rcases two_mul_div (n := n) hq with h | h
    · exact ⟨D, by rw [hD, h]; omega, by omega, hDp⟩
    · refine ⟨D + 1, by rw [hD, h]; omega, by omega, Or.inr ?_⟩
      have hle : p ^ (K + 1) ≤ 2 * n := by
        apply Classical.byContradiction
        intro hgt
        rw [Nat.div_eq_of_lt (by omega)] at h
        omega
      exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hle

/-- **Prime powers dividing `C(2n, n)` are at most `2n`.** If `p` is prime, `e ≥ 1` and
`pᵉ ∣ C(2n, n)`, then `pᵉ ≤ 2n`. -/
theorem pow_dvd_centralBinom_le {p n e : Nat} (hp : Prime p) (he : 1 ≤ e)
    (h : p ^ e ∣ centralBinom n) : p ^ e ≤ 2 * n := by
  have hp1 : 1 < p := hp.1
  have h1 := vp_centralBinom (K := 2 * n) hp (lt_pow_self hp1 _)
  obtain ⟨D, hD, _, hDp⟩ := legendreSum_two_mul (n := n) hp1 (2 * n)
  have hv : vp p (centralBinom n) = D := by omega
  have hle := (pow_dvd_iff_le_vp hp1 (centralBinom_pos n)).1 h
  rcases hDp with h0 | h0
  · omega
  · exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h0

/-- A prime dividing `C(2n, n)` is at most `2n`. -/
theorem prime_dvd_centralBinom_le {p n : Nat} (hp : Prime p) (h : p ∣ centralBinom n) :
    p ≤ 2 * n := by
  have := pow_dvd_centralBinom_le (e := 1) hp (Nat.le_refl 1) (by simpa using h)
  simpa using this

/-- If `p² ∣ C(2n, n)` then `p² ≤ 2n`: primes above `√(2n)` divide `C(2n, n)` at most once. -/
theorem sq_dvd_centralBinom_le {p n : Nat} (hp : Prime p) (h : p * p ∣ centralBinom n) :
    p * p ≤ 2 * n := by
  have := pow_dvd_centralBinom_le (e := 2) hp (by omega) (by rw [Nat.pow_two]; exact h)
  rwa [Nat.pow_two] at this

/-- **Erdős's key observation.** For `n ≥ 3`, a prime `p` with `2n/3 < p ≤ n` does not divide
`C(2n, n)`: it occurs exactly twice in `(2n)!` and once in each factor `n!`. -/
theorem not_dvd_centralBinom {p n : Nat} (hp : Prime p) (hn : 3 ≤ n) (hpn : p ≤ n)
    (h3 : 2 * n < 3 * p) : ¬ p ∣ centralBinom n := by
  have hp1 : 1 < p := hp.1
  have hp3 : 3 ≤ p := by omega
  have hsq : 2 * n < p ^ 2 := by
    rw [Nat.pow_two]; have := Nat.mul_le_mul_right p hp3; omega
  have h1 := vp_centralBinom hp hsq
  have ppos : 0 < p := by omega
  have hd1 : n / p = 1 := by
    have a := (Nat.le_div_iff_mul_le ppos).2 (show 1 * p ≤ n by omega)
    have b := (Nat.div_lt_iff_lt_mul ppos).2 (show n < 2 * p by omega)
    omega
  have hd2 : 2 * n / p = 2 := by
    have a := (Nat.le_div_iff_mul_le ppos).2 (show 2 * p ≤ 2 * n by omega)
    have b := (Nat.div_lt_iff_lt_mul ppos).2 (show 2 * n < 3 * p by omega)
    omega
  have hd3 : n / p ^ 2 = 0 := Nat.div_eq_of_lt (by omega)
  have hd4 : 2 * n / p ^ 2 = 0 := Nat.div_eq_of_lt hsq
  simp only [legendreSum, Nat.zero_add, Nat.pow_one, hd1, hd2, hd3, hd4] at h1
  have hv : vp p (centralBinom n) = 0 := by omega
  intro hdvd
  have := (pow_dvd_iff_le_vp (e := 1) hp1 (centralBinom_pos n)).1 (by simpa using hdvd)
  omega

end Foundations.NumberTheory
