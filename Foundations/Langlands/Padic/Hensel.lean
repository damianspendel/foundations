import Foundations.Langlands.Padic.Integers

/-!
# Hensel's lemma

**Hensel's lemma** (Hensel, 1897–1908) is the `p`-adic Newton's method: if a polynomial `f` with
integer coefficients has a root `a` modulo `p` that is *simple* (`f'(a) ≢ 0 mod p`), then `a`
lifts to a genuine root `x ∈ ℤₚ` with `x ≡ a (mod p)`. The proof lifts the root one power of `p`
at a time. If `f(s) ≡ 0 (mod pⁿ⁺¹)`, Taylor's formula

  `f(s + h) = f(s) + h · f'(s) + h² · (…)`

with `h = t · pⁿ⁺¹` shows that `f(s + h) ≡ 0 (mod pⁿ⁺²)` as soon as
`f(s)/pⁿ⁺¹ + t · f'(s) ≡ 0 (mod p)`, which can be solved for `t` because `f'(s) ≡ f'(a)` is
invertible mod `p`. The successive lifts form a `p`-adic sequence, i.e. an element of `ℤₚ`.

As examples: `√2 ∈ ℤ₇` (from `3² ≡ 2 mod 7`) and `√(−1) ∈ ℤ₅` (from `2² ≡ −1 mod 5`). Since `√2`
is irrational, the first shows that ℤ₇ is strictly bigger than ℤ. The second shows that ℤ₅ — and
hence any field containing it, such as ℚ₅ — cannot be ordered: in an ordered ring `−1` is never a
square. More generally, for every odd prime `p`, `1 − p` is a square in ℤₚ, so ℤₚ is never an
ordered ring the way ℝ is.

Hensel's lemma is the basic tool of the *local* theory: a local field is one where questions
can be settled modulo `p` and then lifted. Combined with the local–global principle (Hasse),
it reduces many global questions about ℚ to congruences.

Polynomials are represented by their lists of integer coefficients, constant term first.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-! ## Polynomials over ℤ -/

/-- Evaluation of the polynomial with coefficient list `[c₀, c₁, …]` at an integer, by Horner's
rule: `c₀ + x (c₁ + x (c₂ + …))`. -/
def peval : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * peval cs x

/-- Evaluation of the *derivative* `f'` at an integer: if `f = c + X · g` then
`f' = g + X · g'`. -/
def pderiv : List Int → Int → Int
  | [], _ => 0
  | _ :: cs, x => peval cs x + x * pderiv cs x

/-- `a − b` divides `f(a) − f(b)`. -/
theorem sub_dvd_peval (f : List Int) (a b : Int) : a - b ∣ peval f a - peval f b := by
  induction f with
  | nil => simp [peval]
  | cons c cs ih =>
    simp only [peval]
    rw [show c + a * peval cs a - (c + b * peval cs b) =
      a * (peval cs a - peval cs b) + (a - b) * peval cs b by grind]
    exact Int.dvd_add (Int.dvd_trans ih (Int.dvd_mul_left _ _)) (Int.dvd_mul_right _ _)

/-- `a − b` divides `f'(a) − f'(b)`. -/
theorem sub_dvd_pderiv (f : List Int) (a b : Int) : a - b ∣ pderiv f a - pderiv f b := by
  induction f with
  | nil => simp [pderiv]
  | cons c cs ih =>
    simp only [pderiv]
    rw [show peval cs a + a * pderiv cs a - (peval cs b + b * pderiv cs b) =
      (peval cs a - peval cs b) + (a * (pderiv cs a - pderiv cs b) + (a - b) * pderiv cs b)
      by grind]
    exact Int.dvd_add (sub_dvd_peval cs a b)
      (Int.dvd_add (Int.dvd_trans ih (Int.dvd_mul_left _ _)) (Int.dvd_mul_right _ _))

/-- **Taylor's formula to second order.** `f(s + h) = f(s) + h · f'(s) + h² · G` for some
integer `G`. -/
theorem taylor (f : List Int) (s h : Int) :
    ∃ G, peval f (s + h) = peval f s + h * pderiv f s + h * h * G := by
  induction f with
  | nil => exact ⟨0, by simp [peval, pderiv]⟩
  | cons c cs ih =>
    obtain ⟨G, hG⟩ := ih
    refine ⟨pderiv cs s + (s + h) * G, ?_⟩
    simp only [peval, pderiv, hG]
    grind

/-! ## Polynomials on ℤₚ -/

/-- Evaluating a polynomial termwise on a `p`-adic sequence gives a `p`-adic sequence. -/
def PSeq.peval {p : Nat} (f : List Int) (x : PSeq p) : PSeq p :=
  ⟨fun n => Padic.peval f (x.seq n), fun n => Int.dvd_trans (x.coh n) (sub_dvd_peval f _ _)⟩

/-- Evaluation of an integer polynomial at a `p`-adic integer. -/
def Zp.peval {p : Nat} (f : List Int) : Zp p → Zp p :=
  Quotient.lift (fun x => Zp.mk (PSeq.peval f x)) fun _ _ h =>
    Quotient.sound fun n => Int.dvd_trans (h n) (sub_dvd_peval f _ _)

/-- Evaluation on `ℤₚ` is Horner's rule in the ring `ℤₚ`: for the empty list it is `0`. -/
theorem Zp.peval_nil {p : Nat} (x : Zp p) : Zp.peval [] x = 0 := by
  induction x using Zp.ind; rfl

/-- Evaluation on `ℤₚ` is Horner's rule in the ring `ℤₚ`: `(c :: f)(x) = c + x · f(x)`. -/
theorem Zp.peval_cons {p : Nat} (c : Int) (f : List Int) (x : Zp p) :
    Zp.peval (c :: f) x = (c : Zp p) + x * Zp.peval f x := by
  induction x using Zp.ind; rfl

/-! ## Hensel's lemma -/

/-- An inverse modulo a prime: if `p ∤ c` there is `u` with `p ∣ u c − 1`. -/
theorem exists_inv_mod {p : Nat} (hp : Prime p) {c : Int} (hc : ¬ (p : Int) ∣ c) :
    ∃ u : Int, (p : Int) ∣ u * c - 1 := by
  obtain ⟨x, y, hxy⟩ := bezout c.natAbs p
  have hg : gcd c.natAbs p = 1 := by
    have ⟨h1, h2⟩ := gcd_dvd c.natAbs p
    rcases hp.2 _ h2 with h | h
    · exact h
    · exfalso; apply hc; rw [h] at h1
      exact Int.dvd_natAbs.1 (Int.ofNat_dvd.2 h1)
  rw [hg] at hxy
  rcases Int.natAbs_eq c with h | h
  · refine ⟨x, ⟨-y, ?_⟩⟩
    rw [h]; grind
  · refine ⟨-x, ⟨-y, ?_⟩⟩
    rw [h]; grind

/-- One Newton step: from `pⁿ⁺¹ ∣ f(s)` and `p ∣ u f'(s) − 1`, the lift
`s' = s − (f(s)/pⁿ⁺¹) u pⁿ⁺¹` satisfies `pⁿ⁺² ∣ f(s')`. -/
theorem newton_step {p : Nat} (f : List Int) (s u : Int) (n : Nat)
    (hs : (p : Int) ^ (n + 1) ∣ peval f s) (hu : (p : Int) ∣ u * pderiv f s - 1) :
    (p : Int) ^ (n + 2) ∣
      peval f (s + (-(peval f s / (p : Int) ^ (n + 1)) * u) * (p : Int) ^ (n + 1)) := by
  generalize hq : peval f s / (p : Int) ^ (n + 1) = q
  have hfs : peval f s = q * (p : Int) ^ (n + 1) := by rw [← hq, Int.ediv_mul_cancel hs]
  obtain ⟨G, hG⟩ := taylor f s ((-q * u) * (p : Int) ^ (n + 1))
  rw [hG, hfs]
  obtain ⟨w, hw⟩ := hu
  have e : q * (p : Int) ^ (n + 1) + -q * u * (p : Int) ^ (n + 1) * pderiv f s +
      -q * u * (p : Int) ^ (n + 1) * (-q * u * (p : Int) ^ (n + 1)) * G =
      (p : Int) ^ (n + 2) * (-q * w + q * q * u * u * (p : Int) ^ n * G) := by
    rw [show (p : Int) ^ (n + 2) = (p : Int) ^ (n + 1) * p by rw [Int.pow_succ],
      show (p : Int) ^ (n + 1) = (p : Int) ^ n * p by rw [Int.pow_succ]]
    have : u * pderiv f s = p * w + 1 := by omega
    grind
  rw [e]; exact Int.dvd_mul_right _ _

/-- **Hensel's lemma.** Let `p` be prime and `f` a polynomial with integer coefficients. If
`f(a) ≡ 0 (mod p)` and `f'(a) ≢ 0 (mod p)`, then there is a `p`-adic integer `x` with `f(x) = 0`
and `x ≡ a (mod p)`. -/
theorem hensel {p : Nat} (hp : Prime p) (f : List Int) (a : Int)
    (h1 : (p : Int) ∣ peval f a) (h2 : ¬ (p : Int) ∣ pderiv f a) :
    ∃ x : Zp p, Zp.peval f x = 0 ∧ Zp.ModPow 1 x (a : Zp p) := by
  obtain ⟨u, hu⟩ := exists_inv_mod hp h2
  -- the Newton iteration
  let step : Nat → Int → Int := fun n s =>
    s + (-(peval f s / (p : Int) ^ (n + 1)) * u) * (p : Int) ^ (n + 1)
  let s : Nat → Int := fun n => Nat.rec a (fun k acc => step k acc) n
  have hs_succ : ∀ n, s (n + 1) = step n (s n) := fun _ => rfl
  have hstep : ∀ n, (p : Int) ^ (n + 1) ∣ s (n + 1) - s n := by
    intro n; rw [hs_succ]
    show _ ∣ s n + _ - s n
    rw [show ∀ a b : Int, a + b - a = b from fun _ _ => by omega]
    exact Int.dvd_mul_left _ _
  -- invariant: `pⁿ⁺¹ ∣ f(sₙ)` and `p ∣ sₙ − a`
  have inv : ∀ n, (p : Int) ^ (n + 1) ∣ peval f (s n) ∧ (p : Int) ∣ s n - a := by
    intro n
    induction n with
    | zero => exact ⟨by show (p : Int) ^ 1 ∣ peval f a; rw [Int.pow_one]; exact h1, by show _ ∣ a - a; rw [Int.sub_self]; exact Int.dvd_zero _⟩
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hpn : (p : Int) ∣ (p : Int) ^ (n + 1) := by
        rw [Int.pow_succ]; exact Int.dvd_mul_left _ _
      refine ⟨?_, ?_⟩
      · have hd : (p : Int) ∣ pderiv f (s n) - pderiv f a :=
          Int.dvd_trans ih2 (sub_dvd_pderiv f _ _)
        have hu' : (p : Int) ∣ u * pderiv f (s n) - 1 := by
          rw [show u * pderiv f (s n) - 1 = u * (pderiv f (s n) - pderiv f a) +
            (u * pderiv f a - 1) by grind]
          exact Int.dvd_add (Int.dvd_trans hd (Int.dvd_mul_left _ _)) hu
        rw [hs_succ]; exact newton_step f (s n) u n ih1 hu'
      · rw [show s (n + 1) - a = (s (n + 1) - s n) + (s n - a) by omega]
        exact Int.dvd_add (Int.dvd_trans hpn (hstep n)) ih2
  let x : PSeq p := ⟨s, fun n => by
    have : (p : Int) ^ n ∣ (p : Int) ^ (n + 1) := by rw [Int.pow_succ]; exact Int.dvd_mul_right _ _
    exact Int.dvd_trans this (hstep n)⟩
  refine ⟨Zp.mk x, ?_, ?_⟩
  · show Zp.mk (PSeq.peval f x) = Zp.mk (PSeq.const 0)
    apply Zp.mk_eq_mk.2
    intro n
    show _ ∣ peval f (s n) - 0
    rw [Int.sub_zero]
    have : (p : Int) ^ n ∣ (p : Int) ^ (n + 1) := by rw [Int.pow_succ]; exact Int.dvd_mul_right _ _
    exact Int.dvd_trans this (inv n).1
  · show (p : Int) ^ 1 ∣ s 1 - a
    rw [Int.pow_one]; exact (inv 1).2

/-! ## Examples -/

/-- `7` is prime. -/
theorem prime_seven : Prime 7 :=
  ⟨by omega, fun d hd => by
    have := Nat.le_of_dvd (by omega) hd
    have key : ∀ d, d < 8 → d ∣ 7 → d = 1 ∨ d = 7 := by decide
    exact key d (by omega) hd⟩

/-- `5` is prime. -/
theorem prime_five : Prime 5 :=
  ⟨by omega, fun d hd => by
    have := Nat.le_of_dvd (by omega) hd
    have key : ∀ d, d < 6 → d ∣ 5 → d = 1 ∨ d = 5 := by decide
    exact key d (by omega) hd⟩

/-- The polynomial `X² − c` evaluated at a `p`-adic integer is `x · x − c`. -/
theorem peval_sq_sub {p : Nat} (c : Int) (x : Zp p) :
    Zp.peval [-c, 0, 1] x = x * x - (c : Zp p) := by
  rw [Zp.peval_cons, Zp.peval_cons, Zp.peval_cons, Zp.peval_nil]
  have h0 : ((0 : Int) : Zp p) = 0 := rfl
  have h1 : ((1 : Int) : Zp p) = 1 := rfl
  have hn : ((-c : Int) : Zp p) = -(c : Zp p) := Lean.Grind.Ring.intCast_neg c
  rw [h0, h1, hn]; grind

/-- **`√2 ∈ ℤ₇`.** There is a 7-adic integer `x` with `x² = 2` and `x ≡ 3 (mod 7)`. -/
theorem sqrt_two_Z7 : ∃ x : Zp 7, x * x = 2 ∧ Zp.ModPow 1 x (3 : Int) := by
  obtain ⟨x, hx, hx3⟩ := hensel prime_seven [-2, 0, 1] 3 (by decide) (by decide)
  refine ⟨x, ?_, hx3⟩
  rw [peval_sq_sub] at hx
  have : ((2 : Int) : Zp 7) = 2 := rfl
  rw [this] at hx; grind

/-- **`√(−1) ∈ ℤ₅`.** There is a 5-adic integer `x` with `x² = −1` and `x ≡ 2 (mod 5)`. -/
theorem sqrt_neg_one_Z5 : ∃ x : Zp 5, x * x = -1 ∧ Zp.ModPow 1 x (2 : Int) := by
  obtain ⟨x, hx, hx2⟩ := hensel prime_five [1, 0, 1] 2 (by decide) (by decide)
  refine ⟨x, ?_, hx2⟩
  have := peval_sq_sub (p := 5) (-1) x
  rw [show -(-1 : Int) = 1 by rfl] at this
  rw [this] at hx
  have : ((-1 : Int) : Zp 5) = -1 := by
    rw [Lean.Grind.Ring.intCast_neg]; rfl
  rw [this] at hx; grind

/-- No integer squares to `2`. -/
theorem int_sq_ne_two (m : Int) : m * m ≠ 2 := by
  intro h
  have h' : m.natAbs * m.natAbs = 2 := by
    have := congrArg Int.natAbs h; rwa [Int.natAbs_mul] at this
  rcases Nat.lt_or_ge m.natAbs 2 with h2 | h2
  · have : m.natAbs * m.natAbs ≤ 1 * 1 := Nat.mul_le_mul (by omega) (by omega); omega
  · have := Nat.mul_le_mul h2 h2; omega

/-- **ℤ₇ is bigger than ℤ.** The 7-adic square root of `2` is not an integer. -/
theorem Z7_ne_Z : ∃ x : Zp 7, ∀ m : Int, x ≠ (m : Zp 7) := by
  obtain ⟨x, hx, -⟩ := sqrt_two_Z7
  refine ⟨x, fun m hm => int_sq_ne_two m ?_⟩
  apply Zp.intCast_injective (p := 7) (by omega)
  rw [hm] at hx
  have e : ((m * m : Int) : Zp 7) = (m : Zp 7) * (m : Zp 7) := rfl
  rw [e, hx]; rfl

/-- **ℤₚ is not ordered like ℝ (odd `p`).** For an odd prime `p`, there is no relation `≤` on
`ℤₚ` that is preserved by adding a constant, makes every square non-negative, and has `¬ 1 ≤ 0`.
(Every ordered ring has these properties; the obstruction is that `1 − p` is a square in ℤₚ.) -/
theorem not_ordered {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) (le : Zp p → Zp p → Prop)
    (htrans : ∀ a b c, le a b → le b c → le a c)
    (hadd : ∀ a b c, le a b → le (a + c) (b + c))
    (hsq : ∀ x, le 0 (x * x)) (h10 : ¬ le 1 0) : False := by
  -- `1 − p` is a square, by Hensel applied to `X² − (1 − p)` at `1`.
  obtain ⟨y, hy, -⟩ := hensel hp [-(1 - (p : Int)), 0, 1] 1
    (by show (p : Int) ∣ -(1 - (p : Int)) + 1 * (0 + 1 * (1 + 1 * 0)); exact ⟨1, by omega⟩)
    (by
      show ¬ (p : Int) ∣ (0 + 1 * (1 + 1 * 0)) + 1 * ((1 + 1 * 0) + 1 * (0 + 1 * 0))
      intro ⟨k, hk⟩
      have := hp.1
      rcases Int.lt_or_le k 1 with h | h
      · have : k ≤ 0 := by omega
        have : (p : Int) * k ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) this
        omega
      · have : (p : Int) * 1 ≤ p * k := Int.mul_le_mul_of_nonneg_left h (by omega)
        omega)
  rw [peval_sq_sub] at hy
  have hy' : y * y = 1 - ((p : Int) : Zp p) := by
    have : (((1 - (p : Int)) : Int) : Zp p) = 1 - ((p : Int) : Zp p) := by
      rw [Lean.Grind.Ring.intCast_sub]; rfl
    rw [← this]; grind
  -- `0 ≤ n` for every natural `n`, then `0 ≤ 1 − p ≤ 1 − 2 = −1`
  have h01 : le 0 1 := by have := hsq 1; rwa [show (1 : Zp p) * 1 = 1 by grind] at this
  have hnat : ∀ n : Nat, le 0 (n : Zp p) := by
    intro n
    induction n with
    | zero => have := hsq 0; rwa [show (0 : Zp p) * 0 = 0 by grind] at this
    | succ n ih =>
      have h := hadd 0 1 (n : Zp p) h01
      rw [show (0 : Zp p) + (n : Zp p) = (n : Zp p) by grind,
        show (1 : Zp p) + (n : Zp p) = ((n + 1 : Nat) : Zp p) by grind] at h
      exact htrans _ _ _ ih h
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.1; omega⟩
  have hsq' := hsq y
  rw [hy'] at hsq'
  have h1 := hadd _ _ ((m : Zp p) + 1) hsq'
  have hpc : ((p : Int) : Zp p) = ((m : Nat) : Zp p) + 1 + 1 := by
    rw [Lean.Grind.Ring.intCast_natCast, hm]; grind
  rw [hpc, show (0 : Zp p) + ((m : Zp p) + 1) = (m : Zp p) + 1 by grind,
    show (1 : Zp p) - ((m : Zp p) + 1 + 1) + ((m : Zp p) + 1) = 0 by grind] at h1
  -- `m + 1 ≤ 0` and `0 ≤ m`, hence `1 ≤ 0`
  have h2 := hadd 0 (m : Zp p) 1 (hnat m)
  rw [show (0 : Zp p) + 1 = 1 by grind] at h2
  exact h10 (htrans _ _ _ h2 h1)

end Foundations.Langlands.Padic
