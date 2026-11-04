import Foundations.Langlands.Padic.ProductFormula
import Foundations.Numbers.Log

/-!
# Absolute values on ℚ

An **absolute value** on ℚ is a function `φ : ℚ → ℝ` that is non-negative, vanishes only at `0`,
is multiplicative and satisfies the triangle inequality. Two examples are already at hand: the
ordinary absolute value `|·|_∞` and, for each prime `p`, the `p`-adic absolute value `|·|ₚ` of
`Valuation`, now viewed as real-valued. Raising an absolute value to a power `s` with `0 < s ≤ 1`
gives another one, so absolute values are naturally considered up to **equivalence**:
`ψ ~ φ` when `ψ = φ^s` for some `s > 0`. To avoid real exponents we phrase this with the natural
logarithm of `Foundations.Numbers.Log`:

  `ψ ~ φ  :⇔  ∃ s > 0, ∀ x ≠ 0, log ψ(x) = s · log φ(x)`,

which is exactly `ψ(x) = exp(s · log φ(x)) = φ(x)^s`.

This file sets up the definitions, the two families of examples, the facts about logarithms we
need, and proves the easy half of Ostrowski's theorem: the absolute values `|·|_∞`, `|·|₂`,
`|·|₃`, `|·|₅`, … are pairwise inequivalent. The hard half — there are no others — is in
`Ostrowski`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Foundations.NumberTheory Lean.Grind R

/-! ## Logarithms -/

/-- `log (y^k) = k · log y` for `y > 0`. -/
theorem log_npow {y : R} (hy : 0 < y) : ∀ k : Nat, log (y ^ k) = (k : R) * log y
  | 0 => by rw [Semiring.pow_zero, log_one]; grind
  | k + 1 => by
    rw [Semiring.pow_succ, log_mul (npow_pos hy k) hy, log_npow hy k]; grind

/-- `log (y⁻¹) = −log y` for `y > 0`. -/
theorem log_inv {y : R} (hy : 0 < y) : log y⁻¹ = -log y := by
  have h := log_mul hy (inv_pos' hy)
  rw [Field.mul_inv_cancel (by grind), log_one] at h
  grind

/-- `log` is monotone on the positive reals. -/
theorem log_le_log {x y : R} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y := by
  rcases (by grind : x < y ∨ x = y) with h | h
  · exact Std.le_of_lt (log_strictMono hx h)
  · rw [h]; exact Std.le_refl _

/-- `log y > 0` for `y > 1`. -/
theorem log_pos {y : R} (hy : 1 < y) : 0 < log y := by
  have := log_strictMono (by grind : (0 : R) < 1) hy; rwa [log_one] at this

/-- `log y < 0` for `0 < y < 1`. -/
theorem log_neg {y : R} (hy : 0 < y) (hy1 : y < 1) : log y < 0 := by
  have := log_strictMono hy hy1; rwa [log_one] at this

/-- `log y ≥ 0` for `y ≥ 1`. -/
theorem log_nonneg {y : R} (hy : 1 ≤ y) : 0 ≤ log y := by
  have := log_le_log (by grind : (0 : R) < 1) hy; rwa [log_one] at this

/-- `log y ≤ y − 1` for `y ≥ 1` (from `1 + x ≤ exp x`). -/
theorem log_le_sub_one {y : R} (hy : 1 ≤ y) : log y ≤ y - 1 := by
  have h := one_add_le_exp (log_nonneg hy)
  rw [exp_log (by grind)] at h; grind

/-- From `log x = log y` with `x, y > 0` we get `x = y`. -/
theorem log_injective {x y : R} (hx : 0 < x) (hy : 0 < y) (h : log x = log y) : x = y := by
  rw [← exp_log hx, ← exp_log hy, h]

/-! ## Rationals inside the reals -/

/-- `ofQ` reflects equality. -/
theorem ofQ_inj {a b : Q} (h : ofQ a = ofQ b) : a = b :=
  Std.le_antisymm (ofQ_le.1 (by rw [h]; exact Std.le_refl _))
    (ofQ_le.1 (by rw [h]; exact Std.le_refl _))

/-- `ofQ` preserves natural powers. -/
theorem ofQ_npow (a : Q) : ∀ k : Nat, ofQ (a ^ k) = ofQ a ^ k
  | 0 => rfl
  | k + 1 => by
    show ofQ (a ^ k * a) = ofQ a ^ k * ofQ a
    rw [ofQ_mul, ofQ_npow a k]

/-- `ofQ` preserves inverses. -/
theorem ofQ_inv (a : Q) : ofQ a⁻¹ = (ofQ a)⁻¹ := by
  by_cases ha : a = 0
  · rw [ha, Q.inv_zero]; exact (Field.inv_zero (α := R)).symm
  · have h : ofQ a * ofQ a⁻¹ = 1 := by rw [← ofQ_mul, Field.mul_inv_cancel ha]; rfl
    have hne : ofQ a ≠ 0 := fun h0 => ha (ofQ_inj (by rw [h0]; rfl))
    have := Field.mul_inv_cancel hne
    grind

/-! ## Absolute values -/

/-- **Absolute values on ℚ.** A real-valued function on ℚ that is non-negative, vanishes exactly
at `0`, is multiplicative and satisfies the triangle inequality. -/
structure AbsVal where
  /-- The function itself. -/
  f : Q → R
  /-- Non-negativity. -/
  nonneg : ∀ x, 0 ≤ f x
  /-- Only `0` has absolute value `0`. -/
  eq_zero : ∀ x, f x = 0 → x = 0
  /-- `0` has absolute value `0`. -/
  map_zero : f 0 = 0
  /-- Multiplicativity. -/
  mul : ∀ x y, f (x * y) = f x * f y
  /-- The triangle inequality. -/
  triangle : ∀ x y, f (x + y) ≤ f x + f y

/-- An absolute value is **trivial** if it is `1` at every nonzero rational; **nontrivial**
otherwise. -/
def AbsVal.Nontrivial (φ : AbsVal) : Prop := ∃ x : Q, x ≠ 0 ∧ φ.f x ≠ 1

/-- **Equivalence of absolute values.** `ψ` is equivalent to `φ` if `ψ = φ^s` for some
`s > 0`, phrased with logarithms: `log ψ(x) = s · log φ(x)` for all `x ≠ 0`. -/
def AbsVal.Equiv (φ ψ : AbsVal) : Prop :=
  ∃ s : R, 0 < s ∧ ∀ x : Q, x ≠ 0 → log (ψ.f x) = s * log (φ.f x)

namespace AbsVal

variable (φ : AbsVal)

/-- Nonzero rationals have positive absolute value. -/
theorem pos {x : Q} (hx : x ≠ 0) : 0 < φ.f x := by
  have h1 := φ.nonneg x
  have h2 : φ.f x ≠ 0 := fun h => hx (φ.eq_zero x h)
  grind

/-- `φ(1) = 1`. -/
theorem map_one : φ.f 1 = 1 := by
  have h := φ.mul 1 1
  rw [Semiring.mul_one] at h
  have hp := φ.pos (x := 1) (by grind)
  have := Field.mul_inv_cancel (show φ.f 1 ≠ 0 by grind)
  have e : φ.f 1 * φ.f 1 * (φ.f 1)⁻¹ = φ.f 1 * (φ.f 1)⁻¹ := by rw [← h]
  rw [Semiring.mul_assoc, this, Semiring.mul_one] at e
  exact e

/-- `φ(−1) = 1`. -/
theorem map_neg_one : φ.f (-1) = 1 := by
  have h := φ.mul (-1) (-1)
  rw [show (-1 : Q) * -1 = 1 by grind, φ.map_one] at h
  have hp := φ.pos (x := -1) (by grind)
  have : (φ.f (-1) - 1) * (φ.f (-1) + 1) = 0 := by grind
  rcases Field.of_mul_eq_zero this with h | h <;> grind

/-- `φ(−x) = φ(x)`. -/
theorem map_neg (x : Q) : φ.f (-x) = φ.f x := by
  rw [show -x = -1 * x by grind, φ.mul, φ.map_neg_one]; grind

/-- `φ(x⁻¹) = φ(x)⁻¹`. -/
theorem map_inv (x : Q) : φ.f x⁻¹ = (φ.f x)⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, Q.inv_zero, φ.map_zero]; exact (Field.inv_zero (α := R)).symm
  · have h := φ.mul x x⁻¹
    rw [Field.mul_inv_cancel hx, φ.map_one] at h
    have := φ.pos hx
    have := Field.mul_inv_cancel (show φ.f x ≠ 0 by grind)
    grind

/-- `φ(n) ≤ n` for natural numbers `n` (by the triangle inequality). -/
theorem map_nat_le : ∀ n : Nat, φ.f (n : Q) ≤ (n : R)
  | 0 => by
    rw [show ((0 : Nat) : Q) = 0 from rfl, φ.map_zero]; exact Std.le_refl _
  | n + 1 => by
    have h := φ.triangle (n : Q) 1
    rw [φ.map_one] at h
    have := map_nat_le n
    rw [show ((n + 1 : Nat) : Q) = (n : Q) + 1 by grind]
    grind

/-- `log φ(n/d) = log φ(|n|) − log φ(d)` for `n ≠ 0`, `d > 0`. -/
theorem log_mk {n d : Int} (hd : 0 < d) (hn : n ≠ 0) :
    log (φ.f (Q.mk n d hd)) = log (φ.f (n.natAbs : Q)) - log (φ.f (d.natAbs : Q)) := by
  have hnQ : ((n.natAbs : Nat) : Q) ≠ 0 := fun h => by
    have := (mk_eq_zero_iff Int.one_pos).1 h; omega
  have hdQ : ((d.natAbs : Nat) : Q) ≠ 0 := fun h => by
    have := (mk_eq_zero_iff Int.one_pos).1 h; omega
  have e1 : φ.f (n : Q) = φ.f (n.natAbs : Q) := by
    rcases Int.natAbs_eq n with h | h
    · rw [show ((n.natAbs : Nat) : Q) = (((n.natAbs : Nat) : Int) : Q) from rfl, ← h]
    · rw [show ((n.natAbs : Nat) : Q) = (((n.natAbs : Nat) : Int) : Q) from rfl,
        show (n : Q) = ((-((n.natAbs : Nat) : Int) : Int) : Q) by rw [← h], ← φ.map_neg]
      congr 1; grind
  have e2 : (d : Q) = ((d.natAbs : Nat) : Q) := by
    rw [show ((d.natAbs : Nat) : Q) = (((d.natAbs : Nat) : Int) : Q) from rfl]
    congr 1; omega
  rw [mk_eq_mul_inv, φ.mul, φ.map_inv, e1, e2, log_mul (φ.pos hnQ) (inv_pos' (φ.pos hdQ)),
    log_inv (φ.pos hdQ)]
  grind

end AbsVal

/-! ## The examples: `|·|_∞` and `|·|ₚ` -/

/-- **The archimedean absolute value** `|·|_∞`: the ordinary absolute value, as a real number. -/
noncomputable def absInf : AbsVal where
  f x := ofQ (Q.abs x)
  nonneg x := by
    have := ofQ_le.2 (Q.abs_nonneg x); exact this
  eq_zero x h := by
    have h0 : Q.abs x = 0 := ofQ_inj h
    rcases Q.abs_cases x with h1 | h1 <;> grind
  map_zero := by rw [Q.abs_zero]; rfl
  mul x y := by rw [Q.abs_mul, ofQ_mul]
  triangle x y := by rw [← ofQ_add]; exact ofQ_le.2 (Q.abs_add x y)

/-- **The `p`-adic absolute value** `|·|ₚ` as a real-valued absolute value (`p` prime). -/
noncomputable def absP {p : Nat} (hp : Prime p) : AbsVal where
  f x := ofQ (padicAbs p x)
  nonneg x := ofQ_le.2 (padicAbs_nonneg hp x)
  eq_zero x h := (padicAbs_eq_zero hp).1 (ofQ_inj h)
  map_zero := by rw [padicAbs_zero]; rfl
  mul x y := by rw [padicAbs_mul hp, ofQ_mul]
  triangle x y := by rw [← ofQ_add]; exact ofQ_le.2 (padicAbs_add hp x y)

/-- A prime, as a real number, is greater than `1`. -/
theorem one_lt_prime_real {p : Nat} (hp : Prime p) : (1 : R) < (p : R) := by
  have := hp.1
  have : ((1 : Nat) : R) < (p : R) := OrderedRing.natCast_lt_natCast_of_lt _ _ (by omega)
  grind

/-- `log |x|_∞ = log |n| − log d` for `x = n/d ≠ 0`. -/
theorem log_absInf_mk {n d : Int} (hd : 0 < d) (hn : n ≠ 0) :
    log (absInf.f (Q.mk n d hd)) = log (n.natAbs : R) - log (d.natAbs : R) := by
  rw [absInf.log_mk hd hn]; rfl

/-- **The `p`-adic absolute value in logarithmic form.** `log |x|ₚ = −vₚ(x) · log p` for
`x ≠ 0`. -/
theorem log_absP {p : Nat} (hp : Prime p) {x : Q} (hx : x ≠ 0) :
    log ((absP hp).f x) = -((vQ p x : Int) : R) * log (p : R) := by
  induction x using Q.ind with | h n d hd => ?_
  have hn : n ≠ 0 := fun h => hx ((mk_eq_zero_iff hd).2 h)
  have hpR : (0 : R) < (p : R) := by have := one_lt_prime_real hp; grind
  show log (ofQ (padicAbs p (Q.mk n d hd))) = _
  rw [padicAbs_mk hp hd hn, ofQ_mul, ofQ_inv, ofQ_npow, ofQ_npow, ofQ_natCast,
    log_mul (npow_pos hpR _) (inv_pos' (npow_pos hpR _)), log_inv (npow_pos hpR _),
    log_npow hpR, log_npow hpR, vQ_mk hp hd hn]
  unfold vZ
  rw [Ring.intCast_sub, Ring.intCast_natCast, Ring.intCast_natCast]
  grind

/-- `log |p|_q = 0` for distinct primes `p, q`. -/
theorem log_absP_other {p q : Nat} (hp : Prime p) (hq : Prime q) (hpq : p ≠ q) :
    log ((absP hq).f (p : Q)) = 0 := by
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  rw [log_absP hq hp0]
  have : vQ q (p : Q) = 0 := by
    rw [show (p : Q) = ((p : Int) : Q) from rfl, vQ_intCast hq (by have := hp.1; omega)]
    unfold vZ
    show ((vp q p : Nat) : Int) = 0
    rw [vp_prime hq hp]; simp [Ne.symm hpq]
  rw [this]; grind

/-- `log |p|ₚ = −log p`. -/
theorem log_absP_self {p : Nat} (hp : Prime p) : log ((absP hp).f (p : Q)) = -log (p : R) := by
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  rw [log_absP hp hp0, vQ_self hp]; grind

/-- `log |p|_∞ = log p`. -/
theorem log_absInf_nat (p : Nat) : log (absInf.f (p : Q)) = log (p : R) := by
  show log (ofQ (Q.abs (p : Q))) = _
  rw [Q.abs_of_nonneg (OrderedRing.natCast_nonneg)]; rfl

/-- **Inequivalence of the places.** For distinct primes `p ≠ q`, no absolute value is
equivalent both to `|·|ₚ` and to `|·|_q`. -/
theorem not_equiv_absP_absP {p q : Nat} (hp : Prime p) (hq : Prime q) (hpq : p ≠ q)
    (ψ : AbsVal) (h1 : (absP hp).Equiv ψ) (h2 : (absP hq).Equiv ψ) : False := by
  obtain ⟨s, hs, hs'⟩ := h1
  obtain ⟨t, _, ht'⟩ := h2
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  have e1 := hs' _ hp0
  have e2 := ht' _ hp0
  rw [log_absP_self hp] at e1
  rw [log_absP_other hp hq hpq] at e2
  have := log_pos (one_lt_prime_real hp)
  have := OrderedRing.mul_pos hs this
  grind

/-- **Inequivalence of the places.** No absolute value is equivalent both to `|·|_∞` and to
some `|·|ₚ`. -/
theorem not_equiv_absInf_absP {p : Nat} (hp : Prime p) (ψ : AbsVal)
    (h1 : absInf.Equiv ψ) (h2 : (absP hp).Equiv ψ) : False := by
  obtain ⟨s, hs, hs'⟩ := h1
  obtain ⟨t, ht, ht'⟩ := h2
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  have e1 := hs' _ hp0
  have e2 := ht' _ hp0
  rw [log_absInf_nat] at e1
  rw [log_absP_self hp] at e2
  have hl := log_pos (one_lt_prime_real hp)
  have := OrderedRing.mul_pos hs hl
  have := OrderedRing.mul_pos ht hl
  grind

end Foundations.Langlands.Padic
