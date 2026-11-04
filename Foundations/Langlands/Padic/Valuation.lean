import Foundations.NumberTheory.Binomial
import Foundations.Numbers.OrderedField

/-!
# The `p`-adic valuation and the `p`-adic absolute value on ℚ

The integers carry, besides their familiar size, one notion of size for every prime `p`: an
integer is *`p`-adically small* when it is divisible by a high power of `p`. Kurt Hensel, in
1897, took this seriously and treated the expansion of an integer in powers of `p` as an analogue
of the Laurent expansion of a function at a point: each prime is a "point", and divisibility by
`p` is vanishing at that point. The resulting `p`-adic numbers are the subject of this part.

This first file turns the `p`-adic valuation `vₚ` on natural numbers — introduced in
`Foundations.NumberTheory.Binomial` for Legendre's formula — into a valuation on the rationals:
for `x = n/d ≠ 0`,

  `vₚ(x) = vₚ(|n|) − vₚ(d)`,

which is well defined on classes of fractions because `vₚ` is additive (Euclid's lemma). Its two
key properties are

* `vₚ(x y) = vₚ(x) + vₚ(y)`, and
* `vₚ(x + y) ≥ min(vₚ(x), vₚ(y))`.

The **`p`-adic absolute value** is `|x|ₚ = p^(−vₚ(x))` (and `|0|ₚ = 0`), a rational number. The
two properties above translate into multiplicativity `|x y|ₚ = |x|ₚ |y|ₚ` and the
**ultrametric inequality** `|x + y|ₚ ≤ max(|x|ₚ, |y|ₚ)`, much stronger than the triangle
inequality: in the `p`-adic world, adding small numbers never makes something big.

Everything here is ℚ-valued; the real-valued theory (needed for Ostrowski's theorem, where other
absolute values with irrational values appear) is in `Ostrowski`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Foundations.NumberTheory Lean.Grind

/-! ## The valuation on integers -/

/-- The `p`-adic valuation of an integer: `vₚ(|n|)`, with the convention `vₚ(0) = 0`. -/
def vZ (p : Nat) (n : Int) : Nat := vp p n.natAbs

/-- **Additivity of `vₚ` on integers.** For a prime `p` and nonzero integers `a, b`,
`vₚ(a b) = vₚ(a) + vₚ(b)`. -/
theorem vZ_mul {p : Nat} (hp : Prime p) {a b : Int} (ha : a ≠ 0) (hb : b ≠ 0) :
    vZ p (a * b) = vZ p a + vZ p b := by
  unfold vZ
  rw [Int.natAbs_mul]
  exact vp_mul hp (by omega) (by omega)

/-- For a nonzero integer `n`, `pᵉ ∣ n` iff `e ≤ vₚ(n)`. -/
theorem pow_dvd_iff_le_vZ {p : Nat} (hp : 1 < p) {n : Int} (hn : n ≠ 0) {e : Nat} :
    ((p ^ e : Nat) : Int) ∣ n ↔ e ≤ vZ p n := by
  unfold vZ
  rw [← pow_dvd_iff_le_vp hp (by omega)]
  exact Int.ofNat_dvd_left

/-- **Ultrametric property of `vₚ` on integers.** If `u + w ≠ 0` then
`min(vₚ(u), vₚ(w)) ≤ vₚ(u + w)` (for nonzero `u, w`). -/
theorem min_le_vZ_add {p : Nat} (hp : 1 < p) {u w : Int} (hu : u ≠ 0) (hw : w ≠ 0)
    (huw : u + w ≠ 0) : min (vZ p u) (vZ p w) ≤ vZ p (u + w) := by
  have h1 := (pow_dvd_iff_le_vZ hp hu (e := min (vZ p u) (vZ p w))).2 (Nat.min_le_left _ _)
  have h2 := (pow_dvd_iff_le_vZ hp hw (e := min (vZ p u) (vZ p w))).2 (Nat.min_le_right _ _)
  exact (pow_dvd_iff_le_vZ hp huw).1 (Int.dvd_add h1 h2)

/-- `vₚ(1) = 0`. -/
theorem vZ_one {p : Nat} (hp : 1 < p) : vZ p 1 = 0 := vp_one hp

/-- `vₚ(p) = 1` for a prime `p`. -/
theorem vZ_self {p : Nat} (hp : Prime p) : vZ p (p : Int) = 1 := by
  unfold vZ
  exact vp_eq (e := 1) (r := 1) hp.1 (by simp) (fun h => by
    have := Nat.le_of_dvd (by omega) h; have := hp.1; omega)

/-- `vₚ(−n) = vₚ(n)`. -/
theorem vZ_neg (p : Nat) (n : Int) : vZ p (-n) = vZ p n := by
  unfold vZ; rw [Int.natAbs_neg]

/-! ## The valuation on rationals -/

/-- The valuation on a single fraction `n/d`: `vₚ(n) − vₚ(d)` if `p` is prime and `n ≠ 0`,
and `0` otherwise (the junk value is irrelevant). -/
noncomputable def fracVal (p : Nat) (f : Frac) : Int :=
  open Classical in
  if Prime p ∧ f.num ≠ 0 then (vZ p f.num : Int) - vZ p f.den else 0

/-- Equivalent fractions have the same valuation. -/
theorem fracVal_wd (p : Nat) (f g : Frac) (h : f ≈ g) : fracVal p f = fracVal p g := by
  have h' : f.num * g.den = g.num * f.den := h
  have hf := f.den_pos
  have hg := g.den_pos
  unfold fracVal
  by_cases hp : Prime p
  · by_cases hn : f.num = 0
    · have : g.num = 0 := by
        rw [hn, Int.zero_mul] at h'
        rcases Int.mul_eq_zero.1 h'.symm with h | h <;> omega
      simp [hn, this]
    · have hgn : g.num ≠ 0 := by
        intro hz; rw [hz, Int.zero_mul] at h'
        rcases Int.mul_eq_zero.1 h' with h | h <;> omega
      simp only [hp, ne_eq, hn, not_false_eq_true, and_self, ↓reduceIte, hgn]
      have e := congrArg (vZ p) h'
      rw [vZ_mul hp hn (by omega), vZ_mul hp hgn (by omega)] at e
      omega
  · simp [hp]

/-- **The `p`-adic valuation on ℚ.** For a prime `p` and `x = n/d ≠ 0`, `vₚ(x) = vₚ(n) − vₚ(d)`
(an integer, possibly negative). By convention `vₚ(0) = 0`. -/
noncomputable def vQ (p : Nat) : Q → Int :=
  Quotient.lift (fracVal p) (fracVal_wd p)

/-- Computing the valuation on a representative. -/
theorem vQ_mk {p : Nat} (hp : Prime p) {n d : Int} (hd : 0 < d) (hn : n ≠ 0) :
    vQ p (Q.mk n d hd) = (vZ p n : Int) - vZ p d := by
  show fracVal p ⟨n, d, hd⟩ = _
  unfold fracVal
  simp [hp, hn]

/-- A rational number `mk n d` is zero iff its numerator is. -/
theorem mk_eq_zero_iff {n d : Int} (hd : 0 < d) : Q.mk n d hd = 0 ↔ n = 0 := by
  show Q.mk n d hd = Q.mk 0 1 Int.one_pos ↔ _
  rw [Q.mk_eq_mk]; omega

/-- **Additivity of the valuation.** `vₚ(x y) = vₚ(x) + vₚ(y)` for nonzero rationals. -/
theorem vQ_mul {p : Nat} (hp : Prime p) {x y : Q} (hx : x ≠ 0) (hy : y ≠ 0) :
    vQ p (x * y) = vQ p x + vQ p y := by
  induction x using Q.ind with | h a b hb => ?_
  induction y using Q.ind with | h c d hd => ?_
  have ha : a ≠ 0 := fun h => hx ((mk_eq_zero_iff hb).2 h)
  have hc : c ≠ 0 := fun h => hy ((mk_eq_zero_iff hd).2 h)
  rw [Q.mk_mul, vQ_mk hp _ (Int.mul_ne_zero ha hc), vQ_mk hp _ ha, vQ_mk hp _ hc,
    vZ_mul hp ha hc, vZ_mul hp (by omega) (by omega)]
  omega

/-- **Ultrametric inequality for the valuation.** If `x, y, x + y` are nonzero then
`min(vₚ(x), vₚ(y)) ≤ vₚ(x + y)`. -/
theorem min_le_vQ_add {p : Nat} (hp : Prime p) {x y : Q} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (vQ p x) (vQ p y) ≤ vQ p (x + y) := by
  induction x using Q.ind with | h a b hb => ?_
  induction y using Q.ind with | h c d hd => ?_
  have ha : a ≠ 0 := fun h => hx ((mk_eq_zero_iff hb).2 h)
  have hc : c ≠ 0 := fun h => hy ((mk_eq_zero_iff hd).2 h)
  rw [Q.mk_add] at hxy ⊢
  have hs : a * d + c * b ≠ 0 := fun h => hxy ((mk_eq_zero_iff _).2 h)
  rw [vQ_mk hp _ hs, vQ_mk hp _ ha, vQ_mk hp _ hc, vZ_mul hp (by omega) (by omega)]
  have hm := min_le_vZ_add hp.1 (Int.mul_ne_zero ha (by omega : d ≠ 0))
    (Int.mul_ne_zero hc (by omega : b ≠ 0)) hs
  rw [vZ_mul hp ha (by omega), vZ_mul hp hc (by omega)] at hm
  omega

/-- `vₚ(−x) = vₚ(x)`. -/
theorem vQ_neg {p : Nat} (hp : Prime p) (x : Q) : vQ p (-x) = vQ p x := by
  induction x using Q.ind with | h a b hb => ?_
  by_cases ha : a = 0
  · subst ha
    have : Q.mk (-0) b hb = Q.mk 0 b hb := rfl
    rw [Q.mk_neg, this]
  · rw [Q.mk_neg, vQ_mk hp _ (by omega), vQ_mk hp _ ha, vZ_neg]

/-- `vₚ(1) = 0`. -/
theorem vQ_one {p : Nat} (hp : Prime p) : vQ p 1 = 0 := by
  show vQ p (Q.mk 1 1 Int.one_pos) = 0
  rw [vQ_mk hp _ (by omega), vZ_one hp.1]; rfl

/-- `vₚ(p) = 1`. -/
theorem vQ_self {p : Nat} (hp : Prime p) : vQ p (p : Q) = 1 := by
  show vQ p (Q.mk (p : Int) 1 Int.one_pos) = 1
  have := hp.1
  rw [vQ_mk hp _ (by omega), vZ_self hp, vZ_one hp.1]; rfl

/-- The valuation of a nonzero integer `n` is `vₚ(n) ≥ 0`. -/
theorem vQ_intCast {p : Nat} (hp : Prime p) {n : Int} (hn : n ≠ 0) :
    vQ p (n : Q) = (vZ p n : Int) := by
  show vQ p (Q.mk n 1 Int.one_pos) = _
  rw [vQ_mk hp _ hn, vZ_one hp.1]; rfl

/-! ## Integer powers in an ordered field -/

section Powers

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- Natural powers of a positive element are positive. -/
theorem npow_pos {c : K} (hc : 0 < c) : ∀ n : Nat, 0 < c ^ n
  | 0 => by rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
  | n + 1 => by rw [Semiring.pow_succ]; exact OrderedRing.mul_pos (npow_pos hc n) hc

/-- Natural powers of an element `≥ 1` are `≥ 1`. -/
theorem one_le_npow {c : K} (hc : 1 ≤ c) : ∀ n : Nat, 1 ≤ c ^ n
  | 0 => by rw [Semiring.pow_zero]; exact Std.le_refl _
  | n + 1 => by
    rw [Semiring.pow_succ]
    have := one_le_npow hc n
    have := OrderedRing.mul_le_mul_of_nonneg_left hc (by grind : (0 : K) ≤ c ^ n)
    grind

/-- The inverse of a positive element is positive. -/
theorem inv_pos' {c : K} (hc : 0 < c) : 0 < c⁻¹ := by
  have h1 : c * c⁻¹ = 1 := Field.mul_inv_cancel (by grind)
  by_cases h : 0 < c⁻¹
  · exact h
  · have h' : c⁻¹ ≤ 0 := by grind
    have := OrderedRing.mul_le_mul_of_nonneg_left h' (by grind : (0 : K) ≤ c)
    grind

/-- Integer powers of a positive element are positive. -/
theorem zpow_pos {c : K} (hc : 0 < c) (z : Int) : 0 < c ^ z := by
  cases z with
  | ofNat n => rw [Int.ofNat_eq_natCast, Field.zpow_natCast]; exact npow_pos hc n
  | negSucc n =>
    rw [Int.negSucc_eq, Field.zpow_neg, ← Int.natCast_add_one, Field.zpow_natCast]
    exact inv_pos' (npow_pos hc _)

/-- For `c ≥ 1`, integer powers are monotone: `a ≤ b → cᵃ ≤ cᵇ`. -/
theorem zpow_le_zpow {c : K} (hc : 1 ≤ c) {a b : Int} (hab : a ≤ b) : c ^ a ≤ c ^ b := by
  have hc0 : c ≠ 0 := by grind
  have e : c ^ b = c ^ a * c ^ (b - a) := by rw [← Field.zpow_add hc0]; congr 1; omega
  have h1 : 1 ≤ c ^ (b - a) := by
    obtain ⟨k, hk⟩ : ∃ k : Nat, b - a = k := ⟨(b - a).toNat, by omega⟩
    rw [hk, Field.zpow_natCast]; exact one_le_npow hc k
  have h2 := zpow_pos (by grind : (0 : K) < c) a
  have := OrderedRing.mul_le_mul_of_nonneg_left h1 (by grind : (0 : K) ≤ c ^ a)
  grind

end Powers

/-! ## The `p`-adic absolute value -/

/-- **The `p`-adic absolute value.** `|x|ₚ = p^(−vₚ(x))` for `x ≠ 0`, and `|0|ₚ = 0`. It is a
rational number: `|p^k · a/b|ₚ = p^(−k)` when `p ∤ a b`. -/
noncomputable def padicAbs (p : Nat) (x : Q) : Q :=
  open Classical in if x = 0 then 0 else (p : Q) ^ (-(vQ p x))

/-- `|0|ₚ = 0`. -/
theorem padicAbs_zero (p : Nat) : padicAbs p 0 = 0 := by simp [padicAbs]

/-- `|x|ₚ = p^(−vₚ(x))` for `x ≠ 0`. -/
theorem padicAbs_of_ne {p : Nat} {x : Q} (hx : x ≠ 0) : padicAbs p x = (p : Q) ^ (-(vQ p x)) := by
  simp [padicAbs, hx]

/-- A prime, viewed in `ℚ`, is at least `2`. -/
theorem two_le_prime {p : Nat} (hp : Prime p) : (2 : Q) ≤ (p : Q) := by
  have := hp.1
  have : ((2 : Nat) : Q) ≤ (p : Q) := OrderedRing.natCast_le_natCast_of_le _ _ (by omega)
  grind

/-- A prime, viewed in `ℚ`, is at least `1`. -/
theorem one_le_prime {p : Nat} (hp : Prime p) : (1 : Q) ≤ (p : Q) := by
  have := two_le_prime hp; grind

/-- `|x|ₚ > 0` for `x ≠ 0`. -/
theorem padicAbs_pos {p : Nat} (hp : Prime p) {x : Q} (hx : x ≠ 0) : 0 < padicAbs p x := by
  rw [padicAbs_of_ne hx]
  have := one_le_prime hp
  exact zpow_pos (by grind) _

/-- `|x|ₚ ≥ 0`. -/
theorem padicAbs_nonneg {p : Nat} (hp : Prime p) (x : Q) : 0 ≤ padicAbs p x := by
  by_cases hx : x = 0
  · rw [hx, padicAbs_zero]; exact Std.le_refl _
  · have := padicAbs_pos hp hx; grind

/-- `|x|ₚ = 0` iff `x = 0`. -/
theorem padicAbs_eq_zero {p : Nat} (hp : Prime p) {x : Q} : padicAbs p x = 0 ↔ x = 0 := by
  constructor
  · intro h; apply Classical.byContradiction; intro hx
    have := padicAbs_pos hp hx; grind
  · intro h; rw [h, padicAbs_zero]

/-- **Multiplicativity.** `|x y|ₚ = |x|ₚ |y|ₚ`. -/
theorem padicAbs_mul {p : Nat} (hp : Prime p) (x y : Q) :
    padicAbs p (x * y) = padicAbs p x * padicAbs p y := by
  by_cases hx : x = 0
  · rw [hx, padicAbs_zero]; simp only [Semiring.zero_mul]; exact padicAbs_zero p
  by_cases hy : y = 0
  · rw [hy, padicAbs_zero]; simp only [Semiring.mul_zero]; exact padicAbs_zero p
  have hxy : x * y ≠ 0 := fun h => by
    rcases Field.of_mul_eq_zero h with h | h <;> contradiction
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  rw [padicAbs_of_ne hx, padicAbs_of_ne hy, padicAbs_of_ne hxy, vQ_mul hp hx hy,
    ← Field.zpow_add hp0]
  congr 1; omega

/-- **The ultrametric inequality.** `|x + y|ₚ ≤ max(|x|ₚ, |y|ₚ)`, stated as: `|x + y|ₚ` is at
most `|x|ₚ` or at most `|y|ₚ`, and in fact `|x + y|ₚ ≤ |x|ₚ` whenever `|y|ₚ ≤ |x|ₚ`. -/
theorem padicAbs_add_le_of_le {p : Nat} (hp : Prime p) {x y : Q}
    (h : padicAbs p y ≤ padicAbs p x) : padicAbs p (x + y) ≤ padicAbs p x := by
  have h1 := one_le_prime hp
  by_cases hy : y = 0
  · rw [hy]; simp only [Semiring.add_zero]; exact Std.le_refl _
  by_cases hx : x = 0
  · have := padicAbs_pos hp hy; rw [hx, padicAbs_zero] at h; grind
  by_cases hxy : x + y = 0
  · rw [hxy, padicAbs_zero]; exact padicAbs_nonneg hp x
  have hv : vQ p x ≤ vQ p y := by
    rw [padicAbs_of_ne hx, padicAbs_of_ne hy] at h
    apply Classical.byContradiction; intro hlt
    have := zpow_le_zpow h1 (show -(vQ p x) + 1 ≤ -(vQ p y) by omega)
    have hp0 : (p : Q) ≠ 0 := by grind
    rw [Field.zpow_add_one hp0] at this
    have hpos := zpow_pos (by grind : (0 : Q) < p) (-(vQ p x))
    have := OrderedRing.mul_le_mul_of_nonneg_left (two_le_prime hp) (Std.le_of_lt hpos)
    grind
  have hm := min_le_vQ_add hp hx hy hxy
  rw [padicAbs_of_ne hx, padicAbs_of_ne hxy]
  exact zpow_le_zpow h1 (by omega)

/-- **Ultrametric inequality, symmetric form.** `|x + y|ₚ ≤ |x|ₚ` or `|x + y|ₚ ≤ |y|ₚ`; i.e.
`|x + y|ₚ ≤ max(|x|ₚ, |y|ₚ)`. -/
theorem padicAbs_ultrametric {p : Nat} (hp : Prime p) (x y : Q) :
    padicAbs p (x + y) ≤ padicAbs p x ∨ padicAbs p (x + y) ≤ padicAbs p y := by
  rcases Std.le_total (a := padicAbs p y) (b := padicAbs p x) with h | h
  · exact Or.inl (padicAbs_add_le_of_le hp h)
  · right; have := padicAbs_add_le_of_le hp h; rwa [Q.add_comm] at this

/-- **Triangle inequality** for `|·|ₚ`, a consequence of the ultrametric inequality. -/
theorem padicAbs_add {p : Nat} (hp : Prime p) (x y : Q) :
    padicAbs p (x + y) ≤ padicAbs p x + padicAbs p y := by
  have := padicAbs_nonneg hp x
  have := padicAbs_nonneg hp y
  rcases padicAbs_ultrametric hp x y with h | h <;> grind

/-- `|−x|ₚ = |x|ₚ`. -/
theorem padicAbs_neg {p : Nat} (hp : Prime p) (x : Q) : padicAbs p (-x) = padicAbs p x := by
  by_cases hx : x = 0
  · have : -x = 0 := by grind
    rw [this, hx]
  · have : -x ≠ 0 := fun h => hx (by grind)
    rw [padicAbs_of_ne hx, padicAbs_of_ne this, vQ_neg hp]

/-- `|p|ₚ = 1/p`. -/
theorem padicAbs_self {p : Nat} (hp : Prime p) : padicAbs p (p : Q) = (p : Q)⁻¹ := by
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  rw [padicAbs_of_ne hp0, vQ_self hp, Field.zpow_neg, Field.zpow_one]

/-- **Integers are `p`-adically small.** `|n|ₚ ≤ 1` for every integer `n`. -/
theorem padicAbs_intCast_le_one {p : Nat} (hp : Prime p) (n : Int) : padicAbs p (n : Q) ≤ 1 := by
  by_cases hn : n = 0
  · subst hn
    have : ((0 : Int) : Q) = 0 := rfl
    rw [this, padicAbs_zero]; exact OrderedRing.zero_le_one
  · have hn' : (n : Q) ≠ 0 := fun h => hn ((mk_eq_zero_iff Int.one_pos).1 h)
    rw [padicAbs_of_ne hn', vQ_intCast hp hn]
    have := zpow_le_zpow (one_le_prime hp) (show -((vZ p n : Nat) : Int) ≤ 0 by omega)
    rwa [Field.zpow_zero] at this

end Foundations.Langlands.Padic
