import Foundations.Numbers.Rat

/-!
# Cauchy sequences of rationals

The rationals have gaps: no rational squares to `2`. Yet we can *approach* the missing point as
closely as we like — `1, 1.4, 1.41, 1.414, …` — by rationals whose squares tend to `2`. The idea
of Cauchy (and of Cantor and Méray, who turned it into a construction of the reals) is to take
such approximating processes themselves as the new numbers.

A sequence `a₀, a₁, a₂, …` of rationals is **Cauchy** if its terms eventually stay arbitrarily
close to *each other*:

  for every rational `ε > 0` there is an `N` such that `|aₘ − aₙ| < ε` whenever `m, n ≥ N`.

Crucially this definition does not mention any limit: it describes a sequence that "ought to
converge" using only the rationals themselves. Two Cauchy sequences are **equivalent** when their
difference tends to `0`, i.e. when they are "aiming at the same point". In the next file a real
number is *defined* to be an equivalence class of Cauchy sequences — once more the method of
definition by abstraction, this time applied to infinite processes rather than pairs.

In this file we develop what is needed about rationals and Cauchy sequences: the absolute value,
the equivalence relation, boundedness, and the arithmetic operations (sum, negation, product) on
Cauchy sequences, together with their compatibility with equivalence.
-/

namespace Foundations.Numbers

namespace Q

open Lean.Grind

/-- A strict inequality implies the weak one. -/
theorem le_of_lt' {x y : Q} (h : x < y) : x ≤ y := h.1

/-- The absolute value `|x|` of a rational number. -/
def abs (x : Q) : Q := if 0 ≤ x then x else -x

/-- The two cases of the absolute value. -/
theorem abs_cases (x : Q) : (0 ≤ x ∧ abs x = x) ∨ (x < 0 ∧ abs x = -x) := by
  by_cases h : 0 ≤ x
  · left; exact ⟨h, by unfold abs; exact ite_eq_left h⟩
  · right; exact ⟨by grind, by unfold abs; exact ite_eq_right h⟩

/-- The absolute value of a non-negative number is the number itself. -/
theorem abs_of_nonneg {x : Q} (h : 0 ≤ x) : abs x = x := by
  rcases abs_cases x with h' | h' <;> grind

/-- The absolute value of a negative number is its negative. -/
theorem abs_of_neg {x : Q} (h : x < 0) : abs x = -x := by
  rcases abs_cases x with h' | h' <;> grind

/-- Absolute values are non-negative. -/
theorem abs_nonneg (x : Q) : 0 ≤ abs x := by
  rcases abs_cases x with h' | h' <;> grind

/-- `|x| < e` iff `-e < x < e`. -/
theorem abs_lt {x e : Q} : abs x < e ↔ -e < x ∧ x < e := by
  rcases abs_cases x with h' | h' <;> grind

/-- `|x| ≤ e` iff `-e ≤ x ≤ e`. -/
theorem abs_le {x e : Q} : abs x ≤ e ↔ -e ≤ x ∧ x ≤ e := by
  rcases abs_cases x with h' | h' <;> grind

/-- `x ≤ |x|` and `-x ≤ |x|`. -/
theorem le_abs (x : Q) : x ≤ abs x ∧ -x ≤ abs x := by
  rcases abs_cases x with h' | h' <;> grind

/-- `|x − y| = |y − x|`. -/
theorem abs_sub_comm (x y : Q) : abs (x - y) = abs (y - x) := by
  rcases abs_cases (x - y) with h | h <;> rcases abs_cases (y - x) with h' | h' <;> grind

/-- `|−x| = |x|`. -/
theorem abs_neg (x : Q) : abs (-x) = abs x := by
  rcases abs_cases (-x) with h | h <;> rcases abs_cases x with h' | h' <;> grind

/-- `|0| = 0`. -/
theorem abs_zero : abs 0 = 0 := abs_of_nonneg (by grind)

/-- **Triangle inequality.** `|x + y| ≤ |x| + |y|`. -/
theorem abs_add (x y : Q) : abs (x + y) ≤ abs x + abs y := by
  rcases abs_cases x with h | h <;> rcases abs_cases y with h' | h' <;>
    rcases abs_cases (x + y) with h'' | h'' <;> grind

/-- The absolute value is multiplicative: `|x · y| = |x| · |y|`. -/
theorem abs_mul (x y : Q) : abs (x * y) = abs x * abs y := by
  rcases abs_cases x with ⟨hx, ex⟩ | ⟨hx, ex⟩ <;> rcases abs_cases y with ⟨hy, ey⟩ | ⟨hy, ey⟩ <;>
    rcases abs_cases (x * y) with ⟨hxy, exy⟩ | ⟨hxy, exy⟩ <;> rw [ex, ey, exy]
  all_goals first
    | grind
    | (have := OrderedRing.mul_nonneg hx hy; grind)
    | (have := OrderedRing.mul_nonneg hx (by grind : 0 ≤ -y); grind)
    | (have := OrderedRing.mul_nonneg (by grind : 0 ≤ -x) hy; grind)
    | (have := OrderedRing.mul_nonneg (by grind : 0 ≤ -x) (by grind : 0 ≤ -y); grind)
    | (have := OrderedRing.mul_pos (by grind : 0 < -x) (by grind : 0 < -y); grind)

/-- The quotient of positive rationals is positive. -/
theorem div_pos {a b : Q} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  OrderedRing.mul_pos ha (Field.IsOrdered.inv_pos_iff.2 hb)

/-- A product estimate: if `|x| ≤ A` with `A > 0` and `|y| < δ`, then `|x · y| < A · δ`. -/
theorem abs_mul_lt {x y A δ : Q} (hx : abs x ≤ A) (hA : 0 < A) (hy : abs y < δ) :
    abs (x * y) < A * δ := by
  rw [abs_mul]
  have h1 := OrderedRing.mul_le_mul_of_nonneg_right hx (abs_nonneg y)
  have h2 := OrderedRing.mul_lt_mul_of_pos_left hy hA
  grind

end Q

/-- A sequence of rationals is **Cauchy** if its terms become arbitrarily close to each other:
for every rational `ε > 0` there is an index `N` beyond which any two terms differ by less
than `ε`. -/
def IsCauchy (a : Nat → Q) : Prop :=
  ∀ ε : Q, 0 < ε → ∃ N : Nat, ∀ m n, N ≤ m → N ≤ n → Q.abs (a m - a n) < ε

/-- A Cauchy sequence of rationals: a sequence together with a proof of the Cauchy property. -/
structure CauSeq where
  /-- The underlying sequence of rationals. -/
  seq : Nat → Q
  /-- The sequence is Cauchy. -/
  isCauchy : IsCauchy seq

namespace CauSeq

open Q

/-- A Cauchy sequence can be applied to an index like a function. -/
instance : CoeFun CauSeq (fun _ => Nat → Q) := ⟨seq⟩

/-- Two Cauchy sequences are *equivalent* when their difference tends to zero: for every `ε > 0`
the terms are eventually within `ε` of each other. -/
def Equiv (a b : CauSeq) : Prop :=
  ∀ ε : Q, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → Q.abs (a n - b n) < ε

/-- Equivalence of Cauchy sequences is reflexive. -/
theorem equiv_refl (a : CauSeq) : Equiv a a :=
  fun ε hε => ⟨0, fun n _ => by
    have : a n - a n = 0 := by grind
    rw [this, abs_zero]; exact hε⟩

/-- Equivalence of Cauchy sequences is symmetric. -/
theorem equiv_symm {a b : CauSeq} (h : Equiv a b) : Equiv b a := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩

/-- Equivalence of Cauchy sequences is transitive (an `ε/2` argument). -/
theorem equiv_trans {a b c : CauSeq} (h₁ : Equiv a b) (h₂ : Equiv b c) : Equiv a c :=
  fun ε hε => by
    obtain ⟨N₁, h₁⟩ := h₁ (ε / 2) (by grind)
    obtain ⟨N₂, h₂⟩ := h₂ (ε / 2) (by grind)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have := h₁ n (by omega)
    have := h₂ n (by omega)
    have := abs_add (a n - b n) (b n - c n)
    have e : a n - b n + (b n - c n) = a n - c n := by grind
    rw [e] at this
    grind

/-- Equivalence of Cauchy sequences is an equivalence relation. -/
instance setoid : Setoid CauSeq where
  r := Equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

/-- Unfolding the setoid relation on Cauchy sequences. -/
theorem equiv_iff {a b : CauSeq} : a ≈ b ↔ Equiv a b := Iff.rfl

/-- Sequences that agree term by term are equivalent. -/
theorem equiv_of_eq {a b : CauSeq} (h : ∀ n, a n = b n) : a ≈ b := fun ε hε =>
  ⟨0, fun n _ => by
    have : a n - b n = 0 := by rw [h n]; grind
    rw [this, abs_zero]; exact hε⟩

/-! ## Boundedness -/

/-- The sum `|a 0| + ⋯ + |a N|`. -/
def sumAbs (a : Nat → Q) : Nat → Q
  | 0 => abs (a 0)
  | n + 1 => sumAbs a n + abs (a (n + 1))

/-- The sum of absolute values is non-negative. -/
theorem sumAbs_nonneg (a : Nat → Q) (N : Nat) : 0 ≤ sumAbs a N := by
  induction N with
  | zero => exact abs_nonneg _
  | succ N ih => have := abs_nonneg (a (N + 1)); simp only [sumAbs]; grind

/-- Each `|a k|` with `k ≤ N` is bounded by `|a 0| + ⋯ + |a N|`. -/
theorem abs_le_sumAbs (a : Nat → Q) {k N : Nat} (h : k ≤ N) : abs (a k) ≤ sumAbs a N := by
  induction N with
  | zero => have : k = 0 := by omega
            subst this; exact Q.le_refl _
  | succ N ih =>
    have := abs_nonneg (a (N + 1))
    simp only [sumAbs]
    by_cases hk : k ≤ N
    · have := ih hk; grind
    · have : k = N + 1 := by omega
      subst this; have := sumAbs_nonneg a N; grind

/-- **Cauchy sequences are bounded.** There is a positive rational `B` with `|aₙ| < B` for all
`n`. -/
theorem bounded (a : CauSeq) : ∃ B : Q, 0 < B ∧ ∀ n, abs (a n) < B := by
  obtain ⟨N, hN⟩ := a.isCauchy 1 (by grind)
  refine ⟨sumAbs a N + 1, by have := sumAbs_nonneg a N; grind, fun n => ?_⟩
  by_cases hn : n ≤ N
  · have := abs_le_sumAbs a hn; grind
  · have h1 := hN n N (by omega) (Nat.le_refl _)
    have h2 := abs_le_sumAbs a (Nat.le_refl N)
    have h3 := abs_add (a n - a N) (a N)
    have e : a n - a N + a N = a n := by grind
    rw [e] at h3
    grind

/-! ## Arithmetic of Cauchy sequences -/

/-- The constant sequence with value `q` (it is trivially Cauchy). -/
def const (q : Q) : CauSeq where
  seq _ := q
  isCauchy ε hε := ⟨0, fun _ _ _ _ => by
    have : q - q = 0 := by grind
    rw [this, abs_zero]; exact hε⟩

/-- The termwise sum of two Cauchy sequences is Cauchy. -/
def add (a b : CauSeq) : CauSeq where
  seq n := a n + b n
  isCauchy ε hε := by
    obtain ⟨N₁, h₁⟩ := a.isCauchy (ε / 2) (by grind)
    obtain ⟨N₂, h₂⟩ := b.isCauchy (ε / 2) (by grind)
    refine ⟨max N₁ N₂, fun m n hm hn => ?_⟩
    have := h₁ m n (by omega) (by omega)
    have := h₂ m n (by omega) (by omega)
    have := abs_add (a m - a n) (b m - b n)
    have e : a m - a n + (b m - b n) = a m + b m - (a n + b n) := by grind
    rw [e] at this
    grind

/-- The termwise negation of a Cauchy sequence is Cauchy. -/
def neg (a : CauSeq) : CauSeq where
  seq n := -a n
  isCauchy ε hε := by
    obtain ⟨N, h⟩ := a.isCauchy ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    have e : -a m - -a n = -(a m - a n) := by grind
    show abs (-a m - -a n) < ε
    rw [e, abs_neg]; exact h m n hm hn

/-- The key estimate for products: `xy − x'y' = x(y − y') + y'(x − x')`, so if `|x| ≤ A`,
`|y'| ≤ B` and the differences are below `ε/(A+B)`, the products differ by less than `ε`. -/
theorem abs_mul_sub_lt {x y x' y' A B ε : Q} (hA : 0 < A) (hB : 0 < B) (_hε : 0 < ε)
    (hx : abs x ≤ A) (hy' : abs y' ≤ B)
    (h1 : abs (y - y') < ε / (A + B)) (h2 : abs (x - x') < ε / (A + B)) :
    abs (x * y - x' * y') < ε := by
  have k1 := abs_mul_lt hx hA h1
  have k2 := abs_mul_lt hy' hB h2
  have k3 := abs_add (x * (y - y')) (y' * (x - x'))
  have e : x * (y - y') + y' * (x - x') = x * y - x' * y' := by grind
  rw [e] at k3
  have e2 : A * (ε / (A + B)) + B * (ε / (A + B)) = ε := by grind
  grind

/-- The termwise product of two Cauchy sequences is Cauchy. -/
def mul (a b : CauSeq) : CauSeq where
  seq n := a n * b n
  isCauchy ε hε := by
    obtain ⟨A, hA, hA'⟩ := a.bounded
    obtain ⟨B, hB, hB'⟩ := b.bounded
    have hδ : 0 < ε / (A + B) := div_pos hε (by grind)
    obtain ⟨N₁, h₁⟩ := a.isCauchy _ hδ
    obtain ⟨N₂, h₂⟩ := b.isCauchy _ hδ
    refine ⟨max N₁ N₂, fun m n hm hn => ?_⟩
    exact abs_mul_sub_lt hA hB hε (Q.le_of_lt' (hA' m)) (Q.le_of_lt' (hB' n))
      (h₂ m n (by omega) (by omega)) (h₁ m n (by omega) (by omega))

/-- The terms of a constant sequence. -/
@[simp] theorem const_apply (q : Q) (n : Nat) : const q n = q := rfl
/-- The terms of a sum of sequences. -/
@[simp] theorem add_apply (a b : CauSeq) (n : Nat) : add a b n = a n + b n := rfl
/-- The terms of a negated sequence. -/
@[simp] theorem neg_apply (a : CauSeq) (n : Nat) : neg a n = -a n := rfl
/-- The terms of a product of sequences. -/
@[simp] theorem mul_apply (a b : CauSeq) (n : Nat) : mul a b n = a n * b n := rfl

/-- Addition respects equivalence. -/
theorem add_equiv {a b a' b' : CauSeq} (h₁ : a ≈ a') (h₂ : b ≈ b') : add a b ≈ add a' b' :=
  fun ε hε => by
    obtain ⟨N₁, h₁⟩ := h₁ (ε / 2) (by grind)
    obtain ⟨N₂, h₂⟩ := h₂ (ε / 2) (by grind)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have := h₁ n (by omega)
    have := h₂ n (by omega)
    have := abs_add (a n - a' n) (b n - b' n)
    have e : a n - a' n + (b n - b' n) = add a b n - add a' b' n := by simp; grind
    rw [e] at this
    grind

/-- Negation respects equivalence. -/
theorem neg_equiv {a a' : CauSeq} (h : a ≈ a') : neg a ≈ neg a' := fun ε hε => by
  obtain ⟨N, h⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have e : neg a n - neg a' n = -(a n - a' n) := by simp; grind
  rw [e, abs_neg]; exact h n hn

/-- Multiplication respects equivalence. -/
theorem mul_equiv {a b a' b' : CauSeq} (h₁ : a ≈ a') (h₂ : b ≈ b') : mul a b ≈ mul a' b' :=
  fun ε hε => by
    obtain ⟨A, hA, hA'⟩ := a.bounded
    obtain ⟨B, hB, hB'⟩ := b'.bounded
    have hδ : 0 < ε / (A + B) := div_pos hε (by grind)
    obtain ⟨N₁, h₁⟩ := h₁ _ hδ
    obtain ⟨N₂, h₂⟩ := h₂ _ hδ
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    exact abs_mul_sub_lt hA hB hε (Q.le_of_lt' (hA' n)) (Q.le_of_lt' (hB' n))
      (h₂ n (by omega)) (h₁ n (by omega))

end CauSeq

end Foundations.Numbers
