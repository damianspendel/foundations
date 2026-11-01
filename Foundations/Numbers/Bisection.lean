import Foundations.Numbers.RealOrder

/-!
# Bisection: manufacturing Cauchy sequences

To prove that the reals have no gaps we must *produce* real numbers, that is, Cauchy sequences of
rationals. The simplest machine for doing so is the ancient method of **bisection** (interval
halving), familiar from the search for a word in a dictionary.

Suppose `P` is some property of rationals, `l ≤ u`, `P` fails at `l` and holds at `u`. Look at
the midpoint `m = (l + u)/2`. If `P m` holds, keep the left half `[l, m]`; otherwise keep the
right half `[m, u]`. Either way we again have an interval whose left end fails `P` and whose right
end satisfies it, now of half the length. Repeating forever gives nested intervals
`[lₙ, uₙ]` of length `(u − l)/2ⁿ`.

Because the intervals shrink to nothing (by the Archimedean property, `2ⁿ` eventually exceeds any
bound), both endpoint sequences are Cauchy, and they are equivalent: they define *one* real
number, the "cut point" where `P` switches from false to true. Note that the choice at each step
("does `P m` hold?") need not be computable; we use classical logic to make it.

This file sets up the machine in general; `Completeness.lean` feeds it the properties
"`q` is an upper bound of `S`" (to obtain least upper bounds) and "`q² ≥ 2`" (to obtain `√2`).
-/

namespace Foundations.Numbers

open Lean.Grind Q

namespace Bisect

/-- One bisection step on an interval `(l, u)`: keep the left half if the midpoint satisfies `P`,
otherwise keep the right half. -/
noncomputable def step (P : Q → Prop) (p : Q × Q) : Q × Q :=
  open Classical in
  if P ((p.1 + p.2) / 2) then (p.1, (p.1 + p.2) / 2) else ((p.1 + p.2) / 2, p.2)

/-- The sequence of intervals produced by repeated bisection starting from `(l, u)`. -/
noncomputable def pair (P : Q → Prop) (l u : Q) : Nat → Q × Q
  | 0 => (l, u)
  | n + 1 => step P (pair P l u n)

/-- The left endpoints of the bisection intervals. -/
noncomputable def lo (P : Q → Prop) (l u : Q) (n : Nat) : Q := (pair P l u n).1

/-- The right endpoints of the bisection intervals. -/
noncomputable def hi (P : Q → Prop) (l u : Q) (n : Nat) : Q := (pair P l u n).2

/-- One bisection step preserves the invariant and halves the interval. -/
theorem step_spec {P : Q → Prop} {p : Q × Q} (h1 : ¬ P p.1) (h2 : P p.2) (h3 : p.1 ≤ p.2) :
    ¬ P (step P p).1 ∧ P (step P p).2 ∧ (step P p).1 ≤ (step P p).2 ∧ p.1 ≤ (step P p).1 ∧
      (step P p).2 ≤ p.2 ∧ ((step P p).2 - (step P p).1) * 2 = p.2 - p.1 := by
  unfold step
  by_cases h : P ((p.1 + p.2) / 2)
  · rw [ite_eq_left h]; exact ⟨h1, h, by grind, by grind, by grind, by grind⟩
  · rw [ite_eq_right h]; exact ⟨h, h2, by grind, by grind, by grind, by grind⟩

/-- `n + 1 ≤ 2ⁿ` in `Q`. -/
theorem two_pow_ge (n : Nat) : (n : Q) + 1 ≤ 2 ^ n := by
  induction n with
  | zero => have : (2 : Q) ^ 0 = 1 := rfl
            grind
  | succ n ih =>
    have : (2 : Q) ^ (n + 1) = 2 ^ n * 2 := rfl
    grind

section

variable {P : Q → Prop} {l u : Q} (hl : ¬ P l) (hu : P u) (hlu : l ≤ u)
include hl hu hlu

/-- The bisection invariant: `P` fails at each left end, holds at each right end, the intervals
are ordered, and the `n`-th interval has length `(u − l)/2ⁿ`. -/
theorem spec (n : Nat) :
    ¬ P (lo P l u n) ∧ P (hi P l u n) ∧ lo P l u n ≤ hi P l u n ∧
      (hi P l u n - lo P l u n) * 2 ^ n = u - l := by
  induction n with
  | zero =>
    have : (2 : Q) ^ 0 = 1 := rfl
    exact ⟨hl, hu, hlu, by simp only [hi, lo, pair]; grind⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    obtain ⟨k1, k2, k3, _, _, k6⟩ := step_spec h1 h2 h3
    have : (2 : Q) ^ (n + 1) = 2 ^ n * 2 := rfl
    refine ⟨k1, k2, k3, ?_⟩
    show ((step P (pair P l u n)).2 - (step P (pair P l u n)).1) * 2 ^ (n + 1) = u - l
    simp only [hi, lo] at h4
    grind

/-- The left endpoints increase. -/
theorem lo_le_succ (n : Nat) : lo P l u n ≤ lo P l u (n + 1) := by
  obtain ⟨h1, h2, h3, _⟩ := spec hl hu hlu n
  exact (step_spec h1 h2 h3).2.2.2.1

/-- The right endpoints decrease. -/
theorem hi_succ_le (n : Nat) : hi P l u (n + 1) ≤ hi P l u n := by
  obtain ⟨h1, h2, h3, _⟩ := spec hl hu hlu n
  exact (step_spec h1 h2 h3).2.2.2.2.1

/-- The intervals are nested: for `N ≤ m`, `[lₘ, uₘ] ⊆ [l_N, u_N]`. -/
theorem nested {N m : Nat} (h : N ≤ m) :
    lo P l u N ≤ lo P l u m ∧ hi P l u m ≤ hi P l u N := by
  obtain ⟨k, rfl⟩ : ∃ k, m = N + k := ⟨m - N, by omega⟩
  induction k with
  | zero => exact ⟨Q.le_refl _, Q.le_refl _⟩
  | succ k ih =>
    have := ih (by omega)
    have := lo_le_succ hl hu hlu (N + k)
    have := hi_succ_le hl hu hlu (N + k)
    rw [← Nat.add_assoc]
    grind

/-- The intervals become arbitrarily short. -/
theorem width_small {ε : Q} (hε : 0 < ε) : ∃ N, hi P l u N - lo P l u N < ε := by
  obtain ⟨N, hN⟩ := Q.archimedean ((u - l) / ε)
  refine ⟨N, ?_⟩
  obtain ⟨_, _, _, h4⟩ := spec hl hu hlu N
  have k1 : u - l < N * ε := (Field.IsOrdered.mul_inv_lt_iff_lt_mul _ _ hε).1 hN
  have k2 := OrderedRing.mul_le_mul_of_nonneg_right (two_pow_ge N) (Q.le_of_lt' hε)
  have hpos : (0 : Q) < 2 ^ N := by have := two_pow_ge N; grind
  have : (hi P l u N - lo P l u N) * 2 ^ N < ε * 2 ^ N := by grind
  exact (Field.IsOrdered.mul_lt_mul_iff_of_pos_right hpos).1 this

/-- Beyond some index, all endpoints are within `ε` of each other. -/
theorem close {ε : Q} (hε : 0 < ε) : ∃ N, ∀ m n, N ≤ m → N ≤ n →
    abs (lo P l u m - lo P l u n) < ε ∧ abs (hi P l u m - hi P l u n) < ε ∧
      abs (lo P l u n - hi P l u n) < ε := by
  obtain ⟨N, hN⟩ := width_small hl hu hlu hε
  refine ⟨N, fun m n hm hn => ?_⟩
  have := nested hl hu hlu hm
  have := nested hl hu hlu hn
  have := (spec hl hu hlu m).2.2.1
  have := (spec hl hu hlu n).2.2.1
  refine ⟨abs_lt.2 ⟨by grind, by grind⟩, abs_lt.2 ⟨by grind, by grind⟩,
    abs_lt.2 ⟨by grind, by grind⟩⟩

/-- The left endpoints form a Cauchy sequence. -/
noncomputable def loSeq : CauSeq :=
  ⟨lo P l u, fun _ hε => (close hl hu hlu hε).imp fun _ h m n hm hn => (h m n hm hn).1⟩

/-- The right endpoints form a Cauchy sequence. -/
noncomputable def hiSeq : CauSeq :=
  ⟨hi P l u, fun _ hε => (close hl hu hlu hε).imp fun _ h m n hm hn => (h m n hm hn).2.1⟩

/-- Both endpoint sequences define the same real number. -/
theorem lo_equiv_hi : loSeq hl hu hlu ≈ hiSeq hl hu hlu := fun _ hε =>
  (close hl hu hlu hε).imp fun _ h n hn => (h n n hn hn).2.2

end

end Bisect

end Foundations.Numbers
