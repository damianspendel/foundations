import Foundations.Numbers.Bisection

/-!
# Completeness of the reals, and the existence of √2

This file proves the property that distinguishes the reals from the rationals and was the whole
point of the construction: **completeness**. In Dedekind's formulation, the line has no gaps;
in the form we prove, *every nonempty set of reals that is bounded above has a least upper bound*
(a *supremum*).

A set of reals is represented as a predicate `S : R → Prop` ("`x` belongs to the set iff
`S x`"). The proof feeds the bisection machine of `Bisection.lean` with the property
"`q` is an upper bound of `S`": starting from a rational below some element of `S` and a rational
upper bound, bisection traps the supremum in ever smaller intervals, and the Cauchy sequence of
right endpoints *is* (represents) the least upper bound.

As a first payoff we show that `√2` exists in `R`: there is a real `r > 0` with `r · r = 2`.
Here too we use bisection, this time on the property "`q² ≥ 2`", and check directly that the
resulting real squares to `2`. Thus the gap in the rationals discovered by the Pythagoreans is
filled.
-/

namespace Foundations.Numbers

open Lean.Grind Q

namespace R

open CauSeq

/-- `ofQ` of a natural number is the corresponding real numeral. -/
theorem ofQ_natCast (n : Nat) : ofQ (n : Q) = (n : R) := rfl

/-- **Completeness of ℝ (least upper bound property).** Every nonempty set `S` of real numbers
that is bounded above has a least upper bound: a real `L` that is an upper bound of `S` and lies
below every other upper bound. -/
theorem exists_lub (S : R → Prop) (hne : ∃ x, S x) (hbdd : ∃ M, ∀ x, S x → x ≤ M) :
    ∃ L : R, (∀ x, S x → x ≤ L) ∧ ∀ M, (∀ x, S x → x ≤ M) → L ≤ M := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨M, hM⟩ := hbdd
  -- A rational strictly below the element `x₀` of `S`, and a rational upper bound.
  obtain ⟨n, hn⟩ := archimedean (-x₀)
  obtain ⟨m, hm⟩ := archimedean M
  let a₀ : Q := -(n : Q) - 1
  let b₀ : Q := m
  have ha₀ : ofQ a₀ = -(n : R) - 1 := rfl
  have hb₀ : ofQ b₀ = (m : R) := rfl
  -- The property "`q` is an upper bound of `S`".
  let P : Q → Prop := fun q => ∀ x, S x → x ≤ ofQ q
  have hl : ¬ P a₀ := fun h => by have := h x₀ hx₀; grind
  have hu : P b₀ := fun x hx => by have := hM x hx; grind
  have hlu : a₀ ≤ b₀ := by
    have := hM x₀ hx₀
    have : ofQ a₀ < ofQ b₀ := by grind
    exact Q.le_of_lt' (ofQ_lt.1 this)
  let lo := Bisect.loSeq hl hu hlu
  let hi := Bisect.hiSeq hl hu hlu
  have hlohi : mk lo = mk hi := mk_eq_mk.2 (Bisect.lo_equiv_hi hl hu hlu)
  refine ⟨mk hi, ?_, ?_⟩
  · -- The limit is an upper bound: otherwise some `x ∈ S` exceeds it by a rational `δ`.
    intro x hx
    apply Classical.byContradiction
    intro hnot
    have hlt : 0 < x - mk hi := by grind
    obtain ⟨δ, hδ, hδx⟩ := pos_iff_rat.1 hlt
    obtain ⟨N, hN⟩ := approx hi (ε := δ / 2) (by grind)
    have h1 := (hN N (Nat.le_refl _)).1
    have h2 : x ≤ ofQ (hi N) := (Bisect.spec hl hu hlu N).2.1 x hx
    have h3 : ofQ δ ≤ ofQ (δ / 2) := by grind
    have := ofQ_le.1 h3
    grind
  · -- The limit is least: otherwise a left endpoint (which is *not* an upper bound) would lie
    -- above the smaller upper bound `M'`.
    intro M' hM'
    apply Classical.byContradiction
    intro hnot
    have hlt : 0 < mk hi - M' := by grind
    obtain ⟨δ, hδ, hδx⟩ := pos_iff_rat.1 hlt
    obtain ⟨N, hN⟩ := approx lo (ε := δ / 2) (by grind)
    have h1 := (hN N (Nat.le_refl _)).2
    have h2 : ¬ P (lo N) := (Bisect.spec hl hu hlu N).1
    have : ∃ x, S x ∧ ¬ x ≤ ofQ (lo N) := by
      apply Classical.byContradiction
      intro hno
      exact h2 fun x hx => Classical.byContradiction fun h => hno ⟨x, hx, h⟩
    obtain ⟨x, hx, hxlo⟩ := this
    have h4 := hM' x hx
    have h3 : ofQ (δ / 2) < ofQ δ := ofQ_lt.2 (by grind)
    rw [hlohi] at h1
    grind

/-- **Existence of √2.** There is a positive real number whose square is `2`. -/
theorem exists_sqrt_two : ∃ r : R, 0 < r ∧ r * r = 2 := by
  let P : Q → Prop := fun q => 2 ≤ q * q
  have hl : ¬ P 1 := by show ¬ (2 : Q) ≤ 1 * 1; grind
  have hu : P 2 := by show (2 : Q) ≤ 2 * 2; grind
  have hlu : (1 : Q) ≤ 2 := by grind
  let lo := Bisect.loSeq hl hu hlu
  let hi := Bisect.hiSeq hl hu hlu
  -- All left endpoints are at least `1`, all right endpoints at most `2`.
  have hbounds : ∀ n, 1 ≤ Bisect.lo P 1 2 n ∧ Bisect.hi P 1 2 n ≤ 2 ∧
      Bisect.lo P 1 2 n ≤ Bisect.hi P 1 2 n ∧ Bisect.lo P 1 2 n * Bisect.lo P 1 2 n < 2 ∧
      2 ≤ Bisect.hi P 1 2 n * Bisect.hi P 1 2 n := by
    intro n
    have h1 := Bisect.nested hl hu hlu (Nat.zero_le n)
    have h2 := Bisect.spec hl hu hlu n
    have e1 : Bisect.lo P 1 2 0 = 1 := rfl
    have e2 : Bisect.hi P 1 2 0 = 2 := rfl
    refine ⟨by grind, by grind, h2.2.2.1, ?_, h2.2.1⟩
    have := h2.1
    simp only [P] at this; grind
  refine ⟨mk hi, ?_, ?_⟩
  · -- `√2 ≥ 1 > 0`.
    have : ofQ 1 ≤ mk hi := le_of_eventually_le ⟨0, fun n _ => by
      have := hbounds n
      show 1 ≤ Bisect.hi P 1 2 n
      grind⟩
    have h1 : (0 : R) < ofQ 1 := ofQ_lt.2 (by grind)
    grind
  · -- `hiₙ² − 2` is squeezed between `0` and `4 (hiₙ − loₙ)`, which tends to `0`.
    rw [mk_mul, ofNat_def]
    show mk _ = mk (const 2)
    rw [mk_eq_mk]
    intro ε hε
    obtain ⟨N, hN⟩ := Bisect.width_small hl hu hlu (ε := ε / 4) (by grind)
    refine ⟨N, fun n hn => ?_⟩
    have hb := hbounds n
    have hnest := Bisect.nested hl hu hlu hn
    have k : (Bisect.hi P 1 2 n - Bisect.lo P 1 2 n) * (Bisect.hi P 1 2 n + Bisect.lo P 1 2 n) ≤
        (Bisect.hi P 1 2 n - Bisect.lo P 1 2 n) * 4 :=
      OrderedRing.mul_le_mul_of_nonneg_left (by grind) (by grind)
    show abs (Bisect.hi P 1 2 n * Bisect.hi P 1 2 n - 2) < ε
    apply abs_lt.2
    constructor <;> grind

end R

end Foundations.Numbers
