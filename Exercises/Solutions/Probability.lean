import Foundations.Probability.Examples

/-!
# Exercises XIV: Probability

Problems on finite probability (`Foundations/Probability`): events and their probabilities,
independence (`Finite`), expectation, variance and the inequalities of Markov and Chebyshev
(`RandomVariables`), and Bernoulli trials with the weak law of large numbers (`LargeNumbers`,
`Examples`).

*Conventions.* A finite probability space `P : FinProb α` is a list of outcomes `P.pts` with
non-negative weights `P.w` of total mass `1`. Events are predicates `α → Prop`; `P.prob A` is
the probability, `P.E X` the expectation, `P.Var X` the variance. Complements and
intersections are written pointwise, e.g. `fun x => ¬ A x` and `fun x => A x ∧ B x`.
The reals `R` are an ordered field, so `grind` closes most of the final arithmetic.

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in
`Exercises/Problems/Probability.lean`.
-/

namespace Exercises.Probability

open Foundations.Numbers Foundations.Probability Foundations.Probability.FinProb Lean.Grind

/-! ## Events -/

/-- **Exercise 14.1 (★) — The union bound.** `P(A ∪ B) ≤ P(A) + P(B)`.

*Hint:* inclusion–exclusion, and probabilities are non-negative.

*Uses:* `FinProb.prob_or`, `FinProb.prob_nonneg`. -/
theorem prob_or_le {α : Type} (P : FinProb α) (A B : Event α) :
    P.prob (fun x => A x ∨ B x) ≤ P.prob A + P.prob B := by
  -- SOLUTION
  rw [prob_or]
  have := P.prob_nonneg (fun x => A x ∧ B x)
  grind
  -- END

/-- **Exercise 14.2 (★★) — Complements of independent events.** If `A` and `B` are
independent, so are `Aᶜ` and `Bᶜ`.

*Hint:* the library passes to the complement in the second argument. Use it, swap the two
events, use it again, and swap back.

*Uses:* `FinProb.Indep.compl`, `FinProb.Indep.symm`. -/
theorem Indep.compl_compl {α : Type} (P : FinProb α) {A B : Event α} (h : P.Indep A B) :
    P.Indep (fun x => ¬ A x) (fun x => ¬ B x) := by
  -- SOLUTION
  exact h.compl.symm.compl.symm
  -- END

/-! ## Expectation and variance -/

/-- **Exercise 14.3 (★★) — A Bernoulli trial has variance at most 1/4.** For every
`p ∈ [0, 1]`, the variance of the success indicator of a Bernoulli(`p`) trial is `≤ 1/4`.

*Hint:* the variance is `p(1 − p)`, and `1/4 − p(1 − p) = (p − 1/2)²`.

*Uses:* `FinProb.Var_success`, `mul_self_nonneg`. -/
theorem Var_success_le {p : R} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) :
    (bernoulli p h₀ h₁).Var success ≤ 1 / 4 := by
  -- SOLUTION
  rw [Var_success]
  have := mul_self_nonneg (p - 1 / 2)
  grind
  -- END

/-- **Exercise 14.4 (★★) — Zero variance means almost surely constant.** If `Var X = 0`, then
for every `ε > 0` the event `|X − E X| ≥ ε` has probability `0`.

*Hint:* Chebyshev bounds the probability by `0 / ε²`; probabilities are non-negative.

*Uses:* `FinProb.chebyshev`, `FinProb.prob_nonneg`. -/
theorem prob_dev_eq_zero_of_Var_eq_zero {α : Type} (P : FinProb α) (X : α → R)
    (hX : P.Var X = 0) {ε : R} (hε : 0 < ε) :
    P.prob (fun x => ε ≤ OF.abs (X x - P.E X)) = 0 := by
  -- SOLUTION
  have h1 := P.chebyshev X hε
  have h2 := P.prob_nonneg (fun x => ε ≤ OF.abs (X x - P.E X))
  rw [hX] at h1
  have : (0 : R) / (ε * ε) = 0 := by grind
  rw [this] at h1
  grind
  -- END

/-! ## The law of large numbers -/

/-- **Exercise 14.5 (★★★) — A bound uniform in `p`.** For `n` Bernoulli(`p`) trials and
`ε > 0`, the relative frequency of success deviates from `p` by at least `ε` with probability at
most `1/(4 n ε²)`, whatever `p` is.

*Hint:* Bernoulli's theorem gives the bound `p(1 − p)/(n ε²)`. Bound `p(1 − p) ≤ 1/4` as in
Exercise 14.3, and divide by `n ε² > 0`: `a ≤ b` gives `a / c ≤ b / c` for `c > 0`
(multiply by `1 / c ≥ 0`). The denominator in the statement is `4 * (n * (ε * ε))`, and
`1 / (4 c) = (1/4) / c`.

*Uses:* `FinProb.bernoulli_theorem`, `mul_self_nonneg`, `natCast_pos`,
`OrderedRing.mul_le_mul_of_nonneg_left`, `OF.div_pos`. -/
theorem bernoulli_uniform {p : R} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) {n : Nat} (hn : 0 < n) {ε : R}
    (hε : 0 < ε) :
    ((bernoulli p h₀ h₁).pow n).prob (fun t => ε ≤ OF.abs (sampleSum success n t / n - p)) ≤
      1 / (4 * (n * (ε * ε))) := by
  -- SOLUTION
  have hb := bernoulli_theorem (h₀ := h₀) (h₁ := h₁) hn hε
  have hc : 0 < (n : R) * (ε * ε) :=
    OrderedRing.mul_pos (natCast_pos hn) (OrderedRing.mul_pos hε hε)
  generalize (n : R) * (ε * ε) = c at hb hc ⊢
  have hp : p * (1 - p) ≤ 1 / 4 := by have := mul_self_nonneg (p - 1 / 2); grind
  have hi : 0 ≤ 1 / c := Std.le_of_lt (OF.div_pos (by grind) hc)
  have hm := OrderedRing.mul_le_mul_of_nonneg_left hp hi
  have hc0 : c ≠ 0 := fun h => by grind
  have e1 : 1 / c * (p * (1 - p)) = p * (1 - p) / c := by grind
  have e2 : 1 / c * (1 / 4) = 1 / (4 * c) := by grind
  rw [e1, e2] at hm
  exact Std.le_trans hb hm
  -- END

end Exercises.Probability
