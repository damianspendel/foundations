import Foundations.Probability.LargeNumbers

/-!
# Worked examples: the binomial distribution and the Monty Hall problem

**The binomial distribution.** A *Bernoulli trial* succeeds with probability `p` and
fails with probability `1 − p`. Repeating it `n` times independently (the product space
of `LargeNumbers`), the number of successes `Sₙ` has the binomial distribution — the
distribution Bernoulli studied in the *Ars Conjectandi*. Its mean `np` and variance
`np(1 − p)` follow at once from linearity of expectation and Bienaymé's identity, with
no binomial coefficients in sight; and the law of large numbers specialises to
Bernoulli's original theorem on relative frequencies.

**The Monty Hall problem** (Selvin 1975; made famous by Marilyn vos Savant in 1990). A
car is behind one of three doors, equally likely. You pick door `0`. The host, who knows
where the car is, opens a door you did not pick that hides no car — choosing at random
if he has a choice. He opens door `1`. Should you switch to door `2`? Bayes' theorem
says yes: the car is behind door `2` with probability `2/3`. We set up the four-outcome
probability space and compute the conditional probability exactly.
-/

namespace Foundations.Probability

open Foundations.Numbers Lean.Grind Classical

namespace FinProb

/-! ## Bernoulli trials and the binomial distribution -/

/-- **A Bernoulli trial** with success probability `p ∈ [0, 1]`. -/
noncomputable def bernoulli (p : R) (h₀ : 0 ≤ p) (h₁ : p ≤ 1) : FinProb Bool where
  pts := [true, false]
  w := fun b => if b then p else 1 - p
  w_nonneg := fun b => by cases b <;> simp <;> grind
  sum_one := by simp [sumL]; grind

/-- The success indicator of a trial. -/
def success (b : Bool) : R := if b then 1 else 0

variable {p : R} {h₀ : 0 ≤ p} {h₁ : p ≤ 1}

/-- A single trial succeeds on average with probability `p`. -/
theorem E_success : (bernoulli p h₀ h₁).E success = p := by
  simp [E, bernoulli, sumL, success]; grind

/-- The variance of a single trial is `p(1 − p)`. -/
theorem Var_success : (bernoulli p h₀ h₁).Var success = p * (1 - p) := by
  rw [Var_eq, E_success]
  have : (bernoulli p h₀ h₁).E (fun b => success b * success b) = p := by
    simp [E, bernoulli, sumL, success]; grind
  rw [this]; grind

/-- **The mean of the binomial distribution**: `E[Sₙ] = np`. -/
theorem binomial_mean (n : Nat) : ((bernoulli p h₀ h₁).pow n).E (sampleSum success n) = n * p := by
  rw [E_sampleSum, E_success]

/-- **The variance of the binomial distribution**: `Var Sₙ = np(1 − p)`. -/
theorem binomial_variance (n : Nat) :
    ((bernoulli p h₀ h₁).pow n).Var (sampleSum success n) = n * (p * (1 - p)) := by
  rw [Var_sampleSum, Var_success]

/-- **Bernoulli's theorem**: the relative frequency of success deviates from `p` by at
least `ε` with probability at most `p(1 − p)/(nε²)`. -/
theorem bernoulli_theorem {n : Nat} (hn : 0 < n) {ε : R} (hε : 0 < ε) :
    ((bernoulli p h₀ h₁).pow n).prob (fun t => ε ≤ OF.abs (sampleSum success n t / n - p)) ≤
      p * (1 - p) / (n * (ε * ε)) := by
  have := (bernoulli p h₀ h₁).weak_law success hn hε
  rwa [E_success, Var_success] at this

/-! ## The Monty Hall problem -/

/-- The Monty Hall space: an outcome `(c, h)` means the car is behind door `c` and the
host opens door `h` (you picked door `0`). -/
noncomputable def montyHall : FinProb (Nat × Nat) where
  pts := [(0, 1), (0, 2), (1, 2), (2, 1)]
  w := fun o => if o = (0, 1) ∨ o = (0, 2) then 1 / 6 else if o = (1, 2) ∨ o = (2, 1) then 1 / 3 else 0
  w_nonneg := fun o => by
    have h6 : (0 : R) < 1 / 6 := OF.div_pos (by grind) (by grind)
    have h3 : (0 : R) < 1 / 3 := OF.div_pos (by grind) (by grind)
    split
    · exact Std.le_of_lt h6
    · split
      · exact Std.le_of_lt h3
      · grind
  sum_one := by simp [sumL]; grind

/-- The host opens door `1`. -/
def opens1 : Event (Nat × Nat) := fun o => o.2 = 1

/-- The car is behind door `2`. -/
def carAt2 : Event (Nat × Nat) := fun o => o.1 = 2

/-- The car is behind door `0` (your original choice). -/
def carAt0 : Event (Nat × Nat) := fun o => o.1 = 0

/-- **Monty Hall: switching wins with probability `2/3`.** Given that the host opened
door `1`, the car is behind door `2` with probability `2/3`. -/
theorem monty_hall_switch : montyHall.cond carAt2 opens1 = 2 / 3 := by
  simp [cond, prob, montyHall, sumL, ind, carAt2, opens1]; grind

/-- **Monty Hall: staying wins with probability only `1/3`.** -/
theorem monty_hall_stay : montyHall.cond carAt0 opens1 = 1 / 3 := by
  simp [cond, prob, montyHall, sumL, ind, carAt0, opens1]; grind

/-- The same answer through Bayes' theorem: `P(car at 2 | opens 1) =
P(opens 1 | car at 2) P(car at 2) / P(opens 1) = 1 · (1/3) / (1/2)`. -/
theorem monty_hall_bayes :
    montyHall.cond opens1 carAt2 = 1 ∧ montyHall.prob carAt2 = 1 / 3 ∧ montyHall.prob opens1 = 1 / 2 ∧
      montyHall.cond carAt2 opens1 =
        montyHall.cond opens1 carAt2 * montyHall.prob carAt2 / montyHall.prob opens1 := by
  have h2 : montyHall.prob carAt2 = 1 / 3 := by
    simp [prob, montyHall, sumL, ind, carAt2]; grind
  refine ⟨?_, h2, ?_, bayes _ (by rw [h2]; grind)⟩
  · simp [cond, prob, montyHall, sumL, ind, carAt2, opens1]; grind
  · simp [prob, montyHall, sumL, ind, opens1]; grind

end FinProb

end Foundations.Probability
