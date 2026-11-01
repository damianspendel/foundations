import Foundations.Numbers.Arithmetic
import Foundations.Numbers.Exp
import Foundations.Numbers.Uncountable
import Foundations.Numbers.CompleteOrderedField
import Foundations.Algebra.Lagrange
import Foundations.Logic.BetaFunction

/-!
# Unification I: one notion of prime, factorial and absolute value

The parts of this project were written side by side, and some elementary notions were
defined more than once — each part wanting to stand on its own feet. An audit of the
whole project found the following duplicates that were never linked:

* **primes**: `Foundations.Numbers.Arith.Prime` (Part II, `Numbers/Arithmetic.lean`)
  and `Foundations.Algebra.IsPrime` (Part IV, `Algebra/Lagrange.lean`);
* **factorials**: `Foundations.Logic.FO.fact` (Part III, `Logic/BetaFunction.lean`,
  used for Gödel's β-function), `Foundations.Numbers.Arith.fact` (Part II,
  `Numbers/Arithmetic.lean`, used for Wilson-style divisibility facts) and
  `Foundations.Numbers.R.fact` (Part II, `Numbers/Exp.lean`, cast into the reals for
  the exponential series);
* **absolute value**: the hand-made `Q.abs` on the rationals (`Numbers/Cauchy.lean`,
  used to define Cauchy sequences) and the general ordered-field absolute value
  `OF.abs` (`Numbers/OrderedField.lean`), which applies both to `Q` and to the reals `R`.

This file proves that each family agrees: the two prime predicates are *the same
predicate*, the three factorials are *the same function* (so the real-valued
factorials of the exponential series are casts of the arithmetic ones), and the two
absolute values on `Q` coincide and are carried to the absolute value of `R` by the
embedding `ofQ : Q → R`. The definitions happen to have been written identically, so
some proofs are short; the point of stating them is that the project now *knows* it,
and any theorem about one notion transfers to the others.

The next files continue the audit with notions of size (countable, finite) and with
the two theories of ordinals.
-/

namespace Foundations.Bridges

open Foundations.Numbers

/-! ## Primes -/

/-- **Bridge: the two prime predicates agree.** Part II's `Arith.Prime`
(`Numbers/Arithmetic.lean`) and Part IV's `IsPrime` (`Algebra/Lagrange.lean`) are the
same predicate on natural numbers. -/
theorem prime_iff_isPrime (p : Nat) : Arith.Prime p ↔ Foundations.Algebra.IsPrime p :=
  Iff.rfl

/-- The two prime predicates are equal as functions `Nat → Prop`. -/
theorem prime_eq_isPrime : Arith.Prime = Foundations.Algebra.IsPrime := rfl

/-- **Euclid's lemma for Part IV's primes.** Transported along `prime_iff_isPrime`:
if `IsPrime p` (`Algebra/Lagrange.lean`) and `p ∣ a·b`, then `p ∣ a` or `p ∣ b`
(`Arith.euclid_lemma`, `Numbers/Arithmetic.lean`). -/
theorem isPrime_euclid {p a b : Nat} (hp : Foundations.Algebra.IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b :=
  Arith.euclid_lemma ((prime_iff_isPrime p).2 hp) h

/-- **Groups of order an arithmetic prime are cyclic.** Lagrange-file's
`isCyclic_of_prime_card` (`Algebra/Lagrange.lean`), stated with Part II's notion of
prime `Arith.Prime` (`Numbers/Arithmetic.lean`). -/
theorem isCyclic_of_arith_prime_card {G : Type} [Foundations.Algebra.Group G]
    [Foundations.Algebra.FiniteType G]
    (hp : Arith.Prime (Foundations.Algebra.FiniteType.card G)) :
    Foundations.Algebra.IsCyclic G :=
  Foundations.Algebra.isCyclic_of_prime_card ((prime_iff_isPrime _).1 hp)

/-! ## Factorials -/

/-- **Bridge: β-function factorial = arithmetic factorial.** Part III's
`FO.fact` (`Logic/BetaFunction.lean`) and Part II's `Arith.fact`
(`Numbers/Arithmetic.lean`) agree at every argument. -/
theorem logic_fact_eq_arith_fact (n : Nat) : Foundations.Logic.FO.fact n = Arith.fact n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (n + 1) * Foundations.Logic.FO.fact n = (n + 1) * Arith.fact n
    rw [ih]

/-- **Bridge: exponential-series factorial = arithmetic factorial.** The factorial
`R.fact` of `Numbers/Exp.lean` agrees with `Arith.fact` of `Numbers/Arithmetic.lean`. -/
theorem exp_fact_eq_arith_fact (n : Nat) : R.fact n = Arith.fact n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (n + 1) * R.fact n = (n + 1) * Arith.fact n
    rw [ih]

/-- **The three factorials are one function.** `FO.fact` (`Logic/BetaFunction.lean`),
`Arith.fact` (`Numbers/Arithmetic.lean`) and `R.fact` (`Numbers/Exp.lean`) are equal as
functions `Nat → Nat`. -/
theorem factorials_agree :
    Foundations.Logic.FO.fact = Arith.fact ∧ R.fact = Arith.fact :=
  ⟨funext logic_fact_eq_arith_fact, funext exp_fact_eq_arith_fact⟩

/-- **The real factorials are the cast of the arithmetic ones.** The denominators
`(n! : R)` of the exponential series (`Numbers/Exp.lean`) are the casts into the reals of
Part II's arithmetic factorial (`Numbers/Arithmetic.lean`) — and equally of the
β-function factorial (`Logic/BetaFunction.lean`). -/
theorem exp_fact_cast (n : Nat) :
    ((R.fact n : Nat) : R) = ((Arith.fact n : Nat) : R) ∧
      ((R.fact n : Nat) : R) = ((Foundations.Logic.FO.fact n : Nat) : R) := by
  rw [exp_fact_eq_arith_fact, logic_fact_eq_arith_fact]
  exact ⟨rfl, rfl⟩

/-! ## Absolute value -/

/-- **Bridge: the two absolute values on `Q` agree.** The hand-made `Q.abs` of
`Numbers/Cauchy.lean` equals the general ordered-field absolute value `OF.abs` of
`Numbers/OrderedField.lean`, instantiated at Part II's rationals `Q`. -/
theorem q_abs_eq_of_abs (q : Q) : Q.abs q = OF.abs q := by
  rcases OF.abs_cases q with ⟨h, e⟩ | ⟨h, e⟩
  · rw [e]; unfold Q.abs; exact ite_eq_left h
  · rw [e]; unfold Q.abs
    have : ¬ (0 : Q) ≤ q := fun h' => by grind
    exact ite_eq_right this

/-- **Bridge: the embedding `Q → R` carries absolute values.** For Part II's
embedding `ofQ` of the rationals into the Cauchy reals (`Numbers/Real.lean`), the
ordered-field absolute value of `R` (`Numbers/OrderedField.lean`) of `ofQ q` is the
image of the rational absolute value `Q.abs q` (`Numbers/Cauchy.lean`). -/
theorem of_abs_ofQ (q : Q) : OF.abs (R.ofQ q) = R.ofQ (Q.abs q) := by
  rw [q_abs_eq_of_abs]
  rcases OF.abs_cases q with ⟨h, e⟩ | ⟨h, e⟩
  · rw [e]
    have h' : (0 : R) ≤ R.ofQ q := R.ofQ_le.2 h
    rcases OF.abs_cases (R.ofQ q) with ⟨_, e'⟩ | ⟨h'', _⟩
    · exact e'
    · exact absurd h' (by grind)
  · rw [e, R.ofQ_neg]
    have h' : R.ofQ q < 0 := R.ofQ_lt.2 h
    rcases OF.abs_cases (R.ofQ q) with ⟨h'', _⟩ | ⟨_, e'⟩
    · exact absurd h'' (by grind)
    · exact e'

end Foundations.Bridges
