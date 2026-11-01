import Foundations.Numbers

/-!
# Finite probability spaces

Probability theory began with a letter. In the summer of 1654 Blaise Pascal and Pierre
de Fermat corresponded about the *problem of points* posed by the Chevalier de Méré: how
should the stakes of an interrupted game of chance be divided? Their answer — count the
equally likely ways the game could have continued — founded the calculus of chances.
Jacob Bernoulli's *Ars Conjectandi* (1713) proved the first limit theorem, the law of
large numbers; Thomas Bayes (1763) and Pierre-Simon Laplace (*Théorie analytique des
probabilités*, 1812) turned probability into a theory of inference from evidence.

What probability *is* remains debated. For the **frequentist**, `P(A)` is the long-run
relative frequency of `A` in repeated trials — and the law of large numbers (in
`LargeNumbers`) is the theorem that makes this reading coherent. For the **Bayesian**,
`P(A)` is a rational degree of belief, revised by Bayes' theorem as evidence arrives.
The mathematics is the same: Andrei Kolmogorov's *Grundbegriffe der
Wahrscheinlichkeitsrechnung* (1933) axiomatised probability as a measure of total mass
`1` on a σ-algebra of events. We stay **finite**, where measure theory reduces to sums:

* a **finite probability space** is a finite list of outcomes with non-negative real
  weights summing to `1` (outcomes may repeat; their weights simply add);
* an **event** is any predicate on outcomes; `P(A)` is the total weight of outcomes in
  `A`.

We prove inclusion–exclusion `P(A ∪ B) = P(A) + P(B) − P(A ∩ B)`, define conditional
probability `P(A | B) = P(A ∩ B) / P(B)`, and prove the **law of total probability** and
**Bayes' theorem** — for a single conditioning event and for a finite partition — and
the basic facts about **independence**. All numbers are the real numbers `R` of Part II.
-/

namespace Foundations.Probability

open Foundations.Numbers Lean.Grind Classical

/-! ## Finite sums -/

/-- The sum `∑_{x ∈ l} f x` over a list (with multiplicity). -/
def sumL {α : Type} (l : List α) (f : α → R) : R := (l.map f).foldr (· + ·) 0

section Sums
variable {α β : Type}

/-- The empty sum. -/
@[simp] theorem sumL_nil (f : α → R) : sumL [] f = 0 := rfl

/-- Peeling off the first term. -/
@[simp] theorem sumL_cons (a : α) (l : List α) (f : α → R) : sumL (a :: l) f = f a + sumL l f :=
  rfl

/-- The sum over a concatenation. -/
theorem sumL_append (l m : List α) (f : α → R) : sumL (l ++ m) f = sumL l f + sumL m f := by
  induction l with
  | nil => simp only [List.nil_append, sumL_nil]; grind
  | cons a l ih => simp only [List.cons_append, sumL_cons, ih]; grind

/-- Sums only depend on the values on the list. -/
theorem sumL_congr {l : List α} {f g : α → R} (h : ∀ x ∈ l, f x = g x) : sumL l f = sumL l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [sumL_cons, h a (List.mem_cons_self ..),
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **Additivity** of sums. -/
theorem sumL_add (l : List α) (f g : α → R) : sumL l (fun x => f x + g x) = sumL l f + sumL l g := by
  induction l with
  | nil => simp; grind
  | cons a l ih => simp only [sumL_cons, ih]; grind

/-- Constants factor out of sums. -/
theorem sumL_mul_left (l : List α) (c : R) (f : α → R) : sumL l (fun x => c * f x) = c * sumL l f := by
  induction l with
  | nil => simp; grind
  | cons a l ih => simp only [sumL_cons, ih]; grind

/-- Constants factor out of sums, on the right. -/
theorem sumL_mul_right (l : List α) (c : R) (f : α → R) : sumL l (fun x => f x * c) = sumL l f * c := by
  induction l with
  | nil => simp; grind
  | cons a l ih => simp only [sumL_cons, ih]; grind

/-- Sums of differences. -/
theorem sumL_sub (l : List α) (f g : α → R) : sumL l (fun x => f x - g x) = sumL l f - sumL l g := by
  induction l with
  | nil => simp; grind
  | cons a l ih => simp only [sumL_cons, ih]; grind

/-- The sum of zeros. -/
theorem sumL_zero (l : List α) : sumL l (fun _ => (0 : R)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [sumL_cons, ih]; grind

/-- **Monotonicity** of sums. -/
theorem sumL_le {l : List α} {f g : α → R} (h : ∀ x ∈ l, f x ≤ g x) : sumL l f ≤ sumL l g := by
  induction l with
  | nil => exact Std.le_refl _
  | cons a l ih =>
      simp only [sumL_cons]
      have h₁ := h a (List.mem_cons_self ..)
      have h₂ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
      grind

/-- Sums of non-negative terms are non-negative. -/
theorem sumL_nonneg {l : List α} {f : α → R} (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ sumL l f := by
  have := sumL_le (g := f) (f := fun _ => 0) h
  rwa [sumL_zero] at this

/-- **Exchanging the order of summation.** -/
theorem sumL_comm (l : List α) (m : List β) (f : α → β → R) :
    sumL l (fun a => sumL m (fun b => f a b)) = sumL m (fun b => sumL l (fun a => f a b)) := by
  induction l with
  | nil => simp; exact (sumL_zero m).symm
  | cons a l ih => simp only [sumL_cons, ih, sumL_add]

/-- Sums over the outcomes of a map. -/
theorem sumL_map (l : List α) (g : α → β) (f : β → R) : sumL (l.map g) f = sumL l (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, sumL_cons, ih]

end Sums

/-! ## Probability spaces and events -/

/-- A **finite probability space**: a list of outcomes with non-negative real weights of
total mass `1`. -/
structure FinProb (α : Type) where
  /-- The outcomes (repetitions allowed; weights add). -/
  pts : List α
  /-- The weight of each outcome. -/
  w : α → R
  /-- Weights are non-negative. -/
  w_nonneg : ∀ x, 0 ≤ w x
  /-- The total mass is `1`. -/
  sum_one : sumL pts w = 1

namespace FinProb

variable {α : Type} (P : FinProb α)

/-- An **event** is a predicate on outcomes. -/
abbrev Event (α : Type) : Type := α → Prop

/-- The indicator function `1_A` of an event. -/
noncomputable def ind (A : Event α) (x : α) : R := if A x then 1 else 0

/-- **The probability of an event**: the total weight of its outcomes. -/
noncomputable def prob (A : Event α) : R := sumL P.pts fun x => P.w x * ind A x

/-- Indicators are `0` or `1`. -/
theorem ind_cases (A : Event α) (x : α) : (A x ∧ ind A x = 1) ∨ (¬ A x ∧ ind A x = 0) := by
  by_cases h : A x
  · exact Or.inl ⟨h, by simp [ind, h]⟩
  · exact Or.inr ⟨h, by simp [ind, h]⟩

/-- Indicators are non-negative. -/
theorem ind_nonneg (A : Event α) (x : α) : 0 ≤ ind A x := by
  rcases ind_cases A x with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> grind

/-- Indicators are at most `1`. -/
theorem ind_le_one (A : Event α) (x : α) : ind A x ≤ 1 := by
  rcases ind_cases A x with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> grind

/-- The indicator of an intersection is the product of indicators. -/
theorem ind_and (A B : Event α) (x : α) : ind (fun y => A y ∧ B y) x = ind A x * ind B x := by
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ind, ha, hb] <;> grind

/-- **Inclusion–exclusion for indicators.** -/
theorem ind_or (A B : Event α) (x : α) :
    ind (fun y => A y ∨ B y) x = ind A x + ind B x - ind (fun y => A y ∧ B y) x := by
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ind, ha, hb] <;> grind

/-- The indicator of a complement. -/
theorem ind_not (A : Event α) (x : α) : ind (fun y => ¬ A y) x = 1 - ind A x := by
  by_cases ha : A x <;> simp [ind, ha] <;> grind

/-- Probabilities are non-negative. -/
theorem prob_nonneg (A : Event α) : 0 ≤ P.prob A :=
  sumL_nonneg fun x _ => OrderedRing.mul_nonneg (P.w_nonneg x) (ind_nonneg A x)

/-- Events with the same outcomes (on the space) have the same probability. -/
theorem prob_congr {A B : Event α} (h : ∀ x ∈ P.pts, (A x ↔ B x)) : P.prob A = P.prob B :=
  sumL_congr fun x hx => by simp only [ind, propext (h x hx)]

/-- The sure event has probability `1`. -/
theorem prob_true : P.prob (fun _ => True) = 1 := by
  rw [prob, ← P.sum_one]; exact sumL_congr fun x _ => by simp [ind]; grind

/-- The impossible event has probability `0`. -/
theorem prob_false : P.prob (fun _ => False) = 0 := by
  rw [prob, ← sumL_zero P.pts]; exact sumL_congr fun x _ => by simp [ind]; grind

/-- **Inclusion–exclusion**: `P(A ∪ B) = P(A) + P(B) − P(A ∩ B)`. -/
theorem prob_or (A B : Event α) :
    P.prob (fun x => A x ∨ B x) = P.prob A + P.prob B - P.prob (fun x => A x ∧ B x) := by
  simp only [prob]
  rw [← sumL_add, ← sumL_sub]
  exact sumL_congr fun x _ => by rw [ind_or]; grind

/-- **Additivity** for disjoint events. -/
theorem prob_or_disjoint {A B : Event α} (h : ∀ x, ¬ (A x ∧ B x)) :
    P.prob (fun x => A x ∨ B x) = P.prob A + P.prob B := by
  rw [prob_or, prob_congr P (B := fun _ => False) fun x _ => ⟨fun hx => h x hx, False.elim⟩,
    prob_false]
  grind

/-- **The complement rule**: `P(Aᶜ) = 1 − P(A)`. -/
theorem prob_not (A : Event α) : P.prob (fun x => ¬ A x) = 1 - P.prob A := by
  rw [← prob_true P, prob, prob, prob, ← sumL_sub]
  exact sumL_congr fun x _ => by rw [ind_not]; simp [ind]; grind

/-- **Monotonicity**: `A ⊆ B` implies `P(A) ≤ P(B)`. -/
theorem prob_mono {A B : Event α} (h : ∀ x, A x → B x) : P.prob A ≤ P.prob B := by
  refine sumL_le fun x _ => OrderedRing.mul_le_mul_of_nonneg_left ?_ (P.w_nonneg x)
  by_cases ha : A x
  · simp [ind, ha, h x ha]
  · exact (show ind A x = 0 by simp [ind, ha]) ▸ ind_nonneg B x

/-- Probabilities are at most `1`. -/
theorem prob_le_one (A : Event α) : P.prob A ≤ 1 := by
  rw [← prob_true P]; exact prob_mono P fun _ _ => trivial

/-! ## Conditional probability, total probability, Bayes -/

/-- **Conditional probability** `P(A | B) = P(A ∩ B) / P(B)`. -/
noncomputable def cond (A B : Event α) : R := P.prob (fun x => A x ∧ B x) / P.prob B

/-- **The multiplication rule** `P(A ∩ B) = P(A | B) · P(B)` (for `P(B) ≠ 0`). -/
theorem prob_and_eq_cond_mul {A B : Event α} (hB : P.prob B ≠ 0) :
    P.prob (fun x => A x ∧ B x) = P.cond A B * P.prob B := by
  simp only [cond]; grind

/-- An event splits along `B` and its complement. -/
theorem prob_split (A B : Event α) :
    P.prob A = P.prob (fun x => A x ∧ B x) + P.prob (fun x => A x ∧ ¬ B x) := by
  rw [← prob_or_disjoint P fun x h => h.2.2 h.1.2]
  exact prob_congr P fun x _ => ⟨fun ha => (Classical.em (B x)).elim (fun hb => Or.inl ⟨ha, hb⟩)
    fun hb => Or.inr ⟨ha, hb⟩, fun h => h.elim And.left And.left⟩

/-- **The law of total probability** (two cases):
`P(A) = P(A | B) P(B) + P(A | Bᶜ) P(Bᶜ)`, provided both conditioning events are possible. -/
theorem total_probability {A B : Event α} (hB : P.prob B ≠ 0) (hB' : P.prob (fun x => ¬ B x) ≠ 0) :
    P.prob A = P.cond A B * P.prob B + P.cond A (fun x => ¬ B x) * P.prob (fun x => ¬ B x) := by
  rw [← prob_and_eq_cond_mul P hB, ← prob_and_eq_cond_mul P hB']; exact prob_split P A B

/-- **Bayes' theorem**: `P(B | A) = P(A | B) P(B) / P(A)`. -/
theorem bayes {A B : Event α} (hB : P.prob B ≠ 0) :
    P.cond B A = P.cond A B * P.prob B / P.prob A := by
  rw [← prob_and_eq_cond_mul P hB]
  simp only [cond]
  rw [prob_congr P (A := fun x => B x ∧ A x) (B := fun x => A x ∧ B x) fun x _ => And.comm]

/-- **Bayes' theorem with the law of total probability** in the denominator:
`P(B | A) = P(A | B) P(B) / (P(A | B) P(B) + P(A | Bᶜ) P(Bᶜ))`. -/
theorem bayes_total {A B : Event α} (hB : P.prob B ≠ 0) (hB' : P.prob (fun x => ¬ B x) ≠ 0) :
    P.cond B A = P.cond A B * P.prob B /
      (P.cond A B * P.prob B + P.cond A (fun x => ¬ B x) * P.prob (fun x => ¬ B x)) := by
  rw [← total_probability P hB hB']; exact bayes P hB

/-- A finite **partition** `B 0, …, B (n−1)` of the space: on the outcomes, exactly one
`B i` holds. -/
def IsPartition (B : Nat → Event α) (n : Nat) : Prop :=
  ∀ x ∈ P.pts, (∃ i, i < n ∧ B i x) ∧ ∀ i j, i < n → j < n → B i x → B j x → i = j

/-- The sum `∑_{i<n} f i`. -/
def sumN (n : Nat) (f : Nat → R) : R := sumL (List.range n) f

/-- The indicator of an event is the sum of its pieces along a partition. -/
theorem ind_partition {B : Nat → Event α} {n : Nat} (A : Event α) (x : α)
    (hx : (∃ i, i < n ∧ B i x) ∧ ∀ i j, i < n → j < n → B i x → B j x → i = j) :
    ind A x = sumN n fun i => ind (fun y => A y ∧ B i y) x := by
  obtain ⟨⟨i₀, hi₀, hB₀⟩, huniq⟩ := hx
  -- split the range at `i₀`
  have key : ∀ m, m ≤ n → sumL (List.range m) (fun i => ind (fun y => A y ∧ B i y) x) =
      if i₀ < m then ind A x else 0 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
        intro hmn
        rw [List.range_succ, sumL_append, ih (by omega)]
        simp only [sumL_cons, sumL_nil]
        by_cases hm : m = i₀
        · subst hm
          simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true, ind_and,
            show ind (B m) x = 1 by simp [ind, hB₀]]
          grind
        · have hBm : ind (fun y => A y ∧ B m y) x = 0 := by
            have hn : ¬ (A x ∧ B m x) := fun h => absurd (huniq m i₀ (by omega) hi₀ h.2 hB₀) hm
            rcases ind_cases (fun y => A y ∧ B m y) x with ⟨h, _⟩ | ⟨_, h⟩
            · exact absurd h hn
            · exact h
          rw [hBm]
          by_cases h : i₀ < m
          · simp [h, show i₀ < m + 1 by omega]; grind
          · simp [h, show ¬ i₀ < m + 1 by omega]; grind
  rw [sumN, key n (Nat.le_refl _)]; simp [hi₀]

/-- **The law of total probability** for a finite partition:
`P(A) = ∑ᵢ P(A ∩ Bᵢ)`, and `= ∑ᵢ P(A | Bᵢ) P(Bᵢ)` when every `Bᵢ` is possible. -/
theorem total_probability_partition {B : Nat → Event α} {n : Nat} (hB : P.IsPartition B n)
    (A : Event α) : P.prob A = sumN n fun i => P.prob (fun x => A x ∧ B i x) := by
  simp only [prob, sumN]
  rw [sumL_comm]
  refine sumL_congr fun x hx => ?_
  rw [ind_partition A x (hB x hx), sumN, ← sumL_mul_left]

/-- Total probability with conditional probabilities. -/
theorem total_probability_cond {B : Nat → Event α} {n : Nat} (hB : P.IsPartition B n)
    (hpos : ∀ i, i < n → P.prob (B i) ≠ 0) (A : Event α) :
    P.prob A = sumN n fun i => P.cond A (B i) * P.prob (B i) := by
  rw [total_probability_partition P hB A]
  exact sumL_congr fun i hi => prob_and_eq_cond_mul P (hpos i (List.mem_range.1 hi))

/-- **Bayes' theorem for a partition**: `P(Bⱼ | A) = P(A | Bⱼ) P(Bⱼ) / ∑ᵢ P(A | Bᵢ) P(Bᵢ)`. -/
theorem bayes_partition {B : Nat → Event α} {n : Nat} (hB : P.IsPartition B n)
    (hpos : ∀ i, i < n → P.prob (B i) ≠ 0) (A : Event α) {j : Nat} (hj : j < n) :
    P.cond (B j) A = P.cond A (B j) * P.prob (B j) / sumN n fun i => P.cond A (B i) * P.prob (B i) := by
  rw [← total_probability_cond P hB hpos A]; exact bayes P (hpos j hj)

/-! ## Independence -/

/-- Events `A` and `B` are **independent** if `P(A ∩ B) = P(A) P(B)`. -/
def Indep (A B : Event α) : Prop := P.prob (fun x => A x ∧ B x) = P.prob A * P.prob B

/-- Independence is symmetric. -/
theorem Indep.symm {A B : Event α} (h : P.Indep A B) : P.Indep B A := by
  unfold Indep at *
  rw [prob_congr P (B := fun x => A x ∧ B x) fun x _ => And.comm, h]; grind

/-- For a possible `B`, independence means that conditioning on `B` does not change the
probability of `A`. -/
theorem indep_iff_cond {A B : Event α} (hB : P.prob B ≠ 0) : P.Indep A B ↔ P.cond A B = P.prob A := by
  unfold Indep cond
  constructor
  · intro h; rw [h]; grind
  · intro h
    have := prob_and_eq_cond_mul P (A := A) hB
    unfold cond at this
    rw [h] at this; exact this

/-- If `A` and `B` are independent, so are `A` and `Bᶜ`. -/
theorem Indep.compl {A B : Event α} (h : P.Indep A B) : P.Indep A (fun x => ¬ B x) := by
  unfold Indep at *
  have hs := prob_split P A B
  rw [prob_not]
  grind

/-- Any event is independent of the sure event. -/
theorem indep_true (A : Event α) : P.Indep A (fun _ => True) := by
  unfold Indep
  rw [prob_true, prob_congr P (B := A) fun x _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩]; grind

end FinProb

end Foundations.Probability
