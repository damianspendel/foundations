import Foundations.Topology.OuterMeasure

/-!
# σ-algebras, measurable functions and measures

## The measure problem

What is the "size" of a set of real numbers? For an interval it is its length, and Émile
**Borel** (1898) proposed that the size of a countable disjoint union should be the sum of the
sizes of the pieces. Henri **Lebesgue**, in his thesis *Intégrale, longueur, aire* (1902), posed
the **measure problem**: find a function `m` on *all* bounded sets of reals that is countably
additive, invariant under translation and gives `[0, 1]` the value `1`. Vitali's set
(`Vitali.lean`) shows that the problem has no solution: with the axiom of choice there are sets
that cannot be measured at all.

The way out — Borel's, Lebesgue's and above all Carathéodory's — is to give up measuring every
set and to measure only the sets of a **σ-algebra**: a family that contains the empty set and is
closed under complements and *countable* unions. Countable (not merely finite) unions are what
makes limits possible; they are the difference between Jordan's content and Lebesgue's measure.

## What this file does

Sets of points of a type `α` are predicates `α → Prop`. We define

* `SigmaAlgebra α` and its closure properties (finite unions and intersections, differences,
  countable intersections);
* **measurable functions** `f : α → R`: all sets `{c < f}` are measurable; then all sets
  `{c ≤ f}`, `{f < c}`, `{f ≤ c}` are as well, sums and pointwise limits of measurable functions
  are measurable (the proof for sums runs through an enumeration of the rationals);
* **measures**: non-negative, countably additive set functions, expressed with `HasSum` from
  Part II. **Our measures are finite**: `μ` takes values in `R`, so `μ(α) < ∞`. This avoids the
  extended reals `[0, ∞]` altogether; Lebesgue measure will be treated on bounded intervals
  `[a, b]`, which is enough for everything we do with it (and for comparison with the Riemann
  integral).
* the basic properties: finite additivity, monotonicity, subtraction, **continuity from below
  and from above**.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace MeasureTheory

/-- Two predicates with the same members are equal (extensionality for sets). -/
theorem set_ext {α : Type} {A B : α → Prop} (h : ∀ x, A x ↔ B x) : A = B :=
  funext fun x => propext (h x)

/-! ## Real-number helpers -/

/-- Division by a positive number preserves a strict lower bound. -/
theorem lt_div_of_mul_lt {x a d : R} (hd : 0 < d) (h : x * d < a) : x < a / d := by
  apply Classical.byContradiction; intro hn
  have := OrderedRing.mul_le_mul_of_nonneg_right (by grind : a / d ≤ x) (Std.le_of_lt hd)
  have e : a / d * d = a := by grind
  grind

/-- Division by a positive number preserves a non-strict upper bound. -/
theorem div_le_of_le_mul {x a d : R} (hd : 0 < d) (h : a ≤ x * d) : a / d ≤ x := by
  apply Classical.byContradiction; intro hn
  have := OrderedRing.mul_lt_mul_of_pos_right (by grind : x < a / d) hd
  have e : a / d * d = a := by grind
  grind

/-- Division by a positive number preserves a strict upper bound. -/
theorem div_lt_of_lt_mul {x a d : R} (hd : 0 < d) (h : a < x * d) : a / d < x := by
  apply Classical.byContradiction; intro hn
  have := OrderedRing.mul_le_mul_of_nonneg_right (by grind : x ≤ a / d) (Std.le_of_lt hd)
  have e : a / d * d = a := by grind
  grind

/-- `1/(n+1) ≤ 1`. -/
theorem eps_le_one (n : Nat) : 1 / ((n : R) + 1) ≤ 1 := by
  have h0 : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  exact div_le_of_le_mul (by grind) (by grind)

/-! ## An enumeration of `ℕ × ℕ` and of the rationals -/

/-- The diagonal walk through `ℕ × ℕ`: `(0,0), (1,0), (0,1), (2,0), (1,1), (0,2), …`. -/
def pairEnum : Nat → Nat × Nat
  | 0 => (0, 0)
  | k + 1 => match pairEnum k with
    | (0, j) => (j + 1, 0)
    | (i + 1, j) => (i, j + 1)

/-- The triangular numbers `0, 1, 3, 6, …`. -/
def tr : Nat → Nat
  | 0 => 0
  | d + 1 => tr d + d + 1

/-- The inverse of the walk: the position of `(i, j)`. -/
def pairIndex (p : Nat × Nat) : Nat := tr (p.1 + p.2) + p.2

/-- The walk visits the `d`-th diagonal from `(d, 0)` to `(0, d)`. -/
theorem pairEnum_diag : ∀ d j, j ≤ d → pairEnum (tr d + j) = (d - j, j) := by
  intro d
  induction d with
  | zero => intro j hj; rw [show j = 0 by omega]; rfl
  | succ d ih =>
    intro j
    induction j with
    | zero =>
      intro _
      have h := ih d (Nat.le_refl d)
      show pairEnum (tr d + d + 1) = _
      simp [pairEnum, h]
    | succ j ihj =>
      intro hj
      have h := ihj (by omega)
      show pairEnum (tr (d + 1) + j + 1) = _
      simp only [pairEnum, h]
      obtain ⟨i, hi⟩ : ∃ i, d + 1 - j = i + 1 := ⟨d - j, by omega⟩
      rw [hi]; simp only; congr 1 <;> omega

/-- **The walk is surjective.** Every pair is visited. -/
theorem pairEnum_surj (i j : Nat) : pairEnum (pairIndex (i, j)) = (i, j) := by
  have := pairEnum_diag (i + j) j (by omega)
  unfold pairIndex; simp only; rw [this]; congr 1; omega

/-- `pairIndex` undoes the walk. -/
theorem pairIndex_enum (k : Nat) : pairIndex (pairEnum k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    revert ih
    show pairIndex (pairEnum k) = k → pairIndex (match pairEnum k with
      | (0, j) => (j + 1, 0) | (i + 1, j) => (i, j + 1)) = k + 1
    generalize pairEnum k = p
    obtain ⟨i, j⟩ := p
    cases i with
    | zero =>
      intro h; unfold pairIndex at *; simp only at *
      show tr (j + 1 + 0) + 0 = k + 1
      rw [Nat.add_zero, Nat.add_zero]; show tr j + j + 1 = k + 1
      rw [Nat.zero_add] at h; omega
    | succ i =>
      intro h; unfold pairIndex at *; simp only at *
      rw [show i + 1 + j = i + (j + 1) by omega] at h; omega

/-- **The walk is injective.** -/
theorem pairEnum_inj {k l : Nat} (h : pairEnum k = pairEnum l) : k = l := by
  rw [← pairIndex_enum k, ← pairIndex_enum l, h]

/-- An enumeration of the integers: `0, −1, 1, −2, 2, …`. -/
def intEnum (k : Nat) : Int := if k % 2 = 0 then (k / 2 : Nat) else -((k / 2 : Nat) : Int) - 1

/-- Every integer is enumerated. -/
theorem intEnum_surj (a : Int) : ∃ k, intEnum k = a := by
  rcases Int.lt_or_le a 0 with h | h
  · refine ⟨2 * (-a - 1).toNat + 1, ?_⟩
    unfold intEnum
    rw [Outer.ite_neg' (by omega)]
    rw [show (2 * (-a - 1).toNat + 1) / 2 = (-a - 1).toNat by omega]; omega
  · exact ⟨2 * a.toNat, by unfold intEnum; split <;> omega⟩

/-- An enumeration `ratEnum 0, ratEnum 1, …` of the rational numbers `a/(n+1)`. -/
noncomputable def ratEnum (k : Nat) : R :=
  ((intEnum (pairEnum k).1 : Int) : R) / (((pairEnum k).2 : Nat) + 1)

/-- **The rationals are dense.** Between two reals lies some `ratEnum k`. -/
theorem ratEnum_dense {x y : R} (h : x < y) : ∃ k, x < ratEnum k ∧ ratEnum k < y := by
  obtain ⟨N, hN⟩ := eps_small (by grind : (0 : R) < y - x)
  have hN := hN N (Nat.le_refl N)
  have h0 : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg
  have hd : (0 : R) < (N : R) + 1 := by grind
  obtain ⟨m, hm1, hm2⟩ := exists_floor (K := R) archimedean (x * ((N : R) + 1))
  obtain ⟨i, hi⟩ := intEnum_surj (m + 1)
  refine ⟨pairIndex (i, N), ?_⟩
  unfold ratEnum; rw [pairEnum_surj]; simp only; rw [hi]
  have e : (((m + 1 : Int)) : R) = (m : R) + 1 := by
    have := Ring.intCast_add (α := R) m 1; rw [this, Ring.intCast_one]
  rw [e]
  constructor
  · exact lt_div_of_mul_lt hd (by grind)
  · have h1 : ((m : R) + 1) / ((N : R) + 1) ≤ x + 1 / ((N : R) + 1) := by
      apply div_le_of_le_mul hd
      have e2 : (x + 1 / ((N : R) + 1)) * ((N : R) + 1) = x * ((N : R) + 1) + 1 := by grind
      grind
    grind

/-! ## σ-algebras -/

/-- **σ-algebra.** A family `M` of subsets of `α` containing `∅` and closed under complements and
countable unions — Borel's and Lebesgue's answer to the measure problem: measure not every set,
but every set of such a family. -/
structure SigmaAlgebra (α : Type) where
  /-- The measurable sets. -/
  M : (α → Prop) → Prop
  /-- `∅` is measurable. -/
  empty : M (fun _ => False)
  /-- Complements of measurable sets are measurable. -/
  compl : ∀ A, M A → M (fun x => ¬ A x)
  /-- Countable unions of measurable sets are measurable. -/
  iUnion : ∀ A : Nat → α → Prop, (∀ n, M (A n)) → M (fun x => ∃ n, A n x)

namespace SigmaAlgebra

variable {α : Type} (S : SigmaAlgebra α)

/-- The sequence `A, B, ∅, ∅, …`. -/
def seq2 {α : Type} (A B : α → Prop) : Nat → α → Prop
  | 0 => A
  | 1 => B
  | _ + 2 => fun _ => False

/-- The union of `A, B, ∅, ∅, …` is `A ∪ B`. -/
theorem iUnion_seq2 {α : Type} (A B : α → Prop) :
    (fun x => ∃ n, seq2 A B n x) = (fun x => A x ∨ B x) :=
  set_ext fun x => ⟨fun ⟨n, h⟩ => by
    match n, h with
    | 0, h => exact Or.inl h
    | 1, h => exact Or.inr h, fun h => h.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)⟩

/-- Only the first two members of `seq2 A B` can be non-empty. -/
theorem seq2_measurable {A B : α → Prop} (hA : S.M A) (hB : S.M B) : ∀ n, S.M (seq2 A B n)
  | 0 => hA
  | 1 => hB
  | _ + 2 => S.empty

/-- The whole space is measurable. -/
theorem univ : S.M (fun _ => True) := by
  have := S.compl _ S.empty
  rwa [show (fun x : α => ¬ False) = fun _ => True from set_ext fun _ => by simp] at this

/-- The union of two measurable sets is measurable. -/
theorem union {A B : α → Prop} (hA : S.M A) (hB : S.M B) : S.M (fun x => A x ∨ B x) := by
  have := S.iUnion _ (S.seq2_measurable hA hB); rwa [iUnion_seq2] at this

/-- Measurability respects equality of sets. -/
theorem congr {A B : α → Prop} (hA : S.M A) (h : ∀ x, A x ↔ B x) : S.M B := by
  rwa [← set_ext h]

/-- The intersection of two measurable sets is measurable. -/
theorem inter {A B : α → Prop} (hA : S.M A) (hB : S.M B) : S.M (fun x => A x ∧ B x) :=
  S.congr (S.compl _ (S.union (S.compl _ hA) (S.compl _ hB))) fun x => by
    by_cases a : A x <;> by_cases b : B x <;> simp [a, b]

/-- The difference of two measurable sets is measurable. -/
theorem diff {A B : α → Prop} (hA : S.M A) (hB : S.M B) : S.M (fun x => A x ∧ ¬ B x) :=
  S.inter hA (S.compl _ hB)

/-- Countable intersections of measurable sets are measurable. -/
theorem iInter (A : Nat → α → Prop) (h : ∀ n, S.M (A n)) : S.M (fun x => ∀ n, A n x) :=
  S.congr (S.compl _ (S.iUnion _ fun n => S.compl _ (h n))) fun _ =>
    ⟨fun h n => Classical.byContradiction fun hn => h ⟨n, hn⟩, fun h ⟨n, hn⟩ => hn (h n)⟩

end SigmaAlgebra

/-! ## Measurable functions -/

/-- **Measurable function.** `f : α → R` is measurable for `S` if every set `{x | c < f x}` is
measurable (Lebesgue's definition). -/
def Measurable {α : Type} (S : SigmaAlgebra α) (f : α → R) : Prop :=
  ∀ c : R, S.M (fun x => c < f x)

namespace Measurable

variable {α : Type} {S : SigmaAlgebra α} {f g : α → R}

/-- `{f ≤ c}` is measurable. -/
theorem le (hf : Measurable S f) (c : R) : S.M (fun x => f x ≤ c) :=
  S.congr (S.compl _ (hf c)) fun x => by grind

/-- `{c ≤ f}` is measurable: it is `⋂ₙ {c − 1/(n+1) < f}`. -/
theorem ge (hf : Measurable S f) (c : R) : S.M (fun x => c ≤ f x) :=
  S.congr (S.iInter _ fun n => hf (c - 1 / ((n : R) + 1))) fun x => by
    constructor
    · intro h; apply Classical.byContradiction; intro hn
      obtain ⟨N, hN⟩ := eps_small (by grind : (0 : R) < c - f x)
      have := h N; have := hN N (Nat.le_refl N); grind
    · intro h n; have := eps_pos n; grind

/-- `{f < c}` is measurable. -/
theorem lt (hf : Measurable S f) (c : R) : S.M (fun x => f x < c) :=
  S.congr (S.compl _ (hf.ge c)) fun x => by grind

/-- Constants are measurable. -/
theorem const (S : SigmaAlgebra α) (a : R) : Measurable S (fun _ => a) := fun c => by
  by_cases h : c < a
  · exact S.congr S.univ fun _ => by simp [h]
  · exact S.congr S.empty fun _ => by simp [h]

/-- The negative of a measurable function is measurable. -/
theorem neg (hf : Measurable S f) : Measurable S (fun x => -f x) := fun c =>
  S.congr (hf.lt (-c)) fun x => by grind

/-- **Sums of measurable functions are measurable.**
`{c < f + g} = ⋃_q {q < f} ∩ {c − q < g}` over the rationals `q`. -/
theorem add (hf : Measurable S f) (hg : Measurable S g) : Measurable S (fun x => f x + g x) :=
  fun c => S.congr (S.iUnion _ fun k => S.inter (hf (ratEnum k)) (hg (c - ratEnum k))) fun x => by
    constructor
    · rintro ⟨k, h1, h2⟩; grind
    · intro h
      obtain ⟨k, hk1, hk2⟩ := ratEnum_dense (by grind : c - g x < f x)
      exact ⟨k, hk2, by grind⟩

/-- Differences of measurable functions are measurable. -/
theorem sub (hf : Measurable S f) (hg : Measurable S g) : Measurable S (fun x => f x - g x) :=
  fun c => S.congr (hf.add hg.neg c) fun x => by grind

/-- Non-negative constant multiples of measurable functions are measurable. -/
theorem const_mul (hf : Measurable S f) {a : R} (ha : 0 ≤ a) : Measurable S (fun x => a * f x) := by
  rcases (by grind : a = 0 ∨ 0 < a) with h | h
  · exact fun c => S.congr (const S 0 c) fun x => by rw [h]; grind
  · intro c
    refine S.congr (hf (c / a)) fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have := OrderedRing.mul_lt_mul_of_pos_left hx h
      have e : a * (c / a) = c := by grind
      grind
    · exact div_lt_of_lt_mul h (by have : c < a * f x := hx; grind)

/-- **Pointwise limits of measurable functions are measurable.**
`{c < f} = ⋃ₘ ⋃_N ⋂_{n ≥ N} {c + 1/(m+1) < fₙ}`. -/
theorem of_tendsto {F : Nat → α → R} (hF : ∀ n, Measurable S (F n))
    (hlim : ∀ x, Tendsto (fun n => F n x) (f x)) : Measurable S f := fun c =>
  S.congr (S.iUnion _ fun m => S.iUnion _ fun N => S.iInter _ fun j =>
      hF (N + j) (c + 1 / ((m : R) + 1))) fun x => by
    constructor
    · rintro ⟨m, N, h⟩
      have := le_of_tendsto ((hlim x).shift N) fun j => Std.le_of_lt (h j)
      have := eps_pos m; grind
    · intro h
      obtain ⟨m, hm⟩ := eps_small (by grind : (0 : R) < (f x - c) / 2)
      have hm := hm m (Nat.le_refl m)
      obtain ⟨N, hN⟩ := hlim x ((f x - c) / 2) (by grind)
      refine ⟨m, N, fun j => ?_⟩
      have := abs_lt.1 (hN (N + j) (by omega)); grind

end Measurable

/-! ## Measures -/

/-- **Measure.** (Finite.) A function `μ` on sets, non-negative on measurable sets, with
`μ ∅ = 0`, and **countably additive**: for pairwise disjoint measurable `A₀, A₁, …` the series
`Σ μ(Aₙ)` converges to `μ(⋃ Aₙ)`. Values lie in `R`, so all our measures are finite. -/
structure Measure {α : Type} (S : SigmaAlgebra α) where
  /-- The measure of a set. -/
  μ : (α → Prop) → R
  /-- Measures are non-negative. -/
  nonneg : ∀ A, S.M A → 0 ≤ μ A
  /-- The empty set has measure `0`. -/
  empty : μ (fun _ => False) = 0
  /-- Countable additivity. -/
  additive : ∀ A : Nat → α → Prop, (∀ n, S.M (A n)) →
    (∀ i j, i ≠ j → ∀ x, A i x → A j x → False) →
    HasSum (fun n => μ (A n)) (μ (fun x => ∃ n, A n x))

namespace Measure

variable {α : Type} {S : SigmaAlgebra α} (m : Measure S)

/-- **Finite additivity.** `μ(A ∪ B) = μ A + μ B` for disjoint measurable `A`, `B`. -/
theorem union {A B : α → Prop} (hA : S.M A) (hB : S.M B) (hd : ∀ x, A x → B x → False) :
    m.μ (fun x => A x ∨ B x) = m.μ A + m.μ B := by
  have h := m.additive _ (S.seq2_measurable hA hB) (by
    intro i j hij x hi hj
    match i, j, hi, hj with
    | 0, 1, hi, hj => exact hd x hi hj
    | 1, 0, hi, hj => exact hd x hj hi
    | 0, 0, _, _ => exact hij rfl
    | 1, 1, _, _ => exact hij rfl)
  rw [SigmaAlgebra.iUnion_seq2] at h
  have h2 := Vitali.InvariantMeasure.hasSum_of_zero (b := fun n => m.μ (SigmaAlgebra.seq2 A B n))
    (m := 2) fun k hk => by
      match k, hk with
      | _ + 2, _ => exact m.empty
  have := h.unique h2
  rw [this]; show 0 + m.μ A + m.μ B = _; grind

/-- Measure respects equality of sets. -/
theorem congr {A B : α → Prop} (h : ∀ x, A x ↔ B x) : m.μ A = m.μ B := by rw [set_ext h]

/-- Splitting `B` along a measurable `A`: `μ B = μ(B ∩ A) + μ(B ∖ A)`. -/
theorem split {A B : α → Prop} (hA : S.M A) (hB : S.M B) :
    m.μ B = m.μ (fun x => B x ∧ A x) + m.μ (fun x => B x ∧ ¬ A x) := by
  rw [← m.union (S.inter hB hA) (S.diff hB hA) (fun x h1 h2 => h2.2 h1.2)]
  exact m.congr fun x => by by_cases a : A x <;> simp [a]

/-- **Monotonicity.** `A ⊆ B` implies `μ A ≤ μ B`. -/
theorem mono {A B : α → Prop} (hA : S.M A) (hB : S.M B) (h : ∀ x, A x → B x) : m.μ A ≤ m.μ B := by
  have e := m.split hA hB
  have : m.μ (fun x => B x ∧ A x) = m.μ A := m.congr fun x => ⟨fun h => h.2, fun hx => ⟨h x hx, hx⟩⟩
  have := m.nonneg _ (S.diff hB hA)
  grind

/-- **Subtraction.** For `A ⊆ B`, `μ(B ∖ A) = μ B − μ A`. -/
theorem diff {A B : α → Prop} (hA : S.M A) (hB : S.M B) (h : ∀ x, A x → B x) :
    m.μ (fun x => B x ∧ ¬ A x) = m.μ B - m.μ A := by
  have e := m.split hA hB
  have : m.μ (fun x => B x ∧ A x) = m.μ A := m.congr fun x => ⟨fun h => h.2, fun hx => ⟨h x hx, hx⟩⟩
  grind

/-- Every measurable set has measure at most `μ(α)`. -/
theorem le_univ {A : α → Prop} (hA : S.M A) : m.μ A ≤ m.μ (fun _ => True) :=
  m.mono hA S.univ fun _ _ => trivial

/-- Subadditivity for two sets: `μ(A ∪ B) ≤ μ A + μ B`. -/
theorem union_le {A B : α → Prop} (hA : S.M A) (hB : S.M B) :
    m.μ (fun x => A x ∨ B x) ≤ m.μ A + m.μ B := by
  have e : m.μ (fun x => A x ∨ B x) = m.μ A + m.μ (fun x => B x ∧ ¬ A x) := by
    rw [← m.union hA (S.diff hB hA) (fun x h1 h2 => h2.2 h1)]
    exact m.congr fun x => by by_cases a : A x <;> simp [a]
  have := m.mono (S.diff hB hA) hB fun x h => h.1
  grind

/-- The "rings" `D 0 = A 0`, `D (n+1) = A (n+1) ∖ A n` of an increasing sequence. -/
def rings {α : Type} (A : Nat → α → Prop) : Nat → α → Prop
  | 0 => A 0
  | n + 1 => fun x => A (n + 1) x ∧ ¬ A n x

/-- Transfer a limit along an index shift by one. -/
theorem tendsto_of_shift1 {a b : Nat → R} {L : R} (h : Tendsto (fun n => a (1 + n)) L)
    (e : ∀ n, a (n + 1) = b n) : Tendsto b L := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by rw [← e, Nat.add_comm]; exact hN n hn⟩

/-- **Continuity from below.** If `A₀ ⊆ A₁ ⊆ ⋯` are measurable, then `μ(Aₙ) → μ(⋃ Aₙ)`. -/
theorem tendsto_iUnion {A : Nat → α → Prop} (hA : ∀ n, S.M (A n))
    (hmono : ∀ n x, A n x → A (n + 1) x) :
    Tendsto (fun n => m.μ (A n)) (m.μ (fun x => ∃ n, A n x)) := by
  have hle : ∀ {i j}, i ≤ j → ∀ x, A i x → A j x := fun {i j} hij x hx => by
    obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
    induction k with
    | zero => exact hx
    | succ k ih => exact hmono _ x (ih (by omega))
  have hD : ∀ n, S.M (rings A n) := fun n => match n with
    | 0 => hA 0
    | n + 1 => S.diff (hA (n + 1)) (hA n)
  have hdisj : ∀ i j, i ≠ j → ∀ x, rings A i x → rings A j x → False := by
    have key : ∀ i j, i < j → ∀ x, rings A i x → rings A j x → False := by
      intro i j hij x hi hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have : A i x := by cases i with | zero => exact hi | succ i => exact hi.1
      exact hj.2 (hle (by omega) x this)
    intro i j hij x hi hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact key i j h x hi hj
    · exact key j i h x hj hi
  have hU : (fun x => ∃ n, rings A n x) = (fun x => ∃ n, A n x) := set_ext fun x => by
    constructor
    · rintro ⟨n, hn⟩; cases n with | zero => exact ⟨0, hn⟩ | succ n => exact ⟨n + 1, hn.1⟩
    · rintro ⟨n, hn⟩
      induction n with
      | zero => exact ⟨0, hn⟩
      | succ n ih => by_cases h : A n x
                     · exact ih h
                     · exact ⟨n + 1, hn, h⟩
  have hsum := m.additive _ hD hdisj
  rw [hU] at hsum
  have hpart : ∀ n, fsum (fun k => m.μ (rings A k)) (n + 1) = m.μ (A n) := by
    intro n
    induction n with
    | zero => show 0 + m.μ (A 0) = _; grind
    | succ n ih =>
      rw [fsum_succ, ih]
      have := m.diff (hA n) (hA (n + 1)) (hmono n)
      show m.μ (A n) + m.μ (fun x => A (n + 1) x ∧ ¬ A n x) = _
      grind
  exact tendsto_of_shift1 (hsum.shift 1) hpart

/-- **Continuity from above.** If `A₀ ⊇ A₁ ⊇ ⋯` are measurable, then `μ(Aₙ) → μ(⋂ Aₙ)`.
(For infinite measures this needs `μ(A₀) < ∞`; ours are finite.) -/
theorem tendsto_iInter {A : Nat → α → Prop} (hA : ∀ n, S.M (A n))
    (hmono : ∀ n x, A (n + 1) x → A n x) :
    Tendsto (fun n => m.μ (A n)) (m.μ (fun x => ∀ n, A n x)) := by
  have h := m.tendsto_iUnion (A := fun n x => ¬ A n x) (fun n => S.compl _ (hA n))
    fun n x h1 h2 => h1 (hmono n x h2)
  have hc : ∀ B : α → Prop, S.M B → m.μ (fun x => ¬ B x) = m.μ (fun _ => True) - m.μ B :=
    fun B hB => by
      rw [← m.diff hB S.univ (fun _ _ => trivial)]; exact m.congr fun x => by simp
  have e1 : (fun x => ∃ n, ¬ A n x) = (fun x => ¬ ∀ n, A n x) := set_ext fun x =>
    ⟨fun ⟨n, hn⟩ h => hn (h n), fun h => Classical.byContradiction fun h' =>
      h fun n => Classical.byContradiction fun hn => h' ⟨n, hn⟩⟩
  rw [e1, hc _ (S.iInter _ hA)] at h
  have e2 : (fun n => m.μ (fun x => ¬ A n x)) = fun n => m.μ (fun _ => True) - m.μ (A n) :=
    funext fun n => hc _ (hA n)
  rw [e2] at h
  have := (tendsto_const (m.μ fun _ => True)).sub h
  have e3 : (fun n => m.μ (fun _ => True) - (m.μ (fun _ => True) - m.μ (A n))) =
      fun n => m.μ (A n) := funext fun n => by grind
  rw [e3, show ∀ u v : R, u - (u - v) = v from fun u v => by grind] at this
  exact this

/-- Restriction of a measure to a smaller σ-algebra. -/
def restrict {S' : SigmaAlgebra α} (h : ∀ A, S'.M A → S.M A) : Measure S' where
  μ := m.μ
  nonneg A hA := m.nonneg A (h A hA)
  empty := m.empty
  additive A hA hd := m.additive A (fun n => h _ (hA n)) hd

end Measure

end MeasureTheory

end Foundations.Topology
