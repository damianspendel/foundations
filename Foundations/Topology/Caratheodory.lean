import Foundations.Topology.SigmaAlgebra

/-!
# Carathéodory's criterion

Lebesgue (1902) defined the measure of a set `E ⊆ [a, b]` by squeezing it between its *outer*
measure `m*(E)` (covers by intervals) and its *inner* measure `(b − a) − m*([a, b] ∖ E)`, and
called `E` measurable when the two agree. Constantin **Carathéodory** (*Vorlesungen über reelle
Funktionen*, 1914) found the definition that works for every outer measure on every set: `E` is
**measurable** when it splits every "test set" `T` additively,

  `ν(T) = ν(T ∩ E) + ν(T ∖ E)`.

The criterion looks innocent, but it carries the whole construction:

**Carathéodory's theorem.** For any outer measure `ν`, the measurable sets form a σ-algebra and
`ν`, restricted to them, is countably additive.

An outer measure need only be monotone and countably *sub*additive. It is a philosophically
pleasing division of labour: the outer measure is defined on *every* set but is only
subadditive; Carathéodory's test singles out the sets on which it behaves like an honest measure.
Vitali's theorem says that there must be sets that fail the test.

As in `SigmaAlgebra`, our outer measures are **finite** (values in `R`); the Lebesgue outer
measure will be used through its restrictions `A ↦ m*(A ∩ [a, b])`.

At the end of the file we prove the **countable subadditivity of Lebesgue outer measure**,
left open in `OuterMeasure.lean`: by the classical `ε/2ⁿ` argument, covers of the pieces `Aₙ` are
merged into one cover of `⋃ Aₙ`. The merging uses the diagonal enumeration of `ℕ × ℕ`, and a
small lemma: an injectively indexed finite sum of non-negative terms is bounded by the sum over a
square containing the indices.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace MeasureTheory

/-! ## Outer measures -/

/-- **Outer measure.** (Finite.) Defined on all sets, non-negative, `ν ∅ = 0`, monotone and
countably subadditive: if `Σ ν(Aₙ)` converges to `s`, then `ν(⋃ Aₙ) ≤ s`. -/
structure OuterMeasure (α : Type) where
  /-- The outer measure of a set. -/
  ν : (α → Prop) → R
  /-- Non-negativity. -/
  nonneg : ∀ A, 0 ≤ ν A
  /-- The empty set has outer measure `0`. -/
  empty : ν (fun _ => False) = 0
  /-- Monotonicity. -/
  mono : ∀ A B : α → Prop, (∀ x, A x → B x) → ν A ≤ ν B
  /-- Countable subadditivity. -/
  subadd : ∀ (A : Nat → α → Prop) (s : R), HasSum (fun n => ν (A n)) s →
    ν (fun x => ∃ n, A n x) ≤ s

namespace OuterMeasure

variable {α : Type} (o : OuterMeasure α)

/-- Outer measure respects equality of sets. -/
theorem congr {A B : α → Prop} (h : ∀ x, A x ↔ B x) : o.ν A = o.ν B := by rw [set_ext h]

/-- Subadditivity for two sets. -/
theorem union_le (A B : α → Prop) : o.ν (fun x => A x ∨ B x) ≤ o.ν A + o.ν B := by
  have h := o.subadd (SigmaAlgebra.seq2 A B) (fsum (fun n => o.ν (SigmaAlgebra.seq2 A B n)) 2)
    (Vitali.InvariantMeasure.hasSum_of_zero fun k hk => by
      match k, hk with
      | _ + 2, _ => exact o.empty)
  rw [SigmaAlgebra.iUnion_seq2] at h
  have : fsum (fun n => o.ν (SigmaAlgebra.seq2 A B n)) 2 = 0 + o.ν A + o.ν B := rfl
  grind

/-- **Carathéodory measurability.** `E` splits every test set additively. -/
def IsMeasurable (E : α → Prop) : Prop :=
  ∀ T : α → Prop, o.ν T = o.ν (fun x => T x ∧ E x) + o.ν (fun x => T x ∧ ¬ E x)

/-- Only one inequality needs checking; the other is subadditivity. -/
theorem isMeasurable_of_le {E : α → Prop}
    (h : ∀ T, o.ν (fun x => T x ∧ E x) + o.ν (fun x => T x ∧ ¬ E x) ≤ o.ν T) : o.IsMeasurable E :=
  fun T => by
    have := o.union_le (fun x => T x ∧ E x) (fun x => T x ∧ ¬ E x)
    have e : o.ν (fun x => (T x ∧ E x) ∨ (T x ∧ ¬ E x)) = o.ν T :=
      o.congr fun x => by by_cases e : E x <;> simp [e]
    have := h T
    grind

/-- Measurability respects equality of sets. -/
theorem IsMeasurable.congr {o : OuterMeasure α} {E F : α → Prop} (hE : o.IsMeasurable E)
    (h : ∀ x, E x ↔ F x) : o.IsMeasurable F := by rwa [← set_ext h]

/-- `∅` is measurable. -/
theorem isMeasurable_empty : o.IsMeasurable (fun _ => False) := fun T => by
  rw [o.congr (A := fun x => T x ∧ False) (B := fun _ => False) (by simp), o.empty,
    o.congr (A := fun x => T x ∧ ¬ False) (B := T) (by simp)]; grind

/-- Complements of measurable sets are measurable. -/
theorem IsMeasurable.compl {o : OuterMeasure α} {E : α → Prop} (hE : o.IsMeasurable E) :
    o.IsMeasurable (fun x => ¬ E x) := fun T => by
  rw [hE T, o.congr (A := fun x => T x ∧ ¬ ¬ E x) (B := fun x => T x ∧ E x)
    (fun x => by by_cases e : E x <;> simp [e])]; grind

/-- Finite unions of measurable sets are measurable. -/
theorem IsMeasurable.union {o : OuterMeasure α} {E F : α → Prop} (hE : o.IsMeasurable E)
    (hF : o.IsMeasurable F) : o.IsMeasurable (fun x => E x ∨ F x) := o.isMeasurable_of_le fun T => by
  have h1 := hE T
  have h2 := hF (fun x => T x ∧ ¬ E x)
  have h3 := o.union_le (fun x => T x ∧ E x) (fun x => (T x ∧ ¬ E x) ∧ F x)
  rw [o.congr (A := fun x => (T x ∧ E x) ∨ ((T x ∧ ¬ E x) ∧ F x))
    (B := fun x => T x ∧ (E x ∨ F x)) (fun x => by by_cases e : E x <;> simp [e])] at h3
  rw [o.congr (A := fun x => (T x ∧ ¬ E x) ∧ ¬ F x) (B := fun x => T x ∧ ¬ (E x ∨ F x))
    (fun x => by by_cases e : E x <;> simp [e])] at h2
  grind

/-- Intersections of two measurable sets are measurable. -/
theorem IsMeasurable.inter {o : OuterMeasure α} {E F : α → Prop} (hE : o.IsMeasurable E)
    (hF : o.IsMeasurable F) : o.IsMeasurable (fun x => E x ∧ F x) :=
  (hE.compl.union hF.compl).compl.congr fun x => by by_cases e : E x <;> simp [e]

/-- The finite union `E 0 ∪ ⋯ ∪ E (n−1)`. -/
def partialUnion (E : Nat → α → Prop) (n : Nat) (x : α) : Prop := ∃ k, k < n ∧ E k x

/-- Finite unions of measurable sets are measurable. -/
theorem isMeasurable_partialUnion {E : Nat → α → Prop} (hE : ∀ n, o.IsMeasurable (E n)) :
    ∀ n, o.IsMeasurable (partialUnion E n)
  | 0 => o.isMeasurable_empty.congr fun x => ⟨False.elim, fun ⟨k, hk, _⟩ => by omega⟩
  | n + 1 => ((isMeasurable_partialUnion hE n).union (hE n)).congr fun x =>
      ⟨fun h => h.elim (fun ⟨k, hk, h⟩ => ⟨k, by omega, h⟩) (fun h => ⟨n, by omega, h⟩),
        fun ⟨k, hk, h⟩ => if e : k = n then Or.inr (e ▸ h) else Or.inl ⟨k, by omega, h⟩⟩

/-- Pairwise disjointness of a sequence of sets. -/
def Disjoint (E : Nat → α → Prop) : Prop := ∀ i j, i ≠ j → ∀ x, E i x → E j x → False

/-- **The key estimate.** For disjoint measurable `Eₙ` with union `U` and any test set `T`:
the series `Σ ν(T ∩ Eₙ)` converges to some `s` with `s + ν(T ∖ U) ≤ ν(T)` and `ν(T ∩ U) ≤ s`. -/
theorem disjoint_estimate {E : Nat → α → Prop} (hE : ∀ n, o.IsMeasurable (E n)) (hd : Disjoint E)
    (T : α → Prop) : ∃ s, HasSum (fun n => o.ν (fun x => T x ∧ E n x)) s ∧
      s + o.ν (fun x => T x ∧ ¬ ∃ n, E n x) ≤ o.ν T ∧ o.ν (fun x => T x ∧ ∃ n, E n x) ≤ s := by
  -- `ν(T ∩ (E₀ ∪ ⋯ ∪ Eₙ₋₁)) = Σ_{k<n} ν(T ∩ Eₖ)`.
  have hfin : ∀ n, o.ν (fun x => T x ∧ partialUnion E n x) =
      fsum (fun k => o.ν (fun x => T x ∧ E k x)) n := by
    intro n
    induction n with
    | zero => rw [fsum_zero, ← o.empty]; exact o.congr fun x => ⟨fun ⟨_, k, hk, _⟩ => by omega,
        False.elim⟩
    | succ n ih =>
      rw [fsum_succ, ← ih, hE n (fun x => T x ∧ partialUnion E (n + 1) x)]
      rw [o.congr (A := fun x => (T x ∧ partialUnion E (n + 1) x) ∧ E n x)
        (B := fun x => T x ∧ E n x) (fun x => ⟨fun h => ⟨h.1.1, h.2⟩,
          fun h => ⟨⟨h.1, n, by omega, h.2⟩, h.2⟩⟩)]
      rw [o.congr (A := fun x => (T x ∧ partialUnion E (n + 1) x) ∧ ¬ E n x)
        (B := fun x => T x ∧ partialUnion E n x) (fun x => ⟨fun ⟨⟨h1, k, hk, h2⟩, h3⟩ =>
          ⟨h1, k, by
            rcases Nat.lt_or_ge k n with h | h
            · exact h
            · exact absurd (show k = n by omega ▸ h2) h3, h2⟩,
          fun ⟨h1, k, hk, h2⟩ => ⟨⟨h1, k, by omega, h2⟩, fun h3 => hd k n (by omega) x h2 h3⟩⟩)]
      grind
  -- The partial sums are bounded by `ν(T) − ν(T ∖ U)`.
  have hbd : ∀ n, fsum (fun k => o.ν (fun x => T x ∧ E k x)) n ≤
      o.ν T - o.ν (fun x => T x ∧ ¬ ∃ n, E n x) := by
    intro n
    have h1 := isMeasurable_partialUnion o hE n T
    have h2 := o.mono (fun x => T x ∧ ¬ ∃ n, E n x) (fun x => T x ∧ ¬ partialUnion E n x)
      fun x ⟨h1, h2⟩ => ⟨h1, fun ⟨k, _, hk⟩ => h2 ⟨k, hk⟩⟩
    rw [hfin n] at h1; grind
  obtain ⟨s, hs, hsle⟩ := summable_of_bounded (fun n => o.nonneg _) hbd
  refine ⟨s, hs, by grind, ?_⟩
  have := o.subadd (fun n x => T x ∧ E n x) s hs
  rwa [o.congr (A := fun x => ∃ n, T x ∧ E n x) (B := fun x => T x ∧ ∃ n, E n x)
    (fun x => ⟨fun ⟨n, h1, h2⟩ => ⟨h1, n, h2⟩, fun ⟨h1, n, h2⟩ => ⟨n, h1, h2⟩⟩)] at this

/-- Disjoint countable unions of measurable sets are measurable. -/
theorem isMeasurable_iUnion_disjoint {E : Nat → α → Prop} (hE : ∀ n, o.IsMeasurable (E n))
    (hd : Disjoint E) : o.IsMeasurable (fun x => ∃ n, E n x) := o.isMeasurable_of_le fun T => by
  obtain ⟨s, _, h1, h2⟩ := o.disjoint_estimate hE hd T; grind

/-- Countable unions of measurable sets are measurable (make them disjoint first:
`Dₙ = Eₙ ∖ (E₀ ∪ ⋯ ∪ Eₙ₋₁)`). -/
theorem isMeasurable_iUnion {E : Nat → α → Prop} (hE : ∀ n, o.IsMeasurable (E n)) :
    o.IsMeasurable (fun x => ∃ n, E n x) := by
  have hD : ∀ n, o.IsMeasurable (fun x => E n x ∧ ¬ partialUnion E n x) :=
    fun n => (hE n).inter (o.isMeasurable_partialUnion hE n).compl
  refine (o.isMeasurable_iUnion_disjoint hD ?_).congr fun x => ⟨fun ⟨n, h, _⟩ => ⟨n, h⟩, ?_⟩
  · intro i j hij x ⟨hi, hi'⟩ ⟨hj, hj'⟩
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hj' ⟨i, h, hi⟩
    · exact hi' ⟨j, h, hj⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk, hmin⟩ := nat_least (fun j => E j x) ⟨n, hn⟩
    exact ⟨k, hk, fun ⟨j, hj, h⟩ => hmin j hj h⟩

/-- **Carathéodory's theorem, part 1.** The measurable sets form a σ-algebra. -/
def sigma : SigmaAlgebra α where
  M := o.IsMeasurable
  empty := o.isMeasurable_empty
  compl _ h := h.compl
  iUnion _ h := o.isMeasurable_iUnion h

/-- **Carathéodory's theorem, part 2.** The outer measure is countably additive on the
measurable sets — it is a measure. -/
def measure : Measure o.sigma where
  μ := o.ν
  nonneg A _ := o.nonneg A
  empty := o.empty
  additive E hE hd := by
    obtain ⟨s, hs, h1, h2⟩ := o.disjoint_estimate hE hd (fun x => ∃ n, E n x)
    have e1 : (fun n => o.ν (fun x => (∃ n, E n x) ∧ E n x)) = fun n => o.ν (E n) :=
      funext fun n => o.congr fun x => ⟨fun h => h.2, fun h => ⟨⟨n, h⟩, h⟩⟩
    rw [e1] at hs
    have e2 : o.ν (fun x => (∃ n, E n x) ∧ ¬ ∃ n, E n x) = 0 := by
      rw [← o.empty]; exact o.congr fun x => ⟨fun h => h.2 h.1, False.elim⟩
    have e3 : o.ν (fun x => (∃ n, E n x) ∧ ∃ n, E n x) = o.ν (fun x => ∃ n, E n x) :=
      o.congr fun x => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
    rw [e2] at h1; rw [e3] at h2
    have : s = o.ν (fun x => ∃ n, E n x) := by grind
    rwa [this] at hs

/-- **Carathéodory's criterion (1914).** In summary: every outer measure `ν` restricts to a
countably additive measure on the σ-algebra of Carathéodory-measurable sets. -/
theorem caratheodory : (∀ A, o.sigma.M A ↔ o.IsMeasurable A) ∧ ∀ A, o.measure.μ A = o.ν A :=
  ⟨fun _ => Iff.rfl, fun _ => rfl⟩

end OuterMeasure

/-! ## Double series of non-negative terms -/

/-- The sum over the square `[0, M) × [0, M)`. -/
def sq (F : Nat → Nat → R) (M : Nat) : R := fsum (fun i => fsum (F i) M) M

/-- A single spike: `Σ_{j<M} [j = q] c = c` if `q < M`. -/
theorem fsum_spike (c : R) (q : Nat) : ∀ M, q < M → fsum (fun j => if j = q then c else 0) M = c
  | 0, h => by omega
  | M + 1, h => by
    rw [fsum_succ]
    by_cases e : M = q
    · subst e
      have : fsum (fun j => if j = M then c else 0) M = 0 := by
        have := fsum_congr (n := M) (a := fun j => if j = M then c else 0) (b := fun _ => 0)
          fun k hk => by simp; omega
        rw [this]; clear this
        induction M with
        | zero => rfl
        | succ M ih => rw [fsum_succ, ih (by omega)]; grind
      rw [this, Outer.ite_pos' rfl]; grind
    · rw [fsum_spike c q M (by omega), Outer.ite_neg' e]; grind

/-- Removing one entry `p` from a square sum. -/
theorem sq_remove (F : Nat → Nat → R) {p : Nat × Nat} {M : Nat} (h1 : p.1 < M) (h2 : p.2 < M) :
    sq F M = sq (fun i j => if i = p.1 ∧ j = p.2 then 0 else F i j) M + F p.1 p.2 := by
  unfold sq
  have e : ∀ i, fsum (F i) M = fsum (fun j => if i = p.1 ∧ j = p.2 then 0 else F i j) M +
      (if i = p.1 then F p.1 p.2 else 0) := by
    intro i
    by_cases hi : i = p.1
    · rw [Outer.ite_pos' hi, ← fsum_spike (F p.1 p.2) p.2 M h2, ← fsum_add]
      exact fsum_congr fun j _ => by by_cases hj : j = p.2 <;> simp [hj, hi] <;> grind
    · rw [Outer.ite_neg' hi]
      have : fsum (fun j => if i = p.1 ∧ j = p.2 then 0 else F i j) M = fsum (F i) M :=
        fsum_congr fun j _ => by simp [hi]
      rw [this]; grind
  rw [fsum_congr (n := M) (b := fun i => fsum (fun j => if i = p.1 ∧ j = p.2 then 0 else F i j) M +
      (if i = p.1 then F p.1 p.2 else 0)) fun i _ => e i, fsum_add, fsum_spike _ _ M h1]

/-- **Injective sums are bounded by square sums.** If `e` is injective and the first `N` values
of `e` lie in `[0, M)²`, then `Σ_{k<N} F(e k) ≤ Σ_{[0,M)²} F` for non-negative `F`. -/
theorem fsum_inj_le_sq {e : Nat → Nat × Nat} (he : ∀ k l, e k = e l → k = l) :
    ∀ (N : Nat) (F : Nat → Nat → R) (M : Nat), (∀ i j, 0 ≤ F i j) →
      (∀ k, k < N → (e k).1 < M ∧ (e k).2 < M) →
      fsum (fun k => F (e k).1 (e k).2) N ≤ sq F M := by
  intro N
  induction N with
  | zero =>
    intro F M hF _
    exact fsum_nonneg (fun i => fsum_nonneg (hF i) M) M
  | succ N ih =>
    intro F M hF hM
    obtain ⟨b1, b2⟩ := hM N (by omega)
    rw [sq_remove F b1 b2, fsum_succ]
    have := ih (fun i j => if i = (e N).1 ∧ j = (e N).2 then 0 else F i j) M
      (fun i j => by split <;> grind [hF i j]) fun k hk => hM k (by omega)
    have eq : fsum (fun k => (fun i j => if i = (e N).1 ∧ j = (e N).2 then 0 else F i j)
        (e k).1 (e k).2) N = fsum (fun k => F (e k).1 (e k).2) N :=
      fsum_congr fun k hk => by
        have : ¬ ((e k).1 = (e N).1 ∧ (e k).2 = (e N).2) := fun ⟨a, b⟩ =>
          absurd (he k N (Prod.ext a b)) (by omega)
        simp only [this]; simp
    grind

/-- **Merging countably many series.** If `Σⱼ F i j = t i` for every `i` and `Σᵢ t i = T`,
with `F ≥ 0`, then the series `Σₖ F(pairEnum k)` converges to some `S ≤ T`. -/
theorem merge_hasSum {F : Nat → Nat → R} (hF : ∀ i j, 0 ≤ F i j) {t : Nat → R}
    (ht : ∀ i, HasSum (F i) (t i)) {T : R} (hT : HasSum t T) :
    ∃ S, HasSum (fun k => F (pairEnum k).1 (pairEnum k).2) S ∧ S ≤ T := by
  have htn : ∀ i, 0 ≤ t i := fun i => hasSum_nonneg (hF i) (ht i)
  apply summable_of_bounded (fun k => hF _ _)
  intro N
  -- A bound `M` for all indices of the first `N` terms.
  have hM : ∃ M, ∀ k, k < N → (pairEnum k).1 < M ∧ (pairEnum k).2 < M := by
    induction N with
    | zero => exact ⟨0, fun k hk => by omega⟩
    | succ N ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨M + (pairEnum N).1 + (pairEnum N).2 + 1, fun k hk => ?_⟩
      by_cases e : k = N
      · subst e; omega
      · have := hM k (by omega); omega
  obtain ⟨M, hM⟩ := hM
  have h1 := fsum_inj_le_sq (fun k l h => pairEnum_inj h) N F M hF hM
  have h2 : sq F M ≤ fsum t M := fsum_le_fsum (fun i => fsum_le_of_hasSum (hF i) (ht i) M) M
  have h3 := fsum_le_of_hasSum htn hT M
  grind

/-! ## Countable subadditivity of Lebesgue outer measure -/

open Outer

/-- `A` admits a countable cover by open intervals of finite total length. -/
def Coverable (A : R → Prop) : Prop := ∃ s, CoverSum A s

/-- A cover of `B` is a cover of any subset of `B`. -/
theorem CoverSum.mono {A B : R → Prop} {s : R} (h : CoverSum B s) (hAB : ∀ x, A x → B x) :
    CoverSum A s := by
  obtain ⟨lo, hi, h1, h2, h3⟩ := h
  exact ⟨lo, hi, h1, fun x hx => h2 x (hAB x hx), h3⟩

/-- **The outer measure is a lower bound.** It bounds the lengths of all covers from below. -/
theorem outer_le {A : R → Prop} {s : R} (h : CoverSum A s) : outer A ≤ s := by
  have hex : ∃ s, CoverSum A s := ⟨s, h⟩
  unfold outer
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have := (Classical.choose_spec (exists_lub _ (outer_ne hex) (outer_bdd A))).1 (-s)
    (by rw [show - -s = s by grind]; exact h)
  grind

/-- **The outer measure is the greatest lower bound.** There are covers of length
`< m*(A) + ε`. -/
theorem outer_approx {A : R → Prop} (hA : Coverable A) {ε : R} (hε : 0 < ε) :
    ∃ s, CoverSum A s ∧ s < outer A + ε := by
  apply Classical.byContradiction; intro hno
  unfold outer at hno
  rw [dite_eq_left_of_eq_true (eq_true (show ∃ s, CoverSum A s from hA))] at hno
  have hspec := Classical.choose_spec (exists_lub _ (outer_ne hA) (outer_bdd A))
  generalize Classical.choose (exists_lub _ (outer_ne hA) (outer_bdd A)) = L at hspec hno
  have := hspec.2 (L - ε) fun t ht => by
    apply Classical.byContradiction; intro h; exact hno ⟨-t, ht, by grind⟩
  grind

/-- The outer measure is non-negative. -/
theorem outer_nonneg (A : R → Prop) : 0 ≤ outer A := by
  unfold outer
  split
  · next h =>
    have := (Classical.choose_spec (exists_lub _ (outer_ne h) (outer_bdd A))).2 0
      fun t ⟨lo, hi, hlh, _, hs⟩ => by
        have := hasSum_nonneg (fun n => by have := hlh n; grind) hs; grind
    grind
  · exact Std.le_refl 0

/-- A real bounded by `y + ε` for every `ε > 0` is at most `y`. -/
theorem le_of_forall_eps {x y : R} (h : ∀ ε : R, 0 < ε → x ≤ y + ε) : x ≤ y := by
  apply Classical.byContradiction; intro hn
  have := h ((x - y) / 2) (by grind); grind

/-- **Comparison of outer measures.** If every cover of `B` is a cover of `A`, and `B` has one,
then `m*(A) ≤ m*(B)`. -/
theorem outer_le_outer {A B : R → Prop} (hB : Coverable B)
    (h : ∀ s, CoverSum B s → CoverSum A s) : outer A ≤ outer B :=
  le_of_forall_eps fun ε hε => by
    obtain ⟨s, hs, hlt⟩ := outer_approx hB hε
    have := outer_le (h s hs); grind

/-- Monotonicity of the outer measure (for coverable `B`). -/
theorem outer_mono {A B : R → Prop} (hB : Coverable B) (h : ∀ x, A x → B x) :
    outer A ≤ outer B := outer_le_outer hB fun _ hs => CoverSum.mono hs h

/-- Outer measure respects equality of sets. -/
theorem outer_congr {A B : R → Prop} (h : ∀ x, A x ↔ B x) : outer A = outer B := by
  rw [set_ext h]

/-- Bounded sets are coverable. -/
theorem coverable_of_bdd {A : R → Prop} {a b : R} (h : ∀ x, A x → a ≤ x ∧ x ≤ b) : Coverable A := by
  rcases (by grind : a ≤ b ∨ b < a) with hab | hab
  · exact ⟨_, CoverSum.mono (coverSum_le a b (ε := 1) (by grind) hab) h⟩
  · exact ⟨_, CoverSum.mono (coverSum_le a a (ε := 1) (by grind) (Std.le_refl a))
      fun x hx => by have := h x hx; grind⟩

/-- The empty set has outer measure `0`. -/
theorem outer_empty : outer (fun _ => False) = 0 := by
  have := outer_le (A := fun _ => False) ⟨fun _ => 0, fun _ => 0, fun _ => Std.le_refl 0,
    fun _ h => h.elim, (Vitali.InvariantMeasure.hasSum_of_zero (m := 0) fun _ _ => by grind).congr
      fun _ => rfl⟩
  have := outer_nonneg (fun _ => False)
  rw [fsum_zero] at *; grind

/-- `Σ ε/2ⁿ⁺¹ = ε`. -/
theorem hasSum_eps_geom (ε : R) : HasSum (fun n => ε * (1 / 2) ^ (n + 1)) ε := by
  have h := (hasSum_geometric (r := 1 / 2) (by rw [abs_of_nonneg (by grind)]; grind)).const_mul
    (ε / 2)
  rw [show ε / 2 * (1 / (1 - 1 / 2)) = ε by grind] at h
  exact h.congr fun n => by rw [Semiring.pow_succ]; grind

/-- `ε/2ⁿ⁺¹ > 0`. -/
theorem eps_geom_pos {ε : R} (hε : 0 < ε) (n : Nat) : 0 < ε * (1 / 2) ^ (n + 1) := by
  have : (0 : R) < (1 / 2) ^ (n + 1) := by
    induction n with
    | zero => rw [Semiring.pow_succ, Semiring.pow_zero]; grind
    | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih (by grind)
  exact OrderedRing.mul_pos hε this

/-- **Countable subadditivity of Lebesgue outer measure.** (Left open in `OuterMeasure.lean`.)
If each `Aₙ` is coverable and `Σ m*(Aₙ) = s`, then `⋃ Aₙ` is coverable and `m*(⋃ Aₙ) ≤ s`. -/
theorem outer_iUnion_le {A : Nat → R → Prop} (hA : ∀ n, Coverable (A n)) {s : R}
    (hs : HasSum (fun n => outer (A n)) s) :
    Coverable (fun x => ∃ n, A n x) ∧ outer (fun x => ∃ n, A n x) ≤ s := by
  -- For each `ε`, merge covers of the `Aₙ` of lengths `< m*(Aₙ) + ε/2ⁿ⁺¹`.
  have key : ∀ ε : R, 0 < ε → ∃ S, CoverSum (fun x => ∃ n, A n x) S ∧ S ≤ s + ε := by
    intro ε hε
    have hc : ∀ n, ∃ p : (Nat → R) × (Nat → R) × R, (∀ k, p.1 k ≤ p.2.1 k) ∧
        (∀ x, A n x → ∃ k, p.1 k < x ∧ x < p.2.1 k) ∧ HasSum (fun k => p.2.1 k - p.1 k) p.2.2 ∧
        p.2.2 < outer (A n) + ε * (1 / 2) ^ (n + 1) := fun n => by
      obtain ⟨t, ⟨lo, hi, h1, h2, h3⟩, ht⟩ := outer_approx (hA n) (eps_geom_pos hε n)
      exact ⟨(lo, hi, t), h1, h2, h3, ht⟩
    obtain ⟨P, hP⟩ := Classical.axiomOfChoice hc
    have hF : ∀ i j, 0 ≤ (P i).2.1 j - (P i).1 j := fun i j => by have := (hP i).1 j; grind
    obtain ⟨T, hT, hTle⟩ := comparison (fun n => hasSum_nonneg (hF n) (hP n).2.2.1)
      (fun n => Std.le_of_lt (hP n).2.2.2) (hs.add (hasSum_eps_geom ε))
    obtain ⟨S, hS, hSle⟩ := merge_hasSum hF (fun i => (hP i).2.2.1) hT
    refine ⟨S, ⟨fun k => (P (pairEnum k).1).1 (pairEnum k).2,
      fun k => (P (pairEnum k).1).2.1 (pairEnum k).2, fun k => (hP _).1 _, ?_, hS⟩, by grind⟩
    rintro x ⟨n, hn⟩
    obtain ⟨k, hk⟩ := (hP n).2.1 x hn
    exact ⟨pairIndex (n, k), by simp only [pairEnum_surj]; exact hk⟩
  obtain ⟨S, hS, _⟩ := key 1 (by grind)
  exact ⟨⟨S, hS⟩, le_of_forall_eps fun ε hε => by
    obtain ⟨S, hS, hle⟩ := key ε hε; have := outer_le hS; grind⟩

/-- Subadditivity of the outer measure for two coverable sets (and their union is coverable). -/
theorem outer_union_le' {A B : R → Prop} (hA : Coverable A) (hB : Coverable B) :
    Coverable (fun x => A x ∨ B x) ∧ outer (fun x => A x ∨ B x) ≤ outer A + outer B := by
  have h := outer_iUnion_le (A := SigmaAlgebra.seq2 A B)
    (fun n => match n with
      | 0 => hA
      | 1 => hB
      | _ + 2 => coverable_of_bdd (a := 0) (b := 0) fun _ h => h.elim)
    (Vitali.InvariantMeasure.hasSum_of_zero (m := 2) fun k hk => by
      match k, hk with
      | _ + 2, _ => exact outer_empty)
  rw [SigmaAlgebra.iUnion_seq2] at h
  have : fsum (fun n => outer (SigmaAlgebra.seq2 A B n)) 2 = 0 + outer A + outer B := rfl
  exact ⟨h.1, by grind⟩

/-- Subadditivity of the outer measure for two coverable sets. -/
theorem outer_union_le {A B : R → Prop} (hA : Coverable A) (hB : Coverable B) :
    outer (fun x => A x ∨ B x) ≤ outer A + outer B := (outer_union_le' hA hB).2

end MeasureTheory

end Foundations.Topology
