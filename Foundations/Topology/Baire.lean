import Foundations.Topology.Vitali

/-!
# The Baire category theorem

René **Baire** (1899) proved that the real line is not "thin": it cannot be written as a
countable union of *nowhere dense* sets (sets whose closure contains no interval). In the form
that became one of the pillars of functional analysis (Banach, Steinhaus):

  **In a complete metric space, a countable intersection of dense open sets is dense.**

The proof builds a nested sequence of closed balls, the `(n+1)`-st inside the `n`-th dense open
set and of radius `≤ 1/(n+1)`; their centres form a Cauchy sequence, and completeness supplies the
limit point, which lies in every set.

Corollaries: `ℝ` is not a countable union of closed nowhere dense sets; in particular (taking
singletons) **ℝ is uncountable** — our third proof, after Cantor's nested intervals
(`Numbers/Uncountable`) and the diagonal-style argument there; this one uses only completeness.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

variable {X : Type} [MetricSpace X]

/-- A set is **dense** if it meets every ball. -/
def Dense (D : X → Prop) : Prop := ∀ x, ∀ ε : R, 0 < ε → ∃ y, D y ∧ dist x y < ε

/-- One step of the construction: inside a ball `B(c, r)` and a dense open `U`, a smaller closed
ball `B̄(c', r')` with `r' ≤ 1/(n+1)` fits inside both. -/
theorem baire_step {U : X → Prop} (hU : IsOpen U) (hD : Dense U) (n : Nat) (c : X) {r : R}
    (hr : 0 < r) : ∃ c' : X, ∃ r' : R, 0 < r' ∧ r' ≤ 1 / ((n : R) + 1) ∧
      ∀ y, dist c' y ≤ r' → dist c y < r ∧ U y := by
  obtain ⟨c', hc'U, hcc'⟩ := hD c r hr
  obtain ⟨ε, hε, hball⟩ := hU c' hc'U
  obtain ⟨a, ha, ha1, ha2⟩ := exists_pos_le_both (by grind : 0 < ε / 2) (by grind : 0 < (r - dist c c') / 2)
  obtain ⟨r', hr', hr'1, hr'2⟩ := exists_pos_le_both ha (eps_pos n)
  exact ⟨c', r', hr', hr'2, fun y hy => ⟨by have := dist_triangle c c' y; grind,
    hball y (by grind)⟩⟩

/-- **Baire category theorem.** In a complete metric space, the intersection of countably many
dense open sets is dense. -/
theorem baire (hX : Complete X) {U : Nat → X → Prop} (hU : ∀ n, IsOpen (U n))
    (hD : ∀ n, Dense (U n)) : Dense (fun x => ∀ n, U n x) := by
  intro x ε hε
  -- The step function on "balls" `(c, r)` with `r > 0`.
  have hs : ∀ (n : Nat) (p : {p : X × R // 0 < p.2}), ∃ q : {p : X × R // 0 < p.2},
      q.1.2 ≤ 1 / ((n : R) + 1) ∧ ∀ y, dist q.1.1 y ≤ q.1.2 → dist p.1.1 y < p.1.2 ∧ U n y :=
    fun n p => by
      obtain ⟨c', r', h1, h2, h3⟩ := baire_step (hU n) (hD n) n p.1.1 p.2
      exact ⟨⟨(c', r'), h1⟩, h2, h3⟩
  let nxt : Nat → {p : X × R // 0 < p.2} → {p : X × R // 0 < p.2} := fun n p => (hs n p).choose
  have hnxt : ∀ n p, (nxt n p).1.2 ≤ 1 / ((n : R) + 1) ∧
      ∀ y, dist (nxt n p).1.1 y ≤ (nxt n p).1.2 → dist p.1.1 y < p.1.2 ∧ U n y :=
    fun n p => (hs n p).choose_spec
  let b : Nat → {p : X × R // 0 < p.2} := fun n =>
    Nat.rec (motive := fun _ => {p : X × R // 0 < p.2}) ⟨(x, ε), hε⟩ (fun k p => nxt k p) n
  have hb : ∀ n, b (n + 1) = nxt n (b n) := fun _ => rfl
  let c : Nat → X := fun n => (b n).1.1
  let r : Nat → R := fun n => (b n).1.2
  -- Closed balls are nested.
  have hnest1 : ∀ n y, dist (c (n + 1)) y ≤ r (n + 1) → dist (c n) y < r n ∧ U n y := fun n y h => by
    have := (hnxt n (b n)).2 y (by rw [← hb]; exact h); exact this
  have hnest : ∀ n j y, dist (c (n + j)) y ≤ r (n + j) → dist (c n) y ≤ r n := by
    intro n j
    induction j with
    | zero => intro y h; exact h
    | succ j ih => intro y h; exact ih y (Std.le_of_lt (hnest1 (n + j) y h).1)
  have hcin : ∀ n m, n ≤ m → dist (c n) (c m) ≤ r n := fun n m hnm => by
    obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
    exact hnest n j _ (by rw [dist_self]; exact Std.le_of_lt (b (n + j)).2)
  have hrsmall : ∀ n, r (n + 1) ≤ 1 / ((n : R) + 1) := fun n => by
    have := (hnxt n (b n)).1; rw [← hb] at this; exact this
  -- The centres form a Cauchy sequence.
  have hcauchy : IsCauchy c := fun δ hδ => by
    obtain ⟨N, hN⟩ := eps_small (by grind : (0 : R) < δ / 2)
    refine ⟨N + 1, fun m n hm hn => ?_⟩
    have k1 := hcin (N + 1) m hm
    have k2 := hcin (N + 1) n hn
    have k3 := hrsmall N
    have k4 := hN N (Nat.le_refl N)
    have := dist_triangle (c m) (c (N + 1)) (c n)
    have := dist_comm (c m) (c (N + 1))
    grind
  obtain ⟨L, hL⟩ := hX c hcauchy
  -- The limit lies in every closed ball.
  have hLin : ∀ n, dist (c n) L ≤ r n := fun n => by
    apply Classical.byContradiction; intro hlt
    obtain ⟨M, hM⟩ := hL (dist (c n) L - r n) (by grind)
    have k1 := hcin n (max n M) (by omega)
    have k2 := hM (max n M) (by omega)
    have := dist_triangle (c n) (c (max n M)) L
    grind
  refine ⟨L, fun n => (hnest1 n L (hLin (n + 1))).2, ?_⟩
  have := (hnest1 0 L (hLin 1)).1
  exact this

/-- A set is **nowhere dense and closed**: closed, and containing no ball. -/
def NowhereDenseClosed (F : X → Prop) : Prop :=
  IsClosed F ∧ ∀ x, ∀ ε : R, 0 < ε → ∃ y, dist x y < ε ∧ ¬ F y

/-- **Baire, second form.** A non-empty complete metric space is not a countable union of
closed nowhere dense sets. -/
theorem not_countable_union_nowhereDense (hX : Complete X) (x₀ : X) {F : Nat → X → Prop}
    (hF : ∀ n, NowhereDenseClosed (F n)) : ¬ ∀ x, ∃ n, F n x := by
  intro hcov
  obtain ⟨y, hy, -⟩ := baire hX (U := fun n x => ¬ F n x) (fun n => (hF n).1)
    (fun n x ε hε => by obtain ⟨y, h1, h2⟩ := (hF n).2 x ε hε; exact ⟨y, h2, h1⟩) x₀ 1 (by grind)
  obtain ⟨n, hn⟩ := hcov y
  exact hy n hn

/-- **ℝ is not a countable union of closed nowhere dense sets.** -/
theorem real_not_meagre {F : Nat → R → Prop} (hF : ∀ n, NowhereDenseClosed (F n)) :
    ¬ ∀ x, ∃ n, F n x :=
  not_countable_union_nowhereDense complete_R 0 hF

/-- **ℝ is uncountable** (third proof, via Baire): no sequence `s` lists all real numbers. -/
theorem real_uncountable_baire (s : Nat → R) : ∃ x, ∀ n, x ≠ s n := by
  apply Classical.byContradiction; intro h
  apply real_not_meagre (F := fun n x => x = s n)
  · intro n
    refine ⟨fun x hx => ⟨abs (x - s n), ?_, fun y hy h' => ?_⟩, fun x ε hε => ?_⟩
    · rcases abs_cases (x - s n) with h | h <;> grind
    · rw [h'] at hy; have : dist x (s n) = abs (x - s n) := rfl; grind
    · by_cases hx : x = s n
      · exact ⟨x + ε / 2, by
          show abs (x - (x + ε / 2)) < ε
          rw [show x - (x + ε / 2) = -(ε / 2) by grind, R.abs_neg, abs_of_nonneg (by grind)]; grind,
          by grind⟩
      · exact ⟨x, by rw [dist_self]; exact hε, hx⟩
  · intro x
    apply Classical.byContradiction; intro hx
    exact h ⟨x, fun n e => hx ⟨n, e⟩⟩

end Foundations.Topology
