import Foundations.Topology.CantorSet

/-!
# Lebesgue outer measure of an interval

Vitali showed that length cannot be extended to *all* sets as a countably additive measure. What
*can* be defined for every set is Lebesgue's **outer measure** (1902):

  `m*(A) = inf { Σ (bₙ − aₙ) | the open intervals (aₙ, bₙ) cover A }`.

It is monotone and countably *sub*additive, and countably additive only on the measurable sets
(Carathéodory 1914). The first non-trivial fact — without which the theory would be empty — is
that it gives an interval its length:

  **`m*([a, b]) = b − a`.**

The inequality `≤` is easy (one slightly larger interval). The inequality `≥` says that countably
many open intervals covering `[a, b]` have total length `> b − a`; by the **Heine–Borel theorem**
finitely many of them already cover, and for finitely many intervals we argue by induction:
the interval containing `a` reaches some `d`, and the remaining ones must cover `[d, b]`. This is
exactly where compactness enters measure theory.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Outer

/-- Reduce an `if` with a true condition. -/
theorem ite_pos' {α : Type} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

/-- Reduce an `if` with a false condition. -/
theorem ite_neg' {α : Type} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- The sum `Σ_{k < N, P k} len k` over the indices satisfying `P`. -/
noncomputable def psum (len : Nat → R) (P : Nat → Prop) : Nat → R
  | 0 => 0
  | n + 1 => psum len P n + (open Classical in if P n then len n else 0)

/-- The number of indices `k < N` with `P k`. -/
noncomputable def pcnt (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => pcnt P n + (open Classical in if P n then 1 else 0)

/-- Sums of non-negative lengths are non-negative. -/
theorem psum_nonneg {len : Nat → R} (h : ∀ k, 0 ≤ len k) (P : Nat → Prop) (N : Nat) :
    0 ≤ psum len P N := by
  induction N with
  | zero => exact Std.le_refl 0
  | succ N ih => show 0 ≤ psum len P N + _; have := h N; split <;> grind

/-- A single selected term is at most the sum. -/
theorem le_psum {len : Nat → R} (h : ∀ k, 0 ≤ len k) {P : Nat → Prop} {j N : Nat} (hj : j < N)
    (hP : P j) : len j ≤ psum len P N := by
  induction N with
  | zero => omega
  | succ N ih =>
    show len j ≤ psum len P N + _
    have := psum_nonneg h P N
    by_cases e : j = N
    · subst e; rw [ite_pos' hP]; grind
    · have := ih (by omega); split <;> grind

/-- Removing the index `j` from the selection. -/
theorem psum_remove (len : Nat → R) {P : Nat → Prop} {j N : Nat} (hj : j < N) (hP : P j) :
    psum len P N = psum len (fun k => P k ∧ k ≠ j) N + len j ∧
      pcnt P N = pcnt (fun k => P k ∧ k ≠ j) N + 1 := by
  induction N with
  | zero => omega
  | succ N ih =>
    show psum len P N + _ = psum len _ N + _ + len j ∧ pcnt P N + _ = pcnt _ N + _ + 1
    dsimp only
    by_cases e : j = N
    · subst e
      have h0 : ∀ M, M ≤ j → psum len (fun k => P k ∧ k ≠ j) M = psum len P M ∧
          pcnt (fun k => P k ∧ k ≠ j) M = pcnt P M := by
        intro M hM
        induction M with
        | zero => exact ⟨rfl, rfl⟩
        | succ M ihM =>
          obtain ⟨a1, a2⟩ := ihM (by omega)
          show psum len _ M + _ = psum len P M + _ ∧ pcnt _ M + _ = pcnt P M + _
          dsimp only
          rw [a1, a2]
          by_cases hM' : P M
          · rw [ite_pos' ⟨hM', by omega⟩, ite_pos' hM', ite_pos' ⟨hM', by omega⟩, ite_pos' hM']
            exact ⟨rfl, rfl⟩
          · rw [ite_neg' (fun h => hM' h.1), ite_neg' hM', ite_neg' (fun h => hM' h.1), ite_neg' hM']
            exact ⟨rfl, rfl⟩
      obtain ⟨b1, b2⟩ := h0 j (Nat.le_refl j)
      rw [b1, b2, ite_pos' hP, ite_pos' hP, ite_neg' (fun h => h.2 rfl), ite_neg' (fun h => h.2 rfl)]
      constructor <;> grind
    · obtain ⟨a1, a2⟩ := ih (by omega)
      rw [a1, a2]
      by_cases hN : P N
      · rw [ite_pos' hN, ite_pos' ⟨hN, fun h => e h.symm⟩, ite_pos' hN, ite_pos' ⟨hN, fun h => e h.symm⟩]
        constructor <;> grind
      · rw [ite_neg' hN, ite_neg' (fun h => hN h.1), ite_neg' hN, ite_neg' (fun h => hN h.1)]
        constructor <;> grind

/-- Selecting every index gives the ordinary partial sum. -/
theorem psum_true (len : Nat → R) (N : Nat) : psum len (fun _ => True) N = fsum len N := by
  induction N with
  | zero => rfl
  | succ N ih => show psum len _ N + _ = _; dsimp only; rw [ih, ite_pos' trivial, fsum_succ]

/-- **Finitely many open intervals covering `[a, b]` have total length `> b − a`.** -/
theorem finite_cover {lo hi : Nat → R} (hlh : ∀ k, lo k ≤ hi k) (N : Nat) (b : R) :
    ∀ n (P : Nat → Prop) (a : R), pcnt P N ≤ n → a ≤ b →
      (∀ x, a ≤ x → x ≤ b → ∃ k, k < N ∧ P k ∧ lo k < x ∧ x < hi k) →
      b - a < psum (fun k => hi k - lo k) P N := by
  have hlen : ∀ k, 0 ≤ hi k - lo k := fun k => by have := hlh k; grind
  intro n
  induction n with
  | zero =>
    intro P a hc hab hcov
    obtain ⟨j, hj, hP, -, -⟩ := hcov a (Std.le_refl a) hab
    have := (psum_remove (fun k => hi k - lo k) hj hP).2; omega
  | succ n ih =>
    intro P a hc hab hcov
    obtain ⟨j, hj, hP, h1, h2⟩ := hcov a (Std.le_refl a) hab
    obtain ⟨r1, r2⟩ := psum_remove (fun k => hi k - lo k) hj hP
    rcases (by grind : b < hi j ∨ hi j ≤ b) with hb | hb
    · have := le_psum hlen hj hP; grind
    · have := ih (fun k => P k ∧ k ≠ j) (hi j) (by omega) hb fun x hx1 hx2 => by
        obtain ⟨k, hk, hPk, k1, k2⟩ := hcov x (by grind) hx2
        exact ⟨k, hk, ⟨hPk, fun e => by subst e; grind⟩, k1, k2⟩
      rw [r1]; grind

/-! ## The outer measure -/

/-- `s` is the total length of a countable cover of `A` by open intervals `(lo n, hi n)`. -/
def CoverSum (A : R → Prop) (s : R) : Prop :=
  ∃ lo hi : Nat → R, (∀ n, lo n ≤ hi n) ∧ (∀ x, A x → ∃ n, lo n < x ∧ x < hi n) ∧
    HasSum (fun n => hi n - lo n) s

/-- The maximum of a list of natural numbers dominates each element. -/
theorem le_max_list (l : List Nat) {k : Nat} (hk : k ∈ l) : k ≤ l.foldr max 0 := by
  have := le_foldr_max (fun k => k) l hk; exact this

/-- **Lower bound.** Every countable cover of `[a, b]` by open intervals has total length
`≥ b − a` (via Heine–Borel and `finite_cover`). -/
theorem coverSum_ge {a b s : R} (hab : a ≤ b) (h : CoverSum (fun x => a ≤ x ∧ x ≤ b) s) :
    b - a ≤ s := by
  obtain ⟨lo, hi, hlh, hcov, hs⟩ := h
  obtain ⟨l, hl⟩ := heine_borel a b Nat (fun n x => lo n < x ∧ x < hi n)
    (fun n x hx => by
      obtain ⟨δ, hδ, h1, h2⟩ := exists_pos_le_both (by grind : 0 < x - lo n) (by grind : 0 < hi n - x)
      exact ⟨δ, hδ, fun y hy => by have := abs_lt.1 hy; constructor <;> grind⟩)
    hcov
  let N := l.foldr max 0 + 1
  have := finite_cover hlh N b N (fun _ => True) a (by
      have : ∀ M, pcnt (fun _ => True) M ≤ M := fun M => by
        induction M with
        | zero => exact Nat.le_refl 0
        | succ M ih => show pcnt _ M + _ ≤ M + 1; dsimp only; rw [ite_pos' trivial]; omega
      exact this N) hab fun x hx1 hx2 => by
    obtain ⟨k, hk, h⟩ := hl x ⟨hx1, hx2⟩
    exact ⟨k, by have := le_max_list l hk; omega, trivial, h⟩
  rw [psum_true] at this
  have := fsum_le_of_hasSum (fun n => by have := hlh n; grind) hs N
  grind

/-- **Upper bound.** `[a, b]` has covers of total length `b − a + ε` for every `ε > 0`. -/
theorem coverSum_le (a b : R) {ε : R} (hε : 0 < ε) (hab : a ≤ b) :
    CoverSum (fun x => a ≤ x ∧ x ≤ b) (b - a + ε) := by
  let lo : Nat → R := fun n => if n = 0 then a - ε / 2 else 0
  let hi : Nat → R := fun n => if n = 0 then b + ε / 2 else 0
  refine ⟨lo, hi, fun n => ?_, fun x hx => ⟨0, ?_, ?_⟩, ?_⟩
  · show (if n = 0 then a - ε / 2 else 0) ≤ (if n = 0 then b + ε / 2 else 0); split <;> grind
  · show (if 0 = 0 then a - ε / 2 else 0) < x; rw [ite_pos' rfl]; grind
  · show x < (if 0 = 0 then b + ε / 2 else 0); rw [ite_pos' rfl]; grind
  · have h := Vitali.InvariantMeasure.hasSum_of_zero (b := fun n => hi n - lo n) (m := 1)
      fun k hk => by show (if k = 0 then b + ε / 2 else 0) - (if k = 0 then a - ε / 2 else 0) = 0
                     rw [ite_neg' (by omega), ite_neg' (by omega)]; grind
    have e : fsum (fun n => hi n - lo n) 1 = b - a + ε := by
      show 0 + ((if 0 = 0 then b + ε / 2 else 0) - (if 0 = 0 then a - ε / 2 else 0)) = _
      rw [ite_pos' rfl, ite_pos' rfl]; grind
    rw [e] at h; exact h

/-- If `A` has a cover, the set `{−s | s a cover length}` is non-empty. -/
theorem outer_ne {A : R → Prop} (h : ∃ s, CoverSum A s) : ∃ t, CoverSum A (-t) := by
  obtain ⟨s, hs⟩ := h; exact ⟨-s, by rw [show - -s = s by grind]; exact hs⟩

/-- Cover lengths are non-negative, so `{−s}` is bounded above by `0`. -/
theorem outer_bdd (A : R → Prop) : ∃ M, ∀ t, CoverSum A (-t) → t ≤ M :=
  ⟨0, fun t ⟨lo, hi, hlh, _, hs⟩ => by
    have := hasSum_nonneg (fun n => by have := hlh n; grind) hs; grind⟩

/-- **Lebesgue outer measure** `m*(A)`: the greatest lower bound of the total lengths of countable
covers of `A` by open intervals (and `0` if `A` has no cover of finite total length, a value of no
significance here). -/
noncomputable def outer (A : R → Prop) : R :=
  open Classical in
  if h : ∃ s, CoverSum A s then -Classical.choose (exists_lub _ (outer_ne h) (outer_bdd A)) else 0

/-- **The outer measure of an interval is its length**: `m*([a, b]) = b − a`. -/
theorem outer_interval {a b : R} (hab : a ≤ b) : outer (fun x => a ≤ x ∧ x ≤ b) = b - a := by
  have hex : ∃ s, CoverSum (fun x => a ≤ x ∧ x ≤ b) s := ⟨_, coverSum_le a b (ε := 1) (by grind) hab⟩
  unfold outer
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h4, h5⟩ := Classical.choose_spec (exists_lub _ (outer_ne hex) (outer_bdd _))
  generalize Classical.choose (exists_lub _ (outer_ne hex) (outer_bdd _)) = L at h4 h5
  -- `a − b` is an upper bound of `{−s}`, and nothing smaller is.
  have up : L ≤ a - b := h5 _ fun t ht => by have := coverSum_ge hab ht; grind
  have low : a - b ≤ L := by
    apply Classical.byContradiction; intro hlt
    have := h4 (-(b - a + (a - b - L) / 2)) (by
      rw [show - -(b - a + (a - b - L) / 2) = b - a + (a - b - L) / 2 by grind]
      exact coverSum_le a b (by grind) hab)
    grind
  grind

end Outer

end Foundations.Topology
