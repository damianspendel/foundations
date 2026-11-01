import Foundations.Topology.Compact

/-!
# Exercises VIII: Topology

Problems on Part VIII (`Foundations/Topology`): topological spaces, compactness by open
covers, convergence, and metric continuity on the real line.

A topology `τ : Topology X` is a predicate `τ.IsOpen` on subsets `X → Prop`. A set `K` is
**compact** (`IsCompact τ K`) when every cover of `K` by open sets `U i`, `i : ι`, has a finite
subcover, given as a *list* of indices. Most compactness proofs below therefore end by
building a list.

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in `Exercises/Problems/Topology.lean`.
-/

namespace Exercises.Topology

open Foundations.Numbers Foundations.Numbers.R Foundations.Numbers.OF Lean.Grind
open Foundations.Topology

variable {X : Type}

/-! ## Compactness arguments -/

/-- **Exercise 8.1 (★★) — Finite sets are compact.** In any topological space, the set of
members of a list `l` is compact.

*Hint:* induction on `l`. For `a :: l`, pick an open set of the cover containing `a`, take a
finite subcover for `l` from the induction hypothesis, and put the two together.

*Uses:* `IsCompact` (the definition), `List.mem_cons`. -/
theorem isCompact_list (τ : Topology X) (l : List X) : IsCompact τ (fun x => x ∈ l) := by
  -- SOLUTION
  intro ι U _ hcov
  induction l with
  | nil => exact ⟨[], fun x hx => absurd hx (List.not_mem_nil)⟩
  | cons a l ih =>
    obtain ⟨i, hi⟩ := hcov a List.mem_cons_self
    obtain ⟨L, hL⟩ := ih fun x hx => hcov x (List.mem_cons_of_mem a hx)
    refine ⟨i :: L, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨i, List.mem_cons_self, hi⟩
    · obtain ⟨j, hj, hU⟩ := hL x hx
      exact ⟨j, List.mem_cons_of_mem i hj, hU⟩
  -- END

/-- **Exercise 8.2 (★★) — Unions of two compact sets are compact.**

*Hint:* a cover of `K ∪ L` covers `K` and `L` separately. Concatenate the two finite
subcovers.

*Uses:* `IsCompact`, `List.mem_append`. -/
theorem IsCompact.union' {τ : Topology X} {K L : X → Prop} (hK : IsCompact τ K)
    (hL : IsCompact τ L) : IsCompact τ (fun x => K x ∨ L x) := by
  -- SOLUTION
  intro ι U hU hcov
  obtain ⟨l₁, h₁⟩ := hK ι U hU fun x hx => hcov x (Or.inl hx)
  obtain ⟨l₂, h₂⟩ := hL ι U hU fun x hx => hcov x (Or.inr hx)
  refine ⟨l₁ ++ l₂, fun x hx => ?_⟩
  rcases hx with hx | hx
  · obtain ⟨i, hi, hU'⟩ := h₁ x hx; exact ⟨i, List.mem_append.2 (Or.inl hi), hU'⟩
  · obtain ⟨i, hi, hU'⟩ := h₂ x hx; exact ⟨i, List.mem_append.2 (Or.inr hi), hU'⟩
  -- END

/-- **Exercise 8.3 (★★★) — Closed subsets of compact sets are compact.** If `K` is compact
and `F` is closed, then `K ∩ F` is compact.

*Hint:* given an open cover `U` of `K ∩ F`, enlarge it by one more open set, the complement
of `F`. Index the enlarged cover by `Option ι`: `none ↦ ¬F`, `some i ↦ U i`. It covers `K`;
take a finite subcover, and throw away `none` (use `List.filterMap id`, or `List.reduceOption`).
Points of `K ∩ F` are not in the complement of `F`, so they are covered by the rest.

*Uses:* `IsCompact`, `Topology.IsClosed`, `List.mem_filterMap`. -/
theorem IsCompact.inter_closed {τ : Topology X} {K F : X → Prop} (hK : IsCompact τ K)
    (hF : τ.IsClosed F) : IsCompact τ (fun x => K x ∧ F x) := by
  -- SOLUTION
  intro ι U hU hcov
  let V : Option ι → X → Prop := fun o => match o with
    | none => fun x => ¬ F x
    | some i => U i
  have hV : ∀ o, τ.IsOpen (V o) := fun o => match o with
    | none => hF
    | some i => hU i
  obtain ⟨l, hl⟩ := hK (Option ι) V hV fun x hx => by
    by_cases hFx : F x
    · obtain ⟨i, hi⟩ := hcov x ⟨hx, hFx⟩; exact ⟨some i, hi⟩
    · exact ⟨none, hFx⟩
  refine ⟨l.filterMap id, fun x ⟨hx, hFx⟩ => ?_⟩
  obtain ⟨o, ho, hVo⟩ := hl x hx
  cases o with
  | none => exact absurd hVo (by simpa [V] using hFx)
  | some i => exact ⟨i, List.mem_filterMap.2 ⟨some i, ho, rfl⟩, hVo⟩
  -- END

/-- **Exercise 8.4 (★★) — In the indiscrete topology, everything is compact.**

*Hint:* the only open sets are `∅` and the whole space. If `K` is empty, the empty list
works; otherwise some open set of the cover contains a point of `K`, so it is the whole space,
and a one-element list suffices.

*Uses:* `Topology.indiscrete`, `IsCompact`. -/
theorem isCompact_indiscrete (K : X → Prop) : IsCompact (Topology.indiscrete X) K := by
  -- SOLUTION
  intro ι U hU hcov
  by_cases h : ∃ x, K x
  · obtain ⟨x, hx⟩ := h
    obtain ⟨i, hi⟩ := hcov x hx
    rcases hU i with hU' | hU'
    · exact absurd hi (hU' x)
    · exact ⟨[i], fun y _ => ⟨i, List.mem_singleton_self i, hU' y⟩⟩
  · exact ⟨[], fun y hy => absurd ⟨y, hy⟩ h⟩
  -- END

/-- **Exercise 8.5 (★★) — The continuous image of `[0, 1]` under squaring is compact.**

*Hint:* the Heine–Borel theorem makes `[0, 1]` compact, and continuous images of compact sets
are compact. The library's `R.continuousAt_mul` gives continuity in the ε-δ sense of Part II;
`continuousAt_iff_R` translates it into the metric-space sense.

*Uses:* `heine_borel`, `IsCompact.image_of_continuousAt`, `continuousAt_iff_R`,
`R.continuousAt_mul`, `R.continuousAt_id`. -/
theorem isCompact_square_image :
    IsCompact (Topology.metric R) (fun y => ∃ x, (0 ≤ x ∧ x ≤ 1) ∧ x * x = y) := by
  -- SOLUTION
  exact IsCompact.image_of_continuousAt (heine_borel 0 1) fun x _ =>
    (continuousAt_iff_R _ x).2 (continuousAt_mul (continuousAt_id x) (continuousAt_id x))
  -- END

/-! ## Convergence and continuity -/

/-- **Exercise 8.6 (★) — Convergent sequences in a discrete space are eventually constant.**
If `sₙ → L` in the discrete topology, then `sₙ = L` for all large `n`.

*Hint:* in the discrete topology the singleton `{L}` is open.

*Uses:* `Topology.Converges`, `Topology.discrete`. -/
theorem converges_discrete {s : Nat → X} {L : X} (h : (Topology.discrete X).Converges s L) :
    ∃ N, ∀ n, N ≤ n → s n = L := by
  -- SOLUTION
  exact h (fun x => x = L) trivial rfl
  -- END

/-- **Exercise 8.7 (★★) — Affine maps are continuous, via Lipschitz.** The map `x ↦ 2x + 1` on
`ℝ` is continuous in the metric sense.

*Hint:* it stretches distances by the factor `2`. The distance on `ℝ` is `|x − y|`; to compare
two absolute values, split each into cases with `OF.abs_cases` and finish with `grind`.

*Uses:* `continuous_of_lipschitz`, `dist_R`, `OF.abs_cases`. -/
theorem continuous_two_mul_add_one : Foundations.Topology.Continuous (fun x : R => 2 * x + 1) := by
  -- SOLUTION
  refine continuous_of_lipschitz (K := 2) (by grind) fun x y => ?_
  rw [dist_R, dist_R]
  rcases abs_cases (2 * x + 1 - (2 * y + 1)) with h₁ | h₁ <;>
    rcases abs_cases (x - y) with h₂ | h₂ <;> grind
  -- END

end Exercises.Topology
