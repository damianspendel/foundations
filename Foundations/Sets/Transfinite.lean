import Foundations.Sets.Ordinals

/-!
# Successor and limit ordinals; transfinite induction

Counting past the finite, one meets two kinds of ordinal. Some are reached by a
single step from a predecessor — the **successor** ordinals `α + 1 = α ∪ {α}`.
Others, like `ω`, have no immediate predecessor: they are reached only as the
"limit" of everything before them, and as von Neumann sets they are simply the
union of all smaller ordinals. Every ordinal is exactly one of: zero, a
successor, or a limit.

This trichotomy is what makes **transfinite induction** usable in practice: to
prove a property of all ordinals, show it for `0`, show that it passes from `α`
to `α + 1`, and show that it passes to a limit from everything below. We derive
both the general (course-of-values) form, from ∈-induction, and this three-case
form. We also show that the union of any set of ordinals is an ordinal — its
supremum — so that limits always exist.
-/

namespace Foundations.Sets

namespace ZFSet

/-- The union of a transitive set is contained in it. -/
theorem sUnion_subset_of_transitive {x : ZFSet} (hx : IsTransitive x) : ⋃₀ x ⊆ x := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := mem_sUnion.1 hz
  exact hx y hy hzy

/-- **Suprema.** The union of a set of ordinals is an ordinal. -/
theorem isOrdinal_sUnion {s : ZFSet} (hs : ∀ x ∈ s, IsOrdinal x) : IsOrdinal (⋃₀ s) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx, hyx⟩ := mem_sUnion.1 hy
    exact mem_sUnion.2 ⟨x, hx, (hs x hx).1 y hyx hz⟩
  · obtain ⟨x, hx, hyx⟩ := mem_sUnion.1 hy
    exact ((hs x hx).mem hyx).1

/-- The union of a set of ordinals is an upper bound for it. -/
theorem subset_sUnion_of_mem {s x : ZFSet} (hx : x ∈ s) : x ⊆ ⋃₀ s :=
  fun _ hz => mem_sUnion.2 ⟨x, hx, hz⟩

/-- A **successor ordinal** is the successor of some ordinal. -/
def IsSuccOrdinal (α : ZFSet) : Prop := ∃ β, IsOrdinal β ∧ α = succ β

/-- A **limit ordinal** is a non-zero ordinal equal to the union of its members. -/
def IsLimitOrdinal (α : ZFSet) : Prop := IsOrdinal α ∧ α ≠ ∅ ∧ ⋃₀ α = α

/-- The union of a successor `succ β` (of an ordinal) is `β`. -/
theorem sUnion_succ {β : ZFSet} (hβ : IsOrdinal β) : ⋃₀ succ β = β := by
  apply subset_antisymm
  · intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_sUnion.1 hz
    rcases mem_succ.1 hy with rfl | hy
    · exact hzy
    · exact hβ.1 y hy hzy
  · intro z hz
    exact mem_sUnion.2 ⟨β, mem_succ_self β, hz⟩

/-- **Classification of ordinals.** Every ordinal is zero, a successor, or a
limit. -/
theorem ordinal_cases {α : ZFSet} (hα : IsOrdinal α) :
    α = ∅ ∨ IsSuccOrdinal α ∨ IsLimitOrdinal α := by
  by_cases h0 : α = ∅
  · exact Or.inl h0
  by_cases hU : ⋃₀ α = α
  · exact Or.inr (Or.inr ⟨hα, h0, hU⟩)
  -- some member `β` of `α` is not in `⋃₀ α`; then `α = succ β`
  have hex : ∃ β, β ∈ α ∧ β ∉ ⋃₀ α := Classical.byContradiction fun hn =>
    hU (subset_antisymm (sUnion_subset_of_transitive hα.1) fun β hβ =>
      Classical.byContradiction fun hβ' => hn ⟨β, hβ, hβ'⟩)
  obtain ⟨β, hβα, hβU⟩ := hex
  have hβ : IsOrdinal β := hα.mem hβα
  refine Or.inr (Or.inl ⟨β, hβ, subset_antisymm (fun γ hγ => ?_) (fun γ hγ => ?_)⟩)
  · rcases ordinal_trichotomy (hα.mem hγ) hβ with h | h | h
    · exact mem_succ.2 (Or.inr h)
    · exact mem_succ.2 (Or.inl h)
    · exact absurd (mem_sUnion.2 ⟨γ, hγ, h⟩) hβU
  · rcases mem_succ.1 hγ with rfl | h
    · exact hβα
    · exact hα.1 β hβα h

/-- Zero is neither a successor nor a limit; a successor is not a limit. -/
theorem ordinal_cases_exclusive {α : ZFSet} :
    ¬ (α = ∅ ∧ IsSuccOrdinal α) ∧ ¬ (α = ∅ ∧ IsLimitOrdinal α) ∧
      ¬ (IsSuccOrdinal α ∧ IsLimitOrdinal α) := by
  refine ⟨fun ⟨h0, β, _, hs⟩ => succ_ne_empty β (hs ▸ h0), fun ⟨h0, _, h, _⟩ => h h0, ?_⟩
  rintro ⟨⟨β, hβ, rfl⟩, _, _, hU⟩
  rw [sUnion_succ hβ] at hU
  have h := mem_succ_self β
  rw [← hU] at h
  exact mem_irrefl β h

/-- **ω is a limit ordinal.** -/
theorem omega_isLimit : IsLimitOrdinal ω := by
  refine ⟨isOrdinal_omega, fun h => not_mem_empty _ (h ▸ empty_mem_omega), ?_⟩
  apply subset_antisymm (sUnion_subset_of_transitive isOrdinal_omega.1)
  intro x hx
  exact mem_sUnion.2 ⟨succ x, succ_mem_omega hx, mem_succ_self x⟩

/-- Every von Neumann natural `vn (n + 1)` is a successor ordinal. -/
theorem vn_succ_isSucc (n : Nat) : IsSuccOrdinal (vn (n + 1)) := ⟨vn n, isOrdinal_vn n, rfl⟩

/-- **Transfinite induction (course-of-values form).** If a property holds of an
ordinal whenever it holds of all smaller ordinals, it holds of every ordinal. -/
theorem transfinite_induction (P : ZFSet → Prop)
    (h : ∀ α, IsOrdinal α → (∀ β ∈ α, P β) → P α) : ∀ α, IsOrdinal α → P α :=
  mem_induction (fun α => IsOrdinal α → P α) fun α ih hα =>
    h α hα fun β hβ => ih β hβ (hα.mem hβ)

/-- **Transfinite induction (zero / successor / limit form).** A property that
holds of `∅`, passes from `β` to `succ β`, and passes to each limit ordinal from
all smaller ordinals, holds of every ordinal. -/
theorem transfinite_induction₃ (P : ZFSet → Prop) (h0 : P ∅)
    (hs : ∀ β, IsOrdinal β → P β → P (succ β))
    (hl : ∀ α, IsLimitOrdinal α → (∀ β ∈ α, P β) → P α) : ∀ α, IsOrdinal α → P α := by
  refine transfinite_induction P fun α hα ih => ?_
  rcases ordinal_cases hα with rfl | ⟨β, hβ, rfl⟩ | hlim
  · exact h0
  · exact hs β hβ (ih β (mem_succ_self β))
  · exact hl α hlim ih

end ZFSet

end Foundations.Sets
