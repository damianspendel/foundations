import Foundations.Sets.Omega

/-!
# Von Neumann ordinals and the Burali-Forti paradox

The natural numbers count *how many*; ordinals count *how far along* — they are
the measure of position in a well-ordered sequence, and they continue past every
natural number: `0, 1, 2, …, ω, ω + 1, …`. Von Neumann's insight is that, as with
the naturals, each ordinal can be taken to be the set of all smaller ordinals,
ordered by membership.

Formally, a set is **transitive** if every member of it is also a subset of it
(members of members are members), and an **ordinal** is a transitive set all of
whose members are transitive. (In the presence of foundation this simple
definition suffices: membership is then automatically well-founded.)

We show that every von Neumann natural and `ω` itself are ordinals, that the
members of an ordinal are ordinals, and that membership is a strict linear order
on ordinals — irreflexive, transitive and *trichotomous*: of two ordinals, one
is a member of the other or they are equal.

Finally, **Burali-Forti's paradox** (1897): there is no set of all ordinals.
Such a set would itself be an ordinal, hence a member of itself — which
foundation forbids. Like Russell's paradox, this marks the boundary between
the sets and the "too large" totalities, such as *all sets* or *all ordinals*,
that cannot be gathered into a set.
-/

namespace Foundations.Sets

namespace ZFSet

/-- A set is **transitive** when each of its members is also a subset of it. -/
def IsTransitive (x : ZFSet) : Prop := ∀ y ∈ x, y ⊆ x

/-- A **(von Neumann) ordinal** is a transitive set all of whose members are transitive. -/
def IsOrdinal (x : ZFSet) : Prop := IsTransitive x ∧ ∀ y ∈ x, IsTransitive y

/-- **Members of ordinals are ordinals.** -/
theorem IsOrdinal.mem {x y : ZFSet} (hx : IsOrdinal x) (hy : y ∈ x) : IsOrdinal y :=
  ⟨hx.2 y hy, fun z hz => hx.2 z (hx.1 y hy hz)⟩

/-- Membership is transitive on (the members of) an ordinal: `x ∈ y ∈ z` gives `x ∈ z`. -/
theorem IsOrdinal.mem_trans {x y z : ZFSet} (hz : IsOrdinal z) (hxy : x ∈ y) (hyz : y ∈ z) :
    x ∈ z :=
  hz.1 y hyz hxy

/-- The empty set is an ordinal (the ordinal `0`). -/
theorem isOrdinal_empty : IsOrdinal ∅ :=
  ⟨fun y hy => absurd hy (not_mem_empty y), fun y hy => absurd hy (not_mem_empty y)⟩

/-- The successor of an ordinal is an ordinal. -/
theorem IsOrdinal.succ {x : ZFSet} (hx : IsOrdinal x) : IsOrdinal (succ x) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · rcases mem_succ.1 hy with rfl | hy
    · exact mem_succ.2 (Or.inr hz)
    · exact mem_succ.2 (Or.inr (hx.1 y hy hz))
  · rcases mem_succ.1 hy with rfl | hy
    · exact hx.1
    · exact hx.2 y hy

/-- **Every von Neumann natural is an ordinal.** -/
theorem isOrdinal_vn (n : Nat) : IsOrdinal (vn n) := by
  induction n with
  | zero => exact isOrdinal_empty
  | succ n ih => exact ih.succ

/-- **ω is an ordinal** (the first infinite ordinal). -/
theorem isOrdinal_omega : IsOrdinal ω := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · obtain ⟨n, rfl⟩ := mem_omega.1 hy
    obtain ⟨m, _, rfl⟩ := mem_vn.1 hz
    exact vn_mem_omega m
  · obtain ⟨n, rfl⟩ := mem_omega.1 hy
    exact (isOrdinal_vn n).1

/-- **Trichotomy for ordinals.** For ordinals `x` and `y`: `x ∈ y`, `x = y`, or `y ∈ x`.
Proved by a double ∈-induction. -/
theorem ordinal_trichotomy {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    x ∈ y ∨ x = y ∨ y ∈ x := by
  have key : ∀ x, IsOrdinal x → ∀ y, IsOrdinal y → x ∈ y ∨ x = y ∨ y ∈ x := by
    refine mem_induction _ (fun x ihx hx => ?_)
    refine mem_induction _ (fun y ihy hy => ?_)
    apply Classical.byContradiction
    intro hne
    have hxy : x ∉ y := fun h => hne (Or.inl h)
    have hyx : y ∉ x := fun h => hne (Or.inr (Or.inr h))
    apply hne
    refine Or.inr (Or.inl (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩))
    · -- `z ∈ x`: compare `z` with `y` using the outer hypothesis
      rcases ihx z hz (hx.mem hz) y hy with h | rfl | h
      · exact h
      · exact absurd hz hyx
      · exact absurd (hx.mem_trans h hz) hyx
    · -- `z ∈ y`: compare `x` with `z` using the inner hypothesis
      rcases ihy z hz (hy.mem hz) with h | rfl | h
      · exact absurd (hy.mem_trans h hz) hxy
      · exact absurd hz hxy
      · exact h
  exact key x hx y hy

/-- **Membership is a strict linear order on ordinals**: irreflexive, transitive,
and trichotomous. -/
theorem ordinal_mem_strictLinearOrder :
    (∀ x, IsOrdinal x → x ∉ x) ∧
    (∀ x y z, IsOrdinal z → x ∈ y → y ∈ z → x ∈ z) ∧
    (∀ x y, IsOrdinal x → IsOrdinal y → x ∈ y ∨ x = y ∨ y ∈ x) :=
  ⟨fun x _ => mem_irrefl x, fun _ _ _ hz hxy hyz => hz.mem_trans hxy hyz,
   fun _ _ hx hy => ordinal_trichotomy hx hy⟩

/-- A transitive set of ordinals is an ordinal. -/
theorem isOrdinal_of_transitive_of_ordinals {s : ZFSet} (ht : IsTransitive s)
    (h : ∀ y ∈ s, IsOrdinal y) : IsOrdinal s :=
  ⟨ht, fun y hy => (h y hy).1⟩

/-- **Burali-Forti paradox.** There is no set of all ordinals: no set `Ω` contains
every ordinal. -/
theorem burali_forti : ¬ ∃ Ω : ZFSet, ∀ x, IsOrdinal x → x ∈ Ω := by
  rintro ⟨Ω, hΩ⟩
  -- the set of all ordinals, separated out of `Ω`
  let O := sep IsOrdinal Ω
  have hO : ∀ x, x ∈ O ↔ IsOrdinal x := fun x =>
    ⟨fun h => (mem_sep.1 h).2, fun h => mem_sep.2 ⟨hΩ x h, h⟩⟩
  have hOrd : IsOrdinal O :=
    isOrdinal_of_transitive_of_ordinals
      (fun y hy z hz => (hO z).2 (((hO y).1 hy).mem hz))
      (fun y hy => (hO y).1 hy)
  exact mem_irrefl O ((hO O).2 hOrd)

end ZFSet

end Foundations.Sets
