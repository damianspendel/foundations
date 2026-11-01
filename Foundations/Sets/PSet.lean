/-!
# Pre-sets: Aczel's model of sets inside type theory

Lean's foundation is a *type theory*, not a set theory. To speak about sets in
the sense of Zermelo–Fraenkel (ZF), we build a model of ZF inside type theory,
following Peter Aczel's idea (1978).

The guiding picture is the *cumulative hierarchy*: a set is nothing but the
collection of its members, and those members are again sets. A **pre-set** makes
this picture literal: a pre-set is given by an *index type* `α` together with a
family `A : α → PSet` that lists the members, one for every index. Since the
members are again pre-sets, `PSet` is an inductive type — every pre-set is built
in well-founded stages, just like the cumulative hierarchy.

A pre-set is a *presentation* of a set, not yet the set itself: the same members
may be listed twice, or in a different order, or with different index types. Two
pre-sets should count as "the same set" exactly when every member of one has an
equal member in the other, and vice versa. This **extensional equivalence**
`PSet.Equiv` is defined by recursion and shown to be an equivalence relation. In
the next file (`ZFSet`) we pass to the quotient, which identifies equivalent
presentations: that quotient is our universe of sets.

*Universe bookkeeping.* Index types live in `Type` (universe 0), so `PSet` itself
lives one universe higher, in `Type 1`. This is the type-theoretic shadow of the
fact that the collection of all sets is not itself a set.
-/

namespace Foundations.Sets

/-- A **pre-set** is given by an index type `α : Type` and a family `A : α → PSet`
listing its members. Different presentations of the same set are identified
later, by extensional equivalence. -/
inductive PSet : Type 1
  | mk (α : Type) (A : α → PSet) : PSet

namespace PSet

/-- The index type of a pre-set: the "labels" of its listed members. -/
def Ix : PSet → Type
  | ⟨α, _⟩ => α

/-- The member of a pre-set listed under a given index. -/
def Func : (x : PSet) → x.Ix → PSet
  | ⟨_, A⟩ => A

@[simp] theorem Ix_mk (α : Type) (A : α → PSet) : (mk α A).Ix = α := rfl

@[simp] theorem Func_mk (α : Type) (A : α → PSet) (a : α) : (mk α A).Func a = A a := rfl

/-- **Extensional equivalence of pre-sets.** Two pre-sets are equivalent when every
listed member of the first is equivalent to some listed member of the second, and
vice versa. Defined by structural recursion: the members are earlier stages. -/
def Equiv : PSet → PSet → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b))

/-- Unfolding the definition of `Equiv` on explicit pre-sets. -/
theorem equiv_iff {α β : Type} {A : α → PSet} {B : β → PSet} :
    Equiv (mk α A) (mk β B) ↔
      (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b)) := by
  simp [Equiv]

/-- Every pre-set is equivalent to itself. -/
theorem Equiv.refl (x : PSet) : Equiv x x := by
  induction x with
  | mk α A ih => exact equiv_iff.2 ⟨fun a => ⟨a, ih a⟩, fun a => ⟨a, ih a⟩⟩

/-- Extensional equivalence is symmetric. -/
theorem Equiv.symm {x y : PSet} : Equiv x y → Equiv y x := by
  induction x generalizing y with
  | mk α A ih =>
    cases y with
    | mk β B =>
      intro h
      obtain ⟨h1, h2⟩ := equiv_iff.1 h
      refine equiv_iff.2 ⟨fun b => ?_, fun a => ?_⟩
      · obtain ⟨a, ha⟩ := h2 b; exact ⟨a, ih a ha⟩
      · obtain ⟨b, hb⟩ := h1 a; exact ⟨b, ih a hb⟩

/-- Extensional equivalence is transitive. -/
theorem Equiv.trans {x y z : PSet} : Equiv x y → Equiv y z → Equiv x z := by
  induction x generalizing y z with
  | mk α A ih =>
    cases y with
    | mk β B =>
      cases z with
      | mk γ C =>
        intro hxy hyz
        obtain ⟨h1, h2⟩ := equiv_iff.1 hxy
        obtain ⟨h3, h4⟩ := equiv_iff.1 hyz
        refine equiv_iff.2 ⟨fun a => ?_, fun c => ?_⟩
        · obtain ⟨b, hb⟩ := h1 a
          obtain ⟨c, hc⟩ := h3 b
          exact ⟨c, ih a hb hc⟩
        · obtain ⟨b, hb⟩ := h4 c
          obtain ⟨a, ha⟩ := h2 b
          exact ⟨a, ih a ha hb⟩

/-- **Extensional equivalence is an equivalence relation** (reflexive, symmetric,
transitive), so it may serve as "equality of sets". -/
theorem equiv_equivalence : Equivalence Equiv :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- The setoid of pre-sets under extensional equivalence; its quotient is `ZFSet`. -/
instance setoid : Setoid PSet := ⟨Equiv, equiv_equivalence⟩

/-- The setoid relation `≈` on pre-sets is `Equiv`. -/
theorem equiv_def {x y : PSet} : x ≈ y ↔ Equiv x y := Iff.rfl

/-- Membership of pre-sets: `x ∈ y` when `x` is equivalent to some listed member of `y`. -/
protected def Mem (y x : PSet) : Prop := ∃ b, Equiv x (y.Func b)

/-- Pre-set membership `x ∈ y`. -/
instance : Membership PSet PSet := ⟨PSet.Mem⟩

/-- Unfolding pre-set membership. -/
theorem mem_iff {x y : PSet} : x ∈ y ↔ ∃ b, Equiv x (y.Func b) := Iff.rfl

/-- Every listed member of a pre-set is a member of it. -/
theorem func_mem (x : PSet) (i : x.Ix) : x.Func i ∈ x := ⟨i, Equiv.refl _⟩

/-- Membership respects equivalence on the left. -/
theorem mem_of_equiv_left {x x' y : PSet} (h : Equiv x x') : x ∈ y → x' ∈ y := by
  rintro ⟨b, hb⟩
  exact ⟨b, h.symm.trans hb⟩

/-- Membership respects equivalence on the right. -/
theorem mem_of_equiv_right {x y y' : PSet} (h : Equiv y y') : x ∈ y → x ∈ y' := by
  cases y with
  | mk β B =>
    cases y' with
    | mk γ C =>
      rintro ⟨b, hb⟩
      obtain ⟨c, hc⟩ := (equiv_iff.1 h).1 b
      exact ⟨c, hb.trans hc⟩

/-- **Membership is well defined on equivalence classes**: replacing either side
by an equivalent pre-set does not change whether membership holds. -/
theorem mem_congr {x x' y y' : PSet} (hx : Equiv x x') (hy : Equiv y y') :
    x ∈ y ↔ x' ∈ y' :=
  ⟨fun h => mem_of_equiv_right hy (mem_of_equiv_left hx h),
   fun h => mem_of_equiv_right hy.symm (mem_of_equiv_left hx.symm h)⟩

/-- **Extensionality for pre-sets.** Pre-sets with the same members (up to
equivalence) are equivalent. -/
theorem equiv_of_mem_iff {x y : PSet} (h : ∀ z, z ∈ x ↔ z ∈ y) : Equiv x y := by
  cases x with
  | mk α A =>
    cases y with
    | mk β B =>
      refine equiv_iff.2 ⟨fun a => ?_, fun b => ?_⟩
      · exact (h (A a)).1 (func_mem (mk α A) a)
      · obtain ⟨a, ha⟩ := (h (B b)).2 (func_mem (mk β B) b)
        exact ⟨a, ha.symm⟩

end PSet

end Foundations.Sets
