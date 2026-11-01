import Foundations.Sets.ZFSet

/-!
# The paradoxes: Russell and Cantor

Naive set theory, in Frege's form, held that every property determines a set:
the set of all things having it. Russell (1901) showed that this is
inconsistent. Consider the property "is not a member of itself". If there were
a set `R` of exactly the sets with that property, then `R ∈ R` would hold if and
only if `R ∉ R` — a contradiction.

ZF escapes by allowing only *separation*: a property may carve a subset out of
an already given set, but need not determine a set outright. Run through
separation, Russell's argument stops being a paradox and becomes a theorem:
**there is no set of all sets**. Our proof uses only separation, not foundation.

The underlying pattern is purely logical — *no barber shaves exactly those who
do not shave themselves* — and we isolate it first. The same diagonal pattern
gives **Cantor's theorem**: no set can be mapped onto the collection of its
subsets. We prove it both for Lean types (with subsets as predicates) and for
ZF sets (with the power set). Cantor's theorem is the source of the endless
hierarchy of infinite sizes; Russell found his paradox by applying Cantor's
argument to the "set of all sets".
-/

namespace Foundations.Sets

/-- A function is **bijective** when it is injective and surjective, i.e. a
one-to-one correspondence. -/
def Bijective {α : Sort _} {β : Sort _} (f : α → β) : Prop :=
  Function.Injective f ∧ Function.Surjective f

/-- **The barber (pure logic).** For any relation `r` on any type, nothing bears
`r` to exactly those things that do not bear `r` to themselves. This is the
logical core of Russell's paradox. -/
theorem barber {α : Sort _} (r : α → α → Prop) : ¬ ∃ b, ∀ x, r x b ↔ ¬ r x x := by
  rintro ⟨b, hb⟩
  have h := hb b
  have hn : ¬ r b b := fun hr => h.1 hr hr
  exact hn (h.2 hn)

/-- **Cantor's theorem for types.** No function from a type `α` to its "power type"
`α → Prop` (predicates on `α`, i.e. subsets) is surjective. -/
theorem cantor_type {α : Type _} : ¬ ∃ f : α → (α → Prop), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨d, hd⟩ := hf (fun x => ¬ f x x)
  exact barber (fun x y => f y x) ⟨d, fun x => by rw [hd]⟩

namespace ZFSet

/-- **Naive comprehension fails.** No set has as members exactly the sets that
are not members of themselves. -/
theorem no_russell_set : ¬ ∃ R : ZFSet, ∀ x, x ∈ R ↔ x ∉ x :=
  barber (fun x y : ZFSet => x ∈ y)

/-- **Russell's argument via separation.** For every set `s`, the Russell set
`{x ∈ s | x ∉ x}` of `s` is not a member of `s`. So every set omits something. -/
theorem russell_not_mem (s : ZFSet) : sep (fun x => x ∉ x) s ∉ s := by
  intro hs
  have h : sep (fun x => x ∉ x) s ∈ sep (fun x => x ∉ x) s ↔
      sep (fun x => x ∉ x) s ∉ sep (fun x => x ∉ x) s := by
    exact ⟨fun h => (mem_sep.1 h).2, fun h => mem_sep.2 ⟨hs, h⟩⟩
  have hn : sep (fun x => x ∉ x) s ∉ sep (fun x => x ∉ x) s := fun hm => h.1 hm hm
  exact hn (h.2 hn)

/-- **Russell's paradox (there is no universal set).** No set contains every
set. Proved by separation alone, without appeal to foundation. -/
theorem russell : ¬ ∃ U : ZFSet, ∀ x, x ∈ U := by
  rintro ⟨U, hU⟩
  exact russell_not_mem U (hU _)

/-- **Cantor's theorem for sets.** For every set `x` and every operation `f` on
sets, `f` does not map the members of `x` onto the subsets of `x`: some subset
of `x` (namely `{z ∈ x | z ∉ f z}`) is not of the form `f z` with `z ∈ x`. -/
theorem cantor (x : ZFSet) (f : ZFSet → ZFSet) :
    ¬ ∀ y ∈ powerset x, ∃ z ∈ x, f z = y := by
  intro h
  let D := sep (fun z => z ∉ f z) x
  obtain ⟨z, hz, hfz⟩ := h D (mem_powerset.2 (sep_subset _ x))
  have key : z ∈ D ↔ z ∉ D := by
    constructor
    · intro h
      have h2 : z ∉ f z := (mem_sep.1 h).2
      rw [hfz] at h2
      exact h2
    · intro h
      refine mem_sep.2 ⟨hz, ?_⟩
      show z ∉ f z
      rw [hfz]
      exact h
  have hn : z ∉ D := fun hm => key.1 hm hm
  exact hn (key.2 hn)

/-- **Cantor's theorem, image form.** The power set of `x` is never contained in
the image of `x` under any operation on sets. -/
theorem powerset_not_subset_image (x : ZFSet) (f : ZFSet → ZFSet) :
    ¬ powerset x ⊆ image f x := fun h =>
  cantor x f fun _ hy => mem_image.1 (h hy)

end ZFSet

end Foundations.Sets
