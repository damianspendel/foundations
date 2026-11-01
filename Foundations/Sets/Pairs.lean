import Foundations.Sets.ZFSet

/-!
# Set algebra, ordered pairs and cartesian products

Sets are unordered: `{a, b} = {b, a}`. Yet mathematics constantly needs *ordered*
pairs — the point `(3, 5)` differs from `(5, 3)` — and with them relations and
functions. Kuratowski (1921) found a purely set-theoretic definition:

    ⟪a, b⟫ := {{a}, {a, b}}.

Nothing about this set "is" an order; what matters is only that it does the job
of one: `⟪a, b⟫ = ⟪c, d⟫` holds exactly when `a = c` and `b = d`. This is an early
and instructive example of the structuralist attitude that pervades the
foundations of mathematics — an object is characterised by its role, not by any
intrinsic nature.

We first add intersection and difference (both by separation), then prove the
characteristic property of Kuratowski pairs, and finally build the cartesian
product `x × y` by separating the pairs out of the power set of the power set of
`x ∪ y` — a nice illustration of how the ZF axioms bound where new sets can come
from.
-/

namespace Foundations.Sets

namespace ZFSet

/-! ## Intersection and difference -/

/-- Intersection `x ∩ y := {z ∈ x | z ∈ y}`. -/
noncomputable instance : Inter ZFSet := ⟨fun x y => sep (· ∈ y) x⟩

/-- Difference `x \ y := {z ∈ x | z ∉ y}`. -/
noncomputable instance : SDiff ZFSet := ⟨fun x y => sep (· ∉ y) x⟩

/-- Members of `x ∩ y` are the common members of `x` and `y`. -/
@[simp] theorem mem_inter {x y z : ZFSet} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := mem_sep

/-- Members of `x \ y` are the members of `x` that are not members of `y`. -/
@[simp] theorem mem_sdiff {x y z : ZFSet} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y := mem_sep

/-- Intersection is commutative. -/
theorem inter_comm (x y : ZFSet) : x ∩ y = y ∩ x :=
  ext fun _ => by simp only [mem_inter]; exact And.comm

/-- Union is commutative. -/
theorem union_comm (x y : ZFSet) : x ∪ y = y ∪ x :=
  ext fun _ => by simp only [mem_union]; exact Or.comm

/-- Intersection distributes over union. -/
theorem inter_union_distrib (x y z : ZFSet) : x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z) :=
  ext fun _ => by simp only [mem_inter, mem_union]; exact and_or_left

/-- **De Morgan for difference.** `x \ (y ∪ z) = (x \ y) ∩ (x \ z)`. -/
theorem sdiff_union (x y z : ZFSet) : x \ (y ∪ z) = (x \ y) ∩ (x \ z) :=
  ext fun w => by
    simp only [mem_sdiff, mem_union, mem_inter]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨hx, fun hy => h (Or.inl hy)⟩, ⟨hx, fun hz => h (Or.inr hz)⟩⟩
    · rintro ⟨⟨hx, hy⟩, ⟨_, hz⟩⟩
      exact ⟨hx, fun h => h.elim hy hz⟩

/-! ## Singletons and unordered pairs -/

/-- Transport membership along an equality of sets. -/
theorem mem_of_eq {x y z : ZFSet} (h : x = y) (hz : z ∈ x) : z ∈ y := h ▸ hz

/-- `{a} = {b}` iff `a = b`. -/
theorem singleton_inj {a b : ZFSet} : ({a} : ZFSet) = {b} ↔ a = b :=
  ⟨fun h => mem_singleton.1 (mem_of_eq h (mem_singleton.2 rfl)), fun h => h ▸ rfl⟩

/-! ## Kuratowski ordered pairs -/

/-- The **Kuratowski ordered pair** `⟪a, b⟫ := {{a}, {a, b}}`. -/
noncomputable def kpair (a b : ZFSet) : ZFSet := {{a}, {a, b}}

/-- Notation `⟪a, b⟫` for the Kuratowski ordered pair. -/
notation "⟪" a ", " b "⟫" => kpair a b

/-- Members of `⟪a, b⟫` are `{a}` and `{a, b}`. -/
theorem mem_kpair {a b z : ZFSet} : z ∈ ⟪a, b⟫ ↔ z = {a} ∨ z = {a, b} := mem_pair

/-- **Characteristic property of ordered pairs.** `⟪a, b⟫ = ⟪c, d⟫` if and only if
`a = c` and `b = d`. -/
theorem kpair_inj {a b c d : ZFSet} : ⟪a, b⟫ = ⟪c, d⟫ ↔ a = c ∧ b = d := by
  constructor
  · intro h
    -- `{a}` is a member of the right-hand side
    have h1 : ({a} : ZFSet) = {c} ∨ ({a} : ZFSet) = {c, d} :=
      mem_kpair.1 (mem_of_eq h (mem_kpair.2 (Or.inl rfl)))
    have hac : a = c := by
      rcases h1 with h1 | h1
      · exact singleton_inj.1 h1
      · exact (mem_singleton.1 (mem_of_eq h1.symm (mem_pair.2 (Or.inl rfl)))).symm
    subst hac
    -- `{a, b}` is a member of the right-hand side, `{a, d}` of the left-hand side
    have h2 : ({a, b} : ZFSet) = {a} ∨ ({a, b} : ZFSet) = {a, d} :=
      mem_kpair.1 (mem_of_eq h (mem_kpair.2 (Or.inr rfl)))
    have h3 : ({a, d} : ZFSet) = {a} ∨ ({a, d} : ZFSet) = {a, b} :=
      mem_kpair.1 (mem_of_eq h.symm (mem_kpair.2 (Or.inr rfl)))
    have hb : b = a ∨ b = d := by
      rcases h2 with h2 | h2
      · exact Or.inl (mem_singleton.1 (mem_of_eq h2 (mem_pair.2 (Or.inr rfl))))
      · exact mem_pair.1 (mem_of_eq h2 (mem_pair.2 (Or.inr rfl)))
    have hd : d = a ∨ d = b := by
      rcases h3 with h3 | h3
      · exact Or.inl (mem_singleton.1 (mem_of_eq h3 (mem_pair.2 (Or.inr rfl))))
      · exact mem_pair.1 (mem_of_eq h3 (mem_pair.2 (Or.inr rfl)))
    refine ⟨rfl, ?_⟩
    rcases hb with hb | hb
    · rcases hd with hd | hd
      · exact hb.trans hd.symm
      · exact hd.symm
    · exact hb
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## Cartesian products -/

/-- The pair `⟪a, b⟫` of members of `x` and `y` lies in `𝒫(𝒫(x ∪ y))`. -/
theorem kpair_mem_powerset_powerset {x y a b : ZFSet} (ha : a ∈ x) (hb : b ∈ y) :
    ⟪a, b⟫ ∈ powerset (powerset (x ∪ y)) := by
  rw [mem_powerset]
  intro z hz
  rw [mem_powerset]
  rcases mem_kpair.1 hz with rfl | rfl
  · intro w hw
    rw [mem_singleton.1 hw]
    exact mem_union.2 (Or.inl ha)
  · intro w hw
    rcases mem_pair.1 hw with rfl | rfl
    · exact mem_union.2 (Or.inl ha)
    · exact mem_union.2 (Or.inr hb)

/-- The **cartesian product** `x × y`: the pairs `⟪a, b⟫` with `a ∈ x`, `b ∈ y`,
separated out of `𝒫(𝒫(x ∪ y))`. -/
noncomputable def prod (x y : ZFSet) : ZFSet :=
  sep (fun z => ∃ a ∈ x, ∃ b ∈ y, z = ⟪a, b⟫) (powerset (powerset (x ∪ y)))

/-- **Members of the cartesian product.** `z ∈ prod x y` iff `z = ⟪a, b⟫` for some
`a ∈ x` and `b ∈ y`. -/
theorem mem_prod {x y z : ZFSet} : z ∈ prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = ⟪a, b⟫ := by
  unfold prod
  rw [mem_sep]
  constructor
  · exact fun h => h.2
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨kpair_mem_powerset_powerset ha hb, a, ha, b, hb, rfl⟩

/-- A pair lies in a product exactly when its components lie in the factors. -/
theorem kpair_mem_prod {x y a b : ZFSet} : ⟪a, b⟫ ∈ prod x y ↔ a ∈ x ∧ b ∈ y := by
  rw [mem_prod]
  constructor
  · rintro ⟨a', ha', b', hb', h⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj.1 h
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl⟩

end ZFSet

end Foundations.Sets
