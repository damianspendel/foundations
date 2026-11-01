import Foundations.Sets.PSet

/-!
# ZF sets and the axioms of Zermelo–Fraenkel set theory

We now pass from *presentations* of sets to sets themselves. A `ZFSet` is an
equivalence class of pre-sets under extensional equivalence: two pre-sets that
have the same members are identified. In philosophical terms, the quotient is
what turns the intensional notion "a way of listing members" into the
extensional notion "a collection, individuated by its members alone".

Membership descends to the quotient because it respects equivalence (proved in
`PSet`). From then on we never look at presentations again, except in two
places:

* **The family principle** `mem_ofFamily`: for any index type `α : Type` and any
  family `f : α → ZFSet` there is a set whose members are exactly the values
  `f a`. Every set-forming operation of ZF — empty set, pairing, union, power set,
  separation, replacement, the infinite set — is obtained from this one
  principle by choosing a suitable index type. (Choosing representatives of the
  `f a` uses the axiom of choice of the ambient logic; this is harmless and
  keeps every construction a one-liner.)
* **∈-induction** `mem_induction`: since pre-sets are built in well-founded
  stages, so are sets; this is the axiom of foundation (regularity).

The axioms of ZF then become *theorems* about this model:
extensionality, empty set, pairing, union, power set, separation, replacement,
infinity and foundation. That the model satisfies them is what justifies
calling `ZFSet` "the universe of sets" in the rest of the project.
-/

namespace Foundations.Sets

open PSet

/-- **The universe of sets.** A ZF set is an equivalence class of pre-sets under
extensional equivalence. It lives in `Type 1`, because its members are indexed by
small types in `Type`. -/
def ZFSet : Type 1 := Quotient PSet.setoid

namespace ZFSet

/-- The set presented by a pre-set. -/
def mk (x : PSet) : ZFSet := Quotient.mk _ x

/-- Two pre-sets present the same set exactly when they are extensionally equivalent. -/
theorem mk_eq_mk {x y : PSet} : mk x = mk y ↔ PSet.Equiv x y :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- Every set is presented by some pre-set: to prove a property of all sets it
suffices to prove it for all presented sets `mk x`. -/
theorem ind {P : ZFSet → Prop} (h : ∀ x, P (mk x)) (s : ZFSet) : P s :=
  Quotient.ind h s

/-- A chosen presentation of a set (uses the axiom of choice). -/
noncomputable def out (s : ZFSet) : PSet := Classical.choose (Quotient.exists_rep s)

/-- The chosen presentation presents the set it was chosen for. -/
@[simp] theorem mk_out (s : ZFSet) : mk s.out = s :=
  Classical.choose_spec (Quotient.exists_rep s)

/-- Membership of sets, lifted from pre-sets. Well defined because pre-set
membership respects extensional equivalence. -/
protected def Mem (t s : ZFSet) : Prop :=
  Quotient.lift₂ (fun (y x : PSet) => x ∈ y)
    (fun _ _ _ _ hy hx => propext (PSet.mem_congr hx hy)) t s

/-- Set membership `x ∈ y`. -/
instance : Membership ZFSet ZFSet := ⟨ZFSet.Mem⟩

/-- Membership of presented sets is membership of the presentations. -/
@[simp] theorem mk_mem_mk {x y : PSet} : mk x ∈ mk y ↔ x ∈ y := Iff.rfl

/-- The members of a presented set `mk ⟨α, A⟩` are exactly the sets `mk (A a)`. -/
theorem mem_mk {z : ZFSet} {α : Type} {A : α → PSet} :
    z ∈ mk (PSet.mk α A) ↔ ∃ a, z = mk (A a) := by
  induction z using ind with
  | h z =>
    simp only [mk_mem_mk, PSet.mem_iff, mk_eq_mk]
    exact Iff.rfl

/-- Subset: every member of `x` is a member of `y`. -/
instance : HasSubset ZFSet := ⟨fun x y => ∀ ⦃z⦄, z ∈ x → z ∈ y⟩

/-- Unfolding `⊆`. -/
theorem subset_def {x y : ZFSet} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y := Iff.rfl

/-- Every set is a subset of itself. -/
theorem subset_refl (x : ZFSet) : x ⊆ x := fun _ h => h

/-- `⊆` is transitive. -/
theorem subset_trans {x y z : ZFSet} (h₁ : x ⊆ y) (h₂ : y ⊆ z) : x ⊆ z :=
  fun _ h => h₂ (h₁ h)

/-! ## Extensionality -/

/-- **Axiom of extensionality.** Sets with the same members are equal. -/
theorem ext {x y : ZFSet} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  induction x using ind with
  | h x =>
    induction y using ind with
    | h y => exact Quotient.sound (PSet.equiv_of_mem_iff fun z => h (mk z))

/-- Extensionality as an equivalence: sets are equal iff they have the same members. -/
theorem ext_iff {x y : ZFSet} : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y :=
  ⟨fun h _ => h ▸ Iff.rfl, ext⟩

/-- Mutual inclusion implies equality. -/
theorem subset_antisymm {x y : ZFSet} (h₁ : x ⊆ y) (h₂ : y ⊆ x) : x = y :=
  ext fun _ => ⟨fun h => h₁ h, fun h => h₂ h⟩

/-! ## The family principle -/

/-- The set of values of a family: for `f : α → ZFSet` (with `α : Type`), the set
`{f a | a : α}`. This is the single construction from which all others follow. -/
noncomputable def ofFamily {α : Type} (f : α → ZFSet) : ZFSet :=
  mk (PSet.mk α fun a => (f a).out)

/-- **The family principle.** The members of `ofFamily f` are exactly the values of `f`. -/
@[simp] theorem mem_ofFamily {α : Type} {f : α → ZFSet} {z : ZFSet} :
    z ∈ ofFamily f ↔ ∃ a, z = f a := by
  simp only [ofFamily, mem_mk, mk_out]

/-- The index type of a set: the labels of its members in the chosen presentation. -/
def Idx (s : ZFSet) : Type := s.out.Ix

/-- The member of `s` with label `i`. -/
noncomputable def elt (s : ZFSet) (i : s.Idx) : ZFSet := mk (s.out.Func i)

/-- The members of `s` are exactly the sets `elt s i`. -/
theorem mem_iff_elt {s z : ZFSet} : z ∈ s ↔ ∃ i, z = s.elt i := by
  have key : ∀ p : PSet, z ∈ mk p ↔ ∃ i, z = mk (p.Func i) := by
    intro p
    cases p with
    | mk α A => exact mem_mk
  have := key s.out
  rw [mk_out] at this
  exact this

/-- Each `elt s i` is a member of `s`. -/
theorem elt_mem (s : ZFSet) (i : s.Idx) : s.elt i ∈ s := mem_iff_elt.2 ⟨i, rfl⟩

/-- Every set is the set of values of its own family of members. -/
theorem ofFamily_elt (s : ZFSet) : ofFamily s.elt = s :=
  ext fun z => by rw [mem_ofFamily, mem_iff_elt]

/-! ## Empty set -/

/-- The empty set, indexed by the empty type. -/
noncomputable def empty : ZFSet := ofFamily (Empty.elim : Empty → ZFSet)

/-- Notation `∅` for the empty set. -/
noncomputable instance : EmptyCollection ZFSet := ⟨empty⟩

/-- Nothing is a member of the empty set. -/
@[simp] theorem not_mem_empty (z : ZFSet) : z ∉ (∅ : ZFSet) := by
  show ¬ z ∈ ofFamily _
  rw [mem_ofFamily]
  rintro ⟨e, _⟩
  exact e.elim

/-- **Axiom of the empty set.** There is a set with no members. -/
theorem empty_set_axiom : ∃ e : ZFSet, ∀ z, z ∉ e := ⟨∅, not_mem_empty⟩

/-- A set without members is the empty set. -/
theorem eq_empty_of_forall_not_mem {x : ZFSet} (h : ∀ z, z ∉ x) : x = ∅ :=
  ext fun z => ⟨fun hz => absurd hz (h z), fun hz => absurd hz (not_mem_empty z)⟩

/-- The empty set is a subset of every set. -/
theorem empty_subset (x : ZFSet) : ∅ ⊆ x := fun z h => absurd h (not_mem_empty z)

/-! ## Insertion, singletons and pairs -/

/-- `insert a s` is the set `s ∪ {a}`, indexed by `Option` of the labels of `s`. -/
noncomputable def insert' (a s : ZFSet) : ZFSet :=
  ofFamily (fun o : Option s.Idx => o.elim a s.elt)

/-- Notation `insert a s` (and hence `{a, b, c}`). -/
noncomputable instance : Insert ZFSet ZFSet := ⟨insert'⟩

/-- Members of `insert a s`: `a` itself, and the members of `s`. -/
@[simp] theorem mem_insert {a s z : ZFSet} : z ∈ insert a s ↔ z = a ∨ z ∈ s := by
  show z ∈ ofFamily _ ↔ _
  rw [mem_ofFamily, mem_iff_elt]
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some i, rfl⟩

/-- The singleton `{a}`, indexed by the one-element type. -/
noncomputable def singleton' (a : ZFSet) : ZFSet := ofFamily (fun _ : Unit => a)

/-- Notation `{a}`. -/
noncomputable instance : Singleton ZFSet ZFSet := ⟨singleton'⟩

/-- The only member of `{a}` is `a`. -/
@[simp] theorem mem_singleton {a z : ZFSet} : z ∈ ({a} : ZFSet) ↔ z = a := by
  show z ∈ ofFamily _ ↔ _
  rw [mem_ofFamily]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

/-- The members of the pair `{a, b}` are `a` and `b`. -/
theorem mem_pair {a b z : ZFSet} : z ∈ ({a, b} : ZFSet) ↔ z = a ∨ z = b := by
  simp

/-- **Axiom of pairing.** For any `a`, `b` there is a set whose members are exactly `a` and `b`. -/
theorem pairing (a b : ZFSet) : ∃ p : ZFSet, ∀ z, z ∈ p ↔ z = a ∨ z = b :=
  ⟨{a, b}, fun _ => mem_pair⟩

/-! ## Union -/

/-- The union `⋃₀ s` of all members of `s`, indexed by pairs (label of a member,
label of a member of that member). -/
noncomputable def sUnion (s : ZFSet) : ZFSet :=
  ofFamily (fun p : (Σ i : s.Idx, (s.elt i).Idx) => (s.elt p.1).elt p.2)

/-- Notation `⋃₀ s` for the union of a set of sets. -/
prefix:110 "⋃₀ " => sUnion

/-- Members of `⋃₀ s` are the members of members of `s`. -/
@[simp] theorem mem_sUnion {s z : ZFSet} : z ∈ ⋃₀ s ↔ ∃ y ∈ s, z ∈ y := by
  unfold sUnion
  rw [mem_ofFamily]
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨s.elt i, elt_mem s i, elt_mem _ j⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨i, rfl⟩ := mem_iff_elt.1 hy
    obtain ⟨j, rfl⟩ := mem_iff_elt.1 hz
    exact ⟨⟨i, j⟩, rfl⟩

/-- **Axiom of union.** For every set `s` there is a set whose members are exactly
the members of members of `s`. -/
theorem union_axiom (s : ZFSet) : ∃ u : ZFSet, ∀ z, z ∈ u ↔ ∃ y ∈ s, z ∈ y :=
  ⟨⋃₀ s, fun _ => mem_sUnion⟩

/-- Binary union `x ∪ y := ⋃₀ {x, y}`. -/
noncomputable instance : Union ZFSet := ⟨fun x y => ⋃₀ {x, y}⟩

/-- Members of `x ∪ y` are the members of `x` and the members of `y`. -/
@[simp] theorem mem_union {x y z : ZFSet} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  show z ∈ ⋃₀ {x, y} ↔ _
  rw [mem_sUnion]
  constructor
  · rintro ⟨w, hw, hz⟩
    rcases mem_pair.1 hw with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (h | h)
    · exact ⟨x, mem_pair.2 (Or.inl rfl), h⟩
    · exact ⟨y, mem_pair.2 (Or.inr rfl), h⟩

/-! ## Power set -/

/-- The power set: indexed by predicates on the labels of `s`; the predicate `p`
gives the subset `{elt s i | p i}`. -/
noncomputable def powerset (s : ZFSet) : ZFSet :=
  ofFamily (fun p : s.Idx → Prop => ofFamily (fun j : {i // p i} => s.elt j.1))

/-- Members of the power set of `s` are exactly the subsets of `s`. -/
@[simp] theorem mem_powerset {s z : ZFSet} : z ∈ powerset s ↔ z ⊆ s := by
  unfold powerset
  rw [mem_ofFamily]
  constructor
  · rintro ⟨p, rfl⟩ w hw
    obtain ⟨j, rfl⟩ := mem_ofFamily.1 hw
    exact elt_mem s j.1
  · intro h
    refine ⟨fun i => s.elt i ∈ z, ext fun w => ?_⟩
    rw [mem_ofFamily]
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := mem_iff_elt.1 (h hw)
      exact ⟨⟨i, hw⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.2

/-- **Axiom of power set.** For every set `s` there is a set whose members are
exactly the subsets of `s`. -/
theorem powerset_axiom (s : ZFSet) : ∃ p : ZFSet, ∀ z, z ∈ p ↔ z ⊆ s :=
  ⟨powerset s, fun _ => mem_powerset⟩

/-! ## Separation -/

/-- Separation `{z ∈ s | P z}`: indexed by the labels of members satisfying `P`.
On the quotient, *every* predicate respects equality of sets, so no definability
restriction is needed. -/
noncomputable def sep (P : ZFSet → Prop) (s : ZFSet) : ZFSet :=
  ofFamily (fun j : {i : s.Idx // P (s.elt i)} => s.elt j.1)

/-- Members of `sep P s` are the members of `s` satisfying `P`. -/
@[simp] theorem mem_sep {P : ZFSet → Prop} {s z : ZFSet} : z ∈ sep P s ↔ z ∈ s ∧ P z := by
  unfold sep
  rw [mem_ofFamily]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨elt_mem s j.1, j.2⟩
  · rintro ⟨hz, hP⟩
    obtain ⟨i, rfl⟩ := mem_iff_elt.1 hz
    exact ⟨⟨i, hP⟩, rfl⟩

/-- **Axiom schema of separation.** For every set `s` and every property `P` of
sets there is a set whose members are exactly the members of `s` having `P`. -/
theorem separation (P : ZFSet → Prop) (s : ZFSet) :
    ∃ t : ZFSet, ∀ z, z ∈ t ↔ z ∈ s ∧ P z :=
  ⟨sep P s, fun _ => mem_sep⟩

/-- A separated set is a subset of the original. -/
theorem sep_subset (P : ZFSet → Prop) (s : ZFSet) : sep P s ⊆ s := fun _ h => (mem_sep.1 h).1

/-! ## Replacement -/

/-- The image `{f z | z ∈ s}` of a set under an arbitrary operation `f`. -/
noncomputable def image (f : ZFSet → ZFSet) (s : ZFSet) : ZFSet := ofFamily (fun i => f (s.elt i))

/-- Members of `image f s` are the values `f z` for `z ∈ s`. -/
@[simp] theorem mem_image {f : ZFSet → ZFSet} {s y : ZFSet} :
    y ∈ image f s ↔ ∃ z ∈ s, f z = y := by
  unfold image
  rw [mem_ofFamily]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨s.elt i, elt_mem s i, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨i, rfl⟩ := mem_iff_elt.1 hz
    exact ⟨i, rfl⟩

/-- **Axiom schema of replacement.** The image of a set under any operation on sets
is again a set. -/
theorem replacement (f : ZFSet → ZFSet) (s : ZFSet) :
    ∃ t : ZFSet, ∀ y, y ∈ t ↔ ∃ z ∈ s, f z = y :=
  ⟨image f s, fun _ => mem_image⟩

/-- **Replacement for functional relations.** If a relation `R` assigns to each
member of `s` exactly one set, then the collection of all assigned sets is a set.
This is the textbook form of the replacement schema. -/
theorem replacement_rel (R : ZFSet → ZFSet → Prop) (s : ZFSet)
    (hR : ∀ z ∈ s, ∃ y, R z y ∧ ∀ y', R z y' → y' = y) :
    ∃ t : ZFSet, ∀ y, y ∈ t ↔ ∃ z ∈ s, R z y := by
  classical
  let f : ZFSet → ZFSet := fun z => if h : z ∈ s then Classical.choose (hR z h) else ∅
  refine ⟨image f s, fun y => ?_⟩
  rw [mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    simp only [f, hz, dite_true]
    exact (Classical.choose_spec (hR z hz)).1
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, hz, ?_⟩
    simp only [f, hz, dite_true]
    exact ((Classical.choose_spec (hR z hz)).2 y hzy).symm

/-! ## Foundation (regularity) -/

/-- **∈-induction (axiom of foundation).** If a property holds of a set whenever
it holds of all its members, then it holds of every set. This reflects the
well-founded, stage-by-stage construction of pre-sets. -/
theorem mem_induction (P : ZFSet → Prop) (h : ∀ x, (∀ y ∈ x, P y) → P x) : ∀ x, P x := by
  intro x
  induction x using ind with
  | h p =>
    induction p with
    | mk α A ih =>
      apply h
      intro y hy
      obtain ⟨a, rfl⟩ := mem_mk.1 hy
      exact ih a

/-- **No set is a member of itself.** A consequence of foundation. -/
theorem mem_irrefl (x : ZFSet) : x ∉ x :=
  mem_induction (fun x => x ∉ x) (fun x ih hx => ih x hx hx) x

/-- **No 2-cycles of membership**: never both `x ∈ y` and `y ∈ x`. -/
theorem mem_asymm {x y : ZFSet} (hxy : x ∈ y) : y ∉ x := by
  have key : ∀ x : ZFSet, ∀ y, x ∈ y → y ∉ x := by
    refine mem_induction (fun x => ∀ y, x ∈ y → y ∉ x) (fun x ih => ?_)
    intro y hxy hyx
    exact ih y hyx x hyx hxy
  exact key x y hxy

/-- **Regularity, in its classical form.** Every non-empty set `x` has an
∈-minimal member: some `y ∈ x` sharing no member with `x`. -/
theorem regularity (x : ZFSet) (hx : ∃ z, z ∈ x) : ∃ y ∈ x, ∀ z ∈ y, z ∉ x := by
  apply Classical.byContradiction
  intro hne
  have key : ∀ y, y ∉ x := by
    refine mem_induction (fun y => y ∉ x) (fun y ih hy => hne ⟨y, hy, fun z hz hzx => ?_⟩)
    exact ih z hz hzx
  obtain ⟨z, hz⟩ := hx
  exact key z hz

/-! ## Infinity -/

/-- The successor `x ∪ {x}` of a set, written `insert x x`. -/
noncomputable def succ (x : ZFSet) : ZFSet := insert x x

/-- Members of `succ x` are `x` itself and the members of `x`. -/
@[simp] theorem mem_succ {x z : ZFSet} : z ∈ succ x ↔ z = x ∨ z ∈ x := mem_insert

/-- Every set is a member of its successor. -/
theorem mem_succ_self (x : ZFSet) : x ∈ succ x := mem_succ.2 (Or.inl rfl)

/-- The **von Neumann natural numbers** as sets: `0 = ∅` and `n + 1 = n ∪ {n}`. -/
noncomputable def vn : Nat → ZFSet
  | 0 => ∅
  | n + 1 => succ (vn n)

/-- `vn 0` is the empty set. -/
@[simp] theorem vn_zero : vn 0 = ∅ := rfl

/-- `vn (n + 1)` is the successor of `vn n`. -/
@[simp] theorem vn_succ (n : Nat) : vn (n + 1) = succ (vn n) := rfl

/-- The set `ω` of all von Neumann naturals, obtained from the family `vn` indexed
by Lean's natural numbers. -/
noncomputable def omega : ZFSet := ofFamily vn

/-- Notation `ω` for the set of von Neumann naturals. -/
notation "ω" => ZFSet.omega

/-- Members of `ω` are exactly the von Neumann naturals. -/
theorem mem_omega {x : ZFSet} : x ∈ ω ↔ ∃ n, x = vn n := mem_ofFamily

/-- **Axiom of infinity.** There is a set containing `∅` and closed under `x ↦ x ∪ {x}`. -/
theorem infinity : ∃ w : ZFSet, ∅ ∈ w ∧ ∀ x ∈ w, succ x ∈ w := by
  refine ⟨ω, mem_omega.2 ⟨0, rfl⟩, fun x hx => ?_⟩
  obtain ⟨n, rfl⟩ := mem_omega.1 hx
  exact mem_omega.2 ⟨n + 1, rfl⟩

end ZFSet

end Foundations.Sets
