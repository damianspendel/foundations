import Foundations.Sets.Ordinals
import Foundations.Sets.CardinalOrder

/-!
# Hartogs' theorem: an ordinal beyond every set

Cantor's theorem produces, for every collection, a bigger one — its power set.
But the power set need not be *well-ordered*, and without the axiom of choice we
cannot compare it with other sizes. Hartogs (1915) found a different way up,
which needs no choice at all:

* **Hartogs' theorem.** For every collection `α` there is an ordinal `ℵ(α)` that
  does **not** inject into `α`; indeed `ℵ(α)` is exactly the set of ordinals that
  do inject into `α`, so it is the *least* ordinal that does not.

The idea is to collect all the ways of well-ordering parts of `α`. Each such
well-ordering `R` has an *order type*, an ordinal computed by the "collapse"
`rank R a = {rank R b | b R a}`, which replaces each point by the set of the
(collapsed) points before it, and the order type of `R` is the set of all ranks.
By the replacement axiom the order types of all well-orderings of parts of `α`
form a set, `ℵ(α)`. It is downward closed (an initial segment of a well-ordering
is a well-ordering), so it is an ordinal. Every ordinal `o` that injects into `α`
lies in `ℵ(α)`, since the injection copies the order of `o` onto a part of `α`,
and the collapse of that copy gives back `o` itself. So if `ℵ(α)` injected into
`α`, we would have `ℵ(α) ∈ ℵ(α)` — impossible by foundation.

Instead of well-orderings we use the slightly more general *transitive
well-founded relations*; this costs nothing and spares us from proving totality.

**On choice.** Mathematically the argument makes no choices: it uses only
replacement, power set (in the form "all relations on `α`"), foundation and
classical logic. In this project, however, ZF sets are modelled as a quotient of
pre-sets, and the set-forming operation `ofFamily` (our replacement) picks
representatives with `Classical.choice`; moreover Lean derives excluded middle
from `Classical.choice`. So `#print axioms` on these theorems does list
`Classical.choice` — the goal of a choice-free proof is achieved *at the level of
the mathematics*, but not as a formal axiom check. (The one place below where
we genuinely choose — turning a member of `ℵ(α)` back into an injection — is in
`mem_hartogs_iff`, and is only needed for the "least" part.)

The theorem is stated for `α : Type`, the universe from which our ZF sets draw
their members.
-/

namespace Foundations.Sets

namespace ZFSet

section Rank

variable {α : Type} (R : α → α → Prop) (hR : WellFounded R)

/-- The **rank** (Mostowski collapse) of a point for a well-founded relation:
`rank a = {rank b | b R a}`, defined by well-founded recursion. -/
noncomputable def rank : α → ZFSet :=
  hR.fix (fun a ih => ofFamily (fun b : {b // R b a} => ih b.1 b.2))

/-- The defining equation of the rank. -/
theorem rank_eq (a : α) : rank R hR a = ofFamily (fun b : {b // R b a} => rank R hR b.1) :=
  WellFounded.fix_eq hR _ a

/-- The members of `rank a` are the ranks of the predecessors of `a`. -/
theorem mem_rank {a : α} {z : ZFSet} : z ∈ rank R hR a ↔ ∃ b, R b a ∧ z = rank R hR b := by
  rw [rank_eq, mem_ofFamily]
  exact ⟨fun ⟨b, h⟩ => ⟨b.1, b.2, h⟩, fun ⟨b, hb, h⟩ => ⟨⟨b, hb⟩, h⟩⟩

variable {R} in
/-- For a transitive relation, every rank is a transitive set. -/
theorem rank_isTransitive (htr : ∀ x y z, R x y → R y z → R x z) (a : α) :
    IsTransitive (rank R hR a) := by
  intro y hy z hz
  obtain ⟨b, hba, rfl⟩ := (mem_rank R hR).1 hy
  obtain ⟨c, hcb, rfl⟩ := (mem_rank R hR).1 hz
  exact (mem_rank R hR).2 ⟨c, htr _ _ _ hcb hba, rfl⟩

variable {R} in
/-- For a transitive relation, every rank is an ordinal. -/
theorem rank_isOrdinal (htr : ∀ x y z, R x y → R y z → R x z) (a : α) :
    IsOrdinal (rank R hR a) := by
  refine ⟨rank_isTransitive hR htr a, fun y hy => ?_⟩
  obtain ⟨b, _, rfl⟩ := (mem_rank R hR).1 hy
  exact rank_isTransitive hR htr b

end Rank

/-- A **transitive well-founded relation on a part of `α`**: a "generalised
well-ordering" of part of `α`. -/
structure WFRel (α : Type) where
  /-- The part of `α` that is ordered. -/
  dom : α → Prop
  /-- The (strict) order. -/
  R : α → α → Prop
  /-- The order only relates points of the part. -/
  lives : ∀ x y, R x y → dom x ∧ dom y
  /-- Transitivity. -/
  trans : ∀ x y z, R x y → R y z → R x z
  /-- Well-foundedness. -/
  wf : WellFounded R

variable {α : Type}

/-- The **order type** of a generalised well-ordering: the set of ranks of the
points of its part. -/
noncomputable def WFRel.otype (W : WFRel α) : ZFSet :=
  ofFamily (fun a : {a // W.dom a} => rank W.R W.wf a.1)

/-- Membership in an order type. -/
theorem WFRel.mem_otype {W : WFRel α} {z : ZFSet} :
    z ∈ W.otype ↔ ∃ a, W.dom a ∧ z = rank W.R W.wf a := by
  unfold WFRel.otype
  rw [mem_ofFamily]
  exact ⟨fun ⟨a, h⟩ => ⟨a.1, a.2, h⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩

/-- Order types are ordinals. -/
theorem WFRel.otype_isOrdinal (W : WFRel α) : IsOrdinal W.otype := by
  refine ⟨fun z hz y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨a, _, rfl⟩ := WFRel.mem_otype.1 hz
    obtain ⟨b, hba, rfl⟩ := (mem_rank _ _).1 hy
    exact WFRel.mem_otype.2 ⟨b, (W.lives b a hba).1, rfl⟩
  · obtain ⟨a, _, rfl⟩ := WFRel.mem_otype.1 hz
    exact rank_isTransitive W.wf W.trans a

/-- The **Hartogs ordinal** `ℵ(α)`: the set of order types of all generalised
well-orderings of parts of `α` (a set by replacement). -/
noncomputable def hartogs (α : Type) : ZFSet := ofFamily (fun W : WFRel α => W.otype)

/-- The initial segment below `a` of a generalised well-ordering. -/
def WFRel.below (W : WFRel α) (a : α) : WFRel α where
  dom b := W.R b a
  R x y := W.R x y ∧ W.R y a
  lives _ _ h := ⟨W.trans _ _ _ h.1 h.2, h.2⟩
  trans _ _ _ h₁ h₂ := ⟨W.trans _ _ _ h₁.1 h₂.1, h₂.2⟩
  wf := Subrelation.wf (fun h => h.1) W.wf

/-- Below `a`, ranks in the initial segment agree with ranks in the whole order. -/
theorem WFRel.rank_below (W : WFRel α) (a : α) :
    ∀ b, W.R b a → rank (W.below a).R (W.below a).wf b = rank W.R W.wf b := by
  intro b
  refine W.wf.induction (C := fun b => W.R b a →
    rank (W.below a).R (W.below a).wf b = rank W.R W.wf b) b (fun b ih hb => ?_)
  apply ext
  intro z
  rw [mem_rank, mem_rank]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc.1, ih c hc.1 (W.trans _ _ _ hc.1 hb)⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, ⟨hc, hb⟩, (ih c hc (W.trans _ _ _ hc hb)).symm⟩

/-- The order type of the initial segment below `a` is the rank of `a`. -/
theorem WFRel.otype_below (W : WFRel α) (a : α) : (W.below a).otype = rank W.R W.wf a := by
  apply ext
  intro z
  rw [WFRel.mem_otype, mem_rank]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, W.rank_below a b hb⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, (W.rank_below a b hb).symm⟩

/-- `ℵ(α)` is downward closed: members of members are members. -/
theorem hartogs_isTransitive (α : Type) : IsTransitive (hartogs α) := by
  intro z hz y hy
  obtain ⟨W, rfl⟩ := mem_ofFamily.1 hz
  obtain ⟨a, _, rfl⟩ := WFRel.mem_otype.1 hy
  exact mem_ofFamily.2 ⟨W.below a, (W.otype_below a).symm⟩

/-- **ℵ(α) is an ordinal**: a transitive set of ordinals. -/
theorem hartogs_isOrdinal (α : Type) : IsOrdinal (hartogs α) := by
  refine isOrdinal_of_transitive_of_ordinals (hartogs_isTransitive α) (fun z hz => ?_)
  obtain ⟨W, rfl⟩ := mem_ofFamily.1 hz
  exact W.otype_isOrdinal

/-- An ordinal `o` that injects into `α` lies in `ℵ(α)`: copy the order of `o` onto
a part of `α`; the order type of the copy is `o` again. -/
theorem mem_hartogs_of_injective {o : ZFSet} (ho : IsOrdinal o) {j : {z // z ∈ o} → α}
    (hj : Function.Injective j) : o ∈ hartogs α := by
  -- the copied order
  let W : WFRel α :=
    { dom := fun x => ∃ z, j z = x
      R := fun x y => ∃ z w, j z = x ∧ j w = y ∧ z.1 ∈ w.1
      lives := fun x y ⟨z, w, hz, hw, _⟩ => ⟨⟨z, hz⟩, ⟨w, hw⟩⟩
      trans := fun x y u ⟨z, w, hz, hw, hzw⟩ ⟨w', v, hw', hv, hwv⟩ => by
        have : w = w' := hj (hw.trans hw'.symm)
        subst this
        exact ⟨z, v, hz, hv, (ho.mem v.2).mem_trans hzw hwv⟩
      wf := by
        have key : ∀ z : ZFSet, ∀ hz : z ∈ o,
            Acc (fun x y => ∃ z w, j z = x ∧ j w = y ∧ z.1 ∈ w.1) (j ⟨z, hz⟩) := by
          refine mem_induction _ (fun z ih hz => ⟨_, fun y ⟨z', w, hz', hw, hzw⟩ => ?_⟩)
          have : w = ⟨z, hz⟩ := hj hw
          subst this
          subst hz'
          exact ih z'.1 hzw z'.2
        refine ⟨fun x => ⟨_, fun y ⟨z', w, hz', hw, _⟩ => ?_⟩⟩
        subst hz'
        exact key z'.1 z'.2 }
  -- the rank of the copy of `z` is `z`
  have hrank : ∀ z : ZFSet, ∀ hz : z ∈ o, rank W.R W.wf (j ⟨z, hz⟩) = z := by
    refine mem_induction _ (fun z ih hz => ext fun u => ?_)
    rw [mem_rank]
    constructor
    · rintro ⟨b, ⟨z', w, rfl, hw, hzw⟩, rfl⟩
      have : w = ⟨z, hz⟩ := hj hw
      subst this
      rw [ih z'.1 hzw z'.2]
      exact hzw
    · intro hu
      have hu' : u ∈ o := ho.1 z hz hu
      exact ⟨j ⟨u, hu'⟩, ⟨⟨u, hu'⟩, ⟨z, hz⟩, rfl, rfl, hu⟩, (ih u hu hu').symm⟩
  have hot : W.otype = o := by
    apply ext
    intro u
    rw [WFRel.mem_otype]
    constructor
    · rintro ⟨a, ⟨z, rfl⟩, rfl⟩
      rw [hrank z.1 z.2]
      exact z.2
    · intro hu
      exact ⟨j ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, (hrank u hu).symm⟩
  exact mem_ofFamily.2 ⟨W, hot.symm⟩

/-- **ℵ(α) does not inject into α.** Otherwise `ℵ(α) ∈ ℵ(α)`, against foundation. -/
theorem hartogs_not_injective (α : Type) :
    ¬ ∃ f : {z // z ∈ hartogs α} → α, Function.Injective f := by
  rintro ⟨f, hf⟩
  exact mem_irrefl _ (mem_hartogs_of_injective (hartogs_isOrdinal α) hf)

/-- The ordinals in `ℵ(α)` are exactly the ordinals that inject into `α`. -/
theorem mem_hartogs_iff {o : ZFSet} (ho : IsOrdinal o) :
    o ∈ hartogs α ↔ ∃ f : {z // z ∈ o} → α, Function.Injective f := by
  refine ⟨fun h => ?_, fun ⟨f, hf⟩ => mem_hartogs_of_injective ho hf⟩
  obtain ⟨W, rfl⟩ := mem_ofFamily.1 h
  have hpt : ∀ z : {z // z ∈ W.otype}, ∃ a, W.dom a ∧ z.1 = rank W.R W.wf a :=
    fun z => WFRel.mem_otype.1 z.2
  refine ⟨fun z => Classical.choose (hpt z), fun z z' hzz' => Subtype.ext ?_⟩
  rw [(Classical.choose_spec (hpt z)).2, (Classical.choose_spec (hpt z')).2]
  simp only at hzz'
  rw [hzz']

/-- **Hartogs' theorem.** For every type `α` there is an ordinal `h` that does not
inject into `α`, and it is the least such: an ordinal `o` lies in `h` exactly when
`o` injects into `α`, and every ordinal not injecting into `α` contains or equals `h`.
(The construction makes no choices; see the module docstring for what
`#print axioms` reports.) -/
theorem hartogs_theorem (α : Type) :
    ∃ h, IsOrdinal h ∧ (¬ ∃ f : {z // z ∈ h} → α, Function.Injective f) ∧
      (∀ o, IsOrdinal o → (o ∈ h ↔ ∃ f : {z // z ∈ o} → α, Function.Injective f)) ∧
      (∀ o, IsOrdinal o → (¬ ∃ f : {z // z ∈ o} → α, Function.Injective f) → h = o ∨ h ∈ o) := by
  refine ⟨hartogs α, hartogs_isOrdinal α, hartogs_not_injective α,
    fun o ho => mem_hartogs_iff ho, fun o ho hno => ?_⟩
  rcases ordinal_trichotomy (hartogs_isOrdinal α) ho with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd ((mem_hartogs_iff ho).1 h) hno

/-- **Hartogs' theorem, type form.** For every type `α` there is a well-ordered type
(a strict, total, well-founded order) that does not inject into `α`. -/
theorem exists_wellOrdered_not_le (α : Type) :
    ∃ (H : Type 1) (lt : H → H → Prop), (∀ x y z, lt x y → lt y z → lt x z) ∧
      (∀ x y, lt x y ∨ x = y ∨ lt y x) ∧ WellFounded lt ∧ ¬ CardLE H α := by
  refine ⟨{z // z ∈ hartogs α}, fun x y => x.1 ∈ y.1, fun x y z hxy hyz => ?_,
    fun x y => ?_, ?_, hartogs_not_injective α⟩
  · exact ((hartogs_isOrdinal α).mem z.2).mem_trans hxy hyz
  · rcases ordinal_trichotomy ((hartogs_isOrdinal α).mem x.2) ((hartogs_isOrdinal α).mem y.2)
      with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h)
  · have key : ∀ z : ZFSet, ∀ hz : z ∈ hartogs α,
        Acc (fun x y : {z // z ∈ hartogs α} => x.1 ∈ y.1) ⟨z, hz⟩ :=
      mem_induction _ (fun z ih hz => ⟨_, fun y hy => ih y.1 hy y.2⟩)
    exact ⟨fun x => key x.1 x.2⟩

end ZFSet

end Foundations.Sets
