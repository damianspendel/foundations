import Foundations.Bridges.RatInSets
import Foundations.Numbers.DedekindField

/-!
# The real numbers as a set

Dedekind (*Stetigkeit und irrationale Zahlen*, 1872) defined a real number as a
*cut* in the rationals. In set theory a cut is simply a **subset** of ℚ, so the
set of all real numbers is cut out of the power set `𝒫(ℚ)` by separation:

    ℝ := { A ∈ 𝒫(ℚ) | A is nonempty, A ≠ ℚ, A is downward closed, A has no maximum }.

Here `ℚ` is the ZF set of rationals of `RatInSets` — so a real number is a set of
equivalence classes of pairs of (a set of equivalence classes of pairs of) von
Neumann naturals: a set, made of sets, made ultimately of nothing but `∅`.

We show that this set is in order-preserving bijection with Part II's Dedekind
cuts `Cut` (which are predicates on the *type* `Q`), and hence — composing with
Part II's isomorphism `Cut.isoR` — with Part II's Cauchy reals `R`. Under the
bijection the order of reals becomes **inclusion** of sets, and the addition of
cuts becomes a set-theoretic operation on subsets of ℚ.

We also prove the completeness of the set-theoretic reals in its purest form:
**the least upper bound of a bounded nonempty set of reals is its union.** This is
the deep reason why Dedekind's construction makes completeness easy — the supremum
is not computed but simply collected, by the axiom of union.

So ℝ literally lives in the set-theoretic universe: the "one building" of this
project has the reals on an upper floor of the same house as `∅`.
-/

namespace Foundations.Bridges

open Foundations.Sets Foundations.Sets.ZFSet Foundations.Numbers

/-! ## Dedekind cuts as sets -/

/-- **The Dedekind cut condition**, stated set-theoretically for a subset `A` of the
ZF set ℚ: `A` is inhabited, misses some rational, is downward closed and has no
greatest element (for the set-theoretic order `qlt`). -/
def IsCutSet (A : ZFSet) : Prop :=
  (∃ q, q ∈ A) ∧ (∃ q ∈ QSet, q ∉ A) ∧
  (∀ p ∈ QSet, ∀ q ∈ A, qlt p q → p ∈ A) ∧ (∀ q ∈ A, ∃ r ∈ A, qlt q r)

/-- **The set ℝ** of real numbers: the Dedekind cuts, separated out of `𝒫(ℚ)`. -/
noncomputable def RSet : ZFSet := sep IsCutSet (powerset QSet)

/-- Membership in ℝ. -/
theorem mem_RSet {A : ZFSet} : A ∈ RSet ↔ A ⊆ QSet ∧ IsCutSet A := by
  simp only [RSet, mem_sep, mem_powerset]

/-! ## From Part II's cuts to sets and back -/

/-- The set of (ZF) rationals in the lower part of a Part II cut. -/
noncomputable def cutToSet (C : Cut) : ZFSet := sep (fun x => ∃ q, qToSet q = x ∧ C.lower q) QSet

/-- A rational lies in `cutToSet C` exactly when it lies in the lower part of `C`. -/
theorem qToSet_mem_cutToSet {C : Cut} {q : Q} : qToSet q ∈ cutToSet C ↔ C.lower q := by
  simp only [cutToSet, mem_sep]
  constructor
  · rintro ⟨_, q', hq', hl⟩
    rw [← qToSet_injective hq']
    exact hl
  · intro h
    exact ⟨qToSet_mem q, q, rfl, h⟩

/-- `cutToSet C` is a subset of ℚ. -/
theorem cutToSet_subset (C : Cut) : cutToSet C ⊆ QSet := sep_subset _ _

/-- `cutToSet C` is a real number in the set-theoretic sense. -/
theorem cutToSet_mem (C : Cut) : cutToSet C ∈ RSet := by
  refine mem_RSet.2 ⟨cutToSet_subset C, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := C.nonempty
    exact ⟨qToSet q, qToSet_mem_cutToSet.2 hq⟩
  · obtain ⟨q, hq⟩ := C.bounded
    exact ⟨qToSet q, qToSet_mem q, fun h => hq (qToSet_mem_cutToSet.1 h)⟩
  · intro p hp q hq hpq
    obtain ⟨p, rfl⟩ := qToSet_surj hp
    obtain ⟨q, rfl⟩ := qToSet_surj (cutToSet_subset C hq)
    exact qToSet_mem_cutToSet.2 (C.down (qToSet_mem_cutToSet.1 hq) ((qToSet_lt p q).2 hpq))
  · intro q hq
    obtain ⟨q, rfl⟩ := qToSet_surj (cutToSet_subset C hq)
    obtain ⟨r, hqr, hr⟩ := C.open_ (qToSet_mem_cutToSet.1 hq)
    exact ⟨qToSet r, qToSet_mem_cutToSet.2 hr, (qToSet_lt q r).1 hqr⟩

/-- A set-theoretic real, read back as a Part II cut: `q` is in the lower part iff its
set-theoretic counterpart is a member. -/
noncomputable def setToCut (A : ZFSet) (hA : A ∈ RSet) : Cut where
  lower q := qToSet q ∈ A
  nonempty := by
    obtain ⟨hsub, ⟨x, hx⟩, _⟩ := mem_RSet.1 hA
    obtain ⟨q, rfl⟩ := qToSet_surj (hsub hx)
    exact ⟨q, hx⟩
  bounded := by
    obtain ⟨_, _, ⟨x, hxQ, hx⟩, _⟩ := mem_RSet.1 hA
    obtain ⟨q, rfl⟩ := qToSet_surj hxQ
    exact ⟨q, hx⟩
  down := fun {p q} hq hpq => by
    obtain ⟨_, _, _, hdown, _⟩ := mem_RSet.1 hA
    exact hdown _ (qToSet_mem p) _ hq ((qToSet_lt p q).1 hpq)
  open_ := fun {q} hq => by
    obtain ⟨hsub, _, _, _, hopen⟩ := mem_RSet.1 hA
    obtain ⟨x, hx, hqx⟩ := hopen _ hq
    obtain ⟨r, rfl⟩ := qToSet_surj (hsub hx)
    exact ⟨r, (qToSet_lt q r).2 hqx, hx⟩

/-- Reading a set-theoretic real back and forth returns it. -/
theorem cutToSet_setToCut (A : ZFSet) (hA : A ∈ RSet) : cutToSet (setToCut A hA) = A := by
  apply ext
  intro x
  constructor
  · intro hx
    obtain ⟨q, rfl⟩ := qToSet_surj (cutToSet_subset _ hx)
    exact qToSet_mem_cutToSet.1 hx
  · intro hx
    obtain ⟨q, rfl⟩ := qToSet_surj ((mem_RSet.1 hA).1 hx)
    exact qToSet_mem_cutToSet.2 hx

/-- Reading a Part II cut as a set and back returns it. -/
theorem setToCut_cutToSet (C : Cut) : setToCut (cutToSet C) (cutToSet_mem C) = C :=
  Cut.ext fun _ => qToSet_mem_cutToSet

/-- **The bijection between Part II's cuts and the set ℝ.** -/
noncomputable def cutBij : Bij Cut {A : ZFSet // A ∈ RSet} where
  toFun C := ⟨cutToSet C, cutToSet_mem C⟩
  invFun A := setToCut A.1 A.2
  left_inv := setToCut_cutToSet
  right_inv A := Subtype.ext (cutToSet_setToCut A.1 A.2)

/-- The order of cuts is inclusion of the corresponding sets. -/
theorem cutToSet_le (C D : Cut) : C ≤ D ↔ cutToSet C ⊆ cutToSet D := by
  constructor
  · intro h x hx
    obtain ⟨q, rfl⟩ := qToSet_surj (cutToSet_subset _ hx)
    exact qToSet_mem_cutToSet.2 (h q (qToSet_mem_cutToSet.1 hx))
  · intro h q hq
    exact qToSet_mem_cutToSet.1 (h (qToSet_mem_cutToSet.2 hq))

/-! ## Addition of set-theoretic reals -/

/-- **Addition of set-theoretic reals**: `A + B = {r ∈ ℚ | r < a + b for some a ∈ A, b ∈ B}`,
with the set-theoretic sum and order of ℚ. -/
noncomputable def radd (A B : ZFSet) : ZFSet :=
  sep (fun r => ∃ a ∈ A, ∃ b ∈ B, qlt r (qadd a b)) QSet

/-- The bijection carries the sum of cuts to the set-theoretic sum. -/
theorem cutToSet_add (C D : Cut) : cutToSet (C + D) = radd (cutToSet C) (cutToSet D) := by
  apply ext
  intro x
  simp only [radd, mem_sep]
  constructor
  · intro hx
    obtain ⟨q, rfl⟩ := qToSet_surj (cutToSet_subset _ hx)
    obtain ⟨a, b, ha, hb, h⟩ := qToSet_mem_cutToSet.1 hx
    refine ⟨qToSet_mem q, qToSet a, qToSet_mem_cutToSet.2 ha, qToSet b,
      qToSet_mem_cutToSet.2 hb, ?_⟩
    rw [← qToSet_add, ← qToSet_lt]
    exact h
  · rintro ⟨hx, a', ha, b', hb, h⟩
    obtain ⟨q, rfl⟩ := qToSet_surj hx
    obtain ⟨a, rfl⟩ := qToSet_surj (cutToSet_subset _ ha)
    obtain ⟨b, rfl⟩ := qToSet_surj (cutToSet_subset _ hb)
    rw [← qToSet_add, ← qToSet_lt] at h
    exact qToSet_mem_cutToSet.2 ⟨a, b, qToSet_mem_cutToSet.1 ha, qToSet_mem_cutToSet.1 hb, h⟩

/-! ## Completeness is union -/

/-- **Dedekind completeness, set-theoretically: the supremum is the union.** If `F` is
a nonempty set of reals (members of ℝ) bounded above by some real `M` (in the order
`⊆`), then the union `⋃F` is again a real, it is an upper bound of `F`, and it lies
below every upper bound. The proof uses nothing but the definition of a cut. -/
theorem sup_is_union {F M : ZFSet} (hF : F ⊆ RSet) (hne : ∃ A, A ∈ F) (hM : M ∈ RSet)
    (hbound : ∀ A ∈ F, A ⊆ M) :
    ⋃₀ F ∈ RSet ∧ (∀ A ∈ F, A ⊆ ⋃₀ F) ∧ (∀ M' : ZFSet, (∀ A ∈ F, A ⊆ M') → ⋃₀ F ⊆ M') := by
  refine ⟨?_, fun A hA x hx => mem_sUnion.2 ⟨A, hA, hx⟩,
    fun M' hM' x hx => let ⟨A, hA, hxA⟩ := mem_sUnion.1 hx; hM' A hA hxA⟩
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨_, _, ⟨q₀, hq₀Q, hq₀M⟩, _⟩ := mem_RSet.1 hM
  refine mem_RSet.2 ⟨fun x hx => ?_, ?_, ⟨q₀, hq₀Q, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨A, hA, hxA⟩ := mem_sUnion.1 hx
    exact (mem_RSet.1 (hF hA)).1 hxA
  · obtain ⟨_, ⟨x, hx⟩, _⟩ := mem_RSet.1 (hF hA₀)
    exact ⟨x, mem_sUnion.2 ⟨A₀, hA₀, hx⟩⟩
  · obtain ⟨A, hA, hq⟩ := mem_sUnion.1 h
    exact hq₀M (hbound A hA hq)
  · intro p hp q hq hpq
    obtain ⟨A, hA, hqA⟩ := mem_sUnion.1 hq
    exact mem_sUnion.2 ⟨A, hA, (mem_RSet.1 (hF hA)).2.2.2.1 p hp q hqA hpq⟩
  · intro q hq
    obtain ⟨A, hA, hqA⟩ := mem_sUnion.1 hq
    obtain ⟨r, hr, hqr⟩ := (mem_RSet.1 (hF hA)).2.2.2.2 q hqA
    exact ⟨r, mem_sUnion.2 ⟨A, hA, hr⟩, hqr⟩

/-! ## The Cauchy reals inside the sets -/

/-- The set-theoretic real corresponding to a Part II (Cauchy) real number `x`: the set
of ZF rationals below it. -/
noncomputable def realToSet (x : R) : ZFSet := cutToSet (Cut.ofR x)

/-- **The real numbers live in the set-theoretic universe.** The map from Part II's
real numbers `R` (Cauchy sequences of rationals up to equivalence) to the ZF set `ℝ`
of Dedekind cuts of the ZF rationals, sending `x` to the set of ZF rationals below it,
is a bijection onto the members of `ℝ`; it turns the order of reals into inclusion of
sets and addition into the set-theoretic addition `radd`. The same holds, directly,
for Part II's Dedekind cuts. -/
theorem reals_in_sets :
    Bijective (fun x : R => (⟨realToSet x, cutToSet_mem _⟩ : {A : ZFSet // A ∈ RSet})) ∧
    (∀ x y : R, x ≤ y ↔ realToSet x ⊆ realToSet y) ∧
    (∀ x y : R, realToSet (x + y) = radd (realToSet x) (realToSet y)) ∧
    Bijective cutBij.toFun ∧
    (∀ C D : Cut, C ≤ D ↔ cutToSet C ⊆ cutToSet D) := by
  refine ⟨⟨fun x y h => ?_, fun A => ?_⟩, fun x y => ?_, fun x y => ?_, cutBij.bijective,
    cutToSet_le⟩
  · have := cutBij.injective h
    exact Cut.ofR_inj this
  · obtain ⟨C, hC⟩ := cutBij.bijective.2 A
    refine ⟨Cut.toR C, ?_⟩
    rw [← hC]
    show (⟨cutToSet (Cut.ofR (Cut.toR C)), _⟩ : {A : ZFSet // A ∈ RSet}) = _
    simp only [Cut.ofR_toR]
    rfl
  · rw [Cut.ofR_le, cutToSet_le]; rfl
  · rw [realToSet, Cut.ofR_add, cutToSet_add]; rfl

end Foundations.Bridges
