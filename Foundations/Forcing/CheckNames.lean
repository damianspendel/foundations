import Foundations.Forcing.BSetModel
import Foundations.Sets.ZFSet

/-!
# Check names: the ground model inside `V^B`

Every ordinary set `x` has a canonical name `x̌` in the Boolean-valued universe: list the
check names of its members, each with degree `⊤`. Through this embedding the ground model
`V` sits inside `V^B`. It is faithful and two-valued:

* `⟦x̌ = y̌⟧` is `⊤` if `x = y` and `⊥` otherwise (`eq_zcheck_of_eq`, `eq_zcheck_of_ne`);
* `⟦x̌ ∈ y̌⟧` is `⊤` if `x ∈ y` and `⊥` otherwise (`mem_zcheck_of_mem`, `mem_zcheck_of_not_mem`).

The values are genuinely different as soon as `B` is non-degenerate (`⊤ ≠ ⊥`). For the Cohen
algebra this is `cohen_top_ne_bot`. Then `⟦x̌ = y̌⟧ = ⊤ ↔ x = y` and `⟦x̌ ∈ y̌⟧ = ⊤ ↔ x ∈ y`
(`eq_zcheck_eq_top_iff`, `mem_zcheck_eq_top_iff`).

The check map is defined on Aczel's pre-sets `PSet` by structural recursion and transferred
to the quotient `ZFSet` through chosen representatives. Equivalent pre-sets have
Boolean-equal check names, so the choice does not matter.

This file also proves two general facts about names used later: Boolean equality *is*
Boolean coextensionality (`eq_eq_iInf_biimp`), and the pairing construction respects
Boolean equality (`pair_congr`, `opair_congr`).
-/

namespace Foundations.Forcing

open CBA Foundations.Sets

attribute [local instance] Classical.propDecidable

variable {B : Type} [CompleteBooleanAlgebra B]

namespace BSet

/-! ### Equality is coextensionality; pairs respect equality -/

/-- **Boolean equality is coextensionality.** `⟦x = y⟧ = ⨅_z (⟦z ∈ x⟧ ⇔ ⟦z ∈ y⟧)`. -/
theorem eq_eq_iInf_biimp (x y : BSet B) : eq x y = iInf fun z => (mem z x ⇔ mem z y) :=
  le_antisymm'
    (le_iInf fun z => le_inf _ _ _ (le_himp_iff.2 (mem_congr_right z x y))
      (le_himp_iff.2 (le_trans' (inf_le_inf (eq_symm x y) le_rfl) (mem_congr_right z y x))))
    (iInf_biimp_le_eq x y)

/-- `a ⊔ a = a`. -/
theorem sup_idem' (a : B) : a ⊔ a = a := le_antisymm' (sup_le _ _ _ le_rfl le_rfl) (le_sup_left _ _)

/-- **Pairs respect equality.** `⟦a = a'⟧ ⊓ ⟦b = b'⟧ ≤ ⟦{a, b} = {a', b'}⟧`. -/
theorem pair_congr (a a' b b' : BSet B) : eq a a' ⊓ eq b b' ≤ eq (pair a b) (pair a' b') := by
  rw [eq_eq_iInf_biimp (pair a b)]
  refine le_iInf fun w => ?_
  rw [BSet.mem_pair, BSet.mem_pair]
  refine le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_)
  · refine le_trans' (inf_sup_le _ _ _) (sup_le_sup ?_ ?_)
    · exact le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (eq_trans w a a')
    · exact le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (eq_trans w b b')
  · refine le_trans' (inf_sup_le _ _ _) (sup_le_sup ?_ ?_)
    · exact le_trans' (le_inf _ _ _ (by lattice_le)
        (inf_le_of_left_le (inf_le_of_left_le (eq_symm a a')))) (eq_trans w a' a)
    · exact le_trans' (le_inf _ _ _ (by lattice_le)
        (inf_le_of_left_le (inf_le_of_right_le (eq_symm b b')))) (eq_trans w b' b)

/-- The **Kuratowski ordered pair** of names, `(a, b) = {{a, a}, {a, b}}`. -/
def opair (a b : BSet B) : BSet B := pair (pair a a) (pair a b)

/-- Ordered pairs respect equality. -/
theorem opair_congr (a a' b b' : BSet B) : eq a a' ⊓ eq b b' ≤ eq (opair a b) (opair a' b') :=
  le_trans' (le_inf _ _ _ (le_trans' (le_inf _ _ _ (inf_le_left _ _) (inf_le_left _ _))
      (pair_congr a a' a a')) (pair_congr a a' b b'))
    (pair_congr _ _ _ _)

/-! ### Two-valued families -/

/-- A join of a family each of whose values is `⊤` or `⊥` is `⊤` as soon as one value is. -/
theorem iSup_eq_top_of {ι : Sort _} {f : ι → B} (i : ι) (h : f i = ⊤) : iSup f = ⊤ :=
  eq_top_iff.2 (le_iSup_of_le i (h ▸ le_rfl))

/-- A join of `⊥`s is `⊥`. -/
theorem iSup_eq_bot_of {ι : Sort _} {f : ι → B} (h : ∀ i, f i = ⊥) : iSup f = ⊥ :=
  eq_bot_iff.2 (iSup_le fun i => (h i) ▸ le_rfl)

end BSet

/-! ### Check names of pre-sets -/

/-- The **check name** `x̌` of a pre-set: its members' check names, each with degree `⊤`. -/
def check : PSet → BSet B
  | ⟨α, A⟩ => .mk α (fun a => check (A a)) (fun _ => ⊤)

/-- Unfolding `check` on an arbitrary pre-set. -/
theorem check_def (x : PSet) :
    (check x : BSet B) = .mk x.Ix (fun i => check (x.Func i)) (fun _ => ⊤) := by
  cases x; rfl

/-- **Check names are two-valued and faithful for equality.** Equivalent pre-sets have
check names equal with value `⊤`, inequivalent ones with value `⊥`. -/
theorem eq_check (x y : PSet) :
    (PSet.Equiv x y → BSet.eq (check x : BSet B) (check y) = ⊤) ∧
    (¬ PSet.Equiv x y → BSet.eq (check x : BSet B) (check y) = ⊥) := by
  induction x generalizing y with
  | mk α A ih =>
    cases y with
    | mk β C =>
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := PSet.equiv_iff.1 h
        apply eq_top_iff.2
        apply BSet.le_eq_of
        · intro i
          obtain ⟨j, hj⟩ := h1 i
          exact le_iSup_of_le j (by
            show _ ≤ ⊤ ⊓ BSet.eq (check (A i)) (check (C j))
            rw [(ih i (C j)).1 hj]; lattice_le)
        · intro j
          obtain ⟨i, hi⟩ := h2 j
          exact le_iSup_of_le i (by
            show _ ≤ ⊤ ⊓ BSet.eq (check (A i)) (check (C j))
            rw [(ih i (C j)).1 hi]; lattice_le)
      · intro h
        apply eq_bot_iff.2
        rw [PSet.equiv_iff] at h
        by_cases h1 : ∀ a, ∃ b, PSet.Equiv (A a) (C b)
        · have h2 : ¬ ∀ b, ∃ a, PSet.Equiv (A a) (C b) := fun h2 => h ⟨h1, h2⟩
          obtain ⟨j, hj⟩ : ∃ b, ¬ ∃ a, PSet.Equiv (A a) (C b) := Classical.byContradiction fun hn => h2 fun b =>
            Classical.byContradiction fun hb => hn ⟨b, hb⟩
          have : BSet.eq (check (.mk α A) : BSet B) (check (.mk β C)) ⊓ ⊤ ≤
              iSup fun i => ⊤ ⊓ BSet.eq (check (A i)) (check (C j)) :=
            BSet.eq_inf_bval_right (check (.mk α A) : BSet B) (check (.mk β C)) j
          rw [inf_top] at this
          refine le_trans' this (iSup_le fun i => inf_le_of_right_le ?_)
          exact ((ih i (C j)).2 fun e => hj ⟨i, e⟩) ▸ le_rfl
        · obtain ⟨i, hi⟩ : ∃ a, ¬ ∃ b, PSet.Equiv (A a) (C b) := Classical.byContradiction fun hn => h1 fun a =>
            Classical.byContradiction fun ha => hn ⟨a, ha⟩
          have : BSet.eq (check (.mk α A) : BSet B) (check (.mk β C)) ⊓ ⊤ ≤
              iSup fun j => ⊤ ⊓ BSet.eq (check (A i)) (check (C j)) :=
            BSet.eq_inf_bval_left (check (.mk α A) : BSet B) (check (.mk β C)) i
          rw [inf_top] at this
          refine le_trans' this (iSup_le fun j => inf_le_of_right_le ?_)
          exact ((ih i (C j)).2 fun e => hi ⟨j, e⟩) ▸ le_rfl

/-- Membership in a check name: `⟦z ∈ y̌⟧ = ⨆ᵢ ⟦z = (yᵢ)ˇ⟧`. -/
theorem mem_check (z : BSet B) (y : PSet) :
    BSet.mem z (check y) = iSup fun i : y.Ix => ⊤ ⊓ BSet.eq z (check (y.Func i)) := by
  rw [check_def]; rfl

/-! ### Check names of ZF sets -/

/-- The **check name of a ZF set**, through a chosen presentation. -/
noncomputable def zcheck (x : ZFSet) : BSet B := check x.out

/-- Equal ZF sets have check names equal with value `⊤` (indeed `zcheck` is a function). -/
theorem eq_zcheck_of_eq {x y : ZFSet} (h : x = y) : BSet.eq (zcheck x : BSet B) (zcheck y) = ⊤ := by
  subst h; exact BSet.eq_self _

/-- Distinct ZF sets have check names equal with value `⊥`. -/
theorem eq_zcheck_of_ne {x y : ZFSet} (h : x ≠ y) : BSet.eq (zcheck x : BSet B) (zcheck y) = ⊥ :=
  (eq_check x.out y.out).2 fun e => h (by rw [← ZFSet.mk_out x, ← ZFSet.mk_out y]; exact ZFSet.mk_eq_mk.2 e)

/-- The check name of a member of a presentation is Boolean-equal (value `⊤`) to the check
name of the corresponding ZF set. -/
theorem eq_check_zcheck (x : PSet) :
    BSet.eq (check x : BSet B) (zcheck (ZFSet.mk x)) = ⊤ :=
  (eq_check x (ZFSet.mk x).out).1 (ZFSet.mk_eq_mk.1 (ZFSet.mk_out _).symm)

/-- **Membership in a check name** ranges over the members of the ZF set:
`⟦z ∈ y̌⟧ = ⨆_{w ∈ y} ⟦z = w̌⟧`. -/
theorem mem_zcheck (z : BSet B) (y : ZFSet) :
    BSet.mem z (zcheck y) = iSup fun w : {w // w ∈ y} => BSet.eq z (zcheck w.1) := by
  unfold zcheck
  rw [mem_check]
  apply le_antisymm'
  · refine iSup_le fun i => ?_
    have hw : ZFSet.mk (y.out.Func i) ∈ y := by
      have h1 : ZFSet.mk (y.out.Func i) ∈ ZFSet.mk y.out := PSet.func_mem _ i
      rwa [ZFSet.mk_out] at h1
    refine le_iSup_of_le ⟨_, hw⟩ ?_
    refine le_trans' (le_inf _ _ _ (inf_le_right _ _) ?_) (BSet.eq_trans _ _ _)
    show _ ≤ BSet.eq (check (y.out.Func i)) (zcheck (ZFSet.mk (y.out.Func i)))
    rw [eq_check_zcheck]; exact le_top'
  · refine iSup_le fun w => ?_
    have hw : w.1.out ∈ y.out := by
      have h1 : ZFSet.mk w.1.out ∈ ZFSet.mk y.out := by rw [ZFSet.mk_out, ZFSet.mk_out]; exact w.2
      exact h1
    obtain ⟨i, hi⟩ := hw
    refine le_iSup_of_le i ?_
    rw [top_inf]
    refine le_trans' (le_inf _ _ _ le_rfl ?_) (BSet.eq_trans _ _ _)
    rw [show (check (y.out.Func i) : BSet B) = check (y.out.Func i) from rfl,
      ((eq_check w.1.out (y.out.Func i)).1 hi)]
    exact le_top'

/-- Members give membership with value `⊤`. -/
theorem mem_zcheck_of_mem {x y : ZFSet} (h : x ∈ y) : BSet.mem (zcheck x : BSet B) (zcheck y) = ⊤ := by
  rw [mem_zcheck]; exact BSet.iSup_eq_top_of ⟨x, h⟩ (BSet.eq_self _)

/-- Non-members give membership with value `⊥`. -/
theorem mem_zcheck_of_not_mem {x y : ZFSet} (h : x ∉ y) :
    BSet.mem (zcheck x : BSet B) (zcheck y) = ⊥ := by
  rw [mem_zcheck]
  exact BSet.iSup_eq_bot_of fun w => eq_zcheck_of_ne fun e => h (e ▸ w.2)

/-- **The check embedding is faithful for equality** (for non-degenerate `B`). -/
theorem eq_zcheck_eq_top_iff (hB : (⊤ : B) ≠ ⊥) (x y : ZFSet) :
    BSet.eq (zcheck x : BSet B) (zcheck y) = ⊤ ↔ x = y :=
  ⟨fun h => Classical.byContradiction fun hne => hB (h.symm.trans (eq_zcheck_of_ne hne)),
   eq_zcheck_of_eq⟩

/-- **The check embedding is faithful for membership** (for non-degenerate `B`). -/
theorem mem_zcheck_eq_top_iff (hB : (⊤ : B) ≠ ⊥) (x y : ZFSet) :
    BSet.mem (zcheck x : BSet B) (zcheck y) = ⊤ ↔ x ∈ y :=
  ⟨fun h => Classical.byContradiction fun hn => hB (h.symm.trans (mem_zcheck_of_not_mem hn)),
   mem_zcheck_of_mem⟩

end Foundations.Forcing
