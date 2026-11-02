import Foundations.Forcing.CollapseEnum

/-!
# σ-closed forcing adds no new reals

The heart of the collapse argument is the observation, going back to the earliest days of
forcing, that a **σ-closed** poset adds no new subsets of `ω`. A name for a set of natural
numbers asks countably many questions "is `n` in?", and by σ-closure a single condition below
any given one answers all of them. So the name is, below that condition, equal to the check
name of a ground-model real. In Boolean-valued form:

> **No new reals** (`mem_powersetB_le`). In `V^{Col I}`, every member of `𝒫(ω̌)` is a mixture
> of ground reals: `⟦z ∈ 𝒫(ω̌)⟧ ≤ ⨆_{a ⊆ ℕ} ⟦z = ǎ⟧`.

Here `𝒫(ω̌)` is the standard power-set name `powersetB` of `NotCH`, whose members are the
Boolean subsets `ω̌↾f` for `f : ℕ → B`. For each such `f` the deciding lemma
`decide_countable` gives, below any condition, a condition `r` deciding every value `f n`;
then `r` forces `ω̌↾f = ǎ` with `a = {n | r decides n ∈}` (`top_le_iSup_eq_ground`).

The second half of the file sets up the generic function `g : I → 𝒫(ℕ)` as a tool: the truth
value `fo ξ a = ⟦g(ξ) = a ∧ ∀η < ξ, g(η) ≠ a⟧` that `ξ` is the **first occurrence** of the
ground real `a` in the generic sequence. Every real has exactly one first occurrence
(`top_le_iSup_fo`, `fo_disj_pos`), and a position is the first occurrence of at most one real
(`fo_disj_real`). Through first occurrences, the reals of `V^{Col I}` are injected into
`I = ω₁`; this is how the generic surjection `ω₁ → 𝒫(ω)` is used in `CollapseCH`, without
building it as an internal name.
-/

namespace Foundations.Forcing

open Foundations.Sets CBA ForcingNotion

attribute [local instance] Classical.propDecidable

variable {I : Type} [Omega1Like I]

/-! ### No new reals -/

omit [Omega1Like I] in
/-- **σ-closed forcing decides every real.** For every Boolean subset `ω̌↾f` of `ω̌` in
`V^{Col I}`, `⨆_{a ⊆ ℕ} ⟦ω̌↾f = ǎ⟧ = ⊤`. -/
theorem top_le_iSup_eq_ground (f : (omegaB : BSet (Col I)).type → Col I) :
    ⊤ ≤ iSup fun a : Nat → Prop => BSet.eq ((omegaB : BSet (Col I)).restrict f) (subsetB a) := by
  refine RO.top_le_of_dense fun p => ?_
  let V : Nat → Bool → Col I := fun n c => if c then f n else (f n)ᶜ
  have hV : ∀ n, (⊤ : Col I) ≤ iSup (V n) := fun n =>
    le_trans' top_le_sup_compl' (sup_le _ _ _ (le_iSup (V n) true) (le_iSup (V n) false))
  obtain ⟨r, hrp, dec, hdec⟩ := decide_countable countable_nat ⊤ V hV (RO.mem_top p)
  let a : Nat → Prop := fun n => dec n = true
  refine ⟨r, hrp, ?_⟩
  refine RO.prin_le_iff.1 (le_trans' ?_ (le_iSup (fun a : Nat → Prop =>
    BSet.eq ((omegaB : BSet (Col I)).restrict f) (subsetB a)) a))
  apply BSet.le_eq_of
  · intro n
    show RO.prin r ⊓ (f n ⊓ ⊤) ≤ iSup fun j : {m // a m} => ⊤ ⊓ BSet.eq (natB n) (natB j.1)
    by_cases hn : dec n = true
    · have key : (⊤ : Col I) ≤ ⊤ ⊓ BSet.eq (natB n) (natB n) := by
        rw [BSet.eq_self, inf_top]; exact le_rfl
      exact le_iSup_of_le (⟨n, hn⟩ : {m // a m}) (le_trans' le_top' key)
    · have hr : ((f n)ᶜ).carrier r := by
        have := hdec n; simp only [V, hn] at this; exact this
      have := RO.prin_le_iff.2 hr
      exact le_trans' (le_trans' (inf_le_inf this (inf_le_left _ _)) compl_inf_le) bot_le'
  · intro j
    show RO.prin r ⊓ ⊤ ≤ iSup fun m : Nat => (f m ⊓ ⊤) ⊓ BSet.eq (natB m) (natB j.1)
    have hr : (f j.1).carrier r := by
      have hj : dec j.1 = true := j.2
      have := hdec j.1; simp only [V, hj] at this; exact this
    refine le_iSup_of_le j.1 ?_
    rw [BSet.eq_self, inf_top, inf_top, inf_top]
    exact RO.prin_le_iff.2 hr

omit [Omega1Like I] in
/-- **No new reals.** In `V^{Col I}`, every member of `𝒫(ω̌)` is a mixture of ground reals:
`⟦z ∈ 𝒫(ω̌)⟧ ≤ ⨆_{a ⊆ ℕ} ⟦z = ǎ⟧`. -/
theorem mem_powersetB_le (z : BSet (Col I)) :
    BSet.mem z powersetB ≤ iSup fun a : Nat → Prop => BSet.eq z (subsetB a) := by
  refine iSup_le fun f => ?_
  show ⊤ ⊓ BSet.eq z ((omegaB : BSet (Col I)).restrict f) ≤ _
  refine le_trans' (le_inf _ _ _ (inf_le_right _ _)
    (le_trans' le_top' (top_le_iSup_eq_ground f))) ?_
  exact BSet.inf_iSup_le_of fun a => le_iSup_of_le a (BSet.eq_trans _ _ _)

/-! ### First occurrences in the generic sequence -/

/-- `⟦ξ is the first position where the generic function takes the value a⟧`. -/
noncomputable def fo (ξ : I) (a : Nat → Prop) : Col I :=
  catom ξ a ⊓ iInf fun η : {η // η < ξ} => (catom η.1 a)ᶜ

/-- A first occurrence is an occurrence. -/
theorem fo_le_catom (ξ : I) (a : Nat → Prop) : fo ξ a ≤ catom ξ a := inf_le_left _ _

/-- **Every real has a first occurrence.** `⨆_ξ ⟦ξ is the first occurrence of a⟧ = ⊤`. -/
theorem top_le_iSup_fo (a : Nat → Prop) : (⊤ : Col I) ≤ iSup fun ξ => fo ξ a :=
  le_trans' (top_le_iSup_catom a) (iSup_le_iSup_least fun ξ => catom ξ a)

/-- A position is the first occurrence of at most one real. -/
theorem fo_disj_real {ξ : I} {a a' : Nat → Prop} (h : a ≠ a') : fo ξ a ⊓ fo ξ a' ≤ ⊥ :=
  le_trans' (inf_le_inf (fo_le_catom ξ a) (fo_le_catom ξ a')) (catom_disj h)

/-- First occurrences of the same real at comparable positions are incompatible. -/
theorem fo_disj_lt {ξ ξ' : I} (h : ξ < ξ') (a : Nat → Prop) : fo ξ a ⊓ fo ξ' a ≤ ⊥ :=
  le_trans' (inf_le_inf (fo_le_catom ξ a) (inf_le_of_right_le
    (iInf_le (fun η : {η // η < ξ'} => (catom η.1 a)ᶜ) ⟨ξ, h⟩))) inf_compl_le

/-- **A real has only one first occurrence.** `fo ξ a ⊓ fo ξ' a = ⊥` for `ξ ≠ ξ'`. -/
theorem fo_disj_pos {ξ ξ' : I} (h : ξ ≠ ξ') (a : Nat → Prop) : fo ξ a ⊓ fo ξ' a ≤ ⊥ := by
  rcases Omega1Like.tri ξ ξ' with h' | h' | h'
  · exact fo_disj_lt h' a
  · exact absurd h' h
  · rw [inf_comm]; exact fo_disj_lt h' a

end Foundations.Forcing
