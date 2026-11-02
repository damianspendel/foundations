import Foundations.Forcing.NotCH

/-!
# Function names, Kuratowski pairs, and congruence in `V^B`

To verify CH in the collapse model (`CollapseCH`), injections must be *built* inside the
Boolean-valued universe. Unlike `NotCH`, which only had to rule injections out, we now need
a supply of names that provably are injective functions. This file provides the general
tools, valid in `V^B` for every complete Boolean algebra `B`:

* **Kuratowski pairs are injective** in the Boolean sense: `⟦(a, b) = (c, d)⟧ ≤ ⟦a = c⟧ ⊓
  ⟦b = d⟧` (`eq_opair_le`). This is the Boolean version of the familiar case analysis on
  `{{a}, {a, b}} = {{c}, {c, d}}`.
* **Graph names.** For a family of pairs `(sⱼ, tⱼ)` with Boolean weights `wⱼ`, the name
  `fname s t w = {((sⱼ, tⱼ), wⱼ)}` is the graph of a relation. Its pair-membership is computed
  exactly up to Boolean equality (`pm_fname_le`, `le_pm_fname`), and
  `le_isFunc_inf_isInj` gives a checkable criterion for it to be an injective function from
  `X` to `Y`: totality, single-valuedness and injectivity, each stated for the listed pairs
  only.
* Ground reals and numerals are two-valued: distinct ground subsets of `ℕ` have Boolean
  equality `⊥` (`eq_subsetB_of_ne`).
* **Congruence** of the notions in the CH sentence under Boolean equality (`subset_congr`,
  `isFunc_congr`, `isInj_congr`), and uniqueness of `ω` and of power sets:
  `⟦w = ω⟧ ≤ ⟦w = ω̌⟧` and `⟦p = 𝒫(w)⟧ ⊓ ⟦w = ω̌⟧ ≤ ⟦p = 𝒫(ω̌)⟧` (`isOmega_le_eq`,
  `isPow_le_eq`). These let the CH sentence be checked at the standard names `ω̌`, `𝒫(ω̌)` only.
-/

namespace Foundations.Forcing

open CBA

attribute [local instance] Classical.propDecidable

variable {B : Type} [CompleteBooleanAlgebra B]

namespace BSet

/-! ### Kuratowski pairs -/

/-- A name equal to `{c, d}` contains `c` and `d`: `⟦X = {c, d}⟧ ≤ ⟦c ∈ X⟧ ⊓ ⟦d ∈ X⟧`. -/
theorem eq_pair_le_mem (X c d : BSet B) : eq X (pair c d) ≤ mem c X ⊓ mem d X := by
  have hc : ⊤ ≤ mem c (pair c d) := by rw [mem_pair, eq_self]; exact le_sup_left _ _
  have hd : ⊤ ≤ mem d (pair c d) := by rw [mem_pair, eq_self]; exact le_sup_right _ _
  exact le_inf _ _ _
    (le_trans' (le_inf _ _ _ (eq_symm _ _) (le_trans' le_top' hc)) (mem_congr_right _ _ _))
    (le_trans' (le_inf _ _ _ (eq_symm _ _) (le_trans' le_top' hd)) (mem_congr_right _ _ _))

/-- `⟦{a, a} = {c, d}⟧ ≤ ⟦c = a⟧ ⊓ ⟦d = a⟧`. -/
theorem eq_sing_pair_le (a c d : BSet B) : eq (pair a a) (pair c d) ≤ eq c a ⊓ eq d a := by
  have := eq_pair_le_mem (pair a a) c d
  rwa [mem_pair, mem_pair, sup_idem', sup_idem'] at this

/-- `⟦{a, b} = {c, d}⟧ ≤ ⟦b = c⟧ ⊔ ⟦b = d⟧`. -/
theorem eq_pair_le_right (a b c d : BSet B) : eq (pair a b) (pair c d) ≤ eq b c ⊔ eq b d := by
  have := eq_pair_le_mem (pair c d) a b
  rw [mem_pair, mem_pair, eq_comm] at this
  exact le_trans' this (inf_le_right _ _)

/-- **Kuratowski pairs are injective (first coordinate).** -/
theorem eq_opair_le_fst (a b c d : BSet B) : eq (opair a b) (opair c d) ≤ eq a c := by
  have h := eq_pair_le_mem (opair c d) (pair a a) (pair a b)
  rw [eq_comm] at h
  refine le_trans' (le_trans' h (inf_le_left _ _)) ?_
  show mem (pair a a) (pair (pair c c) (pair c d)) ≤ _
  rw [mem_pair]
  refine sup_le _ _ _ ?_ ?_
  · rw [eq_comm]; exact le_trans' (eq_sing_pair_le c a a) (le_trans' (inf_le_left _ _) le_rfl)
  · exact le_trans' (eq_sing_pair_le a c d) (le_trans' (inf_le_left _ _) (eq_symm _ _))

/-- **Kuratowski pairs are injective.** `⟦(a, b) = (c, d)⟧ ≤ ⟦a = c⟧ ⊓ ⟦b = d⟧`. -/
theorem eq_opair_le (a b c d : BSet B) : eq (opair a b) (opair c d) ≤ eq a c ⊓ eq b d := by
  refine le_inf _ _ _ (eq_opair_le_fst a b c d) ?_
  have hac := eq_opair_le_fst a b c d
  -- `b ∈ {c, d}` coordinates
  have h1 : eq (opair a b) (opair c d) ≤ eq b c ⊔ eq b d := by
    have h := eq_pair_le_mem (opair c d) (pair a a) (pair a b)
    rw [eq_comm] at h
    refine le_trans' (le_trans' h (inf_le_right _ _)) ?_
    show mem (pair a b) (pair (pair c c) (pair c d)) ≤ _
    rw [mem_pair]
    refine sup_le _ _ _ ?_ (eq_pair_le_right a b c d)
    rw [eq_comm]; exact le_sup_of_le_left (le_trans' (eq_sing_pair_le c a b) (inf_le_right _ _))
  have h2 : eq (opair a b) (opair c d) ≤ eq d a ⊔ eq d b := by
    have h := eq_pair_le_mem (opair a b) (pair c c) (pair c d)
    refine le_trans' (le_trans' h (inf_le_right _ _)) ?_
    show mem (pair c d) (pair (pair a a) (pair a b)) ≤ _
    rw [mem_pair]
    refine sup_le _ _ _ ?_ (eq_pair_le_right c d a b)
    rw [eq_comm]; exact le_sup_of_le_left (le_trans' (eq_sing_pair_le a c d) (inf_le_right _ _))
  -- case analysis
  have hca : eq a c ⊓ eq b c ⊓ eq d a ≤ eq b d :=
    le_trans' (le_inf _ _ _ (le_trans' (le_inf _ _ _ (by lattice_le)
      (inf_le_of_left_le (inf_le_left _ _))) (BSet.eq_trans b c a |> le_trans' (inf_le_inf le_rfl
        (eq_symm a c))))
      (inf_le_of_right_le (eq_symm d a))) (eq_trans b a d)
  refine le_trans' (le_inf _ _ _ (le_inf _ _ _ hac h1) h2) ?_
  refine le_trans' (inf_sup_le _ _ _) (sup_le _ _ _ ?_ (inf_le_of_right_le (eq_symm _ _)))
  refine le_trans' (inf_le_inf (inf_sup_le _ _ _) le_rfl) ?_
  refine le_trans' sup_inf_le (sup_le _ _ _ hca ?_)
  lattice_le

/-! ### Graph names -/

/-- The **graph name** `{((sⱼ, tⱼ), wⱼ) | j ∈ J}` of a family of pairs with Boolean weights. -/
def fname {J : Type} (s t : J → BSet B) (w : J → B) : BSet B :=
  .mk J (fun j => opair (s j) (t j)) w

/-- Pair membership in a graph name is bounded by the listed pairs. -/
theorem pm_fname_le {J : Type} (s t : J → BSet B) (w : J → B) (u y : BSet B) :
    pm u y (fname s t w) ≤ iSup fun j => w j ⊓ (eq u (s j) ⊓ eq y (t j)) :=
  iSup_mono fun _ => inf_le_inf le_rfl (eq_opair_le _ _ _ _)

/-- A listed pair belongs to the graph name to its weight. -/
theorem le_pm_fname {J : Type} (s t : J → BSet B) (w : J → B) (u y : BSet B) (j : J) :
    w j ⊓ (eq u (s j) ⊓ eq y (t j)) ≤ pm u y (fname s t w) :=
  le_iSup_of_le j (inf_le_inf le_rfl (opair_congr _ _ _ _))

/-- Distributing a meet over a join, as an elimination rule. -/
theorem inf_iSup_le_of {ι : Sort _} {c d : B} {f : ι → B} (h : ∀ i, c ⊓ f i ≤ d) :
    c ⊓ iSup f ≤ d := le_trans' inf_iSup_le (iSup_le h)

/-- Distributing a meet over a join in the middle, as an elimination rule. -/
theorem inf_iSup_inf_le_of {ι : Sort _} {c e d : B} {f : ι → B} (h : ∀ i, c ⊓ f i ⊓ e ≤ d) :
    c ⊓ iSup f ⊓ e ≤ d :=
  le_trans' (inf_le_inf inf_iSup_le le_rfl) (le_trans' iSup_inf_le (iSup_le h))

/-- **Criterion for an injective function.** The graph name `F = fname s t w` is, to degree
`c`, an injective function from `X` to `Y`, provided that (to degree `c`) every member of `X`
is some listed `sⱼ` with weight `wⱼ` and `tⱼ ∈ Y`; listed pairs with equal first coordinates
have equal second coordinates; and listed pairs with equal second coordinates have equal first
coordinates. -/
theorem le_isFunc_inf_isInj {J : Type} {s t : J → BSet B} {w : J → B} {X Y : BSet B} {c : B}
    (htot : ∀ u, c ⊓ mem u X ≤ iSup fun j => w j ⊓ eq u (s j) ⊓ mem (t j) Y)
    (hsv : ∀ j j', c ⊓ w j ⊓ w j' ⊓ eq (s j) (s j') ≤ eq (t j) (t j'))
    (hinj : ∀ j j', c ⊓ w j ⊓ w j' ⊓ eq (t j) (t j') ≤ eq (s j) (s j')) :
    c ≤ isFunc (fname s t w) X Y ⊓ isInj (fname s t w) X := by
  refine le_inf _ _ _ (le_inf _ _ _ ?_ ?_) ?_
  · refine le_iInf fun u => le_himp_iff.2 (le_trans' (htot u) (iSup_le fun j => ?_))
    refine le_iSup_of_le (t j) (le_inf _ _ _ (inf_le_right _ _) ?_)
    have he : w j ⊓ eq u (s j) ⊓ mem (t j) Y ≤ eq (t j) (t j) := by rw [eq_self]; exact le_top'
    exact le_trans' (le_inf _ _ _ (by lattice_le) (le_inf _ _ _ (by lattice_le) he))
      (le_pm_fname s t w u (t j) j)
  · refine le_iInf fun u => le_himp_iff.2 <| le_iInf fun y => le_iInf fun y' => le_himp_iff.2 ?_
    have e1 : c ⊓ mem u X ⊓ (pm u y (fname s t w) ⊓ pm u y' (fname s t w)) ≤
        c ⊓ (iSup fun j => w j ⊓ (eq u (s j) ⊓ eq y (t j))) ⊓
          (iSup fun j => w j ⊓ (eq u (s j) ⊓ eq y' (t j))) :=
      le_inf _ _ _ (le_inf _ _ _ (by lattice_le)
        (le_trans' (by lattice_le) (pm_fname_le s t w u y)))
        (le_trans' (by lattice_le) (pm_fname_le s t w u y'))
    refine le_trans' e1 ?_
    refine inf_iSup_le_of fun j' => inf_iSup_inf_le_of fun j => ?_
    have hs : c ⊓ (w j ⊓ (eq u (s j) ⊓ eq y (t j))) ⊓ (w j' ⊓ (eq u (s j') ⊓ eq y' (t j'))) ≤
        eq (s j) (s j') :=
      le_trans' (le_inf _ _ _ (le_trans' (by lattice_le) (eq_symm u (s j))) (by lattice_le))
        (eq_trans _ u _)
    have ht := le_trans' (le_inf _ _ _ (le_inf _ _ _ (le_inf _ _ _ (by lattice_le) (by lattice_le))
      (by lattice_le)) hs) (hsv j j')
    exact le_trans' (le_inf _ _ _ (le_inf _ _ _ (by lattice_le) ht)
      (le_trans' (by lattice_le) (eq_symm y' (t j')))) (le_trans' (inf_le_inf (eq_trans _ _ _)
        le_rfl) (eq_trans _ _ _))
  · refine le_iInf fun u => le_iInf fun u' => le_iInf fun y => le_himp_iff.2 ?_
    have e1 : c ⊓ (mem u X ⊓ mem u' X ⊓ pm u y (fname s t w) ⊓ pm u' y (fname s t w)) ≤
        c ⊓ (iSup fun j => w j ⊓ (eq u (s j) ⊓ eq y (t j))) ⊓
          (iSup fun j => w j ⊓ (eq u' (s j) ⊓ eq y (t j))) :=
      le_inf _ _ _ (le_inf _ _ _ (by lattice_le)
        (le_trans' (by lattice_le) (pm_fname_le s t w u y)))
        (le_trans' (by lattice_le) (pm_fname_le s t w u' y))
    refine le_trans' e1 ?_
    refine inf_iSup_le_of fun j' => inf_iSup_inf_le_of fun j => ?_
    have ht : c ⊓ (w j ⊓ (eq u (s j) ⊓ eq y (t j))) ⊓ (w j' ⊓ (eq u' (s j') ⊓ eq y (t j'))) ≤
        eq (t j) (t j') :=
      le_trans' (le_inf _ _ _ (le_trans' (by lattice_le) (eq_symm y (t j))) (by lattice_le))
        (eq_trans _ y _)
    have hs := le_trans' (le_inf _ _ _ (le_inf _ _ _ (le_inf _ _ _ (by lattice_le) (by lattice_le))
      (by lattice_le)) ht) (hinj j j')
    exact le_trans' (le_inf _ _ _ (le_inf _ _ _ (by lattice_le) hs)
      (le_trans' (by lattice_le) (eq_symm u' (s j')))) (le_trans' (inf_le_inf (eq_trans _ _ _)
        le_rfl) (eq_trans _ _ _))

/-! ### Congruence -/

/-- `⟦x ⊆ p⟧ ⊓ ⟦p = p'⟧ ≤ ⟦x ⊆ p'⟧`. -/
theorem subset_congr (x p p' : BSet B) : subset x p ⊓ eq p p' ≤ subset x p' :=
  le_iInf fun z => le_himp_iff.2 <| le_trans' (le_inf _ _ _ (by lattice_le)
    (le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (iInf_le _ z)))
      (inf_le_right _ _)) himp_inf_le)) (mem_congr_right _ _ _)

/-- `⟦f : X → Y⟧ ⊓ ⟦X = X'⟧ ⊓ ⟦Y = Y'⟧ ≤ ⟦f : X' → Y'⟧`. -/
theorem isFunc_congr (f X X' Y Y' : BSet B) :
    isFunc f X Y ⊓ eq X X' ⊓ eq Y Y' ≤ isFunc f X' Y' := by
  have hX : ∀ a, eq X X' ⊓ mem a X' ≤ mem a X := fun a =>
    le_trans' (inf_le_inf (eq_symm _ _) le_rfl) (mem_congr_right _ _ _)
  refine le_inf _ _ _ (le_iInf fun a => le_himp_iff.2 ?_) (le_iInf fun a => le_himp_iff.2 ?_)
  · have h1 : isFunc f X Y ⊓ eq X X' ⊓ eq Y Y' ⊓ mem a X' ≤
        (iSup fun b => mem b Y ⊓ pm a b f) ⊓ eq Y Y' :=
      le_inf _ _ _ (le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le
        (inf_le_of_left_le (inf_le_of_left_le (iInf_le _ a)))))
        (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (hX a))) himp_inf_le)
        (by lattice_le)
    refine le_trans' h1 (le_trans' iSup_inf_le (iSup_mono fun b => le_inf _ _ _ ?_ (by lattice_le)))
    exact le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (mem_congr_right _ _ _)
  · exact le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (inf_le_of_left_le
      (inf_le_of_right_le (iInf_le _ a))))) (le_trans' (le_inf _ _ _ (by lattice_le)
        (by lattice_le)) (hX a))) himp_inf_le

/-- `⟦f injective on X⟧ ⊓ ⟦X = X'⟧ ≤ ⟦f injective on X'⟧`. -/
theorem isInj_congr (f X X' : BSet B) : isInj f X ⊓ eq X X' ≤ isInj f X' := by
  have hX : ∀ a, eq X X' ⊓ mem a X' ≤ mem a X := fun a =>
    le_trans' (inf_le_inf (eq_symm _ _) le_rfl) (mem_congr_right _ _ _)
  refine le_iInf fun a => le_iInf fun a' => le_iInf fun b => le_himp_iff.2 ?_
  refine le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (iInf_le_of_le a
    (iInf_le_of_le a' (iInf_le _ b))))) ?_) himp_inf_le
  refine le_inf _ _ _ (le_inf _ _ _ (le_inf _ _ _ ?_ ?_) (by lattice_le)) (by lattice_le)
  · exact le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (hX a)
  · exact le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (hX a')

/-- **Uniqueness of `ω`.** `⟦w = ω⟧ ≤ ⟦w = ω̌⟧`: both are least inductive sets. -/
theorem isOmega_le_eq (w : BSet B) : isOmega w ≤ eq w omegaB := by
  rw [eq_eq_iInf_biimp]
  refine le_iInf fun z => le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_)
  · have hsub : isOmega w ≤ subset w omegaB :=
      le_trans' (le_inf _ _ _ (inf_le_of_right_le (iInf_le _ omegaB))
        (by rw [isInductive_omegaB]; exact le_top')) himp_inf_le
    exact le_trans' (inf_le_inf hsub le_rfl) (le_trans' (inf_le_inf (iInf_le _ z) le_rfl)
      himp_inf_le)
  · show _ ⊓ (iSup fun n : Nat => ⊤ ⊓ eq z (natB n)) ≤ _
    refine inf_iSup_le_of fun n => ?_
    exact le_trans' (le_inf _ _ _ (inf_le_of_right_le (inf_le_of_right_le (eq_symm _ _)))
      (inf_le_of_left_le (inf_le_of_left_le (isInductive_le_mem w n)))) (mem_congr_left _ _ _)

/-- **Uniqueness of the power set.** `⟦p = 𝒫(w)⟧ ⊓ ⟦w = ω̌⟧ ≤ ⟦p = 𝒫(ω̌)⟧`, with `𝒫(ω̌)` the
standard name `powersetB`. -/
theorem isPow_le_eq (p w : BSet B) : isPow p w ⊓ eq w omegaB ≤ eq p powersetB := by
  rw [eq_eq_iInf_biimp p]
  have hP := isPow_powersetB (B := B)
  have hPz : ∀ z : BSet B, ⊤ ≤ (mem z powersetB ⇔ subset z omegaB) := fun z => by
    rw [← hP]; exact iInf_le (fun z => mem z powersetB ⇔ subset z omegaB) z
  have hsP : ∀ z : BSet B, subset z omegaB ≤ mem z powersetB := fun z =>
    le_trans' (le_inf _ _ _ (le_trans' le_top' (le_trans' (hPz z) (inf_le_right _ _))) le_rfl)
      himp_inf_le
  have hPs : ∀ z : BSet B, mem z powersetB ≤ subset z omegaB := fun z =>
    le_trans' (le_inf _ _ _ (le_trans' le_top' (le_trans' (hPz z) (inf_le_left _ _))) le_rfl)
      himp_inf_le
  have hp1 : ∀ z, isPow p w ≤ (mem z p ⇨ subset z w) := fun z =>
    le_trans' (iInf_le _ z) (inf_le_left _ _)
  have hp2 : ∀ z, isPow p w ≤ (subset z w ⇨ mem z p) := fun z =>
    le_trans' (iInf_le _ z) (inf_le_right _ _)
  refine le_iInf fun z => le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_)
  · have h0 : isPow p w ⊓ eq w omegaB ⊓ mem z p ≤ subset z w :=
      le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (hp1 z))) (inf_le_right _ _))
        himp_inf_le
    have h1 : isPow p w ⊓ eq w omegaB ⊓ mem z p ≤ subset z omegaB :=
      le_trans' (le_inf _ _ _ h0 (by lattice_le)) (subset_congr _ _ _)
    exact le_trans' h1 (hsP z)
  · have h2 : isPow p w ⊓ eq w omegaB ⊓ mem z powersetB ≤ subset z w :=
      le_trans' (le_inf _ _ _ (inf_le_of_right_le (hPs z))
        (inf_le_of_left_le (inf_le_of_right_le (eq_symm _ _)))) (subset_congr _ _ _)
    exact le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (hp2 z))) h2) himp_inf_le

end BSet

/-! ### Two-valuedness of ground reals -/

/-- **Distinct ground reals are Boolean-distinct.** For `a ≠ a'`, `⟦ǎ = ǎ'⟧ = ⊥`. -/
theorem eq_subsetB_of_ne {a a' : Nat → Prop} (h : a ≠ a') :
    BSet.eq (subsetB a : BSet B) (subsetB a') = ⊥ := by
  have : ∃ n, ¬ (a n ↔ a' n) := Classical.byContradiction fun hn =>
    h (funext fun n => propext (Classical.byContradiction fun hn' => hn ⟨n, hn'⟩))
  obtain ⟨n, hn⟩ := this
  by_cases ha : a n
  · have ha' : ¬ a' n := fun h' => hn ⟨fun _ => h', fun _ => ha⟩
    have := BSet.mem_congr_right (natB n) (subsetB a : BSet B) (subsetB a')
    rw [mem_subsetB_of_mem ha, mem_subsetB_of_not_mem ha', inf_top] at this
    exact eq_bot_iff.2 this
  · have ha' : a' n := Classical.byContradiction fun h' =>
      hn ⟨fun h'' => absurd h'' ha, fun h'' => absurd h'' h'⟩
    have := BSet.mem_congr_right (natB n) (subsetB a' : BSet B) (subsetB a)
    rw [mem_subsetB_of_mem ha', mem_subsetB_of_not_mem ha, inf_top, BSet.eq_comm] at this
    exact eq_bot_iff.2 this

/-- Ground reals: `⟦ǎ = ǎ'⟧` is `⊤` if `a = a'`. -/
theorem eq_subsetB_self (a : Nat → Prop) : BSet.eq (subsetB a : BSet B) (subsetB a) = ⊤ :=
  BSet.eq_self _

end Foundations.Forcing
