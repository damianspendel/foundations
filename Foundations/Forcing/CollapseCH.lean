import Foundations.Forcing.CollapseReals

/-!
# CH holds in the collapse model, and ZF ⊬ ¬CH

We now verify the Continuum Hypothesis in `V^B` for the collapse algebra `B = Col I` over an
`ω₁`-like order `I`, and then take `I = W₁`, the ground `ω₁`. This is the forcing counterpart
of **Gödel's 1938** theorem that CH is consistent with ZF, obtained by the **Lévy collapse**
of `2^ℵ₀` onto `ℵ₁`. The proof uses only **σ-closure** and the combinatorics of `ω₁`; Gödel's
constructible universe is not needed.

By the uniqueness lemmas of `CollapseNames`, it suffices to treat `w = ω̌` and `p = 𝒫(ω̌)`
(`powersetB`). Fix a name `x` with `⟦x ⊆ 𝒫(ω̌)⟧ = s`. We show
`s ≤ ⟦x ↪ ω̌⟧ ⊔ ⟦𝒫(ω̌) ↪ x⟧` (`subset_le_S1_sup_S2`). Let `g : I → 𝒫(ℕ)` be the generic
function and

`A = {ζ ∈ I | ζ is the first occurrence of g(ζ), and g(ζ) ∈ x}`,

given by truth values `bA x ζ`. Since there are no new reals (`mem_powersetB_le`) and every real
has a first occurrence, `ζ ↦ g(ζ)` maps `A` bijectively onto `x`.

* **Countable case** (`countable_case`). If `A` is bounded by a ground `γ`, then
  `a ↦ (first occurrence of a) ↦ e_γ(…)` with a ground injection `e_γ : γ → ℕ` is an injection
  of `x` into `ω̌`. The name is written down explicitly as a graph name.
* **Unbounded case.** Suppose `x` does not inject into `ω̌`, to degree
  `c' = s ⊓ ⟦x ↪ ω̌⟧ᶜ`. Then `A` is unbounded below `c'`, and the increasing enumeration
  `f = enumV (bA x)` of `CollapseEnum` is total (`enum_total`). The countably many values
  `f(β)`, `β < α`, are decided by a single condition (σ-closure, `decide_countable`); they are
  bounded by some `γ < ω₁` (`Omega1Like.exists_bound`); and since `A` is not bounded by `γ`,
  some element of `A` lies above them. Then `a ↦ g(f(first occurrence of a))` is an injection
  of `𝒫(ω̌)` into `x` (`uncountable_case`).

Hence `⟦CH⟧ = ⊤` (`val_CH_eq_top`). Since every axiom of ZF is `⊤` in `V^B` and `Col W₁` is
non-degenerate, soundness gives

> **`ZF_not_proves_notCH : ¬ (ZF ⊢₁ CH.neg)`**, and with `NotCH`,
> **`CH_independent_ZF : ¬ (ZF ⊢₁ CH) ∧ ¬ (ZF ⊢₁ CH.neg)`**.

**Scope.** As in `NotCH`, this is independence over **ZF** (the theory `ZF` of `BSetZF`),
for the specific `LSet` sentence `CH` of `Formulas`. The axiom of choice is not verified in
`V^B`, so neither `ZFC ⊬ CH` nor `ZFC ⊬ ¬CH` is obtained. The surjection `ω̌₁ → 𝒫(ω̌)` given by
the generic is used externally, through the truth values `fo` and `catom`; it is never built as
an internal name, and neither is `ω̌₁`. That `ω₁` is not collapsed is not stated as a separate
theorem; its content is used in `enum_total`.
-/

namespace Foundations.Forcing

open Foundations.Logic.FO Foundations.Sets CBA ForcingNotion BStructure

attribute [local instance] Classical.propDecidable

variable {I : Type} [Omega1Like I]

/-- `⟦x injects into ω̌⟧`. -/
noncomputable def S1 (x : BSet (Col I)) : Col I :=
  iSup fun f => BSet.isFunc f x omegaB ⊓ BSet.isInj f x

/-- `⟦𝒫(ω̌) injects into x⟧`. -/
noncomputable def S2 (x : BSet (Col I)) : Col I :=
  iSup fun f => BSet.isFunc f powersetB x ⊓ BSet.isInj f powersetB

/-- `⟦ζ ∈ A⟧`: `ζ` is the first occurrence of the real `g(ζ)`, and `g(ζ) ∈ x`. -/
noncomputable def bA (x : BSet (Col I)) (ζ : I) : Col I :=
  iSup fun a : Nat → Prop => fo ζ a ⊓ BSet.mem (subsetB a) x

section Cases

variable (x : BSet (Col I))

/-- If `ζ ∈ A` and `g(ζ) = a'`, then `ζ` is the first occurrence of `a'` and `a' ∈ x`. -/
theorem bA_inf_catom (ζ : I) (a' : Nat → Prop) :
    bA x ζ ⊓ catom ζ a' ≤ fo ζ a' ⊓ BSet.mem (subsetB a') x := by
  refine le_trans' iSup_inf_le (iSup_le fun a => ?_)
  by_cases h : a = a'
  · subst h; exact inf_le_left _ _
  · exact le_trans' (le_trans' (inf_le_inf (inf_le_of_left_le (fo_le_catom ζ a)) le_rfl)
      (catom_disj h)) bot_le'

omit [Omega1Like I] in
/-- Members of a subset of `𝒫(ω̌)` are mixtures of ground reals. -/
theorem subset_inf_mem_le (u : BSet (Col I)) (c : Col I) (hc : c ≤ BSet.subset x powersetB) :
    c ⊓ BSet.mem u x ≤ iSup fun a : Nat → Prop => c ⊓ BSet.mem u x ⊓ BSet.eq u (subsetB a) :=
  le_trans' (le_inf _ _ _ le_rfl (le_trans' (le_trans' (inf_le_inf (le_trans' hc (iInf_le _ u))
    le_rfl) himp_inf_le) (mem_powersetB_le u))) inf_iSup_le

/-- **The countable case.** If `A` is contained in the ground initial segment below `γ`, then
`x` injects into `ω̌`: `⟦x ⊆ 𝒫(ω̌)⟧ ⊓ ⨅_{ξ ≥ γ} ⟦ξ ∉ A⟧ ≤ ⟦x ↪ ω̌⟧`. -/
theorem countable_case (γ : I) :
    BSet.subset x powersetB ⊓ (iInf fun ξ : {ξ // ¬ ξ < γ} => (bA x ξ.1)ᶜ) ≤ S1 x := by
  obtain ⟨e, he⟩ := Omega1Like.seg γ
  let J := {q : I × (Nat → Prop) // q.1 < γ}
  let s : J → BSet (Col I) := fun j => subsetB j.1.2
  let t : J → BSet (Col I) := fun j => natB (e ⟨j.1.1, j.2⟩)
  let w : J → Col I := fun j => fo j.1.1 j.1.2
  refine le_iSup_of_le (BSet.fname s t w) (BSet.le_isFunc_inf_isInj ?_ ?_ ?_)
  · intro u
    refine le_trans' (subset_inf_mem_le x u _ (inf_le_left _ _)) (iSup_le fun a => ?_)
    refine le_trans' (le_inf _ _ _ le_rfl (le_trans' le_top' (top_le_iSup_fo a)))
      (BSet.inf_iSup_le_of fun ξ => ?_)
    have hin : BSet.mem u x ⊓ BSet.eq u (subsetB a) ≤ BSet.mem (subsetB a) x := by
      rw [inf_comm]; exact BSet.mem_congr_left _ _ _
    by_cases hξ : ξ < γ
    · refine le_iSup_of_le ⟨(ξ, a), hξ⟩ ?_
      show _ ≤ fo ξ a ⊓ BSet.eq u (subsetB a) ⊓ BSet.mem (natB (e ⟨ξ, hξ⟩)) omegaB
      rw [show BSet.mem (natB (e ⟨ξ, hξ⟩)) (omegaB : BSet (Col I)) = ⊤ from
        mem_natB_family _ _, inf_top]
      exact le_inf _ _ _ (by lattice_le) (by lattice_le)
    · have h1 : BSet.subset x powersetB ⊓ (iInf fun ξ : {ξ // ¬ ξ < γ} => (bA x ξ.1)ᶜ) ⊓
          BSet.mem u x ⊓ BSet.eq u (subsetB a) ⊓ fo ξ a ≤ (bA x ξ)ᶜ :=
        inf_le_of_left_le (inf_le_of_left_le (inf_le_of_left_le (inf_le_of_right_le
          (iInf_le (fun ξ : {ξ // ¬ ξ < γ} => (bA x ξ.1)ᶜ) ⟨ξ, hξ⟩))))
      have h2 : BSet.subset x powersetB ⊓ (iInf fun ξ : {ξ // ¬ ξ < γ} => (bA x ξ.1)ᶜ) ⊓
          BSet.mem u x ⊓ BSet.eq u (subsetB a) ⊓ fo ξ a ≤ bA x ξ :=
        le_trans' (le_inf _ _ _ (by lattice_le) (le_trans' (le_inf _ _ _ (by lattice_le)
          (by lattice_le)) hin)) (le_iSup (fun a => fo ξ a ⊓ BSet.mem (subsetB a) x) a)
      exact le_trans' (le_trans' (le_inf _ _ _ h1 h2) compl_inf_le) bot_le'
  · rintro ⟨⟨ξ, a⟩, hξ⟩ ⟨⟨ξ', a'⟩, hξ'⟩
    show _ ⊓ fo ξ a ⊓ fo ξ' a' ⊓ BSet.eq (subsetB a) (subsetB a') ≤
      BSet.eq (natB (e ⟨ξ, hξ⟩)) (natB (e ⟨ξ', hξ'⟩))
    by_cases ha : a = a'
    · subst ha
      by_cases hx : ξ = ξ'
      · subst hx; exact le_trans' le_top' (eq_top_iff.1 (BSet.eq_self _))
      · exact le_trans' (le_trans' (inf_le_of_left_le (le_inf _ _ _ (by lattice_le)
          (by lattice_le))) (fo_disj_pos hx a)) bot_le'
    · rw [eq_subsetB_of_ne ha]; exact inf_le_of_right_le bot_le'
  · rintro ⟨⟨ξ, a⟩, hξ⟩ ⟨⟨ξ', a'⟩, hξ'⟩
    show _ ⊓ fo ξ a ⊓ fo ξ' a' ⊓ BSet.eq (natB (e ⟨ξ, hξ⟩)) (natB (e ⟨ξ', hξ'⟩)) ≤
      BSet.eq (subsetB a) (subsetB a')
    by_cases hx : ξ = ξ'
    · subst hx
      by_cases ha : a = a'
      · subst ha; exact le_trans' le_top' (eq_top_iff.1 (BSet.eq_self _))
      · exact le_trans' (le_trans' (inf_le_of_left_le (le_inf _ _ _ (by lattice_le)
          (by lattice_le))) (fo_disj_real ha)) bot_le'
    · have hne : e ⟨ξ, hξ⟩ ≠ e ⟨ξ', hξ'⟩ := fun h => hx (congrArg Subtype.val (he h))
      rw [eq_natB_of_ne _ _ hne]; exact inf_le_of_right_le bot_le'

/-- The degree to which `x ⊆ 𝒫(ω̌)` and `x` does not inject into `ω̌`. -/
noncomputable def cU : Col I := BSet.subset x powersetB ⊓ (S1 x)ᶜ

/-- **The enumeration of `A` is total** where `x` is uncountable:
`⟦x ⊆ 𝒫(ω̌)⟧ ⊓ ⟦x ↪ ω̌⟧ᶜ ≤ ⨆_ζ ⟦f(α) = ζ⟧` for every `α < ω₁`. This is where σ-closure is used:
the earlier values are decided by one condition, bounded below `ω₁`, and exceeded by some
element of the unbounded set `A`. -/
theorem enum_total (α : I) : cU x ≤ iSup fun ζ => enumV (bA x) α ζ := by
  refine Omega1Like.wf.induction α (C := fun α => cU x ≤ iSup fun ζ => enumV (bA x) α ζ)
    fun α ih => le_trans' ?_ (enumV_step (bA x) α)
  refine RO.le_of_dense fun q hq => ?_
  obtain ⟨r₁, hr₁q, ζ, hζ⟩ := decide_countable (Omega1Like.seg α) (cU x)
    (fun β : {β // β < α} => enumV (bA x) β.1) (fun β => ih β.1 β.2) hq
  obtain ⟨γ, hγ⟩ := Omega1Like.exists_bound (Omega1Like.seg α) ζ
  have hr₁c : (cU x).carrier r₁ := (cU x).down _ _ hr₁q hq
  have hex : ∃ r', r' ≤ r₁ ∧ ∃ ξ, ¬ ξ < γ ∧ (bA x ξ).carrier r' := by
    refine Classical.byContradiction fun hn => ?_
    have hm : (iInf fun ξ : {ξ // ¬ ξ < γ} => (bA x ξ.1)ᶜ).carrier r₁ :=
      (RO.mem_iInf_iff _ _).2 fun ξ => (RO.mem_compl_iff _ _).2 fun r hr hb =>
        hn ⟨r, hr, ξ.1, ξ.2, hb⟩
    exact hr₁c.2 r₁ (ForcingNotion.refl r₁) (countable_case x γ r₁ ⟨hr₁c.1, hm⟩)
  obtain ⟨r', hr', ξ, hξ, hb⟩ := hex
  have hlt : ∀ β, ζ β < ξ := fun β => by
    rcases Omega1Like.tri ξ γ with h | h | h
    · exact absurd h hξ
    · rw [h]; exact hγ β
    · exact Omega1Like.lt_trans _ _ _ (hγ β) h
  refine ⟨r', ForcingNotion.trans _ _ _ hr' hr₁q, (RO.mem_iSup_iff _ _).2 fun s hs =>
    ⟨s, ForcingNotion.refl s, ξ, (bA x ξ).down r' s hs hb, (RO.mem_iInf_iff _ _).2 fun β =>
      (RO.mem_iSup_iff _ _).2 fun t ht => ⟨t, ForcingNotion.refl t, ⟨ζ β, hlt β⟩, ?_⟩⟩⟩
  exact (enumV (bA x) β.1 (ζ β)).down r₁ t
    (ForcingNotion.trans _ _ _ ht (ForcingNotion.trans _ _ _ hs hr')) (hζ β)

/-- **The uncountable case.** Where `x ⊆ 𝒫(ω̌)` does not inject into `ω̌`, `𝒫(ω̌)` injects
into `x`, via `a ↦ g(f(first occurrence of a))`. -/
theorem uncountable_case : cU x ≤ S2 x := by
  let J := (Nat → Prop) × I × I × (Nat → Prop)
  let s : J → BSet (Col I) := fun j => subsetB j.1
  let t : J → BSet (Col I) := fun j => subsetB j.2.2.2
  let w : J → Col I := fun j => fo j.2.1 j.1 ⊓ enumV (bA x) j.2.1 j.2.2.1 ⊓ catom j.2.2.1 j.2.2.2
  have hfo : ∀ ξ ζ a', enumV (bA x) ξ ζ ⊓ catom ζ a' ≤ fo ζ a' ⊓ BSet.mem (subsetB a') x :=
    fun ξ ζ a' => le_trans' (inf_le_inf (enumV_le_b _ ξ ζ) le_rfl) (bA_inf_catom x ζ a')
  refine le_iSup_of_le (BSet.fname s t w) (BSet.le_isFunc_inf_isInj ?_ ?_ ?_)
  · intro u
    have hP : cU x ⊓ BSet.mem u powersetB ≤
        iSup fun a : Nat → Prop => cU x ⊓ BSet.eq u (subsetB a) :=
      le_trans' (le_inf _ _ _ (inf_le_left _ _) (inf_le_of_right_le (mem_powersetB_le u)))
        inf_iSup_le
    refine le_trans' hP (iSup_le fun a => ?_)
    refine le_trans' (le_inf _ _ _ le_rfl (le_trans' le_top' (top_le_iSup_fo a)))
      (BSet.inf_iSup_le_of fun ξ => ?_)
    refine le_trans' (le_inf _ _ _ le_rfl (inf_le_of_left_le (inf_le_of_left_le
      (enum_total x ξ)))) (BSet.inf_iSup_le_of fun ζ => ?_)
    have hb : enumV (bA x) ξ ζ ≤ iSup fun a' : Nat → Prop => catom ζ a' ⊓ BSet.mem (subsetB a') x :=
      le_trans' (enumV_le_b _ ξ ζ) (iSup_mono fun a' => inf_le_inf (fo_le_catom ζ a') le_rfl)
    refine le_trans' (le_inf _ _ _ le_rfl (inf_le_of_right_le hb))
      (BSet.inf_iSup_le_of fun a' => le_iSup_of_le (a, ξ, ζ, a') ?_)
    show _ ≤ fo ξ a ⊓ enumV (bA x) ξ ζ ⊓ catom ζ a' ⊓ BSet.eq u (subsetB a) ⊓
      BSet.mem (subsetB a') x
    exact le_inf _ _ _ (le_inf _ _ _ (le_inf _ _ _ (le_inf _ _ _ (by lattice_le) (by lattice_le))
      (by lattice_le)) (by lattice_le)) (by lattice_le)
  · rintro ⟨a, ξ, ζ, a'⟩ ⟨a₁, ξ₁, ζ₁, a₁'⟩
    show _ ⊓ (fo ξ a ⊓ enumV (bA x) ξ ζ ⊓ catom ζ a') ⊓
      (fo ξ₁ a₁ ⊓ enumV (bA x) ξ₁ ζ₁ ⊓ catom ζ₁ a₁') ⊓ BSet.eq (subsetB a) (subsetB a₁) ≤
      BSet.eq (subsetB a') (subsetB a₁')
    rcases Classical.em (a = a₁) with ha | ha
    rotate_left
    · rw [eq_subsetB_of_ne ha]; exact inf_le_of_right_le bot_le'
    subst ha
    rcases Classical.em (ξ = ξ₁) with hx | hx
    rotate_left
    · exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
        (fo_disj_pos hx a)) bot_le'
    subst hx
    rcases Classical.em (ζ = ζ₁) with hz | hz
    rotate_left
    · exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
        (enumV_disj _ ξ hz)) bot_le'
    subst hz
    by_cases ha' : a' = a₁'
    · subst ha'; exact le_trans' le_top' (eq_top_iff.1 (BSet.eq_self _))
    · exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
        (catom_disj ha')) bot_le'
  · rintro ⟨a, ξ, ζ, a'⟩ ⟨a₁, ξ₁, ζ₁, a₁'⟩
    show _ ⊓ (fo ξ a ⊓ enumV (bA x) ξ ζ ⊓ catom ζ a') ⊓
      (fo ξ₁ a₁ ⊓ enumV (bA x) ξ₁ ζ₁ ⊓ catom ζ₁ a₁') ⊓ BSet.eq (subsetB a') (subsetB a₁') ≤
      BSet.eq (subsetB a) (subsetB a₁)
    rcases Classical.em (a' = a₁') with ha' | ha'
    rotate_left
    · rw [eq_subsetB_of_ne ha']; exact inf_le_of_right_le bot_le'
    subst ha'
    rcases Classical.em (ζ = ζ₁) with hz | hz
    rotate_left
    · refine le_trans' (le_trans' (le_inf _ _ _ ?_ ?_) (fo_disj_pos hz a')) bot_le'
      · exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (hfo ξ ζ a'))
          (inf_le_left _ _)
      · exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
          (hfo ξ₁ ζ₁ a')) (inf_le_left _ _)
    subst hz
    rcases Classical.em (ξ = ξ₁) with hx | hx
    rotate_left
    · exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
        (enumV_inj _ hx ζ)) bot_le'
    subst hx
    by_cases ha : a = a₁
    · subst ha; exact le_trans' le_top' (eq_top_iff.1 (BSet.eq_self _))
    · exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
        (fo_disj_real ha)) bot_le'

/-- **CH for subsets of `𝒫(ω̌)`.** In `V^{Col I}`, every `x ⊆ 𝒫(ω̌)` injects into `ω̌` or
receives an injection from `𝒫(ω̌)`: `⟦x ⊆ 𝒫(ω̌)⟧ ≤ ⟦x ↪ ω̌⟧ ⊔ ⟦𝒫(ω̌) ↪ x⟧`. -/
theorem subset_le_S1_sup_S2 : BSet.subset x powersetB ≤ S1 x ⊔ S2 x := by
  let s := BSet.subset x powersetB
  calc s ≤ s ⊓ (S1 x ⊔ (S1 x)ᶜ) := le_inf _ _ _ le_rfl (le_trans' le_top' top_le_sup_compl')
    _ ≤ (s ⊓ S1 x) ⊔ (s ⊓ (S1 x)ᶜ) := inf_sup_le _ _ _
    _ ≤ S1 x ⊔ S2 x := sup_le_sup (inf_le_right _ _) (uncountable_case x)

end Cases

/-- **CH holds in the collapse model.** For every `ω₁`-like `I`, `⟦CH⟧ = ⊤` in `V^{Col I}`. -/
theorem val_CH_eq_top (e : Nat → BSet (Col I)) : (VB (Col I)).val e CH = ⊤ := by
  rw [val_CH]
  refine eq_top_iff.2 (le_iInf fun w => le_iInf fun p => le_himp_iff.2 ?_)
  rw [top_inf]
  refine le_iInf fun x => le_himp_iff.2 ?_
  have hE1 : BSet.isOmega w ⊓ BSet.isPow p w ≤ BSet.eq omegaB w :=
    inf_le_of_left_le (le_trans' (BSet.isOmega_le_eq w) (BSet.eq_symm _ _))
  have hE2 : BSet.isOmega w ⊓ BSet.isPow p w ≤ BSet.eq powersetB p :=
    le_trans' (le_trans' (le_inf _ _ _ (inf_le_right _ _) (inf_le_of_left_le
      (BSet.isOmega_le_eq w))) (BSet.isPow_le_eq p w)) (BSet.eq_symm _ _)
  have hs : BSet.isOmega w ⊓ BSet.isPow p w ⊓ BSet.subset x p ≤ BSet.subset x powersetB :=
    le_trans' (le_inf _ _ _ (inf_le_right _ _) (inf_le_of_left_le
      (le_trans' hE2 (BSet.eq_symm _ _)))) (BSet.subset_congr _ _ _)
  have hxx : ⊤ ≤ BSet.eq x x := by rw [BSet.eq_self]; exact le_rfl
  refine le_trans' (le_inf _ _ _ (le_trans' hs (subset_le_S1_sup_S2 x))
    (le_inf _ _ _ (inf_le_of_left_le hE1) (inf_le_of_left_le hE2))) ?_
  refine le_trans' sup_inf_le (sup_le_sup ?_ ?_)
  · refine le_trans' iSup_inf_le (iSup_mono fun f => ?_)
    refine le_inf _ _ _ ?_ (inf_le_of_left_le (inf_le_right _ _))
    exact le_trans' (le_inf _ _ _ (le_inf _ _ _ (inf_le_of_left_le (inf_le_left _ _))
      (le_trans' le_top' hxx)) (inf_le_of_right_le (inf_le_left _ _)))
      (BSet.isFunc_congr f x x omegaB w)
  · refine le_trans' iSup_inf_le (iSup_mono fun f => ?_)
    refine le_inf _ _ _ ?_ ?_
    · exact le_trans' (le_inf _ _ _ (le_inf _ _ _ (inf_le_of_left_le (inf_le_left _ _))
        (inf_le_of_right_le (inf_le_right _ _))) (le_trans' le_top' hxx))
        (BSet.isFunc_congr f powersetB p x x)
    · exact le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_right _ _))
        (inf_le_of_right_le (inf_le_right _ _))) (BSet.isInj_congr f powersetB p)

/-! ### The collapse over the ground `ω₁` -/

/-- **`V^{Col(ω₁)} ⊨ CH`**: the Continuum Hypothesis has truth value `⊤` in the Boolean-valued
universe over the algebra collapsing `2^ℵ₀` onto `ℵ₁`. -/
theorem VB_CH (e : Nat → BSet (Col W₁)) : (VB (Col W₁)).val e CH = ⊤ := val_CH_eq_top e

/-- **ZF does not refute CH** (the forcing counterpart of Gödel 1938). No derivation of `¬CH`
from the axioms `ZF` exists in the first-order natural deduction calculus. -/
theorem ZF_not_proves_notCH : ¬ (ZF ⊢₁ CH.neg) := by
  refine not_proves_of_val (VB (Col W₁)) (fun _ => BSet.empty) (VB_models_ZF _) ?_
  show (VB (Col W₁)).val _ CH ⇨ ⊥ ≠ ⊤
  rw [VB_CH]
  intro h
  exact col_top_ne_bot W₁ (le_antisymm' (himp_eq_top_iff.1 h) bot_le')

/-- **ZF + CH is consistent**: it does not derive `⊥`. -/
theorem ZF_CH_consistent : ¬ (Theory.insert ZF CH ⊢₁ Formula.bot) := by
  refine not_proves_of_val (VB (Col W₁)) (fun _ => BSet.empty) ?_ (col_top_ne_bot W₁).symm
  rintro ψ (rfl | h)
  · exact VB_CH _
  · exact VB_models_ZF _ ψ h

/-- **The independence of the Continuum Hypothesis from ZF.** ZF proves neither `CH` nor
`¬CH` (Gödel 1938, Cohen 1963; here both halves by Boolean-valued models: the Cohen algebra
over `ω₂` and the collapse algebra over `ω₁`). -/
theorem CH_independent_ZF : ¬ (ZF ⊢₁ CH) ∧ ¬ (ZF ⊢₁ CH.neg) :=
  ⟨ZF_not_proves_CH, ZF_not_proves_notCH⟩

end Foundations.Forcing
