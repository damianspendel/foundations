import Foundations.Constructible.Hierarchy

/-!
# The reflection principle for `L` and the separation scheme in `L`

## Why reflection is needed

To show that `L` satisfies separation, take a constructible set `a`, constructible parameters
and a formula `φ`. The set `S = {z ∈ a | φ^L(z)}` must again be constructible. Each new
constructible set is definable over some *set* `L_α`, but `φ^L` quantifies over the whole
*class* `L`. The bridge is the **reflection principle** (Lévy–Montague, here for the
`L`-hierarchy): for every formula `φ` and every ordinal `β` there is an ordinal `α ⊇ β` such that
`φ` is **absolute** between `L_α` and `L`, i.e. for parameters in `L_α`,
`φ^L ↔ φ^{L_α}`. Then `S = {z ∈ a | φ^{L_α}(z)} ∈ Def(L_α) ⊆ L_{α+1}`.

## The proof

* **Tarski–Vaught step** (`absolute_of_closed`). Call `α` *closed* for a formula `χ` if
  whenever `∃y ∈ L χ(y, e)` with parameters `e` in `L_α`, there is already such a witness in
  `L_α`, and likewise for `¬χ`. If `α` is closed for the bodies of all quantifiers of `φ`, then `φ`
  is absolute for `L_α`. The proof is by induction on `φ`: connectives are immediate and each
  quantifier is handled by the closure condition.
* **Closing off** (`exists_closed`). Given finitely many formulas and an ordinal `β`, iterate
  `γ ↦ γ ∪ sup{chosen witness stages for all parameter lists from L_γ}` along `ℕ` and take the
  supremum `α`. Parameters from `L_α` occur already at a finite stage. Only the finitely many
  variables of a formula matter (`RSat_congr`), so a parameter list can be truncated to lie in a
  single `L_{γₙ}`. The suprema exist because the ambient universe `ZFSet` has replacement for
  arbitrary operations, and parameter lists `ℕ → Small (L_γ)` form a small type.

The result `separation_L` is the separation scheme for `L`, the step that needs the most
machinery among the ZF axioms. Collection and power set in `L` (next file) need only the
bounding lemma `exists_stage`, since the ambient universe already satisfies them.
-/

namespace Foundations.Constructible

open Foundations.Logic.FO Foundations.Forcing Foundations.Sets Foundations.Sets.ZFSet
open BStructure (liftBy)

/-- The bodies of all quantifier subformulas of a formula. -/
def qbodies : Formula LSet → List (Formula LSet)
  | .bot => []
  | .eq _ _ => []
  | .rel _ _ => []
  | .imp φ ψ => qbodies φ ++ qbodies ψ
  | .conj φ ψ => qbodies φ ++ qbodies ψ
  | .disj φ ψ => qbodies φ ++ qbodies ψ
  | .all φ => φ :: qbodies φ
  | .ex φ => φ :: qbodies φ

/-- Absoluteness. `φ` is absolute between `L_α` and `L` if for every environment with
values in `L_α`, `φ^L ↔ φ^{L_α}`. -/
def Absolute (α : ZFSet) (φ : Formula LSet) : Prop :=
  ∀ e : Nat → ZFSet, (∀ n, e n ∈ Lev α) → (RSat InL e φ ↔ RSat (· ∈ Lev α) e φ)

/-- `L_α` *contains witnesses for `χ`*: whenever `χ(y, e)` holds in `L` for some constructible
`y` and parameters `e` in `L_α`, it holds for some `y ∈ L_α`. -/
def Witnessed (α : ZFSet) (χ : Formula LSet) : Prop :=
  ∀ e : Nat → ZFSet, (∀ n, e n ∈ Lev α) → (∃ y, InL y ∧ RSat InL (BEnv.cons y e) χ) →
    ∃ y ∈ Lev α, RSat InL (BEnv.cons y e) χ

/-- `α` is *closed* for `χ` if `L_α` contains witnesses for both `χ` and `¬χ`. -/
def Closed (α : ZFSet) (χ : Formula LSet) : Prop := Witnessed α χ ∧ Witnessed α χ.neg

/-- Pushing a value of `L_α` onto an environment in `L_α`. -/
theorem cons_mem {α x : ZFSet} {e : Nat → ZFSet} (hx : x ∈ Lev α) (he : ∀ n, e n ∈ Lev α) :
    ∀ n, BEnv.cons x e n ∈ Lev α
  | 0 => hx
  | n + 1 => he n

/-- **Tarski–Vaught criterion for `L_α ⊆ L`.** If `α` is closed for the body of every
quantifier occurring in `φ`, then `φ` is absolute between `L_α` and `L`. -/
theorem absolute_of_closed {α : ZFSet} (hα : IsOrdinal α) :
    ∀ φ : Formula LSet, (∀ χ ∈ qbodies φ, Closed α χ) → Absolute α φ
  | .bot, _ => fun _ _ => Iff.rfl
  | .eq _ _, _ => fun _ _ => Iff.rfl
  | .rel _ _, _ => fun _ _ => Iff.rfl
  | .imp φ ψ, h => fun e he =>
      imp_congr (absolute_of_closed hα φ (fun χ hχ => h χ (List.mem_append_left _ hχ)) e he)
        (absolute_of_closed hα ψ (fun χ hχ => h χ (List.mem_append_right _ hχ)) e he)
  | .conj φ ψ, h => fun e he =>
      and_congr (absolute_of_closed hα φ (fun χ hχ => h χ (List.mem_append_left _ hχ)) e he)
        (absolute_of_closed hα ψ (fun χ hχ => h χ (List.mem_append_right _ hχ)) e he)
  | .disj φ ψ, h => fun e he =>
      or_congr (absolute_of_closed hα φ (fun χ hχ => h χ (List.mem_append_left _ hχ)) e he)
        (absolute_of_closed hα ψ (fun χ hχ => h χ (List.mem_append_right _ hχ)) e he)
  | .all φ, h => fun e he => by
      have ih := absolute_of_closed hα φ (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ))
      have hc := h φ List.mem_cons_self
      show (∀ x, InL x → RSat InL _ φ) ↔ (∀ x, x ∈ Lev α → RSat _ _ φ)
      constructor
      · intro hall x hx
        exact (ih _ (cons_mem hx he)).1 (hall x (InL.of_mem_Lev hα hx))
      · intro hall
        apply Classical.byContradiction
        intro hn
        have hex : ∃ y, InL y ∧ RSat InL (BEnv.cons y e) φ.neg :=
          Classical.byContradiction fun hne => hn fun x hx =>
            Classical.byContradiction fun hφ => hne ⟨x, hx, hφ⟩
        obtain ⟨y, hy, hφ⟩ := hc.2 e he hex
        exact hφ ((ih _ (cons_mem hy he)).2 (hall y hy))
  | .ex φ, h => fun e he => by
      have ih := absolute_of_closed hα φ (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ))
      have hc := h φ List.mem_cons_self
      show (∃ x, InL x ∧ RSat InL _ φ) ↔ (∃ x, x ∈ Lev α ∧ RSat _ _ φ)
      constructor
      · intro hex
        obtain ⟨y, hy, hφ⟩ := hc.1 e he hex
        exact ⟨y, hy, (ih _ (cons_mem hy he)).1 hφ⟩
      · rintro ⟨x, hx, hφ⟩
        exact ⟨x, InL.of_mem_Lev hα hx, (ih _ (cons_mem hx he)).2 hφ⟩

/-! ### Closing off under witnesses -/

/-- A stage containing a witness for `χ(·, e)` in `L`, if there is one (`∅` otherwise). -/
noncomputable def wit (χ : Formula LSet) (e : Nat → ZFSet) : ZFSet :=
  open Classical in
  if h : ∃ y, InL y ∧ RSat InL (BEnv.cons y e) χ then lrank (Classical.choose h) else ∅

/-- Witness stages are ordinals. -/
theorem wit_ord (χ : Formula LSet) (e : Nat → ZFSet) : IsOrdinal (wit χ e) := by
  unfold wit; split
  · exact lrank_ord _
  · exact isOrdinal_empty

/-- The witness stage contains a witness, when one exists. -/
theorem wit_spec {χ : Formula LSet} {e : Nat → ZFSet}
    (h : ∃ y, InL y ∧ RSat InL (BEnv.cons y e) χ) :
    ∃ y ∈ Lev (wit χ e), RSat InL (BEnv.cons y e) χ := by
  unfold wit
  simp only [h, ↓reduceDIte]
  exact ⟨_, mem_Lev_lrank (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

/-- One closing-off step: `γ` together with witness stages for every formula of `Ψ` and every
parameter list from `L_γ`. -/
noncomputable def closeStep (Ψ : List (Formula LSet)) (γ : ZFSet) : ZFSet :=
  γ ∪ ⋃₀ ofFamily fun p : {χ // χ ∈ Ψ} × (Nat → Small (Lev γ)) =>
    wit p.1.1 fun n => (p.2 n).val

/-- The closing-off step yields an ordinal containing `γ`. -/
theorem closeStep_ord (Ψ : List (Formula LSet)) {γ : ZFSet} (hγ : IsOrdinal γ) :
    IsOrdinal (closeStep Ψ γ) ∧ γ ⊆ closeStep Ψ γ := by
  have hU : IsOrdinal (⋃₀ ofFamily fun p : {χ // χ ∈ Ψ} × (Nat → Small (Lev γ)) =>
      wit p.1.1 fun n => (p.2 n).val) := isOrdinal_sUnion fun x hx => by
    obtain ⟨p, rfl⟩ := mem_ofFamily.1 hx
    exact wit_ord _ _
  exact ⟨(ord_max hγ hU).1, (ord_max hγ hU).2.1⟩

/-- The witness stage for a parameter list in `L_γ` lies inside `closeStep Ψ γ`. -/
theorem wit_subset_closeStep {Ψ : List (Formula LSet)} {γ : ZFSet} {χ : Formula LSet}
    (hχ : χ ∈ Ψ) {e : Nat → ZFSet} (he : ∀ n, e n ∈ Lev γ) : wit χ e ⊆ closeStep Ψ γ := by
  intro z hz
  refine mem_union.2 (Or.inr (mem_sUnion.2 ⟨wit χ e, mem_ofFamily.2
    ⟨(⟨χ, hχ⟩, fun n => Small.ofMem (e n) (he n)), ?_⟩, hz⟩))
  show wit χ e = wit χ fun n => (Small.ofMem (e n) (he n)).val
  congr 1; funext n; exact (Small.val_ofMem _ _).symm

/-- The closing-off chain `β = c₀ ⊆ c₁ ⊆ …`, with `c_{n+1} = closeStep(c_n) + 1`. -/
noncomputable def chain (Ψ : List (Formula LSet)) (β : ZFSet) : Nat → ZFSet
  | 0 => β
  | n + 1 => succ (closeStep Ψ (chain Ψ β n))

/-- Every stage of the chain is an ordinal. -/
theorem chain_ord (Ψ : List (Formula LSet)) {β : ZFSet} (hβ : IsOrdinal β) :
    ∀ n, IsOrdinal (chain Ψ β n)
  | 0 => hβ
  | n + 1 => (closeStep_ord Ψ (chain_ord Ψ hβ n)).1.succ

/-- The chain is increasing by one step. -/
theorem chain_step (Ψ : List (Formula LSet)) (β : ZFSet) (n : Nat) :
    closeStep Ψ (chain Ψ β n) ⊆ chain Ψ β (n + 1) :=
  fun _ hz => mem_succ.2 (Or.inr hz)

/-- The chain is increasing. -/
theorem chain_mono (Ψ : List (Formula LSet)) {β : ZFSet} (hβ : IsOrdinal β) {n : Nat} :
    ∀ {m}, n ≤ m → chain Ψ β n ⊆ chain Ψ β m
  | 0, h => by rw [Nat.le_zero.1 h]; exact subset_refl _
  | m + 1, h => by
      rcases Nat.lt_or_eq_of_le h with h | h
      · exact subset_trans (chain_mono Ψ hβ (Nat.le_of_lt_succ h))
          (subset_trans (closeStep_ord Ψ (chain_ord Ψ hβ m)).2 (chain_step Ψ β m))
      · rw [h]; exact subset_refl _

/-- The supremum of the closing-off chain. -/
noncomputable def closure (Ψ : List (Formula LSet)) (β : ZFSet) : ZFSet :=
  ⋃₀ ofFamily (chain Ψ β)

/-- Members of `L_α`, for `α` the supremum of the chain, appear at a finite stage. -/
theorem mem_Lev_closure {Ψ : List (Formula LSet)} {β z : ZFSet}
    (hz : z ∈ Lev (closure Ψ β)) : ∃ m, z ∈ Lev (chain Ψ β m) := by
  obtain ⟨y, hy, hzy⟩ := mem_Lev.1 hz
  obtain ⟨w, hw, hyw⟩ := mem_sUnion.1 hy
  obtain ⟨m, rfl⟩ := mem_ofFamily.1 hw
  exact ⟨m, Def_subset_Lev hyw hzy⟩

/-- Each stage of the chain is below its supremum. -/
theorem chain_subset_closure (Ψ : List (Formula LSet)) (β : ZFSet) (m : Nat) :
    chain Ψ β m ⊆ closure Ψ β :=
  subset_sUnion_of_mem (mem_ofFamily.2 ⟨m, rfl⟩)

/-- Finitely many parameters from `L_α` appear together at a finite stage of the chain. -/
theorem env_at_stage {Ψ : List (Formula LSet)} {β : ZFSet} (hβ : IsOrdinal β)
    {e : Nat → ZFSet} (he : ∀ n, e n ∈ Lev (closure Ψ β)) :
    ∀ k, ∃ m, ∀ n < k, e n ∈ Lev (chain Ψ β m)
  | 0 => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
      obtain ⟨m₁, h₁⟩ := env_at_stage hβ he k
      obtain ⟨m₂, h₂⟩ := mem_Lev_closure (he k)
      refine ⟨max m₁ m₂, fun n hn => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with hn | rfl
      · exact Lev_mono (chain_mono Ψ hβ (Nat.le_max_left _ _)) (h₁ n hn)
      · exact Lev_mono (chain_mono Ψ hβ (Nat.le_max_right _ _)) h₂

/-- Closing off. For every finite list of formulas `Ψ` and every ordinal `β` there is an
ordinal `α ⊇ β` such that `L_α` contains witnesses for every formula of `Ψ`. -/
theorem exists_witnessed (Ψ : List (Formula LSet)) {β : ZFSet} (hβ : IsOrdinal β) :
    ∃ α, IsOrdinal α ∧ β ⊆ α ∧ ∀ χ ∈ Ψ, Witnessed α χ := by
  refine ⟨closure Ψ β, isOrdinal_sUnion fun x hx => ?_, chain_subset_closure Ψ β 0,
    fun χ hχ e he hex => ?_⟩
  · obtain ⟨m, rfl⟩ := mem_ofFamily.1 hx
    exact chain_ord Ψ hβ m
  classical
  obtain ⟨m, hm⟩ := env_at_stage hβ he (bnd χ)
  -- truncate the parameters to a single stage `c_{m+1}`
  let M := m + 1
  have h0 : (∅ : ZFSet) ∈ Lev (chain Ψ β M) := empty_mem_Lev (mem_succ_self _)
  let e' : Nat → ZFSet := fun n => if n < bnd χ then e n else ∅
  have he' : ∀ n, e' n ∈ Lev (chain Ψ β M) := fun n => by
    by_cases hn : n < bnd χ
    · simp only [e', hn, ↓reduceIte]
      exact Lev_mono (chain_mono Ψ hβ (Nat.le_succ m)) (hm n hn)
    · simp only [e', hn, ↓reduceIte]; exact h0
  have hagree : ∀ y, ∀ n < bnd χ, BEnv.cons y e n = BEnv.cons y e' n := by
    intro y n hn
    cases n with
    | zero => rfl
    | succ n => simp only [cons_succ, e', show n < bnd χ by omega, ↓reduceIte]
  have hex' : ∃ y, InL y ∧ RSat InL (BEnv.cons y e') χ := by
    obtain ⟨y, hy, h⟩ := hex
    exact ⟨y, hy, (RSat_congr _ χ (hagree y)).1 h⟩
  obtain ⟨y, hy, h⟩ := wit_spec hex'
  have hsub : wit χ e' ⊆ closure Ψ β :=
    subset_trans (wit_subset_closeStep hχ he')
      (subset_trans (chain_step Ψ β M) (chain_subset_closure Ψ β (M + 1)))
  exact ⟨y, Lev_mono hsub hy, (RSat_congr _ χ (hagree y)).2 h⟩

/-- **The reflection principle for `L`.** For every formula `φ` and every ordinal `β` there is
an ordinal `α ⊇ β` such that `φ` is absolute between `L_α` and `L`: for all parameters in
`L_α`, `φ^L ↔ φ^{L_α}`. -/
theorem reflection_L (φ : Formula LSet) {β : ZFSet} (hβ : IsOrdinal β) :
    ∃ α, IsOrdinal α ∧ β ⊆ α ∧ Absolute α φ := by
  obtain ⟨α, hα, hβα, hW⟩ := exists_witnessed (qbodies φ ++ (qbodies φ).map Formula.neg) hβ
  refine ⟨α, hα, hβα, absolute_of_closed hα φ fun χ hχ => ⟨hW χ ?_, hW χ.neg ?_⟩⟩
  · exact List.mem_append_left _ hχ
  · exact List.mem_append_right _ (List.mem_map_of_mem hχ)

/-- **Separation in `L`.** For a constructible set `a`, constructible parameters `e` and any
formula `φ`, the set `{z ∈ a | φ^L(z, e)}` is constructible. -/
theorem separation_L (φ : Formula LSet) {a : ZFSet} (ha : InL a) {e : Nat → ZFSet}
    (he : ∀ n, InL (e n)) : InL (sep (fun z => RSat InL (BEnv.cons z e) φ) a) := by
  classical
  obtain ⟨β₁, hβ₁, hβ₁e⟩ := exists_stage_env (k := bnd φ) fun n _ => he n
  obtain ⟨hβ, h₁, h₂⟩ := ord_max hβ₁ (lrank_ord a)
  obtain ⟨α, hα, hβα, habs⟩ := reflection_L φ hβ
  have haα : a ∈ Lev α := Lev_mono (subset_trans h₂ hβα) (mem_Lev_lrank ha)
  let e' : Nat → ZFSet := fun n => if n < bnd φ then e n else a
  have he' : ∀ n, e' n ∈ Lev α := fun n => by
    by_cases hn : n < bnd φ
    · simp only [e', hn, ↓reduceIte]; exact Lev_mono (subset_trans h₁ hβα) (hβ₁e n hn)
    · simp only [e', hn, ↓reduceIte]; exact haα
  have hagree : ∀ y, ∀ n < bnd φ, BEnv.cons y e n = BEnv.cons y e' n := by
    intro y n hn
    cases n with
    | zero => rfl
    | succ n => simp only [cons_succ, e', show n < bnd φ by omega, ↓reduceIte]
  refine InL.of_mem_Def hα (Def_intro (fun z hz => Lev_transitive hα.1 a haα (sep_subset _ _ hz))
    (.conj (memF (v 0) (v 1)) (liftBy 1 φ)) (BEnv.cons a e') (fun n _ => cons_mem haα he' n)
    fun z hz => ?_)
  show z ∈ sep _ a ↔ z ∈ a ∧ RSat _ _ (liftBy 1 φ)
  rw [RSat_liftBy _ 1 φ z _ e' (fun _ => rfl), mem_sep, ← habs _ (cons_mem hz he'),
    ← RSat_congr _ φ (hagree z)]

end Foundations.Constructible
