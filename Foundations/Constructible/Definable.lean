import Foundations.Constructible.RelSat

/-!
# The definable power set `Def(X)`

## Definability

The power set `𝒫(X)` contains *every* subset of `X`, including the ones no description can
pick out. Gödel's construction replaces it by the much thinner **definable power set**

  `Def(X) = { {y ∈ X | (X, ∈) ⊨ φ[y, a₁, …, aₙ]} | φ a formula of LSet, a₁, …, aₙ ∈ X }`,

the subsets of `X` that are first-order definable over the structure `(X, ∈)` from finitely
many parameters taken from `X` itself. The quantifiers of `φ` range only over `X`: a set is
admitted at the next stage only if it can be described using what is already there. This is
the "predicative" step that, iterated along the ordinals, builds the constructible universe
`L` in the next file.

## The formal definition

Satisfaction is the library's Tarskian `Formula.Sat` in the structure `setStr X`, whose domain
is the small type `Small X` of members of `X`. An environment `e : ℕ → Small X` supplies the
parameters; only the finitely many variables occurring in `φ` matter. Because a structure with
empty domain has no environments, the empty set is added by hand: `Def(X)` is `{∅}` together with
all sets `defSet X φ e`. For non-empty `X` this adds nothing new, since `∅` is defined by `⊥`.
Both `Formula LSet` and `ℕ → Small X` live in `Type`, so the family of definable subsets is
indexed by a small type and `Def(X)` is a genuine `ZFSet`.

The working characterisation `mem_Def` re-expresses everything through the relativised
satisfaction `RSat (· ∈ X)` of the previous file, with parameters as plain sets.

## Closure properties

`Def(X) ⊆ 𝒫(X)`, `∅ ∈ Def(X)`, `X ∈ Def(X)`, every finite subset of `X` is in `Def(X)`, and
`Def(X)` is a Boolean algebra of subsets of `X` (closed under complement, binary union and binary
intersection). If `X` is transitive then `X ⊆ Def(X)`: each member `a` of `X` is the subset
`{y ∈ X | y ∈ a}`, defined with the parameter `a`.
-/

namespace Foundations.Constructible

open Foundations.Logic.FO Foundations.Forcing Foundations.Sets Foundations.Sets.ZFSet
open BStructure (liftBy)

/-- The subset of `X` defined over `(X, ∈)` by the formula `φ` (variable `0` is the element
tested) with the parameters `e`. -/
noncomputable def defSet (X : ZFSet) (φ : Formula LSet) (e : Nat → Small X) : ZFSet :=
  sep (fun y => ∃ h : y ∈ X, Formula.Sat (setStr X) (Env.cons (Small.ofMem y h) e) φ) X

/-- Members of `defSet X φ e`: the members `y` of `X` for which `φ[y, e]` holds in `X`. -/
theorem mem_defSet {X : ZFSet} {φ : Formula LSet} {e : Nat → Small X} {y : ZFSet} :
    y ∈ defSet X φ e ↔ y ∈ X ∧ RSat (· ∈ X) (BEnv.cons y fun n => (e n).val) φ := by
  unfold defSet
  rw [mem_sep]
  constructor
  · rintro ⟨hy, _, h⟩
    rw [sat_setStr_iff, val_env_cons, Small.val_ofMem] at h
    exact ⟨hy, h⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, hy, ?_⟩
    rw [sat_setStr_iff, val_env_cons, Small.val_ofMem]
    exact h

/-- **The definable power set.** `Def(X)` consists of the subsets of `X` definable over
`(X, ∈)` by a formula of `LSet` with parameters from `X` (and `∅`, which matters only for
`X = ∅`). -/
noncomputable def Def (X : ZFSet) : ZFSet :=
  insert ∅ (ofFamily fun p : Formula LSet × (Nat → Small X) => defSet X p.1 p.2)

/-- **Membership in `Def(X)`.** A set is definable over `X` iff it is empty or of the form
`{y ∈ X | φ^X[y, e]}` for a formula `φ` and parameters `e n ∈ X`. -/
theorem mem_Def {X z : ZFSet} :
    z ∈ Def X ↔ z = ∅ ∨ ∃ (φ : Formula LSet) (e : Nat → ZFSet), (∀ n, e n ∈ X) ∧
      ∀ y, y ∈ z ↔ y ∈ X ∧ RSat (· ∈ X) (BEnv.cons y e) φ := by
  unfold Def
  rw [mem_insert, mem_ofFamily]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨⟨φ, e⟩, rfl⟩
    exact ⟨φ, fun n => (e n).val, fun n => (e n).val_mem, fun y => mem_defSet⟩
  · rintro ⟨φ, e, he, h⟩
    refine ⟨⟨φ, fun n => Small.ofMem (e n) (he n)⟩, ext fun y => ?_⟩
    rw [h y, mem_defSet]
    have : (fun n => (Small.ofMem (e n) (he n)).val) = e := funext fun n => Small.val_ofMem _ _
    rw [this]

/-- Definable sets are subsets. `Def(X) ⊆ 𝒫(X)`. -/
theorem subset_of_mem_Def {X z : ZFSet} (h : z ∈ Def X) : z ⊆ X := by
  rcases mem_Def.1 h with rfl | ⟨φ, e, _, hz⟩
  · exact empty_subset X
  · exact fun y hy => ((hz y).1 hy).1

/-- `Def(X)` is a subset of the power set `𝒫(X)`. -/
theorem Def_subset_powerset (X : ZFSet) : Def X ⊆ powerset X :=
  fun _ h => mem_powerset.2 (subset_of_mem_Def h)

/-- The empty set is definable over every set. -/
theorem empty_mem_Def (X : ZFSet) : (∅ : ZFSet) ∈ Def X := mem_Def.2 (Or.inl rfl)

/-- Introduction rule for `Def(X)`. If `z ⊆ X` and, for every `y ∈ X`, `y ∈ z` iff
`φ^X[y, e]`, where every parameter actually used by `φ` lies in `X`, then `z ∈ Def(X)`.
(Only the variables below `bnd φ` matter; the others may hold arbitrary sets.) -/
theorem Def_intro {X z : ZFSet} (hz : z ⊆ X) (φ : Formula LSet) (e : Nat → ZFSet)
    (he : ∀ n, n + 1 < bnd φ → e n ∈ X)
    (h : ∀ y ∈ X, y ∈ z ↔ RSat (· ∈ X) (BEnv.cons y e) φ) : z ∈ Def X := by
  classical
  by_cases hX : ∃ a, a ∈ X
  · obtain ⟨a, ha⟩ := hX
    let e' : Nat → ZFSet := fun n => if n + 1 < bnd φ then e n else a
    have hagree : ∀ y, ∀ n < bnd φ, BEnv.cons y e n = BEnv.cons y e' n := by
      intro y n hn
      cases n with
      | zero => rfl
      | succ n => simp only [cons_succ, e', hn, ↓reduceIte]
    refine mem_Def.2 (Or.inr ⟨φ, e', fun n => ?_, fun y => ?_⟩)
    · by_cases hn : n + 1 < bnd φ
      · simp only [e', hn, ↓reduceIte]; exact he n hn
      · simp only [e', hn, ↓reduceIte]; exact ha
    · rw [← RSat_congr _ φ (hagree y)]
      exact ⟨fun hy => ⟨hz hy, (h y (hz hy)).1 hy⟩, fun ⟨hy, hφ⟩ => (h y hy).2 hφ⟩
  · have : z = ∅ := eq_empty_of_forall_not_mem fun y hy => hX ⟨y, hz hy⟩
    rw [this]; exact empty_mem_Def X

/-- A definable set comes with a defining formula and parameters in `X`, provided `X` is
non-empty (then `∅` is defined by `⊥`). -/
theorem Def_spec {X z a : ZFSet} (ha : a ∈ X) (hz : z ∈ Def X) :
    ∃ (φ : Formula LSet) (e : Nat → ZFSet), (∀ n, e n ∈ X) ∧
      ∀ y, y ∈ z ↔ y ∈ X ∧ RSat (· ∈ X) (BEnv.cons y e) φ := by
  rcases mem_Def.1 hz with rfl | h
  · exact ⟨.bot, fun _ => a, fun _ => ha, fun y =>
      ⟨fun hy => absurd hy (not_mem_empty y), fun ⟨_, h⟩ => h.elim⟩⟩
  · exact h

/-! ### Closure properties -/

/-- **`X` is definable over itself.** `X ∈ Def(X)`, defined by a tautology. -/
theorem self_mem_Def (X : ZFSet) : X ∈ Def X :=
  Def_intro (subset_refl X) (.imp .bot .bot) (fun _ => ∅) (fun n h => absurd h (by simp [bnd]))
    fun _ _ => ⟨fun _ h => h, fun _ => by assumption⟩

/-- Pairs are definable. If `a, b ∈ X` then `{a, b} ∈ Def(X)`, defined by
`v₀ = v₁ ∨ v₀ = v₂`. -/
theorem pair_mem_Def {X a b : ZFSet} (ha : a ∈ X) (hb : b ∈ X) : ({a, b} : ZFSet) ∈ Def X := by
  refine Def_intro (fun y hy => ?_) (.disj (.eq (v 0) (v 1)) (.eq (v 0) (v 2)))
    (fun n => if n = 0 then a else b) (fun n hn => ?_) (fun y _ => ?_)
  · rcases mem_pair.1 hy with rfl | rfl <;> assumption
  · by_cases h0 : n = 0
    · simp only [h0, ↓reduceIte]; exact ha
    · simp only [h0, ↓reduceIte]; exact hb
  · show y ∈ ({a, b} : ZFSet) ↔ y = a ∨ y = b
    exact mem_pair

/-- Singletons are definable. If `a ∈ X` then `{a} ∈ Def(X)`. -/
theorem singleton_mem_Def {X a : ZFSet} (ha : a ∈ X) : ({a} : ZFSet) ∈ Def X := by
  have : ({a, a} : ZFSet) = {a} := ext fun y => by rw [mem_pair, mem_singleton, or_self]
  rw [← this]; exact pair_mem_Def ha ha

/-- Adding a point to a definable set. If `z ∈ Def(X)` and `a ∈ X`, then
`z ∪ {a} ∈ Def(X)`, defined by `v₀ = a ∨ φ`. -/
theorem insert_mem_Def {X z a : ZFSet} (hz : z ∈ Def X) (ha : a ∈ X) : insert a z ∈ Def X := by
  obtain ⟨φ, e, he, hφ⟩ := Def_spec ha hz
  refine Def_intro (fun y hy => ?_) (.disj (.eq (v 0) (v 1)) (liftBy 1 φ)) (BEnv.cons a e)
    (fun n _ => ?_) (fun y hy => ?_)
  · rcases mem_insert.1 hy with rfl | hy
    · exact ha
    · exact subset_of_mem_Def hz hy
  · cases n with
    | zero => exact ha
    | succ n => exact he n
  · show y ∈ insert a z ↔ y = a ∨ RSat _ _ (liftBy 1 φ)
    rw [RSat_liftBy _ 1 φ y _ e (fun _ => rfl), mem_insert, hφ]
    exact or_congr Iff.rfl ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

/-- The finite set with the members of a list. -/
noncomputable def finSet : List ZFSet → ZFSet
  | [] => ∅
  | a :: l => insert a (finSet l)

/-- Members of `finSet l` are the entries of `l`. -/
theorem mem_finSet {y : ZFSet} : ∀ {l : List ZFSet}, y ∈ finSet l ↔ y ∈ l
  | [] => by simp only [finSet, List.not_mem_nil, iff_false]; exact not_mem_empty y
  | a :: l => by rw [finSet, mem_insert, mem_finSet, List.mem_cons]

/-- **Finite subsets are definable.** For every list of members of `X`, the finite set of its
entries belongs to `Def(X)`. -/
theorem finSet_mem_Def {X : ZFSet} : ∀ {l : List ZFSet}, (∀ a ∈ l, a ∈ X) → finSet l ∈ Def X
  | [], _ => empty_mem_Def X
  | a :: _, h => insert_mem_Def (finSet_mem_Def fun b hb => h b (List.mem_cons_of_mem a hb))
      (h a List.mem_cons_self)

/-- The relative complement `X ∖ z`. -/
noncomputable def compl (X z : ZFSet) : ZFSet := sep (· ∉ z) X

/-- Complements are definable. If `z ∈ Def(X)` then `X ∖ z ∈ Def(X)`, defined by `¬φ`. -/
theorem compl_mem_Def {X z : ZFSet} (hz : z ∈ Def X) : compl X z ∈ Def X := by
  by_cases hX : ∃ a, a ∈ X
  · obtain ⟨a, ha⟩ := hX
    obtain ⟨φ, e, he, hφ⟩ := Def_spec ha hz
    refine Def_intro (sep_subset _ _) φ.neg e (fun n _ => he n) fun y hy => ?_
    rw [compl, mem_sep, RSat_neg, hφ]
    exact ⟨fun h hφ' => h.2 ⟨hy, hφ'⟩, fun h => ⟨hy, fun h' => h h'.2⟩⟩
  · have : compl X z = ∅ := eq_empty_of_forall_not_mem fun y hy => hX ⟨y, sep_subset _ _ hy⟩
    rw [this]; exact empty_mem_Def X

/-- Interleaving two environments: even indices from `e₁`, odd indices from `e₂`. -/
def merge (e₁ e₂ : Nat → ZFSet) (n : Nat) : ZFSet := if n % 2 = 0 then e₁ (n / 2) else e₂ (n / 2)

/-- The even part of a merged environment is the first environment. -/
theorem merge_even (e₁ e₂ : Nat → ZFSet) (n : Nat) : merge e₁ e₂ (2 * n) = e₁ n := by
  unfold merge
  simp only [show 2 * n % 2 = 0 by omega, show 2 * n / 2 = n by omega, ↓reduceIte]

/-- The odd part of a merged environment is the second environment. -/
theorem merge_odd (e₁ e₂ : Nat → ZFSet) (n : Nat) : merge e₁ e₂ (2 * n + 1) = e₂ n := by
  unfold merge
  simp only [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]
  rfl

/-- Re-index a formula's parameters to the even positions of a merged environment. -/
def evenF (φ : Formula LSet) : Formula LSet := φ.subst (Subst.lift fun n => .var (2 * n))

/-- Re-index a formula's parameters to the odd positions of a merged environment. -/
def oddF (φ : Formula LSet) : Formula LSet := φ.subst (Subst.lift fun n => .var (2 * n + 1))

/-- Satisfaction of `evenF φ` under a merged environment. -/
theorem RSat_evenF (P : ZFSet → Prop) (φ : Formula LSet) (y : ZFSet) (e₁ e₂ : Nat → ZFSet) :
    RSat P (BEnv.cons y (merge e₁ e₂)) (evenF φ) ↔ RSat P (BEnv.cons y e₁) φ := by
  simp only [evenF, RSat_subst, tv_lift, tv_var, merge_even]

/-- Satisfaction of `oddF φ` under a merged environment. -/
theorem RSat_oddF (P : ZFSet → Prop) (φ : Formula LSet) (y : ZFSet) (e₁ e₂ : Nat → ZFSet) :
    RSat P (BEnv.cons y (merge e₁ e₂)) (oddF φ) ↔ RSat P (BEnv.cons y e₂) φ := by
  simp only [oddF, RSat_subst, tv_lift, tv_var, merge_odd]

/-- The intersection `z ∩ w`. -/
noncomputable def inter (z w : ZFSet) : ZFSet := sep (· ∈ w) z

/-- Two definable sets have formulas sharing one merged environment of parameters. -/
theorem Def_spec₂ {X z w : ZFSet} (hz : z ∈ Def X) (hw : w ∈ Def X) (a : ZFSet) (ha : a ∈ X) :
    ∃ (φ ψ : Formula LSet) (e : Nat → ZFSet), (∀ n, e n ∈ X) ∧
      (∀ y, y ∈ z ↔ y ∈ X ∧ RSat (· ∈ X) (BEnv.cons y e) (evenF φ)) ∧
      (∀ y, y ∈ w ↔ y ∈ X ∧ RSat (· ∈ X) (BEnv.cons y e) (oddF ψ)) := by
  obtain ⟨φ, e₁, he₁, hφ⟩ := Def_spec ha hz
  obtain ⟨ψ, e₂, he₂, hψ⟩ := Def_spec ha hw
  refine ⟨φ, ψ, merge e₁ e₂, fun n => ?_, fun y => ?_, fun y => ?_⟩
  · unfold merge; split
    · exact he₁ _
    · exact he₂ _
  · rw [RSat_evenF, hφ]
  · rw [RSat_oddF, hψ]

/-- Intersections are definable. If `z, w ∈ Def(X)` then `z ∩ w ∈ Def(X)`. -/
theorem inter_mem_Def {X z w : ZFSet} (hz : z ∈ Def X) (hw : w ∈ Def X) : inter z w ∈ Def X := by
  by_cases hX : ∃ a, a ∈ X
  · obtain ⟨a, ha⟩ := hX
    obtain ⟨φ, ψ, e, he, hφ, hψ⟩ := Def_spec₂ hz hw a ha
    refine Def_intro (fun y hy => subset_of_mem_Def hz (sep_subset _ _ hy))
      (.conj (evenF φ) (oddF ψ)) e (fun n _ => he n) fun y hy => ?_
    rw [inter, mem_sep, hφ, hψ]
    exact ⟨fun h => ⟨h.1.2, h.2.2⟩, fun h => ⟨⟨hy, h.1⟩, ⟨hy, h.2⟩⟩⟩
  · have : inter z w = ∅ := eq_empty_of_forall_not_mem fun y hy =>
      hX ⟨y, subset_of_mem_Def hz (sep_subset _ _ hy)⟩
    rw [this]; exact empty_mem_Def X

/-- Unions are definable. If `z, w ∈ Def(X)` then `z ∪ w ∈ Def(X)`. -/
theorem union_mem_Def {X z w : ZFSet} (hz : z ∈ Def X) (hw : w ∈ Def X) : z ∪ w ∈ Def X := by
  by_cases hX : ∃ a, a ∈ X
  · obtain ⟨a, ha⟩ := hX
    obtain ⟨φ, ψ, e, he, hφ, hψ⟩ := Def_spec₂ hz hw a ha
    refine Def_intro (fun y hy => ?_) (.disj (evenF φ) (oddF ψ)) e (fun n _ => he n)
      fun y hy => ?_
    · rcases mem_union.1 hy with h | h
      · exact subset_of_mem_Def hz h
      · exact subset_of_mem_Def hw h
    rw [mem_union, hφ, hψ]
    exact ⟨fun h => h.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2),
      fun h => h.elim (fun h => Or.inl ⟨hy, h⟩) (fun h => Or.inr ⟨hy, h⟩)⟩
  · have : z ∪ w = ∅ := eq_empty_of_forall_not_mem fun y hy => by
      rcases mem_union.1 hy with h | h
      · exact hX ⟨y, subset_of_mem_Def hz h⟩
      · exact hX ⟨y, subset_of_mem_Def hw h⟩
    rw [this]; exact empty_mem_Def X

/-- Members of a transitive set are definable over it. If `X` is transitive, every
`a ∈ X` is the subset `{y ∈ X | y ∈ a}` of `X`, so `X ⊆ Def(X)`. -/
theorem subset_Def_of_transitive {X : ZFSet} (hX : IsTransitive X) : X ⊆ Def X := by
  intro a ha
  refine Def_intro (hX a ha) (memF (v 0) (v 1)) (fun _ => a) (fun _ _ => ha) fun y _ => ?_
  show y ∈ a ↔ y ∈ a
  exact Iff.rfl

end Foundations.Constructible
