import Foundations.Forcing.BSetModel

/-!
# `V^B` is a Boolean-valued model of ZF

`BSetModel` verified extensionality, empty set, pairing, union, separation and ∈-induction
in the Boolean-valued universe. This file adds the three remaining axioms of ZF:

* **Power set** `∀x ∃p ∀z (z ∈ p ↔ ∀w (w ∈ z → w ∈ x))`. The witness is the name whose
  members are all "Boolean subsets" `{(Aᵢ, f i ⊓ aᵢ)}` of `x = {(Aᵢ, aᵢ)}`, one for every
  function `f : index → B`. It is a set because `B` is a set: this is the step where the
  smallness of `B : Type` is essential.
* **Infinity** `∃x (∅ ∈ x ∧ ∀y (y ∈ x → y ∪ {y} ∈ x))`, with witness the name `ω̌` of the
  von Neumann naturals; the empty set and successor are expressed by formulas, since the
  language has only `∈`.
* the **Collection scheme** `∀u (∀x ∈ u ∃y φ(x, y) → ∃v ∀x ∈ u ∃y ∈ v φ(x, y))`, for every
  formula `φ` with parameters. A truth value `⨆_y ⟦φ(x, y)⟧` is a supremum over the proper
  class of all names, but it only takes values in the *set* `B`. So for each value one can
  choose one witness, and these witnesses form a set. Over the other axioms Collection
  implies Replacement, so the two formulations of ZF are equivalent.

The headline theorem `VB_models_ZF` collects everything. **For every complete Boolean
algebra `B`, every axiom of ZF has truth value `⊤` in `V^B`** (Scott–Solovay–Vopěnka),
and so, by soundness, does every first-order consequence of ZF (`VB_val_eq_top_of_ZF`). The
axiom of choice in `V^B` is not treated.
-/

namespace Foundations.Forcing

open Foundations.Logic.FO CBA BStructure

attribute [local instance] Classical.propDecidable

section Nat

variable {B : Type} [CompleteBooleanAlgebra B]

/-- The canonical name `ň` of the natural number `n` (the von Neumann numeral
`{0, …, n − 1}`, all members with degree `⊤`). -/
def natB : Nat → BSet B
  | n => .mk {m // m < n} (fun m => natB m.1) (fun _ => ⊤)
termination_by n => n
decreasing_by exact m.2

/-- Unfolding the numeral names. -/
theorem natB_eq (n : Nat) :
    (natB n : BSet B) = .mk {m // m < n} (fun m => natB m.1) (fun _ => ⊤) := by
  rw [natB]

/-- Membership in a numeral: `⟦x ∈ ň⟧ = ⨆_{m < n} ⟦x = m̌⟧`. -/
theorem mem_natB (x : BSet B) (n : Nat) :
    BSet.mem x (natB n) = iSup fun m : {m // m < n} => ⊤ ⊓ BSet.eq x (natB m.1) := by
  rw [natB_eq n]; rfl

/-- **Distinct numerals are Boolean-distinct.** `⟦m̌ = ň⟧ = ⊥` for `m ≠ n`. -/
theorem eq_natB_of_ne : ∀ (m n : Nat), m ≠ n → BSet.eq (natB m : BSet B) (natB n) = ⊥ := by
  -- strong induction on `m + n`
  suffices h : ∀ s m n, m + n < s → m ≠ n → BSet.eq (natB m : BSet B) (natB n) = ⊥ from
    fun m n => h (m + n + 1) m n (Nat.lt_succ_self _)
  intro s
  induction s with
  | zero => intro m n h; omega
  | succ s ih =>
    -- it suffices to treat `m < n`, by symmetry
    have key : ∀ m n, m + n < s + 1 → m < n → BSet.eq (natB m : BSet B) (natB n) = ⊥ := by
      intro m n hs hmn
      apply eq_bot_iff.2
      have hmem : ⊤ ≤ BSet.mem (natB m : BSet B) (natB n) := by
        rw [mem_natB]
        exact le_iSup_of_le ⟨m, hmn⟩ (by rw [BSet.eq_self, top_inf]; exact le_rfl)
      calc BSet.eq (natB m : BSet B) (natB n)
          ≤ BSet.eq (natB n) (natB m) ⊓ BSet.mem (natB m) (natB n) :=
            le_inf _ _ _ (BSet.eq_symm _ _) (le_trans' le_top' hmem)
        _ ≤ BSet.mem (natB m) (natB m) := BSet.mem_congr_right _ _ _
        _ ≤ ⊥ := by
            rw [mem_natB]
            exact iSup_le fun k => inf_le_of_right_le (eq_bot_iff.1
              (ih m k.1 (by have := k.2; omega) (by have := k.2; omega)))
    intro m n hs hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key m n hs h
    · rw [BSet.eq_comm]; exact key n m (by omega) h

/-- The name `ω̌` of the set of natural numbers. -/
def omegaB : BSet B := .mk Nat natB (fun _ => ⊤)

/-- A name listing numerals: `⟦ň ∈ {(m̌, bₘ)}⟧ = bₙ`. -/
theorem mem_natB_family (b : Nat → B) (n : Nat) :
    BSet.mem (natB n) (.mk Nat natB b) = b n :=
  le_antisymm'
    (iSup_le fun m => by
      by_cases h : m = n
      · subst h; exact inf_le_left _ _
      · show b m ⊓ BSet.eq (natB n) (natB m) ≤ b n
        rw [eq_natB_of_ne n m (Ne.symm h)]; exact inf_le_of_right_le bot_le')
    (le_iSup_of_le n (by
      show b n ≤ b n ⊓ BSet.eq (natB n) (natB n)
      rw [BSet.eq_self, inf_top]; exact le_rfl))

/-- The canonical name `ǎ` of a ground-model set of natural numbers `a ⊆ ℕ`. -/
def subsetB (a : Nat → Prop) : BSet B := .mk {n // a n} (fun n => natB n.1) (fun _ => ⊤)

/-- Membership of a numeral in a ground-model subset: `⊤` if `n ∈ a`, `⊥` otherwise. -/
theorem mem_subsetB_of_mem {a : Nat → Prop} {n : Nat} (h : a n) :
    BSet.mem (natB n) (subsetB a : BSet B) = ⊤ :=
  eq_top_iff.2 (le_iSup_of_le ⟨n, h⟩ (by
    show ⊤ ≤ ⊤ ⊓ BSet.eq (natB n) (natB n); rw [BSet.eq_self, inf_top]; exact le_rfl))

/-- Membership of a numeral in a ground-model subset it does not belong to is `⊥`. -/
theorem mem_subsetB_of_not_mem {a : Nat → Prop} {n : Nat} (h : ¬ a n) :
    BSet.mem (natB n) (subsetB a : BSet B) = ⊥ :=
  eq_bot_iff.2 (iSup_le fun m => by
    show ⊤ ⊓ BSet.eq (natB n) (natB m.1) ≤ ⊥
    have hne : n ≠ m.1 := fun e => h (e ▸ m.2)
    rw [eq_natB_of_ne n m.1 hne]; exact inf_le_right _ _)

end Nat

variable {B : Type} [CompleteBooleanAlgebra B]

/-! ### Power set -/

/-- The Boolean subset `{(Aᵢ, f i ⊓ aᵢ)}` of a name `x = {(Aᵢ, aᵢ)}` cut out by `f`. -/
def BSet.restrict (x : BSet B) (f : x.type → B) : BSet B :=
  .mk x.type x.func (fun i => f i ⊓ x.bval i)

/-- The power-set name: all Boolean subsets of `x`, each with degree `⊤`. -/
def BSet.powerset (x : BSet B) : BSet B :=
  .mk (x.type → B) (fun f => x.restrict f) (fun _ => ⊤)

/-- A Boolean subset of `x` is contained in `x`: `⟦w ∈ x↾f⟧ ≤ ⟦w ∈ x⟧`. -/
theorem BSet.mem_restrict_le (x : BSet B) (f : x.type → B) (w : BSet B) :
    BSet.mem w (x.restrict f) ≤ BSet.mem w x :=
  iSup_mono fun _ => inf_le_inf (inf_le_right _ _) le_rfl

/-- Every name `z` contained in `x` (to degree `c`) equals, to degree `c`, the Boolean subset of
`x` cut out by `f i = ⟦Aᵢ ∈ z⟧`. -/
theorem BSet.subset_le_eq_restrict (x z : BSet B) :
    iInf (fun w => BSet.mem w z ⇨ BSet.mem w x) ≤
      BSet.eq z (x.restrict fun i => BSet.mem (x.func i) z) := by
  apply BSet.le_eq_of
  · intro j
    calc iInf (fun w => BSet.mem w z ⇨ BSet.mem w x) ⊓ z.bval j
        ≤ BSet.mem (z.func j) z ⊓ BSet.mem (z.func j) x :=
          le_inf _ _ _ (inf_le_of_right_le (BSet.bval_le_mem z j))
            (le_trans' (inf_le_inf (iInf_le _ (z.func j)) (BSet.bval_le_mem z j)) himp_inf_le)
      _ ≤ iSup (fun i => BSet.mem (z.func j) z ⊓ (x.bval i ⊓ BSet.eq (z.func j) (x.func i))) :=
          inf_iSup_le
      _ ≤ _ := iSup_mono fun i => by
          show _ ≤ (BSet.mem (x.func i) z ⊓ x.bval i) ⊓ BSet.eq (z.func j) (x.func i)
          refine le_inf _ _ _ (le_inf _ _ _ ?_ (by lattice_le)) (by lattice_le)
          exact le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
            (BSet.mem_congr_left (z.func j) (x.func i) z)
  · intro i
    show _ ⊓ (BSet.mem (x.func i) z ⊓ x.bval i) ≤ _
    refine le_trans' (inf_le_of_right_le (inf_le_left _ _)) (iSup_mono fun j => ?_)
    exact inf_le_inf le_rfl (BSet.eq_symm _ _)

/-- The power-set axiom `∀x ∃p ∀z (z ∈ p ↔ ∀w (w ∈ z → w ∈ x))`. -/
def axPow : Formula LSet :=
  .all (.ex (.all (iffF (memF (v 0) (v 1)) (.all (.imp (memF (v 0) (v 1)) (memF (v 0) (v 3)))))))

/-- **The power-set axiom holds in `V^B`.** -/
theorem VB_pow (e : Nat → BSet B) : (VB B).val e axPow = ⊤ := by
  refine eq_top_iff.2 <| le_iInf fun x => le_iSup_of_le (BSet.powerset x) <| le_iInf fun z => ?_
  show ⊤ ≤ (BSet.mem z (BSet.powerset x) ⇔ iInf fun w => BSet.mem w z ⇨ BSet.mem w x)
  refine le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_)
  · rw [top_inf]
    refine iSup_le fun f => le_iInf fun w => le_himp_iff.2 ?_
    show ⊤ ⊓ BSet.eq z (x.restrict f) ⊓ BSet.mem w z ≤ _
    exact le_trans' (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le))
      (BSet.mem_congr_right w z (x.restrict f))) (BSet.mem_restrict_le x f w)
  · rw [top_inf]
    refine le_iSup_of_le (fun i => BSet.mem (x.func i) z) ?_
    show _ ≤ ⊤ ⊓ _
    rw [top_inf]; exact BSet.subset_le_eq_restrict x z

/-! ### Infinity -/

/-- Successor numerals: `⟦w ∈ (n+1)ˇ⟧ = ⟦w ∈ ň⟧ ⊔ ⟦w = ň⟧`. -/
theorem mem_natB_succ (w : BSet B) (n : Nat) :
    BSet.mem w (natB (n + 1)) = BSet.mem w (natB n) ⊔ BSet.eq w (natB n) := by
  rw [mem_natB, mem_natB]
  apply le_antisymm'
  · refine iSup_le fun m => ?_
    by_cases h : m.1 < n
    · exact le_sup_of_le_left (le_iSup_of_le ⟨m.1, h⟩ le_rfl)
    · have : m.1 = n := by have := m.2; omega
      rw [this]; exact le_sup_of_le_right (inf_le_right _ _)
  · exact sup_le _ _ _ (iSup_le fun m => le_iSup_of_le ⟨m.1, by have := m.2; omega⟩ le_rfl)
      (le_iSup_of_le ⟨n, Nat.lt_succ_self n⟩ (by rw [top_inf]; exact le_rfl))

/-- The infinity axiom `∃x (∃e (e ∈ x ∧ ∀z ¬ z ∈ e) ∧ ∀y (y ∈ x → ∃s (s ∈ x ∧
∀w (w ∈ s ↔ w ∈ y ∨ w = y))))`. -/
def axInf : Formula LSet :=
  .ex (.conj (.ex (.conj (memF (v 0) (v 1)) (.all (Formula.neg (memF (v 0) (v 1))))))
    (.all (.imp (memF (v 0) (v 1)) (.ex (.conj (memF (v 0) (v 2))
      (.all (iffF (memF (v 0) (v 1)) (.disj (memF (v 0) (v 2)) (.eq (v 0) (v 2))))))))))

/-- **The axiom of infinity holds in `V^B`**, witnessed by `ω̌`. -/
theorem VB_inf (e : Nat → BSet B) : (VB B).val e axInf = ⊤ := by
  have hω : ∀ n, BSet.mem (natB n) (omegaB : BSet B) = ⊤ := mem_natB_family _
  refine eq_top_iff.2 <| le_iSup_of_le omegaB <| le_inf _ _ _ ?_ ?_
  · refine le_iSup_of_le (natB 0) (le_inf _ _ _ (by show ⊤ ≤ BSet.mem (natB 0) (omegaB : BSet B); rw [hω 0]; exact le_rfl) ?_)
    refine le_iInf fun z => le_himp_iff.2 (inf_le_of_right_le ?_)
    show BSet.mem z (natB 0) ≤ ⊥
    rw [mem_natB]; exact iSup_le fun m => absurd m.2 (Nat.not_lt_zero _)
  · refine le_iInf fun y => le_himp_iff.2 ?_
    show ⊤ ⊓ BSet.mem y omegaB ≤ _
    rw [top_inf]
    refine iSup_le fun (n : Nat) => le_iSup_of_le (natB (n + 1)) ?_
    show ⊤ ⊓ BSet.eq y (natB n) ≤ BSet.mem (natB (n + 1)) omegaB ⊓ _
    rw [top_inf, hω, top_inf]
    refine le_iInf fun w => ?_
    show _ ≤ (BSet.mem w (natB (n + 1)) ⇔ BSet.mem w y ⊔ BSet.eq w y)
    rw [mem_natB_succ]
    have hs := BSet.eq_symm y (natB n)
    refine le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_)
    · refine le_trans' (inf_sup_le _ _ _) (sup_le_sup ?_ ?_)
      · exact le_trans' (inf_le_inf hs le_rfl) (BSet.mem_congr_right _ _ _)
      · exact le_trans' (by rw [inf_comm]; exact inf_le_inf le_rfl le_rfl)
          (BSet.eq_trans w (natB n) y |> le_trans' (inf_le_inf le_rfl hs))
    · refine le_trans' (inf_sup_le _ _ _) (sup_le_sup ?_ ?_)
      · exact BSet.mem_congr_right _ _ _
      · rw [inf_comm]; exact BSet.eq_trans _ _ _

/-! ### Collection -/

/-- Lifting a formula past `k` new binders while keeping its variables `0` and `1`. -/
def lift2By (k : Nat) (φ : Formula LSet) : Formula LSet :=
  φ.subst (Subst.lift (Subst.lift fun n => .var (n + k)))

/-- Truth value of a doubly lifted formula. -/
theorem val_lift2By (k : Nat) (φ : Formula LSet) (y x : BSet B) (env e : Nat → BSet B)
    (h : ∀ n, env (n + k) = e n) :
    (VB B).val (BEnv.cons y (BEnv.cons x env)) (lift2By k φ) =
      (VB B).val (BEnv.cons y (BEnv.cons x e)) φ := by
  simp only [lift2By, val_subst, lift_evalT]
  have : (fun n => (VB B).evalT env (Term.var (n + k) : Term LSet)) = e := funext h
  rw [this]

/-- Leibniz's law in the second variable: `⟦a = x⟧ ⊓ ⟦φ(a, y)⟧ ≤ ⟦φ(x, y)⟧`. -/
theorem eq_inf_val_cons2_le (φ : Formula LSet) (e : Nat → BSet B) (y a x : BSet B) :
    BSet.eq a x ⊓ (VB B).val (BEnv.cons y (BEnv.cons a e)) φ ≤
      (VB B).val (BEnv.cons y (BEnv.cons x e)) φ := by
  have hd : BSet.eq a x ≤ (VB B).envEq (BEnv.cons y (BEnv.cons a e)) (BEnv.cons y (BEnv.cons x e)) :=
    le_iInf fun n => by
      match n with
      | 0 => show _ ≤ BSet.eq y y; rw [BSet.eq_self]; exact le_top'
      | 1 => exact le_rfl
      | k + 2 => show _ ≤ BSet.eq (e k) (e k); rw [BSet.eq_self]; exact le_top'
  exact le_trans' (inf_le_inf hd le_rfl) (envEq_inf_val_le φ _ _)

/-- The collection axiom for `φ` (variable `0` is `y`, variable `1` is `x`, the others are
parameters): `∀u (∀x (x ∈ u → ∃y φ(x, y)) → ∃v ∀x (x ∈ u → ∃y (y ∈ v ∧ φ(x, y))))`. -/
def axColl (φ : Formula LSet) : Formula LSet :=
  .all (.imp (.all (.imp (memF (v 0) (v 1)) (.ex (lift2By 1 φ))))
    (.ex (.all (.imp (memF (v 0) (v 2)) (.ex (.conj (memF (v 0) (v 2)) (lift2By 2 φ)))))))

/-- The collecting name: for every member `Aᵢ` of `u` and every truth value `b` attained by
`⟦φ(Aᵢ, y)⟧`, one chosen witness `y`. The index type is a set because `B` is. -/
noncomputable def BSet.collect (φ : Formula LSet) (e : Nat → BSet B) (u : BSet B) : BSet B :=
  .mk (Σ i : u.type, {b : B // ∃ y : BSet B, (VB B).val (BEnv.cons y (BEnv.cons (u.func i) e)) φ = b})
    (fun p => Classical.choose p.2.2) (fun _ => ⊤)

/-- **The collection scheme holds in `V^B`**, for every formula `φ` and parameters `e`. -/
theorem VB_coll (φ : Formula LSet) (e : Nat → BSet B) : (VB B).val e (axColl φ) = ⊤ := by
  let F : BSet B → BSet B → B := fun x y => (VB B).val (BEnv.cons y (BEnv.cons x e)) φ
  refine eq_top_iff.2 <| le_iInf fun u => le_himp_iff.2 ?_
  rw [top_inf]
  have h1 : ∀ x y : BSet B, (VB B).val (BEnv.cons y (BEnv.cons x (BEnv.cons u e))) (lift2By 1 φ) =
      F x y := fun x y => val_lift2By 1 φ y x _ e (fun _ => rfl)
  have h2 : ∀ (w x y : BSet B),
      (VB B).val (BEnv.cons y (BEnv.cons x (BEnv.cons w (BEnv.cons u e)))) (lift2By 2 φ) =
      F x y := fun w x y => val_lift2By 2 φ y x _ e (fun _ => rfl)
  show iInf (fun x : BSet B => BSet.mem x u ⇨ iSup fun y : BSet B =>
      (VB B).val (BEnv.cons y (BEnv.cons x (BEnv.cons u e))) (lift2By 1 φ)) ≤
    iSup fun w : BSet B => iInf fun x : BSet B => BSet.mem x u ⇨ iSup fun y : BSet B =>
      BSet.mem y w ⊓ (VB B).val (BEnv.cons y (BEnv.cons x (BEnv.cons w (BEnv.cons u e)))) (lift2By 2 φ)
  simp only [h1, h2]
  let V := BSet.collect φ e u
  -- every value `⟦φ(Aᵢ, y)⟧` is attained by a witness listed in `V`
  have hwit : ∀ i, iSup (fun y => F (u.func i) y) ≤ iSup fun y => BSet.mem y V ⊓ F (u.func i) y := by
    intro i
    refine iSup_le fun y => ?_
    let s : {b : B // ∃ y : BSet B, F (u.func i) y = b} := ⟨F (u.func i) y, y, rfl⟩
    have hs : F (u.func i) (Classical.choose s.2) = F (u.func i) y := Classical.choose_spec s.2
    refine le_iSup_of_le (Classical.choose s.2) (le_inf _ _ _ ?_ (by rw [hs]; exact le_rfl))
    exact le_trans' le_top' (BSet.bval_le_mem V ⟨i, s⟩)
  refine le_iSup_of_le V (le_iInf fun x => le_himp_iff.2 ?_)
  refine le_trans' inf_iSup_le (iSup_le fun i => ?_)
  calc iInf (fun x => BSet.mem x u ⇨ iSup fun y => F x y) ⊓ (u.bval i ⊓ BSet.eq x (u.func i))
      ≤ iSup (fun y => F (u.func i) y) ⊓ BSet.eq (u.func i) x :=
        inf_le_inf (le_trans' (le_inf _ _ _ (inf_le_of_left_le (iInf_le _ (u.func i)))
          (inf_le_of_right_le (inf_le_of_left_le (BSet.bval_le_mem u i)))) himp_inf_le)
          (inf_le_of_right_le (BSet.eq_symm _ _)) |> le_trans' (by lattice_le)
    _ ≤ iSup (fun y => BSet.mem y V ⊓ F (u.func i) y) ⊓ BSet.eq (u.func i) x :=
        inf_le_inf (hwit i) le_rfl
    _ ≤ iSup (fun y => BSet.mem y V ⊓ F (u.func i) y ⊓ BSet.eq (u.func i) x) := iSup_inf_le
    _ ≤ _ := iSup_mono fun y => le_inf _ _ _ (by lattice_le)
        (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (eq_inf_val_cons2_le φ e y _ x))

/-! ### ZF -/

/-- **The axioms of ZF** (with Collection, and ∈-induction as the form of Foundation):
extensionality, empty set, pairing, union, power set, infinity, and all instances of the
separation, collection and ∈-induction schemes, each together with all of its universal
closures `∀ⁿ` (so the closed textbook axioms are members). -/
def ZF : Theory LSet := fun ψ =>
  ZFFrag ψ ∨ ψ = axPow ∨ ψ = axInf ∨ ∃ φ n, ψ = allN (axColl φ) n

/-- **`V^B` is a Boolean-valued model of ZF** (Scott–Solovay–Vopěnka). For every complete
Boolean algebra `B : Type` and every environment, every axiom of ZF has truth value `⊤` in
the Boolean-valued universe `V^B`. -/
theorem VB_models_ZF (e : Nat → BSet B) : ∀ ψ, ZF ψ → (VB B).val e ψ = ⊤ := by
  rintro ψ (h | rfl | rfl | ⟨φ, n, rfl⟩)
  · exact VB_models_ZFFrag e ψ h
  · exact VB_pow e
  · exact VB_inf e
  · exact val_allN_eq_top (M := VB B) (VB_coll φ) n e

/-- **Every theorem of ZF is true in `V^B`.** If `ZF ⊢₁ φ`, then `⟦φ⟧ₑ = ⊤` in `V^B` for every
complete Boolean algebra `B` and every environment `e`. Here `ZF` contains the scheme
instances both as open formulas and with all their universal closures, so it derives at
least everything the closed textbook axiomatisation derives. -/
theorem VB_val_eq_top_of_ZF {φ : Formula LSet} (h : ZF ⊢₁ φ) (e : Nat → BSet B) :
    (VB B).val e φ = ⊤ :=
  val_eq_top_of_theory h (VB B) e (VB_models_ZF e)

end Foundations.Forcing
