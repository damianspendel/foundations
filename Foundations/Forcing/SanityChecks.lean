import Foundations.Forcing.NotCH

/-!
# Sanity checks: the CH encoding is not trivially false

`NotCH` proves `⟦CH⟧ = ⊥` in `V^{Cohen(ω₂)}` and concludes `ZF ⊬ CH`. A proof of that shape
is only as good as the sentence `CH`. If the encoding were defective, `⟦CH⟧ = ⊥` could hold
for reasons that have nothing to do with the continuum. For example:

* if the formula for "`f` is an injective function from `X` to `Y`" could never have value
  `⊤`, every instance of "`X` injects into `Y`" would be `⊥`, and so would `CH`;
* if the Kuratowski pair coding lost information, "injective" might mean something else;
* if "`w = ω`" or "`p = 𝒫(w)`" were satisfied by the wrong names (or by none), the
  quantifiers `∀w ∀p` in `CH` would range over the wrong objects.

This file rules these failure modes out by direct computation, in every `V^B` and in the
very model `V^{Cohen(ω₂)}` used by `NotCH`. Nothing here is needed for the main theorem. The
file is an audit: it shows that the formula `CH` says what it is meant to say, on enough test
cases that a vacuous encoding would have been caught.

1. **Kuratowski pairs are injective in the Boolean sense** (`opair_inj`):
   `⟦(a, b) = (c, d)⟧ ≤ ⟦a = c⟧ ⊓ ⟦b = d⟧`.
2. **Injections exist when they should.** The identity relation on `X` is an injective
   function `X → Y` with value `⊤` whenever `X ⊆ Y` (`idName_injfunc`). Any `f` is an injective
   function from the empty name with value `⊤` (`empty_injfunc`). The graph of a family of
   pairwise Boolean-distinct names is injective (`graph_injfunc`).
3. **The CH matrix is satisfiable in `V^{Cohen(ω₂)}`.** `ω̌` injects into the witness `x` of
   `NotCH` (`omega_inj_xName`, so `V^B` sees that `x` is infinite). The matrix of `CH` has
   value `⊤` at `x := 𝒫(ω)` (via the right disjunct, `chMatrix_powersetB`) and at `x := ∅`
   (via the left disjunct, `chMatrix_empty`). So `⟦CH⟧ = ⊥` comes from the specific witness
   `x`, not from a matrix that is false everywhere.
4. **The definitions of `ω` and `𝒫(ω)` pin down unique objects.** Anything satisfying "`w = ω`"
   is Boolean-equal to `ω̌` (`isOmega_le_eq`), and two power sets of the same set are
   Boolean-equal (`isPow_unique`). So the outer quantifiers of `CH` effectively range over the
   single pair `(ω̌, P)` analysed in `NotCH`.

These checks were first written as scratch files during an independent audit of the
development.
-/

namespace Foundations.Forcing

namespace Sanity

open Foundations.Logic.FO CBA BStructure

attribute [local instance] Classical.propDecidable

variable {B : Type} [CompleteBooleanAlgebra B]

/-! ### Kuratowski pairs -/

/-- The left entry of a pair belongs to it with value `⊤`. -/
theorem mem_pair_l (a b : BSet B) : BSet.mem a (BSet.pair a b) = ⊤ := by
  rw [BSet.mem_pair, BSet.eq_self]; exact eq_top_iff.2 (le_sup_left _ _)

/-- The right entry of a pair belongs to it with value `⊤`. -/
theorem mem_pair_r (a b : BSet B) : BSet.mem b (BSet.pair a b) = ⊤ := by
  rw [BSet.mem_pair, BSet.eq_self]; exact eq_top_iff.2 (le_sup_right _ _)

/-- Membership through a member of a pair: `⟦z ∈ w⟧ ⊓ ⟦w ∈ {S, D}⟧ ≤ ⟦z ∈ S⟧ ⊔ ⟦z ∈ D⟧`. -/
theorem nested (z w S D : BSet B) :
    BSet.mem z w ⊓ BSet.mem w (BSet.pair S D) ≤ BSet.mem z S ⊔ BSet.mem z D := by
  rw [BSet.mem_pair]
  refine le_trans' (inf_sup_le _ _ _) (sup_le_sup ?_ ?_)
  · rw [inf_comm]; exact BSet.mem_congr_right _ _ _
  · rw [inf_comm]; exact BSet.mem_congr_right _ _ _

/-- If `⟦z ∈ P⟧ = ⊤`, then `⟦P = Q⟧ ≤ ⟦z ∈ Q⟧`. -/
theorem transfer (z P Q : BSet B) (h : BSet.mem z P = ⊤) : BSet.eq P Q ≤ BSet.mem z Q :=
  le_trans' (le_inf _ _ _ le_rfl (by rw [h]; exact le_top')) (BSet.mem_congr_right _ _ _)

/-- **Boolean Kuratowski injectivity.** `⟦(a, b) = (c, d)⟧ ≤ ⟦a = c⟧ ⊓ ⟦b = d⟧`: the pair name
`{{a, a}, {a, b}}` determines both coordinates, to the degree that two pairs are equal. -/
theorem opair_inj (a b c d : BSet B) :
    BSet.eq (BSet.opair a b) (BSet.opair c d) ≤ BSet.eq a c ⊓ BSet.eq b d := by
  let E := BSet.eq (BSet.opair a b) (BSet.opair c d)
  -- a = c
  have hac : E ≤ BSet.eq a c := by
    have h1 : E ≤ BSet.mem (BSet.pair a a) (BSet.opair c d) :=
      transfer _ _ _ (mem_pair_l _ _)
    refine le_trans' h1 ?_
    show BSet.mem (BSet.pair a a) (BSet.pair (BSet.pair c c) (BSet.pair c d)) ≤ _
    rw [BSet.mem_pair]
    refine sup_le _ _ _ ?_ ?_
    · have := transfer a (BSet.pair a a) (BSet.pair c c) (mem_pair_l _ _)
      rw [BSet.mem_pair, BSet.sup_idem'] at this; exact this
    · have h2 := transfer c (BSet.pair c d) (BSet.pair a a) (mem_pair_l _ _)
      rw [BSet.mem_pair, BSet.sup_idem'] at h2
      exact le_trans' (le_trans' (BSet.eq_symm _ _) h2) (BSet.eq_symm _ _)
  -- b = c or b = d
  have hb : E ≤ BSet.eq b c ⊔ BSet.eq b d := by
    have h1 : E ≤ BSet.mem (BSet.pair a b) (BSet.opair c d) :=
      transfer _ _ _ (mem_pair_r _ _)
    have h2 := le_trans' (le_inf _ _ _ (by rw [mem_pair_r]; exact le_top') h1)
      (nested b (BSet.pair a b) (BSet.pair c c) (BSet.pair c d))
    rw [BSet.mem_pair, BSet.mem_pair, BSet.sup_idem'] at h2
    exact le_trans' h2 (sup_le _ _ _ (le_sup_left _ _) le_rfl)
  -- d = a or d = b
  have hd : E ≤ BSet.eq d a ⊔ BSet.eq d b := by
    have h1 : E ≤ BSet.mem (BSet.pair c d) (BSet.opair a b) :=
      le_trans' (BSet.eq_symm _ _) (transfer _ _ _ (mem_pair_r _ _))
    have h2 := le_trans' (le_inf _ _ _ (by rw [mem_pair_r]; exact le_top') h1)
      (nested d (BSet.pair c d) (BSet.pair a a) (BSet.pair a b))
    rw [BSet.mem_pair, BSet.mem_pair, BSet.sup_idem'] at h2
    exact le_trans' h2 (sup_le _ _ _ (le_sup_left _ _) le_rfl)
  refine le_inf _ _ _ hac ?_
  have hall := le_inf _ _ _ (le_inf _ _ _ hac hb) hd
  refine le_trans' hall ?_
  -- (ac ⊓ (bc ⊔ bd)) ⊓ (da ⊔ db) ≤ bd
  refine le_trans' (inf_sup_le _ _ _) (sup_le _ _ _ ?_ ?_)
  · refine le_trans' (inf_le_inf (inf_sup_le _ _ _) le_rfl) ?_
    refine le_trans' sup_inf_le (sup_le _ _ _ ?_ (inf_le_of_left_le (inf_le_right _ _)))
    -- ac ⊓ bc ⊓ da ≤ bd : d = a, a = c, c = b
    have hda_ac : BSet.eq d a ⊓ BSet.eq a c ≤ BSet.eq d c := BSet.eq_trans _ _ _
    have hcb : BSet.eq b c ≤ BSet.eq c b := BSet.eq_symm _ _
    refine le_trans' (le_inf _ _ _ ?_ ?_) (le_trans' (BSet.eq_trans d c b) (BSet.eq_symm d b))
    · exact le_trans' (le_inf _ _ _ (inf_le_right _ _) (inf_le_of_left_le (inf_le_left _ _))) hda_ac
    · exact inf_le_of_left_le (inf_le_of_right_le hcb)
  · exact le_trans' (inf_le_right _ _) (BSet.eq_symm _ _)

/-! ### Injections with value `⊤` -/

/-- The identity relation `{(a, a) | a ∈ X}` on a name, listed with the degrees of `X`. -/
def idName (X : BSet B) : BSet B :=
  .mk X.type (fun j => BSet.opair (X.func j) (X.func j)) X.bval

/-- The identity relation only relates Boolean-equal names: `⟦(a, b) ∈ id_X⟧ ≤ ⟦a = b⟧`. -/
theorem pm_idName_le (X a b : BSet B) : BSet.pm a b (idName X) ≤ BSet.eq a b := by
  show (iSup fun j => X.bval j ⊓ BSet.eq (BSet.opair a b) (BSet.opair (X.func j) (X.func j))) ≤ _
  refine iSup_le fun j => inf_le_of_right_le (le_trans' (opair_inj _ _ _ _) ?_)
  exact le_trans' (inf_le_inf le_rfl (BSet.eq_symm _ _)) (BSet.eq_trans _ _ _)

/-- Every member of `X` is related to itself: `⟦a ∈ X⟧ ≤ ⟦(a, a) ∈ id_X⟧`. -/
theorem mem_le_pm_idName (X a : BSet B) : BSet.mem a X ≤ BSet.pm a a (idName X) := by
  cases X with
  | mk α A b =>
    show (iSup fun j => b j ⊓ BSet.eq a (A j)) ≤
      iSup fun j => b j ⊓ BSet.eq (BSet.opair a a) (BSet.opair (A j) (A j))
    exact iSup_le fun j => le_iSup_of_le j (inf_le_inf le_rfl
      (le_trans' (le_inf _ _ _ le_rfl le_rfl) (BSet.opair_congr _ _ _ _)))

/-- **Identity injections.** If `X ⊆ Y` pointwise, the identity relation on `X` is an injective
function from `X` to `Y` with value `⊤`. -/
theorem idName_injfunc (X Y : BSet B) (hXY : ∀ a, BSet.mem a X ≤ BSet.mem a Y) :
    BSet.isFunc (idName X) X Y ⊓ BSet.isInj (idName X) X = ⊤ := by
  refine eq_top_iff.2 (le_inf _ _ _ (le_inf _ _ _ ?_ ?_) ?_)
  · exact le_iInf fun a => le_himp_iff.2 (by
      rw [top_inf]; exact le_iSup_of_le a (le_inf _ _ _ (hXY a) (mem_le_pm_idName X a)))
  · refine le_iInf fun a => le_himp_iff.2 (le_iInf fun b => le_iInf fun b' => le_himp_iff.2 ?_)
    refine inf_le_of_right_le ?_
    exact le_trans' (inf_le_inf (le_trans' (pm_idName_le X a b) (BSet.eq_symm _ _))
      (pm_idName_le X a b')) (BSet.eq_trans _ _ _)
  · refine le_iInf fun a => le_iInf fun a' => le_iInf fun b => le_himp_iff.2 (inf_le_of_right_le ?_)
    exact le_trans' (inf_le_inf (inf_le_of_right_le (pm_idName_le X a b))
      (le_trans' (pm_idName_le X a' b) (BSet.eq_symm _ _))) (BSet.eq_trans _ _ _)

/-- **Empty injections.** Every name `f` is an injective function from the empty name to any
`Y`, with value `⊤`. -/
theorem empty_injfunc (f Y : BSet B) :
    BSet.isFunc f BSet.empty Y ⊓ BSet.isInj f BSet.empty = ⊤ := by
  have h0 : ∀ a : BSet B, BSet.mem a BSet.empty ≤ ⊥ := fun a => (BSet.mem_empty a) ▸ le_rfl
  refine eq_top_iff.2 (le_inf _ _ _ (le_inf _ _ _ ?_ ?_) ?_)
  · exact le_iInf fun a => le_himp_iff.2 (inf_le_of_right_le (le_trans' (h0 a) bot_le'))
  · exact le_iInf fun a => le_himp_iff.2 (inf_le_of_right_le (le_trans' (h0 a) bot_le'))
  · exact le_iInf fun a => le_iInf fun a' => le_iInf fun b => le_himp_iff.2
      (inf_le_of_right_le (inf_le_of_left_le (inf_le_of_left_le
        (inf_le_of_left_le (le_trans' (h0 a) bot_le')))))

/-- The graph `{(u t, v t) | t ∈ T}` of a pair of families, all pairs with degree `⊤`. -/
def graph {T : Type} (u v : T → BSet B) : BSet B :=
  .mk T (fun t => BSet.opair (u t) (v t)) (fun _ => ⊤)

/-- A pair in a graph is, coordinatewise, equal to one of its listed pairs. -/
theorem pm_graph_le {T : Type} (u v : T → BSet B) (a b : BSet B) :
    BSet.pm a b (graph u v) ≤ iSup fun t => BSet.eq a (u t) ⊓ BSet.eq b (v t) :=
  iSup_le fun t => le_iSup_of_le t (inf_le_of_right_le (opair_inj _ _ _ _))

/-- Two pairs in a graph: each is coordinatewise equal to a listed pair. -/
theorem pm_pm_le {T : Type} (u v : T → BSet B) (a b a' b' : BSet B) :
    BSet.pm a b (graph u v) ⊓ BSet.pm a' b' (graph u v) ≤
      iSup fun t => iSup fun t' =>
        (BSet.eq a (u t) ⊓ BSet.eq b (v t)) ⊓ (BSet.eq a' (u t') ⊓ BSet.eq b' (v t')) := by
  refine le_trans' (inf_le_inf (pm_graph_le u v a b) (pm_graph_le u v a' b')) ?_
  refine le_trans' iSup_inf_le (iSup_le fun t => le_iSup_of_le t ?_)
  exact inf_iSup_le

/-- **Graphs of distinct families are injections.** If the `u t` are pairwise Boolean-distinct,
the `v t` are pairwise Boolean-distinct, and each `v t` lies in `Y` with value `⊤`, then the
graph is an injective function from `{u t}` to `Y` with value `⊤`. -/
theorem graph_injfunc {T : Type} (u v : T → BSet B) (Y : BSet B)
    (hu : ∀ t t', t ≠ t' → BSet.eq (u t) (u t') = ⊥)
    (hv : ∀ t t', t ≠ t' → BSet.eq (v t) (v t') = ⊥)
    (hY : ∀ t, BSet.mem (v t) Y = ⊤) :
    BSet.isFunc (graph u v) (.mk T u fun _ => ⊤) Y ⊓
      BSet.isInj (graph u v) (.mk T u fun _ => ⊤) = ⊤ := by
  refine eq_top_iff.2 (le_inf _ _ _ (le_inf _ _ _ ?_ ?_) ?_)
  · refine le_iInf fun a => le_himp_iff.2 ?_
    rw [top_inf]
    refine iSup_le fun (t : T) => le_iSup_of_le (v t)
      (le_inf _ _ _ (le_trans' le_top' (eq_top_iff.1 (hY t))) ?_)
    refine le_iSup_of_le t (le_inf _ _ _ (inf_le_left _ _) ?_)
    refine le_trans' (le_inf _ _ _ (inf_le_right _ _) (by rw [BSet.eq_self]; exact le_top'))
      (BSet.opair_congr _ _ _ _)
  · refine le_iInf fun a => le_himp_iff.2 (le_iInf fun b => le_iInf fun b' => le_himp_iff.2 ?_)
    refine inf_le_of_right_le (le_trans' (pm_pm_le u v a b a b')
      (iSup_le fun t => iSup_le fun t' => ?_))
    by_cases h : t = t'
    · subst h
      exact le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_right _ _))
        (inf_le_of_right_le (le_trans' (inf_le_right _ _) (BSet.eq_symm _ _)))) (BSet.eq_trans _ _ _)
    · refine le_trans' ?_ bot_le'
      rw [← hu t t' h]
      exact le_trans' (le_inf _ _ _ (inf_le_of_left_le (le_trans' (inf_le_left _ _) (BSet.eq_symm _ _)))
        (inf_le_of_right_le (inf_le_left _ _))) (BSet.eq_trans _ _ _)
  · refine le_iInf fun a => le_iInf fun a' => le_iInf fun b => le_himp_iff.2 (inf_le_of_right_le ?_)
    have h4 : BSet.mem a (.mk T u fun _ => ⊤) ⊓ BSet.mem a' (.mk T u fun _ => ⊤) ⊓
        BSet.pm a b (graph u v) ⊓ BSet.pm a' b (graph u v) ≤
        BSet.pm a b (graph u v) ⊓ BSet.pm a' b (graph u v) := by lattice_le
    refine le_trans' h4 (le_trans' (pm_pm_le u v a b a' b) (iSup_le fun t => iSup_le fun t' => ?_))
    by_cases h : t = t'
    · subst h
      exact le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_left _ _))
        (inf_le_of_right_le (le_trans' (inf_le_left _ _) (BSet.eq_symm _ _)))) (BSet.eq_trans _ _ _)
    · refine le_trans' ?_ bot_le'
      rw [← hv t t' h]
      exact le_trans' (le_inf _ _ _ (inf_le_of_left_le (le_trans' (inf_le_right _ _) (BSet.eq_symm _ _)))
        (inf_le_of_right_le (inf_le_right _ _))) (BSet.eq_trans _ _ _)

/-! ### The CH matrix in `V^{Cohen(ω₂)}` -/

/-- The matrix of `CH` at `w`, `p`, `x`: "`x` injects into `w`, or `p` injects into `x`". -/
def chMatrix (w p x : BSet B) : B :=
  (iSup fun f => BSet.isFunc f x w ⊓ BSet.isInj f x) ⊔
    (iSup fun f => BSet.isFunc f p x ⊓ BSet.isInj f p)

/-- The truth value of `CH` is built from `chMatrix`:
`⟦CH⟧ = ⨅ w p, (⟦w = ω⟧ ⊓ ⟦p = 𝒫(w)⟧) ⇨ ⨅ x, ⟦x ⊆ p⟧ ⇨ chMatrix w p x`. -/
theorem val_CH_chMatrix (e : Nat → BSet B) : (VB B).val e CH =
    iInf fun w => iInf fun p => (BSet.isOmega w ⊓ BSet.isPow p w) ⇨
      iInf fun x => BSet.subset x p ⇨ chMatrix w p x :=
  val_CH e

/-- **`ω̌` injects into the witness `x`.** In `V^{Cohen(ω₂)}` there is an injective function from
`ω̌` into the name `x = {ċ_ξ | ξ ∈ ω₁}` of `NotCH`, with value `⊤`: the model sees that `x` is
infinite. -/
theorem omega_inj_xName :
    ∃ f : BSet CohenB, BSet.isFunc f omegaB xName ⊓ BSet.isInj f omegaB = ⊤ := by
  obtain ⟨j, hj⟩ := nat_le_W₁
  refine ⟨graph natB (fun n => creal (W₁.incl (j n))), ?_⟩
  exact graph_injfunc natB (fun n => creal (W₁.incl (j n))) xName
    (fun m n h => eq_natB_of_ne m n h)
    (fun m n h => creal_ne fun e => h (hj (W₁.incl_injective e)))
    (fun n => eq_top_iff.2 (BSet.bval_le_mem xName (j n)))

/-- **`𝒫(ω)` injects into itself** in `V^{Cohen(ω₂)}`, with value `⊤`. -/
theorem powersetB_inj_self :
    BSet.isFunc (idName powersetB) powersetB (powersetB : BSet CohenB) ⊓
      BSet.isInj (idName powersetB) powersetB = ⊤ :=
  idName_injfunc _ _ fun _ => le_rfl

/-- **The CH matrix holds at `x := 𝒫(ω)`.** In `V^{Cohen(ω₂)}`, with `w := ω̌` and `p := P`, the
matrix of `CH` has value `⊤` at `x := P` (by the right disjunct, the identity of `P`). -/
theorem chMatrix_powersetB : chMatrix omegaB powersetB (powersetB : BSet CohenB) = ⊤ :=
  eq_top_iff.2 (le_sup_of_le_right (le_iSup_of_le (idName powersetB)
    (eq_top_iff.1 powersetB_inj_self)))

/-- **The CH matrix holds at `x := ∅`.** In `V^{Cohen(ω₂)}`, with `w := ω̌` and `p := P`, the
matrix of `CH` has value `⊤` at `x := ∅` (by the left disjunct, an empty injection). -/
theorem chMatrix_empty : chMatrix omegaB powersetB (BSet.empty : BSet CohenB) = ⊤ :=
  eq_top_iff.2 (le_sup_of_le_left (le_iSup_of_le BSet.empty (eq_top_iff.1 (empty_injfunc _ _))))

/-- The witness `x` injects into the name `{ċ_α | α ∈ ω₂}` of all Cohen reals (by the identity),
with value `⊤`. -/
theorem xName_inj_cName :
    ∃ f : BSet CohenB, BSet.isFunc f xName cName ⊓ BSet.isInj f xName = ⊤ :=
  ⟨idName xName, idName_injfunc _ _ fun _ => iSup_le fun ξ =>
    le_iSup_of_le (W₁.incl ξ) le_rfl⟩

/-! ### Uniqueness of `ω` and `𝒫(ω)` -/

/-- **Uniqueness of ω.** In every `V^B`, anything satisfying "`w = ω`" is Boolean-equal to `ω̌`:
`⟦w = ω⟧ ≤ ⟦w = ω̌⟧`. -/
theorem isOmega_le_eq (w : BSet B) : BSet.isOmega w ≤ BSet.eq w omegaB := by
  rw [BSet.eq_eq_iInf_biimp]
  refine le_iInf fun z => le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_)
  · have hs : BSet.isOmega w ≤ BSet.subset w omegaB :=
      le_trans' (inf_le_of_right_le (iInf_le _ omegaB))
        (le_trans' (le_inf _ _ _ le_rfl (by rw [isInductive_omegaB]; exact le_top')) himp_inf_le)
    exact le_trans' (inf_le_inf (le_trans' hs (iInf_le _ z)) le_rfl) himp_inf_le
  · show _ ⊓ (iSup fun n : Nat => ⊤ ⊓ BSet.eq z (natB n)) ≤ _
    refine le_trans' inf_iSup_le (iSup_le fun n => ?_)
    refine le_trans' (le_inf _ _ _ (inf_le_of_right_le (inf_le_of_right_le (BSet.eq_symm _ _)))
      (inf_le_of_left_le (inf_le_of_left_le (isInductive_le_mem w n)))) (BSet.mem_congr_left _ _ _)

/-- Two names satisfying "`= ω`" are Boolean-equal: `⟦w = ω⟧ ⊓ ⟦w' = ω⟧ ≤ ⟦w = w'⟧`. -/
theorem isOmega_unique (w w' : BSet B) : BSet.isOmega w ⊓ BSet.isOmega w' ≤ BSet.eq w w' :=
  le_trans' (inf_le_inf (isOmega_le_eq w) (le_trans' (isOmega_le_eq w') (BSet.eq_symm _ _)))
    (BSet.eq_trans _ _ _)

/-- **Uniqueness of power sets.** In every `V^B`, two power sets of the same name are
Boolean-equal: `⟦p = 𝒫(w)⟧ ⊓ ⟦p' = 𝒫(w)⟧ ≤ ⟦p = p'⟧`. -/
theorem isPow_unique (p p' w : BSet B) : BSet.isPow p w ⊓ BSet.isPow p' w ≤ BSet.eq p p' := by
  rw [BSet.eq_eq_iInf_biimp]
  refine le_iInf fun z => ?_
  refine le_trans' (inf_le_inf (iInf_le _ z) (iInf_le _ z)) ?_
  refine le_inf _ _ _ (le_himp_iff.2 ?_) (le_himp_iff.2 ?_)
  · -- z ∈ p → z ⊆ w → z ∈ p'
    refine le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_right_le (inf_le_right _ _)))
      (le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (inf_le_left _ _)))
        (inf_le_right _ _)) himp_inf_le)) himp_inf_le
  · refine le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le (inf_le_right _ _)))
      (le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_right_le (inf_le_left _ _)))
        (inf_le_right _ _)) himp_inf_le)) himp_inf_le

/-- **Uniqueness of `𝒫(ω)`.** In every `V^B`, anything satisfying "`p = 𝒫(ω̌)`" is Boolean-equal to
the power-set name `P`: `⟦p = 𝒫(ω̌)⟧ ≤ ⟦p = P⟧`. -/
theorem isPow_le_eq (p : BSet B) : BSet.isPow p omegaB ≤ BSet.eq p powersetB :=
  le_trans' (le_inf _ _ _ le_rfl (by rw [isPow_powersetB]; exact le_top'))
    (isPow_unique p powersetB omegaB)

end Sanity

end Foundations.Forcing
