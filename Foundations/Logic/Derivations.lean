import Foundations.Logic.PrimRec

/-!
# Inductive definitions with computable rules are computably enumerable

Many sets in logic are defined *inductively*: the theorems of a formal system are
the formulas obtained from axioms by finitely many applications of rules; the true
statements "code `c` on input `x` outputs `n`" are those obtained by finitely many
applications of the evaluation rules. In both cases membership is witnessed by a
finite **derivation tree**, and checking that a purported tree is correct is a purely
mechanical, *bounded* task. Searching through all candidate trees therefore gives a
procedure that halts exactly on the members of the set: inductively defined sets with
computable rules are **computably enumerable**. This observation — essentially
Post's (1943) analysis of formal systems as "canonical systems" — is the common
engine behind both the universal code (next file) and the enumerability of the
theorems of Peano arithmetic (later).

We set it up abstractly. Judgements are numbers. A **rule system** is a computable
test `step x w js`: "judgement `x` follows in one step from the (coded) list `js` of
premises, using the auxiliary witness `w`". `Derivable step x` is the least set closed
under the rules. A **tree** is a number `⟨⟨x, w⟩, ⟨js, cs⟩⟩` where `cs` codes the list of
subtrees and `js` the list of their roots; validity is checked by course-of-values
recursion, since subtrees have smaller numbers than the tree.
-/

namespace Foundations.Logic.Computability

/-! ## Every number codes a list -/

/-- Decoding a number as a list (inverse of `encList`). -/
def decList : Nat → List Nat
  | 0 => []
  | n + 1 => fst n :: decList (snd n)
decreasing_by
  have h := snd_le n
  omega

/-- **Every number codes a list**: `encList (decList n) = n`. -/
theorem encList_decList (n : Nat) : encList (decList n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
      cases n with
      | zero => simp [decList, encList]
      | succ n =>
          rw [decList, encList, ih (snd n) (by have := snd_le n; omega), pair_fst_snd]

/-- In-range `getD` is indexing. -/
theorem getD_eq_getElem' (l : List Nat) (i : Nat) (h : i < l.length) : l.getD i 0 = l[i] :=
  (List.getElem_eq_getD 0).symm

/-! ## Rule systems and derivability -/

/-- **Derivability** in a rule system: `x` is derivable if, for some witness `w` and
some list `l` of derivable premises, the rule test `step x w ⌜l⌝` succeeds. -/
inductive Derivable (step : Nat → Nat → Nat → Bool) : Nat → Prop where
  /-- Apply one rule to already derived premises. -/
  | intro (x w : Nat) (l : List Nat) :
      (∀ y ∈ l, Derivable step y) → step x w (encList l) = true → Derivable step x

variable (step : Nat → Nat → Nat → Bool)

/-- The judgement at the root of a tree. -/
def troot (t : Nat) : Nat := fst (fst t)

/-- The one-step check for course-of-values tree validation. Its argument is
`⟨_, ⟨t, H⟩⟩` with `H` the history of validity values below `t`. -/
def treeStep (q : Nat) : Nat :=
  let t := fst (snd q)
  let js := fst (snd t)
  let cs := snd (snd t)
  (step (fst (fst t)) (snd (fst t)) js &&
    llen js == llen cs &&
    ballLt (fun r =>
        let q := fst r
        let i := snd r
        let t := fst (snd q)
        let H := snd (snd q)
        let js := fst (snd t)
        let cs := snd (snd t)
        decide (lnth cs i < t) && histGet H t (lnth cs i) == 1 &&
          troot (lnth cs i) == lnth js i)
      q (llen cs)).toNat

/-- **Validity of a derivation tree** (value `1` = valid). -/
def tvalid (t : Nat) : Nat := covRec (treeStep step) 0 t

/-- Unfolding validity: a tree is valid iff its root follows by a rule from the roots of
its subtrees, and all subtrees are smaller and valid. -/
theorem tvalid_iff (t : Nat) : tvalid step t = 1 ↔
    step (troot t) (snd (fst t)) (fst (snd t)) = true ∧
    llen (fst (snd t)) = llen (snd (snd t)) ∧
    ∀ i, i < llen (snd (snd t)) → lnth (snd (snd t)) i < t ∧
      tvalid step (lnth (snd (snd t)) i) = 1 ∧
      troot (lnth (snd (snd t)) i) = lnth (fst (snd t)) i := by
  rw [show tvalid step t = treeStep step (pair 0 (pair t (covHist (treeStep step) 0 t))) from rfl]
  simp only [treeStep, fst_pair, snd_pair]
  rw [show ∀ b : Bool, b.toNat = 1 ↔ b = true by intro b; cases b <;> simp]
  simp only [Bool.and_eq_true, beq_iff_eq, ballLt_iff, fst_pair, snd_pair, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨h₁, h₂, fun i hi => ?_⟩
    obtain ⟨⟨h₄, h₅⟩, h₆⟩ := h₃ i hi
    have e := histGet_covHist (treeStep step) 0 t _ h₄
    rw [e] at h₅
    exact ⟨h₄, h₅, h₆⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨⟨h₁, h₂⟩, fun i hi => ?_⟩
    obtain ⟨h₄, h₅, h₆⟩ := h₃ i hi
    exact ⟨⟨h₄, by rw [histGet_covHist _ _ _ _ h₄]; exact h₅⟩, h₆⟩

/-- **Soundness of trees.** The root of a valid tree is derivable. -/
theorem derivable_of_tvalid : ∀ t, tvalid step t = 1 → Derivable step (troot t) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
      intro ht
      obtain ⟨h₁, h₂, h₃⟩ := (tvalid_iff step t).1 ht
      refine .intro _ (snd (fst t)) (decList (fst (snd t))) (fun y hy => ?_)
        (by rw [encList_decList]; exact h₁)
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hlen : (decList (fst (snd t))).length = llen (fst (snd t)) := by
        conv => rhs; rw [← encList_decList (fst (snd t))]
        rw [llen_encList]
      have hi' : i < llen (snd (snd t)) := by omega
      obtain ⟨h₄, h₅, h₆⟩ := h₃ i hi'
      have := ih _ h₄ h₅
      rw [h₆] at this
      have e : lnth (fst (snd t)) i = (decList (fst (snd t)))[i] := by
        conv => lhs; rw [← encList_decList (fst (snd t))]
        rw [lnth_encList, getD_eq_getElem']
      rwa [e] at this

/-- Choosing a list of witnesses, one for each member of a list. -/
theorem exists_list_witness {P : Nat → Nat → Prop} :
    ∀ l : List Nat, (∀ y ∈ l, ∃ t, P y t) →
      ∃ ts : List Nat, ts.length = l.length ∧ ∀ i (h : i < l.length) (h' : i < ts.length),
        P l[i] ts[i]
  | [], _ => ⟨[], rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | y :: l, h => by
      obtain ⟨t, ht⟩ := h y (List.mem_cons_self ..)
      obtain ⟨ts, hlen, hts⟩ := exists_list_witness l fun z hz => h z (List.mem_cons_of_mem _ hz)
      refine ⟨t :: ts, by simp [hlen], fun i hi hi' => ?_⟩
      cases i with
      | zero => exact ht
      | succ i => exact hts i (by simpa using hi) (by simpa using hi')

/-- **Completeness of trees.** Every derivable judgement is the root of a valid tree. -/
theorem exists_tvalid {x : Nat} (h : Derivable step x) : ∃ t, tvalid step t = 1 ∧ troot t = x := by
  induction h with
  | intro x w l _ hstep ih =>
      obtain ⟨ts, hlen, hts⟩ := exists_list_witness (P := fun y t => tvalid step t = 1 ∧ troot t = y) l ih
      refine ⟨pair (pair x w) (pair (encList l) (encList ts)), ?_, by simp [troot]⟩
      refine (tvalid_iff step _).2 ⟨by simpa [troot] using hstep, by simp [llen_encList, hlen],
        fun i hi => ?_⟩
      simp only [snd_pair, fst_pair, llen_encList] at hi ⊢
      have hi' : i < l.length := by omega
      obtain ⟨h₁, h₂⟩ := hts i hi' hi
      refine ⟨?_, ?_, ?_⟩
      · have := lnth_lt ts i hi
        have := right_le_pair (encList l) (encList ts)
        have := right_le_pair (pair x w) (pair (encList l) (encList ts))
        omega
      · rw [lnth_encList, getD_eq_getElem' _ _ hi]; exact h₁
      · rw [lnth_encList, lnth_encList, getD_eq_getElem' _ _ hi,
          getD_eq_getElem' _ _ hi', h₂]

/-- **Derivability is witnessed by trees.** -/
theorem derivable_iff_exists_tree (x : Nat) :
    Derivable step x ↔ ∃ t, tvalid step t = 1 ∧ troot t = x :=
  ⟨exists_tvalid step, fun ⟨t, ht, hr⟩ => hr ▸ derivable_of_tvalid step t ht⟩

/-- Feeding three computable arguments to a computable three-place test. -/
theorem CompB.step3 {step : Nat → Nat → Nat → Bool}
    (hstep : CompB fun n => step (fst n) (fst (snd n)) (snd (snd n)))
    {a b c : Nat → Nat} (ha : Comp a) (hb : Comp b) (hc : Comp c) :
    CompB fun n => step (a n) (b n) (c n) :=
  CompB.congr (CompB.comp hstep (Comp.pair ha (Comp.pair hb hc))) fun n => by simp

/-- Tree validity is computable, provided the rules are. -/
theorem comp_tvalid (hstep : CompB fun n => step (fst n) (fst (snd n)) (snd (snd n))) :
    Comp (tvalid step) := by
  have hg : Comp (treeStep step) := by
    unfold treeStep
    refine CompB.and (CompB.and (CompB.step3 hstep
      (Comp.fst (Comp.fst (Comp.fst (Comp.snd Comp.id))))
      (Comp.snd (Comp.fst (Comp.fst (Comp.snd Comp.id))))
      (Comp.fst (Comp.snd (Comp.fst (Comp.snd Comp.id)))))
      (CompB.eq (Comp.llen (Comp.fst (Comp.snd (Comp.fst (Comp.snd Comp.id)))))
        (Comp.llen (Comp.snd (Comp.snd (Comp.fst (Comp.snd Comp.id))))))) ?_
    · refine CompB.ballLt ?_ (Comp.llen (Comp.snd (Comp.snd (Comp.fst (Comp.snd Comp.id)))))
      have ht : Comp fun r => fst (snd (fst r)) := Comp.fst (Comp.snd (Comp.fst Comp.id))
      have hcs : Comp fun r => snd (snd (fst (snd (fst r)))) := Comp.snd (Comp.snd ht)
      have hjs : Comp fun r => fst (snd (fst (snd (fst r)))) := Comp.fst (Comp.snd ht)
      have hc : Comp fun r => lnth (snd (snd (fst (snd (fst r))))) (snd r) :=
        Comp.lnth hcs (Comp.snd Comp.id)
      exact CompB.and (CompB.and (CompB.lt hc ht)
        (CompB.eq (Comp.histGet (Comp.snd (Comp.snd (Comp.fst Comp.id))) ht hc) (Comp.const 1)))
        (CompB.eq (Comp.fst (Comp.fst hc)) (Comp.lnth hjs (Comp.snd Comp.id)))
  have := Comp.comp (Comp.covRec hg) (Comp.pair (Comp.const 0) Comp.id)
  exact Comp.congr this fun n => by simp [Computability.tvalid]

/-- **Searching for derivation trees.** For computable rules and a computable "key"
function on judgements, there is a code which on input `a` finds a valid tree whose
root has key `a` (and diverges if there is none). -/
theorem tree_search (hstep : CompB fun n => step (fst n) (fst (snd n)) (snd (snd n)))
    {key : Nat → Nat} (hkey : Comp key) :
    ∃ c : Code, (∀ a t, Eval c [a] t → tvalid step t = 1 ∧ key (troot t) = a) ∧
      ∀ a, (∃ t, tvalid step t = 1 ∧ key (troot t) = a) → ∃ t, Eval c [a] t := by
  have hp : CompB fun p => tvalid step (snd p) == 1 && key (troot (snd p)) == fst p :=
    CompB.and (CompB.eq (Comp.comp (comp_tvalid step hstep) (Comp.snd Comp.id)) (Comp.const 1))
      (CompB.eq (Comp.comp hkey (Comp.fst (Comp.fst (Comp.snd Comp.id)))) (Comp.fst Comp.id))
  obtain ⟨c, hc⟩ := search hp
  refine ⟨c, fun a t h => ?_, fun a ⟨t, ht⟩ => ?_⟩
  · have := ((hc a t).1 h).1
    simpa using this
  · obtain ⟨t, ht, hmin⟩ := exists_least (p := fun t => tvalid step t = 1 ∧ key (troot t) = a) ⟨t, ht⟩
    refine ⟨t, (hc a t).2 ⟨by simpa using ht, fun m hm => ?_⟩⟩
    have := hmin m hm
    simp only [fst_pair, snd_pair, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    by_cases h : tvalid step m = 1
    · exact Or.inr fun h' => this ⟨h, h'⟩
    · exact Or.inl h

/-- **Inductively defined sets with computable rules are computably enumerable.** -/
theorem ce_derivable (hstep : CompB fun n => step (fst n) (fst (snd n)) (snd (snd n))) :
    ∃ c : Code, ∀ x, Halts c [x] ↔ Derivable step x := by
  obtain ⟨c, h₁, h₂⟩ := tree_search step hstep Comp.id
  refine ⟨c, fun x => ⟨fun ⟨t, ht⟩ => ?_, fun h => h₂ x ((derivable_iff_exists_tree step x).1 h)⟩⟩
  obtain ⟨hv, hr⟩ := h₁ x t ht
  exact hr ▸ derivable_of_tvalid step t hv

end Foundations.Logic.Computability
