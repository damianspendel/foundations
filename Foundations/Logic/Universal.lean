import Foundations.Logic.Derivations
import Foundations.Logic.RecursionTheorem

/-!
# The universal code, Kleene's normal form, s-m-n and the recursion theorem

Turing's most consequential discovery (1936) was the **universal machine**: a single
machine that, given the description of any machine and an input, simulates it. In
Kleene's setting this is a single code `U` with `U(⌜c⌝, x⃗) ≃ c(x⃗)` for every code `c` —
an interpreter for the language of codes, written in that same language. Every
modern computer is a physical realisation of this idea: hardware is fixed, programs
are data.

We obtain `U` from the general principle of the previous file. The evaluation
relation `Eval` is an inductive definition whose rules are mechanically checkable on
Gödel numbers; a *derivation* of `Eval c xs n` is precisely a finite **computation
trace**. So `U` searches for a valid trace for `(⌜c⌝, ⌜xs⌝)` and reads off its
output. The trace test is primitive recursive, so this also gives **Kleene's normal
form theorem** (1943): every partial recursive function is `out(μt. T(e, x, t))`
for a single primitive recursive predicate `T` and a single function `out` —
one unbounded search suffices.

With `U` in hand we define the standard **numbering of partial recursive functions**
`φₑ(y) ≃ U(e, y)` (so that `φ_{⌜c⌝} = c`), and prove

* the **s-m-n theorem**: parameters can be absorbed into programs computably,
  `φ_{s(e, x)}(y) ≃ φₑ(x, y)`;
* the **recursion theorem** in its classical form: for every total computable
  transformation `f` of program numbers there is a program `e` with `φₑ = φ_{f(e)}` —
  a "fixed point" of `f` up to the function computed.
-/

namespace Foundations.Logic.Computability

open Code

/-! ## Evaluation as a rule system -/

/-- The judgement "code number `c`, on the coded input list `xs`, outputs `n`". -/
def judg (c xs n : Nat) : Nat := pair c (pair xs n)

/-- Cons for coded lists. -/
def lcons (a l : Nat) : Nat := pair a l + 1

/-- `lcons` agrees with `encList`. -/
@[simp] theorem lcons_encList (a : Nat) (l : List Nat) : lcons a (encList l) = encList (a :: l) := rfl

/-- **One evaluation step**, checked on Gödel numbers. The argument packs the judgement
`x = ⟨c, ⟨xs, n⟩⟩`, a witness `w` and the coded list `js` of premises. The tag of `c`
selects the rule:
`0` zero, `1` successor, `2` projection, `3` composition (witness: the list of
intermediate values), `4` primitive recursion (witness: the previous value),
`5` minimisation (witness: the list of non-zero values minus one). -/
def evalStep (q : Nat) : Bool :=
  -- abbreviations: x = fst q, w = fst (snd q), js = snd (snd q)
  -- c = fst (fst q), xs = fst (snd (fst q)), n = snd (snd (fst q))
  (fst (fst (fst q)) == 0 && snd (snd (fst q)) == 0) ||
  (fst (fst (fst q)) == 1 && snd (snd (fst q)) == lhead (fst (snd (fst q))) + 1) ||
  (fst (fst (fst q)) == 2 && snd (snd (fst q)) == lnth (fst (snd (fst q))) (snd (fst (fst q)))) ||
  (fst (fst (fst q)) == 3 &&
    llen (fst (snd q)) == llen (snd (snd (fst (fst q)))) &&
    lnth (snd (snd q)) (llen (snd (snd (fst (fst q))))) ==
      judg (fst (snd (fst (fst q)))) (fst (snd q)) (snd (snd (fst q))) &&
    ballLt (fun r => lnth (snd (snd (fst r))) (snd r) ==
        judg (lnth (snd (snd (fst (fst (fst r))))) (snd r)) (fst (snd (fst (fst r))))
          (lnth (fst (snd (fst r))) (snd r)))
      q (llen (snd (snd (fst (fst q)))))) ||
  (fst (fst (fst q)) == 4 && !(fst (snd (fst q)) == 0) &&
    ((lhead (fst (snd (fst q))) == 0 &&
      lnth (snd (snd q)) 0 ==
        judg (fst (snd (fst (fst q)))) (ltail (fst (snd (fst q)))) (snd (snd (fst q)))) ||
     (!(lhead (fst (snd (fst q))) == 0) &&
      lnth (snd (snd q)) 0 ==
        judg (fst (fst q)) (lcons (lhead (fst (snd (fst q))) - 1) (ltail (fst (snd (fst q)))))
          (fst (snd q)) &&
      lnth (snd (snd q)) 1 ==
        judg (snd (snd (fst (fst q))))
          (lcons (lhead (fst (snd (fst q))) - 1) (lcons (fst (snd q)) (ltail (fst (snd (fst q))))))
          (snd (snd (fst q)))))) ||
  (fst (fst (fst q)) == 5 &&
    lnth (snd (snd q)) 0 ==
      judg (snd (fst (fst q))) (lcons (snd (snd (fst q))) (fst (snd (fst q)))) 0 &&
    ballLt (fun r => lnth (snd (snd (fst r))) (snd r + 1) ==
        judg (snd (fst (fst (fst r)))) (lcons (snd r) (fst (snd (fst (fst r)))))
          (lnth (fst (snd (fst r))) (snd r) + 1))
      q (snd (snd (fst q))))

/-- The rule system for evaluation, as a three-place test. -/
def evalRule (x w js : Nat) : Bool := evalStep (pair x (pair w js))

/-- Definition by cases for tests. -/
theorem CompB.cond {p q r : Nat → Bool} (hp : CompB p) (hq : CompB q) (hr : CompB r) :
    CompB fun n => bif p n then q n else r n :=
  CompB.congr (CompB.or (CompB.and hp hq) (CompB.and (CompB.not hp) hr)) fun n => by
    cases p n <;> simp

/-- Cons is computable. -/
theorem Comp.lcons' {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    Comp fun n => Computability.lcons (f n) (g n) := Comp.lcons hf hg

/-- Judgements are computable. -/
theorem Comp.judg {f g h : Nat → Nat} (hf : Comp f) (hg : Comp g) (hh : Comp h) :
    Comp fun n => Computability.judg (f n) (g n) (h n) := Comp.pair hf (Comp.pair hg hh)

/-- A tactic proving computability of explicitly written functions, by repeatedly
applying closure lemmas. -/
macro "comp_tac" : tactic => `(tactic| repeat (first
  | exact Comp.id | exact Comp.const _ | exact CompB.const _
  | apply CompB.or | apply CompB.and | apply CompB.not | apply CompB.eq | apply CompB.lt
  | apply CompB.ballLt | apply Comp.cond | apply CompB.cond | apply Comp.histGet
  | apply Comp.judg | apply Comp.lcons' | apply Comp.pair | apply Comp.lnth | apply Comp.llen
  | apply Comp.lhead | apply Comp.ltail | apply Comp.fst | apply Comp.snd
  | apply Comp.succ | apply Comp.add | apply Comp.sub | apply Comp.mul))

/-- **The evaluation rules are computable.** -/
theorem evalStep_comp : CompB evalStep := by
  unfold evalStep
  comp_tac

/-- The evaluation rules, in the three-place form required by `Derivations`. -/
theorem evalRule_comp : CompB fun n => evalRule (fst n) (fst (snd n)) (snd (snd n)) :=
  CompB.congr evalStep_comp fun n => by simp [evalRule, pair_fst_snd]

/-! ## Correctness of the rule system -/

/-- `List.ofFn` of a function read off a coded list. -/
theorem ofFn_lnth (l : List Nat) : List.ofFn (fun i : Fin l.length => lnth (encList l) i) = l := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [lnth_encList]

/-- Rewriting a judgement about a decoded list. -/
theorem Derivable.of_mem {step} {l : List Nat} (h : ∀ y ∈ l, Derivable step y) (i : Nat)
    (hi : i < l.length) : Derivable step (lnth (encList l) i) := by
  rw [lnth_encList, getD_eq_getElem' l i hi]; exact h _ (List.getElem_mem hi)

/-- Out-of-range `getD` is the default. -/
theorem getD_eq_zero' (l : List Nat) (i : Nat) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- A premise read off a coded list of derivable judgements is true (out-of-range reads
give `0 = judg 0 0 0`, the true judgement "`zero` outputs `0` on the empty input"). -/
theorem eval_of_lnth {l : List Nat}
    (ih : ∀ y ∈ l, ∀ (c : Code) (xs : List Nat) (n : Nat), y = judg (encode c) (encList xs) n →
      Eval c xs n)
    {i : Nat} {c : Code} {xs : List Nat} {n : Nat}
    (h : lnth (encList l) i = judg (encode c) (encList xs) n) : Eval c xs n := by
  by_cases hi : i < l.length
  · exact ih _ (List.getElem_mem hi) c xs n (by rw [← h, lnth_encList, getD_eq_getElem' l i hi])
  · rw [lnth_encList, getD_eq_zero' _ _ (by omega)] at h
    have h1 := pair_inj (show pair 0 0 = pair (encode c) (pair (encList xs) n) from h)
    have h2 := pair_inj (show pair 0 0 = pair (encList xs) n from h1.2)
    have hc : c = .zero := encode_inj (show encode c = encode .zero from h1.1.symm)
    subst hc; rw [← h2.2]; exact .zero

/-- Reading the `i`-th entry of the coded list `⌜ofFn gs⌝`. -/
theorem lnth_ofFn {k : Nat} (v : Fin k → Nat) (i : Fin k) :
    lnth (encList (List.ofFn v)) i = v i := by
  rw [lnth_encList, getD_eq_getElem' _ _ (by simp)]; simp

/-- **Soundness of the rule system**: derivable judgements about codes are true. -/
theorem eval_of_derivable {x : Nat} (h : Derivable evalRule x) :
    ∀ (c : Code) (xs : List Nat) (n : Nat), x = judg (encode c) (encList xs) n → Eval c xs n := by
  induction h with
  | intro x w l hl hstep ih =>
      intro c xs n hx
      subst hx
      have prem := @eval_of_lnth l ih
      cases c with
      | zero =>
          simp only [evalRule, evalStep, judg, encode, fst_pair, snd_pair] at hstep
          simp at hstep
          subst hstep; exact .zero
      | succ =>
          simp only [evalRule, evalStep, judg, encode, fst_pair, snd_pair] at hstep
          simp at hstep
          subst hstep; cases xs <;> simp only [lhead_nil, lhead_cons] <;> exact .succ
      | proj i =>
          simp only [evalRule, evalStep, judg, encode, fst_pair, snd_pair] at hstep
          simp at hstep
          subst hstep; rw [lnth_encList]; exact .proj
      | @comp k f gs =>
          simp only [evalRule, evalStep, judg, encode, fst_pair, snd_pair] at hstep
          simp only [llen_encList, List.length_ofFn] at hstep
          simp at hstep
          obtain ⟨⟨hw, hf⟩, hg⟩ := hstep
          rw [ballLt_iff] at hg
          obtain ⟨vs, rfl⟩ : ∃ vs : List Nat, encList vs = w := ⟨_, encList_decList w⟩
          rw [llen_encList] at hw
          subst hw
          refine .comp (fun i => lnth (encList vs) i) (fun i => prem (i := i.val) ?_) ?_
          · have hgi := hg i.val i.isLt
            simp only [fst_pair, snd_pair, beq_iff_eq, lnth_ofFn] at hgi
            exact hgi
          · rw [ofFn_lnth]; exact prem hf
      | prec f g =>
          simp only [evalRule, evalStep, judg, encode, fst_pair, snd_pair] at hstep
          simp at hstep
          obtain ⟨hne, hcase⟩ := hstep
          cases xs with
          | nil => exact absurd rfl hne
          | cons m rest =>
              simp only [lhead_cons, ltail_cons] at hcase
              rcases hcase with ⟨hm, h0⟩ | ⟨⟨hm, h0⟩, h1⟩
              · subst hm; exact .prec_zero (prem h0)
              · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                simp only [Nat.add_sub_cancel, lcons_encList] at h0 h1
                exact .prec_succ (prem (c := .prec f g) h0) (prem h1)
      | mu f =>
          simp only [evalRule, evalStep, judg, encode, fst_pair, snd_pair] at hstep
          simp at hstep
          obtain ⟨h0, hlt⟩ := hstep
          rw [ballLt_iff] at hlt
          refine .mu (fun m => lnth w m) (prem h0) (fun m hm => prem (i := m + 1) ?_)
          have := hlt m hm
          simp only [fst_pair, snd_pair, beq_iff_eq, lcons_encList] at this
          exact this

/-- Non-empty lists have non-zero codes. -/
@[simp] theorem encList_cons_ne_zero (x : Nat) (l : List Nat) : ¬ encList (x :: l) = 0 := by
  simp [encList]

/-- Head of a coded list, as `headD`. -/
theorem lhead_encList (xs : List Nat) : lhead (encList xs) = xs.headD 0 := by
  cases xs <;> simp

/-- **Completeness of the rule system**: every true evaluation judgement is derivable. -/
theorem derivable_of_eval {c : Code} {xs : List Nat} {n : Nat} (h : Eval c xs n) :
    Derivable evalRule (judg (encode c) (encList xs) n) := by
  induction h with
  | zero => exact .intro _ 0 [] (by simp) (by simp [evalRule, evalStep, judg, encode])
  | succ => exact .intro _ 0 [] (by simp) (by simp [evalRule, evalStep, judg, encode, lhead_encList])
  | proj => exact .intro _ 0 [] (by simp) (by simp [evalRule, evalStep, judg, encode, lnth_encList])
  | @comp k f gs xs n vs _ _ ihg ihf =>
      refine .intro _ (encList (List.ofFn vs))
        (List.ofFn (fun i => judg (encode (gs i)) (encList xs) (vs i)) ++
          [judg (encode f) (encList (List.ofFn vs)) n]) ?_ ?_
      · intro y hy
        simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hy
        rcases hy with ⟨i, rfl⟩ | rfl
        · exact ihg i
        · exact ihf
      · simp [evalRule, evalStep, judg, encode, llen_encList, lnth_encList, List.getD_eq_getElem?_getD, ballLt_iff]
        intro i hi
        rw [List.getElem?_append_left (by simpa using hi)]
        simp [hi]
  | @prec_zero f g xs n _ ih =>
      refine .intro _ 0 [judg (encode f) (encList xs) n] (by simpa using ih) ?_
      simp [evalRule, evalStep, judg, encode, lnth_encList]
  | @prec_succ f g m xs r n _ _ ih₁ ih₂ =>
      refine .intro _ r [judg (encode (.prec f g)) (encList (m :: xs)) r,
        judg (encode g) (encList (m :: r :: xs)) n] (by simp; exact ⟨ih₁, ih₂⟩) ?_
      simp [evalRule, evalStep, judg, encode, lnth_encList]
  | @mu f xs n ks _ _ ih₀ ihlt =>
      refine .intro _ (encList (List.ofFn fun i : Fin n => ks i))
        (judg (encode f) (encList (n :: xs)) 0 ::
          List.ofFn (fun i : Fin n => judg (encode f) (encList (i.val :: xs)) (ks i + 1))) ?_ ?_
      · intro y hy
        simp only [List.mem_cons, List.mem_ofFn] at hy
        rcases hy with rfl | ⟨i, rfl⟩
        · exact ih₀
        · exact ihlt i i.isLt
      · simp [evalRule, evalStep, judg, encode, lnth_encList, List.getD_eq_getElem?_getD, ballLt_iff]
        intro i hi
        simp [hi]

/-- **Evaluation is derivability** in the rule system `evalRule`. -/
theorem eval_iff_derivable (c : Code) (xs : List Nat) (n : Nat) :
    Eval c xs n ↔ Derivable evalRule (judg (encode c) (encList xs) n) :=
  ⟨derivable_of_eval, fun h => eval_of_derivable h c xs n rfl⟩

/-! ## Kleene's normal form -/

/-- **Kleene's T-predicate.** `kleeneT e xs t`: the number `t` is a valid computation
trace (derivation tree) for code number `e` on the coded input list `xs`. -/
def kleeneT (e xs t : Nat) : Bool :=
  tvalid evalRule t == 1 && fst (troot t) == e && fst (snd (troot t)) == xs

/-- The output recorded at the root of a computation trace. -/
def traceOut (t : Nat) : Nat := snd (snd (troot t))

/-- Validity of computation traces is computable. -/
theorem tvalid_evalRule_comp : Comp (tvalid evalRule) := comp_tvalid evalRule evalRule_comp

/-- **The T-predicate is computable** (indeed primitive recursive: it was built
without unbounded search). -/
theorem kleeneT_comp : CompB fun n => kleeneT (fst n) (fst (snd n)) (snd (snd n)) := by
  unfold kleeneT troot
  refine CompB.and (CompB.and (CompB.eq (Comp.comp tvalid_evalRule_comp
    (Comp.snd (Comp.snd Comp.id))) (Comp.const 1)) ?_) ?_ <;> comp_tac

/-- The output function is computable. -/
theorem traceOut_comp : Comp traceOut := by unfold traceOut troot; comp_tac

/-- Reassembling the root of a trace from its components. -/
theorem troot_eq (t : Nat) : troot t = judg (fst (troot t)) (fst (snd (troot t))) (traceOut t) := by
  simp [judg, traceOut, pair_fst_snd]

/-- **Kleene's normal form theorem.** A code `c` outputs `n` on `xs` iff there is a
computation trace `t` satisfying the (computable) T-predicate whose recorded output is
`n`. Hence every partial recursive function has the form `out(μt. T(e, x⃗, t))`. -/
theorem kleene_normal_form (c : Code) (xs : List Nat) (n : Nat) :
    Eval c xs n ↔ ∃ t, kleeneT (encode c) (encList xs) t = true ∧ traceOut t = n := by
  rw [eval_iff_derivable, derivable_iff_exists_tree]
  constructor
  · rintro ⟨t, hv, hr⟩
    refine ⟨t, by simp [kleeneT, hv, hr, judg], by simp [traceOut, hr, judg]⟩
  · rintro ⟨t, hT, rfl⟩
    simp only [kleeneT, Bool.and_eq_true, beq_iff_eq] at hT
    obtain ⟨⟨hv, h₁⟩, h₂⟩ := hT
    exact ⟨t, hv, by rw [troot_eq t, h₁, h₂]⟩

/-! ## The universal code -/

/-- A code finding a computation trace for `⟨e, xs⟩`. -/
theorem exists_traceSearch : ∃ c : Code,
    (∀ a t, Eval c [a] t → tvalid evalRule t = 1 ∧
      pair (fst (troot t)) (fst (snd (troot t))) = a) ∧
    ∀ a, (∃ t, tvalid evalRule t = 1 ∧ pair (fst (troot t)) (fst (snd (troot t))) = a) →
      ∃ t, Eval c [a] t :=
  tree_search evalRule evalRule_comp (Comp.pair (Comp.fst Comp.id) (Comp.fst (Comp.snd Comp.id)))

/-- The trace-searching code. -/
noncomputable def traceSearch : Code := exists_traceSearch.choose

/-- A code computing `traceOut`. -/
noncomputable def traceOutCode : Code := traceOut_comp.choose

/-- **The universal code** (Turing 1936, Kleene): on inputs `(⌜c⌝, ⌜xs⌝)` it searches
for a computation trace of `c` on `xs` and returns its output. -/
noncomputable def univ : Code :=
  .comp traceOutCode (vec1 (.comp traceSearch (vec1 (pairOf (.proj 0) (.proj 1)))))

/-- **Universality.** `univ(⌜c⌝, ⌜xs⌝) ≃ c(xs)`: the universal code halts with output `n`
exactly when `c` does. -/
theorem eval_univ (c : Code) (xs : List Nat) (n : Nat) :
    Eval univ [encode c, encList xs] n ↔ Eval c xs n := by
  obtain ⟨hs₁, hs₂⟩ := exists_traceSearch.choose_spec
  have hout := traceOut_comp.choose_spec
  -- a trace found by the search is a correct computation
  have found : ∀ t, Eval traceSearch [pair (encode c) (encList xs)] t → Eval c xs (traceOut t) := by
    intro t ht
    obtain ⟨hv, hk⟩ := hs₁ _ t ht
    obtain ⟨h₁, h₂⟩ := pair_inj hk
    rw [eval_iff_derivable, derivable_iff_exists_tree]
    exact ⟨t, hv, by rw [troot_eq t, h₁, h₂]⟩
  constructor
  · intro h
    obtain ⟨t, ht, hn⟩ := eval_comp1_inv h
    obtain ⟨a, ha, ht⟩ := eval_comp1_inv ht
    rw [Eval.det ha (eval_pairOf .proj .proj)] at ht
    rw [← Eval.det (hout t) hn]
    exact found t ht
  · intro h
    obtain ⟨t, hv, hr⟩ := (derivable_iff_exists_tree evalRule _).1 ((eval_iff_derivable c xs n).1 h)
    obtain ⟨t', ht'⟩ := hs₂ (pair (encode c) (encList xs)) ⟨t, hv, by simp [hr, judg]⟩
    have := Eval.det (found t' ht') h
    exact eval_comp1 (eval_comp1 (eval_pairOf .proj .proj) ht') (this ▸ hout t')

/-! ## The standard numbering of partial recursive functions -/

/-- The unary universal code: `U(e, y) = univ(e, ⌜[y]⌝)`. -/
noncomputable def U : Code := .comp univ (vec2 (.proj 0) (succOf (pairOf (.proj 1) .zero)))

/-- **The standard numbering** `φₑ`: `phi e y n` means "the `e`-th partial recursive
function, on input `y`, outputs `n`", defined through the universal code. Every
number is an index, and `φ_{⌜c⌝}` is the function computed by `c`. -/
def phi (e y n : Nat) : Prop := Eval U [e, y] n

/-- `φ_{⌜c⌝}` is the function computed by `c`. -/
theorem phi_encode (c : Code) (y n : Nat) : phi (encode c) y n ↔ Eval c [y] n := by
  unfold phi U
  constructor
  · intro h
    obtain ⟨v₀, v₁, h₀, h₁, h⟩ := eval_comp2_inv h
    cases h₀
    obtain ⟨u, hu, hs⟩ := eval_comp1_inv h₁
    obtain ⟨a, b, ha, hb, hp⟩ := eval_comp2_inv hu
    cases ha; cases hb; cases hs
    rw [Eval.det hp (eval_pair _ _ [])] at h
    exact (eval_univ c [y] n).1 h
  · intro h
    exact eval_comp2 .proj (eval_succOf (eval_pairOf .proj .zero)) ((eval_univ c [y] n).2 h)

/-! ## The s-m-n theorem -/

/-- The s-m-n function: from an index `e` of a two-argument function and a value `x`,
the index of the one-argument function `y ↦ φₑ(x, y)`; concretely the number of the
code "compose `e` with (constant `x`, identity)". -/
def smn (e x : Nat) : Nat :=
  pair 3 (pair e (pair (encode (constCode x)) (pair (encode (.proj 0)) 0 + 1) + 1))

/-- On code numbers, `smn` builds the expected code. -/
theorem smn_encode (c : Code) (x : Nat) :
    smn (encode c) x = encode (.comp c (vec2 (constCode x) (.proj 0))) := (encode_comp2 _ _ _).symm

/-- **The s-m-n function is computable.** -/
theorem smn_comp : Comp fun p => smn (fst p) (snd p) := by
  have hc : Comp fun x => encode (constCode x) := ⟨constEncCode, fun n => eval_constEnc [] n⟩
  unfold smn
  exact Comp.pair (Comp.const 3) (Comp.pair (Comp.fst Comp.id)
    (Comp.succ (Comp.pair (Comp.comp hc (Comp.snd Comp.id)) (Comp.const _))))

/-- **The s-m-n theorem** (Kleene 1938). Fixing the first argument of a two-argument
program is a computable operation on program numbers:
`φ_{s(⌜c⌝, x)}(y) ≃ c(x, y)`. -/
theorem smn_spec (c : Code) (x y n : Nat) : phi (smn (encode c) x) y n ↔ Eval c [x, y] n := by
  rw [smn_encode, phi_encode]
  constructor
  · intro h
    obtain ⟨v₀, v₁, h₀, h₁, h⟩ := eval_comp2_inv h
    rw [Eval.det h₀ (eval_const _ x)] at h
    cases h₁
    exact h
  · intro h
    exact eval_comp2 (eval_const _ x) .proj h

/-! ## The recursion theorem, classical form -/

/-- **Kleene's recursion theorem** (classical fixed-point form). For every total
computable function `f` on program numbers there is a program number `e` such that
`φₑ` and `φ_{f(e)}` are the same partial function. -/
theorem recursion_theorem_fixed_point {f : Nat → Nat} (hf : Comp f) :
    ∃ e, ∀ y n, phi e y n ↔ phi (f e) y n := by
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨q, hq⟩ := recursion_theorem (.comp U (vec2 (.comp cf (vec1 (.proj 0))) (.proj 1)))
  refine ⟨encode q, fun y n => ?_⟩
  rw [phi_encode, hq]
  unfold phi
  constructor
  · intro h
    obtain ⟨v₀, v₁, h₀, h₁, h⟩ := eval_comp2_inv h
    obtain ⟨u, hu, h₀⟩ := eval_comp1_inv h₀
    cases hu; cases h₁
    rwa [Eval.det h₀ (hcf _)] at h
  · intro h
    exact eval_comp2 (eval_comp1 .proj (hcf _)) .proj h

end Foundations.Logic.Computability
