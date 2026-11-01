import Foundations.Logic.ArithWellFormed
import Foundations.Logic.Derivations
import Foundations.Logic.FOProofTheory

/-!
# Derivations from Peano arithmetic as a computable rule system

Hilbert's demand that proofs be *mechanically checkable* is met by every reasonable
formal system, and Peano arithmetic in particular: whether a finite object is a
correct derivation can be decided by an algorithm. Consequently an algorithm can
*list* all theorems of PA, by running through all candidate derivations. This is the
second ingredient of the incompleteness theorem.

Our natural deduction `⊢₁` works with *theories* (arbitrary sets of premises) and
re-indexes the premises when passing under a quantifier. A derivation from PA
therefore only ever uses premises of the form

`shiftPA k ∪ Δ`,

the axioms of PA shifted `k` times together with a finite list `Δ` of discharged
assumptions. We record such a situation as a **judgement** `⟨k, ⟨⌜Δ⌝, ⌜φ⌝⟩⟩` and
write down, rule by rule, a computable test `paStep` saying when a judgement follows
from premise judgements (using a witness for data such as the instantiating term of
a ∀-elimination). This file defines the rule system and proves that its rules are
computable; the next file (`PAProofs`) proves that it captures exactly `⊢₁`.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula Theory Computability

/-! ## Contexts of derivations from PA -/

/-- The axioms of PA, shifted `k` times. -/
def shiftPA (k : Nat) : Theory Arith := fun χ => ∃ ψ, PA ψ ∧ χ = shiftN k ψ

/-- The premises available in a judgement: shifted PA axioms and a finite list. -/
def Ctx (k : Nat) (Δ : List (Formula Arith)) : Theory Arith :=
  Theory.union (shiftPA k) (Theory.ofList Δ)

/-- Adding a discharged assumption. -/
theorem ctx_cons_sub (k : Nat) (A : Formula Arith) (Δ : List (Formula Arith)) :
    (Ctx k (A :: Δ)).Subset (Theory.insert (Ctx k Δ) A) := by
  rintro ψ (h | h)
  · exact Or.inr (Or.inl h)
  · rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr h)

/-- Adding a discharged assumption, converse inclusion. -/
theorem insert_ctx_sub (k : Nat) (A : Formula Arith) (Δ : List (Formula Arith)) :
    (Theory.insert (Ctx k Δ) A).Subset (Ctx k (A :: Δ)) := by
  rintro ψ (rfl | h | h)
  · exact Or.inr (List.mem_cons_self ..)
  · exact Or.inl h
  · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Passing under a binder. -/
theorem ctx_shift_sub (k : Nat) (Δ : List (Formula Arith)) :
    (Ctx (k + 1) (Δ.map Formula.shift)).Subset (Theory.shift (Ctx k Δ)) := by
  rintro ψ (⟨χ, hχ, rfl⟩ | h)
  · exact ⟨shiftN k χ, Or.inl ⟨χ, hχ, rfl⟩, rfl⟩
  · obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 h
    exact ⟨χ, Or.inr hχ, rfl⟩

/-- Passing under a binder, converse inclusion. -/
theorem shift_ctx_sub (k : Nat) (Δ : List (Formula Arith)) :
    (Theory.shift (Ctx k Δ)).Subset (Ctx (k + 1) (Δ.map Formula.shift)) := by
  rintro ψ ⟨χ, (⟨θ, hθ, rfl⟩ | h), rfl⟩
  · exact Or.inl ⟨θ, hθ, rfl⟩
  · exact Or.inr (List.mem_map.2 ⟨χ, h, rfl⟩)

/-! ## Codes of the axioms -/

/-- The induction axiom for `χ`. -/
def indAx (χ : Formula Arith) : Formula Arith :=
  imp (conj (χ.inst zero) (all (imp χ (χ.subst succSubst)))) (all χ)

/-- The six closed axioms of PA. -/
def closedAx : List (Formula Arith) :=
  [all (neg (eq (succ (v 0)) zero)),
   all (all (imp (eq (succ (v 1)) (succ (v 0))) (eq (v 1) (v 0)))),
   all (eq (add (v 0) zero) (v 0)),
   all (all (eq (add (v 1) (succ (v 0))) (succ (add (v 1) (v 0))))),
   all (eq (mul (v 0) zero) zero),
   all (all (eq (mul (v 1) (succ (v 0))) (add (mul (v 1) (v 0)) (v 1))))]

/-- The axioms of PA are the closed axioms and the induction axioms. -/
theorem PA_iff (ψ : Formula Arith) : PA ψ ↔ ψ ∈ closedAx ∨ ∃ χ, ψ = indAx χ := by
  constructor
  · intro h
    cases h <;> first | exact Or.inr ⟨_, rfl⟩ | exact Or.inl (by simp [closedAx])
  · rintro (h | ⟨χ, rfl⟩)
    · simp only [closedAx, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor
    · exact PA.induction χ

/-- The code of the induction axiom for (the formula with code) `χ`. -/
def indC (χ : Nat) : Nat :=
  pair 2 (pair (pair 3 (pair (instC χ (pair 1 0)) (pair 5 (pair 2 (pair χ (succSubC χ))))))
    (pair 5 χ))

/-- Correctness of `indC`. -/
theorem indC_fcode (χ : Formula Arith) : indC (fcode χ) = fcode (indAx χ) := by
  have h₁ := instC_fcode χ zero
  simp only [tcode_zero] at h₁
  simp only [indC, indAx, fcode, h₁, succSubC_fcode]

/-- The test "`ψ` is an axiom of PA, with `χ` the formula of its induction instance". -/
def isPAC (ψ χ : Nat) : Bool :=
  (closedAx.map fcode).contains ψ || ψ == indC χ

/-- `isPAC` recognises exactly the axioms. -/
theorem isPAC_iff (ψ χ : Formula Arith) :
    isPAC (fcode ψ) (fcode χ) = true ↔ ψ ∈ closedAx ∨ ψ = indAx χ := by
  simp only [isPAC, Bool.or_eq_true, List.contains_iff_mem, List.mem_map, beq_iff_eq, indC_fcode]
  constructor
  · rintro (⟨a, ha, e⟩ | e)
    · exact Or.inl (fcode_inj e ▸ ha)
    · exact Or.inr (fcode_inj e)
  · rintro (h | rfl)
    · exact Or.inl ⟨ψ, h, rfl⟩
    · exact Or.inr rfl

/-! ## The rules on codes -/

/-- A judgement: from shifted PA (`k` times) and the list `Δ`, derive `φ`. -/
def pj (k Δ φ : Nat) : Nat := pair k (pair Δ φ)

-- Components of the step argument `q = ⟨⟨k, ⟨Δ, φ⟩⟩, ⟨⟨tag, data⟩, premises⟩⟩`.
/-- The shift count of the conclusion. -/
abbrev qk (q : Nat) : Nat := fst (fst q)
/-- The context code of the conclusion. -/
abbrev qD (q : Nat) : Nat := fst (snd (fst q))
/-- The formula code of the conclusion. -/
abbrev qF (q : Nat) : Nat := snd (snd (fst q))
/-- The rule tag. -/
abbrev qtag (q : Nat) : Nat := fst (fst (snd q))
/-- The rule data (witness). -/
abbrev qdat (q : Nat) : Nat := snd (fst (snd q))
/-- The coded list of premises. -/
abbrev qjs (q : Nat) : Nat := snd (snd q)
/-- The `i`-th premise. -/
abbrev qprem (q i : Nat) : Nat := lnth (qjs q) i

/-- Well-formedness of the conclusion: a formula code and a list of formula codes. -/
def wfC (q : Nat) : Bool :=
  isFormulaC (qF q) == 1 &&
    ballLt (fun r => isFormulaC (lnth (qD (fst r)) (snd r)) == 1) q (llen (qD q))

/-- "The data is the code of the context, shifted entrywise". -/
def shiftedC (q c : Nat) : Bool :=
  llen c == llen (qD q) &&
    ballLt (fun r => lnth (fst (fst r)) (snd r) == shiftC (lnth (qD (snd (fst r))) (snd r)))
      (pair c q) (llen (qD q))

/-! The rules of natural deduction from shifted PA, on codes, numbered `0–17`. -/

/-- Rule 0 on codes: assumption. -/
def rC0 (q : Nat) : Bool :=
  qtag q == 0 && decide (qdat q < llen (qD q)) && lnth (qD q) (qdat q) == qF q

/-- Rule 1 on codes: axiom. -/
def rC1 (q : Nat) : Bool :=
  qtag q == 1 && isFormulaC (fst (qdat q)) == 1 && isFormulaC (snd (qdat q)) == 1 &&
    shiftNC (qk q) (fst (qdat q)) == qF q && isPAC (fst (qdat q)) (snd (qdat q))

/-- Rule 2 on codes: →-introduction. -/
def rC2 (q : Nat) : Bool :=
  qtag q == 2 && decide (0 < llen (qjs q)) && fst (qF q) == 2 &&
    qprem q 0 == pj (qk q) (lcons (fst (snd (qF q))) (qD q)) (snd (snd (qF q)))

/-- Rule 3 on codes: →-elimination. -/
def rC3 (q : Nat) : Bool :=
  qtag q == 3 && decide (1 < llen (qjs q)) &&
    qprem q 0 == pj (qk q) (qD q) (pair 2 (pair (qdat q) (qF q))) &&
    qprem q 1 == pj (qk q) (qD q) (qdat q)

/-- Rule 4 on codes: ∧-introduction. -/
def rC4 (q : Nat) : Bool :=
  qtag q == 4 && decide (1 < llen (qjs q)) && fst (qF q) == 3 &&
    qprem q 0 == pj (qk q) (qD q) (fst (snd (qF q))) &&
    qprem q 1 == pj (qk q) (qD q) (snd (snd (qF q)))

/-- Rule 5 on codes: ∧-elimination (left). -/
def rC5 (q : Nat) : Bool :=
  qtag q == 5 && decide (0 < llen (qjs q)) &&
    qprem q 0 == pj (qk q) (qD q) (pair 3 (pair (qF q) (qdat q)))

/-- Rule 6 on codes: ∧-elimination (right). -/
def rC6 (q : Nat) : Bool :=
  qtag q == 6 && decide (0 < llen (qjs q)) &&
    qprem q 0 == pj (qk q) (qD q) (pair 3 (pair (qdat q) (qF q)))

/-- Rule 7 on codes: ∨-introduction (left). -/
def rC7 (q : Nat) : Bool :=
  qtag q == 7 && decide (0 < llen (qjs q)) && fst (qF q) == 4 &&
    qprem q 0 == pj (qk q) (qD q) (fst (snd (qF q)))

/-- Rule 8 on codes: ∨-introduction (right). -/
def rC8 (q : Nat) : Bool :=
  qtag q == 8 && decide (0 < llen (qjs q)) && fst (qF q) == 4 &&
    qprem q 0 == pj (qk q) (qD q) (snd (snd (qF q)))

/-- Rule 9 on codes: ∨-elimination. -/
def rC9 (q : Nat) : Bool :=
  qtag q == 9 && decide (2 < llen (qjs q)) &&
    qprem q 0 == pj (qk q) (qD q) (pair 4 (qdat q)) &&
    qprem q 1 == pj (qk q) (lcons (fst (qdat q)) (qD q)) (qF q) &&
    qprem q 2 == pj (qk q) (lcons (snd (qdat q)) (qD q)) (qF q)

/-- Rule 10 on codes: ex falso. -/
def rC10 (q : Nat) : Bool :=
  qtag q == 10 && decide (0 < llen (qjs q)) && qprem q 0 == pj (qk q) (qD q) 0

/-- Rule 11 on codes: reductio ad absurdum. -/
def rC11 (q : Nat) : Bool :=
  qtag q == 11 && decide (0 < llen (qjs q)) &&
    qprem q 0 == pj (qk q) (lcons (pair 2 (pair (qF q) 0)) (qD q)) 0

/-- Rule 12 on codes: ∀-introduction. -/
def rC12 (q : Nat) : Bool :=
  qtag q == 12 && decide (0 < llen (qjs q)) && fst (qF q) == 5 && shiftedC q (qdat q) &&
    qprem q 0 == pj (qk q + 1) (qdat q) (snd (qF q))

/-- Rule 13 on codes: ∀-elimination. -/
def rC13 (q : Nat) : Bool :=
  qtag q == 13 && decide (0 < llen (qjs q)) && isTermC (snd (qdat q)) == 1 &&
    qprem q 0 == pj (qk q) (qD q) (pair 5 (fst (qdat q))) &&
    instC (fst (qdat q)) (snd (qdat q)) == qF q

/-- Rule 14 on codes: ∃-introduction. -/
def rC14 (q : Nat) : Bool :=
  qtag q == 14 && decide (0 < llen (qjs q)) && fst (qF q) == 6 && isTermC (qdat q) == 1 &&
    qprem q 0 == pj (qk q) (qD q) (instC (snd (qF q)) (qdat q))

/-- Rule 15 on codes: ∃-elimination. -/
def rC15 (q : Nat) : Bool :=
  qtag q == 15 && decide (1 < llen (qjs q)) && shiftedC q (snd (qdat q)) &&
    qprem q 0 == pj (qk q) (qD q) (pair 6 (fst (qdat q))) &&
    qprem q 1 == pj (qk q + 1) (lcons (fst (qdat q)) (snd (qdat q))) (shiftC (qF q))

/-- Rule 16 on codes: reflexivity of equality. -/
def rC16 (q : Nat) : Bool :=
  qtag q == 16 && fst (qF q) == 1 && fst (snd (qF q)) == snd (snd (qF q))

/-- Rule 17 on codes: Leibniz's law. -/
def rC17 (q : Nat) : Bool :=
  qtag q == 17 && decide (1 < llen (qjs q)) && isFormulaC (fst (qdat q)) == 1 &&
    isTermC (fst (snd (qdat q))) == 1 &&
    isTermC (snd (snd (qdat q))) == 1 &&
    qprem q 0 == pj (qk q) (qD q) (pair 1 (snd (qdat q))) &&
    qprem q 1 == pj (qk q) (qD q) (instC (fst (qdat q)) (fst (snd (qdat q)))) &&
    instC (fst (qdat q)) (snd (snd (qdat q))) == qF q

/-- The rules of natural deduction from shifted PA, on codes. -/
def ruleC (q : Nat) : Bool :=
  rC0 q || rC1 q || rC2 q || rC3 q || rC4 q || rC5 q || rC6 q || rC7 q || rC8 q || rC9 q || rC10 q || rC11 q || rC12 q || rC13 q || rC14 q || rC15 q || rC16 q || rC17 q

/-- **One step of a PA derivation**, checked on Gödel numbers. -/
def paStep (q : Nat) : Bool := wfC q && ruleC q

/-- The rule system for derivations from (shifted) PA. -/
def paRule (x w js : Nat) : Bool := paStep (pair x (pair w js))

/-- The code of `⊥` is `0`. -/
theorem fcode_bot : fcode bot = 0 := rfl

/-- Codes of compound formulas. -/
theorem fcode_imp (A B : Formula Arith) : fcode (imp A B) = pair 2 (pair (fcode A) (fcode B)) := rfl
/-- Codes of compound formulas. -/
theorem fcode_conj (A B : Formula Arith) : fcode (conj A B) = pair 3 (pair (fcode A) (fcode B)) := rfl
/-- Codes of compound formulas. -/
theorem fcode_disj (A B : Formula Arith) : fcode (disj A B) = pair 4 (pair (fcode A) (fcode B)) := rfl
/-- Codes of compound formulas. -/
theorem fcode_all (A : Formula Arith) : fcode (all A) = pair 5 (fcode A) := rfl
/-- Codes of compound formulas. -/
theorem fcode_ex (A : Formula Arith) : fcode (ex A) = pair 6 (fcode A) := rfl
/-- Codes of compound formulas. -/
theorem fcode_eq (t s : Term Arith) : fcode (eq t s) = pair 1 (pair (tcode t) (tcode s)) := rfl

/-- The code of a negation. -/
theorem fcode_neg (φ : Formula Arith) : fcode (neg φ) = pair 2 (pair (fcode φ) 0) := rfl

/-! ## The rules are computable -/

-- Hide the internals of the code-level operations from unification.
attribute [local irreducible] fsub tsub trename instC shiftC shiftNC succSubC isFormulaC isTermC
  pair fst snd lnth llen histGet ballLt

/-- A tactic for computability of the explicitly written rule tests. -/
macro "pa_tac" : tactic => `(tactic| repeat (first
  | assumption | exact Comp.id | exact Comp.const _ | exact CompB.const _
  | apply CompB.or | apply CompB.and | apply CompB.not | apply CompB.eq | apply CompB.lt
  | apply CompB.ballLt | apply Comp.cond | apply CompB.cond
  | apply Comp.isFormulaC | apply Comp.isTermC | apply Comp.shiftNC | apply Comp.shiftC
  | apply Comp.instC | apply Comp.succSubC
  | apply Comp.judg | apply Comp.lcons' | apply Comp.pair | apply Comp.lnth | apply Comp.llen
  | apply Comp.lhead | apply Comp.ltail | apply Comp.fst | apply Comp.snd
  | apply Comp.succ | apply Comp.add | apply Comp.sub | apply Comp.mul))

/-- `isPAC` is computable. -/
theorem CompB.isPAC {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    CompB fun n => FO.isPAC (f n) (g n) := by
  unfold FO.isPAC indC
  refine CompB.or ?_ ?_
  · simp only [closedAx, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      Bool.or_false]
    pa_tac
  · apply CompB.eq hf
    pa_tac

/-- `shiftedC` is computable. -/
theorem CompB.shiftedC {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    CompB fun n => FO.shiftedC (f n) (g n) := by
  unfold FO.shiftedC
  refine CompB.and (CompB.eq (Comp.llen hg) (Comp.llen (Comp.fst (Comp.snd (Comp.fst hf))))) ?_
  have h₀ : CompB fun p => ballLt (fun r => lnth (fst (fst r)) (snd r) ==
      shiftC (lnth (qD (snd (fst r))) (snd r))) p (llen (qD (snd p))) :=
    CompB.ballLt (by pa_tac) (by pa_tac)
  exact CompB.congr (CompB.comp h₀ (Comp.pair hg hf)) fun n => by simp only [snd_pair]

attribute [local irreducible] isPAC shiftedC indC

/-- Rule 0 is computable. -/
theorem rC0_comp : CompB rC0 := by unfold rC0; (try unfold pj); pa_tac

/-- Rule 1 is computable. -/
theorem rC1_comp : CompB rC1 := by
  unfold rC1
  refine CompB.and (CompB.and (CompB.and (CompB.and ?_ ?_) ?_) ?_) (CompB.isPAC ?_ ?_) <;> pa_tac

/-- Rule 2 is computable. -/
theorem rC2_comp : CompB rC2 := by unfold rC2; (try unfold pj); pa_tac

/-- Rule 3 is computable. -/
theorem rC3_comp : CompB rC3 := by unfold rC3; (try unfold pj); pa_tac

/-- Rule 4 is computable. -/
theorem rC4_comp : CompB rC4 := by unfold rC4; (try unfold pj); pa_tac

/-- Rule 5 is computable. -/
theorem rC5_comp : CompB rC5 := by unfold rC5; (try unfold pj); pa_tac

/-- Rule 6 is computable. -/
theorem rC6_comp : CompB rC6 := by unfold rC6; (try unfold pj); pa_tac

/-- Rule 7 is computable. -/
theorem rC7_comp : CompB rC7 := by unfold rC7; (try unfold pj); pa_tac

/-- Rule 8 is computable. -/
theorem rC8_comp : CompB rC8 := by unfold rC8; (try unfold pj); pa_tac

/-- Rule 9 is computable. -/
theorem rC9_comp : CompB rC9 := by unfold rC9; (try unfold pj); pa_tac

/-- Rule 10 is computable. -/
theorem rC10_comp : CompB rC10 := by unfold rC10; (try unfold pj); pa_tac

/-- Rule 11 is computable. -/
theorem rC11_comp : CompB rC11 := by unfold rC11; (try unfold pj); pa_tac

/-- Rule 12 is computable. -/
theorem rC12_comp : CompB rC12 := by
  unfold rC12 pj
  refine CompB.and (CompB.and (CompB.and (CompB.and ?_ ?_) ?_) (CompB.shiftedC Comp.id ?_)) ?_ <;>
    pa_tac

/-- Rule 13 is computable. -/
theorem rC13_comp : CompB rC13 := by unfold rC13; (try unfold pj); pa_tac

/-- Rule 14 is computable. -/
theorem rC14_comp : CompB rC14 := by unfold rC14; (try unfold pj); pa_tac

/-- Rule 15 is computable. -/
theorem rC15_comp : CompB rC15 := by
  unfold rC15 pj
  refine CompB.and (CompB.and (CompB.and (CompB.and ?_ ?_) (CompB.shiftedC Comp.id ?_)) ?_) ?_ <;>
    pa_tac

/-- Rule 16 is computable. -/
theorem rC16_comp : CompB rC16 := by unfold rC16; (try unfold pj); pa_tac

/-- Rule 17 is computable. -/
theorem rC17_comp : CompB rC17 := by unfold rC17; (try unfold pj); pa_tac

/-- Well-formedness is computable. -/
theorem wfC_comp : CompB wfC := by unfold wfC; pa_tac

/-- **The PA rules are computable.** -/
theorem paStep_comp : CompB paStep := by
  unfold paStep ruleC
  refine CompB.and wfC_comp ?_
  repeat' apply CompB.or
  all_goals first
    | exact rC0_comp | exact rC1_comp | exact rC2_comp | exact rC3_comp | exact rC4_comp
    | exact rC5_comp | exact rC6_comp | exact rC7_comp | exact rC8_comp | exact rC9_comp
    | exact rC10_comp | exact rC11_comp | exact rC12_comp | exact rC13_comp | exact rC14_comp
    | exact rC15_comp | exact rC16_comp | exact rC17_comp

/-- The PA rules in the three-place form required by `Derivations`. -/
theorem paRule_comp : CompB fun n => paRule (fst n) (fst (snd n)) (snd (snd n)) :=
  CompB.congr paStep_comp fun n => by simp [paRule, pair_fst_snd]

end Foundations.Logic.FO
