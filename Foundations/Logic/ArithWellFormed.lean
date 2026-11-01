import Foundations.Logic.ArithCoding

/-!
# Recognising formulas: well-formedness of Gödel numbers

Not every number is the Gödel number of a formula. A proof checker that receives
numbers as input must first make sure that it is looking at genuine syntax — just
as a human reader must recognise a string of symbols as a grammatical formula before
asking whether it is a theorem. This file provides computable tests `isTermC` and
`isFormulaC` (course-of-values recursions over the code: a code is well formed iff
its tag is legal and its immediate parts are well formed), proves them correct, and
sets up the coding of finite lists of formulas (the discharged assumptions of a
natural deduction derivation).
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula Computability

/-! ## Well-formedness -/

/-- One step of the term test (value `1` = "is a term code"). -/
def isTermStep (q : Nat) : Nat :=
  bif fst (cvN q) == 0 then 1
  else bif fst (cvN q) == 1 then (bif snd (cvN q) == 0 then 1 else 0)
  else bif fst (cvN q) == 2 then cvRec q (snd (cvN q))
  else bif fst (cvN q) == 3 || fst (cvN q) == 4 then
    cvRec q (fst (snd (cvN q))) * cvRec q (snd (snd (cvN q)))
  else 0

/-- **Being a term code** (value `1`), decided by course-of-values recursion. -/
def isTermC (n : Nat) : Nat := covRec isTermStep 0 n

/-- One step of the formula test. -/
def isFormulaStep (q : Nat) : Nat :=
  bif fst (cvN q) == 0 then (bif snd (cvN q) == 0 then 1 else 0)
  else bif fst (cvN q) == 1 then isTermC (fst (snd (cvN q))) * isTermC (snd (snd (cvN q)))
  else bif fst (cvN q) == 2 || fst (cvN q) == 3 || fst (cvN q) == 4 then
    cvRec q (fst (snd (cvN q))) * cvRec q (snd (snd (cvN q)))
  else bif fst (cvN q) == 5 || fst (cvN q) == 6 then cvRec q (snd (cvN q))
  else 0

/-- **Being a formula code** (value `1`). -/
def isFormulaC (n : Nat) : Nat := covRec isFormulaStep 0 n

/-- Every number is a pair. -/
theorem eq_pair_fst_snd (n : Nat) : n = pair (fst n) (snd n) := (pair_fst_snd n).symm

/-- Products of numbers are `1` iff both are `1`. -/
theorem mul_eq_one_iff' {a b : Nat} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp_all [Nat.mul_succ, Nat.succ_mul] <;> omega
  · rintro ⟨rfl, rfl⟩; rfl

/-- Unfolding the term test once. -/
theorem isTermC_unfold (n : Nat) :
    isTermC n = isTermStep (pair 0 (pair n (covHist isTermStep 0 n))) := rfl

/-- Unfolding the formula test once. -/
theorem isFormulaC_unfold (n : Nat) :
    isFormulaC n = isFormulaStep (pair 0 (pair n (covHist isFormulaStep 0 n))) := rfl

/-- **The term test is correct.** -/
theorem isTermC_iff (n : Nat) : isTermC n = 1 ↔ ∃ t, tcode t = n := by
  constructor
  · induction n using Nat.strongRecOn with
    | _ n ih =>
      intro h
      obtain ⟨a, b, rfl⟩ : ∃ a b, n = pair a b := ⟨fst n, snd n, (pair_fst_snd n).symm⟩
      rw [isTermC_unfold] at h
      simp only [isTermStep, cvN, cvRec, fst_pair, snd_pair] at h
      by_cases ha0 : a = 0
      · subst ha0; exact ⟨v b, rfl⟩
      by_cases ha1 : a = 1
      · subst ha1
        by_cases hb : b = 0
        · subst hb; exact ⟨zero, rfl⟩
        · simp [hb] at h
      by_cases ha2 : a = 2
      · subst ha2
        simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true] at h
        rw [histGet_covHist _ _ _ _ (lt_pair_of_pos (by omega))] at h
        obtain ⟨t, ht⟩ := ih b (lt_pair_of_pos (by omega)) h
        exact ⟨succ t, by rw [tcode_succ, ht]⟩
      by_cases ha34 : a = 3 ∨ a = 4
      · obtain ⟨b₁, b₂, rfl⟩ : ∃ b₁ b₂, b = pair b₁ b₂ := ⟨fst b, snd b, (pair_fst_snd b).symm⟩
        have hpos : 0 < a := by omega
        have h' : histGet (covHist isTermStep 0 (pair a (pair b₁ b₂))) (pair a (pair b₁ b₂)) b₁ *
            histGet (covHist isTermStep 0 (pair a (pair b₁ b₂))) (pair a (pair b₁ b₂)) b₂ = 1 := by
          have e0 : (a == 0) = false := by simp [ha0]
          have e1 : (a == 1) = false := by simp [ha1]
          have e2 : (a == 2) = false := by simp [ha2]
          have e34 : (a == 3 || a == 4) = true := by simp [ha34]
          simpa [e0, e1, e2, e34] using h
        rw [histGet_covHist _ _ _ _ (fst_lt_tagged hpos),
          histGet_covHist _ _ _ _ (snd_lt_tagged hpos)] at h'
        obtain ⟨h₁, h₂⟩ := mul_eq_one_iff'.1 h'
        obtain ⟨t₁, ht₁⟩ := ih b₁ (fst_lt_tagged hpos) h₁
        obtain ⟨t₂, ht₂⟩ := ih b₂ (snd_lt_tagged hpos) h₂
        rcases ha34 with rfl | rfl
        · exact ⟨add t₁ t₂, by rw [tcode_add, ht₁, ht₂]⟩
        · exact ⟨mul t₁ t₂, by rw [tcode_mul, ht₁, ht₂]⟩
      · have e0 : (a == 0) = false := by simp [ha0]
        have e1 : (a == 1) = false := by simp [ha1]
        have e2 : (a == 2) = false := by simp [ha2]
        have e34 : (a == 3 || a == 4) = false := by simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
        simp [e0, e1, e2, e34] at h
  · rintro ⟨t, rfl⟩
    induction t using Term.arith_induction with
    | hv n =>
        rw [isTermC_unfold]
        simp only [isTermStep, cvN, tcode_var, fst_pair, snd_pair, beq_self_eq_true, Bool.cond_true]
    | hz =>
        have key : ∀ b, isTermC (pair 1 b) = (bif b == 0 then 1 else 0) := by
          intro b; rw [isTermC_unfold]
          simp only [isTermStep, cvN, fst_pair, snd_pair, Nat.reduceBEq, Bool.cond_false, Bool.cond_true]
        rw [tcode_zero, key]; rfl
    | hs t ih =>
        rw [isTermC_unfold]
        simp only [isTermStep, cvN, cvRec, tcode_succ, fst_pair, snd_pair]
        simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true]
        rw [histGet_covHist _ _ _ _ (lt_pair_of_pos (by omega))]; exact ih
    | ha t s iht ihs =>
        rw [isTermC_unfold]
        simp only [isTermStep, cvN, cvRec, tcode_add, fst_pair, snd_pair]
        simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or]
        rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
          histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
        exact mul_eq_one_iff'.2 ⟨iht, ihs⟩
    | hm t s iht ihs =>
        rw [isTermC_unfold]
        simp only [isTermStep, cvN, cvRec, tcode_mul, fst_pair, snd_pair]
        simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or,
          Bool.or_true]
        rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
          histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
        exact mul_eq_one_iff'.2 ⟨iht, ihs⟩

/-- **The formula test is correct.** -/
theorem isFormulaC_iff (n : Nat) : isFormulaC n = 1 ↔ ∃ φ, fcode φ = n := by
  constructor
  · induction n using Nat.strongRecOn with
    | _ n ih =>
      intro h
      obtain ⟨a, b, rfl⟩ : ∃ a b, n = pair a b := ⟨fst n, snd n, (pair_fst_snd n).symm⟩
      rw [isFormulaC_unfold] at h
      simp only [isFormulaStep, cvN, cvRec, fst_pair, snd_pair] at h
      by_cases ha0 : a = 0
      · subst ha0
        by_cases hb : b = 0
        · subst hb; exact ⟨bot, rfl⟩
        · simp [hb] at h
      have e0 : (a == 0) = false := by simp [ha0]
      by_cases ha1 : a = 1
      · subst ha1
        obtain ⟨b₁, b₂, rfl⟩ : ∃ b₁ b₂, b = pair b₁ b₂ := ⟨fst b, snd b, (pair_fst_snd b).symm⟩
        simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, fst_pair, snd_pair] at h
        obtain ⟨h₁, h₂⟩ := mul_eq_one_iff'.1 h
        obtain ⟨t₁, rfl⟩ := (isTermC_iff b₁).1 h₁
        obtain ⟨t₂, rfl⟩ := (isTermC_iff b₂).1 h₂
        exact ⟨eq t₁ t₂, rfl⟩
      have e1 : (a == 1) = false := by simp [ha1]
      by_cases ha234 : a = 2 ∨ a = 3 ∨ a = 4
      · obtain ⟨b₁, b₂, rfl⟩ : ∃ b₁ b₂, b = pair b₁ b₂ := ⟨fst b, snd b, (pair_fst_snd b).symm⟩
        have hpos : 0 < a := by omega
        have e234 : (a == 2 || a == 3 || a == 4) = true := by simp; omega
        have h' : histGet (covHist isFormulaStep 0 (pair a (pair b₁ b₂))) (pair a (pair b₁ b₂)) b₁ *
            histGet (covHist isFormulaStep 0 (pair a (pair b₁ b₂))) (pair a (pair b₁ b₂)) b₂ = 1 := by
          simpa [e0, e1, e234] using h
        rw [histGet_covHist _ _ _ _ (fst_lt_tagged hpos),
          histGet_covHist _ _ _ _ (snd_lt_tagged hpos)] at h'
        obtain ⟨h₁, h₂⟩ := mul_eq_one_iff'.1 h'
        obtain ⟨φ₁, hφ₁⟩ := ih b₁ (fst_lt_tagged hpos) h₁
        obtain ⟨φ₂, hφ₂⟩ := ih b₂ (snd_lt_tagged hpos) h₂
        rcases ha234 with rfl | rfl | rfl
        · exact ⟨imp φ₁ φ₂, by simp only [fcode, hφ₁, hφ₂]⟩
        · exact ⟨conj φ₁ φ₂, by simp only [fcode, hφ₁, hφ₂]⟩
        · exact ⟨disj φ₁ φ₂, by simp only [fcode, hφ₁, hφ₂]⟩
      have e234 : (a == 2 || a == 3 || a == 4) = false := by simp; omega
      by_cases ha56 : a = 5 ∨ a = 6
      · have hpos : 0 < a := by omega
        have e56 : (a == 5 || a == 6) = true := by simp; omega
        have h' : histGet (covHist isFormulaStep 0 (pair a b)) (pair a b) b = 1 := by
          simpa [e0, e1, e234, e56] using h
        rw [histGet_covHist _ _ _ _ (lt_pair_of_pos hpos)] at h'
        obtain ⟨φ, hφ⟩ := ih b (lt_pair_of_pos hpos) h'
        rcases ha56 with rfl | rfl
        · exact ⟨all φ, by simp only [fcode, hφ]⟩
        · exact ⟨ex φ, by simp only [fcode, hφ]⟩
      · have e56 : (a == 5 || a == 6) = false := by simp; omega
        simp [e0, e1, e234, e56] at h
  · rintro ⟨φ, rfl⟩
    induction φ using Formula.arith_induction with
    | hb =>
        have key : ∀ b, isFormulaC (pair 0 b) = (bif b == 0 then 1 else 0) := by
          intro b; rw [isFormulaC_unfold]
          simp only [isFormulaStep, cvN, fst_pair, snd_pair, Nat.reduceBEq, Bool.cond_false,
            Bool.cond_true]
        show isFormulaC (pair 0 0) = 1
        rw [key]; rfl
    | he t s =>
        rw [isFormulaC_unfold]
        simp only [isFormulaStep, cvN, fcode, fst_pair, snd_pair, Nat.reduceBEq, Bool.cond_false,
          Bool.cond_true]
        exact mul_eq_one_iff'.2 ⟨(isTermC_iff _).2 ⟨t, rfl⟩, (isTermC_iff _).2 ⟨s, rfl⟩⟩
    | hi φ ψ ih₁ ih₂ =>
        rw [isFormulaC_unfold]
        simp only [isFormulaStep, cvN, cvRec, fcode, fst_pair, snd_pair, Nat.reduceBEq,
          Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or]
        rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
          histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
        exact mul_eq_one_iff'.2 ⟨ih₁, ih₂⟩
    | hc φ ψ ih₁ ih₂ =>
        rw [isFormulaC_unfold]
        simp only [isFormulaStep, cvN, cvRec, fcode, fst_pair, snd_pair, Nat.reduceBEq,
          Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or]
        rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
          histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
        exact mul_eq_one_iff'.2 ⟨ih₁, ih₂⟩
    | hd φ ψ ih₁ ih₂ =>
        rw [isFormulaC_unfold]
        simp only [isFormulaStep, cvN, cvRec, fcode, fst_pair, snd_pair, Nat.reduceBEq,
          Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or]
        rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
          histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
        exact mul_eq_one_iff'.2 ⟨ih₁, ih₂⟩
    | ha φ ih =>
        rw [isFormulaC_unfold]
        simp only [isFormulaStep, cvN, cvRec, fcode, fst_pair, snd_pair, Nat.reduceBEq,
          Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or]
        rw [histGet_covHist _ _ _ _ (lt_pair_of_pos (by omega))]
        exact ih
    | hx φ ih =>
        rw [isFormulaC_unfold]
        simp only [isFormulaStep, cvN, cvRec, fcode, fst_pair, snd_pair, Nat.reduceBEq,
          Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or]
        rw [histGet_covHist _ _ _ _ (lt_pair_of_pos (by omega))]
        exact ih

/-- The term test is computable. -/
theorem Comp.isTermC {f : Nat → Nat} (hf : Comp f) : Comp fun n => FO.isTermC (f n) := by
  have hs : Comp isTermStep := by unfold isTermStep; comp_tac
  exact Comp.congr (Comp.comp (Comp.covRec hs) (Comp.pair (Comp.const 0) hf)) fun n => by
    simp [FO.isTermC]

/-- The formula test is computable. -/
theorem Comp.isFormulaC {f : Nat → Nat} (hf : Comp f) : Comp fun n => FO.isFormulaC (f n) := by
  have hs : Comp isFormulaStep := by
    unfold isFormulaStep
    refine Comp.cond ?_ ?_ (Comp.cond ?_ (Comp.mul (Comp.isTermC ?_) (Comp.isTermC ?_)) ?_) <;> comp_tac
  exact Comp.congr (Comp.comp (Comp.covRec hs) (Comp.pair (Comp.const 0) hf)) fun n => by
    simp [FO.isFormulaC]

/-! ## Codes of lists of formulas -/

/-- The code of a list of formulas (a context). -/
def ccode (Δ : List (Formula Arith)) : Nat := encList (Δ.map fcode)

/-- Contexts with equal codes are equal. -/
theorem ccode_inj {Δ Δ' : List (Formula Arith)} (h : ccode Δ = ccode Δ') : Δ = Δ' := by
  have := encList_inj h
  induction Δ generalizing Δ' with
  | nil => cases Δ' <;> simp_all
  | cons φ Δ ih =>
      cases Δ' with
      | nil => simp at this
      | cons ψ Δ' =>
          simp only [List.map_cons, List.cons.injEq] at this
          rw [fcode_inj this.1, ih (by simp [ccode, this.2]) this.2]

/-- Length of a coded context. -/
theorem llen_ccode (Δ : List (Formula Arith)) : llen (ccode Δ) = Δ.length := by
  simp [ccode, llen_encList]

/-- Entries of a coded context. -/
theorem lnth_ccode (Δ : List (Formula Arith)) (i : Nat) (h : i < Δ.length) :
    lnth (ccode Δ) i = fcode Δ[i] := by
  rw [ccode, lnth_encList, getD_eq_getElem' _ _ (by simpa using h)]; simp

/-- Cons on coded contexts. -/
theorem lcons_ccode (φ : Formula Arith) (Δ : List (Formula Arith)) :
    lcons (fcode φ) (ccode Δ) = ccode (φ :: Δ) := rfl

/-- **Decoding contexts.** A number all of whose entries are formula codes is the code
of a context. -/
theorem exists_ccode (c : Nat) (h : ∀ i, i < llen c → isFormulaC (lnth c i) = 1) :
    ∃ Δ : List (Formula Arith), ccode Δ = c := by
  obtain ⟨l, rfl⟩ : ∃ l, encList l = c := ⟨_, encList_decList c⟩
  rw [llen_encList] at h
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
      obtain ⟨φ, hφ⟩ := (isFormulaC_iff x).1 (by simpa [lnth] using h 0 (by simp))
      obtain ⟨Δ, hΔ⟩ := ih fun i hi => by
        have := h (i + 1) (by simp; omega)
        simpa [lnth] using this
      refine ⟨φ :: Δ, ?_⟩
      simp only [ccode, List.map_cons] at hΔ ⊢
      show pair (fcode φ) (encList (Δ.map fcode)) + 1 = pair x (encList l) + 1
      rw [hφ, hΔ]

/-- Mapping a substitution over a coded context, entrywise. -/
theorem ccode_map_shift (Δ : List (Formula Arith)) (c : Nat)
    (hlen : llen c = Δ.length) (h : ∀ i, i < Δ.length → lnth c i = shiftC (lnth (ccode Δ) i)) :
    c = ccode (Δ.map Formula.shift) := by
  obtain ⟨l, rfl⟩ : ∃ l, encList l = c := ⟨_, encList_decList c⟩
  rw [llen_encList] at hlen
  simp only [ccode]
  congr 1
  apply List.ext_getElem (by simp [hlen])
  intro i h₁ h₂
  have := h i (by omega)
  rw [lnth_encList, getD_eq_getElem' _ _ h₁, lnth_ccode _ _ (by omega), shiftC_fcode] at this
  simp [this]

end Foundations.Logic.FO
