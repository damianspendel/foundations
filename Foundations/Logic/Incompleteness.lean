import Foundations.Logic.PAProofs
import Foundations.Logic.Definability
import Foundations.Logic.Undecidability

/-!
# Gödel's first incompleteness theorem for Peano arithmetic

We can now assemble the theorem that ended Hilbert's hope of a complete and
mechanical foundation for arithmetic (Gödel, *Über formal unentscheidbare Sätze der
Principia Mathematica und verwandter Systeme I*, 1931):

> **There is a sentence of arithmetic which is true in `ℕ` but which Peano
> arithmetic can neither prove nor refute.**

We follow the route through computability that Turing, Kleene and Post made
standard, which needs only that PA is *sound* (its theorems are true in `ℕ`), not
merely consistent:

1. **Arithmetic can express non-halting.** By `Definability`, for every code `c` and
   input `x` there is a sentence `nonHaltsF c x` of arithmetic, true in `ℕ` exactly
   when `c` does not halt on `x` (via the universal code and Gödel's β-function).
2. **PA's theorems are computably enumerable.** By `PAProofs`, a code halts on
   `⌜φ⌝` exactly when `PA ⊢ φ`. The Gödel number of `nonHaltsF c x` is a computable
   function of `⌜c⌝` and `x` (this file), so some code `q` halts on `(⌜c⌝, x)` exactly
   when PA proves "`c` does not halt on `x`".
3. **PA is sound** (`PA_sound`): whatever it proves is true in the standard model.
4. **The diagonal argument** (`Undecidability.incompleteness`): for the code
   `g = godelCode q` — "search for a PA-proof that I do not halt on my own number" —
   PA cannot prove that `g` does not halt on `⌜g⌝`: if it did, the search would
   succeed, so `g` *would* halt, and PA would have proved a falsehood. Hence `g`
   does not halt, the sentence `nonHaltsF g ⌜g⌝` is **true**, and it is **not
   provable**; its negation is false, hence (by soundness) not provable either.

The Gödel sentence obtained is, in substance, "I am not provable": `g` halts on its
own number iff PA proves that it does not.

*What is not done here.* Gödel's original theorem assumes only consistency
(ω-consistency, improved by Rosser to plain consistency) instead of soundness; that
version requires the formulas of `Definability` to be *provably* correct in PA (or in
Robinson's `Q`), i.e. representability, together with the diagonal lemma, and is not
formalised; nor is the second incompleteness theorem.
-/

namespace Foundations.Logic.FO

open Arith Formula Computability

/-! ## Gödel numbers of the non-halting sentences, computably -/

/-- The Gödel number of the numeral `n̄`. -/
def ncode (n : Nat) : Nat := tcode (numeral n)

/-- Numerals have computable Gödel numbers. -/
theorem Comp.ncode : Comp FO.ncode := by
  have := Comp.natRec (b := fun _ => pair 1 0) (s := fun q => pair 2 (snd (snd q)))
    (Comp.const _) (Comp.pair (Comp.const 2) (Comp.snd (Comp.snd Comp.id))) Comp.id
  have key : ∀ p k, natRec (fun _ => pair 1 0) (fun q => pair 2 (snd (snd q))) p k = FO.ncode k := by
    intro p k
    induction k with
    | zero => rfl
    | succ k ih => simp only [natRec, snd_pair, ih]; rfl
  exact Comp.congr this fun n => key n n

/-- The Gödel number of the non-halting sentence for (code number) `e` and input `x`. -/
noncomputable def gcode (e x : Nat) : Nat :=
  pair 2 (pair (instC (instC (fcode haltsF) (ncode e)) (ncode x)) 0)

/-- `gcode` computes the Gödel numbers of the non-halting sentences. -/
theorem gcode_spec (c : Code) (x : Nat) : gcode (encode c) x = fcode (nonHaltsF c x) := by
  simp only [gcode, ncode, instC_fcode, nonHaltsF]; rfl

/-- `gcode` is computable. -/
theorem gcode_comp : Comp fun p => gcode (fst p) (snd p) :=
  Comp.pair (Comp.const 2) (Comp.pair (Comp.instC (Comp.instC (Comp.const _)
    (Comp.comp Comp.ncode (Comp.fst Comp.id))) (Comp.comp Comp.ncode (Comp.snd Comp.id)))
    (Comp.const 0))

/-- **Provability of non-halting is computably enumerable.** Some code halts on
`(⌜c⌝, x)` exactly when PA proves the sentence "`c` does not halt on `x`". -/
theorem provable_nonHalts_ce :
    ∃ q : Code, ∀ (c : Code) (x : Nat), Halts q [encode c, x] ↔ PA ⊢₁ nonHaltsF c x := by
  obtain ⟨cPA, hPA⟩ := PA_theorems_ce
  obtain ⟨cg, hcg⟩ := gcode_comp
  let cG : Code := .comp cg (vec1 (pairOf (.proj 0) (.proj 1)))
  have hG : ∀ e x, Eval cG [e, x] (gcode e x) := fun e x => by
    have := eval_comp1 (eval_pairOf (xs := [e, x]) (.proj (i := 0)) (.proj (i := 1))) (hcg (pair e x))
    simpa using this
  refine ⟨.comp cPA (vec1 cG), fun c x => ?_⟩
  rw [← hPA, ← gcode_spec]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨v, hv, hc⟩ := eval_comp1_inv hm
    rw [Eval.det hv (hG _ _)] at hc
    exact ⟨m, hc⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, eval_comp1 (hG _ _) hm⟩

/-- **PA proves only true non-halting statements** (by its soundness in `ℕ`). -/
theorem nonHalts_sound (c : Code) (x : Nat) (h : PA ⊢₁ nonHaltsF c x) : ¬ Halts c [x] :=
  (sat_nonHaltsF c x (fun _ => 0)).1 (PA_sound h _)

/-! ## The theorem -/

/-- The Gödel code: on input `e` it searches for a PA-proof that program `e` does not
halt on `e`. -/
noncomputable def godelProgram : Code := godelCode provable_nonHalts_ce.choose

/-- **The Gödel sentence**: "the Gödel program does not halt on its own number" —
which holds iff PA does not prove it. -/
noncomputable def godelSentence : Formula Arith :=
  nonHaltsF godelProgram (encode godelProgram)

/-- The Gödel program indeed does not halt on its own number, and PA cannot prove this. -/
theorem godelProgram_spec :
    ¬ Halts godelProgram [encode godelProgram] ∧ ¬ (PA ⊢₁ godelSentence) :=
  incompleteness (fun c x => PA ⊢₁ nonHaltsF c x) nonHalts_sound
    provable_nonHalts_ce.choose_spec

/-- **Gödel's first incompleteness theorem** (for PA, assuming its soundness, which we
proved relative to Lean in `PeanoArithmetic`). There is a *sentence* `σ` of arithmetic
(no free variables) which is true in the standard model `ℕ`, yet PA proves neither
`σ` nor its negation `¬σ`. -/
theorem godel_first_incompleteness :
    ∃ σ : Formula Arith, IsSentence σ ∧ (∀ e : Nat → Nat, Sat stdModel e σ) ∧
      ¬ (PA ⊢₁ σ) ∧ ¬ (PA ⊢₁ neg σ) := by
  obtain ⟨hhalt, hnp⟩ := godelProgram_spec
  have htrue : ∀ e : Nat → Nat, Sat stdModel e godelSentence :=
    fun e => (sat_nonHaltsF _ _ e).2 hhalt
  refine ⟨godelSentence, nonHaltsF_sentence _ _, htrue, hnp, fun h => ?_⟩
  exact (PA_sound h (fun _ => 0)) (htrue _)

/-- **PA is incomplete**: it does not decide every formula. -/
theorem PA_incomplete : ¬ ∀ σ : Formula Arith, (PA ⊢₁ σ) ∨ (PA ⊢₁ neg σ) := by
  intro h
  obtain ⟨σ, -, -, h₁, h₂⟩ := godel_first_incompleteness
  rcases h σ with h' | h'
  · exact h₁ h'
  · exact h₂ h'

/-- **Arithmetical truth is not computably enumerable** (Tarski–Gödel, computational
form): no code halts exactly on the Gödel numbers of the formulas true in `ℕ`.
Otherwise the true non-halting sentences could be enumerated, and the argument above
would apply to this "theory of true arithmetic" in place of PA. -/
theorem truth_not_ce : ¬ ∃ c : Code, ∀ φ : Formula Arith,
    Halts c [fcode φ] ↔ ∀ e : Nat → Nat, Sat stdModel e φ := by
  rintro ⟨cT, hT⟩
  obtain ⟨cg, hcg⟩ := gcode_comp
  let cG : Code := .comp cg (vec1 (pairOf (.proj 0) (.proj 1)))
  have hG : ∀ e x, Eval cG [e, x] (gcode e x) := fun e x => by
    have := eval_comp1 (eval_pairOf (xs := [e, x]) (.proj (i := 0)) (.proj (i := 1))) (hcg (pair e x))
    simpa using this
  -- the "theory of truth" is sound and complete for non-halting statements
  have hq : ∀ (c : Code) (x : Nat), Halts (.comp cT (vec1 cG)) [encode c, x] ↔
      ∀ e : Nat → Nat, Sat stdModel e (nonHaltsF c x) := by
    intro c x
    rw [← hT, ← gcode_spec]
    constructor
    · rintro ⟨m, hm⟩
      obtain ⟨v, hv, hc⟩ := eval_comp1_inv hm
      rw [Eval.det hv (hG _ _)] at hc
      exact ⟨m, hc⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, eval_comp1 (hG _ _) hm⟩
  refine no_complete_sound_ce_system (fun c x => ∀ e : Nat → Nat, Sat stdModel e (nonHaltsF c x))
    (fun c x h => (sat_nonHaltsF c x (fun _ => 0)).1 (h _)) ⟨_, hq⟩ ?_
  intro c x h e
  exact (sat_nonHaltsF c x e).2 h

end Foundations.Logic.FO
