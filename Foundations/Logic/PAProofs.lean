import Foundations.Logic.PARules

/-!
# The theorems of Peano arithmetic are computably enumerable

We prove that the rule system `paRule` of the previous file is faithful to natural
deduction: a judgement `⟨k, ⟨⌜Δ⌝, ⌜φ⌝⟩⟩` is derivable in it exactly when
`shiftPA k ∪ Δ ⊢₁ φ`. *Soundness* (derivable judgements are correct) is proved by
induction on rule-system derivations: the well-formedness check decodes the
conclusion, and the Gödel numbering's injectivity identifies the premises with the
formulas required by the corresponding rule of `⊢₁`. *Completeness* is proved by
induction on `⊢₁`-derivations, supplying for each rule the witness data and checking
the computable test. With `k = 0` and `Δ = []` this is derivability from PA, and the
general machinery of `Derivations` turns the rule system into a code that halts
exactly on the Gödel numbers of PA's theorems: **the theorems of PA are computably
enumerable**.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula Theory Computability

-- Hide the internals of the code-level operations from unification.
attribute [local irreducible] fsub tsub trename instC shiftC shiftNC succSubC isFormulaC isTermC
  pair fst snd lnth llen histGet ballLt isPAC shiftedC indC

/-! ## Soundness: derivable judgements are derivations from PA -/

/-- Shape of a formula with a given tag. -/
theorem fcode_tag_imp {Φ : Formula Arith} (h : fst (fcode Φ) = 2) : ∃ A B, Φ = imp A B := by
  cases Φ using Formula.arith_cases <;> simp [fcode] at h ⊢

/-- Shape of a formula with a given tag. -/
theorem fcode_tag_conj {Φ : Formula Arith} (h : fst (fcode Φ) = 3) : ∃ A B, Φ = conj A B := by
  cases Φ using Formula.arith_cases <;> simp [fcode] at h ⊢

/-- Shape of a formula with a given tag. -/
theorem fcode_tag_disj {Φ : Formula Arith} (h : fst (fcode Φ) = 4) : ∃ A B, Φ = disj A B := by
  cases Φ using Formula.arith_cases <;> simp [fcode] at h ⊢

/-- Shape of a formula with a given tag. -/
theorem fcode_tag_all {Φ : Formula Arith} (h : fst (fcode Φ) = 5) : ∃ A, Φ = all A := by
  cases Φ using Formula.arith_cases <;> simp [fcode] at h ⊢

/-- Shape of a formula with a given tag. -/
theorem fcode_tag_ex {Φ : Formula Arith} (h : fst (fcode Φ) = 6) : ∃ A, Φ = ex A := by
  cases Φ using Formula.arith_cases <;> simp [fcode] at h ⊢

/-- Shape of a formula with a given tag. -/
theorem fcode_tag_eq {Φ : Formula Arith} (h : fst (fcode Φ) = 1) : ∃ t s, Φ = eq t s := by
  cases Φ using Formula.arith_cases <;> simp [fcode] at h ⊢

/-- Judgements are injective in their components. -/
theorem pj_inj {k Δ φ k' Δ' φ' : Nat} (h : pj k Δ φ = pj k' Δ' φ') : k = k' ∧ Δ = Δ' ∧ φ = φ' := by
  simp only [pj, pair_eq_pair] at h; exact ⟨h.1, h.2.1, h.2.2⟩

/-- The rule test, as a flat disjunction. -/
theorem ruleC_iff (q : Nat) : ruleC q = true ↔
    rC0 q = true ∨ rC1 q = true ∨ rC2 q = true ∨ rC3 q = true ∨ rC4 q = true ∨ rC5 q = true ∨
    rC6 q = true ∨ rC7 q = true ∨ rC8 q = true ∨ rC9 q = true ∨ rC10 q = true ∨ rC11 q = true ∨
    rC12 q = true ∨ rC13 q = true ∨ rC14 q = true ∨ rC15 q = true ∨ rC16 q = true ∨
    rC17 q = true := by
  simp only [ruleC, Bool.or_eq_true, or_assoc]

/-- A term code passing the term test decodes to a term. -/
theorem tcode_of_isTermC {n : Nat} (h : isTermC n = 1) : ∃ t, tcode t = n := (isTermC_iff n).1 h

/-- The shifted-context test, decoded. -/
theorem shiftedC_iff {q c : Nat} {Δ : List (Formula Arith)} (hΔ : qD q = ccode Δ) :
    shiftedC q c = true ↔ c = ccode (Δ.map Formula.shift) := by
  simp only [shiftedC, Bool.and_eq_true, beq_iff_eq, ballLt_iff, fst_pair, snd_pair, hΔ,
    llen_ccode]
  constructor
  · rintro ⟨hlen, h⟩
    exact ccode_map_shift Δ c hlen fun i hi => h i hi
  · rintro rfl
    refine ⟨by simp [llen_ccode], fun i hi => ?_⟩
    rw [lnth_ccode _ _ (by simpa using hi), lnth_ccode _ _ hi]; simp [shiftC_fcode]

/-- Shifting `k` times commutes into `shiftN`. -/
theorem shiftN_succ (k : Nat) (ψ : Formula Arith) : shiftN (k + 1) ψ = (shiftN k ψ).shift := rfl

/-- **Soundness of the rule system.** Every derivable judgement is the code of a
correct derivability statement `Ctx k Δ ⊢₁ φ`. -/
theorem proves_of_derivable {x : Nat} (h : Derivable paRule x) :
    ∃ k Δ φ, x = pj k (ccode Δ) (fcode φ) ∧ Ctx k Δ ⊢₁ φ := by
  induction h with
  | intro x w l hl hstep ih =>
    -- decode the conclusion
    obtain ⟨k, D, F, rfl⟩ : ∃ k D F, x = pj k D F :=
      ⟨fst x, fst (snd x), snd (snd x), by simp [pj, pair_fst_snd]⟩
    simp only [paRule, paStep, Bool.and_eq_true] at hstep
    obtain ⟨hwf, hrule⟩ := hstep
    simp only [wfC, Bool.and_eq_true, beq_iff_eq, ballLt_iff, qF, qD, pj, fst_pair, snd_pair] at hwf
    obtain ⟨Φ, rfl⟩ := (isFormulaC_iff F).1 hwf.1
    obtain ⟨Δ, rfl⟩ := exists_ccode D fun i hi => by simpa using hwf.2 i hi
    refine ⟨k, Δ, Φ, rfl, ?_⟩
    -- premises
    have prem : ∀ i, i < llen (encList l) → ∀ K D F, lnth (encList l) i = pj K D F →
        ∃ Δ' φ', D = ccode Δ' ∧ F = fcode φ' ∧ Ctx K Δ' ⊢₁ φ' := by
      intro i hi K D F he
      rw [llen_encList] at hi
      obtain ⟨k', Δ', φ', e, hd⟩ := ih _ (List.getElem_mem hi)
      rw [lnth_encList, getD_eq_getElem' _ _ hi, e] at he
      obtain ⟨rfl, rfl, rfl⟩ := pj_inj he
      exact ⟨Δ', φ', rfl, rfl, hd⟩
    rw [ruleC_iff] at hrule
    simp only [rC0, rC1, rC2, rC3, rC4, rC5, rC6, rC7, rC8, rC9, rC10, rC11, rC12, rC13, rC14,
      rC15, rC16, rC17, qtag, qdat, qjs, qprem, qk, qD, qF, pj, fst_pair, snd_pair,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrule
    rcases hrule with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · -- assumption
      obtain ⟨⟨-, hi⟩, he⟩ := h
      rw [llen_ccode] at hi
      rw [lnth_ccode _ _ hi] at he
      exact Proves.hyp (Or.inr (fcode_inj he ▸ List.getElem_mem hi))
    · -- axiom
      obtain ⟨⟨⟨⟨-, h₁⟩, h₂⟩, h₃⟩, h₄⟩ := h
      obtain ⟨ψ, hψ⟩ := (isFormulaC_iff _).1 h₁
      obtain ⟨χ, hχ⟩ := (isFormulaC_iff _).1 h₂
      rw [← hψ, shiftNC_fcode] at h₃
      rw [← hψ, ← hχ, isPAC_iff] at h₄
      exact Proves.hyp (Or.inl ⟨ψ, (PA_iff ψ).2 (h₄.imp id fun e => ⟨χ, e⟩), (fcode_inj h₃).symm⟩)
    · -- →I
      obtain ⟨⟨⟨-, hl⟩, ht⟩, hp⟩ := h
      obtain ⟨A, B, rfl⟩ := fcode_tag_imp ht
      simp only [fcode, fst_pair, snd_pair, lcons_ccode] at hp
      obtain ⟨Δ', φ', e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      rw [← ccode_inj e₁, ← fcode_inj e₂] at hd
      exact Proves.impI (hd.weaken (ctx_cons_sub k A Δ))
    · -- →E
      obtain ⟨⟨⟨-, hl⟩, hp₀⟩, hp₁⟩ := h
      obtain ⟨Δ₁, A, e₁, e₂, hd₁⟩ := prem 1 hl _ _ _ hp₁
      rw [e₂] at hp₀
      obtain ⟨Δ₀, C, e₃, e₄, hd₀⟩ := prem 0 (by omega) _ _ _ hp₀
      rw [← ccode_inj e₁] at hd₁
      rw [← fcode_imp] at e₄
      rw [← ccode_inj e₃, ← fcode_inj e₄] at hd₀
      exact Proves.impE hd₀ hd₁
    · -- ∧I
      obtain ⟨⟨⟨⟨-, hl⟩, ht⟩, hp₀⟩, hp₁⟩ := h
      obtain ⟨A, B, rfl⟩ := fcode_tag_conj ht
      simp only [fcode, fst_pair, snd_pair] at hp₀ hp₁
      obtain ⟨Δ₀, A', e₁, e₂, hd₀⟩ := prem 0 (by omega) _ _ _ hp₀
      obtain ⟨Δ₁, B', e₃, e₄, hd₁⟩ := prem 1 hl _ _ _ hp₁
      rw [← ccode_inj e₁, ← fcode_inj e₂] at hd₀
      rw [← ccode_inj e₃, ← fcode_inj e₄] at hd₁
      exact Proves.conjI hd₀ hd₁
    · -- ∧E₁
      obtain ⟨⟨-, hl⟩, hp⟩ := h
      obtain ⟨Δ₀, C, e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      obtain ⟨A, B, rfl⟩ := fcode_tag_conj (by rw [← e₂]; simp : fst (fcode C) = 3)
      simp only [fcode, pair_eq_pair] at e₂
      rw [← ccode_inj e₁, ← fcode_inj e₂.2.1] at hd
      exact Proves.conjE₁ hd
    · -- ∧E₂
      obtain ⟨⟨-, hl⟩, hp⟩ := h
      obtain ⟨Δ₀, C, e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      obtain ⟨A, B, rfl⟩ := fcode_tag_conj (by rw [← e₂]; simp : fst (fcode C) = 3)
      simp only [fcode, pair_eq_pair] at e₂
      rw [← ccode_inj e₁, ← fcode_inj e₂.2.2] at hd
      exact Proves.conjE₂ hd
    · -- ∨I₁
      obtain ⟨⟨⟨-, hl⟩, ht⟩, hp⟩ := h
      obtain ⟨A, B, rfl⟩ := fcode_tag_disj ht
      simp only [fcode, fst_pair, snd_pair] at hp
      obtain ⟨Δ₀, A', e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      rw [← ccode_inj e₁, ← fcode_inj e₂] at hd
      exact Proves.disjI₁ hd
    · -- ∨I₂
      obtain ⟨⟨⟨-, hl⟩, ht⟩, hp⟩ := h
      obtain ⟨A, B, rfl⟩ := fcode_tag_disj ht
      simp only [fcode, fst_pair, snd_pair] at hp
      obtain ⟨Δ₀, B', e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      rw [← ccode_inj e₁, ← fcode_inj e₂] at hd
      exact Proves.disjI₂ hd
    · -- ∨E
      obtain ⟨⟨⟨⟨-, hl⟩, hp₀⟩, hp₁⟩, hp₂⟩ := h
      obtain ⟨Δ₀, C, e₁, e₂, hd₀⟩ := prem 0 (by omega) _ _ _ hp₀
      obtain ⟨A, B, rfl⟩ := fcode_tag_disj (by rw [← e₂]; simp : fst (fcode C) = 4)
      simp only [fcode, pair_eq_pair] at e₂
      obtain ⟨-, e₂⟩ := e₂
      rw [e₂] at hp₁ hp₂
      simp only [fst_pair, snd_pair, lcons_ccode] at hp₁ hp₂
      obtain ⟨Δ₁, φ₁, e₃, e₄, hd₁⟩ := prem 1 (by omega) _ _ _ hp₁
      obtain ⟨Δ₂, φ₂, e₅, e₆, hd₂⟩ := prem 2 hl _ _ _ hp₂
      rw [← ccode_inj e₁] at hd₀
      rw [← ccode_inj e₃, ← fcode_inj e₄] at hd₁
      rw [← ccode_inj e₅, ← fcode_inj e₆] at hd₂
      exact Proves.disjE hd₀ (hd₁.weaken (ctx_cons_sub k A Δ)) (hd₂.weaken (ctx_cons_sub k B Δ))
    · -- ⊥E
      obtain ⟨⟨-, hl⟩, hp⟩ := h
      obtain ⟨Δ₀, C, e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      rw [← ccode_inj e₁, ← fcode_inj (e₂.symm.trans fcode_bot.symm).symm] at hd
      exact Proves.botE hd
    · -- RAA
      obtain ⟨⟨-, hl⟩, hp⟩ := h
      rw [← fcode_neg, lcons_ccode] at hp
      obtain ⟨Δ₀, C, e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      rw [← ccode_inj e₁, ← fcode_inj (e₂.symm.trans fcode_bot.symm).symm] at hd
      exact Proves.raa (hd.weaken (ctx_cons_sub k _ Δ))
    · -- ∀I
      obtain ⟨⟨⟨⟨-, hl⟩, ht⟩, hs⟩, hp⟩ := h
      obtain ⟨A, rfl⟩ := fcode_tag_all ht
      have hs := (shiftedC_iff (Δ := Δ) (by simp only [qD, fst_pair, snd_pair])).1 hs
      rw [hs] at hp
      simp only [fcode, snd_pair] at hp
      obtain ⟨Δ₀, A', e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      rw [← ccode_inj e₁, ← fcode_inj e₂] at hd
      exact Proves.allI (hd.weaken (ctx_shift_sub k Δ))
    · -- ∀E
      obtain ⟨⟨⟨⟨-, hl⟩, ht⟩, hp⟩, hi⟩ := h
      obtain ⟨T, hT⟩ := tcode_of_isTermC ht
      obtain ⟨Δ₀, C, e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      obtain ⟨A, rfl⟩ := fcode_tag_all (by rw [← e₂]; simp : fst (fcode C) = 5)
      simp only [fcode, pair_eq_pair] at e₂
      rw [e₂.2, ← hT, instC_fcode] at hi
      rw [← ccode_inj e₁] at hd
      rw [← fcode_inj hi]
      exact Proves.allE T hd
    · -- ∃I
      obtain ⟨⟨⟨⟨-, hl⟩, ht⟩, hT⟩, hp⟩ := h
      obtain ⟨A, rfl⟩ := fcode_tag_ex ht
      obtain ⟨T, hT'⟩ := tcode_of_isTermC hT
      rw [← hT'] at hp
      simp only [fcode, snd_pair, instC_fcode] at hp
      obtain ⟨Δ₀, C, e₁, e₂, hd⟩ := prem 0 hl _ _ _ hp
      rw [← ccode_inj e₁, ← fcode_inj e₂] at hd
      exact Proves.exI T hd
    · -- ∃E
      obtain ⟨⟨⟨⟨-, hl⟩, hs⟩, hp₀⟩, hp₁⟩ := h
      have hs := (shiftedC_iff (Δ := Δ) (by simp only [qD, fst_pair, snd_pair])).1 hs
      obtain ⟨Δ₀, C, e₁, e₂, hd₀⟩ := prem 0 (by omega) _ _ _ hp₀
      obtain ⟨A, rfl⟩ := fcode_tag_ex (by rw [← e₂]; simp : fst (fcode C) = 6)
      simp only [fcode, pair_eq_pair] at e₂
      rw [e₂.2, hs, lcons_ccode, shiftC_fcode] at hp₁
      obtain ⟨Δ₁, φ₁, e₃, e₄, hd₁⟩ := prem 1 hl _ _ _ hp₁
      rw [← ccode_inj e₁] at hd₀
      rw [← ccode_inj e₃, ← fcode_inj e₄] at hd₁
      refine Proves.exE hd₀ (hd₁.weaken ?_)
      exact Subset.trans (ctx_cons_sub (k + 1) A _)
        (insert_mono (ctx_shift_sub k Δ) A)
    · -- reflexivity
      obtain ⟨⟨-, ht⟩, he⟩ := h
      obtain ⟨t, s, rfl⟩ := fcode_tag_eq ht
      simp only [fcode, fst_pair, snd_pair] at he
      rw [tcode_inj he]
      exact Proves.refl s
    · -- Leibniz's law
      obtain ⟨⟨⟨⟨⟨⟨⟨-, hl⟩, hA⟩, hS⟩, hT⟩, hp₀⟩, hp₁⟩, hi⟩ := h
      obtain ⟨A, hA'⟩ := (isFormulaC_iff _).1 hA
      obtain ⟨S, hS'⟩ := tcode_of_isTermC hS
      obtain ⟨T, hT'⟩ := tcode_of_isTermC hT
      rw [← pair_fst_snd (snd (snd w)), ← hS', ← hT', ← fcode_eq] at hp₀
      rw [← hA', ← hS', instC_fcode] at hp₁
      rw [← hA', ← hT', instC_fcode] at hi
      obtain ⟨Δ₀, C₀, e₁, e₂, hd₀⟩ := prem 0 (by omega) _ _ _ hp₀
      obtain ⟨Δ₁, C₁, e₃, e₄, hd₁⟩ := prem 1 hl _ _ _ hp₁
      rw [← ccode_inj e₁, ← fcode_inj e₂] at hd₀
      rw [← ccode_inj e₃, ← fcode_inj e₄] at hd₁
      rw [← fcode_inj hi]
      exact Proves.subst hd₀ hd₁

/-! ## Completeness: derivations from PA give derivable judgements -/

/-- Codes of formulas pass the formula test. -/
theorem isFormulaC_fcode (φ : Formula Arith) : isFormulaC (fcode φ) = 1 := (isFormulaC_iff _).2 ⟨φ, rfl⟩

/-- Codes of terms pass the term test. -/
theorem isTermC_tcode (t : Term Arith) : isTermC (tcode t) = 1 := (isTermC_iff _).2 ⟨t, rfl⟩

/-- Well-formedness holds for genuine judgements. -/
theorem wfC_ok (k : Nat) (Δ : List (Formula Arith)) (φ : Formula Arith) (r : Nat) :
    wfC (pair (pj k (ccode Δ) (fcode φ)) r) = true := by
  simp only [wfC, qF, qD, pj, fst_pair, snd_pair, Bool.and_eq_true, beq_iff_eq, ballLt_iff,
    isFormulaC_fcode, true_and]
  intro i hi
  rw [llen_ccode] at hi
  rw [lnth_ccode _ _ hi]; exact isFormulaC_fcode _

/-- To check a step it suffices to check the rule. -/
theorem paRule_of_ruleC {k : Nat} {Δ : List (Formula Arith)} {φ : Formula Arith} {w js : Nat}
    (h : ruleC (pair (pj k (ccode Δ) (fcode φ)) (pair w js)) = true) :
    paRule (pj k (ccode Δ) (fcode φ)) w js = true := by
  simp only [paRule, paStep, wfC_ok, h, Bool.and_self]

/-- Premise lists of length one, two, three. -/
theorem all_mem_one {P : Nat → Prop} {a : Nat} (ha : P a) : ∀ y ∈ [a], P y := by simp [ha]
/-- Premise lists of length two. -/
theorem all_mem_two {P : Nat → Prop} {a b : Nat} (ha : P a) (hb : P b) : ∀ y ∈ [a, b], P y := by
  simp [ha, hb]
/-- Premise lists of length three. -/
theorem all_mem_three {P : Nat → Prop} {a b c : Nat} (ha : P a) (hb : P b) (hc : P c) :
    ∀ y ∈ [a, b, c], P y := by simp [ha, hb, hc]

/-- The simp set used to evaluate rule checks on genuine judgements. -/
macro "rule_simp" : tactic => `(tactic| simp only [rC0, rC1, rC2, rC3, rC4, rC5, rC6, rC7, rC8,
  rC9, rC10, rC11, rC12, rC13, rC14, rC15, rC16, rC17, qtag, qdat, qjs, qprem, qk, qD, qF, pj,
  fst_pair, snd_pair, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, llen_encList, lnth_encList,
  List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ, fcode_imp,
  fcode_conj, fcode_disj, fcode_all, fcode_ex, fcode_eq, fcode_neg, fcode_bot, lcons_ccode,
  instC_fcode, shiftC_fcode, isTermC_tcode, isFormulaC_fcode, shiftNC_fcode, Nat.reduceEqDiff,
  Nat.reduceAdd, Nat.reduceLT, Nat.zero_add,
  and_true, true_and])

/-- **Completeness of the rule system.** Every derivation `Γ ⊢₁ φ` from premises
contained in `Ctx k Δ` yields a derivable judgement. -/
theorem derivable_of_proves {Γ : Theory Arith} {φ : Formula Arith} (h : Γ ⊢₁ φ) :
    ∀ k Δ, Γ.Subset (Ctx k Δ) → Derivable paRule (pj k (ccode Δ) (fcode φ)) := by
  induction h with
  | @hyp Γ φ hφ =>
      intro k Δ hsub
      rcases hsub _ hφ with ⟨ψ, hψ, rfl⟩ | hmem
      · obtain ⟨χ, hχ⟩ : ∃ χ, ψ ∈ closedAx ∨ ψ = indAx χ := by
          rcases (PA_iff ψ).1 hψ with h | ⟨χ, h⟩
          · exact ⟨bot, Or.inl h⟩
          · exact ⟨χ, Or.inr h⟩
        refine .intro _ (pair 1 (pair (fcode ψ) (fcode χ))) [] (by simp) (paRule_of_ruleC ?_)
        rw [ruleC_iff]; right; left
        rule_simp
        exact (isPAC_iff ψ χ).2 hχ
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
        refine .intro _ (pair 0 i) [] (by simp) (paRule_of_ruleC ?_)
        rw [ruleC_iff]; left
        rule_simp
        exact ⟨by simpa [llen_ccode] using hi, lnth_ccode _ _ hi⟩
  | @impI Γ A B _ ih =>
      intro k Δ hsub
      have d := ih k (A :: Δ) (Subset.trans (insert_mono hsub A) (insert_ctx_sub k A Δ))
      refine .intro _ (pair 2 0) [pj k (ccode (A :: Δ)) (fcode B)] (all_mem_one d)
        (paRule_of_ruleC ?_)
      rw [ruleC_iff]; right; right; left
      rule_simp
  | @impE Γ A B _ _ ih₁ ih₂ =>
      intro k Δ hsub
      refine .intro _ (pair 3 (fcode A)) [pj k (ccode Δ) (fcode (imp A B)), pj k (ccode Δ) (fcode A)]
        (all_mem_two (ih₁ k Δ hsub) (ih₂ k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; right; right; right; left
      rule_simp
  | @conjI Γ A B _ _ ih₁ ih₂ =>
      intro k Δ hsub
      refine .intro _ (pair 4 0) [pj k (ccode Δ) (fcode A), pj k (ccode Δ) (fcode B)]
        (all_mem_two (ih₁ k Δ hsub) (ih₂ k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; right; right; right; right; left
      rule_simp
  | @conjE₁ Γ A B _ ih =>
      intro k Δ hsub
      refine .intro _ (pair 5 (fcode B)) [pj k (ccode Δ) (fcode (conj A B))]
        (all_mem_one (ih k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 5 right
      left; rule_simp
  | @conjE₂ Γ A B _ ih =>
      intro k Δ hsub
      refine .intro _ (pair 6 (fcode A)) [pj k (ccode Δ) (fcode (conj A B))]
        (all_mem_one (ih k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 6 right
      left; rule_simp
  | @disjI₁ Γ A B _ ih =>
      intro k Δ hsub
      refine .intro _ (pair 7 0) [pj k (ccode Δ) (fcode A)]
        (all_mem_one (ih k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 7 right
      left; rule_simp
  | @disjI₂ Γ A B _ ih =>
      intro k Δ hsub
      refine .intro _ (pair 8 0) [pj k (ccode Δ) (fcode B)]
        (all_mem_one (ih k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 8 right
      left; rule_simp
  | @disjE Γ A B C _ _ _ ih₀ ih₁ ih₂ =>
      intro k Δ hsub
      have d₁ := ih₁ k (A :: Δ) (Subset.trans (insert_mono hsub A) (insert_ctx_sub k A Δ))
      have d₂ := ih₂ k (B :: Δ) (Subset.trans (insert_mono hsub B) (insert_ctx_sub k B Δ))
      refine .intro _ (pair 9 (pair (fcode A) (fcode B)))
        [pj k (ccode Δ) (fcode (disj A B)), pj k (ccode (A :: Δ)) (fcode C),
          pj k (ccode (B :: Δ)) (fcode C)]
        (all_mem_three (ih₀ k Δ hsub) d₁ d₂) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 9 right
      left; rule_simp
  | @botE Γ A _ ih =>
      intro k Δ hsub
      refine .intro _ (pair 10 0) [pj k (ccode Δ) (fcode bot)]
        (all_mem_one (ih k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 10 right
      left; rule_simp
  | @raa Γ A _ ih =>
      intro k Δ hsub
      have d := ih k (neg A :: Δ) (Subset.trans (insert_mono hsub _) (insert_ctx_sub k _ Δ))
      refine .intro _ (pair 11 0) [pj k (ccode (neg A :: Δ)) (fcode bot)]
        (all_mem_one d) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 11 right
      left; rule_simp
      rw [← fcode_neg, lcons_ccode]
  | @allI Γ A _ ih =>
      intro k Δ hsub
      have d := ih (k + 1) (Δ.map Formula.shift) (Subset.trans (shift_mono hsub) (shift_ctx_sub k Δ))
      refine .intro _ (pair 12 (ccode (Δ.map Formula.shift)))
        [pj (k + 1) (ccode (Δ.map Formula.shift)) (fcode A)] (all_mem_one d) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 12 right
      left; rule_simp
      exact (shiftedC_iff (Δ := Δ) (by simp only [qD, pj, fst_pair, snd_pair])).2 rfl
  | @allE Γ A t _ ih =>
      intro k Δ hsub
      refine .intro _ (pair 13 (pair (fcode A) (tcode t))) [pj k (ccode Δ) (fcode (all A))]
        (all_mem_one (ih k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 13 right
      left; rule_simp
  | @exI Γ A t _ ih =>
      intro k Δ hsub
      refine .intro _ (pair 14 (tcode t)) [pj k (ccode Δ) (fcode (A.inst t))]
        (all_mem_one (ih k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 14 right
      left; rule_simp
  | @exE Γ A B _ _ ih₀ ih₁ =>
      intro k Δ hsub
      have hs : (Theory.insert (Theory.shift Γ) A).Subset (Ctx (k + 1) (A :: Δ.map Formula.shift)) :=
        Subset.trans (insert_mono (Subset.trans (shift_mono hsub) (shift_ctx_sub k Δ)) A)
          (insert_ctx_sub (k + 1) A _)
      have d := ih₁ (k + 1) (A :: Δ.map Formula.shift) hs
      refine .intro _ (pair 15 (pair (fcode A) (ccode (Δ.map Formula.shift))))
        [pj k (ccode Δ) (fcode (ex A)), pj (k + 1) (ccode (A :: Δ.map Formula.shift)) (fcode B.shift)]
        (all_mem_two (ih₀ k Δ hsub) d) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 15 right
      left; rule_simp
      exact (shiftedC_iff (Δ := Δ) (by simp only [qD, pj, fst_pair, snd_pair])).2 rfl
  | @refl Γ t =>
      intro k Δ hsub
      refine .intro _ (pair 16 0) [] (by simp) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 16 right
      left; rule_simp
  | @subst Γ A s t _ _ ih₀ ih₁ =>
      intro k Δ hsub
      refine .intro _ (pair 17 (pair (fcode A) (pair (tcode s) (tcode t))))
        [pj k (ccode Δ) (fcode (eq s t)), pj k (ccode Δ) (fcode (A.inst s))]
        (all_mem_two (ih₀ k Δ hsub) (ih₁ k Δ hsub)) (paRule_of_ruleC ?_)
      rw [ruleC_iff]; iterate 17 right
      rule_simp

/-! ## Enumerability of the theorems of PA -/

/-- PA is the context with no shifts and no assumptions. -/
theorem ctx_zero_nil : (Ctx 0 []).Subset PA ∧ PA.Subset (Ctx 0 []) := by
  refine ⟨?_, fun ψ h => Or.inl ⟨ψ, h, rfl⟩⟩
  rintro ψ (⟨χ, hχ, rfl⟩ | h)
  · exact hχ
  · simp [Theory.ofList] at h

/-- **Derivability in the rule system is derivability from PA.** -/
theorem derivable_iff_PA_proves (φ : Formula Arith) :
    Derivable paRule (pj 0 (ccode []) (fcode φ)) ↔ PA ⊢₁ φ := by
  constructor
  · intro h
    obtain ⟨k, Δ, φ', e, hd⟩ := proves_of_derivable h
    obtain ⟨rfl, e₂, e₃⟩ := pj_inj e
    rw [ccode_inj e₂.symm, fcode_inj e₃.symm] at hd
    exact hd.weaken ctx_zero_nil.1
  · intro h
    exact derivable_of_proves h 0 [] ctx_zero_nil.2

/-- Composing a code with a total computable function preserves halting behaviour. -/
theorem halts_comp_iff {c cf : Code} {f : Nat → Nat} (hf : ∀ n, Eval cf [n] (f n)) (n : Nat) :
    Halts (.comp c (vec1 cf)) [n] ↔ Halts c [f n] := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨v, hv, hc⟩ := eval_comp1_inv hm
    rw [Eval.det hv (hf n)] at hc
    exact ⟨m, hc⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, eval_comp1 (hf n) hm⟩

/-- **The theorems of Peano arithmetic are computably enumerable.** There is a code
which, given the Gödel number of a formula `φ`, halts if and only if `PA ⊢₁ φ`:
it searches through all candidate derivations and checks each mechanically. -/
theorem PA_theorems_ce : ∃ c : Code, ∀ φ : Formula Arith, Halts c [fcode φ] ↔ PA ⊢₁ φ := by
  obtain ⟨c₀, hc₀⟩ := ce_derivable paRule paRule_comp
  obtain ⟨cf, hcf⟩ := (Comp.pair (Comp.const 0) (Comp.pair (Comp.const 0) Comp.id) :
    Comp fun n => pj 0 (ccode []) n)
  exact ⟨.comp c₀ (vec1 cf), fun φ => by
    rw [halts_comp_iff hcf, hc₀]; exact derivable_iff_PA_proves φ⟩

end Foundations.Logic.FO
