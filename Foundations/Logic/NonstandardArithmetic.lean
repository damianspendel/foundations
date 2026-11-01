import Foundations.Logic.FOCompleteness
import Foundations.Logic.PeanoArithmetic

/-!
# A non-standard model of arithmetic

First-order Peano arithmetic was designed to describe the natural numbers
`0, 1, 2, …`. Thoralf Skolem (1933–34) discovered that it cannot pin them down: there
are **non-standard models** of PA, containing "infinite" elements lying beyond every
numeral `S(S(⋯S(0)⋯))`. This is a striking limitation of first-order logic — in
contrast with Dedekind's *second-order* induction axiom, which characterises `ℕ` up
to isomorphism.

The modern proof is a one-line application of compactness. Consider PA together
with the infinitely many formulas `x ≠ 0, x ≠ 1, x ≠ 2, …` about a variable `x`.
Every finite part is satisfiable in `ℕ` itself (take `x` larger than the finitely
many numerals mentioned). So by compactness the whole theory has a model, and there
the value of `x` differs from the value of every numeral.

One technical point: our PA has induction axioms with free *parameters*, while a
model of PA must satisfy them under *every* assignment. So we apply compactness to
all *universal closures* `∀…∀ ψ` of PA axioms, and use the **coincidence lemma**
(satisfaction depends only on the values of free variables) to recover full PA.
-/

namespace Foundations.Logic.FO

variable {L : Signature}

open Formula Theory Arith

/-! ## The coincidence lemma -/

/-- Environments agreeing on the variables occurring in a term give it the same value. -/
theorem Term.eval_congr_fresh {M : Structure L} {e e' : Nat → M.Dom} :
    ∀ t : Term L, (∀ n, ¬ t.Fresh n → e n = e' n) → t.eval M e = t.eval M e'
  | .var m, h => h m (by simp [Term.Fresh])
  | .func f ts, h => by
      simp only [Term.eval]; congr 1; funext i
      exact Term.eval_congr_fresh (ts i) fun n hn => h n fun hf => hn (hf i)

/-- **Coincidence lemma.** Environments agreeing on the free variables of a formula
give it the same truth value. -/
theorem Formula.sat_congr_fresh {M : Structure L} :
    ∀ (φ : Formula L) {e e' : Nat → M.Dom}, (∀ n, ¬ φ.Fresh n → e n = e' n) →
      (Sat M e φ ↔ Sat M e' φ)
  | .bot, _, _, _ => Iff.rfl
  | .eq t s, _, _, h => by
      simp only [Sat]
      rw [Term.eval_congr_fresh t fun n hn => h n fun hf => hn hf.1,
        Term.eval_congr_fresh s fun n hn => h n fun hf => hn hf.2]
  | .rel R ts, _, _, h => by
      simp only [Sat]
      have : (fun i => (ts i).eval M _) = fun i => (ts i).eval M _ :=
        funext fun i => Term.eval_congr_fresh (ts i) fun n hn => h n fun hf => hn (hf i)
      rw [this]
  | .imp φ ψ, _, _, h => by
      simp only [Sat]
      rw [sat_congr_fresh φ fun n hn => h n fun hf => hn hf.1,
        sat_congr_fresh ψ fun n hn => h n fun hf => hn hf.2]
  | .conj φ ψ, _, _, h => by
      simp only [Sat]
      rw [sat_congr_fresh φ fun n hn => h n fun hf => hn hf.1,
        sat_congr_fresh ψ fun n hn => h n fun hf => hn hf.2]
  | .disj φ ψ, _, _, h => by
      simp only [Sat]
      rw [sat_congr_fresh φ fun n hn => h n fun hf => hn hf.1,
        sat_congr_fresh ψ fun n hn => h n fun hf => hn hf.2]
  | .all φ, e, e', h => by
      simp only [Sat]
      refine forall_congr' fun x => sat_congr_fresh φ fun n hn => ?_
      cases n with
      | zero => rfl
      | succ m => exact h m hn
  | .ex φ, e, e', h => by
      simp only [Sat]
      refine exists_congr fun x => sat_congr_fresh φ fun n hn => ?_
      cases n with
      | zero => rfl
      | succ m => exact h m hn

/-! ## Universal closures -/

/-- `allN k θ` prefixes `k` universal quantifiers to `θ`. -/
def allN : Nat → Formula L → Formula L
  | 0, θ => θ
  | k + 1, θ => all (allN k θ)

/-- `∀^k θ` holds under `e₀` iff `θ` holds under every environment that agrees with
`e₀` beyond the first `k` variables (shifted by `k`). -/
theorem sat_allN {M : Structure L} (θ : Formula L) :
    ∀ (k : Nat) (e₀ : Nat → M.Dom),
      Sat M e₀ (allN k θ) ↔ ∀ e : Nat → M.Dom, (∀ n, e (n + k) = e₀ n) → Sat M e θ
  | 0, e₀ => by
      simp only [allN, Nat.add_zero]
      exact ⟨fun h e he => by rw [show e = e₀ from funext he]; exact h, fun h => h e₀ fun _ => rfl⟩
  | k + 1, e₀ => by
      simp only [allN, Sat]
      constructor
      · intro h e he
        refine (sat_allN θ k _).1 (h (e k)) e fun n => ?_
        cases n with
        | zero => simp [Env.cons]
        | succ m =>
            show e (m + 1 + k) = e₀ m
            rw [show m + 1 + k = m + (k + 1) by omega]; exact he m
      · intro h x
        refine (sat_allN θ k _).2 fun e he => h e fun n => ?_
        rw [show n + (k + 1) = (n + 1) + k by omega, he (n + 1)]; rfl

/-! ## Arithmetic -/

/-- The language of arithmetic is countable (four function symbols, no relations). -/
instance : Signature.Countable Arith where
  funcCode := fun k => match k with
    | 0 => some ⟨0, ArithFunc.zero⟩
    | 1 => some ⟨1, ArithFunc.succ⟩
    | 2 => some ⟨2, ArithFunc.add⟩
    | 3 => some ⟨2, ArithFunc.mul⟩
    | _ => none
  funcCode_surj := by
    intro n (f : ArithFunc n)
    cases f
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  relCode := fun _ => none
  relCode_surj := fun _ (R : Empty) => R.elim

/-- The numeral `S(S(⋯S(0)⋯))` for `n`. -/
def numeral : Nat → Term Arith
  | 0 => zero
  | n + 1 => succ (numeral n)

/-- In the standard model, the numeral for `n` denotes `n`. -/
theorem eval_numeral_std (e : Nat → Nat) : ∀ n, (numeral n).eval stdModel e = n
  | 0 => rfl
  | n + 1 => by simp only [numeral, eval_succ, eval_numeral_std e n]

/-- Numerals are closed terms: their value does not depend on the environment. -/
theorem eval_numeral_indep (M : Structure Arith) (e e' : Nat → M.Dom) :
    ∀ n, (numeral n).eval M e = (numeral n).eval M e'
  | 0 => by simp only [numeral, zero, Term.eval]; congr 1; funext i; exact i.elim0
  | n + 1 => by simp only [numeral, succ, Term.eval, eval_numeral_indep M e e' n]

/-- Distinct numbers have distinct numerals. -/
theorem numeral_inj {n m : Nat} (h : numeral n = numeral m) : n = m := by
  have := congrArg (fun t => t.eval stdModel fun _ => (0 : Nat)) h
  simpa only [eval_numeral_std] using this

/-- All universal closures `∀…∀ ψ` of axioms `ψ` of PA. -/
def PAClosure : Theory Arith := fun χ => ∃ ψ k, PA ψ ∧ χ = allN k ψ

/-- The standard model satisfies all universal closures of PA axioms. -/
theorem stdModel_PAClosure : ∀ χ, PAClosure χ → ∀ e, Sat stdModel e χ := by
  rintro _ ⟨ψ, k, hψ, rfl⟩ e
  exact (sat_allN ψ k e).2 fun e' _ => stdModel_isModel ψ hψ e'

/-- A structure satisfying all universal closures of PA axioms under a single
environment is a model of PA (under every environment), by the coincidence lemma. -/
theorem isModel_of_PAClosure {M : Structure Arith} {e₀ : Nat → M.Dom}
    (h : ∀ χ, PAClosure χ → Sat M e₀ χ) : IsModel M PA := by
  intro ψ hψ e
  obtain ⟨B, hB⟩ := eventually_fresh ψ
  let e' : Nat → M.Dom := fun n => if n < B then e n else e₀ (n - B)
  have h₁ := (sat_allN ψ B e₀).1 (h _ ⟨ψ, B, hψ, rfl⟩) e' fun n => by
    simp only [e', show ¬ (n + B < B) by omega, ite_false, Nat.add_sub_cancel]
  refine (sat_congr_fresh ψ fun n hn => ?_).1 h₁
  have : n < B := Classical.byContradiction fun hn' => hn (hB n (by omega))
  simp only [e', this, ite_true]

/-- The theory used to build a non-standard model: PA (in closed form) together with
`x ≠ n̄` for every numeral `n̄`, where `x` is the variable with index `0`. -/
def nonstdTheory : Theory Arith :=
  union PAClosure fun χ => ∃ n, χ = neg (eq (v 0) (numeral n))

/-- Only finitely many numerals are excluded by a finite list of formulas. -/
theorem nonstd_bound : ∀ l : List (Formula Arith), ∃ B, ∀ N, B ≤ N → ∀ χ ∈ l, ∀ n,
    χ = neg (eq (v 0) (numeral n)) → N ≠ n
  | [] => ⟨0, by simp⟩
  | χ :: l => by
      obtain ⟨B, hB⟩ := nonstd_bound l
      by_cases hχ : ∃ n₀, χ = neg (eq (v 0) (numeral n₀))
      · obtain ⟨n₀, rfl⟩ := hχ
        refine ⟨max B (n₀ + 1), fun N hN χ' hχ' n hn => ?_⟩
        rcases List.mem_cons.1 hχ' with rfl | hχ'
        · simp only [neg] at hn
          injection hn with hn
          injection hn with _ hn
          have := numeral_inj hn
          omega
        · exact hB N (by omega) χ' hχ' n hn
      · refine ⟨B, fun N hN χ' hχ' n hn => ?_⟩
        rcases List.mem_cons.1 hχ' with rfl | hχ'
        · exact absurd ⟨n, hn⟩ hχ
        · exact hB N hN χ' hχ' n hn

/-- Every finite part of `nonstdTheory` is satisfied in the standard model, by giving
`x` a value larger than all numerals mentioned. -/
theorem nonstd_finitely_sat (l : List (Formula Arith)) (hl : ∀ ψ ∈ l, nonstdTheory ψ) :
    ∃ (M : Structure Arith) (e : Nat → M.Dom), ∀ ψ ∈ l, Sat M e ψ := by
  obtain ⟨B, hB⟩ := nonstd_bound l
  refine ⟨stdModel, fun _ => B, fun ψ hψ => ?_⟩
  rcases hl ψ hψ with h | ⟨n, rfl⟩
  · exact stdModel_PAClosure ψ h _
  · intro (h : B = (numeral n).eval stdModel fun _ => B)
    rw [eval_numeral_std] at h
    exact hB B (Nat.le_refl _) _ hψ n rfl h

/-- **Existence of a non-standard model of arithmetic** (Skolem). There is a
(countable) model of Peano arithmetic containing an element different from the value
of every numeral `0, S0, SS0, …` — an "infinite" natural number. In particular this
model is not isomorphic to the standard model `ℕ`, in which every element is the
value of a numeral. -/
theorem nonstandard_model :
    ∃ M : Structure Arith, IsModel M PA ∧ (∃ f : Nat → M.Dom, ∀ x, ∃ n, f n = x) ∧
      ∃ a : M.Dom, ∀ (n : Nat) (e : Nat → M.Dom), a ≠ (numeral n).eval M e := by
  obtain ⟨M, e₀, he₀, hcount⟩ := compactness nonstd_finitely_sat
  refine ⟨M, isModel_of_PAClosure fun χ h => he₀ χ (Or.inl h), hcount, e₀ 0, fun n e ha => ?_⟩
  have h := he₀ _ (Or.inr ⟨n, rfl⟩)
  exact h (show e₀ 0 = (numeral n).eval M e₀ by rw [eval_numeral_indep M e₀ e]; exact ha)

/-- In the standard model, by contrast, every element is the value of a numeral. -/
theorem stdModel_all_numerals (a : Nat) (e : Nat → Nat) : (numeral a).eval stdModel e = a :=
  eval_numeral_std e a

end Foundations.Logic.FO
