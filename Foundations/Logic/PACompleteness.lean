import Foundations.Logic.PAModels

/-!
# Completeness for PA, in the form "true in every model of PA ⇒ provable"

The derivability conditions will be established *semantically*: we shall show that
certain sentences hold in every model of PA, reasoning inside the model with its
induction schema, and then invoke Gödel's completeness theorem. There is one wrinkle.
Completeness, as proved in `FOCompleteness`, speaks of a structure together with a
*single* environment `e₀` satisfying all axioms of PA. Our induction axioms are open
formulas — their parameters are free variables — so satisfaction under one environment
only gives induction for properties whose parameters take the values that `e₀`
assigns. Arguments inside a model, however, apply induction to properties with
*arbitrary* parameters (a code of a proof, a bound, …).

The gap is closed by a classical trick, already alluded to in the docstring of `PA`:
the induction instance for the parameter-free formula
`ψ(x) := ∀ȳ [φ(0, ȳ) ∧ ∀z (φ(z, ȳ) → φ(z+1, ȳ)) → φ(x, ȳ)]`
yields, for every choice of parameters `ȳ`, the parametric instance for `φ`. Hence a
structure satisfying PA under a single environment satisfies it under all of them
(`isModel_of_sat_PA`), and so

* `PA_proves_of_models`: *a formula true in every `PAModel` (under every environment)
  is provable in PA.*
-/

namespace Foundations.Logic.FO

open Arith Formula Theory

section
variable {M : Structure Arith}

/-- The successor substitution, semantically: it replaces `x` by `x + 1`. -/
theorem succSubst_eval (z : M.Dom) (e : Nat → M.Dom) :
    (fun n => (succSubst n).eval M (Env.cons z e)) = Env.cons (ms M z) e := by
  funext n; cases n <;> rfl

/-- The body of the "parameters-quantified" induction formula: with the parameters of
`φ` read from `e'` and the induction variable instantiated at `v B`. -/
def indBody (φ : Formula Arith) (B : Nat) : Formula Arith :=
  imp (conj (φ.inst zero) (all (imp φ (φ.subst succSubst)))) (φ.inst (v B))

/-- Meaning of `indBody`: if `φ(·, e')` is inductive, it holds at `e' B`. -/
theorem sat_indBody (φ : Formula Arith) (B : Nat) (e' : Nat → M.Dom) :
    Sat M e' (indBody φ B) ↔
      ((Sat M (Env.cons (mz M) e') φ ∧ ∀ z, Sat M (Env.cons z e') φ → Sat M (Env.cons (ms M z) e') φ) →
        Sat M (Env.cons (e' B) e') φ) := by
  simp only [indBody, Sat, sat_inst, sat_subst, succSubst_eval, eval_zero_M, eval_var_M]

/-- Meaning of an induction axiom. -/
theorem sat_PA_induction (φ : Formula Arith) (e : Nat → M.Dom) :
    Sat M e (imp (conj (φ.inst zero) (all (imp φ (φ.subst succSubst)))) (all φ)) ↔
      ((Sat M (Env.cons (mz M) e) φ ∧ ∀ z, Sat M (Env.cons z e) φ → Sat M (Env.cons (ms M z) e) φ) →
        ∀ x, Sat M (Env.cons x e) φ) := by
  simp only [Sat, sat_inst, sat_subst, succSubst_eval, eval_zero_M]

/-- **Parametric induction from parameter-free induction.** If a structure satisfies
the induction axiom of `∀^B indBody φ B` under one environment `e₀`, and `φ` has no
free variables beyond `B`, then it satisfies the induction axiom of `φ` under *every*
environment. -/
theorem sat_induction_of_closed (φ : Formula Arith) (B : Nat) (hB : ∀ n, B ≤ n → φ.Fresh n)
    (e₀ : Nat → M.Dom)
    (h : Sat M e₀ (imp (conj ((allN B (indBody φ B)).inst zero)
      (all (imp (allN B (indBody φ B)) ((allN B (indBody φ B)).subst succSubst))))
      (all (allN B (indBody φ B)))))
    (e : Nat → M.Dom) :
    Sat M e (imp (conj (φ.inst zero) (all (imp φ (φ.subst succSubst)))) (all φ)) := by
  rw [sat_PA_induction] at h ⊢
  -- `∀^B indBody` holds everywhere
  have main : ∀ x, Sat M (Env.cons x e₀) (allN B (indBody φ B)) := by
    refine h ⟨?_, ?_⟩
    · refine (sat_allN _ B _).2 fun e' he' => (sat_indBody φ B e').2 fun ⟨h0, _⟩ => ?_
      have : e' B = mz M := by have := he' 0; rwa [Nat.zero_add] at this
      rw [this]; exact h0
    · intro x hx
      refine (sat_allN _ B _).2 fun e' he' => (sat_indBody φ B e').2 fun ⟨h0, hs⟩ => ?_
      let e'' : Nat → M.Dom := fun n => if n = B then x else e' n
      have he'' : ∀ n, e'' (n + B) = Env.cons x e₀ n := by
        intro n; cases n with
        | zero => simp [e'']; rfl
        | succ m =>
            simp only [e'', show m + 1 + B ≠ B by omega, ite_false]
            exact he' (m + 1)
      have hc : ∀ z, Sat M (Env.cons z e'') φ ↔ Sat M (Env.cons z e') φ := fun z =>
        sat_congr_fresh φ fun n hn => by
          cases n with
          | zero => rfl
          | succ m =>
              show e'' m = e' m
              by_cases hm : m = B
              · exact absurd (hB _ (by omega)) hn
              · simp [e'', hm]
      have key := (sat_indBody φ B e'').1 ((sat_allN _ B _).1 hx e'' he'')
        ⟨(hc _).2 h0, fun z hz => (hc _).2 (hs z ((hc _).1 hz))⟩
      have hxB : e'' B = x := by simp [e'']
      rw [hxB, hc] at key
      have : e' B = ms M x := by have := he' 0; rwa [Nat.zero_add] at this
      rw [this]; exact hs x key
  rintro ⟨h0, hs⟩ x
  let e' : Nat → M.Dom := fun n => if n < B then e n else if n = B then x else e₀ (n - B - 1)
  have he' : ∀ n, e' (n + B) = Env.cons x e₀ n := by
    intro n; cases n with
    | zero => simp [e']; rfl
    | succ m =>
        simp only [e', show ¬ (m + 1 + B < B) by omega, show m + 1 + B ≠ B by omega, ite_false]
        show e₀ (m + 1 + B - B - 1) = e₀ m
        congr 1; omega
  have hc : ∀ z, Sat M (Env.cons z e') φ ↔ Sat M (Env.cons z e) φ := fun z =>
    sat_congr_fresh φ fun n hn => by
      cases n with
      | zero => rfl
      | succ m =>
          show e' m = e m
          by_cases hm : m < B
          · simp [e', hm]
          · exact absurd (hB _ (by omega)) hn
  have key := (sat_indBody φ B e').1 ((sat_allN _ B _).1 (main x) e' he')
    ⟨(hc _).2 h0, fun z hz => (hc _).2 (hs z ((hc _).1 hz))⟩
  have hxB : e' B = x := by simp [e']
  rwa [hxB, hc] at key

/-- A sentence without free variables has the same truth value everywhere. -/
theorem sat_of_closed {ψ : Formula Arith} (hψ : ∀ n, ψ.Fresh n) {e₀ : Nat → M.Dom}
    (h : Sat M e₀ ψ) (e : Nat → M.Dom) : Sat M e ψ :=
  (sat_congr_fresh ψ fun n hn => absurd (hψ n) hn).1 h

/-- **A structure satisfying PA under one environment is a model of PA.** -/
theorem isModel_of_sat_PA {e₀ : Nat → M.Dom} (h : ∀ ψ, PA ψ → Sat M e₀ ψ) : IsModel M PA := by
  refine ⟨⟨e₀ 0⟩, fun ψ hψ e => ?_⟩
  cases hψ with
  | induction φ =>
      obtain ⟨B, hB⟩ := eventually_fresh φ
      exact sat_induction_of_closed φ B hB e₀ (h _ (PA.induction _)) e
  | succ_ne_zero =>
      exact sat_of_closed (fun n => by
        simp [neg, Formula.Fresh, Term.Fresh, Arith.succ, Arith.zero]) (h _ PA.succ_ne_zero) e
  | succ_inj =>
      exact sat_of_closed (fun n => by
        simp [Formula.Fresh, Term.Fresh, Arith.succ]) (h _ PA.succ_inj) e
  | add_zero =>
      exact sat_of_closed (fun n => by
        simp [Formula.Fresh, Term.Fresh, Arith.add, Arith.zero, args₂]) (h _ PA.add_zero) e
  | add_succ =>
      exact sat_of_closed (fun n => by
        simp [Formula.Fresh, Term.Fresh, Arith.add, Arith.succ, args₂]) (h _ PA.add_succ) e
  | mul_zero =>
      exact sat_of_closed (fun n => by
        simp [Formula.Fresh, Term.Fresh, Arith.mul, Arith.zero, args₂]) (h _ PA.mul_zero) e
  | mul_succ =>
      exact sat_of_closed (fun n => by
        simp [Formula.Fresh, Term.Fresh, Arith.mul, Arith.add, Arith.succ, args₂])
        (h _ PA.mul_succ) e

end

/-- **Completeness for PA, model-theoretic form.** A formula that holds in every model
of PA, under every environment, is provable in PA. -/
theorem PA_proves_of_models {φ : Formula Arith} (h : ∀ (N : PAModel) (e : Nat → N.Dom), Sat N.M e φ) :
    PA ⊢₁ φ :=
  completeness fun M e hM => h ⟨M, isModel_of_sat_PA hM⟩ e

end Foundations.Logic.FO
