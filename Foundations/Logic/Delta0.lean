import Foundations.Logic.RobinsonQ

/-!
# Bounded formulas and Σ₁-completeness of `Q`

A formula is **bounded** (Δ₀) if all its quantifiers are bounded by terms:
`∀x ≤ t` and `∃x ≤ t`. The truth of a bounded sentence can be decided by a finite
computation, and — this is the crucial point — it is the same in *every* model of `Q`
as in `ℕ`: a bounded quantifier `∀x ≤ n̄` ranges, in any model of `Q`, over exactly the
numerals `0̄, …, n̄` (by the previous file). Hence (**Δ₀-absoluteness**)

> for bounded `φ` and numerals `ā`, `M ⊨ φ(ā)` iff `ℕ ⊨ φ(a)`, for every model `M` of `Q`.

By the completeness theorem this means that **`Q` decides every bounded sentence**:
it proves the true ones and refutes the false ones. Prefixing one unbounded `∃`
gives the **Σ₁-formulas**, and a true Σ₁ sentence `∃x φ(x)` is true in every model
of `Q` (the standard witness works), so **`Q` proves every true Σ₁ sentence**
(*Σ₁-completeness*). A false Σ₁ sentence, on the other hand, may well be true in a
non-standard model, through a non-standard witness — which is why the
incompleteness theorems are possible at all.

We write `x ≤ y` as `∃d. d + x = y` (`leF`), and treat it as atomic: the class `D0`
of bounded formulas is closed under the connectives and the bounded quantifiers
`∀x ≤ t`, `∀x (Sx ≤ t → ·)` (that is, `∀x < t`) and `∃x ≤ t`, and under arbitrary
substitution of terms.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula

/-- `x ≤ y` as the formula `∃d. d + x = y` (free variables `0 = x`, `1 = y`). -/
def leF : Formula Arith := ex (eq (add (v 0) (v 1)) (v 2))

/-- Meaning of `leF` in any structure. -/
theorem sat_leF {M : Structure Arith} (e : Nat → M.Dom) : Sat M e leF ↔ mle M (e 0) (e 1) := by
  simp only [leF, Sat, eval_add_M, eval_var_M, Env.cons, mle]

/-- In `ℕ`, `mle` is `≤`. -/
theorem mle_std (x y : Nat) : mle stdModel x y ↔ x ≤ y := by
  constructor
  · rintro ⟨d, hd⟩; exact hd ▸ Nat.le_add_left x d
  · intro h; exact ⟨y - x, Nat.sub_add_cancel h⟩

/-- The bounding formula of `∀x ≤ T` / `∃x ≤ T`, under the new binder. -/
def boundF (T : Term Arith) : Formula Arith := substL [v 0, T.rename Nat.succ] leF

/-- The bounding formula of `∀x < T` (as `Sx ≤ T`), under the new binder. -/
def boundSF (T : Term Arith) : Formula Arith := substL [succ (v 0), T.rename Nat.succ] leF

/-- Evaluating a shifted term under a pushed environment. -/
theorem eval_rename_succ_cons {M : Structure Arith} (T : Term Arith) (x : M.Dom) (e : Nat → M.Dom) :
    (T.rename Nat.succ).eval M (Env.cons x e) = T.eval M e := by
  rw [Term.eval_rename]; rfl

/-- Meaning of the bound `x ≤ T`. -/
theorem sat_boundF {M : Structure Arith} (T : Term Arith) (x : M.Dom) (e : Nat → M.Dom) :
    Sat M (Env.cons x e) (boundF T) ↔ mle M x (T.eval M e) := by
  rw [boundF, substL, sat_subst, sat_leF]
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_var_M, Env.cons, eval_rename_succ_cons]

/-- Meaning of the bound `Sx ≤ T`. -/
theorem sat_boundSF {M : Structure Arith} (T : Term Arith) (x : M.Dom) (e : Nat → M.Dom) :
    Sat M (Env.cons x e) (boundSF T) ↔ mle M (ms M x) (T.eval M e) := by
  rw [boundSF, substL, sat_subst, sat_leF]
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_succ_M, eval_var_M, Env.cons,
    eval_rename_succ_cons]

/-- Operations of the standard model. -/
@[simp] theorem madd_std (a b : Nat) : madd stdModel a b = a + b := rfl
/-- Operations of the standard model. -/
@[simp] theorem mmul_std (a b : Nat) : mmul stdModel a b = a * b := rfl
/-- Operations of the standard model. -/
@[simp] theorem ms_std (a : Nat) : ms stdModel a = a + 1 := rfl
/-- Operations of the standard model. -/
@[simp] theorem mz_std : mz stdModel = (0 : Nat) := rfl

/-- The bound `x ≤ T` in `ℕ`. -/
theorem sat_boundF_std (T : Term Arith) (x : Nat) (e : Nat → Nat) :
    Sat stdModel (Env.cons (α := Nat) x e) (boundF T) ↔ x ≤ T.eval stdModel e := by
  rw [sat_boundF (M := stdModel), mle_std]

/-- The bound `Sx ≤ T` in `ℕ`. -/
theorem sat_boundSF_std (T : Term Arith) (x : Nat) (e : Nat → Nat) :
    Sat stdModel (Env.cons (α := Nat) x e) (boundSF T) ↔ x < T.eval stdModel e := by
  rw [sat_boundSF (M := stdModel), mle_std]; rfl

/-- **Bounded (Δ₀) formulas.** -/
inductive D0 : Formula Arith → Prop where
  /-- Equations. -/
  | eq (t s : Term Arith) : D0 (eq t s)
  /-- Inequalities `t ≤ s`. -/
  | le (t s : Term Arith) : D0 (substL [t, s] leF)
  /-- Falsum. -/
  | bot : D0 bot
  /-- Implication. -/
  | imp {φ ψ} : D0 φ → D0 ψ → D0 (imp φ ψ)
  /-- Conjunction. -/
  | conj {φ ψ} : D0 φ → D0 ψ → D0 (conj φ ψ)
  /-- Disjunction. -/
  | disj {φ ψ} : D0 φ → D0 ψ → D0 (disj φ ψ)
  /-- Bounded universal quantifier `∀x ≤ T`. -/
  | ball (T : Term Arith) {φ} : D0 φ → D0 (all (imp (boundF T) φ))
  /-- Strictly bounded universal quantifier `∀x < T`. -/
  | ballS (T : Term Arith) {φ} : D0 φ → D0 (all (imp (boundSF T) φ))
  /-- Bounded existential quantifier `∃x ≤ T`. -/
  | bex (T : Term Arith) {φ} : D0 φ → D0 (ex (conj (boundF T) φ))

/-- Negations of bounded formulas are bounded. -/
theorem D0.neg {φ : Formula Arith} (h : D0 φ) : D0 (neg φ) := D0.imp h D0.bot

/-- Substituting into a list substitution. -/
theorem substL_subst (ts : List (Term Arith)) (φ : Formula Arith) (σ : Nat → Term Arith) :
    (substL ts φ).subst σ = substL (ts.map fun t => t.subst σ) φ := by
  rw [substL, substL, subst_subst]
  refine subst_ext φ fun n => ?_
  by_cases h : n < ts.length
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-- Substituting into the bound of a bounded quantifier. -/
theorem boundF_subst (T : Term Arith) (σ : Nat → Term Arith) :
    (boundF T).subst (Subst.lift σ) = boundF (T.subst σ) := by
  rw [boundF, boundF, substL_subst]
  simp only [List.map_cons, List.map_nil, Term.rename_succ_subst_lift]; rfl

/-- Substituting into the bound of a strictly bounded quantifier. -/
theorem boundSF_subst (T : Term Arith) (σ : Nat → Term Arith) :
    (boundSF T).subst (Subst.lift σ) = boundSF (T.subst σ) := by
  rw [boundSF, boundSF, substL_subst]
  simp only [List.map_cons, List.map_nil, Term.rename_succ_subst_lift, succ_subst]; rfl

/-- **Bounded formulas are closed under substitution.** -/
theorem D0.subst {φ : Formula Arith} (h : D0 φ) : ∀ σ : Nat → Term Arith, D0 (φ.subst σ) := by
  induction h with
  | eq t s => intro σ; exact D0.eq _ _
  | le t s => intro σ; rw [substL_subst]; exact D0.le _ _
  | bot => intro σ; exact D0.bot
  | imp _ _ ih₁ ih₂ => intro σ; exact D0.imp (ih₁ σ) (ih₂ σ)
  | conj _ _ ih₁ ih₂ => intro σ; exact D0.conj (ih₁ σ) (ih₂ σ)
  | disj _ _ ih₁ ih₂ => intro σ; exact D0.disj (ih₁ σ) (ih₂ σ)
  | ball T _ ih =>
      intro σ; simp only [Formula.subst]; rw [boundF_subst]; exact D0.ball _ (ih _)
  | ballS T _ ih =>
      intro σ; simp only [Formula.subst]; rw [boundSF_subst]; exact D0.ballS _ (ih _)
  | bex T _ ih =>
      intro σ; simp only [Formula.subst]; rw [boundF_subst]; exact D0.bex _ (ih _)

/-! ## Absoluteness -/

section
variable {M : Structure Arith} (hM : IsQModel M)
include hM

/-- **Closed terms evaluate correctly in models of `Q`**: under an environment of
numeral values, every term takes the value of the numeral of its standard value. -/
theorem eval_numM (e : Nat → Nat) :
    ∀ t : Term Arith, t.eval M (fun n => numM M (e n)) = numM M (t.eval stdModel e) := by
  intro t
  induction t using Term.arith_induction with
  | hv n => rfl
  | hz => simp only [eval_zero_M, mz_std]; rfl
  | hs t ih => simp only [eval_succ_M, ms_std, ih]; rfl
  | ha t s iht ihs => simp only [eval_add_M, madd_std, iht, ihs, numM_add hM]
  | hm t s iht ihs => simp only [eval_mul_M, mmul_std, iht, ihs, numM_mul hM]

omit hM in
/-- Pushing a numeral value onto a numeral environment. -/
theorem cons_numM (i : Nat) (e : Nat → Nat) :
    Env.cons (numM M i) (fun n => numM M (e n)) = fun n => numM M (Env.cons i e n) := by
  funext n; cases n <;> rfl

/-- **Δ₀-absoluteness.** A bounded formula has the same truth value, under numeral
values, in any model of `Q` as in `ℕ`. -/
theorem D0.absolute {φ : Formula Arith} (h : D0 φ) :
    ∀ e : Nat → Nat, Sat M (fun n => numM M (e n)) φ ↔ Sat stdModel e φ := by
  induction h with
  | eq t s =>
      intro e
      simp only [Sat, eval_numM hM]
      exact ⟨numM_inj hM, fun h => h ▸ rfl⟩
  | le t s =>
      intro e
      rw [substL, sat_subst, sat_subst, sat_leF, sat_leF]
      simp only [List.getD_cons_zero, List.getD_cons_succ, eval_numM hM]
      rw [mle_numM_iff hM, mle_std]
      constructor
      · rintro ⟨i, hi, h⟩; rw [numM_inj hM h]; exact hi
      · intro h; exact ⟨_, h, rfl⟩
  | bot => intro e; exact Iff.rfl
  | imp _ _ ih₁ ih₂ => intro e; simp only [Sat, ih₁ e, ih₂ e]
  | conj _ _ ih₁ ih₂ => intro e; simp only [Sat, ih₁ e, ih₂ e]
  | disj _ _ ih₁ ih₂ => intro e; simp only [Sat, ih₁ e, ih₂ e]
  | ball T _ ih =>
      intro e
      simp only [Sat, sat_boundF, eval_numM hM]
      constructor
      · intro h i hi
        have := h (numM M i) ((mle_numM_iff hM _ _).2 ⟨i, (sat_boundF_std T i e).1 hi, rfl⟩)
        rwa [cons_numM, ih] at this
      · intro h x hx
        obtain ⟨i, hi, rfl⟩ := (mle_numM_iff hM _ _).1 hx
        rw [cons_numM, ih]; exact h i ((sat_boundF_std T i e).2 hi)
  | ballS T _ ih =>
      intro e
      simp only [Sat, sat_boundSF, eval_numM hM]
      constructor
      · intro h i hi
        have := h (numM M i) ((mle_succ_numM_iff hM _ _).2 ⟨i, (sat_boundSF_std T i e).1 hi, rfl⟩)
        rwa [cons_numM, ih] at this
      · intro h x hx
        obtain ⟨i, hi, rfl⟩ := (mle_succ_numM_iff hM _ _).1 hx
        rw [cons_numM, ih]; exact h i ((sat_boundSF_std T i e).2 hi)
  | bex T _ ih =>
      intro e
      simp only [Sat, sat_boundF, eval_numM hM]
      constructor
      · rintro ⟨x, hx, h⟩
        obtain ⟨i, hi, rfl⟩ := (mle_numM_iff hM _ _).1 hx
        rw [cons_numM, ih] at h
        exact ⟨i, (sat_boundF_std T i e).2 hi, h⟩
      · rintro ⟨i, hi, h⟩
        exact ⟨numM M i, (mle_numM_iff hM _ _).2 ⟨i, (sat_boundF_std T i e).1 hi, rfl⟩,
          by rw [cons_numM, ih]; exact h⟩

/-- **Upward absoluteness of Σ₁ formulas.** A Σ₁ formula `∃x φ` (with `φ` bounded)
true in `ℕ` is true, under numeral values, in every model of `Q`. -/
theorem sigma1_upward {φ : Formula Arith} (h : D0 φ) (e : Nat → Nat)
    (ht : Sat stdModel e (ex φ)) : Sat M (fun n => numM M (e n)) (ex φ) := by
  obtain ⟨w, hw⟩ := ht
  exact ⟨numM M w, by rw [cons_numM, D0.absolute hM h]; exact hw⟩

end

/-! ## Provability in `Q` -/

/-- Substituting numerals, semantically. -/
theorem sat_subst_numerals {M : Structure Arith} (φ : Formula Arith) (e : Nat → Nat)
    (e' : Nat → M.Dom) :
    Sat M e' (φ.subst fun n => numeral (e n)) ↔ Sat M (fun n => numM M (e n)) φ := by
  rw [sat_subst]; simp only [eval_numeral_M]

/-- **`Q` proves every true bounded sentence** (here: a bounded formula with numerals
substituted for its free variables). -/
theorem Q_proves_D0 {φ : Formula Arith} (h : D0 φ) (e : Nat → Nat) (ht : Sat stdModel e φ) :
    Q ⊢₁ φ.subst fun n => numeral (e n) :=
  Q_proves_of_models fun _ e' hM => (sat_subst_numerals φ e e').2 ((D0.absolute hM h e).2 ht)

/-- **`Q` refutes every false bounded sentence.** -/
theorem Q_refutes_D0 {φ : Formula Arith} (h : D0 φ) (e : Nat → Nat) (hf : ¬ Sat stdModel e φ) :
    Q ⊢₁ neg (φ.subst fun n => numeral (e n)) :=
  Q_proves_D0 h.neg e hf

/-- **Σ₁-completeness of `Q`.** Every true Σ₁ sentence `∃x φ(x, ā)` (with `φ` bounded
and numerals `ā` for the parameters) is provable in `Q`. -/
theorem Q_proves_sigma1 {φ : Formula Arith} (h : D0 φ) (e : Nat → Nat)
    (ht : Sat stdModel e (ex φ)) : Q ⊢₁ (ex φ).subst fun n => numeral (e n) :=
  Q_proves_of_models fun _ e' hM => (sat_subst_numerals _ e e').2 (sigma1_upward hM h e ht)

end Foundations.Logic.FO
