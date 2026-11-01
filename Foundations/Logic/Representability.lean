import Foundations.Logic.BoundedGraphs

/-!
# Representability in Robinson's `Q`

A set `P ⊆ ℕ` is **represented** in a theory `T` by a formula `R(x)` if `T` proves
`R(n̄)` for every `n ∈ P` and refutes it for every `n ∉ P`. A total function `f` is
represented by `F(y, x)` if `T` proves that `f(n)‾` is the *unique* `y` with
`F(y, n̄)`. Gödel's 1931 paper proved, in effect, that every primitive recursive
function is representable; we prove that **every decidable set and every total
computable function is representable in `Q`** — and hence in every theory
containing `Q`, PA in particular.

The natural candidates — the Σ₁ graph formulas `∃w grb c 1` — are not enough by
themselves: `Q` proves their true instances (Σ₁-completeness), but cannot refute the
false ones, since a non-standard model may contain a non-standard "computation"
yielding a wrong value. The cure is a beautiful trick due to **Rosser** (1936):
*compare witnesses*. Given two bounded formulas `A(w, x)` and `B(w, x)` such that
`∃w A(w, n)` and `∃w B(w, n)` are never both true, consider

`Sep(x) := ∃w (A(w, x) ∧ ∀u ≤ w ¬B(u, x))`  — "an `A`-witness comes no later than any `B`-witness".

If `∃w A(w, n)` is true, `Sep(n̄)` is a true Σ₁ sentence, hence `Q`-provable. If
`∃w B(w, n)` is true, with standard witness `w₁`, then in any model of `Q` a witness
`w` for `Sep(n̄)` is either `≤ w̄₁` — then it is standard and `A(w, n)` would be true,
impossible — or `≥ w̄₁`, and then `¬B(w̄₁, n̄)` contradicts the truth of `B(w₁, n)`.
So `Q` refutes `Sep(n̄)`. This **Rosser separation lemma** (`rosser_sep`) gives the
representability of decidable sets directly, and with a similar witness comparison
the representability of total functions (`represent_function`), which is what the
diagonal lemma needs.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula
open Computability (Code Eval Halts)

/-! ## Environments of two numbers -/

/-- The environment `0 ↦ a`, `1 ↦ b`, everything else `↦ 0`. -/
def penv (a b : Nat) : Nat → Nat := fun k => [a, b].getD k 0

/-- A two-term list substitution under numeral values. -/
theorem eval_substL2 {M : Structure Arith} (t₀ t₁ : Term Arith) (E : Nat → M.Dom) {a b : Nat}
    (h₀ : t₀.eval M E = numM M a) (h₁ : t₁.eval M E = numM M b) :
    (fun k => ([t₀, t₁].getD k zero).eval M E) = fun k => numM M (penv a b k) := by
  funext k
  match k with
  | 0 => simpa [penv] using h₀
  | 1 => simpa [penv] using h₁
  | k + 2 => simp [penv]; rfl

/-! ## The Rosser separation lemma -/

/-- The **Rosser separation formula** `∃w (A(w, x) ∧ ∀u ≤ w ¬B(u, x))` for formulas `A`,
`B` with free variables `0 = w`, `1 = x` (free variable of the result: `0 = x`). -/
def sepF (A B : Formula Arith) : Formula Arith :=
  ex (conj (substL [v 0, v 1] A) (all (imp (boundF (v 0)) (neg (substL [v 0, v 2] B)))))

/-- `A(w, n)` in `ℕ`. -/
def holds (A : Formula Arith) (w n : Nat) : Prop := Sat stdModel (penv w n) A

/-- Unfolding the separation formula, at an element `x` of a structure. -/
theorem sat_sepF {M : Structure Arith} (A B : Formula Arith) (x : M.Dom) (e : Nat → M.Dom) :
    Sat M (Env.cons x e) (sepF A B) ↔ ∃ w, Sat M (fun k => [w, x].getD k (mz M)) A ∧
      ∀ u, mle M u w → ¬ Sat M (fun k => [u, x].getD k (mz M)) B := by
  simp only [sepF, Sat, substL, sat_subst, sat_boundF, sat_neg]
  have h₁ : ∀ w, (fun k => ([v 0, v 1].getD k zero).eval M (Env.cons w (Env.cons x e))) =
      fun k => [w, x].getD k (mz M) := by
    intro w; funext k; match k with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => simp
  have h₂ : ∀ w u, (fun k => ([v 0, v 2].getD k zero).eval M (Env.cons u (Env.cons w (Env.cons x e)))) =
      fun k => [u, x].getD k (mz M) := by
    intro w u; funext k; match k with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => simp
  simp only [h₁, h₂, eval_var_M, Env.cons]

/-- Numeral environments of two values. -/
theorem penv_numM {M : Structure Arith} (a b : Nat) :
    (fun k => [numM M a, numM M b].getD k (mz M)) = fun k => numM M (penv a b k) := by
  funext k; match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 => simp [penv]; rfl

/-- **The Rosser separation lemma.** Let `A(w, x)` and `B(w, x)` be bounded formulas
such that for no `n` both `∃w A(w, n)` and `∃w B(w, n)` hold in `ℕ`. Then `Q` proves
`Sep(n̄)` whenever `∃w A(w, n)` is true, and refutes it whenever `∃w B(w, n)` is true. -/
theorem rosser_sep {A B : Formula Arith} (hA : D0 A) (hB : D0 B)
    (hdisj : ∀ n w u, holds A w n → holds B u n → False) (n : Nat) :
    ((∃ w, holds A w n) → Q ⊢₁ (sepF A B).inst (numeral n)) ∧
    ((∃ w, holds B w n) → Q ⊢₁ neg ((sepF A B).inst (numeral n))) := by
  constructor
  · rintro ⟨w, hw⟩
    refine Q_proves_of_models fun M e hM => ?_
    rw [sat_inst, eval_numeral_M, sat_sepF]
    refine ⟨numM M w, ?_, fun u hu hBu => ?_⟩
    · rw [penv_numM, D0.absolute hM hA]; exact hw
    · obtain ⟨i, hi, rfl⟩ := (mle_numM_iff hM _ _).1 hu
      rw [penv_numM, D0.absolute hM hB] at hBu
      exact hdisj n w i hw hBu
  · rintro ⟨w₁, hw₁⟩
    refine Q_proves_of_models fun M e hM => ?_
    rw [sat_neg, sat_inst, eval_numeral_M, sat_sepF]
    rintro ⟨w, hAw, hBw⟩
    rcases mle_numM_or hM w w₁ with h | h
    · obtain ⟨i, -, rfl⟩ := (mle_numM_iff hM _ _).1 h
      rw [penv_numM, D0.absolute hM hA] at hAw
      exact hdisj n i w₁ hAw hw₁
    · refine hBw _ h ?_
      rw [penv_numM, D0.absolute hM hB]; exact hw₁

/-- The separation formula has free variable `0` only, if `A` and `B` have free
variables among `0, 1`. -/
theorem sepF_fresh {A B : Formula Arith} (hA : ∀ n, 2 ≤ n → A.Fresh n)
    (hB : ∀ n, 2 ≤ n → B.Fresh n) : ∀ x, 1 ≤ x → (sepF A B).Fresh x := by
  intro x hx
  refine ⟨fresh_substL hA (by simp) ?_, boundF_var_fresh (by omega) (by omega),
    fresh_substL hB (by simp) ?_, trivial⟩
  · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl <;> exact var_fresh (by omega)
  · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl <;> exact var_fresh (by omega)

/-! ## Representability of decidable sets -/

/-- The bounded formula "`c` outputs `k` on `x` within bound `w`" (free variables
`0 = w`, `1 = x`). -/
def outF (c : Code) (k : Nat) : Formula Arith :=
  (grb c 1).subst (Env.cons (numeral k) (Env.cons (v 1) fun _ => v 0))

/-- `outF` is bounded. -/
theorem outF_D0 (c : Code) (k : Nat) : D0 (outF c k) := (grb_D0 c 1).subst _

/-- Meaning of `outF`. -/
theorem holds_outF (c : Code) (k w n : Nat) : holds (outF c k) w n ↔ EvalB w c [n] k := by
  rw [holds, outF, sat_subst, sat_grb]
  simp [penv, Env.cons, List.ofFn_succ, eval_numeral_std]

/-- `outF c k` has free variables among `0, 1`. -/
theorem outF_fresh (c : Code) (k : Nat) : ∀ n, 2 ≤ n → (outF c k).Fresh n := by
  intro n hn
  refine Formula.fresh_subst_of _ fun m _ => ?_
  match m with
  | 0 => exact numeral_fresh _ _
  | 1 => exact var_fresh (by omega)
  | m + 2 => exact var_fresh (by omega)

/-- **Representability of decidable sets in `Q`.** If a code `c` computes the
characteristic function of `p : ℕ → Bool`, there is a formula `R(x)` with only the
free variable `x`, such that `Q ⊢ R(n̄)` when `p n` and `Q ⊢ ¬R(n̄)` otherwise. -/
theorem decidable_representable {p : Nat → Bool} {c : Code} (hc : ∀ n, Eval c [n] (p n).toNat) :
    ∃ R : Formula Arith, (∀ x, 1 ≤ x → R.Fresh x) ∧ ∀ n,
      (p n = true → Q ⊢₁ R.inst (numeral n)) ∧ (p n = false → Q ⊢₁ neg (R.inst (numeral n))) := by
  have hdisj : ∀ n w u, holds (outF c 1) w n → holds (outF c 0) u n → False := by
    intro n w u h₁ h₀
    rw [holds_outF] at h₁ h₀
    exact absurd (Eval.det h₁.sound h₀.sound) (by omega)
  refine ⟨sepF (outF c 1) (outF c 0), sepF_fresh (outF_fresh c 1) (outF_fresh c 0), fun n => ?_⟩
  have hs := rosser_sep (outF_D0 c 1) (outF_D0 c 0) hdisj n
  constructor
  · intro hp
    refine hs.1 ?_
    obtain ⟨w, hw⟩ := EvalB.complete (hc n)
    exact ⟨w, (holds_outF ..).2 (by simpa [hp] using hw)⟩
  · intro hp
    refine hs.2 ?_
    obtain ⟨w, hw⟩ := EvalB.complete (hc n)
    exact ⟨w, (holds_outF ..).2 (by simpa [hp] using hw)⟩

/-! ## Representability of total functions -/

/-- The formula representing the function computed by `c` (free variables `0 = y`,
`1 = x`):
`∃w (y ≤ w ∧ c(x) = y within w ∧ ∀u ≤ w ∀z ≤ w (c(x) = z within u → z = y))`. -/
def funF (c : Code) : Formula Arith :=
  ex (conj (substL [v 1, v 0] leF) (conj
    ((grb c 1).subst (Env.cons (v 1) (Env.cons (v 2) fun _ => v 0)))
    (all (imp (boundF (v 0)) (all (imp (boundF (v 1))
      (imp ((grb c 1).subst (Env.cons (v 0) (Env.cons (v 4) fun _ => v 1))) (eq (v 0) (v 3)))))))))

/-- A three-valued numeral environment for `grb c 1`. -/
theorem env3_numM {M : Structure Arith} (y x w : Nat) :
    (Env.cons (numM M y) (Env.cons (numM M x) fun _ => numM M w)) =
      fun k => numM M (Env.cons y (Env.cons x fun _ => w) k) := by
  funext k; match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 => rfl

/-- `grb c 1` at a three-valued environment in `ℕ`. -/
theorem sat_grb1 (c : Code) (y x w : Nat) :
    Sat stdModel (Env.cons (α := Nat) y (Env.cons x fun _ => w)) (grb c 1) ↔ EvalB w c [x] y := by
  rw [sat_grb]; simp [Env.cons, List.ofFn_succ]

/-- **Representability of total functions in `Q`** (semantic form). If `c` computes
the total function `f`, then in every model of `Q`, for every numeral `n̄`, the
element `y` satisfies `funF c (y, n̄)` iff `y = f(n)‾`. -/
theorem sat_funF {c : Code} {f : Nat → Nat} (hc : ∀ n, Eval c [n] (f n)) {M : Structure Arith}
    (hM : IsQModel M) (n : Nat) (y : M.Dom) (e : Nat → M.Dom) :
    Sat M (Env.cons y (Env.cons (numM M n) e)) (funF c) ↔ y = numM M (f n) := by
  obtain ⟨w₀', hw₀'⟩ := EvalB.complete (hc n)
  let w₀ := max w₀' (f n)
  have hw₀ : EvalB w₀ c [n] (f n) := EvalB.mono (Nat.le_max_left _ _) hw₀'
  have hfw : f n ≤ w₀ := Nat.le_max_right _ _
  -- the graph formula at numeral values
  have gr_abs : ∀ y x w : Nat, Sat M (Env.cons (numM M y) (Env.cons (numM M x) fun _ => numM M w))
      (grb c 1) ↔ EvalB w c [x] y := by
    intro y x w
    rw [env3_numM, D0.absolute hM (grb_D0 c 1)]; exact sat_grb1 c y x w
  simp only [funF, Sat, substL, sat_subst, sat_leF, sat_boundF, eval_var_M,
    List.getD_cons_zero, List.getD_cons_succ]
  have hsub : ∀ (a b d : M.Dom), (fun k => (Env.cons (v 1) (Env.cons (v 2) fun _ => v 0) k).eval M
      (Env.cons d (Env.cons a (Env.cons b e)))) = Env.cons a (Env.cons b fun _ => d) := by
    intro a b d; funext k; match k with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => rfl
  have hsub' : ∀ (a b d u z : M.Dom), (fun k => (Env.cons (v 0) (Env.cons (v 4) fun _ => v 1) k).eval M
      (Env.cons z (Env.cons u (Env.cons d (Env.cons a (Env.cons b e)))))) =
        Env.cons z (Env.cons b fun _ => u) := by
    intro a b d u z; funext k; match k with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => rfl
  simp only [hsub, hsub']
  constructor
  · rintro ⟨w, hyw, hG, hall⟩
    rcases mle_numM_or hM w w₀ with h | h
    · obtain ⟨i, -, rfl⟩ := (mle_numM_iff hM _ _).1 h
      obtain ⟨j, -, rfl⟩ := (mle_numM_iff hM _ _).1 hyw
      rw [gr_abs] at hG
      rw [Eval.det hG.sound (hc n)]
    · have hz : mle M (numM M (f n)) w := mle_numM_trans hM hfw h
      exact (hall _ h _ hz ((gr_abs _ _ _).2 hw₀)).symm
  · rintro rfl
    refine ⟨numM M w₀, (mle_numM_iff hM _ _).2 ⟨_, hfw, rfl⟩, (gr_abs _ _ _).2 hw₀, ?_⟩
    intro u hu z hz hG
    obtain ⟨i, -, rfl⟩ := (mle_numM_iff hM _ _).1 hu
    obtain ⟨j, -, rfl⟩ := (mle_numM_iff hM _ _).1 hz
    rw [gr_abs] at hG
    show numM M j = numM M (f n)
    rw [Eval.det hG.sound (hc n)]

/-- `funF c` has free variables among `0, 1`. -/
theorem funF_fresh (c : Code) : ∀ x, 2 ≤ x → (funF c).Fresh x := by
  intro x hx
  have hvar : ∀ m k, m ≠ k → (v m).Fresh k := fun m k h => h
  refine ⟨fresh_substL leF_fresh (by simp) ?_, Formula.fresh_subst_of _ fun m _ => ?_,
    boundF_var_fresh (by omega) (by omega), boundF_var_fresh (by omega) (by omega),
    Formula.fresh_subst_of _ fun m _ => ?_, hvar _ _ (by omega), hvar _ _ (by omega)⟩
  · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl <;> exact var_fresh (by omega)
  · match m with
    | 0 => exact var_fresh (by omega)
    | 1 => exact var_fresh (by omega)
    | m + 2 => exact var_fresh (by omega)
  · match m with
    | 0 => exact var_fresh (by omega)
    | 1 => exact var_fresh (by omega)
    | m + 2 => exact var_fresh (by omega)

/-- **Representability of total functions in `Q`** (provability form): `Q` proves
`F(f(n)‾, n̄)` and `∀y (F(y, n̄) → y = f(n)‾)`. -/
theorem represent_function {c : Code} {f : Nat → Nat} (hc : ∀ n, Eval c [n] (f n)) (n : Nat) :
    (Q ⊢₁ (funF c).subst (Env.cons (numeral (f n)) fun _ => numeral n)) ∧
    (Q ⊢₁ all (imp ((funF c).subst (Env.cons (v 0) fun _ => numeral n)) (eq (v 0) (numeral (f n))))) := by
  constructor
  · refine Q_proves_of_models fun M e hM => ?_
    rw [sat_subst]
    have : (fun k => (Env.cons (numeral (f n)) (fun _ => numeral n) k).eval M e) =
        Env.cons (numM M (f n)) (Env.cons (numM M n) fun _ => numM M n) := by
      funext k; match k with
        | 0 => simp [Env.cons]
        | 1 => simp [Env.cons]
        | k + 2 => simp [Env.cons]
    rw [this, sat_funF hc hM]
  · refine Q_proves_of_models fun M e hM => ?_
    intro y hy
    simp only [Sat, eval_var_M, Env.cons, eval_numeral_M] at hy ⊢
    rw [sat_subst] at hy
    have : (fun k => (Env.cons (v 0) (fun _ => numeral n) k).eval M (Env.cons y e)) =
        Env.cons y (Env.cons (numM M n) fun _ => numM M n) := by
      funext k; match k with
        | 0 => rfl
        | 1 => simp [Env.cons]
        | k + 2 => simp [Env.cons]
    rw [this, sat_funF hc hM] at hy
    exact hy

/-! ## Σ₁-completeness for computations -/

/-- The Σ₁ formula "`c` outputs `y` on `x`" (free variables `0 = y`, `1 = x`):
`∃w grb c 1 (y, x, w)`. -/
def evalSigma (c : Code) : Formula Arith :=
  ex ((grb c 1).subst (Env.cons (v 1) (Env.cons (v 2) fun _ => v 0)))

/-- `evalSigma` is a Σ₁ formula: an existential quantifier over a bounded formula. -/
theorem evalSigma_D0 (c : Code) : D0 ((grb c 1).subst (Env.cons (v 1) (Env.cons (v 2) fun _ => v 0))) :=
  (grb_D0 c 1).subst _

/-- Meaning of `evalSigma` in `ℕ`. -/
theorem sat_evalSigma (c : Code) (y x : Nat) :
    Sat stdModel (penv y x) (evalSigma c) ↔ Eval c [x] y := by
  rw [eval_iff_exists_evalB]
  simp only [evalSigma, Sat, sat_subst]
  refine exists_congr fun w => ?_
  have : (fun k => (Env.cons (v 1) (Env.cons (v 2) fun _ => v 0) k).eval stdModel
      (Env.cons w (penv y x))) = Env.cons (α := Nat) y (Env.cons x fun _ => w) := by
    funext k; match k with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => rfl
  rw [this, sat_grb1]

/-- **Σ₁-completeness for computations.** Every true statement "`c` outputs `y` on
`x`" is provable in `Q` (in the Σ₁ form `evalSigma`, with numerals for `y` and `x`). -/
theorem Q_proves_eval {c : Code} {x y : Nat} (h : Eval c [x] y) :
    Q ⊢₁ (evalSigma c).subst fun n => numeral (penv y x n) :=
  Q_proves_sigma1 (evalSigma_D0 c) (penv y x) ((sat_evalSigma c y x).2 h)

end Foundations.Logic.FO
