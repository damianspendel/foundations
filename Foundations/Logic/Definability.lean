import Foundations.Logic.BetaFunction
import Foundations.Logic.NonstandardArithmetic
import Foundations.Logic.Universal

/-!
# Arithmetic can talk about computation

The bridge between computability and arithmetic, at the heart of Gödel's 1931 paper:
**every partial recursive function has an arithmetically definable graph**. For each
code `c` and arity `a` we construct, by recursion on `c`, a formula `gr c a` of the
language `{0, S, +, ×}` with free variables `y, x₀, …, x_{a−1}` (de Bruijn indices
`0, 1, …, a`) such that, in the standard model,

`ℕ ⊨ gr c a [y, x⃗]  ⟺  Eval c [x₀, …, x_{a−1}] y`.

The cases follow the definition of codes:

* zero, successor and projections are equations;
* **composition** `f(g₀(x⃗), …, g_{k−1}(x⃗))` becomes `∃v₀ … ∃v_{k−1} (⋀ᵢ gᵢ(x⃗) = vᵢ ∧ f(v⃗) = y)`;
* **primitive recursion** needs to say "there is a sequence `r₀, …, r_m` with
  `r₀ = f(x⃗)`, `r_{j+1} = g(j, r_j, x⃗)` and `y = r_m`" — here Gödel's **β-function**
  from the previous file replaces the sequence by two numbers `A, B`;
* **minimisation** `μn. f(n, x⃗) = 0` becomes
  `f(y, x⃗) = 0 ∧ ∀ m < y ∃ v (f(m, x⃗) = v ∧ v ≠ 0)`.

Applied to the universal code, this yields a single formula `haltsF(e, x)` that is
true in `ℕ` exactly when program `e` halts on input `x`: *the halting problem is
expressible in the language of arithmetic*. Substituting numerals gives, for each
code `c` and input `x`, a **sentence** (no free variables — checked at the end of the
file) asserting that `c` does not halt on `x`. Since halting is undecidable, so is
arithmetical truth; and this is what drives the incompleteness theorem.

*Scope.* We prove **definability in the standard model** (truth in `ℕ`), which is all
that the incompleteness proof via soundness needs. The stronger statement that these
formulas *represent* the functions inside a weak theory such as Robinson's `Q` (i.e.
that the true instances are provable, which is needed for Gödel's original
syntactic proof and for Rosser's theorem) is not formalised here.
-/

namespace Foundations.Logic.FO

open Arith Formula
open Computability (Code Eval Halts)

/-! ## Building blocks -/

/-- Substitution of a list of terms for the variables `0, 1, 2, …`. -/
def substL (ts : List (Term Arith)) (φ : Formula Arith) : Formula Arith :=
  φ.subst fun n => ts.getD n zero

/-- Satisfaction of a list substitution. -/
theorem sat_substL (ts : List (Term Arith)) (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (substL ts φ) ↔ Sat stdModel (fun n => (ts.getD n zero).eval stdModel e) φ :=
  sat_subst _ _ _

/-- Evaluating a substitution of the form `Env.cons o ins`. -/
theorem eval_cons_subst (o : Term Arith) (ins : Nat → Term Arith) (e : Nat → Nat) :
    (fun n => (Env.cons o ins n).eval stdModel e) =
      Env.cons (o.eval stdModel e) (fun n => (ins n).eval stdModel e) := by
  funext n; cases n <;> rfl

/-- Satisfaction of a substitution of the form `Env.cons o ins`. -/
theorem sat_subst_cons (φ : Formula Arith) (o : Term Arith) (ins : Nat → Term Arith)
    (e : Nat → Nat) : Sat stdModel e (φ.subst (Env.cons o ins)) ↔
      Sat stdModel (Env.cons (o.eval stdModel e) (fun n => (ins n).eval stdModel e)) φ := by
  rw [sat_subst, eval_cons_subst]

/-- `a < b`, as the formula `∃d. a + S d = b` (free variables `0 = a`, `1 = b`). -/
def ltF : Formula Arith := ex (eq (add (v 1) (succ (v 0))) (v 2))

/-- Meaning of `ltF`. -/
theorem sat_ltF (e : Nat → Nat) : Sat stdModel e ltF ↔ e 0 < e 1 := by
  simp only [ltF, Sat, eval_add, eval_succ, Term.eval, Env.cons]
  exact ⟨fun ⟨x, h⟩ => by omega, fun h => ⟨e 1 - e 0 - 1, by omega⟩⟩

/-- `ltF` instantiated at two terms. -/
theorem sat_ltF_substL (t s : Term Arith) (e : Nat → Nat) :
    Sat stdModel e (substL [t, s] ltF) ↔ t.eval stdModel e < s.eval stdModel e := by
  rw [sat_substL, sat_ltF]; rfl

/-- The divisor term `1 + (i + 1)·B` of the β-function, with `i = v 4`, `B = v 3`
(the indices it has inside `betaF`). -/
def betaDiv : Term Arith := add (succ zero) (mul (succ (v 4)) (v 3))

/-- **The β-function as a formula**: `z = β(A, B, i)`, i.e.
`∃q. A = q·(1 + (i + 1)·B) + z ∧ z < 1 + (i + 1)·B`
(free variables `0 = z`, `1 = A`, `2 = B`, `3 = i`). -/
def betaF : Formula Arith :=
  ex (conj (eq (v 2) (add (mul (v 0) betaDiv) (v 1))) (substL [v 1, betaDiv] ltF))

/-- Meaning of `betaF`. -/
theorem sat_betaF (e : Nat → Nat) : Sat stdModel e betaF ↔ e 0 = gbeta (e 1) (e 2) (e 3) := by
  simp only [betaF, Sat, sat_ltF_substL, betaDiv, eval_add, eval_mul, eval_succ, eval_zero,
    Term.eval, Env.cons, gbeta]
  constructor
  · rintro ⟨q, h₁, h₂⟩
    rw [h₁, Nat.add_comm (q * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  · intro h
    refine ⟨e 1 / (0 + 1 + (e 3 + 1) * e 2), ?_, ?_⟩
    · rw [h, Nat.mul_comm]; simp only [Nat.zero_add]; exact (Nat.div_add_mod _ _).symm
    · rw [h]; simp only [Nat.zero_add]; exact Nat.mod_lt _ (by omega)

/-- `betaF` instantiated at four terms. -/
theorem sat_betaF_substL (z A B i : Term Arith) (e : Nat → Nat) :
    Sat stdModel e (substL [z, A, B, i] betaF) ↔
      z.eval stdModel e = gbeta (A.eval stdModel e) (B.eval stdModel e) (i.eval stdModel e) := by
  rw [sat_substL, sat_betaF]; rfl

/-- `exN k φ` prefixes `k` existential quantifiers. -/
def exN : Nat → Formula Arith → Formula Arith
  | 0, φ => φ
  | k + 1, φ => ex (exN k φ)

/-- Meaning of `exN`: some environment agreeing with `e` beyond the first `k`
variables (shifted by `k`) satisfies the body. -/
theorem sat_exN (φ : Formula Arith) :
    ∀ (k : Nat) (e : Nat → Nat),
      Sat stdModel e (exN k φ) ↔ ∃ e' : Nat → Nat, (∀ n, e' (n + k) = e n) ∧ Sat stdModel e' φ
  | 0, e => by
      simp only [exN, Nat.add_zero]
      exact ⟨fun h => ⟨e, fun _ => rfl, h⟩, fun ⟨e', he', h⟩ => by
        rwa [show e = e' from funext fun n => (he' n).symm]⟩
  | k + 1, e => by
      simp only [exN, Sat]
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨e', he', h⟩ := (sat_exN φ k _).1 hx
        refine ⟨e', fun n => ?_, h⟩
        rw [show n + (k + 1) = (n + 1) + k by omega, he' (n + 1)]; rfl
      · rintro ⟨e', he', h⟩
        refine ⟨e' k, (sat_exN φ k _).2 ⟨e', fun n => ?_, h⟩⟩
        cases n with
        | zero => simp [Env.cons]
        | succ m =>
            show e' (m + 1 + k) = e m
            rw [show m + 1 + k = m + (k + 1) by omega]; exact he' m

/-- A finite conjunction (the empty conjunction is `⊥ → ⊥`). -/
def conjL : List (Formula Arith) → Formula Arith
  | [] => imp bot bot
  | φ :: l => conj φ (conjL l)

/-- Meaning of `conjL`. -/
theorem sat_conjL (e : Nat → Nat) :
    ∀ l : List (Formula Arith), Sat stdModel e (conjL l) ↔ ∀ φ ∈ l, Sat stdModel e φ
  | [] => by simp [conjL, Sat]
  | φ :: l => by simp [conjL, Sat, sat_conjL e l]

/-! ## Graphs of partial recursive functions -/

/-- **The graph formula** of code `c` at arity `a`: free variable `0` is the output,
`1, …, a` are the inputs. -/
def gr : Code → Nat → Formula Arith
  | .zero, _ => eq (v 0) zero
  | .succ, a => eq (v 0) (succ (if a = 0 then zero else v 1))
  | .proj i, a => eq (v 0) (if i < a then v (i + 1) else zero)
  | @Code.comp k f gs, a =>
      exN k (conj
        (conjL (List.ofFn fun i : Fin k =>
          (gr (gs i) a).subst (Env.cons (v i) fun j => v (j + 1 + k))))
        ((gr f k).subst (Env.cons (v k) fun j => v j)))
  | .prec _ _, 0 => bot
  | .prec f g, a + 1 =>
      -- under `∃A ∃B`: B = v 0, A = v 1, y = v 2, m = v 3, rest = v 4, v 5, …
      ex (ex (conj (conj
        -- `∃r₀ (r₀ = β(A, B, 0) ∧ f(rest) = r₀)`; here r₀ = v 0, B = v 1, A = v 2
        (ex (conj (substL [v 0, v 2, v 1, zero] betaF)
          ((gr f a).subst (Env.cons (v 0) fun j => v (j + 5)))))
        -- `∀j < m ∃u ∃w (u = β(A,B,j) ∧ w = β(A,B,j+1) ∧ g(j, u, rest) = w)`
        (all (imp (substL [v 0, v 4] ltF)
          -- under `∃u ∃w`: w = v 0, u = v 1, j = v 2, B = v 3, A = v 4, rest = v 7, …
          (ex (ex (conj (conj (substL [v 1, v 4, v 3, v 2] betaF)
              (substL [v 0, v 4, v 3, succ (v 2)] betaF))
            ((gr g (a + 2)).subst (Env.cons (v 0) fun j =>
              match j with
              | 0 => v 2
              | 1 => v 1
              | j + 2 => v (j + 7)))))))))
        -- `y = β(A, B, m)`
        (substL [v 2, v 1, v 0, v 3] betaF)))
  | .mu f, a =>
      conj ((gr f (a + 1)).subst (Env.cons zero (Env.cons (v 0) fun j => v (j + 1))))
        (all (imp (substL [v 0, v 1] ltF)
          (ex (conj ((gr f (a + 1)).subst (Env.cons (v 0) (Env.cons (v 1) fun j => v (j + 3))))
            (neg (eq (v 0) zero))))))

/-- Primitive recursion, unfolded with a β-coded sequence of intermediate values. -/
theorem eval_prec_iff_beta (f g : Code) (xs : List Nat) (m y : Nat) :
    Eval (.prec f g) (m :: xs) y ↔ ∃ A B, Eval f xs (gbeta A B 0) ∧
      (∀ j, j < m → Eval g (j :: gbeta A B j :: xs) (gbeta A B (j + 1))) ∧ y = gbeta A B m := by
  constructor
  · intro h
    -- the values of the recursion below `m`
    have hval : ∀ j, j ≤ m → ∃ r, Eval (.prec f g) (j :: xs) r := by
      intro j hj
      induction m generalizing y with
      | zero => rw [Nat.le_zero.1 hj]; exact ⟨y, h⟩
      | succ m ih =>
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj' | rfl
          · cases h with
            | prec_succ h₁ _ => exact ih _ h₁ (by omega)
          · exact ⟨y, h⟩
    let r : Nat → Nat := fun j => if hj : j ≤ m then Classical.choose (hval j hj) else 0
    have hr : ∀ j (hj : j ≤ m), Eval (.prec f g) (j :: xs) (r j) := fun j hj => by
      simp only [r, hj, dite_true]; exact Classical.choose_spec (hval j hj)
    obtain ⟨A, B, hAB⟩ := beta_lemma m r
    refine ⟨A, B, ?_, fun j hj => ?_, ?_⟩
    · rw [hAB 0 (Nat.zero_le _)]
      cases hr 0 (Nat.zero_le _) with
      | prec_zero h' => exact h'
    · rw [hAB j (by omega), hAB (j + 1) hj]
      cases hr (j + 1) hj with
      | prec_succ h₁ h₂ =>
          rw [Eval.det h₁ (hr j (by omega))] at h₂; exact h₂
    · rw [hAB m (Nat.le_refl _)]; exact Eval.det h (hr m (Nat.le_refl _))
  · rintro ⟨A, B, h₀, hs, rfl⟩
    have : ∀ j, j ≤ m → Eval (.prec f g) (j :: xs) (gbeta A B j) := by
      intro j hj
      induction j with
      | zero => exact .prec_zero h₀
      | succ j ih => exact .prec_succ (ih (by omega)) (hs j (by omega))
    exact this m (Nat.le_refl _)

/-- Minimisation, unfolded. -/
theorem eval_mu_iff (f : Code) (xs : List Nat) (y : Nat) :
    Eval (.mu f) xs y ↔ Eval f (y :: xs) 0 ∧ ∀ m, m < y → ∃ w, Eval f (m :: xs) w ∧ ¬ w = 0 := by
  constructor
  · intro h
    cases h with
    | mu ks h₀ hlt => exact ⟨h₀, fun m hm => ⟨ks m + 1, hlt m hm, by omega⟩⟩
  · rintro ⟨h₀, hlt⟩
    refine .mu (fun m => if hm : m < y then Classical.choose (hlt m hm) - 1 else 0) h₀
      (fun m hm => ?_)
    simp only [hm, dite_true]
    obtain ⟨h₁, h₂⟩ := Classical.choose_spec (hlt m hm)
    rwa [Nat.sub_add_cancel (by omega)]

/-- **Definability of partial recursive functions.** The graph formula `gr c a` is
true in `ℕ` under an environment `e` exactly when `c`, run on the inputs
`e 1, …, e a`, outputs `e 0`. -/
theorem sat_gr : ∀ (c : Code) (a : Nat) (e : Nat → Nat),
    Sat stdModel e (gr c a) ↔ Eval c (List.ofFn fun i : Fin a => e (i + 1)) (e 0)
  | .zero, a, e => by
      simp only [gr, Sat, eval_zero, Term.eval]
      exact ⟨fun h => by rw [h]; exact .zero, fun h => Eval.det h .zero⟩
  | .succ, a, e => by
      simp only [gr, Sat, eval_succ, Term.eval]
      have : (List.ofFn fun i : Fin a => e (i + 1)).headD 0 =
          (if a = 0 then zero else v 1).eval stdModel e := by
        cases a with
        | zero => rfl
        | succ a => simp [List.ofFn_succ]; rfl
      rw [← this]
      exact ⟨fun h => by rw [h]; exact .succ, fun h => Eval.det h .succ⟩
  | .proj i, a, e => by
      simp only [gr, Sat, Term.eval]
      have : (List.ofFn fun i : Fin a => e (i + 1)).getD i 0 =
          (if i < a then v (i + 1) else zero).eval stdModel e := by
        by_cases h : i < a
        · simp [h, List.getD_eq_getElem?_getD]; rfl
        · simp [h, List.getD_eq_getElem?_getD]
      rw [← this]
      exact ⟨fun h => by rw [h]; exact .proj, fun h => Eval.det h .proj⟩
  | @Code.comp k f gs, a, e => by
      simp only [gr, sat_exN, Sat, sat_conjL, List.mem_ofFn, forall_exists_index,
        forall_apply_eq_imp_iff, sat_subst_cons, sat_gr, Term.eval, Env.cons]
      constructor
      · rintro ⟨e', he', hg, hf⟩
        have h0 : e' k = e 0 := by simpa using he' 0
        have hxs : (List.ofFn fun j : Fin a => e' (j + 1 + k)) = List.ofFn fun j : Fin a => e (j + 1) :=
          by congr 1; funext j; exact he' _
        refine .comp (fun i => e' i) (fun i => ?_) ?_
        · have := hg i; rwa [hxs] at this
        · rwa [h0] at hf
      · intro h
        cases h with
        | comp vs hg hf =>
            refine ⟨fun n => if hn : n < k then vs ⟨n, hn⟩ else e (n - k), fun n => ?_, fun i => ?_, ?_⟩
            · have : ¬ (n + k < k) := by omega
              simp [this]
            · simp only [Fin.is_lt, dite_true, show ∀ j : Nat, ¬ (j + 1 + k < k) from fun j => by omega,
                dite_false, show ∀ j : Nat, j + 1 + k - k = j + 1 from fun j => by omega]
              exact hg i
            · simp only [Fin.is_lt, dite_true, Nat.lt_irrefl, dite_false, Nat.sub_self]
              exact hf
  | .prec f g, 0, e => by
      simp only [gr, Sat, List.ofFn_zero, false_iff]
      intro h; cases h
  | .prec f g, a + 1, e => by
      rw [List.ofFn_succ, eval_prec_iff_beta]
      simp only [gr, Sat, sat_substL, sat_betaF, sat_ltF, sat_subst_cons, sat_gr, Term.eval,
        Env.cons, List.getD_cons_zero, List.getD_cons_succ, eval_zero, eval_succ]
      simp only [Fin.val_zero, Fin.val_succ, List.ofFn_succ]
      constructor
      · rintro ⟨A, B, ⟨⟨r₀, hr₀, hf⟩, hs⟩, hy⟩
        refine ⟨A, B, by rw [← hr₀]; exact hf, fun j hj => ?_, hy⟩
        obtain ⟨u, w, ⟨hu, hw⟩, hg⟩ := hs j hj
        rw [← hu, ← hw]; exact hg
      · rintro ⟨A, B, hf, hs, hy⟩
        exact ⟨A, B, ⟨⟨_, rfl, hf⟩, fun j hj => ⟨_, _, ⟨rfl, rfl⟩, hs j hj⟩⟩, hy⟩
  | .mu f, a, e => by
      rw [eval_mu_iff]
      simp only [gr, Sat, sat_ltF_substL, sat_subst_cons, sat_gr, Term.eval, Env.cons, eval_zero,
        List.ofFn_succ, Fin.val_zero, Fin.val_succ]
      rfl

/-! ## Halting is arithmetically definable -/

/-- **The halting formula** `haltsF(e, x)` (free variables `0 = e`, `1 = x`):
"program `e` halts on input `x`", i.e. `∃y. U(e, x) = y`. -/
noncomputable def haltsF : Formula Arith :=
  ex ((gr Computability.U 2).subst (Env.cons (v 0) fun j => v (j + 1)))

/-- **Halting is definable in arithmetic.** `ℕ ⊨ haltsF(e, x)` iff the `e`-th partial
recursive function halts on `x`. -/
theorem sat_haltsF (e : Nat → Nat) :
    Sat stdModel e haltsF ↔ Halts Computability.U [e 0, e 1] := by
  simp only [haltsF, Sat, sat_subst_cons, sat_gr, Term.eval, Env.cons, List.ofFn_succ,
    List.ofFn_zero, Fin.val_zero, Fin.val_succ]
  rfl

/-- The sentence "program `c` does not halt on input `x`": the numerals for `⌜c⌝` and
`x` are substituted into `haltsF` (instantiating its two free variables in turn). -/
noncomputable def nonHaltsF (c : Code) (x : Nat) : Formula Arith :=
  neg ((haltsF.inst (numeral (Computability.encode c))).inst (numeral x))

/-- **Truth of non-halting sentences.** `ℕ ⊨ nonHaltsF c x` (under any environment)
iff `c` does not halt on `x`. -/
theorem sat_nonHaltsF (c : Code) (x : Nat) (e : Nat → Nat) :
    Sat stdModel e (nonHaltsF c x) ↔ ¬ Halts c [x] := by
  simp only [nonHaltsF, sat_neg, sat_inst, sat_haltsF, Env.cons, eval_numeral_std]
  constructor
  · intro h ⟨n, hn⟩; exact h ⟨n, (Computability.phi_encode c x n).2 hn⟩
  · intro h ⟨n, hn⟩; exact h ⟨n, (Computability.phi_encode c x n).1 hn⟩

/-! ## The graph formulas have the expected free variables -/

/-- A substitution acting only on the free variables that actually occur: if every
term substituted for a variable occurring free in `t` avoids `x`, so does `t[σ]`. -/
theorem Term.fresh_subst_of {x : Nat} {σ : Nat → Term Arith} :
    ∀ t : Term Arith, (∀ n, ¬ t.Fresh n → (σ n).Fresh x) → (t.subst σ).Fresh x
  | .var m, h => h m (by simp [Term.Fresh])
  | .func _ ts, h => fun i => Term.fresh_subst_of (ts i) fun n hn => h n fun hf => hn (hf i)

/-- A substitution acting only on the free variables that actually occur (formulas). -/
theorem Formula.fresh_subst_of :
    ∀ (φ : Formula Arith) {x : Nat} {σ : Nat → Term Arith},
      (∀ n, ¬ φ.Fresh n → (σ n).Fresh x) → (φ.subst σ).Fresh x
  | .bot, _, _, _ => trivial
  | .eq t s, _, _, h => ⟨Term.fresh_subst_of t fun n hn => h n fun hf => hn hf.1,
      Term.fresh_subst_of s fun n hn => h n fun hf => hn hf.2⟩
  | .rel R _, _, _, _ => (R : Empty).elim
  | .imp φ ψ, _, _, h => ⟨fresh_subst_of φ fun n hn => h n fun hf => hn hf.1,
      fresh_subst_of ψ fun n hn => h n fun hf => hn hf.2⟩
  | .conj φ ψ, _, _, h => ⟨fresh_subst_of φ fun n hn => h n fun hf => hn hf.1,
      fresh_subst_of ψ fun n hn => h n fun hf => hn hf.2⟩
  | .disj φ ψ, _, _, h => ⟨fresh_subst_of φ fun n hn => h n fun hf => hn hf.1,
      fresh_subst_of ψ fun n hn => h n fun hf => hn hf.2⟩
  | .all φ, x, σ, h | .ex φ, x, σ, h => by
      refine fresh_subst_of φ (x := x + 1) fun n hn => ?_
      cases n with
      | zero => simp only [Subst.lift, Term.Fresh]; omega
      | succ m => exact Term.fresh_rename_succ _ (h m hn)

/-- Freshness under a block of existential quantifiers. -/
theorem fresh_exN (φ : Formula Arith) : ∀ k x, (exN k φ).Fresh x ↔ φ.Fresh (x + k)
  | 0, x => Iff.rfl
  | k + 1, x => by
      simp only [exN, Formula.Fresh]
      rw [fresh_exN φ k (x + 1), show x + 1 + k = x + (k + 1) by omega]

/-- Freshness of a finite conjunction. -/
theorem fresh_conjL (x : Nat) :
    ∀ l : List (Formula Arith), (conjL l).Fresh x ↔ ∀ φ ∈ l, φ.Fresh x
  | [] => by simp [conjL, Formula.Fresh]
  | φ :: l => by simp [conjL, Formula.Fresh, fresh_conjL x l]

/-- A list substitution into a formula whose free variables are among the first
`ts.length` avoids `y` if all the substituted terms do. -/
theorem fresh_substL {φ : Formula Arith} {m : Nat} (hφ : ∀ n, m ≤ n → φ.Fresh n)
    {ts : List (Term Arith)} (hlen : m ≤ ts.length) {y : Nat} (hts : ∀ t ∈ ts, t.Fresh y) :
    (substL ts φ).Fresh y := by
  refine Formula.fresh_subst_of φ fun n hn => ?_
  have : n < ts.length := Classical.byContradiction fun h => hn (hφ n (by omega))
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
  exact hts _ (List.getElem_mem this)

/-- Freshness of a sum term. -/
theorem fresh_add (t s : Term Arith) (x : Nat) : (add t s).Fresh x ↔ t.Fresh x ∧ s.Fresh x := by
  simp only [add, Term.Fresh, args₂]
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h₁, h₂⟩ i
    match i with
    | ⟨0, _⟩ => exact h₁
    | ⟨1, _⟩ => exact h₂

/-- Freshness of a product term. -/
theorem fresh_mul (t s : Term Arith) (x : Nat) : (mul t s).Fresh x ↔ t.Fresh x ∧ s.Fresh x := by
  simp only [mul, Term.Fresh, args₂]
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h₁, h₂⟩ i
    match i with
    | ⟨0, _⟩ => exact h₁
    | ⟨1, _⟩ => exact h₂

/-- Freshness of a successor term. -/
theorem fresh_succ (t : Term Arith) (x : Nat) : (succ t).Fresh x ↔ t.Fresh x :=
  ⟨fun h => h 0, fun h _ => h⟩

/-- Freshness of a variable. -/
theorem fresh_var (n x : Nat) : (v n).Fresh x ↔ n ≠ x := Iff.rfl

/-- `0` is closed. -/
theorem fresh_zero (x : Nat) : (zero : Term Arith).Fresh x ↔ True :=
  ⟨fun _ => trivial, fun _ i => i.elim0⟩

/-- `ltF` has free variables among `0, 1`. -/
theorem ltF_fresh : ∀ n, 2 ≤ n → ltF.Fresh n := by
  intro n hn; simp only [ltF, Formula.Fresh, fresh_add, fresh_succ, fresh_var]; omega

/-- `betaF` has free variables among `0, 1, 2, 3`. -/
theorem betaF_fresh : ∀ n, 4 ≤ n → betaF.Fresh n := by
  intro n hn
  have hD : ∀ m, 5 ≤ m → betaDiv.Fresh m := by
    intro m hm
    simp only [betaDiv, fresh_add, fresh_mul, fresh_succ, fresh_var, fresh_zero, true_and]; omega
  simp only [betaF, Formula.Fresh, fresh_add, fresh_mul, fresh_var]
  refine ⟨?_, fresh_substL ltF_fresh (by simp) ?_⟩
  · exact ⟨by omega, ⟨by omega, hD _ (by omega)⟩, by omega⟩
  intro t ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl
  · simp only [fresh_var]; omega
  · exact hD _ (by omega)

/-- Numerals and `0` are closed. -/
theorem zero_fresh (x : Nat) : (zero : Term Arith).Fresh x := fun i => i.elim0

/-- Variables other than `x` avoid `x`. -/
theorem var_fresh {n x : Nat} (h : n ≠ x) : (v n).Fresh x := h

/-- **The graph formula `gr c a` has its free variables among `0, …, a`.** -/
theorem gr_fresh : ∀ (c : Code) (a x : Nat), a < x → (gr c a).Fresh x
  | .zero, a, x, h => ⟨var_fresh (by omega), zero_fresh x⟩
  | .succ, a, x, h => by
      refine ⟨var_fresh (by omega), fun _ => ?_⟩
      split
      · exact zero_fresh x
      · exact var_fresh (by omega)
  | .proj i, a, x, h => by
      refine ⟨var_fresh (by omega), ?_⟩
      split
      · exact var_fresh (by omega)
      · exact zero_fresh x
  | @Code.comp k f gs, a, x, h => by
      simp only [gr]
      rw [fresh_exN]
      refine ⟨(fresh_conjL _ _).2 fun φ hφ => ?_, ?_⟩
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
        refine Formula.fresh_subst_of _ fun n hn => ?_
        have hn' : n ≤ a := Classical.byContradiction fun h' => hn (gr_fresh (gs i) a n (by omega))
        cases n with
        | zero => exact var_fresh (by have := i.isLt; omega)
        | succ j => exact var_fresh (by omega)
      · refine Formula.fresh_subst_of _ fun n hn => ?_
        have hn' : n ≤ k := Classical.byContradiction fun h' => hn (gr_fresh f k n (by omega))
        cases n with
        | zero => exact var_fresh (by omega)
        | succ j => exact var_fresh (by omega)
  | .prec f g, 0, x, h => trivial
  | .prec f g, a + 1, x, h => by
      simp only [gr, Formula.Fresh]
      refine ⟨⟨⟨fresh_substL betaF_fresh (by simp) ?_, Formula.fresh_subst_of _ fun n hn => ?_⟩,
        fresh_substL ltF_fresh (by simp) ?_, ⟨fresh_substL betaF_fresh (by simp) ?_, fresh_substL betaF_fresh (by simp) ?_⟩,
        Formula.fresh_subst_of _ fun n hn => ?_⟩, fresh_substL betaF_fresh (by simp) ?_⟩
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> first | exact zero_fresh _ | exact var_fresh (by omega)
      · have hn' : n ≤ a := Classical.byContradiction fun h' => hn (gr_fresh f a n (by omega))
        cases n with
        | zero => exact var_fresh (by omega)
        | succ j => exact var_fresh (by omega)
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl <;> exact var_fresh (by omega)
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> exact var_fresh (by omega)
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact var_fresh (by omega)
        · exact var_fresh (by omega)
        · exact var_fresh (by omega)
        · intro _; exact var_fresh (by omega)
      · have hn' : n ≤ a + 2 := Classical.byContradiction fun h' => hn (gr_fresh g (a + 2) n (by omega))
        match n, hn' with
        | 0, _ => exact var_fresh (by omega)
        | 1, _ => exact var_fresh (by omega)
        | 2, _ => exact var_fresh (by omega)
        | j + 3, _ => exact var_fresh (by omega)
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> exact var_fresh (by omega)
  | .mu f, a, x, h => by
      simp only [gr, Formula.Fresh]
      refine ⟨Formula.fresh_subst_of _ fun n hn => ?_, fresh_substL ltF_fresh (by simp) ?_,
        Formula.fresh_subst_of _ fun n hn => ?_, ⟨var_fresh (by omega), zero_fresh _⟩, trivial⟩
      · have hn' : n ≤ a + 1 := Classical.byContradiction fun h' => hn (gr_fresh f (a + 1) n (by omega))
        match n, hn' with
        | 0, _ => exact zero_fresh _
        | 1, _ => exact var_fresh (by omega)
        | j + 2, _ => exact var_fresh (by omega)
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl <;> exact var_fresh (by omega)
      · have hn' : n ≤ a + 1 := Classical.byContradiction fun h' => hn (gr_fresh f (a + 1) n (by omega))
        match n, hn' with
        | 0, _ => exact var_fresh (by omega)
        | 1, _ => exact var_fresh (by omega)
        | j + 2, _ => exact var_fresh (by omega)

/-- `haltsF` has its free variables among `0, 1`. -/
theorem haltsF_fresh : ∀ x, 2 ≤ x → haltsF.Fresh x := by
  intro x hx
  refine Formula.fresh_subst_of _ fun n hn => ?_
  have hn' : n ≤ 2 := Classical.byContradiction fun h' => hn (gr_fresh _ 2 n (by omega))
  cases n with
  | zero => exact var_fresh (by omega)
  | succ j => exact var_fresh (by omega)

/-- Numerals are closed terms. -/
theorem numeral_fresh (x : Nat) : ∀ n, (numeral n).Fresh x
  | 0 => zero_fresh x
  | n + 1 => fun _ => numeral_fresh x n

/-- A formula is a **sentence** if no variable occurs free in it. -/
def IsSentence (φ : Formula Arith) : Prop := ∀ x, φ.Fresh x

/-- **The non-halting formulas are sentences.** -/
theorem nonHaltsF_sentence (c : Code) (x : Nat) : IsSentence (nonHaltsF c x) := by
  intro y
  refine ⟨Formula.fresh_subst_of _ fun n hn => ?_, trivial⟩
  cases n with
  | zero => exact numeral_fresh _ _
  | succ m =>
      refine var_fresh fun hm => hn ?_
      subst hm
      refine Formula.fresh_subst_of _ fun n hn' => ?_
      cases n with
      | zero => exact numeral_fresh _ _
      | succ m' =>
          refine var_fresh fun hm' => hn' ?_
          subst hm'
          exact haltsF_fresh _ (by omega)

end Foundations.Logic.FO
