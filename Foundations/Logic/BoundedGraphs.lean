import Foundations.Logic.Delta0

/-!
# Bounded graph formulas: computation as a Σ₁ property

The graph formulas `gr c a` of `Definability` say "there is a computation of `c` on
`x⃗` with output `y`" with *unbounded* quantifiers over the intermediate values and the
β-codes of sequences. To bring the machinery of the previous file to bear, we write a
second family `grb c a` of graph formulas in which **every quantifier is bounded** by
one extra free variable `w` (index `a + 1`): "there is a computation all of whose
ingredients are at most `w`". These formulas are bounded (`D0`), and

`Eval c x⃗ y  ⟺  ∃w. ℕ ⊨ grb c a [y, x⃗, w]`,

so the graph of every partial recursive function is **Σ₁** — of the form `∃w φ` with
`φ` bounded. The proof splits into a purely syntactic part (the formula means a
*bounded evaluation* relation `EvalB w`, defined by recursion on codes) and a purely
semantic part (bounded evaluation is evaluation, and every evaluation is bounded by
some `w`; moreover bounded evaluation is monotone in `w`).
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula
open Computability (Code Eval Halts)

/-! ## Bounded evaluation -/

/-- **Bounded evaluation**: `EvalB w c xs y` says that `c` outputs `y` on `xs` by a
computation all of whose intermediate values (and β-codes of sequences) are `≤ w`. -/
def EvalB (w : Nat) : Code → List Nat → Nat → Prop
  | .zero, _, y => y = 0
  | .succ, xs, y => y = xs.headD 0 + 1
  | .proj i, xs, y => y = xs.getD i 0
  | @Code.comp k f gs, xs, y => ∃ vs : Fin k → Nat, (∀ i, vs i ≤ w) ∧
      (∀ i, EvalB w (gs i) xs (vs i)) ∧ EvalB w f (List.ofFn vs) y
  | .prec _ _, [], _ => False
  | .prec f g, m :: rest, y => ∃ A, A ≤ w ∧ ∃ B, B ≤ w ∧
      ((∃ r, r ≤ w ∧ r = gbeta A B 0 ∧ EvalB w f rest r) ∧
        ∀ j, j < m → ∃ u, u ≤ w ∧ ∃ z, z ≤ w ∧ (u = gbeta A B j ∧ z = gbeta A B (j + 1)) ∧
          EvalB w g (j :: u :: rest) z) ∧ y = gbeta A B m
  | .mu f, xs, y => EvalB w f (y :: xs) 0 ∧ ∀ m, m < y → ∃ z, z ≤ w ∧ EvalB w f (m :: xs) z ∧ ¬ z = 0

/-- Bounded evaluation is evaluation. -/
theorem EvalB.sound {w : Nat} : ∀ {c : Code} {xs : List Nat} {y : Nat}, EvalB w c xs y → Eval c xs y
  | .zero, _, _, h => by simp only [EvalB] at h; subst h; exact .zero
  | .succ, _, _, h => by simp only [EvalB] at h; subst h; exact .succ
  | .proj _, _, _, h => by simp only [EvalB] at h; subst h; exact .proj
  | @Code.comp _ f gs, _, _, h => by
      obtain ⟨vs, -, hg, hf⟩ := h
      exact .comp vs (fun i => EvalB.sound (hg i)) (EvalB.sound hf)
  | .prec _ _, [], _, h => h.elim
  | .prec f g, m :: rest, y, h => by
      obtain ⟨A, -, B, -, ⟨⟨r, -, rfl, hf⟩, hs⟩, rfl⟩ := h
      refine (eval_prec_iff_beta f g rest m _).2 ⟨A, B, EvalB.sound hf, fun j hj => ?_, rfl⟩
      obtain ⟨u, -, z, -, ⟨rfl, rfl⟩, hg⟩ := hs j hj
      exact EvalB.sound hg
  | .mu f, xs, y, h => by
      obtain ⟨h₀, hlt⟩ := h
      refine (eval_mu_iff f xs y).2 ⟨EvalB.sound h₀, fun m hm => ?_⟩
      obtain ⟨z, -, hz, hz0⟩ := hlt m hm
      exact ⟨z, EvalB.sound hz, hz0⟩

/-- Bounded evaluation is monotone in the bound. -/
theorem EvalB.mono {w w' : Nat} (hw : w ≤ w') :
    ∀ {c : Code} {xs : List Nat} {y : Nat}, EvalB w c xs y → EvalB w' c xs y
  | .zero, _, _, h => h
  | .succ, _, _, h => h
  | .proj _, _, _, h => h
  | @Code.comp _ f gs, _, _, h => by
      obtain ⟨vs, hb, hg, hf⟩ := h
      exact ⟨vs, fun i => Nat.le_trans (hb i) hw, fun i => EvalB.mono hw (hg i), EvalB.mono hw hf⟩
  | .prec _ _, [], _, h => h.elim
  | .prec f g, m :: rest, y, h => by
      obtain ⟨A, hA, B, hB, ⟨⟨r, hr, e, hf⟩, hs⟩, hy⟩ := h
      refine ⟨A, by omega, B, by omega, ⟨⟨r, by omega, e, EvalB.mono hw hf⟩, fun j hj => ?_⟩, hy⟩
      obtain ⟨u, hu, z, hz, e', hg⟩ := hs j hj
      exact ⟨u, by omega, z, by omega, e', EvalB.mono hw hg⟩
  | .mu f, xs, y, h => by
      obtain ⟨h₀, hlt⟩ := h
      refine ⟨EvalB.mono hw h₀, fun m hm => ?_⟩
      obtain ⟨z, hz, hz', hz0⟩ := hlt m hm
      exact ⟨z, by omega, EvalB.mono hw hz', hz0⟩

/-- A common bound for finitely many monotone properties indexed by `j < m`. -/
theorem exists_bound_range (P : Nat → Nat → Prop) (hP : ∀ j x x', x ≤ x' → P j x → P j x') :
    ∀ m, (∀ j, j < m → ∃ x, P j x) → ∃ x, ∀ j, j < m → P j x
  | 0, _ => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, h => by
      obtain ⟨x₁, hx₁⟩ := exists_bound_range P hP m fun j hj => h j (by omega)
      obtain ⟨x₂, hx₂⟩ := h m (by omega)
      refine ⟨max x₁ x₂, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hP j _ _ (Nat.le_max_left _ _) (hx₁ j hj)
      · exact hP j _ _ (Nat.le_max_right _ _) hx₂

/-- **Every computation is bounded.** -/
theorem EvalB.complete : ∀ {c : Code} {xs : List Nat} {y : Nat}, Eval c xs y → ∃ w, EvalB w c xs y
  | .zero, _, _, h => ⟨0, by cases h; rfl⟩
  | .succ, _, _, h => ⟨0, by cases h; rfl⟩
  | .proj _, _, _, h => ⟨0, by cases h; rfl⟩
  | @Code.comp k f gs, xs, y, h => by
      cases h with
      | comp vs hg hf =>
          obtain ⟨w₁, hw₁⟩ := fin_eventually (fun i x => vs i ≤ x ∧ EvalB x (gs i) xs (vs i))
            fun i => by
              obtain ⟨w, hw⟩ := EvalB.complete (hg i)
              exact ⟨max w (vs i), fun x hx =>
                ⟨by omega, EvalB.mono (by omega) hw⟩⟩
          obtain ⟨w₂, hw₂⟩ := EvalB.complete hf
          refine ⟨max w₁ w₂, vs, fun i => (hw₁ _ (Nat.le_max_left _ _) i).1,
            fun i => (hw₁ _ (Nat.le_max_left _ _) i).2, EvalB.mono (Nat.le_max_right _ _) hw₂⟩
  | .prec _ _, [], _, h => by cases h
  | .prec f g, m :: rest, y, h => by
      obtain ⟨A, B, hf, hs, rfl⟩ := (eval_prec_iff_beta f g rest m y).1 h
      obtain ⟨w₁, hw₁⟩ := EvalB.complete hf
      obtain ⟨w₂, hw₂⟩ := exists_bound_range (fun j x => EvalB x g (j :: gbeta A B j :: rest)
          (gbeta A B (j + 1))) (fun j x x' hx h => EvalB.mono hx h) m
        fun j hj => EvalB.complete (hs j hj)
      have hβ : ∀ j, gbeta A B j ≤ A := fun j => Nat.mod_le _ _
      let W := max (max A B) (max w₁ w₂)
      refine ⟨W, A, by omega, B, by omega, ⟨⟨_, by have := hβ 0; omega, rfl,
        EvalB.mono (by omega) hw₁⟩, fun j hj => ⟨_, by have := hβ j; omega, _,
          by have := hβ (j + 1); omega, ⟨rfl, rfl⟩, EvalB.mono (by omega) (hw₂ j hj)⟩⟩, rfl⟩
  | .mu f, xs, y, h => by
      obtain ⟨h₀, hlt⟩ := (eval_mu_iff f xs y).1 h
      obtain ⟨w₁, hw₁⟩ := EvalB.complete h₀
      obtain ⟨w₂, hw₂⟩ := exists_bound_range
          (fun m x => ∃ z, z ≤ x ∧ EvalB x f (m :: xs) z ∧ ¬ z = 0)
          (fun j x x' hx ⟨z, hz, hz', hz0⟩ => ⟨z, by omega, EvalB.mono hx hz', hz0⟩) y
        fun m hm => by
          obtain ⟨z, hz, hz0⟩ := hlt m hm
          obtain ⟨w, hw⟩ := EvalB.complete hz
          exact ⟨max w z, z, by omega, EvalB.mono (by omega) hw, hz0⟩
      refine ⟨max w₁ w₂, EvalB.mono (by omega) hw₁, fun m hm => ?_⟩
      obtain ⟨z, hz, hz', hz0⟩ := hw₂ m hm
      exact ⟨z, by omega, EvalB.mono (by omega) hz', hz0⟩

/-- **Evaluation is bounded evaluation for some bound** (and then for all larger ones). -/
theorem eval_iff_exists_evalB (c : Code) (xs : List Nat) (y : Nat) :
    Eval c xs y ↔ ∃ w, EvalB w c xs y :=
  ⟨EvalB.complete, fun ⟨_, h⟩ => h.sound⟩

/-! ## The bounded β-function and bounded quantifier blocks -/

/-- The β-function as a bounded formula: `z = β(A, B, i)`, i.e.
`∃q ≤ A. A = q·(1 + (i + 1)·B) + z ∧ Sz ≤ 1 + (i + 1)·B`
(free variables `0 = z`, `1 = A`, `2 = B`, `3 = i`). -/
def betaB : Formula Arith :=
  ex (conj (boundF (v 1)) (conj (eq (v 2) (add (mul (v 0) betaDiv) (v 1)))
    (substL [succ (v 1), betaDiv] leF)))

/-- `betaB` is bounded. -/
theorem betaB_D0 : D0 betaB := D0.bex _ (D0.conj (D0.eq _ _) (D0.le _ _))

/-- `t ≤ s` in `ℕ`. -/
theorem sat_le_std (t s : Term Arith) (e : Nat → Nat) :
    Sat stdModel e (substL [t, s] leF) ↔ t.eval stdModel e ≤ s.eval stdModel e := by
  rw [substL, sat_subst, sat_leF (M := stdModel), mle_std]; rfl

/-- Meaning of `betaB`. -/
theorem sat_betaB (e : Nat → Nat) : Sat stdModel e betaB ↔ e 0 = gbeta (e 1) (e 2) (e 3) := by
  simp only [betaB, Sat, sat_boundF_std, sat_le_std, betaDiv, eval_add, eval_mul, eval_succ,
    eval_zero, Term.eval, Env.cons, gbeta]
  constructor
  · rintro ⟨q, -, h₁, h₂⟩
    rw [h₁, Nat.add_comm (q * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  · intro h
    refine ⟨e 1 / (0 + 1 + (e 3 + 1) * e 2), Nat.div_le_self _ _, ?_, ?_⟩
    · rw [h, Nat.mul_comm]; simp only [Nat.zero_add]; exact (Nat.div_add_mod _ _).symm
    · rw [h]; simp only [Nat.zero_add]; exact Nat.mod_lt _ (by omega)

/-- `betaB` instantiated at four terms. -/
theorem sat_betaB_substL (z A B i : Term Arith) (e : Nat → Nat) :
    Sat stdModel e (substL [z, A, B, i] betaB) ↔
      z.eval stdModel e = gbeta (A.eval stdModel e) (B.eval stdModel e) (i.eval stdModel e) := by
  rw [substL, sat_subst, sat_betaB]; rfl

/-- `k` existential quantifiers, each bounded by the variable that has index `wi`
just outside the block. -/
def bexN : Nat → Nat → Formula Arith → Formula Arith
  | 0, _, φ => φ
  | k + 1, wi, φ => ex (conj (boundF (v wi)) (bexN k (wi + 1) φ))

/-- Meaning of `bexN` in `ℕ`. -/
theorem sat_bexN (φ : Formula Arith) :
    ∀ (k wi : Nat) (e : Nat → Nat), Sat stdModel e (bexN k wi φ) ↔
      ∃ e' : Nat → Nat, (∀ n, e' (n + k) = e n) ∧ (∀ i, i < k → e' i ≤ e wi) ∧ Sat stdModel e' φ
  | 0, wi, e => by
      simp only [bexN, Nat.add_zero]
      exact ⟨fun h => ⟨e, fun _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), h⟩,
        fun ⟨e', he', _, h⟩ => by rwa [show e = e' from funext fun n => (he' n).symm]⟩
  | k + 1, wi, e => by
      simp only [bexN, Sat, sat_boundF_std, eval_var_M]
      constructor
      · rintro ⟨x, hx, h⟩
        obtain ⟨e', he', hb, h⟩ := (sat_bexN φ k (wi + 1) _).1 h
        refine ⟨e', fun n => ?_, fun i hi => ?_, h⟩
        · rw [show n + (k + 1) = (n + 1) + k by omega, he' (n + 1)]; rfl
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact hb i hi
          · have := he' 0; simp only [Nat.zero_add] at this; rw [this]; exact hx
      · rintro ⟨e', he', hb, h⟩
        refine ⟨e' k, hb k (by omega), (sat_bexN φ k (wi + 1) _).2 ⟨e', fun n => ?_,
          fun i hi => hb i (by omega), h⟩⟩
        cases n with
        | zero => simp [Env.cons]
        | succ m =>
            show e' (m + 1 + k) = e m
            rw [show m + 1 + k = m + (k + 1) by omega]; exact he' m

/-- `bexN` preserves boundedness. -/
theorem D0.bexN {φ : Formula Arith} (h : D0 φ) : ∀ k wi, D0 (FO.bexN k wi φ)
  | 0, _ => h
  | k + 1, wi => D0.bex _ (D0.bexN h k (wi + 1))

/-- Finite conjunctions of bounded formulas are bounded. -/
theorem D0.conjL : ∀ l : List (Formula Arith), (∀ φ ∈ l, D0 φ) → D0 (FO.conjL l)
  | [], _ => D0.imp D0.bot D0.bot
  | φ :: l, h => D0.conj (h φ (by simp)) (D0.conjL l fun ψ hψ => h ψ (by simp [hψ]))

/-! ## The bounded graph formulas -/

/-- The variable renaming used for `g` in the primitive recursion clause. -/
def precIdx : Nat → Nat
  | 0 => 2
  | 1 => 1
  | j + 2 => j + 7

/-- **Bounded graph formula** of code `c` at arity `a`: free variable `0` is the output,
`1, …, a` the inputs, and `a + 1` the bound `w` on all quantifiers. -/
def grb : Code → Nat → Formula Arith
  | .zero, _ => eq (v 0) zero
  | .succ, a => eq (v 0) (succ (if a = 0 then zero else v 1))
  | .proj i, a => eq (v 0) (if i < a then v (i + 1) else zero)
  | @Code.comp k f gs, a =>
      bexN k (a + 1) (conj
        (conjL (List.ofFn fun i : Fin k =>
          (grb (gs i) a).subst (Env.cons (v i) fun j => v (j + 1 + k))))
        ((grb f k).subst (Env.cons (v k) fun j => v (if j < k then j else a + 1 + k))))
  | .prec _ _, 0 => bot
  | .prec f g, a + 1 =>
      -- `∃A ≤ w ∃B ≤ w`; then B = v 0, A = v 1, y = v 2, m = v 3, rest = v 4 …, w = v (a + 4)
      ex (conj (boundF (v (a + 2))) (ex (conj (boundF (v (a + 3))) (conj (conj
        -- `∃r ≤ w (r = β(A, B, 0) ∧ f(rest) = r)`
        (ex (conj (boundF (v (a + 4))) (conj (substL [v 0, v 2, v 1, zero] betaB)
          ((grb f a).subst (Env.cons (v 0) fun j => v (j + 5))))))
        -- `∀j < m ∃u ≤ w ∃z ≤ w (u = β(A,B,j) ∧ z = β(A,B,j+1) ∧ g(j, u, rest) = z)`
        (all (imp (boundSF (v 3))
          (ex (conj (boundF (v (a + 5))) (ex (conj (boundF (v (a + 6)))
            (conj (conj (substL [v 1, v 4, v 3, v 2] betaB)
                (substL [v 0, v 4, v 3, succ (v 2)] betaB))
              ((grb g (a + 2)).subst (Env.cons (v 0) fun j => v (precIdx j)))))))))))
        -- `y = β(A, B, m)`
        (substL [v 2, v 1, v 0, v 3] betaB)))))
  | .mu f, a =>
      conj ((grb f (a + 1)).subst (Env.cons zero (Env.cons (v 0) fun j => v (j + 1))))
        (all (imp (boundSF (v 0))
          (ex (conj (boundF (v (a + 2)))
            (conj ((grb f (a + 1)).subst (Env.cons (v 0) (Env.cons (v 1) fun j => v (j + 3))))
              (neg (eq (v 0) zero)))))))

/-- **The bounded graph formulas are bounded.** -/
theorem grb_D0 : ∀ (c : Code) (a : Nat), D0 (grb c a)
  | .zero, _ => D0.eq _ _
  | .succ, _ => D0.eq _ _
  | .proj _, _ => D0.eq _ _
  | @Code.comp k f gs, a => by
      simp only [grb]
      refine D0.bexN (D0.conj (D0.conjL _ fun φ hφ => ?_) ((grb_D0 f k).subst _)) _ _
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
      exact (grb_D0 (gs i) a).subst _
  | .prec _ _, 0 => D0.bot
  | .prec f g, a + 1 => by
      simp only [grb]
      exact D0.bex _ (D0.bex _ (D0.conj (D0.conj
        (D0.bex _ (D0.conj (betaB_D0.subst _) ((grb_D0 f a).subst _)))
        (D0.ballS _ (D0.bex _ (D0.bex _ (D0.conj (D0.conj (betaB_D0.subst _) (betaB_D0.subst _))
          ((grb_D0 g (a + 2)).subst _)))))) (betaB_D0.subst _)))
  | .mu f, a => by
      simp only [grb]
      exact D0.conj ((grb_D0 f (a + 1)).subst _)
        (D0.ballS _ (D0.bex _ (D0.conj ((grb_D0 f (a + 1)).subst _) (D0.eq _ _).neg)))

/-- **Meaning of the bounded graph formulas**: `ℕ ⊨ grb c a [y, x⃗, w]` iff `c` outputs
`y` on `x⃗` by a computation bounded by `w`. -/
theorem sat_grb : ∀ (c : Code) (a : Nat) (e : Nat → Nat),
    Sat stdModel e (grb c a) ↔ EvalB (e (a + 1)) c (List.ofFn fun i : Fin a => e (i + 1)) (e 0)
  | .zero, a, e => by simp only [grb, Sat, eval_zero, Term.eval, EvalB]
  | .succ, a, e => by
      simp only [grb, Sat, eval_succ, Term.eval, EvalB]
      have : (List.ofFn fun i : Fin a => e (i + 1)).headD 0 =
          (if a = 0 then zero else v 1).eval stdModel e := by
        cases a with
        | zero => rfl
        | succ a => simp [List.ofFn_succ]
      rw [this]
  | .proj i, a, e => by
      simp only [grb, Sat, Term.eval, EvalB]
      have : (List.ofFn fun i : Fin a => e (i + 1)).getD i 0 =
          (if i < a then v (i + 1) else zero).eval stdModel e := by
        by_cases h : i < a
        · simp [h, List.getD_eq_getElem?_getD]
        · simp [h, List.getD_eq_getElem?_getD]
      rw [this]
  | @Code.comp k f gs, a, e => by
      simp only [grb, sat_bexN, Sat, sat_conjL, List.mem_ofFn, forall_exists_index,
        forall_apply_eq_imp_iff, sat_subst_cons, sat_grb, Term.eval, Env.cons, EvalB]
      constructor
      · rintro ⟨e', he', hb, hg, hf⟩
        have h0 : e' k = e 0 := by simpa using he' 0
        have hw : e' (a + 1 + k) = e (a + 1) := by rw [show a + 1 + k = (a + 1) + k by omega]; exact he' _
        have hxs : (List.ofFn fun j : Fin a => e' (j + 1 + k)) = List.ofFn fun j : Fin a => e (j + 1) :=
          by congr 1; funext j; exact he' _
        refine ⟨fun i => e' i, fun i => hb i i.isLt, fun i => ?_, ?_⟩
        · have := hg i
          simp only [show a + 1 + k = (a + 1) + k by omega, he'] at this
          exact this
        · have := hf
          simp only [Fin.is_lt, ite_true, Nat.lt_irrefl, ite_false, hw, h0] at this
          exact this
      · rintro ⟨vs, hb, hg, hf⟩
        refine ⟨fun n => if hn : n < k then vs ⟨n, hn⟩ else e (n - k), fun n => ?_,
          fun i hi => ?_, fun i => ?_, ?_⟩
        · have : ¬ (n + k < k) := by omega
          simp [this]
        · simp only [hi, dite_true]; exact hb _
        · simp only [Fin.is_lt, dite_true, show ∀ j : Nat, ¬ (j + 1 + k < k) from fun j => by omega,
            dite_false, show ∀ j : Nat, j + 1 + k - k = j + 1 from fun j => by omega]
          exact hg i
        · simp only [Fin.is_lt, ite_true, dite_true, Nat.lt_irrefl, ite_false, dite_false,
            Nat.sub_self, show ¬ (a + 1 + k < k) by omega, show a + 1 + k - k = a + 1 by omega]
          exact hf
  | .prec f g, 0, e => by
      simp only [grb, Sat, List.ofFn_zero, EvalB]
  | .prec f g, a + 1, e => by
      rw [List.ofFn_succ]
      simp only [grb, Sat, sat_boundF_std, sat_boundSF_std, sat_betaB_substL, sat_subst_cons,
        sat_grb, Term.eval, Env.cons, eval_zero, eval_succ, EvalB, precIdx]
      simp only [Fin.val_zero, Fin.val_succ, List.ofFn_succ]
  | .mu f, a, e => by
      simp only [grb, Sat, sat_boundF_std, sat_boundSF_std, sat_subst_cons, sat_grb, Term.eval,
        Env.cons, eval_zero, EvalB, List.ofFn_succ, Fin.val_zero, Fin.val_succ, neg]

/-- **The graph of every partial recursive function is Σ₁**: `c` outputs `y` on `x⃗`
iff the bounded formula `grb c a` holds for some bound `w`. -/
theorem eval_iff_exists_grb (c : Code) (a : Nat) (e : Nat → Nat) :
    Eval c (List.ofFn fun i : Fin a => e (i + 1)) (e 0) ↔
      ∃ w, Sat stdModel (fun n => if n = a + 1 then w else e n) (grb c a) := by
  rw [eval_iff_exists_evalB]
  refine exists_congr fun w => ?_
  rw [sat_grb]
  simp only [ite_true, show ∀ i : Nat, i + 1 = a + 1 ↔ i = a from fun i => by omega]
  have : (List.ofFn fun i : Fin a => (if (i : Nat) = a then w else e (i + 1))) =
      List.ofFn fun i : Fin a => e (i + 1) := by
    congr 1; funext i; simp [Nat.ne_of_lt i.isLt]
  rw [this]; simp

/-! ## Free variables of the bounded graph formulas -/

/-- `leF` has free variables among `0, 1`. -/
theorem leF_fresh : ∀ n, 2 ≤ n → leF.Fresh n := by
  intro n hn; simp only [leF, Formula.Fresh, fresh_add, fresh_var]; omega

/-- Freshness of a variable bound. -/
theorem boundF_var_fresh {k y : Nat} (h₀ : y ≠ 0) (hk : k + 1 ≠ y) : (boundF (v k)).Fresh y := by
  refine fresh_substL leF_fresh (by simp) fun t ht => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl
  · exact var_fresh (Ne.symm h₀)
  · exact var_fresh hk

/-- Freshness of a strict variable bound. -/
theorem boundSF_var_fresh {k y : Nat} (h₀ : y ≠ 0) (hk : k + 1 ≠ y) : (boundSF (v k)).Fresh y := by
  refine fresh_substL leF_fresh (by simp) fun t ht => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl
  · exact (fresh_succ _ _).2 (var_fresh (Ne.symm h₀))
  · exact var_fresh hk

/-- `betaB` has free variables among `0, 1, 2, 3`. -/
theorem betaB_fresh : ∀ n, 4 ≤ n → betaB.Fresh n := by
  intro n hn
  have hD : ∀ m, 5 ≤ m → betaDiv.Fresh m := by
    intro m hm
    simp only [betaDiv, fresh_add, fresh_mul, fresh_succ, fresh_var, fresh_zero, true_and]; omega
  refine ⟨boundF_var_fresh (by omega) (by omega), ⟨?_, ?_⟩, fresh_substL leF_fresh (by simp) ?_⟩
  · exact var_fresh (by omega)
  · exact (fresh_add _ _ _).2 ⟨(fresh_mul _ _ _).2 ⟨var_fresh (by omega), hD _ (by omega)⟩,
      var_fresh (by omega)⟩
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl
    · exact (fresh_succ _ _).2 (var_fresh (by omega))
    · exact hD _ (by omega)

/-- Freshness of a block of bounded existentials. -/
theorem bexN_fresh (φ : Formula Arith) :
    ∀ (k wi x : Nat), wi ≠ x → φ.Fresh (x + k) → (bexN k wi φ).Fresh x
  | 0, _, _, _, h => h
  | k + 1, wi, x, hw, h =>
      ⟨boundF_var_fresh (by omega) (by omega),
        bexN_fresh φ k (wi + 1) (x + 1) (by omega) (by rwa [show x + 1 + k = x + (k + 1) by omega])⟩

/-- A list substitution of variables below a bound is fresh. -/
theorem fresh_substL_vars {φ : Formula Arith} {m : Nat} (hφ : ∀ n, m ≤ n → φ.Fresh n)
    {ts : List (Term Arith)} (hlen : m ≤ ts.length) {y : Nat} (hts : ∀ t ∈ ts, t.Fresh y) :
    (substL ts φ).Fresh y := fresh_substL hφ hlen hts

/-- **The bounded graph formula `grb c a` has its free variables among `0, …, a + 1`.** -/
theorem grb_fresh : ∀ (c : Code) (a x : Nat), a + 1 < x → (grb c a).Fresh x
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
      simp only [grb]
      refine bexN_fresh _ k (a + 1) x (by omega) ⟨(fresh_conjL _ _).2 fun φ hφ => ?_, ?_⟩
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
        refine Formula.fresh_subst_of _ fun n hn => ?_
        have hn' : n ≤ a + 1 :=
          Classical.byContradiction fun h' => hn (grb_fresh (gs i) a n (by omega))
        cases n with
        | zero => exact var_fresh (by have := i.isLt; omega)
        | succ j => exact var_fresh (by omega)
      · refine Formula.fresh_subst_of _ fun n hn => ?_
        have hn' : n ≤ k + 1 := Classical.byContradiction fun h' => hn (grb_fresh f k n (by omega))
        cases n with
        | zero => exact var_fresh (by omega)
        | succ j =>
            refine var_fresh ?_
            split <;> omega
  | .prec f g, 0, x, h => trivial
  | .prec f g, a + 1, x, h => by
      have bt : ∀ y, 4 < y → ∀ t ∈ [v 0, v 2, v 1, zero], Term.Fresh y t := by
        intro y hy t ht
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> first | exact zero_fresh _ | exact var_fresh (by omega)
      refine ⟨boundF_var_fresh (by omega) (by omega), boundF_var_fresh (by omega) (by omega),
        ⟨⟨boundF_var_fresh (by omega) (by omega), fresh_substL betaB_fresh (by simp) (bt _ (by omega)),
          Formula.fresh_subst_of _ fun n hn => ?_⟩,
         boundSF_var_fresh (by omega) (by omega), boundF_var_fresh (by omega) (by omega),
         boundF_var_fresh (by omega) (by omega),
         ⟨fresh_substL betaB_fresh (by simp) ?_, fresh_substL betaB_fresh (by simp) ?_⟩,
         Formula.fresh_subst_of _ fun n hn => ?_⟩, fresh_substL betaB_fresh (by simp) ?_⟩
      · have hn' : n ≤ a + 1 := Classical.byContradiction fun h' => hn (grb_fresh f a n (by omega))
        cases n with
        | zero => exact var_fresh (by omega)
        | succ j => exact var_fresh (by omega)
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> exact var_fresh (by omega)
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact var_fresh (by omega)
        · exact var_fresh (by omega)
        · exact var_fresh (by omega)
        · exact (fresh_succ _ _).2 (var_fresh (by omega))
      · have hn' : n ≤ a + 3 :=
          Classical.byContradiction fun h' => hn (grb_fresh g (a + 2) n (by omega))
        match n, hn' with
        | 0, _ => exact var_fresh (by omega)
        | 1, _ => exact var_fresh (by simp [precIdx])
        | 2, _ => exact var_fresh (by simp [precIdx])
        | j + 3, _ => exact var_fresh (by simp [precIdx]; omega)
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> exact var_fresh (by omega)
  | .mu f, a, x, h => by
      refine ⟨Formula.fresh_subst_of _ fun n hn => ?_, boundSF_var_fresh (by omega) (by omega),
        boundF_var_fresh (by omega) (by omega), Formula.fresh_subst_of _ fun n hn => ?_,
        ⟨var_fresh (by omega), zero_fresh _⟩, trivial⟩
      · have hn' : n ≤ a + 2 :=
          Classical.byContradiction fun h' => hn (grb_fresh f (a + 1) n (by omega))
        match n, hn' with
        | 0, _ => exact zero_fresh _
        | 1, _ => exact var_fresh (by omega)
        | j + 2, _ => exact var_fresh (by omega)
      · have hn' : n ≤ a + 2 :=
          Classical.byContradiction fun h' => hn (grb_fresh f (a + 1) n (by omega))
        match n, hn' with
        | 0, _ => exact var_fresh (by omega)
        | 1, _ => exact var_fresh (by omega)
        | j + 2, _ => exact var_fresh (by omega)

end Foundations.Logic.FO
