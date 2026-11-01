import Foundations.Logic.Rosser

/-!
# Löb's theorem and Gödel's second incompleteness theorem (from the derivability conditions)

Gödel's **second incompleteness theorem** says that a consistent theory `T` containing
enough arithmetic cannot prove its own consistency `Con_T := ¬Prov_T(⌜⊥⌝)`. Its modern
proof isolates three properties of a provability formula `Prov(x)`, the
**Hilbert–Bernays–Löb derivability conditions** (writing `□φ` for `Prov(⌜φ⌝)`):

* (D1) if `T ⊢ φ` then `T ⊢ □φ`;
* (D2) `T ⊢ □(φ → ψ) → (□φ → □ψ)`;
* (D3) `T ⊢ □φ → □□φ`.

From these and the diagonal lemma, Löb (1955) derived **Löb's theorem**: *if
`T ⊢ □φ → φ` then `T ⊢ φ`* — a theory can only "trust its own provability predicate"
for statements it already proves. Gödel II is the case `φ = ⊥`.

*What is assumed and what is proved — read carefully.* The theorems `lob` and
`godel_second` below are **abstract**: the formula `P` is arbitrary, and the three
derivability conditions are *hypotheses*. The diagonal lemma is *not* assumed: it is
our theorem `diagonal_lemma` for `Q`, transferred to any `T ⊇ Q`. For the concrete
provability formula of PA (`provPA`, "the PA-proof-search program halts on `x`") we
*prove* condition (D1), by Σ₁-completeness of `Q` (`provPA_D1`). Conditions (D2) and
(D3) for `provPA` are **not proved**: they require formalising, *inside* PA, the
correctness of the proof checker and Σ₁-completeness itself — formal derivations by
induction about our arithmetisation, which the semantic methods of these files do not
supply. Consequently `godel_second_PA` is stated *conditionally* on (D2) and (D3).
(The files `PAModels` … `DerivabilityConditions` remove the condition: they verify
(D1)–(D3) for a provability formula `provH` whose shape is under our control, by
reasoning inside arbitrary models of PA, and prove `godel_second_PA_unconditional`.)
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula Theory Computability

/-! ## Propositional bookkeeping in `⊢₁` -/

section PropLemmas
variable {T : Theory Arith}

/-- Chaining implications. -/
theorem imp_trans {A B C : Formula Arith} (h₁ : T ⊢₁ imp A B) (h₂ : T ⊢₁ imp B C) : T ⊢₁ imp A C :=
  Proves.impI (Proves.impE (Proves.weaken₁ h₂ A)
    (Proves.impE (Proves.weaken₁ h₁ A) (Proves.assume T A)))

/-- The `S` combinator: from `A → (B → C)` and `A → B` infer `A → C`. -/
theorem imp_S {A B C : Formula Arith} (h₁ : T ⊢₁ imp A (imp B C)) (h₂ : T ⊢₁ imp A B) :
    T ⊢₁ imp A C :=
  Proves.impI (Proves.impE (Proves.impE (Proves.weaken₁ h₁ A) (Proves.assume T A))
    (Proves.impE (Proves.weaken₁ h₂ A) (Proves.assume T A)))

end PropLemmas

/-- Instantiation distributes over implication. -/
theorem inst_imp (A B : Formula Arith) (t : Term Arith) : (imp A B).inst t = imp (A.inst t) (B.inst t) :=
  rfl

/-! ## The abstract theorems -/

/-- The "box" `□φ := P(⌜φ⌝)` of a provability formula `P` (free variable `0`). -/
noncomputable def box (P φ : Formula Arith) : Formula Arith := P.inst (numeral (fcode φ))

/-- **The Hilbert–Bernays–Löb derivability conditions** for the formula `P` over the
theory `T`. -/
structure Derivability (T : Theory Arith) (P : Formula Arith) : Prop where
  /-- (D1) Provable formulas are provably provable. -/
  d1 : ∀ φ, T ⊢₁ φ → T ⊢₁ box P φ
  /-- (D2) Provability is closed under modus ponens, provably. -/
  d2 : ∀ φ ψ, T ⊢₁ imp (box P (imp φ ψ)) (imp (box P φ) (box P ψ))
  /-- (D3) Provable formulas are provably provably provable (formalised D1). -/
  d3 : ∀ φ, T ⊢₁ imp (box P φ) (box P (box P φ))

/-- **Löb's theorem** (abstract form: the derivability conditions are hypotheses; the
diagonal lemma is our theorem for `Q`). If `T ⊇ Q` satisfies (D1)–(D3) for `P`, and
`T ⊢ □φ → φ`, then `T ⊢ φ`. -/
theorem lob {T : Theory Arith} (hQ : ∀ ψ, Q ψ → T ⊢₁ ψ) {P : Formula Arith}
    (hD : Derivability T P) {φ : Formula Arith} (h : T ⊢₁ imp (box P φ) φ) : T ⊢₁ φ := by
  -- the diagonal sentence `δ ↔ (□δ → φ)`
  let δ := diagSentence (imp P φ.shift)
  have hd : T ⊢₁ iffF δ (imp (box P δ) φ) := by
    have := proves_of_Q_proves hQ (diagonal_lemma (imp P φ.shift))
    rwa [inst_imp, shift_inst] at this
  have h₁ : T ⊢₁ imp δ (imp (box P δ) φ) := Proves.conjE₁ hd
  have h₂ := hD.d1 _ h₁
  have h₃ : T ⊢₁ imp (box P δ) (box P (imp (box P δ) φ)) := Proves.impE (hD.d2 _ _) h₂
  have h₅ := imp_trans h₃ (hD.d2 (box P δ) φ)
  have h₇ : T ⊢₁ imp (box P δ) (box P φ) := imp_S h₅ (hD.d3 δ)
  have h₈ : T ⊢₁ imp (box P δ) φ := imp_trans h₇ h
  have h₉ : T ⊢₁ δ := Proves.impE (Proves.conjE₂ hd) h₈
  exact Proves.impE h₈ (hD.d1 _ h₉)

/-- The consistency statement `Con := ¬□⊥` for the provability formula `P`. -/
noncomputable def conF (P : Formula Arith) : Formula Arith := neg (box P bot)

/-- **Gödel's second incompleteness theorem** (abstract form, from the derivability
conditions). A consistent theory `T ⊇ Q` satisfying (D1)–(D3) for `P` does not prove
its consistency statement `¬□⊥`. -/
theorem godel_second {T : Theory Arith} (hQ : ∀ ψ, Q ψ → T ⊢₁ ψ) {P : Formula Arith}
    (hD : Derivability T P) (hcon : ¬ T ⊢₁ bot) : ¬ T ⊢₁ conF P :=
  fun h => hcon (lob hQ hD h)

/-! ## The provability formula of PA and condition (D1) -/

/-- The Σ₁ formula "program `c` halts on `x`" (free variable `0 = x`):
`∃y ∃w grb c 1 (y, x, w)`. -/
def haltsSigma (c : Code) : Formula Arith := ex (evalSigma c)

/-- `evalSigma c` has free variables among `0, 1`. -/
theorem evalSigma_fresh (c : Code) : ∀ n, 2 ≤ n → (evalSigma c).Fresh n := by
  intro n hn
  refine Formula.fresh_subst_of _ fun m _ => ?_
  match m with
  | 0 => exact var_fresh (by omega)
  | 1 => exact var_fresh (by omega)
  | m + 2 => exact var_fresh (by omega)

/-- **Σ₁-completeness for halting**: if `c` halts on `x`, `Q` proves it. -/
theorem Q_proves_halts {c : Code} {x : Nat} (h : Halts c [x]) :
    Q ⊢₁ (haltsSigma c).inst (numeral x) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨w, hw⟩ := EvalB.complete hy
  refine Q_proves_of_models fun M e hM => ?_
  rw [sat_inst, eval_numeral_M]
  simp only [haltsSigma, evalSigma, Sat, sat_subst]
  refine ⟨numM M y, numM M w, ?_⟩
  have : (fun k => (Env.cons (v 1) (Env.cons (v 2) fun _ => v 0) k).eval M
      (Env.cons (numM M w) (Env.cons (numM M y) (Env.cons (numM M x) e)))) =
        Env.cons (numM M y) (Env.cons (numM M x) fun _ => numM M w) := by
    funext k; match k with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => rfl
  rw [this, env3_numM, D0.absolute hM (grb_D0 c 1)]
  exact (sat_grb1 c y x w).2 hw

/-- The PA-proof-search program (halts on `⌜φ⌝` iff `PA ⊢ φ`). -/
noncomputable def paSearch : Code := PA_theorems_ce.choose

/-- **The provability formula of PA**: "the PA-proof-search program halts on `x`". -/
noncomputable def provPA : Formula Arith := haltsSigma paSearch

/-- `provPA` defines PA-provability in the standard model. -/
theorem sat_provPA (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provPA φ) ↔ PA ⊢₁ φ := by
  rw [box, sat_inst, eval_numeral_std, ← PA_theorems_ce.choose_spec φ]
  simp only [provPA, haltsSigma, Sat]
  constructor
  · rintro ⟨y, hy⟩
    have := (sat_evalSigma paSearch y (fcode φ)).1
    refine ⟨y, this ?_⟩
    refine (sat_congr_fresh _ fun n hn => ?_).1 hy
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact absurd (evalSigma_fresh _ (n + 2) (by omega)) hn
  · rintro ⟨y, hy⟩
    refine ⟨y, (sat_congr_fresh _ fun n hn => ?_).1 ((sat_evalSigma paSearch y (fcode φ)).2 hy)⟩
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact absurd (evalSigma_fresh _ (n + 2) (by omega)) hn

/-- **Condition (D1) for PA**: if `PA ⊢ φ` then `PA ⊢ Prov_PA(⌜φ⌝)`. -/
theorem provPA_D1 {φ : Formula Arith} (h : PA ⊢₁ φ) : PA ⊢₁ box provPA φ :=
  PA_proves_of_Q_proves (Q_proves_halts ((PA_theorems_ce.choose_spec φ).2 h))

/-- **Gödel's second incompleteness theorem for PA, conditional on (D2) and (D3).**
If the provability formula `provPA` satisfies the derivability conditions (D2) and (D3)
(which are *not* proved here — see the module docstring; (D1) *is* proved), then PA,
being consistent, does not prove its consistency statement `¬Prov_PA(⌜⊥⌝)`. -/
theorem godel_second_PA
    (d2 : ∀ φ ψ, PA ⊢₁ imp (box provPA (imp φ ψ)) (imp (box provPA φ) (box provPA ψ)))
    (d3 : ∀ φ, PA ⊢₁ imp (box provPA φ) (box provPA (box provPA φ))) :
    ¬ PA ⊢₁ conF provPA :=
  godel_second (fun _ h => PA_proves_Q h) ⟨fun _ h => provPA_D1 h, d2, d3⟩ PA_consistent

end Foundations.Logic.FO
