import Foundations.Logic.Representability

/-!
# The diagonal lemma and Tarski's undefinability of truth

The engine of self-reference in arithmetic is the **diagonal (fixed-point) lemma**,
implicit in Gödel (1931) and stated in general form by Carnap (1934):

> for every formula `ψ(x)` there is a sentence `δ` such that `Q ⊢ δ ↔ ψ(⌜δ⌝)`.

`δ` "says of itself" that it has the property `ψ`. The proof is the same diagonal
trick as in Kleene's recursion theorem, now carried out with formulas. The
*diagonal function* `d(⌜θ⌝) = ⌜θ(⌜θ⌝)⌝` — substitute a formula's own Gödel number
into it — is computable (we have computable substitution on codes), hence
representable in `Q` by a formula `D(y, x)`. Put

`θ(x) := ∃y (D(y, x) ∧ ψ(y))`  ("the diagonalisation of `x` has property `ψ`")
and `δ := θ(⌜θ⌝)`.

Then `δ` says that the diagonalisation of `⌜θ⌝` — which *is* `⌜δ⌝` — has property `ψ`;
and since `Q` proves that `d(⌜θ⌝)‾` is the unique `y` with `D(y, ⌜θ⌝)`, it proves
`δ ↔ ψ(⌜δ⌝)`. As elsewhere, we argue in an arbitrary model of `Q` and conclude by the
completeness theorem.

**Tarski's theorem** (1933/36) follows at once: there is no formula `Tr(x)` such
that `ℕ ⊨ Tr(⌜σ⌝) ↔ σ` for all sentences `σ` — apply the diagonal lemma to `¬Tr` to
obtain a "liar" sentence `λ ↔ ¬Tr(⌜λ⌝)`, which would be true iff false. Truth in
arithmetic is not arithmetically definable — in contrast with provability, which
is (it is computably enumerable).
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula Computability

/-- The biconditional `φ ↔ ψ`. -/
def iffF (φ ψ : Formula Arith) : Formula Arith := conj (imp φ ψ) (imp ψ φ)

/-- Meaning of the biconditional. -/
theorem sat_iffF {M : Structure Arith} (e : Nat → M.Dom) (φ ψ : Formula Arith) :
    Sat M e (iffF φ ψ) ↔ (Sat M e φ ↔ Sat M e ψ) := by
  simp only [iffF, Sat]; exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **The diagonal function** on Gödel numbers: substitute the numeral of `n` into
the formula with code `n`. -/
def diagC (n : Nat) : Nat := instC n (ncode n)

/-- Correctness of the diagonal function. -/
theorem diagC_fcode (θ : Formula Arith) : diagC (fcode θ) = fcode (θ.inst (numeral (fcode θ))) := by
  rw [diagC, ncode, instC_fcode]

/-- The diagonal function is computable. -/
theorem diagC_comp : Comp diagC := Comp.instC Comp.id Comp.ncode

/-- A code computing the diagonal function. -/
noncomputable def diagCode : Code := diagC_comp.choose

/-- `diagCode` computes `diagC`. -/
theorem diagCode_spec (n : Nat) : Eval diagCode [n] (diagC n) := diagC_comp.choose_spec n

/-- The formula `θ(x) := ∃y (D(y, x) ∧ ψ(y))` used in the diagonal lemma (the other
free variables of `ψ` become the free variables `1, 2, …` of `θ`). -/
noncomputable def diagTheta (ψ : Formula Arith) : Formula Arith :=
  ex (conj (funF diagCode) (ψ.subst (Env.cons (v 0) fun j => v (j + 2))))

/-- **The diagonal sentence** for `ψ`. -/
noncomputable def diagSentence (ψ : Formula Arith) : Formula Arith :=
  (diagTheta ψ).inst (numeral (fcode (diagTheta ψ)))

/-- The formula `θ`, semantically: in any model of `Q`, `θ(n̄)` holds iff `ψ` holds of
`d(n)‾`. -/
theorem sat_diagTheta {M : Structure Arith} (hM : IsQModel M) (ψ : Formula Arith) (n : Nat)
    (e : Nat → M.Dom) :
    Sat M (Env.cons (numM M n) e) (diagTheta ψ) ↔ Sat M (Env.cons (numM M (diagC n)) e) ψ := by
  unfold diagTheta
  simp only [Sat, sat_subst]
  have henv : ∀ y : M.Dom, (fun k => (Env.cons (v 0) (fun j => v (j + 2)) k).eval M
      (Env.cons y (Env.cons (numM M n) e))) = Env.cons y e := by
    intro y; funext k; cases k <;> rfl
  simp only [henv, sat_funF diagCode_spec hM]
  constructor
  · rintro ⟨y, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

/-- The diagonal sentence, semantically: in any model of `Q`, `δ` holds iff `ψ` holds
of the value of the numeral of `⌜δ⌝`. -/
theorem sat_diagSentence {M : Structure Arith} (hM : IsQModel M) (ψ : Formula Arith)
    (e : Nat → M.Dom) :
    Sat M e (diagSentence ψ) ↔ Sat M e (ψ.inst (numeral (fcode (diagSentence ψ)))) := by
  rw [sat_inst ψ, eval_numeral_M]
  conv => lhs; rw [diagSentence, sat_inst, eval_numeral_M, sat_diagTheta hM, diagC_fcode]
  rfl

/-- **The diagonal lemma for `Q`.** For every formula `ψ` there is a formula `δ` with
`Q ⊢ δ ↔ ψ(⌜δ⌝)`. -/
theorem diagonal_lemma (ψ : Formula Arith) :
    Q ⊢₁ iffF (diagSentence ψ) (ψ.inst (numeral (fcode (diagSentence ψ)))) :=
  Q_proves_of_models fun _ e hM => (sat_iffF e _ _).2 (sat_diagSentence hM ψ e)

/-- **The diagonal lemma for PA** (and any theory containing `Q`). -/
theorem diagonal_lemma_PA (ψ : Formula Arith) :
    PA ⊢₁ iffF (diagSentence ψ) (ψ.inst (numeral (fcode (diagSentence ψ)))) :=
  PA_proves_of_Q_proves (diagonal_lemma ψ)

/-- Instantiating the only free variable of a formula by a closed term gives a
sentence. -/
theorem inst_sentence {θ : Formula Arith} (hθ : ∀ x, 1 ≤ x → θ.Fresh x) {t : Term Arith}
    (ht : ∀ y, t.Fresh y) : IsSentence (θ.inst t) := by
  intro y
  refine Formula.fresh_subst_of θ fun n hn => ?_
  cases n with
  | zero => exact ht y
  | succ m => exact absurd (hθ (m + 1) (by omega)) hn

/-- `θ` has only the free variable `0` if `ψ` does. -/
theorem diagTheta_fresh {ψ : Formula Arith} (hψ : ∀ x, 1 ≤ x → ψ.Fresh x) :
    ∀ x, 1 ≤ x → (diagTheta ψ).Fresh x := by
  intro x hx
  unfold diagTheta
  refine ⟨funF_fresh _ _ (by omega), Formula.fresh_subst_of ψ fun n hn => ?_⟩
  cases n with
  | zero => exact var_fresh (by omega)
  | succ m => exact absurd (hψ (m + 1) (by omega)) hn

/-- If `ψ` has only the free variable `0`, the diagonal sentence is a sentence. -/
theorem diagSentence_sentence {ψ : Formula Arith} (hψ : ∀ x, 1 ≤ x → ψ.Fresh x) :
    IsSentence (diagSentence ψ) := by
  unfold diagSentence
  exact inst_sentence (diagTheta_fresh hψ) (numeral_fresh · _)

/-- **Tarski's undefinability theorem.** No formula `Tr(x)` (with only the free
variable `x`) defines arithmetical truth: there is no `Tr` such that, for every
sentence `σ`, `ℕ ⊨ Tr(⌜σ⌝)` iff `ℕ ⊨ σ`. -/
theorem tarski_undefinability :
    ¬ ∃ Tr : Formula Arith, (∀ x, 1 ≤ x → Tr.Fresh x) ∧
      ∀ σ : Formula Arith, IsSentence σ → ∀ e : Nat → Nat,
        (Sat stdModel e (Tr.inst (numeral (fcode σ))) ↔ Sat stdModel e σ) := by
  rintro ⟨Tr, hfresh, hTr⟩
  let L := diagSentence (neg Tr)
  have hL : IsSentence L := diagSentence_sentence fun x hx => ⟨hfresh x hx, trivial⟩
  have h₁ := sat_diagSentence stdModel_isQModel (neg Tr) (fun _ => 0)
  have h₂ := hTr L hL (fun _ => 0)
  rw [show (neg Tr).inst (numeral (fcode (diagSentence (neg Tr)))) =
    neg (Tr.inst (numeral (fcode (diagSentence (neg Tr))))) from rfl, sat_neg] at h₁
  -- `L ↔ ¬Tr(⌜L⌝) ↔ ¬L`
  have : Sat stdModel (fun _ => 0) L ↔ ¬ Sat stdModel (fun _ => 0) L := h₁.trans (not_congr h₂)
  by_cases h : Sat stdModel (fun _ => 0) L
  · exact this.1 h h
  · exact h (this.2 h)

end Foundations.Logic.FO
