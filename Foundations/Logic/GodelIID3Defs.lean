import Foundations.Logic.GodelIID3Code

/-!
# A transparent derivation predicate `provDP`

The derivation predicate `provD` of `GodelIIDerivations` checks each line with the Σ₁
graph of a program computing the step relation `paStep`. Of that program nothing is known
on non-standard inputs, so inside a non-standard model no line with non-standard content
can ever be *shown* to be justified — and formalised Σ-completeness needs exactly such
lines (instances of axioms at the numerals of non-standard numbers). (D3) for `provD`
itself is therefore out of reach of these methods.

We remedy this in the way Hilbert and Bernays did: by arithmetising the rules that the
completeness argument uses *transparently*, i.e. by explicit formulas whose behaviour in
every model of PA we control. `provDP` is derivability in the same natural-deduction
calculus for PA (every line is still a judgement `⟨k, ⟨Δ, φ⟩⟩`), where a line may be
justified in one of three ways:

1. by one step of the calculus, checked through `paStep` as in `provD`;
2. by **modus ponens** on judgements `PA ⊢ φ → ψ`, `PA ⊢ φ` (rule 3 of the calculus),
   checked by polynomial equations;
3. by **substitution of numerals**: from `PA ⊢ φ` infer `PA ⊢ φ(n̄₀, n̄₁, …)`, the
   substitution being checked by an explicit β-coded table (`SubstM`) that computes it
   subformula by subformula. This rule is admissible (it is ∀-introduction followed by
   ∀-elimination). It is sound because PA proves `φ` only if it proves all its instances;
   its soundness is proved semantically, via the completeness theorem.

In the standard model the three ways derive exactly the same judgements (next files);
the defining formula is a Σ-formula (`SigP`), built by `sudfn`.

*Place in the argument.* Gödel (1931) only sketched the second incompleteness theorem;
Hilbert and Bernays (1939) carried out the arithmetisation it needs; Löb (1955) reduced it to
three derivability conditions, of which (D3) — formalised Σ₁-completeness — is the hard one.
Feferman (1960) showed that the theorem depends on how provability is expressed, which is why
it matters that `provDP` is a derivation predicate rather than one engineered to satisfy (D3).
This file is one step of the proof of (D3) for `provDP` assembled in `GodelIID3Main`.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability GodelII

namespace PAModel

/-- Σ-definitions are closed under substitution of uniformly definable functions. -/
def SUDef.subst {P : ∀ N : PAModel, (Nat → N.Dom) → Prop} (hP : SUDef P)
    {σ : Nat → ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hσ : ∀ n, UDefT (σ n)) :
    SUDef fun N e => P N (fun n => σ n N e) :=
  ⟨UDef.subst hP.toUDef hσ, hP.sig.subst _⟩

/-- The numeral relation at definable arguments is Σ-definable. -/
noncomputable def SUDef.numM {f g : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f)
    (hg : UDefT g) : SUDef fun N e => NumM (f N e) (g N e) :=
  numDef.subst (σ := fun n => match n with | 0 => f | _ => g)
    (fun n => match n with | 0 => hf | _ + 1 => hg)

macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.numM)

variable {N : PAModel}

/-! ## The substitution table -/

/-- `x` codes the table entry `⟨u, ⟨dp, ⟨r, s⟩⟩⟩`: subcode `u` at binder depth `dp` has
substitution result `r`; `s = 0` for terms, `s = 1` for formulas. -/
def Quad (u dp r s x : N.Dom) : Prop := ∃ q, PairM r s q ∧ ∃ p, PairM dp q p ∧ PairM u p x

/-- The entry `(u, dp, r, s)` occurs in the table `(tc, td)` of length `L + 1`. -/
def Entry (tc td L u dp r s : N.Dom) : Prop :=
  ∃ j, j ≤ L ∧ ∃ x, BetaM tc td j x ∧ Quad u dp r s x

/-- **Local correctness of a term entry**: a variable below the depth is kept, a variable
`dp + m'` becomes the numeral of the `m'`-th value; `0` is kept; `S`, `+`, `·` are
recomputed from table entries for the arguments. -/
def TermOK (lc ld tc td L u dp r : N.Dom) : Prop :=
  (∃ m, PairM 0 m u ∧ ((m < dp ∧ r = u) ∨
      (∃ m', dp + m' = m ∧ ∃ w, BetaM lc ld m' w ∧ NumM w r))) ∨
    (u = 2 ∧ r = 2) ∨
    (∃ u₁, PairM 2 u₁ u ∧ ∃ r₁, PairM 2 r₁ r ∧ Entry tc td L u₁ dp r₁ 0) ∨
    (∃ k, (k = 3 ∨ k = 4) ∧ ∃ p, PairM k p u ∧ ∃ u₁, ∃ u₂, PairM u₁ u₂ p ∧ ∃ q, PairM k q r ∧
      ∃ r₁, ∃ r₂, PairM r₁ r₂ q ∧ Entry tc td L u₁ dp r₁ 0 ∧ Entry tc td L u₂ dp r₂ 0)

/-- **Local correctness of a formula entry**: `⊥` is kept; equations, binary connectives
and quantifiers (with depth `dp + 1`) are recomputed from table entries for their parts. -/
def FormOK (tc td L u dp r : N.Dom) : Prop :=
  (u = 0 ∧ r = 0) ∨
    (∃ p, PairM 1 p u ∧ ∃ u₁, ∃ u₂, PairM u₁ u₂ p ∧ ∃ q, PairM 1 q r ∧
      ∃ r₁, ∃ r₂, PairM r₁ r₂ q ∧ Entry tc td L u₁ dp r₁ 0 ∧ Entry tc td L u₂ dp r₂ 0) ∨
    (∃ k, (k = 2 ∨ k = 3 ∨ k = 4) ∧ ∃ p, PairM k p u ∧ ∃ u₁, ∃ u₂, PairM u₁ u₂ p ∧
      ∃ q, PairM k q r ∧ ∃ r₁, ∃ r₂, PairM r₁ r₂ q ∧ Entry tc td L u₁ dp r₁ 1 ∧
        Entry tc td L u₂ dp r₂ 1) ∨
    (∃ k, (k = 5 ∨ k = 6) ∧ ∃ u₁, PairM k u₁ u ∧ ∃ r₁, PairM k r₁ r ∧
      Entry tc td L u₁ (dp + 1) r₁ 1)

/-- **The substitution relation.** `r` is the result of substituting, in the formula with
code `u`, the numeral of the `m`-th value of the list `(lc, ld)` for the free variable
`m`; witnessed by a table every entry of which is locally correct. -/
def SubstM (u r : N.Dom) : Prop :=
  ∃ lc, ∃ ld, ∃ tc, ∃ td, ∃ L, Entry tc td L u 0 r 1 ∧
    ∀ j, j ≤ L → ∃ x, BetaM tc td j x ∧ ∃ u', ∃ dp, ∃ r', ∃ s, Quad u' dp r' s x ∧
      ((s = 0 ∧ TermOK lc ld tc td L u' dp r') ∨ (s = 1 ∧ FormOK tc td L u' dp r'))

/-! ## Lines and derivations -/

/-- `y = J(x) = ⟨0, ⟨0, x⟩⟩` is the judgement "PA ⊢ x". -/
def JM (x y : N.Dom) : Prop := ∃ a, PairM 0 x a ∧ PairM 0 a y

/-- **A justified line** of a `provDP`-derivation: an old step, modus ponens, or
substitution of numerals. -/
def DLineP (c d k : N.Dom) : Prop :=
  ∃ y, BetaM c d k y ∧
    ((∃ w, ∃ js, ∃ u, PairM w js u ∧ ∃ q, PairM y u q ∧ StepM q ∧ PremsM c d k js) ∨
     (∃ i, i < k ∧ ∃ j, j < k ∧ ∃ a, ∃ b, ∃ r, ∃ yi, BetaM c d i yi ∧ JM a yi ∧
        ∃ yj, BetaM c d j yj ∧ JM b yj ∧ JM r y ∧ ∃ p, PairM b r p ∧ PairM 2 p a) ∨
     (∃ i, i < k ∧ ∃ u, ∃ yi, BetaM c d i yi ∧ JM u yi ∧ ∃ r, JM r y ∧ SubstM u r))

/-- A valid `provDP`-derivation code. -/
def DValidP (c d n : N.Dom) : Prop := ∀ k, k ≤ n → DLineP c d k

/-- **Derivable judgement** in the sense of `provDP`. -/
def DerP (y : N.Dom) : Prop := ∃ c, ∃ d, ∃ n, BetaM c d n y ∧ DValidP c d n

/-- **`provDP`-provability in `N`.** -/
def ProvDPM (x : N.Dom) : Prop := ∃ y, JM x y ∧ DerP y

/-- The Σ-definition of `ProvDPM`. -/
noncomputable def provDPDef : SUDef fun N e => ProvDPM (N := N) (e 0) := by
  unfold ProvDPM DerP DValidP DLineP JM SubstM FormOK TermOK Entry Quad PremsM LconsM PairM
  sudfn

end PAModel

open PAModel

/-- **The transparent derivation predicate of PA.** With free variable `0`: "there is a
derivation in the natural-deduction calculus for PA, whose modus-ponens steps and
numeral substitutions may be checked transparently, ending with `PA ⊢ x`". -/
noncomputable def provDP : Formula Arith := provDPDef.φ

/-- `provDP` is a Σ-formula. -/
theorem provDP_sig : SigP provDP := provDPDef.sig

/-- **Meaning of `provDP` in every model of PA.** -/
theorem sat_provDP_M (N : PAModel) (e : Nat → N.Dom) : Sat N.M e provDP ↔ ProvDPM (e 0) :=
  provDPDef.spec N e

/-- Meaning of `□_DP φ` in every model of PA. -/
theorem sat_box_provDP (N : PAModel) (e : Nat → N.Dom) (φ : Formula Arith) :
    Sat N.M e (box provDP φ) ↔ ProvDPM ((fcode φ : Nat) : N.Dom) := by
  rw [box, sat_inst, sat_provDP_M]
  exact Iff.of_eq (congrArg ProvDPM (eval_numeral_M e _))

end Foundations.Logic.FO
