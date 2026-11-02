import Foundations.Logic.GodelIID3Sigma

/-!
# (D3) for a derivation predicate, and Gödel's second theorem for it

**The result.** The derivation predicate `provDP` — derivability in the natural-deduction
calculus for PA, with modus ponens and numeral substitution checked transparently
(`GodelIID3Defs`) — satisfies all three Hilbert–Bernays–Löb derivability conditions over
PA, and so Löb's theorem and Gödel's second incompleteness theorem hold for it
**unconditionally**:

* (D1) `provDP_D1` and (D2) `provDP_D2` (`GodelIID3Closure`);
* (D3) `provDP_D3`: `PA ⊢ □φ → □□φ`. Proof: in a model `N` of PA, suppose `provDP(⌜φ⌝)`
  holds. `provDP` is a Σ-formula, so by formalised Σ-completeness (`sig_complete`) the
  sentence `provDP(⌜φ⌝)` — that is, the instance of `provDP` at the numeral `⌜φ⌝` — is
  `provDP`-derivable in `N`. By completeness, PA proves `□□φ`.

Unlike `provH`, the predicate has no built-in necessitation rule and its axioms are not "all
theorems of PA". Every line is either one step of the calculus, or modus ponens, or an
instance of the admissible rule "from `PA ⊢ φ` infer `PA ⊢ φ(n̄₀, n̄₁, …)`". (D3) is obtained by the textbook
route — formalised Σ-completeness — carried out inside arbitrary models of PA: Gödel's 1931
sketch, as completed by Hilbert and Bernays (1939) and streamlined by Löb (1955).

**What remains intensional (Feferman 1960).** `provDP` checks the *other* rules of the
calculus with the Σ₁ graph of a program computing the step relation `paStep`. That program
is obtained by `Classical.choose` from a computability proof, so it is fixed but not
explicit. The formalised Σ-completeness argument does not need to know which program it is:
it works for every Σ-formula. Also, `provDP` and `provD` are *not* shown to be PA-provably
equivalent. Only `PA ⊢ provD(x) → provDP(x)` holds (`provD_imp_provDP`), and this does not
transfer Gödel II to `provD`. Condition (D3) for `provD` itself (`ProvDD3`) remains open,
because no line of `provD` with non-standard content can be verified inside a model.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability GodelII PAModel

/-- **Condition (D3) for `provDP`.** `PA ⊢ provDP(⌜φ⌝) → provDP(⌜provDP(⌜φ⌝)⌝)`. -/
theorem provDP_D3 (φ : Formula Arith) : PA ⊢₁ imp (box provDP φ) (box provDP (box provDP φ)) :=
  PA_proves_of_models fun N e => by
    simp only [Formula.Sat, sat_box_provDP]
    intro h
    let e' : Nat → Nat := Env.cons (fcode φ) fun _ => 0
    let w : Nat → N.Dom := fun m => (e' m : N.Dom)
    have hw : Sat N.M w provDP := (sat_provDP_M N w).2 (by
      show ProvDPM ((fcode φ : Nat) : N.Dom); exact h)
    -- formalised Σ-completeness: the instance `provDP(⌜φ⌝)` is derivable
    have hd : DerP (JN ((fcode (provDP.subst fun m => numeral (e' m)) : Nat) : N.Dom)) := by
      have := sig_complete provDP_sig w hw
      unfold Der at this
      rwa [codeM_cast0 e' provDP] at this
    -- the instance is PA-provably the box
    have hL : PA ⊢₁ imp (provDP.subst fun m => numeral (e' m)) (box provDP φ) :=
      PA_proves_of_models fun M e => by
        simp only [Formula.Sat, sat_subst, sat_provDP_M, sat_box_provDP]
        intro h'
        simp only [e', cons_0, eval_numeral_M] at h'
        exact h'
    exact (provDPM_iff _).2 (derP_mp (fcode_imp_cast _ _) (derP_of_proves hL) hd)

/-- **The derivability conditions hold for `provDP` over PA.** -/
theorem provDP_derivability : Derivability PA provDP :=
  ⟨fun _ h => provDP_D1 h, provDP_D2, provDP_D3⟩

/-- **Löb's theorem for the derivation predicate `provDP`.** If
`PA ⊢ provDP(⌜φ⌝) → φ`, then `PA ⊢ φ`. -/
theorem lob_provDP {φ : Formula Arith} (h : PA ⊢₁ imp (box provDP φ) φ) : PA ⊢₁ φ :=
  lob (fun _ h => PA_proves_Q h) provDP_derivability h

/-- **Gödel's second incompleteness theorem for the derivation predicate `provDP`.** PA does
not prove `¬provDP(⌜⊥⌝)`. Here `provDP` expresses "there is a derivation, in the
natural-deduction calculus for PA (modus ponens and numeral substitution also checked by
explicit formulas), of `x`" and defines PA-provability in `ℕ` (`sat_provDP`).
It satisfies (D1)–(D3), with (D3) obtained by formalised Σ-completeness, not built in. -/
theorem godel_second_provDP : ¬ PA ⊢₁ conF provDP :=
  godel_second (fun _ h => PA_proves_Q h) provDP_derivability PA_consistent

/-- `provDP` and `provH` have the same extension in `ℕ`. -/
theorem provDP_std_iff_provH (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provDP φ) ↔ Sat stdModel e (box provH φ) := by
  rw [sat_provDP, sat_provH]

/-- PA proves that `provDP`-consistency implies `provD`-consistency:
`PA ⊢ ¬provDP(⌜⊥⌝) → ¬provD(⌜⊥⌝)`. This is the wrong direction for transferring Gödel II
to `provD`. -/
theorem conDP_imp_conD : PA ⊢₁ imp (conF provDP) (conF provD) :=
  PA_proves_of_models fun N e => by
    simp only [conF, neg, Formula.Sat, sat_box_provD, sat_box_provDP]
    exact fun h hD => h (provDPM_of_provDM hD)

end Foundations.Logic.FO
