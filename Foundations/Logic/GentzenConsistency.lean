import Foundations.Logic.CutElimination
import Foundations.Logic.Ordinals

/-!
# Gentzen's consistency proof for arithmetic (1936): an account

This file is mostly commentary. It explains how the propositional Hauptsatz of
`CutElimination` grows into Gentzen's consistency proof for Peano arithmetic, states
precisely which parts of that proof are formalised in this project and which are
not, and proves the one abstract principle on which the proof turns: *a reduction
procedure that lowers an ordinal below ε₀ shows that no bad object exists*.

## Hilbert's programme and Gödel

Hilbert's programme (1920s) proposed to secure classical mathematics by proving the
consistency of formal systems such as PA by *finitary* means: elementary
combinatorial reasoning about derivations as finite strings of symbols. Gödel's
second incompleteness theorem (1931; formalised for PA in `DerivabilityConditions`)
shows that no consistent system containing PA can prove its own consistency — so
any consistency proof of PA must use some principle not available in PA itself.

## Gentzen 1936

Gentzen's answer (*Die Widerspruchsfreiheit der reinen Zahlentheorie*, 1936;
revised proof 1938) identifies that principle exactly. He formulates PA as a sequent
calculus with an *induction rule*

`Γ, A(a) ⊢ A(a+1), Δ`
`――――――――――――――――――――`
`Γ, A(0) ⊢ A(t), Δ`

and with mathematical axioms only quantifier-free (atomic) equations. Cut can no
longer be eliminated outright: the induction rule blocks the reduction steps used
for pure logic. But *a derivation of the empty sequent* can always be transformed into
another derivation of the empty sequent that is, in a precise sense, simpler.

* To each derivation `d` Gentzen assigns an **ordinal** `o(d) < ε₀`, computed from
  the tree structure, the cut grades and the induction inferences (heights of cuts
  enter as exponents — hence towers `ω^ω^…`, hence ε₀).
* He gives a **reduction step**: any derivation of the empty sequent `⊢` (with an
  end-piece containing no logical rules) can be rewritten — by eliminating a
  suitable cut, or by unfolding an induction inference into finitely many cuts once
  its term has been evaluated to a numeral — into another derivation of `⊢` with a
  *strictly smaller* ordinal.
* Since there are no infinite descending sequences of ordinals below ε₀, there can
  be no derivation of `⊢` at all: **PA is consistent**.

The proof uses only finitary reasoning together with **transfinite induction up to
ε₀** (for quantifier-free, indeed primitive recursive, predicates). In 1943 Gentzen
showed that PA proves transfinite induction up to each ordinal `α < ε₀` but not up
to ε₀ itself, so the principle is optimal: ε₀ is the *proof-theoretic ordinal* of
PA. This was the start of *ordinal analysis*. Whether TI(ε₀) is "finitary" remains
a philosophical question; Gentzen argued that its evidence is constructive and
intuitive — one can survey how each descending sequence must terminate.

## The propositional case

For pure propositional logic (this project's `CutElimination`) no transfinite
ordinals are needed: the reduction terminates by a lexicographic induction on
(cut grade, derivation height), i.e. ordinals below `ω²`, and here even by plain
structural induction. The consistency argument has the same shape — derivations of
`⊢` are reduced to cut-free ones, of which there are none (`LK.consistent`).

## What is and isn't formalised

Formalised in this project:

* the sequent calculus `LK` for classical propositional logic, cut elimination, the
  subformula property and syntactic consistency (`SequentCalculus`,
  `CutElimination`, `SequentEquivalence`);
* ordinal notations below ε₀ in Cantor normal form and the **well-foundedness** of
  their order (`Ordinals.ON.wellFounded_R`), proved by Gentzen-style double
  transfinite induction — in Lean's metatheory, not in PA;
* Goodstein's theorem via ε₀ (`Goodstein`), whose unprovability in PA (Kirby–Paris
  1982) is *not* formalised;
* the abstract descent principle below.

*Not* formalised: first-order and arithmetical sequent calculi with the induction
rule, Gentzen's ordinal assignment, the reduction steps and the verification that
they lower the ordinal, and Gentzen's 1943 theorem that PA does not prove TI(ε₀).
In particular **the consistency of PA is not proved by Gentzen's method here**.
(Within this project PA's consistency is proved instead, non-finitarily, from the
existence of its standard model: `PA_consistent` in `PeanoArithmetic`.)
-/

namespace Foundations.Logic.Gentzen

open Ordinals Ordinals.ON

/-- **Consistency by ordinal descent** (the abstract form of Gentzen's argument).
Let `D` be a type of objects (e.g. derivations), `Bad` a property of them (e.g. "is
a derivation of the empty sequent"), and `o` an assignment of ordinal notations
below ε₀ in Cantor normal form. If every bad object can be reduced to a bad object of
strictly smaller ordinal, then no object is bad. The proof is transfinite induction
up to ε₀, i.e. the well-foundedness theorem `wellFounded_R`. -/
theorem consistency_by_descent {D : Type} (Bad : D → Prop) (o : D → ON)
    (hNF : ∀ d, NF (o d)) (reduce : ∀ d, Bad d → ∃ d', Bad d' ∧ lt (o d') (o d)) :
    ∀ d, ¬ Bad d := by
  have key : ∀ x, Acc R x → ∀ d, o d = x → ¬ Bad d := by
    intro x hx
    induction hx with
    | intro x _ ih =>
        intro d hd hbad
        obtain ⟨d', hbad', hlt⟩ := reduce d hbad
        exact ih (o d') ⟨hNF d', hd ▸ hlt⟩ d' rfl hbad'
  exact fun d => key (o d) (wellFounded_R.apply _) d rfl

/-- **Termination of ordinal-decreasing reduction.** If a reduction procedure maps
objects to objects with strictly smaller ordinal (below ε₀) as long as some
condition `Reducible` holds, then iterating it from any start reaches, after finitely
many steps, an object that is no longer reducible. -/
theorem reduction_terminates {D : Type} (Reducible : D → Prop) (step : D → D) (o : D → ON)
    (hNF : ∀ d, NF (o d)) (hstep : ∀ d, Reducible d → lt (o (step d)) (o d)) (d : D) :
    ∃ k, ¬ Reducible (Nat.repeat step k d) := by
  apply Classical.byContradiction
  intro hall
  have hall' : ∀ k, Reducible (Nat.repeat step k d) := fun k =>
    Classical.byContradiction fun h => hall ⟨k, h⟩
  exact no_infinite_descent (fun k => o (Nat.repeat step k d))
    (fun k => ⟨hNF _, hstep _ (hall' k)⟩)

/-- **The propositional instance.** For pure propositional logic Gentzen's
conclusion — the empty sequent is underivable — holds by cut elimination alone,
without transfinite ordinals. (A restatement of `Sequent.LK.consistent`.) -/
theorem propositional_consistency : ¬ Sequent.LK [] [] := Sequent.LK.consistent

end Foundations.Logic.Gentzen
