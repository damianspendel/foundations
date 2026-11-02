import Foundations.Constructible.LModel

/-!
# Absoluteness of bounded formulas

## Why absoluteness matters

A statement about sets is **absolute** for a class `M` if it means the same thing whether its
quantifiers range over `M` or over the whole universe. Absoluteness is the central tool of
Gödel's theory of `L`. To prove that `V = L` holds *inside* `L`, one shows that the whole
construction `α ↦ L_α` is absolute for `L`, so that `L` computes its own hierarchy correctly. To
prove that choice and GCH hold in `L`, one uses that the definable well-ordering of `L` and the
condensation argument are absolute. Forcing has nothing comparable: a generic extension `M[G]`
contains sets that `M` cannot even name. Inner models like `L` agree with the universe on every
absolute statement.

## What is proved here

The basic absoluteness theorem: a **bounded** (`Δ₀`) formula, in which every quantifier is of
the form `∀y ∈ x` or `∃y ∈ x`, is absolute for every transitive class (`delta0_absolute`). The
proof is a direct induction: a bounded quantifier over `x ∈ M` only ever looks at members of
`x`, and these lie in `M` by transitivity.

Applied to `L`: being transitive and being an ordinal are bounded properties, so the ordinals of
`L` in the sense of `L` are the true ordinals (`L_ordinal_iff`). Together with `ordinals_Lev`
(every ordinal is constructible), `L` contains all ordinals and recognises them correctly.

The much harder absoluteness of the formula "`x ∈ L_α`" itself, which needs a set-theoretic
formalisation of the satisfaction relation inside `LSet`, is **not** done; see the aggregator
`Constructible`.
-/

namespace Foundations.Constructible

open Foundations.Logic.FO Foundations.Forcing Foundations.Sets Foundations.Sets.ZFSet

/-- Bounded (`Δ₀`) formulas. Atomic formulas, closed under the connectives and under the
bounded quantifiers `∀y (y ∈ x → φ)` and `∃y (y ∈ x ∧ φ)`, where the bound `x` is the variable
with index `k` outside the quantifier (index `k + 1` inside). -/
inductive IsDelta0 : Formula LSet → Prop
  /-- `⊥` is bounded. -/
  | bot : IsDelta0 .bot
  /-- Equations are bounded. -/
  | eq (t s : Term LSet) : IsDelta0 (.eq t s)
  /-- Atomic membership statements are bounded. -/
  | rel {n : Nat} (R : LSet.Rel n) (ts : Fin n → Term LSet) : IsDelta0 (.rel R ts)
  /-- Implications of bounded formulas are bounded. -/
  | imp {φ ψ : Formula LSet} : IsDelta0 φ → IsDelta0 ψ → IsDelta0 (.imp φ ψ)
  /-- Conjunctions of bounded formulas are bounded. -/
  | conj {φ ψ : Formula LSet} : IsDelta0 φ → IsDelta0 ψ → IsDelta0 (.conj φ ψ)
  /-- Disjunctions of bounded formulas are bounded. -/
  | disj {φ ψ : Formula LSet} : IsDelta0 φ → IsDelta0 ψ → IsDelta0 (.disj φ ψ)
  /-- The bounded universal quantifier `∀y ∈ x_k, φ`. -/
  | ball (k : Nat) {φ : Formula LSet} : IsDelta0 φ →
      IsDelta0 (.all (.imp (memF (v 0) (v (k + 1))) φ))
  /-- The bounded existential quantifier `∃y ∈ x_k, φ`. -/
  | bex (k : Nat) {φ : Formula LSet} : IsDelta0 φ →
      IsDelta0 (.ex (.conj (memF (v 0) (v (k + 1))) φ))

/-- A class is **transitive** if members of its members belong to it. -/
def TransClass (P : ZFSet → Prop) : Prop := ∀ y z, P y → z ∈ y → P z

/-- Pushing a member of `P` onto an environment in `P`. -/
theorem cons_class {P : ZFSet → Prop} {x : ZFSet} {e : Nat → ZFSet} (hx : P x)
    (he : ∀ n, P (e n)) : ∀ n, P (BEnv.cons x e n)
  | 0 => hx
  | n + 1 => he n

/-- **`Δ₀`-absoluteness.** A bounded formula is absolute for every transitive class `P`: for
parameters in `P`, its relativisation to `P` holds iff it holds in the whole universe. -/
theorem delta0_absolute {P : ZFSet → Prop} (hP : TransClass P) {φ : Formula LSet}
    (hφ : IsDelta0 φ) : ∀ e : Nat → ZFSet, (∀ n, P (e n)) →
      (RSat P e φ ↔ RSat (fun _ => True) e φ) := by
  induction hφ with
  | bot => exact fun _ _ => Iff.rfl
  | eq => exact fun _ _ => Iff.rfl
  | rel => exact fun _ _ => Iff.rfl
  | imp _ _ ih₁ ih₂ => exact fun e he => imp_congr (ih₁ e he) (ih₂ e he)
  | conj _ _ ih₁ ih₂ => exact fun e he => and_congr (ih₁ e he) (ih₂ e he)
  | disj _ _ ih₁ ih₂ => exact fun e he => or_congr (ih₁ e he) (ih₂ e he)
  | ball k _ ih =>
      intro e he
      show (∀ x, P x → x ∈ e k → RSat P _ _) ↔ (∀ x, True → x ∈ e k → RSat _ _ _)
      constructor
      · intro h x _ hx
        have hPx := hP _ _ (he k) hx
        exact (ih _ (cons_class hPx he)).1 (h x hPx hx)
      · intro h x hPx hx
        exact (ih _ (cons_class hPx he)).2 (h x trivial hx)
  | bex k _ ih =>
      intro e he
      show (∃ x, P x ∧ x ∈ e k ∧ RSat P _ _) ↔ (∃ x, True ∧ x ∈ e k ∧ RSat _ _ _)
      constructor
      · rintro ⟨x, hPx, hx, h⟩
        exact ⟨x, trivial, hx, (ih _ (cons_class hPx he)).1 h⟩
      · rintro ⟨x, _, hx, h⟩
        have hPx := hP _ _ (he k) hx
        exact ⟨x, hPx, hx, (ih _ (cons_class hPx he)).2 h⟩

/-- Absoluteness between transitive classes. A bounded formula means the same in any two
transitive classes, for parameters in both. -/
theorem delta0_absolute₂ {P Q : ZFSet → Prop} (hP : TransClass P) (hQ : TransClass Q)
    {φ : Formula LSet} (hφ : IsDelta0 φ) (e : Nat → ZFSet) (heP : ∀ n, P (e n))
    (heQ : ∀ n, Q (e n)) : RSat P e φ ↔ RSat Q e φ :=
  (delta0_absolute hP hφ e heP).trans (delta0_absolute hQ hφ e heQ).symm

/-- `L` is a transitive class. -/
theorem InL_transClass : TransClass InL := fun _ _ hy hz => hy.mem hz

/-- "`v₀` is transitive" is a bounded formula. -/
theorem transF_delta0 : IsDelta0 transF :=
  IsDelta0.ball 0 (IsDelta0.ball 0 (IsDelta0.rel _ _))

/-- "`v₀` is an ordinal" is a bounded formula. -/
theorem ordF_delta0 : IsDelta0 ordF := IsDelta0.conj transF_delta0 (IsDelta0.ball 0 transF_delta0)

/-- The formula `ordF` read in the whole universe says "is an ordinal". -/
theorem RSat_univ_ordF (x : ZFSet) (e : Nat → ZFSet) :
    RSat (fun _ => True) (BEnv.cons x e) ordF ↔ IsOrdinal x := by
  simp only [ordF, transF, RSat, RSat_memF, tv_var, cons_zero, cons_succ, true_implies]
  constructor
  · intro ⟨h₁, h₂⟩
    exact ⟨fun y hy w hw => h₁ y hy w hw, fun y hy z hz w hw => h₂ y hy z hz w hw⟩
  · intro ⟨h₁, h₂⟩
    exact ⟨fun y hy w hw => h₁ y hy hw, fun y hy z hz w hw => h₂ y hy z hz hw⟩

/-- **`L` recognises the ordinals correctly.** For constructible `x`, "`x` is an ordinal"
relativised to `L` holds iff `x` is an ordinal. Since every ordinal is constructible
(`ordinals_Lev`), the ordinals of `L` are exactly the ordinals. -/
theorem L_ordinal_iff {x : ZFSet} (hx : InL x) (e : Nat → ZFSet) (he : ∀ n, InL (e n)) :
    RSat InL (BEnv.cons x e) ordF ↔ IsOrdinal x :=
  (delta0_absolute InL_transClass ordF_delta0 _ (cons_class hx he)).trans (RSat_univ_ordF x e)

end Foundations.Constructible
