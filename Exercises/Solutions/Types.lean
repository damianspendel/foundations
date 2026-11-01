import Foundations.Types.STLC

/-!
# Exercises V: Types

Problems on Part V of the library (`Foundations/Types`): typing derivations in the simply
typed λ-calculus with products and sums, subject reduction and progress, and the untyped
λ-calculus with Church numerals.

Terms use **de Bruijn indices**: `var 0` is the variable bound by the nearest `lam`, `var 1`
the next one out, and so on. So `λx. λy. x` is `lam (lam (var 1))`. Contexts are lists of
types with the type of `var 0` first.

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in `Exercises/Problems/Types.lean`.
-/

namespace Exercises.Types

open Foundations.Types

/-! ## Typing derivations in the simply typed λ-calculus -/

section STLC

open Foundations.Types.STLC STLC.Term

/-- **Exercise 5.1 (★★) — A typing derivation: composition.** The composition combinator
`λg. λf. λx. g (f x)` has type `(B → C) → (A → B) → A → C` in the empty context.

Under Curry–Howard this is the proof of the hypothetical syllogism.

*Hint:* apply the typing rules from the outside in: three `HasType.lam`, then `HasType.app`
twice. The variable cases need `[A, A → B, B → C][i]? = some _`, which `rfl` proves.

*Uses:* the constructors of `HasType`. -/
theorem typing_compose (A B C : Ty) :
    HasType [] (lam (lam (lam (app (var 2) (app (var 1) (var 0))))))
      (.arr (.arr B C) (.arr (.arr A B) (.arr A C))) := by
  -- SOLUTION
  exact .lam (.lam (.lam (.app (.var rfl) (.app (.var rfl) (.var rfl)))))
  -- END

/-- **Exercise 5.2 (★★) — Swapping a pair.** `λp. ⟨snd p, fst p⟩ : A × B → B × A`.

*Hint:* `HasType.lam`, then `HasType.pair`, then the projection rules. The projections need
to know the type of `p`, so you may have to give `(A := A) (B := B)` explicitly to
`HasType.snd` and `HasType.fst`.

*Uses:* `HasType.lam`, `HasType.pair`, `HasType.fst`, `HasType.snd`, `HasType.var`. -/
theorem typing_swap (A B : Ty) :
    HasType [] (lam (pair (snd (var 0)) (fst (var 0)))) (.arr (.prod A B) (.prod B A)) := by
  -- SOLUTION
  exact .lam (.pair (.snd (A := A) (.var rfl)) (.fst (B := B) (.var rfl)))
  -- END

/-- **Exercise 5.3 (★★) — Swapping a sum.**
`λs. case s of inl x ⇒ inr x | inr y ⇒ inl y : A + B → B + A`.

*Hint:* in each branch of `case` the bound variable is `var 0`, with type `A` (left branch)
or `B` (right branch) pushed onto the context.

*Uses:* `HasType.case`, `HasType.inl`, `HasType.inr`. -/
theorem typing_sum_swap (A B : Ty) :
    HasType [] (lam (case (var 0) (inr (var 0)) (inl (var 0))))
      (.arr (.sum A B) (.sum B A)) := by
  -- SOLUTION
  exact .lam (.case (A := A) (B := B) (.var rfl) (.inr (.var rfl)) (.inl (.var rfl)))
  -- END

/-- **Exercise 5.4 (★) — β-reduction preserves types.** If `(λ. t) u` has type `B` in a
context `Γ`, so does the substituted body `t[u]`.

*Hint:* this is one β-step.

*Uses:* `subject_reduction`, `Step.beta`. -/
theorem typing_beta {Γ : Ctx} {t u : Term} {B : Ty} (h : HasType Γ (app (lam t) u) B) :
    HasType Γ (inst t u) B := by
  -- SOLUTION
  exact subject_reduction (Step.beta t u) h
  -- END

/-- **Exercise 5.5 (★★★) — No normal proof of falsehood.** There is no closed term in normal
form of the empty type `⊥`.

Under Curry–Howard: intuitionistic propositional logic has no cut-free proof of `⊥`.
(Combined with normalisation, this gives consistency.)

*Hint:* a closed, well-typed normal term is a value (an introduction form: `lam`, `pair`,
`inl`, `inr`). Do a case analysis on the term; in each value case, inverting the typing
derivation (`cases ht`) shows that its type cannot be `⊥`.

*Uses:* `normal_closed_isValue`, `IsValue`, inversion of `HasType`. -/
theorem no_normal_bot {t : Term} (ht : HasType [] t .bot) : ¬ Normal t := by
  -- SOLUTION
  intro hn
  have hv := normal_closed_isValue ht hn
  cases t <;> simp only [IsValue] at hv <;> cases ht
  -- END

end STLC

/-! ## The untyped λ-calculus -/

section Untyped

open Foundations.Types.Lambda Lambda.Term

/-- **Exercise 5.6 (★★) — Adding two with Church numerals.** Applying the Church successor
twice to `n̄` reduces to the numeral for `n + 2`.

*Hint:* reduce the inner application first (reduction inside the argument of an
application is `Red.appR`), then the outer one, and chain the two with `Star.trans`.

*Uses:* `csucc_church`, `Red.appR`, `Star.trans`. -/
theorem csucc_csucc_church (n : Nat) :
    Red (app csucc (app csucc (church n))) (church (n + 2)) := by
  -- SOLUTION
  exact Star.trans (Red.appR (csucc_church n)) (csucc_church (n + 1))
  -- END

/-- **Exercise 5.7 (★★) — Ω is not a number.** The looping term `Ω = (λx. x x)(λx. x x)` never
reduces to a Church numeral.

*Hint:* Church numerals are in normal form, but `Ω` has no normal form.

*Uses:* `Omega_no_nf`, `church_normal`, `HasNF`. -/
theorem omega_not_church (n : Nat) : ¬ Red Omega (church n) := by
  -- SOLUTION
  exact fun h => Omega_no_nf ⟨church n, h, church_normal n⟩
  -- END

end Untyped

end Exercises.Types
