import Foundations.Logic.Undecidability

/-!
# Kleene's recursion theorem: programs that know their own code

Kleene's (second) recursion theorem (1938) says that self-reference is always
available to algorithms: for any computable procedure `F(e, y)` there is a program
`q` which, on input `y`, behaves exactly like `F(⌜q⌝, y)` — as if `q` had been
handed its own Gödel number. It is the computational counterpart of Gödel's
diagonal lemma ("for every property there is a sentence asserting that it itself has
the property"), and it explains *quines*: programs printing their own source code.

The proof is the diagonal trick once more, now at the level of syntax. From a
number `x` we can compute the number of the code
`selfApp x := "run code x on the inputs (x, y)"`; this needs only the arithmetic of
the Gödel numbering (`subCode`), never running `x`. Let `G(x, y) = F(⌜selfApp x⌝, y)`
and `q = selfApp ⌜G⌝`. Then `q(y) = G(⌜G⌝, y) = F(⌜selfApp ⌜G⌝⌝, y) = F(⌜q⌝, y)`.

*Scope.* We prove the theorem in the form "`q(y) ≃ F(⌜q⌝, y)` for every code `F`",
which is the heart of the matter. The textbook corollary "`φ_e = φ_{f(e)}` for every
total computable `f`" additionally needs a *universal* code (an interpreter
`U(e, y) ≃ φ_e(y)` written as a code); it is derived in `Universal`
(`recursion_theorem_fixed_point`).
-/

namespace Foundations.Logic.Computability

open Code

/-- `selfApp G` runs `G` on the inputs `(⌜G⌝, y)`: `G` applied to its own number. -/
def selfApp (G : Code) : Code := .comp G (vec2 (constCode (encode G)) (.proj 0))

/-- A code computing `⌜selfApp G⌝` from `⌜G⌝` (purely syntactic arithmetic). -/
def subCode : Code :=
  pairOf (constCode 3) (pairOf (.proj 0) (succOf (pairOf (.comp constEncCode (vec1 (.proj 0)))
    (succOf (pairOf (constCode (encode (.proj 0))) (constCode 0))))))

/-- `subCode` computes the Gödel number of `selfApp G` from that of `G`. -/
theorem eval_subCode (G : Code) (ys : List Nat) :
    Eval subCode (encode G :: ys) (encode (selfApp G)) := by
  simp only [selfApp, encode_comp2]
  exact eval_pairOf (eval_const _ 3) (eval_pairOf .proj (eval_succOf (eval_pairOf
    (eval_comp1 .proj (eval_constEnc [] _))
    (eval_succOf (eval_pairOf (eval_const _ _) (eval_const _ 0))))))

/-- Running `selfApp G` on `y` is running `G` on `(⌜G⌝, y)`. -/
theorem eval_selfApp (G : Code) (y n : Nat) :
    Eval (selfApp G) [y] n ↔ Eval G [encode G, y] n := by
  constructor
  · intro h
    obtain ⟨v₀, v₁, h₀, h₁, h⟩ := eval_comp2_inv h
    rw [Eval.det h₀ (eval_const _ _)] at h
    cases h₁
    exact h
  · intro h
    exact eval_comp2 (eval_const _ _) .proj h

/-- **Kleene's recursion theorem.** For every code `F` there is a code `q` that
computes `y ↦ F(⌜q⌝, y)`: a program with access to its own Gödel number. -/
theorem recursion_theorem (F : Code) :
    ∃ q : Code, ∀ y n, Eval q [y] n ↔ Eval F [encode q, y] n := by
  let G : Code := .comp F (vec2 subCode (.proj 1))
  refine ⟨selfApp G, fun y n => (eval_selfApp G y n).trans ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨v₀, v₁, h₀, h₁, h⟩ := eval_comp2_inv h
    rw [Eval.det h₀ (eval_subCode G [y])] at h
    cases h₁
    exact h
  · exact eval_comp2 (eval_subCode G [y]) .proj h

/-- **A quine.** There is a code which, on every input, outputs its own Gödel number. -/
theorem exists_quine : ∃ q : Code, ∀ y, Eval q [y] (encode q) := by
  obtain ⟨q, hq⟩ := recursion_theorem (.proj 0)
  exact ⟨q, fun y => (hq y _).2 .proj⟩

/-- A second proof of the undecidability of halting, via the recursion theorem: given
a would-be decider `h` (outputting `0` exactly on non-halting pairs), a program that
consults `h` about itself and does the opposite cannot exist. -/
theorem no_code_zero_iff_not_halts' :
    ¬ ∃ h : Code, ∀ (c : Code) (x : Nat), Eval h [encode c, x] 0 ↔ ¬ Halts c [x] := by
  rintro ⟨h, hh⟩
  -- `F(e, y)`: search for a zero of `h(e, y)`, i.e. halt iff `h` says "does not halt"
  obtain ⟨q, hq⟩ := recursion_theorem (.mu (.comp h (vec2 (.proj 1) (.proj 2))))
  have key : Halts q [encode q] ↔ Eval h [encode q, encode q] 0 := by
    constructor
    · rintro ⟨n, hn⟩
      cases (hq _ n).1 hn with
      | mu _ h₀ _ =>
          obtain ⟨v₀, v₁, h₁, h₂, h₃⟩ := eval_comp2_inv h₀
          cases h₁; cases h₂
          exact h₃
    · intro h₀
      exact ⟨0, (hq _ 0).2 (.mu (fun _ => 0) (eval_comp2 .proj .proj h₀)
        (fun m hm => absurd hm (by omega)))⟩
  by_cases hd : Halts q [encode q]
  · exact (hh q _).1 (key.1 hd) hd
  · exact hd (key.2 ((hh q _).2 hd))

end Foundations.Logic.Computability
