import Foundations.Logic.GodelNumbering

/-!
# The limits of computation: halting, Rice, and incompleteness

**The halting problem** (Turing 1936; in Kleene's setting, the non-recursiveness of
the set `K`): there is no algorithm which, given (the number of) an algorithm `c`
and an input `x`, decides whether `c` halts on `x`. The proof is Cantor's diagonal
argument turned against algorithms. Given a would-be decider `h`, build the code
`d` that on input `e` *searches for a zero of* `h(e, e)` — so `d` halts on `e`
exactly when `h` says "`e` does not halt on `e`". Feeding `d` its own Gödel number
`⌜d⌝` yields: `d` halts on `⌜d⌝` iff `d` does not halt on `⌜d⌝`. Here both the
decider and the diagonal machine are honest codes, and the diagonal code is
written down explicitly.

**Rice's theorem** (1953): *no* non-trivial property of the function computed by a
code is decidable — not "is it total?", not "does it ever output 7?", nothing.
We reduce the halting problem to it, using the code-building code `rhoCode`
(an instance of the s-m-n theorem) from `GodelNumbering`.

**Incompleteness.** Finally, an *abstract* form of Gödel's first incompleteness
theorem, in the computational guise emphasised by Turing, Kleene and Post: no
formal system whose theorems can be listed by an algorithm, and which only proves
true statements of the form "`c` does not halt on `x`", can prove *all* true
statements of this form. The diagonal construction even produces an explicit true
but unprovable statement — a "Gödel sentence".

*What remains abstract.* The incompleteness theorem below is stated for an
arbitrary "proof system" given by a predicate `Provable c x` ("the system proves
that `c` does not halt on `x`"). Its hypotheses are exactly: (1) **soundness** for
these statements, and (2) **computable enumerability**: some code halts on
`(⌜c⌝, x)` exactly when `Provable c x`. To obtain Gödel's theorem for Peano
arithmetic itself one would additionally have to *arithmetise* evaluation —
express "`c` does not halt on `x`" by a PA sentence (representability of `Eval`) —
and show that PA's set of theorems is enumerated by a code (a proof checker
written as a partial recursive function). Neither step is carried out here.
-/

namespace Foundations.Logic.Computability

open Code

/-! ## The halting problem -/

/-- The diagonal code built from a would-be halting decider `h`: on input `e` it
searches for a zero of `h(e, e)`. -/
def diagonal (h : Code) : Code := .mu (.comp h (vec2 (.proj 1) (.proj 1)))

/-- The diagonal code halts on `e` iff `h(e, e) = 0`. -/
theorem halts_diagonal_iff (h : Code) (e : Nat) :
    Halts (diagonal h) [e] ↔ Eval h [e, e] 0 := by
  constructor
  · rintro ⟨n, hn⟩
    cases hn with
    | mu _ h₀ _ =>
        obtain ⟨v₀, v₁, h₁, h₂, h₃⟩ := eval_comp2_inv h₀
        cases h₁; cases h₂
        exact h₃
  · intro h₀
    exact ⟨0, .mu (fun _ => 0) (eval_comp2 .proj .proj h₀) (fun m hm => absurd hm (by omega))⟩

/-- **No code recognises non-halting by outputting zero.** There is no code `h` such
that `h(⌜c⌝, x) = 0` exactly when `c` does not halt on `x`. -/
theorem no_code_zero_iff_not_halts :
    ¬ ∃ h : Code, ∀ (c : Code) (x : Nat), Eval h [encode c, x] 0 ↔ ¬ Halts c [x] := by
  rintro ⟨h, hh⟩
  let d := diagonal h
  have h₁ := halts_diagonal_iff h (encode d)
  have h₂ := hh d (encode d)
  by_cases hd : Halts d [encode d]
  · exact h₂.1 (h₁.1 hd) hd
  · exact hd (h₁.2 (h₂.2 hd))

/-- **Undecidability of the halting problem** (Turing 1936). There is no code `h`
that is total on (Gödel numbers of codes, inputs) and outputs `1` when `c` halts on
`x` and `0` when it does not. -/
theorem halting_undecidable :
    ¬ ∃ h : Code, ∀ (c : Code) (x : Nat),
      (Eval h [encode c, x] 0 ∨ Eval h [encode c, x] 1) ∧
      (Eval h [encode c, x] 1 ↔ Halts c [x]) := by
  rintro ⟨h, hh⟩
  refine no_code_zero_iff_not_halts ⟨h, fun c x => ⟨fun h0 hc => ?_, fun hc => ?_⟩⟩
  · have := Eval.det h0 ((hh c x).2.2 hc); omega
  · rcases (hh c x).1 with h0 | h1
    · exact h0
    · exact absurd ((hh c x).2.1 h1) hc

/-! ## Rice's theorem -/

/-- A code that never halts: it searches for a zero of `n ↦ n + 1`. -/
def loopCode : Code := .mu (.comp .succ (vec1 (.proj 0)))

/-- `loopCode` halts on no input. -/
theorem loopCode_diverges (xs : List Nat) (n : Nat) : ¬ Eval loopCode xs n := by
  intro h
  cases h with
  | mu _ h₀ _ =>
      obtain ⟨v, -, hv⟩ := eval_comp1_inv h₀
      cases hv

/-- If `c` halts on `x`, then `rho a c x` computes the same unary function as `a`. -/
theorem rho_of_halts {a c : Code} {x : Nat} (hc : Halts c [x]) (y n : Nat) :
    Eval (rho a c x) [y] n ↔ Eval a [y] n := by
  constructor
  · intro h
    obtain ⟨v₀, v₁, -, h₁, h₂⟩ := eval_comp2_inv h
    obtain ⟨u, hu, ha⟩ := eval_comp1_inv h₁
    cases hu; cases h₂
    exact ha
  · intro ha
    obtain ⟨v, hv⟩ := hc
    exact eval_comp2 (eval_comp1 (eval_const _ x) hv) (eval_comp1 .proj ha) .proj

/-- If `c` does not halt on `x`, then `rho a c x` halts on no unary input. -/
theorem rho_of_not_halts {a c : Code} {x : Nat} (hc : ¬ Halts c [x]) (y n : Nat) :
    ¬ Eval (rho a c x) [y] n := by
  intro h
  obtain ⟨v₀, v₁, h₀, -, -⟩ := eval_comp2_inv h
  obtain ⟨u, hu, hcu⟩ := eval_comp1_inv h₀
  have : u = x := Eval.det hu (eval_const _ x)
  subst this
  exact hc ⟨v₀, hcu⟩

/-- A code testing for zero: outputs `1` on `0` and `0` on positive numbers. -/
def isZeroCode : Code := .prec (constCode 1) .zero

/-- `isZeroCode` outputs `0` exactly on positive inputs. -/
theorem eval_isZero_zero_iff {v n : Nat} (h : Eval isZeroCode [v] n) : n = 0 ↔ v ≠ 0 := by
  cases v with
  | zero =>
      cases h with
      | prec_zero h' => have := Eval.det h' (eval_const [] 1); omega
  | succ v =>
      cases h with
      | prec_succ _ h' => cases h'; simp

/-- `isZeroCode` is total. -/
theorem isZero_total (v : Nat) : ∃ n, Eval isZeroCode [v] n := by
  cases v with
  | zero => exact ⟨1, .prec_zero (eval_const [] 1)⟩
  | succ v => exact ⟨0, .prec_succ (isZero_total v).choose_spec .zero⟩

/-- **Rice's theorem.** Let `P` be a property of codes that depends only on the
(unary) partial function they compute, and is non-trivial (some code has it, some
does not). Then `P` is undecidable: no code, total on Gödel numbers, outputs `0`
exactly on the numbers of codes lacking `P`. -/
theorem rice (P : Code → Prop)
    (hext : ∀ c c', (∀ x n, Eval c [x] n ↔ Eval c' [x] n) → (P c ↔ P c'))
    {a b : Code} (ha : P a) (hb : ¬ P b) :
    ¬ ∃ r : Code, ∀ c, Halts r [encode c] ∧ (Eval r [encode c] 0 ↔ ¬ P c) := by
  rintro ⟨r, hr⟩
  -- `P (rho a' c x)` is `P a'` or `P loopCode` according as `c` halts on `x`.
  have key : ∀ a' c x, (Halts c [x] → (P (rho a' c x) ↔ P a')) ∧
      (¬ Halts c [x] → (P (rho a' c x) ↔ P loopCode)) := fun a' c x =>
    ⟨fun hc => hext _ _ (rho_of_halts hc),
     fun hc => hext _ _ fun y n => ⟨fun h => absurd h (rho_of_not_halts hc y n),
       fun h => absurd h (loopCode_diverges _ _)⟩⟩
  -- evaluating `r` after `rhoCode a'`
  have comp_r : ∀ a' c x n, Eval (.comp r (vec1 (rhoCode a'))) [encode c, x] n ↔
      Eval r [encode (rho a' c x)] n := fun a' c x n =>
    ⟨fun h => by
      obtain ⟨v, hv, hrv⟩ := eval_comp1_inv h
      rwa [Eval.det hv (eval_rhoCode a' c x)] at hrv,
     fun h => eval_comp1 (eval_rhoCode a' c x) h⟩
  by_cases hloop : P loopCode
  · -- use `b`; then `P (rho b c x) ↔ ¬ Halts c x`, and we negate `r` with `isZeroCode`
    refine no_code_zero_iff_not_halts ⟨.comp isZeroCode (vec1 (.comp r (vec1 (rhoCode b)))),
      fun c x => ?_⟩
    obtain ⟨v, hv⟩ := (hr (rho b c x)).1
    have hv' := (comp_r b c x v).2 hv
    constructor
    · intro h0
      obtain ⟨w, hw, hz⟩ := eval_comp1_inv h0
      rw [Eval.det hw hv'] at hz
      have hv0 : v ≠ 0 := (eval_isZero_zero_iff hz).1 rfl
      intro hc
      have : P (rho b c x) := Classical.byContradiction fun hn => hv0
        (Eval.det hv ((hr _).2.2 hn))
      exact hb (((key b c x).1 hc).1 this)
    · intro hc
      have hP : P (rho b c x) := ((key b c x).2 hc).2 hloop
      have hv0 : v ≠ 0 := fun e => ((hr _).2.1 (e ▸ hv)) hP
      obtain ⟨n, hn⟩ := isZero_total v
      have : n = 0 := (eval_isZero_zero_iff hn).2 hv0
      exact eval_comp1 hv' (this ▸ hn)
  · -- use `a`; then `P (rho a c x) ↔ Halts c x`
    refine no_code_zero_iff_not_halts ⟨.comp r (vec1 (rhoCode a)), fun c x => ?_⟩
    rw [comp_r, (hr _).2]
    constructor
    · intro hn hc; exact hn (((key a c x).1 hc).2 ha)
    · intro hc hP; exact hloop (((key a c x).2 hc).1 hP)

/-! ## Incompleteness (abstract, computational form) -/

/-- The Gödel-sentence code for a proof enumerator `q`: on input `e`, it runs `q` on
`(e, e)`, i.e. it searches for a proof that "code `e` does not halt on `e`". -/
def godelCode (q : Code) : Code := .comp q (vec2 (.proj 0) (.proj 0))

/-- `godelCode q` halts on `e` iff `q` halts on `(e, e)`. -/
theorem halts_godelCode_iff (q : Code) (e : Nat) :
    Halts (godelCode q) [e] ↔ Halts q [e, e] := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨v₀, v₁, h₀, h₁, h⟩ := eval_comp2_inv hn
    cases h₀; cases h₁
    exact ⟨n, h⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, eval_comp2 .proj .proj hn⟩

/-- **Abstract incompleteness theorem** (computational form of Gödel's first
incompleteness theorem; *abstract* — see the module docstring for exactly which
hypotheses remain to be discharged for a concrete system such as PA).

Let `Provable c x` mean "the formal system proves that code `c` does not halt on
input `x`". Suppose the system is
* **sound** for such statements: it proves only true ones; and
* **computably enumerable**: some code `q` halts on `(⌜c⌝, x)` exactly when
  `Provable c x`.

Then the system is **incomplete**: there is an explicit code `c` and input `x` such
that `c` does not halt on `x`, yet this is not provable. Namely `c = godelCode q` and
`x = ⌜c⌝` — the statement "I am not provable", in computational dress. -/
theorem incompleteness (Provable : Code → Nat → Prop)
    (sound : ∀ c x, Provable c x → ¬ Halts c [x])
    {q : Code} (hq : ∀ c x, Halts q [encode c, x] ↔ Provable c x) :
    ¬ Halts (godelCode q) [encode (godelCode q)] ∧
      ¬ Provable (godelCode q) (encode (godelCode q)) := by
  let g := godelCode q
  have h₁ : Halts g [encode g] ↔ Provable g (encode g) :=
    (halts_godelCode_iff q (encode g)).trans (hq g (encode g))
  have hnp : ¬ Provable g (encode g) := fun hp => sound g _ hp (h₁.2 hp)
  exact ⟨fun hh => hnp (h₁.1 hh), hnp⟩

/-- **No sound, computably enumerable system proves all true non-halting statements.**
(A corollary of the abstract incompleteness theorem.) -/
theorem no_complete_sound_ce_system (Provable : Code → Nat → Prop)
    (sound : ∀ c x, Provable c x → ¬ Halts c [x])
    (ce : ∃ q : Code, ∀ c x, Halts q [encode c, x] ↔ Provable c x) :
    ¬ ∀ c x, ¬ Halts c [x] → Provable c x := by
  obtain ⟨q, hq⟩ := ce
  intro hcomplete
  obtain ⟨h₁, h₂⟩ := incompleteness Provable sound hq
  exact h₂ (hcomplete _ _ h₁)

end Foundations.Logic.Computability
