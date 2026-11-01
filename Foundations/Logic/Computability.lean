/-!
# Partial recursive functions

What does it mean for a function on the natural numbers to be *computable*? In
1936 several answers were proposed independently — Turing's machines, Church's
λ-calculus, and the **general recursive functions** of Herbrand, Gödel and Kleene —
and all turned out to define the same class of functions. The *Church–Turing
thesis* asserts that this class captures the informal notion of effective
computability.

We formalise Kleene's version (1936–38). A **code** is a finite description of an
algorithm, built from

* the constant `zero`, the successor `succ`, and projections `proj i`;
* **composition** `comp f (g₀, …, g_{k-1})`: compute all `gᵢ(x⃗)`, then feed the
  results to `f`;
* **primitive recursion** `prec f g`: `h(0, x⃗) = f(x⃗)` and
  `h(m+1, x⃗) = g(m, h(m, x⃗), x⃗)`;
* **minimisation** `mu f`: the least `n` with `f(n, x⃗) = 0` — an *unbounded search*,
  which may run forever.

Because of unbounded search, an algorithm may fail to halt, so codes denote
*partial* functions. Rather than computing with a "fuel" bound, we define
evaluation as an inductive **relation** `Eval c xs n` ("on inputs `xs`, code `c`
halts with output `n`"): a derivation of `Eval c xs n` is a finite record of a
terminating computation. We prove that evaluation is **deterministic**, and exhibit
codes for addition, multiplication, truncated subtraction, and Cantor's pairing
function together with its inverse.

Arities are not enforced by types: arguments form a list, missing arguments read
as `0` and surplus ones are ignored. (This is a harmless simplification.)
-/

namespace Foundations.Logic.Computability

/-- **Codes of partial recursive functions.** Finite descriptions of algorithms
built from zero, successor and projections by composition, primitive recursion and
minimisation (unbounded search). -/
inductive Code : Type where
  /-- The constant function `0`. -/
  | zero : Code
  /-- The successor of the first argument. -/
  | succ : Code
  /-- The `i`-th argument (counting from `0`). -/
  | proj (i : Nat) : Code
  /-- Composition: `comp f gs (x⃗) = f(gs 0 (x⃗), …, gs (k-1) (x⃗))`. -/
  | comp {k : Nat} (f : Code) (gs : Fin k → Code) : Code
  /-- Primitive recursion on the first argument. -/
  | prec (f g : Code) : Code
  /-- Minimisation: the least `n` such that `f(n, x⃗) = 0`. -/
  | mu (f : Code) : Code

open Code

/-- **Big-step evaluation.** `Eval c xs n` means: run on the argument list `xs`, the
algorithm `c` halts with output `n`. Non-termination is the absence of any `n`. -/
inductive Eval : Code → List Nat → Nat → Prop where
  /-- `zero` outputs `0`. -/
  | zero {xs} : Eval .zero xs 0
  /-- `succ` outputs the first argument plus one. -/
  | succ {xs} : Eval .succ xs (xs.headD 0 + 1)
  /-- `proj i` outputs the `i`-th argument. -/
  | proj {i xs} : Eval (.proj i) xs (xs.getD i 0)
  /-- Composition: if each `gs i` outputs `vs i`, and `f` outputs `n` on these values,
  the composite outputs `n`. -/
  | comp {k : Nat} {f : Code} {gs : Fin k → Code} {xs : List Nat} {n : Nat}
      (vs : Fin k → Nat) : (∀ i, Eval (gs i) xs (vs i)) → Eval f (List.ofFn vs) n →
      Eval (.comp f gs) xs n
  /-- Primitive recursion, base case. -/
  | prec_zero {f g xs n} : Eval f xs n → Eval (.prec f g) (0 :: xs) n
  /-- Primitive recursion, step case. -/
  | prec_succ {f g m xs r n} : Eval (.prec f g) (m :: xs) r → Eval g (m :: r :: xs) n →
      Eval (.prec f g) ((m + 1) :: xs) n
  /-- Minimisation: `f(n, x⃗) = 0`, and `f(m, x⃗)` is defined and non-zero for all `m < n`
  (the values `ks m + 1` witness this). -/
  | mu {f xs n} (ks : Nat → Nat) : Eval f (n :: xs) 0 →
      (∀ m, m < n → Eval f (m :: xs) (ks m + 1)) → Eval (.mu f) xs n

/-- Code `c` **halts** on input list `xs`. -/
def Halts (c : Code) (xs : List Nat) : Prop := ∃ n, Eval c xs n

/-- **Determinism.** A computation has at most one result. -/
theorem Eval.det {c : Code} {xs : List Nat} {n : Nat} (h : Eval c xs n) :
    ∀ {m}, Eval c xs m → n = m := by
  induction h with
  | zero => intro m h; cases h; rfl
  | succ => intro m h; cases h; rfl
  | proj => intro m h; cases h; rfl
  | comp vs _ _ ihg ihf =>
      intro m h
      cases h with
      | comp vs' hg' hf' =>
          have : vs = vs' := funext fun i => ihg i (hg' i)
          subst this
          exact ihf hf'
  | prec_zero _ ih => intro m h; cases h with | prec_zero h' => exact ih h'
  | prec_succ _ _ ih₁ ih₂ =>
      intro m h
      cases h with
      | prec_succ h₁ h₂ =>
          have := ih₁ h₁
          subst this
          exact ih₂ h₂
  | @mu f xs n ks _ _ ih₀ ihlt =>
      intro m h
      cases h with
      | mu ks' h₀' hlt' =>
          rcases Nat.lt_trichotomy n m with hnm | rfl | hmn
          · exact absurd (ih₀ (hlt' n hnm)) (by omega)
          · rfl
          · exact absurd (ihlt m hmn h₀') (by omega)

/-! ## Helpers for building codes -/

/-- A one-element tuple. -/
def vec1 {α : Type} (a : α) : Fin 1 → α := fun _ => a

/-- A two-element tuple. -/
def vec2 {α : Type} (a b : α) : Fin 2 → α := fun i => if i.val = 0 then a else b

/-- Evaluating a composition with one inner function. -/
theorem eval_comp1 {f g : Code} {xs : List Nat} {v n : Nat} (hg : Eval g xs v)
    (hf : Eval f [v] n) : Eval (.comp f (vec1 g)) xs n :=
  .comp (vec1 v) (fun _ => hg) hf

/-- Evaluating a composition with two inner functions. -/
theorem eval_comp2 {f g₀ g₁ : Code} {xs : List Nat} {v₀ v₁ n : Nat} (h₀ : Eval g₀ xs v₀)
    (h₁ : Eval g₁ xs v₁) (hf : Eval f [v₀, v₁] n) : Eval (.comp f (vec2 g₀ g₁)) xs n := by
  refine .comp (vec2 v₀ v₁) (fun i => ?_) hf
  match i with
  | ⟨0, _⟩ => exact h₀
  | ⟨1, _⟩ => exact h₁

/-- Inverting a composition with one inner function. -/
theorem eval_comp1_inv {f g : Code} {xs : List Nat} {n : Nat}
    (h : Eval (.comp f (vec1 g)) xs n) : ∃ v, Eval g xs v ∧ Eval f [v] n := by
  cases h with
  | comp vs hg hf => exact ⟨vs 0, hg 0, by
      have : List.ofFn vs = [vs 0] := rfl
      rwa [this] at hf⟩

/-- Inverting a composition with two inner functions. -/
theorem eval_comp2_inv {f g₀ g₁ : Code} {xs : List Nat} {n : Nat}
    (h : Eval (.comp f (vec2 g₀ g₁)) xs n) :
    ∃ v₀ v₁, Eval g₀ xs v₀ ∧ Eval g₁ xs v₁ ∧ Eval f [v₀, v₁] n := by
  cases h with
  | comp vs hg hf => exact ⟨vs 0, vs 1, hg 0, hg 1, by
      have : List.ofFn vs = [vs 0, vs 1] := rfl
      rwa [this] at hf⟩

/-! ## Some computable functions -/

/-- A code for the constant function with value `n`. -/
def constCode : Nat → Code
  | 0 => .zero
  | n + 1 => .comp .succ (vec1 (constCode n))

/-- `constCode n` outputs `n` on any input. -/
theorem eval_const (xs : List Nat) : ∀ n, Eval (constCode n) xs n
  | 0 => .zero
  | n + 1 => eval_comp1 (eval_const xs n) .succ

/-- **Addition is computable**: `add(a, b) = a + b`, by recursion on `a`. -/
abbrev addCode : Code := .prec (.proj 0) (.comp .succ (vec1 (.proj 1)))

/-- `addCode` computes addition. -/
theorem eval_add (b : Nat) (xs : List Nat) : ∀ a, Eval addCode (a :: b :: xs) (a + b)
  | 0 => by
      have := Eval.prec_zero (f := .proj 0) (g := .comp .succ (vec1 (.proj 1))) (xs := b :: xs)
        (n := b) .proj
      simpa using this
  | a + 1 => by
      have := Eval.prec_succ (eval_add b xs a)
        (eval_comp1 (g := .proj 1) (xs := a :: (a + b) :: b :: xs) .proj .succ)
      simpa [Nat.add_right_comm] using this

/-- **Multiplication is computable**: `mul(a, b) = a * b`, by recursion on `a`. -/
abbrev mulCode : Code := .prec .zero (.comp addCode (vec2 (.proj 1) (.proj 2)))

/-- `mulCode` computes multiplication. -/
theorem eval_mul (b : Nat) (xs : List Nat) : ∀ a, Eval mulCode (a :: b :: xs) (a * b)
  | 0 => by
      have := Eval.prec_zero (f := .zero)
        (g := .comp addCode (vec2 (.proj 1) (.proj 2))) (xs := b :: xs) .zero
      simpa using this
  | a + 1 => by
      have := Eval.prec_succ (eval_mul b xs a)
        (eval_comp2 (xs := a :: (a * b) :: b :: xs) .proj .proj (eval_add b [] (a * b)))
      simpa [Nat.succ_mul] using this

/-- **Predecessor is computable**: `pred(a) = a - 1` (with `pred 0 = 0`). -/
abbrev predCode : Code := .prec .zero (.proj 0)

/-- `predCode` computes the predecessor. -/
theorem eval_pred (xs : List Nat) : ∀ a, Eval predCode (a :: xs) (a - 1)
  | 0 => Eval.prec_zero .zero
  | a + 1 => by simpa using Eval.prec_succ (eval_pred xs a) (.proj (i := 0))

/-- **Truncated subtraction is computable**: `monus(a, b) = b - a` (zero if `a > b`). -/
abbrev monusCode : Code := .prec (.proj 0) (.comp predCode (vec1 (.proj 1)))

/-- `monusCode` computes truncated subtraction `b - a`. -/
theorem eval_monus (b : Nat) (xs : List Nat) : ∀ a, Eval monusCode (a :: b :: xs) (b - a)
  | 0 => by
      have := Eval.prec_zero (f := .proj 0)
        (g := .comp predCode (vec1 (.proj 1))) (xs := b :: xs) (n := b) .proj
      simpa using this
  | a + 1 => by
      have := Eval.prec_succ (eval_monus b xs a)
        (eval_comp1 (g := .proj 1) (xs := a :: (b - a) :: b :: xs) .proj (eval_pred [] (b - a)))
      rw [show b - (a + 1) = b - a - 1 by omega]
      simpa using this

/-! ## Cantor pairing -/

/-- Triangular numbers `tri s = 0 + 1 + ⋯ + s`. -/
def tri : Nat → Nat
  | 0 => 0
  | s + 1 => tri s + s + 1

/-- Triangular numbers are monotone. -/
theorem tri_mono {m n : Nat} (h : m ≤ n) : tri m ≤ tri n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (by simp [tri]; omega)

/-- **Cantor's pairing function** `⟨a, b⟩ = tri (a + b) + a`, a bijection `ℕ × ℕ → ℕ`. -/
def pair (a b : Nat) : Nat := tri (a + b) + a

/-- Every number lies on a unique diagonal: `n = tri s + a` with `a ≤ s`. -/
theorem exists_tri_decomp : ∀ n, ∃ s a, a ≤ s ∧ n = tri s + a
  | 0 => ⟨0, 0, Nat.le_refl _, rfl⟩
  | n + 1 => by
      obtain ⟨s, a, ha, rfl⟩ := exists_tri_decomp n
      by_cases h : a < s
      · exact ⟨s, a + 1, h, by omega⟩
      · exact ⟨s + 1, 0, Nat.zero_le _, by simp [tri]; omega⟩

/-- The diagonal decomposition is unique. -/
theorem tri_decomp_unique {s a s' a' : Nat} (ha : a ≤ s) (ha' : a' ≤ s')
    (h : tri s + a = tri s' + a') : s = s' ∧ a = a' := by
  rcases Nat.lt_trichotomy s s' with hs | rfl | hs
  · have := tri_mono (Nat.succ_le_of_lt hs); simp [tri] at this; omega
  · omega
  · have := tri_mono (Nat.succ_le_of_lt hs); simp [tri] at this; omega

/-- Cantor pairing is injective. -/
theorem pair_inj {a b a' b' : Nat} (h : pair a b = pair a' b') : a = a' ∧ b = b' := by
  obtain ⟨h₁, h₂⟩ := tri_decomp_unique (Nat.le_add_right a b) (Nat.le_add_right a' b') h
  omega

/-- A code for the triangular numbers. -/
abbrev triCode : Code := .prec .zero (.comp addCode (vec2 (.proj 1) (.comp .succ (vec1 (.proj 0)))))

/-- `triCode` computes the triangular numbers. -/
theorem eval_tri (xs : List Nat) : ∀ s, Eval triCode (s :: xs) (tri s)
  | 0 => Eval.prec_zero .zero
  | s + 1 => by
      have := Eval.prec_succ (eval_tri xs s)
        (eval_comp2 (xs := s :: tri s :: xs) .proj (eval_comp1 .proj .succ)
          (eval_add (s + 1) [] (tri s)))
      simpa [tri, Nat.add_assoc] using this

/-- **Pairing is computable.** -/
abbrev pairCode : Code := .comp addCode (vec2 (.comp triCode (vec1 addCode)) (.proj 0))

/-- `pairCode` computes Cantor's pairing function. -/
theorem eval_pair (a b : Nat) (xs : List Nat) : Eval pairCode (a :: b :: xs) (pair a b) :=
  eval_comp2 (eval_comp1 (eval_add b xs a) (eval_tri [] _)) .proj (eval_add a [] _)

/-- The diagonal of `n`: the least `s` with `n < tri (s + 1)`, found by unbounded
search. -/
abbrev diagCode : Code :=
  .mu (.comp monusCode (vec2 (.comp triCode (vec1 (.comp .succ (vec1 (.proj 0)))))
    (.comp .succ (vec1 (.proj 1)))))

/-- `diagCode` finds the diagonal `s` of `n = tri s + a` (`a ≤ s`). -/
theorem eval_diag {s a : Nat} (ha : a ≤ s) (xs : List Nat) :
    Eval diagCode ((tri s + a) :: xs) s := by
  have body : ∀ m, Eval (.comp monusCode (vec2 (.comp triCode (vec1 (.comp .succ (vec1 (.proj 0)))))
      (.comp .succ (vec1 (.proj 1))))) (m :: (tri s + a) :: xs) ((tri s + a + 1) - tri (m + 1)) :=
    fun m => eval_comp2 (eval_comp1 (eval_comp1 .proj .succ) (eval_tri [] _))
      (eval_comp1 .proj .succ) (eval_monus _ [] _)
  refine .mu (fun m => tri s + a - tri (m + 1)) ?_ (fun m hm => ?_)
  · have := body s
    rwa [show tri s + a + 1 - tri (s + 1) = 0 by simp [tri]; omega] at this
  · have h₁ := tri_mono (show m + 1 ≤ s by omega)
    have := body m
    rwa [show tri s + a + 1 - tri (m + 1) = tri s + a - tri (m + 1) + 1 by omega] at this

/-- **Unpairing, first component, is computable.** -/
abbrev leftCode : Code := .comp monusCode (vec2 (.comp triCode (vec1 diagCode)) (.proj 0))

/-- **Unpairing, second component, is computable.** -/
abbrev rightCode : Code := .comp monusCode (vec2 leftCode diagCode)

/-- `leftCode` recovers the first component of a pair. -/
theorem eval_left (a b : Nat) (xs : List Nat) : Eval leftCode (pair a b :: xs) a := by
  have hd := eval_diag (Nat.le_add_right a b) xs
  have := eval_comp2 (eval_comp1 hd (eval_tri [] (a + b))) (.proj (i := 0))
    (eval_monus (pair a b) [] (tri (a + b)))
  simpa [pair] using this

/-- `rightCode` recovers the second component of a pair. -/
theorem eval_right (a b : Nat) (xs : List Nat) : Eval rightCode (pair a b :: xs) b := by
  have hd := eval_diag (Nat.le_add_right a b) xs
  have := eval_comp2 (eval_left a b xs) hd (eval_monus (a + b) [] a)
  simpa using this

/-- Unpairing is total: every number is a pair. -/
theorem exists_pair (n : Nat) : ∃ a b, n = pair a b := by
  obtain ⟨s, a, ha, rfl⟩ := exists_tri_decomp n
  exact ⟨a, s - a, by simp [pair, Nat.add_sub_cancel' ha]⟩

end Foundations.Logic.Computability
