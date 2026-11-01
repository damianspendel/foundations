import Foundations.Logic.GodelNumbering

/-!
# A library of total computable functions

Writing algorithms directly as `Code`s is like programming a machine in its raw
instruction set: possible, but quickly unbearable. Before we can write substantial
programs — an *interpreter* for codes, a *proof checker* for arithmetic — we need the
equivalent of a high-level language. This file provides it.

The idea goes back to Gödel (1931) and Kleene (1936): show that the class of
computable functions is **closed** under many natural operations, so that a function
can be recognised as computable by the way it is *defined*, without ever writing its
code by hand. We work with *unary* functions `f : ℕ → ℕ` (several arguments are
packed into one number with Cantor's pairing function) and call `f` **computable**
(`Comp f`) if some code computes it on every input. We prove closure under

* pairing and unpairing, arithmetic (`+`, `×`, truncated `-`), constants;
* composition;
* **primitive recursion** (`natRec`): `h(n, 0) = b(n)`, `h(n, i + 1) = s(n, i, h(n, i))`;
* definition by cases, Boolean connectives, equality and order tests;
* bounded quantification `∀ i < m`;
* operations on **coded lists** (head, tail, `i`-th element, length);
* **course-of-values recursion** (`covRec`): a function whose value at `n` may
  depend on *all* earlier values `f(0), …, f(n − 1)` — the form of recursion
  needed to process tree-shaped data such as formulas, derivations, and
  computation traces, whose immediate parts have smaller Gödel numbers.

Finally, *unbounded search* turns a computable test `p(n, t)` into a code that halts
on `n` exactly when some witness `t` exists: this is how **computably enumerable**
sets arise.

Since every number is a pair, we also need a genuine inverse of Cantor's pairing
function; it is defined by counting along the diagonals.
-/

namespace Foundations.Logic.Computability

open Code

/-! ## Unpairing -/

/-- Inverse of Cantor's pairing, computed by walking along the diagonals:
the successor of `⟨a, b + 1⟩` is `⟨a + 1, b⟩`, and the successor of `⟨a, 0⟩` is
`⟨0, a + 1⟩`. -/
def unpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
      let p := unpair n
      if p.2 = 0 then (0, p.1 + 1) else (p.1 + 1, p.2 - 1)

/-- The first component of the pair coded by `n`. -/
def fst (n : Nat) : Nat := (unpair n).1

/-- The second component of the pair coded by `n`. -/
def snd (n : Nat) : Nat := (unpair n).2

/-- `unpair` really inverts `pair`: `⟨fst n, snd n⟩ = n`. -/
theorem pair_fst_snd : ∀ n, pair (fst n) (snd n) = n
  | 0 => rfl
  | n + 1 => by
      have ih := pair_fst_snd n
      simp only [fst, snd] at ih ⊢
      rw [unpair]
      generalize unpair n = p at ih ⊢
      obtain ⟨a, b⟩ := p
      simp only at ih ⊢
      by_cases h : b = 0
      · subst h
        simp only [↓reduceIte, pair, Nat.zero_add, Nat.add_zero, tri] at ih ⊢
        omega
      · simp only [h, ↓reduceIte] -- the step `⟨a, b⟩ ↦ ⟨a + 1, b - 1⟩`
        simp only [pair] at ih ⊢
        rw [show a + 1 + (b - 1) = a + b by omega]
        omega

/-- First projection of a pair. -/
@[simp] theorem fst_pair (a b : Nat) : fst (pair a b) = a :=
  (pair_inj (pair_fst_snd (pair a b))).1

/-- Second projection of a pair. -/
@[simp] theorem snd_pair (a b : Nat) : snd (pair a b) = b :=
  (pair_inj (pair_fst_snd (pair a b))).2

/-- Triangular numbers dominate their argument. -/
theorem le_tri : ∀ s, s ≤ tri s
  | 0 => Nat.le_refl _
  | s + 1 => by have := le_tri s; simp only [tri]; omega

/-- The first component is bounded by the pair. -/
theorem left_le_pair (a b : Nat) : a ≤ pair a b := Nat.le_add_left _ _

/-- The second component is bounded by the pair. -/
theorem right_le_pair (a b : Nat) : b ≤ pair a b := by
  have := le_tri (a + b); simp only [pair]; omega

/-- `fst n ≤ n`. -/
theorem fst_le (n : Nat) : fst n ≤ n := by
  have := left_le_pair (fst n) (snd n); rwa [pair_fst_snd] at this

/-- `snd n ≤ n`. -/
theorem snd_le (n : Nat) : snd n ≤ n := by
  have := right_le_pair (fst n) (snd n); rwa [pair_fst_snd] at this

/-- `pair 0 0 = 0`. -/
@[simp] theorem pair_zero_zero : pair 0 0 = 0 := rfl

/-- `fst 0 = 0`. -/
@[simp] theorem fst_zero : fst 0 = 0 := rfl

/-- `snd 0 = 0`. -/
@[simp] theorem snd_zero : snd 0 = 0 := rfl

/-! ## Computable functions -/

/-- **Total computability.** A unary function `f : ℕ → ℕ` is *computable* if some
code computes it on every input. Functions of several arguments are handled by
packing the arguments into one number with `pair`. -/
def Comp (f : Nat → Nat) : Prop := ∃ c : Code, ∀ n, Eval c [n] (f n)

/-- A Boolean-valued function is computable if its `0/1`-valued version is. -/
def CompB (p : Nat → Bool) : Prop := Comp fun n => (p n).toNat

/-- Computability is invariant under pointwise equality. -/
theorem Comp.congr {f g : Nat → Nat} (h : Comp f) (e : ∀ n, f n = g n) : Comp g := by
  rw [show g = f from funext fun n => (e n).symm]; exact h

/-- Computability of tests is invariant under pointwise equality. -/
theorem CompB.congr {p q : Nat → Bool} (h : CompB p) (e : ∀ n, p n = q n) : CompB q := by
  rw [show q = p from funext fun n => (e n).symm]; exact h

namespace Comp

/-- The identity is computable. -/
theorem id : Comp fun n => n := ⟨.proj 0, fun _ => .proj⟩

/-- Constant functions are computable. -/
theorem const (k : Nat) : Comp fun _ => k := ⟨constCode k, fun _ => eval_const _ k⟩

/-- **Composition.** -/
theorem comp {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : Comp fun n => f (g n) := by
  obtain ⟨cf, hf⟩ := hf; obtain ⟨cg, hg⟩ := hg
  exact ⟨.comp cf (vec1 cg), fun n => eval_comp1 (hg n) (hf _)⟩

/-- Combining two computable functions with a binary operation computed by a code. -/
theorem bin {op : Nat → Nat → Nat} (c : Code) (hc : ∀ a b, Eval c [a, b] (op a b))
    {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : Comp fun n => op (f n) (g n) := by
  obtain ⟨cf, hf⟩ := hf; obtain ⟨cg, hg⟩ := hg
  exact ⟨.comp c (vec2 cf cg), fun n => eval_comp2 (hf n) (hg n) (hc _ _)⟩

/-- **Pairing** of computable functions is computable. -/
theorem pair {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    Comp fun n => Computability.pair (f n) (g n) :=
  bin pairCode (fun a b => eval_pair a b []) hf hg

/-- Addition. -/
theorem add {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : Comp fun n => f n + g n :=
  bin addCode (fun a b => eval_add b [] a) hf hg

/-- Multiplication. -/
theorem mul {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : Comp fun n => f n * g n :=
  bin mulCode (fun a b => eval_mul b [] a) hf hg

/-- Truncated subtraction. -/
theorem sub {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : Comp fun n => f n - g n :=
  bin (.comp monusCode (vec2 (.proj 1) (.proj 0))) (fun a b =>
    eval_comp2 .proj .proj (eval_monus a [] b)) hf hg

/-- Successor. -/
theorem succ {f : Nat → Nat} (hf : Comp f) : Comp fun n => f n + 1 :=
  comp ⟨.succ, fun _ => .succ⟩ hf

/-- Unpairing, first component. -/
theorem fst {f : Nat → Nat} (hf : Comp f) : Comp fun n => Computability.fst (f n) := by
  refine comp ⟨leftCode, fun n => ?_⟩ hf
  have := eval_left (Computability.fst n) (Computability.snd n) []
  rwa [pair_fst_snd] at this

/-- Unpairing, second component. -/
theorem snd {f : Nat → Nat} (hf : Comp f) : Comp fun n => Computability.snd (f n) := by
  refine comp ⟨rightCode, fun n => ?_⟩ hf
  have := eval_right (Computability.fst n) (Computability.snd n) []
  rwa [pair_fst_snd] at this

end Comp

/-! ## Primitive recursion -/

/-- **Primitive recursion with a parameter.** `natRec b s n i` is defined by
`natRec b s n 0 = b n` and `natRec b s n (i + 1) = s ⟨n, ⟨i, natRec b s n i⟩⟩`. -/
def natRec (b s : Nat → Nat) (n : Nat) : Nat → Nat
  | 0 => b n
  | i + 1 => s (pair n (pair i (natRec b s n i)))

/-- **Closure under primitive recursion.** -/
theorem Comp.natRec {b s m : Nat → Nat} (hb : Comp b) (hs : Comp s) (hm : Comp m) :
    Comp fun n => Computability.natRec b s n (m n) := by
  obtain ⟨cb, hb⟩ := hb; obtain ⟨cs, hs⟩ := hs; obtain ⟨cm, hm⟩ := hm
  let step : Code := .comp cs (vec1 (pairOf (.proj 2) (pairOf (.proj 0) (.proj 1))))
  have key : ∀ n i, Eval (.prec cb step) [i, n] (Computability.natRec b s n i) := by
    intro n i
    induction i with
    | zero => exact .prec_zero (hb n)
    | succ i ih =>
        exact .prec_succ ih (eval_comp1 (eval_pairOf .proj (eval_pairOf .proj .proj)) (hs _))
  exact ⟨.comp (.prec cb step) (vec2 cm (.proj 0)), fun n => eval_comp2 (hm n) .proj (key n _)⟩

/-- **Definition by cases** on whether a computable function vanishes. -/
theorem Comp.ite0 {c f g : Nat → Nat} (hc : Comp c) (hf : Comp f) (hg : Comp g) :
    Comp fun n => if c n = 0 then f n else g n := by
  have := Comp.natRec hf (Comp.comp hg (Comp.fst Comp.id)) hc
  refine Comp.congr this fun n => ?_
  try dsimp only
  cases h : c n with
  | zero => simp [Computability.natRec]
  | succ k => simp [Computability.natRec]

/-! ## Boolean tests -/

namespace CompB

/-- Constant tests. -/
theorem const (b : Bool) : CompB fun _ => b := Comp.const _

/-- **Equality** of computable functions is a computable test. -/
theorem eq {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : CompB fun n => f n == g n := by
  have := Comp.ite0 (Comp.add (Comp.sub hf hg) (Comp.sub hg hf)) (Comp.const 1) (Comp.const 0)
  refine Comp.congr this fun n => ?_
  try dsimp only
  by_cases h : f n = g n
  · simp [h]
  · have : (f n == g n) = false := by simpa using h
    rw [this]; simp; omega

/-- **Order** `f n < g n` is a computable test. -/
theorem lt {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : CompB fun n => decide (f n < g n) := by
  have := Comp.ite0 (Comp.sub (Comp.succ hf) hg) (Comp.const 1) (Comp.const 0)
  refine Comp.congr this fun n => ?_
  try dsimp only
  by_cases h : f n < g n
  · simp [h]; omega
  · simp [h]; omega

/-- Conjunction. -/
theorem and {p q : Nat → Bool} (hp : CompB p) (hq : CompB q) : CompB fun n => p n && q n := by
  have := Comp.mul hp hq
  refine Comp.congr this fun n => ?_
  try dsimp only
  cases p n <;> cases q n <;> rfl

/-- Negation. -/
theorem not {p : Nat → Bool} (hp : CompB p) : CompB fun n => !p n := by
  have := Comp.sub (Comp.const 1) hp
  refine Comp.congr this fun n => ?_
  try dsimp only
  cases p n <;> rfl

/-- Disjunction. -/
theorem or {p q : Nat → Bool} (hp : CompB p) (hq : CompB q) : CompB fun n => p n || q n := by
  have := not (and (not hp) (not hq))
  refine Comp.congr this fun n => ?_
  try dsimp only
  cases p n <;> cases q n <;> rfl

/-- Composition of a test with a computable function. -/
theorem comp {p : Nat → Bool} {f : Nat → Nat} (hp : CompB p) (hf : Comp f) :
    CompB fun n => p (f n) := Comp.comp hp hf

end CompB

/-- **Definition by cases** on a computable test. -/
theorem Comp.cond {p : Nat → Bool} {f g : Nat → Nat} (hp : CompB p) (hf : Comp f) (hg : Comp g) :
    Comp fun n => bif p n then f n else g n := by
  have := Comp.ite0 hp hg hf
  refine Comp.congr this fun n => ?_
  try dsimp only
  cases p n <;> rfl

/-- Bounded universal quantification: `ballLt q n m` says `q ⟨n, i⟩` for all `i < m`. -/
def ballLt (q : Nat → Bool) (n : Nat) : Nat → Bool
  | 0 => true
  | i + 1 => ballLt q n i && q (pair n i)

/-- `ballLt` means what it says. -/
theorem ballLt_iff (q : Nat → Bool) (n : Nat) :
    ∀ m, ballLt q n m = true ↔ ∀ i, i < m → q (pair n i) = true
  | 0 => by simp [ballLt]
  | m + 1 => by
      simp only [ballLt, Bool.and_eq_true, ballLt_iff q n m]
      constructor
      · rintro ⟨h₁, h₂⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · exact h₁ i h
        · exact h₂
      · intro h; exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

/-- **Closure under bounded quantification.** -/
theorem CompB.ballLt {q : Nat → Bool} {m : Nat → Nat} (hq : CompB q) (hm : Comp m) :
    CompB fun n => Computability.ballLt q n (m n) := by
  have := Comp.natRec (Comp.const 1)
    (Comp.mul (Comp.snd (Comp.snd Comp.id))
      (Comp.comp hq (Comp.pair (Comp.fst Comp.id) (Comp.fst (Comp.snd Comp.id))))) hm
  refine Comp.congr this fun n => ?_
  try dsimp only
  generalize m n = k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Computability.natRec, fst_pair, snd_pair, ih, Computability.ballLt]
      cases Computability.ballLt q n k <;> cases q (pair n k) <;> rfl

/-! ## Coded lists

Lists are coded by `encList` (from `GodelNumbering`): `[] ↦ 0` and
`x :: l ↦ ⟨x, ⌜l⌝⟩ + 1`. -/

/-- Head of a coded list (`0` for the empty list). -/
def lhead (l : Nat) : Nat := fst (l - 1)

/-- Tail of a coded list (the empty list for the empty list). -/
def ltail (l : Nat) : Nat := snd (l - 1)

/-- Head of an encoded list. -/
@[simp] theorem lhead_cons (x : Nat) (l : List Nat) : lhead (encList (x :: l)) = x := by
  simp [lhead, encList]

/-- Tail of an encoded list. -/
@[simp] theorem ltail_cons (x : Nat) (l : List Nat) : ltail (encList (x :: l)) = encList l := by
  simp [ltail, encList]

/-- Tail of the empty list. -/
@[simp] theorem ltail_nil : ltail (encList []) = encList [] := rfl

/-- Head of the empty list. -/
@[simp] theorem lhead_nil : lhead (encList []) = 0 := rfl

/-- The `i`-th element of a coded list (`0` if out of range). -/
def lnth (l : Nat) : Nat → Nat
  | 0 => lhead l
  | i + 1 => lnth (ltail l) i

/-- `lnth` reads the `i`-th element of an encoded list. -/
theorem lnth_encList : ∀ (l : List Nat) (i : Nat), lnth (encList l) i = l.getD i 0
  | [], 0 => rfl
  | [], i + 1 => by simp only [lnth, ltail_nil]; rw [lnth_encList [] i]; rfl
  | x :: l, 0 => by simp [lnth]
  | x :: l, i + 1 => by simp only [lnth, ltail_cons, lnth_encList l i]; rfl

/-- Iterated tail. -/
def ldrop (l : Nat) : Nat → Nat
  | 0 => l
  | i + 1 => ltail (ldrop l i)

/-- Iterated tails of an encoded list. -/
theorem ldrop_encList (l : List Nat) : ∀ i, ldrop (encList l) i = encList (l.drop i)
  | 0 => rfl
  | i + 1 => by
      simp only [ldrop, ldrop_encList l i]
      cases h : l.drop i with
      | nil =>
          have : l.drop (i + 1) = [] := by
            rw [← List.drop_drop]; simp [h]
          rw [this]; rfl
      | cons x t =>
          have : l.drop (i + 1) = t := by
            rw [← List.drop_drop, h]; rfl
          rw [this]; exact ltail_cons x t

/-- `lnth` via `ldrop`. -/
theorem lnth_eq_lhead_ldrop (l : Nat) : ∀ i, lnth l i = lhead (ldrop l i) := by
  intro i
  induction i generalizing l with
  | zero => rfl
  | succ i ih =>
      simp only [lnth, ih (ltail l), ldrop]
      congr 1
      clear ih
      induction i generalizing l with
      | zero => rfl
      | succ i ih => simp only [ldrop]; rw [ih]

/-- Length of a coded list: the number of `i < l` with a non-empty `i`-fold tail. -/
def llen (l : Nat) : Nat := natRec (fun _ => 0)
  (fun p => snd (snd p) + (bif ldrop (fst p) (fst (snd p)) == 0 then 0 else 1)) l l

/-- The code of a list is at least its length. -/
theorem length_le_encList : ∀ l : List Nat, l.length ≤ encList l
  | [] => Nat.le_refl _
  | x :: l => by
      have := length_le_encList l
      have := right_le_pair x (encList l)
      simp [encList]; omega

/-- Partial counts in the definition of `llen`. -/
theorem llen_aux (l : List Nat) : ∀ k, natRec (fun _ => 0)
    (fun p => snd (snd p) + (bif ldrop (fst p) (fst (snd p)) == 0 then 0 else 1))
    (encList l) k = min k l.length
  | 0 => by simp [natRec]
  | k + 1 => by
      simp only [natRec, fst_pair, snd_pair, llen_aux l k, ldrop_encList]
      by_cases h : k < l.length
      · have : (encList (l.drop k) == 0) = false := by
          cases hd : l.drop k with
          | nil => simp [List.drop_eq_nil_iff] at hd; omega
          | cons x t => simp [encList]
        rw [this]; simp; omega
      · have : (encList (l.drop k) == 0) = true := by
          rw [List.drop_eq_nil_of_le (by omega)]; rfl
        rw [this]; simp; omega

/-- `llen` computes the length of an encoded list. -/
theorem llen_encList (l : List Nat) : llen (encList l) = l.length := by
  rw [llen, llen_aux]; exact Nat.min_eq_right (length_le_encList l)

/-- Elements of a coded list are smaller than the code. -/
theorem lnth_lt (l : List Nat) (i : Nat) (hi : i < l.length) : lnth (encList l) i < encList l := by
  rw [lnth_encList]
  induction l generalizing i with
  | nil => simp at hi
  | cons x t ih =>
      cases i with
      | zero => have := left_le_pair x (encList t); simp [encList]; omega
      | succ i =>
          have h1 := ih i (by simp at hi; omega)
          have h2 := right_le_pair x (encList t)
          show t.getD i 0 < pair x (encList t) + 1
          omega

namespace Comp

/-- Head is computable. -/
theorem lhead {f : Nat → Nat} (hf : Comp f) : Comp fun n => Computability.lhead (f n) :=
  Comp.fst (Comp.sub hf (Comp.const 1))

/-- Tail is computable. -/
theorem ltail {f : Nat → Nat} (hf : Comp f) : Comp fun n => Computability.ltail (f n) :=
  Comp.snd (Comp.sub hf (Comp.const 1))

/-- Iterated tail is computable. -/
theorem ldrop {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    Comp fun n => Computability.ldrop (f n) (g n) := by
  have := Comp.natRec hf (Comp.ltail (Comp.snd (Comp.snd Comp.id))) hg
  refine Comp.congr this fun n => ?_
  try dsimp only
  generalize g n = k
  induction k with
  | zero => rfl
  | succ k ih => simp only [Computability.natRec, snd_pair, ih, Computability.ldrop]

/-- The `i`-th element is computable. -/
theorem lnth {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    Comp fun n => Computability.lnth (f n) (g n) := by
  have := Comp.lhead (Comp.ldrop hf hg)
  exact Comp.congr this fun n => (lnth_eq_lhead_ldrop _ _).symm

/-- Length is computable. -/
theorem llen {f : Nat → Nat} (hf : Comp f) : Comp fun n => Computability.llen (f n) := by
  refine Comp.comp (Comp.natRec (Comp.const 0) (Comp.add (Comp.snd (Comp.snd Comp.id))
    (Comp.cond (CompB.eq (Comp.ldrop (Comp.fst Comp.id) (Comp.fst (Comp.snd Comp.id)))
      (Comp.const 0)) (Comp.const 0) (Comp.const 1))) Comp.id) hf

/-- Cons is computable. -/
theorem lcons {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    Comp fun n => Computability.pair (f n) (g n) + 1 := Comp.succ (Comp.pair hf hg)

end Comp

/-! ## Course-of-values recursion -/

/-- The history of a course-of-values recursion: `covHist g x n` codes the list
`[f(n−1), …, f(1), f(0)]` of all earlier values of `f = covRec g x`. -/
def covHist (g : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pair (g (pair x (pair n (covHist g x n)))) (covHist g x n) + 1

/-- **Course-of-values recursion.** `covRec g x n = g ⟨x, ⟨n, H⟩⟩` where `H` codes the
list of all earlier values `covRec g x m`, `m < n` (read with `histGet`). -/
def covRec (g : Nat → Nat) (x n : Nat) : Nat := g (pair x (pair n (covHist g x n)))

/-- Reading the value at `m` from a history of length `n`. -/
def histGet (H n m : Nat) : Nat := lnth H (n - 1 - m)

/-- The history list, as a Lean list. -/
def covList (g : Nat → Nat) (x : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => covRec g x n :: covList g x n

/-- The history is the encoded history list. -/
theorem covHist_eq (g : Nat → Nat) (x : Nat) : ∀ n, covHist g x n = encList (covList g x n)
  | 0 => rfl
  | n + 1 => by simp only [covHist, covList, encList, covRec, covHist_eq g x n]

/-- Length of the history list. -/
theorem covList_length (g : Nat → Nat) (x : Nat) : ∀ n, (covList g x n).length = n
  | 0 => rfl
  | n + 1 => by simp [covList, covList_length g x n]

/-- Entries of the history list. -/
theorem covList_getD (g : Nat → Nat) (x : Nat) :
    ∀ n m, m < n → (covList g x n).getD (n - 1 - m) 0 = covRec g x m
  | 0, m, h => absurd h (Nat.not_lt_zero _)
  | n + 1, m, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
      · rw [show n + 1 - 1 - m = (n - 1 - m) + 1 by omega]
        simp only [covList, List.getD_cons_succ]
        exact covList_getD g x n m h'
      · simp [covList]

/-- **The history records all earlier values.** -/
theorem histGet_covHist (g : Nat → Nat) (x n m : Nat) (h : m < n) :
    histGet (covHist g x n) n m = covRec g x m := by
  rw [histGet, covHist_eq, lnth_encList, covList_getD g x n m h]

/-- **Closure under course-of-values recursion.** -/
theorem Comp.covRec {g : Nat → Nat} (hg : Comp g) :
    Comp fun p => Computability.covRec g (Computability.fst p) (Computability.snd p) := by
  have hH : Comp fun p => covHist g (Computability.fst p) (Computability.snd p) := by
    have := Comp.natRec (b := fun _ => 0)
      (s := fun q => Computability.pair (g (Computability.pair (Computability.fst (Computability.fst q))
          (Computability.pair (Computability.fst (Computability.snd q))
            (Computability.snd (Computability.snd q))))) (Computability.snd (Computability.snd q)) + 1)
      (Comp.const 0)
      (Comp.lcons (Comp.comp hg (Comp.pair (Comp.fst (Comp.fst Comp.id))
        (Comp.pair (Comp.fst (Comp.snd Comp.id)) (Comp.snd (Comp.snd Comp.id)))))
        (Comp.snd (Comp.snd Comp.id)))
      (Comp.snd Comp.id)
    refine Comp.congr this fun p => ?_
    try dsimp only
    generalize Computability.snd p = k
    induction k with
    | zero => rfl
    | succ k ih => simp only [Computability.natRec, fst_pair, snd_pair, ih, covHist]
  exact Comp.comp hg (Comp.pair (Comp.fst Comp.id) (Comp.pair (Comp.snd Comp.id) hH))

/-- `histGet` is computable. -/
theorem Comp.histGet {f g h : Nat → Nat} (hf : Comp f) (hg : Comp g) (hh : Comp h) :
    Comp fun n => Computability.histGet (f n) (g n) (h n) :=
  Comp.lnth hf (Comp.sub (Comp.sub hg (Comp.const 1)) hh)

/-! ## Unbounded search: computably enumerable predicates -/

/-- Existence of a least witness (a constructive-enough form of well-ordering). -/
theorem exists_least {p : Nat → Prop} (h : ∃ t, p t) : ∃ t, p t ∧ ∀ m, m < t → ¬ p m := by
  obtain ⟨t, ht⟩ := h
  induction t using Nat.strongRecOn with
  | _ t ih =>
      by_cases hm : ∃ m, m < t ∧ p m
      · obtain ⟨m, hmt, hpm⟩ := hm; exact ih m hmt hpm
      · exact ⟨t, ht, fun m hmt hpm => hm ⟨m, hmt, hpm⟩⟩

/-- **Unbounded search.** For a computable test `p`, there is a code which on input `n`
returns the *least* `t` with `p ⟨n, t⟩`, and diverges if there is none. -/
theorem search {p : Nat → Bool} (hp : CompB p) :
    ∃ c : Code, ∀ n t, Eval c [n] t ↔ p (pair n t) = true ∧ ∀ m, m < t → p (pair n m) = false := by
  obtain ⟨cp, hcp⟩ := CompB.not hp
  -- body on `[t, n]`: `1 - p ⟨n, t⟩`
  let body : Code := .comp cp (vec1 (pairOf (.proj 1) (.proj 0)))
  have hbody : ∀ n t, Eval body (t :: [n]) (!p (pair n t)).toNat := fun n t =>
    eval_comp1 (eval_pairOf .proj .proj) (hcp _)
  refine ⟨.mu body, fun n t => ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩⟩
  · cases h with
    | mu ks h₀ hlt =>
        have e₀ := Eval.det h₀ (hbody n t)
        refine ⟨?_, fun m hm => ?_⟩
        · cases hpt : p (pair n t)
          · rw [hpt] at e₀; simp at e₀
          · rfl
        · have e := Eval.det (hlt m hm) (hbody n m)
          cases hpm : p (pair n m)
          · rfl
          · rw [hpm] at e; simp at e
  · refine .mu (fun _ => 0) ?_ (fun m hm => ?_)
    · have := hbody n t; rwa [h₁] at this
    · have := hbody n m; rwa [h₂ m hm] at this

/-- **Computably enumerable predicates.** If `p` is a computable test, then some code
halts on `n` exactly when a witness `t` with `p ⟨n, t⟩` exists. -/
theorem ce_of_search {p : Nat → Bool} (hp : CompB p) :
    ∃ c : Code, ∀ n, Halts c [n] ↔ ∃ t, p (pair n t) = true := by
  obtain ⟨c, hc⟩ := search hp
  refine ⟨c, fun n => ⟨fun ⟨t, ht⟩ => ⟨t, ((hc n t).1 ht).1⟩, fun h => ?_⟩⟩
  obtain ⟨t, ht, hmin⟩ := exists_least h
  exact ⟨t, (hc n t).2 ⟨ht, fun m hm => by simpa using hmin m hm⟩⟩

end Foundations.Logic.Computability
