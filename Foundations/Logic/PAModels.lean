import Foundations.Logic.RobinsonQ

/-!
# Arithmetic inside an arbitrary model of PA

The second incompleteness theorem is, at bottom, a statement about what PA can prove
*about its own proofs*. By Gödel's completeness theorem, "PA proves `σ`" means "`σ` is
true in every model of PA" — including the **non-standard** models, whose domains
contain, beyond `0, 1, 2, …`, infinitely large elements. In such a model a "proof"
may be a non-standard number, coding a sequence of non-standard length that no
mathematician could ever write down. To show that PA proves facts about provability
we must therefore learn to reason *inside an arbitrary model `M` of PA*: to do
arithmetic with its elements, and to use the one tool that makes PA strong — the
**induction schema**, which holds in `M` for every property *definable by a
formula*.

This file sets up that reasoning.

* `PAModel` bundles a structure with the fact that it satisfies PA.
* **Definability calculus.** A property of environments is `Dfn` if some formula
  defines it in `M`; we prove closure under the connectives, the quantifiers and
  substitution, and a small tactic `dfn` assembles such proofs automatically. With
  it, **induction** (`PAModel.induction`) becomes available for every property we
  can write down — which is how Peano's axiom is used in practice.
* **Algebra.** From the recursion equations and induction we derive the laws of a
  commutative semiring with cancellation (associativity, commutativity,
  distributivity) and register `M` with Lean's `grind` tactic, so that polynomial
  identities in `M` are checked automatically.
* **Order and division.** `x ≤ y` means `∃z, x + z = y`; it is a linear order, and
  division with remainder exists and is unique (`div_exists`, `div_unique`).
* **Gödel's β-function in `M`.** `BetaM c d i y` says that `y` is the remainder of
  `c` modulo `1 + (i+1)·d` — Gödel's device for coding finite sequences by two
  numbers. In the next file we prove, inside `M`, that every definable finite
  sequence (even of non-standard length) has such a code.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula

/-- **A model of Peano arithmetic**: a structure for the language of arithmetic that
satisfies every axiom of PA (and has a non-empty domain). -/
structure PAModel where
  /-- The underlying structure. -/
  M : Structure Arith
  /-- It is a model of PA. -/
  isModel : IsModel M PA

namespace PAModel

variable (N : PAModel)

/-- The domain of a model of PA. -/
abbrev Dom : Type := N.M.Dom

/-- Numerals: the literal `n` denotes the value of the numeral `n̄`. -/
instance instOfNat (n : Nat) : OfNat N.Dom n := ⟨numM N.M n⟩
/-- The canonical map from `ℕ`: `n ↦ n̄`. -/
instance instNatCast : NatCast N.Dom := ⟨numM N.M⟩
/-- Addition of the model. -/
instance instAdd : Add N.Dom := ⟨madd N.M⟩
/-- Multiplication of the model. -/
instance instMul : Mul N.Dom := ⟨mmul N.M⟩

/-- A model of PA is a model of `Q`. -/
theorem isQ : IsQModel N.M :=
  isQModel_of_PA (e := fun _ => Classical.choice N.isModel.1) fun ψ h => N.isModel.2 ψ h _

variable {N}

/-! ## The recursion equations -/

/-- `madd` is `+`. -/
@[simp] theorem madd_eq (x y : N.Dom) : madd N.M x y = x + y := rfl
/-- `mmul` is `*`. -/
@[simp] theorem mmul_eq (x y : N.Dom) : mmul N.M x y = x * y := rfl
/-- `mz` is `0`. -/
@[simp] theorem mz_eq : mz N.M = (0 : N.Dom) := rfl

/-- `x + 0 = x`. -/
theorem add_zero' (x : N.Dom) : x + 0 = x := N.isQ.add_zero x

/-- The successor is `+ 1`. -/
@[simp] theorem ms_eq (x : N.Dom) : ms N.M x = x + 1 := by
  show _ = madd N.M x (ms N.M (mz N.M)); rw [N.isQ.add_succ, N.isQ.add_zero]

/-- `x + (y + 1) = (x + y) + 1`. -/
theorem add_succ' (x y : N.Dom) : x + (y + 1) = x + y + 1 := by
  rw [← ms_eq, ← ms_eq]; exact N.isQ.add_succ x y

/-- `x · 0 = 0`. -/
theorem mul_zero' (x : N.Dom) : x * 0 = 0 := N.isQ.mul_zero x

/-- `x · (y + 1) = x · y + x`. -/
theorem mul_succ' (x y : N.Dom) : x * (y + 1) = x * y + x := by
  rw [← ms_eq]; exact N.isQ.mul_succ x y

/-- `x + 1 ≠ 0`. -/
theorem succ_ne_zero' (x : N.Dom) : x + 1 ≠ 0 := by rw [← ms_eq]; exact N.isQ.succ_ne_zero x

/-- The successor is injective. -/
theorem succ_inj' {x y : N.Dom} (h : x + 1 = y + 1) : x = y := by
  rw [← ms_eq, ← ms_eq] at h; exact N.isQ.succ_inj x y h

/-- Every element is `0` or a successor. -/
theorem zero_or_succ (x : N.Dom) : x = 0 ∨ ∃ y, x = y + 1 := by
  rcases N.isQ.zero_or_succ x with h | ⟨y, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, by rw [h, ms_eq]⟩

/-- `numM` of a successor. -/
theorem numM_succ' (n : Nat) : (numM N.M (n + 1) : N.Dom) = numM N.M n + 1 := ms_eq _

/-! ## Induction and the definability calculus -/

/-- **The induction schema in a model of PA**, for the property defined by `φ` (with
parameters `e`). -/
theorem sat_induction (φ : Formula Arith) (e : Nat → N.Dom) (h0 : Sat N.M (Env.cons 0 e) φ)
    (hs : ∀ x, Sat N.M (Env.cons x e) φ → Sat N.M (Env.cons (x + 1) e) φ) :
    ∀ x, Sat N.M (Env.cons x e) φ := by
  have h := N.isModel.2 _ (PA.induction φ) e
  have hsub : ∀ x : N.Dom, (fun n => (succSubst n).eval N.M (Env.cons x e)) = Env.cons (x + 1) e := by
    intro x; funext n
    cases n with
    | zero => show ms N.M x = x + 1; exact ms_eq x
    | succ n => rfl
  simp only [Sat, sat_inst, sat_subst, hsub, eval_zero_M, mz_eq] at h
  exact h ⟨h0, hs⟩

variable (N)

/-- A property of environments is **definable** in `N` if some formula defines it. -/
def Dfn (P : (Nat → N.Dom) → Prop) : Prop := ∃ φ : Formula Arith, ∀ e, Sat N.M e φ ↔ P e

/-- A function of environments is **definable** if it is the value of a term. -/
def DfnT (f : (Nat → N.Dom) → N.Dom) : Prop := ∃ t : Term Arith, ∀ e, t.eval N.M e = f e

variable {N}

/-- **Induction for definable properties.** If `P` (with parameters `e`) is definable,
holds of `0` and is inherited by successors, it holds everywhere. -/
theorem induction {P : N.Dom → (Nat → N.Dom) → Prop}
    (hP : N.Dfn fun e => P (e 0) (fun n => e (n + 1))) (e : Nat → N.Dom)
    (h0 : P 0 e) (hs : ∀ x, P x e → P (x + 1) e) : ∀ x, P x e := by
  obtain ⟨φ, hφ⟩ := hP
  intro x
  have := sat_induction φ e ((hφ _).2 h0) (fun x hx => (hφ _).2 (hs x ((hφ _).1 hx))) x
  exact (hφ _).1 this

/-- Variables are definable. -/
theorem DfnT.var (n : Nat) : N.DfnT fun e => e n := ⟨v n, fun _ => rfl⟩

/-- Numerals are definable. -/
theorem DfnT.ofNat (k : Nat) : N.DfnT fun _ => (OfNat.ofNat k : N.Dom) :=
  ⟨numeral k, fun e => eval_numeral_M e k⟩

/-- Sums of definable functions are definable. -/
theorem DfnT.add {f g : (Nat → N.Dom) → N.Dom} (hf : N.DfnT f) (hg : N.DfnT g) :
    N.DfnT fun e => f e + g e := by
  obtain ⟨t, ht⟩ := hf; obtain ⟨s, hs⟩ := hg
  exact ⟨Arith.add t s, fun e => by rw [eval_add_M, ht, hs]; rfl⟩

/-- Products of definable functions are definable. -/
theorem DfnT.mul {f g : (Nat → N.Dom) → N.Dom} (hf : N.DfnT f) (hg : N.DfnT g) :
    N.DfnT fun e => f e * g e := by
  obtain ⟨t, ht⟩ := hf; obtain ⟨s, hs⟩ := hg
  exact ⟨Arith.mul t s, fun e => by rw [eval_mul_M, ht, hs]; rfl⟩

/-- Equations between definable functions are definable. -/
theorem Dfn.eq {f g : (Nat → N.Dom) → N.Dom} (hf : N.DfnT f) (hg : N.DfnT g) :
    N.Dfn fun e => f e = g e := by
  obtain ⟨t, ht⟩ := hf; obtain ⟨s, hs⟩ := hg
  exact ⟨Formula.eq t s, fun e => by simp only [Sat, ht, hs]⟩

/-- Definable properties are closed under conjunction. -/
theorem Dfn.and {P Q : (Nat → N.Dom) → Prop} (hP : N.Dfn P) (hQ : N.Dfn Q) :
    N.Dfn fun e => P e ∧ Q e := by
  obtain ⟨φ, hφ⟩ := hP; obtain ⟨ψ, hψ⟩ := hQ
  exact ⟨conj φ ψ, fun e => by simp only [Sat, hφ, hψ]⟩

/-- Definable properties are closed under disjunction. -/
theorem Dfn.or {P Q : (Nat → N.Dom) → Prop} (hP : N.Dfn P) (hQ : N.Dfn Q) :
    N.Dfn fun e => P e ∨ Q e := by
  obtain ⟨φ, hφ⟩ := hP; obtain ⟨ψ, hψ⟩ := hQ
  exact ⟨disj φ ψ, fun e => by simp only [Sat, hφ, hψ]⟩

/-- Definable properties are closed under implication. -/
theorem Dfn.imp {P Q : (Nat → N.Dom) → Prop} (hP : N.Dfn P) (hQ : N.Dfn Q) :
    N.Dfn fun e => P e → Q e := by
  obtain ⟨φ, hφ⟩ := hP; obtain ⟨ψ, hψ⟩ := hQ
  exact ⟨Formula.imp φ ψ, fun e => by simp only [Sat, hφ, hψ]⟩

/-- Definable properties are closed under negation. -/
theorem Dfn.not {P : (Nat → N.Dom) → Prop} (hP : N.Dfn P) : N.Dfn fun e => ¬ P e := by
  obtain ⟨φ, hφ⟩ := hP
  exact ⟨neg φ, fun e => by simp only [neg, Sat, hφ]⟩

/-- Definable properties are closed under existential quantification (over the
variable `0`). -/
theorem Dfn.ex {Q : N.Dom → (Nat → N.Dom) → Prop}
    (h : N.Dfn fun e => Q (e 0) (fun n => e (n + 1))) : N.Dfn fun e => ∃ x, Q x e := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨Formula.ex φ, fun e => exists_congr fun x => hφ (Env.cons x e)⟩

/-- Definable properties are closed under universal quantification. -/
theorem Dfn.all {Q : N.Dom → (Nat → N.Dom) → Prop}
    (h : N.Dfn fun e => Q (e 0) (fun n => e (n + 1))) : N.Dfn fun e => ∀ x, Q x e := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨Formula.all φ, fun e => forall_congr' fun x => hφ (Env.cons x e)⟩

/-- **Definable properties are closed under substitution of definable functions.** -/
theorem Dfn.subst {P : (Nat → N.Dom) → Prop} (hP : N.Dfn P)
    {σ : Nat → (Nat → N.Dom) → N.Dom} (hσ : ∀ n, N.DfnT (σ n)) :
    N.Dfn fun e => P (fun n => σ n e) := by
  obtain ⟨φ, hφ⟩ := hP
  refine ⟨φ.subst fun n => (hσ n).choose, fun e => ?_⟩
  rw [sat_subst, hφ]
  have : (fun n => ((hσ n).choose).eval N.M e) = fun n => σ n e :=
    funext fun n => (hσ n).choose_spec e
  rw [this]

/-- One step of the `dfn` tactic (extensible by further `macro_rules`). -/
syntax "dfn_step" : tactic
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.and)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.or)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.imp)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.not)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.ex)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.all)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.eq)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.DfnT.add)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.DfnT.mul)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.DfnT.ofNat)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.DfnT.var)

/-- `dfn` proves definability goals `N.Dfn P` by decomposing `P` syntactically. -/
macro "dfn" : tactic => `(tactic| repeat' dfn_step)

/-! ## The algebra of a model of PA -/

/-- `0 + x = x`. -/
theorem zero_add' (x : N.Dom) : 0 + x = x := by
  refine induction (P := fun x _ => 0 + x = x) (by dfn) (fun _ => 0) (add_zero' 0) ?_ x
  intro x ih; rw [add_succ', ih]

/-- `(x + 1) + y = (x + y) + 1`. -/
theorem succ_add' (x y : N.Dom) : x + 1 + y = x + y + 1 := by
  refine induction (P := fun y e => e 0 + 1 + y = e 0 + y + 1) (by dfn) (fun _ => x) ?_ ?_ y
  · show x + 1 + 0 = x + 0 + 1; rw [add_zero', add_zero']
  · intro y ih; show x + 1 + (y + 1) = x + (y + 1) + 1; rw [add_succ', add_succ', ih]

/-- Addition is commutative. -/
theorem add_comm' (x y : N.Dom) : x + y = y + x := by
  refine induction (P := fun y e => e 0 + y = y + e 0) (by dfn) (fun _ => x) ?_ ?_ y
  · show x + 0 = 0 + x; rw [add_zero', zero_add']
  · intro y ih; show x + (y + 1) = y + 1 + x; rw [add_succ', succ_add', ih]

/-- Addition is associative. -/
theorem add_assoc' (x y z : N.Dom) : x + y + z = x + (y + z) := by
  refine induction (P := fun z e => e 0 + e 1 + z = e 0 + (e 1 + z)) (by dfn)
    (Env.cons x fun _ => y) ?_ ?_ z
  · show x + y + 0 = x + (y + 0); rw [add_zero', add_zero']
  · intro z (ih : x + y + z = x + (y + z)); show x + y + (z + 1) = x + (y + (z + 1))
    rw [add_succ', add_succ', add_succ', ih]

/-- Addition cancels on the right. -/
theorem add_right_cancel' {x y z : N.Dom} (h : x + z = y + z) : x = y := by
  have key := induction (P := fun z e => e 0 + z = e 1 + z → e 0 = e 1) (by dfn)
    (Env.cons x fun _ => y) (fun h => by rwa [add_zero', add_zero'] at h)
    (fun z ih h => ih (succ_inj' (by rwa [add_succ', add_succ'] at h)))
  exact key z h

/-- `0 · x = 0`. -/
theorem zero_mul' (x : N.Dom) : 0 * x = 0 := by
  refine induction (P := fun x _ => 0 * x = 0) (by dfn) (fun _ => 0) (mul_zero' 0) ?_ x
  intro x ih; rw [mul_succ', ih, add_zero']

/-- `(x + 1) · y = x · y + y`. -/
theorem succ_mul' (x y : N.Dom) : (x + 1) * y = x * y + y := by
  refine induction (P := fun y e => (e 0 + 1) * y = e 0 * y + y) (by dfn) (fun _ => x) ?_ ?_ y
  · show (x + 1) * 0 = x * 0 + 0; rw [mul_zero', mul_zero', add_zero']
  · intro y ih; show (x + 1) * (y + 1) = x * (y + 1) + (y + 1)
    rw [mul_succ', mul_succ', ih]
    calc x * y + y + (x + 1) = x * y + (y + x) + 1 := by rw [add_succ', add_assoc' (x * y) y x]
      _ = x * y + (x + y) + 1 := by rw [add_comm' y x]
      _ = x * y + x + (y + 1) := by rw [add_succ' (x * y + x) y, add_assoc' (x * y) x y]

/-- Multiplication is commutative. -/
theorem mul_comm' (x y : N.Dom) : x * y = y * x := by
  refine induction (P := fun y e => e 0 * y = y * e 0) (by dfn) (fun _ => x) ?_ ?_ y
  · show x * 0 = 0 * x; rw [mul_zero', zero_mul']
  · intro y ih; show x * (y + 1) = (y + 1) * x; rw [mul_succ', succ_mul', ih]

/-- Multiplication distributes over addition. -/
theorem left_distrib' (x y z : N.Dom) : x * (y + z) = x * y + x * z := by
  refine induction (P := fun z e => e 0 * (e 1 + z) = e 0 * e 1 + e 0 * z) (by dfn)
    (Env.cons x fun _ => y) ?_ ?_ z
  · show x * (y + 0) = x * y + x * 0; rw [add_zero', mul_zero', add_zero']
  · intro z (ih : x * (y + z) = x * y + x * z); show x * (y + (z + 1)) = x * y + x * (z + 1)
    rw [add_succ', mul_succ', ih, mul_succ', add_assoc']

/-- Multiplication is associative. -/
theorem mul_assoc' (x y z : N.Dom) : x * y * z = x * (y * z) := by
  refine induction (P := fun z e => e 0 * e 1 * z = e 0 * (e 1 * z)) (by dfn)
    (Env.cons x fun _ => y) ?_ ?_ z
  · show x * y * 0 = x * (y * 0); rw [mul_zero', mul_zero', mul_zero']
  · intro z (ih : x * y * z = x * (y * z)); show x * y * (z + 1) = x * (y * (z + 1)); rw [mul_succ', mul_succ', ih, left_distrib']

/-- `x · 1 = x`. -/
theorem mul_one' (x : N.Dom) : x * 1 = x := by
  have : x * (0 + 1) = x * 0 + x := mul_succ' x 0
  rwa [zero_add', mul_zero', zero_add'] at this

/-- Powers in a model of PA (by recursion on a meta-level exponent). -/
def mpow (a : N.Dom) : Nat → N.Dom
  | 0 => 1
  | n + 1 => mpow a n * a

/-- **A model of PA is a commutative semiring** (registered for `grind`). -/
instance instCommSemiring : Lean.Grind.CommSemiring N.Dom where
  natCast := instNatCast N
  ofNat := fun n => instOfNat N n
  nsmul := ⟨fun n a => (n : N.Dom) * a⟩
  npow := ⟨fun a n => mpow a n⟩
  add_zero := add_zero'
  add_comm := add_comm'
  add_assoc := add_assoc'
  mul_assoc := mul_assoc'
  mul_one := mul_one'
  one_mul := fun a => by rw [mul_comm']; exact mul_one' a
  left_distrib := left_distrib'
  right_distrib := fun a b c => by rw [mul_comm', left_distrib', mul_comm' c, mul_comm' c]
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  pow_zero := fun _ => rfl
  pow_succ := fun _ _ => rfl
  ofNat_succ := fun n => numM_succ' n
  mul_comm := mul_comm'

/-- **Addition in a model of PA is cancellative** (registered for `grind`). -/
instance instAddRightCancel : Lean.Grind.AddRightCancel N.Dom where
  add_right_cancel := fun _ _ _ h => add_right_cancel' h

/-! ## Order -/

/-- `x ≤ y` in a model of PA: `∃z, x + z = y`. -/
instance instLE : LE N.Dom := ⟨fun x y => ∃ z, x + z = y⟩
/-- `x < y` in a model of PA: `x + 1 ≤ y`. -/
instance instLT : LT N.Dom := ⟨fun x y => x + 1 ≤ y⟩

/-- Unfolding `≤`. -/
theorem le_def {x y : N.Dom} : x ≤ y ↔ ∃ z, x + z = y := Iff.rfl
/-- Unfolding `<`. -/
theorem lt_def {x y : N.Dom} : x < y ↔ ∃ z, x + 1 + z = y := Iff.rfl

/-- `≤` is definable. -/
theorem Dfn.le {f g : (Nat → N.Dom) → N.Dom} (hf : N.DfnT f) (hg : N.DfnT g) :
    N.Dfn fun e => f e ≤ g e := by
  obtain ⟨t, ht⟩ := hf; obtain ⟨s, hs⟩ := hg
  refine ⟨Formula.ex (Formula.eq (Arith.add (t.rename Nat.succ) (v 0)) (s.rename Nat.succ)),
    fun e => ?_⟩
  simp only [Sat, eval_add_M, Term.eval_rename, eval_var_M]
  exact exists_congr fun z => by rw [show (fun n => Env.cons z e (n + 1)) = e from rfl, ht, hs]; rfl

/-- `<` is definable. -/
theorem Dfn.lt {f g : (Nat → N.Dom) → N.Dom} (hf : N.DfnT f) (hg : N.DfnT g) :
    N.Dfn fun e => f e < g e := Dfn.le (DfnT.add hf (DfnT.ofNat 1)) hg

macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.le)
macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.lt)

/-- `x + (y + 1) ≠ x`. -/
theorem add_succ_ne_self (x y : N.Dom) : x + (y + 1) ≠ x := by
  intro h
  have : y + 1 + x = 0 + x := by grind
  exact succ_ne_zero' y (add_right_cancel' this)

/-- `a + b = 0` forces `b = 0`. -/
theorem eq_zero_of_add_eq_zero {a b : N.Dom} (h : a + b = 0) : b = 0 := by
  rcases zero_or_succ b with hb | ⟨c, rfl⟩
  · exact hb
  · exact absurd (by grind : a + c + 1 = 0) (succ_ne_zero' _)

/-- `0 ≤ x`. -/
theorem zero_le' (x : N.Dom) : 0 ≤ x := ⟨x, zero_add' x⟩
/-- `x ≤ x`. -/
theorem le_refl' (x : N.Dom) : x ≤ x := ⟨0, add_zero' x⟩
/-- `≤` is transitive. -/
theorem le_trans' {x y z : N.Dom} (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, rfl⟩ := h₂; exact ⟨a + b, by grind⟩
/-- `x ≤ x + y`. -/
theorem le_add_right' (x y : N.Dom) : x ≤ x + y := ⟨y, rfl⟩
/-- `≤` is antisymmetric. -/
theorem le_antisymm' {x y : N.Dom} (h₁ : x ≤ y) (h₂ : y ≤ x) : x = y := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, hb⟩ := h₂
  have : b + a = 0 := add_right_cancel' (by grind : b + a + x = 0 + x)
  have ha : a = 0 := eq_zero_of_add_eq_zero (by grind : b + a = 0)
  rw [ha, add_zero']
/-- `<` is irreflexive. -/
theorem lt_irrefl' (x : N.Dom) : ¬ x < x := by
  rintro ⟨z, hz⟩; exact add_succ_ne_self x z (by grind)
/-- Nothing is below `0`. -/
theorem not_lt_zero' (x : N.Dom) : ¬ x < 0 := by
  rintro ⟨z, hz⟩; exact succ_ne_zero' (x + z) (by grind)
/-- `x < y` iff `x + 1 ≤ y`. -/
theorem lt_iff_succ_le {x y : N.Dom} : x < y ↔ x + 1 ≤ y := Iff.rfl
/-- `x < y + 1` iff `x ≤ y`. -/
theorem lt_succ_iff' {x y : N.Dom} : x < y + 1 ↔ x ≤ y := by
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, add_right_cancel' (by grind : x + z + 1 = y + 1)⟩
  · rintro ⟨z, rfl⟩; exact ⟨z, by grind⟩
/-- `x < x + 1`. -/
theorem lt_succ_self' (x : N.Dom) : x < x + 1 := lt_succ_iff'.2 (le_refl' x)
/-- `≤` is either `=` or `<`. -/
theorem eq_or_lt_of_le {x y : N.Dom} (h : x ≤ y) : x = y ∨ x < y := by
  obtain ⟨z, rfl⟩ := h
  rcases zero_or_succ z with rfl | ⟨w, rfl⟩
  · exact Or.inl (add_zero' x).symm
  · exact Or.inr ⟨w, by grind⟩
/-- `<` implies `≤`. -/
theorem le_of_lt' {x y : N.Dom} (h : x < y) : x ≤ y := by
  obtain ⟨z, rfl⟩ := h; exact ⟨1 + z, by grind⟩
/-- `x < y ≤ z` gives `x < z`. -/
theorem lt_of_lt_of_le' {x y z : N.Dom} (h₁ : x < y) (h₂ : y ≤ z) : x < z := le_trans' h₁ h₂
/-- `x ≤ y < z` gives `x < z`. -/
theorem lt_of_le_of_lt' {x y z : N.Dom} (h₁ : x ≤ y) (h₂ : y < z) : x < z := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, rfl⟩ := h₂; exact ⟨a + b, by grind⟩

/-- **Trichotomy**: the order of a model of PA is linear. -/
theorem trichotomy (x y : N.Dom) : x < y ∨ x = y ∨ y < x := by
  refine induction (P := fun x e => x < e 0 ∨ x = e 0 ∨ e 0 < x) (by dfn) (fun _ => y) ?_ ?_ x
  · show 0 < y ∨ 0 = y ∨ y < 0
    rcases zero_or_succ y with rfl | ⟨w, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl ⟨w, by grind⟩
  · intro x ih
    show x + 1 < y ∨ x + 1 = y ∨ y < x + 1
    rcases ih with h | rfl | h
    · rcases eq_or_lt_of_le (lt_iff_succ_le.1 h) with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inl h'
    · exact Or.inr (Or.inr (lt_succ_self' _))
    · exact Or.inr (Or.inr (lt_succ_iff'.2 (le_of_lt' h)))

/-- `¬ x < y` iff `y ≤ x`. -/
theorem not_lt' {x y : N.Dom} : ¬ x < y ↔ y ≤ x := by
  constructor
  · intro h
    rcases trichotomy x y with h' | rfl | h'
    · exact absurd h' h
    · exact le_refl' _
    · exact le_of_lt' h'
  · intro h h'; exact lt_irrefl' _ (lt_of_le_of_lt' h h')

/-- `y ≤ x` or `x < y`. -/
theorem le_or_lt' (x y : N.Dom) : y ≤ x ∨ x < y := by
  by_cases h : x < y
  · exact Or.inr h
  · exact Or.inl (not_lt'.1 h)

/-- A non-zero element is positive. -/
theorem pos_of_ne_zero {x : N.Dom} (h : x ≠ 0) : 0 < x := by
  rcases zero_or_succ x with rfl | ⟨w, rfl⟩
  · exact absurd rfl h
  · exact ⟨w, by grind⟩

/-! ## Division with remainder -/

/-- **Division with remainder exists** in a model of PA. -/
theorem div_exists {m : N.Dom} (hm : m ≠ 0) (a : N.Dom) : ∃ q r, a = q * m + r ∧ r < m := by
  refine induction (P := fun a e => ∃ q r, a = q * e 0 + r ∧ r < e 0) (by dfn) (fun _ => m)
    ⟨0, 0, by grind, pos_of_ne_zero hm⟩ ?_ a
  rintro a ⟨q, r, rfl, hr⟩
  rcases eq_or_lt_of_le (lt_iff_succ_le.1 hr) with h | h
  · exact ⟨q + 1, 0, by grind, pos_of_ne_zero hm⟩
  · exact ⟨q, r + 1, by grind, h⟩

/-- **Division with remainder is unique.** -/
theorem div_unique {m q r q' r' : N.Dom} (h : q * m + r = q' * m + r') (hr : r < m)
    (hr' : r' < m) : q = q' ∧ r = r' := by
  have key : ∀ {q r q' r' : N.Dom}, q * m + r = q' * m + r' → r < m → q < q' → False := by
    intro q r q' r' h hr hq
    obtain ⟨z, rfl⟩ := hq; obtain ⟨w, hw⟩ := hr
    exact add_succ_ne_self r (w + z * m + r') (add_right_cancel' (by grind : r + (w + z * m + r' + 1) + q * m = r + q * m))
  rcases trichotomy q q' with hq | rfl | hq
  · exact (key h hr hq).elim
  · exact ⟨rfl, add_right_cancel' (by grind : r + q * m = r' + q * m)⟩
  · exact (key h.symm hr' hq).elim

/-! ## Gödel's β-function inside a model of PA -/

/-- The `i`-th β-modulus `1 + (i + 1)·d`. -/
def modB (d i : N.Dom) : N.Dom := 1 + (i + 1) * d

/-- **Gödel's β-relation in a model of PA**: `y` is the remainder of `c` modulo
`1 + (i + 1)·d`, i.e. `y` is the `i`-th entry of the sequence coded by `(c, d)`. -/
def BetaM (c d i y : N.Dom) : Prop := ∃ q, c = q * (1 + (i + 1) * d) + y ∧ y < 1 + (i + 1) * d

/-- The β-moduli are non-zero. -/
theorem modB_ne_zero (d i : N.Dom) : (1 + (i + 1) * d : N.Dom) ≠ 0 := by
  intro h; exact succ_ne_zero' ((i + 1) * d) (by grind)

/-- Every position of a β-code has an entry. -/
theorem betaM_exists (c d i : N.Dom) : ∃ y, BetaM c d i y := by
  obtain ⟨q, r, h, hr⟩ := div_exists (modB_ne_zero d i) c
  exact ⟨r, q, h, hr⟩

/-- The entry at a position of a β-code is unique. -/
theorem betaM_unique {c d i y y' : N.Dom} (h : BetaM c d i y) (h' : BetaM c d i y') : y = y' := by
  obtain ⟨q, hq, hy⟩ := h; obtain ⟨q', hq', hy'⟩ := h'
  exact (div_unique (hq.symm.trans hq') hy hy').2

/-- Entries of a β-code are bounded by the code. -/
theorem betaM_le {c d i y : N.Dom} (h : BetaM c d i y) : y ≤ c := by
  obtain ⟨q, rfl, _⟩ := h; exact ⟨q * (1 + (i + 1) * d), by grind⟩

/-- The β-relation is definable (at variables). -/
theorem Dfn.betaM_var (a b c d : Nat) : N.Dfn fun e => BetaM (e a) (e b) (e c) (e d) := by
  unfold BetaM; dfn

/-- **The β-relation is definable**, at any definable arguments. -/
theorem Dfn.betaM {fc fd fi fy : (Nat → N.Dom) → N.Dom} (hc : N.DfnT fc) (hd : N.DfnT fd)
    (hi : N.DfnT fi) (hy : N.DfnT fy) : N.Dfn fun e => BetaM (fc e) (fd e) (fi e) (fy e) := by
  have := (Dfn.betaM_var (N := N) 0 1 2 3).subst
    (σ := fun n => match n with | 0 => fc | 1 => fd | 2 => fi | _ => fy)
    (fun n => match n with | 0 => hc | 1 => hd | 2 => hi | _ + 3 => hy)
  exact this

macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.betaM)

end PAModel

end Foundations.Logic.FO
