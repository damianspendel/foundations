import Foundations.Logic.Incompleteness

/-!
# Robinson's arithmetic `Q`

Raphael Robinson (1950) isolated a strikingly weak fragment of Peano arithmetic which
is nevertheless strong enough for the incompleteness phenomena: **Robinson's `Q`**
keeps the recursion equations for `+` and `×` and the basic facts about successor,
but *drops induction entirely*, replacing it by the single axiom "every number is `0`
or a successor". `Q` cannot prove even `0 + x = x` or the commutativity of addition —
it has bizarre models — yet it proves every true *numerical* equation and, as the
next files show, every true Σ₁ sentence. This is all the incompleteness theorems
need, so they hold for *every* consistent, computably enumerable theory containing
`Q`.

In this file we define `Q`, show `Q ⊆ PA` (every axiom of `Q` is a theorem of PA; the
only non-trivial one, "every number is zero or a successor", is proved by induction
— via the completeness theorem, by showing it holds in every model of PA), and
develop the basic arithmetic of **arbitrary models of `Q`**. The point of working
semantically is that, by Gödel's completeness theorem, `Q ⊢ φ` iff `φ` holds in every
model of `Q`: we may reason about models instead of building formal derivations.
The key facts are about the *standard part* of a model — the values `n̄` of the
numerals:

* numerals add and multiply correctly: `m̄ + n̄ = (m + n)‾`, `m̄ · n̄ = (mn)‾`;
* distinct numerals have distinct values;
* everything below a numeral is a numeral: if `d + x = n̄` then `x = ī` for some
  `i ≤ n`;
* every element is comparable with every numeral: `x ≤ n̄` or `n̄ ≤ x`.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula

/-! ## The axioms -/

/-- **Robinson's arithmetic `Q`.** The axioms of PA without induction, plus the
axiom that every number is zero or a successor. -/
inductive Q : Theory Arith where
  /-- `∀x. S x ≠ 0`. -/
  | succ_ne_zero : Q (all (neg (eq (succ (v 0)) zero)))
  /-- `∀x ∀y. S x = S y → x = y`. -/
  | succ_inj : Q (all (all (imp (eq (succ (v 1)) (succ (v 0))) (eq (v 1) (v 0)))))
  /-- `∀x. x = 0 ∨ ∃y. x = S y`. -/
  | zero_or_succ : Q (all (disj (eq (v 0) zero) (ex (eq (v 1) (succ (v 0))))))
  /-- `∀x. x + 0 = x`. -/
  | add_zero : Q (all (eq (add (v 0) zero) (v 0)))
  /-- `∀x ∀y. x + S y = S (x + y)`. -/
  | add_succ : Q (all (all (eq (add (v 1) (succ (v 0))) (succ (add (v 1) (v 0))))))
  /-- `∀x. x × 0 = 0`. -/
  | mul_zero : Q (all (eq (mul (v 0) zero) zero))
  /-- `∀x ∀y. x × S y = x × y + x`. -/
  | mul_succ : Q (all (all (eq (mul (v 1) (succ (v 0))) (add (mul (v 1) (v 0)) (v 1)))))

/-! ## Arithmetic operations in a structure -/

variable (M : Structure Arith)

/-- The zero of a structure. -/
def mz : M.Dom := M.funcs (n := 0) ArithFunc.zero Fin.elim0
/-- The successor of a structure. -/
def ms (x : M.Dom) : M.Dom := M.funcs (n := 1) ArithFunc.succ fun _ => x
/-- The addition of a structure. -/
def madd (x y : M.Dom) : M.Dom := M.funcs (n := 2) ArithFunc.add fun i => if i.val = 0 then x else y
/-- The multiplication of a structure. -/
def mmul (x y : M.Dom) : M.Dom := M.funcs (n := 2) ArithFunc.mul fun i => if i.val = 0 then x else y

variable {M}

/-- Value of `0`. -/
@[simp] theorem eval_zero_M (e : Nat → M.Dom) : (zero : Term Arith).eval M e = mz M := by
  simp only [zero, Term.eval, mz]; congr; funext i; exact i.elim0

/-- Value of a successor. -/
@[simp] theorem eval_succ_M (e : Nat → M.Dom) (t : Term Arith) :
    (succ t).eval M e = ms M (t.eval M e) := rfl

/-- Value of a sum. -/
@[simp] theorem eval_add_M (e : Nat → M.Dom) (t s : Term Arith) :
    (add t s).eval M e = madd M (t.eval M e) (s.eval M e) := by
  simp only [add, Term.eval, madd]; congr; funext i; simp only [args₂]; split <;> rfl

/-- Value of a product. -/
@[simp] theorem eval_mul_M (e : Nat → M.Dom) (t s : Term Arith) :
    (mul t s).eval M e = mmul M (t.eval M e) (s.eval M e) := by
  simp only [mul, Term.eval, mmul]; congr; funext i; simp only [args₂]; split <;> rfl

/-- Value of a variable. -/
@[simp] theorem eval_var_M (e : Nat → M.Dom) (n : Nat) : (v n).eval M e = e n := rfl

/-- **Models of `Q`**, stated as properties of the operations. -/
structure IsQModel (M : Structure Arith) : Prop where
  /-- `S x ≠ 0`. -/
  succ_ne_zero : ∀ x, ms M x ≠ mz M
  /-- Successor is injective. -/
  succ_inj : ∀ x y, ms M x = ms M y → x = y
  /-- Every element is zero or a successor. -/
  zero_or_succ : ∀ x, x = mz M ∨ ∃ y, x = ms M y
  /-- `x + 0 = x`. -/
  add_zero : ∀ x, madd M x (mz M) = x
  /-- `x + S y = S (x + y)`. -/
  add_succ : ∀ x y, madd M x (ms M y) = ms M (madd M x y)
  /-- `x × 0 = 0`. -/
  mul_zero : ∀ x, mmul M x (mz M) = mz M
  /-- `x × S y = x × y + x`. -/
  mul_succ : ∀ x y, mmul M x (ms M y) = madd M (mmul M x y) x

/-- A structure satisfying the axioms of `Q` (under some environment) is a model of
`Q` in the sense of `IsQModel` (the axioms are closed). -/
theorem isQModel_of_sat {e : Nat → M.Dom} (h : ∀ ψ, Q ψ → Sat M e ψ) : IsQModel M where
  succ_ne_zero := fun x => by have := h _ Q.succ_ne_zero x; simpa [Sat, Env.cons, neg] using this
  succ_inj := fun x y => by have := h _ Q.succ_inj x y; simpa [Sat, Env.cons] using this
  zero_or_succ := fun x => by have := h _ Q.zero_or_succ x; simpa [Sat, Env.cons] using this
  add_zero := fun x => by have := h _ Q.add_zero x; simpa [Sat, Env.cons] using this
  add_succ := fun x y => by have := h _ Q.add_succ x y; simpa [Sat, Env.cons] using this
  mul_zero := fun x => by have := h _ Q.mul_zero x; simpa [Sat, Env.cons] using this
  mul_succ := fun x y => by have := h _ Q.mul_succ x y; simpa [Sat, Env.cons] using this

/-- Conversely, a model of `Q` satisfies its axioms under every environment. -/
theorem sat_of_isQModel (hM : IsQModel M) (e : Nat → M.Dom) : ∀ ψ, Q ψ → Sat M e ψ := by
  intro ψ hψ
  cases hψ <;> simp only [Sat, Env.cons, eval_succ_M, eval_zero_M, eval_add_M, eval_mul_M,
    eval_var_M, neg]
  · exact fun x => hM.succ_ne_zero x
  · exact fun x y => hM.succ_inj x y
  · intro x
    rcases hM.zero_or_succ x with h | ⟨y, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, h⟩
  · exact fun x => hM.add_zero x
  · exact fun x y => hM.add_succ x y
  · exact fun x => hM.mul_zero x
  · exact fun x y => hM.mul_succ x y

/-- The standard model is a model of `Q`. -/
theorem stdModel_isQModel : IsQModel stdModel where
  succ_ne_zero := fun x h => Nat.succ_ne_zero x h
  succ_inj := fun x y h => Nat.succ.inj h
  zero_or_succ := fun x => by
    cases x with
    | zero => exact Or.inl rfl
    | succ y => exact Or.inr ⟨y, rfl⟩
  add_zero := fun x => rfl
  add_succ := fun x y => rfl
  mul_zero := fun x => rfl
  mul_succ := fun x y => Nat.mul_succ x y

/-- `Q ⊢ φ` iff `φ` holds in every model of `Q` under every environment. -/
theorem Q_proves_of_models {φ : Formula Arith}
    (h : ∀ (M : Structure Arith) (e : Nat → M.Dom), IsQModel M → Sat M e φ) : Q ⊢₁ φ :=
  completeness fun M e hQ => h M e (isQModel_of_sat hQ)

/-- Soundness for `Q`, in model form. -/
theorem sat_of_Q_proves {φ : Formula Arith} (h : Q ⊢₁ φ) {M : Structure Arith} (hM : IsQModel M)
    (e : Nat → M.Dom) : Sat M e φ :=
  Proves.soundness h M e (sat_of_isQModel hM e)

/-! ## `Q` is contained in PA -/

/-- **Every axiom of `Q` is a theorem of PA.** -/
theorem PA_proves_Q {ψ : Formula Arith} (h : Q ψ) : PA ⊢₁ ψ := by
  cases h
  · exact Proves.hyp PA.succ_ne_zero
  · exact Proves.hyp PA.succ_inj
  · -- by induction, semantically in every model of PA
    refine completeness fun M e hPA => ?_
    let φ : Formula Arith := disj (eq (v 0) zero) (ex (eq (v 1) (succ (v 0))))
    have hind := hPA _ (PA.induction φ)
    simp only [Sat] at hind
    refine hind ⟨?_, ?_⟩
    · rw [sat_inst]; left; simp [Sat, Env.cons]
    · intro x _
      rw [sat_subst]
      right
      exact ⟨x, by simp [Sat, Env.cons, succSubst]⟩
  · exact Proves.hyp PA.add_zero
  · exact Proves.hyp PA.add_succ
  · exact Proves.hyp PA.mul_zero
  · exact Proves.hyp PA.mul_succ

/-- A model of PA is a model of `Q`. -/
theorem isQModel_of_PA {e : Nat → M.Dom} (h : ∀ ψ, PA ψ → Sat M e ψ) : IsQModel M :=
  isQModel_of_sat fun _ hψ => Proves.soundness (PA_proves_Q hψ) M e h

/-- **Theories containing `Q`.** If a theory proves every axiom of `Q`, it proves every
theorem of `Q`. -/
theorem proves_of_Q_proves {T : Theory Arith} (hT : ∀ ψ, Q ψ → T ⊢₁ ψ) {φ : Formula Arith}
    (h : Q ⊢₁ φ) : T ⊢₁ φ :=
  completeness fun M e hM =>
    sat_of_Q_proves h (isQModel_of_sat fun ψ hψ => Proves.soundness (hT ψ hψ) M e hM) e

/-- **`Q ⊆ PA`**: every theorem of `Q` is a theorem of PA. -/
theorem PA_proves_of_Q_proves {φ : Formula Arith} (h : Q ⊢₁ φ) : PA ⊢₁ φ :=
  proves_of_Q_proves (fun _ hψ => PA_proves_Q hψ) h

/-! ## The standard part of a model of `Q` -/

/-- The value of the numeral `n̄` in a structure. -/
def numM (M : Structure Arith) : Nat → M.Dom
  | 0 => mz M
  | n + 1 => ms M (numM M n)

/-- Numerals denote their `numM` values. -/
@[simp] theorem eval_numeral_M (e : Nat → M.Dom) : ∀ n, (numeral n).eval M e = numM M n
  | 0 => eval_zero_M e
  | n + 1 => by simp only [numeral, eval_succ_M, eval_numeral_M e n, numM]

/-- `numM` in the standard model is the identity. -/
@[simp] theorem numM_std (n : Nat) : numM stdModel n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [numM, ih]; rfl

/-- "`x ≤ y`" in a structure, as `∃d. d + x = y`. -/
def mle (M : Structure Arith) (x y : M.Dom) : Prop := ∃ d, madd M d x = y

variable (hM : IsQModel M)
include hM

/-- **Numerals add correctly.** -/
theorem numM_add (a : Nat) : ∀ b, madd M (numM M a) (numM M b) = numM M (a + b)
  | 0 => hM.add_zero _
  | b + 1 => by rw [numM, hM.add_succ, numM_add a b]; rfl

/-- `x + n̄` for a numeral `n̄`, unfolded. -/
theorem madd_numM_succ (x : M.Dom) (n : Nat) : madd M x (numM M (n + 1)) = ms M (madd M x (numM M n)) :=
  hM.add_succ _ _

/-- **Numerals multiply correctly.** -/
theorem numM_mul (a : Nat) : ∀ b, mmul M (numM M a) (numM M b) = numM M (a * b)
  | 0 => hM.mul_zero _
  | b + 1 => by rw [numM, hM.mul_succ, numM_mul a b, numM_add hM, Nat.mul_succ]

/-- **Distinct numerals have distinct values.** -/
theorem numM_inj : ∀ {a b : Nat}, numM M a = numM M b → a = b
  | 0, 0, _ => rfl
  | 0, b + 1, h => absurd h.symm (hM.succ_ne_zero _)
  | a + 1, 0, h => absurd h (hM.succ_ne_zero _)
  | a + 1, b + 1, h => by rw [numM_inj (hM.succ_inj _ _ h)]

/-- `0 + n̄ = n̄`. -/
theorem zero_add_numM : ∀ n, madd M (mz M) (numM M n) = numM M n
  | 0 => hM.add_zero _
  | n + 1 => by rw [madd_numM_succ hM, zero_add_numM n]; rfl

/-- `S d + n̄ = S (d + n̄)`. -/
theorem succ_add_numM (d : M.Dom) : ∀ n, madd M (ms M d) (numM M n) = ms M (madd M d (numM M n))
  | 0 => by rw [numM, hM.add_zero, hM.add_zero]
  | n + 1 => by rw [madd_numM_succ hM, madd_numM_succ hM, succ_add_numM d n]

/-- Associativity with a numeral on the right: `(x + y) + n̄ = x + (y + n̄)`. -/
theorem add_assoc_numM (x y : M.Dom) : ∀ n,
    madd M (madd M x y) (numM M n) = madd M x (madd M y (numM M n))
  | 0 => by rw [numM, hM.add_zero, hM.add_zero]
  | n + 1 => by rw [madd_numM_succ hM, madd_numM_succ hM, hM.add_succ, add_assoc_numM x y n]

/-- **Everything below a numeral is a numeral.** In a model of `Q`, `x ≤ n̄` (that is,
`d + x = n̄` for some `d`) iff `x = ī` for some `i ≤ n`. -/
theorem mle_numM_iff (x : M.Dom) (n : Nat) : mle M x (numM M n) ↔ ∃ i, i ≤ n ∧ x = numM M i := by
  constructor
  · rintro ⟨d, hd⟩
    induction n generalizing x with
    | zero =>
        refine ⟨0, Nat.le_refl _, ?_⟩
        rcases hM.zero_or_succ x with rfl | ⟨y, rfl⟩
        · rfl
        · rw [hM.add_succ] at hd; exact absurd hd (hM.succ_ne_zero _)
    | succ n ih =>
        rcases hM.zero_or_succ x with rfl | ⟨y, rfl⟩
        · exact ⟨0, Nat.zero_le _, rfl⟩
        · rw [hM.add_succ] at hd
          obtain ⟨i, hi, rfl⟩ := ih y (hM.succ_inj _ _ hd)
          exact ⟨i + 1, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨numM M (n - i), ?_⟩
    rw [numM_add hM, Nat.sub_add_cancel hi]

/-- Below a numeral, strictly: `S x ≤ n̄` iff `x = ī` with `i < n`. -/
theorem mle_succ_numM_iff (x : M.Dom) (n : Nat) :
    mle M (ms M x) (numM M n) ↔ ∃ i, i < n ∧ x = numM M i := by
  rw [mle_numM_iff hM]
  constructor
  · rintro ⟨i, hi, h⟩
    cases i with
    | zero => exact absurd h (hM.succ_ne_zero _)
    | succ i => exact ⟨i, by omega, hM.succ_inj _ _ h⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i + 1, by omega, rfl⟩

/-- **Comparability with numerals.** Every element `x` of a model of `Q` satisfies
`x ≤ n̄` or `n̄ ≤ x`. -/
theorem mle_numM_or (x : M.Dom) : ∀ n, mle M x (numM M n) ∨ mle M (numM M n) x
  | 0 => Or.inr ⟨x, hM.add_zero x⟩
  | n + 1 => by
      rcases mle_numM_or x n with h | ⟨d, hd⟩
      · obtain ⟨i, hi, rfl⟩ := (mle_numM_iff hM x n).1 h
        exact Or.inl ((mle_numM_iff hM _ _).2 ⟨i, by omega, rfl⟩)
      · rcases hM.zero_or_succ d with rfl | ⟨d', rfl⟩
        · rw [zero_add_numM hM] at hd
          subst hd
          exact Or.inl ((mle_numM_iff hM _ _).2 ⟨n, by omega, rfl⟩)
        · refine Or.inr ⟨d', ?_⟩
          rw [madd_numM_succ hM, ← succ_add_numM hM, hd]

/-- Transitivity through numerals: if `m ≤ k` and `k̄ ≤ x` then `m̄ ≤ x`. -/
theorem mle_numM_trans {m k : Nat} (hmk : m ≤ k) {x : M.Dom} (h : mle M (numM M k) x) :
    mle M (numM M m) x := by
  obtain ⟨d, hd⟩ := h
  refine ⟨madd M d (numM M (k - m)), ?_⟩
  rw [add_assoc_numM hM, numM_add hM, Nat.sub_add_cancel hmk, hd]

end Foundations.Logic.FO
