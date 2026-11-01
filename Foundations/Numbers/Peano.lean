/-!
# The natural numbers, from Peano's axioms

This file begins Part II of the project: the *number systems*. Everything starts with the
natural numbers `0, 1, 2, …`, and we build them in the most austere way possible, following
Dedekind and Peano. A natural number is either

* `zero`, or
* `succ n`, the *successor* ("the next one after") of a natural number `n`.

Nothing else is a natural number, and every natural number arises in exactly one way from these
two clauses. In Lean this is literally an *inductive type*: the type is *generated* by its
constructors. Philosophically this is a striking stance: the numbers are not abstracted from
collections of things, but are the free result of a starting point and a "next" operation.
The principle of mathematical induction is then not an extra axiom but simply the statement that
there is nothing in the type beyond what the two clauses produce.

From this bare skeleton we define addition, multiplication, and the order `≤` by *recursion*
and prove all the familiar laws (associativity, commutativity, distributivity, cancellation, …)
by *induction*. We also prove the **well-ordering principle**: every nonempty collection of
natural numbers has a least element.

Finally we prove a **bridge theorem**: our home-made numbers `N` are isomorphic to Lean's
built-in natural numbers `Nat`, by an explicit bijection preserving `0`, successor, `+`, `×` and
`≤`. This licenses us, in all later files, to use Lean's `Nat` (and its efficient decision
procedure `omega`) freely: it is *the same structure* as the one we built by hand.
-/

namespace Foundations.Numbers

/-- The natural numbers, generated from `zero` by the successor operation `succ`.
This is Peano's axiomatisation, realised as an inductive type. -/
inductive N where
  /-- The first natural number, zero. -/
  | zero : N
  /-- The successor `n + 1` of a natural number `n`. -/
  | succ : N → N

namespace N

/-- Addition, defined by recursion on the second argument:
`n + 0 = n` and `n + succ m = succ (n + m)`. -/
def add : N → N → N
  | n, zero => n
  | n, succ m => succ (add n m)

/-- Multiplication, defined by recursion on the second argument:
`n * 0 = 0` and `n * succ m = n * m + n`. -/
def mul : N → N → N
  | _, zero => zero
  | n, succ m => add (mul n m) n

/-- Addition on the natural numbers. -/
instance : Add N := ⟨add⟩
/-- Multiplication on the natural numbers. -/
instance : Mul N := ⟨mul⟩

/-- The order on `N`: `n ≤ m` means that `m` is reached from `n` by adding something. -/
def le (n m : N) : Prop := ∃ k : N, n + k = m

/-- The order `≤` on the natural numbers. -/
instance : LE N := ⟨le⟩

/-- Strict order: `n < m` means `succ n ≤ m`. -/
instance : LT N := ⟨fun n m => succ n ≤ m⟩

/-- The number one, the successor of zero. -/
def one : N := succ zero

/-! ## Addition -/

/-- Defining equation: adding zero changes nothing. -/
@[simp] theorem add_zero (n : N) : n + zero = n := rfl

/-- Defining equation of addition at a successor. -/
@[simp] theorem add_succ (n m : N) : n + succ m = succ (n + m) := rfl

/-- Zero is also a left identity (this needs induction). -/
@[simp] theorem zero_add (n : N) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- A successor on the left can be pulled out of a sum. -/
@[simp] theorem succ_add (n m : N) : succ n + m = succ (n + m) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih]

/-- **Associativity of addition.** `(a + b) + c = a + (b + c)`. -/
theorem add_assoc (a b c : N) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih => simp [ih]

/-- **Commutativity of addition.** `a + b = b + a`. -/
theorem add_comm (a b : N) : a + b = b + a := by
  induction b with
  | zero => simp
  | succ b ih => simp [ih]

/-- The successor function is injective (one of Peano's axioms, here a theorem). -/
theorem succ_inj {a b : N} (h : succ a = succ b) : a = b := by
  cases h; rfl

/-- **Cancellation for addition.** If `a + c = b + c` then `a = b`. -/
theorem add_right_cancel {a b c : N} (h : a + c = b + c) : a = b := by
  induction c with
  | zero => simpa using h
  | succ c ih => exact ih (succ_inj (by simpa using h))

/-- Left cancellation for addition. -/
theorem add_left_cancel {a b c : N} (h : c + a = c + b) : a = b := by
  rw [add_comm c a, add_comm c b] at h
  exact add_right_cancel h

/-- A sum is zero only if both summands are zero. -/
theorem add_eq_zero {a b : N} (h : a + b = zero) : a = zero ∧ b = zero := by
  cases b with
  | zero => exact ⟨by simpa using h, rfl⟩
  | succ b => simp at h

/-- If `a + b = a` then `b = 0`. -/
theorem add_self_eq {a b : N} (h : a + b = a) : b = zero :=
  add_left_cancel (c := a) (by simpa using h)

/-! ## Multiplication -/

/-- Defining equation: multiplying by zero gives zero. -/
@[simp] theorem mul_zero (n : N) : n * zero = zero := rfl

/-- Defining equation of multiplication at a successor. -/
@[simp] theorem mul_succ (n m : N) : n * succ m = n * m + n := rfl

/-- Zero is also absorbing on the left. -/
@[simp] theorem zero_mul (n : N) : zero * n = zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- A successor on the left of a product. -/
@[simp] theorem succ_mul (n m : N) : succ n * m = n * m + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [mul_succ, ih, add_succ, add_assoc]
    rw [add_comm m n]

/-- **Distributivity.** `a * (b + c) = a * b + a * c`. -/
theorem mul_add (a b c : N) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rfl
  | succ c ih => simp [ih, add_assoc]

/-- **Commutativity of multiplication.** `a * b = b * a`. -/
theorem mul_comm (a b : N) : a * b = b * a := by
  induction b with
  | zero => simp
  | succ b ih => simp [ih]

/-- Right distributivity: `(a + b) * c = a * c + b * c`. -/
theorem add_mul (a b c : N) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

/-- **Associativity of multiplication.** `(a * b) * c = a * (b * c)`. -/
theorem mul_assoc (a b c : N) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih => simp [ih, mul_add]

/-- One is a multiplicative identity. -/
theorem mul_one (n : N) : n * one = n := by simp [one]

/-- A product is zero only if a factor is zero. -/
theorem mul_eq_zero {a b : N} (h : a * b = zero) : a = zero ∨ b = zero := by
  cases b with
  | zero => exact Or.inr rfl
  | succ b => exact Or.inl (add_eq_zero h).2

/-- **Cancellation for multiplication.** If `a * c = b * c` and `c ≠ 0` then `a = b`. -/
theorem mul_right_cancel {a b c : N} (hc : c ≠ zero) (h : a * c = b * c) : a = b := by
  induction a generalizing b with
  | zero =>
    rw [zero_mul] at h
    rcases mul_eq_zero h.symm with h' | h'
    · exact h'.symm
    · exact absurd h' hc
  | succ a ih =>
    cases b with
    | zero =>
      rw [zero_mul, succ_mul] at h
      exact absurd (add_eq_zero h).2 hc
    | succ b =>
      rw [succ_mul, succ_mul] at h
      rw [ih (add_right_cancel h)]

/-! ## Order -/

/-- `≤` is reflexive. -/
theorem le_refl (a : N) : a ≤ a := ⟨zero, rfl⟩

/-- `≤` is transitive. -/
theorem le_trans {a b c : N} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨j, rfl⟩ := h₂
  exact ⟨k + j, (add_assoc a k j).symm⟩

/-- `≤` is antisymmetric. -/
theorem le_antisymm {a b : N} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  rw [add_assoc] at hj
  have := (add_eq_zero (add_self_eq hj)).1
  subst this; rfl

/-- Zero is below everything. -/
theorem zero_le (a : N) : zero ≤ a := ⟨a, zero_add a⟩

/-- Successor is monotone. -/
theorem succ_le_succ {a b : N} (h : a ≤ b) : succ a ≤ succ b := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by simp⟩

/-- Successor reflects `≤`. -/
theorem le_of_succ_le_succ {a b : N} (h : succ a ≤ succ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, succ_inj (by simpa using hk)⟩

/-- `≤` is total: any two numbers are comparable. -/
theorem le_total (a b : N) : a ≤ b ∨ b ≤ a := by
  induction a generalizing b with
  | zero => exact Or.inl (zero_le b)
  | succ a ih =>
    cases b with
    | zero => exact Or.inr (zero_le _)
    | succ b =>
      rcases ih b with h | h
      · exact Or.inl (succ_le_succ h)
      · exact Or.inr (succ_le_succ h)

/-- **`≤` is a linear order.** It is reflexive, transitive, antisymmetric and total. -/
theorem le_linear_order :
    (∀ a : N, a ≤ a) ∧ (∀ a b c : N, a ≤ b → b ≤ c → a ≤ c) ∧
    (∀ a b : N, a ≤ b → b ≤ a → a = b) ∧ (∀ a b : N, a ≤ b ∨ b ≤ a) :=
  ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩

/-- **Order is compatible with addition.** `a ≤ b ↔ a + c ≤ b + c`. -/
theorem add_le_add_iff (a b c : N) : a ≤ b ↔ a + c ≤ b + c := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [add_assoc, add_assoc, add_comm k c]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, add_right_cancel (c := c) ?_⟩
    rw [← hk, add_assoc, add_comm k c, ← add_assoc]

/-- Being `≤ succ n` means being `≤ n` or equal to `succ n`. -/
theorem le_succ_cases {a n : N} (h : a ≤ succ n) : a ≤ n ∨ a = succ n := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => exact Or.inr hk
  | succ k => exact Or.inl ⟨k, succ_inj hk⟩

/-- **Well-ordering principle.** Every nonempty property of natural numbers has a least
witness: if some `n` satisfies `P`, then there is an `m` satisfying `P` with `m ≤ k` for every
`k` satisfying `P`. -/
theorem well_ordering (P : N → Prop) (h : ∃ n, P n) :
    ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  apply Classical.byContradiction
  intro hno
  -- If there is no least element, then no number `≤ n` satisfies `P`, for every `n`.
  have key : ∀ n, ∀ k, k ≤ n → ¬ P k := by
    intro n
    induction n with
    | zero =>
      intro k hk hP
      have hk0 : k = zero := le_antisymm hk (zero_le k)
      subst hk0
      exact hno ⟨zero, hP, fun j _ => zero_le j⟩
    | succ n ih =>
      intro k hk hP
      rcases le_succ_cases hk with hk' | hk'
      · exact ih k hk' hP
      · subst hk'
        apply hno
        refine ⟨succ n, hP, fun j hj => ?_⟩
        rcases le_total (succ n) j with h' | h'
        · exact h'
        · rcases le_succ_cases h' with h'' | h''
          · exact absurd hj (ih j h'')
          · rw [h'']; exact le_refl _
  obtain ⟨n, hn⟩ := h
  exact key n n (le_refl n) hn

/-! ## The bridge to Lean's `Nat` -/

/-- Translate a home-made natural number into Lean's built-in `Nat`. -/
def toNat : N → Nat
  | zero => 0
  | succ n => toNat n + 1

/-- Translate a Lean `Nat` into a home-made natural number. -/
def ofNat : Nat → N
  | 0 => zero
  | n + 1 => succ (ofNat n)

end N

/-- An *equivalence* (bijection with explicit inverse) between two types: a pair of maps
which undo each other. -/
structure Equiv (α β : Type) where
  /-- The forward map. -/
  toFun : α → β
  /-- The backward map. -/
  invFun : β → α
  /-- Going forward then back returns the starting point. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- Going back then forward returns the starting point. -/
  right_inv : ∀ b, toFun (invFun b) = b

namespace N

/-- The translations `toNat` and `ofNat` are mutually inverse: an explicit equivalence. -/
def equivNat : Equiv N Nat where
  toFun := toNat
  invFun := ofNat
  left_inv := by
    intro a
    induction a with
    | zero => rfl
    | succ a ih => simp [toNat, ofNat, ih]
  right_inv := by
    intro b
    induction b with
    | zero => rfl
    | succ b ih => simp [toNat, ofNat, ih]

/-- `toNat` preserves addition. -/
theorem toNat_add (a b : N) : toNat (a + b) = toNat a + toNat b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [toNat, ih]; omega

/-- `toNat` preserves multiplication. -/
theorem toNat_mul (a b : N) : toNat (a * b) = toNat a * toNat b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [toNat, toNat_add, ih, Nat.mul_succ]

/-- `toNat` is injective. -/
theorem toNat_inj {x y : N} (h : toNat x = toNat y) : x = y := by
  rw [← equivNat.left_inv x, ← equivNat.left_inv y]
  exact congrArg ofNat h

/-- `toNat ∘ ofNat` is the identity. -/
theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := equivNat.right_inv n

/-- `toNat` preserves and reflects the order. -/
theorem toNat_le (a b : N) : a ≤ b ↔ toNat a ≤ toNat b := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [toNat_add]; omega
  · intro h
    refine ⟨ofNat (toNat b - toNat a), toNat_inj ?_⟩
    rw [toNat_add, toNat_ofNat]; omega

/-- **Bridge theorem (ℕ).** The equivalence `N ≃ Nat` sends `0` to `0`, successor to `+1`,
and preserves addition, multiplication and order. Hence the home-made natural numbers and Lean's
`Nat` are the same structure, and we may use `Nat` from now on. -/
theorem bridge_nat :
    equivNat.toFun zero = 0 ∧
    (∀ n, equivNat.toFun (succ n) = equivNat.toFun n + 1) ∧
    (∀ a b, equivNat.toFun (a + b) = equivNat.toFun a + equivNat.toFun b) ∧
    (∀ a b, equivNat.toFun (a * b) = equivNat.toFun a * equivNat.toFun b) ∧
    (∀ a b, a ≤ b ↔ equivNat.toFun a ≤ equivNat.toFun b) :=
  ⟨rfl, fun _ => rfl, toNat_add, toNat_mul, toNat_le⟩

end N

end Foundations.Numbers
