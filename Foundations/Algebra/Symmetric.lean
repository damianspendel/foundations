import Foundations.Algebra.FiniteField

/-!
# The symmetric group and the sign of a permutation

The permutations of `n` objects form the **symmetric group** `Sₙ`, here `Perm (Fin n)`. It is
the group in which Lagrange (1770) and Ruffini (1799) first glimpsed why equations of degree
five resist solution by radicals, and it is by Cayley's theorem the universal home of all
finite groups.

Every permutation is a product of **transpositions** (swaps of two letters). The number of
transpositions needed is not determined, but its *parity* is: this is the theorem of the
**sign** `sgn : Sₙ → {±1}`, first used systematically by Cauchy (1815) in his theory of
determinants. We define the parity of `σ` as the parity of its number of **inversions** —
pairs `i < j` with `σ i > σ j` — and show that it is a homomorphism: the parity of `στ` is
the sum of the parities. The proof uses a symmetry argument instead of counting: for each
pair `{i, j}` the quantity "`σ` reverses `{i, j}`" does not depend on the order in which the
pair is listed, and `τ` merely permutes the pairs.

A transposition has sign `-1`: a direct count shows this for `(0 1)`, and every transposition
is a conjugate of `(0 1)`, while conjugate permutations have the same sign because the sign
takes values in a commutative group.

We also introduce the **3-cycles** `(a b c)`, which play the leading role in the next two
files.
-/

namespace Foundations.Algebra

open FiniteType Group

universe u

/-! ## Parities as an additive group -/

/-- Parities `false` (even) and `true` (odd) form an additive group under exclusive or. -/
instance Bool.instAddAbGroup : AddAbGroup Bool where
  add := xor
  zero := false
  neg b := b
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  neg_add_cancel := by decide

/-- Addition of parities is exclusive or. -/
theorem Bool.add_def (a b : Bool) : a + b = xor a b := rfl

/-! ## Basic facts about permutations -/

namespace Perm

variable {α : Type u}

/-- A permutation is injective. -/
theorem injective (σ : Perm α) {x y : α} (h : σ x = σ y) : x = y := by
  rw [← σ.left_inv x, ← σ.left_inv y]; exact congrArg σ.invFun h

/-- Applying the inverse permutation. -/
@[simp] theorem inv_toFun (σ : Perm α) (x : α) : σ⁻¹ x = σ.invFun x := rfl

/-- `σ (σ⁻¹ x) = x`. -/
@[simp] theorem apply_inv (σ : Perm α) (x : α) : σ (σ.invFun x) = x := σ.right_inv x

/-- `σ⁻¹ (σ x) = x`. -/
@[simp] theorem inv_apply (σ : Perm α) (x : α) : σ.invFun (σ x) = x := σ.left_inv x

variable [DecidableEq α]

/-- `swap a b` sends `a` to `b`. -/
@[simp] theorem swap_apply_left (a b : α) : swap a b a = b := by simp [swap]

/-- `swap a b` sends `b` to `a`. -/
@[simp] theorem swap_apply_right (a b : α) : swap a b b = a := by
  show (if b = a then b else if b = b then a else b) = a
  by_cases h : b = a <;> simp [h]

/-- `swap a b` fixes every other point. -/
theorem swap_apply_of_ne {a b x : α} (ha : x ≠ a) (hb : x ≠ b) : swap a b x = x := by
  show (if x = a then b else if x = b then a else x) = x
  simp [ha, hb]

/-- The value of `swap a b` at any point. -/
theorem swap_apply (a b x : α) : swap a b x = if x = a then b else if x = b then a else x := rfl

/-- A transposition is its own inverse. -/
@[simp] theorem swap_mul_self (a b : α) : swap a b * swap a b = 1 := by
  apply ext; intro x
  simp only [mul_apply, one_apply, swap_apply]
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> simp_all

/-- The inverse of a transposition is itself. -/
theorem swap_inv (a b : α) : (swap a b)⁻¹ = swap a b :=
  inv_eq_of_mul_eq_one (swap_mul_self a b)

/-- `swap a b = swap b a`. -/
theorem swap_comm (a b : α) : swap a b = swap b a := by
  apply ext; intro x
  simp only [swap_apply]
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> simp_all

/-- `swap a a` is the identity. -/
theorem swap_self (a : α) : swap a a = 1 := by
  apply ext; intro x; simp only [swap_apply, one_apply]
  by_cases h : x = a <;> simp_all

/-- **Conjugating a transposition** relabels it: `σ (a b) σ⁻¹ = (σa σb)`. -/
theorem conj_swap (σ : Perm α) (a b : α) : σ * swap a b * σ⁻¹ = swap (σ a) (σ b) := by
  apply ext; intro x
  simp only [mul_apply, inv_toFun, swap_apply]
  by_cases h1 : σ.invFun x = a
  · have : x = σ a := by rw [← h1, apply_inv]
    simp [this]
  · by_cases h2 : σ.invFun x = b
    · have hxb : x = σ b := by rw [← h2, apply_inv]
      have hxa : x ≠ σ a := fun h => h1 (by rw [h, inv_apply])
      have hba : b ≠ a := fun e => h1 (h2.trans e)
      have hσ : σ b ≠ σ a := fun e => hba (σ.injective e)
      rw [h2, hxb]
      simp [hba, hσ]
    · have e1 : x ≠ σ a := fun h => h1 (by rw [h, inv_apply])
      have e2 : x ≠ σ b := fun h => h2 (by rw [h, inv_apply])
      simp [h1, h2, e1, e2]

end Perm

open Perm

/-! ## Products of lists -/

/-- The product of a list of group elements. -/
def gprod {G : Type u} [Group G] : List G → G
  | [] => 1
  | a :: l => a * gprod l

/-- The product of a concatenation. -/
theorem gprod_append {G : Type u} [Group G] (l m : List G) : gprod (l ++ m) = gprod l * gprod m := by
  induction l with
  | nil => exact (one_mul _).symm
  | cons a l ih => show a * gprod (l ++ m) = a * gprod l * gprod m; rw [ih, mul_assoc]

/-- A subgroup containing every entry of a list contains its product. -/
theorem gprod_mem {G : Type u} [Group G] (H : Subgroup G) :
    ∀ l : List G, (∀ x, x ∈ l → x ∈ H) → gprod l ∈ H
  | [], _ => H.one_mem
  | a :: l, h => H.mul_mem (h a List.mem_cons_self)
      (gprod_mem H l fun x hx => h x (List.mem_cons_of_mem a hx))

/-! ## Transpositions generate -/

/-- `t` is a **transposition**: `t = (a b)` with `a ≠ b`. -/
def IsTransposition {n : Nat} (t : Perm (Fin n)) : Prop := ∃ a b, a ≠ b ∧ t = swap a b

/-- **Transpositions generate `Sₙ`.** Every permutation of `Fin n` is a product of
transpositions. Proof: if `σ` moves `x`, then `(σx x) σ` fixes `x` and every point fixed by
`σ`; induct on the number of moved points. -/
theorem exists_transpositions {n : Nat} :
    ∀ (k : Nat) (σ : Perm (Fin n)), count (fun x => σ x ≠ x) = k →
      ∃ L : List (Perm (Fin n)), (∀ t, t ∈ L → IsTransposition t) ∧ gprod L = σ := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro σ hk
    by_cases hid : ∀ x, σ x = x
    · exact ⟨[], fun _ h => absurd h List.not_mem_nil, (ext hid).symm⟩
    · have : ∃ x, σ x ≠ x := Classical.byContradiction fun h =>
        hid fun x => Classical.byContradiction fun hx => h ⟨x, hx⟩
      obtain ⟨x, hx⟩ := this
      let σ' := swap (σ x) x * σ
      have hsub : ∀ y, σ' y ≠ y → σ y ≠ y := by
        intro y hy hfix
        apply hy
        show swap (σ x) x (σ y) = y
        rw [hfix]
        have h1 : y ≠ σ x := by
          intro h; apply hx
          have : σ y = σ x := by rw [hfix, h]
          rw [← σ.injective this, hfix]
        have h2 : y ≠ x := by intro h; apply hx; rw [← h, hfix]
        exact swap_apply_of_ne h1 h2
      have hfx : σ' x = x := by show swap (σ x) x (σ x) = x; exact swap_apply_left _ _
      have hlt : count (fun y => σ' y ≠ y) < k := by
        have h1 := count_split (fun y => σ y ≠ y) (fun y => σ' y ≠ y)
        have h2 : count (fun y => σ y ≠ y ∧ σ' y ≠ y) = count (fun y => σ' y ≠ y) :=
          count_congr fun y => ⟨fun h => h.2, fun h => ⟨hsub y h, h⟩⟩
        have h3 : 0 < count (fun y => σ y ≠ y ∧ ¬ σ' y ≠ y) :=
          count_pos.2 ⟨x, hx, fun h => h hfx⟩
        omega
      obtain ⟨L, hL, hprod⟩ := ih _ hlt σ' rfl
      refine ⟨swap (σ x) x :: L, fun t ht => ?_, ?_⟩
      · rcases List.mem_cons.1 ht with h | h
        · exact ⟨σ x, x, hx, h⟩
        · exact hL t h
      · show swap (σ x) x * gprod L = σ
        rw [hprod, ← mul_assoc, swap_mul_self, one_mul]

/-- Every permutation is a product of transpositions. -/
theorem transpositions_generate {n : Nat} (σ : Perm (Fin n)) :
    ∃ L : List (Perm (Fin n)), (∀ t, t ∈ L → IsTransposition t) ∧ gprod L = σ :=
  exists_transpositions _ σ rfl

/-! ## Inversions and parity -/

/-- The ordered pairs `i < j` of elements of `Fin n`. -/
def Pairs (n : Nat) : Type := {p : Fin n × Fin n // p.1 < p.2}

/-- The finitely many pairs, listed explicitly (so that parities can be computed). -/
instance Pairs.instFinite (n : Nat) : FiniteType (Pairs n) where
  elems := listSubtype (fun p : Fin n × Fin n => p.1 < p.2) elems
  nodup := nodup_listSubtype _ _ nodup
  complete x := (mem_listSubtype _ _ x).2 (complete _)

/-- Whether the pair of values `(a, b)` is out of order. -/
def inv {n : Nat} (a b : Fin n) : Bool := decide (b < a)

/-- For distinct `a`, `b`, exactly one of `(a, b)` and `(b, a)` is out of order. -/
theorem inv_swap {n : Nat} {a b : Fin n} (h : a ≠ b) : inv b a = !inv a b := by
  have hv : a.val ≠ b.val := fun e => h (Fin.ext e)
  unfold inv
  rcases Nat.lt_or_gt_of_ne hv with hl | hl
  · have h1 : a < b := hl
    have h2 : ¬ b < a := fun e => absurd (show b.val < a.val from e) (by omega)
    simp [h1, h2]
  · have h1 : b < a := hl
    have h2 : ¬ a < b := fun e => absurd (show a.val < b.val from e) (by omega)
    simp [h1, h2]

/-- The **parity** of a permutation: the parity of its number of inversions. -/
def parity {n : Nat} (σ : Perm (Fin n)) : Bool := isum (fun p : Pairs n => inv (σ p.1.1) (σ p.1.2))

/-- The identity has no inversions. -/
theorem parity_one {n : Nat} : parity (1 : Perm (Fin n)) = false := by
  apply isum_eq_zero
  intro p
  show decide (p.1.2 < p.1.1) = false
  have := p.2
  simp only [decide_eq_false_iff_not]
  intro h; exact absurd (Nat.lt_trans h this) (Nat.lt_irrefl _)

/-- **The parity is a homomorphism**: `parity (στ) = parity σ + parity τ`. -/
theorem parity_mul {n : Nat} (σ τ : Perm (Fin n)) : parity (σ * τ) = parity σ + parity τ := by
  -- `f x y` is symmetric for distinct `x`, `y`.
  let f : Fin n → Fin n → Bool := fun x y => inv (σ x) (σ y) + inv x y
  have hf : ∀ x y, x ≠ y → f x y = f y x := by
    intro x y hxy
    have hσ : σ x ≠ σ y := fun h => hxy (σ.injective h)
    show inv (σ x) (σ y) + inv x y = inv (σ y) (σ x) + inv y x
    rw [inv_swap hσ, inv_swap hxy]
    cases inv (σ x) (σ y) <;> cases inv x y <;> rfl
  -- `τ` permutes the pairs.
  have hne : ∀ p : Pairs n, τ p.1.1 ≠ τ p.1.2 := fun p h =>
    absurd (τ.injective h ▸ p.2) (Nat.lt_irrefl _)
  let φ : Pairs n → Pairs n := fun p =>
    if h : τ p.1.1 < τ p.1.2 then ⟨(τ p.1.1, τ p.1.2), h⟩
    else ⟨(τ p.1.2, τ p.1.1), by
      have := hne p
      have hv : (τ p.1.1).val ≠ (τ p.1.2).val := fun e => this (Fin.ext e)
      show (τ p.1.2).val < (τ p.1.1).val
      have : ¬ (τ p.1.1).val < (τ p.1.2).val := h
      omega⟩
  have hφ : ∀ p, f (τ p.1.1) (τ p.1.2) = f (φ p).1.1 (φ p).1.2 := by
    intro p
    by_cases h : τ p.1.1 < τ p.1.2
    · simp only [φ, h, ↓reduceDIte]
    · simp only [φ, h, ↓reduceDIte]; exact hf _ _ (hne p)
  have hφ_val : ∀ p, ((φ p).1.1 = τ p.1.1 ∧ (φ p).1.2 = τ p.1.2) ∨
      ((φ p).1.1 = τ p.1.2 ∧ (φ p).1.2 = τ p.1.1) := by
    intro p
    by_cases h : τ p.1.1 < τ p.1.2
    · left; simp [φ, h]
    · right; simp [φ, h]
  have lt_asymm : ∀ {a b : Fin n}, a < b → b < a → False := fun h1 h2 =>
    absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl _)
  have hinj : ∀ p q, φ p = φ q → p = q := by
    intro p q hpq
    have e1 : (φ p).1.1 = (φ q).1.1 := by rw [hpq]
    have e2 : (φ p).1.2 = (φ q).1.2 := by rw [hpq]
    apply Subtype.ext
    rcases hφ_val p with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hφ_val q with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact Prod.ext (τ.injective (by rw [← a1, ← b1, e1])) (τ.injective (by rw [← a2, ← b2, e2]))
    · have h1 := τ.injective (show τ p.1.1 = τ q.1.2 by rw [← a1, ← b1, e1])
      have h2 := τ.injective (show τ p.1.2 = τ q.1.1 by rw [← a2, ← b2, e2])
      exact absurd (h1 ▸ h2 ▸ p.2) (fun h => lt_asymm h q.2)
    · have h1 := τ.injective (show τ p.1.2 = τ q.1.1 by rw [← a1, ← b1, e1])
      have h2 := τ.injective (show τ p.1.1 = τ q.1.2 by rw [← a2, ← b2, e2])
      exact absurd (h1 ▸ h2 ▸ p.2) (fun h => lt_asymm h q.2)
    · exact Prod.ext (τ.injective (by rw [← a2, ← b2, e2])) (τ.injective (by rw [← a1, ← b1, e1]))
  have hsurj : ∀ q, ∃ p, φ p = q := by
    intro q
    let x := τ.invFun q.1.1
    let y := τ.invFun q.1.2
    have hxy : x ≠ y := fun h => absurd (by
      have := congrArg τ.toFun h; simp only [x, y] at this
      rw [τ.right_inv, τ.right_inv] at this; exact this ▸ q.2) (Nat.lt_irrefl _)
    have hv : x.val ≠ y.val := fun e => hxy (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hv with hl | hl
    · refine ⟨⟨(x, y), hl⟩, ?_⟩
      have hlt : τ x < τ y := by
        show (τ.toFun (τ.invFun q.1.1)) < τ.toFun (τ.invFun q.1.2)
        rw [τ.right_inv, τ.right_inv]; exact q.2
      apply Subtype.ext
      simp only [φ, hlt, ↓reduceDIte]
      exact Prod.ext (τ.right_inv _) (τ.right_inv _)
    · refine ⟨⟨(y, x), hl⟩, ?_⟩
      have hlt : ¬ τ y < τ x := by
        show ¬ (τ.toFun (τ.invFun q.1.2)) < τ.toFun (τ.invFun q.1.1)
        rw [τ.right_inv, τ.right_inv]; exact fun h => lt_asymm h q.2
      apply Subtype.ext
      simp only [φ, hlt, ↓reduceDIte]
      exact Prod.ext (τ.right_inv _) (τ.right_inv _)
  -- Assemble.
  have step : ∀ p : Pairs n, inv ((σ * τ) p.1.1) ((σ * τ) p.1.2) =
      f (τ p.1.1) (τ p.1.2) + inv (τ p.1.1) (τ p.1.2) := by
    intro p
    show inv (σ (τ p.1.1)) (σ (τ p.1.2)) = (inv (σ (τ p.1.1)) (σ (τ p.1.2)) + inv _ _) + inv _ _
    cases inv (σ (τ p.1.1)) (σ (τ p.1.2)) <;> cases inv (τ p.1.1) (τ p.1.2) <;> rfl
  have hfp : ∀ p : Pairs n, f p.1.1 p.1.2 = inv (σ p.1.1) (σ p.1.2) := by
    intro p
    show inv (σ p.1.1) (σ p.1.2) + decide (p.1.2 < p.1.1) = _
    have : ¬ p.1.2 < p.1.1 := fun h => lt_asymm h p.2
    simp only [this, decide_false]
    cases inv (σ p.1.1) (σ p.1.2) <;> rfl
  unfold parity
  rw [show (fun p : Pairs n => inv ((σ * τ) p.1.1) ((σ * τ) p.1.2)) =
      fun p => f (τ p.1.1) (τ p.1.2) + inv (τ p.1.1) (τ p.1.2) from funext step, isum_add]
  congr 1
  rw [show (fun p : Pairs n => f (τ p.1.1) (τ p.1.2)) = fun p => f (φ p).1.1 (φ p).1.2 from
    funext hφ, isum_comp_bij φ hinj hsurj (fun p => f p.1.1 p.1.2)]
  exact congrArg isum (funext hfp)

/-- A permutation and its inverse have the same parity. -/
theorem parity_inv {n : Nat} (σ : Perm (Fin n)) : parity σ⁻¹ = parity σ := by
  have h := parity_mul σ σ⁻¹
  rw [mul_inv_cancel, parity_one] at h
  revert h; cases parity σ <;> cases parity σ⁻¹ <;> decide

/-- **Conjugate permutations have the same parity.** -/
theorem parity_conj {n : Nat} (π σ : Perm (Fin n)) : parity (π * σ * π⁻¹) = parity σ := by
  rw [parity_mul, parity_mul, parity_inv]
  cases parity π <;> cases parity σ <;> rfl

/-- The transposition `(0 1)` has exactly one inversion. -/
theorem parity_swap01 (m : Nat) : parity (swap (0 : Fin (m + 2)) 1) = true := by
  have hv0 : (0 : Fin (m + 2)).val = 0 := rfl
  have hv1 : (1 : Fin (m + 2)).val = 1 := Fin.val_one m
  have h01 : (0 : Fin (m + 2)) < 1 := by
    show (0 : Fin (m + 2)).val < (1 : Fin (m + 2)).val; rw [hv0, hv1]; decide
  let p0 : Pairs (m + 2) := ⟨(0, 1), h01⟩
  unfold parity
  rw [isum_single _ p0]
  · show inv (swap (0 : Fin (m + 2)) 1 0) (swap 0 1 1) = true
    rw [swap_apply_left, swap_apply_right]
    show decide ((0 : Fin (m + 2)) < 1) = true
    simp [h01]
  · intro p hp
    obtain ⟨⟨i, j⟩, hij⟩ := p
    have hij' : i.val < j.val := hij
    show decide (swap (0 : Fin (m + 2)) 1 j < swap 0 1 i) = false
    apply decide_eq_false
    simp only [swap_apply]
    have hne : ¬ (i = 0 ∧ j = 1) := fun ⟨a, b⟩ => hp (Subtype.ext (Prod.ext a b))
    intro hlt
    have hlt' := hlt
    by_cases hi0 : i = 0
    · have hj0 : j ≠ 0 := fun h => by rw [h, hi0] at hij'; omega
      have hj1 : j ≠ 1 := fun h => hne ⟨hi0, h⟩
      simp only [hi0, hj0, hj1, ↓reduceIte] at hlt'
      have : j.val ≠ 1 := fun e => hj1 (Fin.ext (e.trans hv1.symm))
      have : j.val ≠ 0 := fun e => hj0 (Fin.ext (e.trans hv0.symm))
      have : j.val < (1 : Fin (m + 2)).val := hlt'
      omega
    · by_cases hi1 : i = 1
      · have hj0 : j ≠ 0 := fun h => by
          have := congrArg Fin.val h; have := congrArg Fin.val hi1; omega
        have hj1 : j ≠ 1 := fun h => by rw [h, hi1] at hij'; omega
        simp only [hi1, hj0, hj1, ↓reduceIte, show (1 : Fin (m + 2)) ≠ 0 from
          fun e => by have := congrArg Fin.val e; omega] at hlt'
        have : j.val < (0 : Fin (m + 2)).val := hlt'
        omega
      · have hj0 : j ≠ 0 := fun h => by have := congrArg Fin.val h; omega
        have hj1 : j ≠ 1 := fun h => by
          have h' := congrArg Fin.val h
          have : i.val ≠ 0 := fun e => hi0 (Fin.ext (e.trans hv0.symm))
          omega
        simp only [hi0, hi1, hj0, hj1, ↓reduceIte] at hlt'
        have : j.val < i.val := hlt'
        omega

/-- **A transposition is odd.** Every transposition `(a b)` with `a ≠ b` is conjugate to
`(0 1)`, so it has parity `true` (sign `-1`). -/
theorem parity_swap {n : Nat} {a b : Fin n} (hab : a ≠ b) : parity (swap a b) = true := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by
    have := a.isLt; have := b.isLt
    have : a.val ≠ b.val := fun e => hab (Fin.ext e)
    omega⟩
  -- A permutation `π` with `π 0 = a`, `π 1 = b`.
  let ρ1 := swap (0 : Fin (m + 2)) a
  let b1 := ρ1 b
  have hb1 : b1 ≠ 0 := fun h => by
    apply hab; apply ρ1.injective
    show swap 0 a a = swap 0 a b; rw [swap_apply_right]; exact h.symm
  let ρ2 := swap (1 : Fin (m + 2)) b1
  have h10 : (1 : Fin (m + 2)) ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_one, show (0 : Fin (m + 2)).val = 0 from rfl] at this
    exact absurd this (by omega)
  let ρ := ρ2 * ρ1
  have hρa : ρ a = 0 := by
    show swap 1 b1 (swap 0 a a) = 0
    rw [swap_apply_right]; exact swap_apply_of_ne (Ne.symm h10) (Ne.symm hb1)
  have hρb : ρ b = 1 := by show swap 1 b1 b1 = 1; exact swap_apply_right _ _
  have hconj := conj_swap ρ a b
  rw [hρa, hρb] at hconj
  rw [← parity_conj ρ, hconj, parity_swap01]

/-! ## The sign homomorphism -/

/-- The group `{±1}` of signs, as a subset of `ℤ` under multiplication. -/
def Sign : Type := {z : Int // z = 1 ∨ z = -1}

/-- The group structure on `{±1}`. -/
instance : CommGroup Sign where
  mul a b := ⟨a.1 * b.1, by rcases a.2 with h | h <;> rcases b.2 with h' | h' <;> rw [h, h'] <;> decide⟩
  one := ⟨1, Or.inl rfl⟩
  inv a := a
  mul_assoc a b c := Subtype.ext (Int.mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (Int.one_mul a.1)
  inv_mul_cancel a := Subtype.ext (by
    show a.1 * a.1 = 1; rcases a.2 with h | h <;> rw [h] <;> decide)
  mul_comm a b := Subtype.ext (Int.mul_comm a.1 b.1)

/-- The sign `-1`. -/
def Sign.neg : Sign := ⟨-1, Or.inr rfl⟩

/-- `{±1}` has two elements. -/
instance : FiniteType Sign where
  elems := [1, Sign.neg]
  nodup := List.nodup_cons.2 ⟨fun h => absurd (congrArg Subtype.val (List.mem_singleton.1 h))
    (by decide), List.nodup_cons.2 ⟨by simp, List.Pairwise.nil⟩⟩
  complete x := by
    rcases x.2 with h | h
    · exact List.mem_cons.2 (Or.inl (Subtype.ext h))
    · exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 (Subtype.ext h)))

/-- `{±1}` has exactly two elements. -/
theorem card_sign : card Sign = 2 := rfl

/-- **The sign homomorphism** `sgn : Sₙ → {±1}`: `+1` for even, `-1` for odd permutations. -/
def sgn (n : Nat) : Perm (Fin n) →* Sign where
  toFun σ := if parity σ then Sign.neg else 1
  map_mul σ τ := by
    rw [parity_mul]
    cases parity σ <;> cases parity τ <;> apply Subtype.ext <;> decide

/-- `sgn σ = 1` exactly when `σ` is even. -/
theorem sgn_eq_one_iff {n : Nat} (σ : Perm (Fin n)) : sgn n σ = 1 ↔ parity σ = false := by
  show (if parity σ then Sign.neg else 1) = 1 ↔ _
  cases parity σ
  · simp
  · simp only [↓reduceIte, Bool.true_eq_false, iff_false]
    intro h; exact absurd (congrArg Subtype.val h) (by decide)

/-- **The sign of a transposition is `-1`.** -/
theorem sgn_swap {n : Nat} {a b : Fin n} (hab : a ≠ b) : sgn n (swap a b) = Sign.neg := by
  show (if parity (swap a b) then Sign.neg else 1) = Sign.neg
  rw [parity_swap hab]; rfl

/-- **Well-definedness of the parity of a factorisation.** A product of `k` transpositions has
parity `k mod 2`; in particular no permutation is both a product of an even and of an odd
number of transpositions. -/
theorem parity_gprod_transpositions {n : Nat} :
    ∀ L : List (Perm (Fin n)), (∀ t, t ∈ L → IsTransposition t) →
      parity (gprod L) = decide (L.length % 2 = 1)
  | [], _ => parity_one
  | t :: L, h => by
    obtain ⟨a, b, hab, rfl⟩ := h t List.mem_cons_self
    have ih := parity_gprod_transpositions L fun x hx => h x (List.mem_cons_of_mem _ hx)
    show parity (swap a b * gprod L) = _
    rw [parity_mul, parity_swap hab, ih, List.length_cons]
    by_cases hl : L.length % 2 = 1
    · have : ¬ (L.length + 1) % 2 = 1 := by omega
      simp [hl, this, Bool.add_def]
    · have : (L.length + 1) % 2 = 1 := by omega
      simp [hl, this, Bool.add_def]

/-! ## 3-cycles -/

/-- The **3-cycle** `(a b c)`: `a ↦ b ↦ c ↦ a`, defined as `(a b)(b c)`. -/
def c3 {n : Nat} (a b c : Fin n) : Perm (Fin n) := swap a b * swap b c

/-- `σ` is a 3-cycle. -/
def IsC3 {n : Nat} (σ : Perm (Fin n)) : Prop :=
  ∃ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ σ = c3 a b c

/-- The values of a 3-cycle. -/
theorem c3_apply {n : Nat} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (x : Fin n) :
    c3 a b c x = if x = a then b else if x = b then c else if x = c then a else x := by
  show swap a b (swap b c x) = _
  simp only [swap_apply]
  by_cases h1 : x = a
  · subst h1; simp [hab, hac]
  · by_cases h2 : x = b
    · subst h2; simp [Ne.symm hab, Ne.symm hbc, Ne.symm hac]
    · by_cases h3 : x = c
      · subst h3; simp [h1, h2]
      · simp [h1, h2, h3]

/-- **3-cycles are even.** -/
theorem parity_c3 {n : Nat} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) : parity (c3 a b c) = false := by
  unfold c3; rw [parity_mul, parity_swap hab, parity_swap hbc]; rfl

/-- **Conjugating a 3-cycle** relabels it: `π (a b c) π⁻¹ = (πa πb πc)`. -/
theorem conj_c3 {n : Nat} (π : Perm (Fin n)) (a b c : Fin n) :
    π * c3 a b c * π⁻¹ = c3 (π a) (π b) (π c) := by
  unfold c3
  rw [← conj_swap, ← conj_swap]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- A 3-cycle is not the identity. -/
theorem c3_ne_one {n : Nat} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    c3 a b c ≠ 1 := by
  intro h
  have := congrArg (fun σ : Perm (Fin n) => σ a) h
  simp only [c3_apply hab hbc hac, ↓reduceIte, one_apply] at this
  exact hab this.symm

end Foundations.Algebra
