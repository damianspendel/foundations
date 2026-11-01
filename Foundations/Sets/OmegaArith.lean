import Foundations.Sets.Recursion

/-!
# Arithmetic on ω

With the recursion theorem in hand, arithmetic can be *defined* inside set
theory, exactly as Dedekind and Peano taught: addition is iterated successor,
and multiplication is iterated addition.

    m + 0 = m,      m + succ n = succ (m + n);
    m · 0 = 0,      m · succ n = m · n + m.

For each fixed `m ∈ ω`, the recursion theorem supplies a genuine set-theoretic
function `ω → ω` (a set of pairs) satisfying the first pair of equations, and
`m +ω n` is its value at `n`; likewise for `·`.

The **arithmetic bridge** then shows that these set-theoretically defined
operations agree with Lean's built-in arithmetic under the correspondence
`vn : Nat → ω`: `vn (m + n) = vn m +ω vn n` and `vn (m * n) = vn m *ω vn n`.
This closes the loop begun in `Omega`: the natural numbers *with their
arithmetic* are faithfully represented by sets, and laws such as commutativity
can be transported along the bridge.
-/

namespace Foundations.Sets

namespace ZFSet

/-! ## Addition -/

/-- The successor operation maps `ω` into `ω`. -/
theorem succ_maps_omega : ∀ x ∈ ω, succ x ∈ ω := fun _ hx => succ_mem_omega hx

/-- For fixed `m`, the "add `m`" function `ω → ω`, given by the recursion theorem
with initial value `m` and step `succ`. -/
noncomputable def addFun (m : ZFSet) : ZFSet := recFun ω m succ

/-- **Addition on ω**: `m +ω n` is the value at `n` of the add-`m` function. -/
noncomputable def addω (m n : ZFSet) : ZFSet := app (addFun m) n

@[inherit_doc] infixl:65 " +ω " => addω

/-- The add-`m` function is a set-theoretic function from `ω` to `ω`. -/
theorem addFun_isFunction {m : ZFSet} (hm : m ∈ ω) : IsFunction (addFun m) ω ω :=
  recFun_isFunction hm succ_maps_omega

/-- `m +ω ∅ = m`. -/
theorem addω_zero {m : ZFSet} (hm : m ∈ ω) : m +ω ∅ = m := recFun_zero hm succ_maps_omega

/-- `m +ω succ n = succ (m +ω n)`. -/
theorem addω_succ {m n : ZFSet} (hm : m ∈ ω) (hn : n ∈ ω) : m +ω succ n = succ (m +ω n) :=
  recFun_succ hm succ_maps_omega hn

/-- **Addition bridge.** `vn (m + n) = vn m +ω vn n`. -/
theorem vn_add (m n : Nat) : vn (m + n) = vn m +ω vn n := by
  induction n with
  | zero => exact (addω_zero (vn_mem_omega m)).symm
  | succ n ih =>
    rw [← Nat.add_assoc, vn_succ, vn_succ, addω_succ (vn_mem_omega m) (vn_mem_omega n), ih]

/-- `ω` is closed under `+ω`. -/
theorem addω_mem_omega {m n : ZFSet} (hm : m ∈ ω) (hn : n ∈ ω) : m +ω n ∈ ω := by
  obtain ⟨i, rfl⟩ := mem_omega.1 hm
  obtain ⟨j, rfl⟩ := mem_omega.1 hn
  rw [← vn_add]
  exact vn_mem_omega _

/-! ## Multiplication -/

/-- Adding `m` maps `ω` into `ω`. -/
theorem addω_maps_omega {m : ZFSet} (hm : m ∈ ω) : ∀ x ∈ ω, x +ω m ∈ ω :=
  fun _ hx => addω_mem_omega hx hm

/-- For fixed `m`, the "multiply by `m`" function `ω → ω`, given by the recursion
theorem with initial value `∅` and step `x ↦ x +ω m`. -/
noncomputable def mulFun (m : ZFSet) : ZFSet := recFun ω ∅ (fun x => x +ω m)

/-- **Multiplication on ω**: `m *ω n` is the value at `n` of the multiply-by-`m` function. -/
noncomputable def mulω (m n : ZFSet) : ZFSet := app (mulFun m) n

@[inherit_doc] infixl:70 " *ω " => mulω

/-- The multiply-by-`m` function is a set-theoretic function from `ω` to `ω`. -/
theorem mulFun_isFunction {m : ZFSet} (hm : m ∈ ω) : IsFunction (mulFun m) ω ω :=
  recFun_isFunction empty_mem_omega (addω_maps_omega hm)

/-- `m *ω ∅ = ∅`. -/
theorem mulω_zero {m : ZFSet} (hm : m ∈ ω) : m *ω ∅ = ∅ :=
  recFun_zero empty_mem_omega (addω_maps_omega hm)

/-- `m *ω succ n = (m *ω n) +ω m`. -/
theorem mulω_succ {m n : ZFSet} (hm : m ∈ ω) (hn : n ∈ ω) : m *ω succ n = m *ω n +ω m :=
  recFun_succ empty_mem_omega (addω_maps_omega hm) hn

/-- **Multiplication bridge.** `vn (m * n) = vn m *ω vn n`. -/
theorem vn_mul (m n : Nat) : vn (m * n) = vn m *ω vn n := by
  induction n with
  | zero => exact (mulω_zero (vn_mem_omega m)).symm
  | succ n ih =>
    rw [Nat.mul_succ, vn_succ, mulω_succ (vn_mem_omega m) (vn_mem_omega n), ← ih, vn_add]

/-- `ω` is closed under `*ω`. -/
theorem mulω_mem_omega {m n : ZFSet} (hm : m ∈ ω) (hn : n ∈ ω) : m *ω n ∈ ω := by
  obtain ⟨i, rfl⟩ := mem_omega.1 hm
  obtain ⟨j, rfl⟩ := mem_omega.1 hn
  rw [← vn_mul]
  exact vn_mem_omega _

/-- **Arithmetic bridge.** Under `vn : Nat → ω`, zero, successor, addition and
multiplication of Lean's natural numbers correspond exactly to `∅`, `succ`, `+ω`
and `*ω`, which were defined purely set-theoretically by the recursion theorem. -/
theorem arith_bridge :
    vn 0 = ∅ ∧ (∀ n, vn (n + 1) = succ (vn n)) ∧
      (∀ m n, vn (m + n) = vn m +ω vn n) ∧ (∀ m n, vn (m * n) = vn m *ω vn n) :=
  ⟨rfl, fun _ => rfl, vn_add, vn_mul⟩

/-! ## Laws transported along the bridge -/

/-- Addition on ω is commutative (transported from `Nat`). -/
theorem addω_comm {m n : ZFSet} (hm : m ∈ ω) (hn : n ∈ ω) : m +ω n = n +ω m := by
  obtain ⟨i, rfl⟩ := mem_omega.1 hm
  obtain ⟨j, rfl⟩ := mem_omega.1 hn
  rw [← vn_add, ← vn_add, Nat.add_comm]

/-- Addition on ω is associative. -/
theorem addω_assoc {k m n : ZFSet} (hk : k ∈ ω) (hm : m ∈ ω) (hn : n ∈ ω) :
    k +ω m +ω n = k +ω (m +ω n) := by
  obtain ⟨i, rfl⟩ := mem_omega.1 hk
  obtain ⟨j, rfl⟩ := mem_omega.1 hm
  obtain ⟨l, rfl⟩ := mem_omega.1 hn
  rw [← vn_add, ← vn_add, ← vn_add, ← vn_add, Nat.add_assoc]

/-- Multiplication on ω is commutative. -/
theorem mulω_comm {m n : ZFSet} (hm : m ∈ ω) (hn : n ∈ ω) : m *ω n = n *ω m := by
  obtain ⟨i, rfl⟩ := mem_omega.1 hm
  obtain ⟨j, rfl⟩ := mem_omega.1 hn
  rw [← vn_mul, ← vn_mul, Nat.mul_comm]

/-- Multiplication distributes over addition on ω. -/
theorem mulω_addω {k m n : ZFSet} (hk : k ∈ ω) (hm : m ∈ ω) (hn : n ∈ ω) :
    k *ω (m +ω n) = k *ω m +ω k *ω n := by
  obtain ⟨i, rfl⟩ := mem_omega.1 hk
  obtain ⟨j, rfl⟩ := mem_omega.1 hm
  obtain ⟨l, rfl⟩ := mem_omega.1 hn
  rw [← vn_add, ← vn_mul, ← vn_mul, ← vn_mul, ← vn_add, Nat.mul_add]

end ZFSet

end Foundations.Sets
