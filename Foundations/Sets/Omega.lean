import Foundations.Sets.Paradoxes

/-!
# The von Neumann natural numbers and the set ω

What *is* the number 3? Frege answered: the class of all three-membered classes —
an answer Russell's paradox made untenable. Von Neumann (1923) proposed instead
to let each number be one particular, canonical set: the set of all smaller
numbers.

    0 = ∅,   1 = {0},   2 = {0, 1},   3 = {0, 1, 2},   …,   n + 1 = n ∪ {n}.

These sets `vn n` were defined in `ZFSet`, together with the set `ω` of all of
them, whose existence is the axiom of infinity. Here we show that `ω` behaves
exactly as the natural numbers should, by proving the **Peano axioms** for it:
zero is a number, every number has a successor, successors are injective, zero
is no successor, and induction holds.

Finally, the **bridge theorem** shows that `vn` is a one-to-one correspondence
between Lean's built-in natural numbers and the members of `ω`, sending zero to
`∅` and `n + 1` to the successor set; under it, `<` becomes `∈` and `≤` becomes
`⊆`. This is what licenses later parts of the project to use Lean's `Nat` as a
convenient stand-in for the set-theoretic numbers.
-/

namespace Foundations.Sets

namespace ZFSet

/-! ## Members of a von Neumann natural -/

/-- **Each number is the set of smaller numbers.** The members of `vn n` are
exactly the `vn m` with `m < n`. -/
theorem mem_vn {n : Nat} {x : ZFSet} : x ∈ vn n ↔ ∃ m, m < n ∧ x = vn m := by
  induction n with
  | zero =>
    simp only [vn_zero]
    exact ⟨fun h => absurd h (not_mem_empty x), fun ⟨m, hm, _⟩ => absurd hm (Nat.not_lt_zero m)⟩
  | succ n ih =>
    rw [vn_succ, mem_succ, ih]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      by_cases h : m = n
      · exact Or.inl (h ▸ rfl)
      · exact Or.inr ⟨m, by omega, rfl⟩

/-- If `m < n` then `vn m ∈ vn n`. -/
theorem vn_mem_vn_of_lt {m n : Nat} (h : m < n) : vn m ∈ vn n := mem_vn.2 ⟨m, h, rfl⟩

/-- **`vn` is injective**: distinct natural numbers give distinct sets. -/
theorem vn_injective : Function.Injective vn := by
  intro m n h
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · have := vn_mem_vn_of_lt hlt
    rw [← h] at this
    exact absurd this (mem_irrefl _)
  · exact heq
  · have := vn_mem_vn_of_lt hgt
    rw [h] at this
    exact absurd this (mem_irrefl _)

/-- **Order is membership**: `vn m ∈ vn n ↔ m < n`. -/
theorem vn_mem_vn_iff {m n : Nat} : vn m ∈ vn n ↔ m < n := by
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := mem_vn.1 h
    rw [vn_injective he]
    exact hk
  · exact vn_mem_vn_of_lt

/-- **Non-strict order is inclusion**: `vn m ⊆ vn n ↔ m ≤ n`. -/
theorem vn_subset_vn_iff {m n : Nat} : vn m ⊆ vn n ↔ m ≤ n := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hmn
    have : vn n ∈ vn n := h (vn_mem_vn_of_lt (by omega))
    exact mem_irrefl _ this
  · intro hmn z hz
    obtain ⟨k, hk, rfl⟩ := mem_vn.1 hz
    exact vn_mem_vn_of_lt (by omega)

/-! ## The Peano axioms for ω -/

/-- `vn n` is a member of `ω`. -/
theorem vn_mem_omega (n : Nat) : vn n ∈ ω := mem_omega.2 ⟨n, rfl⟩

/-- **Peano 1.** Zero (the empty set) is a natural number. -/
theorem empty_mem_omega : (∅ : ZFSet) ∈ ω := vn_mem_omega 0

/-- **Peano 2.** The successor of a natural number is a natural number. -/
theorem succ_mem_omega {x : ZFSet} (hx : x ∈ ω) : succ x ∈ ω := by
  obtain ⟨n, rfl⟩ := mem_omega.1 hx
  exact vn_mem_omega (n + 1)

/-- **Peano 3.** Zero is not a successor: `succ x ≠ ∅` for every set `x`. -/
theorem succ_ne_empty (x : ZFSet) : succ x ≠ ∅ := fun h =>
  not_mem_empty x (h ▸ mem_succ_self x)

/-- **The successor operation is injective** on all sets (a consequence of
foundation: it rules out `x ∈ y ∈ x`). -/
theorem succ_injective : Function.Injective succ := by
  intro x y h
  have hx : x ∈ succ y := h ▸ mem_succ_self x
  have hy : y ∈ succ x := h ▸ mem_succ_self y
  rcases mem_succ.1 hx with hxy | hxy
  · exact hxy
  · rcases mem_succ.1 hy with hyx | hyx
    · exact hyx.symm
    · exact absurd hyx (mem_asymm hxy)

/-- **Peano 4.** Successor is injective on `ω`. -/
theorem succ_inj_omega {x y : ZFSet} (_ : x ∈ ω) (_ : y ∈ ω) (h : succ x = succ y) : x = y :=
  succ_injective h

/-- **Peano 5 (induction, property form).** A property that holds of `∅` and is
preserved by successor holds of every member of `ω`. -/
theorem omega_induction (P : ZFSet → Prop) (h0 : P ∅) (hs : ∀ x ∈ ω, P x → P (succ x)) :
    ∀ x ∈ ω, P x := by
  intro x hx
  obtain ⟨n, rfl⟩ := mem_omega.1 hx
  induction n with
  | zero => exact h0
  | succ n ih => exact hs _ (vn_mem_omega n) (ih (vn_mem_omega n))

/-- **Peano 5 (induction, set form).** A subset of `ω` that contains `∅` and is
closed under successor is all of `ω`. -/
theorem omega_induction_set (S : ZFSet) (hS : S ⊆ ω) (h0 : ∅ ∈ S)
    (hs : ∀ x ∈ S, succ x ∈ S) : S = ω :=
  subset_antisymm hS fun x hx => omega_induction (· ∈ S) h0 (fun x _ h => hs x h) x hx

/-- **ω is the least inductive set.** Every set containing `∅` and closed under
successor includes `ω`. -/
theorem omega_subset_of_inductive (S : ZFSet) (h0 : ∅ ∈ S) (hs : ∀ x ∈ S, succ x ∈ S) :
    ω ⊆ S :=
  fun x hx => omega_induction (· ∈ S) h0 (fun x _ h => hs x h) x hx

/-! ## The bridge between `Nat` and ω -/

/-- **Bridge theorem (ω ≅ ℕ).** The map `vn : Nat → ZFSet` sends `0` to `∅`
and `n + 1` to `succ (vn n)`, is injective, and its values are exactly the
members of `ω`; moreover it turns `<` into `∈` and `≤` into `⊆`. Hence `ω`
with `∅` and `succ` is an exact copy of Lean's natural numbers. -/
theorem omega_bridge :
    vn 0 = ∅ ∧ (∀ n, vn (n + 1) = succ (vn n)) ∧ Function.Injective vn ∧
      (∀ x, x ∈ ω ↔ ∃ n, vn n = x) ∧
      (∀ m n, m < n ↔ vn m ∈ vn n) ∧ (∀ m n, m ≤ n ↔ vn m ⊆ vn n) :=
  ⟨rfl, fun _ => rfl, vn_injective,
   fun _ => ⟨fun h => let ⟨n, hn⟩ := mem_omega.1 h; ⟨n, hn.symm⟩,
             fun ⟨n, hn⟩ => mem_omega.2 ⟨n, hn.symm⟩⟩,
   fun _ _ => vn_mem_vn_iff.symm, fun _ _ => vn_subset_vn_iff.symm⟩

/-- The von Neumann natural `vn n`, viewed as an element of the subtype of members of `ω`. -/
noncomputable def toOmega (n : Nat) : {x : ZFSet // x ∈ ω} := ⟨vn n, vn_mem_omega n⟩

/-- **`Nat` is in bijection with ω.** `toOmega` is a one-to-one correspondence
between Lean's natural numbers and the members of `ω`. -/
theorem toOmega_bijective : Bijective toOmega := by
  refine ⟨fun m n h => vn_injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => ?_⟩
  obtain ⟨n, rfl⟩ := mem_omega.1 hx
  exact ⟨n, rfl⟩

end ZFSet

end Foundations.Sets
