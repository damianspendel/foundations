import Foundations.Sets.Cardinality
import Foundations.Sets.Omega
import Foundations.Sets.Infinite

/-!
# Exercises I: Sets

Problems on Part I of the library (`Foundations/Sets`): Cantor's diagonal argument,
countability, Schröder–Bernstein, the axiom of foundation in ZF and infinite types.

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Every proof between the markers `-- SOLUTION` and `-- END` is replaced by `sorry` in the
student version `Exercises/Problems/Sets.lean` (see `EXERCISES.md`).
-/

namespace Exercises.Sets

open Foundations.Sets Foundations.Sets.ZFSet

/-- **Exercise 1.1 (★) — The grid is countable.** The set of pairs of natural numbers
`ℕ × ℕ` is countable: it injects into `ℕ`.

*Hint:* the library proves that `ℕ × ℕ` and `ℕ` are equinumerous; a bijection is in particular
an injection.

*Uses:* `nat_prod_equinum_nat`, `Countable.of_equinum`, `countable_nat`. -/
theorem countable_nat_prod : Countable (Nat × Nat) := by
  -- SOLUTION
  exact Countable.of_equinum nat_prod_equinum_nat countable_nat
  -- END

/-- **Exercise 1.2 (★★) — The diagonal argument for number sequences.** Given any list
`f 0, f 1, f 2, …` of sequences of natural numbers, some sequence `g` is missing from the
list.

*Hint:* make `g` differ from the `n`-th sequence at the `n`-th place: `g n = f n n + 1`.
Then compare `f n` and `g` at the argument `n`.

*Uses:* nothing beyond `congrFun` and `omega`; this is the argument behind `cantor_bool`. -/
theorem diagonal_nat (f : Nat → (Nat → Nat)) : ∃ g : Nat → Nat, ∀ n, f n ≠ g := by
  -- SOLUTION
  refine ⟨fun n => f n n + 1, fun n h => ?_⟩
  have := congrFun h n
  simp at this
  -- END

/-- **Exercise 1.3 (★★) — Two copies of ℕ are no bigger than one.** The disjoint union
`ℕ ⊕ ℕ` is equinumerous with `ℕ`.

*Hint:* you do not need to write down a bijection. Inject `ℕ ⊕ ℕ` into `ℕ` by sending the
left copy to the even numbers and the right copy to the odd numbers, inject `ℕ` into
`ℕ ⊕ ℕ` by `Sum.inl`, and apply Schröder–Bernstein.

*Uses:* `schroeder_bernstein`. -/
theorem sum_nat_equinum_nat : Equinum (Nat ⊕ Nat) Nat := by
  -- SOLUTION
  let f : Nat ⊕ Nat → Nat := fun s => match s with
    | .inl n => 2 * n
    | .inr n => 2 * n + 1
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp only [f] at h
    · exact congrArg Sum.inl (by omega)
    · omega
    · omega
    · exact congrArg Sum.inr (by omega)
  have hg : Function.Injective (Sum.inl : Nat → Nat ⊕ Nat) := fun a b h => Sum.inl.inj h
  exact schroeder_bernstein hf hg
  -- END

/-- **Exercise 1.4 (★★) — No set is its own successor.** For every ZF set `x`,
`x ∪ {x} ≠ x`.

*Hint:* `x` is a member of its successor, but no set is a member of itself.

*Uses:* `mem_succ_self`, `mem_irrefl`. -/
theorem succ_ne_self (x : ZFSet) : succ x ≠ x := by
  -- SOLUTION
  intro h
  have hx := mem_succ_self x
  rw [h] at hx
  exact mem_irrefl x hx
  -- END

/-- **Exercise 1.5 (★★) — No membership triangles.** There are no ZF sets with
`x ∈ y`, `y ∈ z` and `z ∈ x`.

*Hint:* use ∈-induction on `x` with the statement "for all `y`, `z`, not
(`x ∈ y ∧ y ∈ z ∧ z ∈ x`)". In the induction step, `z ∈ x`, so the hypothesis applies to `z`,
with the roles of the other two sets rotated.

*Uses:* `mem_induction` (a consequence of the axiom of foundation). -/
theorem no_mem_cycle3 (x y z : ZFSet) : ¬ (x ∈ y ∧ y ∈ z ∧ z ∈ x) := by
  -- SOLUTION
  revert y z
  refine mem_induction (fun x => ∀ y z, ¬ (x ∈ y ∧ y ∈ z ∧ z ∈ x)) ?_ x
  intro x ih y z ⟨hxy, hyz, hzx⟩
  exact ih z hzx x y ⟨hzx, hxy, hyz⟩
  -- END

/-- **Exercise 1.6 (★★) — Lists of bits are infinite.** The type `List Bool` is infinite
(it does not inject into any `Fin n`).

*Hint:* a type into which `ℕ` injects is infinite. Send `n` to the list of `n` copies
of `true`; lists with different lengths are different.

*Uses:* `isInfinite_of_nat_le`, `CardLE`, `List.length_replicate`. -/
theorem list_bool_infinite : IsInfinite (List Bool) := by
  -- SOLUTION
  refine isInfinite_of_nat_le ⟨fun n => List.replicate n true, fun a b h => ?_⟩
  have := congrArg List.length h
  simpa using this
  -- END

/-- **Exercise 1.7 (★★★) — Binary sequences cannot be numbered, explicitly.** Every map
`e : (ℕ → Bool) → ℕ` sends two *different* binary sequences to the same number.

This is the uncountability of `ℕ → Bool` in its most concrete form. Prove it from scratch:
do not use `nat_bool_uncountable` or `cantor_bool`.

*Hint:* argue by contradiction, so assume `e` is injective. Build a "decoding"
`d : ℕ → (ℕ → Bool)` that sends `e p` back to `p` (for numbers not of the form `e p`, return
anything; `Classical.choose` helps). Then run the diagonal argument on `d`: the sequence
`fun n => !(d n n)` cannot equal `d (e …)` of itself. Finally use classical logic to turn
"not injective" into the existence of a collision.

*Uses:* `Classical.choose`, `Classical.byContradiction`; compare `exists_surjective_of_injective`. -/
theorem collision_of_nat_bool (e : (Nat → Bool) → Nat) :
    ∃ p q : Nat → Bool, p ≠ q ∧ e p = e q := by
  -- SOLUTION
  apply Classical.byContradiction
  intro hne
  have inj : ∀ p q, e p = e q → p = q := fun p q h =>
    Classical.byContradiction fun hpq => hne ⟨p, q, hpq, h⟩
  classical
  let d : Nat → (Nat → Bool) := fun n =>
    if h : ∃ p, e p = n then Classical.choose h else fun _ => false
  have hd : ∀ p, d (e p) = p := by
    intro p
    have h : ∃ p', e p' = e p := ⟨p, rfl⟩
    simp only [d, h, ↓reduceDIte]
    exact inj _ _ (Classical.choose_spec h)
  let diag : Nat → Bool := fun n => !(d n n)
  have := congrFun (hd diag) (e diag)
  cases h : d (e diag) (e diag) <;> simp [diag, h] at this
  -- END

end Exercises.Sets
