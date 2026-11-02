import Foundations.Combinatorics.Ramsey
import Foundations.Combinatorics.Hall

/-!
# Exercises XIII: Combinatorics

Problems on the combinatorics part (`Foundations/Combinatorics`): the finite and infinite
pigeonhole principles (`Pigeonhole`), the finite and infinite Ramsey theorems (`Ramsey`) and
Hall's marriage theorem (`Hall`).

*Conventions.* Finite sets are encoded concretely: a family of `m` points is a map
`f : Nat → Nat` looked at below `m`; a 2-colouring of pairs is `c : Nat → Nat → Bool`;
`InfOften P` means `∀ N, ∃ i ≥ N, P i`. In `Hall`, a family of sets is a relation
`A : Nat → Nat → Prop` (`A i x` means `x ∈ Aᵢ`), and `cnt P n` counts the `x < n` with `P x`;
it unfolds by `simp only [cnt]` or `rfl`-style computation on small numerals.

Grading: ★ a one-liner using a library lemma, ★★ a short proof, ★★★ a mini-project.
Proofs between `-- SOLUTION` and `-- END` become `sorry` in
`Exercises/Problems/Combinatorics.lean`.
-/

namespace Exercises.Combinatorics

open Foundations.Combinatorics

/-! ## Pigeonhole -/

/-- **Exercise 13.1 (★) — Five numbers, four remainders.** Among any five natural numbers
`a 0, …, a 4`, two have the same remainder modulo 4.

*Hint:* the holes are the remainders `0, 1, 2, 3`.

*Uses:* `pigeonhole`, `Nat.mod_lt`. -/
theorem two_same_mod_four (a : Nat → Nat) : ∃ i j, i < j ∧ j < 5 ∧ a i % 4 = a j % 4 := by
  -- SOLUTION
  exact pigeonhole 4 5 (fun i => a i % 4) (fun i _ => Nat.mod_lt _ (by decide)) (by decide)
  -- END

/-- **Exercise 13.2 (★★) — An infinite constant subsequence.** Every sequence of booleans has a
strictly increasing subsequence `f ∘ g` that is constant.

*Hint:* one of the two values is taken infinitely often; an infinitely-often set can be
enumerated in increasing order.

*Uses:* `infinite_pigeonhole_bool`, `InfOften.enum`. -/
theorem bool_constant_subsequence (f : Nat → Bool) :
    ∃ (b : Bool) (g : Nat → Nat), (∀ i j, i < j → g i < g j) ∧ ∀ i, f (g i) = b := by
  -- SOLUTION
  obtain ⟨b, hb⟩ := infinite_pigeonhole_bool f
  obtain ⟨g, hg, hmono⟩ := hb.enum
  exact ⟨b, g, hmono, hg⟩
  -- END

/-! ## Ramsey -/

/-- **Exercise 13.3 (★★) — Exactly when the party is big enough.** `N → (3, 3)` holds exactly
for `N ≥ 6`.

*Hint:* one direction is monotonicity from `R(3,3) ≤ 6`; for the other, if `N ≤ 5` the library
says `N → (3, 3)` fails.

*Uses:* `ramsey_three_three`, `IsRamsey.mono`. -/
theorem isRamsey_three_three_iff (N : Nat) : IsRamsey 3 3 N ↔ 6 ≤ N := by
  -- SOLUTION
  constructor
  · intro h
    refine Classical.byContradiction fun hN => ?_
    exact ramsey_three_three.2 N (by omega) h
  · intro hN
    exact ramsey_three_three.1.mono hN
  -- END

/-- **Exercise 13.4 (★★) — A monochromatic triangle in ℕ.** For every 2-colouring `c` of
pairs of natural numbers there are `x < y < z` such that the three pairs `(x, y)`, `(y, z)`,
`(x, z)` all have the same colour.

*Hint:* the infinite Ramsey theorem gives an infinite monochromatic sequence; take its first
three terms.

*Uses:* `infinite_ramsey`. -/
theorem mono_triangle (c : Nat → Nat → Bool) :
    ∃ x y z, x < y ∧ y < z ∧ c x y = c y z ∧ c x y = c x z := by
  -- SOLUTION
  obtain ⟨b, f, hmono, hcol⟩ := infinite_ramsey c
  refine ⟨f 0, f 1, f 2, hmono 0 1 (by decide), hmono 1 2 (by decide), ?_, ?_⟩
  · rw [hcol 0 1 (by decide), hcol 1 2 (by decide)]
  · rw [hcol 0 1 (by decide), hcol 0 2 (by decide)]
  -- END

/-! ## Hall -/

/-- **Exercise 13.5 (★★★) — Three sets inside a pair have no representatives.** If three sets
`A₀, A₁, A₂` are all contained in `{0, 1}`, there is no system of distinct representatives
taking values below `M`, whatever `M` is.

*Hint:* Hall's condition is necessary. Apply it to the whole family `I = (fun _ => True)`:
it has 3 members, `cnt (fun _ => True) 3 = 3` (unfold `cnt`). Its union lies in `{x | x < 2}`,
so by monotonicity of counting its count below `M` is at most the number of `x < M` with
`x < 2`, which is at most 2 (`cnt_mono` once more into `fun x => x = 0 ∨ x = 1`, or a small
induction on `M`).

*Uses:* `hall_necessary`, `cnt`, `cnt_mono`, `union`. -/
theorem no_sdr_three_in_two (M : Nat) (A : Nat → Nat → Prop) (hA : ∀ i x, A i x → x < 2) :
    ¬ ∃ f : Nat → Nat, (∀ i, i < 3 → f i < M ∧ A i (f i)) ∧
      ∀ i j, i < 3 → j < 3 → i ≠ j → f i ≠ f j := by
  -- SOLUTION
  rintro ⟨f, hf, hinj⟩
  have h := hall_necessary 3 M A f hf hinj (fun _ => True)
  have h3 : cnt (fun _ => True) 3 = 3 := by simp [cnt]
  have hle : ∀ m, cnt (fun x => x < 2) m ≤ 2 := by
    intro m
    induction m with
    | zero => simp [cnt]
    | succ m ih =>
      by_cases hm : m < 2
      · have : cnt (fun x => x < 2) m = m := by
          rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> simp [cnt]
        simp only [cnt, hm, ite_true]; omega
      · simp only [cnt, hm, ite_false]; omega
  have hu : cnt (union 3 A fun _ => True) M ≤ cnt (fun x => x < 2) M :=
    cnt_mono M fun x _ ⟨i, _, _, hx⟩ => hA i x hx
  have := hle M
  omega
  -- END

end Exercises.Combinatorics
