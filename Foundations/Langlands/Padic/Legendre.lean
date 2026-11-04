import Foundations.Langlands.Padic.LegendreSuff

/-!
# Legendre's theorem on ternary quadratic forms

**Legendre's theorem** (A.-M. Legendre, *Recherches d'analyse indéterminée*, 1785; again in the
*Essai sur la théorie des nombres*, 1798). Let `a, b, c` be non-zero, squarefree, pairwise
coprime integers. Then `a x² + b y² + c z² = 0` has a non-trivial integer solution iff

* `a, b, c` are not all of the same sign, and
* `−bc` is a square modulo `|a|`, `−ca` modulo `|b|`, and `−ab` modulo `|c|`.

This is `legendre`. Necessity is `LegendreNec`; sufficiency in the sign pattern `(+, +, −)` is
`LegendreSuff.legendre_core` (pigeonhole on a box of lattice points). Here we reduce every
admissible sign pattern to that one: both the solvability of the conic and Legendre's conditions
are invariant under permuting `(a, b, c)` and under changing all three signs, and a mixed sign
pattern has, up to a global sign, exactly one negative entry.

Legendre's theorem is the arithmetic heart of the **Hasse principle for conics**: the sign
condition is solvability over ℝ and the congruences are solvability over the ℚₚ, `p ∣ abc` (Hasse
1921; Minkowski had earlier treated the analogous question for forms with rational
coefficients via invariants). That reading is made precise in `HasseConic`.

Examples (`legendre_example_five`, `legendre_example_three`): `x² + y² = 5 z²` has the point
`(1, 2, 1)`, while `x² + y² = 3 z²` has none, because `−1` is not a square modulo `3`.
-/

namespace Foundations.Langlands.Padic

namespace Legendre

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Symmetries -/

/-- Solvability of the conic is invariant under the cyclic permutation of the coefficients. -/
theorem conic_rotate {a b c : Int} : ConicSolvableZ a b c ↔ ConicSolvableZ b c a := by
  constructor
  · rintro ⟨x, y, z, hnt, h⟩
    refine ⟨y, z, x, ?_, by omega⟩
    rcases hnt with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro ⟨x, y, z, hnt, h⟩
    refine ⟨z, x, y, ?_, by omega⟩
    rcases hnt with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

/-- Solvability of the conic is invariant under swapping the first two coefficients. -/
theorem conic_swap {a b c : Int} : ConicSolvableZ a b c → ConicSolvableZ b a c := by
  rintro ⟨x, y, z, hnt, h⟩
  refine ⟨y, x, z, ?_, by omega⟩
  rcases hnt with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- Solvability of the conic is invariant under changing all signs. -/
theorem conic_neg {a b c : Int} : ConicSolvableZ (-a) (-b) (-c) → ConicSolvableZ a b c := by
  rintro ⟨x, y, z, hnt, h⟩
  refine ⟨x, y, z, hnt, ?_⟩
  simp only [Int.neg_mul] at h; omega

/-- Legendre's conditions are invariant under the cyclic permutation. -/
theorem LegendreCond.rotate {a b c : Int} (h : LegendreCond a b c) : LegendreCond b c a :=
  ⟨h.2.1, h.2.2, h.1⟩

/-- Legendre's conditions are invariant under swapping the first two coefficients. -/
theorem LegendreCond.swap {a b c : Int} (h : LegendreCond a b c) : LegendreCond b a c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Int.mul_comm]; exact h.2.1
  · rw [Int.mul_comm]; exact h.1
  · rw [Int.mul_comm]; exact h.2.2

/-- Legendre's conditions are invariant under changing all signs. -/
theorem LegendreCond.neg {a b c : Int} (h : LegendreCond a b c) :
    LegendreCond (-a) (-b) (-c) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Int.neg_mul_neg] <;> apply IsSqMod.neg_mod
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- The sign condition is invariant under changing all signs. -/
theorem MixedSigns.neg {a b c : Int} (h : MixedSigns a b c) : MixedSigns (-a) (-b) (-c) :=
  ⟨fun ⟨h1, h2, h3⟩ => h.2 ⟨by omega, by omega, by omega⟩,
    fun ⟨h1, h2, h3⟩ => h.1 ⟨by omega, by omega, by omega⟩⟩

/-! ## Sufficiency -/

/-- Sufficiency for the sign pattern `a, b > 0 > c`, from `legendre_core`. -/
theorem sufficient_pos_pos_neg {a b c : Int} (h : Admissible a b c) (hL : LegendreCond a b c)
    (ha : 0 < a) (hb : 0 < b) (hc : c < 0) : ConicSolvableZ a b c := by
  obtain ⟨A, rfl⟩ : ∃ A : Nat, a = A := ⟨a.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  obtain ⟨B, rfl⟩ : ∃ B : Nat, b = B := ⟨b.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  obtain ⟨K, rfl⟩ : ∃ K : Nat, c = -(K : Int) :=
    ⟨(-c).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
  obtain ⟨h₁, h₂, h₃⟩ := hL
  have sK : Squarefree (K : Int) := by have := h.sc.neg; rwa [Int.neg_neg] at this
  have cBK : Coprime (B : Int) K := by have := h.cbc.neg_right; rwa [Int.neg_neg] at this
  have cKA : Coprime (K : Int) A := by have := h.cca.neg_left; rwa [Int.neg_neg] at this
  refine legendre_core (by omega) (by omega) (by omega) h.sa h.sb sK h.cab cBK cKA ?_ ?_ ?_
  · rwa [Int.mul_neg, Int.neg_neg] at h₁
  · rwa [Int.neg_mul, Int.neg_neg, Int.mul_comm] at h₂
  · have := h₃.neg_mod; rwa [Int.neg_neg] at this

/-- Sufficiency when exactly one coefficient is negative. -/
theorem sufficient_one_neg {a b c : Int} (h : Admissible a b c) (hL : LegendreCond a b c)
    (hs : (0 < a ∧ 0 < b ∧ c < 0) ∨ (0 < a ∧ b < 0 ∧ 0 < c) ∨ (a < 0 ∧ 0 < b ∧ 0 < c)) :
    ConicSolvableZ a b c := by
  rcases hs with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · exact sufficient_pos_pos_neg h hL ha hb hc
  · exact conic_rotate.2 (conic_rotate.2
      (sufficient_pos_pos_neg h.rotate.rotate hL.rotate.rotate hc ha hb))
  · exact conic_rotate.2 (sufficient_pos_pos_neg h.rotate hL.rotate hb hc ha)

/-- **Legendre's theorem, sufficiency.** For non-zero, squarefree, pairwise coprime `a, b, c`
not all of the same sign, if `−bc`, `−ca`, `−ab` are squares modulo `|a|`, `|b|`, `|c|`, then
`a x² + b y² + c z² = 0` has a non-trivial integer solution. -/
theorem legendre_sufficient {a b c : Int} (h : Admissible a b c) (hs : MixedSigns a b c)
    (hL : LegendreCond a b c) : ConicSolvableZ a b c := by
  have ha := h.ha; have hb := h.hb; have hc := h.hc
  by_cases h1 : (0 < a ∧ 0 < b ∧ c < 0) ∨ (0 < a ∧ b < 0 ∧ 0 < c) ∨ (a < 0 ∧ 0 < b ∧ 0 < c)
  · exact sufficient_one_neg h hL h1
  · -- exactly two coefficients are negative: change all signs
    apply conic_neg
    apply sufficient_one_neg h.neg hL.neg
    have := hs.1; have := hs.2
    omega

/-- **Legendre's theorem (1785).** Let `a, b, c` be non-zero, squarefree, pairwise coprime
integers. The conic `a x² + b y² + c z² = 0` has a non-trivial integer point iff `a, b, c` are
not all of the same sign and `−bc`, `−ca`, `−ab` are squares modulo `|a|`, `|b|`, `|c|`. -/
theorem legendre {a b c : Int} (h : Admissible a b c) :
    ConicSolvableZ a b c ↔ MixedSigns a b c ∧ LegendreCond a b c :=
  ⟨fun hs => ⟨not_same_sign_of_solution hs, legendre_necessary h hs⟩,
    fun ⟨hs, hL⟩ => legendre_sufficient h hs hL⟩

/-! ## Examples -/

/-- Small integers not divisible by `4` are squarefree: if `0 < |n| < 9` and `4 ∤ n`, then the
only candidate prime square, `4`, does not divide `n`. -/
theorem squarefree_small {n : Int} (h0 : n ≠ 0) (h9 : n.natAbs < 9) (h4 : ¬ (4 : Int) ∣ n) :
    Squarefree n := by
  intro p hp hd
  have hp2 := hp.1
  have hd' : p * p ∣ n.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hd
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
  have hle := Nat.le_of_dvd (Int.natAbs_pos.2 h0) hd'
  have hp3 : p = 2 := by
    apply Classical.byContradiction; intro hne
    have := Nat.mul_le_mul (show 3 ≤ p by omega) (show 3 ≤ p by omega); omega
  subst hp3
  exact h4 hd

/-- `1` is coprime to everything. -/
theorem coprime_one_left (n : Int) : Coprime 1 n := Nat.coprime_one_left _

/-- Everything is coprime to `1`. -/
theorem coprime_one_right (n : Int) : Coprime n 1 := Nat.coprime_one_right _

/-- The coefficients `(1, 1, −c)` are admissible for a squarefree `c > 0`. -/
theorem admissible_one_one {c : Int} (hc : 0 < c) (sc : Squarefree c) :
    Admissible 1 1 (-c) :=
  ⟨by decide, by decide, by omega, squarefree_small (by decide) (by decide) (by decide),
    squarefree_small (by decide) (by decide) (by decide), sc.neg, coprime_one_left _,
    coprime_one_left _, coprime_one_right _⟩

/-- `−1` is not a square modulo `3`. -/
theorem not_isSqMod_neg_one_three : ¬ IsSqMod (-1) 3 := by
  rintro ⟨t, ht⟩
  have h := Int.emod_emod_of_dvd (t * t - -1) (Int.dvd_refl 3)
  rw [Int.emod_eq_zero_of_dvd ht] at h
  have h' : (t * t + 1) % 3 = 0 := by rw [show t * t + 1 = t * t - -1 by omega]; omega
  rw [Int.add_emod, Int.mul_emod] at h'
  have : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases this with e | e | e <;> rw [e] at h' <;> simp at h'

/-- **Example: `x² + y² = 5 z²` has a non-trivial integer point.** For example `(1, 2, 1)`; consistently
with Legendre's theorem, `−1 ≡ 2² (mod 5)`. -/
theorem legendre_example_five : ConicSolvableZ 1 1 (-5) ∧ LegendreCond 1 1 (-5) :=
  ⟨⟨1, 2, 1, Or.inl (by decide), by decide⟩,
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, ⟨-1, by decide⟩⟩⟩⟩

/-- **Example: `x² + y² = 3 z²` has no non-trivial integer point.** Legendre's condition at `3`
asks for `−1` to be a square modulo `3`, which it is not. -/
theorem legendre_example_three : ¬ ConicSolvableZ 1 1 (-3) := fun hs =>
  not_isSqMod_neg_one_three (by
    have := (legendre_necessary (admissible_one_one (by decide)
      (squarefree_small (by decide) (by decide) (by decide))) hs).2.2
    have := this.neg_mod
    simpa using this)

end Legendre

end Foundations.Langlands.Padic
