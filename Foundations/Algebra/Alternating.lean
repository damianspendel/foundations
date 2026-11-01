import Foundations.Algebra.Symmetric

/-!
# The alternating group

The even permutations — those with sign `+1` — form the **alternating group** `Aₙ`, so called
because the polynomials it leaves unchanged are the *alternating* functions such as Vandermonde's
`∏_{i<j} (xⱼ - xᵢ)`, which change sign under any transposition. As the kernel of the sign
homomorphism, `Aₙ` is a normal subgroup, and for `n ≥ 2` it has index `2`: by the first
isomorphism theorem `Sₙ ⧸ Aₙ ≅ {±1}`.

Our main result is a set of generators: **the 3-cycles generate `Aₙ`.** An even permutation is
a product of an even number of transpositions, and any two transpositions multiply to a product
of at most two 3-cycles: `(a b)(a b) = 1`, `(a b)(b c) = (a b c)`, and for disjoint
transpositions `(a b)(c d) = (a b c)(b c d)`. This is the starting point of the proof, in the
next file, that `A₅` is simple.
-/

namespace Foundations.Algebra

open FiniteType Group Perm QuotientGroup

/-- **The alternating group** `Aₙ`: the even permutations, i.e. the kernel of `sgn`. -/
def alternating (n : Nat) : Subgroup (Perm (Fin n)) := (sgn n).ker

/-- Membership in `Aₙ` means being even. -/
theorem mem_alternating {n : Nat} {σ : Perm (Fin n)} : σ ∈ alternating n ↔ parity σ = false :=
  sgn_eq_one_iff σ

/-- **`Aₙ` is a normal subgroup of `Sₙ`** (being a kernel). -/
instance alternating_normal (n : Nat) : (alternating n).Normal := Hom.ker_normal (sgn n)

/-- For `n ≥ 2` the sign homomorphism is onto `{±1}`. -/
theorem sgn_surjective (m : Nat) : ∀ y, ∃ σ : Perm (Fin (m + 2)), sgn (m + 2) σ = y := by
  intro y
  rcases y.2 with h | h
  · exact ⟨1, Subtype.ext (by rw [(sgn _).map_one]; exact h.symm)⟩
  · refine ⟨swap 0 1, ?_⟩
    have h01 : (0 : Fin (m + 2)) ≠ 1 := fun e => by
      have := congrArg Fin.val e
      rw [Fin.val_one, show (0 : Fin (m + 2)).val = 0 from rfl] at this; exact absurd this (by omega)
    rw [sgn_swap h01]; exact Subtype.ext h.symm

/-- **`Aₙ` has index 2** (for `n ≥ 2`): `Sₙ ⧸ Aₙ ≃* {±1}`, a group with two elements. -/
noncomputable def alternatingQuotient (m : Nat) : Perm (Fin (m + 2)) ⧸ alternating (m + 2) ≃* Sign :=
  firstIsoTheorem' (sgn (m + 2)) (sgn_surjective m)

/-- **The two cosets of `Aₙ`.** Every permutation is either even or a transposition times an
even permutation. -/
theorem alternating_cosets (m : Nat) (σ : Perm (Fin (m + 2))) :
    σ ∈ alternating (m + 2) ∨ swap 0 1 * σ ∈ alternating (m + 2) := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_one, show (0 : Fin (m + 2)).val = 0 from rfl] at this; exact absurd this (by omega)
  rw [mem_alternating, mem_alternating, parity_mul, parity_swap h01]
  cases parity σ <;> simp [Bool.add_def]

/-! ## 3-cycles generate -/

/-- 3-cycles are even. -/
theorem IsC3.mem_alternating {n : Nat} {σ : Perm (Fin n)} (h : IsC3 σ) : σ ∈ alternating n := by
  obtain ⟨a, b, c, hab, hbc, _, rfl⟩ := h
  exact Foundations.Algebra.mem_alternating.2 (parity_c3 hab hbc)

/-- **Two transpositions make at most two 3-cycles.** -/
theorem swap_mul_swap_c3 {n : Nat} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ L : List (Perm (Fin n)), (∀ t, t ∈ L → IsC3 t) ∧ gprod L = swap a b * swap c d := by
  by_cases hbc : b = c
  · subst hbc
    by_cases had : a = d
    · subst had; exact ⟨[], by simp, by rw [swap_comm b a, swap_mul_self]; rfl⟩
    · exact ⟨[c3 a b d], by simpa using ⟨a, b, d, hab, hcd, had, rfl⟩, Group.mul_one _⟩
  · by_cases hac : a = c
    · subst hac
      by_cases hbd : b = d
      · subst hbd; exact ⟨[], by simp, by rw [swap_mul_self]; rfl⟩
      · refine ⟨[c3 b a d], by simpa using ⟨b, a, d, Ne.symm hab, hcd, hbd, rfl⟩, ?_⟩
        show c3 b a d * 1 = _; rw [Group.mul_one, swap_comm a b]; rfl
    · by_cases hbd : b = d
      · subst hbd
        refine ⟨[c3 a b c], by simpa using ⟨a, b, c, hab, hbc, hac, rfl⟩, ?_⟩
        show c3 a b c * 1 = _; rw [Group.mul_one, swap_comm c b]; rfl
      · by_cases had : a = d
        · subst had
          refine ⟨[c3 b a c], by simpa using ⟨b, a, c, Ne.symm hab, Ne.symm hcd, hbc, rfl⟩, ?_⟩
          show c3 b a c * 1 = _; rw [Group.mul_one, swap_comm a b, swap_comm c a]; rfl
        · refine ⟨[c3 a b c, c3 b c d], ?_, ?_⟩
          · intro t ht
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl
            · exact ⟨a, b, c, hab, hbc, hac, rfl⟩
            · exact ⟨b, c, d, hbc, hcd, hbd, rfl⟩
          · show c3 a b c * (c3 b c d * 1) = _
            unfold c3
            rw [Group.mul_one, Group.mul_assoc, ← Group.mul_assoc (swap b c), swap_mul_self,
              Group.one_mul]

/-- A product of an even number of transpositions is a product of 3-cycles. -/
theorem even_transpositions_c3 {n : Nat} :
    ∀ (k : Nat) (L : List (Perm (Fin n))), L.length = 2 * k → (∀ t, t ∈ L → IsTransposition t) →
      ∃ M : List (Perm (Fin n)), (∀ t, t ∈ M → IsC3 t) ∧ gprod M = gprod L := by
  intro k
  induction k with
  | zero => intro L hL _; exact ⟨[], by simp, by rw [List.eq_nil_of_length_eq_zero hL]⟩
  | succ k ih =>
    intro L hL hT
    match L, hL with
    | t1 :: t2 :: L', hL =>
      obtain ⟨a, b, hab, rfl⟩ := hT t1 List.mem_cons_self
      obtain ⟨c, d, hcd, rfl⟩ := hT t2 (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨M1, hM1, h1⟩ := swap_mul_swap_c3 hab hcd
      obtain ⟨M2, hM2, h2⟩ := ih L' (by simp at hL; omega)
        (fun t ht => hT t (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))
      refine ⟨M1 ++ M2, fun t ht => ?_, ?_⟩
      · rcases List.mem_append.1 ht with h | h
        · exact hM1 t h
        · exact hM2 t h
      · rw [gprod_append, h1, h2]
        show swap a b * swap c d * gprod L' = swap a b * (swap c d * gprod L')
        rw [Group.mul_assoc]

/-- **The 3-cycles generate `Aₙ`.** Every even permutation is a product of 3-cycles. -/
theorem c3_generate {n : Nat} {σ : Perm (Fin n)} (hσ : σ ∈ alternating n) :
    ∃ M : List (Perm (Fin n)), (∀ t, t ∈ M → IsC3 t) ∧ gprod M = σ := by
  obtain ⟨L, hL, rfl⟩ := transpositions_generate σ
  have hp := parity_gprod_transpositions L hL
  rw [mem_alternating.1 hσ] at hp
  have hev : L.length % 2 = 0 := by
    by_cases h : L.length % 2 = 1
    · simp [h] at hp
    · omega
  exact even_transpositions_c3 (L.length / 2) L (by omega) hL

/-- **A subgroup containing all 3-cycles contains `Aₙ`.** -/
theorem alternating_le_of_c3 {n : Nat} (H : Subgroup (Perm (Fin n)))
    (h : ∀ σ, IsC3 σ → σ ∈ H) : ∀ σ, σ ∈ alternating n → σ ∈ H := by
  intro σ hσ
  obtain ⟨M, hM, rfl⟩ := c3_generate hσ
  exact gprod_mem H M fun t ht => h t (hM t ht)

end Foundations.Algebra
