import Foundations.Langlands.Padic.AbsoluteValues

/-!
# Ostrowski's theorem, I: the digit bound

Alexander Ostrowski proved in 1916 that the absolute values on ℚ are, up to equivalence, exactly
`|·|_∞` and the `|·|ₚ`: the *places* of ℚ are the primes together with one infinite place. This
file contains the analytic heart of his argument, the **digit bound**: for integers `m, n ≥ 2`
and any absolute value `φ`,

  `log φ(m) · log n ≤ log m · log max(1, φ(n))`.

The proof writes `m^k` in base `n`. It has about `k · log m / log n` digits, each digit `r < n`
has `φ(r) ≤ r < n`, and so `φ(m)^k ≤ (#digits) · n · max(1, φ(n))^(#digits)`. Taking logarithms,
dividing by `k`, and letting `k → ∞` kills the factor `#digits`, which grows only linearly in `k`
(we let `k = t²` run through the squares, so that `log k = 2 log t ≤ 2t` is visibly `o(k)`).

The bound is stated for any `B ≥ max(1, φ(n))`; it is used in `Ostrowski` with `B = 1` and with
`B = φ(n)`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Foundations.NumberTheory Lean.Grind R

namespace AbsVal

variable (φ : AbsVal)

/-- `φ(a b) = φ(a) φ(b)` for natural numbers. -/
theorem map_natCast_mul (a b : Nat) : φ.f ((a * b : Nat) : Q) = φ.f (a : Q) * φ.f (b : Q) := by
  rw [show ((a * b : Nat) : Q) = (a : Q) * (b : Q) by grind, φ.mul]

/-- `φ(aᵏ) = φ(a)ᵏ` for natural numbers. -/
theorem map_natCast_pow (a : Nat) : ∀ k : Nat, φ.f ((a ^ k : Nat) : Q) = φ.f (a : Q) ^ k
  | 0 => by rw [Nat.pow_zero, Semiring.pow_zero]; exact φ.map_one
  | k + 1 => by rw [Nat.pow_succ, map_natCast_mul, map_natCast_pow a k, Semiring.pow_succ]

/-- Natural numbers `n ≥ 1` are nonzero rationals. -/
theorem natCast_ne_zero {n : Nat} (hn : 1 ≤ n) : (n : Q) ≠ 0 := fun h => by
  have := (mk_eq_zero_iff Int.one_pos).1 h; omega

/-- **Digit bound.** If `n ≥ 2`, `B ≥ 1` and `φ(n) ≤ B`, then every `N < n^L` (a number with at
most `L` digits in base `n`) satisfies `φ(N) ≤ L · n · B^L`. -/
theorem digits_bound {n : Nat} (hn : 2 ≤ n) {B : R} (hB : 1 ≤ B) (hnB : φ.f (n : Q) ≤ B) :
    ∀ L N : Nat, N < n ^ L → φ.f (N : Q) ≤ (L : R) * (n : R) * B ^ L := by
  intro L
  induction L with
  | zero =>
    intro N hN
    have : N = 0 := by rw [Nat.pow_zero] at hN; omega
    subst this
    rw [show ((0 : Nat) : Q) = 0 from rfl, φ.map_zero]; grind
  | succ L ih =>
    intro N hN
    have hq : N / n < n ^ L := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← Nat.pow_succ]
    have hr : N % n < n := Nat.mod_lt _ (by omega)
    have e : (N : Q) = (n : Q) * ((N / n : Nat) : Q) + ((N % n : Nat) : Q) := by
      have h0 := Nat.div_add_mod N n
      have h1 : ((n * (N / n) + N % n : Nat) : Q) = (n : Q) * ((N / n : Nat) : Q) +
          ((N % n : Nat) : Q) := by grind
      rw [h0] at h1; exact h1
    have h1 := φ.triangle ((n : Q) * ((N / n : Nat) : Q)) ((N % n : Nat) : Q)
    rw [← e, φ.mul] at h1
    have h2 := ih _ hq
    have h3 := φ.map_nat_le (N % n)
    have h4 : ((N % n : Nat) : R) ≤ (n : R) :=
      OrderedRing.natCast_le_natCast_of_le _ _ (by omega)
    have hq0 := φ.nonneg ((N / n : Nat) : Q)
    have h5 := OrderedRing.mul_le_mul_of_nonneg_right hnB hq0
    have hB0 : (0 : R) ≤ B := by grind
    have h6 := OrderedRing.mul_le_mul_of_nonneg_left h2 hB0
    have h7 : 1 ≤ B ^ (L + 1) := one_le_npow hB _
    have hn0 : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    have h8 := OrderedRing.mul_le_mul_of_nonneg_left h7 hn0
    rw [Semiring.pow_succ] at h8 ⊢
    rw [show ((L + 1 : Nat) : R) = (L : R) + 1 by grind]
    grind

/-- Every `N ≥ 1` lies in a bracket `n^L ≤ N < n^(L+1)` (for `n ≥ 2`). -/
theorem exists_pow_bracket {n : Nat} (hn : 2 ≤ n) :
    ∀ N : Nat, 1 ≤ N → ∃ L : Nat, n ^ L ≤ N ∧ N < n ^ (L + 1) := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro _
    by_cases h0 : N = 0
    · subst h0; exact ⟨0, by simp, by simp; omega⟩
    · obtain ⟨L, h1, h2⟩ := ih (by omega)
      by_cases h3 : N + 1 < n ^ (L + 1)
      · exact ⟨L, by omega, h3⟩
      · refine ⟨L + 1, by omega, ?_⟩
        have hpos : 1 ≤ n ^ (L + 1) := Nat.pow_pos (by omega)
        have := Nat.mul_le_mul_left (n ^ (L + 1)) hn
        rw [Nat.pow_succ n (L + 1)]; omega

/-- **The bound for one power.** For `m, n ≥ 2`, `B ≥ 1`, `φ(n) ≤ B` and every `k`, there is
`L` (the number of base-`n` digits of `mᵏ`, minus one) with `L · log n ≤ k · log m` and
`k · log φ(m) ≤ log (L + 1) + log n + (L + 1) · log B`. -/
theorem pow_bound {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n) {B : R} (hB : 1 ≤ B)
    (hnB : φ.f (n : Q) ≤ B) (k : Nat) :
    ∃ L : Nat, (L : R) * log (n : R) ≤ (k : R) * log (m : R) ∧
      (k : R) * log (φ.f (m : Q)) ≤
        log ((L : R) + 1) + log (n : R) + ((L : R) + 1) * log B := by
  obtain ⟨L, h1, h2⟩ := exists_pow_bracket hn (m ^ k) (Nat.pow_pos (by omega))
  refine ⟨L, ?_, ?_⟩
  · have hc : ((n ^ L : Nat) : R) ≤ ((m ^ k : Nat) : R) :=
      OrderedRing.natCast_le_natCast_of_le _ _ h1
    rw [show ((n ^ L : Nat) : R) = (n : R) ^ L by grind,
      show ((m ^ k : Nat) : R) = (m : R) ^ k by grind] at hc
    have hn0 : (0 : R) < (n : R) := OrderedRing.pos_natCast_of_pos _ (by omega)
    have hm0 : (0 : R) < (m : R) := OrderedRing.pos_natCast_of_pos _ (by omega)
    have := log_le_log (npow_pos hn0 L) hc
    rwa [log_npow hn0, log_npow hm0] at this
  · have hd := φ.digits_bound hn hB hnB (L + 1) (m ^ k) h2
    rw [map_natCast_pow] at hd
    have hφm := φ.pos (natCast_ne_zero (n := m) (by omega))
    have hn0 : (0 : R) < (n : R) := OrderedRing.pos_natCast_of_pos _ (by omega)
    have hL0 : (0 : R) < (L : R) + 1 := by
      have : (0 : R) ≤ (L : R) := OrderedRing.natCast_nonneg; grind
    have hB0 : (0 : R) < B := by grind
    have := log_le_log (npow_pos hφm k) hd
    rw [log_npow hφm, log_mul (OrderedRing.mul_pos (by grind) hn0) (npow_pos hB0 _),
      log_mul (by grind) hn0, log_npow hB0] at this
    rw [show ((L + 1 : Nat) : R) = (L : R) + 1 by grind] at this
    exact this

/-- **Ostrowski's digit bound.** For integers `m, n ≥ 2`, any `B ≥ 1` with `φ(n) ≤ B` satisfies
`log φ(m) · log n ≤ log m · log B`. -/
theorem digit_bound {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n) {B : R} (hB : 1 ≤ B)
    (hnB : φ.f (n : Q) ≤ B) :
    log (φ.f (m : Q)) * log (n : R) ≤ log (m : R) * log B := by
  -- Notation and basic signs.
  have hn1 : (1 : R) < (n : R) := by
    have : ((1 : Nat) : R) < (n : R) := OrderedRing.natCast_lt_natCast_of_lt _ _ (by omega)
    grind
  have hm1 : (1 : R) < (m : R) := by
    have : ((1 : Nat) : R) < (m : R) := OrderedRing.natCast_lt_natCast_of_lt _ _ (by omega)
    grind
  have hln := log_pos hn1
  have hlm := log_pos hm1
  have hlB := log_nonneg hB
  apply Classical.byContradiction
  intro hcon
  -- `A > 0` is the defect we will show cannot exist.
  have hA : 0 < log (φ.f (m : Q)) * log (n : R) - log (m : R) * log B := by grind
  generalize hAdef : log (φ.f (m : Q)) * log (n : R) - log (m : R) * log B = A at hA
  have hinv : log (n : R) * (log (n : R))⁻¹ = 1 := Field.mul_inv_cancel (by grind)
  have hinvpos := inv_pos' hln
  have hc0 : 0 ≤ log (m : R) * (log (n : R))⁻¹ :=
    OrderedRing.mul_nonneg (by grind) (by grind)
  generalize hcdef : log (m : R) * (log (n : R))⁻¹ = c at hc0
  have hD0 : 0 ≤ log (c + 1) + log (n : R) + log B := by
    have := log_nonneg (show (1 : R) ≤ c + 1 by grind); grind
  generalize hDdef : log (c + 1) + log (n : R) + log B = D at hD0
  -- For every `t ≥ 1`: `t² A ≤ (2t + D) log n`.
  have key : ∀ t : Nat, 1 ≤ t → ((t : R) * (t : R)) * A ≤ (2 * (t : R) + D) * log (n : R) := by
    intro t ht
    have ht1 : (1 : R) ≤ (t : R) := by
      have : ((1 : Nat) : R) ≤ (t : R) := OrderedRing.natCast_le_natCast_of_le _ _ ht
      grind
    obtain ⟨L, hL1, hL2⟩ := φ.pow_bound hm hn hB hnB (t * t)
    rw [show ((t * t : Nat) : R) = (t : R) * (t : R) by grind] at hL1 hL2
    have hL0 : (0 : R) ≤ (L : R) := OrderedRing.natCast_nonneg
    have hk1 : (1 : R) ≤ (t : R) * (t : R) := by
      have := OrderedRing.mul_le_mul_of_nonneg_left ht1 (by grind : (0 : R) ≤ (t : R)); grind
    -- multiply the two inequalities by `log n` and `log B`
    have e1 := OrderedRing.mul_le_mul_of_nonneg_right hL2 (Std.le_of_lt hln)
    have e2 := OrderedRing.mul_le_mul_of_nonneg_right hL1 hlB
    have step1 : ((t : R) * (t : R)) * A ≤
        (log ((L : R) + 1) + log (n : R) + log B) * log (n : R) := by
      rw [← hAdef]; grind
    -- `L ≤ t² c`, hence `L + 1 ≤ t² (c + 1)`
    have e3 := OrderedRing.mul_le_mul_of_nonneg_right hL1 (Std.le_of_lt hinvpos)
    have hLc : (L : R) ≤ (t : R) * (t : R) * c := by
      rw [← hcdef]
      have : (L : R) * log (n : R) * (log (n : R))⁻¹ = (L : R) := by
        rw [Semiring.mul_assoc, hinv, Semiring.mul_one]
      grind
    have hc1 := OrderedRing.mul_le_mul_of_nonneg_right hk1 (show (0 : R) ≤ c + 1 by grind)
    have hL1' : (L : R) + 1 ≤ (t : R) * (t : R) * (c + 1) := by grind
    have ht0 : (0 : R) < (t : R) := by grind
    have hlog := log_le_log (by grind : (0 : R) < (L : R) + 1) hL1'
    rw [log_mul (OrderedRing.mul_pos ht0 ht0) (by grind : (0 : R) < c + 1),
      log_mul ht0 ht0] at hlog
    have hlt := log_le_sub_one ht1
    have hfin : log ((L : R) + 1) + log (n : R) + log B ≤ 2 * (t : R) + D := by
      rw [← hDdef]; grind
    have := OrderedRing.mul_le_mul_of_nonneg_right hfin (Std.le_of_lt hln)
    grind
  -- Choose `t` with `t A > K := (2 + D) log n`.
  have hK0 : 0 ≤ (2 + D) * log (n : R) := OrderedRing.mul_nonneg (by grind) (by grind)
  obtain ⟨t0, ht0⟩ := archimedean (((2 + D) * log (n : R)) * A⁻¹)
  have hAinv : A * A⁻¹ = 1 := Field.mul_inv_cancel (by grind)
  have ht1 : (1 : R) ≤ ((t0 + 1 : Nat) : R) := by
    have : ((1 : Nat) : R) ≤ ((t0 + 1 : Nat) : R) :=
      OrderedRing.natCast_le_natCast_of_le _ _ (by omega)
    grind
  have hbig : (2 + D) * log (n : R) < ((t0 + 1 : Nat) : R) * A := by
    have h1 : ((2 + D) * log (n : R)) * A⁻¹ < ((t0 + 1 : Nat) : R) := by
      rw [show ((t0 + 1 : Nat) : R) = (t0 : R) + 1 by grind]; grind
    have := OrderedRing.mul_lt_mul_of_pos_right h1 hA
    rw [Semiring.mul_assoc, show A⁻¹ * A = A * A⁻¹ from CommSemiring.mul_comm _ _, hAinv,
      Semiring.mul_one] at this
    exact this
  have hk := key (t0 + 1) (by omega)
  generalize ((t0 + 1 : Nat) : R) = t at ht1 hbig hk
  have h1 := OrderedRing.mul_lt_mul_of_pos_left hbig (by grind : (0 : R) < t)
  have h2 := OrderedRing.mul_le_mul_of_nonneg_right ht1
    (show (0 : R) ≤ D * log (n : R) from OrderedRing.mul_nonneg hD0 (Std.le_of_lt hln))
  grind

end AbsVal

end Foundations.Langlands.Padic
