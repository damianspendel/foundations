import Foundations.NumberTheory.Mobius
import Foundations.NumberTheory.LFunction

/-!
# Real characters: the divisor sums `r(n) = Σ_{d ∣ n} χ(n)` and the sum `Σ r(n)/√n`

For a **real** character `χ` (values `0, ±1`) the argument used for complex characters breaks
down: `χ̄ = χ`, so a zero of `L(1, χ)` would be counted only once. The classical way out
(Mertens 1897, simplified by many since) looks at the divisor sums

  `r(n) = Σ_{d ∣ n} χ(d)`.

Because `χ` is completely multiplicative, `r(pᵃ m) = (1 + χ(p) + ⋯ + χ(p)ᵃ) · r(m)` for `p ∤ m`;
with `χ(p) ∈ {−1, 0, 1}` each factor is `≥ 0`, and `≥ 1` when `a` is even. Hence

  `r(n) ≥ 0` for all `n`, and `r(k²) ≥ 1`.

(In modern terms, `ζ(s) L(s, χ)` is the zeta function of a quadratic field and has non-negative
coefficients.) Consequently the sum `T(N) = Σ_{n ≤ N} r(n)/√n` grows at least like
`Σ_{k ≤ √N} 1/k ≥ log √N`. On the other hand, counting the pairs `(d, m)` with `dm ≤ N`,

  `T(N) = Σ_{d ≤ N} χ(d)/√d · U(N/d)`,   `U(K) = Σ_{1 ≤ m ≤ K} 1/√m`,

which the next file shows to be `2√N · L(1, χ) + O(1)`. So `L(1, χ) = 0` is impossible.
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Numbers Foundations.Numbers.Arith Lean.Grind
open Foundations.Numbers.C (ofReal)

attribute [local instance] Classical.propDecidable

variable {q : Nat} [NeZero q]

/-- A Dirichlet character is **real** if all its values are real. -/
def IsRealChar (χ : Character (ZModUnits q)) : Prop := ∀ n, (dchar χ n).im = 0

/-- The real values `χ(n)` of a real character. -/
noncomputable def rc (χ : Character (ZModUnits q)) (n : Nat) : R := (dchar χ n).re

section

variable {χ : Character (ZModUnits q)} (hχ : IsRealChar χ)
include hχ

/-- A real character is its real part. -/
theorem dchar_eq_ofReal (n : Nat) : dchar χ n = ofReal (rc χ n) := C.ext rfl (hχ n)

/-- `χ(mn) = χ(m) χ(n)` for the real values. -/
theorem rc_mul (m n : Nat) : rc χ (m * n) = rc χ m * rc χ n := by
  unfold rc; rw [dchar_mul, C.mul_re, hχ m, hχ n]; grind

/-- `χ(pⁱ) = χ(p)ⁱ`. -/
theorem rc_pow (p : Nat) : ∀ i, rc χ (p ^ i) = rc χ p ^ i
  | 0 => by unfold rc; rw [Nat.pow_zero, dchar_one]; rfl
  | i + 1 => by rw [Nat.pow_succ, rc_mul hχ, rc_pow p i]; rfl

/-- **The values of a real character are `1`, `0` or `−1`.** -/
theorem rc_values (n : Nat) : rc χ n = 1 ∨ rc χ n = 0 ∨ rc χ n = -1 := by
  by_cases h : Nat.Coprime n q
  · have h1 := cabs_dchar_le χ n
    rw [dchar_of_coprime χ h, χ.2.cabs_eq_one] at h1
    have h2 : C.normSq (dchar χ n) = 1 := by
      rw [← C.cabs_mul_self, dchar_of_coprime χ h, χ.2.cabs_eq_one]; grind
    unfold C.normSq at h2; rw [hχ n] at h2
    have h3 : (rc χ n - 1) * (rc χ n + 1) = 0 := by unfold rc; grind
    by_cases h4 : rc χ n - 1 = 0
    · left; grind
    · right; right
      have : rc χ n + 1 = (rc χ n - 1)⁻¹ * ((rc χ n - 1) * (rc χ n + 1)) := by
        rw [← Semiring.mul_assoc, Field.inv_mul_cancel h4]; grind
      rw [h3] at this; grind
  · right; left; unfold rc; rw [dchar_of_not_coprime χ h]; rfl

end

/-- Geometric sums `1 + t + ⋯ + tᵃ` with `t ∈ {1, 0, −1}` are `≥ 0`, and `≥ 1` for even `a`. -/
theorem geom_sum_nonneg {t : R} (ht : t = 1 ∨ t = 0 ∨ t = -1) (a : Nat) :
    0 ≤ gsum (fun i => t ^ i) (a + 1) ∧ (a % 2 = 0 → 1 ≤ gsum (fun i => t ^ i) (a + 1)) := by
  rcases ht with rfl | rfl | rfl
  · have : ∀ a, gsum (fun i => (1 : R) ^ i) a = (a : R) := by
      intro a; induction a with
      | zero => rfl
      | succ a ih => rw [gsum_succ, ih, R.one_pow]; grind
    rw [this]
    have := natCast_le' (Nat.zero_le a)
    exact ⟨by grind, fun _ => by grind⟩
  · have : ∀ a, gsum (fun i => (0 : R) ^ i) (a + 1) = 1 := by
      intro a; induction a with
      | zero => show (0 : R) + 1 = 1; grind
      | succ a ih => rw [gsum_succ, ih]; show (1 : R) + (0 : R) ^ a * 0 = 1; grind
    rw [this]; exact ⟨by grind, fun _ => by grind⟩
  · have hp : ∀ a, (-1 : R) ^ a = if a % 2 = 0 then 1 else -1 := by
      intro a; induction a with
      | zero => rfl
      | succ a ih =>
        show (-1 : R) ^ a * (-1) = _
        rw [ih]
        by_cases h : a % 2 = 0
        · rw [ite_eq_left h, ite_eq_right (by omega)]; grind
        · rw [ite_eq_right h, ite_eq_left (by omega)]; grind
    have : ∀ a, gsum (fun i => (-1 : R) ^ i) (a + 1) = if a % 2 = 0 then 1 else 0 := by
      intro a; induction a with
      | zero => show (0 : R) + 1 = 1; grind
      | succ a ih =>
        rw [gsum_succ, ih, hp]
        by_cases h : a % 2 = 0
        · rw [ite_eq_left h, ite_eq_right (show ¬ (a + 1) % 2 = 0 by omega),
            ite_eq_right (show ¬ (a + 1) % 2 = 0 by omega)]; grind
        · rw [ite_eq_right h, ite_eq_left (show (a + 1) % 2 = 0 by omega),
            ite_eq_left (show (a + 1) % 2 = 0 by omega)]; grind
    rw [this]
    exact ⟨by split <;> grind, fun h => by rw [ite_eq_left h]; grind⟩

/-- The divisor sums `r(n) = Σ_{d ∣ n} χ(d)` of a real character. -/
noncomputable def rdiv (χ : Character (ZModUnits q)) (n : Nat) : R := dsum (rc χ) n

/-- Divisor sums of products with a constant factor. -/
theorem dsum_mul_left {α : Type} [Field α] (c : α) (f : Nat → α) (n : Nat) :
    dsum (fun e => c * f e) n = c * dsum f n := by
  unfold dsum; rw [← gsum_mul_left]; apply gsum_congr; intro d _; split <;> grind

section

variable {χ : Character (ZModUnits q)} (hχ : IsRealChar χ)
include hχ

/-- `r(pᵃ m) = (1 + χ(p) + ⋯ + χ(p)ᵃ) · r(m)` for a prime `p ∤ m`. -/
theorem rdiv_prime_pow_mul {p m : Nat} (hp : Prime p) (hpm : ¬ p ∣ m) (hm : 0 < m) (a : Nat) :
    rdiv χ (p ^ a * m) = gsum (fun i => rc χ p ^ i) (a + 1) * rdiv χ m := by
  unfold rdiv
  rw [dsum_prime_pow_mul _ hp hpm hm a, ← gsum_mul_right]
  apply gsum_congr; intro i _
  rw [dsum_congr (g := fun e => rc χ p ^ i * rc χ e) (fun e _ => by rw [rc_mul hχ, rc_pow hχ]),
    dsum_mul_left]

/-- **Positivity of the divisor sums.** `r(n) ≥ 0`, and `r(k²) ≥ 1`. -/
theorem rdiv_props : ∀ n, 0 < n → 0 ≤ rdiv χ n ∧ ∀ k, k * k = n → 1 ≤ rdiv χ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1
      have : rdiv χ 1 = 1 := by
        unfold rdiv rc; rw [dsum_one, dchar_one]; rfl
      rw [this]; exact ⟨by grind, fun _ _ => by grind⟩
    · constructor
      · obtain ⟨p, a, m, hp, ha, hpm, hm, rfl⟩ := exists_prime_pow_mul (show 2 ≤ n by omega)
        rw [rdiv_prime_pow_mul hχ hp hpm hm a]
        have hlt : m < p ^ a * m := by
          have : 2 ≤ p ^ a := Nat.le_trans hp.1 (by
            calc p = p ^ 1 := (Nat.pow_one p).symm
              _ ≤ p ^ a := Nat.pow_le_pow_right (by have := hp.1; omega) ha)
          have : 2 * m ≤ p ^ a * m := Nat.mul_le_mul_right m this
          omega
        exact OrderedRing.mul_nonneg (geom_sum_nonneg (rc_values hχ p) a).1 (ih m hlt hm).1
      · intro k hk
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with h | h
          · exfalso
            rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp at hk <;> omega
          · exact h
        obtain ⟨p, b, m, hp, hb, hpm, hm, rfl⟩ := exists_prime_pow_mul hk2
        have e : p ^ b * m * (p ^ b * m) = p ^ (2 * b) * (m * m) := by
          rw [show 2 * b = b + b by omega, Nat.pow_add]; grind
        have hpmm : ¬ p ∣ m * m := fun h => (euclid_lemma hp h).elim hpm hpm
        have hmm : 0 < m * m := Nat.mul_pos hm hm
        rw [← hk, e, rdiv_prime_pow_mul hχ hp hpmm hmm (2 * b)]
        have hlt : m * m < p ^ (2 * b) * (m * m) := by
          have : 2 ≤ p ^ (2 * b) := Nat.le_trans hp.1 (by
            calc p = p ^ 1 := (Nat.pow_one p).symm
              _ ≤ p ^ (2 * b) := Nat.pow_le_pow_right (by have := hp.1; omega) (by omega))
          have : 2 * (m * m) ≤ p ^ (2 * b) * (m * m) := Nat.mul_le_mul_right _ this
          omega
        have hG := (geom_sum_nonneg (rc_values hχ p) (2 * b)).2 (by omega)
        have hR := (ih (m * m) (by rw [← hk, e]; exact hlt) hmm).2 m rfl
        have := OrderedRing.mul_le_mul_of_nonneg_left hR (show 0 ≤ gsum (fun i => rc χ p ^ i)
          (2 * b + 1) by grind)
        grind

end

/-! ## The sum `T(N) = Σ_{n ≤ N} r(n)/√n` -/

/-- `U(K) = Σ_{1 ≤ m ≤ K} 1/√m`. -/
noncomputable def Usum (K : Nat) : R := gsum (fun m => 1 / R.sqrt (m : R)) (K + 1)

/-- `T(N) = Σ_{n ≤ N} r(n)/√n`. -/
noncomputable def Tsum (χ : Character (ZModUnits q)) (N : Nat) : R :=
  gsum (fun n => rdiv χ n * (1 / R.sqrt (n : R))) (N + 1)

/-- `√(ab) = √a √b` for `a, b ≥ 0`. -/
theorem sqrt_mul' {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : R.sqrt (a * b) = R.sqrt a * R.sqrt b := by
  apply R.sqrt_eq (OrderedRing.mul_nonneg (R.sqrt_nonneg a) (R.sqrt_nonneg b))
  have := (R.sqrt_spec ha).2; have := (R.sqrt_spec hb).2; grind

/-- `√0 = 0`. -/
theorem sqrt_zero' : R.sqrt 0 = 0 := R.sqrt_eq (by grind) (by grind)

/-- `√(n²) = n`. -/
theorem sqrt_natCast_sq (n : Nat) : R.sqrt ((n * n : Nat) : R) = (n : R) :=
  R.sqrt_eq OrderedRing.natCast_nonneg (by grind)

/-- `√n > 0` for `n ≥ 1`. -/
theorem sqrt_natCast_pos {n : Nat} (hn : 0 < n) : 0 < R.sqrt (n : R) := by
  have h := R.sqrt_spec (Std.le_of_lt (natCast_pos' hn))
  rcases (by have := R.sqrt_nonneg (n : R); grind : R.sqrt (n : R) = 0 ∨ 0 < R.sqrt (n : R)) with e | e
  · have := natCast_pos' hn; rw [e] at h; grind
  · exact e

/-- `1/√0 = 0`. -/
theorem one_div_sqrt_zero : 1 / R.sqrt ((0 : Nat) : R) = 0 := by
  rw [show ((0 : Nat) : R) = 0 by grind, sqrt_zero', Field.div_eq_mul_inv, Field.inv_zero]; grind

/-- **Counting pairs.** `T(N) = Σ_{d ≤ N} χ(d)/√d · U(⌊N/d⌋)`. -/
theorem Tsum_eq (χ : Character (ZModUnits q)) (N : Nat) :
    Tsum χ N = gsum (fun d => rc χ d * (1 / R.sqrt (d : R)) * Usum (N / d)) (N + 1) := by
  let F : Nat → Nat → R := fun d m => rc χ d * (1 / R.sqrt (d : R)) * (1 / R.sqrt (m : R))
  have h0 : ∀ m, F 0 m = 0 := fun m => by
    show _ * (1 / R.sqrt ((0 : Nat) : R)) * _ = 0; rw [one_div_sqrt_zero]; grind
  have h0' : ∀ d, F d 0 = 0 := fun d => by
    show _ * (1 / R.sqrt ((0 : Nat) : R)) = 0; rw [one_div_sqrt_zero]; grind
  have e1 : ∀ n, n < N + 1 → rdiv χ n * (1 / R.sqrt (n : R)) =
      gsum (fun d => if d ∣ n then F d (n / d) else 0) (n + 1) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [gsum_succ, gsum_nil, ite_eq_left (Nat.dvd_zero 0), h0, one_div_sqrt_zero]; grind
    · unfold rdiv dsum
      rw [← gsum_mul_right]; apply gsum_congr; intro d _
      by_cases hd : d ∣ n
      · rw [ite_eq_left hd, ite_eq_left hd]
        obtain ⟨m, hm⟩ := hd
        have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
        have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
        show _ = rc χ d * (1 / R.sqrt (d : R)) * (1 / R.sqrt ((n / d : Nat) : R))
        rw [show n / d = m by rw [hm, Nat.mul_div_cancel_left m hd0], hm,
          show ((d * m : Nat) : R) = (d : R) * (m : R) by grind,
          sqrt_mul' OrderedRing.natCast_nonneg OrderedRing.natCast_nonneg]
        have h1 := sqrt_natCast_pos hd0
        have h2 := sqrt_natCast_pos hm0
        have : R.sqrt (d : R) ≠ 0 := by grind
        have : R.sqrt (m : R) ≠ 0 := by grind
        grind
      · rw [ite_eq_right hd, ite_eq_right hd]; grind
  unfold Tsum
  rw [gsum_congr e1, gsum_divisors_eq F h0 h0' N]
  apply gsum_congr; intro d _
  unfold Usum; rw [← gsum_mul_left]

/-- The harmonic sum `H(M) = Σ_{1 ≤ k ≤ M} 1/k` is at least `log (M + 1)`. -/
theorem harmonic_ge (M : Nat) : lnat (M + 1) ≤ gsum (fun k => 1 / (k : R)) (M + 1) := by
  induction M with
  | zero =>
    rw [lnat_one, gsum_succ, gsum_nil, show ((0 : Nat) : R) = 0 by grind, Field.div_eq_mul_inv,
      Field.inv_zero]; grind
  | succ M ih =>
    rw [gsum_succ]
    have := lnat_succ_sub_le (n := M + 1) (by omega)
    grind

/-- **Lower bound.** For a real character, `T(M²) ≥ Σ_{1 ≤ k ≤ M} 1/k ≥ log (M + 1)`. -/
theorem Tsum_sq_ge {χ : Character (ZModUnits q)} (hχ : IsRealChar χ) (M : Nat) :
    lnat (M + 1) ≤ Tsum χ (M * M) := by
  have hnn : ∀ n, 0 ≤ rdiv χ n * (1 / R.sqrt (n : R)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [one_div_sqrt_zero]; grind
    · exact OrderedRing.mul_nonneg (rdiv_props hχ n h).1 (Std.le_of_lt
        (OF.div_pos (by grind) (sqrt_natCast_pos h)))
  have key : ∀ M, gsum (fun k => 1 / (k : R)) (M + 1) ≤ Tsum χ (M * M) := by
    intro M
    induction M with
    | zero =>
      unfold Tsum; rw [gsum_succ, gsum_nil, gsum_succ, gsum_nil, Nat.zero_mul, one_div_sqrt_zero,
        show ((0 : Nat) : R) = 0 by grind, Field.div_eq_mul_inv, Field.inv_zero]; grind
    | succ M ih =>
      rw [gsum_succ (fun k => 1 / (k : R)) (M + 1)]
      unfold Tsum at ih ⊢
      rw [show (M + 1) * (M + 1) + 1 = (M * M + 1) + (2 * M + 1) by grind,
        gsum_split (fun n => rdiv χ n * (1 / R.sqrt (n : R))) (M * M + 1) (2 * M + 1),
        gsum_succ (fun j => rdiv χ (M * M + 1 + j) * (1 / R.sqrt ((M * M + 1 + j : Nat) : R))) (2 * M)]
      have h1 := gsum_nonneg (fun j => hnn (M * M + 1 + j)) (2 * M)
      have hsq : M * M + 1 + 2 * M = (M + 1) * (M + 1) := by grind
      have h2 : 1 / ((M + 1 : Nat) : R) ≤
          rdiv χ (M * M + 1 + 2 * M) * (1 / R.sqrt ((M * M + 1 + 2 * M : Nat) : R)) := by
        rw [hsq, sqrt_natCast_sq]
        have := (rdiv_props hχ ((M + 1) * (M + 1)) (Nat.mul_pos (by omega) (by omega))).2 (M + 1) rfl
        have hp := natCast_pos' (show 0 < M + 1 by omega)
        have := OrderedRing.mul_le_mul_of_nonneg_right this (Std.le_of_lt (OF.div_pos
          (show (0 : R) < 1 by grind) hp))
        grind
      grind
  exact Std.le_trans (harmonic_ge M) (key M)

end Foundations.NumberTheory
