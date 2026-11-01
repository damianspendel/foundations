import Foundations.NumberTheory.PNTTatuzawaIseki
import Foundations.Topology.Stirling

/-!
# Toward the prime number theorem VII: estimates for Selberg's formula

To apply the Tatuzawa–Iseki identity we need three classical estimates, each sharper than the
crude bounds used for Mertens' theorems:

* **Euler's constant.** `H(M) = 1 + 1/2 + ⋯ + 1/M = log M + γ + O(1/M)`. The sequence
  `H(M) − log M` decreases, `H(M) − log(M+1)` increases, and they differ by
  `log(1 + 1/M) ≤ 1/M`; so both converge to a common limit `γ` (Euler 1734; `γ ≈ 0.5772`) and
  `0 ≤ H(M) − log M − γ ≤ 1/M`. Whether `γ` is irrational is still unknown.
* **Stirling with a bounded error.** `log M! = M log M − M + ½ log M + O(1)`, here taken from the
  Stirling file of Part VIII (the sequence `log M! + M − (M + ½) log M` decreases from `1` and
  stays above `3/4`).
* **A logarithmic average.** `Σ_{d ≤ N} log²(N/d) ≤ 6N`: the sum is a Riemann sum for
  `∫₀ᴺ log²(N/t) dt = 2N`; we compare term by term with `h(t) = t (log²(N/t) + 2 log(N/t) + 2)`,
  whose derivative is `log²(N/t)`, by the mean value theorem.

We also record **Chebyshev's identity** `Σ_{n ≤ M} ψ(M/n) = log M!`, the form of
`log M! = Σ Λ(d) ⌊M/d⌋` that the Tatuzawa–Iseki identity consumes.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-! ## The exponential inequality on the whole line -/

/-- **`1 + x ≤ eˣ` for all real `x`.** (For `x ≤ 0`: `1 + t − eᵗ` has derivative `1 − eᵗ ≥ 0` on
`[x, 0]`.) -/
theorem one_add_le_exp' (x : R) : 1 + x ≤ exp x := by
  rcases (by grind : 0 ≤ x ∨ x < 0) with h | h
  · exact one_add_le_exp h
  · have hd : ∀ t, x ≤ t → t ≤ 0 → HasDerivAt (fun t => 1 + t - exp t) (1 - exp t) t := by
      intro t _ _
      have h := ((hasDerivAt_const 1 t).add (hasDerivAt_id t)).sub (hasDerivAt_exp t)
      rw [show (0 : R) + 1 - exp t = 1 - exp t by grind] at h
      exact h
    have := monotone_of_deriv_nonneg (a := x) (b := 0) hd (fun t _ ht => by
      rcases (by grind : t = 0 ∨ t < 0) with h0 | h0
      · subst h0; rw [exp_zero]; grind
      · have := exp_strictMono h0; rw [exp_zero] at this; grind) (Std.le_refl x) (Std.le_of_lt h)
      (Std.le_refl 0)
    rw [exp_zero] at this; grind

/-- **`log y ≤ y − 1` for all `y > 0`.** -/
theorem log_le_sub_one' {y : R} (hy : 0 < y) : R.log y ≤ y - 1 := by
  have h1 := one_add_le_exp' (R.log y)
  rw [exp_log hy] at h1; grind

/-- `log(m+1) − log m ≤ 1/m` and `≥ 1/(m+1)`, in multiplied form, for `m ≥ 1`. -/
theorem log_succ_sub_bounds {m : Nat} (hm : 1 ≤ m) :
    (m : R) * (R.log ((m + 1 : Nat) : R) - R.log (m : R)) ≤ 1 ∧
      1 ≤ ((m : R) + 1) * (R.log ((m + 1 : Nat) : R) - R.log (m : R)) := by
  have hu : (0 : R) < (m : R) := natCast_pos' hm
  have ec : ((m + 1 : Nat) : R) = (m : R) + 1 := by grind
  have hv : (0 : R) < (m : R) + 1 := by grind
  rw [ec]
  have hm0 : (m : R) ≠ 0 := by grind
  have hv0 : (m : R) + 1 ≠ 0 := by grind
  constructor
  · have := log_le_sub_one' (div_pos hv hu)
    rw [log_div' hv hu] at this
    have e : (m : R) * (((m : R) + 1) / (m : R) - 1) = 1 := by grind
    have := OrderedRing.mul_le_mul_of_nonneg_left this (Std.le_of_lt hu)
    grind
  · have := log_le_sub_one' (div_pos hu hv)
    rw [log_div' hu hv] at this
    have e : ((m : R) + 1) * ((m : R) / ((m : R) + 1) - 1) = -1 := by grind
    have := OrderedRing.mul_le_mul_of_nonneg_left this (Std.le_of_lt hv)
    grind

/-! ## Euler's constant -/

/-- The **harmonic number** `H(M) = Σ_{1 ≤ k ≤ M} 1/k`. -/
noncomputable def harmonic (M : Nat) : R := fsum (fun k => if 1 ≤ k then 1 / (k : R) else 0) (M + 1)

/-- `H(M+1) = H(M) + 1/(M+1)`. -/
theorem harmonic_succ (M : Nat) : harmonic (M + 1) = harmonic M + 1 / ((M : R) + 1) := by
  unfold harmonic; rw [fsum_succ]
  simp only [show 1 ≤ M + 1 by omega, ↓reduceIte]
  rw [show ((M + 1 : Nat) : R) = (M : R) + 1 by grind]

/-- `H(1) = 1`. -/
theorem harmonic_one : harmonic 1 = 1 := by
  unfold harmonic; simp only [fsum_succ, fsum_zero]
  simp only [show ¬ 1 ≤ 0 by omega, Nat.le_refl, ↓reduceIte]
  rw [show ((1 : Nat) : R) = 1 by grind]; grind

/-- **Euler's constant** exists: there is `γ` with `0 ≤ H(M) − log M − γ ≤ 1/M` for all `M ≥ 1`
(and `γ ≤ 1`). -/
theorem exists_euler_gamma : ∃ γ : R, 0 ≤ γ ∧ γ ≤ 1 ∧ ∀ M : Nat, 1 ≤ M →
    0 ≤ harmonic M - R.log (M : R) - γ ∧
      (M : R) * (harmonic M - R.log (M : R) - γ) ≤ 1 := by
  -- `a M = H(M) − log M` decreases, `b M = H(M) − log(M+1)` increases.
  obtain ⟨a, had⟩ : ∃ a : Nat → R, a = fun M => harmonic M - R.log (M : R) := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : Nat → R, b = fun M => harmonic M - R.log ((M + 1 : Nat) : R) :=
    ⟨_, rfl⟩
  have hstep : ∀ M, 1 ≤ M → a (M + 1) ≤ a M ∧ b M ≤ b (M + 1) := by
    intro M hM
    have h1 := (log_succ_sub_bounds hM).2
    have h2 := (log_succ_sub_bounds (m := M + 1) (by omega)).1
    have hv : (0 : R) < (M : R) + 1 := by have := natCast_nonneg' M; grind
    have e1 : ((M + 1 : Nat) : R) = (M : R) + 1 := by grind
    rw [e1] at h2
    simp only [had, hbd]; rw [harmonic_succ]
    have hi : ((M : R) + 1) * (1 / ((M : R) + 1)) = 1 := by
      have : (M : R) + 1 ≠ 0 := by grind
      grind
    constructor
    · -- `1/(M+1) ≤ log(M+1) − log M`.
      apply Classical.byContradiction; intro h
      have := OrderedRing.mul_lt_mul_of_pos_left
        (show R.log ((M + 1 : Nat) : R) - R.log (M : R) < 1 / ((M : R) + 1) by grind) hv
      grind
    · -- `log(M+2) − log(M+1) ≤ 1/(M+1)`.
      apply Classical.byContradiction; intro h
      have := OrderedRing.mul_lt_mul_of_pos_left
        (show 1 / ((M : R) + 1) < R.log ((M + 1 + 1 : Nat) : R) - R.log ((M + 1 : Nat) : R) by
          grind) hv
      grind
  have hab : ∀ M, 1 ≤ M → b M ≤ a M ∧ (M : R) * (a M - b M) ≤ 1 := by
    intro M hM
    have h := (log_succ_sub_bounds hM).1
    have h' := (log_succ_sub_bounds hM).2
    have hu : (0 : R) < (M : R) := natCast_pos' hM
    simp only [had, hbd]
    constructor
    · apply Classical.byContradiction; intro hc
      have := OrderedRing.mul_lt_mul_of_pos_left
        (show R.log ((M + 1 : Nat) : R) - R.log (M : R) < 0 by grind)
        (show (0 : R) < (M : R) + 1 by grind)
      grind
    · grind
  -- The shifted sequences.
  have hamono : ∀ n, -a (n + 1) ≤ -a (n + 1 + 1) := fun n => by
    have := (hstep (n + 1) (by omega)).1; grind
  have hbmono : ∀ n, b (n + 1) ≤ b (n + 1 + 1) := fun n => (hstep (n + 1) (by omega)).2
  have hb_le : ∀ n m, b (n + 1) ≤ a (m + 1) := by
    intro n m
    have h1 : ∀ k, b (n + 1) ≤ b (n + 1 + k) := fun k => by
      have := mono_le (a := fun j => b (n + 1 + j)) (fun j => by
        have := hbmono (n + j)
        rw [show n + j + 1 = n + 1 + j by omega, show n + 1 + j + 1 = n + 1 + (j + 1) by omega]
          at this
        exact this) (Nat.zero_le k)
      exact this
    have h2 : ∀ k, a (m + 1 + k) ≤ a (m + 1) := fun k => by
      have := mono_le (a := fun j => -a (m + 1 + j)) (fun j => by
        have := hamono (m + j)
        rw [show m + j + 1 = m + 1 + j by omega, show m + 1 + j + 1 = m + 1 + (j + 1) by omega]
          at this
        exact this) (Nat.zero_le k)
      have e : m + 1 + 0 = m + 1 := rfl
      simp only [e] at this; grind
    have h3 := (hab (n + 1 + m) (by omega)).1
    have := h1 m; have := h2 n
    rw [show m + 1 + n = n + 1 + m by omega] at this
    grind
  obtain ⟨L, hL⟩ := monotone_convergence (a := fun n => -a (n + 1)) hamono
    ⟨-b 1, fun n => by have := hb_le 0 n; simp only [Nat.zero_add] at this; grind⟩
  have hγb : ∀ n, b (n + 1) ≤ -L := by
    intro n
    have := le_of_tendsto (c := b (n + 1)) (hL.const_mul (-1)) (fun m => by
      have := hb_le n m; show b (n + 1) ≤ -1 * -a (m + 1); grind)
    grind
  have hγa : ∀ n, -L ≤ a (n + 1) := by
    intro n
    have := le_lim_of_mono hamono hL n
    grind
  refine ⟨-L, ?_, ?_, ?_⟩
  · -- `γ ≥ b 1 = 1 − log 2 ≥ 0`.
    have hb1 : 0 ≤ b 1 := by
      simp only [hbd]; rw [harmonic_one]
      have := log_le_sub_one' (show (0 : R) < ((1 + 1 : Nat) : R) by
        rw [show ((1 + 1 : Nat) : R) = 2 by grind]; grind)
      rw [show ((1 + 1 : Nat) : R) = 2 by grind] at this ⊢; grind
    have := hγb 0
    simp only [Nat.zero_add] at this; grind
  · -- `γ ≤ a 1 = 1`.
    have := hγa 0
    have ha1 : a 1 = 1 := by
      simp only [had]; rw [harmonic_one, show ((1 : Nat) : R) = 1 by grind, R.log_one]; grind
    simp only [Nat.zero_add] at this; grind
  · intro M hM
    obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
    have h1 := hγa n
    have h2 := hγb n
    have h3 := hab (n + 1) hM
    have hA : a (n + 1) = harmonic (n + 1) - R.log ((n + 1 : Nat) : R) := by rw [had]
    rw [← hA]
    constructor
    · grind
    · have hn0 : (0 : R) ≤ ((n + 1 : Nat) : R) := natCast_nonneg' _
      have := OrderedRing.mul_le_mul_of_nonneg_left (show a (n + 1) - -L ≤ a (n + 1) - b (n + 1) by
        grind) hn0
      grind

/-! ## Stirling's formula with a bounded error -/

/-- **Stirling, bounded form.** For `M ≥ 1`:
`3/4 ≤ log M! + M − (M + ½) log M ≤ 1`. -/
theorem stirling_bounds {M : Nat} (hM : 1 ≤ M) :
    3 / 4 ≤ R.log (Arith.fact M : R) + (M : R) - ((M : R) + 1 / 2) * R.log (M : R) ∧
      R.log (Arith.fact M : R) + (M : R) - ((M : R) + 1 / 2) * R.log (M : R) ≤ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  have e : R.log (Arith.fact (n + 1) : R) + ((n + 1 : Nat) : R) -
      (((n + 1 : Nat) : R) + 1 / 2) * R.log ((n + 1 : Nat) : R) = Foundations.Topology.Stirling.s n := by
    show _ = Foundations.Topology.Stirling.d (n + 1)
    unfold Foundations.Topology.Stirling.d; rw [arith_fact_eq]
  have hs0 : Foundations.Topology.Stirling.s 0 = 1 := by
    show Foundations.Topology.Stirling.d 1 = 1
    unfold Foundations.Topology.Stirling.d
    rw [show (R.fact 1 : R) = 1 by rfl, show ((1 : Nat) : R) = 1 by grind, R.log_one]; grind
  rw [e]
  have hlow := Foundations.Topology.Stirling.s_lower n
  have hup : Foundations.Topology.Stirling.s n ≤ Foundations.Topology.Stirling.s 0 := by
    have := mono_le (a := fun j => -Foundations.Topology.Stirling.s j)
      (fun j => by have := Foundations.Topology.Stirling.s_anti j
                   show -Foundations.Topology.Stirling.s j ≤ -Foundations.Topology.Stirling.s (j + 1)
                   grind) (Nat.zero_le n)
    have h' : -Foundations.Topology.Stirling.s 0 ≤ -Foundations.Topology.Stirling.s n := this
    grind
  rw [hs0] at hlow hup
  constructor <;> grind

/-! ## Chebyshev's identity -/

/-- Counting: `#{1 ≤ n ≤ M : q n ≤ M} = ⌊M/q⌋` for `q ≥ 1`. -/
theorem fsum_count_le_div {q : Nat} (hq : 1 ≤ q) (M : Nat) :
    fsum (fun n => if 1 ≤ n ∧ q * n ≤ M then (1 : R) else 0) (M + 1) = ((M / q : Nat) : R) := by
  rw [fsum_congr (b := fun n => if 1 ≤ n ∧ n ≤ M / q then (1 : R) else 0) (fun n _ => by
    have : (q * n ≤ M) ↔ (n ≤ M / q) := by
      rw [Nat.le_div_iff_mul_le hq, Nat.mul_comm]
    by_cases h : n ≤ M / q
    · simp only [this.2 h, h, and_true]
    · have h' : ¬ q * n ≤ M := fun h'' => h (this.1 h'')
      simp only [h, h', and_false])]
  rw [fsum_ite_const, countBelow_initial _ _ (by have := Nat.div_le_self M q; omega)]; grind

/-- `ψ(K)` as a double sum over any range `p, k ≤ M` with `K ≤ M`. -/
theorem psi_eq_ext {K M : Nat} (hKM : K ≤ M) :
    psi K = fsum (fun p => fsum (fun k =>
      if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ K then R.log (p : R) else 0) (M + 1)) (M + 1) := by
  unfold psi ppSum
  have hvan : ∀ p k, K + 1 ≤ p ∨ K + 1 ≤ k →
      (if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ K then R.log (p : R) else 0) = 0 := by
    intro p k hpk
    split
    · next h =>
      exfalso
      have hp2 := h.1.1
      have h1 : p ≤ p ^ k := by
        have := Nat.pow_le_pow_right (show 0 < p by omega) h.2.1; rwa [Nat.pow_one] at this
      have := lt_pow_self' hp2 k
      omega
    · rfl
  rw [fsum_congr_bound (show K + 1 ≤ M + 1 by omega) (fun p h1 _ => by
    rw [fsum_congr (b := fun _ => 0) (fun k _ => hvan p k (Or.inl h1)), fsum_zeros])]
  apply fsum_congr; intro p _
  exact fsum_congr_bound (show K + 1 ≤ M + 1 by omega) (fun k h1 _ => hvan p k (Or.inr h1))

/-- **Chebyshev's identity.** `Σ_{1 ≤ n ≤ M} ψ(⌊M/n⌋) = log M!`. -/
theorem sum_psi_div (M : Nat) :
    fsum (fun n => if 1 ≤ n then psi (M / n) else 0) (M + 1) = R.log (Arith.fact M : R) := by
  rw [log_fact_eq]
  rw [fsum_congr (b := fun n => fsum (fun p => fsum (fun k =>
      if 1 ≤ n ∧ Prime p ∧ 1 ≤ k ∧ p ^ k ≤ M / n then R.log (p : R) else 0) (M + 1)) (M + 1))
    (fun n _ => by
      by_cases hn : 1 ≤ n
      · simp only [hn, true_and, ↓reduceIte]; exact psi_eq_ext (Nat.div_le_self M n)
      · simp only [hn, false_and, ↓reduceIte]
        rw [fsum_congr (b := fun _ => 0) (fun p _ => fsum_zeros _), fsum_zeros])]
  rw [fsum_swap]
  unfold ppSum
  apply fsum_congr; intro p _
  rw [fsum_swap]
  apply fsum_congr; intro k _
  by_cases h : Prime p ∧ 1 ≤ k
  · have hq : 1 ≤ p ^ k := Nat.pow_pos (by have := h.1.1; omega)
    rw [fsum_congr (b := fun n => (if 1 ≤ n ∧ p ^ k * n ≤ M then (1 : R) else 0) * R.log (p : R))
      (fun n _ => by
        have hiff : 1 ≤ n → ((p ^ k ≤ M / n) ↔ (p ^ k * n ≤ M)) := fun hn =>
          Nat.le_div_iff_mul_le hn
        by_cases h2 : 1 ≤ n ∧ p ^ k * n ≤ M
        · simp only [h2, h.1, h.2, (hiff h2.1).2 h2.2, and_self, ↓reduceIte]; grind
        · have : ¬ (1 ≤ n ∧ Prime p ∧ 1 ≤ k ∧ p ^ k ≤ M / n) := fun h3 =>
            h2 ⟨h3.1, (hiff h3.1).1 h3.2.2.2⟩
          simp only [this, h2, ↓reduceIte]; grind)]
    rw [fsum_mul_const, fsum_count_le_div hq]
    by_cases h3 : p ^ k ≤ M
    · simp only [h.1, h.2, h3, and_self, ↓reduceIte]
    · simp only [h3, and_false, ↓reduceIte]
      rw [Nat.div_eq_of_lt (by omega)]; grind
  · rw [fsum_congr (b := fun _ => 0) (fun n _ => by
      have : ¬ (1 ≤ n ∧ Prime p ∧ 1 ≤ k ∧ p ^ k ≤ M / n) := fun h3 => h ⟨h3.2.1, h3.2.2.1⟩
      simp only [this, ↓reduceIte]), fsum_zeros]
    have : ¬ (Prime p ∧ 1 ≤ k ∧ p ^ k ≤ M) := fun h3 => h ⟨h3.1, h3.2.1⟩
    simp only [this, ↓reduceIte]

/-! ## A logarithmic average -/

/-- `log² N ≤ 4N` for `N ≥ 1`. -/
theorem log_sq_le {N : Nat} (hN : 1 ≤ N) : R.log (N : R) * R.log (N : R) ≤ 4 * (N : R) := by
  obtain ⟨t, ht1, ht2⟩ := exists_sqrt N
  have hl1 : R.log (N : R) ≤ 2 * R.log ((t + 1 : Nat) : R) := by
    have := log_ineq_of_pow_le (a := N) (b := t + 1) (k := 1) (l := 2) (by omega) (by omega)
      (by rw [Nat.pow_one, Nat.pow_two]; omega)
    grind
  have hl2 : R.log ((t + 1 : Nat) : R) ≤ (t : R) := by
    have := log_le_sub_one (one_le_natCast (n := t + 1) (by omega)); grind
  have h0 := log_natCast_nonneg hN
  have hle : R.log (N : R) ≤ 2 * (t : R) := by grind
  have k1 := OrderedRing.mul_le_mul_of_nonneg_left hle h0
  have k2 := OrderedRing.mul_le_mul_of_nonneg_right hle (natCast_nonneg' t)
  have k3 : ((t * t : Nat) : R) ≤ (N : R) := natCast_le' ht1
  rw [natCast_mul'] at k3
  grind

/-- The comparison function `h(t) = t · ((log N − log t)² + 2 (log N − log t) + 2)`, whose
derivative is `(log N − log t)²`. -/
noncomputable def avgH (N : Nat) (t : R) : R :=
  t * ((R.log (N : R) - R.log t) * (R.log (N : R) - R.log t) + 2 * (R.log (N : R) - R.log t) + 2)

/-- `h'(t) = (log N − log t)²` for `t > 0`. -/
theorem hasDerivAt_avgH (N : Nat) {t : R} (ht : 0 < t) :
    HasDerivAt (avgH N) ((R.log (N : R) - R.log t) * (R.log (N : R) - R.log t)) t := by
  have hL := (hasDerivAt_const (R.log (N : R)) t).sub (hasDerivAt_log ht)
  have hQ := ((hL.mul hL).add (hL.const_mul 2)).add (hasDerivAt_const 2 t)
  have h := (hasDerivAt_id t).mul hQ
  have e : 1 * ((R.log (N : R) - R.log t) * (R.log (N : R) - R.log t) +
      2 * (R.log (N : R) - R.log t) + 2) +
      t * (((0 - 1 / t) * (R.log (N : R) - R.log t) + (R.log (N : R) - R.log t) * (0 - 1 / t)) +
        2 * (0 - 1 / t) + 0) = (R.log (N : R) - R.log t) * (R.log (N : R) - R.log t) := by
    have : t ≠ 0 := by grind
    grind
  rw [e] at h
  exact h

/-- **The logarithmic average.** `Σ_{1 ≤ d ≤ N} log²(N/d) ≤ 6N` for `N ≥ 1`. -/
theorem sum_log_sq_le {N : Nat} (hN : 1 ≤ N) :
    fsum (fun d => if 1 ≤ d then R.log ((N : R) / (d : R)) * R.log ((N : R) / (d : R)) else 0)
      (N + 1) ≤ 6 * (N : R) := by
  have hN0 : (0 : R) < (N : R) := natCast_pos' hN
  -- Termwise comparison for `2 ≤ d ≤ N`.
  have step : ∀ d, 2 ≤ d → d ≤ N →
      R.log ((N : R) / (d : R)) * R.log ((N : R) / (d : R)) ≤
        avgH N (d : R) - avgH N ((d - 1 : Nat) : R) := by
    intro d hd2 hdN
    have hd0 : (0 : R) < (d : R) := natCast_pos' (by omega)
    have ec : ((d - 1 : Nat) : R) = (d : R) - 1 := by
      have : ((d - 1 + 1 : Nat) : R) = ((d - 1 : Nat) : R) + 1 := by grind
      rw [show d - 1 + 1 = d by omega] at this; grind
    have hd1 : (1 : R) ≤ ((d - 1 : Nat) : R) := one_le_natCast (by omega)
    rw [ec] at hd1 ⊢
    rw [log_div' hN0 hd0]
    let c := (R.log (N : R) - R.log (d : R)) * (R.log (N : R) - R.log (d : R))
    have hc0 : 0 ≤ R.log (N : R) - R.log (d : R) := by
      have := log_le_log hd0 (natCast_le' hdN); grind
    have hmono := monotone_of_deriv_nonneg (f := fun t => avgH N t - c * t)
      (f' := fun t => (R.log (N : R) - R.log t) * (R.log (N : R) - R.log t) - c)
      (a := (d : R) - 1) (b := (d : R))
      (fun t h1 _ => by
        have h := (hasDerivAt_avgH N (show 0 < t by grind)).sub
          ((hasDerivAt_id t).const_mul c)
        rw [show (R.log (N : R) - R.log t) * (R.log (N : R) - R.log t) - c * 1 =
          (R.log (N : R) - R.log t) * (R.log (N : R) - R.log t) - c by grind] at h
        exact h)
      (fun t h1 h2 => by
        have ht0 : 0 < t := by grind
        have h3 : R.log t ≤ R.log (d : R) := log_le_log ht0 h2
        have h4 : R.log (N : R) - R.log (d : R) ≤ R.log (N : R) - R.log t := by grind
        have := OrderedRing.mul_le_mul_of_nonneg_left h4 hc0
        have := OrderedRing.mul_le_mul_of_nonneg_right h4 (by grind : 0 ≤ R.log (N : R) - R.log t)
        show 0 ≤ _ - c; grind)
      (Std.le_refl _) (by grind : (d : R) - 1 ≤ (d : R)) (Std.le_refl _)
    grind
  -- Telescoping.
  have tele : ∀ M, 1 ≤ M → M ≤ N →
      fsum (fun d => if 2 ≤ d then avgH N (d : R) - avgH N ((d - 1 : Nat) : R) else 0) (M + 1) =
        avgH N (M : R) - avgH N 1 := by
    intro M hM1 _
    induction M with
    | zero => omega
    | succ M ih =>
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · simp only [fsum_succ, fsum_zero, show ¬ 2 ≤ 0 by omega, show ¬ 2 ≤ 0 + 1 by omega,
          ↓reduceIte]
        rw [show ((0 + 1 : Nat) : R) = 1 by grind]; grind
      · rw [fsum_succ, ih hM (by omega)]
        simp only [show 2 ≤ M + 1 by omega, ↓reduceIte, show M + 1 - 1 = M by omega]; grind
  have hT := tele N hN (Nat.le_refl N)
  have hHN : avgH N (N : R) = 2 * (N : R) := by unfold avgH; grind
  have hH1 : 0 ≤ avgH N 1 := by
    unfold avgH
    have := OrderedRing.mul_nonneg (show (0 : R) ≤ 1 by grind)
      (show 0 ≤ (R.log (N : R) - R.log 1 + 1) * (R.log (N : R) - R.log 1 + 1) by
        rcases abs_cases (R.log (N : R) - R.log 1 + 1) with h | h
        · exact OrderedRing.mul_nonneg h.1 h.1
        · have := OrderedRing.mul_pos (show 0 < -(R.log (N : R) - R.log 1 + 1) by grind)
            (show 0 < -(R.log (N : R) - R.log 1 + 1) by grind)
          grind)
    grind
  -- Combine: the `d = 1` term is `log² N ≤ 4N`.
  have hsplit : fsum (fun d => if 1 ≤ d then
      R.log ((N : R) / (d : R)) * R.log ((N : R) / (d : R)) else 0) (N + 1) ≤
      R.log (N : R) * R.log (N : R) +
        fsum (fun d => if 2 ≤ d then avgH N (d : R) - avgH N ((d - 1 : Nat) : R) else 0) (N + 1) := by
    have e1 : fsum (fun d => if d = 1 then R.log (N : R) * R.log (N : R) else 0) (N + 1) =
        R.log (N : R) * R.log (N : R) := by
      rw [fsum_ite_eq]; simp only [show 1 < N + 1 by omega, ↓reduceIte]
    rw [← e1, ← fsum_add]
    apply fsum_le_fsum'; intro d hd
    by_cases h1 : d = 1
    · subst h1
      simp only [Nat.le_refl, ↓reduceIte, show ¬ 2 ≤ 1 by omega]
      rw [show ((1 : Nat) : R) = 1 by grind, show (N : R) / 1 = (N : R) by grind]; grind
    · by_cases h2 : 2 ≤ d
      · simp only [h1, h2, show 1 ≤ d by omega, ↓reduceIte]
        have := step d h2 (by omega); grind
      · obtain rfl : d = 0 := by omega
        simp only [show ¬ 1 ≤ 0 by omega, show ¬ 2 ≤ 0 by omega, ↓reduceIte]; grind
  have := log_sq_le hN
  grind

end Foundations.NumberTheory.PNT
