import Foundations.NumberTheory.PNTTauberianA

/-!
# Toward the prime number theorem XIII: the averaging machinery

Divided by `N`, the iterated Selberg inequality reads

  `|V(N)| log² N ≤ Σ_{k ≤ N} (a(k)/k) |V(⌊N/k⌋)| + O(log N)`,

a weighted average of `|V|` with weights `a(k)/k` of total `log² N + O(log N)`. To show that
this average is noticeably below `sup |V|`, we exhibit many `k` for which `⌊N/k⌋` falls into one
of the good intervals of the previous file, and show that their weights add up to a positive
proportion of `log² N`. This file provides the tools:

* the **normalised inequality** above;
* **peeling disjoint blocks**: for non-negative terms, the sum over all `k ≤ N` dominates the sum
  of the partial sums over disjoint ranges `(lo_j, hi_j]`;
* a **block lower bound**: if `⌊N/k⌋` should lie in `[m, m + ⌊m/T⌋]`, the range
  `k ∈ (⌊N/(m + ⌊m/T⌋)⌋, ⌊N/m⌋]` carries weight `Σ a(k)/k ≥ log N/(8T) − 2 KA` — Selberg's
  formula again, now as a *lower* bound for the density of the weights `a(k)` in short ranges;
* the **tail bound** `Σ_{N/Y < k ≤ N} a(k)/k ≤ Y (2 log N + KA)`, controlling the `k` for which
  `⌊N/k⌋` is too small for any information about `V`;
* **logarithmic counting** of blocks: `b^J ≤ X < b^{J+1}` for some `J`.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- **The normalised iterated inequality.** For `N ≥ 1`,
`|V(N)| log² N ≤ Σ_{k ≤ N} (a(k)/k) |V(⌊N/k⌋)| + 2K₁ log N + C₀ log 1024`. -/
theorem normalized_ineq {N : Nat} (hN : 1 ≤ N) :
    abs (vrem N) * (R.log (N : R) * R.log (N : R)) ≤
      fsum (fun k => selA k * (1 / (k : R)) * abs (vrem (N / k))) (N + 1) +
        (2 * K1 * R.log (N : R) + C0 * R.log 1024) := by
  have hN0 : (0 : R) < (N : R) := natCast_pos' hN
  have h := iterated_ineq hN
  -- Each `a(k) |R(⌊N/k⌋)| ≤ N (a(k)/k) |V(⌊N/k⌋)|`.
  have hterm : fsum (fun k => selA k * abs (rem (N / k))) (N + 1) ≤
      (N : R) * fsum (fun k => selA k * (1 / (k : R)) * abs (vrem (N / k))) (N + 1) := by
    rw [← fsum_const_mul]; apply fsum_le_fsum'; intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [selA_zero]; grind
    · have hQ : 1 ≤ N / k := (Nat.le_div_iff_mul_le hk1).2 (by omega)
      rw [rem_eq_mul hQ, abs_mul, abs_of_nonneg (natCast_nonneg' _)]
      have hk0 : (0 : R) < (k : R) := natCast_pos' hk1
      have hQk : ((N / k : Nat) : R) ≤ (N : R) * (1 / (k : R)) := by
        have h1 : ((N / k * k : Nat) : R) ≤ (N : R) := natCast_le' (Nat.div_mul_le_self N k)
        rw [natCast_mul'] at h1
        apply le_of_mul_le_mul_right' (C := (k : R)) _ hk0
        have : (k : R) ≠ 0 := by grind
        have e : (N : R) * (1 / (k : R)) * (k : R) = (N : R) := by grind
        rw [e]; exact h1
      have := OrderedRing.mul_le_mul_of_nonneg_right hQk (abs_nonneg (vrem (N / k)))
      have := OrderedRing.mul_le_mul_of_nonneg_left this (selA_nonneg k)
      grind
  have hrem : abs (rem N) = (N : R) * abs (vrem N) := by
    rw [rem_eq_mul hN, abs_mul, abs_of_nonneg (natCast_nonneg' N)]
  rw [hrem] at h
  apply le_of_mul_le_mul_right' (C := (N : R)) _ hN0
  unfold C0
  generalize fsum (fun k => selA k * abs (rem (N / k))) (N + 1) = S1 at h hterm
  generalize fsum (fun k => selA k * (1 / (k : R)) * abs (vrem (N / k))) (N + 1) = S2 at hterm ⊢
  grind

/-! ## Peeling disjoint blocks -/

/-- **Peeling.** If `g ≥ 0` on `[0, N]` and the ranges `(lo_j, hi_j]` are disjoint and decreasing
(`hi_{j+1} ≤ lo_j ≤ hi_j`, `hi_0 ≤ N`), then
`Σ_{j < J} Σ_{lo_j < k ≤ hi_j} g(k) ≤ Σ_{k ≤ N} g(k)` (block sums written as differences of
partial sums). -/
theorem peel_blocks (g : Nat → R) {N : Nat} (hg : ∀ k, k ≤ N → 0 ≤ g k) (lo hi : Nat → Nat)
    (hlh : ∀ j, lo j ≤ hi j) (hdec : ∀ j, hi (j + 1) ≤ lo j) (h0 : hi 0 ≤ N) (J : Nat) :
    fsum (fun j => fsum g (hi j + 1) - fsum g (lo j + 1)) J ≤ fsum g (N + 1) := by
  have hmono : ∀ a b, a ≤ b → b ≤ N → fsum g (a + 1) ≤ fsum g (b + 1) := by
    intro a b hab hbN
    have e : fsum g (b + 1) = fsum g (a + 1) + fsum (fun k => g (a + 1 + k)) (b - a) := by
      rw [← fsum_split]; congr 1; omega
    have := fsum_nonneg' (a := fun k => g (a + 1 + k)) (n := b - a) (fun k hk => hg _ (by omega))
    rw [e]; grind
  have hhiN : ∀ j, hi j ≤ N := by
    intro j; induction j with
    | zero => exact h0
    | succ j ih => have := hdec j; have := hlh j; omega
  -- `Σ_{j < J+1} ≤ F(hi 0) − F(lo J)`.
  have key : ∀ J, fsum (fun j => fsum g (hi j + 1) - fsum g (lo j + 1)) (J + 1) ≤
      fsum g (hi 0 + 1) - fsum g (lo J + 1) := by
    intro J; induction J with
    | zero => simp only [fsum_succ, fsum_zero]; grind
    | succ J ih =>
      rw [fsum_succ]
      have := hmono (hi (J + 1)) (lo J) (hdec J) (by have := hlh J; have := hhiN J; omega)
      grind
  have hF0 : 0 ≤ fsum g (0 + 1) := by
    simp only [fsum_succ, fsum_zero]; have := hg 0 (by omega); grind
  rcases J with _ | J
  · simp only [fsum_zero]
    have := hmono 0 N (by omega) (Nat.le_refl N); grind
  · have h1 := key J
    have h2 := hmono 0 (lo J) (by omega) (by have := hlh J; have := hhiN J; omega)
    have h3 := hmono (hi 0) N h0 (Nat.le_refl N)
    grind

/-! ## The weight of a block -/

/-- A block sum of the weights: `Σ_{lo < k ≤ hi} a(k)/k ≥ (A(hi) − A(lo))/hi`, in multiplied
form, for `1 ≤ hi`, `lo ≤ hi`. -/
theorem block_weight_ge {lo hi : Nat} (_hhi : 1 ≤ hi) (hlh : lo ≤ hi) :
    bigA hi - bigA lo ≤ (hi : R) *
      (fsum (fun k => selA k * (1 / (k : R))) (hi + 1) -
        fsum (fun k => selA k * (1 / (k : R))) (lo + 1)) := by
  rw [bigA_sub hlh, show hi + 1 = (lo + 1) + (hi - lo) by omega, fsum_split]
  rw [show fsum (fun k => selA k * (1 / (k : R))) (lo + 1) +
    fsum (fun k => selA (lo + 1 + k) * (1 / ((lo + 1 + k : Nat) : R))) (hi - lo) -
    fsum (fun k => selA k * (1 / (k : R))) (lo + 1) =
    fsum (fun k => selA (lo + 1 + k) * (1 / ((lo + 1 + k : Nat) : R))) (hi - lo) by grind,
    ← fsum_const_mul]
  apply fsum_le_fsum'; intro j hj
  have hk0 : (0 : R) < ((lo + 1 + j : Nat) : R) := natCast_pos' (by omega)
  have hkh : ((lo + 1 + j : Nat) : R) ≤ (hi : R) := natCast_le' (by omega)
  have ha := selA_nonneg (lo + 1 + j)
  have e : (hi : R) * (selA (lo + 1 + j) * (1 / ((lo + 1 + j : Nat) : R))) =
      selA (lo + 1 + j) * ((hi : R) / ((lo + 1 + j : Nat) : R)) := by grind
  rw [e]
  have h1 : 1 ≤ (hi : R) / ((lo + 1 + j : Nat) : R) := by
    apply le_of_mul_le_mul_right' (C := ((lo + 1 + j : Nat) : R)) _ hk0
    have : ((lo + 1 + j : Nat) : R) ≠ 0 := by grind
    have e2 : (hi : R) / ((lo + 1 + j : Nat) : R) * ((lo + 1 + j : Nat) : R) = (hi : R) := by grind
    rw [e2]; grind
  have := OrderedRing.mul_le_mul_of_nonneg_left h1 ha
  grind

/-- `t log t` is monotone on the naturals: `lo log lo ≤ lo log hi ≤ hi log hi`-type estimate
`2 hi log hi − 2 lo log lo ≥ 2 (hi − lo) log hi`. -/
theorem nlogn_diff {lo hi : Nat} (_hhi : 1 ≤ hi) (hlh : lo ≤ hi) :
    2 * ((hi : R) - (lo : R)) * R.log (hi : R) ≤
      2 * (hi : R) * R.log (hi : R) - 2 * (lo : R) * R.log (lo : R) := by
  rcases Nat.eq_zero_or_pos lo with rfl | hlo
  · rw [show ((0 : Nat) : R) = 0 by grind]; grind
  · have := log_le_log (natCast_pos' hlo) (natCast_le' hlh)
    have := OrderedRing.mul_le_mul_of_nonneg_left this (natCast_nonneg' lo)
    grind

/-- The partial sums `F(x) = Σ_{k ≤ x} a(k)/k` of the weights. -/
noncomputable def wsum (x : Nat) : R := fsum (fun k => selA k * (1 / (k : R))) (x + 1)

/-- Arithmetic of a block: with `hi = ⌊N/m⌋`, `lo = ⌊N/(m + ⌊m/T⌋)⌋`, if `2T ≤ m` and
`64 T² m² ≤ N` then `hi ≤ 8T (hi − lo)` and `N ≤ hi²` (and `1 ≤ hi`). -/
theorem block_arith {N m T : Nat} (hT : 1 ≤ T) (hm : 2 * T ≤ m)
    (hN : 64 * (T * T) * (m * m) ≤ N) :
    1 ≤ N / m ∧ N / (m + m / T) ≤ N / m ∧
      N / m + 8 * T * (N / (m + m / T)) ≤ 8 * T * (N / m) ∧ N ≤ N / m * (N / m) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hi, hhi⟩ : ∃ hi, hi = N / m := ⟨_, rfl⟩
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = N / (m + m / T) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = m / T := ⟨_, rfl⟩
  rw [← hhi, ← hlo]; rw [← hd] at hlo
  -- Basic facts.
  have f1 : hi * m ≤ N := by rw [hhi]; exact Nat.div_mul_le_self N m
  have f2 : N < hi * m + m := by
    have := Nat.div_add_mod N m; have := Nat.mod_lt N (show 0 < m by omega)
    rw [hhi]; grind
  have f3 : lo * (m + d) ≤ N := by rw [hlo]; exact Nat.div_mul_le_self N (m + d)
  have f4 : m ≤ 2 * (T * d) := by
    have := Nat.div_add_mod m T; have := Nat.mod_lt m (show 0 < T by omega)
    rw [hd]; omega
  have hTT : 1 ≤ T * T := Nat.mul_le_mul hT hT
  have f5 : 64 * m ≤ N := by
    have : 64 * m ≤ 64 * (T * T) * (m * m) := by
      have h1 : m ≤ m * m := Nat.le_mul_of_pos_right m (by omega)
      have h2 : 1 * m ≤ (T * T) * (m * m) := Nat.mul_le_mul hTT h1
      grind
    omega
  -- `hi ≥ 64 T² m ≥ 4T`.
  have f6 : 64 * (T * T) * m ≤ hi := by
    have : 64 * (T * T) * m * m < (hi + 1) * m := by
      have e : 64 * (T * T) * m * m = 64 * (T * T) * (m * m) := by grind
      have e2 : (hi + 1) * m = hi * m + m := by grind
      omega
    have h' : 64 * (T * T) * m < hi + 1 := Nat.lt_of_mul_lt_mul_right this
    omega
  have f7 : 4 * T ≤ hi := by
    have : 4 * T ≤ 64 * (T * T) * m := by
      have h1 : T ≤ T * T := Nat.le_mul_of_pos_right T (by omega)
      have h2 : T * T ≤ T * T * m := Nat.le_mul_of_pos_right _ (by omega)
      grind
    omega
  have hhi1 : 1 ≤ hi := by omega
  refine ⟨hhi1, ?_, ?_, ?_⟩
  · rw [hlo, hhi]; exact Nat.div_le_div_left (by omega) (by omega)
  · -- `lo (2T+1) < 2T (hi + 1)`.
    have g1 : lo * (2 * T + 1) * m < 2 * T * (hi + 1) * m := by
      have a1 : (2 * T + 1) * m ≤ 2 * T * (m + d) := by
        have e1 : (2 * T + 1) * m = 2 * (T * m) + m := by grind
        have e2 : 2 * T * (m + d) = 2 * (T * m) + 2 * (T * d) := by grind
        omega
      have a2 := Nat.mul_le_mul_left lo a1
      have a3 := Nat.mul_le_mul_left (2 * T) f3
      have a4 : 2 * T * N < 2 * T * (hi * m + m) := Nat.mul_lt_mul_of_pos_left f2 (by omega)
      have e3 : lo * (2 * T + 1) * m = lo * ((2 * T + 1) * m) := by grind
      have e4 : lo * (2 * T * (m + d)) = 2 * T * (lo * (m + d)) := by grind
      have e5 : 2 * T * (hi + 1) * m = 2 * T * (hi * m + m) := by grind
      omega
    have g2 := Nat.lt_of_mul_lt_mul_right g1
    -- Multiply by `8T` and compare with `(hi + 8T lo)(2T+1) ≤ 8T hi (2T+1)`.
    have g3 : (hi + 8 * T * lo) * (2 * T + 1) ≤ 8 * T * hi * (2 * T + 1) := by
      have b1 := Nat.mul_le_mul_left (8 * T) (show lo * (2 * T + 1) + 1 ≤ 2 * T * (hi + 1) by omega)
      have b2 : 4 * (T * T) ≤ T * hi := by
        have := Nat.mul_le_mul_left T f7; grind
      have b3 : hi ≤ 2 * (T * hi) := by
        have := Nat.mul_le_mul_right hi hT; grind
      have e6 : (hi + 8 * T * lo) * (2 * T + 1) = 2 * (T * hi) + hi + 8 * T * (lo * (2 * T + 1)) := by
        grind
      have e7 : 8 * T * hi * (2 * T + 1) = 16 * (T * (T * hi)) + 8 * (T * hi) := by grind
      have e8 : 8 * T * (2 * T * (hi + 1)) = 16 * (T * (T * hi)) + 16 * (T * T) := by grind
      have e9 : 8 * T * (lo * (2 * T + 1) + 1) = 8 * T * (lo * (2 * T + 1)) + 8 * T := by grind
      omega
    have := Nat.le_of_mul_le_mul_right g3 (show 0 < 2 * T + 1 by omega)
    grind
  · -- `hi² ≥ 64 m hi ≥ 64 (N − m) ≥ N`.
    have c0 : 64 * m ≤ 64 * (T * T) * m := by
      have := Nat.mul_le_mul_right m hTT; grind
    have c1 : hi * (64 * m) ≤ hi * hi := Nat.mul_le_mul_left hi (by omega)
    have e : hi * (64 * m) = 64 * (hi * m) := by grind
    omega

/-- **The weight of a block.** If `1 ≤ T`, `2T ≤ m` and `64 T² m² ≤ N`, then the `k` with
`⌊N/(m + ⌊m/T⌋)⌋ < k ≤ ⌊N/m⌋` carry weight `Σ a(k)/k ≥ log N/(8T) − 2 KA`, in the form
`8T · Σ ≥ log N − 16 T KA`. -/
theorem block_lower {N m T : Nat} (hT : 1 ≤ T) (hm : 2 * T ≤ m)
    (hN : 64 * (T * T) * (m * m) ≤ N) :
    R.log (N : R) - 16 * (T : R) * KA ≤
      8 * (T : R) * (wsum (N / m) - wsum (N / (m + m / T))) := by
  obtain ⟨h1, h2, h3, h4⟩ := block_arith hT hm hN
  generalize N / m = hi at h1 h2 h3 h4 ⊢
  generalize N / (m + m / T) = lo at h2 h3 h4 ⊢
  have hhi0 : (0 : R) < (hi : R) := natCast_pos' h1
  have hT0 : (0 : R) < (T : R) := natCast_pos' hT
  have hN1 : 1 ≤ N := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hT hT) (Nat.mul_le_mul (show 1 ≤ m by omega)
      (show 1 ≤ m by omega))
    grind
  -- Real versions.
  have r1 : (hi : R) + 8 * (T : R) * (lo : R) ≤ 8 * (T : R) * (hi : R) := by
    have h3' : ((hi + 8 * T * lo : Nat) : R) ≤ ((8 * T * hi : Nat) : R) := natCast_le' h3
    rw [natCast_add', natCast_mul', natCast_mul', natCast_mul'] at h3'
    have e : ((8 : Nat) : R) = 8 := by grind
    rw [e] at h3'; grind
  have r2 : R.log (N : R) ≤ 2 * R.log (hi : R) := by
    have := log_ineq_of_pow_le (a := N) (b := hi) (k := 1) (l := 2) (by omega) h1
      (by rw [Nat.pow_one, Nat.pow_two]; exact h4)
    grind
  have r3 := block_weight_ge h1 h2
  have hA1 := bigA_bounds hi
  have hA2 := bigA_bounds lo
  rw [abs_le] at hA1 hA2
  have r5 := nlogn_diff h1 h2
  have hlo : (lo : R) ≤ (hi : R) := natCast_le' h2
  have hKA := KA_nonneg
  have k0 := OrderedRing.mul_le_mul_of_nonneg_left hlo hKA
  have hlhi := log_natCast_nonneg h1
  -- `8T (hi − lo) log hi ≥ hi log hi ≥ hi log N / 2`.
  have k1 := OrderedRing.mul_le_mul_of_nonneg_right
    (show (hi : R) ≤ 8 * (T : R) * ((hi : R) - (lo : R)) by grind) hlhi
  have k2 := OrderedRing.mul_le_mul_of_nonneg_left r2 (Std.le_of_lt hhi0)
  unfold wsum at ⊢
  generalize fsum (fun k => selA k * (1 / (k : R))) (hi + 1) -
    fsum (fun k => selA k * (1 / (k : R))) (lo + 1) = Δ at r3 ⊢
  -- `hi Δ ≥ 2 (hi − lo) log hi − 2 KA hi`.
  have k3 : 2 * ((hi : R) - (lo : R)) * R.log (hi : R) - 2 * KA * (hi : R) ≤ (hi : R) * Δ := by
    grind
  have k4 := OrderedRing.mul_le_mul_of_nonneg_left k3 (show 0 ≤ 8 * (T : R) by grind)
  apply le_of_mul_le_mul_right' (C := (hi : R)) _ hhi0
  grind

/-- **The tail.** For `Y ≥ 1`, `N ≥ 1`: `Σ_{N/Y < k ≤ N} a(k)/k ≤ Y (2 log N + KA)`. -/
theorem tail_weight {N Y : Nat} (hY : 1 ≤ Y) (hN : 1 ≤ N) :
    wsum N - wsum (N / Y) ≤ (Y : R) * (2 * R.log (N : R) + KA) := by
  have hN0 : (0 : R) < (N : R) := natCast_pos' hN
  have hle : N / Y ≤ N := Nat.div_le_self N Y
  have e : wsum N - wsum (N / Y) =
      fsum (fun j => selA (N / Y + 1 + j) * (1 / ((N / Y + 1 + j : Nat) : R))) (N - N / Y) := by
    unfold wsum
    have : fsum (fun k => selA k * (1 / (k : R))) (N + 1) =
        fsum (fun k => selA k * (1 / (k : R))) (N / Y + 1) +
        fsum (fun j => selA (N / Y + 1 + j) * (1 / ((N / Y + 1 + j : Nat) : R))) (N - N / Y) := by
      rw [← fsum_split]; congr 1; omega
    rw [this]; grind
  rw [e]
  -- Each `N/k ≤ Y`.
  have hterm : ∀ j, j < N - N / Y →
      (N : R) * (selA (N / Y + 1 + j) * (1 / ((N / Y + 1 + j : Nat) : R))) ≤
        (Y : R) * selA (N / Y + 1 + j) := by
    intro j _
    have hk : N ≤ (N / Y + 1 + j) * Y := by
      have := Nat.div_add_mod N Y; have := Nat.mod_lt N (show 0 < Y by omega)
      grind
    have hk0 : (0 : R) < ((N / Y + 1 + j : Nat) : R) :=
      natCast_pos' (Nat.lt_of_lt_of_le (Nat.succ_pos (N / Y)) (Nat.le_add_right _ _))
    have hkR : (N : R) ≤ ((N / Y + 1 + j : Nat) : R) * (Y : R) := by
      have h' : (N : R) ≤ (((N / Y + 1 + j) * Y : Nat) : R) := natCast_le' hk
      rw [natCast_mul'] at h'; exact h'
    have ha := selA_nonneg (N / Y + 1 + j)
    have e2 : (N : R) * (selA (N / Y + 1 + j) * (1 / ((N / Y + 1 + j : Nat) : R))) =
        selA (N / Y + 1 + j) * ((N : R) / ((N / Y + 1 + j : Nat) : R)) := by grind
    rw [e2]
    have h1 : (N : R) / ((N / Y + 1 + j : Nat) : R) ≤ (Y : R) := by
      apply le_of_mul_le_mul_right' (C := ((N / Y + 1 + j : Nat) : R)) _ hk0
      have : ((N / Y + 1 + j : Nat) : R) ≠ 0 := by grind
      have e3 : (N : R) / ((N / Y + 1 + j : Nat) : R) * ((N / Y + 1 + j : Nat) : R) = (N : R) := by
        grind
      rw [e3]; grind
    have := OrderedRing.mul_le_mul_of_nonneg_left h1 ha
    grind
  have hs := fsum_le_fsum' hterm
  rw [fsum_const_mul, fsum_const_mul, ← bigA_sub hle] at hs
  have hA := bigA_bounds N; rw [abs_le] at hA
  have hA0 : 0 ≤ bigA (N / Y) := by unfold bigA; exact fsum_nonneg selA_nonneg _
  have hY0 := natCast_nonneg' Y
  have k1 := OrderedRing.mul_le_mul_of_nonneg_left
    (show bigA N - bigA (N / Y) ≤ 2 * (N : R) * R.log (N : R) + KA * (N : R) by grind) hY0
  apply le_of_mul_le_mul_right' (C := (N : R)) _ hN0
  generalize fsum (fun j => selA (N / Y + 1 + j) * (1 / ((N / Y + 1 + j : Nat) : R))) (N - N / Y)
    = S at hs ⊢
  grind

/-- **Logarithmic counting.** For `b ≥ 2` and `X ≥ 1` there is `J` with `b^J ≤ X < b^(J+1)`. -/
theorem pow_bracket {b : Nat} (hb : 2 ≤ b) : ∀ X, 1 ≤ X → ∃ J, b ^ J ≤ X ∧ X < b ^ (J + 1) := by
  intro X
  induction X using Nat.strongRecOn with
  | _ X ih =>
    intro hX
    by_cases hXb : X < b
    · exact ⟨0, by simp; omega, by simpa using hXb⟩
    · have h1 : 1 ≤ X / b := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have h2 : X / b < X := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨J, hJ1, hJ2⟩ := ih (X / b) h2 h1
      refine ⟨J + 1, ?_, ?_⟩
      · rw [Nat.pow_succ]
        exact Nat.le_trans (Nat.mul_le_mul_right b hJ1) (Nat.div_mul_le_self X b)
      · rw [Nat.pow_succ]
        have := Nat.div_add_mod X b; have := Nat.mod_lt X (show 0 < b by omega)
        have h3 : X / b + 1 ≤ b ^ (J + 1) := hJ2
        have := Nat.mul_le_mul_right b h3
        have e : (X / b + 1) * b = b * (X / b) + b := by grind
        omega

end Foundations.NumberTheory.PNT
