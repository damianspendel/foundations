import Foundations.NumberTheory.RealCharacters

/-!
# `L(1, χ) ≠ 0` for real characters

We finish the argument begun in `RealCharacters`. Let `χ ≠ χ₀` be real and suppose
`L(1, χ) = 0`. Take `N = M²`. In

  `T(N) = Σ_{d ≤ N} χ(d)/√d · U(⌊N/d⌋)`,   `U(K) = Σ_{1 ≤ m ≤ K} 1/√m = 2√K + V(K)`,

where `V(K)` is non-increasing with values in `[−2, 0]` (compare the sum with `∫ dt/√t`):

* the **tail** `d > M` is a sum of `χ(d)` against the non-increasing weights `U(N/d)/√d`, so by
  Abel summation it is at most `2q · U(M)/√(M+1) ≤ 4q`;
* in the **head** `d ≤ M`, the main term `2M Σ_{d ≤ M} χ(d)/d` is `2M` times a tail of the series
  for `L(1, χ) = 0`, hence at most `4q`; replacing `√⌊N/d⌋` by `M/√d` costs at most `2/M` per
  term, `2` in all; and `Σ χ(d) V(N/d)/√d` is again handled by Abel summation, since
  `d ↦ V(⌊N/d⌋)` is monotone and bounded.

So `T(M²)` stays bounded, while `T(M²) ≥ log (M + 1)` because `r(n) ≥ 0` and `r(k²) ≥ 1`. This
contradiction shows `L(1, χ) ≠ 0`.
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Numbers Foundations.Numbers.Arith Lean.Grind
open Foundations.Numbers.C (ofReal)

attribute [local instance] Classical.propDecidable

/-! ## Square roots of integers -/

/-- `√` is monotone. -/
theorem sqrt_le_sqrt' {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : R.sqrt a ≤ R.sqrt b := by
  apply R.le_of_mul_self_le (R.sqrt_nonneg b)
  rw [(R.sqrt_spec ha).2, (R.sqrt_spec (by grind : 0 ≤ b)).2]; exact hab

/-- `√n · √n = n`. -/
theorem sqrt_natCast_mul_self (n : Nat) : R.sqrt (n : R) * R.sqrt (n : R) = (n : R) :=
  (R.sqrt_spec OrderedRing.natCast_nonneg).2

/-- `1/√(k+1) ≤ 2(√(k+1) − √k)`. -/
theorem one_div_sqrt_succ_le (k : Nat) :
    1 / R.sqrt ((k + 1 : Nat) : R) ≤ 2 * (R.sqrt ((k + 1 : Nat) : R) - R.sqrt (k : R)) := by
  have hs := sqrt_natCast_pos (show 0 < k + 1 by omega)
  have ht := R.sqrt_nonneg (k : R)
  have hs2 := sqrt_natCast_mul_self (k + 1)
  have ht2 := sqrt_natCast_mul_self k
  have hc : ((k + 1 : Nat) : R) = (k : R) + 1 := by grind
  have hk : (0 : R) ≤ (k : R) := OrderedRing.natCast_nonneg
  -- `√k √(k+1) ≤ k + 1/2`
  have hst : R.sqrt (k : R) * R.sqrt ((k + 1 : Nat) : R) ≤ (k : R) + 1 / 2 := by
    apply R.le_of_mul_self_le (by grind)
    have : R.sqrt (k : R) * R.sqrt ((k + 1 : Nat) : R) * (R.sqrt (k : R) * R.sqrt ((k + 1 : Nat) : R))
        = (k : R) * ((k : R) + 1) := by rw [← hc, ← hs2, ← ht2]; grind
    rw [this]; grind
  apply div_le_of_le_mul hs
  grind

/-- `2(√(k+2) − √(k+1)) ≤ 1/√(k+1)`. -/
theorem two_mul_sqrt_sub_le (k : Nat) :
    2 * (R.sqrt ((k + 2 : Nat) : R) - R.sqrt ((k + 1 : Nat) : R)) ≤ 1 / R.sqrt ((k + 1 : Nat) : R) := by
  have hs := sqrt_natCast_pos (show 0 < k + 1 by omega)
  have hu := R.sqrt_nonneg ((k + 2 : Nat) : R)
  have hs2 := sqrt_natCast_mul_self (k + 1)
  have hu2 := sqrt_natCast_mul_self (k + 2)
  have hc1 : ((k + 1 : Nat) : R) = (k : R) + 1 := by grind
  have hc2 : ((k + 2 : Nat) : R) = (k : R) + 2 := by grind
  have hk : (0 : R) ≤ (k : R) := OrderedRing.natCast_nonneg
  have hsu : R.sqrt ((k + 1 : Nat) : R) * R.sqrt ((k + 2 : Nat) : R) ≤ (k : R) + 3 / 2 := by
    apply R.le_of_mul_self_le (by grind)
    have : R.sqrt ((k + 1 : Nat) : R) * R.sqrt ((k + 2 : Nat) : R) *
        (R.sqrt ((k + 1 : Nat) : R) * R.sqrt ((k + 2 : Nat) : R)) = ((k : R) + 1) * ((k : R) + 2) := by
      rw [← hc1, ← hc2, ← hs2, ← hu2]; grind
    rw [this]; grind
  apply le_div_of_mul_le hs
  grind

/-- `1/√(d+1) ≤ 1/√d` for `d ≥ 1`. -/
theorem one_div_sqrt_succ_le_one_div_sqrt {d : Nat} (hd : 1 ≤ d) :
    1 / R.sqrt ((d + 1 : Nat) : R) ≤ 1 / R.sqrt (d : R) := by
  have h1 := sqrt_natCast_pos (show 0 < d by omega)
  have h2 := sqrt_natCast_pos (show 0 < d + 1 by omega)
  have h3 := sqrt_le_sqrt' (OrderedRing.natCast_nonneg) (natCast_le' (show d ≤ d + 1 by omega))
  apply le_div_of_mul_le h1
  rw [show 1 / R.sqrt ((d + 1 : Nat) : R) * R.sqrt (d : R) =
    R.sqrt (d : R) / R.sqrt ((d + 1 : Nat) : R) by grind]
  apply div_le_of_le_mul h2; grind

/-- `1/√d ≥ 0`. -/
theorem one_div_sqrt_nonneg (d : Nat) : 0 ≤ 1 / R.sqrt (d : R) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; rw [one_div_sqrt_zero]; grind
  · exact Std.le_of_lt (OF.div_pos (by grind) (sqrt_natCast_pos h))

/-! ## `U(K) = 2√K + V(K)` -/

/-- `U(K) ≤ 2√K`. -/
theorem Usum_le (K : Nat) : Usum K ≤ 2 * R.sqrt (K : R) := by
  induction K with
  | zero => unfold Usum; rw [gsum_succ, gsum_nil, one_div_sqrt_zero]
            have := R.sqrt_nonneg ((0 : Nat) : R); grind
  | succ K ih =>
    unfold Usum at ih ⊢; rw [gsum_succ]
    have := one_div_sqrt_succ_le K; grind

/-- `U(K) ≥ 2√(K+1) − 2`. -/
theorem Usum_ge (K : Nat) : 2 * R.sqrt ((K + 1 : Nat) : R) - 2 ≤ Usum K := by
  induction K with
  | zero =>
    unfold Usum; rw [gsum_succ, gsum_nil, one_div_sqrt_zero,
      show ((0 + 1 : Nat) : R) = (1 : Nat) by rfl, show ((1 : Nat) : R) = ((1 * 1 : Nat) : R) by rfl,
      sqrt_natCast_sq]; grind
  | succ K ih =>
    unfold Usum at ih ⊢; rw [gsum_succ]
    have := two_mul_sqrt_sub_le K; grind

/-- `U` is monotone. -/
theorem Usum_mono {K K' : Nat} (h : K ≤ K') : Usum K ≤ Usum K' := by
  unfold Usum; exact gsum_mono_of_nonneg one_div_sqrt_nonneg (by omega)

/-- `U(K) ≥ 0`. -/
theorem Usum_nonneg (K : Nat) : 0 ≤ Usum K := gsum_nonneg one_div_sqrt_nonneg _

/-- Products of non-negative quantities are monotone. -/
theorem mul_le_mul'' {a a' b b' : R} (h1 : a' ≤ a) (h2 : b' ≤ b) (h3 : 0 ≤ a') (h4 : 0 ≤ b) :
    a' * b' ≤ a * b := by
  have := OrderedRing.mul_le_mul_of_nonneg_left h2 h3
  have := OrderedRing.mul_le_mul_of_nonneg_right h1 h4
  grind

/-- `V(K) = U(K) − 2√K`. -/
noncomputable def Vsum (K : Nat) : R := Usum K - 2 * R.sqrt (K : R)

/-- `−2 ≤ V(K) ≤ 0`. -/
theorem Vsum_bounds (K : Nat) : -2 ≤ Vsum K ∧ Vsum K ≤ 0 := by
  unfold Vsum
  have h1 := Usum_le K
  have h2 := Usum_ge K
  have h3 := sqrt_le_sqrt' (OrderedRing.natCast_nonneg) (natCast_le' (show K ≤ K + 1 by omega))
  constructor <;> grind

/-- `V` is non-increasing. -/
theorem Vsum_anti {K K' : Nat} (h : K ≤ K') : Vsum K' ≤ Vsum K := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  induction c with
  | zero => grind
  | succ c ih =>
    apply Std.le_trans _ (ih (by omega))
    unfold Vsum Usum
    rw [show K + (c + 1) = K + c + 1 by omega, gsum_succ]
    have := one_div_sqrt_succ_le (K + c); grind

/-! ## Abel summation for a real character -/

variable {q : Nat} [NeZero q]

/-- Abel summation with the real values of a real character. -/
theorem abel_real {χ : Character (ZModUnits q)} (hχ : IsRealChar χ) (hne : χ ≠ Character.one)
    {b : Nat → R} {M : Nat} (hmono : ∀ n, M ≤ n → b (n + 1) ≤ b n) (hpos : ∀ n, M ≤ n → 0 ≤ b n)
    (K : Nat) (hK : M ≤ K) :
    OF.abs (gsum (fun n => rc χ n * b n) K - gsum (fun n => rc χ n * b n) M) ≤ 2 * (q : R) * b M := by
  have h := abel_bound (cabs_gsum_dchar_le χ hne) hmono hpos K hK
  have e : ∀ K, gsum (fun n => dchar χ n * ofReal (b n)) K = ofReal (gsum (fun n => rc χ n * b n) K) := by
    intro K; rw [ofReal_gsum]; apply gsum_congr; intro n _; rw [dchar_eq_ofReal hχ, ofReal_mul']
  rw [e, e, ← ofReal_sub', cabs_ofReal'] at h; exact h

/-- If `L(1, χ) = 0`: `|Σ_{n<M} χ(n)/n| ≤ 2q/M`. -/
theorem tail_real {χ : Character (ZModUnits q)} (hχ : IsRealChar χ) (hne : χ ≠ Character.one)
    (hL : Lone χ = 0) {M : Nat} (hM : 1 ≤ M) :
    OF.abs (gsum (fun n => rc χ n * (1 / (n : R))) M) ≤ 2 * (q : R) / (M : R) := by
  have h := (Lone_spec χ hne).2 M hM
  have e : lpart (dchar χ) M = ofReal (gsum (fun n => rc χ n * (1 / (n : R))) M) := by
    unfold lpart; rw [ofReal_gsum]; apply gsum_congr; intro n _; rw [dchar_eq_ofReal hχ, ofReal_mul']
  rw [hL, e] at h
  generalize gsum (fun n => rc χ n * (1 / (n : R))) M = x at h ⊢
  rw [show (0 : C) - ofReal x = ofReal (-x) from
    C.ext (by show (0 : R) - x = -x; grind) (by show (0 : R) - 0 = -0; grind), cabs_ofReal',
    R.abs_neg] at h
  exact h

/-- `|χ(n)| ≤ 1` for the real values. -/
theorem abs_rc_le {χ : Character (ZModUnits q)} (hχ : IsRealChar χ) (n : Nat) : OF.abs (rc χ n) ≤ 1 := by
  have := cabs_dchar_le χ n
  rw [dchar_eq_ofReal hχ, cabs_ofReal'] at this; exact this

/-! ## The upper bound -/

/-- `|Σ_{n<K} χ(n) w(n)| ≤ Σ_{n<K} |w(n)|`. -/
theorem abs_gsum_rc_le {χ : Character (ZModUnits q)} (hχ : IsRealChar χ) (w : Nat → R) (K : Nat) :
    OF.abs (gsum (fun n => rc χ n * w n) K) ≤ gsum (fun n => OF.abs (w n)) K := by
  induction K with
  | zero => show OF.abs (0 : R) ≤ 0; rw [R.abs_zero]; grind
  | succ K ih =>
    rw [gsum_succ, gsum_succ]
    have := OF.abs_add (gsum (fun n => rc χ n * w n) K) (rc χ K * w K)
    rw [OF.abs_mul] at this
    have := OrderedRing.mul_le_mul_of_nonneg_right (abs_rc_le hχ K) (OF.abs_nonneg (w K))
    grind

/-- **If `L(1, χ) = 0` for a real `χ ≠ χ₀`, then `T(M²) ≤ 16q + 2`.** -/
theorem Tsum_sq_le {χ : Character (ZModUnits q)} (hχ : IsRealChar χ) (hne : χ ≠ Character.one)
    (hL : Lone χ = 0) {M : Nat} (hM : 1 ≤ M) : Tsum χ (M * M) ≤ 16 * (q : R) + 2 := by
  have hq : (0 : R) ≤ (q : R) := OrderedRing.natCast_nonneg
  let N := M * M
  have hMR := natCast_pos' (show 0 < M by omega)
  let term : Nat → R := fun d => rc χ d * (1 / R.sqrt (d : R) * Usum (N / d))
  have hT : Tsum χ N = gsum term (N + 1) := by
    rw [Tsum_eq]; apply gsum_congr; intro d _; show _ = rc χ d * _; grind
  -- the tail `d > M`
  have htail : OF.abs (gsum term (N + 1) - gsum term (M + 1)) ≤ 4 * (q : R) := by
    have hle : M + 1 ≤ N + 1 := by have := Nat.le_mul_self M; omega
    have h := abel_real hχ hne (b := fun d => 1 / R.sqrt (d : R) * Usum (N / d)) (M := M + 1)
      (fun n hn => mul_le_mul'' (one_div_sqrt_succ_le_one_div_sqrt (by omega))
        (Usum_mono (Nat.div_le_div_left (by omega) (by omega))) (one_div_sqrt_nonneg _)
        (Usum_nonneg _))
      (fun n _ => OrderedRing.mul_nonneg (one_div_sqrt_nonneg n) (Usum_nonneg _))
      (N + 1) hle
    have hb : 1 / R.sqrt ((M + 1 : Nat) : R) * Usum (N / (M + 1)) ≤ 2 := by
        have h1 : N / (M + 1) ≤ M := Nat.div_le_of_le_mul (by
          show M * M ≤ (M + 1) * M; exact Nat.mul_le_mul_right M (by omega))
        have h2 := Std.le_trans (Usum_mono h1) (Usum_le M)
        have h3 := sqrt_le_sqrt' OrderedRing.natCast_nonneg (natCast_le' (show M ≤ M + 1 by omega))
        have h4 := sqrt_natCast_pos (show 0 < M + 1 by omega)
        rw [show 1 / R.sqrt ((M + 1 : Nat) : R) * Usum (N / (M + 1)) =
          Usum (N / (M + 1)) / R.sqrt ((M + 1 : Nat) : R) by grind]
        apply div_le_of_le_mul h4; grind
    have := OrderedRing.mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * (q : R) by grind)
    show OF.abs (gsum (fun n => rc χ n * (1 / R.sqrt (n : R) * Usum (N / n))) (N + 1) -
      gsum (fun n => rc χ n * (1 / R.sqrt (n : R) * Usum (N / n))) (M + 1)) ≤ _
    grind
  -- the head `d ≤ M`: decompose each term
  let g : Nat → R := fun d => Vsum (N / d)
  let δ : Nat → R := fun d => 2 * (M : R) * (1 / (d : R)) - 2 * R.sqrt ((N / d : Nat) : R) *
    (1 / R.sqrt (d : R))
  have hdec : gsum term (M + 1) = 2 * (M : R) * gsum (fun d => rc χ d * (1 / (d : R))) (M + 1) -
      gsum (fun d => rc χ d * δ d) (M + 1) + gsum (fun d => rc χ d * (g d * (1 / R.sqrt (d : R))))
        (M + 1) := by
    rw [← gsum_mul_left, ← gsum_sub', ← gsum_add]; apply gsum_congr; intro d _
    show rc χ d * (1 / R.sqrt (d : R) * Usum (N / d)) = _
    have : Usum (N / d) = Vsum (N / d) + 2 * R.sqrt ((N / d : Nat) : R) := by unfold Vsum; grind
    rw [this]; show _ = _ * (rc χ d * _) - rc χ d * (2 * (M : R) * (1 / (d : R)) -
      2 * R.sqrt ((N / d : Nat) : R) * (1 / R.sqrt (d : R))) + rc χ d * (Vsum (N / d) * _)
    grind
  -- (H1) the main term
  have hH1 : OF.abs (2 * (M : R) * gsum (fun d => rc χ d * (1 / (d : R))) (M + 1)) ≤ 4 * (q : R) := by
    have h := tail_real hχ hne hL (M := M + 1) (by omega)
    rw [OF.abs_mul, R.abs_of_nonneg (show (0 : R) ≤ 2 * (M : R) by grind)]
    have := OrderedRing.mul_le_mul_of_nonneg_left h (show (0 : R) ≤ 2 * (M : R) by grind)
    have hM1 := natCast_pos' (show 0 < M + 1 by omega)
    have e : 2 * (M : R) * (2 * (q : R) / ((M + 1 : Nat) : R)) ≤ 4 * (q : R) := by
      rw [show 2 * (M : R) * (2 * (q : R) / ((M + 1 : Nat) : R)) =
        4 * (q : R) * (M : R) / ((M + 1 : Nat) : R) by grind]
      apply div_le_of_le_mul hM1
      exact OrderedRing.mul_le_mul_of_nonneg_left (natCast_le' (show M ≤ M + 1 by omega))
        (show 0 ≤ 4 * (q : R) by grind)
    grind
  -- (H2) replacing `√⌊N/d⌋` by `M/√d`
  have hδ : ∀ d, d < M + 1 → OF.abs (δ d) ≤ if 1 ≤ d then 2 / (M : R) else 0 := by
    intro d hd
    rcases Nat.eq_zero_or_pos d with h0 | hd0
    · subst h0
      show OF.abs (2 * (M : R) * (1 / ((0 : Nat) : R)) - 2 * R.sqrt ((N / 0 : Nat) : R) *
        (1 / R.sqrt ((0 : Nat) : R))) ≤ _
      rw [one_div_sqrt_zero, show (1 : R) / ((0 : Nat) : R) = 0 by
        rw [show ((0 : Nat) : R) = 0 by grind, Field.div_eq_mul_inv, Field.inv_zero]; grind,
        ite_eq_right (by omega)]
      rw [show 2 * (M : R) * 0 - 2 * R.sqrt ((N / 0 : Nat) : R) * 0 = 0 by grind, R.abs_zero]; grind
    · rw [ite_eq_left (show 1 ≤ d by omega)]
      let s := R.sqrt (d : R)
      let k := N / d
      let t := R.sqrt (k : R)
      have hs0 : 0 < s := sqrt_natCast_pos hd0
      have hss : s * s = (d : R) := sqrt_natCast_mul_self d
      have ht0 : 0 ≤ t := R.sqrt_nonneg _
      have htt : t * t = (k : R) := sqrt_natCast_mul_self k
      let x := (M : R) * (1 / s)
      have hsne : s ≠ 0 := by grind
      have hdne : (d : R) ≠ 0 := by have := natCast_pos' hd0; grind
      have hx0 : 0 < x := OrderedRing.mul_pos hMR (OF.div_pos (by grind) hs0)
      have hxs : x * s = (M : R) := by show (M : R) * (1 / s) * s = _; grind
      have hxx : x * x = (N : R) / (d : R) := by
        show (M : R) * (1 / s) * ((M : R) * (1 / s)) = ((M * M : Nat) : R) / (d : R)
        rw [show ((M * M : Nat) : R) = (M : R) * (M : R) by grind, ← hss]; grind
      have hk1 : (k : R) ≤ x * x := by rw [hxx]; exact natDiv_le N hd0
      have hk2 : x * x ≤ (k : R) + 1 := by rw [hxx]; exact div_le_natDiv_add_one N hd0
      have htx : t ≤ x := R.le_of_mul_self_le (Std.le_of_lt hx0) (by grind)
      have hprod : (x - t) * x ≤ 1 := by
        have := OrderedRing.mul_le_mul_of_nonneg_left (show x ≤ x + t by grind)
          (show 0 ≤ x - t by grind)
        grind
      have hδs : δ d * s = 2 * (x - t) := by
        show (2 * (M : R) * (1 / (d : R)) - 2 * t * (1 / s)) * s = _
        rw [← hxs, ← hss]; grind
      have hδ0 : 0 ≤ δ d := by
        have := nonneg_of_mul_nonneg_left' hs0 (show 0 ≤ s * δ d by grind); exact this
      rw [R.abs_of_nonneg hδ0]
      apply le_div_of_mul_le hMR
      rw [← hxs]
      have := OrderedRing.mul_le_mul_of_nonneg_left hprod (show (0 : R) ≤ 2 by grind)
      have : δ d * s * x = 2 * (x - t) * x := by rw [hδs]
      grind
  have hH2 : OF.abs (gsum (fun d => rc χ d * δ d) (M + 1)) ≤ 2 := by
    apply Std.le_trans (abs_gsum_rc_le hχ δ (M + 1))
    apply Std.le_trans (gsum_le_gsum hδ)
    rw [gsum_ite_one_le]
    have : (M : R) ≠ 0 := by grind
    grind
  -- (H3) the term with `V`: Abel summation twice
  have hg_mono : ∀ a b, 1 ≤ a → a ≤ b → g a ≤ g b := fun a b ha hab =>
    Vsum_anti (Nat.div_le_div_left hab ha)
  have hgM := Vsum_bounds (N / M)
  have hg1 := Vsum_bounds (N / 1)
  have hB1 : OF.abs (gsum (fun d => rc χ d * (1 / R.sqrt (d : R))) (M + 1)) ≤ 2 * (q : R) := by
    have h := abel_real hχ hne (b := fun d => 1 / R.sqrt (d : R)) (M := 1)
      (fun n hn => one_div_sqrt_succ_le_one_div_sqrt hn) (fun n _ => one_div_sqrt_nonneg n)
      (M + 1) (by omega)
    have e1 : gsum (fun d => rc χ d * (1 / R.sqrt (d : R))) 1 = 0 := by
      rw [gsum_succ, gsum_nil, one_div_sqrt_zero]; grind
    have e2 : 1 / R.sqrt ((1 : Nat) : R) = 1 := by
      rw [show ((1 : Nat) : R) = ((1 * 1 : Nat) : R) from rfl, sqrt_natCast_sq]; grind
    rw [e1, e2] at h; grind
  let b' : Nat → R := fun d => if d ≤ M then (g M - g d) * (1 / R.sqrt (d : R)) else 0
  have hW2 : OF.abs (gsum (fun d => rc χ d * b' d) (M + 1)) ≤ 4 * (q : R) := by
    have h := abel_real hχ hne (b := b') (M := 1) (fun n hn => by
        show (if n + 1 ≤ M then _ else _) ≤ (if n ≤ M then _ else _)
        by_cases h1 : n + 1 ≤ M
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
          exact mul_le_mul'' (by have := hg_mono n (n + 1) hn (by omega); grind)
            (one_div_sqrt_succ_le_one_div_sqrt hn)
            (by have := hg_mono (n + 1) M (by omega) h1; grind) (one_div_sqrt_nonneg n)
        · rw [ite_eq_right h1]
          by_cases h2 : n ≤ M
          · rw [ite_eq_left h2]
            exact OrderedRing.mul_nonneg (by have := hg_mono n M hn h2; grind) (one_div_sqrt_nonneg n)
          · rw [ite_eq_right h2]; grind)
      (fun n hn => by
        show 0 ≤ (if n ≤ M then _ else _)
        by_cases h : n ≤ M
        · rw [ite_eq_left h]
          exact OrderedRing.mul_nonneg (by have := hg_mono n M hn h; grind) (one_div_sqrt_nonneg n)
        · rw [ite_eq_right h]; grind) (M + 1) (by omega)
    have e1 : gsum (fun d => rc χ d * b' d) 1 = 0 := by
      rw [gsum_succ, gsum_nil]
      show (0 : R) + rc χ 0 * (if 0 ≤ M then _ else _) = 0
      rw [ite_eq_left (Nat.zero_le M), one_div_sqrt_zero]; grind
    have e2 : b' 1 ≤ 2 := by
      show (if 1 ≤ M then _ else _) ≤ 2
      rw [ite_eq_left hM, show ((1 : Nat) : R) = ((1 * 1 : Nat) : R) from rfl, sqrt_natCast_sq]
      show (Vsum (N / M) - Vsum (N / 1)) * (1 / ((1 : Nat) : R)) ≤ 2
      rw [show ((1 : Nat) : R) = 1 by grind]; grind
    rw [e1] at h
    have := OrderedRing.mul_le_mul_of_nonneg_left e2 (show 0 ≤ 2 * (q : R) by grind)
    grind
  have hW : gsum (fun d => rc χ d * (g d * (1 / R.sqrt (d : R)))) (M + 1) =
      g M * gsum (fun d => rc χ d * (1 / R.sqrt (d : R))) (M + 1) - gsum (fun d => rc χ d * b' d) (M + 1) := by
    rw [← gsum_mul_left, ← gsum_sub']; apply gsum_congr; intro d hd
    show _ = _ - rc χ d * (if d ≤ M then _ else _)
    rw [ite_eq_left (show d ≤ M by omega)]; grind
  have hgMabs : OF.abs (g M) ≤ 2 := by
    rw [OF.abs_le]; show -2 ≤ Vsum (N / M) ∧ Vsum (N / M) ≤ 2; grind
  have hH3 : OF.abs (gsum (fun d => rc χ d * (g d * (1 / R.sqrt (d : R)))) (M + 1)) ≤ 8 * (q : R) := by
    rw [hW]
    have h1 := OF.abs_add (g M * gsum (fun d => rc χ d * (1 / R.sqrt (d : R))) (M + 1))
      (-gsum (fun d => rc χ d * b' d) (M + 1))
    rw [R.abs_neg, OF.abs_mul] at h1
    have h2 := mul_le_mul'' hgMabs hB1 (OF.abs_nonneg _) (show 0 ≤ 2 * (q : R) by grind)
    rw [show g M * gsum (fun d => rc χ d * (1 / R.sqrt (d : R))) (M + 1) +
      -gsum (fun d => rc χ d * b' d) (M + 1) = g M * gsum (fun d => rc χ d * (1 / R.sqrt (d : R)))
        (M + 1) - gsum (fun d => rc χ d * b' d) (M + 1) by grind] at h1
    grind
  -- assemble
  rw [show M * M = N from rfl, hT]
  have e : gsum term (N + 1) = (gsum term (N + 1) - gsum term (M + 1)) + gsum term (M + 1) := by grind
  rw [e, hdec]
  have a1 := (OF.le_abs (gsum term (N + 1) - gsum term (M + 1))).1
  have a2 := (OF.le_abs (2 * (M : R) * gsum (fun d => rc χ d * (1 / (d : R))) (M + 1))).1
  have a3 := (OF.le_abs (gsum (fun d => rc χ d * δ d) (M + 1))).2
  have a4 := (OF.le_abs (gsum (fun d => rc χ d * (g d * (1 / R.sqrt (d : R)))) (M + 1))).1
  grind

end Foundations.NumberTheory
