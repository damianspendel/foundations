import Foundations.Langlands.Padic.QpAbs

/-!
# ℚₚ is complete

A sequence `(zₘ)` in ℚₚ is **Cauchy** for `|·|ₚ` if for every `k` its terms are eventually
within `p^(−k)` of each other, and it **converges** to `L` if eventually `|zₘ − L|ₚ ≤ p^(−k)`.
We prove that every Cauchy sequence in ℚₚ converges: ℚₚ is **complete**, and so (with ℚ dense
in it, not proved here) it is a completion of ℚ for `|·|ₚ` — the `p`-adic counterpart of ℝ.

The proof reduces to the completeness of ℤₚ (`Zp.complete`):

* the closed unit ball `{|q|ₚ ≤ 1}` of ℚₚ is exactly ℤₚ, and for `x ∈ ℤₚ`,
  `|x|ₚ ≤ p^(−k)` iff `x ≡ 0 (mod pᵏ)`;
* a Cauchy sequence is bounded, so after multiplying by a fixed power `pᴷ` its tail lies in ℤₚ,
  where `|·|ₚ`-Cauchy means Cauchy modulo powers of `p`;
* the limit in ℤₚ, divided by `pᴷ`, is the limit in ℚₚ.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- For `c ≥ 2`, integer powers are strictly increasing. -/
theorem zpow_lt_zpow {c : Q} (hc : 2 ≤ c) {a b : Int} (hab : a < b) : c ^ a < c ^ b := by
  have hc0 : c ≠ 0 := by grind
  have h1 := zpow_le_zpow (show (1 : Q) ≤ c by grind) (show a + 1 ≤ b by omega)
  rw [Field.zpow_add_one hc0] at h1
  have hpos := zpow_pos (show (0 : Q) < c by grind) a
  have := OrderedRing.mul_le_mul_of_nonneg_left hc (Std.le_of_lt hpos)
  grind

/-- For `c ≥ 2`: `c^(−a) ≤ c^(−b)` iff `b ≤ a`. -/
theorem zpow_neg_le_iff {c : Q} (hc : 2 ≤ c) {a b : Int} : c ^ (-a) ≤ c ^ (-b) ↔ b ≤ a := by
  constructor
  · intro h; apply Classical.byContradiction; intro hn
    have := zpow_lt_zpow hc (show -b < -a by omega); grind
  · intro h; exact zpow_le_zpow (by grind) (by omega)

namespace Zp

variable {p : Nat}

/-- Congruence is congruence of the difference to `0`. -/
theorem modPow_iff_sub {k : Nat} {x y : Zp p} : ModPow k x y ↔ ModPow k (x - y) 0 := by
  induction x using ind with | h a => ?_
  induction y using ind with | h b => ?_
  show _ ∣ a.seq k - b.seq k ↔ _ ∣ (a.seq k + -b.seq k) - ((0 : Nat) : Int)
  rw [show a.seq k + -b.seq k - ((0 : Nat) : Int) = a.seq k - b.seq k by omega]

/-- `x ≡ 0 (mod pᵏ)` iff `k ≤ v(x)`, for `x ≠ 0`. -/
theorem modPow_zero_iff (hp : Prime p) {x : Zp p} (hx : x ≠ 0) {k : Nat} :
    ModPow k x 0 ↔ k ≤ val hp x := by
  obtain ⟨u, hu, hxu⟩ := val_spec hp hx
  generalize val hp x = v at hxu
  subst hxu
  induction u using ind with | h a => ?_
  have ha : ¬ (p : Int) ∣ a.seq 1 := fun h' => hu (modPow_mk.2 (by
    show _ ∣ a.seq 1 - 0; rw [Int.pow_one, Int.sub_zero]; exact h'))
  rw [pow_p_eq]
  show (p : Int) ^ k ∣ (p : Int) ^ v * a.seq k - ((0 : Nat) : Int) ↔ _
  rw [show ((0 : Nat) : Int) = 0 from rfl, Int.sub_zero]
  constructor
  · intro h; apply Classical.byContradiction; intro hlt
    have h' : (p : Int) ^ v * p ∣ (p : Int) ^ v * a.seq k := by
      rw [← Int.pow_succ]; exact Int.dvd_trans (Int.pow_dvd_pow_of_le' (by omega)) h
    exact not_dvd_seq ha (n := k) (by omega)
      (int_dvd_cancel (Int.pow_ne_zero (by have := hp.1; omega)) h')
  · intro h; exact Int.dvd_trans (Int.pow_dvd_pow_of_le' h) (Int.dvd_mul_right _ _)

end Zp

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- A prime is at least `2` in `ℚ`. -/
theorem two_le_p : (2 : Q) ≤ (p : Q) := two_le_prime hP.prime

/-- **The unit ball is ℤₚ, with precision.** For `x ∈ ℤₚ`: `|x|ₚ ≤ p^(−k)` iff
`x ≡ 0 (mod pᵏ)`. -/
theorem abs_ofZp_le_iff (x : Zp p) (k : Nat) :
    abs (ofZp x) ≤ (p : Q) ^ (-(k : Int)) ↔ Zp.ModPow k x 0 := by
  by_cases hx : x = 0
  · subst hx
    have : abs (ofZp (0 : Zp p)) = 0 := abs_eq_zero.2 rfl
    rw [this]
    refine ⟨fun _ => ?_, fun _ => Std.le_of_lt (zpow_pos (by have := two_le_p (p := p); grind) _)⟩
    show _ ∣ _ - _; rw [Int.sub_self]; exact Int.dvd_zero _
  · have hne : ofZp x ≠ 0 := fun h => hx (mk_eq_zero.1 h)
    rw [abs_of_ne hne, Zp.modPow_zero_iff hP.prime hx]
    unfold ofZp; rw [val_mk hx, zpow_neg_le_iff two_le_p]; omega

/-- **Elements of absolute value `≤ 1` are `p`-adic integers.** -/
theorem exists_ofZp_of_abs_le_one {q : Qp p} (hq : abs q ≤ 1) : ∃ x, q = ofZp x := by
  induction q using ind with | h x k => ?_
  by_cases hx : x = 0
  · exact ⟨0, mk_eq_mk.2 (by rw [hx]; grind)⟩
  have hne : mk x k ≠ 0 := fun h => hx (mk_eq_zero.1 h)
  rw [abs_of_ne hne, val_mk hx, show (1 : Q) = (p : Q) ^ (-(0 : Int)) from rfl,
    zpow_neg_le_iff two_le_p] at hq
  obtain ⟨u, _, hxu⟩ := Zp.val_spec hP.prime hx
  generalize Zp.val hP.prime x = v at hq hxu
  refine ⟨(p : Zp p) ^ (v - k) * u, mk_eq_mk.2 ?_⟩
  rw [hxu, show v = k + (v - k) by omega, Semiring.pow_add, Semiring.pow_zero]
  rw [show k + (v - k) - k = v - k by omega]; grind

/-- `|pᴷ|ₚ = p^(−K)`. -/
theorem abs_pow (K : Nat) : abs (ofZp ((p : Zp p) ^ K)) = (p : Q) ^ (-(K : Int)) := by
  have h1 : ((p : Zp p) ^ K) ≠ 0 := pow_ne_zero K
  rw [abs_of_ne (q := ofZp ((p : Zp p) ^ K)) (fun h => h1 (mk_eq_zero.1 h))]
  unfold ofZp
  rw [val_mk h1, show (p : Zp p) ^ K = (p : Zp p) ^ K * 1 by grind, val_pow_mul' _
    (Zp.one_ne_zero hP.prime.1), zp_val_one]
  congr 1

/-- A sequence in ℚₚ is **Cauchy** for `|·|ₚ`. -/
def IsCauchy (z : Nat → Qp p) : Prop :=
  ∀ k : Nat, ∃ N, ∀ m n, N ≤ m → N ≤ n → abs (z m - z n) ≤ (p : Q) ^ (-(k : Int))

/-- A sequence in ℚₚ **converges** to `L` for `|·|ₚ`. -/
def Converges (z : Nat → Qp p) (L : Qp p) : Prop :=
  ∀ k : Nat, ∃ N, ∀ m, N ≤ m → abs (z m - L) ≤ (p : Q) ^ (-(k : Int))

/-- **Completeness of ℚₚ.** Every Cauchy sequence in ℚₚ converges. -/
theorem complete (z : Nat → Qp p) (hz : IsCauchy z) : ∃ L, Converges z L := by
  have hp2 := two_le_p (p := p)
  have hp0 : (p : Q) ≠ 0 := by grind
  obtain ⟨N0, hN0⟩ := hz 0
  induction hzN : z N0 using ind with | h x0 K => ?_
  -- scale by `c = pᴷ`
  let c : Qp p := ofZp ((p : Zp p) ^ K)
  have hc : c ≠ 0 := fun h => pow_ne_zero (p := p) K (mk_eq_zero.1 h)
  have hcinv := Field.mul_inv_cancel hc
  have habs_c : abs c = (p : Q) ^ (-(K : Int)) := abs_pow K
  have hcle : abs c ≤ 1 := by
    rw [habs_c, show (1 : Q) = (p : Q) ^ (-(0 : Int)) from rfl, zpow_neg_le_iff hp2]; omega
  have hcpos : (0 : Q) ≤ abs c := abs_nonneg c
  have hcz : c * z N0 = ofZp x0 := by
    rw [hzN]; show mk _ (0 + K) = mk _ 0; apply mk_eq_mk.2
    simp only [Semiring.pow_zero]; grind
  -- the scaled tail lies in ℤₚ
  have hball : ∀ m, abs (c * z (m + N0)) ≤ 1 := by
    intro m
    have h1 := hN0 (m + N0) N0 (by omega) (Nat.le_refl _)
    rw [show ((0 : Nat) : Int) = 0 from rfl, show (p : Q) ^ (-(0 : Int)) = 1 from rfl] at h1
    have e : c * z (m + N0) = c * (z (m + N0) - z N0) + ofZp x0 := by rw [← hcz]; grind
    have h2 : abs (c * (z (m + N0) - z N0)) ≤ 1 := by
      rw [abs_mul]
      have := OrderedRing.mul_le_mul_of_nonneg_left h1 hcpos
      have := abs_nonneg (z (m + N0) - z N0)
      grind
    rw [e]
    rcases abs_ultrametric (c * (z (m + N0) - z N0)) (ofZp x0) with h | h
    · exact Std.le_trans h h2
    · exact Std.le_trans h (abs_ofZp_le_one x0)
  let y : Nat → Zp p := fun m => Classical.choose (exists_ofZp_of_abs_le_one (hball m))
  have hy : ∀ m, c * z (m + N0) = ofZp (y m) := fun m =>
    Classical.choose_spec (exists_ofZp_of_abs_le_one (hball m))
  -- `y` is Cauchy in ℤₚ
  have hyC : Zp.IsCauchy y := by
    intro k
    obtain ⟨N, hN⟩ := hz k
    refine ⟨N, fun m hm => ?_⟩
    apply Zp.modPow_iff_sub.2
    apply (abs_ofZp_le_iff _ k).1
    have e : ofZp (y m - y N) = c * (z (m + N0) - z (N + N0)) := by
      rw [show y m - y N = y m + (-1) * y N by grind, ofZp_add, ofZp_mul, ← hy, ← hy]
      rw [show ofZp (-1 : Zp p) = -1 from rfl]; grind
    rw [e, abs_mul]
    have h1 := hN (m + N0) (N + N0) (by omega) (by omega)
    have h2 := abs_nonneg (z (m + N0) - z (N + N0))
    have := OrderedRing.mul_le_mul_of_nonneg_right hcle h2
    grind
  obtain ⟨L', hL'⟩ := Zp.complete y hyC
  refine ⟨c⁻¹ * ofZp L', fun k => ?_⟩
  obtain ⟨N, hN⟩ := hL' (k + K)
  refine ⟨N + N0, fun m hm => ?_⟩
  have h1 := (abs_ofZp_le_iff _ (k + K)).2 (Zp.modPow_iff_sub.1 (hN (m - N0) (by omega)))
  have e : ofZp (y (m - N0) - L') = c * (z m - c⁻¹ * ofZp L') := by
    rw [show y (m - N0) - L' = y (m - N0) + (-1) * L' by grind, ofZp_add, ofZp_mul, ← hy,
      show m - N0 + N0 = m by omega, show ofZp (-1 : Zp p) = -1 from rfl]
    grind
  rw [e, abs_mul, habs_c] at h1
  -- divide by `p^(−K)`
  have hpk := zpow_pos (show (0 : Q) < p by grind) (K : Int)
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left h1 (Std.le_of_lt hpk)
  rw [← Semiring.mul_assoc, ← Field.zpow_add hp0, ← Field.zpow_add hp0,
    show (K : Int) + -(K : Int) = 0 by omega, Field.zpow_zero,
    show (K : Int) + -(((k + K : Nat) : Int)) = -(k : Int) by omega] at h2
  grind

end Qp

end Foundations.Langlands.Padic
