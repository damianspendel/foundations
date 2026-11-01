import Foundations.Numbers.FTC

/-!
# Analysis on the reals VIII: sine, cosine and π

Geometry defines sine and cosine by a circle and π by its circumference; but "arc length" and
"angle" presuppose the calculus. Following Euler (and the modern rigorous treatment), we turn
the order around and define the trigonometric functions by power series:

  `cos x = 1 − x²/2! + x⁴/4! − ⋯`,  `sin x = x − x³/3! + x⁵/5! − ⋯`.

Both are instances of a **power series `Σ cₙ xⁿ/n!` with bounded coefficients** `|cₙ| ≤ 1`; for
such series we prove convergence (by comparison with the exponential series) and **termwise
differentiation**: the derivative has coefficients `cₙ₊₁`, by the same quadratic estimate that
gave `exp' = exp`. The coefficient sequences of cosine and sine are `1, 0, −1, 0, 1, …` and
`0, 1, 0, −1, 0, …`; shifting one gives (minus) the other, so

  `sin' = cos`,  `cos' = −sin`,  and hence `sin² + cos² = 1`

(the derivative of `sin² + cos²` vanishes). A numerical estimate of the series shows
`cos 2 < 0`, and since `cos 0 = 1 > 0`, cosine has a **first positive zero** `p` — the supremum of
the points up to which cosine stays positive. We **define `π = 2p`**: the circle has not been
mentioned, yet this is the familiar number (`sin (π/2) = 1`, `0 < π ≤ 4`).
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-! ## Power series with bounded coefficients -/

/-- The `n`-th term `cₙ xⁿ / n!` of the power series with coefficients `c`. -/
noncomputable def pterm (c : Nat → R) (x : R) (n : Nat) : R := c n * expTerm x n

/-- `|xⁿ/n!| = |x|ⁿ/n!`. -/
theorem abs_expTerm (x : R) (n : Nat) : abs (expTerm x n) = expTerm (abs x) n := by
  unfold expTerm
  rw [abs_div_pos (fact_pos' n), abs_pow, Field.div_eq_mul_inv]

/-- The terms of a power series with `|cₙ| ≤ 1` are dominated by those of `exp |x|`. -/
theorem abs_pterm_le {c : Nat → R} (hc : ∀ n, abs (c n) ≤ 1) (x : R) (n : Nat) :
    abs (pterm c x n) ≤ expTerm (abs x) n := by
  unfold pterm
  rw [abs_mul, abs_expTerm]
  have := OrderedRing.mul_le_mul_of_nonneg_right (hc n) (expTerm_nonneg (abs_nonneg x) n)
  grind

/-- A power series with bounded coefficients converges everywhere. -/
theorem exists_hasSum_pterm {c : Nat → R} (hc : ∀ n, abs (c n) ≤ 1) (x : R) :
    ∃ s, HasSum (pterm c x) s := by
  obtain ⟨t, ht, -⟩ := comparison (fun n => abs_nonneg _) (abs_pterm_le hc x)
    (hasSum_exp (abs x))
  obtain ⟨s, hs, -⟩ := summable_of_abs ht
  exact ⟨s, hs⟩

/-- **The power series** `Σ cₙ xⁿ / n!` (its sum, where it converges). -/
noncomputable def pser (c : Nat → R) (x : R) : R :=
  open Classical in if h : ∃ s, HasSum (pterm c x) s then h.choose else 0

/-- For bounded coefficients, `pser c x` is the sum of the series. -/
theorem hasSum_pser {c : Nat → R} (hc : ∀ n, abs (c n) ≤ 1) (x : R) :
    HasSum (pterm c x) (pser c x) := by
  have h := exists_hasSum_pterm hc x
  unfold pser
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- The value at `0` is the constant coefficient. -/
theorem pser_zero {c : Nat → R} (hc : ∀ n, abs (c n) ≤ 1) : pser c 0 = c 0 := by
  have h : HasSum (pterm c 0) (c 0) := by
    apply (tendsto_const (c 0)).congr_eventually 1
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    induction k with
    | zero =>
      show c 0 = 0 + c 0 * ((0 : R) ^ 0 / ((1 : Nat) : R)); grind
    | succ k ih =>
      rw [fsum_succ, ← ih (by omega)]
      unfold pterm; rw [expTerm_succ]; grind
  exact (hasSum_pser hc 0).unique h

/-- The error term vanishes for `n = 0`. -/
theorem powErr_zero (x y : R) : powErr x y 0 = 0 := by
  unfold powErr; show y ^ 0 - x ^ 0 - ((0 : Nat) : R) * x ^ 0 * (y - x) = 0; grind

/-- The error term vanishes for `n = 1`. -/
theorem powErr_one (x y : R) : powErr x y 1 = 0 := by
  unfold powErr; show y ^ 0 * y - x ^ 0 * x - ((1 : Nat) : R) * x ^ 0 * (y - x) = 0; grind

/-- **Termwise differentiation.** A power series `Σ cₙ xⁿ/n!` with `|cₙ| ≤ 1` is differentiable
everywhere, and its derivative is the power series with the shifted coefficients `cₙ₊₁`. -/
theorem hasDerivAt_pser {c : Nat → R} (hc : ∀ n, abs (c n) ≤ 1) (x : R) :
    HasDerivAt (pser c) (pser (fun n => c (n + 1)) x) x := by
  let D := pser (fun n => c (n + 1)) x
  -- The termwise derivative `Σ cₙ n xⁿ⁻¹/n!` sums to `D`.
  have hD : HasSum (fun n => c n * derTerm x n) D := by
    apply hasSum_succ_iff.1
    have e0 : c 0 * derTerm x 0 = 0 := by
      unfold derTerm; show c 0 * (((0 : Nat) : R) * x ^ (0 - 1) / _) = 0; grind
    rw [e0, show D - 0 = D by grind]
    refine (hasSum_pser (fun n => hc (n + 1)) x).congr fun n => ?_
    unfold pterm derTerm expTerm
    rw [fact_succ', show n + 1 - 1 = n by omega]
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    have := OrderedRing.mul_pos (by grind : (0 : R) < (n : R) + 1) (fact_pos' n)
    have := fact_pos' n
    grind
  let M := abs x + 1
  have hE : 0 ≤ exp M := by
    have := one_add_le_exp (by have := abs_nonneg x; grind : 0 ≤ M)
    have := abs_nonneg x; grind
  refine hasDerivAt_of_quadratic (C := exp M / 2) (by grind) fun y hy => ?_
  have hx : abs x ≤ M := by grind
  have hyM : abs y ≤ M := by
    have := abs_add (y - x) x; rw [show y - x + x = y by grind] at this; grind
  -- The error series sums to `f y − f x − D (y − x)` …
  have h1 : HasSum (fun n => c n * (powErr x y n / (fact n : R)))
      (pser c y - pser c x - (y - x) * D) := by
    refine (((hasSum_pser hc y).sub (hasSum_pser hc x)).sub (hD.const_mul (y - x))).congr
      fun n => ?_
    unfold pterm expTerm derTerm powErr
    have := fact_pos' n
    grind
  -- … its first two terms vanish …
  have h2 : HasSum (fun n => c (2 + n) * (powErr x y (2 + n) / (fact (2 + n) : R)))
      (pser c y - pser c x - (y - x) * D) := by
    have := (hasSum_shift_iff (a := fun n => c n * (powErr x y n / (fact n : R))) 2).2 h1
    have e : fsum (fun n => c n * (powErr x y n / (fact n : R))) 2 = 0 := by
      rw [fsum_succ, fsum_succ, fsum_zero, powErr_zero, powErr_one]; grind
    rw [e, show pser c y - pser c x - (y - x) * D - 0 = pser c y - pser c x - (y - x) * D by
      grind] at this
    exact this
  -- … and the terms are dominated as for `exp`.
  have h3 : ∀ n, abs (c (2 + n) * (powErr x y (2 + n) / (fact (2 + n) : R))) ≤
      abs (y - x) * abs (y - x) / 2 * expTerm M n := fun n => by
    rw [abs_mul]
    have k := abs_powErr_div_le hx hyM n
    have := OrderedRing.mul_le_mul_of_nonneg_right (hc (2 + n)) (abs_nonneg
      (powErr x y (2 + n) / (fact (2 + n) : R)))
    grind
  have := abs_hasSum_le h3 h2 ((hasSum_exp M).const_mul (abs (y - x) * abs (y - x) / 2))
  rw [show pser c y - pser c x - (y - x) * D = pser c y - pser c x - D * (y - x) by grind] at this
  grind

/-- Power series with equal coefficients are equal. -/
theorem pser_congr {c c' : Nat → R} (h : ∀ n, c n = c' n) : pser c = pser c' := by
  have : c = c' := funext h
  rw [this]

/-- Negating the coefficients negates the series. -/
theorem pser_neg {c : Nat → R} (hc : ∀ n, abs (c n) ≤ 1) (x : R) :
    pser (fun n => -c n) x = -pser c x := by
  have hc' : ∀ n, abs (-c n) ≤ 1 := fun n => by rw [abs_neg]; exact hc n
  have h := (hasSum_pser hc x).const_mul (-1)
  have h' : HasSum (pterm (fun n => -c n) x) (-1 * pser c x) :=
    h.congr fun n => by unfold pterm; grind
  rw [(hasSum_pser hc' x).unique h']; grind

/-! ## Cosine and sine -/

/-- The coefficient pairs `(cₙ, sₙ)` of cosine and sine: `(1, 0)`, then `(cₙ₊₁, sₙ₊₁) =
(−sₙ, cₙ)`. So `cₙ = 1, 0, −1, 0, 1, …` and `sₙ = 0, 1, 0, −1, 0, …`. -/
def csPair : Nat → R × R
  | 0 => (1, 0)
  | n + 1 => (-(csPair n).2, (csPair n).1)

/-- The coefficients `1, 0, −1, 0, …` of the cosine series. -/
def cosCoeff (n : Nat) : R := (csPair n).1

/-- The coefficients `0, 1, 0, −1, …` of the sine series. -/
def sinCoeff (n : Nat) : R := (csPair n).2

/-- The cosine coefficients are bounded by `1`, and so are the sine coefficients. -/
theorem abs_coeff_le (n : Nat) : abs (cosCoeff n) ≤ 1 ∧ abs (sinCoeff n) ≤ 1 := by
  induction n with
  | zero =>
    constructor
    · show abs (1 : R) ≤ 1; rw [abs_of_nonneg (by grind)]; grind
    · show abs (0 : R) ≤ 1; rw [abs_zero]; grind
  | succ n ih =>
    exact ⟨by show abs (-(csPair n).2) ≤ 1; rw [abs_neg]; exact ih.2, ih.1⟩

/-- **The cosine** `cos x = Σ (−1)ᵏ x²ᵏ/(2k)!`. -/
noncomputable def cos (x : R) : R := pser cosCoeff x

/-- **The sine** `sin x = Σ (−1)ᵏ x²ᵏ⁺¹/(2k+1)!`. -/
noncomputable def sin (x : R) : R := pser sinCoeff x

/-- `cos 0 = 1`. -/
theorem cos_zero : cos 0 = 1 := pser_zero fun n => (abs_coeff_le n).1

/-- `sin 0 = 0`. -/
theorem sin_zero : sin 0 = 0 := pser_zero fun n => (abs_coeff_le n).2

/-- **The derivative of sine is cosine.** -/
theorem hasDerivAt_sin (x : R) : HasDerivAt sin (cos x) x := by
  have := hasDerivAt_pser (fun n => (abs_coeff_le n).2) x
  rw [pser_congr (c := fun n => sinCoeff (n + 1)) (c' := cosCoeff) fun n => rfl] at this
  exact this

/-- **The derivative of cosine is minus sine.** -/
theorem hasDerivAt_cos (x : R) : HasDerivAt cos (-sin x) x := by
  have := hasDerivAt_pser (fun n => (abs_coeff_le n).1) x
  rw [pser_congr (c := fun n => cosCoeff (n + 1)) (c' := fun n => -sinCoeff n) fun n => rfl,
    pser_neg (fun n => (abs_coeff_le n).2)] at this
  exact this

/-- **Pythagoras' identity.** `sin² x + cos² x = 1`. -/
theorem sin_sq_add_cos_sq (x : R) : sin x * sin x + cos x * cos x = 1 := by
  have hd : ∀ t, HasDerivAt (fun t => sin t * sin t + cos t * cos t)
      (cos t * sin t + sin t * cos t + (-sin t * cos t + cos t * -sin t)) t := fun t =>
    ((hasDerivAt_sin t).mul (hasDerivAt_sin t)).add ((hasDerivAt_cos t).mul (hasDerivAt_cos t))
  have := const_of_deriv_zero' hd (fun t => by grind) x 0
  rw [sin_zero, cos_zero] at this
  grind

/-- Sine and cosine lie in `[−1, 1]`. -/
theorem abs_cos_le (x : R) : abs (cos x) ≤ 1 := by
  have h := sin_sq_add_cos_sq x
  have := OrderedRing.sq_nonneg (a := sin x)
  apply Classical.byContradiction; intro hlt
  rcases abs_cases (cos x) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := OrderedRing.mul_lt_mul_of_pos_left (by grind : 1 < cos x) (by grind : (0 : R) < cos x)
    grind
  · have := OrderedRing.mul_lt_mul_of_pos_left (by grind : 1 < -cos x) (by grind : (0 : R) < -cos x)
    grind

/-- Cosine is continuous. -/
theorem continuousAt_cos (x : R) : ContinuousAt cos x := (hasDerivAt_cos x).continuousAt

/-! ## A numerical estimate: `cos 2 < 0` -/

/-- **`cos 2 < 0`.** The series gives `cos 2 = 1 − 2 + 2/3 − ⋯`; the terms from the sixth on add
up to at most `8/45`, so `cos 2 ≤ −1/3 + 8/45 < 0`. -/
theorem cos_two_neg : cos 2 < 0 := by
  have hc : ∀ n, abs (cosCoeff n) ≤ 1 := fun n => (abs_coeff_le n).1
  have hs := (hasSum_shift_iff (a := pterm cosCoeff 2) 6).2 (hasSum_pser hc 2)
  -- The first six terms: `1 + 0 − 2 + 0 + 2/3 + 0 = −1/3`.
  have h6 : fsum (pterm cosCoeff 2) 6 = -1 / 3 := by
    simp only [fsum_succ, fsum_zero, pterm, expTerm]
    rw [show cosCoeff 0 = 1 from rfl, show cosCoeff 1 = -0 from rfl,
      show cosCoeff 2 = -1 from rfl, show cosCoeff 3 = - -0 from rfl,
      show cosCoeff 4 = - -1 from rfl, show cosCoeff 5 = - - -0 from rfl,
      show fact 0 = 1 from rfl, show fact 1 = 1 from rfl, show fact 2 = 2 from rfl,
      show fact 3 = 6 from rfl, show fact 4 = 24 from rfl, show fact 5 = 120 from rfl]
    grind
  -- The tail is dominated by `(4/45) · (1/2)ᵏ`.
  have hdom : ∀ k, abs (pterm cosCoeff 2 (6 + k)) ≤ 4 / 45 * (1 / 2) ^ k := fun k => by
    refine Std.le_trans (abs_pterm_le hc 2 (6 + k)) ?_
    rw [abs_of_nonneg (by grind : (0 : R) ≤ 2)]
    induction k with
    | zero =>
      unfold expTerm; rw [show fact (6 + 0) = 720 from rfl]
      show (2 : R) ^ 6 / ((720 : Nat) : R) ≤ 4 / 45 * 1; grind
    | succ k ih =>
      rw [← Nat.add_assoc, expTerm_succ, pow_succ']
      have hk : (0 : R) ≤ ((6 + k : Nat) : R) := OrderedRing.natCast_nonneg
      have hle : 2 / (((6 + k : Nat) : R) + 1) ≤ 1 / 2 := by
        have := one_div_le_one_div (by grind : (0 : R) < 4) (by
          have := OrderedRing.natCast_le_natCast_of_le (R := R) 6 (6 + k) (by omega)
          grind : (4 : R) ≤ ((6 + k : Nat) : R) + 1)
        have e : 2 / (((6 + k : Nat) : R) + 1) = 2 * (1 / (((6 + k : Nat) : R) + 1)) := by grind
        grind
      have h0 := expTerm_nonneg (by grind : (0 : R) ≤ 2) (6 + k)
      have k1 := OrderedRing.mul_le_mul_of_nonneg_right ih
        (Std.le_of_lt (div_pos (by grind : (0 : R) < 2) (by grind : (0 : R) < ((6 + k : Nat) : R) + 1)))
      have hp : (0 : R) ≤ (1 / 2) ^ k := Std.le_trans (abs_nonneg _) (by
        rw [abs_pow, abs_of_nonneg (by grind : (0 : R) ≤ 1 / 2)]; exact Std.le_refl _)
      have k2 := OrderedRing.mul_le_mul_of_nonneg_left hle
        (OrderedRing.mul_nonneg (by grind : (0 : R) ≤ 4 / 45) hp)
      grind
  have hgeo := (hasSum_geometric (r := 1 / 2) (by
    rw [abs_of_nonneg (by grind : (0 : R) ≤ 1 / 2)]; grind)).const_mul (4 / 45)
  have := abs_hasSum_le hdom hs hgeo
  rw [h6] at this
  have := (abs_le.1 this).2
  show pser cosCoeff 2 < 0
  grind

/-! ## π -/

/-- **Cosine has a first positive zero** `p ∈ (0, 2]`: `cos p = 0`, and `cos x > 0` for
`0 ≤ x < p`. It is the supremum of the points up to which cosine stays positive. -/
theorem exists_first_zero_cos :
    ∃ p, 0 < p ∧ p ≤ 2 ∧ cos p = 0 ∧ ∀ x, 0 ≤ x → x < p → 0 < cos x := by
  let G : R → Prop := fun x => 0 ≤ x ∧ x ≤ 2 ∧ ∀ t, 0 ≤ t → t ≤ x → 0 < cos t
  have hG0 : G 0 := ⟨Std.le_refl 0, by grind, fun t h1 h2 => by
    have : t = 0 := by grind
    rw [this, cos_zero]; grind⟩
  obtain ⟨p, hp1, hp2⟩ := exists_lub G ⟨0, hG0⟩ ⟨2, fun x hx => hx.2.1⟩
  have hp0 : 0 ≤ p := hp1 0 hG0
  have hp2' : p ≤ 2 := hp2 2 fun x hx => hx.2.1
  -- Below `p`, cosine is positive.
  have hbelow : ∀ x, 0 ≤ x → x < p → 0 < cos x := fun x hx hxp => by
    apply Classical.byContradiction; intro hneg
    have : p ≤ x := hp2 x fun g hg => by
      apply Classical.byContradiction; intro hgx
      have := hg.2.2 x hx (by grind); grind
    grind
  have hcos : cos p = 0 := by
    rcases (by grind : cos p < 0 ∨ cos p = 0 ∨ 0 < cos p) with h | h | h
    · -- Then cosine is negative slightly to the left of `p`, contradicting `hbelow`.
      exfalso
      obtain ⟨δ, hδ, hδ'⟩ := continuousAt_cos p (-cos p) (by grind)
      have hp : 0 < p := by
        rcases (by grind : p = 0 ∨ 0 < p) with h' | h'
        · rw [h', cos_zero] at h; grind
        · exact h'
      obtain ⟨x, hx0, hxp, hxd⟩ : ∃ x, 0 ≤ x ∧ x < p ∧ abs (x - p) < δ := by
        rcases (by grind : p - δ / 2 < 0 ∨ 0 ≤ p - δ / 2) with h' | h'
        · exact ⟨0, Std.le_refl 0, hp, abs_lt.2 ⟨by grind, by grind⟩⟩
        · exact ⟨p - δ / 2, h', by grind, abs_lt.2 ⟨by grind, by grind⟩⟩
      have := abs_lt.1 (hδ' x hxd)
      have := hbelow x hx0 hxp
      grind
    · exact h
    · -- Then cosine stays positive slightly beyond `p`, contradicting `p = sup G`.
      exfalso
      obtain ⟨δ, hδ, hδ'⟩ := continuousAt_cos p (cos p) h
      have hp2'' : p < 2 := by
        rcases (by grind : p = 2 ∨ p < 2) with h' | h'
        · rw [h'] at h; have := cos_two_neg; grind
        · exact h'
      obtain ⟨q, hq1, hq2, hq3⟩ : ∃ q, p < q ∧ q ≤ 2 ∧ q ≤ p + δ / 2 := by
        rcases (by grind : p + δ / 2 ≤ 2 ∨ 2 < p + δ / 2) with h' | h'
        · exact ⟨p + δ / 2, by grind, h', Std.le_refl _⟩
        · exact ⟨2, hp2'', Std.le_refl 2, Std.le_of_lt h'⟩
      have hGq : G q := ⟨by grind, hq2, fun t ht1 ht2 => by
        rcases (by grind : t < p ∨ p ≤ t) with h' | h'
        · exact hbelow t ht1 h'
        · have := abs_lt.1 (hδ' t (abs_lt.2 ⟨by grind, by grind⟩)); grind⟩
      have := hp1 q hGq
      grind
  have hp : 0 < p := by
    rcases (by grind : p = 0 ∨ 0 < p) with h' | h'
    · rw [h', cos_zero] at hcos; grind
    · exact h'
  exact ⟨p, hp, hp2', hcos, hbelow⟩

/-- **The number π**, defined as twice the first positive zero of cosine. -/
noncomputable def pi : R := 2 * Classical.choose exists_first_zero_cos

/-- `π/2` is the first positive zero of cosine: `0 < π/2 ≤ 2`, `cos (π/2) = 0`, and `cos x > 0`
for `0 ≤ x < π/2`. -/
theorem pi_div_two_spec :
    0 < pi / 2 ∧ pi / 2 ≤ 2 ∧ cos (pi / 2) = 0 ∧ ∀ x, 0 ≤ x → x < pi / 2 → 0 < cos x := by
  have h := Classical.choose_spec exists_first_zero_cos
  have e : pi / 2 = Classical.choose exists_first_zero_cos := by unfold pi; grind
  rw [e]; exact h

/-- **`cos (π/2) = 0`.** -/
theorem cos_pi_div_two : cos (pi / 2) = 0 := pi_div_two_spec.2.2.1

/-- **Bounds for π.** `0 < π ≤ 4`. -/
theorem pi_pos_le_four : 0 < pi ∧ pi ≤ 4 := by
  have h1 := pi_div_two_spec.1
  have h2 := pi_div_two_spec.2.1
  constructor <;> grind

/-- **`sin (π/2) = 1`.** -/
theorem sin_pi_div_two : sin (pi / 2) = 1 := by
  obtain ⟨h0, -, hcos, hpos⟩ := pi_div_two_spec
  -- Sine increases on `[0, π/2]`, so `sin (π/2) > 0`; and `sin² (π/2) = 1 − cos² (π/2) = 1`.
  have k1 : sin 0 < sin (pi / 4) := strictMono_of_deriv_pos (a := 0) (b := pi / 4)
    (fun t _ _ => hasDerivAt_sin t) (fun t h1 h2 => hpos t h1 (by grind))
    (Std.le_refl 0) (by grind) (Std.le_refl _)
  have k2 : sin (pi / 4) ≤ sin (pi / 2) := monotone_of_deriv_nonneg (a := pi / 4) (b := pi / 2)
    (fun t _ _ => hasDerivAt_sin t) (fun t h1 h2 => by
      rcases (by grind : t < pi / 2 ∨ t = pi / 2) with h | h
      · exact Std.le_of_lt (hpos t (by grind) h)
      · rw [h, hcos]; grind)
    (Std.le_refl _) (by grind) (Std.le_refl _)
  rw [sin_zero] at k1
  have hs := sin_sq_add_cos_sq (pi / 2)
  rw [hcos] at hs
  have hspos : 0 < sin (pi / 2) := by grind
  rcases (by grind : sin (pi / 2) < 1 ∨ sin (pi / 2) = 1 ∨ 1 < sin (pi / 2)) with h | h | h
  · have := OrderedRing.mul_lt_mul_of_pos_left h hspos; grind
  · exact h
  · have := OrderedRing.mul_lt_mul_of_pos_left h hspos; grind

end R

end Foundations.Numbers
