import Foundations.Langlands.Elliptic.PointCount

/-!
# Point counts and the Hasse bound for two curves

We count points over `𝔽_p` for small primes on two classical curves, by enumeration in the
kernel (`decide`), and check the Hasse bound `|a_p| ≤ 2√p`, in the form `a_p² ≤ 4p`, on each
of them. These are finitely many checked instances; the bound itself (**Hasse**, 1933) is not
proved here.

* `y² = x³ − x` (conductor 32), the congruent-number curve for `n = 1`. It has complex
  multiplication by `ℤ[i]`, and indeed `a_p = 0` for every `p ≡ 3 (mod 4)` in the table:
  for those `p` the map `x ↦ −x` swaps the sets of `x` with `x³ − x` a nonzero square and a
  non-square.
* `y² + y = x³ − x²` (conductor 11, Cremona's `11a3`), the curve of smallest conductor. It is not
  in short Weierstrass form; completing the square and the cube (with `c₄ = 16`, `c₆ = −152`)
  gives the short model `y² = x³ − 432x + 8208`, related to the original by a change of variables
  that is invertible when `6` is. That change of variables is **not** formalised here;
  instead we count both models directly and check that they give the same `a_p` for
  `p = 5, 7, 13, …, 29`. For `p = 2, 3` only the long model is valid, and at `p = 11` the curve
  has bad (split multiplicative) reduction: the cubic is singular and we count the points of
  the singular cubic, the usual convention, which gives `a₁₁ = 1`.
-/

namespace Foundations.Langlands.Elliptic

/-- `2` is prime. -/
instance : PrimeNat 2 := ⟨isPrime_of_check 2 (by decide) (by decide)⟩
/-- `3` is prime. -/
instance : PrimeNat 3 := ⟨isPrime_of_check 3 (by decide) (by decide)⟩

/-- A short Weierstrass curve over `𝔽_p` from its coefficients, given the (decidable)
nondegeneracy and characteristic conditions. -/
def Curve.ofCoeffs {p : Nat} [PrimeNat p] (a b : Fp p)
    (h : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 ∧ (2 : Fp p) ≠ 0 ∧ (3 : Fp p) ≠ 0) : Curve (Fp p) :=
  ⟨a, b, h.1, h.2.1, h.2.2⟩

/-! ## `y² = x³ − x` -/

/-- **The curve `y² = x³ − x` over `𝔽_p`**, for primes `p > 3` (passed as a decidable side
condition). -/
def congruentCurve (p : Nat) [PrimeNat p]
    (h : 4 * (-1 : Fp p) ^ 3 + 27 * (0 : Fp p) ^ 2 ≠ 0 ∧ (2 : Fp p) ≠ 0 ∧ (3 : Fp p) ≠ 0) :
    Curve (Fp p) :=
  Curve.ofCoeffs (-1) 0 h

/-- **`#E(𝔽_p)` for `y² = x³ − x`.** For `p = 5, 7, 11, 13, 17, 19, 23, 29` the curve has
`8, 8, 12, 8, 16, 20, 24, 40` points. -/
theorem congruentCurve_card :
    (congruentCurve 5 (by decide)).card = 8 ∧ (congruentCurve 7 (by decide)).card = 8 ∧
    (congruentCurve 11 (by decide)).card = 12 ∧ (congruentCurve 13 (by decide)).card = 8 ∧
    (congruentCurve 17 (by decide)).card = 16 ∧ (congruentCurve 19 (by decide)).card = 20 ∧
    (congruentCurve 23 (by decide)).card = 24 ∧ (congruentCurve 29 (by decide)).card = 40 := by
  decide

/-- **`a_p` for `y² = x³ − x`.** For `p = 5, 7, 11, 13, 17, 19, 23, 29`:
`a_p = −2, 0, 0, 6, 2, 0, 0, −10`; it vanishes exactly at the listed `p ≡ 3 (mod 4)`. -/
theorem congruentCurve_ap :
    (congruentCurve 5 (by decide)).ap = -2 ∧ (congruentCurve 7 (by decide)).ap = 0 ∧
    (congruentCurve 11 (by decide)).ap = 0 ∧ (congruentCurve 13 (by decide)).ap = 6 ∧
    (congruentCurve 17 (by decide)).ap = 2 ∧ (congruentCurve 19 (by decide)).ap = 0 ∧
    (congruentCurve 23 (by decide)).ap = 0 ∧ (congruentCurve 29 (by decide)).ap = -10 := by
  decide

/-- **Hasse bound, checked for `y² = x³ − x`.** `a_p² ≤ 4p` for
`p = 5, 7, 11, 13, 17, 19, 23, 29`. -/
theorem congruentCurve_hasse :
    (congruentCurve 5 (by decide)).ap ^ 2 ≤ 4 * 5 ∧ (congruentCurve 7 (by decide)).ap ^ 2 ≤ 4 * 7 ∧
    (congruentCurve 11 (by decide)).ap ^ 2 ≤ 4 * 11 ∧
    (congruentCurve 13 (by decide)).ap ^ 2 ≤ 4 * 13 ∧
    (congruentCurve 17 (by decide)).ap ^ 2 ≤ 4 * 17 ∧
    (congruentCurve 19 (by decide)).ap ^ 2 ≤ 4 * 19 ∧
    (congruentCurve 23 (by decide)).ap ^ 2 ≤ 4 * 23 ∧
    (congruentCurve 29 (by decide)).ap ^ 2 ≤ 4 * 29 := by
  decide

/-! ## The conductor-11 curve -/

/-- **Short model of the conductor-11 curve**, `y² = x³ − 432x + 8208` over `𝔽_p`, for primes
`p ∉ {2, 3, 11}` (passed as a decidable side condition). -/
def curve11 (p : Nat) [PrimeNat p]
    (h : 4 * (-432 : Fp p) ^ 3 + 27 * (8208 : Fp p) ^ 2 ≠ 0 ∧ (2 : Fp p) ≠ 0 ∧ (3 : Fp p) ≠ 0) :
    Curve (Fp p) :=
  Curve.ofCoeffs (-432) 8208 h

/-- The affine solutions over `𝔽_p` of the general Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. -/
def longAffinePoints {p : Nat} [PrimeNat p] (a₁ a₂ a₃ a₄ a₆ : Fp p) : List (Fp p × Fp p) :=
  (Curve.allPairs p).filter fun q =>
    decide (q.2 ^ 2 + a₁ * q.1 * q.2 + a₃ * q.2 = q.1 ^ 3 + a₂ * q.1 ^ 2 + a₄ * q.1 + a₆)

/-- **`a_p` of the curve `y² + y = x³ − x²`**, counted on that equation directly:
`p + 1 − (1 + #{(x, y) ∈ 𝔽_p² : y² + y = x³ − x²})`. Valid for every prime `p`; at `p = 11`
(bad reduction) it counts the points of the singular cubic. -/
def ap11 (p : Nat) [PrimeNat p] : Int :=
  (p : Int) + 1 - ((longAffinePoints (p := p) 0 (-1) 1 0 0).length + 1 : Nat)

/-- **`a_p` of the conductor-11 curve for `p < 30`**, counted on `y² + y = x³ − x²`:
`a₂ = −2, a₃ = −1, a₅ = 1, a₇ = −2, a₁₁ = 1, a₁₃ = 4, a₁₇ = −2, a₁₉ = 0, a₂₃ = −1, a₂₉ = 0`. -/
theorem ap11_values :
    ap11 2 = -2 ∧ ap11 3 = -1 ∧ ap11 5 = 1 ∧ ap11 7 = -2 ∧ ap11 11 = 1 ∧ ap11 13 = 4 ∧
    ap11 17 = -2 ∧ ap11 19 = 0 ∧ ap11 23 = -1 ∧ ap11 29 = 0 := by
  decide

/-- **The two models agree.** For `p = 5, 7, 13, 17, 19, 23, 29` the short model
`y² = x³ − 432x + 8208` (a `Curve` in the sense of `Weierstrass`) has the same `a_p` as the
long model `y² + y = x³ − x²`. (A finite check, not a proof of the isomorphism.) -/
theorem curve11_ap_eq :
    (curve11 5 (by decide)).ap = ap11 5 ∧ (curve11 7 (by decide)).ap = ap11 7 ∧
    (curve11 13 (by decide)).ap = ap11 13 ∧ (curve11 17 (by decide)).ap = ap11 17 ∧
    (curve11 19 (by decide)).ap = ap11 19 ∧ (curve11 23 (by decide)).ap = ap11 23 ∧
    (curve11 29 (by decide)).ap = ap11 29 := by
  decide

/-- **Hasse bound, checked for the conductor-11 curve.** `a_p² ≤ 4p` for every prime `p < 30`. -/
theorem ap11_hasse :
    ap11 2 ^ 2 ≤ 4 * 2 ∧ ap11 3 ^ 2 ≤ 4 * 3 ∧ ap11 5 ^ 2 ≤ 4 * 5 ∧ ap11 7 ^ 2 ≤ 4 * 7 ∧
    ap11 11 ^ 2 ≤ 4 * 11 ∧ ap11 13 ^ 2 ≤ 4 * 13 ∧ ap11 17 ^ 2 ≤ 4 * 17 ∧
    ap11 19 ^ 2 ≤ 4 * 19 ∧ ap11 23 ^ 2 ≤ 4 * 23 ∧ ap11 29 ^ 2 ≤ 4 * 29 := by
  decide

end Foundations.Langlands.Elliptic
