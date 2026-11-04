import Foundations.Langlands.Padic.Valuation
import Foundations.Langlands.Padic.ProductFormula
import Foundations.Langlands.Padic.AbsoluteValues
import Foundations.Langlands.Padic.OstrowskiBound
import Foundations.Langlands.Padic.Ostrowski
import Foundations.Langlands.Padic.Integers
import Foundations.Langlands.Padic.Hensel
import Foundations.Langlands.Padic.Units
import Foundations.Langlands.Padic.Field
import Foundations.Langlands.Padic.QpAbs
import Foundations.Langlands.Padic.QpComplete
import Foundations.Langlands.Padic.StrongHensel

/-!
# Part XV, local side: absolute values on ℚ and the `p`-adic integers

The Langlands programme is organised place by place: for each prime `p` and for `∞` there is a
*local* theory (representations of groups over ℚₚ or ℝ, and their Galois-side parameters), and
the global theory over ℚ is assembled from all of them through the adèles. This sub-part builds,
from scratch, the arithmetic that says what the places of ℚ are and what the local objects at a
finite place look like.

Historically: Hensel (1897) introduced the `p`-adic numbers by analogy with power-series
expansions of functions at a point; Ostrowski (1916) showed that the `p`-adic absolute values
and the ordinary one are, up to equivalence, the only absolute values on ℚ; Hasse (1921) proved
the first *local–global principle* — a rational quadratic form represents zero over ℚ iff it does
over ℝ and over every ℚₚ — making the collection of all completions of ℚ a tool for global
questions. Local fields (ℚₚ, ℝ and their finite extensions) are exactly where local Langlands
lives. (These historical remarks are context; Hasse's principle is not formalised here.)

## What is proved

1. `Valuation` — the valuation `vₚ : ℚ → ℤ` (well defined on fractions, additive, ultrametric),
   the `p`-adic absolute value `|x|ₚ = p^(−vₚ x)` (ℚ-valued), multiplicativity, the ultrametric
   inequality `padicAbs_ultrametric`, and `|n|ₚ ≤ 1` for integers.
2. `ProductFormula` — `product_formula`: for `x ≠ 0` there is `N` with `|x|ₚ = 1` for all
   `p ≥ N`, and `(∏_{p < M prime} |x|ₚ) · |x|_∞ = 1` for all `M ≥ N`.
3. `AbsoluteValues` — real-valued absolute values `AbsVal`, equivalence (`ψ = φ^s`, phrased as
   `log ψ = s · log φ`), the examples `absInf` and `absP`, and their pairwise inequivalence.
4. `OstrowskiBound`, `Ostrowski` — **Ostrowski's theorem** `ostrowski` and its uniqueness form
   `ostrowski_unique`: every nontrivial absolute value on ℚ is equivalent to `|·|_∞` or to
   `|·|ₚ` for exactly one prime `p`, and not to both kinds.
5. `Integers` — ℤₚ as compatible sequences `xₙ` (`pⁿ ∣ xₙ₊₁ − xₙ`) modulo `pⁿ ∣ xₙ − yₙ`, i.e.
   `lim ℤ/pⁿ`; a commutative ring (`Lean.Grind.CommRing`), with ℤ embedded injectively
   (`intCast_injective`), congruences mod `pᵏ`, and completeness `Zp.complete`: every sequence
   that is Cauchy modulo powers of `p` converges.
6. `Hensel` — **Hensel's lemma** `hensel` for integer polynomials and simple roots mod `p`;
   `sqrt_two_Z7` (`x² = 2` in ℤ₇), `sqrt_neg_one_Z5` (`x² = −1` in ℤ₅), `Z7_ne_Z` (ℤ₇ ≠ ℤ),
   and `not_ordered`: for odd primes `p`, ℤₚ carries no order compatible with addition in which
   squares are non-negative and `¬ 1 ≤ 0`.

7. `Units` — ℤₚ: `Zp.isUnit_iff` (`x` invertible iff `x ≢ 0 mod p`), `Zp.eq_pow_mul_unit`
   (every nonzero `x` is `pᵛ · u`, `u` a unit), and `Zp.eq_zero_or_eq_zero` (integral domain).
8. `Field` — ℚₚ = ℤₚ[1/p] as classes of `x / pᵏ`; `Qp.instField`: ℚₚ is a field
   (`Lean.Grind.Field`); `ℤₚ → ℚₚ` is an injective ring map.
9. `QpAbs` — uniqueness of `v` in `x = pᵛ u` (`Zp.pow_unique`); the valuation on ℤₚ and ℚₚ,
   additive and ultrametric; `Qp.abs` with `Qp.abs_mul` and `Qp.abs_ultrametric`,
   `Qp.abs_ofZp_le_one`; the embedding `Qp.ofQ : ℚ → ℚₚ`, additive, multiplicative, injective
   (`Qp.ofQ_injective`), and `Qp.abs_ofQ`: `|ofQ x|ₚ = |x|ₚ`, so the absolute value on ℚₚ
   extends the one on ℚ.

10. `QpComplete` — `Qp.abs_ofZp_le_iff` (for `x ∈ ℤₚ`, `|x|ₚ ≤ p^(−k)` iff `x ≡ 0 mod pᵏ`),
    `Qp.exists_ofZp_of_abs_le_one` (the unit ball of ℚₚ is ℤₚ), and **`Qp.complete`**: every
    `|·|ₚ`-Cauchy sequence in ℚₚ converges.
11. `StrongHensel` — **`hensel_strong`**: if `vₚ(f'(a)) = e` and `p^(2e+1) ∣ f(a)` (i.e.
    `|f(a)|ₚ < |f'(a)|ₚ²`), then `f` has a root `x ∈ ℤₚ` with `x ≡ a mod pᵉ⁺¹`;
    `sqrt_neg_seven_Z2`: `x² = −7` in ℤ₂ with `x ≡ 1 mod 4`.

## Not proved here

Density of ℚ in ℚₚ, hence the identification of ℚₚ with *the* `|·|ₚ`-completion of ℚ (explained
in prose only); compactness of ℤₚ; Hasse's local–global principle (local or global part).
-/
