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
import Foundations.Langlands.Padic.Density
import Foundations.Langlands.Padic.Compact
import Foundations.Langlands.Padic.CompactMetric
import Foundations.Langlands.Padic.SquareLift
import Foundations.Langlands.Padic.Hilbert
import Foundations.Langlands.Padic.HilbertLegendre
import Foundations.Langlands.Padic.HilbertBilinear
import Foundations.Langlands.Padic.HilbertInf
import Foundations.Langlands.Padic.Primitive
import Foundations.Langlands.Padic.Hilbert2
import Foundations.Langlands.Padic.HilbertProduct
import Foundations.Langlands.Padic.Hilbert2Bilinear
import Foundations.Langlands.Padic.HilbertLocal
import Foundations.Langlands.Padic.HilbertReciprocity

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

12. `Density` — **`Qp.dense`**: for every `q ∈ ℚₚ` and `k` there is `r ∈ ℚ` with
    `|q − r|ₚ ≤ p^(−k)`; `Qp.exists_seq_tendsto`: every `q` is a limit of rationals. With
    `Qp.complete` and `Qp.abs_ofQ`, ℚₚ is a complete valued field in which ℚ is dense.
13. `Compact` — **`Zp.seqCompact`**: every sequence in ℤₚ has a subsequence converging in the
    `Zp.Converges` sense (residues chosen digit by digit with the infinite pigeonhole principle
    `Combinatorics.infinite_pigeonhole`, then a diagonal subsequence and `Zp.complete`).
14. `CompactMetric` — ℤₚ as a `Topology.MetricSpace` with `d(x, y) = |x − y|ₚ`
    (`Zp.instMetricSpace`); `Zp.converges_iff`: metric convergence is `Zp.Converges`;
    **`Zp.isSeqCompact`** and **`Zp.isCompact`**: ℤₚ is (sequentially) compact in the
    Topology part's sense.
15. `SquareLift` — **`Zp.exists_sq_of_modPow`** (odd `p`): a `p`-adic integer congruent mod `p`
    to `a²`, `p ∤ a`, is a square in ℤₚ (Hensel for integer approximations plus compactness);
    **`exists_sum_sq_eq_one_mod`**: `c x² + d y² ≡ 1 (mod p)` is solvable for `p ∤ c d`.
16. `Hilbert` — the Hilbert symbol `Qp.hilbert a b` (`1` iff `z² = a x² + b y²` has a non-trivial
    solution in ℚₚ, else `−1`); `Qp.hilbert_comm`, `Qp.hilbert_mul_self` (`(a, c²) = 1`),
    `Qp.hilbert_neg_self` (`(a, −a) = 1`), `Qp.hilbert_one_sub` (`(a, 1 − a) = 1`), and
    **`Qp.hilbert_units`**: `(u, v)ₚ = 1` for units of ℤₚ, `p` odd.
17. `HilbertLegendre` — **`Qp.hilbert_p`**: `(u, p)ₚ = (u/p)` (Legendre symbol) for odd `p` and
    natural `u` prime to `p`; more generally `Qp.hilbertSolvable_unit_pv_iff` for `(u, p v)`.
18. `HilbertBilinear` — square-class invariance, `(a, b) = (a, −ab)`, the normal form
    `a = c² u` or `c² p u`, the explicit table **`Qp.hilbert_std`**, and **bilinearity**
    `Qp.hilbert_mul_right` / `Qp.hilbert_mul_left` for odd `p` (non-zero arguments);
    `Zp.chi_neg_one`: `χ(−1) = (−1)^((p−1)/2)`.
19. `HilbertInf` — the Hilbert symbol at `∞`: **`hilbertInf_eq_neg_one_iff`**:
    `(a, b)_∞ = −1` iff `a < 0` and `b < 0`.
20. `Primitive` — **`Qp.exists_primitive`**: a non-trivial ℚₚ-solution of `z² = a x² + b y²`
    (`a, b ∈ ℤₚ`) gives a solution in ℤₚ not divisible by `p` (clearing denominators, descent).
21. `Hilbert2` — **`Zp.exists_sq_of_modPow_eight`**: `u ≡ 1 (mod 8)` is a square in ℤ₂ (strong
    Hensel plus compactness); **`Qp.hilbert_two_units`**: for units of ℤ₂, `(u, v)₂ = −1` iff
    `u ≡ v ≡ 3 (mod 4)`.
22. `HilbertProduct` — **`hilbert_product_formula_primes`** (and the finite-product form
    `hilbert_product_formula_primes'`): for distinct odd primes `p, q`, `(p, q)_ℓ = 1` at primes
    `ℓ ∉ {2, p, q}` and `(p, q)_∞ (p, q)_2 (p, q)_p (p, q)_q = 1` — via quadratic reciprocity.

23. `Hilbert2Bilinear` — the symbol at `2` with the factor `2`: **`Qp.hilbertSolvable_unit_two_iff`**
    (`z² = u x² + 2v y²` is solvable iff `u ≡ 1` or `u + 2v ≡ 1 (mod 8)`), the full table
    **`Qp.hilbert_std_two`**: `(2^α u, 2^β v)₂ = (−1)^(ε(u)ε(v) + α ω(v) + β ω(u))` on residues
    mod `8` (`table2`), and **bilinearity at `2`** `Qp.hilbert_mul_right_two` /
    `Qp.hilbert_mul_left_two` (non-zero arguments).
24. `HilbertLocal` — local symbols of rationals at every place: bilinearity
    (`hilbertAt_mul_left`, `hilbertInfQ_mul_left`), symmetry, square classes,
    `(a, a)_v = (a, −1)_v`; `hilbertAt_neg_one_self`: `(−1, p)ₚ = (−1)^((p−1)/2)` and
    `hilbertAt_two_self`: `(2, p)ₚ = (2/p) = (−1)^((p²−1)/8)` for odd `p`; the values at `2` of
    odd integers and `2` (`hilbertAt_two_units_int`, `hilbertAt_two_int_two`).
25. `HilbertReciprocity` — **`hilbert_product_formula`**: for all non-zero rationals `a, b`, there
    is `N` with `(a, b)_ℓ = 1` for `ℓ ≥ N` and `(∏_{ℓ < M prime} (a, b)_ℓ) · (a, b)_∞ = 1` for all
    `M ≥ N`. Proof: multiplicativity of the formula (`HilbertPF.mul_left`), reduction to the
    generators `−1`, `2`, odd primes (`HilbertPF.of_generators`), and the generator pairs
    (`hilbertPF_gen`), which are quadratic reciprocity and its two supplements.

## Not proved here

The general uniqueness of completions up to isometry (so "ℚₚ is *the* completion" rests on
density plus completeness, not on a formalised universal property); Hilbert symbols over finite
extensions of ℚₚ; the converse direction of the product formula (existence of a global
element with prescribed local symbols); Hasse's local–global principle (local or global part).
-/
