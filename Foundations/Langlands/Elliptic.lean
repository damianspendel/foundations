import Foundations.Langlands.Elliptic.Weierstrass
import Foundations.Langlands.Elliptic.Assoc
import Foundations.Langlands.Elliptic.Cancel
import Foundations.Langlands.Elliptic.AssocFull
import Foundations.Langlands.Elliptic.Group
import Foundations.Langlands.Elliptic.Fp
import Foundations.Langlands.Elliptic.PointCount
import Foundations.Langlands.Elliptic.Examples
import Foundations.Langlands.Elliptic.Modularity

/-!
# Elliptic curves

An elliptic curve over a field `K` of characteristic not `2` or `3` is a curve
`y² = x³ + ax + b` with `4a³ + 27b² ≠ 0`, together with a point at infinity `O`. Its points form
an abelian group under the chord–tangent law of **Diophantus**, **Fermat** and **Newton**, a
structure first made explicit by **Poincaré** (1901); **Mordell** (1922) proved the group of
rational points finitely generated. Over `𝔽_p` the number of points is `p + 1 − a_p` with
`|a_p| ≤ 2√p` (**Hasse**, 1933). **Eichler** and **Shimura** found the numbers `a_p` of the
conductor-11 curve as Fourier coefficients of a modular form; the **Taniyama–Shimura–Weil**
conjecture that this happens for every curve over `ℚ` was proved for semistable curves by
**Wiles** (1995, with **Taylor**), giving **Fermat's Last Theorem**, and in general by Breuil,
Conrad, Diamond and Taylor (2001). Of these results only finitely many numerical instances
are checked here; the theorems themselves are not formalised.

## What this sub-part proves

* `Weierstrass` — curves `Curve K` over any `Lean.Grind.Field K` with decidable equality,
  points `Point E` (affine points and `O`), negation and chord–tangent addition. Addition lands
  on the curve (`Curve.third_point_onCurve`, built into `Point.add`); `O` is a two-sided
  identity (`Point.zero_add`, `Point.add_zero`); `P + (−P) = O` (`Point.add_neg_self`);
  addition is commutative (`Point.add_comm`).
* `Assoc` — **associativity in the generic case** (`Point.add_assoc_generic`): for affine
  `P₁, P₂, P₃` with pairwise distinct `x`-coordinates such that `x(P₁ + P₂) ≠ x₃` and
  `x(P₂ + P₃) ≠ x₁`. The proof interpolates the three points by a parabola
  `y = αx² + βx + γ` and shows `(P₁ + P₂) + P₃ = −P₄` with `P₄` the fourth intersection
  (`Point.add_add_eq_neg`), a symmetric expression.
* `Cancel` — `−(P + Q) = −P + −Q` (`Point.neg_add`) and the cancellation law
  `P + (−P + Q) = Q` (`Point.add_neg_add_cancel`, which uses `4a³ + 27b² ≠ 0`); the slope of
  the addition law is characterised by the two chord relations (`Curve.slope_eq_of_rel`).
* `AssocFull` — the key lemma with all four Vieta relations, valid for doublings too
  (`Point.add_add_eq_neg_of_parabola`), and the parabolas through three distinct points or
  tangent at a doubled point (`Curve.parabola_of_distinct`, `Curve.parabola_of_double`).
* `Group` — **associativity in all cases** (`Point.add_assoc`), by reducing every degenerate
  configuration to cancellation and commutativity, and the **abelian group of points**
  (`Point.instAddAbGroup : AddAbGroup (Point E)`).
* `Fp` — the prime field `𝔽_p` (`Fp p`, i.e. `Fin p` with inverse `a^(p−2)` by Fermat's little
  theorem) as a `Lean.Grind.Field`.
* `PointCount` — `#E(𝔽_p)` by enumeration (`Curve.card`, with `Curve.mem_affinePoints` and
  `Curve.nodup_affinePoints` saying the enumeration is exact) and `a_p = p + 1 − #E(𝔽_p)`.
* `Examples` — `#E(𝔽_p)` and `a_p` for `y² = x³ − x` and for the conductor-11 curve
  `y² + y = x³ − x²` (also via its short model `y² = x³ − 432x + 8208`) at small primes, and the
  Hasse bound `a_p² ≤ 4p` checked on all of them.
* `Modularity` — the `q`-expansion of `q ∏ (1 − qⁿ)² (1 − q¹¹ⁿ)²` to order 30, and the check that
  its `q^p`-coefficient is `a_p` of the conductor-11 curve for every prime `p < 30`
  (`modularity_check_lt_30`): a checked instance of the modularity correspondence at ten
  primes, nothing more.

## Not proved

* The Hasse bound in general, Mordell's theorem, the change of variables between long and short
  Weierstrass models, modular forms, and any form of the modularity theorem beyond the finite
  check above.
* No connection is made between `Curve.card` and the group structure (e.g. Lagrange's theorem
  for `E(𝔽_p)`), and nothing is said about the structure of `E(𝔽_p)` or `E(ℚ)`.
-/
