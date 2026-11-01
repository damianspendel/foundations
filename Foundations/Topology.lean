import Foundations.Topology.Metric
import Foundations.Topology.Topological
import Foundations.Topology.Compact
import Foundations.Topology.Connected
import Foundations.Topology.FixedPoint
import Foundations.Topology.Tychonoff
import Foundations.Topology.Vitali
import Foundations.Topology.Baire
import Foundations.Topology.CantorSet
import Foundations.Topology.OuterMeasure
import Foundations.Topology.UniformConvergence
import Foundations.Topology.PicardLindelof
import Foundations.Topology.Weierstrass
import Foundations.Topology.ArzelaAscoli
import Foundations.Topology.Wallis
import Foundations.Topology.Basel
import Foundations.Topology.Zeta4
import Foundations.Topology.Stirling
import Foundations.Topology.Leibniz
import Foundations.Topology.SigmaAlgebra
import Foundations.Topology.Caratheodory
import Foundations.Topology.LebesgueMeasure
import Foundations.Topology.SimpleFunctions
import Foundations.Topology.LebesgueIntegral
import Foundations.Topology.DominatedConvergence
import Foundations.Topology.LebesgueRiemann
import Foundations.Topology.Paths
import Foundations.Topology.FundamentalGroup
import Foundations.Topology.Circle
import Foundations.Topology.Covering
import Foundations.Topology.CircleGroup
import Foundations.Topology.NoRetraction
import Foundations.Topology.WindingFTA

/-!
# Part VIII: Topology

From the analysis of the real line to general spaces:

1. `Metric` — metric spaces (Fréchet); ℝ and ℂ; open and closed sets; convergence; ε-δ,
   sequential and topological continuity are equivalent.
2. `Topological` — topological spaces (Hausdorff, Kuratowski); the metric topology; discrete,
   indiscrete and Sierpiński spaces; subspaces and products; the Hausdorff property.
3. `Compact` — compactness; Heine–Borel; compact ⇔ sequentially compact for metric spaces;
   continuous images; the extreme value theorem from compactness.
4. `Connected` — connectedness; intervals and ℝ are connected; continuous images; the
   intermediate value theorem from connectedness; ℝ ≇ ℝ ∖ {0}; ℚ is totally disconnected.
5. `FixedPoint` — complete metric spaces; Banach's fixed-point theorem; Brouwer's fixed-point
   theorem in dimension one.
6. `Tychonoff` — the product of two compact sets is compact (tube lemma).
7. `Vitali` — no countably additive, translation-invariant measure on all subsets of `[0, 1)`.
8. `Baire` — the Baire category theorem; ℝ is not meagre; ℝ is uncountable (third proof).
9. `CantorSet` — the Cantor set: closed, compact, empty interior, uncountable.
10. `OuterMeasure` — Lebesgue outer measure; `m*([a, b]) = b − a`.
11. `UniformConvergence` — uniform limits of continuous functions are continuous; integrals of
    uniform limits; `C[a, b]` with the sup metric is complete.
12. `PicardLindelof` — existence and uniqueness for `y' = F(t, y)` via Banach's fixed-point
    theorem; `y' = y` gives `exp`.
13. `Weierstrass` — polynomials are dense in `C[a, b]` (Bernstein polynomials).
14. `ArzelaAscoli` — bounded equicontinuous sequences have uniformly convergent subsequences.
15. `Wallis` — the integrals `∫₀^{π/2} cosⁿ`, their reduction formula, and the Wallis product.
16. `Basel` — Jordan's inequality and Euler's `Σ 1/n² = π²/6`.
17. `Zeta4` — Euler's `Σ 1/n⁴ = π⁴/90` by the same integral method.
18. `Stirling` — Stirling's formula `n! ~ √(2πn) (n/e)ⁿ`, the constant from the Wallis product.
19. `Leibniz` — `∫₀¹ dt/(1+t²) = π/4` and the Leibniz series `1 − 1/3 + 1/5 − ⋯ = π/4`.

Lebesgue's theory of measure and integration (finite measures, real values):

20. `SigmaAlgebra` — the measure problem; σ-algebras, measurable functions (closed under sums and
    pointwise limits), finite measures, continuity from below and above.
21. `Caratheodory` — outer measures; Carathéodory's criterion: the measurable sets form a
    σ-algebra carrying a countably additive measure; countable subadditivity of Lebesgue outer
    measure.
22. `LebesgueMeasure` — Lebesgue measure `λ_{a,b}`; intervals are measurable with
    `λ([c, d]) = d − c`; translation invariance; the Vitali set is not Lebesgue measurable.
23. `SimpleFunctions` — simple functions; the integral of non-negative functions as a supremum;
    monotonicity, constants, homogeneity.
24. `LebesgueIntegral` — additivity of the integral; the monotone convergence theorem.
25. `DominatedConvergence` — integrable functions and linearity; Fatou's lemma; the dominated
    convergence theorem.
26. `LebesgueRiemann` — for continuous `f` on `[a, b]` the Lebesgue and Riemann integrals agree.

Algebraic topology: the fundamental group (Poincaré, *Analysis Situs*, 1895):

27. `Paths` — subspaces; joint continuity and the pasting lemma; paths, concatenation, reverse;
    homotopy rel endpoints; the reparametrisation lemma.
28. `FundamentalGroup` — the group laws up to homotopy; `π₁(X, x₀)` as a `Group`.
29. `Circle` — continuity in `ℂ`; the kernel of `θ ↦ cis θ`; the Lipschitz local inverse `ang`
    (via Jordan's inequality); uniform continuity on the square.
30. `Covering` — path lifting and homotopy lifting for `cis : ℝ → S¹`; uniqueness of lifts.
31. `CircleGroup` — the degree (winding number) of a loop; homotopy invariance; additivity;
    `π₁(S¹) ≅ ℤ`.
32. `NoRetraction` — the disc does not retract onto its boundary circle; Brouwer's fixed-point
    theorem in dimension 2; loops of non-zero degree are surjective.
33. `WindingFTA` — the fundamental theorem of algebra by winding numbers (Gauss's topological
    proof, alongside the analytic `C.fta` of Part II).
-/
