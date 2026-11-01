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
-/
