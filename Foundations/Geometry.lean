import Foundations.Geometry.Tarski
import Foundations.Geometry.CartesianModel
import Foundations.Geometry.Euclid
import Foundations.Geometry.Pythagoras
import Foundations.Geometry.KleinModel
import Foundations.Geometry.KleinSegment
import Foundations.Geometry.Independence

/-!
# Part VI: Geometry

Where the user's own Lean journey began — with Euclid. Tarski's axioms for plane
Euclidean geometry (one sort of points, betweenness and equidistance) with their
first consequences; the Cartesian plane `ℝ²` as a model of all of them (so
geometry is consistent relative to the real numbers of Part II), with nine of
the eleven axioms holding over every ordered field; Euclid's Proposition I.1
(the equilateral triangle) in `ℝ²` and its failure in the rational plane `ℚ²`,
where also segment construction and continuity fail — the space is fixed by its
number field; and Pythagoras, Thales, Heron, Cauchy–Schwarz and the triangle
inequality in coordinates. Finally, the Beltrami–Klein model of the hyperbolic
plane inside the unit disc, with the Cayley–Klein invariant as congruence: it
satisfies every Tarski axiom except Euclid's, which it refutes — so the parallel
postulate is independent of the other axioms.
-/
