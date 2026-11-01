import Foundations.Algebra.Group
import Foundations.Algebra.Finite
import Foundations.Algebra.Lagrange
import Foundations.Algebra.Cayley
import Foundations.Algebra.Quotient
import Foundations.Algebra.Ring
import Foundations.Algebra.Action
import Foundations.Algebra.Cauchy
import Foundations.Algebra.Sylow
import Foundations.Algebra.RingHom
import Foundations.Algebra.Polynomial
import Foundations.Algebra.PolyDivision
import Foundations.Algebra.PID
import Foundations.Algebra.UFD
import Foundations.Algebra.GaussianInt
import Foundations.Algebra.TwoSquares
import Foundations.Algebra.VectorSpace
import Foundations.Algebra.FieldExt
import Foundations.Algebra.Algebraic
import Foundations.Algebra.Constructible
import Foundations.Algebra.FiniteField
import Foundations.Algebra.Symmetric
import Foundations.Algebra.Alternating
import Foundations.Algebra.A5
import Foundations.Algebra.Solvable
import Foundations.Algebra.QuadraticResidues
import Foundations.Algebra.GaussLemma
import Foundations.Algebra.Reciprocity
import Foundations.Algebra.FieldAut
import Foundations.Algebra.GaloisCorrespondence
import Foundations.Algebra.Quintic
import Foundations.Algebra.S5Generation
import Foundations.Algebra.QuinticReal
import Foundations.Algebra.Eisenstein
import Foundations.Algebra.QuinticIrreducible
import Foundations.Algebra.ComplexField
import Foundations.Algebra.Adjoin
import Foundations.Algebra.Embedding
import Foundations.Algebra.QuinticRoots
import Foundations.Algebra.SplittingField
import Foundations.Algebra.QuinticGalois

/-!
# Part IV: Algebra

Aggregator for the algebra part of the Foundations project: groups, finite groups and
counting, Lagrange's theorem with Fermat and Euler, Cayley's theorem, quotient groups and
the isomorphism theorems, rings, ideals and quotient rings, group actions with the
orbit–stabiliser theorem, Cauchy's theorem and Sylow's first theorem; ring homomorphisms,
the first isomorphism theorem for rings and the Chinese remainder theorem; polynomial rings,
the division algorithm, the factor theorem and the root bound; Euclidean domains, PIDs and
unique factorisation (for ℤ and F[x]); the Gaussian integers; Fermat's two-squares
theorem; vector spaces and dimension, field extensions and the tower law, quadratic and
cubic extensions, the impossibility of doubling the cube and trisecting the angle; and
the prime-power order of finite fields; the symmetric group and the sign homomorphism, the
alternating group and its generation by 3-cycles, the simplicity of A₅, and the
non-solvability of Sₙ for n ≥ 5; quadratic residues, Euler's criterion, Gauss's lemma, the
two supplements and the law of quadratic reciprocity; field automorphisms, Dedekind's lemma,
Artin's theorem and the Galois correspondence (Artin's half); and the group-theoretic core
of the insolvability of the quintic.

The final chapter computes a Galois group. A transposition and any 5-cycle generate `S₅`;
`x⁵ - 6x + 3` has exactly three real roots (intermediate value theorem and Rolle) and is
irreducible over `ℚ` (Gauss's lemma and Eisenstein's criterion). Inside `ℂ` (from Part II,
with the fundamental theorem of algebra), simple algebraic extensions `F(γ)` are built and
embeddings are extended along them. The splitting field `L` of `x⁵ - 6x + 3` is a finite
extension of `ℚ`, and its automorphism group `Aut(L/ℚ)` is isomorphic to `S₅`, hence **not
solvable** (`quintic_galois_not_solvable`). Galois's criterion (solvable by radicals ⇒
solvable Galois group) and the full Galois correspondence for intermediate fields are not
formalised.
-/
