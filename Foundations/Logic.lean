import Foundations.Logic.PropSyntax
import Foundations.Logic.PropSemantics
import Foundations.Logic.NaturalDeduction
import Foundations.Logic.Hilbert
import Foundations.Logic.PropCompleteness
import Foundations.Logic.Kalmar
import Foundations.Logic.FOSyntax
import Foundations.Logic.FOSemantics
import Foundations.Logic.FOSoundness
import Foundations.Logic.PeanoArithmetic
import Foundations.Logic.FOSubstitution
import Foundations.Logic.FOProofTheory
import Foundations.Logic.FOEnumeration
import Foundations.Logic.Henkin
import Foundations.Logic.TermModel
import Foundations.Logic.FOCompleteness
import Foundations.Logic.NonstandardArithmetic
import Foundations.Logic.Computability
import Foundations.Logic.GodelNumbering
import Foundations.Logic.Undecidability
import Foundations.Logic.RecursionTheorem
import Foundations.Logic.PrimRec
import Foundations.Logic.Derivations
import Foundations.Logic.Universal
import Foundations.Logic.BetaFunction
import Foundations.Logic.Definability
import Foundations.Logic.ArithCoding
import Foundations.Logic.ArithWellFormed
import Foundations.Logic.PARules
import Foundations.Logic.PAProofs
import Foundations.Logic.Incompleteness
import Foundations.Logic.RobinsonQ
import Foundations.Logic.Delta0
import Foundations.Logic.BoundedGraphs
import Foundations.Logic.Representability
import Foundations.Logic.DiagonalLemma
import Foundations.Logic.Rosser
import Foundations.Logic.Lob
import Foundations.Logic.PAModels
import Foundations.Logic.PASequences
import Foundations.Logic.PACompleteness
import Foundations.Logic.UniformDefinability
import Foundations.Logic.HilbertProvability
import Foundations.Logic.DerivabilityConditions
import Foundations.Logic.Ordinals
import Foundations.Logic.Goodstein
import Foundations.Logic.SequentCalculus
import Foundations.Logic.CutElimination
import Foundations.Logic.SequentEquivalence
import Foundations.Logic.GentzenConsistency

/-!
# Part III: Logic

Logic as a mathematical object: syntax as inductive types, semantics as functions,
proofs as inductively defined derivability. Propositional logic (truth tables,
natural deduction, Hilbert systems, soundness, completeness, compactness), then
first-order logic with de Bruijn indices (substitution lemma, natural deduction,
soundness), Peano arithmetic with its standard model, and finally Gödel's
completeness theorem via Henkin's term-model construction, with compactness,
downward Löwenheim–Skolem and a non-standard model of arithmetic as corollaries.
The last files turn to the limits of formal systems: partial recursive functions,
Gödel numbering, the undecidability of halting, Rice's theorem, Kleene's recursion
theorem, and an abstract (computational) form of Gödel's incompleteness theorem;
then a library of primitive recursive constructions, the universal code (Kleene's
normal form, s-m-n, the classical recursion theorem), Gödel's β-function and the
arithmetical definability of computation, the arithmetisation of syntax with the
computable enumerability of PA's theorems, and Gödel's first incompleteness
theorem for Peano arithmetic. The final files treat Robinson's arithmetic `Q`:
Δ₀-absoluteness and Σ₁-completeness, representability of decidable sets and total
computable functions (via Rosser's witness comparison), the diagonal lemma,
Tarski's undefinability of truth, and the Gödel–Rosser theorem: every consistent,
computably enumerable extension of `Q` is incomplete. Löb's theorem and Gödel's
second incompleteness theorem are derived from the Hilbert–Bernays–Löb derivability
conditions; then, reasoning inside arbitrary (possibly non-standard) models of PA —
internal arithmetic, induction for definable properties, β-coding and concatenation
of sequences of non-standard length — and using completeness, the conditions (D1)–(D3)
are verified for a Hilbert-style provability formula of PA, which yields Löb's theorem
and Gödel's second incompleteness theorem for PA unconditionally. Finally, ordinals below ε₀
in Cantor normal form are shown to be well-ordered, which yields Goodstein's theorem —
a true arithmetical statement unprovable in PA (Kirby–Paris).
The closing files turn to Gentzen's structural proof theory: the sequent calculus LK,
the Hauptsatz (cut elimination) with the subformula property and a purely syntactic
consistency proof, cut-free completeness via terminating proof search (a second
decision procedure for tautologies), syntactic translations between LK and natural
deduction, and an account of Gentzen's 1936 consistency proof for PA by induction up
to ε₀, with its abstract descent principle formalised.
-/
