/-!
# Propositional logic: syntax

Logic, studied mathematically, begins by treating *sentences* as objects. Frege's
*Begriffsschrift* (1879) was the first fully formal language for logic; Hilbert's
programme (1920s) then made the formulas themselves the subject matter of
mathematics ("metamathematics"). Here we follow that tradition: a propositional
formula is simply a finite tree, given as an inductive type.

**Design choices.**
* Atoms (propositional variables) are indexed by natural numbers: `var 0`, `var 1`, ...
* The primitive connectives are falsum `⊥`, implication `→`, conjunction `∧`
  and disjunction `∨`.
* Negation is *not* primitive: `¬φ` abbreviates `φ → ⊥` ("φ leads to absurdity"),
  as in Gentzen's and Heyting's presentations. Likewise `⊤ := ⊥ → ⊥` and
  `φ ↔ ψ := (φ → ψ) ∧ (ψ → φ)`.

We also introduce *theories* (arbitrary, possibly infinite, sets of formulas,
represented as predicates) and the finite list `atoms φ` of variables occurring in
a formula, which is what makes truth tables finite in the next file.
-/

namespace Foundations.Logic

/-- **Propositional formulas.** The syntax trees of propositional logic over the
atoms `var 0, var 1, …`, built from falsum, implication, conjunction and disjunction. -/
inductive Formula : Type where
  /-- Falsum `⊥`, the absurd proposition. -/
  | bot : Formula
  /-- The `n`-th propositional variable (atom). -/
  | var : Nat → Formula
  /-- Implication `φ → ψ`. -/
  | imp : Formula → Formula → Formula
  /-- Conjunction `φ ∧ ψ`. -/
  | conj : Formula → Formula → Formula
  /-- Disjunction `φ ∨ ψ`. -/
  | disj : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

/-- Negation, defined as `φ → ⊥`. -/
def neg (φ : Formula) : Formula := imp φ bot

/-- Verum `⊤`, defined as `⊥ → ⊥`. -/
def top : Formula := imp bot bot

/-- The biconditional `φ ↔ ψ`, defined as `(φ → ψ) ∧ (ψ → φ)`. -/
def iff (φ ψ : Formula) : Formula := conj (imp φ ψ) (imp ψ φ)

/-- The list of atoms occurring in a formula (possibly with repetitions). -/
def atoms : Formula → List Nat
  | bot => []
  | var n => [n]
  | imp φ ψ => atoms φ ++ atoms ψ
  | conj φ ψ => atoms φ ++ atoms ψ
  | disj φ ψ => atoms φ ++ atoms ψ

/-- The number of connectives in a formula; a measure of its complexity. -/
def size : Formula → Nat
  | bot => 0
  | var _ => 0
  | imp φ ψ => size φ + size ψ + 1
  | conj φ ψ => size φ + size ψ + 1
  | disj φ ψ => size φ + size ψ + 1

end Formula

/-- A *theory* (or set of premises): an arbitrary, possibly infinite, set of formulas,
represented as a predicate on formulas. -/
abbrev Theory := Formula → Prop

namespace Theory

/-- The theory `Γ ∪ {φ}`, obtained by adding one more premise. -/
def insert (Γ : Theory) (φ : Formula) : Theory := fun ψ => ψ = φ ∨ Γ ψ

/-- Inclusion of theories: every premise of `Γ` is a premise of `Δ`. -/
def Subset (Γ Δ : Theory) : Prop := ∀ ψ, Γ ψ → Δ ψ

/-- The empty theory (no premises). -/
def empty : Theory := fun _ => False

/-- The finite theory whose premises are the members of a list. -/
def ofList (l : List Formula) : Theory := fun ψ => ψ ∈ l

/-- Inclusion of theories is reflexive. -/
theorem Subset.refl (Γ : Theory) : Subset Γ Γ := fun _ h => h

/-- Inclusion of theories is transitive. -/
theorem Subset.trans {Γ Δ Θ : Theory} (h₁ : Subset Γ Δ) (h₂ : Subset Δ Θ) : Subset Γ Θ :=
  fun ψ h => h₂ ψ (h₁ ψ h)

/-- A theory is included in any extension of it by one premise. -/
theorem subset_insert (Γ : Theory) (φ : Formula) : Subset Γ (insert Γ φ) :=
  fun _ h => Or.inr h

/-- Adding the same premise preserves inclusion. -/
theorem insert_mono {Γ Δ : Theory} (h : Subset Γ Δ) (φ : Formula) :
    Subset (insert Γ φ) (insert Δ φ) := by
  intro ψ hψ
  rcases hψ with h' | h'
  · exact Or.inl h'
  · exact Or.inr (h ψ h')

/-- The empty theory is included in every theory. -/
theorem empty_subset (Γ : Theory) : Subset empty Γ := fun _ h => h.elim

end Theory

end Foundations.Logic
