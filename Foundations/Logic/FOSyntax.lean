/-!
# First-order logic: syntax with de Bruijn indices

Propositional logic treats sentences as unanalysed atoms. Frege's great innovation
(1879) was to look *inside* sentences: "every number has a successor" has the form
`∀x ∃y S(x, y)`, with **quantifiers** binding **variables**. First-order logic,
isolated as a system in its own right by Hilbert and Ackermann (1928) and by
Skolem, quantifies over individuals only (not over properties), and is the logic in
which modern mathematics is usually formalised.

**Signatures.** A first-order language is specified by its *signature*: which
function symbols (with arities) and which relation symbols (with arities) it has.
Arithmetic has `0, S, +, ×`; set theory has a single binary relation `∈`.

**De Bruijn indices.** The subtle part of first-order syntax is variable binding:
`∀x P(x, y)` and `∀z P(z, y)` should be "the same" formula, and substituting `x`
for `y` must not let the `x` be *captured* by the quantifier. Following N. G. de
Bruijn (1972) we avoid names altogether: a variable is a number counting how many
quantifiers one must cross outward to reach its binder. `var 0` is bound by the
nearest enclosing quantifier; indices beyond the binders refer to *free* variables
(entries of an environment). So `∀x ∃y S(x, y)` becomes `∀ ∃ S(var 1, var 0)`.
Alpha-equivalent formulas are then literally equal, and capture-avoiding
substitution becomes a simple structural recursion: when passing under a binder,
the substitution is *lifted* (index `0` is left alone, and all other indices are
shifted up by one).

We include equality `=` as a logical primitive, since Peano arithmetic needs it.
The first-order development lives in the namespace `Foundations.Logic.FO`; its
formulas form a new type, independent of the propositional `Formula` (the
propositional connectives and rules are simply re-declared for it).
-/

namespace Foundations.Logic.FO

/-- **First-order signature.** For each arity `n`, a type of `n`-ary function symbols
and a type of `n`-ary relation symbols. Constants are `0`-ary function symbols. -/
structure Signature where
  /-- The `n`-ary function symbols. -/
  Func : Nat → Type
  /-- The `n`-ary relation symbols. -/
  Rel : Nat → Type

variable {L : Signature}

/-- **Terms** of a first-order language: variables (de Bruijn indices) and function
symbols applied to the right number of argument terms. -/
inductive Term (L : Signature) : Type where
  /-- The variable with de Bruijn index `n`. -/
  | var : Nat → Term L
  /-- An `n`-ary function symbol applied to `n` argument terms. -/
  | func {n : Nat} : L.Func n → (Fin n → Term L) → Term L

namespace Term

/-- Rename the variables of a term along a function `ρ : ℕ → ℕ`. -/
def rename (ρ : Nat → Nat) : Term L → Term L
  | var n => var (ρ n)
  | func f ts => func f fun i => rename ρ (ts i)

/-- Simultaneous substitution: replace each variable `var n` by the term `σ n`. -/
def subst (σ : Nat → Term L) : Term L → Term L
  | var n => σ n
  | func f ts => func f fun i => subst σ (ts i)

/-- Substituting every variable by itself does nothing. -/
theorem subst_var : ∀ t : Term L, t.subst var = t
  | var _ => rfl
  | func f ts => by simp only [subst]; congr; funext i; exact subst_var (ts i)

/-- Renaming is a special case of substitution. -/
theorem rename_eq_subst (ρ : Nat → Nat) : ∀ t : Term L, t.rename ρ = t.subst (fun n => var (ρ n))
  | var _ => rfl
  | func f ts => by simp only [rename, subst]; congr; funext i; exact rename_eq_subst ρ (ts i)

end Term

/-- Lift a substitution under a binder: index `0` (the newly bound variable) is
left alone; every other index `n + 1` is sent to `σ n`, with its free variables
shifted up by one so they skip over the new binder. This is what makes substitution
capture-avoiding. -/
def Subst.lift (σ : Nat → Term L) : Nat → Term L
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

/-- The substitution replacing the variable `0` by `t` and lowering every other index
by one: the effect of instantiating a quantifier `∀x φ(x)` at `t`. -/
def Subst.single (t : Term L) : Nat → Term L
  | 0 => t
  | n + 1 => .var n

/-- The identity substitution is unchanged by lifting. -/
theorem Subst.lift_var : Subst.lift (L := L) Term.var = Term.var := by
  funext n; cases n <;> rfl

/-- **First-order formulas** over a signature, with de Bruijn-indexed variables. The
quantifiers `all` and `ex` bind the variable with index `0` in their body. -/
inductive Formula (L : Signature) : Type where
  /-- Falsum `⊥`. -/
  | bot : Formula L
  /-- Equation `t = s` between terms. -/
  | eq : Term L → Term L → Formula L
  /-- An `n`-ary relation symbol applied to `n` terms. -/
  | rel {n : Nat} : L.Rel n → (Fin n → Term L) → Formula L
  /-- Implication. -/
  | imp : Formula L → Formula L → Formula L
  /-- Conjunction. -/
  | conj : Formula L → Formula L → Formula L
  /-- Disjunction. -/
  | disj : Formula L → Formula L → Formula L
  /-- Universal quantification `∀`, binding index `0`. -/
  | all : Formula L → Formula L
  /-- Existential quantification `∃`, binding index `0`. -/
  | ex : Formula L → Formula L

namespace Formula

/-- Negation `¬φ`, defined as `φ → ⊥`. -/
def neg (φ : Formula L) : Formula L := imp φ bot

/-- Capture-avoiding simultaneous substitution of terms for the free variables of a
formula; the substitution is lifted each time it passes under a quantifier. -/
def subst : (Nat → Term L) → Formula L → Formula L
  | _, bot => bot
  | σ, eq t s => eq (t.subst σ) (s.subst σ)
  | σ, rel R ts => rel R fun i => (ts i).subst σ
  | σ, imp φ ψ => imp (subst σ φ) (subst σ ψ)
  | σ, conj φ ψ => conj (subst σ φ) (subst σ ψ)
  | σ, disj φ ψ => disj (subst σ φ) (subst σ ψ)
  | σ, all φ => all (subst (Subst.lift σ) φ)
  | σ, ex φ => ex (subst (Subst.lift σ) φ)

/-- Shift all free variables up by one, making room for a new binder (used when a
formula is carried into the scope of a quantifier). -/
def shift (φ : Formula L) : Formula L := φ.subst fun n => .var (n + 1)

/-- Instantiate the outermost bound variable: `φ.inst t` is `φ(t)`, where `φ`
is thought of as the body of `∀x φ(x)` or `∃x φ(x)`. -/
def inst (φ : Formula L) (t : Term L) : Formula L := φ.subst (Subst.single t)

/-- Substituting every variable by itself does nothing. -/
theorem subst_var : ∀ φ : Formula L, φ.subst Term.var = φ
  | bot => rfl
  | eq t s => by simp [subst, Term.subst_var]
  | rel R ts => by simp [subst, Term.subst_var]
  | imp φ ψ => by simp [subst, subst_var φ, subst_var ψ]
  | conj φ ψ => by simp [subst, subst_var φ, subst_var ψ]
  | disj φ ψ => by simp [subst, subst_var φ, subst_var ψ]
  | all φ => by simp [subst, Subst.lift_var, subst_var φ]
  | ex φ => by simp [subst, Subst.lift_var, subst_var φ]

end Formula

/-- A first-order theory: a set of formulas, represented as a predicate. -/
abbrev Theory (L : Signature) := Formula L → Prop

namespace Theory

/-- The theory `Γ ∪ {φ}`. -/
def insert (Γ : Theory L) (φ : Formula L) : Theory L := fun ψ => ψ = φ ∨ Γ ψ

/-- Inclusion of theories. -/
def Subset (Γ Δ : Theory L) : Prop := ∀ ψ, Γ ψ → Δ ψ

/-- Shift every formula of a theory (used when reasoning under a new binder: the
premises must be re-indexed so that they do not mention the fresh variable `0`). -/
def shift (Γ : Theory L) : Theory L := fun ψ => ∃ χ, Γ χ ∧ ψ = χ.shift

/-- Adding the same formula preserves inclusion. -/
theorem insert_mono {Γ Δ : Theory L} (h : Subset Γ Δ) (φ : Formula L) :
    Subset (insert Γ φ) (insert Δ φ) := by
  intro ψ hψ
  rcases hψ with h' | h'
  · exact Or.inl h'
  · exact Or.inr (h ψ h')

/-- Shifting preserves inclusion. -/
theorem shift_mono {Γ Δ : Theory L} (h : Subset Γ Δ) : Subset (shift Γ) (shift Δ) :=
  fun _ ⟨χ, hχ, e⟩ => ⟨χ, h χ hχ, e⟩

end Theory

end Foundations.Logic.FO
