import Foundations.Logic.PropSyntax

/-!
# Propositional logic: semantics and truth tables

Syntax says which strings are sentences; *semantics* says what they mean. For
classical propositional logic the meaning of a formula is fixed once we know the
truth value of each atom. This is the bivalent, truth-functional picture made
precise by Boole, Frege, Peirce, and — as the method of *truth tables* — by Post
and Wittgenstein (*Tractatus*, 1921).

* A **valuation** assigns a Boolean truth value to every atom.
* `eval v φ` computes the truth value of `φ` under `v`, connective by connective.
* `φ` is a **tautology** if it is true under every valuation.
* `Γ ⊨ φ` (**semantic consequence**): every valuation making all of `Γ` true makes
  `φ` true. This is the model-theoretic notion of "following from", due in its
  modern form to Tarski (1936).

Although there are uncountably many valuations, the truth of `φ` depends only on
the finitely many atoms occurring in it. So "is `φ` a tautology?" can be settled by
checking finitely many rows of a truth table. We implement this procedure and
**prove it correct**, which yields a `Decidable` instance for tautologyhood.
-/

namespace Foundations.Logic

/-- A valuation: an assignment of a truth value to every propositional atom. -/
abbrev Valuation := Nat → Bool

namespace Formula

/-- The truth value of a formula under a valuation, computed by the truth tables of
the connectives (`→` is material implication). -/
def eval (v : Valuation) : Formula → Bool
  | bot => false
  | var n => v n
  | imp φ ψ => !eval v φ || eval v ψ
  | conj φ ψ => eval v φ && eval v ψ
  | disj φ ψ => eval v φ || eval v ψ

/-- A negation is true exactly when the negated formula is false. -/
@[simp] theorem eval_neg (v : Valuation) (φ : Formula) : eval v (neg φ) = !eval v φ := by
  simp [neg, eval]

/-- **Tautology.** A formula is a tautology if it is true under every valuation. -/
def Tautology (φ : Formula) : Prop := ∀ v : Valuation, eval v φ = true

/-- **Coincidence lemma.** Two valuations agreeing on the atoms of `φ` give `φ` the
same truth value: the meaning of a formula depends only on its own atoms. -/
theorem eval_congr {v w : Valuation} :
    ∀ φ : Formula, (∀ a ∈ atoms φ, v a = w a) → eval v φ = eval w φ
  | bot, _ => rfl
  | var n, h => by simp [eval, h n (by simp [atoms])]
  | imp φ ψ, h => by
      simp only [eval]
      rw [eval_congr φ (fun a ha => h a (by simp [atoms, ha])),
          eval_congr ψ (fun a ha => h a (by simp [atoms, ha]))]
  | conj φ ψ, h => by
      simp only [eval]
      rw [eval_congr φ (fun a ha => h a (by simp [atoms, ha])),
          eval_congr ψ (fun a ha => h a (by simp [atoms, ha]))]
  | disj φ ψ, h => by
      simp only [eval]
      rw [eval_congr φ (fun a ha => h a (by simp [atoms, ha])),
          eval_congr ψ (fun a ha => h a (by simp [atoms, ha]))]

end Formula

namespace Valuation

/-- Change the value of a valuation at a single atom `a` to `b`. -/
def update (v : Valuation) (a : Nat) (b : Bool) : Valuation :=
  fun n => if n = a then b else v n

/-- The rows of a truth table for the atoms in `l`: a finite list of valuations
(`2 ^ length l` of them) covering every combination of values on `l`, and `false`
elsewhere. -/
def rows : List Nat → List Valuation
  | [] => [fun _ => false]
  | a :: l => (rows l).flatMap fun v => [update v a false, update v a true]

/-- **Truth tables are exhaustive.** For any valuation `v` and list of atoms `l`
there is a row of the truth table for `l` agreeing with `v` on every atom of `l`. -/
theorem exists_row (v : Valuation) :
    ∀ l : List Nat, ∃ w ∈ rows l, ∀ a ∈ l, w a = v a
  | [] => ⟨fun _ => false, by simp [rows], by simp⟩
  | a :: l => by
      obtain ⟨w, hw, hagree⟩ := exists_row v l
      refine ⟨update w a (v a), ?_, ?_⟩
      · simp only [rows, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        refine ⟨w, hw, ?_⟩
        cases v a <;> simp
      · intro b hb
        simp only [update]
        by_cases hba : b = a
        · simp [hba]
        · simp only [hba, ite_false]
          simp only [List.mem_cons, hba, false_or] at hb
          exact hagree b hb

end Valuation

namespace Formula

/-- The truth-table procedure: evaluate `φ` on every row of the truth table for its
atoms and check that every row gives `true`. -/
def truthTable (φ : Formula) : Bool :=
  (Valuation.rows (atoms φ)).all fun v => eval v φ

/-- **Correctness of truth tables.** The truth-table procedure returns `true`
exactly when the formula is a tautology. -/
theorem truthTable_iff (φ : Formula) : truthTable φ = true ↔ Tautology φ := by
  constructor
  · intro h v
    obtain ⟨w, hw, hagree⟩ := Valuation.exists_row v (atoms φ)
    have hw' : eval w φ = true := by
      simp only [truthTable, List.all_eq_true] at h
      exact h w hw
    rw [← hw']
    exact eval_congr φ (fun a ha => (hagree a ha).symm)
  · intro h
    simp only [truthTable, List.all_eq_true]
    exact fun v _ => h v

/-- **Decidability of tautologyhood.** Whether a propositional formula is a tautology
is decidable, by the (verified) truth-table method. -/
instance decTautology (φ : Formula) : Decidable (Tautology φ) :=
  decidable_of_iff _ (truthTable_iff φ)

/-- Peirce's law `((p → q) → p) → p` is a tautology, checked by the truth-table
procedure (a small example of the decision procedure at work). -/
example : Tautology (imp (imp (imp (var 0) (var 1)) (var 0)) (var 0)) := by decide

/-- The law of excluded middle `p ∨ ¬p` is a tautology. -/
example : Tautology (disj (var 0) (neg (var 0))) := by decide

/-- A bare atom is not a tautology. -/
example : ¬ Tautology (var 0) := by decide

end Formula

namespace Theory

/-- A valuation *satisfies* a theory if it makes every premise true. -/
def Satisfies (v : Valuation) (Γ : Theory) : Prop := ∀ ψ, Γ ψ → ψ.eval v = true

/-- A theory is *satisfiable* if some valuation makes all of its premises true. -/
def Satisfiable (Γ : Theory) : Prop := ∃ v, Satisfies v Γ

end Theory

/-- **Semantic consequence** `Γ ⊨ φ`: every valuation satisfying all premises in `Γ`
also makes `φ` true. -/
def Entails (Γ : Theory) (φ : Formula) : Prop :=
  ∀ v : Valuation, Theory.Satisfies v Γ → φ.eval v = true

@[inherit_doc] infix:50 " ⊨ " => Entails

/-- A formula is a tautology iff it is a semantic consequence of no premises. -/
theorem tautology_iff_entails_empty (φ : Formula) : φ.Tautology ↔ Theory.empty ⊨ φ :=
  ⟨fun h v _ => h v, fun h v => h v (fun _ hψ => hψ.elim)⟩

/-- Semantic consequence is monotone: more premises, more consequences. -/
theorem Entails.mono {Γ Δ : Theory} {φ : Formula} (h : Γ ⊨ φ) (hsub : Γ.Subset Δ) :
    Δ ⊨ φ :=
  fun v hv => h v (fun ψ hψ => hv ψ (hsub ψ hψ))

end Foundations.Logic
