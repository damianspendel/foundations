import Foundations.Logic.Henkin

/-!
# The term model of a maximal consistent Henkin theory

Henkin's remarkable observation: a maximal consistent Henkin theory `M` *is* already
a description of a model, and the model can be built **out of syntax itself**.

* The individuals are the **terms**, except that two terms `s, t` with `s = t ∈ M`
  must denote the same individual. So the domain is the quotient of the set of terms
  by provable equality — an equivalence relation, and indeed a *congruence*, thanks
  to the equality lemmas of `FOProofTheory`.
* A function symbol acts on (classes of) terms by forming the compound term.
* A relation holds of (classes of) terms iff the atomic formula is in `M`.
* A variable denotes its own class.

The **truth lemma** then states that a formula is satisfied in this term model iff it
belongs to `M`. Maximality handles the connectives (as in the propositional case);
the Henkin property handles the quantifiers: `∃x φ(x) ∈ M` gives a witness term `t`
with `φ(t) ∈ M`, and the class of `t` is the required individual. The induction is on
the *size* of formulas, since `φ(t)` is not a subformula of `∃x φ(x)` but has the
same size as `φ`.

Since each individual is the class of some term, and (for a countable language) the
terms can be enumerated, the term model is **countable** — the germ of the
Löwenheim–Skolem theorem.
-/

namespace Foundations.Logic.FO

variable {L : Signature}

open Formula Theory

namespace MaximalHenkin

variable {M : Theory L} (hM : MaximalHenkin M)
include hM

/-- A maximal consistent theory is deductively closed. -/
theorem closed {φ : Formula L} (h : M ⊢₁ φ) : M φ := by
  rcases hM.maximal φ with h' | h'
  · exact h'
  · refine absurd ?_ hM.consistent
    exact Classical.byContradiction fun hc => h' fun hb => hc (Proves.impE (Proves.impI hb) h)

/-- `¬φ ∈ M` iff `φ ∉ M`. -/
theorem neg_iff (φ : Formula L) : M φ.neg ↔ ¬ M φ := by
  constructor
  · intro h₁ h₂
    exact hM.consistent (Proves.impE (.hyp h₁) (.hyp h₂))
  · intro h
    rcases hM.maximal φ with h' | h'
    · exact absurd h' h
    · exact hM.closed (Proves.impI (Classical.byContradiction h'))

/-- `φ → ψ ∈ M` iff (`φ ∈ M` implies `ψ ∈ M`). -/
theorem imp_iff (φ ψ : Formula L) : M (imp φ ψ) ↔ (M φ → M ψ) := by
  constructor
  · exact fun h h₁ => hM.closed (Proves.impE (.hyp h) (.hyp h₁))
  · intro h
    by_cases h₁ : M φ
    · exact hM.closed (Proves.impI (Proves.hyp (Or.inr (h h₁))))
    · have hn := (hM.neg_iff φ).2 h₁
      exact hM.closed (Proves.impI (Proves.botE (Proves.impE (.hyp (Or.inr hn))
        (Proves.assume _ _))))

/-- `φ ∧ ψ ∈ M` iff both are. -/
theorem conj_iff (φ ψ : Formula L) : M (conj φ ψ) ↔ M φ ∧ M ψ :=
  ⟨fun h => ⟨hM.closed (Proves.conjE₁ (.hyp h)), hM.closed (Proves.conjE₂ (.hyp h))⟩,
    fun h => hM.closed (Proves.conjI (.hyp h.1) (.hyp h.2))⟩

/-- `φ ∨ ψ ∈ M` iff one of them is. -/
theorem disj_iff (φ ψ : Formula L) : M (disj φ ψ) ↔ M φ ∨ M ψ := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    have h₁ := (hM.neg_iff φ).2 fun h' => hn (Or.inl h')
    have h₂ := (hM.neg_iff ψ).2 fun h' => hn (Or.inr h')
    refine hM.consistent (Proves.disjE (.hyp h) ?_ ?_)
    · exact Proves.impE (.hyp (Or.inr h₁)) (Proves.assume _ _)
    · exact Proves.impE (.hyp (Or.inr h₂)) (Proves.assume _ _)
  · rintro (h | h)
    · exact hM.closed (Proves.disjI₁ (.hyp h))
    · exact hM.closed (Proves.disjI₂ (.hyp h))

/-- `∀x φ ∈ M` iff every instance `φ(t)` is in `M` (uses the Henkin property). -/
theorem all_iff (φ : Formula L) : M (all φ) ↔ ∀ t, M (φ.inst t) := by
  constructor
  · exact fun h t => hM.closed (Proves.allE t (.hyp h))
  · intro h
    refine Classical.byContradiction fun hn => ?_
    have h₁ := hM.closed (Proves.ex_neg_of_neg_all (.hyp ((hM.neg_iff _).2 hn)))
    obtain ⟨t, ht⟩ := hM.henkin _ h₁
    exact (hM.neg_iff _).1 ht (h t)

/-- `∃x φ ∈ M` iff some instance `φ(t)` is in `M` (uses the Henkin property). -/
theorem ex_iff (φ : Formula L) : M (ex φ) ↔ ∃ t, M (φ.inst t) :=
  ⟨hM.henkin φ, fun ⟨t, ht⟩ => hM.closed (Proves.exI t (.hyp ht))⟩

/-- Provable equality is an equivalence relation on terms. -/
theorem eq_equivalence : Equivalence fun s t : Term L => M (eq s t) :=
  ⟨fun t => hM.closed (Proves.refl t),
   fun h => hM.closed (Proves.eq_symm (.hyp h)),
   fun h₁ h₂ => hM.closed (Proves.eq_trans (.hyp h₁) (.hyp h₂))⟩

end MaximalHenkin

variable {M : Theory L} (hM : MaximalHenkin M)

/-- Terms identified up to provable equality in `M`. -/
def termSetoid : Setoid (Term L) := ⟨fun s t => M (eq s t), hM.eq_equivalence⟩

/-- A chosen representative term of an equivalence class. -/
noncomputable def rep (q : Quotient (termSetoid hM)) : Term L :=
  Classical.choose (Quotient.exists_rep q)

/-- The representative of the class of `t` is provably equal to `t`. -/
theorem rep_mk (t : Term L) : M (eq (rep hM (Quotient.mk _ t)) t) :=
  Quotient.exact (Classical.choose_spec (Quotient.exists_rep (Quotient.mk (termSetoid hM) t)))

/-- **The term model** of a maximal consistent Henkin theory: classes of terms modulo
provable equality, with function symbols acting syntactically and relations holding
exactly when the corresponding atomic formula is in `M`. -/
noncomputable def termModel : Structure L where
  Dom := Quotient (termSetoid hM)
  funcs := fun f a => Quotient.mk _ (.func f fun i => rep hM (a i))
  rels := fun R a => M (.rel R fun i => rep hM (a i))

/-- The canonical environment: each variable denotes its own class. -/
def termEnv : Nat → (termModel hM).Dom := fun n => Quotient.mk (termSetoid hM) (.var n)

/-- In the term model, every term denotes its own class. -/
theorem eval_termEnv : ∀ t : Term L, t.eval (termModel hM) (termEnv hM) = Quotient.mk _ t
  | .var _ => rfl
  | .func f ts => by
      simp only [Term.eval]
      have ih : (fun i => (ts i).eval (termModel hM) (termEnv hM)) =
          fun i => Quotient.mk (termSetoid hM) (ts i) := funext fun i => eval_termEnv (ts i)
      rw [ih]
      exact Quotient.sound (hM.closed (Proves.func_congr f fun i => .hyp (rep_mk hM (ts i))))

/-- Every individual of the term model is denoted by some term. -/
theorem termModel_denoted (x : (termModel hM).Dom) :
    ∃ t : Term L, t.eval (termModel hM) (termEnv hM) = x := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  exact ⟨t, eval_termEnv hM t⟩

/-- **Truth lemma.** A formula is satisfied in the term model (under the canonical
environment) iff it belongs to the maximal consistent Henkin theory `M`. -/
theorem truth_lemma : ∀ φ : Formula L, Sat (termModel hM) (termEnv hM) φ ↔ M φ
  | .bot => ⟨False.elim, fun h => hM.consistent (.hyp h)⟩
  | .eq s t => by
      simp only [Sat, eval_termEnv]
      exact ⟨Quotient.exact, fun h => Quotient.sound h⟩
  | .rel R ts => by
      simp only [Sat, eval_termEnv]
      show M (.rel R fun i => rep hM (Quotient.mk _ (ts i))) ↔ M (.rel R ts)
      constructor
      · exact fun h => hM.closed (Proves.rel_congr R (fun i => .hyp (rep_mk hM (ts i))) (.hyp h))
      · exact fun h => hM.closed (Proves.rel_congr R
          (fun i => Proves.eq_symm (.hyp (rep_mk hM (ts i)))) (.hyp h))
  | .imp φ ψ => by
      simp only [Sat, truth_lemma φ, truth_lemma ψ, hM.imp_iff]
  | .conj φ ψ => by
      simp only [Sat, truth_lemma φ, truth_lemma ψ, hM.conj_iff]
  | .disj φ ψ => by
      simp only [Sat, truth_lemma φ, truth_lemma ψ, hM.disj_iff]
  | .all φ => by
      rw [hM.all_iff]
      show (∀ x, Sat (termModel hM) (Env.cons x (termEnv hM)) φ) ↔ _
      constructor
      · intro h t
        have := h (Quotient.mk _ t)
        rw [← eval_termEnv hM t, ← sat_inst] at this
        exact (truth_lemma (φ.inst t)).1 this
      · intro h x
        obtain ⟨t, rfl⟩ := Quotient.exists_rep x
        rw [← eval_termEnv hM t, ← sat_inst]
        exact (truth_lemma (φ.inst t)).2 (h t)
  | .ex φ => by
      rw [hM.ex_iff]
      show (∃ x, Sat (termModel hM) (Env.cons x (termEnv hM)) φ) ↔ _
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨t, rfl⟩ := Quotient.exists_rep x
        rw [← eval_termEnv hM t, ← sat_inst] at hx
        exact ⟨t, (truth_lemma (φ.inst t)).1 hx⟩
      · rintro ⟨t, ht⟩
        refine ⟨Quotient.mk _ t, ?_⟩
        rw [← eval_termEnv hM t, ← sat_inst]
        exact (truth_lemma (φ.inst t)).2 ht
termination_by φ => φ.size
decreasing_by all_goals simp [Formula.size]; try omega

/-- **The term model is countable** (for a countable language): there is a surjection
from `ℕ` onto its domain. -/
theorem termModel_countable [Signature.Countable L] :
    ∃ f : Nat → (termModel hM).Dom, ∀ x, ∃ n, f n = x := by
  refine ⟨fun m => match (termsUpTo L (pairAt m).1)[(pairAt m).2]? with
    | some t => Quotient.mk _ t
    | none => Quotient.mk _ (.var 0), fun x => ?_⟩
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  obtain ⟨k, hk⟩ := exists_mem_termsUpTo t
  obtain ⟨j, hj, hjt⟩ := List.getElem_of_mem hk
  obtain ⟨m, hm⟩ := pairAt_surj k j
  refine ⟨m, ?_⟩
  simp only [hm, List.getElem?_eq_getElem hj, hjt]
  rfl

end Foundations.Logic.FO
