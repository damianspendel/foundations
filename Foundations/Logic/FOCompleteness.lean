import Foundations.Logic.TermModel

/-!
# Gödel's completeness theorem, compactness, and Löwenheim–Skolem

Kurt Gödel's doctoral dissertation (Vienna, 1929; published 1930) answered a question
posed by Hilbert and Ackermann in 1928: is the first-order calculus *complete* — is
every logically valid formula derivable? Gödel proved that it is. We follow Henkin's
1949 proof, assembled from the previous files:

1. **Model existence.** Every consistent theory has a model. To have fresh variables
   available as Henkin witnesses even when `Γ` itself uses every variable, we first
   rename the variables of `Γ` to *even* indices (`n ↦ 2n`): the odd variables are
   then fresh. We extend the renamed theory to a maximal consistent Henkin theory,
   take its term model, and read the variables back through the renaming.
2. **Completeness.** If `Γ ⊨ φ` but `Γ ⊬ φ`, then `Γ ∪ {¬φ}` is consistent, hence has
   a model — one in which `Γ` holds but `φ` fails. Contradiction. Together with
   soundness: `Γ ⊢ φ ↔ Γ ⊨ φ`.

Two celebrated corollaries:

* **Compactness** (Gödel 1930, Maltsev 1936): if every finite part of `Γ` has a model,
  so does `Γ`. Here this follows from the finiteness of derivations.
* **Downward Löwenheim–Skolem** (Löwenheim 1915, Skolem 1920): a consistent theory
  in a countable language has a *countable* model. The term model is one, since its
  elements are classes of terms. (*Skolem's paradox*: even a first-order set theory
  proving "uncountable sets exist" has a countable model.)
-/

namespace Foundations.Logic.FO

variable {L : Signature} [Signature.Countable L]

open Formula Theory

/-- The renaming `n ↦ 2n`, moving all variables to even indices. -/
def evenSubst : Nat → Term L := fun n => .var (2 * n)

/-- The substitution `n ↦ ⌊n/2⌋`, undoing `evenSubst`. -/
def halfSubst : Nat → Term L := fun n => .var (n / 2)

omit [Signature.Countable L] in
/-- Halving undoes doubling. -/
theorem subst_even_half (φ : Formula L) : (φ.subst evenSubst).subst halfSubst = φ := by
  rw [subst_subst]
  conv => rhs; rw [← subst_var φ]
  apply subst_ext; intro n
  simp [evenSubst, halfSubst, Term.subst]

omit [Signature.Countable L] in
/-- After doubling, all odd variables are fresh: a fresh supply of witnesses. -/
theorem freshSupply_even (Γ : Theory L) : FreshSupply (Γ.image evenSubst) := by
  intro k
  refine ⟨2 * k + 1, by omega, ?_⟩
  rintro _ ⟨ψ, _, rfl⟩
  exact fresh_subst ψ fun n => by simp only [evenSubst, Term.Fresh]; omega

/-- **Model existence (Henkin).** Every consistent theory in a countable language has
a model, and in fact a countable one: a structure with a surjection from `ℕ` onto its
domain. -/
theorem model_existence {Γ : Theory L} (hΓ : Consistent Γ) :
    ∃ (M : Structure L) (e : Nat → M.Dom), (∀ ψ, Γ ψ → Sat M e ψ) ∧
      ∃ f : Nat → M.Dom, ∀ x, ∃ n, f n = x := by
  have hc : Consistent (union (Γ.image evenSubst) (ofList [])) := by
    intro hb
    refine hΓ ((hb.subst_closed halfSubst).weaken ?_)
    rintro _ ⟨χ, ⟨ψ, hψ, rfl⟩ | h, rfl⟩
    · rw [subst_even_half]; exact hψ
    · simp [ofList] at h
  obtain ⟨hsub, -, hM⟩ := henkin_lindenbaum (freshSupply_even Γ) [] hc
  refine ⟨termModel hM, fun n => termEnv hM (2 * n), fun ψ hψ => ?_, termModel_countable hM⟩
  have := (truth_lemma hM (ψ.subst evenSubst)).2 (hsub _ ⟨ψ, hψ, rfl⟩)
  rw [sat_subst] at this
  exact this

/-- **Gödel's completeness theorem.** In a countable first-order language, every
semantic consequence is derivable: `Γ ⊨ φ → Γ ⊢ φ`. -/
theorem completeness {Γ : Theory L} {φ : Formula L} (h : Entails Γ φ) : Γ ⊢₁ φ := by
  refine Classical.byContradiction fun hn => ?_
  have hc : Consistent (insert Γ φ.neg) := fun hb => hn (Proves.raa hb)
  obtain ⟨M, e, he, -⟩ := model_existence hc
  exact he _ (Or.inl rfl) (h M e fun ψ hψ => he ψ (Or.inr hψ))

/-- **Soundness and completeness of first-order logic.** Derivability and semantic
consequence coincide. -/
theorem proves_iff_entails (Γ : Theory L) (φ : Formula L) : Γ ⊢₁ φ ↔ Entails Γ φ :=
  ⟨Proves.soundness, completeness⟩

omit [Signature.Countable L] in
/-- A theory with a model is consistent. -/
theorem consistent_of_sat {Γ : Theory L} {M : Structure L} {e : Nat → M.Dom}
    (h : ∀ ψ, Γ ψ → Sat M e ψ) : Consistent Γ :=
  fun hb => Proves.soundness hb M e h

omit [Signature.Countable L] in
/-- A finitely satisfiable theory is consistent. -/
theorem consistent_of_finitely_sat {Γ : Theory L}
    (h : ∀ l : List (Formula L), (∀ ψ ∈ l, Γ ψ) →
      ∃ (M : Structure L) (e : Nat → M.Dom), ∀ ψ ∈ l, Sat M e ψ) : Consistent Γ := by
  intro hb
  obtain ⟨l, hl, hd⟩ := Proves.finite_premises (Γ₀ := empty) hb (fun ψ h => Or.inr h)
  obtain ⟨M, e, he⟩ := h l hl
  exact Proves.soundness hd M e (fun ψ hψ => by
    rcases hψ with h | h
    · exact h.elim
    · exact he ψ h)

/-- **Compactness theorem for first-order logic.** If every finite subset of `Γ` has a
model, then `Γ` has a model (which may moreover be taken countable). -/
theorem compactness {Γ : Theory L}
    (h : ∀ l : List (Formula L), (∀ ψ ∈ l, Γ ψ) →
      ∃ (M : Structure L) (e : Nat → M.Dom), ∀ ψ ∈ l, Sat M e ψ) :
    ∃ (M : Structure L) (e : Nat → M.Dom), (∀ ψ, Γ ψ → Sat M e ψ) ∧
      ∃ f : Nat → M.Dom, ∀ x, ∃ n, f n = x :=
  model_existence (consistent_of_finitely_sat h)

/-- **Compactness (consequence form).** If `Γ ⊨ φ`, then finitely many premises of `Γ`
already entail `φ`. -/
theorem compactness_entails {Γ : Theory L} {φ : Formula L} (h : Entails Γ φ) :
    ∃ l : List (Formula L), (∀ ψ ∈ l, Γ ψ) ∧ Entails (ofList l) φ := by
  obtain ⟨l, hl, hd⟩ := Proves.finite_premises (Γ₀ := empty) (completeness h)
    (fun ψ h => Or.inr h)
  refine ⟨l, hl, fun M e he => Proves.soundness hd M e fun ψ hψ => ?_⟩
  rcases hψ with h | h
  · exact h.elim
  · exact he ψ h

/-- **Downward Löwenheim–Skolem theorem.** If a theory in a countable language has
any model at all (of whatever size), then it has a countable model: one admitting a
surjection from `ℕ` onto its domain. -/
theorem lowenheim_skolem {Γ : Theory L} {M : Structure L} {e : Nat → M.Dom}
    (h : ∀ ψ, Γ ψ → Sat M e ψ) :
    ∃ (N : Structure L) (e' : Nat → N.Dom), (∀ ψ, Γ ψ → Sat N e' ψ) ∧
      ∃ f : Nat → N.Dom, ∀ x, ∃ n, f n = x :=
  model_existence (consistent_of_sat h)

end Foundations.Logic.FO
