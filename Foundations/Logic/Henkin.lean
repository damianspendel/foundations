import Foundations.Logic.FOEnumeration

/-!
# Henkin theories: Lindenbaum's lemma with witnesses

Leon Henkin's dissertation (1947; published 1949) gave the proof of Gödel's
completeness theorem that is now standard. Its idea: a consistent theory `Γ` should
be enlarged to a theory `M` that is

* **maximal consistent** — it decides every formula, like a complete description
  of a possible world (Lindenbaum's construction, as in the propositional case); and
* **Henkin** (or *witness-complete*) — whenever `M` contains `∃x φ(x)`, it also
  contains `φ(t)` for some term `t`: every existential claim has a *named* witness.

From such an `M` one can read off a model whose individuals are the terms
themselves (next file).

To have names available for witnesses, we keep infinitely many variables *fresh*
for the base theory (`FreshSupply`). During the construction, whenever we add an
existential formula `∃x φ(x)` we simultaneously add `φ(y)` for a variable `y` not
occurring in anything so far; the witness lemma (`Proves.witness`) guarantees this
preserves consistency. Formulas are processed in the order given by the enumeration
`formsUpTo` of the previous file.
-/

namespace Foundations.Logic.FO

variable {L : Signature}

open Formula Theory

/-- A first-order theory is **consistent** if it does not derive `⊥`. -/
def Consistent (Γ : Theory L) : Prop := ¬ (Γ ⊢₁ bot)

/-- A theory is **maximal consistent and Henkin** if it is consistent, decides every
formula (adding any formula not already in it makes it inconsistent), and contains a
witness instance `φ(t)` for each existential `∃x φ(x)` it contains. -/
structure MaximalHenkin (M : Theory L) : Prop where
  /-- `M` is consistent. -/
  consistent : Consistent M
  /-- `M` cannot be consistently extended. -/
  maximal : ∀ ψ, M ψ ∨ ¬ Consistent (insert M ψ)
  /-- Every existential in `M` has a witness in `M`. -/
  henkin : ∀ φ, M (ex φ) → ∃ t, M (φ.inst t)

/-- A theory has a **fresh supply** of variables if arbitrarily large variables occur
free in none of its formulas. -/
def FreshSupply (Γ₀ : Theory L) : Prop := ∀ k, ∃ x, k ≤ x ∧ ∀ χ, Γ₀ χ → χ.Fresh x

section Construction

variable {Γ₀ : Theory L} (hΓ₀ : FreshSupply Γ₀)

/-- A variable fresh for the base theory, for the formula `ψ`, and for the finitely
many formulas `A` added so far. -/
noncomputable def freshVar (A : List (Formula L)) (ψ : Formula L) : Nat :=
  Classical.choose (hΓ₀ (Classical.choose (eventually_fresh_list (ψ :: A))))

/-- The chosen variable really is fresh for everything in sight. -/
theorem freshVar_spec (A : List (Formula L)) (ψ : Formula L) :
    (∀ χ, Γ₀ χ → χ.Fresh (freshVar hΓ₀ A ψ)) ∧ ∀ χ ∈ ψ :: A, χ.Fresh (freshVar hΓ₀ A ψ) := by
  have h₁ := Classical.choose_spec (hΓ₀ (Classical.choose (eventually_fresh_list (ψ :: A))))
  have h₂ := Classical.choose_spec (eventually_fresh_list (ψ :: A))
  exact ⟨h₁.2, h₂ _ h₁.1⟩

/-- The witness formulas to be added along with `ψ`: `φ(y)` with `y` fresh if `ψ` is
`∃x φ(x)`, and nothing otherwise. -/
noncomputable def witnesses (A : List (Formula L)) : Formula L → List (Formula L)
  | ex φ => [φ.inst (.var (freshVar hΓ₀ A (ex φ)))]
  | _ => []

/-- `witnesses` is either empty, or the single witness instance of an existential. -/
theorem witnesses_cases (A : List (Formula L)) (ψ : Formula L) :
    witnesses hΓ₀ A ψ = [] ∨
      ∃ φ, ψ = ex φ ∧ witnesses hΓ₀ A ψ = [φ.inst (.var (freshVar hΓ₀ A ψ))] := by
  cases ψ <;> simp [witnesses]

/-- The formulas added when `ψ` is accepted: `ψ` itself and its witnesses. -/
noncomputable def henkinAdd (A : List (Formula L)) (ψ : Formula L) : List (Formula L) :=
  ψ :: witnesses hΓ₀ A ψ

/-- Adding an acceptable formula together with its witness preserves consistency. -/
theorem consistent_henkinAdd {A : List (Formula L)} {ψ : Formula L}
    (h : Consistent (union Γ₀ (ofList (ψ :: A)))) :
    Consistent (union Γ₀ (ofList (henkinAdd hΓ₀ A ψ ++ A))) := by
  -- `Γ₀ ∪ (ψ :: A)` written as an insertion
  have eqv : (union Γ₀ (ofList (ψ :: A))).Subset (insert (union Γ₀ (ofList A)) ψ) := by
    rintro χ (h | h)
    · exact Or.inr (Or.inl h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inr h)
  have eqv' : (insert (union Γ₀ (ofList A)) ψ).Subset (union Γ₀ (ofList (ψ :: A))) := by
    rintro χ (rfl | h | h)
    · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)
  rcases witnesses_cases hΓ₀ A ψ with hw | ⟨φ, rfl, hw⟩
  · intro hb
    refine h (hb.weaken ?_)
    rintro χ (h | h)
    · exact Or.inl h
    · simp only [henkinAdd, hw, ofList, List.cons_append, List.nil_append] at h
      exact Or.inr h
  · intro hb
    obtain ⟨hfΓ, hfA⟩ := freshVar_spec hΓ₀ A (ex φ)
    let x := freshVar hΓ₀ A (ex φ)
    refine h (Proves.witness (Δ := union Γ₀ (ofList (ex φ :: A))) (x := x) ?_ ?_
      (Proves.hyp (Or.inr (List.mem_cons_self ..))) (hb.weaken ?_))
    · rintro χ (h | h)
      · exact hfΓ χ h
      · exact hfA χ h
    · exact hfA _ (List.mem_cons_self ..)
    · rintro χ (h | h)
      · exact Or.inr (Or.inl h)
      · simp only [henkinAdd, hw, ofList, List.cons_append, List.mem_cons] at h
        rcases h with rfl | rfl | h
        · exact Or.inr (Or.inr (List.mem_cons_self ..))
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

open Classical in
/-- Process a list of formulas: accept each (with its witness) when consistent. -/
noncomputable def extendH (A : List (Formula L)) : List (Formula L) → List (Formula L)
  | [] => A
  | ψ :: l => extendH
      (if Consistent (union Γ₀ (ofList (ψ :: A))) then henkinAdd hΓ₀ A ψ ++ A else A) l

/-- Processing only adds formulas. -/
theorem subset_extendH : ∀ (l A : List (Formula L)), ∀ χ ∈ A, χ ∈ extendH hΓ₀ A l
  | [], _, _, h => h
  | ψ :: l, A, χ, h => by
      unfold extendH
      split
      · exact subset_extendH l _ χ (List.mem_append_right _ h)
      · exact subset_extendH l _ χ h

/-- Processing preserves consistency. -/
theorem consistent_extendH : ∀ (l A : List (Formula L)), Consistent (union Γ₀ (ofList A)) →
    Consistent (union Γ₀ (ofList (extendH hΓ₀ A l)))
  | [], _, h => h
  | ψ :: l, A, h => by
      unfold extendH
      split
      · exact consistent_extendH l _ (consistent_henkinAdd hΓ₀ (by assumption))
      · exact consistent_extendH l _ h

/-- Each processed formula was either accepted with its witnesses, or rejected
because it is inconsistent with part of the result. -/
theorem extendH_decides : ∀ (l A : List (Formula L)) (ψ : Formula L), ψ ∈ l →
    ∃ A' : List (Formula L), (∀ χ ∈ A', χ ∈ extendH hΓ₀ A l) ∧
      ((∀ χ ∈ henkinAdd hΓ₀ A' ψ, χ ∈ extendH hΓ₀ A l) ∨
        ¬ Consistent (union Γ₀ (ofList (ψ :: A'))))
  | [], _, _, h => by simp at h
  | θ :: l, A, ψ, h => by
      rcases List.mem_cons.1 h with rfl | h
      · refine ⟨A, fun χ hχ => ?_, ?_⟩
        · unfold extendH; split
          · exact subset_extendH hΓ₀ l _ χ (List.mem_append_right _ hχ)
          · exact subset_extendH hΓ₀ l _ χ hχ
        · unfold extendH
          by_cases hc : Consistent (union Γ₀ (ofList (ψ :: A)))
          · left; intro χ hχ; simp only [hc, ↓reduceIte]
            exact subset_extendH hΓ₀ l _ χ (List.mem_append_left _ hχ)
          · right; exact hc
      · unfold extendH
        exact extendH_decides l _ ψ h

variable [Signature.Countable L] (A₀ : List (Formula L))

/-- The `n`-th stage of the Henkin construction (a finite list of added formulas). -/
noncomputable def henkinStage : Nat → List (Formula L)
  | 0 => A₀
  | n + 1 => extendH hΓ₀ (henkinStage n) (formsUpTo L n)

/-- The stages increase. -/
theorem henkinStage_mono {m n : Nat} (h : m ≤ n) :
    ∀ χ ∈ henkinStage hΓ₀ A₀ m, χ ∈ henkinStage hΓ₀ A₀ n := by
  induction h with
  | refl => exact fun _ h => h
  | step _ ih => exact fun χ h => subset_extendH hΓ₀ _ _ χ (ih χ h)

/-- The limit of the Henkin construction: the base theory together with everything
added at some stage. -/
def henkinLimit : Theory L := union Γ₀ fun χ => ∃ n, χ ∈ henkinStage hΓ₀ A₀ n

/-- Finitely many formulas of the limit already occur at a single stage. -/
theorem henkinStage_finite :
    ∀ l : List (Formula L), (∀ χ ∈ l, ∃ n, χ ∈ henkinStage hΓ₀ A₀ n) →
      ∃ n, ∀ χ ∈ l, χ ∈ henkinStage hΓ₀ A₀ n
  | [], _ => ⟨0, by simp⟩
  | ψ :: l, h => by
      obtain ⟨m, hm⟩ := h ψ (by simp)
      obtain ⟨n, hn⟩ := henkinStage_finite l (fun χ hχ => h χ (by simp [hχ]))
      refine ⟨max m n, fun χ hχ => ?_⟩
      rcases List.mem_cons.1 hχ with rfl | hχ
      · exact henkinStage_mono hΓ₀ A₀ (Nat.le_max_left _ _) _ hm
      · exact henkinStage_mono hΓ₀ A₀ (Nat.le_max_right _ _) _ (hn χ hχ)

/-- **Henkin–Lindenbaum lemma.** If the base theory has a fresh supply of variables
and is consistent together with the finite list `A₀`, then it extends (together with
`A₀`) to a maximal consistent Henkin theory. -/
theorem henkin_lindenbaum (hc : Consistent (union Γ₀ (ofList A₀))) :
    Γ₀.Subset (henkinLimit hΓ₀ A₀) ∧ (∀ χ ∈ A₀, henkinLimit hΓ₀ A₀ χ) ∧
      MaximalHenkin (henkinLimit hΓ₀ A₀) := by
  have cons_stage : ∀ n, Consistent (union Γ₀ (ofList (henkinStage hΓ₀ A₀ n))) := by
    intro n
    induction n with
    | zero => exact hc
    | succ n ih => exact consistent_extendH hΓ₀ _ _ ih
  have hcons : Consistent (henkinLimit hΓ₀ A₀) := by
    intro hb
    obtain ⟨l, hl, hd⟩ := Proves.finite_premises hb (Subset.refl _)
    obtain ⟨n, hn⟩ := henkinStage_finite hΓ₀ A₀ l hl
    exact cons_stage n (hd.weaken (union_mono (Subset.refl _) hn))
  -- inclusion of a stage-relative theory in the limit
  have into : ∀ {n : Nat} {A' : List (Formula L)} (ψ : Formula L),
      (∀ χ ∈ A', χ ∈ henkinStage hΓ₀ A₀ n) →
      (union Γ₀ (ofList (ψ :: A'))).Subset (insert (henkinLimit hΓ₀ A₀) ψ) := by
    intro n A' ψ hA' χ hχ
    rcases hχ with h | h
    · exact Or.inr (Or.inl h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨n, hA' χ h⟩)
  refine ⟨fun χ h => Or.inl h, fun χ h => Or.inr ⟨0, h⟩, hcons, ?_, ?_⟩
  · intro ψ
    obtain ⟨n, hn⟩ := exists_mem_formsUpTo ψ
    obtain ⟨A', hA', h⟩ := extendH_decides hΓ₀ (formsUpTo L n) (henkinStage hΓ₀ A₀ n) ψ hn
    rcases h with h | h
    · exact Or.inl (Or.inr ⟨n + 1, h ψ (List.mem_cons_self ..)⟩)
    · exact Or.inr fun hc' => h fun hb => hc' (hb.weaken (into (n := n + 1) ψ hA'))
  · intro φ hφ
    obtain ⟨n, hn⟩ := exists_mem_formsUpTo (ex φ)
    obtain ⟨A', hA', h⟩ :=
      extendH_decides hΓ₀ (formsUpTo L n) (henkinStage hΓ₀ A₀ n) (ex φ) hn
    rcases h with h | h
    · exact ⟨.var (freshVar hΓ₀ A' (ex φ)), Or.inr ⟨n + 1, h _ (by simp [henkinAdd, witnesses])⟩⟩
    · refine absurd ?_ h
      intro hb
      refine hcons ((hb.weaken (into (n := n + 1) _ hA')).weaken ?_)
      rintro χ (rfl | h)
      · exact hφ
      · exact h

end Construction

end Foundations.Logic.FO
