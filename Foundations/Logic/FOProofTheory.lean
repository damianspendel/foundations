import Foundations.Logic.FOSubstitution

/-!
# Proof theory of first-order natural deduction

Before we can build models out of syntax (Henkin's method, next files), we need
several facts about *derivations themselves*:

* **Substitution invariance.** If `Γ ⊢ φ` then `Γ[σ] ⊢ φ[σ]` for any substitution
  `σ`: a derivation with free variables is really a *schema* of derivations. In
  particular derivations can be shifted under a binder.
* **Finiteness.** A derivation uses only finitely many premises (relative to a fixed
  "background" theory). This is the syntactic heart of compactness.
* **Equality reasoning.** Symmetry, transitivity and *congruence* of `=` (equal
  arguments give equal values and equivalent atomic formulas), all derived from
  Leibniz's law. These make "provable equality" a congruence relation, so that we
  can later take the quotient of terms by it.
* **The witness lemma.** The crucial step in Henkin's proof (1949): if `∃x φ(x)` is
  derivable and `y` is a variable not occurring anywhere, then *naming* a witness by
  adding `φ(y)` cannot produce a contradiction. Informally: "let `y` be such that
  `φ(y)`" is a harmless move — the rule of ∃-elimination, internalised.
-/

namespace Foundations.Logic.FO

variable {L : Signature}

open Formula

namespace Theory

/-- The image of a theory under a substitution. -/
def image (Γ : Theory L) (σ : Nat → Term L) : Theory L := fun ψ => ∃ χ, Γ χ ∧ ψ = χ.subst σ

/-- The union of two theories. -/
def union (Γ Δ : Theory L) : Theory L := fun ψ => Γ ψ ∨ Δ ψ

/-- The finite theory whose members are those of a list. -/
def ofList (l : List (Formula L)) : Theory L := fun ψ => ψ ∈ l

/-- The empty theory. -/
def empty : Theory L := fun _ => False

/-- Inclusion of theories is reflexive. -/
theorem Subset.refl (Γ : Theory L) : Γ.Subset Γ := fun _ h => h

/-- Inclusion of theories is transitive. -/
theorem Subset.trans {Γ Δ Θ : Theory L} (h₁ : Γ.Subset Δ) (h₂ : Δ.Subset Θ) : Γ.Subset Θ :=
  fun ψ h => h₂ ψ (h₁ ψ h)

/-- Substituting into an extended theory. -/
theorem image_insert (Γ : Theory L) (φ : Formula L) (σ : Nat → Term L) :
    ((insert Γ φ).image σ).Subset (insert (Γ.image σ) (φ.subst σ)) := by
  rintro _ ⟨χ, hχ | hχ, rfl⟩
  · exact Or.inl (by rw [hχ])
  · exact Or.inr ⟨χ, hχ, rfl⟩

/-- Substituting (lifted) into a shifted theory. -/
theorem image_shift (Γ : Theory L) (σ : Nat → Term L) :
    ((shift Γ).image (Subst.lift σ)).Subset (shift (Γ.image σ)) := by
  rintro _ ⟨_, ⟨χ, hχ, rfl⟩, rfl⟩
  exact ⟨χ.subst σ, ⟨χ, hχ, rfl⟩, shift_subst_lift χ σ⟩

/-- Union is monotone in both arguments. -/
theorem union_mono {Γ Γ' Δ Δ' : Theory L} (h₁ : Γ.Subset Γ') (h₂ : Δ.Subset Δ') :
    (union Γ Δ).Subset (union Γ' Δ') := by
  rintro ψ (h | h)
  · exact Or.inl (h₁ ψ h)
  · exact Or.inr (h₂ ψ h)

/-- A list is included in its extension on the right. -/
theorem ofList_append_left (l₁ l₂ : List (Formula L)) : (ofList l₁).Subset (ofList (l₁ ++ l₂)) :=
  fun _ h => List.mem_append_left _ h

/-- A list is included in its extension on the left. -/
theorem ofList_append_right (l₁ l₂ : List (Formula L)) :
    (ofList l₂).Subset (ofList (l₁ ++ l₂)) :=
  fun _ h => List.mem_append_right _ h

/-- Membership in a concatenation of lists of premises. -/
theorem all_append {Γ : Theory L} {l₁ l₂ : List (Formula L)} (h₁ : ∀ ψ ∈ l₁, Γ ψ)
    (h₂ : ∀ ψ ∈ l₂, Γ ψ) : ∀ ψ ∈ l₁ ++ l₂, Γ ψ := by
  intro ψ hψ
  rcases List.mem_append.1 hψ with h | h
  · exact h₁ ψ h
  · exact h₂ ψ h

/-- A finite list of members of a shifted theory comes from a finite list of members
of the original theory. -/
theorem pullback_shift {Γ : Theory L} : ∀ l : List (Formula L), (∀ ψ ∈ l, shift Γ ψ) →
    ∃ l' : List (Formula L), (∀ χ ∈ l', Γ χ) ∧ (ofList l).Subset (shift (ofList l'))
  | [], _ => ⟨[], by simp, fun _ h => by simp [ofList] at h⟩
  | ψ :: l, h => by
      obtain ⟨χ, hχ, rfl⟩ := h ψ (by simp)
      obtain ⟨l', hl', hsub⟩ := pullback_shift l (fun ψ hψ => h ψ (by simp [hψ]))
      refine ⟨χ :: l', fun θ hθ => ?_, fun θ hθ => ?_⟩
      · rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hχ
        · exact hl' θ hθ
      · rcases List.mem_cons.1 hθ with rfl | hθ
        · exact ⟨χ, by simp [ofList], rfl⟩
        · obtain ⟨θ', h₁, h₂⟩ := hsub θ hθ
          exact ⟨θ', List.mem_cons_of_mem _ h₁, h₂⟩

end Theory

open Theory

namespace Proves

/-- The newly added premise is derivable. -/
theorem assume (Γ : Theory L) (φ : Formula L) : insert Γ φ ⊢₁ φ := hyp (Or.inl rfl)

/-- Weakening by a single premise. -/
theorem weaken₁ {Γ : Theory L} {φ : Formula L} (h : Γ ⊢₁ φ) (ψ : Formula L) :
    insert Γ ψ ⊢₁ φ :=
  h.weaken fun _ h => Or.inr h

/-- **Substitution invariance of derivations.** If `Γ ⊢ φ` then `Γ[σ] ⊢ φ[σ]`. -/
theorem subst_closed {Γ : Theory L} {φ : Formula L} (h : Γ ⊢₁ φ) :
    ∀ σ : Nat → Term L, Γ.image σ ⊢₁ φ.subst σ := by
  induction h with
  | hyp hφ => exact fun σ => hyp ⟨_, hφ, rfl⟩
  | impI _ ih => exact fun σ => impI ((ih σ).weaken (image_insert _ _ σ))
  | impE _ _ ih₁ ih₂ => exact fun σ => impE (ih₁ σ) (ih₂ σ)
  | conjI _ _ ih₁ ih₂ => exact fun σ => conjI (ih₁ σ) (ih₂ σ)
  | conjE₁ _ ih => exact fun σ => conjE₁ (ih σ)
  | conjE₂ _ ih => exact fun σ => conjE₂ (ih σ)
  | disjI₁ _ ih => exact fun σ => disjI₁ (ih σ)
  | disjI₂ _ ih => exact fun σ => disjI₂ (ih σ)
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
      exact fun σ => disjE (ih₁ σ) ((ih₂ σ).weaken (image_insert _ _ σ))
        ((ih₃ σ).weaken (image_insert _ _ σ))
  | botE _ ih => exact fun σ => botE (ih σ)
  | raa _ ih => exact fun σ => raa ((ih σ).weaken (image_insert _ _ σ))
  | allI _ ih => exact fun σ => allI ((ih (Subst.lift σ)).weaken (image_shift _ σ))
  | allE t _ ih =>
      intro σ; rw [inst_subst]; exact allE (t.subst σ) (ih σ)
  | exI t _ ih =>
      intro σ; exact exI (t.subst σ) (by rw [← inst_subst]; exact ih σ)
  | @exE Γ φ ψ _ _ ih₁ ih₂ =>
      intro σ
      refine exE (ih₁ σ) ?_
      rw [← shift_subst_lift]
      exact (ih₂ (Subst.lift σ)).weaken ((image_insert _ _ _).trans
        (insert_mono (image_shift Γ σ) _))
  | refl t => exact fun σ => refl _
  | subst _ _ ih₁ ih₂ =>
      intro σ; rw [inst_subst]
      exact subst (ih₁ σ) (by rw [← inst_subst]; exact ih₂ σ)

/-- Derivations can be shifted: `Γ ⊢ φ` implies `Γ↑ ⊢ φ↑`. -/
theorem shift_closed {Γ : Theory L} {φ : Formula L} (h : Γ ⊢₁ φ) : shift Γ ⊢₁ φ.shift :=
  h.subst_closed fun n => .var (n + 1)

/-- **Finiteness of first-order derivations.** If `φ` is derivable from premises
drawn from `Γ₀ ∪ Γ`, then already from `Γ₀` together with finitely many premises of
`Γ`. -/
theorem finite_premises {Δ : Theory L} {φ : Formula L} (h : Δ ⊢₁ φ) :
    ∀ {Γ₀ Γ : Theory L}, Δ.Subset (union Γ₀ Γ) →
      ∃ l : List (Formula L), (∀ ψ ∈ l, Γ ψ) ∧ union Γ₀ (ofList l) ⊢₁ φ := by
  -- inclusion bookkeeping used repeatedly
  have ins : ∀ {Γ₀ Δ : Theory L} {φ : Formula L},
      (union (insert Γ₀ φ) Δ).Subset (insert (union Γ₀ Δ) φ) := by
    rintro Γ₀ Δ φ ψ ((rfl | h) | h)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have ins' : ∀ {Δ Γ₀ Γ : Theory L} {φ : Formula L}, Δ.Subset (union Γ₀ Γ) →
      (insert Δ φ).Subset (union (insert Γ₀ φ) Γ) := by
    rintro Δ Γ₀ Γ φ hs ψ (rfl | h)
    · exact Or.inl (Or.inl rfl)
    · rcases hs ψ h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  have shf : ∀ {Δ Γ₀ Γ : Theory L}, Δ.Subset (union Γ₀ Γ) →
      (shift Δ).Subset (union (shift Γ₀) (shift Γ)) := by
    rintro Δ Γ₀ Γ hs _ ⟨χ, hχ, rfl⟩
    rcases hs χ hχ with h | h
    · exact Or.inl ⟨χ, h, rfl⟩
    · exact Or.inr ⟨χ, h, rfl⟩
  have shu : ∀ {Γ₀ A B : Theory L}, A.Subset (shift B) →
      (union (shift Γ₀) A).Subset (shift (union Γ₀ B)) := by
    rintro Γ₀ A B hAB ψ (⟨χ, hχ, rfl⟩ | h)
    · exact ⟨χ, Or.inl hχ, rfl⟩
    · obtain ⟨χ, hχ, rfl⟩ := hAB ψ h
      exact ⟨χ, Or.inr hχ, rfl⟩
  have L₁ := fun {Γ₀ : Theory L} (l₁ l₂ : List (Formula L)) =>
    union_mono (Subset.refl Γ₀) (ofList_append_left l₁ l₂)
  have L₂ := fun {Γ₀ : Theory L} (l₁ l₂ : List (Formula L)) =>
    union_mono (Subset.refl Γ₀) (ofList_append_right l₁ l₂)
  induction h with
  | @hyp Δ φ hφ =>
      intro Γ₀ Γ hs
      rcases hs φ hφ with h | h
      · exact ⟨[], by simp, hyp (Or.inl h)⟩
      · exact ⟨[φ], by simpa using h, hyp (Or.inr (by simp [ofList]))⟩
  | impI _ ih =>
      intro Γ₀ Γ hs
      obtain ⟨l, hl, hd⟩ := ih (ins' hs)
      exact ⟨l, hl, impI (hd.weaken ins)⟩
  | impE _ _ ih₁ ih₂ =>
      intro Γ₀ Γ hs
      obtain ⟨l₁, hl₁, hd₁⟩ := ih₁ hs
      obtain ⟨l₂, hl₂, hd₂⟩ := ih₂ hs
      exact ⟨l₁ ++ l₂, all_append hl₁ hl₂, impE (hd₁.weaken (L₁ _ _)) (hd₂.weaken (L₂ _ _))⟩
  | conjI _ _ ih₁ ih₂ =>
      intro Γ₀ Γ hs
      obtain ⟨l₁, hl₁, hd₁⟩ := ih₁ hs
      obtain ⟨l₂, hl₂, hd₂⟩ := ih₂ hs
      exact ⟨l₁ ++ l₂, all_append hl₁ hl₂, conjI (hd₁.weaken (L₁ _ _)) (hd₂.weaken (L₂ _ _))⟩
  | conjE₁ _ ih => intro Γ₀ Γ hs; obtain ⟨l, hl, hd⟩ := ih hs; exact ⟨l, hl, conjE₁ hd⟩
  | conjE₂ _ ih => intro Γ₀ Γ hs; obtain ⟨l, hl, hd⟩ := ih hs; exact ⟨l, hl, conjE₂ hd⟩
  | disjI₁ _ ih => intro Γ₀ Γ hs; obtain ⟨l, hl, hd⟩ := ih hs; exact ⟨l, hl, disjI₁ hd⟩
  | disjI₂ _ ih => intro Γ₀ Γ hs; obtain ⟨l, hl, hd⟩ := ih hs; exact ⟨l, hl, disjI₂ hd⟩
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
      intro Γ₀ Γ hs
      obtain ⟨l₁, hl₁, hd₁⟩ := ih₁ hs
      obtain ⟨l₂, hl₂, hd₂⟩ := ih₂ (ins' hs)
      obtain ⟨l₃, hl₃, hd₃⟩ := ih₃ (ins' hs)
      refine ⟨l₁ ++ (l₂ ++ l₃), all_append hl₁ (all_append hl₂ hl₃),
        disjE (hd₁.weaken (L₁ _ _)) (hd₂.weaken ?_) (hd₃.weaken ?_)⟩
      · exact ins.trans (insert_mono ((L₁ l₂ l₃).trans (L₂ _ _)) _)
      · exact ins.trans (insert_mono ((L₂ l₂ l₃).trans (L₂ _ _)) _)
  | botE _ ih => intro Γ₀ Γ hs; obtain ⟨l, hl, hd⟩ := ih hs; exact ⟨l, hl, botE hd⟩
  | raa _ ih =>
      intro Γ₀ Γ hs
      obtain ⟨l, hl, hd⟩ := ih (ins' hs)
      exact ⟨l, hl, raa (hd.weaken ins)⟩
  | allI _ ih =>
      intro Γ₀ Γ hs
      obtain ⟨l, hl, hd⟩ := ih (shf hs)
      obtain ⟨l', hl', hsub⟩ := pullback_shift l hl
      exact ⟨l', hl', allI (hd.weaken (shu hsub))⟩
  | allE t _ ih => intro Γ₀ Γ hs; obtain ⟨l, hl, hd⟩ := ih hs; exact ⟨l, hl, allE t hd⟩
  | exI t _ ih => intro Γ₀ Γ hs; obtain ⟨l, hl, hd⟩ := ih hs; exact ⟨l, hl, exI t hd⟩
  | exE _ _ ih₁ ih₂ =>
      intro Γ₀ Γ hs
      obtain ⟨l₁, hl₁, hd₁⟩ := ih₁ hs
      obtain ⟨l₂, hl₂, hd₂⟩ := ih₂ (ins' (shf hs))
      obtain ⟨l₂', hl₂', hsub⟩ := pullback_shift l₂ hl₂
      refine ⟨l₁ ++ l₂', all_append hl₁ hl₂', exE (hd₁.weaken (L₁ _ _)) (hd₂.weaken ?_)⟩
      refine ins.trans (insert_mono ?_ _)
      exact (shu (hsub.trans (shift_mono (ofList_append_right l₁ l₂'))))
  | refl t => intro Γ₀ Γ hs; exact ⟨[], by simp, refl t⟩
  | subst _ _ ih₁ ih₂ =>
      intro Γ₀ Γ hs
      obtain ⟨l₁, hl₁, hd₁⟩ := ih₁ hs
      obtain ⟨l₂, hl₂, hd₂⟩ := ih₂ hs
      exact ⟨l₁ ++ l₂, all_append hl₁ hl₂, subst (hd₁.weaken (L₁ _ _)) (hd₂.weaken (L₂ _ _))⟩

/-! ## Equality reasoning -/

/-- Transitivity of equality, from Leibniz's law. -/
theorem eq_trans {Γ : Theory L} {r s t : Term L} (h₁ : Γ ⊢₁ eq r s) (h₂ : Γ ⊢₁ eq s t) :
    Γ ⊢₁ eq r t := by
  have key : ∀ u : Term L, (eq (r.rename Nat.succ) (.var 0)).inst u = eq r u := by
    intro u; simp only [inst, Formula.subst, Term.rename_succ_single]; rfl
  have := subst (φ := eq (r.rename Nat.succ) (.var 0)) h₂ (by rw [key]; exact h₁)
  rwa [key] at this

/-- **Replacing arguments one at a time.** Let `Φ` be a family of formulas indexed by
argument tuples, such that changing one argument is an instance of Leibniz's law.
Then provably equal tuples give provably equivalent formulas. -/
theorem replace_args {Γ : Theory L} {n : Nat} (Φ : (Fin n → Term L) → Formula L)
    (hΦ : ∀ (us : Fin n → Term L) (k : Fin n), ∃ χ : Formula L,
      ∀ w, χ.inst w = Φ (fun i => if i = k then w else us i))
    {ts ts' : Fin n → Term L} (h : ∀ i, Γ ⊢₁ eq (ts i) (ts' i)) (h₀ : Γ ⊢₁ Φ ts) :
    Γ ⊢₁ Φ ts' := by
  let mix : Nat → Fin n → Term L := fun k i => if i.val < k then ts' i else ts i
  have step : ∀ k, Γ ⊢₁ Φ (mix k) := by
    intro k
    induction k with
    | zero =>
        have : mix 0 = ts := by funext i; simp [mix]
        rw [this]; exact h₀
    | succ k ih =>
        by_cases hk : k < n
        · let kk : Fin n := ⟨k, hk⟩
          obtain ⟨χ, hχ⟩ := hΦ (mix k) kk
          have e₁ : (fun i => if i = kk then ts kk else mix k i) = mix k := by
            funext i
            by_cases hi : i = kk
            · subst hi; simp [mix, kk]
            · simp [hi]
          have e₂ : (fun i => if i = kk then ts' kk else mix k i) = mix (k + 1) := by
            funext i
            by_cases hi : i = kk
            · subst hi; simp [mix, kk]
            · have : i.val ≠ k := fun e => hi (Fin.ext e)
              simp only [hi, ite_false, mix]
              by_cases h' : i.val < k
              · simp [h', show i.val < k + 1 by omega]
              · simp [h', show ¬ i.val < k + 1 by omega]
          have := subst (φ := χ) (h kk) (by rw [hχ, e₁]; exact ih)
          rwa [hχ, e₂] at this
        · have : mix (k + 1) = mix k := by
            funext i
            have : i.val < k := by omega
            simp [mix, this, show i.val < k + 1 by omega]
          rw [this]; exact ih
  have : mix n = ts' := by funext i; simp [mix, i.isLt]
  rw [← this]; exact step n

/-- Changing one argument of a tuple, written with a placeholder variable `0`. -/
theorem inst_args (us : Fin n → Term L) (k : Fin n) (w : Term L) :
    (fun i => (if i = k then Term.var 0 else (us i).rename Nat.succ).subst (Subst.single w)) =
      (fun i => if i = k then w else us i) := by
  funext i
  by_cases hi : i = k
  · simp only [hi, ite_true]; rfl
  · simp only [hi, ite_false, Term.rename_succ_single]

/-- **Congruence for function symbols.** Provably equal arguments give provably
equal values. -/
theorem func_congr {Γ : Theory L} {n : Nat} (f : L.Func n) {ts ts' : Fin n → Term L}
    (h : ∀ i, Γ ⊢₁ eq (ts i) (ts' i)) : Γ ⊢₁ eq (.func f ts) (.func f ts') := by
  refine replace_args (fun us => eq (.func f ts) (.func f us)) ?_ h (refl _)
  intro us k
  refine ⟨eq ((Term.func f ts).rename Nat.succ)
    (.func f fun i => if i = k then .var 0 else (us i).rename Nat.succ), fun w => ?_⟩
  simp only [inst, Formula.subst, Term.rename_succ_single]
  rw [← inst_args us k w]; rfl

/-- **Congruence for relation symbols.** Provably equal arguments give provably
equivalent atomic formulas. -/
theorem rel_congr {Γ : Theory L} {n : Nat} (R : L.Rel n) {ts ts' : Fin n → Term L}
    (h : ∀ i, Γ ⊢₁ eq (ts i) (ts' i)) (h₀ : Γ ⊢₁ rel R ts) : Γ ⊢₁ rel R ts' := by
  refine replace_args (fun us => rel R us) ?_ h h₀
  intro us k
  refine ⟨rel R fun i => if i = k then .var 0 else (us i).rename Nat.succ, fun w => ?_⟩
  simp only [inst, Formula.subst]
  rw [← inst_args us k w]

/-! ## Quantifier lemmas -/

/-- Classical quantifier duality: from `¬∀x φ` derive `∃x ¬φ`. -/
theorem ex_neg_of_neg_all {Γ : Theory L} {φ : Formula L} (h : Γ ⊢₁ (all φ).neg) :
    Γ ⊢₁ ex φ.neg := by
  apply raa
  refine impE (h.weaken₁ _) (allI (raa ?_))
  -- in context: shift (Γ ∪ {¬∃¬φ}) ∪ {¬φ}
  have hyp₁ : insert (shift (insert Γ (ex φ.neg).neg)) φ.neg ⊢₁ imp (ex φ.neg).shift bot :=
    hyp (Or.inr ⟨(ex φ.neg).neg, Or.inl rfl, rfl⟩)
  refine impE hyp₁ (exI (.var 0) ?_)
  show _ ⊢₁ (φ.neg.subst (Subst.lift fun n => .var (n + 1))).inst (.var 0)
  rw [lift_shift_inst_zero]
  exact assume _ _

/-- **The witness lemma** (Henkin). Suppose the variable `x` occurs free neither in
the premises `Δ` nor in `∃y φ(y)`. If `Δ ⊢ ∃y φ(y)` and `Δ ∪ {φ(x)}` is
inconsistent, then `Δ` itself is inconsistent. So a fresh variable can always be
consistently declared to be a witness. -/
theorem witness {Δ : Theory L} {φ : Formula L} {x : Nat} (hΔ : ∀ χ, Δ χ → χ.Fresh x)
    (hφ : (ex φ).Fresh x) (hex : Δ ⊢₁ ex φ) (h : insert Δ (φ.inst (.var x)) ⊢₁ bot) :
    Δ ⊢₁ bot := by
  let σ : Nat → Term L := fun n => if n = x then .var 0 else .var (n + 1)
  have h₂ := (impI h).subst_closed σ
  have e₁ : (φ.inst (.var x)).subst σ = φ := by
    simp only [inst, subst_subst]
    conv => rhs; rw [← subst_var φ]
    refine subst_congr_fresh φ (x := x + 1) (fun n hn => ?_) hφ
    cases n with
    | zero => simp [Subst.single, Term.subst, σ]
    | succ m =>
        have : m ≠ x := by omega
        simp [Subst.single, Term.subst, σ, this]
  have hsub : (Δ.image σ).Subset (shift Δ) := by
    rintro _ ⟨χ, hχ, rfl⟩
    refine ⟨χ, hχ, subst_congr_fresh χ (fun n hn => ?_) (hΔ χ hχ)⟩
    simp [σ, hn]
  have h₃ : shift Δ ⊢₁ φ.neg := by
    have := h₂.weaken hsub
    change shift Δ ⊢₁ ((φ.inst (.var x)).neg).subst σ at this
    rwa [neg_subst, e₁] at this
  exact exE hex (impE (h₃.weaken₁ _) (assume _ _))

end Proves

end Foundations.Logic.FO
