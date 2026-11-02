import Foundations.Logic.GodelIID3Arith

/-!
# Atomic formulas and bounded quantifiers, internally

Continuing the internal Σ-completeness argument inside a model `N` of PA:

* `der_terms2`: a true (or false) relation between the *values* of two terms, derivable for
  their numerals, is derivable for the terms themselves (via `der_eval`); this gives the
  atomic cases `t = s`, `t ≠ s`, `t ≤ s`, `¬ t ≤ s` of formalised Σ-completeness;
* `der_ball`, `der_ballS`: if `ψ(x̄)` is derivable for every `x ≤ T` (resp. `x < T`), then
  `∀x ≤ T. ψ` (resp. `∀x < T. ψ`) is derivable. Here `T` may be non-standard, so this is an
  internal induction on the bound, carried by the instance
  `(∀x ≤ g. ψ) → ψ(g+1) → ∀x ≤ g+1. ψ` of a theorem of PA at every `g`.

*Place in the argument.* Gödel (1931) only sketched the second incompleteness theorem;
Hilbert and Bernays (1939) carried out the arithmetisation it needs; Löb (1955) reduced it to
three derivability conditions, of which (D3) — formalised Σ₁-completeness — is the hard one.
Feferman (1960) showed that the theorem depends on how provability is expressed, which is why
it matters that `provDP` is a derivation predicate rather than one engineered to satisfy (D3).
This file is one step of the proof of (D3) for `provDP` assembled in `GodelIID3Main`.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability GodelII

namespace GodelII

/-- Shifting the free variables of a formula up by `k`. -/
def shiftF (k : Nat) (φ : Formula Arith) : Formula Arith := φ.subst fun m => Term.var (m + k)

/-- Satisfaction of a shifted formula. -/
theorem sat_shiftF {M : Structure Arith} (k : Nat) (φ : Formula Arith) (e : Nat → M.Dom) :
    Sat M e (shiftF k φ) ↔ Sat M (fun m => e (m + k)) φ :=
  sat_subst φ e _

end GodelII

namespace PAModel

variable {N : PAModel}

/-- Derivability of a shifted formula. -/
theorem der_shiftF_iff {k : Nat} {χ : Formula Arith} {v : Nat → N.Dom} :
    Der (shiftF k χ) v ↔ Der χ (fun m => v (m + k)) :=
  der_subst_iff fun _ => tcM_var0 _ _

/-- Removing a shift under a pushed value. -/
theorem der_shiftF_cons {χ : Formula Arith} {a : N.Dom} {w : Nat → N.Dom}
    (h : Der (shiftF 1 χ) (Env.cons a w)) : Der χ w := by
  have h' := der_shiftF_iff.1 h
  have e : (fun m => Env.cons a w (m + 1)) = w := funext fun _ => rfl
  rw [e] at h'; exact h'

/-- `≤` of the model, as the formula `∃z (z + t = s)`. -/
theorem sat_substL_leF (t s : Term Arith) (e : Nat → N.Dom) :
    Sat N.M e (substL [t, s] leF) ↔ t.eval N.M e ≤ s.eval N.M e := by
  rw [substL, sat_subst, sat_leF]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' _ _⟩,
    fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' _ _⟩⟩

/-- **From values to terms.** If a two-variable formula `ψ(x, y)` is derivable at the
numerals of the values of `t` and `s`, then `ψ(t, s)` is derivable. -/
theorem der_terms2 (ψ : Formula Arith)
    (hψ : ∀ (M : PAModel) (e e' : Nat → M.Dom), e 0 = e' 0 → e 1 = e' 1 →
      (Sat M.M e ψ ↔ Sat M.M e' ψ))
    (hψc : ∀ w w' : Nat → N.Dom, w 0 = w' 0 → w 1 = w' 1 → codeM ψ 0 w = codeM ψ 0 w')
    (t s : Term Arith) (e : Nat → N.Dom) (h : Der ψ (env2 (t.eval N.M e) (s.eval N.M e))) :
    Der (substL [t, s] ψ) e := by
  let a := t.eval N.M e
  let b := s.eval N.M e
  let E : Nat → N.Dom := Env.cons a (Env.cons b e)
  have hL := der_inst (N := N) (χ := imp (eq (shiftT 2 t) (v 0)) (imp (eq (shiftT 2 s) (v 1))
      (imp ψ (shiftF 2 (substL [t, s] ψ)))))
    (pa_of_valid fun M e => by
      simp only [Formula.Sat, eval_shiftT, eval_var_M]
      intro h₁ h₂ h₃
      rw [sat_shiftF, substL, sat_subst]
      refine (hψ M _ _ ?_ ?_).1 h₃
      · simp only [List.getD_cons_zero]; exact h₁.symm
      · simp only [List.getD_cons_succ, List.getD_cons_zero]; exact h₂.symm) E
  have p₁ : Der (eq (shiftT 2 t) (v 0)) E :=
    der_congr (by simp [codeM, eqT, tcM_shiftT, E, a]) (der_eval t e)
  have p₂ : Der (eq (shiftT 2 s) (v 1)) E :=
    der_congr (by simp [codeM, eqT, tcM_shiftT, E, b]) (der_eval s e)
  have p₃ : Der ψ E := der_congr (hψc (env2 a b) E rfl rfl) h
  have := der_shiftF_iff.1 (der_mp (der_mp (der_mp hL p₁) p₂) p₃)
  exact this

/-! ## Atomic formulas -/

/-- True equations are derivable. -/
theorem der_atom_eq {t s : Term Arith} {e : Nat → N.Dom} (h : t.eval N.M e = s.eval N.M e) :
    Der (eq t s) e := by
  have := der_terms2 (eq (v 0) (v 1)) (fun M e e' h₀ h₁ => by simp [Formula.Sat, h₀, h₁])
    (fun w w' h₀ h₁ => by simp [codeM, h₀, h₁]) t s e
    (der_congr (by simp [codeM, h]) (der_refl (t.eval N.M e)))
  exact this

/-- False equations are refutable. -/
theorem der_atom_neq {t s : Term Arith} {e : Nat → N.Dom} (h : t.eval N.M e ≠ s.eval N.M e) :
    Der (neg (eq t s)) e := by
  have := der_terms2 neqF (fun M e e' h₀ h₁ => by simp [neqF, neg, Formula.Sat, h₀, h₁])
    (fun w w' h₀ h₁ => by simp [codeM, neqF, neg, h₀, h₁]) t s e (der_neq _ _ h)
  exact this

/-- The code of `leF` depends on two values only. -/
theorem codeM_leF (w w' : Nat → N.Dom) (h₀ : w 0 = w' 0) (h₁ : w 1 = w' 1) :
    codeM leF 0 w = codeM leF 0 w' := by
  simp [codeM, leF, tcM, h₀, h₁]

/-- The satisfaction of `leF` depends on two values only. -/
theorem sat_leF_congr (M : PAModel) (e e' : Nat → M.Dom) (h₀ : e 0 = e' 0) (h₁ : e 1 = e' 1) :
    Sat M.M e leF ↔ Sat M.M e' leF := by
  rw [sat_leF, sat_leF, h₀, h₁]

/-- True inequalities `t ≤ s` are derivable. -/
theorem der_atom_le {t s : Term Arith} {e : Nat → N.Dom} (h : t.eval N.M e ≤ s.eval N.M e) :
    Der (substL [t, s] leF) e :=
  der_terms2 leF sat_leF_congr codeM_leF t s e (der_le h)

/-- False inequalities `t ≤ s` are refutable. -/
theorem der_atom_nle {t s : Term Arith} {e : Nat → N.Dom} (h : ¬ t.eval N.M e ≤ s.eval N.M e) :
    Der (neg (substL [t, s] leF)) e := by
  have hlt : s.eval N.M e < t.eval N.M e := by
    rcases le_or_lt' (s.eval N.M e) (t.eval N.M e) with h' | h'
    · exact absurd h' h
    · exact h'
  have := der_terms2 (neg leF)
    (fun M e e' h₀ h₁ => by simp only [neg, Formula.Sat]; rw [sat_leF_congr M e e' h₀ h₁])
    (fun w w' h₀ h₁ => by simp only [neg, codeM]; rw [codeM_leF w w' h₀ h₁]) t s e
    (der_nle _ _ hlt)
  exact this

/-! ## Bounded quantifiers -/

/-- The formula `∀x ≤ v₀. ψ(x, v₁, v₂, …)`, the bound as the free variable `0`. -/
def ballF (ψ : Formula Arith) : Formula Arith :=
  all (imp (boundF (v 0)) (ψ.subst (Env.cons (v 0) fun m => v (m + 2))))

/-- Meaning of `ballF`. -/
theorem sat_ballF (M : PAModel) (ψ : Formula Arith) (g : M.Dom) (e : Nat → M.Dom) :
    Sat M.M (Env.cons g e) (ballF ψ) ↔ ∀ x, x ≤ g → Sat M.M (Env.cons x e) ψ := by
  simp only [ballF, Formula.Sat, sat_boundF, sat_subst]
  refine forall_congr' fun x => imp_congr ?_ ?_
  · simp only [eval_var_M, cons_0]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' _ _⟩,
      fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' _ _⟩⟩
  · have : (fun n => (Env.cons (v 0) (fun m => v (m + 2)) n).eval M.M (Env.cons x (Env.cons g e))) =
        Env.cons x e := by
      funext n; cases n <;> rfl
    rw [this]

/-- Meaning of `ballF`, at an arbitrary assignment. -/
theorem sat_ballF' (M : PAModel) (ψ : Formula Arith) (e : Nat → M.Dom) :
    Sat M.M e (ballF ψ) ↔ ∀ x, x ≤ e 0 → Sat M.M (Env.cons x fun n => e (n + 1)) ψ := by
  have he : e = Env.cons (e 0) (fun n => e (n + 1)) := by funext n; cases n <;> rfl
  conv => lhs; rw [he]
  exact sat_ballF M ψ _ _

/-- Meaning of `eqT`. -/
theorem sat_eqT (M : PAModel) (T : Term Arith) (e : Nat → M.Dom) :
    Sat M.M e (eqT T) ↔ T.eval M.M (fun m => e (m + 1)) = e 0 := by
  simp only [eqT, Formula.Sat, eval_shiftT, eval_var_M]

/-- Meaning of a `≤`-bounded universal quantifier. -/
theorem sat_ball_bound (M : PAModel) (T : Term Arith) (ψ : Formula Arith) (e : Nat → M.Dom) :
    Sat M.M e (all (imp (boundF T) ψ)) ↔ ∀ x, x ≤ T.eval M.M e → Sat M.M (Env.cons x e) ψ := by
  simp only [Formula.Sat, sat_boundF]
  refine forall_congr' fun x => imp_congr ?_ Iff.rfl
  exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' _ _⟩,
    fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' _ _⟩⟩

/-- Meaning of a `<`-bounded universal quantifier. -/
theorem sat_ballS_bound (M : PAModel) (T : Term Arith) (ψ : Formula Arith) (e : Nat → M.Dom) :
    Sat M.M e (all (imp (boundSF T) ψ)) ↔ ∀ x, x < T.eval M.M e → Sat M.M (Env.cons x e) ψ := by
  simp only [Formula.Sat, sat_boundSF, ms_eq]
  refine forall_congr' fun x => imp_congr ?_ Iff.rfl
  exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' _ _⟩,
    fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' _ _⟩⟩

/-- **Internal bounded induction**: if `ψ(x̄)` is derivable for all `x ≤ G`, then so is
`∀x ≤ Ḡ. ψ`. -/
theorem der_ballF (ψ : Formula Arith) (e : Nat → N.Dom) (G : N.Dom)
    (h : ∀ x, x ≤ G → Der ψ (Env.cons x e)) : Der (ballF ψ) (Env.cons G e) := by
  have hP : N.Dfn fun p => (fun (g : N.Dom) (p : Nat → N.Dom) =>
      g ≤ p 0 → Der (ballF ψ) (Env.cons g fun n => p (n + 1))) (p 0) (fun n => p (n + 1)) := by
    refine Dfn.imp (by simp only [le_def]; dfn) ((der_dfn_at (ballF ψ)
      (τ := fun n p => match n with | 0 => p 0 | n + 1 => p (n + 2)) fun n => ?_).congr' fun p => ?_)
    · match n with
      | 0 => exact DfnT.var 0
      | n + 1 => exact DfnT.var (n + 2)
    · have : (fun n => match n with | 0 => p 0 | n + 1 => p (n + 2)) =
          Env.cons (p 0) fun n => p (n + 1 + 1) := by
        funext n; cases n <;> rfl
      simp only [this]
  let τ₀ : Nat → Term Arith := Env.cons zero fun m => v m
  let τ₁ : Nat → Term Arith := Env.cons (succ (v 0)) fun m => v (m + 1)
  have hτ₀ : ∀ m, tcM (τ₀ m) 0 e = NumN ((Env.cons (0 : N.Dom) e) m) := fun m => by
    cases m <;> simp [τ₀, numN_zero]
  have hτ₁ : ∀ g : N.Dom, ∀ m, tcM (τ₁ m) 0 (Env.cons g e) = NumN ((Env.cons (g + 1) e) m) :=
    fun g m => by cases m <;> simp [τ₁, numN_succ]
  have key := induction (P := fun g p => g ≤ p 0 → Der (ballF ψ) (Env.cons g fun n => p (n + 1)))
    hP (Env.cons G e) (fun _ => by
      have hL := der_inst (N := N) (χ := imp (ψ.subst τ₀) ((ballF ψ).subst τ₀))
        (pa_of_valid fun M e => by
          simp only [Formula.Sat, sat_subst]
          have h0 : (fun n => (τ₀ n).eval M.M e) = Env.cons (0 : M.Dom) e := by
            funext n; cases n <;> simp [τ₀]
          rw [h0, sat_ballF]
          intro h x hx
          rw [eq_zero_of_le_zero hx]; exact h) e
      exact (der_subst_iff hτ₀).1 (der_mp hL ((der_subst_iff hτ₀).2 (h 0 (zero_le' G)))))
    (fun g ih hg => by
      have hL := der_inst (N := N) (χ := imp (ballF ψ) (imp (ψ.subst τ₁) ((ballF ψ).subst τ₁)))
        (pa_of_valid fun M e => by
          simp only [Formula.Sat, sat_subst]
          have h1 : (fun n => (τ₁ n).eval M.M e) = Env.cons (e 0 + 1) (fun n => e (n + 1)) := by
            funext n; cases n <;> simp [τ₁]
          rw [h1]
          have he : e = Env.cons (e 0) (fun n => e (n + 1)) := by funext n; cases n <;> rfl
          rw [he, sat_ballF, sat_ballF]
          simp only [cons_0]
          intro hb hs x hx
          rcases eq_or_lt_of_le hx with rfl | hx'
          · exact hs
          · exact hb x (lt_succ_iff'.1 hx'))
        (Env.cons g e)
      have hg' : g ≤ G := le_trans' (le_of_lt' (lt_succ_self' g)) hg
      exact (der_subst_iff (hτ₁ g)).1 (der_mp (der_mp hL (ih hg'))
        ((der_subst_iff (hτ₁ g)).2 (h _ hg))))
  exact key G (le_refl' G)

/-- `∀x ≤ T. ψ` is derivable when `ψ(x̄)` is, for every `x ≤ T`. -/
theorem der_ball (ψ : Formula Arith) (T : Term Arith) (e : Nat → N.Dom)
    (h : ∀ x, x ≤ T.eval N.M e → Der ψ (Env.cons x e)) : Der (all (imp (boundF T) ψ)) e := by
  have hL := der_inst (N := N) (χ := imp (eqT T) (imp (ballF ψ)
      (shiftF 1 (all (imp (boundF T) ψ)))))
    (pa_of_valid fun M e => by
      show Sat M.M e (eqT T) → Sat M.M e (ballF ψ) → Sat M.M e (shiftF 1 _)
      rw [sat_eqT, sat_ballF', sat_shiftF, sat_ball_bound]
      intro hT hb x hx
      exact hb x (hT ▸ hx))
    (Env.cons (T.eval N.M e) e)
  exact der_shiftF_cons (der_mp (der_mp hL (der_eval T e)) (der_ballF ψ e _ h))

/-- `∀x < T. ψ` is derivable when `ψ(x̄)` is, for every `x < T`. -/
theorem der_ballS (ψ : Formula Arith) (T : Term Arith) (e : Nat → N.Dom)
    (h : ∀ x, x < T.eval N.M e → Der ψ (Env.cons x e)) : Der (all (imp (boundSF T) ψ)) e := by
  rcases zero_or_succ (T.eval N.M e) with h0 | ⟨G, hG⟩
  · have hL := der_inst (N := N) (χ := imp (eq T zero) (all (imp (boundSF T) ψ)))
      (pa_of_valid fun M e => by
        show Sat M.M e (eq T zero) → _
        rw [sat_ballS_bound]
        intro hT x hx
        simp only [Formula.Sat, eval_zero_M, mz_eq] at hT
        rw [hT] at hx
        exact absurd hx (not_lt_zero' x)) e
    exact der_mp hL (der_atom_eq (by rw [h0, eval_zero_M, mz_eq]))
  · have hL := der_inst (N := N) (χ := imp (eq (shiftT 1 T) (succ (v 0))) (imp (ballF ψ)
        (shiftF 1 (all (imp (boundSF T) ψ)))))
      (pa_of_valid fun M e => by
        show Sat M.M e (eq _ _) → Sat M.M e (ballF ψ) → Sat M.M e (shiftF 1 _)
        rw [sat_ballF', sat_shiftF, sat_ballS_bound]
        simp only [Formula.Sat, eval_shiftT, eval_succ_M, eval_var_M, ms_eq]
        intro hT hb x hx
        rw [hT] at hx
        exact hb x (lt_succ_iff'.1 hx))
      (Env.cons G e)
    have p₁ : Der (eq (shiftT 1 T) (succ (v 0))) (Env.cons G e) := by
      have := der_eval T e
      rw [hG] at this
      exact der_congr (by simp [codeM, eqT, tcM_shiftT, numN_succ]) this
    have p₂ := der_ballF ψ e G fun x hx => h x (by rw [hG]; exact lt_succ_iff'.2 hx)
    exact der_shiftF_cons (der_mp (der_mp hL p₁) p₂)

end PAModel

end Foundations.Logic.FO
