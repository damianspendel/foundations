import Foundations.Logic.FOSoundness

/-!
# The algebra of de Bruijn substitution

To prove Gödel's completeness theorem we need to *transform derivations*: rename
variables in them, and move them under binders. For that, the purely syntactic
behaviour of substitution must be under control. This file develops the small
"substitution calculus" that de Bruijn indices make possible (in the style of
Abadi–Cardelli–Curien–Lévy's *explicit substitutions*, 1991):

* **composition**: substituting `τ` and then `σ` is the same as substituting the
  composite `n ↦ (τ n)[σ]` — and this law survives passing under binders, because
  lifting commutes with composition;
* consequences such as `φ↑[t/0] = φ` (shifting then instantiating does nothing) and
  `φ[t/0][σ] = φ[⇑σ][t[σ]/0]`;
* **freshness**: `Fresh x φ` says that the variable `x` does not occur free in `φ`;
  substitutions that agree away from `x` then act identically on `φ`. Every formula
  has only finitely many free variables, so all sufficiently large `x` are fresh;
* the **size** of a formula (number of connectives and quantifiers) is invariant
  under substitution, which lets us do induction "on the complexity of formulas"
  across instantiations `∀x φ ⇝ φ(t)`.
-/

namespace Foundations.Logic.FO

variable {L : Signature}

namespace Term

/-- **Composition of substitutions (terms).** `t[τ][σ] = t[n ↦ (τ n)[σ]]`. -/
theorem subst_subst (σ τ : Nat → Term L) :
    ∀ t : Term L, (t.subst τ).subst σ = t.subst (fun n => (τ n).subst σ)
  | var _ => rfl
  | func f ts => by simp only [subst]; congr; funext i; exact subst_subst σ τ (ts i)

/-- Shifting a term and then instantiating index `0` gives the term back. -/
theorem rename_succ_single (t u : Term L) : (t.rename Nat.succ).subst (Subst.single u) = t := by
  rw [rename_eq_subst, subst_subst]; exact subst_var t

/-- Shifting commutes with lifted substitution. -/
theorem rename_succ_subst_lift (t : Term L) (σ : Nat → Term L) :
    (t.rename Nat.succ).subst (Subst.lift σ) = (t.subst σ).rename Nat.succ := by
  rw [rename_eq_subst, subst_subst, rename_eq_subst, subst_subst]
  congr; funext n; exact rename_eq_subst _ (σ n)

end Term

/-- Lifting commutes with composition of substitutions. -/
theorem Subst.lift_comp (τ σ : Nat → Term L) :
    (fun n => (Subst.lift τ n).subst (Subst.lift σ)) = Subst.lift (fun n => (τ n).subst σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact Term.rename_succ_subst_lift (τ n) σ

namespace Formula

/-- **Composition of substitutions (formulas).** `φ[τ][σ] = φ[n ↦ (τ n)[σ]]`, also
under binders. -/
theorem subst_subst : ∀ (φ : Formula L) (σ τ : Nat → Term L),
    (φ.subst τ).subst σ = φ.subst (fun n => (τ n).subst σ)
  | bot, _, _ => rfl
  | eq t s, σ, τ => by simp [subst, Term.subst_subst]
  | rel R ts, σ, τ => by simp [subst, Term.subst_subst]
  | imp φ ψ, σ, τ => by simp [subst, subst_subst φ, subst_subst ψ]
  | conj φ ψ, σ, τ => by simp [subst, subst_subst φ, subst_subst ψ]
  | disj φ ψ, σ, τ => by simp [subst, subst_subst φ, subst_subst ψ]
  | all φ, σ, τ => by simp only [subst, subst_subst φ, Subst.lift_comp]
  | ex φ, σ, τ => by simp only [subst, subst_subst φ, Subst.lift_comp]

/-- Two substitutions that agree everywhere act identically. -/
theorem subst_ext {σ τ : Nat → Term L} (φ : Formula L) (h : ∀ n, σ n = τ n) :
    φ.subst σ = φ.subst τ := by
  rw [show σ = τ from funext h]

/-- Shifting commutes with lifted substitution: `φ↑[⇑σ] = φ[σ]↑`. -/
theorem shift_subst_lift (φ : Formula L) (σ : Nat → Term L) :
    φ.shift.subst (Subst.lift σ) = (φ.subst σ).shift := by
  simp only [shift, subst_subst]
  apply subst_ext; intro n; simp [Subst.lift, Term.subst, Term.rename_eq_subst]

/-- Instantiation commutes with substitution: `φ[t/0][σ] = φ[⇑σ][t[σ]/0]`. -/
theorem inst_subst (φ : Formula L) (t : Term L) (σ : Nat → Term L) :
    (φ.inst t).subst σ = (φ.subst (Subst.lift σ)).inst (t.subst σ) := by
  simp only [inst, subst_subst]
  apply subst_ext; intro n
  cases n with
  | zero => rfl
  | succ n => simp only [Subst.single, Subst.lift, Term.subst, Term.rename_succ_single]

/-- Shifting then instantiating gives the formula back: `φ↑[t/0] = φ`. -/
theorem shift_inst (φ : Formula L) (t : Term L) : φ.shift.inst t = φ := by
  simp only [shift, inst, subst_subst]
  conv => rhs; rw [← subst_var φ]
  rfl

/-- Lifting the shift and instantiating with the new variable is the identity. -/
theorem lift_shift_inst_zero (φ : Formula L) :
    (φ.subst (Subst.lift fun n => .var (n + 1))).inst (.var 0) = φ := by
  simp only [inst, subst_subst]
  conv => rhs; rw [← subst_var φ]
  apply subst_ext; intro n; cases n <;> rfl

/-- Substitution distributes over negation. -/
@[simp] theorem neg_subst (φ : Formula L) (σ : Nat → Term L) :
    φ.neg.subst σ = (φ.subst σ).neg := rfl

/-- The *size* (logical complexity) of a formula: the number of connectives and
quantifiers in it. -/
def size : Formula L → Nat
  | bot => 0
  | eq _ _ => 0
  | rel _ _ => 0
  | imp φ ψ => size φ + size ψ + 1
  | conj φ ψ => size φ + size ψ + 1
  | disj φ ψ => size φ + size ψ + 1
  | all φ => size φ + 1
  | ex φ => size φ + 1

/-- Substitution does not change the size of a formula. -/
theorem size_subst : ∀ (φ : Formula L) (σ : Nat → Term L), (φ.subst σ).size = φ.size
  | bot, _ => rfl
  | eq _ _, _ => rfl
  | rel _ _, _ => rfl
  | imp φ ψ, σ => by simp [subst, size, size_subst φ, size_subst ψ]
  | conj φ ψ, σ => by simp [subst, size, size_subst φ, size_subst ψ]
  | disj φ ψ, σ => by simp [subst, size, size_subst φ, size_subst ψ]
  | all φ, σ => by simp [subst, size, size_subst φ]
  | ex φ, σ => by simp [subst, size, size_subst φ]

/-- Instantiation does not change the size of a formula. -/
@[simp] theorem size_inst (φ : Formula L) (t : Term L) : (φ.inst t).size = φ.size :=
  size_subst φ _

end Formula

/-! ## Freshness -/

/-- `Term.Fresh x t`: the variable `x` does not occur in the term `t`. -/
def Term.Fresh (x : Nat) : Term L → Prop
  | .var n => n ≠ x
  | .func _ ts => ∀ i, Term.Fresh x (ts i)

/-- `Formula.Fresh x φ`: the variable `x` does not occur free in `φ`. Under a
quantifier the free variable `x` is called `x + 1`. -/
def Formula.Fresh : Nat → Formula L → Prop
  | _, .bot => True
  | x, .eq t s => t.Fresh x ∧ s.Fresh x
  | x, .rel _ ts => ∀ i, (ts i).Fresh x
  | x, .imp φ ψ => Formula.Fresh x φ ∧ Formula.Fresh x ψ
  | x, .conj φ ψ => Formula.Fresh x φ ∧ Formula.Fresh x ψ
  | x, .disj φ ψ => Formula.Fresh x φ ∧ Formula.Fresh x ψ
  | x, .all φ => Formula.Fresh (x + 1) φ
  | x, .ex φ => Formula.Fresh (x + 1) φ

namespace Term

/-- Substitutions agreeing away from a fresh variable act identically on a term. -/
theorem subst_congr_fresh {x : Nat} {σ τ : Nat → Term L} (h : ∀ n, n ≠ x → σ n = τ n) :
    ∀ t : Term L, t.Fresh x → t.subst σ = t.subst τ
  | var n, hf => h n hf
  | func f ts, hf => by
      simp only [subst]; congr; funext i; exact subst_congr_fresh h (ts i) (hf i)

/-- Shifting moves freshness from `x` to `x + 1`. -/
theorem fresh_rename_succ {x : Nat} : ∀ t : Term L, t.Fresh x → (t.rename Nat.succ).Fresh (x + 1)
  | var n, hf => by simp only [rename, Fresh] at hf ⊢; omega
  | func _ ts, hf => fun i => fresh_rename_succ (ts i) (hf i)

/-- If every substituted term avoids `x`, so does the result of substitution. -/
theorem fresh_subst {x : Nat} {σ : Nat → Term L} (h : ∀ n, (σ n).Fresh x) :
    ∀ t : Term L, (t.subst σ).Fresh x
  | var n => h n
  | func _ ts => fun i => fresh_subst h (ts i)

end Term

/-- A monotone property holding eventually at each of finitely many indices holds
eventually at all of them simultaneously. -/
theorem fin_eventually {n : Nat} (P : Fin n → Nat → Prop)
    (h : ∀ i, ∃ k, ∀ x, k ≤ x → P i x) : ∃ k, ∀ x, k ≤ x → ∀ i, P i x := by
  induction n with
  | zero => exact ⟨0, fun _ _ i => i.elim0⟩
  | succ n ih =>
      obtain ⟨k₁, h₁⟩ := ih (fun i => P i.succ) (fun i => h i.succ)
      obtain ⟨k₀, h₀⟩ := h 0
      refine ⟨max k₀ k₁, fun x hx i => ?_⟩
      cases i using Fin.cases with
      | zero => exact h₀ x (by omega)
      | succ i => exact h₁ x (by omega) i

/-- Every term has only finitely many variables: all large enough `x` are fresh. -/
theorem Term.eventually_fresh : ∀ t : Term L, ∃ k, ∀ x, k ≤ x → t.Fresh x
  | .var n => ⟨n + 1, fun x hx => by simp only [Fresh]; omega⟩
  | .func _ ts => fin_eventually (fun i x => (ts i).Fresh x) (fun i => eventually_fresh (ts i))

namespace Formula

/-- Substitutions agreeing away from a fresh variable act identically on a formula. -/
theorem subst_congr_fresh : ∀ (φ : Formula L) {x : Nat} {σ τ : Nat → Term L},
    (∀ n, n ≠ x → σ n = τ n) → φ.Fresh x → φ.subst σ = φ.subst τ
  | bot, _, _, _, _, _ => rfl
  | eq t s, _, _, _, h, hf => by
      simp only [subst, Term.subst_congr_fresh h t hf.1, Term.subst_congr_fresh h s hf.2]
  | rel R ts, _, _, _, h, hf => by
      simp only [subst]; congr; funext i; exact Term.subst_congr_fresh h (ts i) (hf i)
  | imp φ ψ, _, _, _, h, hf => by
      simp only [subst, subst_congr_fresh φ h hf.1, subst_congr_fresh ψ h hf.2]
  | conj φ ψ, _, _, _, h, hf => by
      simp only [subst, subst_congr_fresh φ h hf.1, subst_congr_fresh ψ h hf.2]
  | disj φ ψ, _, _, _, h, hf => by
      simp only [subst, subst_congr_fresh φ h hf.1, subst_congr_fresh ψ h hf.2]
  | all φ, x, σ, τ, h, hf => by
      simp only [subst]; congr 1
      refine subst_congr_fresh φ (x := x + 1) (fun n hn => ?_) hf
      cases n with
      | zero => rfl
      | succ n => simp only [Subst.lift]; rw [h n (by omega)]
  | ex φ, x, σ, τ, h, hf => by
      simp only [subst]; congr 1
      refine subst_congr_fresh φ (x := x + 1) (fun n hn => ?_) hf
      cases n with
      | zero => rfl
      | succ n => simp only [Subst.lift]; rw [h n (by omega)]

/-- If every substituted term avoids `x`, so does the result of substitution. -/
theorem fresh_subst : ∀ (φ : Formula L) {x : Nat} {σ : Nat → Term L},
    (∀ n, (σ n).Fresh x) → (φ.subst σ).Fresh x
  | bot, _, _, _ => trivial
  | eq t s, _, _, h => ⟨Term.fresh_subst h t, Term.fresh_subst h s⟩
  | rel _ ts, _, _, h => fun i => Term.fresh_subst h (ts i)
  | imp φ ψ, _, _, h => ⟨fresh_subst φ h, fresh_subst ψ h⟩
  | conj φ ψ, _, _, h => ⟨fresh_subst φ h, fresh_subst ψ h⟩
  | disj φ ψ, _, _, h => ⟨fresh_subst φ h, fresh_subst ψ h⟩
  | all φ, x, σ, h | ex φ, x, σ, h => by
      refine fresh_subst φ (x := x + 1) (fun n => ?_)
      cases n with
      | zero => simp only [Subst.lift, Term.Fresh]; omega
      | succ n => exact Term.fresh_rename_succ _ (h n)

/-- Every formula has only finitely many free variables: all large `x` are fresh. -/
theorem eventually_fresh : ∀ φ : Formula L, ∃ k, ∀ x, k ≤ x → φ.Fresh x
  | bot => ⟨0, fun _ _ => trivial⟩
  | eq t s => by
      obtain ⟨k₁, h₁⟩ := t.eventually_fresh
      obtain ⟨k₂, h₂⟩ := s.eventually_fresh
      exact ⟨max k₁ k₂, fun x hx => ⟨h₁ x (by omega), h₂ x (by omega)⟩⟩
  | rel _ ts => fin_eventually (fun i x => (ts i).Fresh x) (fun i => (ts i).eventually_fresh)
  | imp φ ψ | conj φ ψ | disj φ ψ => by
      obtain ⟨k₁, h₁⟩ := eventually_fresh φ
      obtain ⟨k₂, h₂⟩ := eventually_fresh ψ
      exact ⟨max k₁ k₂, fun x hx => ⟨h₁ x (by omega), h₂ x (by omega)⟩⟩
  | all φ | ex φ => by
      obtain ⟨k, h⟩ := eventually_fresh φ
      exact ⟨k, fun x hx => h (x + 1) (by omega)⟩

/-- A finite list of formulas has a common bound beyond which all variables are fresh. -/
theorem eventually_fresh_list : ∀ l : List (Formula L), ∃ k, ∀ x, k ≤ x → ∀ φ ∈ l, φ.Fresh x
  | [] => ⟨0, fun _ _ _ h => by simp at h⟩
  | φ :: l => by
      obtain ⟨k₁, h₁⟩ := eventually_fresh φ
      obtain ⟨k₂, h₂⟩ := eventually_fresh_list l
      refine ⟨max k₁ k₂, fun x hx ψ hψ => ?_⟩
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact h₁ x (by omega)
      · exact h₂ x (by omega) ψ hψ

end Formula

end Foundations.Logic.FO
