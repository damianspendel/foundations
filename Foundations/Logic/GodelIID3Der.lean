import Foundations.Logic.GodelIID3Inst

/-!
# A small calculus of internal derivations

We write `Der χ v` for "the judgement `PA ⊢ χ(v̄₀, v̄₁, …)` is `provDP`-derivable" inside a
model `N` of PA, for a standard formula `χ` and an assignment `v` of elements of `N`.
The rules available are

* `der_inst`: every instance of a theorem of PA;
* `der_mp`: modus ponens;
* `der_congr`: two judgements with the same internal code are the same judgement — used
  with the substitution lemma `codeM_subst0` to move between formulas with different
  variable layouts.

To run *internal* inductions over such statements we need them to be definable in `N`:
`der_dfn` shows that `Der χ v` is definable as a property of `v`, through the definability
of the code function `codeM χ 0` (`GDef`, "graph-definable"), built from the definable
graphs of internal pairing and internal numerals.

*Place in the argument.* Gödel (1931) only sketched the second incompleteness theorem;
Hilbert and Bernays (1939) carried out the arithmetisation it needs; Löb (1955) reduced it to
three derivability conditions, of which (D3) — formalised Σ₁-completeness — is the hard one.
Feferman (1960) showed that the theorem depends on how provability is expressed, which is why
it matters that `provDP` is a derivation predicate rather than one engineered to satisfy (D3).
This file is one step of the proof of (D3) for `provDP` assembled in `GodelIID3Main`.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability GodelII

namespace PAModel

variable {N : PAModel}

/-- **Internal derivability** of the instance `χ(v̄₀, v̄₁, …)`. -/
def Der (χ : Formula Arith) (v : Nat → N.Dom) : Prop := DerP (JN (codeM χ 0 v))

/-- Instances of theorems of PA are derivable. -/
theorem der_inst {χ : Formula Arith} (h : PA ⊢₁ χ) (v : Nat → N.Dom) : Der χ v := derP_inst h v

/-- **Modus ponens.** -/
theorem der_mp {A B : Formula Arith} {v : Nat → N.Dom} (h₁ : Der (imp A B) v) (h₂ : Der A v) :
    Der B v :=
  derP_mp rfl h₁ h₂

/-- Judgements with equal codes. -/
theorem der_congr {χ χ' : Formula Arith} {v v' : Nat → N.Dom}
    (h : codeM χ 0 v = codeM χ' 0 v') (hd : Der χ v) : Der χ' v' := by
  unfold Der at *; rwa [← h]

/-- **Moving between variable layouts.** -/
theorem der_subst_iff {χ : Formula Arith} {σ : Nat → Term Arith} {v v' : Nat → N.Dom}
    (hσ : ∀ m, tcM (σ m) 0 v = NumN (v' m)) : Der (χ.subst σ) v ↔ Der χ v' := by
  unfold Der; rw [codeM_subst0 hσ]

/-- Validity in all models of PA gives provability. -/
theorem pa_of_valid {φ : Formula Arith} (h : ∀ (M : PAModel) (e : Nat → M.Dom), Sat M.M e φ) :
    PA ⊢₁ φ :=
  PA_proves_of_models h

/-! ## Definability -/

/-- Definability respects equivalence. -/
theorem Dfn.congr' {P Q : (Nat → N.Dom) → Prop} (h : N.Dfn P) (hPQ : ∀ e, P e ↔ Q e) : N.Dfn Q := by
  obtain ⟨φ, hφ⟩ := h; exact ⟨φ, fun e => (hφ e).trans (hPQ e)⟩

/-- Definability is preserved by reindexing the variables. -/
theorem Dfn.reindex {P : (Nat → N.Dom) → Prop} (h : N.Dfn P) (ρ : Nat → Nat) :
    N.Dfn fun e => P (fun n => e (ρ n)) :=
  Dfn.subst h fun n => DfnT.var (ρ n)

/-- **A graph-definable function** of the assignment. -/
def GDef (F : (Nat → N.Dom) → N.Dom) : Prop := N.Dfn fun e => e 0 = F (fun n => e (n + 1))

/-- Substituting a graph-definable function into a definable property. -/
theorem GDef.app {F : (Nat → N.Dom) → N.Dom} (hF : GDef F) {P : N.Dom → (Nat → N.Dom) → Prop}
    (hP : N.Dfn fun e => P (e 0) (fun n => e (n + 1))) : N.Dfn fun e => P (F e) e := by
  have := Dfn.ex (Q := fun y e => y = F e ∧ P y e) (Dfn.and hF hP)
  exact this.congr' fun e => ⟨fun ⟨y, hy, h⟩ => hy ▸ h, fun h => ⟨_, rfl, h⟩⟩

/-- Graph-definability is preserved by shifting the assignment. -/
theorem GDef.shift {F : (Nat → N.Dom) → N.Dom} (hF : GDef F) (k : Nat) :
    GDef fun e => F (fun n => e (n + k)) :=
  (hF.reindex fun n => match n with | 0 => 0 | n + 1 => n + 1 + k).congr' fun e => by
    have : (fun n => e (n + 1 + k)) = fun n => e (n + k + 1) :=
      funext fun n => by rw [Nat.add_right_comm]
    simp only [this]

/-- Numerals are graph-definable constants. -/
theorem GDef.const (k : Nat) : GDef (N := N) fun _ => ((k : Nat) : N.Dom) :=
  Dfn.eq (DfnT.var 0) (DfnT.ofNat k)

/-- Variables are graph-definable. -/
theorem GDef.var (n : Nat) : GDef (N := N) fun e => e n := Dfn.eq (DfnT.var 0) (DfnT.var (n + 1))

/-- The numeral function preserves graph-definability. -/
theorem GDef.numN {F : (Nat → N.Dom) → N.Dom} (hF : GDef F) : GDef fun e => NumN (F e) := by
  have h₁ : GDef fun e => F (fun n => e (n + 1)) := hF.shift 1
  have h₂ : N.Dfn fun e => NumM (e 0) (e 1) := numDef.toUDef.dfn N
  have := h₁.app (P := fun a e => NumM a (e 0)) h₂
  exact this.congr' fun e => by rw [numM_iff]

/-- Pairing preserves graph-definability. -/
theorem GDef.pairN {F G : (Nat → N.Dom) → N.Dom} (hF : GDef F) (hG : GDef G) :
    GDef fun e => pairN (F e) (G e) := by
  have hPM : N.Dfn fun e => PairM (e 1) (e 0) (e 2) := by unfold PairM; dfn
  have h₁ : N.Dfn fun e => PairM (e 0) (G (fun n => e (n + 2))) (e 1) :=
    (hG.shift 2).app (P := fun b e => PairM (e 0) b (e 1)) hPM
  have h₂ := (hF.shift 1).app (P := fun a e => PairM a (G (fun n => e (n + 1))) (e 0)) h₁
  exact h₂.congr' fun e => by rw [pairM_iff]

/-- Internal function codes are graph-definable. -/
theorem GDef.funcCodeM {n : Nat} (f : ArithFunc n) {F : Fin n → (Nat → N.Dom) → N.Dom}
    (hF : ∀ i, GDef (F i)) : GDef fun e => funcCodeM f fun i => F i e := by
  cases f with
  | zero => exact GDef.const 2
  | succ => exact (GDef.const 2).pairN (hF 0)
  | add => exact (GDef.const 3).pairN ((hF 0).pairN (hF 1))
  | mul => exact (GDef.const 4).pairN ((hF 0).pairN (hF 1))

/-- Internal term codes are graph-definable. -/
theorem GDef.tcM : ∀ (t : Term Arith) (d : Nat), GDef (N := N) fun e => tcM t d e
  | .var m, d => by
    by_cases h : m < d
    · simp only [PAModel.tcM, h, ite_true]; exact GDef.const _
    · simp only [PAModel.tcM, h, ite_false]; exact (GDef.var _).numN
  | .func f ts, d => by
    simp only [PAModel.tcM]; exact GDef.funcCodeM f fun i => GDef.tcM (ts i) d

/-- **Internal formula codes are graph-definable.** -/
theorem GDef.codeM : ∀ (φ : Formula Arith) (d : Nat), GDef (N := N) fun e => codeM φ d e
  | .bot, _ => GDef.const 0
  | .eq t s, d => (GDef.const 1).pairN ((GDef.tcM t d).pairN (GDef.tcM s d))
  | .rel R _, _ => (R : Empty).elim
  | .imp φ ψ, d => (GDef.const 2).pairN ((GDef.codeM φ d).pairN (GDef.codeM ψ d))
  | .conj φ ψ, d => (GDef.const 3).pairN ((GDef.codeM φ d).pairN (GDef.codeM ψ d))
  | .disj φ ψ, d => (GDef.const 4).pairN ((GDef.codeM φ d).pairN (GDef.codeM ψ d))
  | .all φ, d => (GDef.const 5).pairN (GDef.codeM φ (d + 1))
  | .ex φ, d => (GDef.const 6).pairN (GDef.codeM φ (d + 1))

/-- **Internal derivability is definable** (as a property of the assignment). -/
theorem der_dfn (χ : Formula Arith) : N.Dfn fun e => Der χ e := by
  have h : N.Dfn fun e => ProvDPM (e 0) := provDPDef.toUDef.dfn N
  exact ((GDef.codeM χ 0).app (P := fun y _ => ProvDPM y) h).congr' fun e => provDPM_iff _

/-- Internal derivability at a definable assignment is definable. -/
theorem der_dfn_at (χ : Formula Arith) {τ : Nat → (Nat → N.Dom) → N.Dom} (hτ : ∀ n, N.DfnT (τ n)) :
    N.Dfn fun e => Der χ (fun n => τ n e) :=
  Dfn.subst (der_dfn χ) hτ

end PAModel

end Foundations.Logic.FO
