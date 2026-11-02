import Foundations.Logic.GodelIIStandard

/-!
# Towards (D3): Σ-formulas, internal pairing and internal numerals

Löb's third derivability condition (D3), `□φ → □□φ`, is the formalised version of the
Σ₁-completeness theorem: what is true and Σ₁ is provable, *and PA knows it*. Hilbert and
Bernays (1939) proved the corresponding conditions for their provability predicate by a
long arithmetisation; Löb (1955) isolated them; Feferman (1960) showed that the choice of
the arithmetisation matters (`GodelIIFeferman`). This file and the following
`GodelIID3*` files carry out the arithmetisation needed for (D3), reasoning inside an
arbitrary model `N` of PA (and using completeness to return to provability).

This first file provides three basic tools.

* **Σ-formulas** (`SigP`): the closure of the bounded formulas `D0` under `∧`, `∨`, `∃` and
  bounded universal quantifiers. These are the formulas for which formalised
  Σ-completeness will be proved. `SUDef` is a uniform definition (`UDef`) whose defining
  formula is a Σ-formula, and the tactic `sudfn` builds such definitions syntactically.
* **Internal pairing.** Cantor's pairing function exists as a *function* in every model
  of PA (`pairN`), because `s(s+1)` is always even there (an internal induction).
* **Internal numerals.** In every model there is a function `NumN` with `NumN 0 = ⌜0⌝`
  and `NumN (a+1) = ⟨2, NumN a⟩ = ⌜S(·)⌝`, defined by a β-coded computation of
  possibly non-standard length; on standard `n` it is the Gödel number `ncode n` of the
  numeral `n̄`. `NumN a` is "the code of the numeral of `a`", also for non-standard `a`.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability

namespace GodelII

/-- **Σ-formulas**: bounded formulas closed under `∧`, `∨`, `∃` and bounded `∀`. -/
inductive SigP : Formula Arith → Prop where
  /-- Bounded formulas. -/
  | d0 {φ} : D0 φ → SigP φ
  /-- Conjunction. -/
  | conj {φ ψ} : SigP φ → SigP ψ → SigP (conj φ ψ)
  /-- Disjunction. -/
  | disj {φ ψ} : SigP φ → SigP ψ → SigP (disj φ ψ)
  /-- Unbounded existential quantification. -/
  | ex {φ} : SigP φ → SigP (ex φ)
  /-- Bounded universal quantification `∀x ≤ T`. -/
  | ball (T : Term Arith) {φ} : SigP φ → SigP (all (imp (boundF T) φ))
  /-- Bounded universal quantification `∀x < T`. -/
  | ballS (T : Term Arith) {φ} : SigP φ → SigP (all (imp (boundSF T) φ))

/-- Σ-formulas are closed under substitution. -/
theorem SigP.subst {φ : Formula Arith} (h : SigP φ) : ∀ σ : Nat → Term Arith, SigP (φ.subst σ) := by
  induction h with
  | d0 h => exact fun σ => SigP.d0 (h.subst σ)
  | conj _ _ ih₁ ih₂ => exact fun σ => SigP.conj (ih₁ σ) (ih₂ σ)
  | disj _ _ ih₁ ih₂ => exact fun σ => SigP.disj (ih₁ σ) (ih₂ σ)
  | ex _ ih => exact fun σ => SigP.ex (ih _)
  | ball T _ ih =>
      intro σ; simp only [Formula.subst]; rw [boundF_subst]; exact SigP.ball _ (ih _)
  | ballS T _ ih =>
      intro σ; simp only [Formula.subst]; rw [boundSF_subst]; exact SigP.ballS _ (ih _)

/-- The Σ₁ graph formula of a program is a Σ-formula. -/
theorem SigP.evalSigma (c : Code) : SigP (evalSigma c) := SigP.ex (SigP.d0 (evalSigma_D0 c))

end GodelII

open GodelII

namespace PAModel

/-- **A Σ-definition**: a uniform definition whose formula is a Σ-formula. -/
structure SUDef (P : ∀ N : PAModel, (Nat → N.Dom) → Prop) extends UDef P where
  /-- The defining formula is a Σ-formula. -/
  sig : SigP φ

variable {f g : ∀ N : PAModel, (Nat → N.Dom) → N.Dom}

/-- Equations are Σ-definable. -/
def SUDef.eq (hf : UDefT f) (hg : UDefT g) : SUDef fun N e => f N e = g N e :=
  ⟨UDef.eq hf hg, SigP.d0 (D0.eq _ _)⟩

/-- Conjunction of Σ-definitions. -/
def SUDef.and {P Q : ∀ N : PAModel, (Nat → N.Dom) → Prop} (hP : SUDef P) (hQ : SUDef Q) :
    SUDef fun N e => P N e ∧ Q N e :=
  ⟨UDef.and hP.toUDef hQ.toUDef, SigP.conj hP.sig hQ.sig⟩

/-- Disjunction of Σ-definitions. -/
def SUDef.or {P Q : ∀ N : PAModel, (Nat → N.Dom) → Prop} (hP : SUDef P) (hQ : SUDef Q) :
    SUDef fun N e => P N e ∨ Q N e :=
  ⟨UDef.or hP.toUDef hQ.toUDef, SigP.disj hP.sig hQ.sig⟩

/-- Existential quantification of a Σ-definition. -/
def SUDef.ex {Q : ∀ N : PAModel, N.Dom → (Nat → N.Dom) → Prop}
    (h : SUDef fun N e => Q N (e 0) (fun n => e (n + 1))) : SUDef fun N e => ∃ x, Q N x e :=
  ⟨UDef.ex h.toUDef, SigP.ex h.sig⟩

/-- `≤` is Σ-definable. -/
def SUDef.le (hf : UDefT f) (hg : UDefT g) : SUDef fun N e => f N e ≤ g N e :=
  ⟨UDef.le hf hg, SigP.ex (SigP.d0 (D0.eq _ _))⟩

/-- `<` is Σ-definable. -/
def SUDef.lt (hf : UDefT f) (hg : UDefT g) : SUDef fun N e => f N e < g N e :=
  ⟨UDef.lt hf hg, SigP.ex (SigP.d0 (D0.eq _ _))⟩

/-- The β-relation is Σ-definable. -/
def SUDef.betaM {fc fd fi fy : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hc : UDefT fc)
    (hd : UDefT fd) (hi : UDefT fi) (hy : UDefT fy) :
    SUDef fun N e => BetaM (fc N e) (fd N e) (fi N e) (fy N e) :=
  ⟨UDef.betaM hc hd hi hy, SigP.subst (SigP.ex (SigP.conj (SigP.d0 (D0.eq _ _))
    (SigP.ex (SigP.d0 (D0.eq _ _))))) _⟩

/-- The step test is Σ-definable. -/
noncomputable def SUDef.dstep (hf : UDefT f) : SUDef fun N e => StepM (f N e) :=
  ⟨UDef.dstep hf, SigP.subst (SigP.evalSigma _) _⟩

/-- **Bounded universal quantification `∀x ≤ G`** of a Σ-definition. -/
def SUDef.ballLe {Q : ∀ N : PAModel, N.Dom → (Nat → N.Dom) → Prop} (hG : UDefT g)
    (h : SUDef fun N e => Q N (e 0) (fun n => e (n + 1))) :
    SUDef fun N e => ∀ x, x ≤ g N e → Q N x e :=
  ⟨⟨all (imp (boundF hG.t) h.φ), fun N e => by
      simp only [Sat]
      refine forall_congr' fun x => imp_congr ?_ (h.spec N (Env.cons x e))
      rw [sat_boundF, hG.spec]
      exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' x z⟩,
        fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' z x⟩⟩⟩,
    SigP.ball _ h.sig⟩

/-- **Bounded universal quantification `∀x < G`** of a Σ-definition. -/
def SUDef.ballLt {Q : ∀ N : PAModel, N.Dom → (Nat → N.Dom) → Prop} (hG : UDefT g)
    (h : SUDef fun N e => Q N (e 0) (fun n => e (n + 1))) :
    SUDef fun N e => ∀ x, x < g N e → Q N x e :=
  ⟨⟨all (imp (boundSF hG.t) h.φ), fun N e => by
      simp only [Sat]
      refine forall_congr' fun x => imp_congr ?_ (h.spec N (Env.cons x e))
      rw [sat_boundSF, hG.spec, ms_eq]
      exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' (x + 1) z⟩,
        fun ⟨z, hz⟩ => ⟨z, by rw [← hz]; exact add_comm' z (x + 1)⟩⟩⟩,
    SigP.ballS _ h.sig⟩

/-- One step of the `sudfn` tactic. -/
syntax "sudfn_step" : tactic
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.UDefT.add)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.UDefT.mul)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.UDefT.ofNat)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.UDefT.var)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.and)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.or)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.ex)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.eq)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.le)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.lt)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.betaM)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.dstep)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.ballLe)
macro_rules | `(tactic| sudfn_step) => `(tactic| apply PAModel.SUDef.ballLt)

/-- `sudfn` builds Σ-definitions `SUDef P` by decomposing `P` syntactically. -/
macro "sudfn" : tactic => `(tactic| repeat' sudfn_step)

/-- A uniform definition gives definability in each model. -/
theorem UDef.dfn {P : ∀ N : PAModel, (Nat → N.Dom) → Prop} (h : UDef P) (N : PAModel) :
    N.Dfn (P N) :=
  ⟨h.φ, h.spec N⟩

macro_rules | `(tactic| dfn_step) => `(tactic| apply PAModel.Dfn.betaM)

variable {N : PAModel}

/-! ## Internal pairing -/

/-- In a model of PA, `s(s+1)` is even. -/
theorem exists_half_pronic (s : N.Dom) : ∃ h, h + h = s * (s + 1) := by
  have hd : N.Dfn fun e => (fun (s : N.Dom) (_ : Nat → N.Dom) => ∃ h, h + h = s * (s + 1))
      (e 0) (fun n => e (n + 1)) := by
    show N.Dfn fun e => ∃ h, h + h = e 0 * (e 0 + 1)
    dfn
  exact induction (P := fun (s : N.Dom) (_ : Nat → N.Dom) => ∃ h, h + h = s * (s + 1)) hd
    (fun _ => 0) ⟨0, by grind⟩ (fun x ⟨h, hh⟩ => ⟨h + x + 1, by grind⟩) s

/-- Cantor pairs exist in every model of PA. -/
theorem pair_exists (a b : N.Dom) : ∃ p, PairM a b p := by
  obtain ⟨h, hh⟩ := exists_half_pronic (a + b)
  exact ⟨h + a, by unfold PairM; grind⟩

/-- **Internal Cantor pairing**, as a function on the model. -/
noncomputable def pairN (a b : N.Dom) : N.Dom := (pair_exists a b).choose

/-- `pairN` computes Cantor pairing. -/
theorem pairN_spec (a b : N.Dom) : PairM a b (pairN a b) := (pair_exists a b).choose_spec

/-- The pairing relation is the graph of `pairN`. -/
theorem pairM_iff {a b p : N.Dom} : PairM a b p ↔ p = pairN a b :=
  ⟨fun h => pairM_unique h (pairN_spec a b), fun h => h ▸ pairN_spec a b⟩

/-- `pairN` agrees with `pair` on numerals. -/
theorem pairN_cast (a b : Nat) : pairN (a : N.Dom) (b : N.Dom) = ((pair a b : Nat) : N.Dom) :=
  (pairM_unique (pairM_natCast a b) (pairN_spec _ _)).symm

/-! ## Finite sequences of arbitrary elements -/

/-- **Appending an element** to a β-coded sequence `s₀, …, sₙ`. -/
theorem seq_snoc (c d n v : N.Dom) : ∃ c' d', (∀ i y, i ≤ n → BetaM c d i y → BetaM c' d' i y) ∧
    BetaM c' d' (n + 1) v := by
  obtain ⟨c', d', -, hA, hB, -⟩ := concat_exists c d n v v 0 v 0
  refine ⟨c', d', hA, ?_⟩
  have := hB 0 v (le_refl' _) (betaM_single v)
  rwa [add_zero'] at this

/-- **Every finite family of elements has a β-code.** -/
theorem seq_of_fun (f : Nat → N.Dom) : ∀ n : Nat, ∃ c d, ∀ i : Nat, i ≤ n → BetaM c d (i : N.Dom) (f i)
  | 0 => ⟨f 0, f 0, fun i hi => by
      rw [show i = 0 by omega]; exact betaM_single _⟩
  | n + 1 => by
    obtain ⟨c, d, h⟩ := seq_of_fun f n
    obtain ⟨c', d', hA, hv⟩ := seq_snoc c d (n : N.Dom) (f (n + 1))
    refine ⟨c', d', fun i hi => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with h' | h'
    · exact hA _ _ (by
        obtain ⟨z, hz⟩ : ∃ z, i + z = n := ⟨n - i, by omega⟩
        exact ⟨(z : N.Dom), by rw [← natCast_add, hz]⟩) (h i (by omega))
    · rw [show i = n + 1 by omega, natCast_add, natCast_one]; exact hv

/-! ## Internal numerals -/

/-- **The numeral relation.** `y` is the code of the numeral of `a`: there is a β-coded
sequence `s₀ = ⌜0⌝ = 2`, `sᵢ₊₁ = ⟨2, sᵢ⟩`, with `s_a = y`. -/
def NumM (a y : N.Dom) : Prop :=
  ∃ c, ∃ d, BetaM c d 0 2 ∧
    (∀ i, i < a → ∃ u, BetaM c d i u ∧ ∃ w, BetaM c d (i + 1) w ∧ PairM 2 u w) ∧ BetaM c d a y

/-- The Σ-definition of `NumM`. -/
noncomputable def numDef : SUDef fun N e => NumM (N := N) (e 0) (e 1) := by
  unfold NumM PairM; sudfn

/-- Extending a numeral computation by one step. -/
theorem numM_succ {a y : N.Dom} (h : NumM a y) : NumM (a + 1) (pairN 2 y) := by
  obtain ⟨c, d, h0, hstep, ha⟩ := h
  obtain ⟨c', d', hA, hv⟩ := seq_snoc c d a (pairN 2 y)
  refine ⟨c', d', hA 0 2 (zero_le' a) h0, fun i hi => ?_, hv⟩
  rcases eq_or_lt_of_le (lt_succ_iff'.1 hi) with rfl | hi'
  · exact ⟨y, hA _ _ (le_refl' _) ha, _, hv, pairN_spec 2 y⟩
  · obtain ⟨u, hu, w, hw, hp⟩ := hstep i hi'
    exact ⟨u, hA _ _ (le_of_lt' hi') hu, w, hA _ _ hi' hw, hp⟩

/-- Numeral computations exist. -/
theorem numM_exists (a : N.Dom) : ∃ y, NumM a y := by
  have hd : N.Dfn fun e => (fun (a : N.Dom) (_ : Nat → N.Dom) => ∃ y, NumM a y)
      (e 0) (fun n => e (n + 1)) := by
    have := (SUDef.ex (Q := fun N y e => NumM (N := N) (e 0) y) (by
      unfold NumM PairM; sudfn)).toUDef.dfn N
    exact this
  refine induction (P := fun (a : N.Dom) (_ : Nat → N.Dom) => ∃ y, NumM a y) hd
    (fun _ => 0) ⟨2, 2, 2, betaM_single 2, fun i hi => absurd hi (not_lt_zero' i),
    betaM_single 2⟩ (fun x ⟨y, hy⟩ => ⟨_, numM_succ hy⟩) a

/-- Numeral computations are unique. -/
theorem numM_unique {a y y' : N.Dom} (h : NumM a y) (h' : NumM a y') : y = y' := by
  obtain ⟨c, d, h0, hs, ha⟩ := h
  obtain ⟨c', d', h0', hs', ha'⟩ := h'
  have hd : N.Dfn fun e => (fun (i : N.Dom) (p : Nat → N.Dom) =>
      i ≤ p 0 → ∀ y y', BetaM (p 1) (p 2) i y → BetaM (p 3) (p 4) i y' → y = y')
      (e 0) (fun n => e (n + 1)) := by
    show N.Dfn fun e => e 0 ≤ e 1 → ∀ y y', BetaM (e 2) (e 3) (e 0) y →
      BetaM (e 4) (e 5) (e 0) y' → y = y'
    simp only [le_def]; dfn
  have key := induction (P := fun (i : N.Dom) (p : Nat → N.Dom) =>
      i ≤ p 0 → ∀ y y', BetaM (p 1) (p 2) i y → BetaM (p 3) (p 4) i y' → y = y') hd (Env.cons a (Env.cons c (Env.cons d (Env.cons c' (Env.cons d'
    fun _ => 0))))) (fun _ y y' hy hy' => by
      rw [betaM_unique hy h0, betaM_unique hy' h0'])
    (fun i ih hi y y' hy hy' => by
      have hlt : i < a := hi
      obtain ⟨u, hu, w, hw, hp⟩ := hs i hlt
      obtain ⟨u', hu', w', hw', hp'⟩ := hs' i hlt
      have := ih (le_of_lt' hlt) u u' hu hu'
      subst this
      rw [betaM_unique hy hw, betaM_unique hy' hw', pairM_unique hp hp'])
  exact key a (le_refl' a) y y' ha ha'

/-- **The internal numeral function**: `NumN a` is the code of the numeral of `a`. -/
noncomputable def NumN (a : N.Dom) : N.Dom := (numM_exists a).choose

/-- `NumN` computes the numeral relation. -/
theorem numN_spec (a : N.Dom) : NumM a (NumN a) := (numM_exists a).choose_spec

/-- The numeral relation is the graph of `NumN`. -/
theorem numM_iff {a y : N.Dom} : NumM a y ↔ y = NumN a :=
  ⟨fun h => numM_unique h (numN_spec a), fun h => h ▸ numN_spec a⟩

/-- The numeral of `0` is `⌜0⌝ = 2`. -/
theorem numN_zero : NumN (0 : N.Dom) = 2 :=
  (numM_unique (numN_spec 0) ⟨2, 2, betaM_single 2, fun i hi => absurd hi (not_lt_zero' i),
    betaM_single 2⟩)

/-- The numeral of `a + 1` is `⟨2, NumN a⟩ = ⌜S(ā)⌝`. -/
theorem numN_succ (a : N.Dom) : NumN (a + 1) = pairN 2 (NumN a) :=
  numM_unique (numN_spec _) (numM_succ (numN_spec a))

/-- `⌜0⌝ = ⟨1, 0⟩ = 2`. -/
theorem pair_one_zero : pair 1 0 = 2 := by decide

/-- **On standard numbers, `NumN` is the Gödel numbering of numerals.** -/
theorem numN_cast : ∀ n : Nat, NumN (n : N.Dom) = ((ncode n : Nat) : N.Dom)
  | 0 => by
    rw [show ((0 : Nat) : N.Dom) = 0 from rfl, numN_zero]
    show (2 : N.Dom) = ((tcode zero : Nat) : N.Dom)
    rw [tcode_zero, pair_one_zero]; rfl
  | n + 1 => by
    rw [natCast_add, natCast_one, numN_succ, numN_cast n]
    show pairN ((2 : Nat) : N.Dom) _ = _
    rw [pairN_cast]; rfl

end PAModel

end Foundations.Logic.FO
