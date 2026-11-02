import Foundations.Logic.Lob
import Foundations.Logic.UniformDefinability

/-!
# A provability predicate for PA built for the derivability conditions

`Lob` defined the provability formula `provPA` as "the PA-proof-search program halts
on `x`", proved condition (D1) for it, and left (D2) and (D3) open. The program
`paSearch` there is an *arbitrary* code with the right halting behaviour on the
standard numbers (it is chosen by the axiom of choice from an existence proof); about
its behaviour on *non-standard* inputs nothing can be said, and so nothing about it
can be verified inside a non-standard model of PA. To prove (D2) and (D3) we therefore
introduce a provability formula whose *shape* we control.

**The formula `provH`.** Read `x` as the Gödel number of a formula. `provH(x)` says:
*there is a finite sequence `y₀, …, yₙ` (coded by Gödel's β-function) with `yₙ = x`,
each entry of which is justified, in one of three ways:*

1. *(axiom)* the (strengthened) PA proof search accepts it — `accF(yₖ)`, a Σ₁ formula;
2. *(modus ponens)* there are earlier entries `yᵢ = ⌜φ → ψ⌝`, `yⱼ = ⌜φ⌝` with
   `yₖ = ⌜ψ⌝` — here `⌜φ → ψ⌝ = ⟨2, ⟨⌜φ⌝, ⌜ψ⌝⟩⟩` is expressed by the polynomial
   equations of Cantor's pairing function;
3. *(necessitation)* there is an earlier entry `yᵢ = ⌜φ⌝` with `yₖ = ⌜accF(⌜φ⌝)⌝` — the
   function `⌜φ⌝ ↦ ⌜accF(⌜φ⌝)⌝` is computable and enters through its Σ₁ graph.

This is a Hilbert-style proof system whose axioms are the theorems of PA and whose
rules are modus ponens and the (admissible) necessitation rule "from `φ` infer
`Prov(⌜φ⌝)`". In the standard model it defines exactly PA-provability
(`sat_provH`): every rule preserves PA-provability, since PA is closed under modus
ponens and satisfies (D1). The point of the design is that the closure properties
which (D2) and (D3) assert are now visible in the *shape* of the definition, so that
they can be verified in an arbitrary model of PA by manipulating coded sequences
(next file). The formula is built by the uniform definability calculus and is a
definite formula of arithmetic (a well-defined mathematical object, though not written
out explicitly: its two program parameters are obtained by `Classical.choose`).

This file proves the standard characterisation and condition (D1) for `provH`.

**Status relative to the textbook predicate.** `provH` is not Gödel's "there is a
derivation of `x`": its axiom clause accepts *all* theorems of PA through the opaque
program `searchPA`, of which only its behaviour on standard inputs (`searchPA_spec`) is
known, and it has a built-in necessitation rule. Since nothing constrains `accF` on
non-standard arguments, a PA-provable comparison between `provH` and an independently
defined (e.g. derivation-based) provability formula is not available from what is known
about `provH`; only `PA ⊢ accF(x) → provH(x)` is proved (`GodelII.accF_imp_provH_uniform`). The files
`GodelIITransfer`, `GodelIIFeferman`, `GodelIIDerivations` and `GodelIIStandard` analyse
the gap: they show why the choice of predicate matters (Feferman 1960), introduce a
derivation-based formula `provD` for PA's natural-deduction calculus with (D1), (D2) and
the standard characterisation, and reduce Gödel II for `provD` to (D3) for `provD`
(formalised Σ₁-completeness), which remains unproved. The files `GodelIID3*` prove (D3) and
Gödel II for the transparent derivation predicate `provDP` (`godel_second_provDP`).
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability

/-! ## The strengthened proof search -/

/-- **Strengthened enumerability of PA's theorems.** A code that halts on `x` exactly
when `x` is the Gödel number of a theorem of PA (and on nothing else). -/
theorem PA_theorems_ce' : ∃ c : Code, ∀ x, Halts c [x] ↔ ∃ φ, x = fcode φ ∧ PA ⊢₁ φ := by
  obtain ⟨c₀, hc₀⟩ := ce_derivable paRule paRule_comp
  obtain ⟨cf, hcf⟩ := (Comp.pair (Comp.const 0) (Comp.pair (Comp.const 0) Comp.id) :
    Comp fun n => pj 0 (ccode []) n)
  refine ⟨.comp c₀ (vec1 cf), fun x => ?_⟩
  rw [halts_comp_iff hcf, hc₀]
  constructor
  · intro h
    obtain ⟨k, Δ, φ, e, -⟩ := proves_of_derivable h
    obtain ⟨-, -, rfl⟩ := pj_inj e
    exact ⟨φ, rfl, (derivable_iff_PA_proves φ).1 h⟩
  · rintro ⟨φ, rfl, h⟩
    exact (derivable_iff_PA_proves φ).2 h

/-- The strengthened PA proof search. -/
noncomputable def searchPA : Code := PA_theorems_ce'.choose

/-- Specification of `searchPA`. -/
theorem searchPA_spec (x : Nat) : Halts searchPA [x] ↔ ∃ φ, x = fcode φ ∧ PA ⊢₁ φ :=
  PA_theorems_ce'.choose_spec x

/-- **The axiom clause.** The Σ₁ formula "the PA proof search halts on `x`"
(free variable `0`). -/
noncomputable def accF : Formula Arith := haltsSigma searchPA

/-- `accF` has no free variable other than `0`. -/
theorem accF_fresh (m : Nat) : accF.Fresh (m + 1) := evalSigma_fresh _ (m + 2) (by omega)

/-- Only the value of the variable `0` matters for `accF`. -/
theorem sat_accF_cons {M : Structure Arith} (y : M.Dom) (e e' : Nat → M.Dom) :
    Sat M (Env.cons y e) accF ↔ Sat M (Env.cons y e') accF :=
  sat_congr_fresh accF fun n hn => by
    cases n with
    | zero => rfl
    | succ m => exact absurd (accF_fresh m) hn

/-- Meaning of `accF` in `ℕ`. -/
theorem sat_accF_std (x : Nat) (e : Nat → Nat) :
    Sat stdModel (Env.cons x e) accF ↔ ∃ φ, x = fcode φ ∧ PA ⊢₁ φ := by
  rw [← searchPA_spec]
  simp only [accF, haltsSigma, Sat]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, (sat_evalSigma searchPA y x).1 ((sat_congr_fresh _ fun n hn => ?_).1 hy)⟩
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact absurd (evalSigma_fresh _ (n + 2) (by omega)) hn
  · rintro ⟨y, hy⟩
    refine ⟨y, (sat_congr_fresh _ fun n hn => ?_).1 ((sat_evalSigma searchPA y x).2 hy)⟩
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact absurd (evalSigma_fresh _ (n + 2) (by omega)) hn

/-! ## The necessitation function -/

/-- The necessitation function on Gödel numbers: `⌜φ⌝ ↦ ⌜accF(⌜φ⌝)⌝`. -/
noncomputable def necFun (a : Nat) : Nat := instC (fcode accF) (ncode a)

/-- `necFun` computes the necessitation of a formula. -/
theorem necFun_fcode (φ : Formula Arith) : necFun (fcode φ) = fcode (box accF φ) := by
  rw [necFun, ncode, instC_fcode, box]

/-- `necFun` is computable. -/
theorem necFun_comp : Comp necFun := Comp.instC (Comp.const _) Comp.ncode

/-- A program computing `necFun`. -/
noncomputable def necCode : Code := necFun_comp.choose

/-- Specification of `necCode`. -/
theorem necCode_spec (a : Nat) : Eval necCode [a] (necFun a) := necFun_comp.choose_spec a

/-! ## The semantic predicates, in an arbitrary model of PA -/

namespace PAModel

variable {N : PAModel}

/-- The axiom clause in `N`: the proof search "halts on `y`" in the sense of `N`. -/
@[irreducible] def AccM (y : N.Dom) : Prop := Sat N.M (Env.cons y fun _ => 0) accF

/-- The necessitation clause in `N`: `y = necFun(a)` in the sense of `N` (via the Σ₁
graph of the program `necCode`). -/
@[irreducible] def NecM (a y : N.Dom) : Prop :=
  Sat N.M (Env.cons y (Env.cons a fun _ => 0)) (evalSigma necCode)

/-- Cantor pairing in `N`: `p = ⟨a, b⟩`, expressed by `2p = (a+b)(a+b+1) + 2a`. -/
def PairM (a b p : N.Dom) : Prop := p + p = (a + b) * (a + b + 1) + a + a

/-- The modus ponens clause in `N`: `a = ⟨2, ⟨b, y⟩⟩`, i.e. `a = ⌜φ → ψ⌝` when `b = ⌜φ⌝`
and `y = ⌜ψ⌝`. -/
def MPM (a b y : N.Dom) : Prop := ∃ u, PairM b y u ∧ PairM 2 u a

/-- **A justified line.** The `k`-th entry of the sequence coded by `(c, d)` is accepted
by the proof search, or follows from two earlier entries by modus ponens, or from one
earlier entry by necessitation. -/
def LineOK (c d k : N.Dom) : Prop :=
  ∃ y, BetaM c d k y ∧ (AccM y ∨
    (∃ i, i < k ∧ ∃ j, j < k ∧ ∃ a, ∃ b, BetaM c d i a ∧ BetaM c d j b ∧ MPM a b y) ∨
    (∃ i, i < k ∧ ∃ a, BetaM c d i a ∧ NecM a y))

/-- **Provability in `N`.** `x` is the last entry `yₙ` of a coded sequence all of whose
entries `y₀, …, yₙ` are justified. -/
def ProvM (x : N.Dom) : Prop := ∃ c d n, BetaM c d n x ∧ ∀ k, k ≤ n → LineOK c d k

/-- The axiom clause is uniformly definable. -/
noncomputable def UDef.acc {f : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f) :
    UDef fun N e => AccM (f N e) :=
  ⟨accF.subst (Env.cons hf.t fun _ => numeral 0), fun N e => by
    rw [sat_subst, AccM]
    have : (fun n => (Env.cons hf.t (fun _ => numeral 0) n).eval N.M e) =
        Env.cons (f N e) fun _ => (0 : N.Dom) := by
      funext n; cases n with
      | zero => exact hf.spec N e
      | succ n => exact eval_numeral_M e 0
    rw [this]⟩

/-- The necessitation clause is uniformly definable. -/
noncomputable def UDef.nec {f g : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f)
    (hg : UDefT g) : UDef fun N e => NecM (f N e) (g N e) :=
  ⟨(evalSigma necCode).subst (Env.cons hg.t (Env.cons hf.t fun _ => numeral 0)), fun N e => by
    rw [sat_subst, NecM]
    have : (fun n => (Env.cons hg.t (Env.cons hf.t fun _ => numeral 0) n).eval N.M e) =
        Env.cons (g N e) (Env.cons (f N e) fun _ => (0 : N.Dom)) := by
      funext n; match n with
      | 0 => exact hg.spec N e
      | 1 => exact hf.spec N e
      | n + 2 => exact eval_numeral_M e 0
    rw [this]⟩

macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.acc)
macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.nec)

/-- The uniform definition of `ProvM`. -/
noncomputable def provHDef : UDef fun N e => ProvM (N := N) (e 0) := by
  unfold ProvM LineOK MPM PairM; udfn

end PAModel

open PAModel

/-- **The Hilbert-style provability formula of PA.** With free variable `0`, it says "`x` is the
last line of a finite sequence each line of which is a theorem accepted by the PA proof
search, or follows from earlier lines by modus ponens or by necessitation". -/
noncomputable def provH : Formula Arith := provHDef.φ

/-- **Meaning of `provH` in every model of PA.** -/
theorem sat_provH_M (N : PAModel) (e : Nat → N.Dom) : Sat N.M e provH ↔ ProvM (e 0) :=
  provHDef.spec N e

/-- Meaning of `□φ := provH(⌜φ⌝)` in every model of PA. -/
theorem sat_box_provH (N : PAModel) (e : Nat → N.Dom) (φ : Formula Arith) :
    Sat N.M e (box provH φ) ↔ ProvM ((fcode φ : Nat) : N.Dom) := by
  rw [box, sat_inst, sat_provH_M]
  exact Iff.of_eq (congrArg ProvM (eval_numeral_M e _))

/-- Meaning of `accF(⌜φ⌝)` in every model of PA. -/
theorem sat_box_accF (N : PAModel) (e : Nat → N.Dom) (φ : Formula Arith) :
    Sat N.M e (box accF φ) ↔ AccM ((fcode φ : Nat) : N.Dom) := by
  rw [box, sat_inst, AccM, eval_numeral_M]
  exact sat_accF_cons _ _ _

/-! ## Standard facts hold for numerals in every model -/

namespace PAModel

variable {N : PAModel}

/-- The cast `ℕ → N` preserves addition. -/
theorem natCast_add (a b : Nat) : ((a + b : Nat) : N.Dom) = a + b := (numM_add N.isQ a b).symm

/-- The cast `ℕ → N` preserves multiplication. -/
theorem natCast_mul (a b : Nat) : ((a * b : Nat) : N.Dom) = a * b := (numM_mul N.isQ a b).symm

/-- The cast of `1`. -/
theorem natCast_one : ((1 : Nat) : N.Dom) = 1 := rfl

/-- Twice a triangular number. -/
theorem tri_double (s : Nat) : Computability.tri s + Computability.tri s = s * (s + 1) := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [Computability.tri]; grind

/-- Twice a Cantor pair. -/
theorem pair_double (a b : Nat) : pair a b + pair a b = (a + b) * (a + b + 1) + a + a := by
  have := tri_double (a + b); unfold pair; omega

/-- Cantor pairing of numerals, inside `N`. -/
theorem pairM_natCast (a b : Nat) : PairM (a : N.Dom) b (pair a b) := by
  have h := congrArg (fun n : Nat => (n : N.Dom)) (pair_double a b)
  simp only [natCast_add, natCast_mul, natCast_one] at h
  exact h

/-- The modus ponens relation for numerals, inside `N`. -/
theorem mpm_natCast (b y : Nat) : MPM ((pair 2 (pair b y) : Nat) : N.Dom) (b : N.Dom) (y : N.Dom) :=
  ⟨_, pairM_natCast b y, pairM_natCast 2 (pair b y)⟩

/-- **Σ₁-completeness for the axiom clause.** If the proof search halts on `x`, then
`N` thinks so too. -/
theorem acc_of_halts {x : Nat} (h : Halts searchPA [x]) : AccM ((x : Nat) : N.Dom) := by
  have := sat_of_Q_proves (Q_proves_halts h) N.isQ (fun _ => 0)
  rw [sat_inst, eval_numeral_M] at this
  rw [AccM]; exact this

/-- **Σ₁-completeness for the necessitation clause.** -/
theorem nec_natCast (a : Nat) : NecM ((a : Nat) : N.Dom) ((necFun a : Nat) : N.Dom) := by
  have := sat_of_Q_proves (Q_proves_eval (necCode_spec a)) N.isQ (fun _ => 0)
  rw [sat_subst_numerals] at this
  rw [NecM]
  have e : (fun n => numM N.M (penv (necFun a) a n)) =
      Env.cons ((necFun a : Nat) : N.Dom) (Env.cons ((a : Nat) : N.Dom) fun _ => 0) := by
    funext n; match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => simp [penv]; rfl
  rw [← e]; exact this

/-- A one-entry β-code: `(a, a)` codes the sequence `a`. -/
theorem betaM_single (a : N.Dom) : BetaM a a 0 a := ⟨0, by grind, ⟨0, by grind⟩⟩

/-- `k ≤ 0` forces `k = 0`. -/
theorem eq_zero_of_le_zero {k : N.Dom} (h : k ≤ 0) : k = 0 := le_antisymm' h (zero_le' k)

/-- **Accepted formulas are provable**, by a one-line proof. -/
theorem provM_of_acc {y : N.Dom} (h : AccM y) : ProvM y :=
  ⟨y, y, 0, betaM_single y, fun k hk => ⟨y, by rw [eq_zero_of_le_zero hk]; exact betaM_single y,
    Or.inl h⟩⟩

end PAModel

/-! ## The standard model -/

/-- The standard model, as a model of PA. -/
abbrev stdPA : PAModel := ⟨stdModel, stdModel_isModel⟩

/-- `≤` of the standard model is the usual order. -/
theorem stdPA_le {a b : Nat} : @LE.le stdPA.Dom PAModel.instLE a b ↔ a ≤ b :=
  ⟨fun ⟨z, hz⟩ => by have hz' : a + (z : Nat) = b := hz; omega,
    fun h => ⟨b - a, by change (a + (b - a) : Nat) = b; omega⟩⟩

/-- `<` of the standard model is the usual order. -/
theorem stdPA_lt {a b : Nat} : @LT.lt stdPA.Dom PAModel.instLT a b ↔ a < b :=
  ⟨fun ⟨z, hz⟩ => by have hz' : a + 1 + (z : Nat) = b := hz; omega,
    fun h => ⟨b - a - 1, by change (a + 1 + (b - a - 1) : Nat) = b; omega⟩⟩

/-- Cantor pairing in the standard model is Cantor pairing. -/
theorem stdPA_pairM {a b p : Nat} (h : PairM (N := stdPA) a b p) : p = pair a b := by
  change (p + p : Nat) = (a + b) * (a + b + 1) + a + a at h
  have := (h.trans (PAModel.pair_double a b).symm); omega

/-- **Soundness of `ProvM` in the standard model.** Every line of a justified sequence
is the Gödel number of a theorem of PA. -/
theorem provM_std_sound {x : Nat} (h : ProvM (N := stdPA) x) : ∃ φ, x = fcode φ ∧ PA ⊢₁ φ := by
  obtain ⟨c, d, n, hn, hall⟩ := h
  have key : ∀ k : Nat, k ≤ n → ∀ y : Nat, BetaM (N := stdPA) c d k y →
      ∃ φ, y = fcode φ ∧ PA ⊢₁ φ := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk y hy
      obtain ⟨y', hy', hj⟩ := hall k (stdPA_le.2 hk)
      rw [betaM_unique hy hy']
      rcases hj with hacc | ⟨i, hi, j, hj, a, b, ha, hb, u, hu, hu'⟩ | ⟨i, hi, a, ha, hnec⟩
      · rw [AccM] at hacc
        exact (sat_accF_std y' _).1 hacc
      · have hi' := stdPA_lt.1 hi; have hj' := stdPA_lt.1 hj
        obtain ⟨φa, rfl, hφa⟩ := ih i hi' (by omega) a ha
        obtain ⟨φb, rfl, hφb⟩ := ih j hj' (by omega) b hb
        have e₁ := stdPA_pairM hu; have e₂ := stdPA_pairM hu'
        obtain ⟨A, B, rfl⟩ := fcode_tag_imp (Φ := φa) (by rw [e₂]; exact fst_pair _ _)
        have e₃ : pair 2 (pair (fcode A) (fcode B)) = pair 2 (pair (fcode φb) y') := by
          rw [← e₁]; exact e₂
        obtain ⟨-, e₄⟩ := pair_inj e₃
        obtain ⟨e₅, rfl⟩ := pair_inj e₄
        rw [fcode_inj e₅] at hφa
        exact ⟨B, rfl, Proves.impE hφa hφb⟩
      · have hi' := stdPA_lt.1 hi
        obtain ⟨φa, rfl, hφa⟩ := ih i hi' (by omega) a ha
        unfold NecM at hnec
        have hev : Eval necCode [fcode φa] y' := by
          have := (sat_evalSigma necCode y' (fcode φa)).1
          refine this ((sat_congr_fresh _ fun n hn => ?_).1 hnec)
          match n with
          | 0 => rfl
          | 1 => rfl
          | n + 2 => exact absurd (evalSigma_fresh _ (n + 2) (by omega)) hn
        rw [← Eval.det (necCode_spec (fcode φa)) hev, necFun_fcode]
        exact ⟨_, rfl, PA_proves_of_Q_proves
          (Q_proves_halts ((searchPA_spec _).2 ⟨φa, rfl, hφa⟩))⟩
  exact key n (Nat.le_refl n) x hn

/-- **`provH` defines PA-provability in the standard model.** -/
theorem sat_provH (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provH φ) ↔ PA ⊢₁ φ := by
  have hc : (@Nat.cast stdPA.Dom (PAModel.instNatCast stdPA) (fcode φ)) = fcode φ := numM_std _
  refine (sat_box_provH stdPA e φ).trans ?_
  rw [hc]
  constructor
  · intro h
    obtain ⟨ψ, hψ, hp⟩ := provM_std_sound h
    rwa [fcode_inj hψ]
  · intro h
    have := PAModel.provM_of_acc (N := stdPA) (PAModel.acc_of_halts ((searchPA_spec _).2 ⟨φ, rfl, h⟩))
    rwa [hc] at this

/-- **Condition (D1) for `provH`.** If `PA ⊢ φ` then `PA ⊢ provH(⌜φ⌝)`. -/
theorem provH_D1 {φ : Formula Arith} (h : PA ⊢₁ φ) : PA ⊢₁ box provH φ :=
  PA_proves_of_models fun N e => (sat_box_provH N e φ).2
    (PAModel.provM_of_acc (PAModel.acc_of_halts ((searchPA_spec _).2 ⟨φ, rfl, h⟩)))

end Foundations.Logic.FO
