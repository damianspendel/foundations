import Foundations.Logic.Universal
import Foundations.Logic.PeanoArithmetic

/-!
# Arithmetisation of syntax: Gödel numbers of formulas, computably manipulated

To show that the theorems of Peano arithmetic can be *listed by an algorithm*, the
algorithm must handle formulas — and algorithms handle only numbers. This is the
step Gödel called the **arithmetisation of syntax**: we assign to every term and
formula of arithmetic a **Gödel number** and show that the basic syntactic operations
become *computable functions* on these numbers.

* Terms: `var n ↦ ⟨0, n⟩`, `0 ↦ ⟨1, 0⟩`, `S t ↦ ⟨2, ⌜t⌝⟩`, `t + s ↦ ⟨3, ⟨⌜t⌝, ⌜s⌝⟩⟩`,
  `t × s ↦ ⟨4, ⟨⌜t⌝, ⌜s⌝⟩⟩`.
* Formulas: `⊥ ↦ ⟨0, 0⟩`, `t = s ↦ ⟨1, ⟨⌜t⌝, ⌜s⌝⟩⟩`, `→, ∧, ∨ ↦ ⟨2|3|4, ⟨⌜φ⌝, ⌜ψ⌝⟩⟩`,
  `∀, ∃ ↦ ⟨5|6, ⌜φ⌝⟩`.

The numbering is injective, and **well-formedness** ("is this number the code of a
formula?") is decidable by a computable test. The central computable operation is
**substitution**: shifting free variables (needed by the ∀-introduction rule),
instantiating a quantifier `φ(t)` (∀-elimination, ∃-introduction, Leibniz's law) and
the substitution `x ↦ Sx` of the induction schema. All three are instances of one
course-of-values recursion on codes, carrying the number `d` of binders passed so far
(de Bruijn's *lifting*); since a subformula has a smaller number than the formula,
the pair `⟨φ, d⟩` decreases at each recursive call even when `d` grows.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula Computability

/-! ## Canonical forms of arithmetic terms -/

/-- A `0`-ary application is the constant `0`. -/
theorem func_zero_eq (ts : Fin 0 → Term Arith) : Term.func (L := Arith) ArithFunc.zero ts = zero := by
  unfold zero; congr; funext i; exact i.elim0

/-- A unary application is a successor term. -/
theorem func_succ_eq (ts : Fin 1 → Term Arith) :
    Term.func (L := Arith) ArithFunc.succ ts = succ (ts 0) := by
  unfold succ; congr; funext i; match i with | ⟨0, _⟩ => rfl

/-- A binary `+`-application is a sum term. -/
theorem func_add_eq (ts : Fin 2 → Term Arith) :
    Term.func (L := Arith) ArithFunc.add ts = add (ts 0) (ts 1) := by
  unfold add args₂; congr; funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

/-- A binary `×`-application is a product term. -/
theorem func_mul_eq (ts : Fin 2 → Term Arith) :
    Term.func (L := Arith) ArithFunc.mul ts = mul (ts 0) (ts 1) := by
  unfold mul args₂; congr; funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

/-- **Induction over arithmetic terms**, by their five canonical forms. -/
theorem Term.arith_induction {P : Term Arith → Prop} (hv : ∀ n, P (v n)) (hz : P zero)
    (hs : ∀ t, P t → P (succ t)) (ha : ∀ t s, P t → P s → P (add t s))
    (hm : ∀ t s, P t → P s → P (mul t s)) : ∀ t, P t := by
  intro t
  induction t with
  | var n => exact hv n
  | func f ts ih =>
      cases f
      · rw [func_zero_eq]; exact hz
      · rw [func_succ_eq]; exact hs _ (ih 0)
      · rw [func_add_eq]; exact ha _ _ (ih 0) (ih 1)
      · rw [func_mul_eq]; exact hm _ _ (ih 0) (ih 1)

/-- Case analysis over arithmetic terms. -/
theorem Term.arith_cases {P : Term Arith → Prop} (hv : ∀ n, P (v n)) (hz : P zero)
    (hs : ∀ t, P (succ t)) (ha : ∀ t s, P (add t s)) (hm : ∀ t s, P (mul t s)) : ∀ t, P t :=
  Term.arith_induction hv hz (fun t _ => hs t) (fun t s _ _ => ha t s) (fun t s _ _ => hm t s)

/-- **Induction over arithmetic formulas** (the language has no relation symbols
besides equality). -/
theorem Formula.arith_induction {P : Formula Arith → Prop} (hb : P bot)
    (he : ∀ t s, P (eq t s)) (hi : ∀ φ ψ, P φ → P ψ → P (imp φ ψ))
    (hc : ∀ φ ψ, P φ → P ψ → P (conj φ ψ)) (hd : ∀ φ ψ, P φ → P ψ → P (disj φ ψ))
    (ha : ∀ φ, P φ → P (all φ)) (hx : ∀ φ, P φ → P (ex φ)) : ∀ φ, P φ
  | .bot => hb
  | .eq t s => he t s
  | .rel R _ => (R : Empty).elim
  | .imp φ ψ => hi _ _ (Formula.arith_induction hb he hi hc hd ha hx φ)
      (Formula.arith_induction hb he hi hc hd ha hx ψ)
  | .conj φ ψ => hc _ _ (Formula.arith_induction hb he hi hc hd ha hx φ)
      (Formula.arith_induction hb he hi hc hd ha hx ψ)
  | .disj φ ψ => hd _ _ (Formula.arith_induction hb he hi hc hd ha hx φ)
      (Formula.arith_induction hb he hi hc hd ha hx ψ)
  | .all φ => ha _ (Formula.arith_induction hb he hi hc hd ha hx φ)
  | .ex φ => hx _ (Formula.arith_induction hb he hi hc hd ha hx φ)

/-- Case analysis over arithmetic formulas. -/
theorem Formula.arith_cases {P : Formula Arith → Prop} (hb : P bot)
    (he : ∀ t s, P (eq t s)) (hi : ∀ φ ψ, P (imp φ ψ)) (hc : ∀ φ ψ, P (conj φ ψ))
    (hd : ∀ φ ψ, P (disj φ ψ)) (ha : ∀ φ, P (all φ)) (hx : ∀ φ, P (ex φ)) : ∀ φ, P φ :=
  Formula.arith_induction hb he (fun φ ψ _ _ => hi φ ψ) (fun φ ψ _ _ => hc φ ψ)
    (fun φ ψ _ _ => hd φ ψ) (fun φ _ => ha φ) (fun φ _ => hx φ)

/-- Renaming and substitution on the canonical term forms. -/
@[simp] theorem zero_rename (ρ : Nat → Nat) : zero.rename ρ = zero := by
  simp only [zero, Term.rename]; congr; funext i; exact i.elim0

/-- Renaming a successor term. -/
@[simp] theorem succ_rename (ρ : Nat → Nat) (t : Term Arith) :
    (succ t).rename ρ = succ (t.rename ρ) := rfl

/-- Renaming a sum term. -/
@[simp] theorem add_rename (ρ : Nat → Nat) (t s : Term Arith) :
    (add t s).rename ρ = add (t.rename ρ) (s.rename ρ) := by
  simp only [add, Term.rename]; congr; funext i; simp only [args₂]; split <;> rfl

/-- Renaming a product term. -/
@[simp] theorem mul_rename (ρ : Nat → Nat) (t s : Term Arith) :
    (mul t s).rename ρ = mul (t.rename ρ) (s.rename ρ) := by
  simp only [mul, Term.rename]; congr; funext i; simp only [args₂]; split <;> rfl

/-- Substituting into `0`. -/
@[simp] theorem zero_subst' (σ : Nat → Term Arith) : zero.subst σ = zero := zero_subst σ

/-- Substituting into a successor term. -/
@[simp] theorem succ_subst (σ : Nat → Term Arith) (t : Term Arith) :
    (succ t).subst σ = succ (t.subst σ) := rfl

/-- Substituting into a sum term. -/
@[simp] theorem add_subst (σ : Nat → Term Arith) (t s : Term Arith) :
    (add t s).subst σ = add (t.subst σ) (s.subst σ) := by
  simp only [add, Term.subst]; congr; funext i; simp only [args₂]; split <;> rfl

/-- Substituting into a product term. -/
@[simp] theorem mul_subst (σ : Nat → Term Arith) (t s : Term Arith) :
    (mul t s).subst σ = mul (t.subst σ) (s.subst σ) := by
  simp only [mul, Term.subst]; congr; funext i; simp only [args₂]; split <;> rfl

/-! ## Gödel numbers -/

/-- Codes of applications of the function symbols, given the codes of the arguments. -/
def funcCode : {n : Nat} → ArithFunc n → (Fin n → Nat) → Nat
  | _, .zero, _ => pair 1 0
  | _, .succ, c => pair 2 (c 0)
  | _, .add, c => pair 3 (pair (c 0) (c 1))
  | _, .mul, c => pair 4 (pair (c 0) (c 1))

/-- **Gödel number of a term.** -/
def tcode : Term Arith → Nat
  | .var n => pair 0 n
  | .func f ts => funcCode f fun i => tcode (ts i)

/-- Code of a variable. -/
@[simp] theorem tcode_var (n : Nat) : tcode (v n) = pair 0 n := rfl
/-- Code of `0`. -/
@[simp] theorem tcode_zero : tcode zero = pair 1 0 := rfl
/-- Code of a successor term. -/
@[simp] theorem tcode_succ (t : Term Arith) : tcode (succ t) = pair 2 (tcode t) := rfl
/-- Code of a sum term. -/
@[simp] theorem tcode_add (t s : Term Arith) : tcode (add t s) = pair 3 (pair (tcode t) (tcode s)) := rfl
/-- Code of a product term. -/
@[simp] theorem tcode_mul (t s : Term Arith) : tcode (mul t s) = pair 4 (pair (tcode t) (tcode s)) := rfl

/-- **Gödel number of a formula.** -/
def fcode : Formula Arith → Nat
  | .bot => pair 0 0
  | .eq t s => pair 1 (pair (tcode t) (tcode s))
  | .rel R _ => (R : Empty).elim
  | .imp φ ψ => pair 2 (pair (fcode φ) (fcode ψ))
  | .conj φ ψ => pair 3 (pair (fcode φ) (fcode ψ))
  | .disj φ ψ => pair 4 (pair (fcode φ) (fcode ψ))
  | .all φ => pair 5 (fcode φ)
  | .ex φ => pair 6 (fcode φ)

/-- Injectivity of pairing, as an equivalence. -/
theorem pair_eq_pair {a b c d : Nat} : pair a b = pair c d ↔ a = c ∧ b = d :=
  ⟨pair_inj, fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩

/-- Only `⟨0, 0⟩` is `0`. -/
@[simp] theorem zero_eq_pair {a b : Nat} : 0 = pair a b ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h; have := pair_inj (show pair 0 0 = pair a b from h); omega
  · rintro ⟨rfl, rfl⟩; rfl

/-- Only `⟨0, 0⟩` is `0`. -/
@[simp] theorem pair_eq_zero {a b : Nat} : pair a b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [eq_comm, zero_eq_pair]

/-- **The numbering of terms is injective.** -/
theorem tcode_inj : ∀ {t s : Term Arith}, tcode t = tcode s → t = s := by
  intro t
  induction t using Term.arith_induction with
  | hv n => intro s h; cases s using Term.arith_cases <;> simp_all [pair_eq_pair]
  | hz => intro s h; cases s using Term.arith_cases <;> simp_all [pair_eq_pair]
  | hs t ih =>
      intro s h; cases s using Term.arith_cases <;> simp [pair_eq_pair] at h
      exact congrArg succ (ih h)
  | ha t s iht ihs =>
      intro u h; cases u using Term.arith_cases <;> simp [pair_eq_pair] at h
      rw [iht h.1, ihs h.2]
  | hm t s iht ihs =>
      intro u h; cases u using Term.arith_cases <;> simp [pair_eq_pair] at h
      rw [iht h.1, ihs h.2]

/-- **The numbering of formulas is injective.** -/
theorem fcode_inj : ∀ {φ ψ : Formula Arith}, fcode φ = fcode ψ → φ = ψ := by
  intro φ
  induction φ using Formula.arith_induction with
  | hb => intro ψ h; cases ψ using Formula.arith_cases <;> simp [fcode, pair_eq_pair] at h ⊢
  | he t s =>
      intro ψ h; cases ψ using Formula.arith_cases <;> simp [fcode, pair_eq_pair] at h
      rw [tcode_inj h.1, tcode_inj h.2]
  | hi φ ψ ih₁ ih₂ =>
      intro χ h; cases χ using Formula.arith_cases <;> simp [fcode, pair_eq_pair] at h
      rw [ih₁ h.1, ih₂ h.2]
  | hc φ ψ ih₁ ih₂ =>
      intro χ h; cases χ using Formula.arith_cases <;> simp [fcode, pair_eq_pair] at h
      rw [ih₁ h.1, ih₂ h.2]
  | hd φ ψ ih₁ ih₂ =>
      intro χ h; cases χ using Formula.arith_cases <;> simp [fcode, pair_eq_pair] at h
      rw [ih₁ h.1, ih₂ h.2]
  | ha φ ih =>
      intro χ h; cases χ using Formula.arith_cases <;> simp [fcode, pair_eq_pair] at h
      rw [ih h]
  | hx φ ih =>
      intro χ h; cases χ using Formula.arith_cases <;> simp [fcode, pair_eq_pair] at h
      rw [ih h]

/-! ## Course-of-values notation -/

/-- The parameter in a course-of-values step argument `⟨p, ⟨n, H⟩⟩`. -/
abbrev cvP (q : Nat) : Nat := fst q
/-- The current index in a course-of-values step argument. -/
abbrev cvN (q : Nat) : Nat := fst (snd q)
/-- The value at an earlier index `m`, read from the history. -/
abbrev cvRec (q m : Nat) : Nat := histGet (snd (snd q)) (fst (snd q)) m

/-- Unfolding a course-of-values recursion at an index whose recursive calls are at
smaller indices. -/
theorem covRec_unfold (g : Nat → Nat) (x n : Nat) :
    covRec g x n = g (pair x (pair n (covHist g x n))) := rfl

/-- The second component of a pair with positive first component is smaller. -/
theorem lt_pair_of_pos {a b : Nat} (ha : 0 < a) : b < pair a b := by
  have := right_le_pair a b
  have : tri (a + b) ≥ a + b := le_tri _
  simp only [pair]; omega

/-- Components of a code with positive tag are smaller than the code. -/
theorem fst_lt_tagged {a b c : Nat} (ha : 0 < a) : b < pair a (pair b c) :=
  Nat.lt_of_le_of_lt (left_le_pair b c) (lt_pair_of_pos ha)

/-- Components of a code with positive tag are smaller than the code. -/
theorem snd_lt_tagged {a b c : Nat} (ha : 0 < a) : c < pair a (pair b c) :=
  Nat.lt_of_le_of_lt (right_le_pair b c) (lt_pair_of_pos ha)

/-- Pairing is strictly monotone in the first argument. -/
theorem pair_lt_pair_left {a a' b : Nat} (h : a < a') : pair a b < pair a' b := by
  have := tri_mono (show a + b ≤ a' + b by omega)
  simp only [pair]; omega

/-- Passing under a binder: `⟨φ', d + 1⟩ < ⟨φ, d⟩` whenever `φ' < φ`. -/
theorem pair_lt_pair_succ {a a' d : Nat} (h : a < a') : pair a (d + 1) < pair a' d := by
  have := tri_mono (show a + (d + 1) ≤ a' + d by omega)
  simp only [pair]; omega

/-- Congruence for codes of binary constructions. -/
theorem pair_congr3 {k a a' b b' : Nat} (h₁ : a = a') (h₂ : b = b') :
    pair k (pair a b) = pair k (pair a' b') := by rw [h₁, h₂]

/-! ## Renaming terms by `+ d` -/

/-- One step of `trename`: add the parameter `d` to every variable index. -/
def trenameStep (q : Nat) : Nat :=
  bif fst (cvN q) == 0 then pair 0 (snd (cvN q) + cvP q)
  else bif fst (cvN q) == 2 then pair 2 (cvRec q (snd (cvN q)))
  else bif fst (cvN q) == 3 || fst (cvN q) == 4 then
    pair (fst (cvN q)) (pair (cvRec q (fst (snd (cvN q)))) (cvRec q (snd (snd (cvN q)))))
  else cvN q

/-- `trename d ⌜t⌝ = ⌜t[n ↦ n + d]⌝` (on codes). -/
def trename (d t : Nat) : Nat := covRec trenameStep d t

/-- Correctness of `trename`. -/
theorem trename_tcode (d : Nat) : ∀ t : Term Arith, trename d (tcode t) = tcode (t.rename (· + d)) := by
  intro t
  induction t using Term.arith_induction with
  | hv n => simp [trename, covRec_unfold, cvN, cvP, cvRec, trenameStep, Term.rename]
  | hz => simp [trename, covRec_unfold, cvN, cvP, cvRec, trenameStep]
  | hs t ih =>
      simp only [trename, covRec_unfold, cvN, cvP, cvRec, trenameStep, tcode_succ, fst_pair, snd_pair, succ_rename]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false]
      rw [histGet_covHist _ _ _ _ (lt_pair_of_pos (by omega))]; exact congrArg _ ih
  | ha t s iht ihs =>
      simp only [trename, covRec_unfold, cvN, cvP, cvRec, trenameStep, tcode_add, fst_pair, snd_pair, add_rename]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or]
      rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
        histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
      exact pair_congr3 (iht) (ihs)
  | hm t s iht ihs =>
      simp only [trename, covRec_unfold, cvN, cvP, cvRec, trenameStep, tcode_mul, fst_pair, snd_pair, mul_rename]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true]
      rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
        histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
      exact pair_congr3 (iht) (ihs)

/-- `trename` is computable. -/
theorem Comp.trename {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    Comp fun n => FO.trename (f n) (g n) := by
  have hs : Comp trenameStep := by unfold trenameStep; comp_tac
  exact Comp.congr (Comp.comp (Comp.covRec hs) (Comp.pair hf hg)) fun n => by simp [FO.trename]

/-! ## Substitution -/

/-- The three substitutions needed by the proof rules: `sigma 0 t` instantiates
index `0` by `t` (and lowers the others), `sigma 1 _` shifts all indices up, and
`sigma 2 _` (or larger) is the induction substitution `x ↦ Sx`. -/
def sigma : Nat → Term Arith → Nat → Term Arith
  | 0, t => Subst.single t
  | 1, _ => fun n => .var (n + 1)
  | _ + 2, _ => succSubst

/-- `d`-fold lifting of a substitution (passing under `d` binders). -/
def liftN : Nat → (Nat → Term Arith) → Nat → Term Arith
  | 0, σ => σ
  | d + 1, σ => Subst.lift (liftN d σ)

/-- Renamings compose. -/
theorem rename_rename (ρ ρ' : Nat → Nat) :
    ∀ t : Term Arith, (t.rename ρ).rename ρ' = t.rename (fun n => ρ' (ρ n)) := by
  intro t
  induction t using Term.arith_induction with
  | hv n => rfl
  | hz => simp
  | hs t ih => simp [ih]
  | ha t s iht ihs => simp [iht, ihs]
  | hm t s iht ihs => simp [iht, ihs]

/-- **Lifting, explicitly**: under `d` binders, indices below `d` are untouched and
the others are substituted and shifted by `d`. -/
theorem liftN_apply (σ : Nat → Term Arith) :
    ∀ d n, liftN d σ n = if n < d then .var n else (σ (n - d)).rename (· + d)
  | 0, n => by
      simp only [liftN, Nat.not_lt_zero, ite_false, Nat.sub_zero]
      have : ∀ t : Term Arith, t.rename (· + 0) = t := by
        intro t; rw [Term.rename_eq_subst]; exact Term.subst_var t
      exact (this _).symm
  | d + 1, n => by
      cases n with
      | zero => simp [liftN, Subst.lift]
      | succ n =>
          simp only [liftN, Subst.lift, liftN_apply σ d n]
          by_cases h : n < d
          · simp [h, Term.rename]
          · simp only [h, ite_false, show ¬ (n + 1 < d + 1) by omega, rename_rename,
              show n + 1 - (d + 1) = n - d by omega]
            exact congrArg (fun ρ => Term.rename ρ _) (funext fun m => by omega)

/-- The code of the term substituted for variable `n` under `d` binders, given the
mode and the code `t` of the instantiating term. -/
def tvar (mode t d n : Nat) : Nat :=
  bif decide (n < d) then pair 0 n
  else bif mode == 0 then (bif n == d then trename d t else pair 0 (n - 1))
  else bif mode == 1 then pair 0 (n + 1)
  else bif n == d then pair 2 (pair 0 d) else pair 0 n

/-- Correctness of `tvar`. -/
theorem tvar_spec (mode : Nat) (t : Term Arith) (d n : Nat) :
    tvar mode (tcode t) d n = tcode (liftN d (sigma mode t) n) := by
  rw [liftN_apply]
  by_cases h : n < d
  · simp [tvar, h]
  · simp only [tvar, h, decide_false, Bool.cond_false, ite_false]
    obtain ⟨m, hm⟩ : ∃ m, n = d + m := ⟨n - d, by omega⟩
    subst hm
    rw [show d + m - d = m by omega]
    match mode, m with
    | 0, 0 => simp [sigma, Subst.single, trename_tcode]
    | 0, m + 1 =>
        have hb : (d + (m + 1) == d) = false := by simp
        simp only [beq_self_eq_true, Bool.cond_true, hb, Bool.cond_false, sigma, Subst.single,
          Term.rename, tcode_var]
        congr 1; omega
    | 1, m =>
        simp only [show (1 == 0) = false from rfl, beq_self_eq_true, Bool.cond_false,
          Bool.cond_true, sigma, Term.rename, tcode_var]
        congr 1; omega
    | k + 2, 0 =>
        simp [sigma, succSubst, Term.rename]
    | k + 2, m + 1 =>
        have hb : (d + (m + 1) == d) = false := by simp
        simp only [show (k + 2 == 0) = false from rfl, show (k + 2 == 1) = false from rfl,
          Bool.cond_false, hb, sigma, succSubst, Term.rename, tcode_var]
        congr 1; omega

/-- One step of term substitution; the parameter is `⟨mode, ⟨t, d⟩⟩`. -/
def tsubStep (q : Nat) : Nat :=
  bif fst (cvN q) == 0 then tvar (fst (cvP q)) (fst (snd (cvP q))) (snd (snd (cvP q))) (snd (cvN q))
  else bif fst (cvN q) == 2 then pair 2 (cvRec q (snd (cvN q)))
  else bif fst (cvN q) == 3 || fst (cvN q) == 4 then
    pair (fst (cvN q)) (pair (cvRec q (fst (snd (cvN q)))) (cvRec q (snd (snd (cvN q)))))
  else cvN q

/-- Term substitution on codes: `tsub ⟨mode, ⟨⌜t⌝, d⟩⟩ ⌜s⌝ = ⌜s[liftN d (sigma mode t)]⌝`. -/
def tsub (p s : Nat) : Nat := covRec tsubStep p s

/-- Correctness of `tsub`. -/
theorem tsub_tcode (mode : Nat) (t : Term Arith) (d : Nat) :
    ∀ s : Term Arith, tsub (pair mode (pair (tcode t) d)) (tcode s) =
      tcode (s.subst (liftN d (sigma mode t))) := by
  intro s
  induction s using Term.arith_induction with
  | hv n => simp [tsub, covRec_unfold, cvN, cvP, cvRec, tsubStep, Term.subst, tvar_spec]
  | hz => simp [tsub, covRec_unfold, cvN, cvP, cvRec, tsubStep]
  | hs t ih =>
      simp only [tsub, covRec_unfold, cvN, cvP, cvRec, tsubStep, tcode_succ, fst_pair, snd_pair, succ_subst]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false]
      rw [histGet_covHist _ _ _ _ (lt_pair_of_pos (by omega))]; exact congrArg _ ih
  | ha t s iht ihs =>
      simp only [tsub, covRec_unfold, cvN, cvP, cvRec, tsubStep, tcode_add, fst_pair, snd_pair, add_subst]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or]
      rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
        histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
      exact pair_congr3 (iht) (ihs)
  | hm t s iht ihs =>
      simp only [tsub, covRec_unfold, cvN, cvP, cvRec, tsubStep, tcode_mul, fst_pair, snd_pair, mul_subst]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true]
      rw [histGet_covHist _ _ _ _ (fst_lt_tagged (by omega)),
        histGet_covHist _ _ _ _ (snd_lt_tagged (by omega))]
      exact pair_congr3 (iht) (ihs)

/-- `tvar` is computable. -/
theorem Comp.tvar {f g h k : Nat → Nat} (hf : Comp f) (hg : Comp g) (hh : Comp h) (hk : Comp k) :
    Comp fun n => FO.tvar (f n) (g n) (h n) (k n) := by
  unfold FO.tvar
  refine Comp.cond (CompB.lt hk hh) (Comp.pair (Comp.const 0) hk) (Comp.cond (CompB.eq hf (Comp.const 0))
    (Comp.cond (CompB.eq hk hh) (Comp.trename hh hg) (Comp.pair (Comp.const 0) (Comp.sub hk (Comp.const 1))))
    (Comp.cond (CompB.eq hf (Comp.const 1)) (Comp.pair (Comp.const 0) (Comp.succ hk))
      (Comp.cond (CompB.eq hk hh) (Comp.pair (Comp.const 2) (Comp.pair (Comp.const 0) hh))
        (Comp.pair (Comp.const 0) hk))))

/-- `tsub` is computable. -/
theorem Comp.tsub {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : Comp fun n => FO.tsub (f n) (g n) := by
  have hs : Comp tsubStep := by
    unfold tsubStep
    refine Comp.cond (CompB.eq (Comp.fst (Comp.fst (Comp.snd Comp.id))) (Comp.const 0))
      (Comp.tvar (Comp.fst (Comp.fst Comp.id)) (Comp.fst (Comp.snd (Comp.fst Comp.id)))
        (Comp.snd (Comp.snd (Comp.fst Comp.id))) (Comp.snd (Comp.fst (Comp.snd Comp.id)))) ?_
    comp_tac
  exact Comp.congr (Comp.comp (Comp.covRec hs) (Comp.pair hf hg)) fun n => by simp [FO.tsub]

/-- One step of formula substitution; the parameter is `⟨mode, t⟩` and the index is
`⟨φ, d⟩`. -/
def fsubStep (q : Nat) : Nat :=
  bif fst (fst (cvN q)) == 1 then
    pair 1 (pair (tsub (pair (fst (cvP q)) (pair (snd (cvP q)) (snd (cvN q)))) (fst (snd (fst (cvN q)))))
      (tsub (pair (fst (cvP q)) (pair (snd (cvP q)) (snd (cvN q)))) (snd (snd (fst (cvN q))))))
  else bif fst (fst (cvN q)) == 2 || fst (fst (cvN q)) == 3 || fst (fst (cvN q)) == 4 then
    pair (fst (fst (cvN q))) (pair (cvRec q (pair (fst (snd (fst (cvN q)))) (snd (cvN q))))
      (cvRec q (pair (snd (snd (fst (cvN q)))) (snd (cvN q)))))
  else bif fst (fst (cvN q)) == 5 || fst (fst (cvN q)) == 6 then
    pair (fst (fst (cvN q))) (cvRec q (pair (snd (fst (cvN q))) (snd (cvN q) + 1)))
  else fst (cvN q)

/-- Formula substitution on codes: `fsub ⟨mode, ⌜t⌝⟩ ⟨⌜φ⌝, d⟩ = ⌜φ[liftN d (sigma mode t)]⌝`. -/
def fsub (p q : Nat) : Nat := covRec fsubStep p q

/-- **Correctness of substitution on Gödel numbers.** -/
theorem fsub_fcode (mode : Nat) (t : Term Arith) :
    ∀ (φ : Formula Arith) (d : Nat), fsub (pair mode (tcode t)) (pair (fcode φ) d) =
      fcode (φ.subst (liftN d (sigma mode t))) := by
  intro φ
  induction φ using Formula.arith_induction with
  | hb => intro d; simp [fsub, covRec_unfold, cvN, cvP, cvRec, fsubStep, fcode, Formula.subst]
  | he t s =>
      intro d
      simp [fsub, covRec_unfold, cvN, cvP, cvRec, fsubStep, fcode, Formula.subst, tsub_tcode]
  | hi φ ψ ih₁ ih₂ =>
      intro d
      simp only [fsub, covRec_unfold, cvN, cvP, cvRec, fsubStep, fcode, Formula.subst, fst_pair, snd_pair]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true]
      rw [histGet_covHist _ _ _ _ (pair_lt_pair_left (fst_lt_tagged (by omega))),
        histGet_covHist _ _ _ _ (pair_lt_pair_left (snd_lt_tagged (by omega)))]
      exact pair_congr3 (ih₁ d) (ih₂ d)
  | hc φ ψ ih₁ ih₂ =>
      intro d
      simp only [fsub, covRec_unfold, cvN, cvP, cvRec, fsubStep, fcode, Formula.subst, fst_pair, snd_pair]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true]
      rw [histGet_covHist _ _ _ _ (pair_lt_pair_left (fst_lt_tagged (by omega))),
        histGet_covHist _ _ _ _ (pair_lt_pair_left (snd_lt_tagged (by omega)))]
      exact pair_congr3 (ih₁ d) (ih₂ d)
  | hd φ ψ ih₁ ih₂ =>
      intro d
      simp only [fsub, covRec_unfold, cvN, cvP, cvRec, fsubStep, fcode, Formula.subst, fst_pair, snd_pair]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true]
      rw [histGet_covHist _ _ _ _ (pair_lt_pair_left (fst_lt_tagged (by omega))),
        histGet_covHist _ _ _ _ (pair_lt_pair_left (snd_lt_tagged (by omega)))]
      exact pair_congr3 (ih₁ d) (ih₂ d)
  | ha φ ih =>
      intro d
      simp only [fsub, covRec_unfold, cvN, cvP, cvRec, fsubStep, fcode, Formula.subst, fst_pair, snd_pair]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true]
      rw [histGet_covHist _ _ _ _ (pair_lt_pair_succ (lt_pair_of_pos (by omega)))]
      exact congrArg (pair 5) (ih (d + 1))
  | hx φ ih =>
      intro d
      simp only [fsub, covRec_unfold, cvN, cvP, cvRec, fsubStep, fcode, Formula.subst, fst_pair, snd_pair]
      simp only [Nat.reduceBEq, Bool.cond_false, Bool.cond_true, Bool.or_false, Bool.false_or, Bool.or_true]
      rw [histGet_covHist _ _ _ _ (pair_lt_pair_succ (lt_pair_of_pos (by omega)))]
      exact congrArg (pair 6) (ih (d + 1))

/-- `fsub` is computable. -/
theorem Comp.fsub {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) : Comp fun n => FO.fsub (f n) (g n) := by
  have hs : Comp fsubStep := by
    unfold fsubStep
    refine Comp.cond ?_ (Comp.pair (Comp.const 1) (Comp.pair (Comp.tsub ?_ ?_) (Comp.tsub ?_ ?_))) ?_ <;>
      comp_tac
  exact Comp.congr (Comp.comp (Comp.covRec hs) (Comp.pair hf hg)) fun n => by simp [FO.fsub]

/-! ## The three substitutions on codes -/

/-- Shifting on codes. -/
def shiftC (φ : Nat) : Nat := fsub (pair 1 0) (pair φ 0)

/-- Instantiation on codes. -/
def instC (φ t : Nat) : Nat := fsub (pair 0 t) (pair φ 0)

/-- The induction substitution `x ↦ Sx` on codes. -/
def succSubC (φ : Nat) : Nat := fsub (pair 2 0) (pair φ 0)

/-- Correctness of `shiftC`. -/
theorem shiftC_fcode (φ : Formula Arith) : shiftC (fcode φ) = fcode φ.shift := by
  have := fsub_fcode 1 (v 0) φ 0
  simpa [shiftC, liftN, sigma, Formula.shift] using this

/-- Correctness of `instC`. -/
theorem instC_fcode (φ : Formula Arith) (t : Term Arith) :
    instC (fcode φ) (tcode t) = fcode (φ.inst t) := by
  have := fsub_fcode 0 t φ 0
  simpa [instC, liftN, sigma, Formula.inst] using this

/-- Correctness of `succSubC`. -/
theorem succSubC_fcode (φ : Formula Arith) : succSubC (fcode φ) = fcode (φ.subst succSubst) := by
  have := fsub_fcode 2 (v 0) φ 0
  simpa [succSubC, liftN, sigma] using this

/-- Iterated shifting on codes. -/
def shiftNC (k φ : Nat) : Nat := natRec (fun φ => φ) (fun q => shiftC (snd (snd q))) φ k

/-- Iterated shifting of formulas. -/
def shiftN : Nat → Formula Arith → Formula Arith
  | 0, φ => φ
  | k + 1, φ => (shiftN k φ).shift

/-- Correctness of `shiftNC`. -/
theorem shiftNC_fcode (φ : Formula Arith) : ∀ k, shiftNC k (fcode φ) = fcode (shiftN k φ)
  | 0 => rfl
  | k + 1 => by
      simp only [shiftNC, natRec, snd_pair] at *
      rw [show natRec (fun φ => φ) (fun q => shiftC (snd (snd q))) (fcode φ) k = fcode (shiftN k φ)
        from shiftNC_fcode φ k]
      exact shiftC_fcode _

/-- The substitutions on codes are computable. -/
theorem Comp.shiftC {f : Nat → Nat} (hf : Comp f) : Comp fun n => FO.shiftC (f n) :=
  Comp.fsub (Comp.const _) (Comp.pair hf (Comp.const 0))

/-- Instantiation on codes is computable. -/
theorem Comp.instC {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    Comp fun n => FO.instC (f n) (g n) :=
  Comp.fsub (Comp.pair (Comp.const 0) hg) (Comp.pair hf (Comp.const 0))

/-- The induction substitution on codes is computable. -/
theorem Comp.succSubC {f : Nat → Nat} (hf : Comp f) : Comp fun n => FO.succSubC (f n) :=
  Comp.fsub (Comp.const _) (Comp.pair hf (Comp.const 0))

/-- Iterated shifting on codes is computable. -/
theorem Comp.shiftNC {f g : Nat → Nat} (hf : Comp f) (hg : Comp g) :
    Comp fun n => FO.shiftNC (f n) (g n) := by
  have := Comp.natRec hg (Comp.shiftC (Comp.snd (Comp.snd Comp.id))) hf
  refine Comp.congr this fun n => ?_
  unfold FO.shiftNC
  generalize f n = k
  induction k with
  | zero => rfl
  | succ k ih => simp only [natRec, snd_pair] at ih ⊢; rw [ih]

end Foundations.Logic.FO
