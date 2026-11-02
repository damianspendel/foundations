import Foundations.Logic.GodelIID3Der

/-!
# Formalised arithmetic of numerals

The first part of formalised Σ-completeness, the analogue inside a model `N` of PA of the
fact that `Q` proves every true numerical equation: for **all** elements `u, w` of `N`,

* `der_add`: `PA ⊢ ū + w̄ = (u+w)‾` is `provDP`-derivable,
* `der_mul`: `PA ⊢ ū · w̄ = (u·w)‾`,
* `der_neq`: `PA ⊢ ¬ ū = w̄` when `u ≠ w`,
* `der_le`, `der_nle`: `PA ⊢ ∃z (z + ū = w̄)` when `u ≤ w`, its negation otherwise,
* `der_eval`: for every term `t`, `PA ⊢ t(ē) = (t(e))‾`.

The proofs are *internal inductions*: the statements to be proved are definable in `N`
(`der_dfn`), and each inductive step appends a modus ponens to an instance, at the
numerals of non-standard numbers, of a fixed theorem of PA such as `x + y = z → x + Sy = Sz`.
This is the formal counterpart of the textbook argument, run inside every model of PA.

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

/-- The formula `v₀ + v₁ = v₂`. -/
def eqAdd : Formula Arith := eq (add (v 0) (v 1)) (v 2)
/-- The formula `v₀ · v₁ = v₂`. -/
def eqMul : Formula Arith := eq (mul (v 0) (v 1)) (v 2)
/-- The formula `¬ v₀ = v₁`. -/
def neqF : Formula Arith := neg (eq (v 0) (v 1))
/-- Shifting the variables of a term up by `k`. -/
def shiftT (k : Nat) (t : Term Arith) : Term Arith := t.subst fun m => Term.var (m + k)
/-- The formula `t = v₀`, the variables of `t` shifted up by one. -/
def eqT (t : Term Arith) : Formula Arith := eq (shiftT 1 t) (v 0)

/-- `Env.cons` at `0`. -/
@[simp] theorem cons_0 {α : Type} (x : α) (e : Nat → α) : Env.cons x e 0 = x := rfl
/-- `Env.cons` at `1`. -/
@[simp] theorem cons_1 {α : Type} (x : α) (e : Nat → α) : Env.cons x e 1 = e 0 := rfl
/-- `Env.cons` at `2`. -/
@[simp] theorem cons_2 {α : Type} (x : α) (e : Nat → α) : Env.cons x e 2 = e 1 := rfl
/-- `Env.cons` at `3`. -/
@[simp] theorem cons_3 {α : Type} (x : α) (e : Nat → α) : Env.cons x e 3 = e 2 := rfl
/-- `Env.cons` at a successor. -/
@[simp] theorem cons_succ {α : Type} (x : α) (e : Nat → α) (n : Nat) :
    Env.cons x e (n + 1) = e n := rfl

/-- Evaluating a shifted term. -/
theorem eval_shiftT {M : Structure Arith} (k : Nat) (t : Term Arith) (e : Nat → M.Dom) :
    (shiftT k t).eval M e = t.eval M (fun m => e (m + k)) :=
  Term.eval_subst e _ t

end GodelII

namespace PAModel

variable {N : PAModel}

/-- The code of a shifted term. -/
theorem tcM_shiftT (k : Nat) (t : Term Arith) (v : Nat → N.Dom) :
    tcM (shiftT k t) 0 v = tcM t 0 (fun m => v (m + k)) :=
  tcM_subst (σ := fun m => Term.var (m + k)) (fun _ => tcM_var0 _ _) 0 t

/-- The code of the numeral of `a + 1`. -/
theorem numN_succ' (a : N.Dom) : pairN 2 (NumN a) = NumN (a + 1) := (numN_succ a).symm

/-- **Instances through a substitution**: if `χ(σ)` is valid in all models of PA, and the
terms `σ m` have, under `v`, the codes of the numerals of `v' m`, then `χ(v̄')` is
derivable. -/
theorem der_of_valid {χ : Formula Arith} (σ : Nat → Term Arith) {v v' : Nat → N.Dom}
    (hvalid : ∀ (M : PAModel) (e : Nat → M.Dom), Sat M.M (fun n => (σ n).eval M.M e) χ)
    (hσ : ∀ m, tcM (σ m) 0 v = NumN (v' m)) : Der χ v' :=
  (der_subst_iff hσ).1 (der_inst (pa_of_valid fun M e => (sat_subst χ e σ).2 (hvalid M e)) v)

/-- Three-element assignment. -/
abbrev env3 (a b c : N.Dom) : Nat → N.Dom := Env.cons a (Env.cons b (Env.cons c fun _ => 0))
/-- Two-element assignment. -/
abbrev env2 (a b : N.Dom) : Nat → N.Dom := Env.cons a (Env.cons b fun _ => 0)

/-- `tcM` of `0`, as a numeral code. -/
theorem tcM_zero_num (v : Nat → N.Dom) : tcM zero 0 v = NumN 0 := numN_zero.symm

/-! ## Addition and multiplication -/

/-- **Formalised addition table**: `ū + w̄ = (u + w)‾` is derivable, for all `u, w`. -/
theorem der_add (u w : N.Dom) : Der eqAdd (env3 u w (u + w)) := by
  have hP : N.Dfn fun e => (fun (w : N.Dom) (e : Nat → N.Dom) =>
      Der eqAdd (env3 (e 0) w (e 0 + w))) (e 0) (fun n => e (n + 1)) := by
    refine (der_dfn_at eqAdd (τ := fun n e => match n with
      | 0 => e 1 | 1 => e 0 | 2 => e 1 + e 0 | _ => 0) fun n => ?_).congr' fun e => ?_
    · match n with
      | 0 => exact DfnT.var 1
      | 1 => exact DfnT.var 0
      | 2 => exact DfnT.add (DfnT.var 1) (DfnT.var 0)
      | _ + 3 => exact DfnT.ofNat 0
    · have : (fun n => match n with | 0 => e 1 | 1 => e 0 | 2 => e 1 + e 0 | _ => (0 : N.Dom)) =
          env3 (e 1) (e 0) (e 1 + e 0) := by
        funext n; match n with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | _ + 3 => rfl
      simp only [this]
  refine induction (P := fun w e => Der eqAdd (env3 (e 0) w (e 0 + w))) hP
    (Env.cons u fun _ => 0) ?_ ?_ w
  · -- `x + 0 = x`
    show Der eqAdd (env3 u 0 (u + 0))
    rw [add_zero']
    exact der_of_valid (χ := eqAdd) (v := Env.cons u fun _ => 0) (v' := env3 u 0 u)
      (Env.cons (v 0) (Env.cons zero (Env.cons (v 0) fun _ => zero)))
      (fun M e => by simp [eqAdd, Sat, add_zero'])
      (fun m => by rcases m with _ | _ | _ | _ | m <;> simp [numN_zero])
  · -- `x + y = z → x + Sy = Sz`
    intro x ih
    show Der eqAdd (env3 u (x + 1) (u + (x + 1)))
    let σ : Nat → Term Arith := Env.cons (v 0) (Env.cons (succ (v 1)) (Env.cons (succ (v 2))
      fun m => v (m + 3)))
    have hL := der_inst (N := N) (χ := imp eqAdd (eqAdd.subst σ))
      (pa_of_valid fun M e => by
        simp [eqAdd, Sat, sat_subst, σ]; intro h; rw [add_succ', h])
      (env3 u x (u + x))
    have := (der_subst_iff (χ := eqAdd) (σ := σ) (v' := env3 u (x + 1) (u + x + 1))
      (fun m => by rcases m with _ | _ | _ | _ | m <;> simp [numN_zero, σ, numN_succ])).1
      (der_mp hL ih)
    rwa [← add_succ'] at this

/-- **Formalised multiplication table**: `ū · w̄ = (u · w)‾` is derivable, for all `u, w`. -/
theorem der_mul (u w : N.Dom) : Der eqMul (env3 u w (u * w)) := by
  have hP : N.Dfn fun e => (fun (w : N.Dom) (e : Nat → N.Dom) =>
      Der eqMul (env3 (e 0) w (e 0 * w))) (e 0) (fun n => e (n + 1)) := by
    refine (der_dfn_at eqMul (τ := fun n e => match n with
      | 0 => e 1 | 1 => e 0 | 2 => e 1 * e 0 | _ => 0) fun n => ?_).congr' fun e => ?_
    · match n with
      | 0 => exact DfnT.var 1
      | 1 => exact DfnT.var 0
      | 2 => exact DfnT.mul (DfnT.var 1) (DfnT.var 0)
      | _ + 3 => exact DfnT.ofNat 0
    · have : (fun n => match n with | 0 => e 1 | 1 => e 0 | 2 => e 1 * e 0 | _ => (0 : N.Dom)) =
          env3 (e 1) (e 0) (e 1 * e 0) := by
        funext n; match n with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | _ + 3 => rfl
      simp only [this]
  refine induction (P := fun w e => Der eqMul (env3 (e 0) w (e 0 * w))) hP
    (Env.cons u fun _ => 0) ?_ ?_ w
  · show Der eqMul (env3 u 0 (u * 0))
    rw [mul_zero']
    exact der_of_valid (χ := eqMul) (v := Env.cons u fun _ => 0) (v' := env3 u 0 0)
      (Env.cons (v 0) fun _ => zero)
      (fun M e => by simp [eqMul, Sat, mul_zero'])
      (fun m => by rcases m with _ | _ | _ | _ | m <;> simp [numN_zero])
  · intro x ih
    show Der eqMul (env3 u (x + 1) (u * (x + 1)))
    let E : Nat → N.Dom := Env.cons u (Env.cons x (Env.cons (u * x) (Env.cons (u * x + u)
      fun _ => 0)))
    let τ : Nat → Term Arith := Env.cons (v 2) (Env.cons (v 0) (Env.cons (v 3) fun _ => zero))
    let σ : Nat → Term Arith := Env.cons (v 0) (Env.cons (succ (v 1)) (Env.cons (v 3)
      fun _ => zero))
    have hL := der_inst (N := N) (χ := imp eqMul (imp (eqAdd.subst τ) (eqMul.subst σ)))
      (pa_of_valid fun M e => by
        simp [eqAdd, eqMul, Sat, sat_subst, τ, σ]
        intro h₁ h₂; rw [mul_succ', h₁, h₂]) E
    have i₁ : Der eqMul E := der_congr (by simp [codeM, eqMul, E]) ih
    have i₂ := (der_subst_iff (χ := eqAdd) (σ := τ) (v := E) (v' := env3 (u * x) u (u * x + u))
      (fun m => by rcases m with _ | _ | _ | _ | m <;> simp [numN_zero, τ, E])).2
        (der_add (u * x) u)
    have := (der_subst_iff (χ := eqMul) (σ := σ) (v' := env3 u (x + 1) (u * x + u))
      (fun m => by rcases m with _ | _ | _ | _ | m <;> simp [numN_zero, σ, E, numN_succ])).1 (der_mp (der_mp hL i₁) i₂)
    rwa [← mul_succ'] at this

/-! ## Inequations and the order -/

/-- **Formalised inequations**: `¬ ā = b̄` is derivable whenever `a ≠ b`. -/
theorem der_neq : ∀ a b : N.Dom, a ≠ b → Der neqF (env2 a b) := by
  have hP : N.Dfn fun e => (fun (a : N.Dom) (_ : Nat → N.Dom) =>
      ∀ b, a ≠ b → Der neqF (env2 a b)) (e 0) (fun n => e (n + 1)) := by
    refine Dfn.all (Dfn.imp (Dfn.not (Dfn.eq (DfnT.var 1) (DfnT.var 0)))
      ((der_dfn_at neqF (τ := fun n e => match n with | 0 => e 1 | 1 => e 0 | _ => 0)
        fun n => ?_).congr' fun e => ?_))
    · match n with
      | 0 => exact DfnT.var 1
      | 1 => exact DfnT.var 0
      | _ + 2 => exact DfnT.ofNat 0
    · have : (fun n => match n with | 0 => e 1 | 1 => e 0 | _ => (0 : N.Dom)) = env2 (e 1) (e 0) := by
        funext n; match n with
        | 0 => rfl
        | 1 => rfl
        | _ + 2 => rfl
      simp only [this]
  intro a
  refine induction (P := fun a _ => ∀ b, a ≠ b → Der neqF (env2 a b)) hP (fun _ => 0) ?_ ?_ a
  · intro b hb
    obtain ⟨b', rfl⟩ := (zero_or_succ b).resolve_left (Ne.symm hb)
    exact der_of_valid (χ := neqF) (v := Env.cons b' fun _ => 0)
      (Env.cons zero (Env.cons (succ (v 0)) fun _ => zero))
      (fun M e => by simp [neqF, neg, Sat]; exact fun h => succ_ne_zero' _ h.symm)
      (fun m => by rcases m with _ | _ | _ | m <;> simp [numN_zero, numN_succ])
  · intro x ih b hb
    rcases zero_or_succ b with rfl | ⟨b', rfl⟩
    · exact der_of_valid (χ := neqF) (v := Env.cons x fun _ => 0)
        (Env.cons (succ (v 0)) (Env.cons zero fun _ => zero))
        (fun M e => by simp [neqF, neg, Sat]; exact fun h => succ_ne_zero' _ h)
        (fun m => by rcases m with _ | _ | _ | m <;> simp [numN_zero, numN_succ])
    · have hne : x ≠ b' := fun h => hb (by rw [h])
      let σ : Nat → Term Arith := Env.cons (succ (v 0)) (Env.cons (succ (v 1)) fun _ => zero)
      have hL := der_inst (N := N) (χ := imp neqF (neqF.subst σ))
        (pa_of_valid fun M e => by
          simp [neqF, neg, Sat, sat_subst, σ]; exact fun h h' => h (succ_inj' h')) (env2 x b')
      exact (der_subst_iff (χ := neqF) (σ := σ) (v' := env2 (x + 1) (b' + 1))
        (fun m => by rcases m with _ | _ | _ | m <;> simp [numN_zero, σ, numN_succ])).1
        (der_mp hL (ih b' hne))

/-- **Formalised order, positive case**: `∃z (z + ā = b̄)` is derivable when `a ≤ b`. -/
theorem der_le {a b : N.Dom} (h : a ≤ b) : Der leF (env2 a b) := by
  obtain ⟨z, rfl⟩ := h
  let τ : Nat → Term Arith := fun m => v (m + 1)
  have hL := der_inst (N := N) (χ := imp eqAdd (leF.subst τ))
    (pa_of_valid fun M e => by
      simp only [Formula.Sat, sat_subst]
      intro h
      rw [sat_leF]
      exact ⟨e 0, by simpa [eqAdd, Sat, τ] using h⟩) (env3 z a (z + a))
  have := der_mp hL (der_add z a)
  have := (der_subst_iff (χ := leF) (σ := τ) (v' := env2 a (z + a))
    (fun m => by rcases m with _ | _ | _ | m <;> simp [numN_zero, τ])).1 this
  rwa [add_comm' z a] at this

/-- **Formalised order, negative case**: `¬∃z (z + ā = b̄)` is derivable when `b < a`. -/
theorem der_nle : ∀ b a : N.Dom, b < a → Der (neg leF) (env2 a b) := by
  have hP : N.Dfn fun e => (fun (b : N.Dom) (_ : Nat → N.Dom) =>
      ∀ a, b < a → Der (neg leF) (env2 a b)) (e 0) (fun n => e (n + 1)) := by
    refine Dfn.all (Dfn.imp ?_ ((der_dfn_at (neg leF)
      (τ := fun n e => match n with | 0 => e 0 | 1 => e 1 | _ => 0) fun n => ?_).congr' fun e => ?_))
    · simp only [lt_def]; dfn
    · match n with
      | 0 => exact DfnT.var 0
      | 1 => exact DfnT.var 1
      | _ + 2 => exact DfnT.ofNat 0
    · have : (fun n => match n with | 0 => e 0 | 1 => e 1 | _ => (0 : N.Dom)) = env2 (e 0) (e 1) := by
        funext n; match n with
        | 0 => rfl
        | 1 => rfl
        | _ + 2 => rfl
      simp only [this]
  intro b
  refine induction (P := fun b _ => ∀ a, b < a → Der (neg leF) (env2 a b)) hP (fun _ => 0) ?_ ?_ b
  · intro a ha
    obtain ⟨a', rfl⟩ := (zero_or_succ a).resolve_left (fun h => by rw [h] at ha; exact lt_irrefl' 0 ha)
    exact der_of_valid (χ := neg leF) (v := Env.cons a' fun _ => 0)
      (Env.cons (succ (v 0)) (Env.cons zero fun _ => zero))
      (fun M e => by
        simp only [neg, Formula.Sat, sat_leF]
        rintro ⟨d, hd⟩
        simp [Env.cons] at hd
        exact succ_ne_zero' _ (by rw [← hd, add_succ']))
      (fun m => by rcases m with _ | _ | _ | m <;> simp [numN_zero, numN_succ])
  · intro x ih a ha
    obtain ⟨a', rfl⟩ := (zero_or_succ a).resolve_left (fun h => by
      rw [h] at ha; exact not_lt_zero' _ ha)
    have ha' : x < a' := by obtain ⟨z, hz⟩ := ha; exact ⟨z, succ_inj' (by rw [← hz]; grind)⟩
    let σ : Nat → Term Arith := Env.cons (succ (v 0)) (Env.cons (succ (v 1)) fun _ => zero)
    have hL := der_inst (N := N) (χ := imp (neg leF) ((neg leF).subst σ))
      (pa_of_valid fun M e => by
        simp only [neg, Formula.Sat, sat_subst, sat_leF]
        rintro h ⟨d, hd⟩
        apply h
        simp [σ] at hd ⊢
        exact ⟨d, succ_inj' (by rw [← hd, add_succ']; rfl)⟩) (env2 a' x)
    exact (der_subst_iff (χ := neg leF) (σ := σ) (v' := env2 (a' + 1) (x + 1))
      (fun m => by rcases m with _ | _ | _ | m <;> simp [numN_zero, σ, numN_succ])).1
      (der_mp hL (ih a' ha'))

/-! ## Evaluation of terms -/

/-- Reflexivity instances: `ā = ā`. -/
theorem der_refl (a : N.Dom) : Der (eq (v 0) (v 0)) (Env.cons a fun _ => 0) :=
  der_inst (pa_of_valid fun _ _ => by simp [Formula.Sat]) _

/-- The successor case of `der_eval`. -/
theorem der_eval_succ (t : Term Arith) (ht : ∀ e : Nat → N.Dom, Der (eqT t) (Env.cons (t.eval N.M e) e))
    (e : Nat → N.Dom) : Der (eqT (succ t)) (Env.cons ((succ t).eval N.M e) e) := by
  have hL := der_inst (N := N) (χ := imp (eqT t) (eq (shiftT 1 (succ t)) (succ (v 0))))
    (pa_of_valid fun M e => by
      simp only [eqT, Formula.Sat, eval_shiftT, eval_succ_M, eval_var_M]
      intro h; rw [h]) (Env.cons (t.eval N.M e) e)
  refine der_congr ?_ (der_mp hL (ht e))
  simp only [codeM, eqT, tcM_shiftT, tcM_succ, tcM_var0, cons_0, cons_succ, eval_succ_M, ms_eq,
    numN_succ]

/-- The sum case of `der_eval`. -/
theorem der_eval_add (t s : Term Arith)
    (ht : ∀ e : Nat → N.Dom, Der (eqT t) (Env.cons (t.eval N.M e) e))
    (hs : ∀ e : Nat → N.Dom, Der (eqT s) (Env.cons (s.eval N.M e) e)) (e : Nat → N.Dom) :
    Der (eqT (add t s)) (Env.cons ((add t s).eval N.M e) e) := by
  let a := t.eval N.M e
  let b := s.eval N.M e
  let E : Nat → N.Dom := Env.cons a (Env.cons b (Env.cons (a + b) e))
  have hL := der_inst (N := N) (χ := imp (eq (shiftT 3 t) (v 0)) (imp (eq (shiftT 3 s) (v 1))
      (imp eqAdd (eq (add (shiftT 3 t) (shiftT 3 s)) (v 2)))))
    (pa_of_valid fun M e => by
      simp only [eqAdd, Formula.Sat, eval_shiftT, eval_add_M, eval_var_M]
      intro h₁ h₂ h₃; rw [h₁, h₂, h₃]) E
  have p₁ : Der (eq (shiftT 3 t) (v 0)) E := der_congr (by simp [codeM, eqT, tcM_shiftT, E, a]) (ht e)
  have p₂ : Der (eq (shiftT 3 s) (v 1)) E := der_congr (by simp [codeM, eqT, tcM_shiftT, E, b]) (hs e)
  have p₃ : Der eqAdd E := der_congr (by simp [codeM, eqAdd, E]) (der_add a b)
  refine der_congr ?_ (der_mp (der_mp (der_mp hL p₁) p₂) p₃)
  simp [codeM, eqT, tcM_shiftT, E, a, b]

/-- The product case of `der_eval`. -/
theorem der_eval_mul (t s : Term Arith)
    (ht : ∀ e : Nat → N.Dom, Der (eqT t) (Env.cons (t.eval N.M e) e))
    (hs : ∀ e : Nat → N.Dom, Der (eqT s) (Env.cons (s.eval N.M e) e)) (e : Nat → N.Dom) :
    Der (eqT (mul t s)) (Env.cons ((mul t s).eval N.M e) e) := by
  let a := t.eval N.M e
  let b := s.eval N.M e
  let E : Nat → N.Dom := Env.cons a (Env.cons b (Env.cons (a * b) e))
  have hL := der_inst (N := N) (χ := imp (eq (shiftT 3 t) (v 0)) (imp (eq (shiftT 3 s) (v 1))
      (imp eqMul (eq (mul (shiftT 3 t) (shiftT 3 s)) (v 2)))))
    (pa_of_valid fun M e => by
      simp only [eqMul, Formula.Sat, eval_shiftT, eval_mul_M, eval_var_M]
      intro h₁ h₂ h₃; rw [h₁, h₂, h₃]) E
  have p₁ : Der (eq (shiftT 3 t) (v 0)) E := der_congr (by simp [codeM, eqT, tcM_shiftT, E, a]) (ht e)
  have p₂ : Der (eq (shiftT 3 s) (v 1)) E := der_congr (by simp [codeM, eqT, tcM_shiftT, E, b]) (hs e)
  have p₃ : Der eqMul E := der_congr (by simp [codeM, eqMul, E]) (der_mul a b)
  refine der_congr ?_ (der_mp (der_mp (der_mp hL p₁) p₂) p₃)
  simp [codeM, eqT, tcM_shiftT, E, a, b]

/-- Binary argument vectors. -/
theorem args₂_eta (ts : Fin 2 → Term Arith) : args₂ (ts 0) (ts 1) = ts := by
  funext i; match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- **Formalised evaluation of terms**: for every term `t` and every assignment `e`,
`t(ē) = (t(e))‾` is derivable. -/
theorem der_eval : ∀ (t : Term Arith) (e : Nat → N.Dom), Der (eqT t) (Env.cons (t.eval N.M e) e)
  | .var m, e => der_congr (by simp [codeM, eqT, tcM_shiftT]) (der_refl (e m))
  | .func ArithFunc.zero ts, e => by
    have hts : ts = Fin.elim0 := funext fun i => i.elim0
    subst hts
    show Der (eqT zero) (Env.cons ((zero : Term Arith).eval N.M e) e)
    rw [eval_zero_M, mz_eq]
    exact der_congr (by simp [codeM, eqT, tcM_shiftT, numN_zero]) (der_refl 0)
  | .func ArithFunc.succ ts, e => by
    have h := der_eval_succ (ts 0) (der_eval (ts 0)) e
    have hts : (fun _ => ts 0) = ts := funext fun i => by
      match i with
      | ⟨0, _⟩ => rfl
    rw [succ, hts] at h; exact h
  | .func ArithFunc.add ts, e => by
    have h : Der (eqT (.func ArithFunc.add (args₂ (ts 0) (ts 1))))
        (Env.cons ((Term.func ArithFunc.add (args₂ (ts 0) (ts 1))).eval N.M e) e) :=
      der_eval_add (ts 0) (ts 1) (der_eval (ts 0)) (der_eval (ts 1)) e
    rwa [args₂_eta] at h
  | .func ArithFunc.mul ts, e => by
    have h : Der (eqT (.func ArithFunc.mul (args₂ (ts 0) (ts 1))))
        (Env.cons ((Term.func ArithFunc.mul (args₂ (ts 0) (ts 1))).eval N.M e) e) :=
      der_eval_mul (ts 0) (ts 1) (der_eval (ts 0)) (der_eval (ts 1)) e
    rwa [args₂_eta] at h

end PAModel

end Foundations.Logic.FO
