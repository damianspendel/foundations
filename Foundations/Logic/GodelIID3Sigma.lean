import Foundations.Logic.GodelIID3Bounded

/-!
# Formalised Σ-completeness

**Theorem (formalised Σ-completeness, inside every model of PA).** Let `N` be a model of PA,
`φ` a Σ-formula and `e` an assignment of elements of `N` (standard or not). If `φ` holds in
`N` under `e`, then the judgement `PA ⊢ φ(ē)` — with the numerals of the values substituted
for the free variables — is `provDP`-derivable in `N` (`sig_complete`).

This is the internal counterpart of the Σ₁-completeness of `Q` proved in `Representability`
for the standard model, and the heart of Löb's condition (D3). The proof is by induction on
the formula, *outside* `N`, with the induction hypothesis quantified over all assignments:

* bounded formulas `D0` are handled two-sidedly (`d0_complete`): what holds is derivable,
  what fails is refutable, which is what the propositional connectives need;
* atomic formulas reduce to the formalised arithmetic of numerals (`GodelIID3Arith`);
* bounded universal quantifiers are internal inductions on the bound (`der_ball`);
* existential quantifiers and the bounded existential quantifier are instances of
  `ψ(x) → ∃y ψ(y)` at the numeral of a witness.

Every logical step is an instance (at numerals of elements of `N`) of a fixed theorem of PA,
followed by modus ponens; these theorems are proved semantically, by the completeness
theorem.

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

/-- Every theorem of PA is derivable at every assignment. -/
theorem der_valid {φ : Formula Arith} (h : ∀ (M : PAModel) (e : Nat → M.Dom), Sat M.M e φ)
    (e : Nat → N.Dom) : Der φ e :=
  der_inst (pa_of_valid h) e

/-- Splitting an assignment into its first value and the rest. -/
theorem exists_cons {M : PAModel} (e : Nat → M.Dom) : ∃ x e', e = Env.cons x e' :=
  ⟨e 0, fun n => e (n + 1), funext fun n => by cases n <;> rfl⟩

/-- `boundF T` at `x` is derivable when `x ≤ T`. -/
theorem der_boundF {T : Term Arith} {x : N.Dom} {e : Nat → N.Dom} (h : x ≤ T.eval N.M e) :
    Der (boundF T) (Env.cons x e) :=
  der_atom_le (t := v 0) (s := T.rename Nat.succ) (by
    simp only [eval_var_M, cons_0, eval_rename_succ_cons]; exact h)

/-- `boundSF T` at `x` is derivable when `x < T`. -/
theorem der_boundSF {T : Term Arith} {x : N.Dom} {e : Nat → N.Dom} (h : x < T.eval N.M e) :
    Der (boundSF T) (Env.cons x e) :=
  der_atom_le (t := succ (v 0)) (s := T.rename Nat.succ) (by
    simp only [eval_succ_M, ms_eq, eval_var_M, cons_0, eval_rename_succ_cons]; exact h)

/-- Shifted formulas under a pushed value. -/
theorem sat_shiftF_cons {M : PAModel} (φ : Formula Arith) (x : M.Dom) (e : Nat → M.Dom) :
    Sat M.M (Env.cons x e) (shiftF 1 φ) ↔ Sat M.M e φ := by
  rw [sat_shiftF]; exact Iff.rfl

/-- **Formalised completeness for bounded formulas**, two-sided. -/
theorem d0_complete {φ : Formula Arith} (h : D0 φ) : ∀ e : Nat → N.Dom,
    (Sat N.M e φ → Der φ e) ∧ (¬ Sat N.M e φ → Der (neg φ) e) := by
  induction h with
  | eq t s => exact fun e => ⟨fun hs => der_atom_eq hs, fun hs => der_atom_neq hs⟩
  | le t s => exact fun e => ⟨fun hs => der_atom_le ((sat_substL_leF t s e).1 hs),
      fun hs => der_atom_nle fun h' => hs ((sat_substL_leF t s e).2 h')⟩
  | bot => exact fun e => ⟨fun hs => hs.elim, fun _ => der_valid (φ := neg bot) (fun _ _ h => h) e⟩
  | @imp A B _ _ ihA ihB =>
    intro e
    constructor
    · intro hs
      by_cases ha : Sat N.M e A
      · exact der_mp (der_valid (φ := imp B (imp A B)) (fun _ _ hb _ => hb) e) ((ihB e).1 (hs ha))
      · exact der_mp (der_valid (φ := imp (neg A) (imp A B)) (fun _ _ hna ha => (hna ha).elim) e)
          ((ihA e).2 ha)
    · intro hs
      have ha : Sat N.M e A := Classical.byContradiction fun ha => hs fun h => (ha h).elim
      have hb : ¬ Sat N.M e B := fun hb => hs fun _ => hb
      exact der_mp (der_mp (der_valid (φ := imp A (imp (neg B) (neg (imp A B))))
        (fun _ _ ha hnb hab => hnb (hab ha)) e) ((ihA e).1 ha)) ((ihB e).2 hb)
  | @conj A B _ _ ihA ihB =>
    intro e
    constructor
    · intro ⟨ha, hb⟩
      exact der_mp (der_mp (der_valid (φ := imp A (imp B (conj A B))) (fun _ _ ha hb => ⟨ha, hb⟩) e)
        ((ihA e).1 ha)) ((ihB e).1 hb)
    · intro hs
      by_cases ha : Sat N.M e A
      · exact der_mp (der_valid (φ := imp (neg B) (neg (conj A B))) (fun _ _ hnb hab => hnb hab.2) e)
          ((ihB e).2 fun hb => hs ⟨ha, hb⟩)
      · exact der_mp (der_valid (φ := imp (neg A) (neg (conj A B))) (fun _ _ hna hab => hna hab.1) e)
          ((ihA e).2 ha)
  | @disj A B _ _ ihA ihB =>
    intro e
    constructor
    · rintro (ha | hb)
      · exact der_mp (der_valid (φ := imp A (disj A B)) (fun _ _ ha => Or.inl ha) e) ((ihA e).1 ha)
      · exact der_mp (der_valid (φ := imp B (disj A B)) (fun _ _ hb => Or.inr hb) e) ((ihB e).1 hb)
    · intro hs
      exact der_mp (der_mp (der_valid (φ := imp (neg A) (imp (neg B) (neg (disj A B))))
        (fun _ _ hna hnb hab => hab.elim hna hnb) e) ((ihA e).2 fun ha => hs (Or.inl ha)))
        ((ihB e).2 fun hb => hs (Or.inr hb))
  | @ball T φ _ ih =>
    intro e
    constructor
    · intro hs
      exact der_ball φ T e fun x hx => (ih (Env.cons x e)).1 ((sat_ball_bound N T φ e).1 hs x hx)
    · intro hs
      obtain ⟨x, hx, hnx⟩ : ∃ x, x ≤ T.eval N.M e ∧ ¬ Sat N.M (Env.cons x e) φ :=
        Classical.byContradiction fun hne => hs ((sat_ball_bound N T φ e).2 fun x hx =>
          Classical.byContradiction fun h => hne ⟨x, hx, h⟩)
      have hL := der_valid (N := N) (φ := imp (boundF T) (imp (neg φ)
          (shiftF 1 (neg (all (imp (boundF T) φ)))))) (fun M e => by
        obtain ⟨y, e', rfl⟩ := exists_cons e
        show Sat M.M _ (boundF T) → ¬ Sat M.M _ φ → Sat M.M _ (shiftF 1 _)
        rw [sat_shiftF_cons, sat_boundF]
        intro hb hnφ hall
        rw [sat_ball_bound] at hall
        refine hnφ (hall y ?_)
        obtain ⟨z, hz⟩ := hb
        exact ⟨z, by simp only [madd_eq] at hz; rw [← hz]; exact add_comm' _ _⟩) (Env.cons x e)
      exact der_shiftF_cons (der_mp (der_mp hL (der_boundF hx)) ((ih (Env.cons x e)).2 hnx))
  | @ballS T φ _ ih =>
    intro e
    constructor
    · intro hs
      exact der_ballS φ T e fun x hx => (ih (Env.cons x e)).1 ((sat_ballS_bound N T φ e).1 hs x hx)
    · intro hs
      obtain ⟨x, hx, hnx⟩ : ∃ x, x < T.eval N.M e ∧ ¬ Sat N.M (Env.cons x e) φ :=
        Classical.byContradiction fun hne => hs ((sat_ballS_bound N T φ e).2 fun x hx =>
          Classical.byContradiction fun h => hne ⟨x, hx, h⟩)
      have hL := der_valid (N := N) (φ := imp (boundSF T) (imp (neg φ)
          (shiftF 1 (neg (all (imp (boundSF T) φ)))))) (fun M e => by
        obtain ⟨y, e', rfl⟩ := exists_cons e
        show Sat M.M _ (boundSF T) → ¬ Sat M.M _ φ → Sat M.M _ (shiftF 1 _)
        rw [sat_shiftF_cons, sat_boundSF]
        intro hb hnφ hall
        rw [sat_ballS_bound] at hall
        refine hnφ (hall y ?_)
        obtain ⟨z, hz⟩ := hb
        exact ⟨z, by simp only [madd_eq, ms_eq] at hz; rw [← hz]; exact add_comm' _ _⟩)
        (Env.cons x e)
      exact der_shiftF_cons (der_mp (der_mp hL (der_boundSF hx)) ((ih (Env.cons x e)).2 hnx))
  | @bex T φ _ ih =>
    intro e
    constructor
    · rintro ⟨x, hb, hx⟩
      have hb' : x ≤ T.eval N.M e := by
        rw [sat_boundF] at hb
        obtain ⟨z, hz⟩ := hb
        exact ⟨z, by simp only [madd_eq] at hz; rw [← hz]; exact add_comm' _ _⟩
      have hL := der_valid (N := N) (φ := imp (boundF T) (imp φ
          (shiftF 1 (ex (conj (boundF T) φ))))) (fun M e => by
        obtain ⟨y, e', rfl⟩ := exists_cons e
        show Sat M.M _ (boundF T) → Sat M.M _ φ → Sat M.M _ (shiftF 1 _)
        rw [sat_shiftF_cons]
        intro hb hφ
        exact ⟨y, hb, hφ⟩) (Env.cons x e)
      exact der_shiftF_cons (der_mp (der_mp hL (der_boundF hb')) ((ih (Env.cons x e)).1 hx))
    · intro hs
      have hall : Der (all (imp (boundF T) (neg φ))) e := der_ball (neg φ) T e fun x hx =>
        (ih (Env.cons x e)).2 fun hφ => hs ⟨x, by
          rw [sat_boundF]
          obtain ⟨z, hz⟩ := hx
          exact ⟨z, by simp only [madd_eq]; rw [← hz]; exact add_comm' _ _⟩, hφ⟩
      have hL := der_valid (N := N) (φ := imp (all (imp (boundF T) (neg φ)))
          (neg (ex (conj (boundF T) φ)))) (fun M e hall ⟨y, hb, hφ⟩ => hall y hb hφ) e
      exact der_mp hL hall

/-- **Formalised Σ-completeness.** Inside every model of PA: every Σ-formula true under an
assignment is `provDP`-derivable at the numerals of that assignment. -/
theorem sig_complete {φ : Formula Arith} (h : SigP φ) : ∀ e : Nat → N.Dom,
    Sat N.M e φ → Der φ e := by
  induction h with
  | d0 h => exact fun e => (d0_complete h e).1
  | @conj A B _ _ ihA ihB =>
    exact fun e ⟨ha, hb⟩ => der_mp (der_mp (der_valid (φ := imp A (imp B (conj A B)))
      (fun _ _ ha hb => ⟨ha, hb⟩) e) (ihA e ha)) (ihB e hb)
  | @disj A B _ _ ihA ihB =>
    rintro e (ha | hb)
    · exact der_mp (der_valid (φ := imp A (disj A B)) (fun _ _ ha => Or.inl ha) e) (ihA e ha)
    · exact der_mp (der_valid (φ := imp B (disj A B)) (fun _ _ hb => Or.inr hb) e) (ihB e hb)
  | @ex φ _ ih =>
    rintro e ⟨x, hx⟩
    have hL := der_valid (N := N) (φ := imp φ (shiftF 1 (ex φ))) (fun M e => by
      obtain ⟨y, e', rfl⟩ := exists_cons e
      show Sat M.M _ φ → Sat M.M _ (shiftF 1 _)
      rw [sat_shiftF_cons]
      exact fun hφ => ⟨y, hφ⟩) (Env.cons x e)
    exact der_shiftF_cons (der_mp hL (ih (Env.cons x e) hx))
  | @ball T φ _ ih =>
    exact fun e hs => der_ball φ T e fun x hx => ih (Env.cons x e) ((sat_ball_bound N T φ e).1 hs x hx)
  | @ballS T φ _ ih =>
    exact fun e hs => der_ballS φ T e fun x hx =>
      ih (Env.cons x e) ((sat_ballS_bound N T φ e).1 hs x hx)

end PAModel

end Foundations.Logic.FO
