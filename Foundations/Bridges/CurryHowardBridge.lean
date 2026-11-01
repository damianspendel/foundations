import Foundations.Types.CurryHoward
import Foundations.Logic.NaturalDeduction

/-!
# Intuitionistic and classical logic: Glivenko's bridge

Two parts of this project formalised Gentzen's natural deduction for propositional
logic, from two different motives:

* **Part III (Logic)** studied *classical* logic: `Derives Γ φ` has the
  introduction and elimination rules plus *reductio ad absurdum*, and is sound and
  complete for truth tables.
* **Part V (Types)** studied *intuitionistic* logic through the Curry–Howard
  correspondence: `ND Γ A` has the same rules *without* reductio, and its
  derivations are exactly the typed λ-terms. There it was shown that excluded middle,
  Peirce's law and double-negation elimination are *not* intuitionistically provable.

The formulas of the two systems are separately defined inductive types (Part V's
are the simple types), but they have the same shape; we write down the evident
translation and its inverse. Then:

1. **Intuitionistic ⊆ classical.** Every intuitionistic derivation translates into a
   classical one (the rules of `ND` are among those of `Derives`). Since `A ∨ ¬A` is
   classically but not intuitionistically provable, the inclusion is strict.

2. **Glivenko's theorem** (1929). Conversely, if `φ` is classically derivable from
   `Γ`, then its *double negation* `¬¬φ` is intuitionistically derivable from `Γ`.
   Classical logic thus embeds in intuitionistic logic: what the classical
   mathematician asserts, the intuitionist can at least assert to be *irrefutable*.
   In particular a *negated* formula `¬φ` is classically provable iff it is
   intuitionistically provable, and classical and intuitionistic propositional logic
   are equally consistent.

Philosophically, Glivenko's theorem (and its first-order refinement, the
Gödel–Gentzen negative translation of 1933) is the technical core of the claim that
the dispute between Brouwer and Hilbert is not about *which* propositional
statements are consistent to assert, but about what an assertion *means*: for the
intuitionist, `A ∨ B` demands a proof of one of the disjuncts; `¬¬(A ∨ B)` only
the impossibility of refuting both — and that much classical logic never exceeds.

The proof is by induction on classical derivations; the key observation is that
double negation is a *monad* in intuitionistic logic (`A ⊢ ¬¬A`, and from `¬¬A` and
`A ⊢ ¬¬B` follows `¬¬B`), and that reductio becomes provable under `¬¬`.
-/

namespace Foundations.Bridges

open Foundations.Types.STLC (ND Ty)

/-! ## Translating formulas -/

/-- Translation of intuitionistic formulas (Part V's simple types) into classical
formulas (Part III): atoms to variables, `→` to `→`, `×` to `∧`, `+` to `∨`, `⊥` to `⊥`. -/
def toClassical : Ty → Logic.Formula
  | .atom n => .var n
  | .bot => .bot
  | .arr A B => .imp (toClassical A) (toClassical B)
  | .prod A B => .conj (toClassical A) (toClassical B)
  | .sum A B => .disj (toClassical A) (toClassical B)

/-- Translation of classical formulas into intuitionistic formulas (the inverse). -/
def toIntuitionistic : Logic.Formula → Ty
  | .var n => .atom n
  | .bot => .bot
  | .imp φ ψ => .arr (toIntuitionistic φ) (toIntuitionistic ψ)
  | .conj φ ψ => .prod (toIntuitionistic φ) (toIntuitionistic ψ)
  | .disj φ ψ => .sum (toIntuitionistic φ) (toIntuitionistic ψ)

/-- The translations are mutually inverse (one direction). -/
@[simp] theorem toClassical_toIntuitionistic (φ : Logic.Formula) :
    toClassical (toIntuitionistic φ) = φ := by
  induction φ <;> simp_all [toClassical, toIntuitionistic]

/-- The translations are mutually inverse (other direction). -/
@[simp] theorem toIntuitionistic_toClassical (A : Ty) :
    toIntuitionistic (toClassical A) = A := by
  induction A <;> simp_all [toClassical, toIntuitionistic]

/-- Intuitionistic double negation `¬¬A`. -/
abbrev nn (A : Ty) : Ty := Types.STLC.neg (Types.STLC.neg A)

/-! ## Structural rules for intuitionistic natural deduction -/

/-- Any member of the context is derivable. -/
theorem ND.ofMem {Γ : List Ty} {A : Ty} (h : A ∈ Γ) : ND Γ A := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 h
  exact ND.hyp hn

/-- **Weakening** for intuitionistic natural deduction: enlarging the context (as a
set of hypotheses) preserves derivability. -/
theorem ND.mono {Γ : List Ty} {A : Ty} (h : ND Γ A) :
    ∀ {Δ : List Ty}, (∀ B ∈ Γ, B ∈ Δ) → ND Δ A := by
  induction h with
  | hyp hn => exact fun hs => ND.ofMem (hs _ (List.mem_of_getElem? hn))
  | impI _ ih =>
    exact fun hs => ND.impI (ih (fun B hB => by
      rcases List.mem_cons.1 hB with rfl | hB
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hs B hB)))
  | impE _ _ ih₁ ih₂ => exact fun hs => ND.impE (ih₁ hs) (ih₂ hs)
  | andI _ _ ih₁ ih₂ => exact fun hs => ND.andI (ih₁ hs) (ih₂ hs)
  | andE₁ _ ih => exact fun hs => ND.andE₁ (ih hs)
  | andE₂ _ ih => exact fun hs => ND.andE₂ (ih hs)
  | orI₁ _ ih => exact fun hs => ND.orI₁ (ih hs)
  | orI₂ _ ih => exact fun hs => ND.orI₂ (ih hs)
  | orE _ _ _ ih ih₁ ih₂ =>
    exact fun hs => ND.orE (ih hs)
      (ih₁ (fun B hB => by
        rcases List.mem_cons.1 hB with rfl | hB
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs B hB)))
      (ih₂ (fun B hB => by
        rcases List.mem_cons.1 hB with rfl | hB
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs B hB)))
  | botE _ ih => exact fun hs => ND.botE (ih hs)

/-- Weakening by one hypothesis at the front. -/
theorem ND.wk {Γ : List Ty} {A : Ty} (B : Ty) (h : ND Γ A) : ND (B :: Γ) A :=
  ND.mono h fun _ hC => List.mem_cons_of_mem _ hC

/-- Weakening under the first hypothesis. -/
theorem ND.wk₁ {Γ : List Ty} {A C : Ty} (B : Ty) (h : ND (C :: Γ) A) : ND (C :: B :: Γ) A :=
  ND.mono h fun D hD => by
    rcases List.mem_cons.1 hD with rfl | hD
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hD)

/-- The first hypothesis. -/
theorem ND.h0 {Γ : List Ty} {A : Ty} : ND (A :: Γ) A := ND.ofMem List.mem_cons_self

/-- The second hypothesis. -/
theorem ND.h1 {Γ : List Ty} {A B : Ty} : ND (B :: A :: Γ) A :=
  ND.ofMem (List.mem_cons_of_mem _ List.mem_cons_self)

/-! ## Double negation is a monad -/

/-- **Unit**: `A ⊢ ¬¬A`. -/
theorem nn_intro {Γ : List Ty} {A : Ty} (h : ND Γ A) : ND Γ (nn A) :=
  ND.impI (ND.impE ND.h0 (ND.wk _ h))

/-- **Bind**: from `¬¬A`, and `¬¬B` under the hypothesis `A`, infer `¬¬B`. -/
theorem nn_bind {Γ : List Ty} {A B : Ty} (hA : ND Γ (nn A)) (hB : ND (A :: Γ) (nn B)) :
    ND Γ (nn B) :=
  ND.impI (ND.impE (ND.wk _ hA) (ND.impI (ND.impE (ND.wk₁ _ hB) ND.h1)))

/-- `¬¬` and implication introduction: from `A ⊢ ¬¬B` infer `¬¬(A → B)`. -/
theorem nn_impI {Γ : List Ty} {A B : Ty} (h : ND (A :: Γ) (nn B)) : ND Γ (nn (.arr A B)) := by
  -- Under `k : ¬(A → B)` we get `¬B` (from `B` build `A → B`).
  have notB : ND (Types.STLC.neg (.arr A B) :: Γ) (Types.STLC.neg B) :=
    ND.impI (ND.impE ND.h1 (ND.impI ND.h1))
  refine ND.impI (ND.impE ND.h0 (ND.impI (ND.botE ?_)))
  exact ND.impE (ND.wk₁ _ h) (ND.wk _ notB)

/-- Reductio becomes intuitionistic under `¬¬`: from `¬A ⊢ ¬¬⊥` infer `¬¬A`. -/
theorem nn_raa {Γ : List Ty} {A : Ty} (h : ND (Types.STLC.neg A :: Γ) (nn .bot)) :
    ND Γ (nn A) :=
  ND.impI (ND.impE h (ND.impI ND.h0))

/-! ## Intuitionistic ⊆ classical -/

/-- **Every intuitionistic derivation is a classical derivation.** If `A` is derivable
from `Γ` in Part V's intuitionistic natural deduction, then its translation is
derivable from the translated hypotheses in Part III's classical natural deduction. -/
theorem intuitionistic_to_classical {Γ : List Ty} {A : Ty} (h : ND Γ A) :
    Logic.Derives (Logic.Theory.ofList (Γ.map toClassical)) (toClassical A) := by
  have cons_sub : ∀ (B : Ty) (L : List Ty),
      (Logic.Theory.ofList ((B :: L).map toClassical)).Subset
        (Logic.Theory.insert (Logic.Theory.ofList (L.map toClassical)) (toClassical B)) := by
    intro B L ψ hψ
    rcases List.mem_cons.1 hψ with h | h
    · exact Or.inl h
    · exact Or.inr h
  induction h with
  | hyp hn =>
    exact Logic.Derives.hyp (List.mem_map_of_mem (List.mem_of_getElem? hn))
  | impI _ ih => exact Logic.Derives.impI (ih.weaken (cons_sub _ _))
  | impE _ _ ih₁ ih₂ => exact Logic.Derives.impE ih₁ ih₂
  | andI _ _ ih₁ ih₂ => exact Logic.Derives.conjI ih₁ ih₂
  | andE₁ _ ih => exact Logic.Derives.conjE₁ ih
  | andE₂ _ ih => exact Logic.Derives.conjE₂ ih
  | orI₁ _ ih => exact Logic.Derives.disjI₁ ih
  | orI₂ _ ih => exact Logic.Derives.disjI₂ ih
  | orE _ _ _ ih ih₁ ih₂ =>
    exact Logic.Derives.disjE ih (ih₁.weaken (cons_sub _ _)) (ih₂.weaken (cons_sub _ _))
  | botE _ ih => exact Logic.Derives.botE ih

/-- **The inclusion is strict.** For any atom `p`, excluded middle `p ∨ ¬p` is
classically derivable but not intuitionistically derivable. -/
theorem intuitionistic_ne_classical (k : Nat) :
    Logic.Derives Logic.Theory.empty (toClassical (.sum (.atom k) (Types.STLC.neg (.atom k)))) ∧
    ¬ ND [] (.sum (.atom k) (Types.STLC.neg (.atom k))) :=
  ⟨Logic.Derives.lem _ (.var k), Types.STLC.lem_unprovable k⟩

/-! ## Glivenko's theorem -/

/-- The inductive core of Glivenko's theorem: a classical derivation from `Δ` gives an
intuitionistic derivation of the double negation from any context containing the
translations of `Δ`. -/
theorem glivenko_aux {Δ : Logic.Theory} {φ : Logic.Formula} (h : Logic.Derives Δ φ) :
    ∀ L : List Ty, (∀ ψ, Δ ψ → toIntuitionistic ψ ∈ L) → ND L (nn (toIntuitionistic φ)) := by
  have ins : ∀ {Δ : Logic.Theory} {L : List Ty} (φ : Logic.Formula),
      (∀ ψ, Δ ψ → toIntuitionistic ψ ∈ L) →
      ∀ ψ, Logic.Theory.insert Δ φ ψ → toIntuitionistic ψ ∈ toIntuitionistic φ :: L := by
    intro Δ L φ hL ψ hψ
    rcases hψ with rfl | hψ
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hL ψ hψ)
  induction h with
  | hyp hφ => exact fun L hL => nn_intro (ND.ofMem (hL _ hφ))
  | impI _ ih => exact fun L hL => nn_impI (ih _ (ins _ hL))
  | impE _ _ ih₁ ih₂ =>
    intro L hL
    exact nn_bind (ih₁ L hL) (nn_bind (ND.wk _ (ih₂ L hL)) (nn_intro (ND.impE ND.h1 ND.h0)))
  | conjI _ _ ih₁ ih₂ =>
    intro L hL
    exact nn_bind (ih₁ L hL) (nn_bind (ND.wk _ (ih₂ L hL)) (nn_intro (ND.andI ND.h1 ND.h0)))
  | conjE₁ _ ih => exact fun L hL => nn_bind (ih L hL) (nn_intro (ND.andE₁ ND.h0))
  | conjE₂ _ ih => exact fun L hL => nn_bind (ih L hL) (nn_intro (ND.andE₂ ND.h0))
  | disjI₁ _ ih => exact fun L hL => nn_bind (ih L hL) (nn_intro (ND.orI₁ ND.h0))
  | disjI₂ _ ih => exact fun L hL => nn_bind (ih L hL) (nn_intro (ND.orI₂ ND.h0))
  | disjE _ _ _ ih ih₁ ih₂ =>
    intro L hL
    exact nn_bind (ih L hL) (ND.orE ND.h0 (ND.wk₁ _ (ih₁ _ (ins _ hL))) (ND.wk₁ _ (ih₂ _ (ins _ hL))))
  | botE _ ih => exact fun L hL => nn_bind (ih L hL) (ND.botE ND.h0)
  | raa _ ih => exact fun L hL => nn_raa (ih _ (ins _ hL))

/-- **Glivenko's theorem (1929).** If `φ` is classically derivable from the hypotheses
`Γ`, then `¬¬φ` is intuitionistically derivable from the same hypotheses. -/
theorem glivenko {Γ : List Logic.Formula} {φ : Logic.Formula}
    (h : Logic.Derives (Logic.Theory.ofList Γ) φ) :
    ND (Γ.map toIntuitionistic) (nn (toIntuitionistic φ)) :=
  glivenko_aux h _ fun _ hψ => List.mem_map_of_mem hψ

/-- **Glivenko, as an equivalence.** A formula is classically provable (from no
hypotheses) if and only if its double negation is intuitionistically provable. -/
theorem classical_iff_nn_intuitionistic (φ : Logic.Formula) :
    Logic.Derives Logic.Theory.empty φ ↔ ND [] (nn (toIntuitionistic φ)) := by
  constructor
  · intro h
    exact glivenko (Γ := []) (h.weaken (Logic.Theory.empty_subset _))
  · intro h
    have := intuitionistic_to_classical h
    simp only [List.map_nil, toClassical, toClassical_toIntuitionistic] at this
    exact Logic.Derives.dne (this.weaken fun _ h => absurd h List.not_mem_nil)

/-- `¬¬¬A ⊢ ¬A` intuitionistically. -/
theorem nnn_elim {Γ : List Ty} {A : Ty} (h : ND Γ (nn (Types.STLC.neg A))) :
    ND Γ (Types.STLC.neg A) :=
  ND.impI (ND.impE (ND.wk _ h) (nn_intro ND.h0))

/-- **Negated formulas agree.** A negation `¬φ` is classically provable if and only if
it is intuitionistically provable: on negative statements the two logics coincide. -/
theorem neg_classical_iff_intuitionistic (φ : Logic.Formula) :
    Logic.Derives Logic.Theory.empty (Logic.Formula.neg φ) ↔
      ND [] (Types.STLC.neg (toIntuitionistic φ)) := by
  constructor
  · intro h
    exact nnn_elim ((classical_iff_nn_intuitionistic _).1 h)
  · intro h
    have := intuitionistic_to_classical h
    simp only [List.map_nil, toClassical, toClassical_toIntuitionistic] at this
    exact this.weaken fun _ h => absurd h List.not_mem_nil

/-- **Consistency of classical natural deduction (via Glivenko).** Classical propositional natural deduction is consistent
(does not derive `⊥`) — a consequence of Glivenko's theorem and the consistency of
intuitionistic natural deduction, which Part V proved by normalization (cut
elimination), without any appeal to truth tables. -/
theorem classical_consistent : ¬ Logic.Derives Logic.Theory.empty .bot := fun h => by
  have := (classical_iff_nn_intuitionistic .bot).1 h
  exact Types.STLC.nd_consistent (ND.impE this (ND.impI ND.h0))

end Foundations.Bridges
