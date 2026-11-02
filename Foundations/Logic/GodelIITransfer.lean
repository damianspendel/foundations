import Foundations.Logic.DerivabilityConditions

/-!
# Gödel II and the choice of provability predicate: transfer principles

**History.** Gödel's 1931 paper *Über formal unentscheidbare Sätze* proved the first
incompleteness theorem in full and announced the second — "the consistency of a system
cannot be proved in the system" — with only a sketch: the argument for the first theorem,
he observed, can itself be carried out inside the system. The sketch was first worked out
by Hilbert and Bernays in volume II of the *Grundlagen der Mathematik* (1939), who isolated
the properties of the arithmetised provability predicate that the argument needs. Löb
(1955), answering Henkin's question about sentences asserting their own provability,
streamlined them into the three **derivability conditions** (D1)–(D3) and proved Löb's
theorem, of which Gödel II is the special case `φ = ⊥` (see `Lob`).

**Why the predicate matters.** Gödel II is not a statement about *the* fact "PA is
consistent", but about a particular *sentence* expressing it, and different sentences can
express it equally well in the standard model while behaving differently inside PA.
Feferman (1960, *Arithmetization of metamathematics in a general setting*) made this
precise: the theorem is **intensional** — it depends on how provability is written down,
not only on which numbers satisfy the formula. He exhibited formulas which define the set
of theorems of PA correctly in `ℕ` but whose consistency statement *is* provable in PA.
The file `GodelIIFeferman` gives a kernel-checked example of this phenomenon.

**What is proved in this library, and the gap.** `godel_second_PA_unconditional` proves
that PA does not prove `¬provH(⌜⊥⌝)` for the Hilbert-style formula `provH`, which
satisfies (D1)–(D3) provably in PA. The canonical, "textbook" consistency statement uses
instead the Σ₁ formula *"there is (a code of) a PA-derivation whose last formula is `x`"*.
The arithmetical formulas that the computability machinery of this library supplies are
Σ₁ graphs of programs chosen by `Classical.choose` from existence proofs (`Comp f` is an
existential proposition); of such a program nothing is known except its behaviour on
*standard* inputs. In particular the axiom clause of `provH` is "the program `searchPA`
halts on `x`", and the only fact about `searchPA` is `searchPA_spec`, a statement about
standard numbers. Consequently nothing constrains the axiom clause of `provH` on
non-standard arguments, and a PA-provable comparison between `provH` and an independently
defined provability formula (such as the derivation-based `provD` of `GodelIIDerivations`)
is not available by the methods of this library. What a proof of Gödel II for a
derivation-based formula needs instead is its (D3) — formalised Σ₁-completeness — which
rests on an arithmetisation of syntax *inside* arbitrary models of PA (formula codes,
numerals, substitution, derivations of true Δ₀ sentences by internal induction). That
internal arithmetisation is the missing piece.

**This file.** We make the remaining task precise by proving the *transfer principles*
which reduce it to a single PA-provable implication:

* `godel_second_transfer`: Gödel II passes from `P` to `P'` whenever
  `PA ⊢ Con_{P'} → Con_P`;
* `godel_second_of_dominates`: for *any* formula `P`, if
  `PA ⊢ provH(⌜⊥⌝) → P(⌜⊥⌝)` then `PA ⊬ Con_P` — this is exactly what a future
  textbook predicate would have to satisfy to inherit the theorem;
* `derivability_congr`: the derivability conditions are invariant under PA-provable
  equivalence of the boxes `□_P φ ↔ □_{P'} φ` — so a proof of `PA ⊢ provH(x) ↔ Prov(x)`
  for a textbook `Prov` would give (D1)–(D3), Löb's theorem and Gödel II for `Prov` at once.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory

namespace GodelII

/-- **Soundness inside a model of PA.** Every theorem of PA holds in every model of PA,
under every assignment. -/
theorem sat_of_PA_proves (N : PAModel) {φ : Formula Arith} (h : PA ⊢₁ φ) (e : Nat → N.Dom) :
    Sat N.M e φ :=
  Proves.soundness h N.M e fun ψ hψ => N.isModel.2 ψ hψ e

/-- Propositional bookkeeping: from `A' → A`, `A → (B → C)`, `B' → B` and `C → C'`
infer `A' → (B' → C')`. -/
theorem imp_imp_congr {T : Theory Arith} {A A' B B' C C' : Formula Arith}
    (ha : T ⊢₁ imp A' A) (hb : T ⊢₁ imp B' B) (hc : T ⊢₁ imp C C') (h : T ⊢₁ imp A (imp B C)) :
    T ⊢₁ imp A' (imp B' C') := by
  have w : ∀ {X : Formula Arith}, T ⊢₁ X → insert (insert T A') B' ⊢₁ X :=
    fun hx => Proves.weaken₁ (Proves.weaken₁ hx _) _
  have hA' : insert (insert T A') B' ⊢₁ A' := Proves.weaken₁ (Proves.assume T A') B'
  have hB' : insert (insert T A') B' ⊢₁ B' := Proves.assume _ B'
  exact Proves.impI (Proves.impI (Proves.impE (w hc)
    (Proves.impE (Proves.impE (w h) (Proves.impE (w ha) hA')) (Proves.impE (w hb) hB'))))

/-- **Invariance of the derivability conditions.** If the boxes of `P` and `P'` are
PA-provably (indeed `T`-provably) equivalent for every formula, and `P` satisfies
(D1)–(D3) over `T`, then so does `P'`. -/
theorem derivability_congr {T : Theory Arith} {P P' : Formula Arith}
    (h₁ : ∀ φ, T ⊢₁ imp (box P φ) (box P' φ)) (h₂ : ∀ φ, T ⊢₁ imp (box P' φ) (box P φ))
    (hD : Derivability T P) : Derivability T P' where
  d1 φ h := Proves.impE (h₁ φ) (hD.d1 φ h)
  d2 φ ψ := imp_imp_congr (h₂ _) (h₂ _) (h₁ _) (hD.d2 φ ψ)
  d3 φ := by
    -- `□'φ → □φ → □□φ → □□'φ → □'□'φ`
    have hstep : T ⊢₁ imp (box P (box P φ)) (box P (box P' φ)) :=
      Proves.impE (hD.d2 _ _) (hD.d1 _ (h₁ φ))
    exact imp_trans (h₂ φ) (imp_trans (hD.d3 φ) (imp_trans hstep (h₁ _)))

/-- **Transfer of Gödel II.** If `PA ⊢ Con_{P'} → Con_P` and PA does not prove `Con_P`,
then PA does not prove `Con_{P'}`. -/
theorem godel_second_transfer {P P' : Formula Arith} (h : PA ⊢₁ imp (conF P') (conF P))
    (hP : ¬ PA ⊢₁ conF P) : ¬ PA ⊢₁ conF P' :=
  fun h' => hP (Proves.impE h h')

/-- **Gödel II for every predicate dominating `provH` at `⊥`.** Let `P` be any formula
such that `PA ⊢ provH(⌜⊥⌝) → P(⌜⊥⌝)` — "a `provH`-proof of `⊥` yields a `P`-proof of
`⊥`", provably in PA. Then PA does not prove `Con_P = ¬P(⌜⊥⌝)`. This is the single
PA-provable implication a textbook provability formula would have to satisfy in order to
inherit `godel_second_PA_unconditional`. -/
theorem godel_second_of_dominates {P : Formula Arith}
    (h : PA ⊢₁ imp (box provH bot) (box P bot)) : ¬ PA ⊢₁ conF P := by
  refine godel_second_transfer (PA_proves_of_models fun N e => ?_) godel_second_PA_unconditional
  intro hcon hH
  exact hcon (sat_of_PA_proves N h e hH)

/-- **Everything transfers along a PA-provable equivalence.** If `PA ⊢ □_H φ ↔ □_P φ`
(as two implications) for every `φ`, then `P` satisfies (D1)–(D3) over PA, Löb's theorem
holds for `P`, and PA does not prove `Con_P`. -/
theorem godel_second_of_equiv {P : Formula Arith}
    (h₁ : ∀ φ, PA ⊢₁ imp (box provH φ) (box P φ)) (h₂ : ∀ φ, PA ⊢₁ imp (box P φ) (box provH φ)) :
    Derivability PA P ∧ (∀ φ, PA ⊢₁ imp (box P φ) φ → PA ⊢₁ φ) ∧ ¬ PA ⊢₁ conF P := by
  have hD := derivability_congr h₁ h₂ provH_derivability
  exact ⟨hD, fun _ h => lob (fun _ h => PA_proves_Q h) hD h, godel_second_of_dominates (h₁ bot)⟩

/-- The instance for the provability formula `provPA` of `Lob` ("the PA proof search
halts on `x`"): Gödel II holds for it as soon as `PA ⊢ provH(⌜⊥⌝) → provPA(⌜⊥⌝)`.
Whether this implication is PA-provable is **open** here: `provPA` is the Σ₁ halting
formula of a program known only by its standard behaviour. -/
theorem godel_second_provPA_of_dominates (h : PA ⊢₁ imp (box provH bot) (box provPA bot)) :
    ¬ PA ⊢₁ conF provPA :=
  godel_second_of_dominates h

/-- **One direction does hold: the axiom clause is dominated by `provH`.** For every `x`,
PA proves `accF(x) → provH(x)` ("if the PA proof search accepts `x`, then `x` has a
`provH`-proof"), uniformly in a free variable — not only for standard codes. Consequently
`PA ⊢ Con_H → Con_acc`: the consistency statement for `provH` *implies* the halting-style
statement "the search for a PA-proof of `⊥` does not halt". This is the wrong direction for
transferring Gödel II to `Con_acc`, which is why it does not close the gap. -/
theorem accF_imp_provH_uniform : PA ⊢₁ imp accF provH :=
  PA_proves_of_models fun N e => by
    intro h
    rw [sat_provH_M]
    apply PAModel.provM_of_acc
    rw [PAModel.AccM]
    exact (sat_accF_cons (e 0) _ _).1 (by
      have : Env.cons (e 0) (fun n => e (n + 1)) = e := by funext n; cases n <;> rfl
      rw [this]; exact h)

/-- `PA ⊢ Con_H → ¬accF(⌜⊥⌝)`: consistency in the sense of `provH` implies that the PA
proof search does not accept `⌜⊥⌝` (provably in PA). -/
theorem conH_imp_conAcc : PA ⊢₁ imp (conF provH) (conF accF) :=
  PA_proves_of_models fun N e => by
    intro hH hA
    apply hH
    have h := sat_of_PA_proves N accF_imp_provH_uniform
      (Env.cons ((numeral (fcode bot)).eval N.M e) e)
    simp only [box, sat_inst] at hA ⊢
    exact h hA

end GodelII

end Foundations.Logic.FO
