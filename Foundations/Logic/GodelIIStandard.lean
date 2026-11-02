import Foundations.Logic.GodelIIDerivations

/-!
# The derivation-based provability formula in the standard model, and what remains

Gödel's 1931 provability formula is meant to express, in the standard model `ℕ`, exactly
"`x` is the code of a theorem". This file proves that the derivation-based formula
`provD` of `GodelIIDerivations` does so (`sat_provD`): a derivation code in `ℕ` decodes,
line by line, into a derivation in the inductive rule system `Derivable paRule`, which is
PA-provability by `derivable_iff_PA_proves`.

Together with (D1) and (D2) from the previous file, this places `provD` where the
Hilbert–Bernays–Löb analysis (1939, 1955) says Gödel's second theorem needs it, *except
for (D3)*. We record the consequences precisely:

* `godel_second_provD_of_D3`: if (D3) holds for `provD` — i.e. PA proves formalised
  Σ₁-completeness in the form `□_D φ → □_D □_D φ` — then PA does not prove
  `Con_D := ¬provD(⌜⊥⌝)`; likewise Löb's theorem for `provD`. This improves on
  `godel_second_PA` of `Lob`, which assumed both (D2) and (D3) for `provPA`: (D2) is now
  a theorem for a derivation-based formula.
* `godel_second_provD_of_dominates`: alternatively, `PA ⊬ Con_D` follows from the single
  PA-provable implication `provH(⌜⊥⌝) → provD(⌜⊥⌝)` (via `GodelIITransfer`).
* `provD_std_iff_provH`: `provD` and `provH` have the same extension in `ℕ`. By Feferman's
  observation (`godel_second_intensional`) this alone transfers nothing.

**Status of the caveat.** Neither hypothesis is proved *for `provD`*. Both are statements
about non-standard derivations inside models of PA. Every line of a `provD`-derivation is
checked by the Σ₁ graph of a program known only on standard inputs, so no line with
non-standard content can be verified inside a non-standard model. `ProvDD3` therefore
remains open.

The files `GodelIID3*` carry out the missing internal arithmetisation of syntax for a
variant `provDP` of `provD`. It is the same calculus, but modus ponens and the substitution
of numerals (a derived rule) may also be checked by explicit formulas. For `provDP` they
prove formalised Σ-completeness inside every model of PA (`PAModel.sig_complete`), hence
(D3) (`provDP_D3`), and so **Gödel's second theorem unconditionally**
(`godel_second_provDP : ¬ PA ⊢ ¬provDP(⌜⊥⌝)`). `provDP` defines PA-provability in `ℕ`
(`sat_provDP`). PA proves `provD(x) → provDP(x)` but not, as far as is shown, the converse,
so the result does not transfer back to `provD`.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability PAModel

namespace GodelII

/-- The step test in the standard model is the step relation `paStep`. -/
theorem stepM_std {q : Nat} (h : StepM (N := stdPA) q) : paStep q = true := by
  unfold StepM at h
  have hev : Eval stepCode [q] 1 := by
    refine (sat_evalSigma stepCode 1 q).1 ((sat_congr_fresh _ fun n hn => ?_).1 h)
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact absurd (evalSigma_fresh _ (n + 2) (by omega)) hn
  have := Eval.det (stepCode_spec q) hev
  cases hq : paStep q
  · rw [hq] at this; exact absurd this (by decide)
  · rfl

/-- Decoding a list code `⟨a, t⟩ + 1`. -/
theorem decList_lcons (a t : Nat) : decList (pair a t + 1) = a :: decList t := by
  rw [decList, fst_pair, snd_pair]

/-- Walking along the tails of a premise list in `ℕ`, from the end: if the tails
`s₀, …, sₘ = 0` are coded by `(c', d')` and each `sⱼ` (`j < m`) is `⟨a, sⱼ₊₁⟩ + 1` with
`a` good, then every element of the list `sₘ₋ᵢ` is good. -/
theorem tails_std {c' d' m : Nat} {Good : Nat → Prop}
    (hm : BetaM (N := stdPA) c' d' m (0 : Nat))
    (hprem : ∀ j : Nat, j < m → ∃ s : Nat, BetaM (N := stdPA) c' d' j s ∧
      ∃ t : Nat, BetaM (N := stdPA) c' d' (j + 1 : Nat) t ∧ ∃ a : Nat, s = pair a t + 1 ∧ Good a) :
    ∀ i : Nat, i ≤ m → ∀ s : Nat, BetaM (N := stdPA) c' d' (m - i : Nat) s →
      ∀ z ∈ decList s, Good z := by
  intro i
  induction i with
  | zero =>
    intro _ s hs z hz
    rw [Nat.sub_zero] at hs
    rw [betaM_unique hs hm, decList] at hz
    exact absurd hz List.not_mem_nil
  | succ i ihi =>
    intro hi s hs
    obtain ⟨s', hs', t, ht, a, rfl, ha⟩ := hprem (m - (i + 1)) (by omega)
    rw [betaM_unique hs hs', decList_lcons]
    have ht' : BetaM (N := stdPA) c' d' (m - i : Nat) t := by
      have e : m - (i + 1) + 1 = m - i := by omega
      rw [← e]; exact ht
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ha
    · exact ihi (by omega) t ht' z hz

/-- **Soundness of derivation codes in `ℕ`.** Every entry of a valid derivation code in the
standard model is a derivable judgement. -/
theorem derM_std_sound {y : Nat} (h : DerM (N := stdPA) y) : Derivable paRule y := by
  obtain ⟨c, d, n, hn, hall⟩ := h
  have key : ∀ k : Nat, k ≤ n → ∀ y : Nat, BetaM (N := stdPA) c d k y → Derivable paRule y := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk y hy
      obtain ⟨y', hy', w, js, u, hu, q, hq, hs, c', d', m, h0, hm, hprem⟩ :=
        hall k (stdPA_le.2 hk)
      rw [betaM_unique hy hy']
      have e₁ := stdPA_pairM hu
      have e₂ := stdPA_pairM hq
      have hstep := stepM_std hs
      -- walk along the tails of the premise list, from the end
      have hprem' : ∀ j : Nat, j < (m : Nat) → ∃ s : Nat, BetaM (N := stdPA) c' d' j s ∧
          ∃ t : Nat, BetaM (N := stdPA) c' d' (j + 1 : Nat) t ∧ ∃ a : Nat, s = pair a t + 1 ∧
            Derivable paRule a := by
        intro j hj
        obtain ⟨s, hs, t, ht, a, ⟨v, hv, hsv⟩, p, hp, hpa⟩ := hprem j (stdPA_lt.2 hj)
        have hp' : (p : Nat) < k := stdPA_lt.1 hp
        refine ⟨s, hs, t, ht, a, ?_, ih p hp' (Nat.le_trans (Nat.le_of_lt hp') hk) a hpa⟩
        have hsv' : (s : Nat) = (v : Nat) + 1 := hsv
        rw [hsv', stdPA_pairM hv]
      have tails := tails_std (Good := Derivable paRule) (m := (m : Nat)) hm hprem'
      refine Derivable.intro y' w (decList js) (tails (m : Nat) (Nat.le_refl _) js (by rw [Nat.sub_self]; exact h0))
        ?_
      rw [encList_decList]
      show paStep (pair y' (pair w js)) = true
      rw [← e₁, ← e₂]; exact hstep
  exact key n (Nat.le_refl n) y hn

/-- The cast `ℕ → stdPA` is the identity. -/
theorem stdPA_cast (n : Nat) : (@Nat.cast stdPA.Dom (PAModel.instNatCast stdPA) n) = n :=
  numM_std n

/-- **`provD` defines PA-provability in the standard model.** -/
theorem sat_provD (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provD φ) ↔ PA ⊢₁ φ := by
  constructor
  · intro h
    have h' := (provDM_natCast_iff (N := stdPA) (fcode φ)).1 ((sat_box_provD stdPA e φ).1 h)
    rw [stdPA_cast] at h'
    exact (derivable_iff_PA_proves φ).1 (derM_std_sound h')
  · intro h
    exact PA_sound (provD_D1 h) e

/-- **`provD` and `provH` have the same extension in `ℕ`.** -/
theorem provD_std_iff_provH (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provD φ) ↔ Sat stdModel e (box provH φ) := by
  rw [sat_provD, sat_provH]

/-- **The open condition (D3) for `provD`** — formalised Σ₁-completeness for the
derivation predicate: `PA ⊢ provD(⌜φ⌝) → provD(⌜provD(⌜φ⌝)⌝)` for every formula `φ`.
This is a *statement*, not a theorem of the library; it is proved instead for the
transparent variant `provDP` (`provDP_D3` in `GodelIID3Main`). -/
def ProvDD3 : Prop := ∀ φ : Formula Arith, PA ⊢₁ imp (box provD φ) (box provD (box provD φ))

/-- (D1)–(D3) for `provD`, given (D3). -/
theorem provD_derivability_of_D3 (h3 : ProvDD3) : Derivability PA provD :=
  ⟨fun _ h => provD_D1 h, provD_D2, h3⟩

/-- **Löb's theorem for the derivation predicate, conditional on (D3) only.** -/
theorem lob_provD_of_D3 (h3 : ProvDD3) {φ : Formula Arith} (h : PA ⊢₁ imp (box provD φ) φ) :
    PA ⊢₁ φ :=
  lob (fun _ h => PA_proves_Q h) (provD_derivability_of_D3 h3) h

/-- **Gödel's second theorem for the derivation predicate, conditional on (D3) only.** If
PA proves formalised Σ₁-completeness for `provD` in the form (D3), then PA does not prove
the derivation-based consistency statement `Con_D = ¬provD(⌜⊥⌝)`. -/
theorem godel_second_provD_of_D3 (h3 : ProvDD3) : ¬ PA ⊢₁ conF provD :=
  godel_second (fun _ h => PA_proves_Q h) (provD_derivability_of_D3 h3) PA_consistent

/-- **Gödel's second theorem for the derivation predicate, from domination.** If
`PA ⊢ provH(⌜⊥⌝) → provD(⌜⊥⌝)`, then PA does not prove `Con_D`. -/
theorem godel_second_provD_of_dominates (h : PA ⊢₁ imp (box provH bot) (box provD bot)) :
    ¬ PA ⊢₁ conF provD :=
  godel_second_of_dominates h

/-- **Consequence of (D1) and (D2) alone: `Con_D` is equivalent to the consistency of the
`provD`-theorems on any formula.** For every `φ`, PA proves `□_D φ → □_D ¬φ → □_D ⊥`; so
`Con_D` implies, provably in PA, that no formula and its negation are both `provD`-provable.
-/
theorem provD_no_contradiction (φ : Formula Arith) :
    PA ⊢₁ imp (box provD φ) (imp (box provD (neg φ)) (box provD bot)) :=
  PA_proves_of_models fun N e hφ hnφ =>
    sat_of_PA_proves N (provD_D2 φ bot) e hnφ hφ

end GodelII

end Foundations.Logic.FO
