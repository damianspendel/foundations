import Foundations.Logic.HilbertProvability

/-!
# The derivability conditions for PA, and Gödel's second incompleteness theorem

We now verify the Hilbert–Bernays–Löb conditions (D2) and (D3) for the provability
formula `provH` of the previous file, and obtain Löb's theorem and Gödel's second
incompleteness theorem for PA **without hypotheses**.

*Method.* By completeness for PA (`PA_proves_of_models`), it suffices to show that
the two sentences hold in every model `N` of PA. Inside `N` a "proof" is a pair
`(c, d)` coding, via Gödel's β-function, a sequence whose length `n + 1` may be a
*non-standard* element of `N`. Two operations on such proofs are needed:

* **combining proofs** (D2): given proofs of `⌜φ → ψ⌝` and of `⌜φ⌝`, write one after
  the other and append `⌜ψ⌝`, justified by modus ponens from the two last lines. That
  the concatenation of two coded sequences of non-standard lengths again has a code is
  the concatenation lemma `concat_exists` of `PASequences`, proved inside `N` by
  induction (an internal Chinese remainder theorem). The lines of the two original
  proofs remain justified in the new code because their justifications only refer to
  earlier lines, which have merely been shifted (`lineOK_shift`).
* **necessitation** (D3): from a proof of `⌜φ⌝`, append the line `⌜accF(⌜φ⌝)⌝` by the
  necessitation rule; then use the PA-theorem `accF(⌜φ⌝) → provH(⌜φ⌝)` (an axiom line
  — it is provable in PA because every accepted formula has a one-line proof) and
  modus ponens to reach `⌜provH(⌜φ⌝)⌝`.

The only facts about *standard* numbers transported into `N` are Σ₁ statements —
that the proof search accepts a particular PA-theorem, that the necessitation program
maps one particular number to another, and polynomial identities for Cantor pairing —
which hold in every model of PA by Σ₁-completeness.

*What has been shown, exactly.* `provH` is a Σ₁-style formula (built uniformly by the
definability calculus) which defines PA-provability in the standard model
(`sat_provH`, and `provH_std_iff_provPA` relates it to `provPA` of `Lob`) and satisfies
(D1)–(D3) over PA. The (D3) argument uses the necessitation rule built into the proof
notion; formalised Σ₁-completeness for arbitrary Σ₁ formulas is *not* developed here,
and (D2)/(D3) are not established for the formula `provPA` itself (whose program is
not under our control in non-standard models). Gödel's second theorem is therefore
stated for `provH`: `godel_second_PA_unconditional : ¬ PA ⊢ ¬provH(⌜⊥⌝)`.

*Relation to the textbook consistency statement (see the `GodelII*` files).* It is **not**
shown that `provH` is PA-provably equivalent to a derivation-based provability formula,
nor that `PA ⊢ Con_textbook → Con_H`; the known specification of `provH` (whose axiom
clause is an opaque search program, unconstrained on non-standard arguments) does not
supply such a relation. What has been added:
the transfer principles `GodelII.godel_second_of_dominates` and `GodelII.derivability_congr`
(Gödel II passes to any `P` with `PA ⊢ provH(⌜⊥⌝) → P(⌜⊥⌝)`); a Feferman-style example
`GodelII.provF` with the same extension as `provH` in `ℕ` whose consistency PA *does* prove
(`GodelII.godel_second_intensional`); and a derivation-based formula `provD` for PA's
natural-deduction calculus satisfying (D1) and (D2) over PA and defining PA-provability in
`ℕ`, for which Gödel II is proved *conditionally on (D3)* (`GodelII.godel_second_provD_of_D3`).
(D3) for `provD` — formalised Σ₁-completeness — needs an arithmetisation of syntax inside
models of PA and remains open.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory

namespace PAModel

variable {N : PAModel}

/-- **A valid proof code.** Every line `0, …, n` of the sequence coded by `(c, d)` is
justified. -/
def Valid (c d n : N.Dom) : Prop := ∀ k, k ≤ n → LineOK c d k

/-- Adding on the left preserves `<`. -/
theorem add_lt_add_left'' {i j : N.Dom} (s : N.Dom) (h : i < j) : s + i < s + j := by
  obtain ⟨z, hz⟩ := h; exact ⟨z, by grind⟩

/-- **Justified lines survive shifting.** If the entries `0, …, n` of `(c₁, d₁)` reappear
in `(c, d)` at positions `s, …, s + n`, then a justified line `j ≤ n` of `(c₁, d₁)` is a
justified line `s + j` of `(c, d)`: its premises have been shifted along with it. -/
theorem lineOK_shift {c₁ d₁ c d s n j : N.Dom}
    (hcopy : ∀ i y, i ≤ n → BetaM c₁ d₁ i y → BetaM c d (s + i) y) (hj : j ≤ n)
    (h : LineOK c₁ d₁ j) : LineOK c d (s + j) := by
  obtain ⟨y, hy, hjust⟩ := h
  refine ⟨y, hcopy j y hj hy, ?_⟩
  rcases hjust with hacc | ⟨i, hi, i', hi', a, b, ha, hb, hmp⟩ | ⟨i, hi, a, ha, hnec⟩
  · exact Or.inl hacc
  · have hin : i ≤ n := le_of_lt' (lt_of_lt_of_le' hi hj)
    have hin' : i' ≤ n := le_of_lt' (lt_of_lt_of_le' hi' hj)
    exact Or.inr (Or.inl ⟨s + i, add_lt_add_left'' s hi, s + i', add_lt_add_left'' s hi', a, b,
      hcopy i a hin ha, hcopy i' b hin' hb, hmp⟩)
  · have hin : i ≤ n := le_of_lt' (lt_of_lt_of_le' hi hj)
    exact Or.inr (Or.inr ⟨s + i, add_lt_add_left'' s hi, a, hcopy i a hin ha, hnec⟩)

/-- **Concatenating valid proofs.** Given valid codes of lengths `n₁ + 1` and `n₂ + 1`
and a further entry `v`, there is a code of the concatenation followed by `v`; it is
valid as soon as its last line (position `n₁ + n₂ + 2`) is justified. -/
theorem concat_valid {c₁ d₁ n₁ c₂ d₂ n₂ : N.Dom} (h₁ : Valid c₁ d₁ n₁) (h₂ : Valid c₂ d₂ n₂)
    (v : N.Dom) : ∃ c d, (∀ i y, i ≤ n₁ → BetaM c₁ d₁ i y → BetaM c d i y) ∧
      (∀ i y, i ≤ n₂ → BetaM c₂ d₂ i y → BetaM c d (n₁ + 1 + i) y) ∧
      BetaM c d (n₁ + n₂ + 2) v ∧ (LineOK c d (n₁ + n₂ + 2) → Valid c d (n₁ + n₂ + 2)) := by
  obtain ⟨c, d, -, hA, hB, hv⟩ := concat_exists c₁ d₁ n₁ c₂ d₂ n₂ v 0
  refine ⟨c, d, hA, hB, hv, fun hlast k hk => ?_⟩
  rcases le_or_lt' n₁ k with h | h
  · have := lineOK_shift (s := 0) (fun i y hi hy => by rw [zero_add']; exact hA i y hi hy) h
      (h₁ k h)
    rwa [zero_add'] at this
  · obtain ⟨j, rfl⟩ := exists_of_lt h
    rcases le_or_lt' n₂ j with hj | hj
    · have := lineOK_shift hB hj (h₂ j hj)
      rwa [show n₁ + 1 + j = n₁ + (j + 1) by grind] at this
    · obtain ⟨δ, rfl⟩ := exists_of_lt hj
      rcases zero_or_succ δ with rfl | ⟨δ', rfl⟩
      · rwa [show n₁ + (n₂ + (0 + 1) + 1) = n₁ + n₂ + 2 by grind]
      · obtain ⟨z, hz⟩ := hk
        exact absurd (by grind : (n₁ + n₂ + 2) + ((δ' + z) + 1) = n₁ + n₂ + 2)
          (add_succ_ne_self _ _)

/-- **Provability in a model of PA is closed under modus ponens.** -/
theorem provM_mp {a b y : N.Dom} (hmp : MPM a b y) (ha : ProvM a) (hb : ProvM b) : ProvM y := by
  obtain ⟨c₁, d₁, n₁, e₁, v₁⟩ := ha
  obtain ⟨c₂, d₂, n₂, e₂, v₂⟩ := hb
  obtain ⟨c, d, hA, hB, hv, hval⟩ := concat_valid v₁ v₂ y
  refine ⟨c, d, _, hv, hval ⟨y, hv, Or.inr (Or.inl ⟨n₁, ⟨n₂ + 1, by grind⟩, n₁ + 1 + n₂,
    ⟨0, by grind⟩, a, b, hA n₁ a (le_refl' _) e₁, hB n₂ b (le_refl' _) e₂, hmp⟩)⟩⟩

/-- **Provability in a model of PA is closed under necessitation.** -/
theorem provM_nec {a y : N.Dom} (hnec : NecM a y) (ha : ProvM a) : ProvM y := by
  obtain ⟨c₁, d₁, n₁, e₁, v₁⟩ := ha
  obtain ⟨c, d, hA, -, hv, hval⟩ := concat_valid v₁ v₁ y
  exact ⟨c, d, _, hv, hval ⟨y, hv, Or.inr (Or.inr ⟨n₁, ⟨n₁ + 1, by grind⟩, a,
    hA n₁ a (le_refl' _) e₁, hnec⟩)⟩⟩

end PAModel

open PAModel

/-- **Condition (D2) for `provH`.** `PA ⊢ □(φ → ψ) → (□φ → □ψ)`. -/
theorem provH_D2 (φ ψ : Formula Arith) :
    PA ⊢₁ imp (box provH (imp φ ψ)) (imp (box provH φ) (box provH ψ)) :=
  PA_proves_of_models fun N e => by
    simp only [Sat, sat_box_provH]
    exact fun h₁ h₂ => provM_mp (mpm_natCast (fcode φ) (fcode ψ)) h₁ h₂

/-- Every formula accepted by the proof search is `provH`-provable, provably in PA:
`PA ⊢ accF(⌜φ⌝) → provH(⌜φ⌝)`. -/
theorem accF_imp_provH (φ : Formula Arith) : PA ⊢₁ imp (box accF φ) (box provH φ) :=
  PA_proves_of_models fun N e => by
    simp only [Sat, sat_box_provH, sat_box_accF]
    exact provM_of_acc

/-- **Condition (D3) for `provH`.** `PA ⊢ □φ → □□φ`. -/
theorem provH_D3 (φ : Formula Arith) : PA ⊢₁ imp (box provH φ) (box provH (box provH φ)) :=
  PA_proves_of_models fun N e => by
    simp only [Sat, sat_box_provH]
    intro h
    -- necessitation: `□φ ⊢ accF(⌜φ⌝)` as a line
    have h₁ : ProvM ((fcode (box accF φ) : Nat) : N.Dom) := by
      rw [← necFun_fcode]; exact provM_nec (nec_natCast _) h
    -- the axiom line `accF(⌜φ⌝) → provH(⌜φ⌝)`
    have h₂ : ProvM ((fcode (imp (box accF φ) (box provH φ)) : Nat) : N.Dom) :=
      provM_of_acc (acc_of_halts ((searchPA_spec _).2 ⟨_, rfl, accF_imp_provH φ⟩))
    -- modus ponens
    exact provM_mp (mpm_natCast _ _) h₂ h₁

/-- **The derivability conditions hold for `provH` over PA.** -/
theorem provH_derivability : Derivability PA provH :=
  ⟨fun _ h => provH_D1 h, provH_D2, provH_D3⟩

/-- `provH` and the formula `provPA` of `Lob` agree in the standard model: both define
PA-provability. -/
theorem provH_std_iff_provPA (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provH φ) ↔ Sat stdModel e (box provPA φ) := by
  rw [sat_provH, sat_provPA]

/-- **Löb's theorem for PA.** Unconditionally: if `PA ⊢ provH(⌜φ⌝) → φ`, then `PA ⊢ φ`. -/
theorem lob_PA {φ : Formula Arith} (h : PA ⊢₁ imp (box provH φ) φ) : PA ⊢₁ φ :=
  lob (fun _ h => PA_proves_Q h) provH_derivability h

/-- **Gödel's second incompleteness theorem for PA.** Unconditionally, PA does not prove
the consistency statement `¬provH(⌜⊥⌝)` for the provability formula `provH`, which defines
PA-provability in the standard model and satisfies (D1)–(D3) provably in PA.

Caveat (Gödel II is intensional, Feferman 1960): `provH` is not the textbook "there is a
PA-derivation of x"; its proofs are modus-ponens/necessitation closures of a Σ₁ listing of
PA's theorems, and PA-provable equivalence of `conF provH` with the canonical Con(PA) is not
established here. `provH` contains no consistency filter, so this is a genuine instance of
the Hilbert–Bernays–Löb form of the theorem, not a Feferman-style artefact (contrast
`GodelII.provF`, which has the same extension in `ℕ` but fails (D2) and has a PA-provable
consistency statement). For the derivation-based formula `provD`, Gödel II is reduced to
(D3) in `GodelII.godel_second_provD_of_D3`, and to `PA ⊢ provH(⌜⊥⌝) → provD(⌜⊥⌝)` in
`GodelII.godel_second_provD_of_dominates`; neither hypothesis is proved. -/
theorem godel_second_PA_unconditional : ¬ PA ⊢₁ conF provH :=
  godel_second (fun _ h => PA_proves_Q h) provH_derivability PA_consistent

end Foundations.Logic.FO
