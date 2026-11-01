import Foundations.Logic.DiagonalLemma

/-!
# The Gödel–Rosser incompleteness theorem

Gödel's own 1931 theorem needed more than the consistency of the theory: it assumed
*ω-consistency* (and our version in `Incompleteness` even assumed soundness, i.e.
truth in `ℕ`). J. Barkley **Rosser** (1936) removed this blemish:

> **Every consistent, computably enumerable theory `T` containing Robinson's `Q` is
> incomplete**: there is a sentence `σ` such that `T` proves neither `σ` nor `¬σ`.

No truth, no ω-consistency — just consistency. In particular this holds for PA,
assuming only that PA is consistent.

We give a computational proof in the style of Kleene's *recursively inseparable
sets*. For each program number `e`, let `R(e)` be the **Rosser sentence**

`∃w ( φₑ(e) = 0 within w  ∧  ∀u ≤ w ¬(φₑ(e) = 1 within u) )`

("a computation of `φₑ(e)` with output `0` appears no later than any with output
`1`"). By the Rosser separation lemma of `Representability`:

* if `φₑ(e) = 0`, then `Q ⊢ R(e)`;
* if `φₑ(e) = 1`, then `Q ⊢ ¬R(e)`.

Now let `d` be the program which, on input `e`, enumerates the theorems of `T`
(possible, since `T` is c.e., by Kleene's normal form) until it finds a proof of
`R(e)` or of `¬R(e)`, and outputs `1` in the first case and `0` in the second — *doing
the opposite of what `T` predicts*. Consider `σ := R(⌜d⌝)`. If `T` decided `σ`, then
`d` would halt on its own number: if it found a proof of `σ` it outputs `1`, so
`φ_{⌜d⌝}(⌜d⌝) = 1` and `Q` — hence `T` — proves `¬σ`; if it found a proof of `¬σ` it
outputs `0`, so `T` proves `σ`. Either way `T` is inconsistent.

*The second incompleteness theorem* is not proved in this file. It needs (1) a formula
`Prov(x)` expressing PA-provability *inside* PA and (2) the **Hilbert–Bernays–Löb
derivability conditions**, above all `PA ⊢ Prov(⌜φ⌝) → Prov(⌜Prov(⌜φ⌝)⌝)`. Both are
supplied later: `DerivabilityConditions.lean` verifies (D1)–(D3) for a Hilbert-style
provability formula `provH` and proves Gödel II in Hilbert–Bernays–Löb form
(`godel_second_PA_unconditional : ¬ PA ⊢₁ conF provH`), and `Lob.lean` gives Löb's
theorem. Caveat: `conF provH` is not shown to be PA-provably equivalent to the textbook
consistency sentence Con(PA) built from another arithmetisation of proofs.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

open Arith Formula Computability

/-! ## The Rosser sentences -/

/-- The bounded formula "`φₓ(x) = k` within the bound `w`" (free variables `0 = w`,
`1 = x`), from the bounded graph of the universal code. -/
noncomputable def outU (k : Nat) : Formula Arith :=
  (grb U 2).subst (Env.cons (numeral k) (Env.cons (v 1) (Env.cons (v 1) fun _ => v 0)))

/-- `outU` is bounded. -/
theorem outU_D0 (k : Nat) : D0 (outU k) := (grb_D0 U 2).subst _

/-- Meaning of `outU`. -/
theorem holds_outU (k w n : Nat) : holds (outU k) w n ↔ EvalB w U [n, n] k := by
  rw [holds, outU, sat_subst, sat_grb]
  simp [penv, Env.cons, List.ofFn_succ, eval_numeral_std]

/-- `outU k` has free variables among `0, 1`. -/
theorem outU_fresh (k : Nat) : ∀ n, 2 ≤ n → (outU k).Fresh n := by
  intro n hn
  refine Formula.fresh_subst_of _ fun m _ => ?_
  match m with
  | 0 => exact numeral_fresh _ _
  | 1 => exact var_fresh (by omega)
  | 2 => exact var_fresh (by omega)
  | m + 3 => exact var_fresh (by omega)

/-- The Rosser formula `R(x)`. -/
noncomputable def rosserF : Formula Arith := sepF (outU 0) (outU 1)

/-- **The Rosser sentence** `R(e)` for the program number `e`. -/
noncomputable def rosserSent (e : Nat) : Formula Arith := rosserF.inst (numeral e)

/-- The Rosser sentences are sentences. -/
theorem rosserSent_sentence (e : Nat) : IsSentence (rosserSent e) :=
  inst_sentence (sepF_fresh (outU_fresh 0) (outU_fresh 1)) (numeral_fresh · e)

/-- Outputs `0` and `1` exclude each other. -/
theorem outU_disjoint : ∀ n w u, holds (outU 0) w n → holds (outU 1) u n → False := by
  intro n w u h₀ h₁
  rw [holds_outU] at h₀ h₁
  exact absurd (Eval.det h₀.sound h₁.sound) (by omega)

/-- If `φₑ(e) = 0`, then `Q ⊢ R(e)`. -/
theorem Q_proves_rosser {e : Nat} (h : phi e e 0) : Q ⊢₁ rosserSent e := by
  refine (rosser_sep (outU_D0 0) (outU_D0 1) outU_disjoint e).1 ?_
  obtain ⟨w, hw⟩ := EvalB.complete h
  exact ⟨w, (holds_outU 0 w e).2 hw⟩

/-- If `φₑ(e) = 1`, then `Q ⊢ ¬R(e)`. -/
theorem Q_refutes_rosser {e : Nat} (h : phi e e 1) : Q ⊢₁ neg (rosserSent e) := by
  refine (rosser_sep (outU_D0 0) (outU_D0 1) outU_disjoint e).2 ?_
  obtain ⟨w, hw⟩ := EvalB.complete h
  exact ⟨w, (holds_outU 1 w e).2 hw⟩

/-! ## Codes of the Rosser sentences -/

/-- The Gödel number of `R(e)`. -/
noncomputable def rcode (e : Nat) : Nat := instC (fcode rosserF) (ncode e)

/-- Correctness of `rcode`. -/
theorem rcode_spec (e : Nat) : rcode e = fcode (rosserSent e) := by
  rw [rcode, ncode, instC_fcode]; rfl

/-- The Gödel number of `¬R(e)`. -/
noncomputable def nrcode (e : Nat) : Nat := pair 2 (pair (rcode e) 0)

/-- Correctness of `nrcode`. -/
theorem nrcode_spec (e : Nat) : nrcode e = fcode (neg (rosserSent e)) := by
  rw [nrcode, rcode_spec, fcode_neg]

/-- `rcode` is computable. -/
theorem rcode_comp {f : Nat → Nat} (hf : Comp f) : Comp fun n => rcode (f n) :=
  Comp.instC (Comp.const _) (Comp.comp Comp.ncode hf)

/-- `nrcode` is computable. -/
theorem nrcode_comp {f : Nat → Nat} (hf : Comp f) : Comp fun n => nrcode (f n) :=
  Comp.pair (Comp.const 2) (Comp.pair (rcode_comp hf) (Comp.const 0))

/-- Coded one-element lists are computable. -/
theorem encList_single_comp {f : Nat → Nat} (hf : Comp f) : Comp fun n => encList [f n] :=
  Comp.congr (Comp.succ (Comp.pair hf (Comp.const 0))) fun _ => rfl

/-- Halting via the T-predicate. -/
theorem halts_iff_kleeneT (c : Code) (m : Nat) :
    Halts c [m] ↔ ∃ t, kleeneT (encode c) (encList [m]) t = true := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨t, ht, -⟩ := (kleene_normal_form c [m] n).1 hn
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨traceOut t, (kleene_normal_form c [m] _).2 ⟨t, ht, rfl⟩⟩

/-! ## The theorem -/

/-- **The Gödel–Rosser incompleteness theorem.** Let `T` be a theory of arithmetic
which proves all axioms of `Q`, is computably enumerable (some code halts exactly on
the Gödel numbers of its theorems), and is **consistent**. Then `T` is incomplete:
some sentence is neither provable nor refutable in `T`. -/
theorem rosser_incompleteness {T : Theory Arith} (hQ : ∀ ψ, Q ψ → T ⊢₁ ψ)
    (hce : ∃ c : Code, ∀ φ : Formula Arith, Halts c [fcode φ] ↔ T ⊢₁ φ) (hcon : ¬ T ⊢₁ bot) :
    ∃ σ : Formula Arith, IsSentence σ ∧ ¬ T ⊢₁ σ ∧ ¬ T ⊢₁ neg σ := by
  obtain ⟨cT, hcT⟩ := hce
  let K : Nat := encode cT
  -- "proof of `R(e)` (resp. `¬R(e)`) found at stage `t`"
  let t₁ : Nat → Bool := fun q => kleeneT K (encList [rcode (fst q)]) (snd q)
  let t₂ : Nat → Bool := fun q => kleeneT K (encList [nrcode (fst q)]) (snd q)
  have ht₁ : CompB t₁ := CompB.step3 kleeneT_comp (Comp.const K)
    (encList_single_comp (rcode_comp (Comp.fst Comp.id))) (Comp.snd Comp.id)
  have ht₂ : CompB t₂ := CompB.step3 kleeneT_comp (Comp.const K)
    (encList_single_comp (nrcode_comp (Comp.fst Comp.id))) (Comp.snd Comp.id)
  obtain ⟨cs, hcs⟩ := search (CompB.or ht₁ ht₂)
  obtain ⟨co, hco⟩ := Comp.cond ht₁ (Comp.const 1) (Comp.const 0)
  -- the program `d`
  let d : Code := .comp co (vec1 (pairOf (.proj 0) cs))
  have hd : ∀ n t, Eval cs [n] t → Eval d [n] (bif t₁ (pair n t) then 1 else 0) :=
    fun n t ht => eval_comp1 (eval_pairOf .proj ht) (hco _)
  let g := encode d
  let σ := rosserSent g
  have hT₁ : ∀ t, t₁ (pair g t) = true → T ⊢₁ σ := by
    intro t ht
    rw [← hcT, ← rcode_spec, halts_iff_kleeneT]
    exact ⟨t, by simpa [t₁] using ht⟩
  have hT₂ : ∀ t, t₂ (pair g t) = true → T ⊢₁ neg σ := by
    intro t ht
    rw [← hcT, ← nrcode_spec, halts_iff_kleeneT]
    exact ⟨t, by simpa [t₂] using ht⟩
  have key : (T ⊢₁ σ ∨ T ⊢₁ neg σ) → T ⊢₁ bot := by
    intro h
    have hex : ∃ t, (t₁ (pair g t) || t₂ (pair g t)) = true := by
      rcases h with h | h
      · rw [← hcT, ← rcode_spec, halts_iff_kleeneT] at h
        obtain ⟨t, ht⟩ := h
        have h' : t₁ (pair g t) = true := by simpa [t₁] using ht
        exact ⟨t, by rw [h']; rfl⟩
      · rw [← hcT, ← nrcode_spec, halts_iff_kleeneT] at h
        obtain ⟨t, ht⟩ := h
        have h' : t₂ (pair g t) = true := by simpa [t₂] using ht
        exact ⟨t, by rw [h', Bool.or_true]⟩
    obtain ⟨t₀, ht₀, hmin⟩ := exists_least hex
    have hs : Eval cs [g] t₀ := (hcs g t₀).2 ⟨by simpa using ht₀, fun m hm => by
      simpa using hmin m hm⟩
    have hdg := hd g t₀ hs
    cases h₁ : t₁ (pair g t₀) with
    | true =>
        rw [h₁] at hdg
        have hphi : phi g g 1 := (phi_encode d g 1).2 hdg
        exact Proves.impE (proves_of_Q_proves hQ (Q_refutes_rosser hphi)) (hT₁ t₀ h₁)
    | false =>
        rw [h₁] at hdg
        have h₂ : t₂ (pair g t₀) = true := by simpa [h₁] using ht₀
        have hphi : phi g g 0 := (phi_encode d g 0).2 hdg
        exact Proves.impE (hT₂ t₀ h₂) (proves_of_Q_proves hQ (Q_proves_rosser hphi))
  exact ⟨σ, rosserSent_sentence g, fun h => hcon (key (Or.inl h)), fun h => hcon (key (Or.inr h))⟩

/-- **Gödel–Rosser for PA**: if PA is consistent, it is incomplete — no soundness or
ω-consistency assumption is needed. -/
theorem PA_rosser (hcon : ¬ PA ⊢₁ bot) :
    ∃ σ : Formula Arith, IsSentence σ ∧ ¬ PA ⊢₁ σ ∧ ¬ PA ⊢₁ neg σ :=
  rosser_incompleteness (fun _ h => PA_proves_Q h) PA_theorems_ce hcon

/-- PA is incomplete (combining Gödel–Rosser with the consistency of PA relative to
Lean, `PA_consistent`). -/
theorem PA_incomplete_rosser :
    ∃ σ : Formula Arith, IsSentence σ ∧ ¬ PA ⊢₁ σ ∧ ¬ PA ⊢₁ neg σ :=
  PA_rosser PA_consistent

end Foundations.Logic.FO
