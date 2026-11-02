import Foundations.Logic.GodelIIFeferman

/-!
# A derivation-based provability formula for PA: conditions (D1) and (D2)

Gödel (1931) arithmetised provability as "there is a number coding a *proof* — a finite
sequence of formulas each of which is an axiom or follows from earlier ones by a rule —
whose last formula is `x`". Hilbert and Bernays (1939) and Löb (1955) showed that the
second incompleteness theorem follows from three derivability conditions on such a
formula. Feferman (1960) stressed that the theorem is intensional: it is about *this kind*
of formula, not about any formula with the right extension (`GodelIIFeferman`).

The formula `provH` used for `godel_second_PA_unconditional` is *not* of Gödel's kind:
its "axioms" are all theorems of PA (as accepted by an opaque search program), and it
has a built-in necessitation rule. This file introduces a formula of Gödel's kind for the
proof calculus that the library actually uses for PA — natural deduction from (shifted)
PA axioms, arithmetised on Gödel numbers by the explicit decidable step relation
`paStep` of `PARules`:

  `provD(x)` :⇔ *there is a β-coded sequence of judgements `y₀, …, yₙ` with
  `yₙ = ⌜PA ⊢ x⌝ = ⟨0, ⟨0, x⟩⟩`, such that each `yₖ` follows by one rule of the calculus
  (`paStep ⟨yₖ, ⟨w, js⟩⟩ = true` for some witness `w` and coded list `js`) from premises
  all of which occur at earlier positions.*

"Occurring at earlier positions" is expressed by a second β-coded sequence, of the tails
`js = s₀, s₁, …, sₘ = 0` of the premise list, `sⱼ = ⟨aⱼ, sⱼ₊₁⟩ + 1`, each head `aⱼ`
being an earlier entry `y_p` (`p < k`). Everything is written with polynomial equations
and the β-relation, except the one-step test `paStep`, which enters through the Σ₁ graph
of a program computing it (this is how representability supplies such formulas; the
program is any one computing `paStep`, obtained from `paStep_comp`).

**What is proved.**
* `provD_D1`: if `PA ⊢ φ` then `PA ⊢ provD(⌜φ⌝)` — by transporting the external
  derivation into every model of PA, one rule at a time (`derM_step`);
* `provD_D2`: `PA ⊢ provD(⌜φ → ψ⌝) → (provD(⌜φ⌝) → provD(⌜ψ⌝))` — inside a model of
  PA, two derivations of non-standard length are concatenated and the conclusion is
  appended by →-elimination;
* (next file) `provD` defines PA-provability in `ℕ`, and Gödel II for `provD` follows
  from (D3) alone.

**What is not proved.** Condition (D3), `PA ⊢ provD(⌜φ⌝) → provD(⌜provD(⌜φ⌝)⌝)`, is
formalised Σ₁-completeness: inside a model of PA, from a derivation `p` (possibly
non-standard) one must build a derivation of the *sentence* asserting that `p` is a
derivation, with the numeral of `p` in it. That requires an arithmetisation of syntax
*inside* models of PA (numerals, substitution, derivations of true Δ₀ sentences by
internal induction), which this library does not contain.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability

/-! ## The one-step test as a Σ₁ formula -/

namespace GodelII

/-- A program computing the characteristic function of the step relation `paStep`. -/
noncomputable def stepCode : Code := paStep_comp.choose

/-- Specification of `stepCode`. -/
theorem stepCode_spec (q : Nat) : Eval stepCode [q] (paStep q).toNat := paStep_comp.choose_spec q

end GodelII

open GodelII

namespace PAModel

variable {N : PAModel}

/-- The one-step test in `N`: "`stepCode` outputs `1` on `q`", in the sense of `N`. -/
@[irreducible] def StepM (q : N.Dom) : Prop :=
  Sat N.M (Env.cons 1 (Env.cons q fun _ => 0)) (evalSigma stepCode)

/-- The step test is uniformly definable. -/
noncomputable def UDef.dstep {f : ∀ N : PAModel, (Nat → N.Dom) → N.Dom} (hf : UDefT f) :
    UDef fun N e => StepM (f N e) :=
  ⟨(evalSigma stepCode).subst (Env.cons (numeral 1) (Env.cons hf.t fun _ => numeral 0)),
    fun N e => by
      rw [sat_subst, StepM]
      have : (fun n => (Env.cons (numeral 1) (Env.cons hf.t fun _ => numeral 0) n).eval N.M e) =
          Env.cons (1 : N.Dom) (Env.cons (f N e) fun _ => (0 : N.Dom)) := by
        funext n; match n with
        | 0 => exact eval_numeral_M e 1
        | 1 => exact hf.spec N e
        | n + 2 => exact eval_numeral_M e 0
      rw [this]⟩

macro_rules | `(tactic| udfn_step) => `(tactic| apply PAModel.UDef.dstep)

/-- List construction in `N`: `s = ⟨a, t⟩ + 1` (the code of `a :: t`). -/
def LconsM (a t s : N.Dom) : Prop := ∃ u, PairM a t u ∧ s = u + 1

/-- **Premises occur earlier.** Every element of the list coded by `js` is an entry of the
sequence `(c, d)` at a position `< k`; witnessed by a β-coded sequence `(c', d')` of the
tails `js = s₀, …, sₘ = 0` of the list. -/
def PremsM (c d k js : N.Dom) : Prop :=
  ∃ c', ∃ d', ∃ m, BetaM c' d' 0 js ∧ BetaM c' d' m 0 ∧
    ∀ j, j < m → ∃ s, BetaM c' d' j s ∧ ∃ t, BetaM c' d' (j + 1) t ∧ ∃ a, LconsM a t s ∧
      ∃ p, p < k ∧ BetaM c d p a

/-- **A justified line.** The `k`-th entry `y` of `(c, d)` follows by one rule of the
calculus: `paStep ⟨y, ⟨w, js⟩⟩` holds and all premises listed in `js` occur earlier. -/
def DLineM (c d k : N.Dom) : Prop :=
  ∃ y, BetaM c d k y ∧ ∃ w, ∃ js, ∃ u, PairM w js u ∧ ∃ q, PairM y u q ∧ StepM q ∧
    PremsM c d k js

/-- A valid derivation code: all lines `0, …, n` are justified. -/
def DValid (c d n : N.Dom) : Prop := ∀ k, k ≤ n → DLineM c d k

/-- **Derivable judgement in `N`.** `y` is the last entry of a valid derivation code. -/
def DerM (y : N.Dom) : Prop := ∃ c, ∃ d, ∃ n, BetaM c d n y ∧ DValid c d n

/-- **PA-provability in `N`.** The judgement `⟨0, ⟨0, x⟩⟩` ("from PA, with no shifts and
no assumptions, derive `x`") is derivable. -/
def ProvDM (x : N.Dom) : Prop := ∃ u, PairM 0 x u ∧ ∃ y, PairM 0 u y ∧ DerM y

/-- The uniform definition of `ProvDM`. -/
noncomputable def provDDef : UDef fun N e => ProvDM (N := N) (e 0) := by
  unfold ProvDM DerM DValid DLineM PremsM LconsM PairM; udfn

end PAModel

open PAModel

/-- **The derivation-based provability formula of PA.** With free variable `0`: "there is
a sequence of judgements of the natural-deduction calculus for PA, each following from
earlier ones by a rule, ending with `PA ⊢ x`". -/
noncomputable def provD : Formula Arith := provDDef.φ

/-- **Meaning of `provD` in every model of PA.** -/
theorem sat_provD_M (N : PAModel) (e : Nat → N.Dom) : Sat N.M e provD ↔ ProvDM (e 0) :=
  provDDef.spec N e

/-- Meaning of `□_D φ := provD(⌜φ⌝)` in every model of PA. -/
theorem sat_box_provD (N : PAModel) (e : Nat → N.Dom) (φ : Formula Arith) :
    Sat N.M e (box provD φ) ↔ ProvDM ((fcode φ : Nat) : N.Dom) := by
  rw [box, sat_inst, sat_provD_M]
  exact Iff.of_eq (congrArg ProvDM (eval_numeral_M e _))

/-! ## Standard facts inside an arbitrary model -/

namespace PAModel

variable {N : PAModel}

/-- **Σ₁-completeness for the step test.** -/
theorem step_natCast {q : Nat} (h : paStep q = true) : StepM ((q : Nat) : N.Dom) := by
  have hev : Eval stepCode [q] 1 := by
    have := stepCode_spec q; rw [h] at this; exact this
  have := sat_of_Q_proves (Q_proves_eval hev) N.isQ (fun _ => 0)
  rw [sat_subst_numerals] at this
  rw [StepM]
  have e : (fun n => numM N.M (penv 1 q n)) =
      Env.cons (1 : N.Dom) (Env.cons ((q : Nat) : N.Dom) fun _ => 0) := by
    funext n; match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => simp [penv]; rfl
  rw [← e]; exact this

/-- **The β-relation for numerals.** A true instance of Gödel's β-function holds in `N`. -/
theorem betaM_natCast {A B i y : Nat} (h : gbeta A B i = y) :
    BetaM (A : N.Dom) (B : N.Dom) (i : N.Dom) (y : N.Dom) := by
  unfold gbeta at h
  have hm : 0 < 1 + (i + 1) * B := by omega
  have e₁ : A = A / (1 + (i + 1) * B) * (1 + (i + 1) * B) + y := by
    rw [← h]; exact (Nat.div_add_mod' A _).symm
  have e₂ : y + 1 + (1 + (i + 1) * B - y - 1) = 1 + (i + 1) * B := by
    have := Nat.mod_lt A hm; omega
  refine ⟨((A / (1 + (i + 1) * B) : Nat) : N.Dom), ?_, ?_⟩
  · have := congrArg (fun n : Nat => (n : N.Dom)) e₁
    simp only [natCast_add, natCast_mul, natCast_one] at this
    exact this
  · refine ⟨((1 + (i + 1) * B - y - 1 : Nat) : N.Dom), ?_⟩
    have := congrArg (fun n : Nat => (n : N.Dom)) e₂
    simp only [natCast_add, natCast_mul, natCast_one] at this
    exact this

/-- **Below a numeral there are only numerals.** -/
theorem lt_natCast_cases : ∀ (m : Nat) (j : N.Dom), j < (m : N.Dom) → ∃ j' : Nat, j' < m ∧ j = j'
  | 0, j, h => absurd h (not_lt_zero' j)
  | m + 1, j, h => by
    rw [natCast_add, natCast_one] at h
    rcases eq_or_lt_of_le (lt_succ_iff'.1 h) with rfl | h'
    · exact ⟨m, by omega, rfl⟩
    · obtain ⟨j', hj', rfl⟩ := lt_natCast_cases m j h'
      exact ⟨j', by omega, rfl⟩

/-- Cantor pairing in `N` determines the pair code. -/
theorem pairM_unique {a b p p' : N.Dom} (h : PairM a b p) (h' : PairM a b p') : p = p' := by
  unfold PairM at h h'
  rcases trichotomy p p' with hlt | heq | hlt
  · obtain ⟨z, rfl⟩ := hlt
    exact (add_succ_ne_self _ _ (by grind : p + p + (z + z + 1 + 1) = p + p)).elim
  · exact heq
  · obtain ⟨z, rfl⟩ := hlt
    exact (add_succ_ne_self _ _ (by grind : p' + p' + (z + z + 1 + 1) = p' + p')).elim

/-! ## Operations on derivation codes inside `N` -/

/-- **Transporting a justified line.** If the entries `0, …, j` of `(c₁, d₁)` reappear in
`(c, d)` at positions `s + p`, all of them before `K` for `p < j`, and the entry `j`
reappears at `K`, then a justified line `j` of `(c₁, d₁)` is a justified line `K` of
`(c, d)`. -/
theorem dline_transport {c₁ d₁ c d s j K : N.Dom}
    (hcopy : ∀ p y, p ≤ j → BetaM c₁ d₁ p y → BetaM c d (s + p) y)
    (hlt : ∀ p, p < j → s + p < K) (hK : ∀ y, BetaM c₁ d₁ j y → BetaM c d K y)
    (h : DLineM c₁ d₁ j) : DLineM c d K := by
  obtain ⟨y, hy, w, js, u, hu, q, hq, hs, c', d', m, h0, hm, hall⟩ := h
  refine ⟨y, hK y hy, w, js, u, hu, q, hq, hs, c', d', m, h0, hm, fun jj hjj => ?_⟩
  obtain ⟨s', hs', t, ht, a, ha, p, hp, hpa⟩ := hall jj hjj
  exact ⟨s', hs', t, ht, a, ha, s + p, hlt p hp, hcopy p a (le_of_lt' hp) hpa⟩

/-- Shifting a justified line by `s`. -/
theorem dline_shift {c₁ d₁ c d s n j : N.Dom}
    (hcopy : ∀ i y, i ≤ n → BetaM c₁ d₁ i y → BetaM c d (s + i) y) (hj : j ≤ n)
    (h : DLineM c₁ d₁ j) : DLineM c d (s + j) :=
  dline_transport (fun p y hp hy => hcopy p y (le_trans' hp hj) hy)
    (fun _ hp => add_lt_add_left'' s hp) (fun y hy => hcopy j y hj hy) h

/-- **Concatenating valid derivation codes**, with a further entry `v` at the end; the
result is valid once its last line is justified. -/
theorem dconcat {c₁ d₁ n₁ c₂ d₂ n₂ : N.Dom} (h₁ : DValid c₁ d₁ n₁) (h₂ : DValid c₂ d₂ n₂)
    (v : N.Dom) : ∃ c d, (∀ i y, i ≤ n₁ → BetaM c₁ d₁ i y → BetaM c d i y) ∧
      (∀ i y, i ≤ n₂ → BetaM c₂ d₂ i y → BetaM c d (n₁ + 1 + i) y) ∧
      BetaM c d (n₁ + n₂ + 2) v ∧ (DLineM c d (n₁ + n₂ + 2) → DValid c d (n₁ + n₂ + 2)) := by
  obtain ⟨c, d, -, hA, hB, hv⟩ := concat_exists c₁ d₁ n₁ c₂ d₂ n₂ v 0
  refine ⟨c, d, hA, hB, hv, fun hlast k hk => ?_⟩
  rcases le_or_lt' n₁ k with h | h
  · have := dline_shift (s := 0) (fun i y hi hy => by rw [zero_add']; exact hA i y hi hy) h
      (h₁ k h)
    rwa [zero_add'] at this
  · obtain ⟨j, rfl⟩ := exists_of_lt h
    rcases le_or_lt' n₂ j with hj | hj
    · have := dline_shift hB hj (h₂ j hj)
      rwa [show n₁ + 1 + j = n₁ + (j + 1) by grind] at this
    · obtain ⟨δ, rfl⟩ := exists_of_lt hj
      rcases zero_or_succ δ with rfl | ⟨δ', rfl⟩
      · rwa [show n₁ + (n₂ + (0 + 1) + 1) = n₁ + n₂ + 2 by grind]
      · obtain ⟨z, hz⟩ := hk
        exact absurd (by grind : (n₁ + n₂ + 2) + ((δ' + z) + 1) = n₁ + n₂ + 2)
          (add_succ_ne_self _ _)

/-- `y` occurs in `(c, d)` at a position `≤ n`. -/
def Occ (c d n y : N.Dom) : Prop := ∃ p, p ≤ n ∧ BetaM c d p y

/-- **Appending a derivation.** Given valid codes `(c₁, d₁, n₁)` and `(c₂, d₂, n₂)`, there
is a valid code in which every entry of either occurs. -/
theorem dappend {c₁ d₁ n₁ c₂ d₂ n₂ : N.Dom} (h₁ : DValid c₁ d₁ n₁) (h₂ : DValid c₂ d₂ n₂) :
    ∃ c d n, DValid c d n ∧ (∀ p y, p ≤ n₁ → BetaM c₁ d₁ p y → Occ c d n y) ∧
      (∀ p y, p ≤ n₂ → BetaM c₂ d₂ p y → Occ c d n y) := by
  obtain ⟨y₁, hy₁⟩ := betaM_exists c₁ d₁ n₁
  obtain ⟨c, d, hA, hB, hv, hval⟩ := dconcat h₁ h₂ y₁
  -- the last line is a copy of line `n₁`, whose premises lie before `n₁`
  have hlast : DLineM c d (n₁ + n₂ + 2) :=
    dline_transport (s := 0) (fun p y hp hy => by rw [zero_add']; exact hA p y hp hy)
      (fun p hp => by rw [zero_add']; exact lt_of_lt_of_le' hp ⟨n₂ + 2, by grind⟩)
      (fun y hy => by rw [betaM_unique hy hy₁]; exact hv) (h₁ n₁ (le_refl' _))
  refine ⟨c, d, _, hval hlast, fun p y hp hy => ⟨p, le_trans' hp ⟨n₂ + 2, by grind⟩, hA p y hp hy⟩,
    fun p y hp hy => ⟨n₁ + 1 + p, ?_, hB p y hp hy⟩⟩
  obtain ⟨z, rfl⟩ := hp
  exact ⟨z + 1, by grind⟩

/-- **Collecting derivations.** Starting from a valid code, derivations of all members of a
(standard) list of judgements can be added, keeping all old entries. -/
theorem dcollect : ∀ (l : List Nat), (∀ y ∈ l, DerM ((y : Nat) : N.Dom)) →
    ∀ c₁ d₁ n₁, DValid c₁ d₁ n₁ → ∃ c d n, DValid c d n ∧
      (∀ p y, p ≤ n₁ → BetaM c₁ d₁ p y → Occ c d n y) ∧ ∀ y ∈ l, Occ c d n ((y : Nat) : N.Dom)
  | [], _, c₁, d₁, n₁, h₁ => ⟨c₁, d₁, n₁, h₁, fun p _ hp hy => ⟨p, hp, hy⟩, by simp⟩
  | y :: l, hl, c₁, d₁, n₁, h₁ => by
    obtain ⟨c₂, d₂, n₂, hy, h₂⟩ := hl y (by simp)
    obtain ⟨c', d', n', h', hA, hB⟩ := dappend h₁ h₂
    obtain ⟨c, d, n, h, hA', hl'⟩ := dcollect l (fun z hz => hl z (by simp [hz])) c' d' n' h'
    refine ⟨c, d, n, h, fun p z hp hz => ?_, ?_⟩
    · obtain ⟨p', hp', hz'⟩ := hA p z hp hz; exact hA' p' z hp' hz'
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · obtain ⟨p', hp', hz'⟩ := hB n₂ _ (le_refl' _) hy; exact hA' p' _ hp' hz'
      · exact hl' z hz

/-- **Premise lists of numerals.** If every element of the standard list `l` occurs in
`(c, d)` before position `k`, then `PremsM c d k ⌜l⌝`. -/
theorem prems_natCast {c d k : N.Dom} (l : List Nat)
    (hocc : ∀ a ∈ l, ∃ p, p < k ∧ BetaM c d p ((a : Nat) : N.Dom)) :
    PremsM c d k ((encList l : Nat) : N.Dom) := by
  obtain ⟨A, B, hAB⟩ := beta_lemma l.length fun j => encList (l.drop j)
  refine ⟨(A : N.Dom), (B : N.Dom), (l.length : N.Dom), ?_, ?_, fun j hj => ?_⟩
  · exact betaM_natCast (by rw [hAB 0 (Nat.zero_le _)]; rfl)
  · exact betaM_natCast (by rw [hAB _ (Nat.le_refl _), List.drop_length]; rfl)
  · obtain ⟨j, hj', rfl⟩ := lt_natCast_cases _ j hj
    have hd : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj'
    refine ⟨((encList (l.drop j) : Nat) : N.Dom), betaM_natCast (hAB j (by omega)),
      ((encList (l.drop (j + 1)) : Nat) : N.Dom), ?_, ((l[j] : Nat) : N.Dom), ?_,
      hocc _ (List.getElem_mem hj')⟩
    · have := betaM_natCast (N := N) (hAB (j + 1) (by omega))
      rwa [natCast_add, natCast_one] at this
    · refine ⟨((pair l[j] (encList (l.drop (j + 1))) : Nat) : N.Dom), pairM_natCast _ _, ?_⟩
      rw [hd, encList, natCast_add, natCast_one]

/-- **A justified line from a true rule instance.** -/
theorem dline_of_step {c d k : N.Dom} {x w : Nat} {l : List Nat}
    (hstep : paStep (pair x (pair w (encList l))) = true) (hx : BetaM c d k ((x : Nat) : N.Dom))
    (hocc : ∀ a ∈ l, ∃ p, p < k ∧ BetaM c d p ((a : Nat) : N.Dom)) : DLineM c d k :=
  ⟨_, hx, (w : N.Dom), ((encList l : Nat) : N.Dom), _, pairM_natCast _ _, _, pairM_natCast _ _,
    step_natCast hstep, prems_natCast l hocc⟩

/-- **Closure under the rules.** If a rule instance `paStep ⟨x, ⟨w, ⌜l⌝⟩⟩` holds for
standard `x, w, l`, and every judgement in `l` is derivable in `N`, then so is `x`. -/
theorem derM_step {x w : Nat} {l : List Nat} (hstep : paStep (pair x (pair w (encList l))) = true)
    (hl : ∀ y ∈ l, DerM ((y : Nat) : N.Dom)) : DerM ((x : Nat) : N.Dom) := by
  cases l with
  | nil =>
    refine ⟨_, _, 0, betaM_single _, fun k hk => ?_⟩
    rw [eq_zero_of_le_zero hk]
    exact dline_of_step hstep (betaM_single _) (by simp)
  | cons y l =>
    obtain ⟨c₀, d₀, n₀, -, h₀⟩ := hl y (by simp)
    obtain ⟨c₁, d₁, n₁, h₁, -, hocc⟩ := dcollect (y :: l) hl c₀ d₀ n₀ h₀
    obtain ⟨c, d, hA, -, hv, hval⟩ := dconcat h₁ h₁ ((x : Nat) : N.Dom)
    refine ⟨c, d, _, hv, hval (dline_of_step hstep hv fun a ha => ?_)⟩
    obtain ⟨p, hp, hpa⟩ := hocc a ha
    exact ⟨p, lt_of_le_of_lt' hp ⟨n₁ + 1, by grind⟩, hA p _ hp hpa⟩

/-- **Every externally derivable judgement is derivable in `N`.** -/
theorem derM_of_derivable {z : Nat} (h : Derivable paRule z) : DerM ((z : Nat) : N.Dom) := by
  induction h with
  | intro x w l _ hstep ih => exact derM_step hstep ih

/-- The judgement code `⟨0, ⟨0, x⟩⟩` ("PA ⊢ x"). -/
theorem pj_zero_nil (x : Nat) : pj 0 (ccode []) x = pair 0 (pair 0 x) := rfl

/-- For standard `x`, `ProvDM x` is derivability of the judgement `⟨0, ⟨0, x⟩⟩`. -/
theorem provDM_natCast_iff (x : Nat) :
    ProvDM ((x : Nat) : N.Dom) ↔ DerM ((pj 0 (ccode []) x : Nat) : N.Dom) := by
  have h₁ : PairM (0 : N.Dom) (x : N.Dom) ((pair 0 x : Nat) : N.Dom) := pairM_natCast 0 x
  have h₂ : PairM (0 : N.Dom) ((pair 0 x : Nat) : N.Dom) ((pair 0 (pair 0 x) : Nat) : N.Dom) :=
    pairM_natCast 0 _
  constructor
  · rintro ⟨u, hu, y, hy, hd⟩
    rw [pairM_unique hu h₁] at hy
    rw [pairM_unique hy h₂] at hd
    exact hd
  · intro hd
    exact ⟨_, h₁, _, h₂, hd⟩

end PAModel

/-! ## The derivability conditions (D1) and (D2) -/

/-- **Condition (D1) for `provD`.** If `PA ⊢ φ` then `PA ⊢ provD(⌜φ⌝)`. -/
theorem provD_D1 {φ : Formula Arith} (h : PA ⊢₁ φ) : PA ⊢₁ box provD φ :=
  PA_proves_of_models fun N e => (sat_box_provD N e φ).2 ((provDM_natCast_iff _).2
    (derM_of_derivable ((derivable_iff_PA_proves φ).2 h)))

/-- The rule instance of →-elimination for PA-judgements. -/
theorem paStep_impE (φ ψ : Formula Arith) :
    paStep (pair (pj 0 (ccode []) (fcode ψ)) (pair (pair 3 (fcode φ))
      (encList [pj 0 (ccode []) (fcode (imp φ ψ)), pj 0 (ccode []) (fcode φ)]))) = true := by
  have : ruleC (pair (pj 0 (ccode []) (fcode ψ)) (pair (pair 3 (fcode φ))
      (encList [pj 0 (ccode []) (fcode (imp φ ψ)), pj 0 (ccode []) (fcode φ)]))) = true := by
    rw [ruleC_iff]; right; right; right; left
    rule_simp
  exact paRule_of_ruleC this

/-- **Condition (D2) for `provD`.** `PA ⊢ □_D(φ → ψ) → (□_D φ → □_D ψ)`: inside every model of
PA, derivations of `φ → ψ` and of `φ` combine into a derivation of `ψ`. -/
theorem provD_D2 (φ ψ : Formula Arith) :
    PA ⊢₁ imp (box provD (imp φ ψ)) (imp (box provD φ) (box provD ψ)) :=
  PA_proves_of_models fun N e => by
    simp only [Sat, sat_box_provD, provDM_natCast_iff]
    intro h₁ h₂
    refine derM_step (paStep_impE φ ψ) fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact h₁
    · exact h₂

end Foundations.Logic.FO
