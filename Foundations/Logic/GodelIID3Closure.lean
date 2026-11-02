import Foundations.Logic.GodelIID3Defs

/-!
# Closure properties of `provDP` inside models of PA; (D1) and (D2)

Inside an arbitrary model `N` of PA we show that `provDP`-derivable judgements are closed
under the three ways of justifying a line — for *arbitrary*, possibly non-standard,
elements of `N`, not only for standard ones:

* `derP_step`: one step of the calculus (for standard data, checked through `paStep`);
* `derP_mp`: modus ponens on judgements `PA ⊢ a`, `PA ⊢ b` with `a = ⟨2, ⟨b, r⟩⟩`;
* `derP_subst`: substitution of numerals, whenever the table relation `SubstM u r` holds.

The method is the one used for `provD` in `GodelIIDerivations`: concatenate β-coded
derivations of non-standard length (`concat_exists`) and append one justified line.
As consequences, `provDP` satisfies (D1) and (D2), and every `provD`-derivation is a
`provDP`-derivation (`provD_imp_provDP`).

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

/-- The judgement "PA ⊢ x", as a function: `J(x) = ⟨0, ⟨0, x⟩⟩`. -/
noncomputable def JN (x : N.Dom) : N.Dom := pairN 0 (pairN 0 x)

/-- `JM` is the graph of `JN`. -/
theorem jm_iff {x y : N.Dom} : JM x y ↔ y = JN x := by
  constructor
  · rintro ⟨a, ha, hy⟩; rw [pairM_iff] at ha hy; rw [hy, ha]; rfl
  · rintro rfl; exact ⟨_, pairN_spec 0 x, pairN_spec 0 _⟩

/-- `provDP`-provability is derivability of `J(x)`. -/
theorem provDPM_iff (x : N.Dom) : ProvDPM x ↔ DerP (JN x) := by
  constructor
  · rintro ⟨y, hy, hd⟩; rwa [jm_iff.1 hy] at hd
  · intro hd; exact ⟨_, jm_iff.2 rfl, hd⟩

/-- `J` on standard numbers. -/
theorem jn_cast (x : Nat) : JN ((x : Nat) : N.Dom) = ((pj 0 (ccode []) x : Nat) : N.Dom) := by
  unfold JN
  rw [show (0 : N.Dom) = ((0 : Nat) : N.Dom) from rfl, pairN_cast, pairN_cast]; rfl

/-- **Transporting a justified line** (as `dline_transport`, for `provDP`). -/
theorem dlineP_transport {c₁ d₁ c d s j K : N.Dom}
    (hcopy : ∀ p y, p ≤ j → BetaM c₁ d₁ p y → BetaM c d (s + p) y)
    (hlt : ∀ p, p < j → s + p < K) (hK : ∀ y, BetaM c₁ d₁ j y → BetaM c d K y)
    (h : DLineP c₁ d₁ j) : DLineP c d K := by
  obtain ⟨y, hy, hj⟩ := h
  refine ⟨y, hK y hy, ?_⟩
  rcases hj with ⟨w, js, u, hu, q, hq, hs, c', d', m, h0, hm, hall⟩ |
    ⟨i, hi, i', hi', a, b, r, yi, hyi, hai, yj, hyj, hbj, hr, p, hp, hp'⟩ |
    ⟨i, hi, u, yi, hyi, hui, r, hr, hsub⟩
  · refine Or.inl ⟨w, js, u, hu, q, hq, hs, c', d', m, h0, hm, fun jj hjj => ?_⟩
    obtain ⟨s', hs', t, ht, a, ha, p, hp, hpa⟩ := hall jj hjj
    exact ⟨s', hs', t, ht, a, ha, s + p, hlt p hp, hcopy p a (le_of_lt' hp) hpa⟩
  · exact Or.inr (Or.inl ⟨s + i, hlt i hi, s + i', hlt i' hi', a, b, r, yi,
      hcopy i yi (le_of_lt' hi) hyi, hai, yj, hcopy i' yj (le_of_lt' hi') hyj, hbj, hr, p, hp, hp'⟩)
  · exact Or.inr (Or.inr ⟨s + i, hlt i hi, u, yi, hcopy i yi (le_of_lt' hi) hyi, hui, r, hr, hsub⟩)

/-- Shifting a justified line by `s`. -/
theorem dlineP_shift {c₁ d₁ c d s n j : N.Dom}
    (hcopy : ∀ i y, i ≤ n → BetaM c₁ d₁ i y → BetaM c d (s + i) y) (hj : j ≤ n)
    (h : DLineP c₁ d₁ j) : DLineP c d (s + j) :=
  dlineP_transport (fun p y hp hy => hcopy p y (le_trans' hp hj) hy)
    (fun _ hp => add_lt_add_left'' s hp) (fun y hy => hcopy j y hj hy) h

/-- **Concatenating valid `provDP`-derivation codes**, with a further entry `v`. -/
theorem dconcatP {c₁ d₁ n₁ c₂ d₂ n₂ : N.Dom} (h₁ : DValidP c₁ d₁ n₁) (h₂ : DValidP c₂ d₂ n₂)
    (v : N.Dom) : ∃ c d, (∀ i y, i ≤ n₁ → BetaM c₁ d₁ i y → BetaM c d i y) ∧
      (∀ i y, i ≤ n₂ → BetaM c₂ d₂ i y → BetaM c d (n₁ + 1 + i) y) ∧
      BetaM c d (n₁ + n₂ + 2) v ∧ (DLineP c d (n₁ + n₂ + 2) → DValidP c d (n₁ + n₂ + 2)) := by
  obtain ⟨c, d, -, hA, hB, hv⟩ := concat_exists c₁ d₁ n₁ c₂ d₂ n₂ v 0
  refine ⟨c, d, hA, hB, hv, fun hlast k hk => ?_⟩
  rcases le_or_lt' n₁ k with h | h
  · have := dlineP_shift (s := 0) (fun i y hi hy => by rw [zero_add']; exact hA i y hi hy) h
      (h₁ k h)
    rwa [zero_add'] at this
  · obtain ⟨j, rfl⟩ := exists_of_lt h
    rcases le_or_lt' n₂ j with hj | hj
    · have := dlineP_shift hB hj (h₂ j hj)
      rwa [show n₁ + 1 + j = n₁ + (j + 1) by grind] at this
    · obtain ⟨δ, rfl⟩ := exists_of_lt hj
      rcases zero_or_succ δ with rfl | ⟨δ', rfl⟩
      · rwa [show n₁ + (n₂ + (0 + 1) + 1) = n₁ + n₂ + 2 by grind]
      · obtain ⟨z, hz⟩ := hk
        exact absurd (by grind : (n₁ + n₂ + 2) + ((δ' + z) + 1) = n₁ + n₂ + 2)
          (add_succ_ne_self _ _)

/-- **Appending a derivation**, keeping every entry of both. -/
theorem dappendP {c₁ d₁ n₁ c₂ d₂ n₂ : N.Dom} (h₁ : DValidP c₁ d₁ n₁) (h₂ : DValidP c₂ d₂ n₂) :
    ∃ c d n, DValidP c d n ∧ (∀ p y, p ≤ n₁ → BetaM c₁ d₁ p y → Occ c d n y) ∧
      (∀ p y, p ≤ n₂ → BetaM c₂ d₂ p y → Occ c d n y) := by
  obtain ⟨y₁, hy₁⟩ := betaM_exists c₁ d₁ n₁
  obtain ⟨c, d, hA, hB, hv, hval⟩ := dconcatP h₁ h₂ y₁
  have hlast : DLineP c d (n₁ + n₂ + 2) :=
    dlineP_transport (s := 0) (fun p y hp hy => by rw [zero_add']; exact hA p y hp hy)
      (fun p hp => by rw [zero_add']; exact lt_of_lt_of_le' hp ⟨n₂ + 2, by grind⟩)
      (fun y hy => by rw [betaM_unique hy hy₁]; exact hv) (h₁ n₁ (le_refl' _))
  refine ⟨c, d, _, hval hlast, fun p y hp hy => ⟨p, le_trans' hp ⟨n₂ + 2, by grind⟩, hA p y hp hy⟩,
    fun p y hp hy => ⟨n₁ + 1 + p, ?_, hB p y hp hy⟩⟩
  obtain ⟨z, rfl⟩ := hp
  exact ⟨z + 1, by grind⟩

/-- **Adding one justified line** after a valid code: if every extension of `(c, d, n)`
carrying `y` at position `n + n + 2` justifies that line, then `y` is derivable. -/
theorem derP_of_line {c d n y : N.Dom} (h : DValidP c d n)
    (hline : ∀ c' d', (∀ i z, i ≤ n → BetaM c d i z → BetaM c' d' i z) →
      BetaM c' d' (n + n + 2) y → DLineP c' d' (n + n + 2)) : DerP y := by
  obtain ⟨c', d', hA, -, hv, hval⟩ := dconcatP h h y
  exact ⟨c', d', _, hv, hval (hline c' d' hA hv)⟩

/-- Positions `≤ n` are below `n + n + 2`. -/
theorem lt_double_add_two {p n : N.Dom} (h : p ≤ n) : p < n + n + 2 :=
  lt_of_le_of_lt' h ⟨n + 1, by grind⟩

/-- **Modus ponens is admissible**, for arbitrary elements: from derivations of
`J(a)` and `J(b)` with `a = ⟨2, ⟨b, r⟩⟩` obtain a derivation of `J(r)`. -/
theorem derP_mp {a b r : N.Dom} (hab : a = pairN 2 (pairN b r)) (ha : DerP (JN a))
    (hb : DerP (JN b)) : DerP (JN r) := by
  obtain ⟨c₁, d₁, n₁, e₁, v₁⟩ := ha
  obtain ⟨c₂, d₂, n₂, e₂, v₂⟩ := hb
  obtain ⟨c, d, n, hv, hA, hB⟩ := dappendP v₁ v₂
  obtain ⟨pa, hpa, hpa'⟩ := hA n₁ _ (le_refl' _) e₁
  obtain ⟨pb, hpb, hpb'⟩ := hB n₂ _ (le_refl' _) e₂
  refine derP_of_line hv fun c' d' hcopy hy => ⟨_, hy, Or.inr (Or.inl ⟨pa,
    lt_double_add_two hpa, pb, lt_double_add_two hpb, a, b, r, _, hcopy _ _ hpa hpa',
    jm_iff.2 rfl, _, hcopy _ _ hpb hpb', jm_iff.2 rfl, jm_iff.2 rfl, _, pairN_spec b r, ?_⟩)⟩
  rw [hab]; exact pairN_spec _ _

/-- **Substitution of numerals is admissible**, for arbitrary elements. -/
theorem derP_subst {u r : N.Dom} (hs : SubstM u r) (hu : DerP (JN u)) : DerP (JN r) := by
  obtain ⟨c, d, n, e, v⟩ := hu
  exact derP_of_line v fun c' d' hcopy hy => ⟨_, hy, Or.inr (Or.inr ⟨n,
    lt_double_add_two (le_refl' n), u, _, hcopy _ _ (le_refl' n) e, jm_iff.2 rfl, r,
    jm_iff.2 rfl, hs⟩)⟩

/-- **Collecting derivations** of a standard list of judgements. -/
theorem dcollectP : ∀ (l : List Nat), (∀ y ∈ l, DerP ((y : Nat) : N.Dom)) →
    ∀ c₁ d₁ n₁, DValidP c₁ d₁ n₁ → ∃ c d n, DValidP c d n ∧
      (∀ p y, p ≤ n₁ → BetaM c₁ d₁ p y → Occ c d n y) ∧ ∀ y ∈ l, Occ c d n ((y : Nat) : N.Dom)
  | [], _, c₁, d₁, n₁, h₁ => ⟨c₁, d₁, n₁, h₁, fun p _ hp hy => ⟨p, hp, hy⟩, by simp⟩
  | y :: l, hl, c₁, d₁, n₁, h₁ => by
    obtain ⟨c₂, d₂, n₂, hy, h₂⟩ := hl y (by simp)
    obtain ⟨c', d', n', h', hA, hB⟩ := dappendP h₁ h₂
    obtain ⟨c, d, n, h, hA', hl'⟩ := dcollectP l (fun z hz => hl z (by simp [hz])) c' d' n' h'
    refine ⟨c, d, n, h, fun p z hp hz => ?_, ?_⟩
    · obtain ⟨p', hp', hz'⟩ := hA p z hp hz; exact hA' p' z hp' hz'
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · obtain ⟨p', hp', hz'⟩ := hB n₂ _ (le_refl' _) hy; exact hA' p' _ hp' hz'
      · exact hl' z hz

/-- An old-style justified line from a true rule instance. -/
theorem dlineP_of_step {c d k : N.Dom} {x w : Nat} {l : List Nat}
    (hstep : paStep (pair x (pair w (encList l))) = true) (hx : BetaM c d k ((x : Nat) : N.Dom))
    (hocc : ∀ a ∈ l, ∃ p, p < k ∧ BetaM c d p ((a : Nat) : N.Dom)) : DLineP c d k :=
  ⟨_, hx, Or.inl ⟨(w : N.Dom), ((encList l : Nat) : N.Dom), _, pairM_natCast _ _, _,
    pairM_natCast _ _, step_natCast hstep, prems_natCast l hocc⟩⟩

/-- **Closure under the steps of the calculus** (standard data). -/
theorem derP_step {x w : Nat} {l : List Nat} (hstep : paStep (pair x (pair w (encList l))) = true)
    (hl : ∀ y ∈ l, DerP ((y : Nat) : N.Dom)) : DerP ((x : Nat) : N.Dom) := by
  cases l with
  | nil =>
    refine ⟨_, _, 0, betaM_single _, fun k hk => ?_⟩
    rw [eq_zero_of_le_zero hk]
    exact dlineP_of_step hstep (betaM_single _) (by simp)
  | cons y l =>
    obtain ⟨c₀, d₀, n₀, -, h₀⟩ := hl y (by simp)
    obtain ⟨c₁, d₁, n₁, h₁, -, hocc⟩ := dcollectP (y :: l) hl c₀ d₀ n₀ h₀
    refine derP_of_line h₁ fun c' d' hcopy hy => dlineP_of_step hstep hy fun a ha => ?_
    obtain ⟨p, hp, hpa⟩ := hocc a ha
    exact ⟨p, lt_double_add_two hp, hcopy p _ hp hpa⟩

/-- **Every externally derivable judgement is `provDP`-derivable in `N`.** -/
theorem derP_of_derivable {z : Nat} (h : Derivable paRule z) : DerP ((z : Nat) : N.Dom) := by
  induction h with
  | intro x w l _ hstep ih => exact derP_step hstep ih

/-- **Theorems of PA are internally derivable**: `J(⌜φ⌝)` is `provDP`-derivable. -/
theorem derP_of_proves {φ : Formula Arith} (h : PA ⊢₁ φ) : DerP (JN ((fcode φ : Nat) : N.Dom)) := by
  rw [jn_cast]; exact derP_of_derivable ((derivable_iff_PA_proves φ).2 h)

/-- Every `provD`-line is a `provDP`-line. -/
theorem dlineP_of_dlineM {c d k : N.Dom} (h : DLineM c d k) : DLineP c d k := by
  obtain ⟨y, hy, w, js, u, hu, q, hq, hs, hp⟩ := h
  exact ⟨y, hy, Or.inl ⟨w, js, u, hu, q, hq, hs, hp⟩⟩

/-- Every `provD`-provable code is `provDP`-provable. -/
theorem provDPM_of_provDM {x : N.Dom} (h : ProvDM x) : ProvDPM x := by
  obtain ⟨u, hu, y, hy, c, d, n, hn, hv⟩ := h
  exact ⟨y, ⟨u, hu, hy⟩, c, d, n, hn, fun k hk => dlineP_of_dlineM (hv k hk)⟩

end PAModel

open PAModel

/-- **Condition (D1) for `provDP`.** -/
theorem provDP_D1 {φ : Formula Arith} (h : PA ⊢₁ φ) : PA ⊢₁ box provDP φ :=
  PA_proves_of_models fun N e => (sat_box_provDP N e φ).2 ((provDPM_iff _).2 (derP_of_proves h))

/-- The code of an implication, inside a model. -/
theorem fcode_imp_cast {N : PAModel} (φ ψ : Formula Arith) :
    ((fcode (imp φ ψ) : Nat) : N.Dom) =
      pairN 2 (pairN ((fcode φ : Nat) : N.Dom) ((fcode ψ : Nat) : N.Dom)) :=
  (pairN_tag 2 _ _).symm

/-- **Condition (D2) for `provDP`.** -/
theorem provDP_D2 (φ ψ : Formula Arith) :
    PA ⊢₁ imp (box provDP (imp φ ψ)) (imp (box provDP φ) (box provDP ψ)) :=
  PA_proves_of_models fun N e => by
    simp only [Sat, sat_box_provDP, provDPM_iff]
    exact fun h₁ h₂ => derP_mp (fcode_imp_cast φ ψ) h₁ h₂

/-- **`provD` implies `provDP`, uniformly**: `PA ⊢ provD(x) → provDP(x)`. -/
theorem provD_imp_provDP : PA ⊢₁ imp provD provDP :=
  PA_proves_of_models fun N e => by
    simp only [Sat, sat_provD_M, sat_provDP_M]
    exact provDPM_of_provDM

end Foundations.Logic.FO
