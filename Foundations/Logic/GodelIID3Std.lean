import Foundations.Logic.GodelIID3Closure

/-!
# `provDP` in the standard model

The two new ways of justifying a line in a `provDP`-derivation are *sound*: in `ℕ`, a
substitution table computes a genuine substitution instance (`substM_std_sound`), and a
modus-ponens line follows by →-elimination. Hence every `provDP`-derivation in `ℕ` yields
a derivation in the rule system `Derivable paRule` (`derP_std_sound`), and `provDP`
defines PA-provability in `ℕ` (`sat_provDP`), like `provD` and `provH`.

*Place in the argument.* Gödel (1931) only sketched the second incompleteness theorem;
Hilbert and Bernays (1939) carried out the arithmetisation it needs; Löb (1955) reduced it to
three derivability conditions, of which (D3) — formalised Σ₁-completeness — is the hard one.
Feferman (1960) showed that the theorem depends on how provability is expressed, which is why
it matters that `provDP` is a derivation predicate rather than one engineered to satisfy (D3).
This file is one step of the proof of (D3) for `provDP` assembled in `GodelIID3Main`.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability GodelII PAModel

namespace GodelII

/-- `0 ≠ 1` in a model of PA. -/
theorem zero_ne_one_M {N : PAModel} : (0 : N.Dom) ≠ 1 := fun h =>
  succ_ne_zero' (0 : N.Dom) (by rw [← ms_eq]; exact h.symm)

/-- Pairing in the standard model. -/
theorem pairM_std {a b p : Nat} (h : PairM (N := stdPA) a b p) : p = pair a b := stdPA_pairM h

/-- Table entries in `ℕ` are determined by their code. -/
theorem quad_std {u dp r s x : Nat} (h : Quad (N := stdPA) u dp r s x) :
    x = pair u (pair dp (pair r s)) := by
  obtain ⟨q, hq, p, hp, hx⟩ := h
  rw [pairM_std hx, pairM_std hp, pairM_std hq]

/-- `tri m ≠ 2`, so no variable code is the code `2` of `0`. -/
theorem tri_ne_two : ∀ m, Computability.tri m ≠ 2
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
    have := le_tri (m + 2)
    have h3 : Computability.tri (m + 2) ≥ 3 := by
      simp only [Computability.tri]; have := le_tri m; omega
    omega

/-- Codes with tag `≥ 2` exceed `2`. -/
theorem two_lt_pair {k b : Nat} (hk : 2 ≤ k) : 2 < pair k b := by
  have := le_tri (k + b); unfold pair; omega

/-- Codes with positive tag are positive. -/
theorem pos_pair {k b : Nat} (hk : 1 ≤ k) : 0 < pair k b := by
  have := Computability.left_le_pair k b; omega

section Table

variable (lc ld tc td L : stdPA.Dom)

/-- The values listed by `(lc, ld)` in `ℕ`. -/
noncomputable def valStd (m : Nat) : Nat := (betaM_exists (N := stdPA) lc ld m).choose

/-- The substitution described by the value list `(lc, ld)`. -/
noncomputable def σStd : Nat → Term Arith := fun m => numeral (valStd lc ld m)

/-- All entries of the table `(tc, td, L)` are locally correct. -/
def TableOK : Prop := ∀ u dp r s : stdPA.Dom, Entry tc td L u dp r s →
  (s = 0 ∧ TermOK lc ld tc td L u dp r) ∨ (s = 1 ∧ FormOK tc td L u dp r)

variable {lc ld tc td L}

/-- A term entry of a correct table is term-correct. -/
theorem termOK_of (hok : TableOK lc ld tc td L) {u dp r : stdPA.Dom}
    (hE : Entry tc td L u dp r 0) : TermOK lc ld tc td L u dp r := by
  rcases hok _ _ _ _ hE with ⟨-, hT⟩ | ⟨hs, -⟩
  · exact hT
  · exact absurd hs zero_ne_one_M

/-- A formula entry of a correct table is formula-correct. -/
theorem formOK_of (hok : TableOK lc ld tc td L) {u dp r : stdPA.Dom}
    (hE : Entry tc td L u dp r 1) : FormOK tc td L u dp r := by
  rcases hok _ _ _ _ hE with ⟨hs, -⟩ | ⟨-, hF⟩
  · exact absurd hs.symm zero_ne_one_M
  · exact hF

/-- Term entries of a correct table in `ℕ` compute substitution instances. -/
theorem term_sound (hok : TableOK lc ld tc td L) : ∀ (t : Term Arith) (dp r : stdPA.Dom),
    Entry tc td L (tcode t) dp r 0 → @Eq Nat r (tcode (t.subst (liftN dp (σStd lc ld))))
  | .var m₀, dp, r, hE => by
    have hT := termOK_of hok hE
    rcases hT with ⟨m, hm, hc⟩ | ⟨hu2, -⟩ | ⟨u₁, hu₁, -⟩ | ⟨k, hk, p, hp, -⟩
    · have e := pairM_std hm
      simp only [tcode, pair_eq_pair] at e
      obtain ⟨-, rfl⟩ := e
      rcases hc with ⟨hlt, hr⟩ | ⟨m', hm', w, hw, hn⟩
      · have hlt' : (m₀ : Nat) < dp := stdPA_lt.1 hlt
        rw [hr]; simp [Term.subst, liftN_apply, hlt']
      · have hm'' : @Eq Nat (dp + m') m₀ := hm'
        have hn' : @Eq Nat r (ncode w) := by
          have h1 := numM_iff.1 hn
          have h2 := numN_cast (N := stdPA) w
          rw [stdPA_cast, stdPA_cast] at h2
          rw [h1]; exact h2
        have hw' : w = valStd lc ld m' := betaM_unique hw
          (betaM_exists (N := stdPA) lc ld m').choose_spec
        simp only [Term.subst, liftN_apply, show ¬ (m₀ : Nat) < dp by omega, ite_false,
          σStd, numeral_rename, show (m₀ : Nat) - dp = m' by omega, ← hw', hn', ncode]
    · have e : @Eq Nat (tcode (Term.var m₀)) 2 := hu2
      exact absurd e (by simp only [tcode, pair, Nat.zero_add, Nat.add_zero]; exact tri_ne_two _)
    · have e := pairM_std hu₁
      simp only [tcode, pair_eq_pair] at e; omega
    · have e := pairM_std hp
      have hk' : @Eq Nat k 3 ∨ @Eq Nat k 4 := hk
      simp only [tcode, pair_eq_pair] at e; omega
  | .func ArithFunc.zero ts, dp, r, hE => by
    have hT := termOK_of hok hE
    rcases hT with ⟨m, hm, -⟩ | ⟨-, hr2⟩ | ⟨u₁, hu₁, -⟩ | ⟨k, hk, p, hp, -⟩
    · have e := pairM_std hm
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
    · have e : @Eq Nat r 2 := hr2
      rw [e]; rfl
    · have e := pairM_std hu₁
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
    · have e := pairM_std hp
      have hk' : @Eq Nat k 3 ∨ @Eq Nat k 4 := hk
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
  | .func ArithFunc.succ ts, dp, r, hE => by
    have hT := termOK_of hok hE
    rcases hT with ⟨m, hm, -⟩ | ⟨hu2, -⟩ | ⟨u₁, hu₁, r₁, hr₁, hE₁⟩ | ⟨k, hk, p, hp, -⟩
    · have e := pairM_std hm
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
    · have e : @Eq Nat (tcode (Term.func ArithFunc.succ ts)) 2 := hu2
      simp only [tcode, funcCode] at e
      exact absurd e (Nat.ne_of_gt (two_lt_pair (Nat.le_refl 2)))
    · have e := pairM_std hu₁
      simp only [tcode, funcCode, pair_eq_pair] at e
      obtain ⟨-, e⟩ := e
      rw [← e] at hE₁
      have ih := term_sound hok (ts 0) dp r₁ hE₁
      rw [pairM_std hr₁, ih]; rfl
    · have e := pairM_std hp
      have hk' : @Eq Nat k 3 ∨ @Eq Nat k 4 := hk
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
  | .func ArithFunc.add ts, dp, r, hE => by
    have hT := termOK_of hok hE
    rcases hT with ⟨m, hm, -⟩ | ⟨hu2, -⟩ | ⟨u₁, hu₁, -⟩ |
      ⟨k, hk, p, hp, u₁, u₂, hu, q, hq, r₁, r₂, hr, hE₁, hE₂⟩
    · have e := pairM_std hm
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
    · have e : @Eq Nat (tcode (Term.func ArithFunc.add ts)) 2 := hu2
      simp only [tcode, funcCode] at e
      exact absurd e (Nat.ne_of_gt (two_lt_pair (by omega)))
    · have e := pairM_std hu₁
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
    · have e := pairM_std hp
      have hk' : @Eq Nat k 3 ∨ @Eq Nat k 4 := hk
      simp only [tcode, funcCode, pair_eq_pair] at e
      obtain ⟨ek, e⟩ := e
      rw [pairM_std hu, pair_eq_pair] at e
      obtain ⟨e₁, e₂⟩ := e
      rw [← e₁] at hE₁; rw [← e₂] at hE₂
      rw [pairM_std hq, pairM_std hr, term_sound hok (ts 0) dp r₁ hE₁,
        term_sound hok (ts 1) dp r₂ hE₂, ← ek]; rfl
  | .func ArithFunc.mul ts, dp, r, hE => by
    have hT := termOK_of hok hE
    rcases hT with ⟨m, hm, -⟩ | ⟨hu2, -⟩ | ⟨u₁, hu₁, -⟩ |
      ⟨k, hk, p, hp, u₁, u₂, hu, q, hq, r₁, r₂, hr, hE₁, hE₂⟩
    · have e := pairM_std hm
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
    · have e : @Eq Nat (tcode (Term.func ArithFunc.mul ts)) 2 := hu2
      simp only [tcode, funcCode] at e
      exact absurd e (Nat.ne_of_gt (two_lt_pair (by omega)))
    · have e := pairM_std hu₁
      simp only [tcode, funcCode, pair_eq_pair] at e; omega
    · have e := pairM_std hp
      have hk' : @Eq Nat k 3 ∨ @Eq Nat k 4 := hk
      simp only [tcode, funcCode, pair_eq_pair] at e
      obtain ⟨ek, e⟩ := e
      rw [pairM_std hu, pair_eq_pair] at e
      obtain ⟨e₁, e₂⟩ := e
      rw [← e₁] at hE₁; rw [← e₂] at hE₂
      rw [pairM_std hq, pairM_std hr, term_sound hok (ts 0) dp r₁ hE₁,
        term_sound hok (ts 1) dp r₂ hE₂, ← ek]; rfl

/-- The binary-connective case of `form_sound`. -/
theorem form_bin (hok : TableOK lc ld tc td L) (k : Nat) (hk : 2 ≤ k ∧ k ≤ 4)
    (A B φ : Formula Arith) (hφ : fcode φ = pair k (pair (fcode A) (fcode B)))
    (hs : ∀ σ, @Eq Nat (fcode (φ.subst σ)) (pair k (pair (fcode (A.subst σ)) (fcode (B.subst σ)))))
    (dp r : stdPA.Dom) (hE : Entry tc td L (fcode φ) dp r 1)
    (ihA : ∀ dp r : stdPA.Dom, Entry tc td L (fcode A) dp r 1 →
      @Eq Nat r (fcode (A.subst (liftN dp (σStd lc ld)))))
    (ihB : ∀ dp r : stdPA.Dom, Entry tc td L (fcode B) dp r 1 →
      @Eq Nat r (fcode (B.subst (liftN dp (σStd lc ld))))) :
    @Eq Nat r (fcode (φ.subst (liftN dp (σStd lc ld)))) := by
  rw [hφ] at hE
  rw [hs]
  rcases formOK_of hok hE with ⟨hu, -⟩ | ⟨p, hp, -⟩ |
    ⟨k', hk', p, hp, u₁, u₂, hu, q, hq, r₁, r₂, hr, hE₁, hE₂⟩ | ⟨k', hk', u₁, hu₁, -⟩
  · have e : @Eq Nat (pair k (pair (fcode A) (fcode B))) 0 := hu
    exact absurd e (Nat.ne_of_gt (pos_pair (by omega)))
  · have e := pairM_std hp; rw [pair_eq_pair] at e; omega
  · have e := pairM_std hp
    rw [pair_eq_pair] at e
    obtain ⟨ek, e⟩ := e
    rw [pairM_std hu, pair_eq_pair] at e
    obtain ⟨e₁, e₂⟩ := e
    rw [← e₁] at hE₁; rw [← e₂] at hE₂
    rw [pairM_std hq, pairM_std hr, ihA dp r₁ hE₁, ihB dp r₂ hE₂, ← ek]
  · have e := pairM_std hu₁; have hk'' : @Eq Nat k' 5 ∨ @Eq Nat k' 6 := hk'
    rw [pair_eq_pair] at e; omega

/-- The quantifier case of `form_sound`. -/
theorem form_quant (hok : TableOK lc ld tc td L) (k : Nat) (hk : 5 ≤ k ∧ k ≤ 6)
    (A φ : Formula Arith) (hφ : fcode φ = pair k (fcode A))
    (hs : ∀ σ, @Eq Nat (fcode (φ.subst σ)) (pair k (fcode (A.subst (Subst.lift σ)))))
    (dp r : stdPA.Dom) (hE : Entry tc td L (fcode φ) dp r 1)
    (ihA : ∀ dp r : stdPA.Dom, Entry tc td L (fcode A) dp r 1 →
      @Eq Nat r (fcode (A.subst (liftN dp (σStd lc ld))))) :
    @Eq Nat r (fcode (φ.subst (liftN dp (σStd lc ld)))) := by
  rw [hφ] at hE
  rw [hs]
  rcases formOK_of hok hE with ⟨hu, -⟩ | ⟨p, hp, -⟩ | ⟨k', hk', p, hp, -⟩ |
    ⟨k', hk', u₁, hu₁, r₁, hr₁, hE₁⟩
  · have e : @Eq Nat (pair k (fcode A)) 0 := hu
    exact absurd e (Nat.ne_of_gt (pos_pair (by omega)))
  · have e := pairM_std hp; rw [pair_eq_pair] at e; omega
  · have e := pairM_std hp; have hk'' : @Eq Nat k' 2 ∨ @Eq Nat k' 3 ∨ @Eq Nat k' 4 := hk'
    rw [pair_eq_pair] at e; omega
  · have e := pairM_std hu₁
    rw [pair_eq_pair] at e
    obtain ⟨ek, e⟩ := e
    rw [← e] at hE₁
    rw [pairM_std hr₁, ihA (dp + 1) r₁ hE₁, ← ek]; rfl

/-- Formula entries of a correct table in `ℕ` compute substitution instances. -/
theorem form_sound (hok : TableOK lc ld tc td L) : ∀ (φ : Formula Arith) (dp r : stdPA.Dom),
    Entry tc td L (fcode φ) dp r 1 → @Eq Nat r (fcode (φ.subst (liftN dp (σStd lc ld))))
  | .bot, dp, r, hE => by
    rcases formOK_of hok hE with ⟨-, hr⟩ | ⟨p, hp, -⟩ | ⟨k, hk, p, hp, -⟩ | ⟨k, hk, u₁, hu₁, -⟩
    · exact hr
    · have e := pairM_std hp; simp only [fcode, pair_eq_pair] at e; omega
    · have e := pairM_std hp; have hk' : @Eq Nat k 2 ∨ @Eq Nat k 3 ∨ @Eq Nat k 4 := hk
      simp only [fcode, pair_eq_pair] at e; omega
    · have e := pairM_std hu₁; have hk' : @Eq Nat k 5 ∨ @Eq Nat k 6 := hk
      simp only [fcode, pair_eq_pair] at e; omega
  | .eq t s, dp, r, hE => by
    rcases formOK_of hok hE with ⟨hu, -⟩ | ⟨p, hp, u₁, u₂, hu, q, hq, r₁, r₂, hr, hE₁, hE₂⟩ |
      ⟨k, hk, p, hp, -⟩ | ⟨k, hk, u₁, hu₁, -⟩
    · have e : @Eq Nat (fcode (Formula.eq t s)) 0 := hu
      exact absurd e (Nat.ne_of_gt (pos_pair (Nat.le_refl 1)))
    · have e := pairM_std hp
      simp only [fcode, pair_eq_pair] at e
      obtain ⟨-, e⟩ := e
      rw [pairM_std hu, pair_eq_pair] at e
      obtain ⟨e₁, e₂⟩ := e
      rw [← e₁] at hE₁; rw [← e₂] at hE₂
      rw [pairM_std hq, pairM_std hr, term_sound hok t dp r₁ hE₁, term_sound hok s dp r₂ hE₂]
      rfl
    · have e := pairM_std hp; have hk' : @Eq Nat k 2 ∨ @Eq Nat k 3 ∨ @Eq Nat k 4 := hk
      simp only [fcode, pair_eq_pair] at e; omega
    · have e := pairM_std hu₁; have hk' : @Eq Nat k 5 ∨ @Eq Nat k 6 := hk
      simp only [fcode, pair_eq_pair] at e; omega
  | .rel R _, _, _, _ => (R : Empty).elim
  | .imp A B, dp, r, hE => form_bin hok 2 (by omega) A B (Formula.imp A B) rfl (fun _ => rfl) dp r hE
      (form_sound hok A) (form_sound hok B)
  | .conj A B, dp, r, hE => form_bin hok 3 (by omega) A B (Formula.conj A B) rfl (fun _ => rfl) dp r hE
      (form_sound hok A) (form_sound hok B)
  | .disj A B, dp, r, hE => form_bin hok 4 (by omega) A B (Formula.disj A B) rfl (fun _ => rfl) dp r hE
      (form_sound hok A) (form_sound hok B)
  | .all A, dp, r, hE => form_quant hok 5 (by omega) A (Formula.all A) rfl (fun _ => rfl) dp r hE
      (form_sound hok A)
  | .ex A, dp, r, hE => form_quant hok 6 (by omega) A (Formula.ex A) rfl (fun _ => rfl) dp r hE
      (form_sound hok A)

end Table

/-- **Soundness of the substitution table in `ℕ`.** If `SubstM u r` holds in `ℕ` and `u`
is the code of `φ`, then `r` is the code of a substitution instance of `φ`. -/
theorem substM_std_sound {u r : stdPA.Dom} (h : SubstM u r) (φ : Formula Arith)
    (hu : @Eq Nat (fcode φ) u) : ∃ σ : Nat → Term Arith, @Eq Nat r (fcode (φ.subst σ)) := by
  obtain ⟨lc, ld, tc, td, L, hE, hall⟩ := h
  have hok : TableOK lc ld tc td L := by
    rintro u dp r s ⟨j, hj, x, hx, hq⟩
    obtain ⟨x', hx', u', dp', r', s', hq', hc⟩ := hall j hj
    have e₁ := quad_std hq
    have e₂ := quad_std hq'
    rw [betaM_unique hx hx', e₂] at e₁
    obtain ⟨e₃, e₄⟩ := pair_inj e₁
    obtain ⟨e₅, e₆⟩ := pair_inj e₄
    obtain ⟨e₇, e₈⟩ := pair_inj e₆
    have : u' = u ∧ dp' = dp ∧ r' = r ∧ s' = s := ⟨e₃, e₅, e₇, e₈⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    exact hc
  rw [← hu] at hE
  exact ⟨_, form_sound hok φ 0 r hE⟩

/-- A derivable judgement `PA ⊢ a` has a formula with code `a`, provable in PA. -/
theorem derivable_J {a : Nat} (h : Derivable paRule (pj 0 (ccode []) a)) :
    ∃ φ, a = fcode φ ∧ PA ⊢₁ φ := by
  obtain ⟨k, Δ, φ, e, hd⟩ := proves_of_derivable h
  obtain ⟨rfl, e₂, rfl⟩ := pj_inj e
  rw [ccode_inj e₂.symm] at hd
  exact ⟨φ, rfl, hd.weaken ctx_zero_nil.1⟩

/-- `J` in the standard model. -/
theorem jm_std {a y : stdPA.Dom} (h : JM a y) : @Eq Nat y (pj 0 (ccode []) a) := by
  obtain ⟨x, hx, hy⟩ := h
  rw [pairM_std hy, pairM_std hx]; rfl

/-- **Soundness of `provDP`-derivation codes in `ℕ`.** -/
theorem derP_std_sound {y : stdPA.Dom} (h : DerP y) : Derivable paRule y := by
  obtain ⟨c, d, n, hn, hall⟩ := h
  have key : ∀ k : Nat, k ≤ n → ∀ y : Nat, BetaM (N := stdPA) c d k y → Derivable paRule y := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk y hy
      obtain ⟨y', hy', hj⟩ := hall k (stdPA_le.2 hk)
      rw [betaM_unique hy hy']
      rcases hj with ⟨w, js, u, hu, q, hq, hs, c', d', m, h0, hm, hprem⟩ |
        ⟨i, hi, j, hj, a, b, r, yi, hyi, hai, yj, hyj, hbj, hr, p, hp, hp'⟩ |
        ⟨i, hi, u, yi, hyi, hui, r, hr, hsub⟩
      · have e₁ := stdPA_pairM hu
        have e₂ := stdPA_pairM hq
        have hstep := stepM_std hs
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
        have h0' : BetaM (N := stdPA) c' d' (0 : Nat) js := h0
        refine Derivable.intro y' w (decList js)
          (tails (m : Nat) (Nat.le_refl _) js (by rw [Nat.sub_self]; exact h0')) ?_
        rw [encList_decList]
        show paStep (pair y' (pair w js)) = true
        rw [← e₁, ← e₂]; exact hstep
      · have hi' : (i : Nat) < k := stdPA_lt.1 hi
        have hj' : (j : Nat) < k := stdPA_lt.1 hj
        have da := ih i hi' (Nat.le_trans (Nat.le_of_lt hi') hk) yi hyi
        have db := ih j hj' (Nat.le_trans (Nat.le_of_lt hj') hk) yj hyj
        rw [jm_std hai] at da; rw [jm_std hbj] at db
        obtain ⟨φa, rfl, hφa⟩ := derivable_J da
        obtain ⟨φb, rfl, hφb⟩ := derivable_J db
        have e₁ := pairM_std hp
        have e₂ := pairM_std hp'
        obtain ⟨A, B, rfl⟩ := fcode_tag_imp (Φ := φa) (by rw [e₂]; exact fst_pair _ _)
        have e₃ : pair 2 (pair (fcode A) (fcode B)) = pair 2 (pair (fcode φb) r) := by
          rw [← e₁]; exact e₂
        obtain ⟨-, e₄⟩ := pair_inj e₃
        obtain ⟨e₅, e₆⟩ := pair_inj e₄
        rw [fcode_inj e₅] at hφa
        rw [jm_std hr, ← e₆]
        exact (derivable_iff_PA_proves B).2 (Proves.impE hφa hφb)
      · have hi' : (i : Nat) < k := stdPA_lt.1 hi
        have du := ih i hi' (Nat.le_trans (Nat.le_of_lt hi') hk) yi hyi
        rw [jm_std hui] at du
        obtain ⟨φ, hφ, hp⟩ := derivable_J du
        obtain ⟨σ, hσ⟩ := substM_std_sound hsub φ hφ.symm
        rw [jm_std hr, hσ]
        exact (derivable_iff_PA_proves _).2 (PA_proves_of_models fun N e =>
          (sat_subst φ e σ).2 (sat_of_PA_proves N hp _))
  exact key n (Nat.le_refl n) y hn

end GodelII

open GodelII

/-- **`provDP` defines PA-provability in the standard model.** -/
theorem sat_provDP (φ : Formula Arith) (e : Nat → Nat) :
    Sat stdModel e (box provDP φ) ↔ PA ⊢₁ φ := by
  constructor
  · intro h
    have h' := (provDPM_iff (N := stdPA) _).1 ((sat_box_provDP stdPA e φ).1 h)
    rw [jn_cast, stdPA_cast] at h'
    exact (derivable_iff_PA_proves φ).1 (derP_std_sound h')
  · intro h
    exact PA_sound (provDP_D1 h) e

end Foundations.Logic.FO
