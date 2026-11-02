import Foundations.Logic.GodelIID3Std

/-!
# Instances of theorems at non-standard numerals

The basic tool of formalised Σ-completeness: if `PA ⊢ L` for a (standard) formula `L`,
then inside every model `N` of PA, *for all elements* `v₀, v₁, …` of `N` — standard or
not — the judgement "PA ⊢ L(v̄₀, v̄₁, …)" is `provDP`-derivable (`derP_inst`).

The derivation has two lines: the standard derivation of `L`, and the substitution rule,
justified by a table of standard length listing, for every subterm and subformula of `L`
and its binder depth, the (possibly non-standard) code of its substitution instance
`codeM`. The values `vₘ` are listed by a β-code; since every variable index occurring in
`L` is at most the Gödel number of `L`, a list of length `⌜L⌝ + 1` suffices.

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

/-- Casts preserve `≤`. -/
theorem natCast_le {m n : Nat} (h : m ≤ n) : (m : N.Dom) ≤ (n : N.Dom) :=
  ⟨((n - m : Nat) : N.Dom), by rw [← natCast_add]; congr 1; omega⟩

/-- Casts preserve `<`. -/
theorem natCast_lt {m n : Nat} (h : m < n) : (m : N.Dom) < (n : N.Dom) := by
  have := natCast_le (N := N) (show m + 1 ≤ n from h)
  rwa [natCast_add, natCast_one] at this

/-- Below or at a numeral there are only numerals. -/
theorem le_natCast_cases (n : Nat) (j : N.Dom) (h : j ≤ (n : N.Dom)) : ∃ i : Nat, i ≤ n ∧ j = i := by
  have h' : j < ((n + 1 : Nat) : N.Dom) := by rw [natCast_add, natCast_one]; exact lt_succ_iff'.2 h
  obtain ⟨i, hi, rfl⟩ := lt_natCast_cases _ j h'
  exact ⟨i, by omega, rfl⟩

/-- The code of a table entry `⟨u, ⟨dp, ⟨r, s⟩⟩⟩`. -/
noncomputable def quadN (u dp r s : N.Dom) : N.Dom := pairN u (pairN dp (pairN r s))

/-- `quadN` satisfies `Quad`. -/
theorem quad_quadN (u dp r s : N.Dom) : Quad u dp r s (quadN u dp r s) :=
  ⟨_, pairN_spec r s, _, pairN_spec dp _, pairN_spec u _⟩

/-- Table entries for a term at depth `dp`. -/
noncomputable def tEnt (vals : Nat → N.Dom) : Term Arith → Nat → List N.Dom
  | .var m, dp => [quadN ((tcode (.var m) : Nat) : N.Dom) dp (tcM (.var m) dp vals) 0]
  | .func ArithFunc.zero ts, dp =>
      [quadN ((tcode (.func ArithFunc.zero ts) : Nat) : N.Dom) dp (tcM (.func ArithFunc.zero ts) dp vals) 0]
  | .func ArithFunc.succ ts, dp =>
      quadN ((tcode (.func ArithFunc.succ ts) : Nat) : N.Dom) dp
        (tcM (.func ArithFunc.succ ts) dp vals) 0 :: tEnt vals (ts 0) dp
  | .func ArithFunc.add ts, dp =>
      quadN ((tcode (.func ArithFunc.add ts) : Nat) : N.Dom) dp
        (tcM (.func ArithFunc.add ts) dp vals) 0 :: (tEnt vals (ts 0) dp ++ tEnt vals (ts 1) dp)
  | .func ArithFunc.mul ts, dp =>
      quadN ((tcode (.func ArithFunc.mul ts) : Nat) : N.Dom) dp
        (tcM (.func ArithFunc.mul ts) dp vals) 0 :: (tEnt vals (ts 0) dp ++ tEnt vals (ts 1) dp)

/-- The head entry of a formula. -/
noncomputable def fHead (vals : Nat → N.Dom) (φ : Formula Arith) (dp : Nat) : N.Dom :=
  quadN ((fcode φ : Nat) : N.Dom) dp (codeM φ dp vals) 1

/-- Table entries for a formula at depth `dp`. -/
noncomputable def fEnt (vals : Nat → N.Dom) : Formula Arith → Nat → List N.Dom
  | .bot, dp => [fHead vals .bot dp]
  | .eq t s, dp => fHead vals (.eq t s) dp :: (tEnt vals t dp ++ tEnt vals s dp)
  | .rel R _, _ => (R : Empty).elim
  | .imp A B, dp => fHead vals (.imp A B) dp :: (fEnt vals A dp ++ fEnt vals B dp)
  | .conj A B, dp => fHead vals (.conj A B) dp :: (fEnt vals A dp ++ fEnt vals B dp)
  | .disj A B, dp => fHead vals (.disj A B) dp :: (fEnt vals A dp ++ fEnt vals B dp)
  | .all A, dp => fHead vals (.all A) dp :: fEnt vals A (dp + 1)
  | .ex A, dp => fHead vals (.ex A) dp :: fEnt vals A (dp + 1)

section Table

variable {lc ld tc td L : N.Dom} {vals : Nat → N.Dom} {B : Nat}

/-- A list element is in the table. -/
def InTab (tc td L x : N.Dom) : Prop := ∃ j, j ≤ L ∧ BetaM tc td j x

/-- An element of the table is a locally correct entry. -/
def LocOK (lc ld tc td L x : N.Dom) : Prop :=
  ∃ u', ∃ dp, ∃ r', ∃ s, Quad u' dp r' s x ∧
    ((s = 0 ∧ TermOK lc ld tc td L u' dp r') ∨ (s = 1 ∧ FormOK tc td L u' dp r'))

/-- The head of `tEnt` is its first element. -/
theorem tEnt_head (t : Term Arith) (dp : Nat) :
    quadN ((tcode t : Nat) : N.Dom) dp (tcM t dp vals) 0 ∈ tEnt vals t dp := by
  rcases t with m | ⟨f, ts⟩
  · simp [tEnt]
  · cases f <;> simp [tEnt]

/-- An entry from the table. -/
theorem entry_of_inTab {u dp r s : N.Dom} (h : InTab tc td L (quadN u dp r s)) :
    Entry tc td L u dp r s := by
  obtain ⟨j, hj, hb⟩ := h; exact ⟨j, hj, _, hb, quad_quadN u dp r s⟩

/-- The binary-term case of `tEnt_ok`. -/
theorem tEnt_ok_bin (k : Nat)
    (hk : k = 3 ∨ k = 4) (ts : Fin 2 → Term Arith) (dp : Nat) (t : Term Arith)
    (htc : tcode t = pair k (pair (tcode (ts 0)) (tcode (ts 1))))
    (htm : tcM t dp vals = pairN ((k : Nat) : N.Dom) (pairN (tcM (ts 0) dp vals) (tcM (ts 1) dp vals)))
    (hent : tEnt vals t dp = quadN ((tcode t : Nat) : N.Dom) dp (tcM t dp vals) 0 ::
      (tEnt vals (ts 0) dp ++ tEnt vals (ts 1) dp))
    (hB : tcode t ≤ B) (hin : ∀ x ∈ tEnt vals t dp, InTab tc td L x) (x : N.Dom)
    (hx : x ∈ tEnt vals t dp)
    (ih₀ : tcode (ts 0) ≤ B → (∀ x ∈ tEnt vals (ts 0) dp, InTab tc td L x) →
      ∀ x ∈ tEnt vals (ts 0) dp, LocOK lc ld tc td L x)
    (ih₁ : tcode (ts 1) ≤ B → (∀ x ∈ tEnt vals (ts 1) dp, InTab tc td L x) →
      ∀ x ∈ tEnt vals (ts 1) dp, LocOK lc ld tc td L x) : LocOK lc ld tc td L x := by
  have hpos : 0 < k := by omega
  have hB₀ : tcode (ts 0) ≤ B := Nat.le_trans (Nat.le_of_lt (fst_lt_tagged hpos)) (htc ▸ hB)
  have hB₁ : tcode (ts 1) ≤ B := Nat.le_trans (Nat.le_of_lt (snd_lt_tagged hpos)) (htc ▸ hB)
  rw [hent] at hin
  rw [hent] at hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx | hx
  · have hk' : ((k : Nat) : N.Dom) = 3 ∨ ((k : Nat) : N.Dom) = 4 := by
      rcases hk with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    refine ⟨_, _, _, _, quad_quadN _ _ _ _, Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr
      ⟨((k : Nat) : N.Dom), hk', ((pair (tcode (ts 0)) (tcode (ts 1)) : Nat) : N.Dom),
        by rw [htc]; exact pairM_natCast _ _, _, _, pairM_natCast _ _, _,
        by rw [htm]; exact pairN_spec _ _, _, _, pairN_spec _ _,
        entry_of_inTab (hin _ (by simp [tEnt_head])),
        entry_of_inTab (hin _ (by simp [tEnt_head]))⟩))⟩⟩
  · exact ih₀ hB₀ (fun y hy => hin y (by simp [hy])) x hx
  · exact ih₁ hB₁ (fun y hy => hin y (by simp [hy])) x hx

/-- **Term entries are locally correct**, provided all of them are in the table and the value
list covers every index up to `B ≥ ⌜t⌝`. -/
theorem tEnt_ok (hlist : ∀ i : Nat, i ≤ B → BetaM lc ld (i : N.Dom) (vals i)) :
    ∀ (t : Term Arith) (dp : Nat), tcode t ≤ B → (∀ x ∈ tEnt vals t dp, InTab tc td L x) →
      ∀ x ∈ tEnt vals t dp, LocOK lc ld tc td L x
  | .var m, dp, hB, hin, x, hx => by
    simp only [tEnt, List.mem_singleton] at hx; subst hx
    refine ⟨_, _, _, _, quad_quadN _ _ _ _, Or.inl ⟨rfl, Or.inl ⟨(m : N.Dom), pairM_natCast 0 m, ?_⟩⟩⟩
    by_cases h : m < dp
    · left; exact ⟨natCast_lt h, by simp [tcM, h, tcode]⟩
    · right
      have hm : m ≤ B := Nat.le_trans (Computability.right_le_pair 0 m) hB
      refine ⟨((m - dp : Nat) : N.Dom), by rw [← natCast_add]; congr 1; omega, vals (m - dp),
        hlist _ (by omega), ?_⟩
      simp only [tcM, h, ite_false]; exact numN_spec _
  | .func ArithFunc.zero ts, dp, hB, hin, x, hx => by
    simp only [tEnt, List.mem_singleton] at hx; subst hx
    exact ⟨_, _, _, _, quad_quadN _ _ _ _, Or.inl ⟨rfl, Or.inr (Or.inl ⟨two_eq_cast.symm, rfl⟩)⟩⟩
  | .func ArithFunc.succ ts, dp, hB, hin, x, hx => by
    have hB₁ : tcode (ts 0) ≤ B := Nat.le_trans (Nat.le_of_lt (lt_pair_of_pos (by omega))) hB
    simp only [tEnt, List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨_, _, _, _, quad_quadN _ _ _ _, Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl
        ⟨_, pairM_natCast 2 (tcode (ts 0)), _, pairN_spec _ _, entry_of_inTab
          (hin _ (by simp only [tEnt]; exact List.mem_cons_of_mem _ (tEnt_head _ _)))⟩))⟩⟩
    · exact tEnt_ok hlist (ts 0) dp hB₁ (fun y hy => hin y (by simp [tEnt, hy])) x hx
  | .func ArithFunc.add ts, dp, hB, hin, x, hx => tEnt_ok_bin 3 (by omega) ts dp
      (.func ArithFunc.add ts) rfl rfl (by simp [tEnt]) hB hin x hx
      (tEnt_ok hlist (ts 0) dp) (tEnt_ok hlist (ts 1) dp)
  | .func ArithFunc.mul ts, dp, hB, hin, x, hx => tEnt_ok_bin 4 (by omega) ts dp
      (.func ArithFunc.mul ts) rfl rfl (by simp [tEnt]) hB hin x hx
      (tEnt_ok hlist (ts 0) dp) (tEnt_ok hlist (ts 1) dp)

/-- The head of `fEnt` is its first element. -/
theorem fEnt_head (φ : Formula Arith) (dp : Nat) : fHead vals φ dp ∈ fEnt vals φ dp := by
  rcases φ with _ | ⟨t, s⟩ | ⟨R, _⟩ | ⟨A, B⟩ | ⟨A, B⟩ | ⟨A, B⟩ | A | A
  all_goals first | exact (R : Empty).elim | simp [fEnt]

/-- The binary-connective case of `fEnt_ok`. -/
theorem fEnt_ok_bin (k : Nat) (hk : k = 2 ∨ k = 3 ∨ k = 4) (A B' φ : Formula Arith) (dp : Nat)
    (hfc : fcode φ = pair k (pair (fcode A) (fcode B')))
    (hcm : codeM φ dp vals = pairN ((k : Nat) : N.Dom) (pairN (codeM A dp vals) (codeM B' dp vals)))
    (hent : fEnt vals φ dp = fHead vals φ dp :: (fEnt vals A dp ++ fEnt vals B' dp))
    (hB : fcode φ ≤ B) (hin : ∀ x ∈ fEnt vals φ dp, InTab tc td L x) (x : N.Dom)
    (hx : x ∈ fEnt vals φ dp)
    (ih₀ : fcode A ≤ B → (∀ x ∈ fEnt vals A dp, InTab tc td L x) →
      ∀ x ∈ fEnt vals A dp, LocOK lc ld tc td L x)
    (ih₁ : fcode B' ≤ B → (∀ x ∈ fEnt vals B' dp, InTab tc td L x) →
      ∀ x ∈ fEnt vals B' dp, LocOK lc ld tc td L x) : LocOK lc ld tc td L x := by
  have hpos : 0 < k := by omega
  have hB₀ : fcode A ≤ B := Nat.le_trans (Nat.le_of_lt (fst_lt_tagged hpos)) (hfc ▸ hB)
  have hB₁ : fcode B' ≤ B := Nat.le_trans (Nat.le_of_lt (snd_lt_tagged hpos)) (hfc ▸ hB)
  rw [hent] at hin hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx | hx
  · have hk' : ((k : Nat) : N.Dom) = 2 ∨ ((k : Nat) : N.Dom) = 3 ∨ ((k : Nat) : N.Dom) = 4 := by
      rcases hk with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    refine ⟨_, _, _, _, quad_quadN _ _ _ _, Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl
      ⟨((k : Nat) : N.Dom), hk', ((pair (fcode A) (fcode B')) : Nat),
        by rw [hfc]; exact pairM_natCast _ _, _, _, pairM_natCast _ _, _,
        by rw [hcm]; exact pairN_spec _ _, _, _, pairN_spec _ _,
        entry_of_inTab (hin _ (List.mem_cons_of_mem _ (List.mem_append_left _ (fEnt_head A dp)))),
        entry_of_inTab (hin _ (List.mem_cons_of_mem _
          (List.mem_append_right _ (fEnt_head B' dp))))⟩))⟩⟩
  · exact ih₀ hB₀ (fun y hy => hin y (by simp [hy])) x hx
  · exact ih₁ hB₁ (fun y hy => hin y (by simp [hy])) x hx

/-- The quantifier case of `fEnt_ok`. -/
theorem fEnt_ok_quant (k : Nat) (hk : k = 5 ∨ k = 6) (A φ : Formula Arith) (dp : Nat)
    (hfc : fcode φ = pair k (fcode A))
    (hcm : codeM φ dp vals = pairN ((k : Nat) : N.Dom) (codeM A (dp + 1) vals))
    (hent : fEnt vals φ dp = fHead vals φ dp :: fEnt vals A (dp + 1))
    (hB : fcode φ ≤ B) (hin : ∀ x ∈ fEnt vals φ dp, InTab tc td L x) (x : N.Dom)
    (hx : x ∈ fEnt vals φ dp)
    (ih₀ : fcode A ≤ B → (∀ x ∈ fEnt vals A (dp + 1), InTab tc td L x) →
      ∀ x ∈ fEnt vals A (dp + 1), LocOK lc ld tc td L x) : LocOK lc ld tc td L x := by
  have hB₀ : fcode A ≤ B := Nat.le_trans (Nat.le_of_lt (lt_pair_of_pos (by omega))) (hfc ▸ hB)
  rw [hent] at hin hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · have hk' : ((k : Nat) : N.Dom) = 5 ∨ ((k : Nat) : N.Dom) = 6 := by
      rcases hk with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hE := entry_of_inTab (hin _ (List.mem_cons_of_mem _ (fEnt_head A (dp + 1))))
    rw [natCast_add, natCast_one] at hE
    exact ⟨_, _, _, _, quad_quadN _ _ _ _, Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr
      ⟨((k : Nat) : N.Dom), hk', _, by rw [hfc]; exact pairM_natCast _ _, _,
        by rw [hcm]; exact pairN_spec _ _, hE⟩))⟩⟩
  · exact ih₀ hB₀ (fun y hy => hin y (by simp [hy])) x hx

/-- **Formula entries are locally correct.** -/
theorem fEnt_ok (hlist : ∀ i : Nat, i ≤ B → BetaM lc ld (i : N.Dom) (vals i)) :
    ∀ (φ : Formula Arith) (dp : Nat), fcode φ ≤ B → (∀ x ∈ fEnt vals φ dp, InTab tc td L x) →
      ∀ x ∈ fEnt vals φ dp, LocOK lc ld tc td L x
  | .bot, dp, _, _, x, hx => by
    simp only [fEnt, List.mem_singleton] at hx; subst hx
    exact ⟨_, _, _, _, quad_quadN _ _ _ _, Or.inr ⟨rfl, Or.inl ⟨by rw [fcode_bot]; rfl, rfl⟩⟩⟩
  | .eq t s, dp, hB, hin, x, hx => by
    have hBt : tcode t ≤ B := Nat.le_trans (Nat.le_of_lt (fst_lt_tagged (by omega))) hB
    have hBs : tcode s ≤ B := Nat.le_trans (Nat.le_of_lt (snd_lt_tagged (by omega))) hB
    simp only [fEnt, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact ⟨_, _, _, _, quad_quadN _ _ _ _, Or.inr ⟨rfl, Or.inr (Or.inl
        ⟨((pair (tcode t) (tcode s) : Nat) : N.Dom), pairM_natCast 1 _, _, _, pairM_natCast _ _,
          _, pairN_spec _ _, _, _, pairN_spec _ _,
          entry_of_inTab (hin _ (by simp [fEnt, tEnt_head])),
          entry_of_inTab (hin _ (by simp [fEnt, tEnt_head]))⟩)⟩⟩
    · exact tEnt_ok hlist t dp hBt (fun y hy => hin y (by simp [fEnt, hy])) x hx
    · exact tEnt_ok hlist s dp hBs (fun y hy => hin y (by simp [fEnt, hy])) x hx
  | .rel R _, _, _, _, _, _ => (R : Empty).elim
  | .imp A B', dp, hB, hin, x, hx => fEnt_ok_bin 2 (by omega) A B' _ dp rfl rfl rfl hB hin x hx
      (fEnt_ok hlist A dp) (fEnt_ok hlist B' dp)
  | .conj A B', dp, hB, hin, x, hx => fEnt_ok_bin 3 (by omega) A B' _ dp rfl rfl rfl hB hin x hx
      (fEnt_ok hlist A dp) (fEnt_ok hlist B' dp)
  | .disj A B', dp, hB, hin, x, hx => fEnt_ok_bin 4 (by omega) A B' _ dp rfl rfl rfl hB hin x hx
      (fEnt_ok hlist A dp) (fEnt_ok hlist B' dp)
  | .all A, dp, hB, hin, x, hx => fEnt_ok_quant 5 (by omega) A _ dp rfl rfl rfl hB hin x hx
      (fEnt_ok hlist A (dp + 1))
  | .ex A, dp, hB, hin, x, hx => fEnt_ok_quant 6 (by omega) A _ dp rfl rfl rfl hB hin x hx
      (fEnt_ok hlist A (dp + 1))

end Table

/-- **Instances at arbitrary values.** If `PA ⊢ L`, then for every assignment `vals` of
elements of `N` to the variables, "PA ⊢ L(v̄al₀, v̄al₁, …)" is `provDP`-derivable in `N`. -/
theorem derP_inst {Lf : Formula Arith} (h : PA ⊢₁ Lf) (vals : Nat → N.Dom) :
    DerP (JN (codeM Lf 0 vals)) := by
  refine derP_subst ?_ (derP_of_proves h)
  obtain ⟨lc, ld, hl⟩ := seq_of_fun vals (fcode Lf)
  obtain ⟨tc, td, ht⟩ := seq_of_fun (fun i => (fEnt vals Lf 0).getD i 0) ((fEnt vals Lf 0).length - 1)
  have hin : ∀ x ∈ fEnt vals Lf 0, InTab tc td (((fEnt vals Lf 0).length - 1 : Nat) : N.Dom) x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    refine ⟨(i : N.Dom), natCast_le (by omega), ?_⟩
    have := ht i (by omega)
    have e : (fEnt vals Lf 0).getD i 0 = (fEnt vals Lf 0)[i] := by
      simp [List.getD_eq_getElem?_getD, hi]
    rwa [e] at this
  refine ⟨lc, ld, tc, td, _, entry_of_inTab (hin _ (fEnt_head Lf 0)), fun j hj => ?_⟩
  obtain ⟨i, hi, rfl⟩ := le_natCast_cases _ j hj
  have hlen : 0 < (fEnt vals Lf 0).length := List.length_pos_of_mem (fEnt_head Lf 0)
  have hmem : (fEnt vals Lf 0).getD i 0 ∈ fEnt vals Lf 0 := by
    have hi' : i < (fEnt vals Lf 0).length := by omega
    have e : (fEnt vals Lf 0).getD i 0 = (fEnt vals Lf 0)[i] := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [e]; exact List.getElem_mem _
  obtain ⟨u', dp, r', s, hq, hc⟩ := fEnt_ok hl Lf 0 (Nat.le_refl _) hin _ hmem
  exact ⟨_, ht i hi, u', dp, r', s, hq, hc⟩


end PAModel

end Foundations.Logic.FO
