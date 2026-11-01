import Foundations.Numbers.CompleteOrderedField

/-!
# Analysis on the reals I: sequences

With the reals in hand we can do what Dedekind wanted to do in 1858: *prove* the basic theorems
of the calculus instead of appealing to geometric intuition. All of them rest on completeness.

* A sequence `a₀, a₁, …` of reals **converges** to `L` if for every `ε > 0` its terms are
  eventually within `ε` of `L`. Limits are unique.
* **Monotone convergence theorem**: an increasing sequence that is bounded above converges (to
  the least upper bound of its terms).
* **Bolzano–Weierstrass theorem**: every bounded sequence has a convergent subsequence. We take
  `L` to be the *limit superior* (the supremum of the values that the sequence exceeds infinitely
  often) and pick terms ever closer to `L`.
* **Cauchy completeness**: every Cauchy sequence of *reals* converges. Thus repeating Cantor's
  construction on `R` instead of `Q` would produce nothing new — the process of completion has
  come to rest.

Absolute values are those of `OF.abs` (the absolute value of any ordered field).
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-- The sequence `a` **converges** to `L`: for every `ε > 0`, eventually `|aₙ − L| < ε`. -/
def Tendsto (a : Nat → R) (L : R) : Prop :=
  ∀ ε : R, 0 < ε → ∃ N, ∀ n, N ≤ n → abs (a n - L) < ε

/-- A sequence of reals is **Cauchy** if its terms become arbitrarily close to each other. -/
def IsCauchySeq (a : Nat → R) : Prop :=
  ∀ ε : R, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → abs (a m - a n) < ε

/-- **Uniqueness of limits.** A sequence has at most one limit. -/
theorem tendsto_unique {a : Nat → R} {L M : R} (hL : Tendsto a L) (hM : Tendsto a M) : L = M := by
  apply Classical.byContradiction
  intro hne
  have hpos : 0 < abs (L - M) := by rcases abs_cases (L - M) with h | h <;> grind
  obtain ⟨N₁, h₁⟩ := hL (abs (L - M) / 2) (by grind)
  obtain ⟨N₂, h₂⟩ := hM (abs (L - M) / 2) (by grind)
  have k1 := h₁ (max N₁ N₂) (by omega)
  have k2 := h₂ (max N₁ N₂) (by omega)
  have k3 := abs_add (L - a (max N₁ N₂)) (a (max N₁ N₂) - M)
  rw [abs_sub_comm] at k1
  have e : L - a (max N₁ N₂) + (a (max N₁ N₂) - M) = L - M := by grind
  rw [e] at k3
  grind

/-- Limits preserve non-strict lower bounds. -/
theorem le_of_tendsto {a : Nat → R} {L c : R} (h : Tendsto a L) (hc : ∀ n, c ≤ a n) : c ≤ L := by
  apply Classical.byContradiction
  intro hlt
  obtain ⟨N, hN⟩ := h (c - L) (by grind)
  have := abs_lt.1 (hN N (Nat.le_refl _)); have := hc N; grind

/-- Limits preserve non-strict upper bounds. -/
theorem tendsto_le {a : Nat → R} {L c : R} (h : Tendsto a L) (hc : ∀ n, a n ≤ c) : L ≤ c := by
  apply Classical.byContradiction
  intro hlt
  obtain ⟨N, hN⟩ := h (L - c) (by grind)
  have := abs_lt.1 (hN N (Nat.le_refl _)); have := hc N; grind

/-- `1/(k+1)` is eventually below any `ε > 0`. -/
theorem eps_small {ε : R} (hε : 0 < ε) : ∃ N : Nat, ∀ k : Nat, N ≤ k → 1 / ((k : R) + 1) < ε := by
  obtain ⟨N, hN⟩ := archimedean (1 / ε)
  refine ⟨N, fun k hk => ?_⟩
  have hk' : (N : R) ≤ (k : R) := OrderedRing.natCast_le_natCast_of_le _ _ hk
  have h0 : (0 : R) ≤ (k : R) := OrderedRing.natCast_nonneg
  have hpos : (0 : R) < (k : R) + 1 := by grind
  rw [Field.div_eq_mul_inv]
  rw [Field.div_eq_mul_inv] at hN
  have h1 : 1 < (N : R) * ε := (Field.IsOrdered.mul_inv_lt_iff_lt_mul 1 (N : R) hε).1 hN
  have h2 := OrderedRing.mul_le_mul_of_nonneg_right (by grind : (N : R) ≤ (k : R) + 1)
    (Std.le_of_lt hε)
  exact (Field.IsOrdered.mul_inv_lt_iff_lt_mul 1 ε hpos).2 (by grind)

/-- `1/(k+1) > 0`. -/
theorem eps_pos (k : Nat) : (0 : R) < 1 / ((k : R) + 1) :=
  div_pos (by grind) (by have : (0 : R) ≤ (k : R) := OrderedRing.natCast_nonneg; grind)

/-! ## Monotone convergence -/

/-- An increasing sequence is monotone over any range of indices. -/
theorem mono_le {a : Nat → R} (h : ∀ n, a n ≤ a (n + 1)) {m n : Nat} (hmn : m ≤ n) : a m ≤ a n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  induction k with
  | zero => grind
  | succ k ih => have := ih (by omega); have := h (m + k); rw [← Nat.add_assoc]; grind

/-- **Monotone convergence theorem.** An increasing sequence of reals that is bounded above
converges. -/
theorem monotone_convergence {a : Nat → R} (hmono : ∀ n, a n ≤ a (n + 1))
    (hbdd : ∃ B, ∀ n, a n ≤ B) : ∃ L, Tendsto a L := by
  obtain ⟨L, hL1, hL2⟩ := exists_lub (fun x => ∃ n, x = a n) ⟨_, 0, rfl⟩
    (by obtain ⟨B, hB⟩ := hbdd; exact ⟨B, fun x ⟨n, hn⟩ => hn ▸ hB n⟩)
  refine ⟨L, fun ε hε => ?_⟩
  have : ¬ ∀ x, (∃ n, x = a n) → x ≤ L - ε := fun h => by have := hL2 _ h; grind
  have : ∃ N, L - ε < a N := by
    apply Classical.byContradiction; intro hno; apply this
    rintro x ⟨n, rfl⟩
    apply Classical.byContradiction; intro h; exact hno ⟨n, by grind⟩
  obtain ⟨N, hN⟩ := this
  refine ⟨N, fun n hn => abs_lt.2 ⟨?_, ?_⟩⟩
  · have := mono_le hmono hn; grind
  · have := hL1 _ ⟨n, rfl⟩; grind

/-! ## Bolzano–Weierstrass -/

/-- Recursively choose indices `φ 0 < φ 1 < ⋯` with `|a (φ k) − L| < 1/(k+1)`, given that terms
within any `ε` of `L` occur arbitrarily late. -/
noncomputable def chooseSubseq (a : Nat → R) (L : R)
    (h : ∀ ε : R, 0 < ε → ∀ N, ∃ n, N ≤ n ∧ abs (a n - L) < ε) : Nat → Nat
  | 0 => Classical.choose (h (1 / ((0 : Nat) + 1)) (eps_pos 0) 0)
  | k + 1 => Classical.choose (h (1 / ((k + 1 : Nat) + 1)) (eps_pos (k + 1))
      (chooseSubseq a L h k + 1))

/-- The chosen indices increase and the chosen terms are within `1/(k+1)` of `L`. -/
theorem chooseSubseq_spec (a : Nat → R) (L : R)
    (h : ∀ ε : R, 0 < ε → ∀ N, ∃ n, N ≤ n ∧ abs (a n - L) < ε) (k : Nat) :
    abs (a (chooseSubseq a L h k) - L) < 1 / ((k : R) + 1) ∧
      chooseSubseq a L h k < chooseSubseq a L h (k + 1) := by
  constructor
  · cases k with
    | zero => exact (Classical.choose_spec (h (1 / ((0 : Nat) + 1)) (eps_pos 0) 0)).2
    | succ k => exact (Classical.choose_spec (h _ (eps_pos (k + 1)) (chooseSubseq a L h k + 1))).2
  · have := (Classical.choose_spec (h _ (eps_pos (k + 1)) (chooseSubseq a L h k + 1))).1
    show chooseSubseq a L h k < Classical.choose _
    omega

/-- A strictly increasing sequence of indices satisfies `φ k ≥ k`. -/
theorem le_of_strictMono {φ : Nat → Nat} (h : ∀ k, φ k < φ (k + 1)) (k : Nat) : k ≤ φ k := by
  induction k with
  | zero => omega
  | succ k ih => have := h k; omega

/-- If terms within any `ε` of `L` occur arbitrarily late, some subsequence converges to `L`. -/
theorem exists_subseq_tendsto {a : Nat → R} {L : R}
    (h : ∀ ε : R, 0 < ε → ∀ N, ∃ n, N ≤ n ∧ abs (a n - L) < ε) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ Tendsto (fun k => a (φ k)) L := by
  refine ⟨chooseSubseq a L h, fun k => (chooseSubseq_spec a L h k).2, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := eps_small hε
  exact ⟨N, fun k hk => by have := (chooseSubseq_spec a L h k).1; have := hN k hk; grind⟩

/-- **Bolzano–Weierstrass theorem.** Every bounded sequence of reals has a convergent
subsequence. -/
theorem bolzano_weierstrass {a : Nat → R} (hbdd : ∃ B, ∀ n, abs (a n) ≤ B) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ L, Tendsto (fun k => a (φ k)) L := by
  obtain ⟨B, hB⟩ := hbdd
  -- `S` = the values exceeded by the sequence infinitely often; `L = sup S` (the limsup).
  let S : R → Prop := fun x => ∀ N, ∃ n, N ≤ n ∧ x ≤ a n
  have hS : S (-B) := fun N => ⟨N, Nat.le_refl _, by have := abs_le.1 (hB N); grind⟩
  have hSb : ∀ x, S x → x ≤ B := fun x hx => by
    obtain ⟨n, _, hn⟩ := hx 0; have := abs_le.1 (hB n); grind
  obtain ⟨L, hL1, hL2⟩ := exists_lub S ⟨_, hS⟩ ⟨B, hSb⟩
  refine ⟨_, (exists_subseq_tendsto (L := L) ?_).choose_spec.1,
    L, (exists_subseq_tendsto (L := L) ?_).choose_spec.2⟩ <;>
  · intro ε hε N
    -- Some value above `L − ε` is exceeded infinitely often...
    have h1 : ∃ x, S x ∧ L - ε < x := by
      apply Classical.byContradiction; intro hno
      have := hL2 (L - ε) fun x hx => by
        apply Classical.byContradiction; intro h; exact hno ⟨x, hx, by grind⟩
      grind
    obtain ⟨x, hx, hxL⟩ := h1
    -- ...while `L + ε/2` is exceeded only finitely often.
    have h2 : ∃ N₀, ∀ n, N₀ ≤ n → a n < L + ε / 2 := by
      have : ¬ S (L + ε / 2) := fun h => by have := hL1 _ h; grind
      apply Classical.byContradiction; intro hno; apply this; intro M
      apply Classical.byContradiction; intro hM
      exact hno ⟨M, fun n hn => by
        apply Classical.byContradiction; intro h; exact hM ⟨n, hn, by grind⟩⟩
    obtain ⟨N₀, hN₀⟩ := h2
    obtain ⟨n, hn, hxn⟩ := hx (max N N₀)
    exact ⟨n, by omega, abs_lt.2 ⟨by grind, by have := hN₀ n (by omega); grind⟩⟩

/-! ## Cauchy completeness -/

/-- The sum `|a 0| + ⋯ + |a N|`. -/
noncomputable def sumAbs (a : Nat → R) : Nat → R
  | 0 => abs (a 0)
  | n + 1 => sumAbs a n + abs (a (n + 1))

/-- The sum of absolute values is non-negative. -/
theorem sumAbs_nonneg (a : Nat → R) (N : Nat) : 0 ≤ sumAbs a N := by
  induction N with
  | zero => exact abs_nonneg _
  | succ N ih => have := abs_nonneg (a (N + 1)); show 0 ≤ sumAbs a N + abs (a (N + 1)); grind

/-- Each `|a k|` with `k ≤ N` is bounded by `|a 0| + ⋯ + |a N|`. -/
theorem abs_le_sumAbs (a : Nat → R) {k N : Nat} (h : k ≤ N) : abs (a k) ≤ sumAbs a N := by
  induction N with
  | zero => have : k = 0 := by omega
            subst this; show abs (a 0) ≤ abs (a 0); grind
  | succ N ih =>
    have := abs_nonneg (a (N + 1))
    show abs (a k) ≤ sumAbs a N + abs (a (N + 1))
    by_cases hk : k ≤ N
    · have := ih hk; grind
    · have : k = N + 1 := by omega
      subst this
      have := sumAbs_nonneg a N
      grind

/-- Cauchy sequences of reals are bounded. -/
theorem cauchy_bounded {a : Nat → R} (h : IsCauchySeq a) : ∃ B, ∀ n, abs (a n) ≤ B := by
  obtain ⟨N, hN⟩ := h 1 (by grind)
  refine ⟨sumAbs a N + 1, fun n => ?_⟩
  by_cases hn : n ≤ N
  · have := abs_le_sumAbs a hn; grind
  · have h1 := hN n N (by omega) (Nat.le_refl _)
    have h2 := abs_le_sumAbs a (Nat.le_refl N)
    have h3 := abs_add (a n - a N) (a N)
    have e : a n - a N + a N = a n := by grind
    rw [e] at h3; grind

/-- **Cauchy completeness of ℝ.** Every Cauchy sequence of real numbers converges. -/
theorem cauchy_complete {a : Nat → R} (h : IsCauchySeq a) : ∃ L, Tendsto a L := by
  obtain ⟨φ, hφ, L, hL⟩ := bolzano_weierstrass (cauchy_bounded h)
  refine ⟨L, fun ε hε => ?_⟩
  obtain ⟨N₁, h₁⟩ := h (ε / 2) (by grind)
  obtain ⟨K, hK⟩ := hL (ε / 2) (by grind)
  refine ⟨N₁, fun n hn => ?_⟩
  let k := max K N₁
  have hk := le_of_strictMono hφ k
  have k1 := h₁ n (φ k) hn (by omega)
  have k2 := hK k (by omega)
  have k3 := abs_add (a n - a (φ k)) (a (φ k) - L)
  have e : a n - a (φ k) + (a (φ k) - L) = a n - L := by grind
  rw [e] at k3
  simp only at k2
  grind

end R

end Foundations.Numbers
