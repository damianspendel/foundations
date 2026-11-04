import Foundations.Langlands.Padic.Integers
import Foundations.Combinatorics.Pigeonhole

/-!
# ℤₚ is sequentially compact

Every sequence of `p`-adic integers has a convergent subsequence. This is the `p`-adic analogue
of Bolzano–Weierstrass, and the proof is the same "bisection" idea with `p`-fold instead of
two-fold splitting: modulo `pᵏ` there are only `pᵏ` residue classes, so infinitely many terms
of the sequence share one of them (infinite pigeonhole, `Combinatorics.infinite_pigeonhole`).

Concretely, we choose nested infinite sets of indices `S₀ ⊇ S₁ ⊇ S₂ ⊇ ⋯`, where all `zₘ` with
`m ∈ Sₖ` are congruent modulo `pᵏ`: `Sₖ₊₁` is an infinite fibre of the residue map modulo
`pᵏ⁺¹` restricted to `Sₖ`. A diagonal choice `φ 0 < φ 1 < ⋯` with `φ k ∈ Sₖ` gives a
subsequence that is Cauchy modulo powers of `p`, and the completeness of ℤₚ (`Zp.complete`)
supplies the limit.

The result is stated in the `Zp.Converges` sense ("eventually congruent to the limit modulo every
`pᵏ`"), which is convergence for the `p`-adic absolute value. The file `CompactMetric` turns ℤₚ
into a metric space of the Topology part and restates the theorem as `IsSeqCompact`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Combinatorics

namespace Zp

variable {p : Nat}

/-- The **residue modulo `pᵏ`** of a `p`-adic integer, as a natural number `< pᵏ`
(computed from a chosen representative). -/
noncomputable def residue (k : Nat) (x : Zp p) : Nat :=
  ((rep x).seq k % ((p : Int) ^ k)).toNat

/-- The residue modulo `pᵏ` is smaller than `pᵏ`. -/
theorem residue_lt (hp : Prime p) (k : Nat) (x : Zp p) :
    residue k x < ((p : Int) ^ k).toNat := by
  have hpos : (0 : Int) < (p : Int) ^ k := Int.pow_pos (by have := hp.1; omega)
  have h1 := Int.emod_nonneg ((rep x).seq k) (Int.ne_of_gt hpos)
  have h2 := Int.emod_lt_of_pos ((rep x).seq k) hpos
  unfold residue; omega

/-- Equal residues modulo `pᵏ` mean congruence modulo `pᵏ`. -/
theorem modPow_of_residue_eq (hp : Prime p) {k : Nat} {x y : Zp p}
    (h : residue k x = residue k y) : ModPow k x y := by
  have hpos : (0 : Int) < (p : Int) ^ k := Int.pow_pos (by have := hp.1; omega)
  rw [← mk_rep x, ← mk_rep y]
  apply modPow_mk.2
  generalize hn : (p : Int) ^ k = n at hpos
  unfold residue at h
  rw [hn] at h
  generalize (rep x).seq k = a at h
  generalize (rep y).seq k = b at h
  have ha := Int.mul_ediv_add_emod a n
  have hb := Int.mul_ediv_add_emod b n
  have h1 := Int.emod_nonneg a (Int.ne_of_gt hpos)
  have h2 := Int.emod_nonneg b (Int.ne_of_gt hpos)
  have hab : a % n = b % n := by omega
  refine ⟨a / n - b / n, ?_⟩
  rw [Int.mul_sub]
  generalize n * (a / n) = A at ha
  generalize n * (b / n) = B at hb
  omega

/-- Congruence modulo `p⁰ = 1` always holds. -/
theorem modPow_zero (x y : Zp p) : ModPow 0 x y := by
  rw [← mk_rep x, ← mk_rep y]
  apply modPow_mk.2
  rw [Int.pow_zero]; exact Int.one_dvd _

/-- A strictly increasing sequence of naturals dominates the identity. -/
theorem le_of_strictMono {g : Nat → Nat} (hg : ∀ i j, i < j → g i < g j) : ∀ i, i ≤ g i
  | 0 => Nat.zero_le _
  | i + 1 => by have := le_of_strictMono hg i; have := hg i (i + 1) (Nat.lt_succ_self i); omega

/-- **Infinite pigeonhole on an infinite set.** If `S` holds infinitely often and `f` takes
values `< K`, then for some value `c` the set `{m ∈ S | f m = c}` is still infinite. -/
theorem infOften_refine {S : Nat → Prop} (hS : InfOften S) {K : Nat} (f : Nat → Nat)
    (hf : ∀ m, f m < K) : ∃ c, InfOften fun m => S m ∧ f m = c := by
  obtain ⟨g, hgS, hg⟩ := hS.enum
  obtain ⟨c, -, hc⟩ := infinite_pigeonhole K (fun i => f (g i)) (fun i => hf _)
  refine ⟨c, fun N => ?_⟩
  obtain ⟨i, hi, hfi⟩ := hc N
  exact ⟨g i, Nat.le_trans hi (le_of_strictMono hg i), hgS i, hfi⟩

/-- One refinement step: inside an infinite set of indices, an infinite subset on which the
terms `zₘ` all have the same residue modulo `pᵏ`. -/
theorem exists_refine (hp : Prime p) (z : Nat → Zp p) (k : Nat) {S : Nat → Prop}
    (hS : InfOften S) : ∃ T : Nat → Prop, InfOften T ∧ (∀ m, T m → S m) ∧
      ∀ m m', T m → T m' → ModPow k (z m) (z m') := by
  obtain ⟨c, hc⟩ := infOften_refine hS (fun m => residue k (z m)) (fun m => residue_lt hp k _)
  refine ⟨fun m => S m ∧ residue k (z m) = c, hc, fun m h => h.1, fun m m' h h' => ?_⟩
  exact modPow_of_residue_eq hp (h.2.trans h'.2.symm)

/-- The nested infinite index sets `S₀ ⊇ S₁ ⊇ ⋯`, with all `zₘ`, `m ∈ Sₖ`, congruent mod `pᵏ`
(chosen by `exists_refine`). -/
noncomputable def nestedSets (hp : Prime p) (z : Nat → Zp p) : Nat → {S : Nat → Prop // InfOften S}
  | 0 => ⟨fun _ => True, fun N => ⟨N, Nat.le_refl N, trivial⟩⟩
  | k + 1 =>
    let S := nestedSets hp z k
    ⟨Classical.choose (exists_refine hp z (k + 1) S.2),
      (Classical.choose_spec (exists_refine hp z (k + 1) S.2)).1⟩

/-- Each set of the chain is contained in the previous one. -/
theorem nestedSets_succ_sub (hp : Prime p) (z : Nat → Zp p) (k m : Nat)
    (h : (nestedSets hp z (k + 1)).1 m) : (nestedSets hp z k).1 m :=
  (Classical.choose_spec (exists_refine hp z (k + 1) (nestedSets hp z k).2)).2.1 m h

/-- The chain is decreasing: `Sₖ ⊇ Sⱼ` for `k ≤ j`. -/
theorem nestedSets_antitone (hp : Prime p) (z : Nat → Zp p) {k j : Nat} (hkj : k ≤ j) (m : Nat)
    (h : (nestedSets hp z j).1 m) : (nestedSets hp z k).1 m := by
  induction j with
  | zero => have : k = 0 := by omega
            subst this; exact h
  | succ j ih =>
    by_cases hk : k = j + 1
    · subst hk; exact h
    · exact ih (by omega) (nestedSets_succ_sub hp z j m h)

/-- All terms indexed by `Sₖ` are congruent modulo `pᵏ`. -/
theorem nestedSets_modPow (hp : Prime p) (z : Nat → Zp p) (k m m' : Nat)
    (h : (nestedSets hp z k).1 m) (h' : (nestedSets hp z k).1 m') : ModPow k (z m) (z m') := by
  cases k with
  | zero => exact modPow_zero _ _
  | succ k =>
    exact (Classical.choose_spec (exists_refine hp z (k + 1) (nestedSets hp z k).2)).2.2 m m' h h'

/-- The diagonal indices: `φ k ∈ Sₖ`, strictly increasing. -/
noncomputable def diagIdx (hp : Prime p) (z : Nat → Zp p) : Nat → Nat
  | 0 => Classical.choose ((nestedSets hp z 0).2 0)
  | k + 1 => Classical.choose ((nestedSets hp z (k + 1)).2 (diagIdx hp z k + 1))

/-- The diagonal index `φ k` lies in `Sₖ`. -/
theorem diagIdx_mem (hp : Prime p) (z : Nat → Zp p) (k : Nat) :
    (nestedSets hp z k).1 (diagIdx hp z k) := by
  cases k with
  | zero => exact (Classical.choose_spec ((nestedSets hp z 0).2 0)).2
  | succ k => exact (Classical.choose_spec ((nestedSets hp z (k + 1)).2 (diagIdx hp z k + 1))).2

/-- The diagonal indices are strictly increasing. -/
theorem diagIdx_lt_succ (hp : Prime p) (z : Nat → Zp p) (k : Nat) :
    diagIdx hp z k < diagIdx hp z (k + 1) := by
  have := (Classical.choose_spec ((nestedSets hp z (k + 1)).2 (diagIdx hp z k + 1))).1
  show diagIdx hp z k < Classical.choose ((nestedSets hp z (k + 1)).2 (diagIdx hp z k + 1))
  omega

/-- The diagonal subsequence is Cauchy modulo powers of `p`. -/
theorem diag_isCauchy (hp : Prime p) (z : Nat → Zp p) :
    IsCauchy (fun k => z (diagIdx hp z k)) := fun k =>
  ⟨k, fun m hm => nestedSets_modPow hp z k _ _
    (nestedSets_antitone hp z hm _ (diagIdx_mem hp z m)) (diagIdx_mem hp z k)⟩

/-- **Sequential compactness of ℤₚ.** Every sequence of `p`-adic integers has a subsequence
(strictly increasing indices `φ`) converging in ℤₚ, in the sense of `Zp.Converges`. -/
theorem seqCompact (hp : Prime p) (z : Nat → Zp p) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ L, Converges (fun k => z (φ k)) L :=
  ⟨diagIdx hp z, diagIdx_lt_succ hp z, complete _ (diag_isCauchy hp z)⟩

end Zp

end Foundations.Langlands.Padic
