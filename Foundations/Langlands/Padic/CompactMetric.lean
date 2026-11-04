import Foundations.Langlands.Padic.Compact
import Foundations.Langlands.Padic.QpComplete
import Foundations.Topology.Compact

/-!
# ℤₚ as a compact metric space

The Topology part works with metric spaces whose distances are real numbers (`Topology.
MetricSpace`). Here ℤₚ becomes such a space with the `p`-adic distance
`d(x, y) = |x − y|ₚ`, computed in ℚₚ (`Qp.abs`) and viewed in ℝ through `ℚ ⊆ ℝ`.
The triangle inequality comes from the stronger ultrametric inequality
`|a + b|ₚ ≤ max(|a|ₚ, |b|ₚ)` (`Qp.abs_ultrametric`).

We check that metric convergence in this space is exactly the congruence convergence
`Zp.Converges` of the earlier files (`Zp.converges_iff`): `|x − L|ₚ ≤ p^(−k)` means
`x ≡ L (mod pᵏ)` (`Qp.abs_ofZp_le_iff`), and the numbers `p^(−k)` become smaller than any real
`ε > 0`. With the digit-by-digit compactness theorem `Zp.seqCompact` this gives
`Zp.isSeqCompact`, and the Topology part's equivalence of sequential compactness and compactness
for metric spaces (`isCompact_iff_isSeqCompact`) gives **`Zp.isCompact`**: ℤₚ is compact —
every cover of ℤₚ by open sets has a finite subcover.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- `v(−1) = 0`, since `v(−1) + v(−1) = v(1) = 0`. -/
theorem val_neg_one : val (-1 : Qp p) = 0 := by
  have h1 : (-1 : Qp p) ≠ 0 := fun h => zero_ne_one (p := p) (by grind)
  have h := val_mul h1 h1
  rw [show (-1 : Qp p) * -1 = 1 by grind] at h
  have h0 : val (1 : Qp p) = 0 := by
    have := val_mul (p := p) (q := 1) (r := 1) (fun h => zero_ne_one (p := p) h.symm)
      (fun h => zero_ne_one (p := p) h.symm)
    rw [show (1 : Qp p) * 1 = 1 by grind] at this; omega
  omega

/-- `|−q|ₚ = |q|ₚ`. -/
theorem abs_neg (q : Qp p) : abs (-q) = abs q := by
  by_cases hq : q = 0
  · subst hq; rw [show -(0 : Qp p) = 0 by grind]
  have h1 : (-1 : Qp p) ≠ 0 := fun h => zero_ne_one (p := p) (by grind)
  have hnq : -q ≠ 0 := fun h => hq (by grind)
  rw [abs_of_ne hnq, abs_of_ne hq, show -q = -1 * q by grind, val_mul h1 hq, val_neg_one,
    Int.zero_add]

/-- `|x − y|ₚ = |y − x|ₚ` for `p`-adic integers. -/
theorem abs_ofZp_sub_comm (x y : Zp p) : abs (ofZp (x - y)) = abs (ofZp (y - x)) := by
  rw [show x - y = -1 * (y - x) by grind, ofZp_mul, show ofZp (-1 : Zp p) = -1 from rfl,
    show -1 * ofZp (y - x) = -(ofZp (y - x)) by grind, abs_neg]

/-- The `p`-adic absolute value satisfies the ordinary triangle inequality. -/
theorem abs_add_le (q r : Qp p) : abs (q + r) ≤ abs q + abs r := by
  have := abs_nonneg q; have := abs_nonneg r
  rcases abs_ultrametric q r with h | h <;> grind

/-- **The numbers `p^(−k)` tend to `0`.** For every rational `δ > 0` some `p^(−k)` is
smaller than `δ`. -/
theorem exists_zpow_lt {δ : Q} (hδ : 0 < δ) : ∃ k : Nat, (p : Q) ^ (-(k : Int)) < δ := by
  obtain ⟨n, hn⟩ := Q.archimedean δ⁻¹
  refine ⟨n, ?_⟩
  have hp2 := two_le_p (p := p)
  have hlt : (n : Q) < ((p ^ n : Nat) : Q) :=
    OrderedRing.natCast_lt_natCast_of_lt _ _ (Zp.lt_pow hP.prime.1 n)
  rw [Semiring.natCast_pow] at hlt
  rw [Field.zpow_neg, Field.zpow_natCast]
  have hP0 : 0 < (p : Q) ^ n := npow_pos (by grind) n
  have hδ0 : δ ≠ 0 := by grind
  have hPne : (p : Q) ^ n ≠ 0 := by grind
  have e1 := Field.mul_inv_cancel hδ0
  have e2 := Field.mul_inv_cancel hPne
  have hPi := inv_pos' hP0
  -- `δ⁻¹ < pⁿ`; multiply by `δ · (pⁿ)⁻¹ > 0`.
  have hm : 0 < δ * ((p : Q) ^ n)⁻¹ := OrderedRing.mul_pos hδ hPi
  have := OrderedRing.mul_lt_mul_of_pos_left (Std.lt_trans hn hlt) hm
  rw [show δ * ((p : Q) ^ n)⁻¹ * δ⁻¹ = (δ * δ⁻¹) * ((p : Q) ^ n)⁻¹ by grind,
    show δ * ((p : Q) ^ n)⁻¹ * (p : Q) ^ n = δ * ((p : Q) ^ n * ((p : Q) ^ n)⁻¹) by grind,
    e1, e2] at this
  grind

end Qp

namespace Zp

variable {p : Nat} [hP : PrimeP p]

/-- The **`p`-adic distance** `d(x, y) = |x − y|ₚ` on ℤₚ, as a real number. -/
noncomputable def dist (x y : Zp p) : R := R.ofQ (Qp.abs (Qp.ofZp (x - y)))

/-- **ℤₚ is a metric space** under the `p`-adic distance `d(x, y) = |x − y|ₚ`. -/
noncomputable instance instMetricSpace : Topology.MetricSpace (Zp p) where
  dist := dist
  dist_self x := by
    unfold dist
    rw [show x - x = 0 by grind, (Qp.abs_eq_zero (p := p) (q := Qp.ofZp 0)).2 rfl]; rfl
  eq_of_dist_eq_zero {x y} h := by
    unfold dist at h
    have h' : Qp.abs (Qp.ofZp (x - y)) = 0 := Padic.ofQ_inj (h.trans rfl)
    have h'' := Qp.ofZp_injective ((Qp.abs_eq_zero.1 h').trans rfl)
    grind
  dist_comm x y := by unfold dist; rw [Qp.abs_ofZp_sub_comm]
  dist_triangle x y z := by
    unfold dist
    rw [show x - z = (x - y) + (y - z) by grind, Qp.ofZp_add, ← R.ofQ_add]
    exact R.ofQ_le.2 (Qp.abs_add_le _ _)

/-- The metric distance on ℤₚ is `|x − y|ₚ`. -/
theorem dist_eq (x y : Zp p) :
    Topology.dist x y = R.ofQ (Qp.abs (Qp.ofZp (x - y))) := rfl

/-- **Metric convergence in ℤₚ is congruence convergence.** A sequence converges to `L` for the
distance `|x − y|ₚ` iff for every `k` it is eventually congruent to `L` modulo `pᵏ`. -/
theorem converges_iff (s : Nat → Zp p) (L : Zp p) :
    Topology.Converges s L ↔ Converges s L := by
  have hp2 := Qp.two_le_p (p := p)
  constructor
  · intro h k
    have hpos : (0 : R) < R.ofQ ((p : Q) ^ (-(k : Int))) := by
      have := R.ofQ_lt.2 (zpow_pos (show (0 : Q) < p by grind) (-(k : Int)))
      exact this
    obtain ⟨N, hN⟩ := h _ hpos
    refine ⟨N, fun m hm => ?_⟩
    have h1 := R.ofQ_lt.1 (hN m hm)
    exact modPow_iff_sub.2 ((Qp.abs_ofZp_le_iff _ k).1 (Std.le_of_lt h1))
  · intro h ε hε
    obtain ⟨δ, hδ, hδε⟩ := R.pos_iff_rat.1 hε
    obtain ⟨k, hk⟩ := Qp.exists_zpow_lt (p := p) hδ
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, fun m hm => ?_⟩
    have h1 := (Qp.abs_ofZp_le_iff _ k).2 (modPow_iff_sub.1 (hN m hm))
    rw [dist_eq]
    exact Std.lt_of_lt_of_le (R.ofQ_lt.2 (Std.lt_of_le_of_lt h1 hk)) hδε

/-- **ℤₚ is sequentially compact** as a metric space: every sequence of `p`-adic integers has a
subsequence converging for the distance `|x − y|ₚ`. -/
theorem isSeqCompact : Topology.IsSeqCompact (fun _ : Zp p => True) := by
  intro s _
  obtain ⟨φ, hφ, L, hL⟩ := seqCompact hP.prime s
  exact ⟨φ, hφ, L, trivial, (converges_iff _ _).2 hL⟩

/-- **Compactness of ℤₚ.** In the metric topology of `|x − y|ₚ`, every cover of ℤₚ by open
sets has a finite subcover. -/
theorem isCompact : Topology.IsCompact (Topology.Topology.metric (Zp p)) (fun _ => True) :=
  (Topology.isCompact_iff_isSeqCompact _).2 isSeqCompact

end Zp

end Foundations.Langlands.Padic
