import Foundations.Topology.Connected

/-!
# Fixed-point theorems

Two classical answers to the question "when must an equation `f x = x` have a solution?".

**Banach's fixed-point theorem** (Stefan Banach, doctoral thesis, 1920/1922): on a *complete*
metric space, a **contraction** (a map shrinking all distances by a factor `q < 1`) has exactly one
fixed point, and the iterates `x₀, f x₀, f (f x₀), …` of *any* starting point converge to it. The
proof is constructive in spirit — it is an algorithm with an error bound `qⁿ d(x₁, x₀)/(1 − q)` —
and is the engine behind Picard's existence theorem for differential equations and Newton's
method. Completeness is essential: on `ℚ` the contraction `x ↦ x/2 + 1/x` has no fixed point
(it would be `√2`).

**Brouwer's fixed-point theorem** (L. E. J. Brouwer, 1911) says that every continuous map of a
closed ball to itself has a fixed point. We prove dimension one: every continuous
`f : [0, 1] → [0, 1]` has a fixed point — the intermediate value theorem applied to `x − f x`. There
is an irony here: Brouwer was the founder of **intuitionism**, which rejects non-constructive
existence proofs, and later disowned his own theorem in its classical form; indeed no algorithm
can locate the fixed point of an arbitrary continuous map, and our proof — via suprema and the
law of excluded middle — produces no way to compute it.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

variable {X : Type} [MetricSpace X]

/-! ## Complete metric spaces -/

/-- A sequence is **Cauchy** if its terms become arbitrarily close to each other. -/
def IsCauchy (s : Nat → X) : Prop :=
  ∀ ε : R, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → dist (s m) (s n) < ε

/-- A metric space is **complete** if every Cauchy sequence converges. -/
def Complete (X : Type) [MetricSpace X] : Prop := ∀ s : Nat → X, IsCauchy s → ∃ L, Converges s L

/-- **ℝ is complete** (the Cauchy completeness theorem of `Numbers/Analysis`). -/
theorem complete_R : Complete R := fun _ h => cauchy_complete h

/-! ## Banach's fixed-point theorem -/

/-- The orbit `x₀, f x₀, f (f x₀), …`. -/
def orbit (f : X → X) (x₀ : X) : Nat → X
  | 0 => x₀
  | n + 1 => f (orbit f x₀ n)

/-- Consecutive orbit points get closer geometrically: `d(xₙ₊₁, xₙ) ≤ qⁿ d(x₁, x₀)`. -/
theorem dist_orbit_succ {f : X → X} {q : R} (hq0 : 0 ≤ q)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y) (x₀ : X) (n : Nat) :
    dist (orbit f x₀ (n + 1)) (orbit f x₀ n) ≤ q ^ n * dist (orbit f x₀ 1) x₀ := by
  induction n with
  | zero => show dist (orbit f x₀ 1) x₀ ≤ 1 * _; clear hf; grind
  | succ n ih =>
    have := hf (orbit f x₀ (n + 1)) (orbit f x₀ n)
    have := OrderedRing.mul_le_mul_of_nonneg_left ih hq0
    show dist (f (orbit f x₀ (n + 1))) (f (orbit f x₀ n)) ≤ q ^ (n + 1) * _
    rw [pow_succ']; grind

/-- Far orbit points: `d(xₙ₊ₖ, xₙ) ≤ qⁿ d(x₁, x₀) (1 − qᵏ)/(1 − q)`. -/
theorem dist_orbit_add {f : X → X} {q : R} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y) (x₀ : X) (n k : Nat) :
    dist (orbit f x₀ (n + k)) (orbit f x₀ n) ≤
      q ^ n * dist (orbit f x₀ 1) x₀ * ((1 - q ^ k) / (1 - q)) := by
  induction k with
  | zero =>
    show dist (orbit f x₀ n) (orbit f x₀ n) ≤ _ * ((1 - 1) / (1 - q))
    rw [dist_self]; grind
  | succ k ih =>
    have h1 := dist_orbit_succ hq0 hf x₀ (n + k)
    have h2 := dist_triangle (orbit f x₀ (n + k + 1)) (orbit f x₀ (n + k)) (orbit f x₀ n)
    rw [← Nat.add_assoc]
    have e : q ^ (n + k) = q ^ n * q ^ k := R.pow_add' q n k
    have e2 : q ^ (k + 1) = q ^ k * q := pow_succ' q k
    have hne : 1 - q ≠ 0 := by grind
    rw [e] at h1
    rw [e2]
    have i1 := Field.mul_inv_cancel hne
    rw [Field.div_eq_mul_inv] at ih ⊢
    clear hf
    generalize q ^ n = a at ih h1 ⊢
    generalize q ^ k = P at ih h1 ⊢
    generalize (1 - q)⁻¹ = J at ih i1 ⊢
    generalize dist (orbit f x₀ 1) x₀ = D at ih h1 ⊢
    have key : a * P * D + a * D * ((1 - P) * J) = a * D * ((1 - P * q) * J) := by grind
    grind

/-- **Banach's fixed-point theorem.** On a complete metric space, a contraction `f`
(`d(f x, f y) ≤ q d(x, y)` with `0 ≤ q < 1`) has a unique fixed point, and the orbit of every
starting point converges to it. -/
theorem banach_fixed_point (hX : Complete X) {f : X → X} {q : R} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y) (x₀ : X) :
    ∃ x, f x = x ∧ Converges (orbit f x₀) x ∧ ∀ y, f y = y → y = x := by
  let D := dist (orbit f x₀ 1) x₀
  have hD : 0 ≤ D := dist_nonneg _ _
  have hpos : 0 < 1 - q := by grind
  -- `d(xₘ, x_N) ≤ q^N D/(1 − q)` for `m ≥ N`.
  have hbound : ∀ N m, N ≤ m → dist (orbit f x₀ m) (orbit f x₀ N) ≤ q ^ N * D / (1 - q) := by
    intro N m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = N + k := ⟨m - N, by omega⟩
    have h := dist_orbit_add hq0 hq1 hf x₀ N k
    have hqk : 0 ≤ q ^ k := pow_le_pow_left.pow_nonneg hq0 k
    have hqN : 0 ≤ q ^ N := pow_le_pow_left.pow_nonneg hq0 N
    have hinv := Field.mul_inv_cancel (show 1 - q ≠ 0 by grind)
    have hi : 0 < (1 - q)⁻¹ := Field.IsOrdered.inv_pos_iff.2 hpos
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hqN hD) (Std.le_of_lt hi)
    have := OrderedRing.mul_nonneg this hqk
    rw [Field.div_eq_mul_inv] at h ⊢
    clear hf
    grind
  have hqpow := tendsto_pow_zero hq0 hq1
  -- The orbit is Cauchy …
  have hc : IsCauchy (orbit f x₀) := fun ε hε => by
    clear hf
    obtain ⟨N, hN⟩ := hqpow (ε * (1 - q) / (2 * (D + 1))) (div_pos (OrderedRing.mul_pos hε hpos)
      (by grind))
    refine ⟨N, fun m n hm hn => ?_⟩
    have k1 := hbound N m hm
    have k2 := hbound N n hn
    have k3 := dist_triangle (orbit f x₀ m) (orbit f x₀ N) (orbit f x₀ n)
    have k4 := dist_comm (orbit f x₀ N) (orbit f x₀ n)
    have k5 := abs_lt.1 (hN N (Nat.le_refl N))
    simp only at k5
    have hqN : 0 ≤ q ^ N := pow_le_pow_left.pow_nonneg hq0 N
    -- `q^N D/(1 − q) < ε/2`.
    have k6 : q ^ N * D / (1 - q) < ε / 2 := by
      have a1 := OrderedRing.mul_le_mul_of_nonneg_left (by grind : D ≤ D + 1) hqN
      have a2 := OrderedRing.mul_lt_mul_of_pos_right (by grind : q ^ N < ε * (1 - q) / (2 * (D + 1)))
        (by grind : (0 : R) < D + 1)
      have e1 : ε * (1 - q) / (2 * (D + 1)) * (D + 1) = ε * (1 - q) / 2 := by grind
      have e2 : q ^ N * D / (1 - q) = q ^ N * D * (1 - q)⁻¹ := Field.div_eq_mul_inv _ _
      have hi : 0 < (1 - q)⁻¹ := Field.IsOrdered.inv_pos_iff.2 hpos
      have a3 := OrderedRing.mul_lt_mul_of_pos_right
        (show q ^ N * D < ε * (1 - q) / 2 by grind) hi
      have e3 : ε * (1 - q) / 2 * (1 - q)⁻¹ = ε / 2 := by
        have := Field.mul_inv_cancel (show 1 - q ≠ 0 by grind); grind
      grind
    grind
  -- … hence converges to some `x`, which is fixed because `f` is continuous.
  obtain ⟨x, hx⟩ := hX _ hc
  have hcont := continuous_of_lipschitz hq0 hf
  have h1 : Converges (fun n => f (orbit f x₀ n)) (f x) :=
    (continuousAt_iff_seq f x).1 (hcont x) _ hx
  have h2 : Converges (fun n => f (orbit f x₀ n)) x := fun ε hε => by
    obtain ⟨N, hN⟩ := hx ε hε
    exact ⟨N, fun n hn => hN (n + 1) (by omega)⟩
  have hfx : f x = x := h1.unique h2
  refine ⟨x, hfx, hx, fun y hy => ?_⟩
  -- Uniqueness: `d(y, x) = d(f y, f x) ≤ q d(y, x)` forces `d(y, x) = 0`.
  have := hf y x
  clear hf hbound hc
  rw [hy, hfx] at this
  have := dist_nonneg y x
  have h0 : dist y x = 0 := by
    rcases (by grind : dist y x = 0 ∨ 0 < dist y x) with h | h
    · exact h
    · have := OrderedRing.mul_lt_mul_of_pos_right hq1 h; grind
  exact eq_of_dist_eq_zero h0

/-! ## Brouwer's fixed-point theorem in dimension one -/

/-- **Brouwer's fixed-point theorem, dimension 1.** Every `f` continuous at every point of `[0, 1]`
and mapping `[0, 1]` into itself has a fixed point. -/
theorem brouwer_one_dim {f : R → R} (hf : ∀ x, 0 ≤ x → x ≤ 1 → R.ContinuousAt f x)
    (hmaps : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ f x ∧ f x ≤ 1) : ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ f x = x := by
  -- Apply the intermediate value theorem to `g x = x − f x`, with `g 0 ≤ 0 ≤ g 1`.
  obtain ⟨c, h0, h1, hc⟩ := intermediate_value_connected (f := fun x => x - f x) (a := 0) (b := 1)
    (v := 0) (by grind) (fun x h0 h1 => continuousAt_sub (continuousAt_id x) (hf x h0 h1))
    (by have := hmaps 0 (Std.le_refl 0) (by grind); show 0 - f 0 ≤ 0; grind)
    (by have := hmaps 1 (by grind) (Std.le_refl 1); show 0 ≤ 1 - f 1; grind)
  exact ⟨c, h0, h1, by have : c - f c = 0 := hc; grind⟩

end Foundations.Topology
