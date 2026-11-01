import Foundations.Probability.Finite

/-!
# Random variables, expectation and variance

A **random variable** on a finite probability space is simply a real-valued function
of the outcome. Its **expectation** `E[X] = ∑ₓ P(x) X(x)` — Huygens' *expectatio*
(*De ratiociniis in ludo aleae*, 1657), the fair price of a gamble — is linear, and its
**variance** `Var X = E[(X − E X)²]` measures its spread around the mean.

We prove linearity of expectation; `Var X = E[X²] − (E X)²`; that for **independent**
random variables `E[XY] = E[X] E[Y]` — by decomposing each variable along its finitely
many values — and hence that variances of independent (indeed of pairwise
*uncorrelated*) variables add; and the two classical tail bounds:

* **Markov's inequality** `P(X ≥ a) ≤ E[X] / a` for `X ≥ 0`, `a > 0`;
* **Chebyshev's inequality** (Bienaymé 1853, Chebyshev 1867)
  `P(|X − E X| ≥ ε) ≤ Var X / ε²`.

Chebyshev's inequality turns a bound on the variance into a bound on the probability of
large deviations; it is the engine of the weak law of large numbers (next file).
-/

namespace Foundations.Probability

open Foundations.Numbers Lean.Grind Classical

/-! ## Order helpers -/

/-- Squares are monotone on the non-negatives. -/
theorem mul_self_le_mul_self {a b : R} (h0 : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b := by
  have h₁ := OrderedRing.mul_le_mul_of_nonneg_left h h0
  have h₂ := OrderedRing.mul_le_mul_of_nonneg_left h (show 0 ≤ b by grind)
  grind

/-- Squares are non-negative. -/
theorem mul_self_nonneg (a : R) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact OrderedRing.mul_nonneg h h
  · have := OrderedRing.mul_nonneg (show 0 ≤ -a by grind) (show 0 ≤ -a by grind); grind

/-- Dividing an inequality `c · p ≤ e` by `c > 0`. -/
theorem le_div_of_mul_le {c p e : R} (hc : 0 < c) (h : c * p ≤ e) : p ≤ e / c := by
  have hi : 0 ≤ 1 / c := Std.le_of_lt (OF.div_pos (by grind) hc)
  have := OrderedRing.mul_le_mul_of_nonneg_left h hi
  have hc0 : c ≠ 0 := fun h => by grind
  have e1 : 1 / c * (c * p) = p := by grind
  have e2 : 1 / c * e = e / c := by grind
  rw [e1, e2] at this; exact this

/-- `ε ≤ |d|` with `ε ≥ 0` gives `ε² ≤ d²`. -/
theorem sq_le_sq_of_le_abs {e d : R} (he : 0 ≤ e) (h : e ≤ OF.abs d) : e * e ≤ d * d := by
  have := mul_self_le_mul_self he h
  rcases OF.abs_cases d with ⟨_, h'⟩ | ⟨_, h'⟩ <;> rw [h'] at this <;> grind

namespace FinProb

variable {α : Type} (P : FinProb α)

/-! ## Expectation -/

/-- **The expectation** `E[X] = ∑ₓ P(x) X(x)`. -/
noncomputable def E (X : α → R) : R := sumL P.pts fun x => P.w x * X x

/-- Probabilities are expectations of indicators. -/
theorem prob_eq_E (A : Event α) : P.prob A = P.E (ind A) := rfl

/-- Expectations only depend on the values on the outcomes. -/
theorem E_congr {X Y : α → R} (h : ∀ x ∈ P.pts, X x = Y x) : P.E X = P.E Y :=
  sumL_congr fun x hx => by rw [h x hx]

/-- **Linearity**: `E[X + Y] = E[X] + E[Y]`. -/
theorem E_add (X Y : α → R) : P.E (fun x => X x + Y x) = P.E X + P.E Y := by
  simp only [E]; rw [← sumL_add]; exact sumL_congr fun x _ => by grind

/-- **Linearity**: `E[cX] = c E[X]`. -/
theorem E_smul (c : R) (X : α → R) : P.E (fun x => c * X x) = c * P.E X := by
  simp only [E]; rw [← sumL_mul_left]; exact sumL_congr fun x _ => by grind

/-- `E[X − Y] = E[X] − E[Y]`. -/
theorem E_sub (X Y : α → R) : P.E (fun x => X x - Y x) = P.E X - P.E Y := by
  simp only [E]; rw [← sumL_sub]; exact sumL_congr fun x _ => by grind

/-- The expectation of a constant. -/
theorem E_const (c : R) : P.E (fun _ => c) = c := by
  simp only [E]; rw [sumL_mul_right, P.sum_one]; grind

/-- **Monotonicity** of expectation. -/
theorem E_mono {X Y : α → R} (h : ∀ x ∈ P.pts, X x ≤ Y x) : P.E X ≤ P.E Y :=
  sumL_le fun x hx => OrderedRing.mul_le_mul_of_nonneg_left (h x hx) (P.w_nonneg x)

/-- Expectations of non-negative variables are non-negative. -/
theorem E_nonneg {X : α → R} (h : ∀ x ∈ P.pts, 0 ≤ X x) : 0 ≤ P.E X := by
  have := P.E_mono (X := fun _ => 0) h; rwa [E_const] at this

/-- Expectation commutes with finite sums of random variables. -/
theorem E_sumN (n : Nat) (X : Nat → α → R) :
    P.E (fun x => sumN n fun i => X i x) = sumN n fun i => P.E (X i) := by
  simp only [E, sumN]
  rw [sumL_comm]
  exact sumL_congr fun x _ => by rw [sumL_mul_left]

/-! ## Variance -/

/-- **The variance** `Var X = E[(X − E X)²]`. -/
noncomputable def Var (X : α → R) : R := P.E fun x => (X x - P.E X) * (X x - P.E X)

/-- Variances are non-negative. -/
theorem Var_nonneg (X : α → R) : 0 ≤ P.Var X := P.E_nonneg fun _ _ => mul_self_nonneg _

/-- **`Var X = E[X²] − (E X)²`.** -/
theorem Var_eq (X : α → R) : P.Var X = P.E (fun x => X x * X x) - P.E X * P.E X := by
  unfold Var
  have : (fun x => (X x - P.E X) * (X x - P.E X)) =
      fun x => (X x * X x - (2 * P.E X) * X x) + P.E X * P.E X := by funext x; grind
  rw [this, E_add, E_sub, E_smul, E_const]; grind

/-- `Var(cX) = c² Var X`. -/
theorem Var_smul (c : R) (X : α → R) : P.Var (fun x => c * X x) = c * c * P.Var X := by
  unfold Var
  rw [E_smul, show (fun x => (c * X x - c * P.E X) * (c * X x - c * P.E X)) =
    fun x => (c * c) * ((X x - P.E X) * (X x - P.E X)) from funext fun x => by grind, E_smul]

/-- Shifting by a constant does not change the variance. -/
theorem Var_add_const (X : α → R) (c : R) : P.Var (fun x => X x + c) = P.Var X := by
  unfold Var
  rw [E_add, E_const]
  exact P.E_congr fun x _ => by grind

/-- The **covariance** `Cov(X, Y) = E[XY] − E[X] E[Y]`. -/
noncomputable def Cov (X Y : α → R) : R := P.E (fun x => X x * Y x) - P.E X * P.E Y

/-- **Variance of a sum**: `Var(X + Y) = Var X + Var Y + 2 Cov(X, Y)`. -/
theorem Var_add (X Y : α → R) : P.Var (fun x => X x + Y x) = P.Var X + P.Var Y + 2 * P.Cov X Y := by
  rw [Var_eq, Var_eq, Var_eq, Cov, E_add]
  have : (fun x => (X x + Y x) * (X x + Y x)) =
      fun x => (X x * X x + Y x * Y x) + 2 * (X x * Y x) := by funext x; grind
  rw [this, E_add, E_add, E_smul]; grind

/-- Two random variables are **uncorrelated** if `Cov(X, Y) = 0`, i.e. `E[XY] = E[X] E[Y]`. -/
def Uncorr (X Y : α → R) : Prop := P.Cov X Y = 0

/-- Variances of uncorrelated variables add. -/
theorem Var_add_of_uncorr {X Y : α → R} (h : P.Uncorr X Y) :
    P.Var (fun x => X x + Y x) = P.Var X + P.Var Y := by
  rw [Var_add]; unfold Uncorr at h; rw [h]; grind

/-- Covariance is additive in the first argument, over finite sums. -/
theorem Cov_sumN (n : Nat) (X : Nat → α → R) (Y : α → R) :
    P.Cov (fun x => sumN n fun i => X i x) Y = sumN n fun i => P.Cov (X i) Y := by
  unfold Cov
  have : (fun x => (sumN n fun i => X i x) * Y x) = fun x => sumN n fun i => X i x * Y x := by
    funext x; simp only [sumN]; rw [sumL_mul_right]
  rw [this, E_sumN, E_sumN, sumN, sumN, sumN, ← sumL_mul_right, ← sumL_sub]

/-- **Bienaymé's identity**: the variance of a sum of pairwise uncorrelated random
variables is the sum of their variances. -/
theorem Var_sumN (n : Nat) (X : Nat → α → R) (h : ∀ i j, i < j → j < n → P.Uncorr (X i) (X j)) :
    P.Var (fun x => sumN n fun i => X i x) = sumN n fun i => P.Var (X i) := by
  induction n with
  | zero =>
      simp only [sumN, List.range_zero, sumL_nil]
      rw [Var_eq]; simp only [E_const]; grind
  | succ n ih =>
      have hsplit : ∀ f : Nat → R, sumN (n + 1) f = sumN n f + f n := by
        intro f; simp only [sumN]; rw [List.range_succ, sumL_append]; simp; grind
      have : (fun x => sumN (n + 1) fun i => X i x) = fun x => (sumN n fun i => X i x) + X n x := by
        funext x; exact hsplit _
      rw [this, Var_add, ih fun i j hij hj => h i j hij (by omega), hsplit, Cov_sumN]
      have hz : (sumN n fun i => P.Cov (X i) (X n)) = 0 := by
        simp only [sumN]
        rw [sumL_congr (g := fun _ => 0) fun i hi => h i n (List.mem_range.1 hi) (by omega),
          sumL_zero]
      rw [hz]; grind

/-! ## Independence and `E[XY] = E[X] E[Y]` -/

/-- Random variables `X` and `Y` are **independent** if `P(X = a, Y = b) = P(X = a) P(Y = b)`
for all values `a`, `b`. -/
def IndepRV (X Y : α → R) : Prop :=
  ∀ a b, P.prob (fun x => X x = a ∧ Y x = b) = P.prob (fun x => X x = a) * P.prob (fun x => Y x = b)

/-- Removing duplicates from a list. -/
noncomputable def dedupL : List R → List R
  | [] => []
  | a :: l => if a ∈ dedupL l then dedupL l else a :: dedupL l

/-- Deduplication keeps the elements. -/
theorem mem_dedupL {a : R} : ∀ {l : List R}, a ∈ l → a ∈ dedupL l
  | b :: l, h => by
      simp only [dedupL]
      rcases List.mem_cons.1 h with rfl | h
      · split
        · assumption
        · exact List.mem_cons_self ..
      · have := mem_dedupL h
        split
        · exact this
        · exact List.mem_cons_of_mem _ this

/-- Deduplication removes duplicates. -/
theorem nodup_dedupL : ∀ l : List R, (dedupL l).Nodup
  | [] => List.nodup_nil
  | b :: l => by
      simp only [dedupL]
      split
      · exact nodup_dedupL l
      · next h => exact List.nodup_cons.2 ⟨h, nodup_dedupL l⟩

/-- The (distinct) values taken by `X` on the outcomes. -/
noncomputable def vals (X : α → R) : List R := dedupL (P.pts.map X)

/-- **Decomposition along the values**: `X(x) = ∑_a a · 1[X = a](x)`. -/
theorem decomp_vals (X : α → R) (x : α) :
    ∀ V : List R, V.Nodup → X x ∈ V → sumL V (fun a => a * ind (fun y => X y = a) x) = X x := by
  intro V
  induction V with
  | nil => intro _ h; simp at h
  | cons b V ih =>
      intro hnd hmem
      rw [List.nodup_cons] at hnd
      simp only [sumL_cons]
      by_cases hb : X x = b
      · have hrest : sumL V (fun a => a * ind (fun y => X y = a) x) = 0 := by
          rw [← sumL_zero V]
          refine sumL_congr fun a ha => ?_
          have : ¬ X x = a := fun h => hnd.1 (hb ▸ h ▸ ha)
          simp [ind, this]; grind
        rw [hrest]; simp [ind, hb]; grind
      · have hx : X x ∈ V := (List.mem_cons.1 hmem).resolve_left hb
        rw [ih hnd.2 hx]; simp [ind, hb]; grind

/-- The expectation along the values: `E[X] = ∑_a a P(X = a)`. -/
theorem E_eq_vals (X : α → R) :
    P.E X = sumL (P.vals X) fun a => a * P.prob (fun y => X y = a) := by
  have h : ∀ x ∈ P.pts, X x = sumL (P.vals X) (fun a => a * ind (fun y => X y = a) x) :=
    fun x hx => (decomp_vals X x _ (nodup_dedupL _) (mem_dedupL (List.mem_map_of_mem hx))).symm
  rw [P.E_congr h]
  simp only [E, prob]
  rw [sumL_congr (fun x _ => (sumL_mul_left _ _ _).symm), sumL_comm]
  refine sumL_congr fun a _ => ?_
  rw [← sumL_mul_left]; exact sumL_congr fun x _ => by grind

/-- **Independence implies `E[XY] = E[X] E[Y]`.** -/
theorem E_mul_of_indep {X Y : α → R} (h : P.IndepRV X Y) : P.E (fun x => X x * Y x) = P.E X * P.E Y := by
  have hX : ∀ x ∈ P.pts, X x = sumL (P.vals X) (fun a => a * ind (fun y => X y = a) x) :=
    fun x hx => (decomp_vals X x _ (nodup_dedupL _) (mem_dedupL (List.mem_map_of_mem hx))).symm
  have hY : ∀ x ∈ P.pts, Y x = sumL (P.vals Y) (fun b => b * ind (fun y => Y y = b) x) :=
    fun x hx => (decomp_vals Y x _ (nodup_dedupL _) (mem_dedupL (List.mem_map_of_mem hx))).symm
  -- `E[XY] = ∑_a ∑_b a b P(X = a, Y = b)`
  have h₁ : P.E (fun x => X x * Y x) = sumL (P.vals X) fun a => sumL (P.vals Y) fun b =>
      a * b * P.prob (fun y => X y = a ∧ Y y = b) := by
    rw [P.E_congr (Y := fun x => sumL (P.vals X) fun a => sumL (P.vals Y) fun b =>
        a * b * (ind (fun y => X y = a) x * ind (fun y => Y y = b) x)) fun x hx => by
      rw [hX x hx, hY x hx, ← sumL_mul_right]
      refine sumL_congr fun a _ => ?_
      rw [← sumL_mul_left]; exact sumL_congr fun b _ => by grind]
    simp only [E, prob]
    rw [sumL_congr (fun x _ => (sumL_mul_left _ _ _).symm), sumL_comm]
    refine sumL_congr fun a _ => ?_
    rw [sumL_congr (fun x _ => (sumL_mul_left _ _ _).symm), sumL_comm]
    refine sumL_congr fun b _ => ?_
    rw [← sumL_mul_left]; exact sumL_congr fun x _ => by rw [ind_and]; grind
  rw [h₁, E_eq_vals P X, E_eq_vals P Y, ← sumL_mul_right]
  refine sumL_congr fun a _ => ?_
  rw [← sumL_mul_left]
  exact sumL_congr fun b _ => by rw [h a b]; grind

/-- Independent random variables are uncorrelated. -/
theorem uncorr_of_indep {X Y : α → R} (h : P.IndepRV X Y) : P.Uncorr X Y := by
  unfold Uncorr Cov; rw [E_mul_of_indep P h]; grind

/-- **The variance of a sum of independent random variables** is the sum of the
variances. -/
theorem Var_add_of_indep {X Y : α → R} (h : P.IndepRV X Y) :
    P.Var (fun x => X x + Y x) = P.Var X + P.Var Y :=
  P.Var_add_of_uncorr (P.uncorr_of_indep h)

/-! ## Markov and Chebyshev -/

/-- **Markov's inequality.** For a non-negative random variable `X` and `a > 0`,
`P(X ≥ a) ≤ E[X] / a`. -/
theorem markov {X : α → R} (hX : ∀ x ∈ P.pts, 0 ≤ X x) {a : R} (ha : 0 < a) :
    P.prob (fun x => a ≤ X x) ≤ P.E X / a := by
  refine le_div_of_mul_le ha ?_
  rw [prob_eq_E, ← E_smul]
  refine P.E_mono fun x hx => ?_
  rcases ind_cases (fun y => a ≤ X y) x with ⟨h, h'⟩ | ⟨_, h'⟩ <;> rw [h']
  · grind
  · have := hX x hx; grind

/-- **Chebyshev's inequality.** For `ε > 0`, `P(|X − E X| ≥ ε) ≤ Var X / ε²`. -/
theorem chebyshev (X : α → R) {ε : R} (hε : 0 < ε) :
    P.prob (fun x => ε ≤ OF.abs (X x - P.E X)) ≤ P.Var X / (ε * ε) := by
  have hm := P.markov (X := fun x => (X x - P.E X) * (X x - P.E X)) (fun x _ => mul_self_nonneg _)
    (a := ε * ε) (by have := OrderedRing.mul_lt_mul_of_pos_left hε hε; grind)
  refine Std.le_trans (P.prob_mono fun x hx => ?_) hm
  exact sq_le_sq_of_le_abs (Std.le_of_lt hε) hx

end FinProb

end Foundations.Probability
