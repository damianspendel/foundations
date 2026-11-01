import Foundations.Probability.RandomVariables

/-!
# The weak law of large numbers

Jacob Bernoulli spent twenty years on what he called his *theorema aureum*, published
posthumously in the *Ars Conjectandi* (1713): in a long run of independent trials, the
relative frequency of success is, with probability as close to `1` as one wishes,
as close to the true probability of success as one wishes. It is the theorem that
links probability to observed frequencies — the mathematical backbone of the
frequentist interpretation, and of every statistical estimate.

We prove it in Chebyshev's form (1867). Repeat a finite experiment `P` independently `n`
times: the **product space** `Pⁿ` has as outcomes all lists `t = (t₀, …, t_{n−1})` of
outcomes of `P`, with weight `P(t₀) ⋯ P(t_{n−1})`. A random variable `X` on `P` gives `n`
random variables `Xᵢ(t) = X(tᵢ)` on `Pⁿ`, which are identically distributed and pairwise
independent; in particular `E[Xᵢ] = μ := E[X]`, `Var Xᵢ = σ² := Var X`, and
`E[Xᵢ Xⱼ] = μ²` for `i ≠ j`. For the sample mean `Sₙ/n = (X₀ + ⋯ + X_{n−1})/n` Bienaymé's
identity gives `Var(Sₙ/n) = σ²/n`, and Chebyshev's inequality yields

`P(|Sₙ/n − μ| ≥ ε) ≤ σ² / (n ε²) → 0`  (as `n → ∞`).

The *strong* law (almost sure convergence, Borel 1909 and Kolmogorov 1930) concerns an
infinite sequence of trials and needs measure theory; it is not treated here.
-/

namespace Foundations.Probability

open Foundations.Numbers Lean.Grind Classical
open FinProb (sumN)

/-! ## Arithmetic helpers -/

/-- The cast `ℕ → R` is monotone. -/
theorem natCast_le {n m : Nat} (h : n ≤ m) : (n : R) ≤ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have : ((n + k : Nat) : R) = n + k := by grind
  have : (0 : R) ≤ k := by grind
  grind

/-- Positive naturals are positive reals. -/
theorem natCast_pos {n : Nat} (h : 0 < n) : (0 : R) < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have : ((k + 1 : Nat) : R) = k + 1 := by grind
  have : (0 : R) ≤ k := by grind
  grind

/-- The sum of `n` copies of a constant. -/
theorem sumN_const (n : Nat) (c : R) : sumN n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumN]; grind
  | succ n ih =>
      simp only [sumN] at ih ⊢
      rw [List.range_succ, sumL_append, ih]; simp; grind

/-- Dividing an inequality `a ≤ b · c` by `c > 0`. -/
theorem div_le_of_le_mul {a b c : R} (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  have hi : 0 ≤ 1 / c := Std.le_of_lt (OF.div_pos (by grind) hc)
  have := OrderedRing.mul_le_mul_of_nonneg_left h hi
  have hc0 : c ≠ 0 := fun h => by grind
  have e1 : 1 / c * (b * c) = b := by grind
  have e2 : 1 / c * a = a / c := by grind
  rw [e1, e2] at this; exact this

/-! ## Sums over lists of lists -/

section Lists
variable {α : Type}

/-- Sums over a `flatMap`. -/
theorem sumL_flatMap {β : Type} (l : List α) (g : α → List β) (F : β → R) :
    sumL (l.flatMap g) F = sumL l (fun a => sumL (g a) F) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, sumL_append, ih, sumL_cons]

/-- All lists of length `n` with entries from `l`. -/
def powL (l : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => l.flatMap fun a => (powL l n).map fun t => a :: t

/-- Sums over `powL`, peeling off the first entry. -/
theorem sumL_powL_succ (l : List α) (n : Nat) (F : List α → R) :
    sumL (powL l (n + 1)) F = sumL l fun a => sumL (powL l n) fun t => F (a :: t) := by
  rw [powL, sumL_flatMap]; exact sumL_congr fun a _ => sumL_map _ _ _

/-- The members of `powL l n` have length `n`. -/
theorem length_of_mem_powL {l : List α} : ∀ {n : Nat} {t : List α}, t ∈ powL l n → t.length = n
  | 0, t, h => by simp [powL] at h; subst h; rfl
  | n + 1, t, h => by
      simp only [powL, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, _, s, hs, rfl⟩ := h
      simp [length_of_mem_powL hs]

/-- The product weight of a list of outcomes. -/
def wprod (w : α → R) : List α → R
  | [] => 1
  | a :: t => w a * wprod w t

end Lists

namespace FinProb

variable {α : Type} (P : FinProb α)

/-- **The product space** `Pⁿ`: `n` independent repetitions of the experiment `P`. -/
noncomputable def pow (n : Nat) : FinProb (List α) where
  pts := powL P.pts n
  w := wprod P.w
  w_nonneg := by
    intro t
    induction t with
    | nil => simp [wprod]; grind
    | cons a t ih => exact OrderedRing.mul_nonneg (P.w_nonneg a) ih
  sum_one := by
    induction n with
    | zero => simp [powL, wprod]; grind
    | succ n ih =>
        rw [sumL_powL_succ]
        simp only [wprod]
        rw [sumL_congr (g := fun a => P.w a * 1) fun a _ => by rw [sumL_mul_left, ih]]
        rw [sumL_mul_right, P.sum_one]; grind

/-- Expectations on `Pⁿ⁺¹`: average over the first coordinate of the expectation over
the remaining `n`. -/
theorem E_pow_succ (n : Nat) (F : List α → R) :
    (P.pow (n + 1)).E F = P.E fun a => (P.pow n).E fun t => F (a :: t) := by
  show sumL (powL P.pts (n + 1)) (fun t => wprod P.w t * F t) = _
  rw [sumL_powL_succ]
  refine sumL_congr fun a _ => ?_
  simp only [wprod, E, pow]
  rw [← sumL_mul_left]; exact sumL_congr fun t _ => by grind

/-- The `i`-th coordinate random variable `Xᵢ(t) = X(tᵢ)` on the product space. -/
def coord (X : α → R) (i : Nat) (t : List α) : R := (t.map X).getD i 0

/-- The coordinates of a list beginning with `a`. -/
@[simp] theorem coord_cons_zero (X : α → R) (a : α) (t : List α) : coord X 0 (a :: t) = X a := rfl

/-- The coordinates of a list beginning with `a`, shifted. -/
@[simp] theorem coord_cons_succ (X : α → R) (a : α) (t : List α) (i : Nat) :
    coord X (i + 1) (a :: t) = coord X i t := rfl

/-- **The coordinates are distributed like `X`**: `E[Xᵢ] = E[X]`. -/
theorem E_coord (X : α → R) : ∀ {n i : Nat}, i < n → (P.pow n).E (coord X i) = P.E X
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => by
      rw [E_pow_succ]; simp only [coord_cons_zero, E_const]
  | n + 1, i + 1, h => by
      rw [E_pow_succ]
      simp only [coord_cons_succ, E_coord X (show i < n by omega), E_const]

/-- **Distinct coordinates are independent** in mean: `E[Xᵢ Yⱼ] = E[X] E[Y]` for `i ≠ j`. -/
theorem E_coord_mul (X Y : α → R) : ∀ {n i j : Nat}, i < n → j < n → i ≠ j →
    (P.pow n).E (fun t => coord X i t * coord Y j t) = P.E X * P.E Y
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, 0, _, _, h => absurd rfl h
  | n + 1, 0, j + 1, _, hj, _ => by
      rw [E_pow_succ]
      simp only [coord_cons_zero, coord_cons_succ, E_smul, E_coord P Y (show j < n by omega)]
      exact E_smul_right P _ _
  | n + 1, i + 1, 0, hi, _, _ => by
      rw [E_pow_succ]
      simp only [coord_cons_zero, coord_cons_succ]
      rw [P.E_congr (Y := fun a => (P.pow n).E (coord X i) * Y a) fun a _ => by
        rw [show (fun t => coord X i t * Y a) = fun t => Y a * coord X i t from
          funext fun t => by grind, E_smul]; grind]
      rw [E_smul, E_coord P X (show i < n by omega)]
  | n + 1, i + 1, j + 1, hi, hj, hij => by
      rw [E_pow_succ]
      simp only [coord_cons_succ]
      rw [E_coord_mul X Y (show i < n by omega) (show j < n by omega) (by omega), E_const]
where
  /-- `E[f · c] = E[f] · c`. -/
  E_smul_right (P : FinProb α) (f : α → R) (c : R) : P.E (fun a => f a * c) = P.E f * c := by
    rw [show (fun a => f a * c) = fun a => c * f a from funext fun a => by grind, E_smul]; grind

/-- Products of the same coordinate. -/
theorem coord_mul_self (X : α → R) {n i : Nat} {t : List α} (ht : t ∈ powL P.pts n) (hi : i < n) :
    coord X i t * coord X i t = coord (fun x => X x * X x) i t := by
  have hl := length_of_mem_powL ht
  simp only [coord, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show i < t.length by omega), Option.map_some, Option.getD_some]

/-- **The coordinates have the variance of `X`.** -/
theorem Var_coord (X : α → R) {n i : Nat} (hi : i < n) : (P.pow n).Var (coord X i) = P.Var X := by
  rw [Var_eq, Var_eq, E_coord P X hi,
    (P.pow n).E_congr (Y := coord (fun x => X x * X x) i) fun t ht => coord_mul_self P X ht hi,
    E_coord P _ hi]

/-- **Distinct coordinates are uncorrelated.** -/
theorem uncorr_coord (X : α → R) {n i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (P.pow n).Uncorr (coord X i) (coord X j) := by
  unfold Uncorr Cov
  rw [E_coord_mul P X X hi hj hij, E_coord P X hi, E_coord P X hj]; grind

/-- The sample sum `Sₙ = X₀ + ⋯ + X_{n−1}`. -/
def sampleSum (X : α → R) (n : Nat) (t : List α) : R := sumN n fun i => coord X i t

/-- `E[Sₙ] = n μ`. -/
theorem E_sampleSum (X : α → R) (n : Nat) : (P.pow n).E (sampleSum X n) = n * P.E X := by
  unfold sampleSum
  rw [E_sumN, sumN, sumL_congr (g := fun _ => P.E X) fun i hi =>
    E_coord P X (List.mem_range.1 hi)]
  exact sumN_const n _

/-- `Var(Sₙ) = n σ²`. -/
theorem Var_sampleSum (X : α → R) (n : Nat) : (P.pow n).Var (sampleSum X n) = n * P.Var X := by
  unfold sampleSum
  rw [Var_sumN _ n _ fun i j hij hj => uncorr_coord P X (by omega) hj (by omega), sumN,
    sumL_congr (g := fun _ => P.Var X) fun i hi => Var_coord P X (List.mem_range.1 hi)]
  exact sumN_const n _

/-- **The weak law of large numbers** (Bernoulli 1713, in Chebyshev's form). For `n ≥ 1`
independent repetitions and any `ε > 0`,

`Pⁿ(|Sₙ/n − μ| ≥ ε) ≤ σ² / (n ε²)`, where `μ = E[X]`, `σ² = Var X`. -/
theorem weak_law (X : α → R) {n : Nat} (hn : 0 < n) {ε : R} (hε : 0 < ε) :
    (P.pow n).prob (fun t => ε ≤ OF.abs (sampleSum X n t / n - P.E X)) ≤
      P.Var X / (n * (ε * ε)) := by
  have hn' : (0 : R) < n := natCast_pos hn
  have hn0 : (n : R) ≠ 0 := fun h => by grind
  let Y : List α → R := fun t => (1 / n) * sampleSum X n t
  have hEY : (P.pow n).E Y = P.E X := by
    show (P.pow n).E (fun t => (1 / n) * sampleSum X n t) = _
    rw [E_smul, E_sampleSum]; grind
  have hVY : (P.pow n).Var Y = P.Var X / n := by
    show (P.pow n).Var (fun t => (1 / n) * sampleSum X n t) = _
    rw [Var_smul, Var_sampleSum]; grind
  have hc := (P.pow n).chebyshev Y hε
  rw [hEY, hVY] at hc
  have hev : (P.pow n).prob (fun t => ε ≤ OF.abs (sampleSum X n t / n - P.E X)) =
      (P.pow n).prob (fun t => ε ≤ OF.abs (Y t - P.E X)) :=
    prob_congr _ fun t _ => by
      rw [show sampleSum X n t / n = Y t from by simp only [Y]; grind]
  rw [hev]
  have : P.Var X / n / (ε * ε) = P.Var X / (n * (ε * ε)) := by
    have : ε * ε ≠ 0 := fun h => by
      have := OrderedRing.mul_lt_mul_of_pos_left hε hε; grind
    grind
  rw [← this]; exact hc

/-- **The weak law of large numbers, limit form**: for every `ε > 0` and `δ > 0` there is
`N` such that for all `n ≥ N`, `Pⁿ(|Sₙ/n − μ| ≥ ε) ≤ δ` — the sample mean converges to
the true mean in probability. -/
theorem weak_law_limit (X : α → R) {ε δ : R} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → 0 < n →
      (P.pow n).prob (fun t => ε ≤ OF.abs (sampleSum X n t / n - P.E X)) ≤ δ := by
  have hK : 0 < ε * ε * δ := by
    have h₁ := OrderedRing.mul_lt_mul_of_pos_left hε hε
    have h₂ := OrderedRing.mul_lt_mul_of_pos_left hδ (show 0 < ε * ε by grind)
    grind
  obtain ⟨N, hN⟩ := R.archimedean (P.Var X / (ε * ε * δ))
  refine ⟨N, fun n hNn hn => Std.le_trans (P.weak_law X hn hε) ?_⟩
  have hn' : (0 : R) < n := natCast_pos hn
  have hNn' : (N : R) ≤ n := natCast_le hNn
  -- `σ² ≤ δ · (n ε²)`
  have h₁ : P.Var X / (ε * ε * δ) < n := by grind
  have h₂ := OrderedRing.mul_lt_mul_of_pos_right h₁ hK
  have hK0 : ε * ε * δ ≠ 0 := fun h => by grind
  have h₃ : P.Var X / (ε * ε * δ) * (ε * ε * δ) = P.Var X := by grind
  rw [h₃] at h₂
  refine div_le_of_le_mul (by
    have := OrderedRing.mul_lt_mul_of_pos_left hε hε
    have := OrderedRing.mul_lt_mul_of_pos_left (show 0 < ε * ε by grind) hn'
    grind) ?_
  have : δ * (n * (ε * ε)) = n * (ε * ε * δ) := by grind
  rw [this]; exact Std.le_of_lt h₂

end FinProb

end Foundations.Probability
