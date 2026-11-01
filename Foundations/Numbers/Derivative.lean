import Foundations.Numbers.Continuity

/-!
# Analysis on the reals III: the derivative

Newton and Leibniz computed with "infinitely small" increments; Cauchy and Weierstrass replaced
them by inequalities. We follow the modern form of their idea: `f` has **derivative `d` at `x`**
if, near `x`, `f` is approximated by the straight line `y ↦ f x + d · (y − x)` with an error
that is small *compared with the distance* `|y − x|`:

  for every `ε > 0` there is `δ > 0` with `|f y − f x − d (y − x)| ≤ ε |y − x|`
  whenever `|y − x| < δ`.

This avoids dividing by `y − x` (and hence any special treatment of `y = x`), and makes the
**chain rule** a two-line estimate. From the definition we derive the usual rules — sums,
constant multiples, the **product rule** and the **chain rule** — and the derivatives of
powers and polynomials.

The heart of the file is the passage from *local* to *global* information, which again rests on
completeness (through the extreme value theorem of the previous file):

* **Fermat**: at an interior maximum or minimum the derivative vanishes;
* **Rolle's theorem**: if `f a = f b` then `f' c = 0` somewhere strictly between;
* the **mean value theorem**: `f b − f a = f' c · (b − a)` for some `c` between `a` and `b`;
* hence a function with `f' ≥ 0` is increasing, with `f' > 0` strictly increasing, and with
  `f' = 0` constant. Over the rationals all three fail.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-! ## Small helper facts -/

/-- Two positive numbers have a positive common lower bound. -/
theorem exists_pos_le_both {δ₁ δ₂ : R} (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) :
    ∃ δ : R, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ := by
  rcases (by grind : δ₁ ≤ δ₂ ∨ δ₂ ≤ δ₁) with h | h
  · exact ⟨δ₁, h₁, by grind, h⟩
  · exact ⟨δ₂, h₂, h, by grind⟩

/-- Product estimate with non-strict inequalities: `|u| ≤ A` and `|v| ≤ B` give
`|u v| ≤ A B`. -/
theorem abs_mul_le {u v A B : R} (hu : abs u ≤ A) (hv : abs v ≤ B) : abs (u * v) ≤ A * B := by
  rw [abs_mul]
  have hA : 0 ≤ A := by have := abs_nonneg u; grind
  have h1 := OrderedRing.mul_le_mul_of_nonneg_right hu (abs_nonneg v)
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left hv hA
  grind

/-- For every `c` and `ε > 0` there is `η > 0` with `|c| · η ≤ ε` (take `η = ε / (|c| + 1)`). -/
theorem exists_mul_le (c : R) {ε : R} (hε : 0 < ε) : ∃ η : R, 0 < η ∧ abs c * η ≤ ε := by
  have hc := abs_nonneg c
  refine ⟨ε / (abs c + 1), div_pos hε (by grind), ?_⟩
  have hη : 0 < ε / (abs c + 1) := div_pos hε (by grind)
  have e : (abs c + 1) * (ε / (abs c + 1)) = ε := by grind
  grind

/-- `|0| = 0`. -/
theorem abs_zero : abs (0 : R) = 0 := by rcases abs_cases (0 : R) with h | h <;> grind

/-- `|−x| = |x|`. -/
theorem abs_neg (x : R) : abs (-x) = abs x := by
  rw [show -x = 0 - x by grind, abs_sub_comm]; congr 1; grind

/-- `|x| = 0` only for `x = 0`. -/
theorem eq_zero_of_abs_le {x : R} (h : abs x ≤ 0) : x = 0 := by
  rcases abs_cases x with h' | h' <;> grind

/-! ## The definition -/

/-- `f` **has derivative `d` at `x`**: for every `ε > 0` there is `δ > 0` such that
`|f y − f x − d (y − x)| ≤ ε |y − x|` whenever `|y − x| < δ`. -/
def HasDerivAt (f : R → R) (d : R) (x : R) : Prop :=
  ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧
    ∀ y, abs (y - x) < δ → abs (f y - f x - d * (y - x)) ≤ ε * abs (y - x)

/-- A differentiable function grows at most linearly near the point: `|f y − f x| ≤
(|d| + 1) |y − x|` for `y` near `x`. -/
theorem HasDerivAt.lipschitz {f : R → R} {d x : R} (h : HasDerivAt f d x) :
    ∃ δ : R, 0 < δ ∧ ∀ y, abs (y - x) < δ → abs (f y - f x) ≤ (abs d + 1) * abs (y - x) := by
  obtain ⟨δ, hδ, hδf⟩ := h 1 (by grind)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have k1 := hδf y hy
  have k2 := abs_add (f y - f x - d * (y - x)) (d * (y - x))
  rw [show f y - f x - d * (y - x) + d * (y - x) = f y - f x by grind, abs_mul] at k2
  grind

/-- **Differentiable functions are continuous.** -/
theorem HasDerivAt.continuousAt {f : R → R} {d x : R} (h : HasDerivAt f d x) :
    ContinuousAt f x := fun ε hε => by
  obtain ⟨δ₁, hδ₁, h₁⟩ := h.lipschitz
  have hd := abs_nonneg d
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₁ (div_pos hε (by grind : 0 < abs d + 1))
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have k1 := h₁ y (by grind)
  have k2 := OrderedRing.mul_lt_mul_of_pos_left (show abs (y - x) < δ from hy)
    (by grind : 0 < abs d + 1)
  have k3 := OrderedRing.mul_le_mul_of_nonneg_left hδ2 (by grind : 0 ≤ abs d + 1)
  have e : (abs d + 1) * (ε / (abs d + 1)) = ε := by grind
  grind

/-- Derivatives are unique. -/
theorem HasDerivAt.unique {f : R → R} {d₁ d₂ x : R} (h₁ : HasDerivAt f d₁ x)
    (h₂ : HasDerivAt f d₂ x) : d₁ = d₂ := by
  apply Classical.byContradiction
  intro hne
  have hpos : 0 < abs (d₁ - d₂) := by rcases abs_cases (d₁ - d₂) with h | h <;> grind
  obtain ⟨δ₁, hδ₁, k₁⟩ := h₁ (abs (d₁ - d₂) / 4) (by grind)
  obtain ⟨δ₂, hδ₂, k₂⟩ := h₂ (abs (d₁ - d₂) / 4) (by grind)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₁ hδ₂
  have hy : abs (x + δ / 2 - x) = δ / 2 := by
    rw [show x + δ / 2 - x = δ / 2 by grind]; rcases abs_cases (δ / 2) with h | h <;> grind
  have a1 := k₁ (x + δ / 2) (by grind)
  have a2 := k₂ (x + δ / 2) (by grind)
  rw [hy] at a1 a2
  have a3 := abs_add (f (x + δ / 2) - f x - d₂ * (x + δ / 2 - x))
    (-(f (x + δ / 2) - f x - d₁ * (x + δ / 2 - x)))
  rw [abs_neg, show f (x + δ / 2) - f x - d₂ * (x + δ / 2 - x) +
    -(f (x + δ / 2) - f x - d₁ * (x + δ / 2 - x)) = (d₁ - d₂) * (δ / 2) by grind, abs_mul] at a3
  have : abs (δ / 2) = δ / 2 := by rcases abs_cases (δ / 2) with h | h <;> grind
  rw [this] at a3
  have := OrderedRing.mul_lt_mul_of_pos_right
    (by grind : abs (d₁ - d₂) / 4 + abs (d₁ - d₂) / 4 < abs (d₁ - d₂)) (by grind : (0 : R) < δ / 2)
  grind

/-! ## Rules of differentiation -/

/-- `|c| = c` for `c ≥ 0`. -/
theorem abs_of_nonneg {c : R} (h : 0 ≤ c) : abs c = c := by
  rcases abs_cases c with h' | h' <;> grind

/-- Constant functions have derivative `0`. -/
theorem hasDerivAt_const (c x : R) : HasDerivAt (fun _ => c) 0 x := fun ε hε =>
  ⟨1, by grind, fun y _ => by
    simp only
    rw [show c - c - 0 * (y - x) = 0 by grind, abs_zero]
    have := OrderedRing.mul_nonneg (Std.le_of_lt hε) (abs_nonneg (y - x)); grind⟩

/-- The identity function has derivative `1`. -/
theorem hasDerivAt_id (x : R) : HasDerivAt (fun y => y) 1 x := fun ε hε =>
  ⟨1, by grind, fun y _ => by
    simp only
    rw [show y - x - 1 * (y - x) = 0 by grind, abs_zero]
    have := OrderedRing.mul_nonneg (Std.le_of_lt hε) (abs_nonneg (y - x)); grind⟩

/-- **Sum rule.** `(f + g)' = f' + g'`. -/
theorem HasDerivAt.add {f g : R → R} {a b x : R} (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun y => f y + g y) (a + b) x := fun ε hε => by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε / 2) (by grind)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε / 2) (by grind)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₁ hδ₂
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have k1 := h₁ y (by grind)
  have k2 := h₂ y (by grind)
  have k3 := abs_add (f y - f x - a * (y - x)) (g y - g x - b * (y - x))
  rw [show f y - f x - a * (y - x) + (g y - g x - b * (y - x)) =
    f y + g y - (f x + g x) - (a + b) * (y - x) by grind] at k3
  grind

/-- **Constant multiple rule.** `(c f)' = c f'`. -/
theorem HasDerivAt.const_mul (c : R) {f : R → R} {a x : R} (hf : HasDerivAt f a x) :
    HasDerivAt (fun y => c * f y) (c * a) x := fun ε hε => by
  obtain ⟨η, hη, hηc⟩ := exists_mul_le c hε
  obtain ⟨δ, hδ, h⟩ := hf η hη
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [show c * f y - c * f x - c * a * (y - x) = c * (f y - f x - a * (y - x)) by grind, abs_mul]
  have k1 := OrderedRing.mul_le_mul_of_nonneg_left (h y hy) (abs_nonneg c)
  have k2 := OrderedRing.mul_le_mul_of_nonneg_right hηc (abs_nonneg (y - x))
  grind

/-- Negation rule. `(−f)' = −f'`. -/
theorem HasDerivAt.neg {f : R → R} {a x : R} (hf : HasDerivAt f a x) :
    HasDerivAt (fun y => -f y) (-a) x := by
  have := hf.const_mul (-1)
  simp only [show ∀ t : R, -1 * t = -t from fun t => by grind] at this
  exact this

/-- **Difference rule.** `(f − g)' = f' − g'`. -/
theorem HasDerivAt.sub {f g : R → R} {a b x : R} (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun y => f y - g y) (a - b) x := by
  have := hf.add hg.neg
  simp only [show ∀ s t : R, s + -t = s - t from fun s t => by grind] at this
  exact this

/-- Functions agreeing everywhere have the same derivatives. -/
theorem HasDerivAt.congr {f g : R → R} {a x : R} (hf : HasDerivAt f a x) (h : ∀ y, f y = g y) :
    HasDerivAt g a x := by
  have : f = g := funext h
  exact this ▸ hf

/-- A term `u` with `|u| ≤ η |h|`, multiplied by `c`, stays below `ε |h|` once `|c| η ≤ ε`. -/
theorem abs_mul_bound {c u η ε k : R} (hu : abs u ≤ η * abs k) (hc : abs c * η ≤ ε) :
    abs (c * u) ≤ ε * abs k := by
  rw [abs_mul]
  have k1 := OrderedRing.mul_le_mul_of_nonneg_left hu (abs_nonneg c)
  have k2 := OrderedRing.mul_le_mul_of_nonneg_right hc (abs_nonneg k)
  grind

/-- **Product rule** (Leibniz). `(f g)' = f' g + f g'`. -/
theorem HasDerivAt.mul {f g : R → R} {a b x : R} (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun y => f y * g y) (a * g x + f x * b) x := fun ε hε => by
  obtain ⟨ε₁, hε₁, hε₁c⟩ := exists_mul_le (g x) (by grind : 0 < ε / 3)
  obtain ⟨ε₂, hε₂, hε₂c⟩ := exists_mul_le (f x) (by grind : 0 < ε / 3)
  have ha := abs_nonneg a
  obtain ⟨η, hη, hηc⟩ := exists_mul_le (abs a + 1) (by grind : 0 < ε / 3)
  rw [abs_of_nonneg (by grind : 0 ≤ abs a + 1)] at hηc
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf ε₁ hε₁
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg ε₂ hε₂
  obtain ⟨δ₃, hδ₃, h₃⟩ := hf.lipschitz
  obtain ⟨δ₄, hδ₄, h₄⟩ := hg.continuousAt η hη
  obtain ⟨δ₅, hδ₅, h₅1, h₅2⟩ := exists_pos_le_both hδ₁ hδ₂
  obtain ⟨δ₆, hδ₆, h₆1, h₆2⟩ := exists_pos_le_both hδ₃ hδ₄
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₅ hδ₆
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have t1 := abs_mul_bound (h₁ y (by grind)) hε₁c
  have t3 := abs_mul_bound (h₂ y (by grind)) hε₂c
  have t2 : abs ((f y - f x) * (g y - g x)) ≤ ε / 3 * abs (y - x) := by
    have k := abs_mul_le (h₃ y (by grind)) (Std.le_of_lt (h₄ y (by grind)))
    have k2 := OrderedRing.mul_le_mul_of_nonneg_left hηc (abs_nonneg (y - x))
    grind
  have s1 := abs_add (g x * (f y - f x - a * (y - x)) + (f y - f x) * (g y - g x))
    (f x * (g y - g x - b * (y - x)))
  have s2 := abs_add (g x * (f y - f x - a * (y - x))) ((f y - f x) * (g y - g x))
  rw [show g x * (f y - f x - a * (y - x)) + (f y - f x) * (g y - g x) +
    f x * (g y - g x - b * (y - x)) = f y * g y - f x * g x - (a * g x + f x * b) * (y - x)
    by grind] at s1
  grind

/-- **Chain rule.** `(g ∘ f)' (x) = g' (f x) · f' (x)`. -/
theorem HasDerivAt.comp {f g : R → R} {a b x : R} (hg : HasDerivAt g b (f x))
    (hf : HasDerivAt f a x) : HasDerivAt (fun y => g (f y)) (b * a) x := fun ε hε => by
  have ha := abs_nonneg a
  obtain ⟨ε₁, hε₁, hε₁c⟩ := exists_mul_le (abs a + 1) (by grind : 0 < ε / 2)
  rw [abs_of_nonneg (by grind : 0 ≤ abs a + 1)] at hε₁c
  obtain ⟨ε₂, hε₂, hε₂c⟩ := exists_mul_le b (by grind : 0 < ε / 2)
  obtain ⟨δg, hδg, hg'⟩ := hg ε₁ hε₁
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf.continuousAt δg hδg
  obtain ⟨δ₂, hδ₂, h₂⟩ := hf.lipschitz
  obtain ⟨δ₃, hδ₃, h₃⟩ := hf ε₂ hε₂
  obtain ⟨δ₄, hδ₄, h₄1, h₄2⟩ := exists_pos_le_both hδ₁ hδ₂
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₄ hδ₃
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have t1 : abs (g (f y) - g (f x) - b * (f y - f x)) ≤ ε / 2 * abs (y - x) := by
    have k := hg' (f y) (h₁ y (by grind))
    have k2 := OrderedRing.mul_le_mul_of_nonneg_left (h₂ y (by grind)) (Std.le_of_lt hε₁)
    have k3 := OrderedRing.mul_le_mul_of_nonneg_right hε₁c (abs_nonneg (y - x))
    grind
  have t2 := abs_mul_bound (h₃ y (by grind)) hε₂c
  have s := abs_add (g (f y) - g (f x) - b * (f y - f x)) (b * (f y - f x - a * (y - x)))
  rw [show g (f y) - g (f x) - b * (f y - f x) + b * (f y - f x - a * (y - x)) =
    g (f y) - g (f x) - b * a * (y - x) by grind] at s
  grind

/-! ## Powers and polynomials -/

/-- **Power rule.** `(yⁿ⁺¹)' = (n + 1) yⁿ`. -/
theorem hasDerivAt_pow (n : Nat) (x : R) :
    HasDerivAt (fun y => y ^ (n + 1)) (((n : R) + 1) * x ^ n) x := by
  induction n with
  | zero =>
    have h := (hasDerivAt_id x).congr (g := fun y => y ^ (0 + 1)) (fun y => by
      show y = y ^ 0 * y; grind)
    have e : (1 : R) = (((0 : Nat) : R) + 1) * x ^ 0 := by grind
    exact e ▸ h
  | succ n ih =>
    have h := (ih.mul (hasDerivAt_id x)).congr (g := fun y => y ^ (n + 1 + 1)) (fun y => rfl)
    have e : ((n : R) + 1) * x ^ n * x + x ^ (n + 1) * 1 = (((n + 1 : Nat) : R) + 1) * x ^ (n + 1) := by
      rw [pow_succ']; grind
    exact e ▸ h

/-- Derivative of `yᵏ` for every `k` (including `k = 0`): `k · yᵏ⁻¹`. -/
theorem hasDerivAt_pow' (k : Nat) (x : R) :
    HasDerivAt (fun y => y ^ k) ((k : R) * x ^ (k - 1)) x := by
  cases k with
  | zero =>
    have h := (hasDerivAt_const 1 x).congr (g := fun y => y ^ 0) (fun y => by grind)
    have e : (0 : R) = ((0 : Nat) : R) * x ^ (0 - 1) := by grind
    exact e ▸ h
  | succ k =>
    have e : ((k : R) + 1) * x ^ k = ((k + 1 : Nat) : R) * x ^ (k + 1 - 1) := by
      rw [show k + 1 - 1 = k by omega]; grind
    exact e ▸ hasDerivAt_pow k x

/-- The finite sum `a 0 + a 1 + ⋯ + a (n − 1)`. -/
def fsum (a : Nat → R) : Nat → R
  | 0 => 0
  | n + 1 => fsum a n + a n

/-- **Derivative of a finite sum** is the sum of the derivatives. -/
theorem hasDerivAt_fsum (F : Nat → R → R) (D : Nat → R) (n : Nat) {x : R}
    (h : ∀ k, k < n → HasDerivAt (F k) (D k) x) :
    HasDerivAt (fun y => fsum (fun k => F k y) n) (fsum D n) x := by
  induction n with
  | zero => exact hasDerivAt_const 0 x
  | succ n ih =>
    exact (ih fun k hk => h k (by omega)).add (h n (by omega))

/-- The polynomial function `y ↦ c₀ + c₁ y + ⋯ + cₙ₋₁ yⁿ⁻¹` with coefficients `c`. -/
def poly (c : Nat → R) (n : Nat) (y : R) : R := fsum (fun k => c k * y ^ k) n

/-- **Derivative of a polynomial**, computed term by term:
`(Σ cₖ yᵏ)' = Σ cₖ · k · yᵏ⁻¹`. -/
theorem hasDerivAt_poly (c : Nat → R) (n : Nat) (x : R) :
    HasDerivAt (poly c n) (fsum (fun k => c k * ((k : R) * x ^ (k - 1))) n) x :=
  hasDerivAt_fsum (fun k y => c k * y ^ k) _ n fun k _ => (hasDerivAt_pow' k x).const_mul (c k)

/-! ## Fermat, Rolle and the mean value theorem -/

/-- `f` has a **local maximum** at `c`: `f y ≤ f c` for all `y` near `c`. -/
def IsLocalMax (f : R → R) (c : R) : Prop := ∃ δ : R, 0 < δ ∧ ∀ y, abs (y - c) < δ → f y ≤ f c

/-- **Fermat's theorem.** At a local maximum the derivative vanishes. -/
theorem deriv_eq_zero_of_isLocalMax {f : R → R} {d c : R} (hd : HasDerivAt f d c)
    (hmax : IsLocalMax f c) : d = 0 := by
  obtain ⟨δ₀, hδ₀, h₀⟩ := hmax
  apply Classical.byContradiction
  intro hne
  have hpos : 0 < abs d := by rcases abs_cases d with h | h <;> grind
  obtain ⟨δ₁, hδ₁, h₁⟩ := hd (abs d / 2) (by grind)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₀ hδ₁
  have hh : abs (δ / 2) = δ / 2 := abs_of_nonneg (by grind)
  rcases (by grind : 0 < d ∨ d < 0) with hs | hs
  · -- To the right of `c`, the function would increase.
    have e : c + δ / 2 - c = δ / 2 := by grind
    have k1 := h₁ (c + δ / 2) (by rw [e, hh]; grind)
    have k2 := h₀ (c + δ / 2) (by rw [e, hh]; grind)
    rw [e, hh, abs_of_nonneg (Std.le_of_lt hs)] at k1
    have := (abs_le.1 k1).1
    have := OrderedRing.mul_pos hs (by grind : (0 : R) < δ / 2)
    grind
  · -- To the left of `c`, the function would increase.
    have e : c - δ / 2 - c = -(δ / 2) := by grind
    have k1 := h₁ (c - δ / 2) (by rw [e, abs_neg, hh]; grind)
    have k2 := h₀ (c - δ / 2) (by rw [e, abs_neg, hh]; grind)
    rw [e, abs_neg, hh] at k1
    have ed : abs d = -d := by rcases abs_cases d with h | h <;> grind
    rw [ed] at k1
    have := (abs_le.1 k1).1
    have := OrderedRing.mul_pos (by grind : 0 < -d) (by grind : (0 : R) < δ / 2)
    grind

/-- **Fermat's theorem** for minima. At a local minimum the derivative vanishes. -/
theorem deriv_eq_zero_of_isLocalMin {f : R → R} {d c : R} (hd : HasDerivAt f d c)
    (hmin : ∃ δ : R, 0 < δ ∧ ∀ y, abs (y - c) < δ → f c ≤ f y) : d = 0 := by
  obtain ⟨δ, hδ, h⟩ := hmin
  have := deriv_eq_zero_of_isLocalMax hd.neg ⟨δ, hδ, fun y hy => by have := h y hy; grind⟩
  grind

/-- An interior point `a < c < b` has a neighbourhood inside `(a, b)`. -/
theorem nhds_of_interior {a b c : R} (hac : a < c) (hcb : c < b) :
    ∃ δ : R, 0 < δ ∧ ∀ y, abs (y - c) < δ → a < y ∧ y < b := by
  obtain ⟨δ, hδ, h1, h2⟩ := exists_pos_le_both (by grind : 0 < c - a) (by grind : 0 < b - c)
  exact ⟨δ, hδ, fun y hy => by have := abs_lt.1 hy; grind⟩

/-- **Rolle's theorem.** If `f` is continuous on `[a, b]`, differentiable on `(a, b)`, and
`f a = f b`, then `f' c = 0` at some `c` strictly between `a` and `b`. -/
theorem rolle {f f' : R → R} {a b : R} (hab : a < b)
    (hc : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x)
    (hd : ∀ x, a < x → x < b → HasDerivAt f (f' x) x) (hfab : f a = f b) :
    ∃ c, a < c ∧ c < b ∧ f' c = 0 := by
  obtain ⟨c₁, hc₁a, hc₁b, hmax⟩ := extreme_value (Std.le_of_lt hab) hc
  obtain ⟨c₂, hc₂a, hc₂b, hmin'⟩ := extreme_value (f := fun y => 0 - f y) (Std.le_of_lt hab)
    fun x h1 h2 => continuousAt_sub (continuousAt_const 0 x) (hc x h1 h2)
  have hmin : ∀ x, a ≤ x → x ≤ b → f c₂ ≤ f x := fun x h1 h2 => by
    have : 0 - f x ≤ 0 - f c₂ := hmin' x h1 h2
    grind
  by_cases h₁ : a < c₁ ∧ c₁ < b
  · -- An interior maximum.
    obtain ⟨δ, hδ, hδ'⟩ := nhds_of_interior h₁.1 h₁.2
    exact ⟨c₁, h₁.1, h₁.2, deriv_eq_zero_of_isLocalMax (hd c₁ h₁.1 h₁.2)
      ⟨δ, hδ, fun y hy => have := hδ' y hy; hmax y (by grind) (by grind)⟩⟩
  by_cases h₂ : a < c₂ ∧ c₂ < b
  · -- An interior minimum.
    obtain ⟨δ, hδ, hδ'⟩ := nhds_of_interior h₂.1 h₂.2
    exact ⟨c₂, h₂.1, h₂.2, deriv_eq_zero_of_isLocalMin (hd c₂ h₂.1 h₂.2)
      ⟨δ, hδ, fun y hy => have := hδ' y hy; hmin y (by grind) (by grind)⟩⟩
  · -- Maximum and minimum both at the end points: `f` is constant on `[a, b]`.
    have e₁ : f c₁ = f a := by
      rcases (by grind : c₁ = a ∨ c₁ = b) with h | h <;> rw [h]; exact hfab.symm
    have e₂ : f c₂ = f a := by
      rcases (by grind : c₂ = a ∨ c₂ = b) with h | h <;> rw [h]; exact hfab.symm
    let m := (a + b) / 2
    have hm1 : a < m := by grind
    have hm2 : m < b := by grind
    have hfm : f m = f a := by
      have := hmax m (by grind) (by grind); have := hmin m (by grind) (by grind); grind
    obtain ⟨δ, hδ, hδ'⟩ := nhds_of_interior hm1 hm2
    refine ⟨m, hm1, hm2, deriv_eq_zero_of_isLocalMax (hd m hm1 hm2) ⟨δ, hδ, fun y hy => ?_⟩⟩
    have := hδ' y hy
    have := hmax y (by grind) (by grind)
    grind

/-- **Mean value theorem** (Lagrange). If `f` is continuous on `[a, b]` and differentiable on
`(a, b)`, then the chord slope is attained as a derivative: `f b − f a = f' c · (b − a)` for some
`c` strictly between `a` and `b`. -/
theorem mean_value {f f' : R → R} {a b : R} (hab : a < b)
    (hc : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x)
    (hd : ∀ x, a < x → x < b → HasDerivAt f (f' x) x) :
    ∃ c, a < c ∧ c < b ∧ f b - f a = f' c * (b - a) := by
  -- Apply Rolle to `g y = f y · (b − a) − y · (f b − f a)`, which has `g a = g b`.
  let g : R → R := fun y => f y * (b - a) - y * (f b - f a)
  have hgc : ∀ x, a ≤ x → x ≤ b → ContinuousAt g x := fun x h1 h2 =>
    continuousAt_sub (continuousAt_mul (hc x h1 h2) (continuousAt_const _ x))
      (continuousAt_mul (continuousAt_id x) (continuousAt_const _ x))
  have hgd : ∀ x, a < x → x < b →
      HasDerivAt g (f' x * (b - a) + f x * 0 - (1 * (f b - f a) + x * 0)) x := fun x h1 h2 =>
    ((hd x h1 h2).mul (hasDerivAt_const _ x)).sub ((hasDerivAt_id x).mul (hasDerivAt_const _ x))
  obtain ⟨c, hc1, hc2, hc3⟩ := rolle hab hgc hgd (by grind)
  exact ⟨c, hc1, hc2, by grind⟩

/-! ## Consequences of the mean value theorem -/

/-- **Monotonicity test.** A function with non-negative derivative on `[a, b]` is increasing
there. -/
theorem monotone_of_deriv_nonneg {f f' : R → R} {a b : R}
    (hd : ∀ x, a ≤ x → x ≤ b → HasDerivAt f (f' x) x) (hpos : ∀ x, a ≤ x → x ≤ b → 0 ≤ f' x)
    {x y : R} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) : f x ≤ f y := by
  rcases (by grind : x = y ∨ x < y) with h | h
  · rw [h]; grind
  · obtain ⟨c, hc1, hc2, hc3⟩ := mean_value h
      (fun t h1 h2 => (hd t (by grind) (by grind)).continuousAt)
      (fun t h1 h2 => hd t (by grind) (by grind))
    have := OrderedRing.mul_nonneg (hpos c (by grind) (by grind)) (by grind : (0 : R) ≤ y - x)
    grind

/-- **Strict monotonicity test.** A function with positive derivative on `[a, b]` is strictly
increasing there. -/
theorem strictMono_of_deriv_pos {f f' : R → R} {a b : R}
    (hd : ∀ x, a ≤ x → x ≤ b → HasDerivAt f (f' x) x) (hpos : ∀ x, a ≤ x → x ≤ b → 0 < f' x)
    {x y : R} (hax : a ≤ x) (hxy : x < y) (hyb : y ≤ b) : f x < f y := by
  obtain ⟨c, hc1, hc2, hc3⟩ := mean_value hxy
    (fun t h1 h2 => (hd t (by grind) (by grind)).continuousAt)
    (fun t h1 h2 => hd t (by grind) (by grind))
  have := OrderedRing.mul_pos (hpos c (by grind) (by grind)) (by grind : (0 : R) < y - x)
  grind

/-- **Zero derivative means constant.** A function whose derivative vanishes on `[a, b]` is
constant there. -/
theorem const_of_deriv_zero {f f' : R → R} {a b : R}
    (hd : ∀ x, a ≤ x → x ≤ b → HasDerivAt f (f' x) x) (hz : ∀ x, a ≤ x → x ≤ b → f' x = 0)
    {x y : R} (hax : a ≤ x) (hxb : x ≤ b) (hay : a ≤ y) (hyb : y ≤ b) : f x = f y := by
  have k1 : ∀ {s t : R}, a ≤ s → s ≤ t → t ≤ b → f s ≤ f t := fun h1 h2 h3 =>
    monotone_of_deriv_nonneg (f := f) hd (fun t h1 h2 => by rw [hz t h1 h2]; grind) h1 h2 h3
  have k2 : ∀ {s t : R}, a ≤ s → s ≤ t → t ≤ b → -f s ≤ -f t := fun h1 h2 h3 =>
    monotone_of_deriv_nonneg (f := fun t => -f t) (fun t h1 h2 => (hd t h1 h2).neg)
      (fun t h1 h2 => by rw [hz t h1 h2]; grind) h1 h2 h3
  rcases (by grind : x ≤ y ∨ y ≤ x) with h | h
  · have := k1 hax h hyb; have := k2 hax h hyb; grind
  · have := k1 hay h hxb; have := k2 hay h hxb; grind

/-- **Zero derivative everywhere means constant** (on the whole line). -/
theorem const_of_deriv_zero' {f f' : R → R} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hz : ∀ x, f' x = 0) (x y : R) : f x = f y := by
  rcases (by grind : x ≤ y ∨ y ≤ x) with h | h
  · exact const_of_deriv_zero (a := x) (b := y) (fun t _ _ => hd t) (fun t _ _ => hz t)
      (Std.le_refl x) h h (Std.le_refl y)
  · exact const_of_deriv_zero (a := y) (b := x) (fun t _ _ => hd t) (fun t _ _ => hz t)
      h (Std.le_refl x) (Std.le_refl y) h

/-- **Positive derivative everywhere means strictly increasing** (on the whole line). -/
theorem strictMono_of_deriv_pos' {f f' : R → R} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 < f' x) {x y : R} (hxy : x < y) : f x < f y :=
  strictMono_of_deriv_pos (a := x) (b := y) (fun t _ _ => hd t) (fun t _ _ => hpos t)
    (Std.le_refl x) hxy (Std.le_refl y)

end R

end Foundations.Numbers
