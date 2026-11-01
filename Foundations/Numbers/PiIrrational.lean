import Foundations.Numbers.TrigIdentities

/-!
# π is irrational

Lambert proved in 1761 that π is irrational; we give Ivan Niven's one-page proof (1947), which
uses nothing but the calculus built in the previous files.

Suppose `π = a/b` with natural numbers `a, b`. For a natural number `n` consider the polynomial

  `f(x) = xⁿ (a − b x)ⁿ / n!`.

* `n! f` has integer coefficients and starts with `xⁿ`, so every derivative `f⁽ᵐ⁾(0)` is an
  integer (it is `m!/n!` times an integer coefficient, and vanishes for `m < n`). Since
  `f(π − x) = f(x)`, also `f⁽ᵐ⁾(π) = ±f⁽ᵐ⁾(0)` is an integer.
* With `F = f − f'' + f⁽⁴⁾ − ⋯ ± f⁽²ⁿ⁾` we have `F'' + F = f`, hence
  `(F' sin − F cos)' = f sin`, and by the **fundamental theorem of calculus**
  `∫₀^π f(x) sin x dx = F(π) + F(0)`, an integer.
* But on `(0, π)` we have `0 < f(x) sin x ≤ (π a)ⁿ / n!`, so the integral lies strictly between
  `0` and `π (π a)ⁿ / n!`, which is `< 1` for large `n` — the terms of the exponential series tend
  to `0`. An integer strictly between `0` and `1`: contradiction.

Polynomials are represented by their coefficient sequences `c : ℕ → ℝ` (evaluated by
`poly c d x = Σ_{k<d} cₖ xᵏ`); differentiation acts on coefficients by `cₖ ↦ (k+1) cₖ₊₁`.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-! ## Integers inside `R` -/

/-- `x` is an **integer** (the image of some `z : Int`). -/
def IsInt (x : R) : Prop := ∃ z : Int, x = (z : R)

/-- `0` is an integer. -/
theorem isInt_zero : IsInt 0 := ⟨0, by grind⟩

/-- Natural numbers are integers. -/
theorem isInt_natCast (n : Nat) : IsInt (n : R) := ⟨n, (Ring.intCast_natCast n).symm⟩

/-- Sums of integers are integers. -/
theorem IsInt.add {x y : R} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨z, rfl⟩ := hx; obtain ⟨w, rfl⟩ := hy; exact ⟨z + w, by grind⟩

/-- Products of integers are integers. -/
theorem IsInt.mul {x y : R} (hx : IsInt x) (hy : IsInt y) : IsInt (x * y) := by
  obtain ⟨z, rfl⟩ := hx; obtain ⟨w, rfl⟩ := hy; exact ⟨z * w, by grind⟩

/-- Negatives of integers are integers. -/
theorem IsInt.neg {x : R} (hx : IsInt x) : IsInt (-x) := by
  obtain ⟨z, rfl⟩ := hx; exact ⟨-z, by grind⟩

/-- Differences of integers are integers. -/
theorem IsInt.sub {x y : R} (hx : IsInt x) (hy : IsInt y) : IsInt (x - y) := by
  have := hx.add hy.neg; rw [show x + -y = x - y by grind] at this; exact this

/-- Finite sums of integers are integers. -/
theorem isInt_fsum {f : Nat → R} (h : ∀ k, IsInt (f k)) (n : Nat) : IsInt (fsum f n) := by
  induction n with
  | zero => exact isInt_zero
  | succ n ih => rw [fsum_succ]; exact ih.add (h n)

/-- Powers of `−1` are integers. -/
theorem isInt_neg_one_pow (j : Nat) : IsInt ((-1 : R) ^ j) := by
  induction j with
  | zero => exact ⟨1, by show (1 : R) = _; grind⟩
  | succ j ih => rw [pow_succ']; exact ih.mul ⟨-1, by grind⟩

/-- `(−1)²ʲ = 1`. -/
theorem neg_one_pow_two_mul (j : Nat) : (-1 : R) ^ (2 * j) = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, pow_succ', pow_succ', ih]; grind

/-! ## Polynomials as coefficient sequences -/

/-- The coefficients `cₖ` vanish from index `d` on. -/
def Vanish (c : Nat → R) (d : Nat) : Prop := ∀ k, d ≤ k → c k = 0

/-- The **derivative** of a polynomial, on coefficients: `cₖ ↦ (k + 1) cₖ₊₁`. -/
def pderiv (c : Nat → R) (k : Nat) : R := ((k : R) + 1) * c (k + 1)

/-- The `m`-th derivative, on coefficients. -/
def iterD : Nat → (Nat → R) → (Nat → R)
  | 0, c => c
  | m + 1, c => pderiv (iterD m c)

/-- Differentiation does not raise the degree. -/
theorem Vanish.pderiv {c : Nat → R} {d : Nat} (h : Vanish c d) : Vanish (pderiv c) d :=
  fun k hk => by unfold R.pderiv; rw [h (k + 1) (by omega)]; grind

/-- All derivatives vanish beyond the degree bound. -/
theorem Vanish.iterD {c : Nat → R} {d : Nat} (h : Vanish c d) (m : Nat) : Vanish (iterD m c) d := by
  induction m with
  | zero => exact h
  | succ m ih => exact ih.pderiv

/-- A sum of zeros is zero. -/
theorem fsum_zero' {f : Nat → R} (h : ∀ k, f k = 0) (n : Nat) : fsum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fsum_succ, ih, h n]; grind

/-- **Derivative of a polynomial** in coefficient form: `(poly c d)' = poly (pderiv c) d`, if the
coefficients vanish from `d` on. -/
theorem hasDerivAt_poly' {c : Nat → R} {d : Nat} (hc : Vanish c d) (x : R) :
    HasDerivAt (poly c d) (poly (pderiv c) d x) x := by
  have h := hasDerivAt_poly c d x
  have e : fsum (fun k => c k * ((k : R) * x ^ (k - 1))) d = poly (pderiv c) d x := by
    cases d with
    | zero => rfl
    | succ d =>
      unfold poly
      rw [fsum_succ', fsum_succ]
      have : pderiv c d = 0 := by unfold R.pderiv; rw [hc (d + 1) (Nat.le_refl _)]; grind
      rw [this]
      have e0 : c 0 * (((0 : Nat) : R) * x ^ (0 - 1)) = 0 := by grind
      rw [e0]
      have : fsum (fun k => c (k + 1) * (((k + 1 : Nat) : R) * x ^ (k + 1 - 1))) d =
          fsum (fun k => pderiv c k * x ^ k) d := fsum_congr fun k _ => by
        unfold R.pderiv; rw [show k + 1 - 1 = k by omega]; grind
      rw [this]; grind
  rw [e] at h; exact h

/-- Evaluating at `0` gives the constant coefficient. -/
theorem poly_zero (c : Nat → R) (d : Nat) : poly c (d + 1) 0 = c 0 := by
  unfold poly
  rw [fsum_succ', fsum_zero' fun k => by show c (k + 1) * (0 : R) ^ (k + 1) = 0; rw [pow_succ']; grind]
  show c 0 * 1 + 0 = c 0; grind

/-- The `m`-th derivative in coefficient form: `k! · (Dᵐc)ₖ = (k + m)! · cₖ₊ₘ`. -/
theorem fact_mul_iterD (c : Nat → R) (m : Nat) :
    ∀ k, (fact k : R) * iterD m c k = (fact (k + m) : R) * c (k + m) := by
  induction m with
  | zero => intro k; rfl
  | succ m ih =>
    intro k
    show (fact k : R) * (((k : R) + 1) * iterD m c (k + 1)) = _
    have := ih (k + 1)
    rw [fact_succ'] at this
    rw [show k + (m + 1) = k + 1 + m by omega]
    grind

/-- Derivatives of order beyond the degree vanish. -/
theorem iterD_eq_zero {c : Nat → R} {d : Nat} (hc : Vanish c d) {m k : Nat} (h : d ≤ k + m) :
    iterD m c k = 0 := by
  have := fact_mul_iterD c m k
  rw [hc (k + m) h] at this
  have := fact_pos' k
  apply Classical.byContradiction; intro hne
  have := OrderedRing.mul_pos this (by
    rcases (by grind : iterD m c k < 0 ∨ 0 < iterD m c k) with h' | h'
    · exfalso
      have := OrderedRing.mul_pos (fact_pos' k) (by grind : 0 < -iterD m c k); grind
    · exact h')
  grind

/-- **Reflection of derivatives.** If `poly e d (P − y) = poly e d y` for all `y`, then the
`m`-th derivative satisfies `e⁽ᵐ⁾(P − y) = (−1)ᵐ e⁽ᵐ⁾(y)`. -/
theorem poly_reflect {e : Nat → R} {d : Nat} (he : Vanish e d) (P : R)
    (h0 : ∀ y, poly e d (P - y) = poly e d y) :
    ∀ m y, poly (iterD m e) d (P - y) = (-1) ^ m * poly (iterD m e) d y := by
  intro m
  induction m with
  | zero => intro y; show poly e d (P - y) = (-1) ^ 0 * poly e d y; rw [h0]; show _ = 1 * _; grind
  | succ m ih =>
    intro y
    -- Differentiate both sides of the identity for `m`.
    have h1 : HasDerivAt (fun y => poly (iterD m e) d (P - y))
        (poly (iterD (m + 1) e) d (P - y) * (0 - 1)) y :=
      (hasDerivAt_poly' (he.iterD m) (P - y)).comp (f := fun y => P - y)
        ((hasDerivAt_const P y).sub (hasDerivAt_id y))
    have h2 : HasDerivAt (fun y => (-1) ^ m * poly (iterD m e) d y)
        ((-1) ^ m * poly (iterD (m + 1) e) d y) y :=
      (hasDerivAt_poly' (he.iterD m) y).const_mul _
    have := h1.unique (h2.congr fun y => (ih y).symm)
    rw [pow_succ']; grind

/-! ## Niven's polynomial -/

/-- The coefficients of `(a − b x)ʲ`. -/
def linPow (a b : R) : Nat → Nat → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, 0 => a * linPow a b j 0
  | j + 1, k + 1 => a * linPow a b j (k + 1) - b * linPow a b j k

/-- `(a − b x)ʲ` has degree `≤ j`. -/
theorem linPow_vanish (a b : R) : ∀ j k, j < k → linPow a b j k = 0 := by
  intro j
  induction j with
  | zero => intro k hk; obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl
  | succ j ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    show a * linPow a b j (k + 1) - b * linPow a b j k = 0
    rw [ih (k + 1) (by omega), ih k (by omega)]; grind

/-- For integers `a, b`, the coefficients of `(a − b x)ʲ` are integers. -/
theorem linPow_isInt {a b : R} (ha : IsInt a) (hb : IsInt b) : ∀ j k, IsInt (linPow a b j k) := by
  intro j
  induction j with
  | zero => intro k; cases k with
    | zero => exact ⟨1, by show (1 : R) = _; grind⟩
    | succ k => exact isInt_zero
  | succ j ih => intro k; cases k with
    | zero => exact ha.mul (ih 0)
    | succ k => exact (ha.mul (ih (k + 1))).sub (hb.mul (ih k))

/-- Evaluation: `Σ_{k ≤ j} linPow j k · xᵏ = (a − b x)ʲ`. -/
theorem poly_linPow (a b x : R) (j : Nat) : poly (linPow a b j) (j + 1) x = (a - b * x) ^ j := by
  induction j with
  | zero => show 0 + 1 * x ^ 0 = (a - b * x) ^ 0; show (0 : R) + 1 * 1 = 1; grind
  | succ j ih =>
    unfold poly at ih ⊢
    rw [fsum_succ']
    have e1 : fsum (fun k => linPow a b (j + 1) (k + 1) * x ^ (k + 1)) (j + 1) =
        a * fsum (fun k => linPow a b j (k + 1) * x ^ (k + 1)) (j + 1) -
          b * x * fsum (fun k => linPow a b j k * x ^ k) (j + 1) := by
      rw [← fsum_const_mul, ← fsum_const_mul, ← fsum_sub]
      exact fsum_congr fun k _ => by
        show (a * linPow a b j (k + 1) - b * linPow a b j k) * x ^ (k + 1) = _
        rw [pow_succ']; grind
    have e2 := fsum_succ' (fun k => linPow a b j k * x ^ k) (j + 1)
    rw [fsum_succ, linPow_vanish a b j (j + 1) (by omega), ih] at e2
    rw [e1, ih, pow_succ']
    show a * linPow a b j 0 * x ^ 0 + _ = _
    have : linPow a b j 0 * x ^ 0 + fsum (fun k => linPow a b j (k + 1) * x ^ (k + 1)) (j + 1) =
        (a - b * x) ^ j := by grind
    grind

/-- `x^(n + k) = xⁿ xᵏ`. -/
theorem pow_add' (x : R) (n k : Nat) : x ^ (n + k) = x ^ n * x ^ k := by
  induction k with
  | zero => show x ^ n = x ^ n * 1; grind
  | succ k ih => rw [← Nat.add_assoc, pow_succ', pow_succ', ih]; grind

/-- `(u v)ⁿ = uⁿ vⁿ`. -/
theorem mul_pow' (u v : R) (n : Nat) : (u * v) ^ n = u ^ n * v ^ n := by
  induction n with
  | zero => show (1 : R) = 1 * 1; grind
  | succ n ih => rw [pow_succ', pow_succ', pow_succ', ih]; grind

/-- The integer coefficients of `n! f(x) = xⁿ (a − b x)ⁿ`. -/
def nivenH (a b : R) (n k : Nat) : R := if n ≤ k then linPow a b n (k - n) else 0

/-- Evaluation: `Σ nivenHₖ xᵏ = xⁿ (a − b x)ⁿ`. -/
theorem poly_nivenH (a b x : R) (n : Nat) :
    poly (nivenH a b n) (2 * n + 1) x = x ^ n * (a - b * x) ^ n := by
  have h2 : fsum (fun k => nivenH a b n (n + k) * x ^ (n + k)) (n + 1) =
      x ^ n * poly (linPow a b n) (n + 1) x := by
    unfold poly; rw [← fsum_const_mul]
    exact fsum_congr fun k _ => by
      unfold nivenH
      split
      · rw [Nat.add_sub_cancel_left, pow_add']; grind
      · omega
  unfold poly
  rw [show 2 * n + 1 = n + (n + 1) by omega, fsum_split]
  have h1 : fsum (fun k => nivenH a b n k * x ^ k) n = 0 := by
    rw [fsum_congr (b := fun _ => 0) fun k hk => by
      show nivenH a b n k * x ^ k = 0
      unfold nivenH; split
      · omega
      · grind]
    exact fsum_zero' (fun _ => rfl) n
  rw [h1, h2, poly_linPow]; grind

/-- Niven's polynomial vanishes from degree `2n + 1` on. -/
theorem nivenH_vanish (a b : R) (n : Nat) : Vanish (nivenH a b n) (2 * n + 1) := fun k hk => by
  unfold nivenH; split
  · exact linPow_vanish a b n (k - n) (by omega)
  · rfl

/-- For integers `a, b`, the coefficients of `n! f` are integers. -/
theorem nivenH_isInt {a b : R} (ha : IsInt a) (hb : IsInt b) (n k : Nat) : IsInt (nivenH a b n k) := by
  unfold nivenH; split
  · exact linPow_isInt ha hb n _
  · exact isInt_zero

/-- The coefficients of **Niven's polynomial** `f(x) = xⁿ (a − b x)ⁿ / n!`. -/
noncomputable def nivenC (a b : R) (n k : Nat) : R := nivenH a b n k / (fact n : R)

/-- `f` vanishes from degree `2n + 1` on. -/
theorem nivenC_vanish (a b : R) (n : Nat) : Vanish (nivenC a b n) (2 * n + 1) := fun k hk => by
  unfold nivenC; rw [nivenH_vanish a b n k hk]; grind

/-- Evaluation of Niven's polynomial: `f(x) = xⁿ (a − b x)ⁿ / n!`. -/
theorem poly_nivenC (a b x : R) (n : Nat) :
    poly (nivenC a b n) (2 * n + 1) x = x ^ n * (a - b * x) ^ n / (fact n : R) := by
  have := poly_nivenH a b x n
  unfold poly at this ⊢
  have e : fsum (fun k => nivenC a b n k * x ^ k) (2 * n + 1) =
      (1 / (fact n : R)) * fsum (fun k => nivenH a b n k * x ^ k) (2 * n + 1) := by
    rw [← fsum_const_mul]; exact fsum_congr fun k _ => by unfold nivenC; grind
  rw [e, this]; grind

/-- **All derivatives of `f` at `0` are integers.** -/
theorem iterD_nivenC_isInt {a b : R} (ha : IsInt a) (hb : IsInt b) (n m : Nat) :
    IsInt (iterD m (nivenC a b n) 0) := by
  have h := fact_mul_iterD (nivenC a b n) m 0
  rw [Nat.zero_add, show fact 0 = 1 from rfl] at h
  have e : iterD m (nivenC a b n) 0 = (fact m : R) * nivenC a b n m := by grind
  rw [e]; unfold nivenC
  by_cases hm : n ≤ m
  · obtain ⟨r, hr⟩ := fact_dvd_fact hm
    have : (fact m : R) = (fact n : R) * (r : R) := by rw [hr]; grind
    rw [this]
    have := fact_pos' n
    have e2 : (fact n : R) * (r : R) * (nivenH a b n m / (fact n : R)) = (r : R) * nivenH a b n m := by
      grind
    rw [e2]; exact (isInt_natCast r).mul (nivenH_isInt ha hb n m)
  · unfold nivenH; rw [show (if n ≤ m then linPow a b n (m - n) else 0) = 0 by split <;> first | omega | rfl]
    exact ⟨0, by grind⟩

/-- Telescoping sums: `Σ_{j<N} (uⱼ − uⱼ₊₁) = u₀ − u_N`. -/
theorem fsum_telescope (u : Nat → R) (N : Nat) : fsum (fun j => u j - u (j + 1)) N = u 0 - u N := by
  induction N with
  | zero => show (0 : R) = u 0 - u 0; grind
  | succ N ih => rw [fsum_succ, ih]; grind

/-- The alternating sums `F⁽ⁱ⁾ = Σ_{j ≤ n} (−1)ʲ f⁽²ʲ⁺ⁱ⁾`; `F = nivenF 0`, `F' = nivenF 1`,
`F'' = nivenF 2`. -/
noncomputable def nivenF (a b : R) (n i : Nat) (x : R) : R :=
  fsum (fun j => (-1) ^ j * poly (iterD (2 * j + i) (nivenC a b n)) (2 * n + 1) x) (n + 1)

/-- `(F⁽ⁱ⁾)' = F⁽ⁱ⁺¹⁾`. -/
theorem hasDerivAt_nivenF (a b : R) (n i : Nat) (x : R) :
    HasDerivAt (nivenF a b n i) (nivenF a b n (i + 1) x) x :=
  hasDerivAt_fsum _ _ (n + 1) fun j _ =>
    (hasDerivAt_poly' ((nivenC_vanish a b n).iterD (2 * j + i)) x).const_mul _

/-- **`F'' + F = f`**: the alternating sum telescopes, and `f⁽²ⁿ⁺²⁾ = 0`. -/
theorem nivenF_two_add (a b : R) (n : Nat) (x : R) :
    nivenF a b n 2 x + nivenF a b n 0 x = poly (nivenC a b n) (2 * n + 1) x := by
  let u : Nat → R := fun j => (-1) ^ j * poly (iterD (2 * j) (nivenC a b n)) (2 * n + 1) x
  have h := fsum_telescope u (n + 1)
  have hz : u (n + 1) = 0 := by
    show (-1) ^ (n + 1) * poly (iterD (2 * (n + 1)) (nivenC a b n)) (2 * n + 1) x = 0
    unfold poly
    rw [fsum_zero' fun k => by
      rw [iterD_eq_zero (nivenC_vanish a b n) (by omega : 2 * n + 1 ≤ k + 2 * (n + 1))]; grind]
    grind
  have h0 : u 0 = poly (nivenC a b n) (2 * n + 1) x := by
    show (-1) ^ 0 * poly (iterD (2 * 0) (nivenC a b n)) (2 * n + 1) x = _
    show 1 * poly (nivenC a b n) (2 * n + 1) x = _; grind
  rw [hz, h0, show ∀ t : R, t - 0 = t from fun t => by grind] at h
  rw [← h]
  unfold nivenF
  rw [← fsum_add]
  apply fsum_congr
  intro j _
  show (-1) ^ j * poly (iterD (2 * j + 2) (nivenC a b n)) (2 * n + 1) x +
    (-1) ^ j * poly (iterD (2 * j + 0) (nivenC a b n)) (2 * n + 1) x =
    (-1) ^ j * poly (iterD (2 * j) (nivenC a b n)) (2 * n + 1) x -
    (-1) ^ (j + 1) * poly (iterD (2 * (j + 1)) (nivenC a b n)) (2 * n + 1) x
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.add_zero, pow_succ']
  grind

/-- `n! f(π − y) = n! f(y)` when `b π = a`. -/
theorem poly_nivenC_reflect {a b P : R} (hP : b * P = a) (n : Nat) (y : R) :
    poly (nivenC a b n) (2 * n + 1) (P - y) = poly (nivenC a b n) (2 * n + 1) y := by
  rw [poly_nivenC, poly_nivenC, ← mul_pow', ← mul_pow']
  rw [show (P - y) * (a - b * (P - y)) = y * (a - b * y) by rw [← hP]; grind]

/-- `0 < x ⇒ 0 < xⁿ`. -/
theorem pow_pos' {x : R} (hx : 0 < x) (n : Nat) : 0 < x ^ n := by
  induction n with
  | zero => show (0 : R) < 1; grind
  | succ n ih => rw [pow_succ']; exact OrderedRing.mul_pos ih hx

/-- `sin x ≤ 1`. -/
theorem sin_le_one (x : R) : sin x ≤ 1 := by
  have h := sin_sq_add_cos_sq x
  have := OrderedRing.sq_nonneg (a := cos x)
  apply Classical.byContradiction; intro hlt
  have := OrderedRing.mul_lt_mul_of_pos_left (by grind : 1 < sin x) (by grind : (0 : R) < sin x)
  grind

/-- The terms of the exponential series tend to `0`. -/
theorem tendsto_expTerm_zero (x : R) : Tendsto (expTerm x) 0 := by
  have h := ((hasSum_exp x : Tendsto _ _).shift 1).sub (hasSum_exp x : Tendsto _ _)
  rw [show exp x - exp x = 0 by grind] at h
  exact h.congr_eventually 0 fun n _ => by
    show fsum (expTerm x) (1 + n) - fsum (expTerm x) n = expTerm x n
    rw [Nat.add_comm, fsum_succ]; grind

/-- **π is irrational** (Lambert 1761; proof of Niven 1947). There are no integers `p` and
`q > 0` with `π = p / q`. -/
theorem pi_irrational : ¬ ∃ p : Int, ∃ q : Nat, 0 < q ∧ pi = (p : R) / (q : R) := by
  rintro ⟨p, q, hq, hpq⟩
  have hπ := pi_pos
  have hb : (0 : R) < (q : R) := OrderedRing.pos_natCast_of_pos _ hq
  have hbP : (q : R) * pi = (p : R) := by rw [hpq]; grind
  have ha : (0 : R) < (p : R) := by rw [← hbP]; exact OrderedRing.mul_pos hb hπ
  -- Notation: `a = p`, `b = q`, and `n` so large that `π (π a)ⁿ / n! < 1`.
  generalize hA : (p : R) = a at ha hbP
  generalize hB : (q : R) = b at hb hbP
  have hai : IsInt a := ⟨p, hA.symm⟩
  have hbi : IsInt b := ⟨q, by rw [← hB]; exact (Ring.intCast_natCast q).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : Nat, pi * expTerm (pi * a) n < 1 := by
    obtain ⟨N, hN⟩ := tendsto_expTerm_zero (pi * a) (1 / pi) (div_pos (by grind) hπ)
    have := abs_lt.1 (hN N (Nat.le_refl N))
    refine ⟨N, ?_⟩
    have k := OrderedRing.mul_lt_mul_of_pos_left (by grind : expTerm (pi * a) N < 1 / pi) hπ
    have : pi * (1 / pi) = 1 := by grind
    grind
  let d := 2 * n + 1
  let c := nivenC a b n
  let f : R → R := fun x => poly c d x
  let h : R → R := fun x => f x * sin x
  have hfd : ∀ x, HasDerivAt f (poly (pderiv c) d x) x := fun x =>
    hasDerivAt_poly' (nivenC_vanish a b n) x
  have hcont : ∀ x, ContinuousAt h x := fun x => ((hfd x).mul (hasDerivAt_sin x)).continuousAt
  -- The integral `∫₀^π f sin` equals `F(π) + F(0) = 2 F(0)`, an even integer.
  let G : R → R := fun x => nivenF a b n 1 x * sin x - nivenF a b n 0 x * cos x
  have hG : ∀ x, HasDerivAt G (h x) x := fun x => by
    have := ((hasDerivAt_nivenF a b n 1 x).mul (hasDerivAt_sin x)).sub
      ((hasDerivAt_nivenF a b n 0 x).mul (hasDerivAt_cos x))
    have e : nivenF a b n (1 + 1) x * sin x + nivenF a b n 1 x * cos x -
        (nivenF a b n (0 + 1) x * cos x + nivenF a b n 0 x * -sin x) = h x := by
      have := nivenF_two_add a b n x
      show _ = poly c d x * sin x
      rw [← this]; grind
    rw [e] at this; exact this
  have hI : integral h 0 pi = G pi - G 0 :=
    integral_eq_sub (Std.le_of_lt hπ) (fun t _ _ => hG t) (fun t _ _ => hcont t)
  have hrefl := poly_reflect (nivenC_vanish a b n) pi (poly_nivenC_reflect hbP n)
  have hFπ : nivenF a b n 0 pi = nivenF a b n 0 0 := by
    unfold nivenF
    apply fsum_congr; intro j _
    have := hrefl (2 * j + 0) 0
    rw [show pi - 0 = pi by grind, Nat.add_zero, neg_one_pow_two_mul] at this
    rw [Nat.add_zero, this]; grind
  have hF0 : IsInt (nivenF a b n 0 0) := isInt_fsum (fun j => (isInt_neg_one_pow j).mul (by
    show IsInt (poly (iterD (2 * j + 0) (nivenC a b n)) (2 * n + 1) 0)
    rw [poly_zero]; exact iterD_nivenC_isInt hai hbi n _)) (n + 1)
  have hIval : integral h 0 pi = 2 * nivenF a b n 0 0 := by
    rw [hI]; show nivenF a b n 1 pi * sin pi - nivenF a b n 0 pi * cos pi -
      (nivenF a b n 1 0 * sin 0 - nivenF a b n 0 0 * cos 0) = _
    rw [sin_pi, cos_pi, sin_zero, cos_zero, hFπ]; grind
  -- Pointwise bounds: `0 < f sin` on `(0, π)` and `f sin ≤ (π a)ⁿ / n!` on `[0, π]`.
  have hfval : ∀ x, f x = x ^ n * (a - b * x) ^ n / (fact n : R) := fun x => poly_nivenC a b x n
  have hfpos : ∀ x, 0 < x → x < pi → 0 < h x := fun x h0 h1 => by
    show 0 < f x * sin x
    rw [hfval]
    have k1 := pow_pos' h0 n
    have hbx : b * x < b * pi := OrderedRing.mul_lt_mul_of_pos_left h1 hb
    have k2 := pow_pos' (by grind : 0 < a - b * x) n
    exact OrderedRing.mul_pos (div_pos (OrderedRing.mul_pos k1 k2) (fact_pos' n))
      (sin_pos_of_pos_of_lt_pi h0 h1)
  have hfle : ∀ x, 0 ≤ x → x ≤ pi → h x ≤ expTerm (pi * a) n := fun x h0 h1 => by
    show f x * sin x ≤ _
    rw [hfval]
    have hbx : b * x ≤ b * pi := OrderedRing.mul_le_mul_of_nonneg_left h1 (Std.le_of_lt hb)
    have hbx0 : 0 ≤ b * x := OrderedRing.mul_nonneg (Std.le_of_lt hb) h0
    have k1 := pow_le_pow_left h0 h1 n
    have k2 := pow_le_pow_left (by grind : 0 ≤ a - b * x) (by grind : a - b * x ≤ a) n
    have p1 := pow_le_pow_left.pow_nonneg h0 n
    have p2 := pow_le_pow_left.pow_nonneg (by grind : 0 ≤ a - b * x) n
    have p3 := pow_le_pow_left.pow_nonneg (Std.le_of_lt hπ) n
    have k3 := OrderedRing.mul_le_mul_of_nonneg_right k1 p2
    have k4 := OrderedRing.mul_le_mul_of_nonneg_left k2 p3
    have hinv := Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 (fact_pos' n))
    have k5 := OrderedRing.mul_le_mul_of_nonneg_right (Std.le_trans k3 k4) hinv
    have hfx : 0 ≤ x ^ n * (a - b * x) ^ n / (fact n : R) := by
      rw [Field.div_eq_mul_inv]; exact OrderedRing.mul_nonneg (OrderedRing.mul_nonneg p1 p2) hinv
    have k6 := OrderedRing.mul_le_mul_of_nonneg_left (sin_le_one x) hfx
    unfold expTerm
    rw [mul_pow']
    rw [Field.div_eq_mul_inv] at hfx k6 ⊢
    grind
  -- Lower bound: on `[π/4, 3π/4]` the integrand is at least its (positive) minimum.
  obtain ⟨m, hm1, hm2, hmin⟩ := extreme_value (f := fun x => 0 - h x) (a := pi / 4)
    (b := 3 * pi / 4) (by grind) (fun x _ _ => continuousAt_sub (continuousAt_const 0 x) (hcont x))
  have hmin' : ∀ x, pi / 4 ≤ x → x ≤ 3 * pi / 4 → h m ≤ h x := fun x h1 h2 => by
    have : 0 - h x ≤ 0 - h m := hmin x h1 h2
    grind
  have hm0 : 0 < h m := hfpos m (by grind) (by grind)
  have hnn : ∀ t, 0 ≤ t → t ≤ pi → 0 ≤ h t := fun t h1 h2 => by
    rcases (by grind : t = 0 ∨ t = pi ∨ (0 < t ∧ t < pi)) with e | e | ⟨e1, e2⟩
    · show 0 ≤ f t * sin t; rw [e, sin_zero]; grind
    · show 0 ≤ f t * sin t; rw [e, sin_pi]; grind
    · exact Std.le_of_lt (hfpos t e1 e2)
  have hc : ∀ u v : R, ∀ x, u ≤ x → x ≤ v → ContinuousAt h x := fun _ _ x _ _ => hcont x
  have I1 := HasIntegral.mono (by grind) (hasIntegral_const 0 (by grind : (0 : R) ≤ pi / 4))
    (hasIntegral_integral (by grind : (0 : R) ≤ pi / 4) (hc 0 (pi / 4)))
    (fun t h1 h2 => hnn t h1 (by grind))
  have I2 := HasIntegral.mono (by grind)
    (hasIntegral_const (h m) (by grind : pi / 4 ≤ 3 * pi / 4))
    (hasIntegral_integral (by grind : pi / 4 ≤ 3 * pi / 4) (hc (pi / 4) (3 * pi / 4)))
    (fun t h1 h2 => hmin' t h1 h2)
  have I3 := HasIntegral.mono (by grind) (hasIntegral_const 0 (by grind : 3 * pi / 4 ≤ pi))
    (hasIntegral_integral (by grind : 3 * pi / 4 ≤ pi) (hc (3 * pi / 4) pi))
    (fun t h1 h2 => hnn t (by grind) h2)
  have I4 := HasIntegral.mono (by grind)
    (hasIntegral_integral (Std.le_of_lt hπ) (hc 0 pi))
    (hasIntegral_const (expTerm (pi * a) n) (Std.le_of_lt hπ))
    (fun t h1 h2 => hfle t h1 h2)
  have A1 := integral_add_interval (f := h) (a := 0) (u := 3 * pi / 4) (v := pi) (by grind) (by grind)
    (hc 0 pi)
  have A2 := integral_add_interval (f := h) (a := 0) (u := pi / 4) (v := 3 * pi / 4) (by grind)
    (by grind) (hc 0 (3 * pi / 4))
  have hpos : 0 < integral h 0 pi := by
    have := OrderedRing.mul_pos hm0 (by grind : (0 : R) < 3 * pi / 4 - pi / 4)
    grind
  have hlt : integral h 0 pi < 1 := by grind
  -- So `2 F(0)` is an integer strictly between `0` and `1`.
  obtain ⟨z, hz⟩ := hF0
  rw [hIval, hz] at hpos hlt
  have z1 : ((0 : Int) : R) < ((2 * z : Int) : R) := by grind
  have z2 : ((2 * z : Int) : R) < ((1 : Int) : R) := by grind
  have := (intCast_lt (K := R)).1 z1
  have := (intCast_lt (K := R)).1 z2
  omega

end R

end Foundations.Numbers
