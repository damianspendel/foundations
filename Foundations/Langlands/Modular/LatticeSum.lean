import Foundations.Langlands.Modular.SquareSums

/-!
# The lattice-sum estimate

For `τ ∈ ℍ` the numbers `mτ + n`, `(m, n) ∈ ℤ²`, form a **lattice** `Λ_τ = ℤτ + ℤ` in ℂ. Since
`τ` and `1` are linearly independent over ℝ, a lattice vector can only be short if both of its
coordinates are small. Quantitatively (`lattice_estimate`):

  **there is `C(τ) > 0` with `|mτ + n| ≥ C(τ) · max(|m|, |n|)` for all integers `m, n`.**

We prove it from an explicit inequality for the positive definite quadratic form
`|mτ + n|² = (mx + n)² + (my)²` (`τ = x + iy`): with `D = x² + y² + 1`,

  `y² (m² + n²) ≤ 4D · |mτ + n|²`  (`normSq_lin_ge`),

and `C(τ) = √(y²/4D)`.

Consequently, for `k ≥ 3`, the terms `|mτ + n|^{−k}` are at most `C^{−k} max(|m|, |n|)^{−3}`
(`cabs_eterm_mul_le`). On the boundary of the square `Q_N` there are exactly
`(2N + 1)² − (2N − 1)² = 8N` lattice points, all with `max(|m|, |n|) = N`; so the contribution of
that shell is at most `8N · C^{−k} N^{−3} = 8 C^{−k} N^{−2}`. Summing over shells
(`Lattice.sq_cabs_le`, with `Σ 1/N² ≤ 2` by telescoping) gives

  **`Σ_{(m,n) ∈ Q_N} |mτ + n|^{−k} ≤ 16 C(τ)^{−k}` for all `N`** (`abs_lattice_sum_bounded`),

so the double series `Σ' |mτ + n|^{−k}` **converges** along squares (`abs_lattice_sum_converges`).
This is the classical argument of Eisenstein (1847), who was the first to sum such double series
with care, and it is what makes the definition of the Eisenstein series in the next file possible.

We also set up limits of complex sequences in the modulus (`CLim`), with uniqueness and the
Cauchy criterion, built on the completeness of ℝ.
-/

namespace Foundations.Langlands.Modular

open Foundations.Numbers Foundations.Numbers.C Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

namespace Lattice

/-! ## Small real lemmas -/

/-- `0 < x⁻¹` for `0 < x`. -/
theorem inv_pos' {x : R} (hx : 0 < x) : 0 < x⁻¹ := Field.IsOrdered.inv_pos_iff.2 hx

/-- From `X · T ≤ P` with `P, X > 0` deduce `P⁻¹ · T ≤ X⁻¹`. -/
theorem inv_mul_le_inv {P T X : R} (hP : 0 < P) (hX : 0 < X) (h : X * T ≤ P) :
    P⁻¹ * T ≤ X⁻¹ := by
  have h1 : 0 ≤ P⁻¹ * X⁻¹ := Std.le_of_lt (OrderedRing.mul_pos (inv_pos' hP) (inv_pos' hX))
  have := OrderedRing.mul_le_mul_of_nonneg_left h h1
  have e1 : P * P⁻¹ = 1 := by grind
  have e2 : X * X⁻¹ = 1 := by grind
  have e3 : P⁻¹ * X⁻¹ * (X * T) = P⁻¹ * T := by grind
  have e4 : P⁻¹ * X⁻¹ * P = X⁻¹ := by grind
  grind

/-- Powers of positive reals are positive. -/
theorem rpow_pos {x : R} (hx : 0 < x) (n : Nat) : 0 < x ^ n := by
  induction n with
  | zero => show (0 : R) < 1; grind
  | succ n ih => rw [R.pow_succ']; exact OrderedRing.mul_pos ih hx

/-- `(uv)ⁿ = uⁿvⁿ` in ℝ. -/
theorem rmul_pow (u v : R) (n : Nat) : (u * v) ^ n = u ^ n * v ^ n := by
  induction n with
  | zero => show (1 : R) = 1 * 1; grind
  | succ n ih => rw [R.pow_succ', R.pow_succ', R.pow_succ', ih]; grind

/-- `1 ≤ x` implies `xᵃ ≤ xᵃ⁺ᵇ`. -/
theorem pow_le_pow_add {x : R} (hx : 1 ≤ x) (a b : Nat) : x ^ a ≤ x ^ (a + b) := by
  induction b with
  | zero => grind
  | succ b ih =>
    rw [← Nat.add_assoc, R.pow_succ']
    have h0 : 0 ≤ x ^ (a + b) := Std.le_of_lt (rpow_pos (by grind) _)
    have := OrderedRing.mul_le_mul_of_nonneg_left hx h0
    grind

/-- Squares of real numbers are non-negative. -/
theorem sq_nonneg' (a : R) : 0 ≤ a * a := C.mul_self_nonneg a

/-- The square of `|m|` (as a natural number cast to ℝ) is `m²`. -/
theorem natAbs_sq (m : Int) :
    ((m.natAbs : Nat) : R) * ((m.natAbs : Nat) : R) = (m : R) * (m : R) := by
  rw [← Ring.intCast_natCast, ← Ring.intCast_mul, ← Ring.intCast_mul, Int.natAbs_mul_self']

/-! ## The lattice and its sup-norm -/

/-- The lattice vector `mτ + n`. -/
def lin (z : C) (m n : Int) : C := (m : C) * z + (n : C)

/-- `|mτ + n|² = (mx + n)² + (my)²`. -/
theorem normSq_lin (z : C) (m n : Int) : normSq (lin z m n) = SL2Z.Q z m n := by
  simp only [normSq, lin, SL2Z.Q, add_re, add_im, mul_re, mul_im, SL2Z.intCast_re,
    SL2Z.intCast_im]
  grind

/-- **The sup-norm** `max(|m|, |n|)` of a lattice point. -/
def supNorm (m n : Int) : Nat := max m.natAbs n.natAbs

/-- `max(|m|, |n|)² ≤ m² + n²`. -/
theorem supNorm_sq_le (m n : Int) :
    ((supNorm m n : Nat) : R) * ((supNorm m n : Nat) : R) ≤ (m : R) * (m : R) + (n : R) * (n : R) := by
  have h1 := natAbs_sq m
  have h2 := natAbs_sq n
  have h3 := sq_nonneg' (m : R)
  have h4 := sq_nonneg' (n : R)
  unfold supNorm
  rcases Nat.le_total m.natAbs n.natAbs with h | h
  · rw [Nat.max_eq_right h]; grind
  · rw [Nat.max_eq_left h]; grind

/-- **The quadratic-form inequality.** For `τ = x + iy` and `D = x² + y² + 1`,
`y² (m² + n²) ≤ 4D · |mτ + n|²`. -/
theorem normSq_lin_ge (z : C) (m n : Int) :
    z.im * z.im * ((m : R) * (m : R) + (n : R) * (n : R)) ≤
      4 * (z.re * z.re + z.im * z.im + 1) * normSq (lin z m n) := by
  rw [normSq_lin]; unfold SL2Z.Q
  generalize z.re = x; generalize z.im = y; generalize (m : R) = a; generalize (n : R) = b
  -- with `u = ax + b`, all the terms below are non-negative.
  have k1 := sq_nonneg' (y * (a * x + b + a * x))
  have k2 := sq_nonneg' (x * (a * x + b))
  have k3 := sq_nonneg' (y * (a * x + b))
  have k4 := sq_nonneg' (a * x + b)
  have k5 := sq_nonneg' (x * a * y)
  have k6 := sq_nonneg' (y * y * a)
  have k7 := sq_nonneg' (a * y)
  grind

/-- **The lattice-sum estimate.** For `τ ∈ ℍ` there is a constant `C(τ) > 0` such that
`|mτ + n| ≥ C(τ) · max(|m|, |n|)` for all integers `m, n`. -/
theorem lattice_estimate (p : UHP) : ∃ c : R, 0 < c ∧
    ∀ m n : Int, c * ((supNorm m n : Nat) : R) ≤ cabs (lin p.z m n) := by
  have hy := p.pos
  have hD : 0 < 4 * (p.z.re * p.z.re + p.z.im * p.z.im + 1) := by
    have := sq_nonneg' p.z.re; have := sq_nonneg' p.z.im; grind
  have hyy : 0 < p.z.im * p.z.im := OrderedRing.mul_pos hy hy
  let D := 4 * (p.z.re * p.z.re + p.z.im * p.z.im + 1)
  let c2 := p.z.im * p.z.im / D
  have hc2 : 0 < c2 := OF.div_pos hyy hD
  obtain ⟨hc0, hcc⟩ := R.sqrt_spec (Std.le_of_lt hc2)
  have hcpos : 0 < R.sqrt c2 := by
    rcases (by grind : R.sqrt c2 = 0 ∨ 0 < R.sqrt c2) with h | h
    · rw [h] at hcc; grind
    · exact h
  refine ⟨R.sqrt c2, hcpos, fun m n => ?_⟩
  · apply R.le_of_mul_self_le (cabs_nonneg _)
    rw [cabs_mul_self]
    have k := normSq_lin_ge p.z m n
    have ks := supNorm_sq_le m n
    generalize ((supNorm m n : Nat) : R) = s at *
    have hs : 0 ≤ s * s := sq_nonneg' s
    -- `c2 · s² ≤ y²(m² + n²)/D ≤ |mτ + n|²`.
    have e : R.sqrt c2 * s * (R.sqrt c2 * s) = c2 * (s * s) := by rw [← hcc]; grind
    rw [e]
    have hDinv := inv_pos' hD
    have k' := OrderedRing.mul_le_mul_of_nonneg_left ks (Std.le_of_lt hyy)
    have k'' := OrderedRing.mul_le_mul_of_nonneg_right (Std.le_trans k' k) (Std.le_of_lt hDinv)
    have : D * D⁻¹ = 1 := by grind
    have e2 : c2 * (s * s) = p.z.im * p.z.im * (s * s) * D⁻¹ := by
      show p.z.im * p.z.im * D⁻¹ * (s * s) = _; grind
    rw [e2]
    have e3 : D * normSq (lin p.z m n) * D⁻¹ = normSq (lin p.z m n) := by grind
    exact Std.le_trans k'' (by rw [e3]; grind)

/-! ## The terms of the Eisenstein series -/

/-- `|w⁻¹| = |w|⁻¹`. -/
theorem cabs_inv (w : C) : cabs w⁻¹ = (cabs w)⁻¹ := by
  by_cases hw : w = 0
  · rw [hw, C.inv_zero, cabs_zero]; grind
  · have h1 := cabs_mul w w⁻¹
    rw [C.mul_inv_cancel hw, show cabs 1 = 1 from cabs_ofReal (x := 1) (by grind)] at h1
    have := cabs_pos hw
    grind

/-- **The Eisenstein term** `(mτ + n)^{−k}` (for `k ≥ 1` it is `0` at `(m, n) = (0, 0)`). -/
noncomputable def eterm (k : Nat) (z : C) (m n : Int) : C := ((lin z m n) ^ k)⁻¹

/-- `|(mτ + n)^{−k}| = |mτ + n|^{−k}`. -/
theorem cabs_eterm (k : Nat) (z : C) (m n : Int) :
    cabs (eterm k z m n) = (cabs (lin z m n) ^ k)⁻¹ := by
  rw [eterm, cabs_inv, cabs_pow]

/-- **Term bound.** For `k ≥ 3` and the constant `C` of `lattice_estimate`,
`|mτ + n|^{−k} · max(|m|, |n|)³ ≤ C^{−k}` for all `(m, n)`. -/
theorem cabs_eterm_mul_le {k : Nat} (hk : 3 ≤ k) (p : UHP) {c : R} (hc : 0 < c)
    (hest : ∀ m n : Int, c * ((supNorm m n : Nat) : R) ≤ cabs (lin p.z m n)) (m n : Int) :
    cabs (eterm k p.z m n) * ((supNorm m n : Nat) : R) ^ 3 ≤ (c ^ k)⁻¹ := by
  rw [cabs_eterm]
  have hck : 0 < c ^ k := rpow_pos hc k
  by_cases h0 : supNorm m n = 0
  · rw [h0, show ((0 : Nat) : R) ^ 3 = 0 by grind]
    have := inv_pos' hck; grind
  · have hs : (1 : R) ≤ ((supNorm m n : Nat) : R) := by
      have : 1 ≤ supNorm m n := by omega
      have := OrderedRing.natCast_le_natCast_of_le (R := R) 1 _ this; grind
    have hpos : 0 < cabs (lin p.z m n) := by
      have := hest m n
      have := OrderedRing.mul_pos hc (by grind : (0 : R) < ((supNorm m n : Nat) : R)); grind
    apply inv_mul_le_inv (rpow_pos hpos k) hck
    generalize hS : ((supNorm m n : Nat) : R) = s at *
    -- `c^k s³ ≤ c^k s^k = (cs)^k ≤ |mτ + n|^k`.
    have h1 : s ^ 3 ≤ s ^ k := by
      have := pow_le_pow_add hs 3 (k - 3); rwa [show 3 + (k - 3) = k by omega] at this
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left h1 (Std.le_of_lt hck)
    have h3 : c ^ k * s ^ k = (c * s) ^ k := (rmul_pow c s k).symm
    have h4 := R.pow_le_pow_left (Std.le_of_lt (OrderedRing.mul_pos hc (by grind)))
      (hS ▸ hest m n) k
    grind

/-! ## Counting lattice points on squares -/

/-- `Σ_{Q_0} g = g(0, 0)`. -/
theorem sq_zero {α : Type} [Field α] (g : Int → Int → α) : sq 0 g = g 0 0 := by
  show (0 : α) + ((0 : α) + g (-((0 : Nat) : Int) + ((0 : Nat) : Int))
    (-((0 : Nat) : Int) + ((0 : Nat) : Int))) = g 0 0
  rw [show -((0 : Nat) : Int) + ((0 : Nat) : Int) = 0 by omega]; grind

/-- `x³ = x · x · x` in ℝ. -/
theorem pow_three (x : R) : x ^ 3 = x * x * x := by show 1 * x * x * x = _; grind

/-- Adding the shell `Q_{N+1} ∖ Q_N` to a square sum. -/
theorem sq_succ_sub {α : Type} [Field α] (N : Nat) (a : Int → Int → α) :
    sq (N + 1) a - sq N a = sq (N + 1) (fun m n => a m n - if InSq N m n then a m n else 0) := by
  rw [sq_sub, sq_restrict (by omega)]

/-- A square sum of zeros vanishes. -/
theorem sq_zero_fun {α : Type} [Field α] (N : Nat) : sq N (fun _ _ => (0 : α)) = 0 := by
  show isum _ _ (fun _ => isum _ _ (fun _ => (0 : α))) = 0
  simp only [isum_zero]

/-- Real square sums of non-negative terms grow with the square. -/
theorem sq_mono {a : Int → Int → R} (ha : ∀ m n, 0 ≤ a m n) (N : Nat) : sq N a ≤ sq (N + 1) a := by
  have e := sq_succ_sub N a
  have : 0 ≤ sq (N + 1) (fun m n => a m n - if InSq N m n then a m n else 0) := by
    refine Std.le_trans (Std.le_of_eq (sq_zero_fun (N + 1)).symm) ?_
    apply sq_le; intro m n _ _ _ _
    by_cases h : InSq N m n
    · rw [ite_t h]; grind
    · rw [ite_f h]; have := ha m n; grind
  grind

/-- **The shell estimate.** If `|g(m, n)| · max(|m|, |n|)³ ≤ B` everywhere, then the shell
`Q_{N+1} ∖ Q_N` (which has `8(N + 1)` points) contributes at most
`8B/(N + 1)² ≤ 16B (1/(N + 1) − 1/(N + 2))`. -/
theorem shell_step (g : Int → Int → C) {B : R}
    (hB : ∀ m n, cabs (g m n) * ((supNorm m n : Nat) : R) ^ 3 ≤ B) (N : Nat) :
    sq (N + 1) (fun m n => cabs (g m n)) ≤
      sq N (fun m n => cabs (g m n)) + 16 * B * (((N : R) + 1)⁻¹ - ((N : R) + 2)⁻¹) := by
  have hB0 : 0 ≤ B := by
    have := hB 0 0
    rw [show supNorm 0 0 = 0 from rfl, pow_three] at this
    have := cabs_nonneg (g 0 0); grind
  have hu : (0 : R) < (N : R) + 1 := by have : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg; grind
  have hu1 : (1 : R) ≤ (N : R) + 1 := by have : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg; grind
  generalize hU : (N : R) + 1 = u at hu hu1
  have huuu : 0 < u * u * u := OrderedRing.mul_pos (OrderedRing.mul_pos hu hu) hu
  let c := B * (u * u * u)⁻¹
  have key : sq (N + 1) (fun m n => cabs (g m n) - if InSq N m n then cabs (g m n) else 0) ≤
      sq (N + 1) (fun m n => c * ((1 : R) - if InSq N m n then 1 else 0)) := by
    apply sq_le; intro m n h1 h2 h3 h4
    by_cases h : InSq N m n
    · rw [ite_t h, ite_t h]; grind
    · rw [ite_f h, ite_f h]
      have hs : supNorm m n = N + 1 := by unfold supNorm; unfold InSq at h; omega
      have k := hB m n
      rw [hs, pow_three, show ((N + 1 : Nat) : R) = u by rw [← hU]; grind] at k
      have hinv := inv_pos' huuu
      have := OrderedRing.mul_le_mul_of_nonneg_right k (Std.le_of_lt hinv)
      have e : u * u * u * (u * u * u)⁻¹ = 1 := by grind
      have e' : cabs (g m n) * (u * u * u) * (u * u * u)⁻¹ = cabs (g m n) := by
        rw [Semiring.mul_assoc, e, Semiring.mul_one]
      show cabs (g m n) - 0 ≤ B * (u * u * u)⁻¹ * (1 - 0)
      grind
  rw [sq_mul_left, sq_sub, sq_restrict (by omega),
    sq_sub (N + 1) (fun _ _ => (1 : R)) (fun m n => if InSq N m n then 1 else 0),
    sq_restrict (by omega) (fun _ _ => (1 : R)), sq_one, sq_one] at key
  have c1 : ((2 * (N + 1) + 1 : Nat) : R) = 2 * u + 1 := by rw [← hU]; grind
  have c2 : ((2 * N + 1 : Nat) : R) = 2 * u - 1 := by rw [← hU]; grind
  rw [c1, c2] at key
  rw [show (N : R) + 2 = u + 1 by rw [← hU]; grind]
  -- the arithmetic: `c · 8u = 8B/u² ≤ 16B/(u(u+1))`.
  have hv : 0 < u⁻¹ := inv_pos' hu
  have hw : 0 < (u + 1)⁻¹ := inv_pos' (by grind)
  have ev : u * u⁻¹ = 1 := by grind
  have ew : (u + 1) * (u + 1)⁻¹ = 1 := by grind
  have et : u * u * u * (u * u * u)⁻¹ = 1 := by grind
  have p1 : 0 ≤ u⁻¹ * (u + 1)⁻¹ * (u - 1) :=
    OrderedRing.mul_nonneg (Std.le_of_lt (OrderedRing.mul_pos hv hw)) (by grind)
  have p2 : 0 ≤ B * u⁻¹ * (2 * (u + 1)⁻¹ - u⁻¹) :=
    OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hB0 (Std.le_of_lt hv)) (by
      have : u⁻¹ * (u + 1)⁻¹ * (u - 1) = 2 * (u + 1)⁻¹ - u⁻¹ := by grind
      grind)
  have e2 : c * ((2 * u + 1) * (2 * u + 1) - (2 * u - 1) * (2 * u - 1)) = 8 * B * (u⁻¹ * u⁻¹) := by
    show B * (u * u * u)⁻¹ * _ = _; grind
  have e3 : u⁻¹ - (u + 1)⁻¹ = u⁻¹ * (u + 1)⁻¹ := by grind
  rw [e2] at key; rw [e3]
  have e4 : B * u⁻¹ * (2 * (u + 1)⁻¹ - u⁻¹) = 2 * (B * (u⁻¹ * (u + 1)⁻¹)) - B * (u⁻¹ * u⁻¹) := by
    grind
  rw [e4] at p2
  generalize B * (u⁻¹ * (u + 1)⁻¹) = X at *
  generalize B * (u⁻¹ * u⁻¹) = Y at *
  grind

/-- **Absolute convergence along squares.** If `|g(m, n)| · max(|m|, |n|)³ ≤ B` everywhere, then
`Σ_{Q_N} |g| ≤ |g(0, 0)| + 16 B` for every `N` (by `Σ_{N ≥ 1} 1/N² ≤ 2`, telescoped). -/
theorem sq_cabs_le (g : Int → Int → C) {B : R}
    (hB : ∀ m n, cabs (g m n) * ((supNorm m n : Nat) : R) ^ 3 ≤ B) (N : Nat) :
    sq N (fun m n => cabs (g m n)) ≤ cabs (g 0 0) + 16 * B := by
  have hB0 : 0 ≤ B := by
    have := hB 0 0
    rw [show supNorm 0 0 = 0 from rfl, pow_three] at this
    have := cabs_nonneg (g 0 0); grind
  have aux : ∀ N : Nat, sq N (fun m n => cabs (g m n)) ≤
      cabs (g 0 0) + 16 * B * (1 - ((N : R) + 1)⁻¹) := by
    intro N
    induction N with
    | zero =>
      rw [sq_zero]
      have : ((0 : Nat) : R) + 1 = 1 := by grind
      rw [this, show (1 : R)⁻¹ = 1 by grind]; grind
    | succ N ih =>
      have := shell_step g hB N
      rw [show ((N + 1 : Nat) : R) + 1 = (N : R) + 2 by grind]
      grind
  have := aux N
  have : 0 ≤ ((N : R) + 1)⁻¹ := Std.le_of_lt (inv_pos' (by
    have : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg; grind))
  have := OrderedRing.mul_nonneg (by grind : (0 : R) ≤ 16 * B) this
  grind

/-! ## Absolute convergence of the Eisenstein double series -/

/-- **The partial sums of `Σ' |mτ + n|^{−k}` over squares are bounded**, for `k ≥ 3`. -/
theorem abs_lattice_sum_bounded {k : Nat} (hk : 3 ≤ k) (p : UHP) :
    ∃ K : R, ∀ N, sq N (fun m n => cabs (eterm k p.z m n)) ≤ K := by
  obtain ⟨c, hc, hest⟩ := lattice_estimate p
  exact ⟨_, sq_cabs_le _ (cabs_eterm_mul_le hk p hc hest)⟩

/-- **Absolute convergence.** For `k ≥ 3` and `τ ∈ ℍ`, the double series `Σ' |mτ + n|^{−k}`
converges along the squares `Q_N`. -/
theorem abs_lattice_sum_converges {k : Nat} (hk : 3 ≤ k) (p : UHP) :
    ∃ L : R, R.Tendsto (fun N => sq N (fun m n => cabs (eterm k p.z m n))) L :=
  R.monotone_convergence (sq_mono (fun _ _ => cabs_nonneg _)) (abs_lattice_sum_bounded hk p)

end Lattice

end Foundations.Langlands.Modular
