import Foundations.Topology.PicardLindelof

/-!
# The Weierstrass approximation theorem

**Every continuous function on `[a, b]` is a uniform limit of polynomials** (Weierstrass, 1885):
in the metric space `C[a, b]` the polynomials are dense. The most elegant proof is Sergei
**Bernstein**'s (1912), originally probabilistic: if a coin with probability `x` of heads is tossed
`n` times and `k` heads appear, then `k/n` is close to `x` with high probability (the law of large
numbers), hence `f(k/n)` is close to `f(x)` on average. The average is the **Bernstein polynomial**

  `Bₙf(x) = Σ_{k=0}^{n} f(k/n) · C(n, k) xᵏ (1 − x)ⁿ⁻ᵏ`.

The "law of large numbers" needed is the exact variance identity

  `Σₖ (k/n − x)² C(n, k) xᵏ (1 − x)ⁿ⁻ᵏ = x(1 − x)/n`,

which we derive from the binomial theorem (in the form `Σ xᵏ/k! · yⁿ⁻ᵏ/(n−k)! = (x + y)ⁿ/n!`,
already proved for the exponential series). Combined with uniform continuity of `f` the estimate
`|f(k/n) − f(x)| ≤ ε/2 + 2M (k/n − x)²/δ²` gives `|Bₙf(x) − f(x)| ≤ ε/2 + 2M/(δ² n)`.

Polynomial functions are those generated from constants and the identity by `+` and `×`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

/-! ## Polynomial functions -/

/-- The **polynomial functions** `ℝ → ℝ`: generated from the constants and `x ↦ x` by sums and
products. -/
inductive IsPolyFn : (R → R) → Prop
  /-- Constants are polynomials. -/
  | const (c : R) : IsPolyFn (fun _ => c)
  /-- The identity is a polynomial. -/
  | id : IsPolyFn (fun x => x)
  /-- Sums of polynomials are polynomials. -/
  | add {p q : R → R} : IsPolyFn p → IsPolyFn q → IsPolyFn (fun x => p x + q x)
  /-- Products of polynomials are polynomials. -/
  | mul {p q : R → R} : IsPolyFn p → IsPolyFn q → IsPolyFn (fun x => p x * q x)

namespace IsPolyFn

/-- Being a polynomial depends only on the values. -/
theorem congr {p q : R → R} (hp : IsPolyFn p) (h : ∀ x, p x = q x) : IsPolyFn q := by
  have : p = q := funext h
  exact this ▸ hp

/-- Composition of polynomials is a polynomial. -/
theorem comp {p q : R → R} (hp : IsPolyFn p) (hq : IsPolyFn q) : IsPolyFn (fun x => p (q x)) := by
  induction hp with
  | const c => exact const c
  | id => exact hq
  | add _ _ ih1 ih2 => exact add ih1 ih2
  | mul _ _ ih1 ih2 => exact mul ih1 ih2

/-- Powers `x ↦ xⁿ` are polynomials. -/
theorem pow (n : Nat) : IsPolyFn (fun x => x ^ n) := by
  induction n with
  | zero => exact const 1
  | succ n ih => exact mul ih id

/-- Finite sums of polynomials are polynomials. -/
theorem fsum {p : Nat → R → R} (h : ∀ k, IsPolyFn (p k)) (n : Nat) :
    IsPolyFn (fun x => R.fsum (fun k => p k x) n) := by
  induction n with
  | zero => exact const 0
  | succ n ih => exact add ih (h n)

/-- The exponential terms `x ↦ xⁿ/n!` are polynomials. -/
theorem expTerm (n : Nat) : IsPolyFn (fun x => R.expTerm x n) :=
  (mul (pow n) (const ((fact n : R))⁻¹)).congr fun x => by
    unfold R.expTerm; rw [Field.div_eq_mul_inv]

end IsPolyFn

/-! ## Bernstein polynomials -/

/-- The Bernstein basis polynomial `C(n, k) xᵏ (1 − x)ⁿ⁻ᵏ`, written as
`n! · xᵏ/k! · (1 − x)ⁿ⁻ᵏ/(n − k)!`. -/
noncomputable def bern (n k : Nat) (x : R) : R := (fact n : R) * (expTerm x k * expTerm (1 - x) (n - k))

/-- Bernstein basis polynomials are polynomials. -/
theorem isPolyFn_bern (n k : Nat) : IsPolyFn (bern n k) :=
  IsPolyFn.mul (IsPolyFn.const _) (IsPolyFn.mul (IsPolyFn.expTerm k)
    ((IsPolyFn.expTerm (n - k)).comp ((IsPolyFn.add (IsPolyFn.const 1)
      (IsPolyFn.mul (IsPolyFn.const (-1)) IsPolyFn.id)).congr fun x => by grind)))

/-- On `[0, 1]` the basis polynomials are non-negative. -/
theorem bern_nonneg {x : R} (h0 : 0 ≤ x) (h1 : x ≤ 1) (n k : Nat) : 0 ≤ bern n k x :=
  OrderedRing.mul_nonneg (Std.le_of_lt (fact_pos' n))
    (OrderedRing.mul_nonneg (expTerm_nonneg h0 k) (expTerm_nonneg (by grind) _))

/-- `n + 1 ≠ 0` in `R`. -/
theorem natCast_succ_ne (n : Nat) : (n : R) + 1 ≠ 0 := by
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg; grind

/-- **Binomial theorem** (exponential form): `Σ_{k ≤ n} xᵏ/k! · yⁿ⁻ᵏ/(n−k)! = (x + y)ⁿ/n!`. -/
theorem binom_sum (x y : R) (n : Nat) :
    R.fsum (fun k => expTerm x k * expTerm y (n - k)) (n + 1) = expTerm (x + y) n := by
  rw [← gsum_eq_fsum]
  exact gsum_binomial (α := R) expTerm expTerm_zero expTerm_rec natCast_succ_ne x y n

/-- First moment, exponential form. -/
theorem moment1 (x y : R) (m : Nat) :
    R.fsum (fun k => (k : R) * (expTerm x k * expTerm y (m + 1 - k))) (m + 2) =
      x * expTerm (x + y) m := by
  rw [fsum_succ', ← binom_sum, ← fsum_const_mul]
  rw [show ((0 : Nat) : R) * (expTerm x 0 * expTerm y (m + 1 - 0)) = 0 by grind]
  rw [show ∀ t : R, (0 : R) + t = t from fun t => by grind]
  apply fsum_congr; intro j _
  have := expTerm_rec x j
  rw [show m + 1 - (j + 1) = m - j by omega]
  have : ((j + 1 : Nat) : R) = (j : R) + 1 := by grind
  grind

/-- Second factorial moment, exponential form. -/
theorem moment2 (x y : R) (m : Nat) :
    R.fsum (fun k => (k : R) * ((k : R) - 1) * (expTerm x k * expTerm y (m + 2 - k))) (m + 3) =
      x * x * expTerm (x + y) m := by
  rw [fsum_succ', fsum_succ', ← binom_sum, ← fsum_const_mul]
  rw [show ((0 : Nat) : R) * (((0 : Nat) : R) - 1) * (expTerm x 0 * expTerm y (m + 2 - 0)) = 0 by
    grind]
  rw [show ((0 + 1 : Nat) : R) * (((0 + 1 : Nat) : R) - 1) *
    (expTerm x (0 + 1) * expTerm y (m + 2 - (0 + 1))) = 0 by grind]
  rw [show ∀ t : R, (0 : R) + t = t from fun t => by grind,
    show ∀ t : R, (0 : R) + t = t from fun t => by grind]
  apply fsum_congr; intro j _
  have h1 := expTerm_rec x j
  have h2 := expTerm_rec x (j + 1)
  rw [show m + 2 - (j + 1 + 1) = m - j by omega]
  have : ((j + 1 + 1 : Nat) : R) = (j : R) + 2 := by grind
  have : ((j + 1 : Nat) : R) = (j : R) + 1 := by grind
  grind

/-- `Σ_k C(n, k) xᵏ (1 − x)ⁿ⁻ᵏ = 1`. -/
theorem sum_bern (n : Nat) (x : R) : R.fsum (fun k => bern n k x) (n + 1) = 1 := by
  unfold bern
  rw [fsum_const_mul, binom_sum, show x + (1 - x) = 1 by grind, expTerm_one]
  have := fact_pos' n; grind

/-- `Σ_k k · C(n, k) xᵏ (1 − x)ⁿ⁻ᵏ = n x` (here `n = m + 2`). -/
theorem sum_k_bern (m : Nat) (x : R) :
    R.fsum (fun k => (k : R) * bern (m + 2) k x) (m + 3) = ((m + 2 : Nat) : R) * x := by
  unfold bern
  have e : R.fsum (fun k => (k : R) * ((fact (m + 2) : R) * (expTerm x k * expTerm (1 - x) (m + 2 - k))))
      (m + 3) = (fact (m + 2) : R) *
        R.fsum (fun k => (k : R) * (expTerm x k * expTerm (1 - x) (m + 1 + 1 - k))) (m + 1 + 2) := by
    rw [← fsum_const_mul]; apply fsum_congr; intro k _; grind
  rw [e, moment1, show x + (1 - x) = 1 by grind, expTerm_one, fact_succ', fact_succ']
  have hm0 : (0 : R) ≤ (m : R) := OrderedRing.natCast_nonneg
  have hpos := OrderedRing.mul_pos (show (0 : R) < (m : R) + 1 by grind) (fact_pos' m)
  grind

/-- `Σ_k k(k − 1) · C(n, k) xᵏ (1 − x)ⁿ⁻ᵏ = n(n − 1) x²` (here `n = m + 2`). -/
theorem sum_kk_bern (m : Nat) (x : R) :
    R.fsum (fun k => (k : R) * ((k : R) - 1) * bern (m + 2) k x) (m + 3) =
      ((m + 2 : Nat) : R) * (((m + 2 : Nat) : R) - 1) * (x * x) := by
  unfold bern
  have e : R.fsum (fun k => (k : R) * ((k : R) - 1) *
      ((fact (m + 2) : R) * (expTerm x k * expTerm (1 - x) (m + 2 - k)))) (m + 3) =
      (fact (m + 2) : R) * R.fsum (fun k => (k : R) * ((k : R) - 1) *
        (expTerm x k * expTerm (1 - x) (m + 2 - k))) (m + 3) := by
    rw [← fsum_const_mul]; apply fsum_congr; intro k _; grind
  rw [e, moment2, show x + (1 - x) = 1 by grind, expTerm_one, fact_succ', fact_succ']
  have := fact_pos' m; grind

/-- **The variance identity**: `Σ_k (k/n − x)² C(n, k) xᵏ (1 − x)ⁿ⁻ᵏ = x(1 − x)/n`. -/
theorem variance (m : Nat) (x N : R) (hN : ((m + 2 : Nat) : R) = N) :
    R.fsum (fun k => ((k : R) / N - x) * ((k : R) / N - x) *
      bern (m + 2) k x) (m + 3) = x * (1 - x) / N := by
  have hN0 : N ≠ 0 := by rw [← hN]; have := natCast_succ_ne (m + 1); grind
  have e : ∀ k : Nat, ((k : R) / N - x) * ((k : R) / N - x) * bern (m + 2) k x =
      1 / (N * N) * ((k : R) * ((k : R) - 1) * bern (m + 2) k x) +
      ((1 / (N * N) - 2 * x / N) * ((k : R) * bern (m + 2) k x) + x * x * bern (m + 2) k x) :=
    fun k => by grind
  rw [fsum_congr (fun k _ => e k), fsum_add, fsum_add, fsum_const_mul, fsum_const_mul,
    fsum_const_mul, sum_kk_bern, sum_k_bern, sum_bern, hN]
  grind

/-- Partial sums are monotone in terms with indices below the bound. -/
theorem fsum_le_fsum' {a b : Nat → R} {n : Nat} (h : ∀ k, k < n → a k ≤ b k) :
    R.fsum a n ≤ R.fsum b n := by
  induction n with
  | zero => exact Std.le_refl _
  | succ n ih => rw [fsum_succ, fsum_succ]; have := ih fun k hk => h k (by omega); have := h n (by omega); grind

/-- **Weierstrass approximation theorem on `[0, 1]`** (via Bernstein polynomials). -/
theorem weierstrass01 {f : R → R} (hf : ∀ x, 0 ≤ x → x ≤ 1 → R.ContinuousAt f x) {ε : R}
    (hε : 0 < ε) : ∃ p, IsPolyFn p ∧ ∀ x, 0 ≤ x → x ≤ 1 → abs (f x - p x) < ε := by
  obtain ⟨M, hM⟩ := bound_on (by grind : (0 : R) ≤ 1) hf
  have hM0 : 0 ≤ M := Std.le_trans (abs_nonneg _) (hM 0 (Std.le_refl _) (by grind))
  obtain ⟨δ, hδ, hδf⟩ := uniform_continuous hf (by grind : 0 < ε / 2)
  let K := M * (δ * δ)⁻¹
  have hK : 0 ≤ K := OrderedRing.mul_nonneg hM0
    (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 (OrderedRing.mul_pos hδ hδ)))
  obtain ⟨m, hm⟩ := archimedean (4 * K / ε)
  let N : R := ((m + 2 : Nat) : R)
  have hN : (m : R) + 2 = N := by show _ = ((m + 2 : Nat) : R); grind
  have hNpos : 0 < N := by have : (0 : R) ≤ (m : R) := OrderedRing.natCast_nonneg; grind
  refine ⟨fun x => R.fsum (fun k => f ((k : R) / N) * bern (m + 2) k x) (m + 3),
    IsPolyFn.fsum (fun k => IsPolyFn.mul (IsPolyFn.const _) (isPolyFn_bern _ _)) _,
    fun x hx0 hx1 => ?_⟩
  -- `f(x) − Bₙf(x) = Σ (f x − f(k/n)) bₖ(x)`.
  have hdiff : f x - R.fsum (fun k => f ((k : R) / N) * bern (m + 2) k x) (m + 3) =
      R.fsum (fun k => (f x - f ((k : R) / N)) * bern (m + 2) k x) (m + 3) := by
    have := sum_bern (m + 2) x
    have e2 : R.fsum (fun k => f x * bern (m + 2) k x) (m + 3) = f x := by
      rw [fsum_const_mul, this]; grind
    rw [show (fun k : Nat => (f x - f ((k : R) / N)) * bern (m + 2) k x) =
      fun k : Nat => f x * bern (m + 2) k x - f ((k : R) / N) * bern (m + 2) k x from
      funext fun k => by grind, fsum_sub, e2]
  rw [hdiff]
  -- Termwise: `|f x − f(k/n)| bₖ ≤ (ε/2 + 2K (k/n − x)²) bₖ`.
  have hterm : ∀ k, k < m + 3 → abs ((f x - f ((k : R) / N)) * bern (m + 2) k x) ≤
      (ε / 2 + 2 * K * (((k : R) / N - x) * ((k : R) / N - x))) * bern (m + 2) k x := by
    intro k hk
    have hb := bern_nonneg hx0 hx1 (m + 2) k
    have hu0 : 0 ≤ (k : R) / N := by
      rw [Field.div_eq_mul_inv]; exact OrderedRing.mul_nonneg OrderedRing.natCast_nonneg
        (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hNpos))
    have hu1 : (k : R) / N ≤ 1 := by
      have : (k : R) ≤ N := by
        have := OrderedRing.natCast_le_natCast_of_le (R := R) k (m + 2) (by omega); grind
      have e : (k : R) / N * N = (k : R) := by grind
      apply Classical.byContradiction; intro hc
      have := OrderedRing.mul_lt_mul_of_pos_right (by grind : (1 : R) < (k : R) / N) hNpos; grind
    rw [abs_mul, abs_of_nonneg hb]
    apply OrderedRing.mul_le_mul_of_nonneg_right _ hb
    generalize (k : R) / N = u at hu0 hu1
    have hd2 : 0 ≤ 2 * K * ((u - x) * (u - x)) :=
      OrderedRing.mul_nonneg (by grind) (C.mul_self_nonneg _)
    rcases (by grind : abs (x - u) < δ ∨ δ ≤ abs (x - u)) with h | h
    · have := hδf x u hx0 hx1 hu0 hu1 h; grind
    · have hsq : δ * δ ≤ (u - x) * (u - x) := by
        have := OrderedRing.mul_le_mul_of_nonneg_left h (Std.le_of_lt hδ)
        have := OrderedRing.mul_le_mul_of_nonneg_right h (abs_nonneg (x - u))
        have e : abs (x - u) * abs (x - u) = (u - x) * (u - x) := by
          rw [← abs_mul, abs_of_nonneg (C.mul_self_nonneg _)]; grind
        grind
      have hpos : 0 < δ * δ := OrderedRing.mul_pos hδ hδ
      have h1 : 1 ≤ (u - x) * (u - x) * (δ * δ)⁻¹ :=
        (Field.IsOrdered.le_mul_inv_iff_mul_le 1 _ hpos).2 (by grind)
      have h2 := OrderedRing.mul_le_mul_of_nonneg_left h1 (by grind : (0 : R) ≤ 2 * M)
      have h3 := OF.abs_add (f x) (-(f u))
      rw [R.abs_neg, show f x + -f u = f x - f u by grind] at h3
      have := hM x hx0 hx1; have := hM u hu0 hu1
      have e : 2 * K * ((u - x) * (u - x)) = 2 * M * ((u - x) * (u - x) * (δ * δ)⁻¹) := by grind
      grind
  have k1 := Std.le_trans (abs_fsum_le _ _) (fsum_le_fsum' hterm)
  -- Sum the bound using the moment identities.
  have e3 : R.fsum (fun k => (ε / 2 + 2 * K * (((k : R) / N - x) * ((k : R) / N - x))) *
      bern (m + 2) k x) (m + 3) = ε / 2 * R.fsum (fun k => bern (m + 2) k x) (m + 3) +
      2 * K * R.fsum (fun k => ((k : R) / N - x) * ((k : R) / N - x) * bern (m + 2) k x) (m + 3) := by
    rw [← fsum_const_mul, ← fsum_const_mul, ← fsum_add]; apply fsum_congr; intro k _; grind
  rw [e3, sum_bern, variance m x N rfl] at k1
  clear hterm hδf hM hf hdiff e3
  -- `2K x(1−x)/N ≤ 2K/N < ε/2`.
  have hx : x * (1 - x) ≤ 1 := by have := C.mul_self_nonneg x; grind
  have hx' : 0 ≤ x * (1 - x) := OrderedRing.mul_nonneg hx0 (by grind)
  have hm' : 4 * K < ε * N := by
    have := OrderedRing.mul_lt_mul_of_pos_left (by grind : 4 * K / ε < N) hε
    have e : ε * (4 * K / ε) = 4 * K := by grind
    grind
  have hfin : 2 * K * (x * (1 - x) / N) < ε / 2 := by
    have e : 2 * K * (x * (1 - x) / N) = 2 * K * (x * (1 - x)) * N⁻¹ := by grind
    rw [e]
    apply (Field.IsOrdered.mul_inv_lt_iff_lt_mul _ _ hNpos).2
    have := OrderedRing.mul_le_mul_of_nonneg_left hx (by grind : (0 : R) ≤ 2 * K)
    grind
  grind

/-- **Weierstrass approximation theorem.** Every function continuous on `[a, b]` can be
approximated uniformly on `[a, b]` by polynomials to within any `ε > 0`: the polynomials are dense
in `C[a, b]`. -/
theorem weierstrass {f : R → R} {a b : R} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → R.ContinuousAt f x) {ε : R} (hε : 0 < ε) :
    ∃ p, IsPolyFn p ∧ ∀ x, a ≤ x → x ≤ b → abs (f x - p x) < ε := by
  rcases (by grind : a = b ∨ a < b) with e | e
  · exact ⟨fun _ => f a, IsPolyFn.const _, fun x h1 h2 => by
      rw [show x = a by grind, show f a - f a = 0 by grind, R.abs_zero]; exact hε⟩
  · -- Rescale `[a, b]` to `[0, 1]`.
    let L := b - a
    have hL : 0 < L := by grind
    let g : R → R := fun t => f (a + L * t)
    have hg : ∀ t, 0 ≤ t → t ≤ 1 → R.ContinuousAt g t := fun t h1 h2 η hη => by
      have := OrderedRing.mul_le_mul_of_nonneg_left h2 (Std.le_of_lt hL)
      have := OrderedRing.mul_nonneg (Std.le_of_lt hL) h1
      obtain ⟨δ, hδ, k⟩ := hf (a + L * t) (by grind) (by grind) η hη
      refine ⟨δ / L, div_pos hδ hL, fun s hs => k _ ?_⟩
      have := abs_lt.1 hs
      have e1 : L * (δ / L) = δ := by grind
      have := OrderedRing.mul_lt_mul_of_pos_left (abs_lt.1 hs).2 hL
      have := OrderedRing.mul_lt_mul_of_pos_left (abs_lt.1 hs).1 hL
      exact abs_lt.2 ⟨by grind, by grind⟩
    obtain ⟨p, hp, hpg⟩ := weierstrass01 hg hε
    refine ⟨fun x => p ((x - a) * L⁻¹), hp.comp ((IsPolyFn.mul (IsPolyFn.add IsPolyFn.id
      (IsPolyFn.const (-a))) (IsPolyFn.const L⁻¹)).congr fun x => by grind), fun x h1 h2 => ?_⟩
    have hi := Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hL)
    have hL1 : L * L⁻¹ = 1 := Field.mul_inv_cancel (by grind)
    have t0 : 0 ≤ (x - a) * L⁻¹ := OrderedRing.mul_nonneg (by grind) hi
    have t1 : (x - a) * L⁻¹ ≤ 1 := by
      have := OrderedRing.mul_le_mul_of_nonneg_right (by grind : x - a ≤ L) hi; grind
    have := hpg _ t0 t1
    have e2 : g ((x - a) * L⁻¹) = f x := by
      show f (a + L * ((x - a) * L⁻¹)) = f x
      congr 1; grind
    rw [e2] at this; exact this

end Foundations.Topology
