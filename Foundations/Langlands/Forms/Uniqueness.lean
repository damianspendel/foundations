import Foundations.Langlands.Forms.Reduction

/-!
# Uniqueness of the reduced form

Gauss's normalisation is chosen so that reduction is not only possible but **canonical**:
two different reduced forms of negative discriminant are never properly equivalent
(*Disquisitiones*, art. 172; in the modern form due to Dirichlet and Dedekind). On the
automorphic side this is the statement that the closed fundamental domain `F`, with its
boundary identified correctly, meets each orbit exactly once; the library file
`FundamentalDomainUnique` proves the interior case of that statement (`eq_of_interior`). Here
the **full** arithmetic statement is proved, boundary cases included, without the root map.

## The argument

For a reduced form `f = (a, b, c)` the smallest values are visible from the coefficients
(`le_eval`, `eval_ge_of_ne`):

* `f(x, 0) = ax² ≥ a` and `f(0, y) = cy² ≥ c ≥ a`;
* if `x, y ≠ 0` then `f(x, y) ≥ a − |b| + c ≥ c` (`core_bound`: for `x ≥ y ≥ 1` the difference
  is `(x − y)(ax + (a − |b|)y) + (a − |b| + c)(y² − 1) + (b + |b|)xy ≥ 0`).

So `a` is the minimum of `f` on `ℤ² ∖ {0}`. If `g = f·γ` with `γ = (p q; r s)`, then
`g.a = f(p, r)`; comparing minima in both directions gives `g.a = f.a`. Now two cases:

* `r = 0`: then `γ = ±(1 q; 0 1)` and `g.b = f.b ± 2aq`. Both middle coefficients lie in the
  window `−a < b ≤ a`, forcing `q = 0`, so `g = f`.
* `r ≠ 0`: the minimum `a` is attained at a point with non-zero second coordinate, which by the
  bounds above forces `c = a` (`c_eq_a_of_eval`); by symmetry also `g.c = g.a`. Then the
  discriminant gives `f.b² = g.b²`, and the boundary convention `b ≥ 0` when `a = c` gives
  `f.b = g.b`.
-/

namespace Foundations.Langlands.Forms

open Foundations.Algebra Foundations.Langlands.Modular

namespace Form

/-- The core estimate. If `|b| ≤ a`, `|b| ≤ c` and `x, y ≥ 1`, then
`ax² + bxy + cy² ≥ a − |b| + c`. -/
theorem core_bound {a b c x y : Int} (h1 : (b.natAbs : Int) ≤ a) (h2 : (b.natAbs : Int) ≤ c)
    (hx : 1 ≤ x) (hy : 1 ≤ y) : a - b.natAbs + c ≤ a * x * x + b * x * y + c * y * y := by
  generalize hB : (b.natAbs : Int) = B at h1 h2 ⊢
  have hbB : 0 ≤ b + B := by omega
  have hxy : 0 ≤ (b + B) * (x * y) := Int.mul_nonneg hbB (Int.mul_nonneg (by omega) (by omega))
  rcases Int.le_total y x with hle | hle
  · have t1 : 0 ≤ (x - y) * (a * x + (a - B) * y) :=
      Int.mul_nonneg (by omega) (Int.add_nonneg (Int.mul_nonneg (by omega) (by omega))
        (Int.mul_nonneg (by omega) (by omega)))
    have t2 : 0 ≤ (a - B + c) * (y * y - 1) :=
      Int.mul_nonneg (by omega) (by have := Int.mul_le_mul hy hy (by omega) (by omega); omega)
    have e : a * x * x + b * x * y + c * y * y = (a - B + c) + (x - y) * (a * x + (a - B) * y) +
        (a - B + c) * (y * y - 1) + (b + B) * (x * y) := by grind
    omega
  · have t1 : 0 ≤ (y - x) * (c * y + (c - B) * x) :=
      Int.mul_nonneg (by omega) (Int.add_nonneg (Int.mul_nonneg (by omega) (by omega))
        (Int.mul_nonneg (by omega) (by omega)))
    have t2 : 0 ≤ (a - B + c) * (x * x - 1) :=
      Int.mul_nonneg (by omega) (by have := Int.mul_le_mul hx hx (by omega) (by omega); omega)
    have e : a * x * x + b * x * y + c * y * y = (a - B + c) + (y - x) * (c * y + (c - B) * x) +
        (a - B + c) * (x * x - 1) + (b + B) * (x * y) := by grind
    omega

/-- **Lower bound off the axes.** For a reduced form and `x, y ≠ 0`,
`f(x, y) ≥ a − |b| + c`. -/
theorem eval_ge_of_ne {f : Form} (hf : f.IsReduced) {x y : Int} (hx : x ≠ 0) (hy : y ≠ 0) :
    f.a - f.b.natAbs + f.c ≤ f.eval x y := by
  have h1 : (f.b.natAbs : Int) ≤ f.a := hf.1
  have h2 : (f.b.natAbs : Int) ≤ f.c := by have := hf.2.1; omega
  unfold eval
  rcases Int.le_total 0 x with hx0 | hx0 <;> rcases Int.le_total 0 y with hy0 | hy0
  · exact core_bound h1 h2 (by omega) (by omega)
  · have := core_bound (b := -f.b) (x := x) (y := -y) (by simpa using h1) (by simpa using h2)
      (by omega) (by omega)
    simp only [Int.natAbs_neg] at this
    have e : f.a * x * x + -f.b * x * -y + f.c * -y * -y = f.a * x * x + f.b * x * y +
      f.c * y * y := by grind
    omega
  · have := core_bound (b := -f.b) (x := -x) (y := y) (by simpa using h1) (by simpa using h2)
      (by omega) (by omega)
    simp only [Int.natAbs_neg] at this
    have e : f.a * -x * -x + -f.b * -x * y + f.c * y * y = f.a * x * x + f.b * x * y +
      f.c * y * y := by grind
    omega
  · have := core_bound (b := f.b) (x := -x) (y := -y) h1 h2 (by omega) (by omega)
    have e : f.a * -x * -x + f.b * -x * -y + f.c * -y * -y = f.a * x * x + f.b * x * y +
      f.c * y * y := by grind
    omega

/-- For `y ≠ 0`, `y² ≥ 1`. -/
theorem one_le_sq {y : Int} (hy : y ≠ 0) : 1 ≤ y * y := by
  rw [← Int.natAbs_mul_self]
  have : 1 ≤ y.natAbs := by omega
  have := Nat.mul_le_mul this this
  omega

/-- If `0 ≤ c` and `y ≠ 0` then `c ≤ c y²`. -/
theorem le_mul_sq {c y : Int} (hc : 0 ≤ c) (hy : y ≠ 0) : c ≤ c * y * y := by
  have := Int.mul_le_mul_of_nonneg_left (one_le_sq hy) hc
  rw [Int.mul_assoc]; omega

/-- **The leading coefficient is the minimum.** A reduced form satisfies `f(x, y) ≥ a` for
every `(x, y) ≠ (0, 0)`. -/
theorem le_eval {f : Form} (hf : f.IsReduced) {x y : Int} (h : x ≠ 0 ∨ y ≠ 0) :
    f.a ≤ f.eval x y := by
  have h1 : (f.b.natAbs : Int) ≤ f.a := hf.1
  have h2 := hf.2.1
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by omega
    have := le_mul_sq (c := f.c) (by omega) hy
    simp only [eval, hx]; simp; omega
  · by_cases hy : y = 0
    · have := le_mul_sq (c := f.a) (by omega) hx
      simp only [eval, hy]; simp; omega
    · have := eval_ge_of_ne hf hx hy; omega

/-- **Where the minimum is attained.** If a reduced form takes the value `a` at a point with
`y ≠ 0`, then `c = a`. -/
theorem c_eq_a_of_eval {f : Form} (hf : f.IsReduced) {x y : Int} (hy : y ≠ 0)
    (h : f.eval x y = f.a) : f.c = f.a := by
  have h1 : (f.b.natAbs : Int) ≤ f.a := hf.1
  have h2 := hf.2.1
  by_cases hx : x = 0
  · have := le_mul_sq (c := f.c) (by omega) hy
    simp only [eval, hx] at h; simp at h; omega
  · have := eval_ge_of_ne hf hx hy; omega

/-- The first column of a matrix in SL₂(ℤ) is never `(0, 0)`. -/
theorem first_col_ne_zero (g : SL2Z) : g.a ≠ 0 ∨ g.c ≠ 0 := by
  apply Classical.byContradiction; intro h
  have ha : g.a = 0 := Classical.byContradiction fun ha => h (Or.inl ha)
  have hc : g.c = 0 := Classical.byContradiction fun hc => h (Or.inr hc)
  have := g.det; rw [ha, hc] at this; simp at this

/-- Equivalent reduced forms have the same leading coefficient (the minimum of the form). -/
theorem a_eq_of_equiv {f g : Form} (hf : f.IsReduced) (hg : g.IsReduced) (γ : SL2Z)
    (h : f.act γ = g) : f.a = g.a := by
  have e1 : g.a = f.eval γ.a γ.c := by rw [← h, act_a]
  have e2 : f.a = g.eval γ⁻¹.a γ⁻¹.c := by rw [← act_a, ← h, act_act_inv]
  have l1 := le_eval hf (first_col_ne_zero γ)
  have l2 := le_eval hg (first_col_ne_zero γ⁻¹)
  omega

/-- If `0 < a` and `−2a < 2at < 2a` then `t = 0`. -/
theorem eq_zero_of_window {a t : Int} (ha : 0 < a) (h1 : -(2 * a) < 2 * a * t)
    (h2 : 2 * a * t < 2 * a) : t = 0 := by
  have e : 2 * a * t = 2 * (a * t) := by grind
  rcases Int.lt_trichotomy t 0 with ht | ht | ht
  · have := Int.mul_le_mul_of_nonneg_left (by omega : t ≤ -1) (by omega : 0 ≤ a); omega
  · exact ht
  · have := Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ t) (by omega : 0 ≤ a); omega

/-- Two non-negative integers with the same square are equal. -/
theorem eq_of_sq_eq {b b' : Int} (h0 : 0 ≤ b) (h0' : 0 ≤ b') (h : b * b = b' * b') : b = b' := by
  rw [← Int.natAbs_mul_self, ← Int.natAbs_mul_self] at h
  have := Nat.mul_self_inj.1 (Int.ofNat.inj h)
  omega

/-- **Uniqueness of the reduced form.** Two reduced forms of negative discriminant that are
properly equivalent are equal. -/
theorem reduced_unique {f g : Form} (hf : f.IsReduced) (hg : g.IsReduced) (hD : f.disc < 0)
    (h : Equiv f g) : f = g := by
  obtain ⟨γ, hγ⟩ := h
  have ha := a_eq_of_equiv hf hg γ hγ
  have hpos : 0 < f.a := (hf.posDef hD).2
  have hdisc : g.disc = f.disc := by rw [← hγ, disc_act]
  unfold disc at hdisc
  have hfb := hf.1
  have hgb := hg.1
  have hfr := hf.2.2
  have hgr := hg.2.2
  by_cases hc : γ.c = 0
  · have hdet := γ.det
    rw [hc, Int.mul_zero, Int.sub_zero] at hdet
    have hb : g.b = f.b + 2 * f.a * (γ.a * γ.b) := by
      rw [← hγ]; simp only [act, hc, hdet]; grind
    have hw : γ.a * γ.b = 0 := eq_zero_of_window hpos (by omega) (by omega)
    have hbb : g.b = f.b := by rw [hb, hw]; simp
    have hcc : f.c = g.c := by
      rw [hbb, ← ha] at hdisc
      have : 4 * f.a * g.c = 4 * f.a * f.c := by omega
      exact (Int.eq_of_mul_eq_mul_left (by omega) this).symm
    exact ext ha hbb.symm hcc
  · have e1 : f.eval γ.a γ.c = f.a := by rw [← act_a, hγ, ← ha]
    have e2 : g.eval γ⁻¹.a γ⁻¹.c = g.a := by
      rw [← act_a, ← ha, ← hγ, act_act_inv]
    have hfc := c_eq_a_of_eval hf hc e1
    have hgc := c_eq_a_of_eval hg (by simp; exact hc) e2
    have hbf : 0 ≤ f.b := hfr (Or.inr hfc.symm)
    have hbg : 0 ≤ g.b := hgr (Or.inr hgc.symm)
    have hbb : f.b = g.b := by
      apply eq_of_sq_eq hbf hbg
      rw [hgc, hfc, ← ha] at hdisc
      omega
    exact ext ha hbb (by omega)

/-- **Each positive definite class contains exactly one reduced form.** -/
theorem existsUnique_reduced (f : Form) (hf : f.PosDef) :
    ∃ g : Form, Equiv f g ∧ g.IsReduced ∧
      ∀ g' : Form, Equiv f g' → g'.IsReduced → g' = g := by
  obtain ⟨g, eg, hg⟩ := exists_reduced f hf
  refine ⟨g, eg, hg, fun g' eg' hg' => ?_⟩
  have hD : g'.disc < 0 := by rw [← eg'.disc_eq]; exact hf.1
  exact reduced_unique hg' hg hD (eg'.symm.trans eg)

end Form

end Foundations.Langlands.Forms
