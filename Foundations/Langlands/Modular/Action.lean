import Foundations.Numbers.ComplexModulus
import Foundations.Algebra.Action
import Foundations.Langlands.Modular.SL2

/-!
# SL₂(ℤ) acting on the upper half-plane

The **upper half-plane** is `ℍ = { τ ∈ ℂ : Im τ > 0 }`. A matrix `γ = (a b; c d)` of
determinant one acts on it by the **Möbius transformation**

  `γ τ = (a τ + b) / (c τ + d)`.

Poincaré's insight (1882) was that ℍ, with the metric `|dτ|² / (Im τ)²`, is a model of the
hyperbolic plane of Bolyai and Lobachevsky, and that these transformations are exactly its
orientation-preserving isometries (for real matrices). We do not formalise the metric; we
prove the algebraic heart of the matter, the imaginary-part formula

  `Im (γ τ) = Im τ / |c τ + d|²`  (`im_mob`, valid because `ad − bc = 1`),

from which it follows that `γ` maps ℍ into ℍ. We then show that this is a **group action**
of SL₂(ℤ) on ℍ (`instMulAction`: `I τ = τ` and `(γδ) τ = γ (δ τ)`), using the
**cocycle identity** for the automorphy factor `j(γ, τ) = c τ + d`,

  `j(γδ, τ) = j(γ, δτ) · j(δ, τ)`  (`denom_mul`),

which is also exactly what makes the definition of a modular form of weight `k`
(`f(γτ) = j(γ, τ)^k f(τ)`, file `Forms`) consistent. Finally `−I` acts trivially
(`negOne_smul`), so the action factors through `PSL₂(ℤ) = SL₂(ℤ)/{±I}`.

The complex numbers `C` and the reals `R` are the from-scratch constructions of Part II;
integer matrix entries enter through the canonical casts `ℤ → ℝ → ℂ`.
-/

namespace Foundations.Langlands.Modular

open Foundations.Numbers Foundations.Algebra Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

/-- **The upper half-plane** `ℍ = {τ ∈ ℂ : Im τ > 0}`. -/
structure UHP where
  /-- The underlying complex number. -/
  z : C
  /-- Its imaginary part is positive. -/
  pos : 0 < z.im

namespace UHP

/-- Points of ℍ with the same underlying complex number are equal. -/
theorem ext {p q : UHP} (h : p.z = q.z) : p = q := by cases p; cases q; simp only at h; subst h; rfl

end UHP

namespace SL2Z

/-- The real part of an integer, viewed as a complex number, is that integer. -/
@[simp] theorem intCast_re (n : Int) : ((n : C)).re = (n : R) := rfl
/-- The imaginary part of an integer, viewed as a complex number, is zero. -/
@[simp] theorem intCast_im (n : Int) : ((n : C)).im = 0 := rfl

/-- The **automorphy factor** `j(γ, τ) = c τ + d`, the denominator of the Möbius map. -/
def denom (g : SL2Z) (z : C) : C := (g.c : C) * z + (g.d : C)

/-- The **Möbius transformation** `γ τ = (a τ + b) / (c τ + d)`, as a map `ℂ → ℂ`. -/
noncomputable def mob (g : SL2Z) (z : C) : C := ((g.a : C) * z + (g.b : C)) / denom g z

/-- The determinant identity cast into the reals: `a d − b c = 1` in `ℝ`. -/
theorem det_real (g : SL2Z) : (g.a : R) * (g.d : R) - (g.b : R) * (g.c : R) = 1 := by
  have h : ((g.a * g.d - g.b * g.c : Int) : R) = ((1 : Int) : R) := by rw [g.det]
  rw [Ring.intCast_sub, Ring.intCast_mul, Ring.intCast_mul, Ring.intCast_one] at h
  exact h

/-- The integer cast into `ℝ` is injective. -/
theorem intCast_inj {m n : Int} (h : (m : R) = (n : R)) : m = n := by
  rcases Int.lt_trichotomy m n with hl | he | hg
  · have := (OF.intCast_lt (K := R)).2 hl; grind
  · exact he
  · have := (OF.intCast_lt (K := R)).2 hg; grind

/-- `|c τ + d|² = (c x + d)² + (c y)²` for `τ = x + i y`. -/
theorem normSq_denom (g : SL2Z) (z : C) :
    C.normSq (denom g z) = ((g.c : R) * z.re + g.d) * ((g.c : R) * z.re + g.d) +
      ((g.c : R) * z.im) * ((g.c : R) * z.im) := by
  simp only [C.normSq, denom, C.add_re, C.add_im, C.mul_re, C.mul_im, intCast_re, intCast_im]
  grind

/-- **The automorphy factor does not vanish on ℍ.** If `Im τ > 0` then `c τ + d ≠ 0`: the
imaginary part forces `c = 0`, the real part then `d = 0`, contradicting `ad − bc = 1`. -/
theorem denom_ne_zero (g : SL2Z) {z : C} (hz : 0 < z.im) : denom g z ≠ 0 := by
  intro h
  have him := congrArg C.im h
  have hre := congrArg C.re h
  simp only [denom, C.add_re, C.add_im, C.mul_re, C.mul_im, intCast_re, intCast_im,
    C.zero_re, C.zero_im] at him hre
  have hc0 : (g.c : R) = 0 := by
    apply Classical.byContradiction; intro hc
    have : (g.c : R) * z.im = 0 := by grind
    rcases Classical.em (0 < (g.c : R)) with hp | hp
    · have := OrderedRing.mul_pos hp hz; grind
    · have hn : 0 < -(g.c : R) := by grind
      have := OrderedRing.mul_pos hn hz; grind
  have hd0 : (g.d : R) = 0 := by rw [hc0] at hre; grind
  have hc : g.c = 0 := intCast_inj (by rw [hc0, Ring.intCast_zero])
  have hd : g.d = 0 := intCast_inj (by rw [hd0, Ring.intCast_zero])
  have := g.det; rw [hc, hd] at this; simp at this

/-- `|c τ + d|² > 0` on ℍ. -/
theorem normSq_denom_pos (g : SL2Z) {z : C} (hz : 0 < z.im) : 0 < C.normSq (denom g z) := by
  have h0 := C.normSq_nonneg (denom g z)
  have hne : C.normSq (denom g z) ≠ 0 := fun h => denom_ne_zero g hz (C.normSq_eq_zero h)
  grind

/-- **Imaginary part of a Möbius transform.** For `γ ∈ SL₂(ℤ)` and any `τ ∈ ℂ`,
`Im (γ τ) = Im τ / |c τ + d|²`. -/
theorem im_mob (g : SL2Z) (z : C) : (mob g z).im = z.im / C.normSq (denom g z) := by
  have hdet := det_real g
  show (((g.a : C) * z + (g.b : C)) * (denom g z)⁻¹).im = _
  simp only [C.mul_re, C.mul_im, C.inv_re, C.inv_im, C.add_re, C.add_im, intCast_re, intCast_im,
    denom]
  generalize C.normSq ((g.c : C) * z + (g.d : C)) = N
  grind

/-- **Imaginary part via the modulus.** `Im (γ τ) = Im τ / (|c τ + d| · |c τ + d|)`, with the
modulus `|·|` of Part II. -/
theorem im_mob_cabs (g : SL2Z) (z : C) :
    (mob g z).im = z.im / (C.cabs (denom g z) * C.cabs (denom g z)) := by
  rw [C.cabs_mul_self, im_mob]

/-- Möbius maps preserve ℍ: if `Im τ > 0` then `Im (γ τ) > 0`. -/
theorem im_mob_pos (g : SL2Z) {z : C} (hz : 0 < z.im) : 0 < (mob g z).im := by
  rw [im_mob]; exact OF.div_pos hz (normSq_denom_pos g hz)

/-- The identity matrix acts as the identity: `I τ = τ`. -/
theorem mob_one (z : C) : mob 1 z = z := by
  simp only [mob, denom, one_a, one_b, one_c, one_d]; grind

/-- **The cocycle identity.** `j(γδ, τ) = j(γ, δτ) · j(δ, τ)` whenever `j(δ, τ) ≠ 0`. -/
theorem denom_mul (g h : SL2Z) {z : C} (hz : denom h z ≠ 0) :
    denom (g * h) z = denom g (mob h z) * denom h z := by
  simp only [denom, mob, mul_c, mul_d] at hz ⊢
  grind

/-- **Compatibility with multiplication.** `(γδ) τ = γ (δ τ)` whenever `j(δ, τ) ≠ 0` (in
particular on ℍ). -/
theorem mob_mul (g h : SL2Z) {z : C} (hz : denom h z ≠ 0) :
    mob (g * h) z = mob g (mob h z) := by
  simp only [denom, mob, mul_a, mul_b, mul_c, mul_d] at hz ⊢
  grind

/-- `−I` acts trivially: `(−τ + 0)/(0 τ − 1) = τ`. -/
theorem mob_negOne (z : C) : mob negOne z = z := by
  simp only [mob, denom, negOne]; grind

/-- `−γ` and `γ` induce the same Möbius map. -/
theorem mob_neg (g : SL2Z) (z : C) : mob (neg g) z = mob g z := by
  simp only [mob, denom, neg]; grind

/-- `S τ = −1/τ`. -/
theorem mob_S (z : C) : mob S z = -1 / z := by
  simp only [mob, denom, S]; grind

/-- `Tₙ τ = τ + n`. -/
theorem mob_Tn (n : Int) (z : C) : mob (Tn n) z = z + (n : C) := by
  simp only [mob, denom, Tn]; grind

/-- Translations do not change the imaginary part: `Im (τ + n) = Im τ`. -/
theorem im_mob_Tn (n : Int) (z : C) : (mob (Tn n) z).im = z.im := by
  rw [mob_Tn]; simp only [C.add_im, intCast_im]; grind

/-- Translations shift the real part: `Re (τ + n) = Re τ + n`. -/
theorem re_mob_Tn (n : Int) (z : C) : (mob (Tn n) z).re = z.re + (n : R) := by
  rw [mob_Tn]; simp

/-- `Im (S τ) = Im τ / |τ|²`. -/
theorem im_mob_S (z : C) : (mob S z).im = z.im / C.normSq z := by
  rw [im_mob]; congr 1; simp only [denom, S]; congr 1; grind

/-- The action of `γ ∈ SL₂(ℤ)` on a point of ℍ. -/
noncomputable def act (g : SL2Z) (p : UHP) : UHP := ⟨mob g p.z, im_mob_pos g p.pos⟩

/-- The action on ℍ, written `γ • τ`. -/
noncomputable instance : SMul SL2Z UHP := ⟨act⟩

/-- The underlying complex number of `γ • τ` is the Möbius transform `γ τ`. -/
@[simp] theorem smul_z (g : SL2Z) (p : UHP) : (g • p).z = mob g p.z := rfl

/-- **SL₂(ℤ) acts on ℍ.** The Möbius transformations define a group action:
`I • τ = τ` and `(γδ) • τ = γ • (δ • τ)`. -/
noncomputable instance instMulAction : MulAction SL2Z UHP where
  one_smul p := UHP.ext (mob_one p.z)
  mul_smul g h p := UHP.ext (mob_mul g h (denom_ne_zero h p.pos))

/-- **−I acts trivially on ℍ.** Hence the action factors through `PSL₂(ℤ)`. -/
theorem negOne_smul (p : UHP) : negOne • p = p := UHP.ext (mob_negOne p.z)

/-- `γ` and `−γ` act identically on ℍ. -/
theorem neg_smul (g : SL2Z) (p : UHP) : neg g • p = g • p := UHP.ext (mob_neg g p.z)

/-- **The imaginary-part formula on ℍ.** `Im (γ • τ) = Im τ / |c τ + d|²`. -/
theorem im_smul (g : SL2Z) (p : UHP) :
    (g • p).z.im = p.z.im / C.normSq (denom g p.z) := im_mob g p.z

end SL2Z

end Foundations.Langlands.Modular
