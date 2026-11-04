import Foundations.Langlands.Modular.Generation
import Foundations.Langlands.Modular.FundamentalDomainUnique

/-!
# The transformation law of modular forms

A **modular form of weight `k`** for SL₂(ℤ) is a function `f : ℍ → ℂ` such that

  `f(γτ) = (cτ + d)^k f(τ)`  for all `γ = (a b; c d) ∈ SL₂(ℤ)`,

which is moreover **holomorphic** on ℍ and **holomorphic at the cusp** `i∞` (bounded as
`Im τ → ∞`). Eisenstein (1847) and Weierstrass gave the first examples, the series
`G_k(τ) = Σ' (mτ + n)^{−k}` for even `k ≥ 4`; Klein's `j`-invariant (1878) is the basic
modular *function* (weight `0`, meromorphic), and it classifies elliptic curves over ℂ up to
isomorphism. Hecke (1930s) attached `L`-functions with Euler products and functional
equations to modular forms, and this is the bridge to arithmetic.

**What is, and is not, formalised here.** The library has the complex numbers and some real
analysis, but no theory of holomorphic functions of a complex variable (no complex
derivative on open subsets of ℂ, no Laurent or `q`-expansions). We therefore define only the
**transformation law** `IsModular k f`, i.e. "weakly modular of weight `k`" with no
analytic condition. This is a predicate on arbitrary functions; it is *not* the notion of a
modular form, and nothing below is a modular form in the classical sense.

What we prove:

* the transformation law is consistent, thanks to the cocycle identity `denom_mul`;
* **it suffices to check `S` and `T`** (`isModular_of_S_T`): if `f(−1/τ) = τ^k f(τ)` and
  `f(τ + 1) = f(τ)`, then `f` satisfies the law for every `γ`, by generation (`Generation`);
* **odd weights are empty** (`eq_zero_of_odd`): `−I` gives `f = (−1)^k f`;
* **a non-trivial weight-0 example** (`height`): the *height* `h(τ) = max_γ Im(γτ)`, which
  exists by `FundamentalDomain.exists_max_im`, is SL₂(ℤ)-invariant (`height_smul`), equals
  `Im τ` on `F` (`height_of_mem_F`), and is not constant (`height_i`, `height_two_i`); hence
  `i` and `2i` are not equivalent (`not_equiv_i_two_i`). The height is continuous but not
  holomorphic — it is a weight-0 invariant, not a modular function such as `j`.

## The modularity theorem and the automorphic side of Langlands (prose only)

Modular forms of weight `2` for the congruence subgroups `Γ₀(N) ⊂ SL₂(ℤ)` that are Hecke
eigenforms have Fourier coefficients `a_p` which are algebraic integers. The
**modularity theorem** (Wiles and Taylor–Wiles 1995 for semistable curves;
Breuil–Conrad–Diamond–Taylor 2001 in general) says that for every elliptic curve `E` over ℚ of conductor `N` there is such a
newform `f` with `a_p(f) = p + 1 − #E(𝔽_p)` for all primes `p ∤ N`. It implies Fermat's Last
Theorem via Frey, Serre and Ribet. **It is not stated or proved in this library.**

In Langlands' language a modular eigenform generates an *automorphic representation* of
`GL₂` over the adèles of ℚ, and an elliptic curve gives a two-dimensional *Galois
representation* (on its Tate module); modularity is the statement that these match prime by
prime, a case of the Langlands reciprocity conjecture for `GL₂`. The `Cyclotomic` chapter
treats the `GL₁` prototype on the Galois side; this chapter takes only the first step on the
automorphic side: the group, its action on ℍ, the fundamental domain, generation, and the
transformation law.
-/

namespace Foundations.Langlands.Modular

open Foundations.Numbers Foundations.Algebra Foundations.Algebra.Group Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

namespace SL2Z

/-- **Weakly modular of weight k.** `f : ℍ → ℂ` satisfies the transformation law
`f(γτ) = (cτ + d)^k f(τ)` for all `γ ∈ SL₂(ℤ)`. No holomorphy is required (the library has no
complex analysis), so this is a *predicate on arbitrary functions*, not the full notion of a
modular form. -/
def IsModular (k : Nat) (f : UHP → C) : Prop :=
  ∀ (g : SL2Z) (p : UHP), f (g • p) = denom g p.z ^ k * f p

/-- `j(I, τ) = 1`. -/
theorem denom_one (z : C) : denom 1 z = 1 := by simp only [denom, one_c, one_d]; grind

/-- `j(S, τ) = τ`. -/
theorem denom_S (z : C) : denom S z = z := by simp only [denom, S]; grind

/-- `j(T, τ) = 1`. -/
theorem denom_T (z : C) : denom T z = 1 := by simp only [denom, T]; grind

/-- `j(−I, τ) = −1`. -/
theorem denom_negOne (z : C) : denom negOne z = -1 := by simp only [denom, negOne]; grind

/-- `1^k = 1` in ℂ. -/
theorem one_pow (k : Nat) : (1 : C) ^ k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Semiring.pow_succ, ih]; grind

/-- `(−1)^(2m+1) = −1` in ℂ. -/
theorem neg_one_pow_odd (m : Nat) : (-1 : C) ^ (2 * m + 1) = -1 := by
  induction m with
  | zero => rw [Semiring.pow_succ, Semiring.pow_zero]; grind
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega, Semiring.pow_succ, Semiring.pow_succ,
      ih]
    grind

/-- The transformation law for `γ` and `δ` gives it for `γδ` (by the cocycle identity). -/
theorem law_mul {k : Nat} {f : UHP → C} {g h : SL2Z}
    (hg : ∀ p, f (g • p) = denom g p.z ^ k * f p) (hh : ∀ p, f (h • p) = denom h p.z ^ k * f p) :
    ∀ p, f ((g * h) • p) = denom (g * h) p.z ^ k * f p := by
  intro p
  rw [MulAction.mul_smul, hg, hh, denom_mul g h (denom_ne_zero h p.pos), C.mul_pow]
  show _ = denom g (mob h p.z) ^ k * denom h p.z ^ k * f p
  rw [← smul_z]; grind

/-- The transformation law for `γ` gives it for `γ⁻¹`. -/
theorem law_inv {k : Nat} {f : UHP → C} {g : SL2Z}
    (hg : ∀ p, f (g • p) = denom g p.z ^ k * f p) :
    ∀ p, f (g⁻¹ • p) = denom g⁻¹ p.z ^ k * f p := by
  intro p
  have hu : denom g (g⁻¹ • p).z * denom g⁻¹ p.z = 1 := by
    rw [smul_z, ← denom_mul g g⁻¹ (denom_ne_zero _ p.pos), mul_inv_cancel, denom_one]
  have h1 := hg (g⁻¹ • p)
  rw [MulAction.smul_inv_smul] at h1
  have hk : denom g⁻¹ p.z ^ k * denom g (g⁻¹ • p).z ^ k = 1 := by
    rw [← C.mul_pow, C.mul_comm, hu, one_pow]
  rw [h1]
  calc f (g⁻¹ • p) = (denom g⁻¹ p.z ^ k * denom g (g⁻¹ • p).z ^ k) * f (g⁻¹ • p) := by
        rw [hk]; grind
    _ = denom g⁻¹ p.z ^ k * (denom g (g⁻¹ • p).z ^ k * f (g⁻¹ • p)) := by grind

/-- **S and T suffice.** If `f(−1/τ) = τ^k f(τ)` and `f(τ + 1) = f(τ)` for all `τ ∈ ℍ`, then
`f` satisfies the weight-`k` transformation law for all of SL₂(ℤ). (Uses generation.) -/
theorem isModular_of_S_T {k : Nat} {f : UHP → C}
    (hS : ∀ p : UHP, f (S • p) = p.z ^ k * f p) (hT : ∀ p : UHP, f (T • p) = f p) :
    IsModular k f := by
  intro g
  have key : ∀ x, Gen x → ∀ p, f (x • p) = denom x p.z ^ k * f p := by
    intro x hx
    induction hx with
    | S => intro p; rw [denom_S]; exact hS p
    | T => intro p; rw [denom_T, one_pow]; rw [hT]; grind
    | one => intro p; rw [MulAction.one_smul, denom_one, one_pow]; grind
    | mul _ _ ih1 ih2 => exact law_mul ih1 ih2
    | inv _ ih => exact law_inv ih
  exact key g (generation g)

/-- The converse: a weakly modular function satisfies the `S` and `T` laws. -/
theorem S_T_of_isModular {k : Nat} {f : UHP → C} (hf : IsModular k f) :
    (∀ p : UHP, f (S • p) = p.z ^ k * f p) ∧ (∀ p : UHP, f (T • p) = f p) :=
  ⟨fun p => by rw [hf, denom_S], fun p => by rw [hf, denom_T, one_pow]; grind⟩

/-- **Odd weights vanish.** A function weakly modular of odd weight is identically zero,
because `−I` acts trivially but with factor `(−1)^k = −1`. -/
theorem eq_zero_of_odd {m : Nat} {f : UHP → C} (hf : IsModular (2 * m + 1) f) (p : UHP) :
    f p = 0 := by
  have h := hf negOne p
  rw [negOne_smul, denom_negOne, neg_one_pow_odd] at h
  have h1 := congrArg C.re h
  have h2 := congrArg C.im h
  simp only [C.mul_re, C.mul_im, C.neg_re, C.neg_im, C.one_re, C.one_im] at h1 h2
  apply C.ext
  · show (f p).re = 0; grind
  · show (f p).im = 0; grind

/-! ## A non-trivial invariant of weight 0: the height -/

/-- **The height** `h(τ) = max_{γ ∈ SL₂(ℤ)} Im(γτ)`; the maximum exists by
`exists_max_im`. -/
noncomputable def height (p : UHP) : R := ((Classical.choose (exists_max_im p)) • p).z.im

/-- The height bounds every imaginary part on the orbit. -/
theorem im_le_height (g : SL2Z) (p : UHP) : (g • p).z.im ≤ height p :=
  Classical.choose_spec (exists_max_im p) g

/-- **The height is SL₂(ℤ)-invariant.** `h(γτ) = h(τ)`. -/
theorem height_smul (g : SL2Z) (p : UHP) : height (g • p) = height p := by
  have h1 : height (g • p) ≤ height p := by
    have := im_le_height (Classical.choose (exists_max_im (g • p)) * g) p
    rw [MulAction.mul_smul] at this; exact this
  have h2 : height p ≤ height (g • p) := by
    have := im_le_height (Classical.choose (exists_max_im p) * g⁻¹) (g • p)
    rw [MulAction.mul_smul, MulAction.inv_smul_smul] at this; exact this
  grind

/-- **On F the height is the imaginary part.** -/
theorem height_of_mem_F {p : UHP} (hF : InF p.z) : height p = p.z.im := by
  have h1 := im_smul_le_of_mem_F (Classical.choose (exists_max_im p)) hF
  have h2 := im_le_height 1 p
  rw [MulAction.one_smul] at h2
  have e : height p = ((Classical.choose (exists_max_im p)) • p).z.im := rfl
  grind

/-- The point `i·t ∈ ℍ` for `t > 0`. -/
def iMul (t : R) (ht : 0 < t) : UHP := ⟨⟨0, t⟩, ht⟩

/-- `i·t ∈ F` when `t ≥ 1`. -/
theorem iMul_mem_F {t : R} (ht : 0 < t) (h1 : 1 ≤ t) : InF (iMul t ht).z := by
  refine ⟨OF.abs_le.2 ⟨by show -(1 / 2 : R) ≤ 0; grind, by show (0 : R) ≤ 1 / 2; grind⟩, ?_⟩
  show 1 ≤ (0 : R) * 0 + t * t
  have := OrderedRing.mul_le_mul_of_nonneg_left h1 (by grind : 0 ≤ t)
  grind

/-- **The height at i is 1.** -/
theorem height_i : height (iMul 1 (by grind)) = 1 :=
  height_of_mem_F (iMul_mem_F _ (by grind))

/-- **The height at 2i is 2.** -/
theorem height_two_i : height (iMul 2 (by grind)) = 2 :=
  height_of_mem_F (iMul_mem_F _ (by grind))

/-- **The height as a weight-0 function** `ℍ → ℂ`. -/
noncomputable def heightC (p : UHP) : C := C.ofReal (height p)

/-- **A non-trivial weakly modular function of weight 0.** The (real-valued) height satisfies
the weight-0 transformation law and is not constant. (It is not holomorphic, so it is not a
modular function in the classical sense.) -/
theorem heightC_isModular : IsModular 0 heightC ∧
    heightC (iMul 1 (by grind)) ≠ heightC (iMul 2 (by grind)) := by
  refine ⟨fun g p => ?_, fun h => ?_⟩
  · show C.ofReal (height (g • p)) = 1 * C.ofReal (height p)
    rw [height_smul]; grind
  · have := congrArg C.re h
    simp only [heightC, C.ofReal, height_i, height_two_i] at this
    grind

/-- **i and 2i are not SL₂(ℤ)-equivalent**, since their heights differ. -/
theorem not_equiv_i_two_i : ¬ ∃ g : SL2Z, g • iMul 1 (by grind) = iMul 2 (by grind) := by
  rintro ⟨g, hg⟩
  have := height_smul g (iMul 1 (by grind))
  rw [hg, height_i, height_two_i] at this
  grind

end SL2Z

end Foundations.Langlands.Modular
