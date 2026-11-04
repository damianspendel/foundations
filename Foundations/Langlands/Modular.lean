import Foundations.Langlands.Modular.SL2
import Foundations.Langlands.Modular.Action
import Foundations.Langlands.Modular.FundamentalDomain
import Foundations.Langlands.Modular.FundamentalDomainUnique
import Foundations.Langlands.Modular.Generation
import Foundations.Langlands.Modular.Forms

/-!
# Part XV, chapter 4: the modular group and the upper half-plane

The Langlands programme has two sides. The chapters `Padic`, `Rep` and `Cyclotomic` work on
the arithmetic (Galois) side. This chapter takes the first step on the **automorphic side**,
whose oldest and most concrete instance is the theory of modular forms: functions on the
upper half-plane `ℍ` transforming in a prescribed way under the modular group SL₂(ℤ).

## History

Klein (1877–1880) and Poincaré (1880–1884) made SL₂(ℤ) and its subgroups central to analysis.
Klein studied the **modular figure**, the tessellation of ℍ by the images of one curvilinear
triangle, and the elliptic modular function `j`; Poincaré recognised the Möbius action as the
isometries of the hyperbolic plane and built automorphic functions for every Fuchsian group
from fundamental polygons. Earlier, Gauss's reduction theory of binary quadratic forms (1801)
had been the same fundamental-domain theorem in other words. Eisenstein, Weierstrass and later
Hecke supplied modular forms with arithmetic content, Hecke attaching to them `L`-functions
with Euler products.

**Modularity theorem (prose only, not formalised or claimed).** Every elliptic curve over ℚ is
modular: its `L`-function is that of a weight-2 newform on `Γ₀(N)` (Wiles; Taylor–Wiles;
Breuil–Conrad–Diamond–Taylor). In Langlands' terms, the 2-dimensional Galois representation
of the curve corresponds to an automorphic representation of `GL₂`; this is one case of the
reciprocity conjecture, far beyond what is built here.

## What is proved

* `SL2`: **SL₂(ℤ) is a group** (`SL2Z.instGroup`); the generators `S = (0 −1; 1 0)` and
  `T = (1 1; 0 1)` satisfy **`S² = −I`** (`S_mul_S`) and **`(ST)³ = −I`** (`ST_cube`).
* `Action`: on `ℍ = {Im τ > 0}` (`UHP`), the Möbius map `γτ = (aτ + b)/(cτ + d)` satisfies
  **`Im(γτ) = Im τ / |cτ + d|²`** (`im_mob`, `im_mob_cabs`), defines a **group action**
  (`instMulAction`), with cocycle `j(γδ, τ) = j(γ, δτ) j(δ, τ)` (`denom_mul`), and **`−I` acts
  trivially** (`negOne_smul`).
* `FundamentalDomain`: with `F = {|Re τ| ≤ 1/2, |τ| ≥ 1}` (`InF`, stated with `|τ|²`;
  `one_le_cabs_iff`), **every point of ℍ is equivalent to a point of F** (`exists_mem_F`),
  by maximising `Im` over the orbit (`exists_max_im`, using that only finitely many bottom
  rows have `|cτ + d| ≤ 1`, `bounds`), translating by a power of `T` and inverting by `S`.
* `FundamentalDomainUnique`: points of `F` have maximal height in their orbit
  (`im_smul_le_of_mem_F`), and **two interior points of F are equivalent only if equal**
  (`eq_of_interior`).
* `Generation`: **S and T generate SL₂(ℤ)** (`generation`, `genST_eq_top`), by the Euclidean
  algorithm on the first column; with an induction principle (`induction_on`).
* `Forms`: the **weight-k transformation law** `IsModular k f` (a predicate only: no holomorphy,
  since the library has no complex analysis); **S and T suffice** (`isModular_of_S_T`); odd
  weights force `f = 0` (`eq_zero_of_odd`); and a **non-constant weight-0 invariant**, the
  height `max_γ Im(γτ)` (`heightC_isModular`), which also shows `i ≁ 2i`
  (`not_equiv_i_two_i`).

## Not formalised

Holomorphy and the cusp condition; Eisenstein series, the discriminant `Δ`, the `j`-function
and `q`-expansions; the dimension formula; the boundary identifications of `F` and the
stabilisers of `i` and `ρ`; the presentation `⟨S, T | S⁴, (ST)³, S²(ST)⁻³⟩`; congruence
subgroups, Hecke operators, `L`-functions; automorphic representations; modularity.
-/
