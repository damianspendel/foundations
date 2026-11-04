import Foundations.Langlands.Cyclotomic.Dedekind

/-!
# `Φ_n` has integer coefficients and is irreducible over `ℚ`

**Theorem (Gauss for prime `n`, 1801; Kronecker 1854 and Dedekind 1857 in general).** For every
`n ≥ 1` the cyclotomic polynomial `Φ_n = ∏_{gcd(a,n)=1} (x - ζ_n^a)` has integer coefficients,
is monic of degree `φ(n)`, and is irreducible over `ℚ`. It is the minimal polynomial of `ζ_n`.

Let `P` be the monic minimal polynomial of `ζ_n` over `ℚ`.

* `P` divides `xⁿ - 1`, so by Gauss's lemma it has integer coefficients.
* By Dedekind's lemma (`Dedekind.lean`) every primitive root `ζ_n^a` is a root of `P`. These
  `φ(n)` roots are distinct, so `Φ_n ∣ P` in `ℂ[x]`.
* Every root `ω` of `P` is primitive. `ω` is an `n`-th root of unity, `ω = ζ_n^j`. If
  `g = gcd(j, n) > 1`, then `ω^{n/g} = 1`, so the irreducible `P` divides `x^{n/g} - 1`, giving
  `ζ_n^{n/g} = 1`, which is false.
* Write `P = Φ_n T`. From `xⁿ - 1 = P R = Φ_n · ∏_{gcd(a,n)≠1} (x - ζ_n^a)`, `T` divides the
  product of the non-primitive linear factors. If `T` were not constant it would have a
  non-primitive root, which would be a root of `P`. So `T = 1` and `P = Φ_n`.

The integer polynomial `cycloZ n` is the one whose image in `ℂ[x]` is `Φ_n` (`map_cycloZ`), and
`cycloQ n` is its image in `ℚ[x]`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

section Roots

variable {n : Nat} (hn : 1 ≤ n)

include hn in
/-- `ζ_n` is a root of `xⁿ - 1`. -/
theorem aeval_zetaN_X_pow_sub_one : aeval Qc (zeta n) ((X : Polynomial Qc) ^ n + -1) = 0 := by
  rw [aeval_X_pow_sub_one, zeta_rpow_self hn]; exact Ring.add_neg_cancel _

include hn in
/-- **Roots of `P` are primitive.** If an irreducible rational polynomial `P` vanishes at `ζ_n`,
then each of its complex roots is a primitive `n`-th root of unity `ζ_n^j`,
`gcd(j, n) = 1`. -/
theorem root_primitive {P : Polynomial Qc} (hP : Irreducible P) (hPζ : aeval Qc (zeta n) P = 0)
    {ω : ℂ} (hω : aeval Qc ω P = 0) : ∃ j, j < n ∧ Nat.Coprime j n ∧ ω = rpow (zeta n) j := by
  have hroot : ∀ m : Nat, aeval Qc ω ((X : Polynomial Qc) ^ m + -1) = 0 →
      aeval Qc (zeta n) ((X : Polynomial Qc) ^ m + -1) = 0 := fun m h => by
    obtain ⟨c, hc⟩ := dvd_of_irreducible_root hP hω h
    rw [hc, aeval_mul, hPζ, Ring.zero_mul]
  have hpow : ∀ x : ℂ, ∀ m : Nat, aeval Qc x ((X : Polynomial Qc) ^ m + -1) = 0 ↔ rpow x m = 1 := by
    intro x m
    rw [aeval_X_pow_sub_one]
    constructor
    · intro h; have := congrArg (· + 1) h
      rw [Ring.add_assoc, Ring.neg_add_cancel, Ring.add_zero, Ring.zero_add] at this; exact this
    · intro h; rw [h]; exact Ring.add_neg_cancel _
  have hωn : rpow ω n = 1 := by
    obtain ⟨c, hc⟩ := dvd_of_irreducible_root hP hPζ (aeval_zetaN_X_pow_sub_one hn)
    exact (hpow ω n).1 (by rw [hc, aeval_mul, hω, Ring.zero_mul])
  obtain ⟨j, hj, rfl⟩ := eq_zeta_rpow hn hωn
  refine ⟨j, hj, ?_, rfl⟩
  apply Classical.byContradiction; intro hg
  let g := Nat.gcd j n
  have hg1 : g ≠ 1 := hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right j (by omega)
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right j n
  obtain ⟨j', hj'⟩ := Nat.gcd_dvd_left j n
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hm; omega
  have hmn : m < n := by
    rw [hm]
    calc m = 1 * m := (Nat.one_mul m).symm
      _ < g * m := Nat.mul_lt_mul_of_pos_right (by omega) hm0
  have hζm : rpow (zeta n) m = 1 := by
    apply (hpow _ m).1
    apply hroot m
    apply (hpow _ m).2
    rw [← rpow_mul', show j * m = n * j' by
      rw [hj']; show g * j' * m = n * j'; rw [hm]; grind, rpow_mul', zeta_rpow_self hn, one_rpow']
  have := Nat.le_of_dvd hm0 ((zeta_rpow_eq_one_iff hn).1 hζm)
  omega

/-- The image of an integer polynomial in `ℂ[x]` through `ℚ[x]`. -/
theorem map_incl_icast (F : Polynomial Int) :
    mapPoly Qc.incl (mapPoly (icastHom Qc) F) = mapPoly (icastHom ℂ) F := by
  apply ext; intro k
  rw [coeff_mapPoly, coeff_mapPoly, coeff_mapPoly]
  exact Subfield.coe_intCast Qc _

include hn in
/-- **The minimal polynomial of `ζ_n` is `Φ_n`, with integer coefficients.** There is a monic
integer polynomial of degree `φ(n)` whose image in `ℂ[x]` is `Φ_n` and whose image in `ℚ[x]`
generates the ideal of rational polynomials vanishing at `ζ_n`. -/
theorem exists_cycloZ : ∃ F : Polynomial Int, Monic F (totient n) ∧
    mapPoly (icastHom ℂ) F = cycloC n ∧
    ∀ q, aeval Qc (zeta n) q = 0 ↔ Divides (mapPoly (icastHom Qc) F) q := by
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  have hDC : IsDomain (Polynomial ℂ) := Polynomial.isDomain C.isDomain
  let B : Polynomial Int := X ^ n + -1
  have hBQ : mapPoly (icastHom Qc) B = X ^ n + -1 := mapPoly_X_pow_sub_one _ n
  have hBm : Monic (mapPoly (icastHom Qc) B) n := by rw [hBQ]; exact monic_X_pow_sub_one hn
  have hBζ : aeval Qc (zeta n) (mapPoly (icastHom Qc) B) = 0 := by
    rw [hBQ]; exact aeval_zetaN_X_pow_sub_one hn
  obtain ⟨P, d, hPm, hP⟩ := exists_monic_minpoly ⟨_, hBm.ne_zero hD.1, hBζ⟩
  have hPirr := irreducible_of_minpoly hP (hPm.ne_zero hD.1)
  have hPζ : aeval Qc (zeta n) P = 0 := (hP P).2 ⟨1, (Ring.mul_one P).symm⟩
  obtain ⟨R, hR⟩ := (hP _).1 hBζ
  obtain ⟨_, hRm⟩ := hPm.of_mul hD hBm hR.symm
  obtain ⟨PZ, hPZ⟩ := int_of_monic_factor_Q hPm hRm hR
  obtain ⟨RZ, hRZ⟩ := int_of_monic_factor_Q hRm hPm (by rw [hR]; exact CommRing.mul_comm _ _)
  have hPZm : Monic PZ d := Monic.of_map_icast (hPZ ▸ hPm)
  have hev : ∀ x : ℂ, aeval Qc x P = eval x (mapPoly (icastHom ℂ) PZ) := fun x => by
    rw [← aeval_map_icast, hPZ]
  -- `Φ_n ∣ P`
  obtain ⟨T, hT⟩ := prodLin_dvd C.isDomain (primRoots n) (mapPoly (icastHom ℂ) PZ)
    (nodup_primRoots hn) (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      rw [← hev]
      exact aeval_zeta_pow_of_coprime hn hPζ a (mem_unitExps.1 ha).2)
  -- `xⁿ - 1 = Φ_n T R` in `ℂ[x]`
  have hBZ : B = PZ * RZ := by
    apply mapPoly_icast_inj_Q
    show _ = (mapHom (icastHom Qc)).toFun (PZ * RZ)
    rw [(mapHom (icastHom Qc)).map_mul]
    show _ = mapPoly (icastHom Qc) PZ * mapPoly (icastHom Qc) RZ
    rw [hPZ, hRZ, hR]
  have hC : cycloC n * prodLin (nonPrimRoots n) = cycloC n * (T * mapPoly (icastHom ℂ) RZ) := by
    rw [← X_pow_sub_one_eq hn, ← mapPoly_X_pow_sub_one (icastHom ℂ) n]
    show mapPoly (icastHom ℂ) B = _
    rw [hBZ]
    show (mapHom (icastHom ℂ)).toFun (PZ * RZ) = _
    rw [(mapHom (icastHom ℂ)).map_mul]
    show mapPoly (icastHom ℂ) PZ * _ = _
    rw [hT]; exact Ring.mul_assoc _ _ _
  have hC' := hDC.mul_left_cancel ((monic_cycloC n).ne_zero C.isField.1) hC
  -- `T` is constant
  have hT0 : natDegree T = 0 := by
    apply Classical.byContradiction; intro hpos
    obtain ⟨x, hx, hTx⟩ := exists_root_of_dvd_prodLin C.isDomain _ T _ hC'.symm (by omega)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨han, hna⟩ := mem_nonUnitExps.1 ha
    have hPx : aeval Qc (rpow (zeta n) a) P = 0 := by
      rw [hev, hT, eval_mul, hTx, Ring.mul_zero]
    obtain ⟨j, hj, hjc, hjx⟩ := root_primitive hn hPirr hPζ hPx
    exact hna (zeta_rpow_inj hn han hj hjx ▸ hjc)
  obtain ⟨hle, hTm⟩ := (monic_cycloC n).of_mul C.isDomain (hPZm.map (icastHom ℂ))
    (show cycloC n * T = _ from hT.symm)
  have hd : d = totient n := by
    have := hTm.natDegree_eq C.isField.1; omega
  rw [hd, Nat.sub_self] at hTm
  refine ⟨PZ, hd ▸ hPZm, ?_, fun q => hPZ ▸ hP q⟩
  rw [hT, hTm.eq_one, Ring.mul_one]; rfl

end Roots

/-! ## The integer polynomial `Φ_n` -/

/-- **The `n`-th cyclotomic polynomial with integer coefficients** (for `n ≥ 1`; `1` for
`n = 0`). Its image in `ℂ[x]` is `Φ_n = ∏_{gcd(a,n)=1} (x - ζ_n^a)` (`map_cycloZ`). -/
noncomputable def cycloZ (n : Nat) : Polynomial Int :=
  if h : 1 ≤ n then Classical.choose (exists_cycloZ h) else 1

/-- **`Φ_n` over `ℚ`**: the image of `cycloZ n` in `ℚ[x]`. -/
noncomputable def cycloQ (n : Nat) : Polynomial Qc := mapPoly (icastHom Qc) (cycloZ n)

section Spec

variable {n : Nat} (hn : 1 ≤ n)

include hn in
/-- The defining properties of `cycloZ n`. -/
theorem cycloZ_spec : Monic (cycloZ n) (totient n) ∧ mapPoly (icastHom ℂ) (cycloZ n) = cycloC n ∧
    ∀ q, aeval Qc (zeta n) q = 0 ↔ Divides (cycloQ n) q := by
  unfold cycloQ cycloZ; rw [dite_eq_left hn]; exact Classical.choose_spec (exists_cycloZ hn)

include hn in
/-- **`Φ_n` has integer coefficients.** For `n ≥ 1` the polynomial
`Φ_n = ∏_{a < n, gcd(a,n) = 1} (x - ζ_n^a)` over `ℂ` is the image of the integer polynomial
`cycloZ n`. -/
theorem map_cycloZ : mapPoly (icastHom ℂ) (cycloZ n) = cycloC n := (cycloZ_spec hn).2.1

include hn in
/-- `Φ_n` is monic of degree `φ(n)` over `ℤ`. -/
theorem monic_cycloZ : Monic (cycloZ n) (totient n) := (cycloZ_spec hn).1

include hn in
/-- **The degree of `Φ_n` is `φ(n)`.** -/
theorem natDegree_cycloZ : natDegree (cycloZ n) = totient n :=
  (monic_cycloZ hn).natDegree_eq (by decide)

include hn in
/-- `Φ_n` is monic of degree `φ(n)` over `ℚ`. -/
theorem monic_cycloQ : Monic (cycloQ n) (totient n) := (monic_cycloZ hn).map _

include hn in
/-- **The minimal polynomial of `ζ_n` is `Φ_n`.** A rational polynomial vanishes at `ζ_n`
exactly when it is a multiple of `Φ_n`. -/
theorem aeval_zetaN_eq_zero_iff (q : Polynomial Qc) :
    aeval Qc (zeta n) q = 0 ↔ Divides (cycloQ n) q := (cycloZ_spec hn).2.2 q

include hn in
/-- `Φ_n(ζ_n) = 0`. -/
theorem aeval_cycloQ_zeta : aeval Qc (zeta n) (cycloQ n) = 0 :=
  (aeval_zetaN_eq_zero_iff hn _).2 ⟨1, (Ring.mul_one _).symm⟩

include hn in
/-- **Irreducibility of `Φ_n` over `ℚ`.** For every `n ≥ 1` the cyclotomic polynomial `Φ_n`
is irreducible in `ℚ[x]`. -/
theorem cycloQ_irreducible : Irreducible (cycloQ n) :=
  irreducible_of_minpoly (aeval_zetaN_eq_zero_iff hn)
    ((monic_cycloQ hn).ne_zero (Qc.isField C.isField).1)

include hn in
/-- **The roots of `Φ_n`.** A complex number is a root of `Φ_n` exactly when it is a primitive
`n`-th root of unity `ζ_n^j`, `j < n`, `gcd(j, n) = 1`. -/
theorem aeval_cycloQ_eq_zero_iff (ω : ℂ) :
    aeval Qc ω (cycloQ n) = 0 ↔ ∃ j, j < n ∧ Nat.Coprime j n ∧ ω = rpow (zeta n) j := by
  constructor
  · exact root_primitive hn (cycloQ_irreducible hn) (aeval_cycloQ_zeta hn)
  · rintro ⟨j, _, hj, rfl⟩
    exact aeval_zeta_pow_of_coprime hn (aeval_cycloQ_zeta hn) j hj

end Spec

/-! ## Compatibility with the prime case -/

/-- **`Φ_p` is the earlier `1 + x + ⋯ + x^{p-1}`.** For a prime `p`, the general cyclotomic
polynomial `cycloQ p` is the polynomial `cyclo Qc p` of `CyclotomicPoly.lean`: both are monic
minimal polynomials of `ζ_p`. -/
theorem cycloQ_prime {p : Nat} (hp : IsPrime p) : cycloQ p = cyclo Qc p := by
  have h2 := hp.1
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  have hm : Monic (cyclo Qc p) (p - 1) :=
    ⟨by rw [show p - 1 + 1 = p by omega]; exact degLT_cyclo p,
      by rw [coeff_cyclo, ite_true_of (by omega)]⟩
  have hΦ : aeval Qc (zeta p) (cyclo Qc p) = 0 :=
    (aeval_zeta_eq_zero_iff hp _).2 ⟨1, (Ring.mul_one _).symm⟩
  obtain ⟨T, hT⟩ := (aeval_zetaN_eq_zero_iff (by omega) _).1 hΦ
  obtain ⟨_, hTm⟩ := (monic_cycloQ (n := p) (by omega)).of_mul hD hm hT.symm
  rw [totient_prime hp, Nat.sub_self] at hTm
  rw [hT, hTm.eq_one, Ring.mul_one]

end Foundations.Langlands
