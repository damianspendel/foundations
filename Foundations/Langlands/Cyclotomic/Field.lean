import Foundations.Langlands.Cyclotomic.Irreducible
import Foundations.Langlands.Cyclotomic.GaussSum

/-!
# The cyclotomic field `ℚ(ζ_p)`

Inside the complex numbers of Part II we form the field `ℚ(ζ_p)` generated over the rationals
`ℚ ⊆ ℂ` by `ζ_p = e^{2πi/p}`, using the simple-extension construction of the algebra part
(`adjoin`). Kummer called these fields the *cyclotomic* fields. His theory of ideal numbers in
`ℤ[ζ_p]` (1847) was built to repair the failure of unique factorisation there, which had
broken Lamé's attempted proof of Fermat's last theorem.

Two facts about `ζ_p` drive the Galois theory in the next file.

* **The minimal polynomial is `Φ_p`.** A rational polynomial vanishes at `ζ_p` exactly when it
  is a multiple of `Φ_p = 1 + x + ⋯ + x^{p-1}`. The polynomials vanishing at `ζ_p` are the
  multiples of a single polynomial `m`, which divides `Φ_p`; since `Φ_p` is irreducible
  (`Irreducible.lean`) and `m` is not a unit, `Φ_p` and `m` differ by a unit.
* **The other roots.** Every power `ζ_p^a` with `p ∤ a` is again a root of `Φ_p`, being a
  `p`-th root of unity different from `1`.

We also record the first arithmetic dividend. The Gauss sum `g = Σ_a (a/p) ζ_p^a` lies in
`ℚ(ζ_p)` and satisfies `g² = p*`, so **`ℚ(ζ_p)` contains a square root of
`p* = (-1)^((p-1)/2) p`**, and hence the quadratic field `ℚ(√p*)`. The Kronecker–Weber theorem
(stated by Kronecker in 1853; proofs by Weber in 1886 and Hilbert in 1896) says much more:
*every* finite abelian extension of `ℚ` lies in some cyclotomic field `ℚ(ζ_n)`. We do not prove
or use it.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

section Zeta

variable {p : Nat}

/-- `ζ_p ≠ 1` for `p ≥ 2`. -/
theorem zeta_ne_one (hp : 2 ≤ p) : zeta p ≠ 1 := by
  intro h
  apply zeta_pow_ne_one (m := p) (k := 1) (by decide) (by omega)
  rw [C.pow_eq_rpow, rpow_one', h]

/-- `ζ_p^a ≠ 1` when `p ∤ a`. -/
theorem zeta_rpow_ne_one (hp : 2 ≤ p) {a : Nat} (ha : ¬ p ∣ a) : rpow (zeta p) a ≠ 1 := by
  intro h
  have hpow : rpow (zeta p) p = 1 := zeta_rpow_self (by omega)
  have h' : rpow (zeta p) (a % p) = 1 := by
    rw [← h]; exact (pow_mod_of_pow_eq_one (R := ℂ) hpow a).symm
  apply zeta_pow_ne_one (m := p) (k := a % p)
  · rcases Nat.eq_zero_or_pos (a % p) with h0 | h0
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) ha
    · exact h0
  · exact Nat.mod_lt _ (by omega)
  · rw [C.pow_eq_rpow]; exact h'

/-- A `p`-th root of unity `ω ≠ 1` in `ℂ` satisfies `1 + ω + ⋯ + ω^{p-1} = 0`. -/
theorem rsum_root_of_unity {ω : ℂ} (hω : rpow ω p = 1) (hω1 : ω ≠ 1) :
    rsum (fun j => rpow ω j) p = 0 := by
  have h : (ω + -1) * rsum (fun j => rpow ω j) p = rpow ω p + -1 := geom_sum_mul ω p
  rw [hω, Ring.add_neg_cancel] at h
  rcases C.isDomain.2 _ _ h with h1 | h1
  · exact absurd (by grind) hω1
  · exact h1

/-- `Φ_p` over `ℚ` evaluated at a complex number `γ`: `Φ_p(γ) = 1 + γ + ⋯ + γ^{p-1}`. -/
theorem aeval_cyclo (γ : ℂ) (n : Nat) : aeval Qc γ (cyclo Qc n) = rsum (fun j => rpow γ j) n := by
  unfold aeval; rw [mapPoly_cyclo, eval_cyclo]; rfl

/-- `Φ_p(ζ_p^a) = 0` for `p ∤ a`. -/
theorem aeval_cyclo_zeta_pow (hp : 2 ≤ p) {a : Nat} (ha : ¬ p ∣ a) :
    aeval Qc (rpow (zeta p) a) (cyclo Qc p) = 0 := by
  rw [aeval_cyclo]
  apply rsum_root_of_unity _ (zeta_rpow_ne_one hp ha)
  rw [← rpow_mul', Nat.mul_comm, rpow_mul', zeta_rpow_self (by omega), one_rpow']

/-- `ζ_p` is algebraic over `ℚ`: a root of `Φ_p`. -/
theorem zeta_isAlgebraic (hp : IsPrime p) : IsAlgebraic Qc (zeta p) := by
  refine ⟨cyclo Qc p, cyclo_ne_zero (Qc.isField C.isField).1 (by have := hp.1; omega), ?_⟩
  have := aeval_cyclo_zeta_pow hp.1 (a := 1)
    (fun h => by have := Nat.le_of_dvd (by decide) h; have := hp.1; omega)
  rwa [rpow_one'] at this

end Zeta

/-! ## The field and its generator -/

section Field

variable {p : Nat} (hp : IsPrime p)

/-- **The cyclotomic field `ℚ(ζ_p)`** inside `ℂ`, generated over `ℚ` by `ζ_p = e^{2πi/p}`. -/
noncomputable def cycloField : Subfield ℂ := adjoin C.isField Qc (zeta p) (zeta_isAlgebraic hp)

/-- `ℚ ⊆ ℚ(ζ_p)`. -/
theorem Qc_le_cycloField : Qc.le (cycloField hp) := le_adjoin _ _ _ _

/-- `ζ_p ∈ ℚ(ζ_p)`. -/
theorem zeta_mem : zeta p ∈ cycloField hp := mem_adjoin_self _ _ _ _

/-- `ℚ(ζ_p)` is a finite extension of `ℚ`. -/
theorem cycloField_finite : FiniteExt Qc (cycloField hp) (Qc_le_cycloField hp) :=
  adjoin_finite _ _ _ _

include hp in
/-- **The minimal polynomial of `ζ_p` is `Φ_p`.** A rational polynomial vanishes at `ζ_p`
exactly when it is a multiple of `Φ_p`. -/
theorem aeval_zeta_eq_zero_iff (f : Polynomial Qc) :
    aeval Qc (zeta p) f = 0 ↔ Divides (cyclo Qc p) f := by
  obtain ⟨m, hm0, hm⟩ := exists_minpoly Qc (zeta p) C.isField (zeta_isAlgebraic hp)
  have hirr : Irreducible (cyclo Qc p) := cyclo_irreducible C.isField C.charZero hp
  have hΦ : aeval Qc (zeta p) (cyclo Qc p) = 0 := by
    have := aeval_cyclo_zeta_pow hp.1 (a := 1)
      (fun h => by have := Nat.le_of_dvd (by decide) h; have := hp.1; omega)
    rwa [rpow_one'] at this
  obtain ⟨c, hc⟩ := (hm _).1 hΦ
  -- `m` is not a unit, so `c` is
  have hmu : ¬ IsUnit m := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (aeval Qc (zeta p)) hu
    rw [aeval_mul, (hm m).2 ⟨1, (Ring.mul_one m).symm⟩, Ring.zero_mul, aeval_one] at h1
    exact C.isField.1 h1
  obtain ⟨d, hd⟩ : IsUnit c := (hirr.2.2 m c hc).resolve_left hmu
  have hmΦ : m = cyclo Qc p * d := by
    rw [hc, Ring.mul_assoc, hd, Ring.mul_one]
  constructor
  · intro h
    obtain ⟨e, he⟩ := (hm f).1 h
    exact ⟨d * e, by rw [he, hmΦ, Ring.mul_assoc]⟩
  · rintro ⟨e, rfl⟩
    rw [aeval_mul, hΦ, Ring.zero_mul]

include hp in
/-- **Conjugates of `ζ_p`.** Every rational polynomial vanishing at `ζ_p` also vanishes at
`ζ_p^a` for `p ∤ a`. -/
theorem aeval_zeta_pow_eq_zero {a : Nat} (ha : ¬ p ∣ a) {f : Polynomial Qc}
    (hf : aeval Qc (zeta p) f = 0) : aeval Qc (rpow (zeta p) a) f = 0 := by
  obtain ⟨e, rfl⟩ := (aeval_zeta_eq_zero_iff hp f).1 hf
  rw [aeval_mul, aeval_cyclo_zeta_pow hp.1 ha, Ring.zero_mul]

/-- Integers lie in every subfield. -/
theorem icast_mem (K : Subfield ℂ) : ∀ z : Int, (icast z : ℂ) ∈ K
  | .ofNat n => ncast_mem K n
  | .negSucc n => K.neg_mem (ncast_mem K (n + 1))
where
  /-- Natural numbers lie in every subfield. -/
  ncast_mem (K : Subfield ℂ) : ∀ n : Nat, (ncast n : ℂ) ∈ K
    | 0 => K.zero_mem
    | 1 => K.one_mem
    | n + 2 => K.add_mem (ncast_mem K (n + 1)) K.one_mem

/-- Finite sums of elements of a subfield lie in it. -/
theorem rsum_mem (K : Subfield ℂ) (t : Nat → ℂ) (ht : ∀ k, t k ∈ K) : ∀ n, rsum t n ∈ K
  | 0 => K.zero_mem
  | n + 1 => K.add_mem (rsum_mem K t ht n) (ht n)

/-- The Gauss sum `g = Σ_a (a/p) ζ_p^a` lies in `ℚ(ζ_p)`. -/
theorem gaussSum_mem : gaussSum p (zeta p) ∈ cycloField hp :=
  rsum_mem _ _ (fun a => (cycloField hp).mul_mem (icast_mem _ _)
    (rpow_mem (zeta_mem hp) a)) p

/-- **`√p*` lies in `ℚ(ζ_p)`.** For an odd prime `p`, the cyclotomic field `ℚ(ζ_p)` contains a
square root of `p* = (-1)^((p-1)/2) p`, namely the Gauss sum. -/
theorem sqrt_pstar_mem (hodd : p % 2 = 1) :
    ∃ s : ℂ, s ∈ cycloField hp ∧ s * s = icast (pstar p) :=
  ⟨gaussSum p (zeta p), gaussSum_mem hp, gaussSum_sq_complex hp hodd⟩

end Field

end Foundations.Langlands
