import Foundations.Langlands.Cyclotomic.Irreducible
import Foundations.Langlands.Cyclotomic.Reciprocity
import Foundations.Langlands.Cyclotomic.Frobenius

/-!
# Irreducibility of `Φ_{p^{k+1}}` over `ℚ`

For a prime power `n = p^{k+1}` the primitive `n`-th roots of unity are the roots of

  `Φ_n(x) = Φ_p(x^{p^k}) = 1 + x^{p^k} + x^{2p^k} + ⋯ + x^{(p-1)p^k}`,

of degree `φ(n) = (p - 1)p^k`. Indeed `(x^{p^k} - 1) Φ_n(x) = x^n - 1`, and the roots of
`x^{p^k} - 1` are the non-primitive ones. Eisenstein's argument extends. The polynomial
`T(x) = Φ_n(x + 1) = Σ_{j<p} (x + 1)^{j p^k}` has integer coefficients and is monic of degree
`(p-1)p^k`. Its constant term is `T(0) = p`, and modulo `p`

  `T(x) ≡ Σ_j (x^{p^k} + 1)^j = ((x^{p^k} + 1)^p - 1)/x^{p^k} ≡ x^{(p-1)p^k}`,

because `(x + 1)^{p^k} ≡ x^{p^k} + 1` in characteristic `p` (freshman's dream). So every
non-leading coefficient of `T` is divisible by `p` and Eisenstein's criterion applies.

The reduction is computed in `𝔽_p[x]`: there `(X + 1)^p = X^p + 1`, and the identity
`Y · T̄ = Y^p` with `Y = X^{p^k}` is cancelled in the domain `𝔽_p[x]`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial

universe u v

section Def

variable {R : Type u} [CommRing R]

/-- **The cyclotomic polynomial of a prime power** `Φ_{p^{k+1}} = Σ_{j<p} X^{j p^k}`. -/
noncomputable def cycloPP (R : Type u) [CommRing R] (p k : Nat) : Polynomial R :=
  rsum (fun j => (X : Polynomial R) ^ (j * p ^ k)) p

/-- `(X^{p^k} - 1) Φ_{p^{k+1}} = X^{p^{k+1}} - 1`. -/
theorem X_pow_sub_one_mul_cycloPP (p k : Nat) :
    ((X : Polynomial R) ^ (p ^ k) + -1) * cycloPP R p k = X ^ (p ^ (k + 1)) + -1 := by
  have h := geom_sum_mul ((X : Polynomial R) ^ (p ^ k)) p
  rw [← pow_mul'] at h
  rw [Nat.pow_succ, ← h]
  unfold cycloPP
  congr 1
  apply rsum_congr; intro j _
  rw [← pow_mul', Nat.mul_comm]

/-- Mapping coefficients: `Φ_{p^{k+1}}` over `A` maps to `Φ_{p^{k+1}}` over `B`. -/
theorem mapPoly_cycloPP {S : Type v} [CommRing S] (φ : RingHom R S) (p k : Nat) :
    mapPoly φ (cycloPP R p k) = cycloPP S p k := by
  show (mapHom φ).toFun _ = _
  unfold cycloPP
  rw [RingHom.map_rsum]
  apply rsum_congr; intro j _
  rw [RingHom.map_pow']
  show mapPoly φ X ^ _ = _
  rw [mapPoly_X]

/-- Evaluating `Φ_{p^{k+1}}`. -/
theorem eval_cycloPP (x : R) (p k : Nat) :
    eval x (cycloPP R p k) = rsum (fun j => x ^ (j * p ^ k)) p := by
  show (evalHom x).toFun _ = _
  unfold cycloPP
  rw [RingHom.map_rsum]
  apply rsum_congr; intro j _
  rw [RingHom.map_pow']
  show eval x X ^ _ = _
  rw [eval_X]

end Def

/-! ## Degrees of sums of powers -/

section Degrees

variable {R : Type u} [CommRing R]

/-- `deg` bounds add. -/
theorem degLT_add {f g : Polynomial R} {d : Nat} (hf : DegLT f d) (hg : DegLT g d) :
    DegLT (f + g) d := fun n hn => by rw [coeff_add, hf n hn, hg n hn, Ring.add_zero]

/-- `(X + 1)^e` has degree `≤ e` with leading coefficient `1` and constant term `1`. -/
theorem X_add_one_pow (e : Nat) : DegLT ((X : Polynomial R) + 1) 2 ∧
    DegLT (((X : Polynomial R) + 1) ^ e) (e + 1) ∧ coeff (((X : Polynomial R) + 1) ^ e) e = 1 ∧
    coeff (((X : Polynomial R) + 1) ^ e) 0 = 1 := by
  have h1 : DegLT ((X : Polynomial R) + 1) 2 := fun n hn => by
    rw [coeff_add, coeff_X, coeff_one, ite_false_of (by omega), ite_false_of (by omega),
      Ring.add_zero]
  have c1 : coeff ((X : Polynomial R) + 1) 1 = 1 := by
    rw [coeff_add, coeff_X, coeff_one, ite_true_of rfl, ite_false_of (by omega), Ring.add_zero]
  have c0 : coeff ((X : Polynomial R) + 1) 0 = 1 := by
    rw [coeff_add, coeff_X, coeff_one, ite_false_of (by omega), ite_true_of rfl, Ring.zero_add]
  refine ⟨h1, ?_⟩
  induction e with
  | zero =>
    refine ⟨fun n hn => ?_, ?_, ?_⟩
    · show coeff 1 n = 0; rw [coeff_one, ite_false_of (by omega)]
    · show coeff 1 0 = 1; rw [coeff_one, ite_true_of rfl]
    · show coeff 1 0 = 1; rw [coeff_one, ite_true_of rfl]
  | succ e ih =>
    obtain ⟨hd, hc, hc0⟩ := ih
    have := mul_top (s := e) (t := 1) hd h1
    refine ⟨this.2, ?_, ?_⟩
    · show coeff (((X : Polynomial R) + 1) ^ e * (X + 1)) (e + 1) = 1
      rw [this.1, hc, c1, Ring.mul_one]
    · show coeff (((X : Polynomial R) + 1) ^ e * (X + 1)) 0 = 1
      rw [coeff_mul_sum]
      show 0 + coeff _ 0 * coeff _ (0 - 0) = 1
      rw [hc0, Nat.sub_self, c0, Ring.mul_one, Ring.zero_add]

/-- **`Φ_{p^{k+1}}(x + 1)` over any ring**: `T = Σ_{j<p} (X + 1)^{j p^k}`. -/
noncomputable def shiftedPP (R : Type u) [CommRing R] (p k : Nat) : Polynomial R :=
  rsum (fun j => ((X : Polynomial R) + 1) ^ (j * p ^ k)) p

/-- The substitution `x ↦ x + 1` turns `Φ_{p^{k+1}}` into `T`. -/
theorem shiftHom_cycloPP (p k : Nat) :
    (shiftHom (1 : R)).toFun (cycloPP R p k) = shiftedPP R p k := by
  unfold cycloPP shiftedPP
  rw [RingHom.map_rsum]
  apply rsum_congr; intro j _
  rw [RingHom.map_pow', shiftHom_X, C_one]

/-- Mapping coefficients commutes with forming `T`. -/
theorem mapPoly_shiftedPP {S : Type v} [CommRing S] (φ : RingHom R S) (p k : Nat) :
    mapPoly φ (shiftedPP R p k) = shiftedPP S p k := by
  show (mapHom φ).toFun _ = _
  unfold shiftedPP
  rw [RingHom.map_rsum]
  apply rsum_congr; intro j _
  rw [RingHom.map_pow', (mapHom φ).map_add, (mapHom φ).map_one]
  show (mapPoly φ X + 1) ^ _ = _
  rw [mapPoly_X]

/-- `T` is monic of degree `(p - 1) p^k`, with constant term `p`. -/
theorem shiftedPP_deg {p : Nat} (hp : 2 ≤ p) (k : Nat) :
    DegLT (shiftedPP R p k) ((p - 1) * p ^ k + 1) ∧
      coeff (shiftedPP R p k) ((p - 1) * p ^ k) = 1 ∧
      coeff (shiftedPP R p k) 0 = (((p : Nat) : Int) : R) := by
  have hm : 1 ≤ p ^ k := Nat.pow_pos (by omega)
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  rw [show r + 1 - 1 = r by omega]
  have hlow : ∀ j, j < r → DegLT (((X : Polynomial R) + 1) ^ (j * (r + 1) ^ k)) (r * (r + 1) ^ k) :=
    fun j hj => (X_add_one_pow (R := R) _).2.1.mono (by
      have : (j + 1) * (r + 1) ^ k ≤ r * (r + 1) ^ k := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega)
  have hsumlow : ∀ n, n ≤ r → DegLT (rsum (fun j => ((X : Polynomial R) + 1) ^ (j * (r + 1) ^ k)) n)
      (r * (r + 1) ^ k) := by
    intro n
    induction n with
    | zero => intro _ m _; exact coeff_zero m
    | succ n ih => intro hn; exact degLT_add (ih (by omega)) (hlow n (by omega))
  have htop := X_add_one_pow (R := R) (r * (r + 1) ^ k)
  refine ⟨?_, ?_, ?_⟩
  · show DegLT (rsum _ r + _) _
    exact degLT_add ((hsumlow r (Nat.le_refl r)).mono (by omega)) htop.2.1
  · show coeff (rsum _ r + _) _ = 1
    rw [coeff_add, hsumlow r (Nat.le_refl r) _ (Nat.le_refl _), htop.2.2.1, Ring.zero_add]
  · unfold shiftedPP
    rw [coeff_rsum, rsum_congr _ fun j _ => (X_add_one_pow (R := R) (j * (r + 1) ^ k)).2.2.2,
      rsum_const, Ring.mul_one]

end Degrees

/-! ## Reduction modulo `p` -/

section ModP

variable {p : Nat} (hp : IsPrime p)

include hp in
/-- **`T ≡ x^{(p-1)p^k} (mod p)`.** In `𝔽_p[x]`, `Φ_{p^{k+1}}(x + 1) = x^{(p-1)p^k}`. -/
theorem shiftedPP_mod_p (k : Nat) :
    haveI : NeZero p := ⟨by have := hp.1; omega⟩
    shiftedPP (Fin p) p k = (X : Polynomial (Fin p)) ^ ((p - 1) * p ^ k) := by
  haveI : NeZero p := ⟨by have := hp.1; omega⟩
  have hF : IsField (Fin p) := (fin_isField_iff_prime p).2 hp
  have hD := Polynomial.isDomain hF.isDomain
  -- characteristic `p` in `𝔽_p[x]`
  have hchar : (((p : Nat) : Int) : Polynomial (Fin p)) = 0 := by
    rw [← RingHom.map_intCast (CHom (R := Fin p))]
    show C (icast (p : Int) : Fin p) = 0
    rw [fin_icast_self, C_zero]
  -- `(X + 1)^{p^k} = X^{p^k} + 1`
  have hfrob : ∀ k, ((X : Polynomial (Fin p)) + 1) ^ (p ^ k) = X ^ (p ^ k) + 1 := by
    intro k
    induction k with
    | zero => show 1 * (X + 1) = 1 * X + 1; rw [Ring.one_mul, Ring.one_mul]
    | succ k ih =>
      rw [Nat.pow_succ, pow_mul', ih, add_pow_char hp hchar, one_pow', ← pow_mul']
  let Y : Polynomial (Fin p) := X ^ (p ^ k)
  have hT : shiftedPP (Fin p) p k = rsum (fun j => (Y + 1) ^ j) p := by
    unfold shiftedPP
    apply rsum_congr; intro j _
    rw [Nat.mul_comm, pow_mul', hfrob]
  have hgeom := geom_sum_mul (Y + 1) p
  rw [← hT, add_pow_char hp hchar, one_pow'] at hgeom
  have hY0 : Y ≠ 0 := by
    intro h
    have : coeff Y (p ^ k) = 1 := by
      show coeff (X ^ (p ^ k)) (p ^ k) = 1
      rw [X_pow_eq_Xpow, ← Ring.mul_one (Xpow _), coeff_Xpow_mul, ite_true_of (Nat.le_refl _),
        Nat.sub_self, coeff_one, ite_true_of rfl]
    rw [h, coeff_zero] at this; exact hF.1 this
  apply hD.mul_left_cancel hY0
  have e1 : Y + 1 + -1 = Y := by grind
  rw [e1] at hgeom
  rw [hgeom]
  have e2 : Y ^ p = Y * (X : Polynomial (Fin p)) ^ ((p - 1) * p ^ k) := by
    show (X ^ (p ^ k)) ^ p = X ^ (p ^ k) * X ^ ((p - 1) * p ^ k)
    rw [← pow_mul', ← pow_add']
    congr 1
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by have := hp.1; omega⟩
    rw [show r + 1 - 1 = r by omega, Nat.mul_comm, Nat.add_mul, Nat.one_mul]; omega
  rw [e2]; grind

end ModP

/-! ## Irreducibility -/

/-- In `ℤ` itself, the ring-theoretic cast of a natural number is the number. -/
theorem ncast_int : ∀ n : Nat, (ncast n : Int) = (n : Int)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show (ncast (n + 1) : Int) + 1 = _
    rw [ncast_int (n + 1)]; omega

section Irreducible

variable {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω) (hc : CharZero Ω)

include hΩ hc in
/-- **Irreducibility of `Φ_{p^{k+1}}` over `ℚ`.** For a prime `p` and `k ≥ 0`, the cyclotomic
polynomial `Φ_{p^{k+1}}(x) = Σ_{j<p} x^{j p^k}` is irreducible in `ℚ[x]` (`ℚ` the prime field of
a field of characteristic zero). (Eisenstein's criterion at `p` for `Φ_{p^{k+1}}(x + 1)`.) -/
theorem cycloPP_irreducible {p : Nat} (hp : IsPrime p) (k : Nat) :
    Irreducible (cycloPP (ratField hΩ hc) p k) := by
  let K := ratField hΩ hc
  have h2 := hp.1
  haveI : NeZero p := ⟨by omega⟩
  apply irreducible_of_shift (1 : K)
  rw [shiftHom_cycloPP, ← mapPoly_shiftedPP (icastHom K)]
  let T := shiftedPP Int p k
  obtain ⟨hTd, hTc, hT0⟩ := shiftedPP_deg (R := Int) hp.1 k
  have hmod := shiftedPP_mod_p hp k
  rw [← mapPoly_shiftedPP (icastHom (Fin p))] at hmod
  have hm : 1 ≤ p ^ k := Nat.pow_pos (by omega)
  refine eisenstein_irreducible hΩ hc hp (mapPoly (icastHom K) T) (F := fun i => coeff T i)
    (n := (p - 1) * p ^ k) (Nat.mul_pos (by omega) hm |> fun h => h) ?_ ?_ hTc ?_ ?_
  · intro i
    rw [coeff_mapPoly]
    exact Subfield.coe_intCast K _
  · intro i hi; exact hTd i hi
  · intro i hi
    apply dvd_of_fin_icast_eq_zero (q := p)
    have := congrArg (fun f => coeff f i) hmod
    simp only [coeff_mapPoly] at this
    rw [X_pow_eq_Xpow, ← Ring.mul_one (Xpow _), coeff_Xpow_mul, ite_false_of (by omega)] at this
    exact this
  · rw [hT0]
    show ¬ (p : Int) * p ∣ (ncast p : Int)
    rw [ncast_int]
    intro ⟨c, hc'⟩
    have hp0 : (p : Int) ≠ 0 := by omega
    have e : (p : Int) * 1 = p * (p * c) := by rw [Int.mul_one, ← Int.mul_assoc]; exact hc'
    have e1 : (1 : Int) = p * c := Int.eq_of_mul_eq_mul_left hp0 e
    have : (p : Int) ∣ 1 := ⟨c, e1⟩
    have := Int.le_of_dvd (by decide) this
    omega

end Irreducible

end Foundations.Langlands
