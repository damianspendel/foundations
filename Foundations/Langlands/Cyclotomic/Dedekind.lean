import Foundations.Langlands.Cyclotomic.CyclotomicN

/-!
# Dedekind's lemma: `ζ ↦ ζ^p` preserves minimal polynomials

**Theorem (Dedekind 1857).** Let `ω ∈ ℂ` be an `n`-th root of unity and `p` a prime not
dividing `n`. Every rational polynomial vanishing at `ω` vanishes at `ω^p`
(`dedekind_step`). Iterating over the prime factors of `a`, every rational polynomial vanishing
at `ζ_n` vanishes at every primitive root `ζ_n^a`, `gcd(a, n) = 1`
(`aeval_zeta_pow_of_coprime`).

The proof is the one in van der Waerden's *Moderne Algebra*, going back to Dedekind and
simplified by Landau. Let `P` and `Q` be the monic minimal polynomials of `ω` and `ω^p` over
`ℚ`, and suppose `P(ω^p) ≠ 0`. Then

* `P ≠ Q`, so the coprime irreducibles `P` and `Q` both divide `xⁿ - 1 = P Q S`;
* `P`, `Q` and `S` have integer coefficients (Gauss's lemma for monic factors,
  `MonicPoly.lean`);
* `ω` is a root of `Q(x^p)`, so `Q(x^p) = P T` with `T` integral.

Reduce modulo `p`. In `𝔽_p[x]` the substitution `x ↦ x^p` on coefficients from `𝔽_p` is the
`p`-th power map, so `Q̄^p = P̄ T̄`. An irreducible factor `π` of `P̄` therefore divides `Q̄`,
and `π² ∣ P̄ Q̄ ∣ xⁿ - 1`. Since `p ∤ n`, the polynomial `xⁿ - 1` is separable over `𝔽_p`
(`isUnit_of_sq_dvd_X_pow_sub_one`), a contradiction.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Generalities -/

/-- `xⁿ - 1` is compatible with ring homomorphisms. -/
theorem mapPoly_X_pow_sub_one {A B : Type} [CommRing A] [CommRing B] (φ : RingHom A B) (n : Nat) :
    mapPoly φ ((X : Polynomial A) ^ n + -1) = (X : Polynomial B) ^ n + -1 := by
  show (mapHom φ).toFun _ = _
  rw [(mapHom φ).map_add, (mapHom φ).map_neg, (mapHom φ).map_one, RingHom.map_pow']
  show mapPoly φ X ^ n + -1 = _
  rw [mapPoly_X]

/-- Evaluating `xⁿ - 1` over `ℚ` at a complex number. -/
theorem aeval_X_pow_sub_one (ω : ℂ) (n : Nat) :
    aeval Qc ω ((X : Polynomial Qc) ^ n + -1) = rpow ω n + -1 := by
  rw [aeval_add, aeval_neg, aeval_one]
  show (aevalHom Qc ω).toFun _ + _ = _
  rw [RingHom.map_pow']
  show rpow (aeval Qc ω X) n + _ = _
  rw [aeval_X]

/-- If an integer polynomial is monic over `ℚ`, it is monic over `ℤ`. -/
theorem Monic.of_map_icast {F : Polynomial Int} {d : Nat}
    (h : Monic (mapPoly (icastHom Qc) F) d) : Monic F d := by
  have key : ∀ k (z : Int), coeff (mapPoly (icastHom Qc) F) k = (icastHom Qc).toFun z →
      coeff F k = z := fun k z hk => by
    rw [coeff_mapPoly] at hk
    have := congrArg Subtype.val hk
    exact C.charZero.cast_inj
      ((Subfield.coe_intCast Qc _).symm.trans (this.trans (Subfield.coe_intCast Qc _)))
  exact ⟨fun k hk => key k 0 (by rw [h.1 k hk]; exact (icastHom Qc).map_zero.symm),
    key d 1 (by rw [h.2]; exact (icastHom Qc).map_one.symm)⟩

/-- Over `ℚ`, evaluating an integer polynomial at `ω` is evaluating it in `ℂ`. -/
theorem aeval_map_icast (ω : ℂ) (F : Polynomial Int) :
    aeval Qc ω (mapPoly (icastHom Qc) F) = eval ω (mapPoly (icastHom ℂ) F) := by
  unfold aeval
  rw [mapPoly_mapPoly]
  congr 1
  apply ext; intro k
  rw [coeff_mapPoly, coeff_mapPoly]
  exact Subfield.coe_intCast Qc _

/-- Gauss's lemma for monic factors (`int_of_monic_factor`), for `ℚ ⊆ ℂ`. -/
theorem int_of_monic_factor_Q {F : Polynomial Int} {f g : Polynomial Qc} {d e : Nat}
    (hf : Monic f d) (hg : Monic g e) (hF : mapPoly (icastHom Qc) F = f * g) :
    ∃ F₁ : Polynomial Int, mapPoly (icastHom Qc) F₁ = f :=
  int_of_monic_factor C.isField C.charZero hf hg hF

/-- Division by monic integer polynomials (`int_dvd_of_monic`), for `ℚ ⊆ ℂ`. -/
theorem int_dvd_of_monic_Q {P A : Polynomial Int} {d : Nat} (hP : Monic P d)
    (h : Divides (mapPoly (icastHom Qc) P) (mapPoly (icastHom Qc) A)) : ∃ T, A = P * T :=
  int_dvd_of_monic C.isField C.charZero hP h

/-- Mapping integer polynomials to `ℚ[x]` is injective (`mapPoly_icast_inj`), for `ℚ ⊆ ℂ`. -/
theorem mapPoly_icast_inj_Q {A B : Polynomial Int}
    (h : mapPoly (icastHom Qc) A = mapPoly (icastHom Qc) B) : A = B :=
  mapPoly_icast_inj C.isField C.charZero h

/-! ## Minimal polynomials over `ℚ` -/

/-- **Monic minimal polynomials.** An algebraic number `ω` has a monic minimal polynomial `P`
over `ℚ`: the rational polynomials vanishing at `ω` are exactly the multiples of `P`. -/
theorem exists_monic_minpoly {ω : ℂ} (hω : IsAlgebraic Qc ω) :
    ∃ P : Polynomial Qc, ∃ d, Monic P d ∧ ∀ q, aeval Qc ω q = 0 ↔ Divides P q := by
  obtain ⟨m, hm0, hm⟩ := exists_minpoly Qc ω C.isField hω
  have hF : IsField Qc := Qc.isField C.isField
  obtain ⟨b, hb⟩ := hF.2 _ (leadingCoeff_ne_zero hm0)
  have hCb : DegLT (C b) (0 + 1) := fun k hk => by rw [coeff_C, ite_false_of (by omega)]
  obtain ⟨h1, h2⟩ := mul_top (degLT_natDegree hm0) hCb
  have e1 : C b * C (leadingCoeff m) = 1 := by rw [← C_mul, CommRing.mul_comm, hb, C_one]
  refine ⟨m * C b, natDegree m, ⟨h2, ?_⟩, fun q => ?_⟩
  · show coeff (m * C b) (natDegree m + 0) = 1
    rw [h1, coeff_C_zero]; exact hb
  · rw [hm q]
    constructor
    · rintro ⟨e, rfl⟩
      refine ⟨C (leadingCoeff m) * e, ?_⟩
      calc m * e = m * (C b * C (leadingCoeff m) * e) := by rw [e1, Ring.one_mul]
        _ = m * C b * (C (leadingCoeff m) * e) := by rw [Ring.mul_assoc m, Ring.mul_assoc]
    · rintro ⟨e, rfl⟩
      exact ⟨C b * e, Ring.mul_assoc _ _ _⟩

/-- **Minimal polynomials are irreducible.** -/
theorem irreducible_of_minpoly {ω : ℂ} {P : Polynomial Qc}
    (hP : ∀ q, aeval Qc ω q = 0 ↔ Divides P q) (hP0 : P ≠ 0) : Irreducible P := by
  have hD : IsDomain (Polynomial Qc) := Polynomial.isDomain (Qc.isField C.isField).isDomain
  have hPω : aeval Qc ω P = 0 := (hP P).2 ⟨1, (Ring.mul_one P).symm⟩
  refine ⟨hP0, fun ⟨v, hv⟩ => ?_, fun a b hab => ?_⟩
  · have := congrArg (aeval Qc ω) hv
    rw [aeval_mul, hPω, Ring.zero_mul, aeval_one] at this
    exact C.isField.1 this
  · have h := hPω
    rw [hab, aeval_mul] at h
    rcases C.isDomain.2 _ _ h with h1 | h1
    · obtain ⟨c, hc⟩ := (hP a).1 h1
      right
      refine ⟨c, hD.mul_left_cancel hP0 ?_⟩
      rw [Ring.mul_one]
      calc P * (b * c) = a * b := by rw [hc]; grind
        _ = P := hab.symm
    · obtain ⟨c, hc⟩ := (hP b).1 h1
      left
      refine ⟨c, hD.mul_left_cancel hP0 ?_⟩
      rw [Ring.mul_one]
      calc P * (a * c) = a * b := by rw [hc]; grind
        _ = P := hab.symm

/-- An irreducible rational polynomial with root `ω` divides every rational polynomial with
root `ω`. -/
theorem dvd_of_irreducible_root {ω : ℂ} {P q : Polynomial Qc} (hP : Irreducible P)
    (hPω : aeval Qc ω P = 0) (hq : aeval Qc ω q = 0) : Divides P q := by
  obtain ⟨m, hm0, hm⟩ := exists_minpoly Qc ω C.isField ⟨P, hP.1, hPω⟩
  obtain ⟨c, hc⟩ := (hm P).1 hPω
  have hmu : ¬ IsUnit m := fun ⟨v, hv⟩ => by
    have := congrArg (aeval Qc ω) hv
    rw [aeval_mul, (hm m).2 ⟨1, (Ring.mul_one m).symm⟩, Ring.zero_mul, aeval_one] at this
    exact C.isField.1 this
  obtain ⟨c', hc'⟩ := (hP.2.2 m c hc).resolve_left hmu
  obtain ⟨e, he⟩ := (hm q).1 hq
  refine ⟨c' * e, ?_⟩
  rw [he, hc]
  calc m * e = m * (c * c') * e := by rw [hc', Ring.mul_one]
    _ = m * c * (c' * e) := by grind

/-! ## Reduction modulo `p` -/

/-- **Frobenius on `𝔽_p[x]`.** Reducing `f(x^p)` modulo `p` gives `f̄(x)^p`. -/
theorem redp_powSubst {p : Nat} [NeZero p] (hp : IsPrime p) (f : Polynomial Int) :
    mapPoly (icastHom (Fin p)) ((powSubst p).toFun f) = mapPoly (icastHom (Fin p)) f ^ p := by
  have hchar : (((p : Nat) : Int) : Polynomial (Fin p)) = 0 := by
    rw [← RingHom.map_intCast (CHom (R := Fin p))]
    show C (icast (p : Int) : Fin p) = 0
    rw [fin_icast_self, C_zero]
  let frob : RingHom (Polynomial (Fin p)) (Polynomial (Fin p)) :=
    { toFun := fun y => y ^ p
      map_add := add_pow_char hp hchar
      map_mul := fun x y => mul_pow' x y p
      map_one := one_pow' p }
  exact polyHom_ext (RingHom.comp (mapHom (icastHom (Fin p))) (powSubst p))
    (RingHom.comp frob (mapHom (icastHom (Fin p))))
    (fun c => by
      show mapPoly _ (eval _ (mapPoly CHom (C c))) = (mapPoly _ (C c)) ^ p
      rw [mapPoly_C, eval_C]
      show mapPoly (icastHom (Fin p)) (C c) = (mapPoly (icastHom (Fin p)) (C c)) ^ p
      rw [mapPoly_C]
      show C _ = CHom.toFun _ ^ p
      rw [← RingHom.map_pow' CHom]
      exact congrArg CHom.toFun (fin_pow_self hp _).symm)
    (by
      show mapPoly _ (eval _ (mapPoly CHom X)) = (mapPoly _ X) ^ p
      rw [mapPoly_X, eval_X, mapPoly_X]
      show (mapHom (icastHom (Fin p))).toFun (X ^ p) = _
      rw [RingHom.map_pow']
      show mapPoly _ X ^ p = _
      rw [mapPoly_X]) f

/-- **The contradiction modulo `p`.** Let `p ∤ n` be prime and `P, Q, S, T` integer
polynomials with `P` monic of degree `≥ 1`, `xⁿ - 1 = P Q S` and `Q(x^p) = P T`. This is
impossible: an irreducible factor of `P̄` would be a repeated factor of `xⁿ - 1` in `𝔽_p[x]`. -/
theorem dedekind_mod_p {n p d : Nat} (hp : IsPrime p) (hpn : ¬ p ∣ n) {P Q S T : Polynomial Int}
    (hd : 1 ≤ d) (hP : Monic P d) (hB : (X : Polynomial Int) ^ n + -1 = P * Q * S)
    (hT : (powSubst p).toFun Q = P * T) : False := by
  haveI : NeZero p := ⟨by have := hp.1; omega⟩
  have hF : IsField (Fin p) := (fin_isField_iff_prime p).2 hp
  have hD := hF.isDomain
  let ρ := mapHom (icastHom (Fin p))
  have hfrob : ρ.toFun ((powSubst p).toFun Q) = ρ.toFun Q ^ p := redp_powSubst hp Q
  rw [hT, ρ.map_mul] at hfrob
  have hPm : Monic (ρ.toFun P) d := hP.map _
  have hP0 := hPm.ne_zero hD.1
  have hPu : ¬ IsUnit (ρ.toFun P) :=
    not_isUnit_of_natDegree_pos hD hP0 (by rw [hPm.natDegree_eq hD.1]; omega)
  obtain ⟨π, hπ, a, ha⟩ := exists_irreducible_factor hF hP0 hPu
  have hπp := (polynomial_isPID hF).irreducible_isPrime hπ
  obtain ⟨b, hb⟩ : Divides π (ρ.toFun Q) :=
    IsPrimeElt.dvd_of_dvd_pow hπp p ⟨a * ρ.toFun T, by rw [← hfrob, ha, Ring.mul_assoc]⟩
  have hn : (icast ((n : Nat) : Int) : Fin p) ≠ 0 := fun h =>
    hpn (Int.ofNat_dvd.1 (dvd_of_fin_icast_eq_zero h))
  apply hπ.2.1
  apply isUnit_of_sq_dvd_X_pow_sub_one hF hn
  refine ⟨a * b * ρ.toFun S, ?_⟩
  have h := congrArg ρ.toFun hB
  rw [ρ.map_mul, ρ.map_mul, ha, hb] at h
  have e : (X : Polynomial (Fin p)) ^ n + -1 = ρ.toFun ((X : Polynomial Int) ^ n + -1) :=
    (mapPoly_X_pow_sub_one _ n).symm
  rw [e, h]
  grind

/-! ## Dedekind's lemma -/

/-- Evaluating `f(x^a)` at `ω` is evaluating `f` at `ω^a`. -/
theorem aeval_map_powSubst (ω : ℂ) (a : Nat) (F : Polynomial Int) :
    aeval Qc ω (mapPoly (icastHom Qc) ((powSubst a).toFun F)) =
      aeval Qc (rpow ω a) (mapPoly (icastHom Qc) F) := by
  exact polyHom_ext (RingHom.comp (aevalHom Qc ω) (RingHom.comp (mapHom (icastHom Qc)) (powSubst a)))
    (RingHom.comp (aevalHom Qc (rpow ω a)) (mapHom (icastHom Qc)))
    (fun c => by
      show aeval Qc ω (mapPoly _ (eval _ (mapPoly CHom (C c)))) = aeval Qc _ (mapPoly _ (C c))
      rw [mapPoly_C, eval_C]
      show aeval Qc ω (mapPoly _ (C c)) = _
      rw [mapPoly_C, aeval_C, aeval_C])
    (by
      show aeval Qc ω (mapPoly _ (eval _ (mapPoly CHom X))) = aeval Qc _ (mapPoly _ X)
      rw [mapPoly_X, eval_X, mapPoly_X, aeval_X]
      show (aevalHom Qc ω).toFun ((mapHom (icastHom Qc)).toFun (X ^ a)) = _
      rw [RingHom.map_pow', RingHom.map_pow']
      show rpow (aeval Qc ω (mapPoly _ X)) a = _
      rw [mapPoly_X, aeval_X]) F

/-- **Dedekind's lemma.** Let `ω ∈ ℂ` with `ωⁿ = 1` (`n ≥ 1`) and let `p` be a prime not
dividing `n`. Every rational polynomial vanishing at `ω` vanishes at `ω^p`. -/
theorem dedekind_step {n : Nat} (hn : 1 ≤ n) {ω : ℂ} (hω : rpow ω n = 1) {p : Nat}
    (hp : IsPrime p) (hpn : ¬ p ∣ n) {f : Polynomial Qc} (hf : aeval Qc ω f = 0) :
    aeval Qc (rpow ω p) f = 0 := by
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  let B : Polynomial Int := X ^ n + -1
  have hBQ : mapPoly (icastHom Qc) B = X ^ n + -1 := mapPoly_X_pow_sub_one _ n
  have hBm : Monic (mapPoly (icastHom Qc) B) n := by rw [hBQ]; exact monic_X_pow_sub_one hn
  have hB0 := hBm.ne_zero hD.1
  have hroot : ∀ x : ℂ, rpow x n = 1 → aeval Qc x (mapPoly (icastHom Qc) B) = 0 := fun x hx => by
    rw [hBQ, aeval_X_pow_sub_one, hx]; exact Ring.add_neg_cancel _
  have hωp : rpow (rpow ω p) n = 1 := by rw [← rpow_mul', Nat.mul_comm, rpow_mul', hω, one_rpow']
  obtain ⟨P, d, hPm, hP⟩ := exists_monic_minpoly ⟨_, hB0, hroot ω hω⟩
  obtain ⟨Q, e, hQm, hQ⟩ := exists_monic_minpoly ⟨_, hB0, hroot _ hωp⟩
  obtain ⟨g, rfl⟩ := (hP f).1 hf
  rw [aeval_mul]
  suffices h : aeval Qc (rpow ω p) P = 0 by rw [h, Ring.zero_mul]
  apply Classical.byContradiction; intro hPne
  -- `xⁿ - 1 = P Q S` over `ℚ`
  obtain ⟨R, hR⟩ := (hP _).1 (hroot ω hω)
  have hQp := (polynomial_isPID (Qc.isField C.isField)).irreducible_isPrime
    (irreducible_of_minpoly hQ (hQm.ne_zero hD.1))
  obtain ⟨S, hS⟩ : Divides Q R := by
    rcases hQp.2.2 P R (hR ▸ (hQ _).1 (hroot _ hωp)) with h | h
    · exact absurd ((hQ P).2 h) hPne
    · exact h
  obtain ⟨_, hRm⟩ := hPm.of_mul hD hBm hR.symm
  obtain ⟨_, hSm⟩ := hQm.of_mul hD hRm hS.symm
  -- integrality
  obtain ⟨PZ, hPZ⟩ := int_of_monic_factor_Q hPm hRm hR
  obtain ⟨QZ, hQZ⟩ := int_of_monic_factor_Q hQm (hPm.mul hSm)
    (by rw [hR, hS]; grind)
  have hPZm : Monic PZ d := Monic.of_map_icast (hPZ ▸ hPm)
  have hQZm : Monic QZ e := Monic.of_map_icast (hQZ ▸ hQm)
  obtain ⟨SZ, hSZ⟩ := int_dvd_of_monic_Q (hPZm.mul hQZm) (P := PZ * QZ) (A := B)
    ⟨S, by
      show mapPoly (icastHom Qc) B = (mapHom (icastHom Qc)).toFun (PZ * QZ) * S
      rw [(mapHom (icastHom Qc)).map_mul]
      show _ = mapPoly (icastHom Qc) PZ * mapPoly (icastHom Qc) QZ * S
      rw [hPZ, hQZ, hR, hS, Ring.mul_assoc]⟩
  obtain ⟨T, hT⟩ := int_dvd_of_monic_Q hPZm (A := (powSubst p).toFun QZ)
    (by
      show Divides (mapPoly (icastHom Qc) PZ) _
      rw [hPZ]
      apply (hP _).1
      rw [aeval_map_powSubst, hQZ]
      exact (hQ Q).2 ⟨1, (Ring.mul_one Q).symm⟩)
  -- `deg P ≥ 1`
  have hd : 1 ≤ d := by
    apply Classical.byContradiction; intro h0
    have hd0 : d = 0 := by omega
    subst hd0
    have := (hP P).2 ⟨1, (Ring.mul_one P).symm⟩
    rw [hPm.eq_one, aeval_one] at this
    exact C.isField.1 this.symm
  exact dedekind_mod_p hp hpn hd hPZm hSZ hT

/-- `ζ_1 = 1`. -/
theorem zeta_one : zeta 1 = 1 := by
  have := zeta_rpow_self (p := 1) (Nat.le_refl 1)
  rwa [rpow_one'] at this

/-- **Conjugates of `ζ_n`.** Every rational polynomial vanishing at `ζ_n` vanishes at every
primitive `n`-th root of unity `ζ_n^a`, `gcd(a, n) = 1`. -/
theorem aeval_zeta_pow_of_coprime {n : Nat} (hn : 1 ≤ n) {f : Polynomial Qc}
    (hf : aeval Qc (zeta n) f = 0) : ∀ a, Nat.Coprime a n → aeval Qc (rpow (zeta n) a) f = 0 := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro ha
    rcases Nat.lt_or_ge a 2 with h2 | h2
    · rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
      · have hn1 : n = 1 := (Nat.coprime_zero_left n).1 ha
        subst hn1
        show aeval Qc 1 f = 0
        rw [← zeta_one]; exact hf
      · rw [rpow_one']; exact hf
    · obtain ⟨p, hp, b, rfl⟩ := exists_prime_factor h2
      have hb : b < p * b := by
        have := hp.1
        have hb0 : 0 < b := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at h2; omega
        calc b = 1 * b := (Nat.one_mul b).symm
          _ < p * b := Nat.mul_lt_mul_of_pos_right (by omega) hb0
      have hbn : Nat.Coprime b n := Nat.Coprime.coprime_dvd_left ⟨p, Nat.mul_comm p b⟩ ha
      have hpn : ¬ p ∣ n := fun h => by
        have h1 : p ∣ Nat.gcd (p * b) n := Nat.dvd_gcd ⟨b, rfl⟩ h
        have h2 : Nat.gcd (p * b) n = 1 := ha
        rw [h2] at h1
        have := Nat.le_of_dvd (by decide) h1
        have := hp.1
        omega
      have hω : rpow (rpow (zeta n) b) n = 1 := by
        rw [← rpow_mul', Nat.mul_comm, rpow_mul', zeta_rpow_self hn, one_rpow']
      have := dedekind_step hn hω hp hpn (ih b hb hbn)
      rwa [← rpow_mul', Nat.mul_comm] at this

end Foundations.Langlands
