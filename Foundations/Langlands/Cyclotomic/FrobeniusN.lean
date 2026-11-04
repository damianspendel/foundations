import Foundations.Langlands.Cyclotomic.GaloisN

/-!
# `σ_q` is the Frobenius at `q`, for every `n ≥ 1`

This file extends `Frobenius.lean` from prime `p` to arbitrary `n ≥ 1`, using the integer
cyclotomic polynomial `Φ_n = cycloZ n` of `IrreducibleN.lean`.

* **The ring `ℤ[ζ_n]`** is the image of evaluation `ℤ[x] → ℂ`, `f ↦ f(ζ_n)` (`intZeta n`, as in
  `Frobenius.lean`). It lies in `ℚ(ζ_n)`.
* **The kernel of evaluation** consists of the integer multiples of `Φ_n`
  (`dvd_cycloZ_of_evZeta`). `Φ_n` is monic with integer coefficients and is the minimal
  polynomial of `ζ_n` over `ℚ`, so `Φ_n ∣ f` over `ℚ` and then over `ℤ`.
* **Reduction modulo `q`.** Hence `f(ζ_n) ↦ f mod (q, Φ_n)` is a well-defined ring homomorphism
  `ℤ[ζ_n] → A_n = 𝔽_q[x]/(Φ̄_n)` with `ζ_n ↦ x` (`reduceN`). The ring `A_n` is not zero,
  because `Φ̄_n` is monic of degree `φ(n) ≥ 1` (`resRingN_nontrivial`).
* **Frobenius.** For a prime `q ∤ n` and `α = f(ζ_n)`, `σ_q(α) = f(ζ_n^q)` reduces to
  `f̄(x^q) = f̄(x)^q`. So **`σ_q(α) ≡ α^q (mod q)`** for every `α ∈ ℤ[ζ_n]`
  (`reduceN_galAut`).

As in `Frobenius.lean`, we do not prove that `A_n ≅ ℤ[ζ_n]/(q)`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## `ℤ[ζ_n]` -/

section IntZetaN

variable {n : Nat} (hn : 1 ≤ n)

/-- `ℤ[ζ_n] ⊆ ℚ(ζ_n)`. -/
theorem intZeta_leN {α : ℂ} (hα : α ∈ intZeta n) : α ∈ cycloFieldN hn := by
  obtain ⟨f, rfl⟩ := hα
  rw [evZeta_eq_aeval]
  exact aeval_mem Qc (zeta n) (Qc_le_cycloFieldN hn) (zetaN_mem hn) _

include hn in
/-- **The kernel of evaluation at `ζ_n` consists of multiples of `Φ_n`.** If `f ∈ ℤ[x]` and
`f(ζ_n) = 0`, then `f = Q · Φ_n` for some `Q ∈ ℤ[x]`. -/
theorem dvd_cycloZ_of_evZeta {f : Polynomial Int} (hf : (evZeta n).toFun f = 0) :
    ∃ Q, f = Q * cycloZ n := by
  rw [evZeta_eq_aeval] at hf
  obtain ⟨T, hT⟩ := int_dvd_of_monic_Q (monic_cycloZ hn) ((aeval_zetaN_eq_zero_iff hn _).1 hf)
  exact ⟨T, by rw [hT, CommRing.mul_comm]⟩

end IntZetaN

/-! ## The ring `𝔽_q[x]/(Φ_n)` -/

section ResRingN

variable (q n : Nat) [NeZero q]

/-- The principal ideal `(Φ̄_n)` of `𝔽_q[x]`, `Φ̄_n` the reduction of `Φ_n` modulo `q`. -/
noncomputable def cycloIdealN : Ideal (Polynomial (Fin q)) :=
  Ideal.span (mapPoly (icastHom (Fin q)) (cycloZ n))

/-- **The ring `A_n = 𝔽_q[x]/(Φ̄_n)`**, of characteristic `q`. -/
abbrev ResRingN : Type := QuotientRing (cycloIdealN q n)

/-- The class `ζ` of `x` in `𝔽_q[x]/(Φ̄_n)`. -/
noncomputable def zetaResN : ResRingN q n := QuotientRing.mk (cycloIdealN q n) X

/-- The structure map `𝔽_q → 𝔽_q[x]/(Φ̄_n)`. -/
noncomputable def constHomN : RingHom (Fin q) (ResRingN q n) :=
  RingHom.comp (QuotientRing.proj (cycloIdealN q n)) CHom

/-- Reduction of integer polynomials to `𝔽_q[x]/(Φ̄_n)`: reduce the coefficients modulo `q`
and take the class modulo `Φ̄_n`. -/
noncomputable def redHomN : RingHom (Polynomial Int) (ResRingN q n) :=
  RingHom.comp (QuotientRing.proj (cycloIdealN q n)) (mapHom (icastHom (Fin q)))

variable {q n}

/-- `q = 0` in `𝔽_q[x]/(Φ̄_n)`. -/
theorem resRingN_char : (((q : Nat) : Int) : ResRingN q n) = 0 := by
  have := RingHom.map_intCast (constHomN q n) (q : Int)
  rw [← this]
  show (constHomN q n).toFun (icast (q : Int)) = 0
  rw [fin_icast_self]; exact (constHomN q n).map_zero

/-- `x` reduces to the class `ζ` of `x`. -/
theorem redHomN_X : (redHomN q n).toFun X = zetaResN q n := by
  show QuotientRing.mk _ (mapPoly _ X) = _; rw [mapPoly_X]; rfl

/-- `Φ_n` reduces to `0`. -/
theorem redHomN_cycloZ : (redHomN q n).toFun (cycloZ n) = 0 :=
  QuotientRing.mk_eq_zero.2 ⟨1, (Ring.one_mul _).symm⟩

/-- An integer constant reduces through the structure map `𝔽_q → A_n`. -/
theorem redHomN_C (a : Int) :
    (redHomN q n).toFun (C a) = (constHomN q n).toFun ((a : Int) : Fin q) := by
  show QuotientRing.mk _ (mapPoly _ (C a)) = _; rw [mapPoly_C]; rfl

/-- `φ(n) ≥ 1` for `n ≥ 1`. -/
theorem totient_pos {n : Nat} (hn : 1 ≤ n) : 0 < totient n := by
  rw [← length_unitExps]
  apply List.length_pos_of_mem (a := if n = 1 then 0 else 1)
  rw [mem_unitExps]
  by_cases h : n = 1
  · subst h; exact ⟨by decide, by decide⟩
  · rw [ite_false_of h]; exact ⟨by omega, Nat.coprime_one_left n⟩

/-- **`𝔽_q[x]/(Φ̄_n)` is not the zero ring** for a prime `q` and `n ≥ 1`: `Φ̄_n` is monic of
degree `φ(n) ≥ 1`, so it is not a unit. -/
theorem resRingN_nontrivial (hq : IsPrime q) (hn : 1 ≤ n) : (0 : ResRingN q n) ≠ 1 := by
  intro h
  have hF : IsField (Fin q) := (fin_isField_iff_prime q).2 hq
  have h1 : (1 : Polynomial (Fin q)) ∈ cycloIdealN q n := QuotientRing.mk_eq_zero.1 h.symm
  obtain ⟨r, hr⟩ := h1
  have hm := (monic_cycloZ hn).map (icastHom (Fin q))
  exact not_isUnit_of_natDegree_pos hF.isDomain (hm.ne_zero hF.1)
    (by rw [hm.natDegree_eq hF.1]; exact totient_pos hn)
    ⟨r, by rw [CommRing.mul_comm]; exact hr.symm⟩

variable (hn : 1 ≤ n)

include hn in
/-- **Reduction is well defined on `ℤ[ζ_n]`**: if `f(ζ_n) = g(ζ_n)` then `f` and `g` have the
same image in `𝔽_q[x]/(Φ̄_n)`. -/
theorem redHomN_congr {f g : Polynomial Int} (h : (evZeta n).toFun f = (evZeta n).toFun g) :
    (redHomN q n).toFun f = (redHomN q n).toFun g := by
  have h0 : (evZeta n).toFun (f + -g) = 0 := by
    rw [(evZeta n).map_add, (evZeta n).map_neg, h, Ring.add_neg_cancel]
  obtain ⟨Q, hQ⟩ := dvd_cycloZ_of_evZeta hn h0
  have h1 : (redHomN q n).toFun (f + -g) = 0 := by
    rw [hQ, (redHomN q n).map_mul, redHomN_cycloZ, Ring.mul_zero]
  rw [(redHomN q n).map_add, (redHomN q n).map_neg] at h1
  grind

/-- **Reduction modulo `q`**, the ring homomorphism `ℤ[ζ_n] → 𝔽_q[x]/(Φ̄_n)`,
`f(ζ_n) ↦ f(x) mod (q, Φ_n)`. -/
noncomputable def reduceN : RingHom (intZeta n) (ResRingN q n) where
  toFun α := (redHomN q n).toFun (Classical.choose α.2)
  map_add α β := by
    rw [← (redHomN q n).map_add]
    apply redHomN_congr hn
    rw [(evZeta n).map_add, Classical.choose_spec α.2, Classical.choose_spec β.2,
      Classical.choose_spec (α + β).2]; rfl
  map_mul α β := by
    rw [← (redHomN q n).map_mul]
    apply redHomN_congr hn
    rw [(evZeta n).map_mul, Classical.choose_spec α.2, Classical.choose_spec β.2,
      Classical.choose_spec (α * β).2]; rfl
  map_one := by
    rw [← (redHomN q n).map_one]
    apply redHomN_congr hn
    rw [(evZeta n).map_one, Classical.choose_spec (1 : intZeta n).2]; rfl

/-- `reduceN (f(ζ_n)) = f mod (q, Φ_n)`. -/
theorem reduceN_evZeta (f : Polynomial Int) :
    (reduceN (q := q) hn).toFun ⟨(evZeta n).toFun f, f, rfl⟩ = (redHomN q n).toFun f :=
  redHomN_congr hn (Classical.choose_spec (⟨(evZeta n).toFun f, f, rfl⟩ : intZeta n).2)

/-- `ζ_n ∈ ℤ[ζ_n]` reduces to `ζ = x mod Φ̄_n`. -/
theorem reduceN_zeta : (reduceN (q := q) hn).toFun ⟨zeta n, X, evZeta_X⟩ = zetaResN q n := by
  have := reduceN_evZeta (q := q) hn X
  rw [redHomN_X] at this
  exact (congrArg (reduceN hn).toFun (Subtype.ext evZeta_X.symm)).trans this

end ResRingN

/-! ## `σ_q` reduces to the `q`-th power map -/

section FrobN

variable {n : Nat} (hn : 1 ≤ n)

/-- **`σ_a` on `ℤ[ζ_n]`.** `σ_a(f(ζ_n)) = f(ζ_n^a)`. -/
theorem galAutN_evZeta {a : Nat} (ha : Nat.Coprime a n) (f : Polynomial Int) :
    ((galAutN hn ha).toFun ⟨(evZeta n).toFun f, intZeta_leN hn ⟨f, rfl⟩⟩).1 =
      (evZeta n).toFun ((powSubst a).toFun f) := by
  let σ := galAutN hn ha
  let φ : RingHom (Polynomial Int) ℂ :=
    { toFun := fun f => (σ.toFun ⟨(evZeta n).toFun f, intZeta_leN hn ⟨f, rfl⟩⟩).1
      map_add := fun f g => by
        show _ = (σ.toFun _ + σ.toFun _).1
        rw [← σ.map_add]; congr 2; apply Subtype.ext; exact (evZeta n).map_add f g
      map_mul := fun f g => by
        show _ = (σ.toFun _ * σ.toFun _).1
        rw [← σ.map_mul]; congr 2; apply Subtype.ext; exact (evZeta n).map_mul f g
      map_one := by
        show _ = ((1 : cycloFieldN hn)).1
        rw [← σ.map_one]; congr 2; apply Subtype.ext; exact (evZeta n).map_one }
  exact polyHom_ext φ (RingHom.comp (evZeta n) (powSubst a))
    (fun c => by
      show (σ.toFun _).1 = (evZeta n).toFun (eval _ (mapPoly CHom (C c)))
      rw [mapPoly_C, eval_C]
      have hval : (evZeta n).toFun (C c) = icast c := by
        show eval (zeta n) (mapPoly _ (C c)) = _; rw [mapPoly_C, eval_C]; rfl
      have hmem : ((evZeta n).toFun (C c)) ∈ Qc := by rw [hval]; exact icast_mem Qc c
      rw [σ.fix _ hmem]
      rfl)
    (by
      show (σ.toFun ⟨(evZeta n).toFun X, _⟩).1 = (evZeta n).toFun (eval _ (mapPoly CHom X))
      have e : (⟨(evZeta n).toFun X, intZeta_leN hn ⟨X, rfl⟩⟩ : cycloFieldN hn) = zetaKN hn :=
        Subtype.ext evZeta_X
      rw [e, mapPoly_X, eval_X, RingHom.map_pow', galAutN_zeta, evZeta_X]; rfl) f

/-- `σ_a` maps `ℤ[ζ_n]` into itself. -/
theorem galAutN_mem_intZeta {a : Nat} (ha : Nat.Coprime a n) (α : intZeta n) :
    ((galAutN hn ha).toFun ⟨α.1, intZeta_leN hn α.2⟩).1 ∈ intZeta n := by
  obtain ⟨f, hf⟩ := α.2
  have e : (⟨α.1, intZeta_leN hn α.2⟩ : cycloFieldN hn) =
      ⟨(evZeta n).toFun f, intZeta_leN hn ⟨f, rfl⟩⟩ := Subtype.ext hf.symm
  rw [e, galAutN_evZeta hn ha f]
  exact ⟨_, rfl⟩

/-- `σ_a` as a map `ℤ[ζ_n] → ℤ[ζ_n]`. -/
noncomputable def galAutIntN {a : Nat} (ha : Nat.Coprime a n) (α : intZeta n) : intZeta n :=
  ⟨((galAutN hn ha).toFun ⟨α.1, intZeta_leN hn α.2⟩).1, galAutN_mem_intZeta hn ha α⟩

/-- **Frobenius on integer polynomials mod `(q, Φ_n)`**: `f(x^q) ≡ f(x)^q`. -/
theorem redHomN_powSubst {q : Nat} [NeZero q] (hq : IsPrime q) (f : Polynomial Int) :
    (redHomN q n).toFun ((powSubst q).toFun f) = (redHomN q n).toFun f ^ q := by
  let frob : RingHom (ResRingN q n) (ResRingN q n) :=
    { toFun := fun y => y ^ q
      map_add := add_pow_char hq resRingN_char
      map_mul := fun x y => mul_pow' x y q
      map_one := one_pow' q }
  exact polyHom_ext (RingHom.comp (redHomN q n) (powSubst q)) (RingHom.comp frob (redHomN q n))
    (fun c => by
      show (redHomN q n).toFun (eval _ (mapPoly CHom (C c))) = ((redHomN q n).toFun (C c)) ^ q
      rw [mapPoly_C, eval_C]
      show (redHomN q n).toFun (C c) = _
      rw [redHomN_C, ← RingHom.map_pow']
      exact congrArg (constHomN q n).toFun (fin_pow_self hq _).symm)
    (by
      show (redHomN q n).toFun (eval _ (mapPoly CHom X)) = ((redHomN q n).toFun X) ^ q
      rw [mapPoly_X, eval_X, RingHom.map_pow']) f

/-- **`σ_q` is the Frobenius at `q`.** For `n ≥ 1`, a prime `q` not dividing `n`, and every
`α ∈ ℤ[ζ_n]`, `σ_q(α) ≡ α^q (mod q)`: under the reduction `ℤ[ζ_n] → 𝔽_q[x]/(Φ̄_n)`, the
automorphism `ζ_n ↦ ζ_n^q` becomes the `q`-th power map. -/
theorem reduceN_galAut {q : Nat} [NeZero q] (hq : IsPrime q) (hqn : Nat.Coprime q n)
    (α : intZeta n) :
    (reduceN (q := q) hn).toFun (galAutIntN hn hqn α) = (reduceN (q := q) hn).toFun α ^ q := by
  obtain ⟨f, hf⟩ := α.2
  have eα : α = ⟨(evZeta n).toFun f, f, rfl⟩ := Subtype.ext hf.symm
  have eσ : galAutIntN hn hqn α = ⟨(evZeta n).toFun ((powSubst q).toFun f), _, rfl⟩ := by
    apply Subtype.ext
    show ((galAutN hn hqn).toFun ⟨α.1, _⟩).1 = _
    have e : (⟨α.1, intZeta_leN hn α.2⟩ : cycloFieldN hn) =
        ⟨(evZeta n).toFun f, intZeta_leN hn ⟨f, rfl⟩⟩ := Subtype.ext hf.symm
    rw [e, galAutN_evZeta hn hqn f]
  rw [eσ, eα, reduceN_evZeta, reduceN_evZeta, redHomN_powSubst hq]

/-- For a prime `q`, `q ∤ n` is the same as `gcd(q, n) = 1`. -/
theorem coprime_of_prime_not_dvd {q : Nat} (hq : IsPrime q) (h : ¬ q ∣ n) : Nat.Coprime q n :=
  (Nat.coprime_comm).1 ((coprime_prime_iff hq).2 h)

end FrobN

end Foundations.Langlands
