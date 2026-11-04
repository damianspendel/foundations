import Foundations.Langlands.Cyclotomic.Eisenstein

/-!
# Irreducibility of `Φ_p` over `ℚ`

**Theorem (Gauss 1801, *Disquisitiones* art. 341).** For a prime `p`, the cyclotomic polynomial
`Φ_p = 1 + x + ⋯ + x^{p-1}` is irreducible over `ℚ`.

Gauss's own proof was intricate. Eisenstein's (1850) takes three lines: substitute `x + 1`
for `x`. Since `(x - 1) Φ_p(x) = x^p - 1`,

  `x · Φ_p(x + 1) = (x + 1)^p - 1 = Σ_{k=1}^{p} C(p, k) xᵏ`,

so `Φ_p(x + 1) = Σ_{k=0}^{p-1} C(p, k+1) xᵏ`. This is monic of degree `p - 1`, every other
coefficient `C(p, k+1)` (`k + 1 < p`) is divisible by `p`, and the constant term `C(p, 1) = p`
is not divisible by `p²`. Eisenstein's criterion applies. The substitution `f(x) ↦ f(x + 1)` is
a ring automorphism of `ℚ[x]` (its inverse is `f(x) ↦ f(x - 1)`), so it preserves
irreducibility.

The substitution is built from the existing machinery as a composite of ring homomorphisms,
`f ↦ (f with coefficients viewed as constants)(X + c)`. Two ring homomorphisms out of `R[x]`
that agree on constants and on `X` are equal, since every polynomial is built from them; this
gives the inverse.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial
open Foundations.NumberTheory (choose choose_zero_right choose_succ_succ choose_self)

universe u

/-! ## Substitution `x ↦ x + c` -/

section Shift

variable {R : Type u} [CommRing R]

/-- **Ring homomorphisms out of `R[x]` are determined by constants and `X`.** -/
theorem polyHom_ext {S : Type u} [CommRing S] (φ ψ : RingHom (Polynomial R) S)
    (hC : ∀ a, φ.toFun (C a) = ψ.toFun (C a)) (hX : φ.toFun X = ψ.toFun X) :
    ∀ f, φ.toFun f = ψ.toFun f := by
  intro f
  induction f using Quotient.ind with
  | _ l =>
  show φ.toFun (mk l) = ψ.toFun (mk l)
  induction l with
  | nil => exact (φ.map_zero).trans (ψ.map_zero).symm
  | cons a l ih => rw [mk_cons, φ.map_add, ψ.map_add, φ.map_mul, ψ.map_mul, hC, hX, ih]

/-- **The substitution** `f(x) ↦ f(x + c)`, as a ring homomorphism `R[x] → R[x]`. -/
def shiftHom (c : R) : RingHom (Polynomial R) (Polynomial R) :=
  RingHom.comp (evalHom (X + C c)) (mapHom CHom)

/-- The substitution fixes constants. -/
theorem shiftHom_C (c a : R) : (shiftHom c).toFun (C a) = C a := by
  show eval (X + C c) (mapPoly CHom (C a)) = C a
  rw [mapPoly_C, eval_C]; rfl

/-- The substitution sends `X` to `X + c`. -/
theorem shiftHom_X (c : R) : (shiftHom c).toFun X = X + C c := by
  show eval (X + C c) (mapPoly CHom X) = _
  rw [mapPoly_X, eval_X]

/-- Substituting `x - c` after `x + c` gives back `f`. -/
theorem shiftHom_shiftHom (c : R) (f : Polynomial R) :
    (shiftHom (-c)).toFun ((shiftHom c).toFun f) = f := by
  have := polyHom_ext (RingHom.comp (shiftHom (-c)) (shiftHom c)) (RingHom.id _)
    (fun a => by
      show (shiftHom (-c)).toFun ((shiftHom c).toFun (C a)) = C a
      rw [shiftHom_C, shiftHom_C])
    (by
      show (shiftHom (-c)).toFun ((shiftHom c).toFun X) = X
      rw [shiftHom_X, (shiftHom (-c)).map_add, shiftHom_X, shiftHom_C, Ring.add_assoc, ← C_add,
        Ring.neg_add_cancel, C_zero, Ring.add_zero]) f
  exact this

/-- **Irreducibility is invariant under substitution.** If `f(x + c)` is irreducible, so is
`f(x)`. -/
theorem irreducible_of_shift (c : R) {f : Polynomial R} (h : Irreducible ((shiftHom c).toFun f)) :
    Irreducible f := by
  obtain ⟨h0, hu, hfac⟩ := h
  have unit_of : ∀ g, IsUnit ((shiftHom c).toFun g) → IsUnit g := by
    rintro g ⟨u, hu⟩
    refine ⟨(shiftHom (-c)).toFun u, ?_⟩
    rw [← shiftHom_shiftHom c g, ← (shiftHom (-c)).map_mul, hu, (shiftHom (-c)).map_one]
  refine ⟨fun hf => h0 (by rw [hf]; exact (shiftHom c).map_zero), fun ⟨u, hfu⟩ => hu ?_,
    fun a b hab => ?_⟩
  · exact ⟨(shiftHom c).toFun u, by rw [← (shiftHom c).map_mul, hfu, (shiftHom c).map_one]⟩
  · rcases hfac _ _ (by rw [hab, (shiftHom c).map_mul]) with h1 | h1
    · exact Or.inl (unit_of a h1)
    · exact Or.inr (unit_of b h1)

end Shift

/-! ## `Φ_p(x + 1)` -/

section ShiftedCyclo

variable {R : Type u} [CommRing R]

/-- `C(n, 1) = n`. -/
theorem choose_one : ∀ n, choose n 1 = n
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_zero_right, choose_one n]; omega

/-- **`Φ_p(x + 1)` written out**: the polynomial `Σ_{k<p} C(p, k+1) xᵏ`. -/
noncomputable def shiftedCyclo (R : Type u) [CommRing R] (p : Nat) : Polynomial R :=
  rsum (fun k => ((choose p (k + 1) : Int) : Polynomial R) * X ^ k) p

/-- `X^k` is the monomial `Xpow k`. -/
theorem X_pow_eq_Xpow : ∀ k, (X : Polynomial R) ^ k = Xpow k
  | 0 => rfl
  | k + 1 => by
    show X ^ k * X = X * Xpow k
    rw [X_pow_eq_Xpow k, CommRing.mul_comm]

/-- Coefficients of a finite sum of polynomials. -/
theorem coeff_rsum (t : Nat → Polynomial R) (m : Nat) :
    ∀ n, coeff (rsum t n) m = rsum (fun k => coeff (t k) m) n
  | 0 => coeff_zero m
  | n + 1 => by
    show coeff (rsum t n + t n) m = _
    rw [coeff_add, coeff_rsum t m n]; rfl

/-- The coefficients of `Σ_{k<p} C(p, k+1) xᵏ`. -/
theorem coeff_shiftedCyclo (p m : Nat) :
    coeff (shiftedCyclo R p) m = if m < p then ((choose p (m + 1) : Int) : R) else 0 := by
  unfold shiftedCyclo
  rw [coeff_rsum]
  have hterm : ∀ k, coeff (((choose p (k + 1) : Int) : Polynomial R) * X ^ k) m =
      if m = k then ((choose p (k + 1) : Int) : R) else 0 := by
    intro k
    rw [← RingHom.map_intCast (CHom (R := R)), X_pow_eq_Xpow, CommRing.mul_comm,
      coeff_Xpow_mul]
    show (if k ≤ m then coeff (C _) (m - k) else 0) = _
    by_cases h : m = k
    · subst h; rw [ite_true_of (Nat.le_refl m), Nat.sub_self, coeff_C, ite_true_of rfl,
        ite_true_of rfl]
    · rw [ite_false_of h]
      by_cases h' : k ≤ m
      · rw [ite_true_of h', coeff_C, ite_false_of (by omega)]
      · rw [ite_false_of h']
  rw [rsum_congr p fun k _ => hterm k]
  by_cases hm : m < p
  · rw [ite_true_of hm, rsum_single _ p hm (fun k _ hk => ite_false_of (Ne.symm hk)),
      ite_true_of rfl]
  · rw [ite_false_of hm]
    exact rsum_zero p fun k hk => ite_false_of (by omega)

/-- **Eisenstein's substitution.** Over a domain, `Φ_p(x + 1) = Σ_{k<p} C(p, k+1) xᵏ`: multiply
`(x - 1) Φ_p(x) = x^p - 1` through by the substitution and expand `(x + 1)^p` by the binomial
theorem. -/
theorem shiftHom_cyclo (hD : IsDomain R) (p : Nat) :
    (shiftHom (1 : R)).toFun (cyclo R p) = shiftedCyclo R p := by
  have hDP := Polynomial.isDomain hD
  have hX0 : (X : Polynomial R) ≠ 0 := by
    intro h; have := coeff_X (R := R) 1
    rw [h, coeff_zero, ite_true_of rfl] at this; exact hD.1 this
  apply hDP.mul_left_cancel hX0
  -- apply the substitution to `(X - 1) Φ_p = X^p - 1`
  have h := congrArg (shiftHom (1 : R)).toFun (X_sub_one_mul_cyclo (R := R) p)
  rw [(shiftHom 1).map_mul, (shiftHom 1).map_add, (shiftHom 1).map_add, (shiftHom 1).map_neg,
    (shiftHom 1).map_one, RingHom.map_pow', shiftHom_X, C_one] at h
  have h1 : (X : Polynomial R) + 1 + -1 = X := by grind
  rw [h1] at h
  rw [h]
  -- expand `(X + 1)^p`
  rw [binomial_theorem, rsum_succ']
  unfold bterm shiftedCyclo
  rw [choose_zero_right, mul_rsum]
  have hterm : ∀ k, k < p → ((choose p (k + 1) : Int) : Polynomial R) *
      ((X : Polynomial R) ^ (k + 1) * (1 : Polynomial R) ^ (p - (k + 1))) =
      X * (((choose p (k + 1) : Int) : Polynomial R) * X ^ k) := by
    intro k _
    rw [one_pow', Ring.mul_one]
    show _ * (X ^ k * X) = _
    grind
  rw [rsum_congr p hterm]
  rw [one_pow']
  show (((1 : Nat) : Int) : Polynomial R) * (1 * 1) + _ + -1 = _
  grind

end ShiftedCyclo

/-! ## The theorem -/

section Irreducible

variable {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω) (hc : CharZero Ω)

include hΩ hc in
/-- **Gauss's theorem: `Φ_p` is irreducible over `ℚ`.** For a prime `p`, the cyclotomic
polynomial `1 + x + ⋯ + x^{p-1}` is irreducible in `ℚ[x]`, where `ℚ` is the prime field of any
field of characteristic zero. (Eisenstein's criterion at `p`, applied to `Φ_p(x + 1)`.) -/
theorem cyclo_irreducible {p : Nat} (hp : IsPrime p) : Irreducible (cyclo (ratField hΩ hc) p) := by
  let K := ratField hΩ hc
  have hD : IsDomain K := (K.isField hΩ).isDomain
  have h2 := hp.1
  apply irreducible_of_shift (1 : K)
  rw [shiftHom_cyclo hD p]
  let F : Nat → Int := fun k => if k < p then (choose p (k + 1) : Int) else 0
  refine eisenstein_irreducible hΩ hc hp (shiftedCyclo K p) (F := F) (n := p - 1) (by omega)
    ?_ ?_ ?_ ?_ ?_
  · intro k
    rw [coeff_shiftedCyclo]
    by_cases hk : k < p
    · rw [ite_true_of hk]; show ((Int.cast _ : K) : Ω) = Int.cast (F k)
      rw [Subfield.coe_intCast]; simp only [F, ite_true_of hk]
    · rw [ite_false_of hk]; simp only [F, ite_false_of hk]; exact icast_zero'.symm
  · intro k hk; simp only [F]; rw [ite_false_of (by omega)]
  · simp only [F]; rw [ite_true_of (by omega), show p - 1 + 1 = p by omega, choose_self]; rfl
  · intro k hk
    simp only [F]; rw [ite_true_of (by omega)]
    exact Int.ofNat_dvd.2 (prime_dvd_choose hp (by omega) (by omega))
  · simp only [F]; rw [ite_true_of (by omega), choose_one]
    intro ⟨c, hc⟩
    have hp0 : (p : Int) ≠ 0 := by omega
    have e : (p : Int) * 1 = p * (p * c) := by rw [Int.mul_one, ← Int.mul_assoc]; exact hc
    have e1 : (1 : Int) = p * c := Int.eq_of_mul_eq_mul_left hp0 e
    have : (p : Int) ∣ 1 := ⟨c, e1⟩
    have := Int.le_of_dvd (by decide) this
    omega

end Irreducible

end Foundations.Langlands
