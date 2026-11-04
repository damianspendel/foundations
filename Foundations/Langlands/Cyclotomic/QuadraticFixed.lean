import Foundations.Langlands.Cyclotomic.Quadratic

/-!
# The fixed field of the squares is `ℚ(√p*)`

We finish the identification of the quadratic subfield using the Galois-correspondence tools
of the algebra part (Artin's theorem, the tower law, and "equal degrees force equality").

1. **`[ℚ(√p*) : ℚ] = 2`.** The powers `1, g` form a basis. They span, because division by
   `x² - p*` reduces every polynomial in `g` to one of degree `< 2`. They are independent
   because `g` is irrational. (General lemma: if `γ` is a root of `m ≠ 0` and no non-zero
   polynomial of degree `< deg m` vanishes at `γ`, then `[ℚ(γ) : ℚ] = deg m`.)
2. **The squares as a finite group.** `H = {σ_{(i+1)²} : i < (p-1)/2}`. These are distinct
   (the squares `1², …, ((p-1)/2)²` are distinct mod `p`), contain `σ_1 = id`, and are closed
   under composition (fold `(i+1)(j+1) mod p` into `1, …, (p-1)/2`).
3. **Comparing degrees.** Artin gives `[ℚ(ζ_p) : Fix(H)] = (p-1)/2`. The tower
   `ℚ ⊆ ℚ(√p*) ⊆ ℚ(ζ_p)` gives `[ℚ(ζ_p) : ℚ(√p*)] = (p-1)/2` as well. Since
   `ℚ(√p*) ⊆ Fix(H)`, the two fields are equal.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield Foundations.Algebra.FiniteType

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Degree of a simple extension -/

section SimpleDegree

variable (γ : ℂ) (hγ : IsAlgebraic Qc γ)

/-- **Degree of a simple extension.** If `γ` is a root of `m ≠ 0` and no non-zero rational
polynomial of degree `< deg m` vanishes at `γ`, then `[ℚ(γ) : ℚ] = deg m`. -/
theorem deg_adjoin_eq {m : Polynomial Qc} (hm0 : m ≠ 0) (hmz : aeval Qc γ m = 0)
    (hind : ∀ r : Polynomial Qc, DegLT r (natDegree m) → aeval Qc γ r = 0 → r = 0) :
    deg Qc (adjoin C.isField Qc γ hγ) (le_adjoin _ _ _ _) = natDegree m := by
  let A := adjoin C.isField Qc γ hγ
  let d := natDegree m
  let u : Fin d → A.over Qc (le_adjoin _ _ _ _) := fun i =>
    ⟨rpow γ i.val, rpow_mem (mem_adjoin_self C.isField Qc γ hγ) i.val⟩
  have hspan : Spans Qc u := by
    intro x
    obtain ⟨f, hf⟩ := x.2
    obtain ⟨q, r, hqr, hr⟩ := div_mod (Qc.isField C.isField) f m hm0
    have hrd : DegLT r d := by
      by_cases hr0 : r = 0
      · rw [hr0]; intro n _; exact coeff_zero n
      · rcases hr with h | h
        · exact absurd h hr0
        · exact (degLT_natDegree hr0).mono (by omega)
    have hfr : aeval Qc γ f = aeval Qc γ r := by
      rw [hqr, aeval_add, aeval_mul, hmz, Ring.mul_zero, Ring.zero_add]
    refine ⟨fun i => coeff r i.val, Subtype.ext ?_⟩
    rw [KSubspace.coe_isum]
    show x.1 = isum (fun i : Fin d => (coeff r i.val).1 * rpow γ i.val)
    rw [isum_fin_eq_rsum d (fun k => (coeff r k).1 * rpow γ k), ← hf, hfr]
    unfold aeval
    rw [eval_eq_rsum' γ _ (N := d) (fun n hn => by rw [coeff_mapPoly, hrd n hn]; rfl)]
    exact rsum_congr _ fun k _ => by rw [coeff_mapPoly]; rfl
  have hindep : LinIndep Qc u := by
    intro c hc
    let a : Nat → Qc := fun k => if h : k < d then c ⟨k, h⟩ else 0
    let r : Polynomial Qc := rsum (fun k => C (a k) * X ^ k) d
    have hcoef : ∀ k, coeff r k = if k < d then a k else 0 := coeff_rsum_monomial a d
    have hr0 : aeval Qc γ r = 0 := by
      have h1 := congrArg Subtype.val hc
      rw [KSubspace.coe_isum] at h1
      have h1' : isum (fun i : Fin d => (a i.val).1 * rpow γ i.val) = 0 := by
        refine Eq.trans ?_ h1; congr 1; funext i
        show (a i.val).1 * _ = (c i).1 * _
        simp only [a, dite_eq_left i.isLt]
        rfl
      rw [isum_fin_eq_rsum d (fun k => (a k).1 * rpow γ k)] at h1'
      rw [← h1']
      show (aevalHom Qc γ).toFun r = _
      rw [RingHom.map_rsum]
      apply rsum_congr; intro k _
      rw [(aevalHom Qc γ).map_mul, RingHom.map_pow']
      show aeval Qc γ (C (a k)) * rpow (aeval Qc γ X) k = _
      rw [aeval_C, aeval_X]
    have hrz := hind r (fun k hk => by rw [hcoef, ite_false_of (by omega)]) hr0
    intro i
    have := hcoef i.val
    rw [hrz, coeff_zero, ite_true_of i.isLt] at this
    simp only [a, dite_eq_left i.isLt] at this
    exact this.symm
  have h := card_eq_dim (Qc.isField C.isField) (adjoin_finite C.isField Qc γ hγ)
    (b := u) ⟨hindep, hspan⟩
  rw [card_fin] at h
  exact h.symm

end SimpleDegree

section Fixed

variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

include hp hodd in
/-- **`[ℚ(√p*) : ℚ] = 2`.** -/
theorem deg_sqrtField : deg Qc (sqrtField hp hodd) (Qc_le_sqrtField hp hodd) = 2 := by
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  let c : Qc := Int.cast (pstar p)
  have hdeg : natDegree (binomial c 1) = 2 :=
    natDegree_eq_of (degLT_binomial c 1) (by rw [coeff_binomial]; exact fun h => hD.1 h.symm)
  rw [← hdeg]
  apply deg_adjoin_eq _ _ (binomial_ne_zero hD.1 c 1)
  · unfold aeval
    rw [mapPoly_binomial, eval_binomial]
    show 1 * gaussSum p (zeta p) * gaussSum p (zeta p) + -((Int.cast (pstar p) : Qc)).1 = 0
    rw [Ring.one_mul, gaussSum_sq_complex hp hodd, Subfield.coe_intCast]
    exact Ring.add_neg_cancel _
  · intro r hr hrz
    rw [hdeg] at hr
    -- `r(g) = r₀ + r₁ g`
    have hval : aeval Qc (gaussSum p (zeta p)) r =
        (coeff r 0).1 + (coeff r 1).1 * gaussSum p (zeta p) := by
      unfold aeval
      rw [eval_eq_rsum' _ _ (N := 2) (fun n hn => by rw [coeff_mapPoly, hr n hn]; rfl)]
      show 0 + (coeff (mapPoly _ r) 0) * 1 + (coeff (mapPoly _ r) 1) * (1 * _) = _
      rw [coeff_mapPoly, coeff_mapPoly]
      show 0 + (coeff r 0).1 * 1 + (coeff r 1).1 * (1 * _) = _
      grind
    rw [hval] at hrz
    by_cases h1 : coeff r 1 = 0
    · rw [h1] at hrz
      have h0 : coeff r 0 = 0 := by
        apply Subtype.ext
        show (coeff r 0).1 = 0
        have : (0 : Qc).1 = (0 : ℂ) := rfl
        rw [this, Ring.zero_mul, Ring.add_zero] at hrz
        exact hrz
      apply ext; intro n
      rw [coeff_zero]
      match n with
      | 0 => exact h0
      | 1 => exact h1
      | n + 2 => exact hr (n + 2) (by omega)
    · exfalso
      obtain ⟨b, hb⟩ := (Qc.isField C.isField).2 _ h1
      apply gaussSum_not_rat hp hodd
      have hb' : (coeff r 1).1 * b.1 = 1 := congrArg Subtype.val hb
      have : gaussSum p (zeta p) = (-(coeff r 0) * b).1 := by
        show gaussSum p (zeta p) = -(coeff r 0).1 * b.1
        generalize gaussSum p (zeta p) = g at hrz ⊢
        generalize (coeff r 0).1 = x at hrz ⊢
        generalize (coeff r 1).1 = y at hrz hb' ⊢
        generalize b.1 = z at hb' ⊢
        grind
      rw [this]; exact (-(coeff r 0) * b).2

/-- The square `(i+1)²` used to index the subgroup of squares. -/
def sqIdx (i : Nat) : Nat := (i + 1) * (i + 1)

include hp in
/-- `p ∤ (i+1)²` for `i < (p-1)/2`. -/
theorem sqIdx_not_dvd {i : Nat} (hi : i < half p) : ¬ p ∣ sqIdx i := by
  intro h
  rcases hp.dvd_mul h with h1 | h1 <;>
  · have := Nat.le_of_dvd (by omega) h1
    unfold half at hi; omega

/-- **The group of squares** in `Gal(ℚ(ζ_p)/ℚ)`, listed as `σ_{(i+1)²}`, `i < (p-1)/2`. -/
noncomputable def squaresFam : Fin (half p) → FieldAut Qc (cycloField hp) :=
  fun i => galAut hp (sqIdx_not_dvd hp i.isLt)

/-- `(p - x)² ≡ x² (mod p)`. -/
theorem sub_sq_mod {x : Nat} (hx : x ≤ p) : (p - x) * (p - x) % p = x * x % p := by
  obtain ⟨y, rfl⟩ : ∃ y, p = x + y := ⟨p - x, by omega⟩
  rw [show x + y - x = y by omega]
  have e : y * y + (x + y) * (2 * x) = x * x + (x + y) * (x + y) := by grind
  have := congrArg (· % (x + y)) e
  simp only [Nat.add_mul_mod_self_left] at this
  exact this

include hodd in
/-- The squares are closed under composition. -/
theorem squaresFam_mul (i j : Fin (half p)) :
    ∃ k, squaresFam hp k = squaresFam hp i * squaresFam hp j := by
  have h3 := hp.1
  have ⟨_, _, hh⟩ := half_spec hp hodd
  let x := (i.val + 1) * (j.val + 1) % p
  have hx0 : x ≠ 0 := by
    intro h
    rcases hp.dvd_mul (Nat.dvd_of_mod_eq_zero h) with h1 | h1 <;>
    · have := Nat.le_of_dvd (by omega) h1
      have := i.isLt; have := j.isLt; omega
  have hxp : x < p := Nat.mod_lt _ (by omega)
  let y := if x ≤ half p then x else p - x
  have hy0 : 0 < y := by simp only [y]; split <;> omega
  have hyh : y ≤ half p := by simp only [y]; split <;> omega
  have hyx : y * y % p = x * x % p := by
    simp only [y]; split
    · rfl
    · exact sub_sq_mod (by omega)
  have hmul : ¬ p ∣ sqIdx i.val * sqIdx j.val := fun h =>
    (hp.dvd_mul h).elim (sqIdx_not_dvd hp i.isLt) (sqIdx_not_dvd hp j.isLt)
  refine ⟨⟨y - 1, by omega⟩, ?_⟩
  show galAut hp _ = galAut hp _ * galAut hp _
  rw [← galAut_mul hp _ _ hmul]
  apply galAut_congr
  show (y - 1 + 1) * (y - 1 + 1) % p = _
  rw [show y - 1 + 1 = y by omega, hyx]
  show (i.val + 1) * (j.val + 1) % p * ((i.val + 1) * (j.val + 1) % p) % p =
    (i.val + 1) * (i.val + 1) * ((j.val + 1) * (j.val + 1)) % p
  rw [← Nat.mul_mod]
  congr 1; grind

include hodd in
/-- The listed squares are distinct automorphisms. -/
theorem squaresFam_injective (i j : Fin (half p)) (h : squaresFam hp i = squaresFam hp j) :
    i = j := by
  have h3 := hp.1
  have hζ : rpow (zeta p) p = 1 := zeta_rpow_self (by omega)
  have h1 := congrArg (fun σ : FieldAut Qc (cycloField hp) => (σ.toFun (zetaK hp)).1) h
  change ((galAut hp _).toFun (zetaK hp)).1 = ((galAut hp _).toFun (zetaK hp)).1 at h1
  rw [galAut_zeta, galAut_zeta] at h1
  have h1' : rpow (zeta p) (sqIdx i.val % p) = rpow (zeta p) (sqIdx j.val % p) :=
    (pow_mod_of_pow_eq_one (R := ℂ) hζ _).symm.trans (h1.trans (pow_mod_of_pow_eq_one (R := ℂ) hζ _))
  have := rpow_injective_of_lt C.isField hp hζ (zeta_ne_one (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) h1'
  have := sq_inj hp hodd (u := i.val + 1) (v := j.val + 1) (by omega) (by omega)
    (by have := i.isLt; omega) (by have := j.isLt; omega) this
  exact Fin.ext (by omega)

include hodd in
/-- The identity is among the squares: `σ_1 = 1`. -/
theorem squaresFam_one : ∃ i, squaresFam hp i = 1 := by
  have ⟨_, h1, _⟩ := half_spec hp hodd
  refine ⟨⟨0, by omega⟩, aut_ext_zeta hp (Subtype.ext ?_)⟩
  show ((galAut hp _).toFun (zetaK hp)).1 = zeta p
  rw [galAut_zeta]
  exact rpow_one' _

include hodd in
/-- **The fixed field of the squares is `ℚ(√p*)`.** The subfield of `ℚ(ζ_p)` fixed by the
automorphisms `σ_a` with `a` a non-zero square mod `p` is exactly `ℚ(√p*)`. -/
theorem fixedField_squares :
    (famFix (squaresFam hp)).le (sqrtField hp hodd) ∧
      (sqrtField hp hodd).le (famFix (squaresFam hp)) := by
  have ⟨h2h, _, _⟩ := half_spec hp hodd
  have hart := artin (squaresFam hp) C.isField (squaresFam_injective hp hodd)
    (squaresFam_one hp hodd) (squaresFam_mul hp hodd)
  have hFFix : (sqrtField hp hodd).le (famFix (squaresFam hp)) := by
    intro x hx
    refine ⟨sqrtField_le hp hodd x hx, fun τ ⟨i, hi⟩ => ?_⟩
    rw [← hi]
    exact (galAut_fixes_sqrtField_iff hp hodd (sqIdx_not_dvd hp i.isLt)).2 ⟨i.val + 1, rfl⟩
      ⟨x, sqrtField_le hp hodd x hx⟩ hx
  refine ⟨?_, hFFix⟩
  have hQF := Qc_le_sqrtField hp hodd
  have hFL := sqrtField_le hp hodd
  have hfinQF : FiniteExt Qc (sqrtField hp hodd) hQF := adjoin_finite _ _ _ _
  have hfinFL : FiniteExt (sqrtField hp hodd) (cycloField hp) hFL :=
    finiteExt_of_tower hQF hFL (cycloField_finite hp)
  have htow := (tower_law C.isField hQF hFL hfinQF hfinFL).2
  have hdQL : deg Qc (cycloField hp) (le_trans hQF hFL) = p - 1 := deg_cycloField hp
  rw [hdQL, deg_sqrtField hp hodd] at htow
  have hdFL : deg (sqrtField hp hodd) (cycloField hp) hFL = half p := by omega
  exact le_of_deg_eq C.isField hFFix (famFix_le _) hFL hfinFL hart.1 (by rw [hart.2, hdFL])

end Fixed

end Foundations.Langlands
