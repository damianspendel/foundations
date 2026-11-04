import Foundations.Langlands.Padic.HilbertLegendre

/-!
# The Hilbert symbol for odd `p`: explicit formula and bilinearity

Every non-zero `a ∈ ℚₚ` is `c² · u` or `c² · p u` with `c ≠ 0` and `u` a unit of ℤₚ
(`Qp.exists_normal_form`), and the Hilbert symbol only depends on square classes
(`Qp.hilbert_mul_sq_left`, `Qp.hilbert_mul_sq_right`). So `(a, b)ₚ` is determined by its values
on `u`, `p u` (units `u`), which we compute for odd `p` (`Qp.hilbert_std`), writing
`χ(u) = ((u mod p)/p)` for the Legendre symbol of the residue of `u` (`Zp.chi`):

* `(u, v)ₚ = 1` (`Qp.hilbert_units`),
* `(u, p v)ₚ = χ(u)` and `(p u, v)ₚ = χ(v)` (`Qp.hilbertSolvable_unit_pv_iff`),
* `(p u, p v)ₚ = χ(−1) χ(u) χ(v)`, from the identity `(a, b)ₚ = (a, −ab)ₚ`
  (`Qp.hilbert_neg_mul`, for `a ≠ 0`): `(p u, p v) = (p u, −p² u v) = (p u, −u v) = χ(−u v)`.

`χ` is multiplicative (`Zp.chi_mul`, from `Algebra.legendre_mul`, a consequence of Euler's
criterion), and from the table one reads off **bilinearity** (`Qp.hilbert_mul_right`,
`Qp.hilbert_mul_left`): `(a, b b')ₚ = (a, b)ₚ (a, b')ₚ` for non-zero `a, b, b'`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-! ## The residue character `χ` -/

/-- If `p ∣ a − b` for natural numbers, then `a ≡ b (mod p)` as natural numbers. -/
theorem nat_mod_eq_of_dvd {p a b : Nat} (h : (p : Int) ∣ (a : Int) - b) : a % p = b % p := by
  have h' := Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.dvd_iff_emod_eq_zero.1 h)
  rw [← Int.natCast_emod, ← Int.natCast_emod] at h'
  exact Int.ofNat_inj.1 h'

/-- The Legendre symbol only depends on the residue class modulo `p`. -/
theorem legendre_congr {p a b : Nat} (h : a % p = b % p) :
    Foundations.Algebra.legendre a p = Foundations.Algebra.legendre b p := by
  have h1 : p ∣ a ↔ p ∣ b := by rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, h]
  have h2 : Foundations.Algebra.IsQR a p ↔ Foundations.Algebra.IsQR b p := by
    unfold Foundations.Algebra.IsQR; rw [h]
  unfold Foundations.Algebra.legendre
  by_cases hb : p ∣ b
  · simp [hb, h1.2 hb]
  · have ha : ¬ p ∣ a := fun h => hb (h1.1 h)
    by_cases hq : Foundations.Algebra.IsQR b p
    · simp [ha, hb, hq, h2.2 hq]
    · have hq' : ¬ Foundations.Algebra.IsQR a p := fun h => hq (h2.1 h)
      simp [ha, hb, hq, hq']

namespace Zp

variable {p : Nat} [hP : PrimeP p]

/-- The **residue character** of a `p`-adic integer: the Legendre symbol of its residue
modulo `p`, `χ(u) = ((u mod p)/p)`. -/
noncomputable def chi (u : Zp p) : Int := Foundations.Algebra.legendre (residue 1 u) p

/-- A `p`-adic integer is congruent modulo `p` to its residue. -/
theorem modPow_residue (u : Zp p) : ModPow 1 u (((residue 1 u : Nat) : Int) : Zp p) := by
  have hpos : (0 : Int) < (p : Int) ^ 1 := Int.pow_pos (by have := hP.prime.1; omega)
  refine (modPow_rep 1 u).trans (modPow_intCast.2 ?_)
  unfold residue
  generalize (rep u).seq 1 = c
  generalize hn : (p : Int) ^ 1 = n at hpos ⊢
  rw [Int.toNat_of_nonneg (Int.emod_nonneg c (Int.ne_of_gt hpos))]
  have := Int.mul_ediv_add_emod c n
  refine ⟨c / n, ?_⟩
  generalize n * (c / n) = A at this ⊢
  omega

/-- `χ` on a unit: `1` if `u` is a square modulo `p`, `−1` otherwise. -/
theorem chi_cases {u : Zp p} (hu : IsPUnit u) :
    (chi u = 1 ∧ ∃ a : Int, ModPow 1 u ((a * a : Int) : Zp p)) ∨
      (chi u = -1 ∧ ¬ ∃ a : Int, ModPow 1 u ((a * a : Int) : Zp p)) := by
  have hr : ¬ p ∣ residue 1 u := fun h =>
    hu ((modPow_residue u).trans (modPow_intCast_zero (Int.ofNat_dvd.2 h)))
  have key : (∃ a : Int, ModPow 1 u ((a * a : Int) : Zp p)) ↔
      Foundations.Algebra.IsQR (residue 1 u) p := by
    refine Iff.trans ?_ (Qp.isQR_iff (p := p)).symm
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, (modPow_residue u).symm.trans ha⟩
    · rintro ⟨a, ha⟩; exact ⟨a, (modPow_residue u).trans ha⟩
  unfold chi Foundations.Algebra.legendre
  by_cases hq : Foundations.Algebra.IsQR (residue 1 u) p
  · left; simp only [hr, hq, ite_true, ite_false]; exact ⟨trivial, key.2 hq⟩
  · right; simp only [hr, hq, ite_false]; exact ⟨trivial, fun h => hq (key.1 h)⟩

/-- `χ(u)² = 1` for a unit `u`. -/
theorem chi_mul_self {u : Zp p} (hu : IsPUnit u) : chi u * chi u = 1 := by
  rcases chi_cases hu with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide

/-- **`χ` is multiplicative** (odd `p`): `χ(u v) = χ(u) χ(v)`. -/
theorem chi_mul (hodd : p % 2 = 1) (u v : Zp p) : chi (u * v) = chi u * chi v := by
  have h := (modPow_residue (u * v)).symm.trans ((modPow_residue u).mul (modPow_residue v))
  rw [← Ring.intCast_mul, ← Int.natCast_mul] at h
  have h' := modPow_intCast.1 h
  rw [Int.pow_one] at h'
  unfold chi
  rw [legendre_congr (nat_mod_eq_of_dvd h')]
  exact Foundations.Algebra.legendre_mul hP.prime hodd _ _

/-- `−1` is a unit of ℤₚ. -/
theorem isPUnit_neg_one : IsPUnit (-1 : Zp p) := not_modPow_neg_one hP.prime

/-- **First supplement.** `χ(−1) = (−1)^((p−1)/2)` for odd `p`. -/
theorem chi_neg_one (hodd : p % 2 = 1) :
    chi (-1 : Zp p) = (-1) ^ Foundations.Algebra.half p := by
  have hp2 := hP.prime.1
  have h1 : ModPow 1 (-1 : Zp p) (((p - 1 : Nat) : Int) : Zp p) := by
    rw [show (-1 : Zp p) = ((-1 : Int) : Zp p) from (Ring.intCast_neg_one).symm]
    apply modPow_intCast.2
    rw [Int.pow_one]
    exact ⟨-1, by omega⟩
  have h := modPow_intCast.1 ((modPow_residue (-1 : Zp p)).symm.trans h1)
  rw [Int.pow_one] at h
  unfold chi
  rw [legendre_congr (nat_mod_eq_of_dvd h)]
  exact Foundations.Algebra.legendre_neg_one hP.prime hodd

end Zp

/-! ## Square classes and the identity `(a, b) = (a, −ab)` -/

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- Two Hilbert symbols agree when the solvability conditions are equivalent. -/
theorem hilbert_congr {a b a' b' : Qp p} (h : HilbertSolvable a b ↔ HilbertSolvable a' b') :
    hilbert a b = hilbert a' b' := by
  by_cases h1 : HilbertSolvable a b
  · rw [(hilbert_eq_one_iff _ _).2 h1, (hilbert_eq_one_iff _ _).2 (h.1 h1)]
  · rw [(hilbert_eq_neg_one_iff _ _).2 h1, (hilbert_eq_neg_one_iff _ _).2 (fun h2 => h1 (h.2 h2))]

/-- The inverse of a non-zero element is non-zero. -/
theorem inv_ne_zero' {c : Qp p} (hc : c ≠ 0) : c⁻¹ ≠ 0 := fun h => by
  have := Field.mul_inv_cancel hc; rw [h] at this; exact zero_ne_one (p := p) (by grind)

/-- **Square classes.** `(c² a, b)ₚ = (a, b)ₚ` for `c ≠ 0`. -/
theorem hilbert_mul_sq_left {a b c : Qp p} (hc : c ≠ 0) : hilbert (c * c * a) b = hilbert a b := by
  have hci := Field.mul_inv_cancel hc
  apply hilbert_congr
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨c * x, y, z, ?_, by rw [h]; grind⟩
    rcases hne with hx | hy | hz
    · exact Or.inl (mul_ne_zero' hc hx)
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hz)
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨c⁻¹ * x, y, z, ?_, ?_⟩
    · rcases hne with hx | hy | hz
      · exact Or.inl (mul_ne_zero' (inv_ne_zero' hc) hx)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hz)
    · rw [h, show c * c * a * (c⁻¹ * x * (c⁻¹ * x)) = (c * c⁻¹) * (c * c⁻¹) * (a * (x * x)) by
        grind, hci]
      grind

/-- **Square classes.** `(a, c² b)ₚ = (a, b)ₚ` for `c ≠ 0`. -/
theorem hilbert_mul_sq_right {a b c : Qp p} (hc : c ≠ 0) : hilbert a (c * c * b) = hilbert a b := by
  rw [hilbert_comm, hilbert_mul_sq_left hc, hilbert_comm]

/-- If `z² = A x² + B y²` has a non-trivial point and `B ≠ 0`, so does `z² = −AB x² + B y²`:
`(x, y, z) ↦ (x, z, B y)`. -/
theorem hilbertSolvable_neg_mul {A B : Qp p} (hB : B ≠ 0) (h : HilbertSolvable A B) :
    HilbertSolvable (-(A * B)) B := by
  obtain ⟨x, y, z, hne, h⟩ := h
  refine ⟨x, z, B * y, ?_, ?_⟩
  · by_cases hx : x = 0
    · by_cases hz : z = 0
      · have hy : y ≠ 0 := by
          rcases hne with h' | h' | h'
          · exact absurd hx h'
          · exact h'
          · exact absurd hz h'
        exact Or.inr (Or.inr (mul_ne_zero' hB hy))
      · exact Or.inr (Or.inl hz)
    · exact Or.inl hx
  · have : B * y * (B * y) = B * (z * z) - A * B * (x * x) := by rw [h]; grind
    rw [this]; grind

/-- **`(a, b)ₚ = (a, −ab)ₚ`** for `a ≠ 0`. -/
theorem hilbert_neg_mul {a b : Qp p} (ha : a ≠ 0) :
    hilbert a b = hilbert a (-(a * b)) := by
  have hcomm : ∀ {a b : Qp p}, HilbertSolvable a b → HilbertSolvable b a := fun {a b} h =>
    (hilbert_eq_one_iff b a).1 ((hilbert_comm b a).trans ((hilbert_eq_one_iff a b).2 h))
  apply hilbert_congr
  constructor
  · intro h
    have := hcomm (hilbertSolvable_neg_mul ha (hcomm h))
    rwa [show -(b * a) = -(a * b) by grind] at this
  · intro h
    have h1 := hcomm (hilbertSolvable_neg_mul ha (hcomm h))
    rw [show -(-(a * b) * a) = a * a * b by grind] at h1
    have h2 : hilbert a (a * a * b) = 1 := (hilbert_eq_one_iff _ _).2 h1
    rw [hilbert_mul_sq_right ha] at h2
    exact (hilbert_eq_one_iff _ _).1 h2

/-! ## Normal forms -/

/-- The standard representatives of `ℚₚˣ / (ℚₚˣ)²`-classes: `std false u = u`,
`std true u = p u`. -/
def std : Bool → Zp p → Qp p
  | false, u => ofZp u
  | true, u => ofZp ((p : Zp p) * u)

/-- A standard representative with a unit is non-zero. -/
theorem std_ne_zero (α : Bool) {u : Zp p} (hu : Zp.IsPUnit u) : std α u ≠ 0 := by
  cases α
  · exact fun h0 => hu ((ofZp_injective (h0.trans rfl)) ▸ Zp.ModPow.refl 1 0)
  · exact ofZp_pv_ne_zero hu

/-- **Normal form.** Every non-zero `a ∈ ℚₚ` is `c² · u` or `c² · p u` with `c ≠ 0` and `u` a
unit of ℤₚ. -/
theorem exists_normal_form {a : Qp p} (ha : a ≠ 0) :
    ∃ c : Qp p, c ≠ 0 ∧ ∃ α : Bool, ∃ u : Zp p, Zp.IsPUnit u ∧ a = c * c * std α u := by
  induction a using ind with | h x k => ?_
  have hx : x ≠ 0 := fun h => ha (mk_eq_zero.2 h)
  obtain ⟨v, w, hw, rfl⟩ := Zp.eq_pow_mul_unit hP.prime hx
  have hK : ofZp ((p : Zp p) ^ k) ≠ 0 := fun h => pow_ne_zero (p := p) k (mk_eq_zero.1 h)
  have hKi := Field.mul_inv_cancel hK
  rw [mk_eq_div]
  show ∃ c : Qp p, c ≠ 0 ∧ ∃ α : Bool, ∃ u : Zp p, Zp.IsPUnit u ∧
    ofZp ((p : Zp p) ^ v * w) * (ofZp ((p : Zp p) ^ k))⁻¹ = c * c * std α u
  obtain ⟨m, hm | hm⟩ : ∃ m, v + k = m + m ∨ v + k = m + m + 1 := ⟨(v + k) / 2, by omega⟩
  · have hM : ofZp ((p : Zp p) ^ m) ≠ 0 := fun h => pow_ne_zero (p := p) m (mk_eq_zero.1 h)
    have hrel : ofZp ((p : Zp p) ^ v) * ofZp ((p : Zp p) ^ k) =
        ofZp ((p : Zp p) ^ m) * ofZp ((p : Zp p) ^ m) := by
      rw [← ofZp_mul, ← ofZp_mul, ← Semiring.pow_add, ← Semiring.pow_add, hm]
    refine ⟨ofZp ((p : Zp p) ^ m) * (ofZp ((p : Zp p) ^ k))⁻¹,
      mul_ne_zero' hM (inv_ne_zero' hK), false, w, hw, ?_⟩
    show _ = _ * ofZp w
    rw [ofZp_mul]
    generalize ofZp ((p : Zp p) ^ v) = V at hrel ⊢
    generalize ofZp ((p : Zp p) ^ k) = K at hrel hKi ⊢
    generalize ofZp ((p : Zp p) ^ m) = M at hrel ⊢
    rw [show M * K⁻¹ * (M * K⁻¹) * ofZp w = (M * M) * K⁻¹ * K⁻¹ * ofZp w by grind, ← hrel,
      show V * K * K⁻¹ * K⁻¹ * ofZp w = V * ofZp w * K⁻¹ * (K * K⁻¹) by grind, hKi]
    grind
  · have hM : ofZp ((p : Zp p) ^ m) ≠ 0 := fun h => pow_ne_zero (p := p) m (mk_eq_zero.1 h)
    have hrel : ofZp ((p : Zp p) ^ v) * ofZp ((p : Zp p) ^ k) =
        ofZp ((p : Zp p) ^ m) * ofZp ((p : Zp p) ^ m) * ofZp (p : Zp p) := by
      rw [← ofZp_mul, ← ofZp_mul, ← ofZp_mul, ← Semiring.pow_add, ← Semiring.pow_add, hm,
        Semiring.pow_succ]
    refine ⟨ofZp ((p : Zp p) ^ m) * (ofZp ((p : Zp p) ^ k))⁻¹,
      mul_ne_zero' hM (inv_ne_zero' hK), true, w, hw, ?_⟩
    show _ = _ * ofZp ((p : Zp p) * w)
    rw [ofZp_mul, ofZp_mul]
    generalize ofZp ((p : Zp p) ^ v) = V at hrel ⊢
    generalize ofZp ((p : Zp p) ^ k) = K at hrel hKi ⊢
    generalize ofZp ((p : Zp p) ^ m) = M at hrel ⊢
    generalize ofZp (p : Zp p) = P at hrel ⊢
    rw [show M * K⁻¹ * (M * K⁻¹) * (P * ofZp w) = (M * M * P) * K⁻¹ * K⁻¹ * ofZp w by grind,
      ← hrel, show V * K * K⁻¹ * K⁻¹ * ofZp w = V * ofZp w * K⁻¹ * (K * K⁻¹) by grind, hKi]
    grind

/-- Products of standard representatives: `std β v · std β' v' = e² · std (β ≠ β') (v v')`
with `e = p` if both are `true` and `e = 1` otherwise. -/
theorem std_mul (β β' : Bool) (v v' : Zp p) :
    ∃ e : Qp p, e ≠ 0 ∧ std β v * std β' v' = e * e * std (β != β') (v * v') := by
  have hP0 : ofZp (p : Zp p) ≠ 0 := fun h0 => zp_p_ne_zero (ofZp_injective (h0.trans rfl))
  cases β <;> cases β'
  · exact ⟨1, one_ne_zero', by show ofZp v * ofZp v' = _ * ofZp (v * v'); rw [ofZp_mul]; grind⟩
  · exact ⟨1, one_ne_zero', by
      show ofZp v * ofZp ((p : Zp p) * v') = _ * ofZp ((p : Zp p) * (v * v'))
      simp only [ofZp_mul]; grind⟩
  · exact ⟨1, one_ne_zero', by
      show ofZp ((p : Zp p) * v) * ofZp v' = _ * ofZp ((p : Zp p) * (v * v'))
      simp only [ofZp_mul]; grind⟩
  · exact ⟨ofZp (p : Zp p), hP0, by
      show ofZp ((p : Zp p) * v) * ofZp ((p : Zp p) * v') = _ * ofZp (v * v')
      simp only [ofZp_mul]; grind⟩

/-! ## The table and bilinearity -/

/-- The value table of the Hilbert symbol on standard representatives (odd `p`). -/
noncomputable def hilbertTable : Bool → Bool → Zp p → Zp p → Int
  | false, false, _, _ => 1
  | false, true, u, _ => Zp.chi u
  | true, false, _, v => Zp.chi v
  | true, true, u, v => Zp.chi (-1 : Zp p) * Zp.chi u * Zp.chi v

/-- `(u, p v)ₚ = χ(u)` for units `u, v` (odd `p`). -/
theorem hilbert_unit_pv (hodd : p % 2 = 1) {u v : Zp p} (hu : Zp.IsPUnit u) (hv : Zp.IsPUnit v) :
    hilbert (ofZp u) (ofZp ((p : Zp p) * v)) = Zp.chi u := by
  have key := hilbertSolvable_unit_pv_iff hodd hu hv
  rcases Zp.chi_cases hu with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h]; exact (hilbert_eq_one_iff _ _).2 (key.2 h')
  · rw [h]; exact (hilbert_eq_neg_one_iff _ _).2 (fun h2 => h' (key.1 h2))

/-- **The Hilbert symbol formula (odd `p`).** For units `u, v` of ℤₚ and `α, β ∈ {0, 1}`:
`(u, v) = 1`, `(u, p v) = χ(u)`, `(p u, v) = χ(v)`, `(p u, p v) = χ(−1) χ(u) χ(v)`, where
`χ(w) = ((w mod p)/p)` is the Legendre symbol of the residue. -/
theorem hilbert_std (hodd : p % 2 = 1) (α β : Bool) {u v : Zp p} (hu : Zp.IsPUnit u)
    (hv : Zp.IsPUnit v) : hilbert (std α u) (std β v) = hilbertTable α β u v := by
  cases α <;> cases β
  · exact hilbert_units hodd hu hv
  · exact hilbert_unit_pv hodd hu hv
  · rw [hilbert_comm]; exact hilbert_unit_pv hodd hv hu
  · -- `(p u, p v) = (p u, −p² u v) = (p u, −u v) = χ(−u v)`
    show hilbert (ofZp ((p : Zp p) * u)) (ofZp ((p : Zp p) * v)) = _
    rw [hilbert_neg_mul (ofZp_pv_ne_zero hu)]
    have hP0 : ofZp (p : Zp p) ≠ 0 := fun h0 => zp_p_ne_zero (ofZp_injective (h0.trans rfl))
    have e : -(ofZp ((p : Zp p) * u) * ofZp ((p : Zp p) * v)) =
        ofZp (p : Zp p) * ofZp (p : Zp p) * ofZp ((-1 : Zp p) * u * v) := by
      rw [ofZp_mul, ofZp_mul, ofZp_mul, ofZp_mul, show ofZp (-1 : Zp p) = -1 from rfl]; grind
    rw [e, hilbert_mul_sq_right hP0, hilbert_comm]
    have hw : Zp.IsPUnit ((-1 : Zp p) * u * v) :=
      (Zp.isPUnit_neg_one.mul hP.prime hu).mul hP.prime hv
    rw [hilbert_unit_pv hodd hw hu, Zp.chi_mul hodd, Zp.chi_mul hodd]
    rfl

/-- The table is multiplicative in the second unit and the `xor` of the second exponent. -/
theorem hilbertTable_mul (hodd : p % 2 = 1) (α β β' : Bool) {u : Zp p} (v v' : Zp p)
    (hu : Zp.IsPUnit u) :
    hilbertTable α (β != β') u (v * v') = hilbertTable α β u v * hilbertTable α β' u v' := by
  have h1 := Zp.chi_mul_self hu
  have h2 := Zp.chi_mul_self (Zp.isPUnit_neg_one (p := p))
  have hm := Zp.chi_mul hodd v v'
  cases α <;> cases β <;> cases β' <;> simp only [hilbertTable] <;> grind

/-- **Bilinearity of the Hilbert symbol (odd `p`).** For non-zero `a, b, b' ∈ ℚₚ`,
`(a, b b')ₚ = (a, b)ₚ (a, b')ₚ`. -/
theorem hilbert_mul_right (hodd : p % 2 = 1) {a b b' : Qp p} (ha : a ≠ 0) (hb : b ≠ 0)
    (hb' : b' ≠ 0) : hilbert a (b * b') = hilbert a b * hilbert a b' := by
  obtain ⟨c, hc, α, u, hu, rfl⟩ := exists_normal_form ha
  obtain ⟨d, hd, β, v, hv, rfl⟩ := exists_normal_form hb
  obtain ⟨d', hd', β', v', hv', rfl⟩ := exists_normal_form hb'
  obtain ⟨e, he, hprod⟩ := std_mul β β' v v'
  rw [show d * d * std β v * (d' * d' * std β' v') = (d * d' * e) * (d * d' * e) *
      std (β != β') (v * v') by
      rw [show d * d * std β v * (d' * d' * std β' v') = d * d * (d' * d') * (std β v * std β' v')
        by grind, hprod]
      grind]
  rw [hilbert_mul_sq_left hc, hilbert_mul_sq_left hc, hilbert_mul_sq_left hc,
    hilbert_mul_sq_right (mul_ne_zero' (mul_ne_zero' hd hd') he),
    hilbert_mul_sq_right hd, hilbert_mul_sq_right hd',
    hilbert_std hodd _ _ hu (Zp.IsPUnit.mul hP.prime hv hv'), hilbert_std hodd _ _ hu hv,
    hilbert_std hodd _ _ hu hv']
  exact hilbertTable_mul hodd α β β' v v' hu

/-- **Bilinearity in the first argument (odd `p`).** For non-zero `a, a', b ∈ ℚₚ`,
`(a a', b)ₚ = (a, b)ₚ (a', b)ₚ`. -/
theorem hilbert_mul_left (hodd : p % 2 = 1) {a a' b : Qp p} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb : b ≠ 0) : hilbert (a * a') b = hilbert a b * hilbert a' b := by
  rw [hilbert_comm, hilbert_mul_right hodd hb ha ha', hilbert_comm b a, hilbert_comm b a']

end Qp

end Foundations.Langlands.Padic
