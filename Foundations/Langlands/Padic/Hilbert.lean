import Foundations.Langlands.Padic.SquareLift
import Foundations.Langlands.Padic.QpComplete

/-!
# The Hilbert symbol

For `a, b ∈ ℚₚ` the **Hilbert symbol** `(a, b)ₚ` is `1` if the conic
`z² = a x² + b y²` has a point `(x, y, z) ≠ (0, 0, 0)` with coordinates in ℚₚ, and `−1`
otherwise (Hilbert, *Zahlbericht*, 1897). It records whether the quadratic form
`a x² + b y² − z²` is *isotropic* over ℚₚ, and it is the local ingredient of Hasse's
local–global principle for ternary forms and of Hilbert's reformulation of quadratic
reciprocity as a product formula `∏_v (a, b)_v = 1`. The definition is made for all `a, b`; the
classical theory concerns `a, b ≠ 0`.

Proved here, from the definition:

* `Qp.hilbert_comm` — symmetry `(a, b) = (b, a)`;
* `Qp.hilbert_mul_self` — `(a, c²) = 1`, and `Qp.hilbert_of_eq_sq` — `(c², b) = 1`;
* `Qp.hilbert_neg_self` — `(a, −a) = 1`, and `Qp.hilbert_one_sub` — `(a, 1 − a) = 1`;
* **`Qp.hilbert_units`** — for an odd prime `p` and `p`-adic units `u, v ∈ ℤₚˣ`,
  `(u, v)ₚ = 1`: there are integers with `u₀x₀² + v₀y₀² ≡ 1 (mod p)` (pigeonhole, `SquareLift`),
  and the square root needed to make this exact exists in ℤₚ by Hensel's lemma plus compactness
  (`Zp.exists_sq_of_modPow`).

The computation `(u, p)ₚ = (u/p)` is in `HilbertLegendre`; the explicit formula and bilinearity
are in `HilbertBilinear`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-! ## Congruence helpers in ℤₚ -/

namespace Zp

variable {p : Nat}

/-- Congruences modulo `pᵏ` can be added. -/
theorem ModPow.add {k : Nat} {a b c d : Zp p} (h : ModPow k a b) (h' : ModPow k c d) :
    ModPow k (a + c) (b + d) := by
  rw [← mk_rep a, ← mk_rep b, ← mk_rep c, ← mk_rep d] at *
  have h := modPow_mk.1 h
  have h' := modPow_mk.1 h'
  rw [mk_add, mk_add]
  apply modPow_mk.2
  show _ ∣ (rep a).seq k + (rep c).seq k - ((rep b).seq k + (rep d).seq k)
  rw [show (rep a).seq k + (rep c).seq k - ((rep b).seq k + (rep d).seq k) =
    ((rep a).seq k - (rep b).seq k) + ((rep c).seq k - (rep d).seq k) by omega]
  exact Int.dvd_add h h'

/-- Multiples of an element `≡ 0 (mod pᵏ)` are `≡ 0 (mod pᵏ)`. -/
theorem ModPow.zero_mul {k : Nat} {a : Zp p} (b : Zp p) (h : ModPow k a 0) : ModPow k (b * a) 0 := by
  have := (ModPow.refl k b).mul h
  rwa [show b * (0 : Zp p) = 0 by grind] at this

/-- Sums of elements `≡ 0 (mod pᵏ)` are `≡ 0 (mod pᵏ)`. -/
theorem ModPow.zero_add {k : Nat} {a c : Zp p} (h : ModPow k a 0) (h' : ModPow k c 0) :
    ModPow k (a + c) 0 := by
  have := h.add h'
  rwa [show (0 : Zp p) + 0 = 0 by grind] at this

/-- For a prime `p`, `−1 ≢ 0 (mod p)`. -/
theorem not_modPow_neg_one (hp : Prime p) : ¬ ModPow 1 (-1 : Zp p) 0 := fun h => by
  rw [show (-1 : Zp p) = ((-1 : Int) : Zp p) from (Ring.intCast_neg_one).symm,
    show (0 : Zp p) = ((0 : Int) : Zp p) from rfl] at h
  have h := modPow_intCast.1 h
  rw [Int.pow_one, Int.sub_zero] at h
  have := Int.le_of_dvd (by decide) (Int.dvd_neg.1 h); have := hp.1; omega

/-- An integer divisible by `p` is `≡ 0 (mod p)` in ℤₚ. -/
theorem modPow_intCast_zero {a : Int} (h : (p : Int) ∣ a) : ModPow 1 (a : Zp p) 0 := by
  show ModPow 1 (a : Zp p) ((0 : Int) : Zp p)
  apply modPow_intCast.2; rw [Int.pow_one, Int.sub_zero]; exact h

/-- The first digit `x₁` of a unit is prime to `p`. -/
theorem not_dvd_rep_of_isPUnit {u : Zp p} (hu : IsPUnit u) : ¬ (p : Int) ∣ (rep u).seq 1 :=
  fun h => hu ((modPow_rep 1 u).trans (modPow_intCast_zero h))

/-- The core computation behind `(u, v)ₚ = 1`: if `u` is invertible, `p ∤ x₀` and
`u x₀² + v y₀² ≡ 1 (mod p)`, then `u X² + v Y² = 1` for some `X, Y ∈ ℤₚ` (take `Y = y₀` and
`X = √((1 − v y₀²)/u)`). -/
theorem solve_core (hp : Prime p) (hodd : p % 2 = 1) {u v uinv : Zp p} (huinv : u * uinv = 1)
    {x0 y0 : Int} (hx0 : ¬ (p : Int) ∣ x0)
    (E : ModPow 1 (u * ((x0 : Zp p) * (x0 : Zp p)) + v * ((y0 : Zp p) * (y0 : Zp p)) - 1) 0) :
    ∃ X Y : Zp p, u * (X * X) + v * (Y * Y) = 1 := by
  let w := uinv * (1 - v * ((y0 : Zp p) * (y0 : Zp p)))
  have hw : w - (x0 : Zp p) * (x0 : Zp p) =
      (-uinv) * (u * ((x0 : Zp p) * (x0 : Zp p)) + v * ((y0 : Zp p) * (y0 : Zp p)) - 1) := by
    show uinv * (1 - v * ((y0 : Zp p) * (y0 : Zp p))) - _ = _
    grind
  have hmod : ModPow 1 w ((x0 * x0 : Int) : Zp p) := by
    rw [modPow_iff_sub, Ring.intCast_mul, hw]
    exact E.zero_mul _
  obtain ⟨X, hX⟩ := exists_sq_of_modPow hp hodd hx0 hmod
  refine ⟨X, y0, ?_⟩
  rw [hX]
  show u * (uinv * (1 - v * ((y0 : Zp p) * (y0 : Zp p)))) + _ = _
  grind

/-- For units `u, v` of ℤₚ (`p` odd) there are `X, Y ∈ ℤₚ` with `u X² + v Y² = 1`. -/
theorem exists_unit_sum_sq_eq_one (hp : Prime p) (hodd : p % 2 = 1) {u v : Zp p}
    (hu : IsPUnit u) (hv : IsPUnit v) : ∃ X Y : Zp p, u * (X * X) + v * (Y * Y) = 1 := by
  let c := (rep u).seq 1
  let d := (rep v).seq 1
  obtain ⟨x0, y0, hxy⟩ := exists_sum_sq_eq_one_mod hp hodd (not_dvd_rep_of_isPUnit hu)
    (not_dvd_rep_of_isPUnit hv)
  have Uc : ModPow 1 (u - (c : Zp p)) 0 := modPow_iff_sub.1 (modPow_rep 1 u)
  have Vd : ModPow 1 (v - (d : Zp p)) 0 := modPow_iff_sub.1 (modPow_rep 1 v)
  have I0 := modPow_intCast_zero (p := p) hxy
  simp only [Ring.intCast_sub, Ring.intCast_add, Ring.intCast_mul, Ring.intCast_one] at I0
  have E : ModPow 1 (u * ((x0 : Zp p) * (x0 : Zp p)) + v * ((y0 : Zp p) * (y0 : Zp p)) - 1) 0 := by
    rw [show u * ((x0 : Zp p) * (x0 : Zp p)) + v * ((y0 : Zp p) * (y0 : Zp p)) - 1 =
      ((x0 : Zp p) * (x0 : Zp p)) * (u - (c : Zp p)) + ((y0 : Zp p) * (y0 : Zp p)) * (v - (d : Zp p))
      + ((c : Zp p) * x0 * x0 + (d : Zp p) * y0 * y0 - 1) by grind]
    exact ((Uc.zero_mul _).zero_add (Vd.zero_mul _)).zero_add I0
  obtain ⟨uinv, huinv⟩ := (isUnit_iff hp u).2 hu
  obtain ⟨vinv, hvinv⟩ := (isUnit_iff hp v).2 hv
  by_cases hx0 : (p : Int) ∣ x0
  · -- then `p ∤ y₀`, and we solve for `X` with the roles of `u` and `v` exchanged
    have hy0 : ¬ (p : Int) ∣ y0 := fun hy0 => by
      have h1 := ((modPow_intCast_zero (p := p) hx0).zero_mul (u * (x0 : Zp p))).zero_add
        ((modPow_intCast_zero (p := p) hy0).zero_mul (v * (y0 : Zp p)))
      have h2 := E.zero_add (h1.zero_mul (-1))
      rw [show u * ((x0 : Zp p) * (x0 : Zp p)) + v * ((y0 : Zp p) * (y0 : Zp p)) - 1 +
        -1 * (u * (x0 : Zp p) * (x0 : Zp p) + v * (y0 : Zp p) * (y0 : Zp p)) = -1 by grind] at h2
      exact not_modPow_neg_one hp h2
    obtain ⟨X, Y, hXY⟩ := solve_core hp hodd hvinv hy0 (u := v) (v := u) (y0 := x0) (by
      rw [show v * ((y0 : Zp p) * (y0 : Zp p)) + u * ((x0 : Zp p) * (x0 : Zp p)) - 1 =
        u * ((x0 : Zp p) * (x0 : Zp p)) + v * ((y0 : Zp p) * (y0 : Zp p)) - 1 by grind]
      exact E)
    exact ⟨Y, X, by grind⟩
  · exact solve_core hp hodd huinv hx0 E

end Zp

/-! ## The Hilbert symbol -/

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- The conic `z² = a x² + b y²` has a **non-trivial point** over ℚₚ: some `(x, y, z) ≠ 0`
with `z² = a x² + b y²`. -/
def HilbertSolvable (a b : Qp p) : Prop :=
  ∃ x y z : Qp p, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ z * z = a * (x * x) + b * (y * y)

/-- The **Hilbert symbol** `(a, b)ₚ`: `1` if `z² = a x² + b y²` has a non-trivial solution in
ℚₚ, `−1` otherwise. -/
noncomputable def hilbert (a b : Qp p) : Int := by
  classical exact if HilbertSolvable a b then 1 else -1

/-- `(a, b)ₚ = 1` iff the conic has a non-trivial point. -/
theorem hilbert_eq_one_iff (a b : Qp p) : hilbert a b = 1 ↔ HilbertSolvable a b := by
  unfold hilbert
  by_cases h : HilbertSolvable a b
  · simp [h]
  · simp only [h, ite_false, iff_false]; decide

/-- `(a, b)ₚ = −1` iff the conic has no non-trivial point. -/
theorem hilbert_eq_neg_one_iff (a b : Qp p) : hilbert a b = -1 ↔ ¬ HilbertSolvable a b := by
  unfold hilbert
  by_cases h : HilbertSolvable a b
  · simp only [h, ite_true, not_true_eq_false, iff_false]; decide
  · simp [h]

/-- The Hilbert symbol takes only the values `±1`. -/
theorem hilbert_cases (a b : Qp p) : hilbert a b = 1 ∨ hilbert a b = -1 := by
  unfold hilbert; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Symmetry of the Hilbert symbol.** `(a, b)ₚ = (b, a)ₚ`. -/
theorem hilbert_comm (a b : Qp p) : hilbert a b = hilbert b a := by
  have : HilbertSolvable a b ↔ HilbertSolvable b a := by
    constructor
    · rintro ⟨x, y, z, hne, h⟩
      exact ⟨y, x, z, by rcases hne with h | h | h <;> simp_all, by rw [h]; grind⟩
    · rintro ⟨x, y, z, hne, h⟩
      exact ⟨y, x, z, by rcases hne with h | h | h <;> simp_all, by rw [h]; grind⟩
  unfold hilbert
  by_cases h : HilbertSolvable a b
  · simp [h, this.1 h]
  · simp [h, show ¬ HilbertSolvable b a from fun h' => h (this.2 h')]

/-- `1 ≠ 0` in ℚₚ. -/
theorem one_ne_zero' : (1 : Qp p) ≠ 0 := fun h => zero_ne_one (p := p) h.symm

/-- **`(a, c²)ₚ = 1`.** The point `(0, 1, c)` lies on `z² = a x² + c² y²`. -/
theorem hilbert_mul_self (a c : Qp p) : hilbert a (c * c) = 1 :=
  (hilbert_eq_one_iff _ _).2 ⟨0, 1, c, Or.inr (Or.inl one_ne_zero'), by grind⟩

/-- **`(c², b)ₚ = 1`.** If `a` is a square then `(a, b)ₚ = 1`. -/
theorem hilbert_of_eq_sq {a b c : Qp p} (h : a = c * c) : hilbert a b = 1 := by
  rw [hilbert_comm, h]; exact hilbert_mul_self b c

/-- **`(a, −a)ₚ = 1`.** The point `(1, 1, 0)` lies on `z² = a x² − a y²`. -/
theorem hilbert_neg_self (a : Qp p) : hilbert a (-a) = 1 :=
  (hilbert_eq_one_iff _ _).2 ⟨1, 1, 0, Or.inl one_ne_zero', by grind⟩

/-- **`(a, 1 − a)ₚ = 1`.** The point `(1, 1, 1)` lies on `z² = a x² + (1 − a) y²`. -/
theorem hilbert_one_sub (a : Qp p) : hilbert a (1 - a) = 1 :=
  (hilbert_eq_one_iff _ _).2 ⟨1, 1, 1, Or.inl one_ne_zero', by grind⟩

/-- **The Hilbert symbol of two units is trivial (odd `p`).** For an odd prime `p` and units
`u, v` of ℤₚ, `(u, v)ₚ = 1`. -/
theorem hilbert_units (hodd : p % 2 = 1) {u v : Zp p} (hu : Zp.IsPUnit u) (hv : Zp.IsPUnit v) :
    hilbert (ofZp u) (ofZp v) = 1 := by
  obtain ⟨X, Y, h⟩ := Zp.exists_unit_sum_sq_eq_one hP.prime hodd hu hv
  refine (hilbert_eq_one_iff _ _).2 ⟨ofZp X, ofZp Y, 1, Or.inr (Or.inr one_ne_zero'), ?_⟩
  rw [← ofZp_mul, ← ofZp_mul, ← ofZp_mul, ← ofZp_mul, ← ofZp_add, h]
  show (1 : Qp p) * 1 = 1; grind

end Qp

end Foundations.Langlands.Padic
