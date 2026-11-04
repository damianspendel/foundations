import Foundations.Langlands.Padic.HilbertProduct

/-!
# The Hilbert symbol at `2`: the factor `2`, the full table, and bilinearity

`Hilbert2` computed `(u, v)₂` for units `u, v` of ℤ₂. Here we compute the symbols involving the
uniformiser `2`, and obtain the full value table and bilinearity at `p = 2`, completing the
local theory at every prime.

Write `r(u) ∈ {1, 3, 5, 7}` for the residue of a unit `u ∈ ℤ₂ˣ` modulo `8` (`Zp.res8`), and
`ε(u) = (u − 1)/2`, `ω(u) = (u² − 1)/8` modulo `2`. Then for `α, β ∈ {0, 1}`
(**`Qp.hilbert_std_two`**)

  `(2^α u, 2^β v)₂ = (−1)^(ε(u) ε(v) + α ω(v) + β ω(u))`,

encoded by the finite table `table2` on residues modulo `8`.

* `(u, 2v)₂` (`Qp.hilbertSolvable_unit_two_iff`): a primitive solution of
  `z² = u x² + 2v y²` has `x`, `z` odd (parity and squares modulo `4`), so squares modulo `8`
  give `u ≡ 1` or `u + 2v ≡ 1 (mod 8)`; conversely, in these cases `u` resp. `u + 2v` is a
  square in ℤ₂ (`Zp.exists_sq_of_modPow_eight`), giving the points `(1, 0, √u)` and
  `(1, 1, √(u + 2v))`. Comparing with the table is a finite check over residues.
* `(2u, 2v)₂ = (2u, −4uv)₂ = (2u, −uv)₂`, by `Qp.hilbert_neg_mul` and square classes.

The normal form `a = c² · 2^α · u` (`Qp.exists_normal_form`) is available for every prime, so
bilinearity (**`Qp.hilbert_mul_right_two`**, **`Qp.hilbert_mul_left_two`**) follows from the
multiplicativity of the table, exactly as in `HilbertBilinear` for odd `p`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-! ## Integer lemmas modulo 8 -/

/-- `U a²` modulo `8`: for odd `a` it is `U + 8X`, for even `a` it is `4X`. -/
theorem int_mul_sq_mod8 (U a : Int) :
    (a % 2 = 1 ∧ ∃ X, U * (a * a) = 8 * X + U) ∨
      (a % 2 = 0 ∧ ∃ X, U * (a * a) = 4 * X) := by
  have h : a = 2 * (a / 2) + a % 2 := by omega
  generalize a / 2 = k at h
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with h2 | h2
  · right; refine ⟨h2, U * (k * k), ?_⟩; rw [h2] at h; rw [h]; grind
  · left
    refine ⟨h2, ?_⟩
    rw [h2] at h
    have hk : k = 2 * (k / 2) + k % 2 := by omega
    generalize k / 2 = m at hk
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h3 | h3
    · rw [h3] at hk; refine ⟨U * (2 * m * m + m), ?_⟩; rw [h, hk]; grind
    · rw [h3] at hk; refine ⟨U * (2 * m * m + 3 * m + 1), ?_⟩; rw [h, hk]; grind

/-- **The congruence behind `(u, 2v)₂`.** If `U`, `V` are odd, `8 ∣ c² − (U a² + 2 V b²)` and
`a, b, c` are not all even, then `U ≡ 1` or `U + 2V ≡ 1 (mod 8)`. -/
theorem key_mod8 {U V a b c : Int} (hU : U % 2 = 1) (hV : V % 2 = 1)
    (h : (8 : Int) ∣ c * c - (U * (a * a) + 2 * (V * (b * b))))
    (hprim : ¬ (a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0)) : U % 8 = 1 ∨ (U + 2 * V) % 8 = 1 := by
  obtain ⟨t, ht⟩ := h
  have hc := int_mul_sq_mod8 1 c
  rcases int_mul_sq_mod8 U a with ⟨ha, X, hX⟩ | ⟨ha, X, hX⟩ <;>
  rcases int_mul_sq_mod8 V b with ⟨hb, Y, hY⟩ | ⟨hb, Y, hY⟩ <;>
  rcases hc with ⟨hc', Z, hZ⟩ | ⟨hc', Z, hZ⟩ <;>
  · rw [Int.one_mul] at hZ; rw [hX, hY, hZ] at ht; omega

/-! ## Residues modulo 8 in ℤ₂ -/

namespace Zp

/-- The **residue modulo `8`** of a `2`-adic integer, a natural number `< 8`. -/
noncomputable def res8 (u : Zp 2) : Nat := ((rep u).seq 3 % 8).toNat

/-- `(2 : ℤ)³ = 8`, as it appears in congruences modulo `2³` in ℤ₂. -/
theorem two_pow_three : ((2 : Nat) : Int) ^ 3 = 8 := rfl

/-- The residue modulo `8` is `< 8`. -/
theorem res8_lt (u : Zp 2) : res8 u < 8 := by
  unfold res8
  have := Int.emod_nonneg ((rep u).seq 3) (by decide : (8 : Int) ≠ 0)
  have := Int.emod_lt_of_pos ((rep u).seq 3) (by decide : (0 : Int) < 8)
  omega

/-- A `2`-adic integer is congruent modulo `8` to its residue. -/
theorem modPow_res8 (u : Zp 2) : ModPow 3 u (((res8 u : Nat) : Int) : Zp 2) := by
  refine (modPow_rep 3 u).trans (modPow_intCast.2 ?_)
  rw [two_pow_three]
  unfold res8
  have := Int.emod_nonneg ((rep u).seq 3) (by decide : (8 : Int) ≠ 0)
  have := Int.emod_lt_of_pos ((rep u).seq 3) (by decide : (0 : Int) < 8)
  omega

/-- The residue modulo `8` is determined by any congruence modulo `8` with an integer. -/
theorem res8_of_modPow {u : Zp 2} {n : Int} (h : ModPow 3 u (n : Zp 2)) :
    (res8 u : Int) = n % 8 := by
  have h1 := modPow_intCast.1 ((modPow_res8 u).symm.trans h)
  rw [two_pow_three] at h1
  have := res8_lt u
  omega

/-- The residue modulo `8` of an integer. -/
theorem res8_intCast (n : Int) : (res8 (n : Zp 2) : Int) = n % 8 :=
  res8_of_modPow (ModPow.refl 3 _)

/-- The residue of `−1` is `7`. -/
theorem res8_neg_one : res8 (-1 : Zp 2) = 7 := by
  have h := res8_intCast (-1)
  rw [Ring.intCast_neg_one] at h
  omega

/-- The residue of `1` is `1`. -/
theorem res8_one : res8 (1 : Zp 2) = 1 := by
  have h := res8_intCast 1
  rw [Ring.intCast_one] at h
  omega

/-- The residue of a product is the product of the residues, modulo `8`. -/
theorem res8_mul (x y : Zp 2) : res8 (x * y) = res8 x * res8 y % 8 := by
  have h := (modPow_res8 x).mul (modPow_res8 y)
  rw [← Ring.intCast_mul, ← Int.natCast_mul] at h
  have h1 := res8_of_modPow h
  generalize res8 x * res8 y = m at h1
  omega

/-- The residue modulo `8` of a unit is odd. -/
theorem res8_odd {u : Zp 2} (hu : IsPUnit u) : res8 u % 2 = 1 := by
  have h := odd_rep_of_isPUnit hu 3 (by omega)
  unfold res8
  have := Int.emod_nonneg ((rep u).seq 3) (by decide : (8 : Int) ≠ 0)
  omega

/-- `u ≡ 3 (mod 4)` iff its residue modulo `8` is `3` or `7`. -/
theorem modPow_three_iff (u : Zp 2) :
    ModPow 2 u ((3 : Int) : Zp 2) ↔ res8 u % 4 = 3 := by
  have hr := (modPow_res8 u).mono (show 2 ≤ 3 by omega)
  have hl := res8_lt u
  constructor
  · intro h
    have h1 := modPow_intCast.1 (hr.symm.trans h)
    rw [show ((2 : Nat) : Int) ^ 2 = 4 from rfl] at h1
    omega
  · intro h
    refine hr.trans (modPow_intCast.2 ?_)
    rw [show ((2 : Nat) : Int) ^ 2 = 4 from rfl]
    omega

/-- A `2`-adic integer with residue `1` modulo `8` is `≡ 1 (mod 8)`. -/
theorem modPow_one_of_res8 {u : Zp 2} (h : res8 u = 1) : ModPow 3 u ((1 : Int) : Zp 2) := by
  refine (modPow_res8 u).trans (modPow_intCast.2 ?_)
  rw [two_pow_three, h]; decide

end Zp

/-! ## The table -/

/-- The sign `(−1)^(ε(r) ε(s))` on residues: `−1` iff `r ≡ s ≡ 3 (mod 4)`. -/
def eps2 (r s : Nat) : Int := if r % 4 = 3 ∧ s % 4 = 3 then -1 else 1

/-- The sign `(−1)^ω(r)`, `ω(r) = (r² − 1)/8`: `−1` iff `r ≡ ±3 (mod 8)`. -/
def omega2 (r : Nat) : Int := if r % 8 = 3 ∨ r % 8 = 5 then -1 else 1

/-- The **value table of the Hilbert symbol at `2`** on residues `r, s` modulo `8` of units:
`(2^α u, 2^β v)₂ = (−1)^(ε(u) ε(v) + α ω(v) + β ω(u))`. -/
def table2 (α β : Bool) (r s : Nat) : Int :=
  eps2 r s * (if β then omega2 r else 1) * (if α then omega2 s else 1)

/-- The odd residues modulo `8`. -/
theorem odd_lt_eight {r : Nat} (h1 : r < 8) (h2 : r % 2 = 1) :
    r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  omega

/-- The table in the case `(u, 2v)`: `1` iff `r ≡ 1` or `r + 2s ≡ 1 (mod 8)`. -/
theorem table2_false_true {r s : Nat} (hr : r < 8) (hr' : r % 2 = 1) (hs : s < 8)
    (hs' : s % 2 = 1) :
    table2 false true r s = if r = 1 ∨ (r + 2 * s) % 8 = 1 then 1 else -1 := by
  rcases odd_lt_eight hr hr' with h | h | h | h <;>
  rcases odd_lt_eight hs hs' with h' | h' | h' | h' <;> subst h h' <;> decide

/-- The table is symmetric under exchanging `(α, r)` and `(β, s)`. -/
theorem table2_swap (α β : Bool) (r s : Nat) : table2 β α s r = table2 α β r s := by
  unfold table2 eps2
  cases α <;> cases β <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
  by_cases h1 : r % 4 = 3 <;> by_cases h2 : s % 4 = 3 <;> simp [h1, h2] <;> grind

/-- The case `(2u, 2v)` of the table: `(2u, 2v)₂ = (−uv, 2u)₂`. -/
theorem table2_true_true {r s : Nat} (hr : r < 8) (hr' : r % 2 = 1) (hs : s < 8)
    (hs' : s % 2 = 1) : table2 false true (7 * r * s % 8) r = table2 true true r s := by
  rcases odd_lt_eight hr hr' with h | h | h | h <;>
  rcases odd_lt_eight hs hs' with h' | h' | h' | h' <;> subst h h' <;> decide

/-- **Multiplicativity of the table at `2`** in the second unit and the `xor` of the second
exponent (residues of units, i.e. odd residues modulo `8`). -/
theorem table2_mul (α β β' : Bool) {r s s' : Nat} (hr : r < 8) (hr' : r % 2 = 1) (hs : s < 8)
    (hs' : s % 2 = 1) (ht : s' < 8) (ht' : s' % 2 = 1) :
    table2 α (β != β') r (s * s' % 8) = table2 α β r s * table2 α β' r s' := by
  rcases odd_lt_eight hr hr' with h | h | h | h <;>
  rcases odd_lt_eight hs hs' with h' | h' | h' | h' <;>
  rcases odd_lt_eight ht ht' with h'' | h'' | h'' | h'' <;> subst h h' h'' <;>
  cases α <;> cases β <;> cases β' <;> decide

/-! ## The symbols involving `2` -/

namespace Qp

/-- **The conic `z² = u x² + 2v y²` over ℚ₂.** For units `u, v` of ℤ₂ it has a non-trivial
point iff `u ≡ 1` or `u + 2v ≡ 1 (mod 8)`. -/
theorem hilbertSolvable_unit_two_iff {u v : Zp 2} (hu : Zp.IsPUnit u) (hv : Zp.IsPUnit v) :
    HilbertSolvable (ofZp u) (ofZp (((2 : Nat) : Zp 2) * v)) ↔
      Zp.res8 u = 1 ∨ (Zp.res8 u + 2 * Zp.res8 v) % 8 = 1 := by
  constructor
  · intro hs
    have hs' : HilbertSolvable (ofZp u) (ofZp (((2 : Int) : Zp 2) * v)) := hs
    obtain ⟨X, Y, Z, hprim, h⟩ := exists_primitive hs'
    have hX := Zp.modPow_rep 3 X
    have hY := Zp.modPow_rep 3 Y
    have hZ := Zp.modPow_rep 3 Z
    have hu8 := Zp.modPow_rep 3 u
    have hv8 := Zp.modPow_rep 3 v
    have H : Zp.ModPow 3 (Z * Z)
        (((Zp.rep u).seq 3 : Zp 2) * (((Zp.rep X).seq 3 : Zp 2) * ((Zp.rep X).seq 3 : Zp 2)) +
          ((2 : Int) : Zp 2) * (((Zp.rep v).seq 3 : Zp 2) *
            (((Zp.rep Y).seq 3 : Zp 2) * ((Zp.rep Y).seq 3 : Zp 2)))) := by
      rw [h, show u * (X * X) + ((2 : Int) : Zp 2) * v * (Y * Y) =
        u * (X * X) + ((2 : Int) : Zp 2) * (v * (Y * Y)) by grind]
      exact (hu8.mul hX.sq).add ((Zp.ModPow.refl 3 _).mul (hv8.mul hY.sq))
    have H2 := hZ.sq.symm.trans H
    simp only [← Ring.intCast_mul, ← Ring.intCast_add] at H2
    have H3 := Zp.modPow_intCast.1 H2
    rw [Zp.two_pow_three] at H3
    have hk := key_mod8 (Zp.odd_rep_of_isPUnit hu 3 (by omega))
      (Zp.odd_rep_of_isPUnit hv 3 (by omega)) H3 (fun ⟨ha, hb, hc⟩ => hprim
        ⟨(hX.mono (by omega)).trans (Zp.modPow_intCast_zero (Int.dvd_of_emod_eq_zero ha)),
          (hY.mono (by omega)).trans (Zp.modPow_intCast_zero (Int.dvd_of_emod_eq_zero hb)),
          (hZ.mono (by omega)).trans (Zp.modPow_intCast_zero (Int.dvd_of_emod_eq_zero hc))⟩)
    unfold Zp.res8
    have := Int.emod_nonneg ((Zp.rep u).seq 3) (by decide : (8 : Int) ≠ 0)
    have := Int.emod_nonneg ((Zp.rep v).seq 3) (by decide : (8 : Int) ≠ 0)
    omega
  · rintro (h1 | h1)
    · obtain ⟨X, hX⟩ := Zp.exists_sq_of_modPow_eight (Zp.modPow_one_of_res8 h1)
      refine ⟨1, 0, ofZp X, Or.inl one_ne_zero', ?_⟩
      rw [← ofZp_mul, hX]; grind
    · have hw : Zp.ModPow 3 (u + ((2 : Nat) : Zp 2) * v) ((1 : Int) : Zp 2) := by
        have h2 := (Zp.modPow_res8 u).add ((Zp.ModPow.refl 3 ((2 : Int) : Zp 2)).mul
          (Zp.modPow_res8 v))
        rw [← Ring.intCast_mul, ← Ring.intCast_add] at h2
        refine h2.trans (Zp.modPow_intCast.2 ?_)
        rw [Zp.two_pow_three]
        omega
      obtain ⟨Z, hZ⟩ := Zp.exists_sq_of_modPow_eight hw
      refine ⟨1, 1, ofZp Z, Or.inl one_ne_zero', ?_⟩
      rw [← ofZp_mul, hZ, ofZp_add, ofZp_mul]; grind

/-- **`(u, 2v)₂`** for units `u, v` of ℤ₂: the table value `table2 false true`, i.e.
`(−1)^(ε(u) ε(v) + ω(u))`. -/
theorem hilbert_unit_two {u v : Zp 2} (hu : Zp.IsPUnit u) (hv : Zp.IsPUnit v) :
    hilbert (ofZp u) (ofZp (((2 : Nat) : Zp 2) * v)) =
      table2 false true (Zp.res8 u) (Zp.res8 v) := by
  have key := hilbertSolvable_unit_two_iff hu hv
  rw [table2_false_true (Zp.res8_lt u) (Zp.res8_odd hu) (Zp.res8_lt v) (Zp.res8_odd hv)]
  by_cases hc : Zp.res8 u = 1 ∨ (Zp.res8 u + 2 * Zp.res8 v) % 8 = 1
  · simp only [hc, ite_true]; exact (hilbert_eq_one_iff _ _).2 (key.2 hc)
  · simp only [hc, ite_false]
    exact (hilbert_eq_neg_one_iff _ _).2 (fun h => hc (key.1 h))

/-- `(u, v)₂` for units, in terms of the table: `table2 false false`. -/
theorem hilbert_units_two {u v : Zp 2} (hu : Zp.IsPUnit u) (hv : Zp.IsPUnit v) :
    hilbert (ofZp u) (ofZp v) = table2 false false (Zp.res8 u) (Zp.res8 v) := by
  rw [hilbert_two_units hu hv]
  by_cases hc : Zp.res8 u % 4 = 3 ∧ Zp.res8 v % 4 = 3
  · have hc' : Zp.ModPow 2 u ((3 : Int) : Zp 2) ∧ Zp.ModPow 2 v ((3 : Int) : Zp 2) :=
      ⟨(Zp.modPow_three_iff u).2 hc.1, (Zp.modPow_three_iff v).2 hc.2⟩
    simp only [hc', and_self, ite_true]
    simp [table2, eps2, hc]
  · have hc' : ¬ (Zp.ModPow 2 u ((3 : Int) : Zp 2) ∧ Zp.ModPow 2 v ((3 : Int) : Zp 2)) := fun h =>
      hc ⟨(Zp.modPow_three_iff u).1 h.1, (Zp.modPow_three_iff v).1 h.2⟩
    simp only [hc', ite_false]
    simp [table2, eps2, hc]

/-- **The Hilbert symbol formula at `2`.** For units `u, v` of ℤ₂ and `α, β ∈ {0, 1}`,
`(2^α u, 2^β v)₂ = table2 α β (u mod 8) (v mod 8) = (−1)^(ε(u) ε(v) + α ω(v) + β ω(u))`. -/
theorem hilbert_std_two (α β : Bool) {u v : Zp 2} (hu : Zp.IsPUnit u) (hv : Zp.IsPUnit v) :
    hilbert (std α u) (std β v) = table2 α β (Zp.res8 u) (Zp.res8 v) := by
  cases α <;> cases β
  · exact hilbert_units_two hu hv
  · exact hilbert_unit_two hu hv
  · rw [hilbert_comm, ← table2_swap]; exact hilbert_unit_two hv hu
  · -- `(2u, 2v) = (2u, −4uv) = (2u, −uv) = (−uv, 2u)`
    show hilbert (ofZp (((2 : Nat) : Zp 2) * u)) (ofZp (((2 : Nat) : Zp 2) * v)) = _
    rw [hilbert_neg_mul (ofZp_pv_ne_zero hu)]
    have hP0 : ofZp ((2 : Nat) : Zp 2) ≠ 0 := fun h0 =>
      zp_p_ne_zero (ofZp_injective (h0.trans rfl))
    have e : -(ofZp (((2 : Nat) : Zp 2) * u) * ofZp (((2 : Nat) : Zp 2) * v)) =
        ofZp ((2 : Nat) : Zp 2) * ofZp ((2 : Nat) : Zp 2) * ofZp ((-1 : Zp 2) * u * v) := by
      rw [ofZp_mul, ofZp_mul, ofZp_mul, ofZp_mul, show ofZp (-1 : Zp 2) = -1 from rfl]; grind
    rw [e, hilbert_mul_sq_right hP0, hilbert_comm]
    have hw : Zp.IsPUnit ((-1 : Zp 2) * u * v) :=
      (Zp.isPUnit_neg_one.mul prime_two hu).mul prime_two hv
    rw [hilbert_unit_two hw hu, Zp.res8_mul, Zp.res8_mul, Zp.res8_neg_one,
      show 7 * Zp.res8 u % 8 * Zp.res8 v % 8 = 7 * Zp.res8 u * Zp.res8 v % 8 by
        rw [Nat.mod_mul_mod]]
    exact table2_true_true (Zp.res8_lt u) (Zp.res8_odd hu) (Zp.res8_lt v) (Zp.res8_odd hv)

/-- **Bilinearity of the Hilbert symbol at `2`.** For non-zero `a, b, b' ∈ ℚ₂`,
`(a, b b')₂ = (a, b)₂ (a, b')₂`. -/
theorem hilbert_mul_right_two {a b b' : Qp 2} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbert a (b * b') = hilbert a b * hilbert a b' := by
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
    hilbert_std_two _ _ hu (Zp.IsPUnit.mul prime_two hv hv'), hilbert_std_two _ _ hu hv,
    hilbert_std_two _ _ hu hv', Zp.res8_mul]
  exact table2_mul α β β' (Zp.res8_lt u) (Zp.res8_odd hu) (Zp.res8_lt v) (Zp.res8_odd hv)
    (Zp.res8_lt v') (Zp.res8_odd hv')

/-- **Bilinearity at `2` in the first argument.** For non-zero `a, a', b ∈ ℚ₂`,
`(a a', b)₂ = (a, b)₂ (a', b)₂`. -/
theorem hilbert_mul_left_two {a a' b : Qp 2} (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbert (a * a') b = hilbert a b * hilbert a' b := by
  rw [hilbert_comm, hilbert_mul_right_two hb ha ha', hilbert_comm b a, hilbert_comm b a']

end Qp

end Foundations.Langlands.Padic
