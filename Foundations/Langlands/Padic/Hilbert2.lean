import Foundations.Langlands.Padic.Primitive
import Foundations.Langlands.Padic.StrongHensel

/-!
# The Hilbert symbol at `2` for units

At `p = 2` the simple Hensel lemma never applies to `X² − u` (the derivative `2X` is always
even), and squares are detected modulo `8`: a `2`-adic integer `u ≡ 1 (mod 8)` is a square in
ℤ₂ (`Zp.exists_sq_of_modPow_eight`). As at odd primes, the strong Hensel lemma
(`hensel_strong`) is applied to integer approximations of `u`, and compactness of ℤ₂ supplies
the root.

**`Qp.hilbert_two_units`.** For units `u, v` of ℤ₂, `(u, v)₂ = −1` iff `u ≡ v ≡ 3 (mod 4)`;
that is, `(u, v)₂ = (−1)^(ε(u) ε(v))` with `ε(u) = (u − 1)/2 mod 2`.

* If `u ≡ 1 (mod 8)`, `u` is a square and `(1, 0, √u)` is a point.
* If `u ≡ 5 (mod 8)`, then `u + 4v ≡ 1 (mod 8)` is a square `z²`, and `(1, 2, z)` is a point.
* If `u ≡ v ≡ 3 (mod 4)`, a primitive solution (`Qp.exists_primitive`) would give
  `z² + x² + y² ≡ 0 (mod 4)` with one of `x, y, z` odd; but squares are `0` or `1` mod `4`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- `2` is prime, as an instance (so that ℚ₂ is available). -/
instance primeP_two : PrimeP 2 := ⟨prime_two⟩

/-! ## Integer lemmas modulo 4 and 8 -/

/-- Squares modulo `4`: `a² ≡ 0` for even `a` and `a² ≡ 1` for odd `a`. -/
theorem int_sq_mod4 (a : Int) :
    (a % 2 = 0 ∧ ∃ M, a * a = 4 * M) ∨ (a % 2 = 1 ∧ ∃ M, a * a = 4 * M + 1) := by
  have h : a = 2 * (a / 2) + a % 2 := by omega
  generalize a / 2 = k at h
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with h2 | h2
  · left; refine ⟨h2, k * k, ?_⟩; rw [h2] at h; rw [h]; grind
  · right; refine ⟨h2, k * k + k, ?_⟩; rw [h2] at h; rw [h]; grind

/-- If `4 ∣ c² − 3a² − 3b²` then `a`, `b`, `c` are all even. -/
theorem even_of_four_dvd {a b c : Int} (h : (4 : Int) ∣ c * c - (3 * (a * a) + 3 * (b * b))) :
    a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 := by
  obtain ⟨t, ht⟩ := h
  rcases int_sq_mod4 a with ⟨ha, M, hM⟩ | ⟨ha, M, hM⟩ <;>
  rcases int_sq_mod4 b with ⟨hb, N, hN⟩ | ⟨hb, N, hN⟩ <;>
  rcases int_sq_mod4 c with ⟨hc, L, hL⟩ | ⟨hc, L, hL⟩ <;>
  · rw [hM, hN, hL] at ht; omega

namespace Zp

/-- **Squares in ℤ₂.** A `2`-adic integer `u ≡ 1 (mod 8)` is a square in ℤ₂. -/
theorem exists_sq_of_modPow_eight {u : Zp 2} (h : ModPow 3 u ((1 : Int) : Zp 2)) :
    ∃ x : Zp 2, x * x = u := by
  let c : Nat → Int := fun N => (rep u).seq (N + 3)
  have hc : ∀ N, (8 : Int) ∣ c N - 1 := by
    intro N
    have h1 : ModPow 3 ((c N : Int) : Zp 2) ((1 : Int) : Zp 2) :=
      ((modPow_rep (N + 3) u).mono (by omega)).symm.trans h
    exact modPow_intCast.1 h1
  have hroot : ∀ N, ∃ x : Zp 2, x * x = ((c N : Int) : Zp 2) := by
    intro N
    obtain ⟨x, hx, -⟩ := hensel_strong prime_two [-(c N), 0, 1] 1 1
      (by show ((2 : Nat) : Int) ^ 1 ∣ (0 + 1 * (1 + 1 * 0)) + 1 * ((1 + 1 * 0) + 1 * (0 + 1 * 0))
          decide)
      (by show ¬ ((2 : Nat) : Int) ^ (1 + 1) ∣
            (0 + 1 * (1 + 1 * 0)) + 1 * ((1 + 1 * 0) + 1 * (0 + 1 * 0))
          decide)
      (by
        show ((2 : Nat) : Int) ^ (2 * 1 + 1) ∣ -(c N) + 1 * (0 + 1 * (1 + 1 * 0))
        rw [show -(c N) + 1 * (0 + 1 * (1 + 1 * 0)) = -(c N - 1) by omega]
        exact Int.dvd_neg.2 (hc N))
    refine ⟨x, ?_⟩
    rw [peval_sq_sub] at hx
    have := congrArg (· + ((c N : Int) : Zp 2)) hx
    rw [show x * x - ((c N : Int) : Zp 2) + ((c N : Int) : Zp 2) = x * x by grind,
      show (0 : Zp 2) + ((c N : Int) : Zp 2) = ((c N : Int) : Zp 2) by grind] at this
    exact this
  let xs : Nat → Zp 2 := fun N => Classical.choose (hroot N)
  have hxs : ∀ N, xs N * xs N = ((c N : Int) : Zp 2) := fun N => Classical.choose_spec (hroot N)
  have hxu : ∀ N, ModPow (N + 3) (xs N * xs N) u := fun N => by
    rw [hxs N]; exact (modPow_rep (N + 3) u).symm
  obtain ⟨φ, hφ, L, hL⟩ := seqCompact prime_two xs
  have hφge : ∀ i, i ≤ φ i := by
    intro i; induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := hφ i; omega
  refine ⟨L, eq_iff_modPow.2 fun k => ?_⟩
  obtain ⟨N, hN⟩ := hL k
  have h1 := (hN (max N k) (Nat.le_max_left _ _)).sq
  have h2 := (hxu (φ (max N k))).mono (show k ≤ φ (max N k) + 3 by
    have := hφge (max N k); omega)
  exact h1.symm.trans h2

/-- A unit of ℤ₂ is odd modulo `8`: its third digit `(rep u).seq 3` is odd. -/
theorem odd_rep_of_isPUnit {u : Zp 2} (hu : IsPUnit u) (k : Nat) (hk : 1 ≤ k) :
    (rep u).seq k % 2 = 1 := by
  apply Classical.byContradiction; intro h
  apply hu
  refine ((modPow_rep k u).mono hk).trans (modPow_intCast_zero ?_)
  exact Int.dvd_of_emod_eq_zero (by omega)

/-- A unit of ℤ₂ is `≡ 1` or `≡ 3 (mod 4)`. -/
theorem unit_mod_four {u : Zp 2} (hu : IsPUnit u) :
    ModPow 2 u ((1 : Int) : Zp 2) ∨ ModPow 2 u ((3 : Int) : Zp 2) := by
  have h := odd_rep_of_isPUnit hu 2 (by omega)
  have hr := modPow_rep 2 u
  rcases (by omega : (rep u).seq 2 % 4 = 1 ∨ (rep u).seq 2 % 4 = 3) with h4 | h4
  · exact Or.inl (hr.trans (modPow_intCast.2 (Int.dvd_of_emod_eq_zero (by omega))))
  · exact Or.inr (hr.trans (modPow_intCast.2 (Int.dvd_of_emod_eq_zero (by omega))))

end Zp

namespace Qp

/-- If `u ≡ 1 (mod 4)` (and `v` is a unit), then `(u, v)₂ = 1`. -/
theorem hilbert_two_of_one_mod_four {u v : Zp 2} (hu : Zp.ModPow 2 u ((1 : Int) : Zp 2))
    (hv : Zp.IsPUnit v) : hilbert (ofZp u) (ofZp v) = 1 := by
  apply (hilbert_eq_one_iff _ _).2
  have hcu := (Zp.modPow_rep 3 u)
  have h4 : (4 : Int) ∣ (Zp.rep u).seq 3 - 1 :=
    Zp.modPow_intCast.1 (((hcu.mono (by omega)).symm).trans hu)
  have hv1 := Zp.odd_rep_of_isPUnit hv 3 (by omega)
  rcases (by omega : (Zp.rep u).seq 3 % 8 = 1 ∨ (Zp.rep u).seq 3 % 8 = 5) with h8 | h8
  · -- `u` is a square
    obtain ⟨X, hX⟩ := Zp.exists_sq_of_modPow_eight
      (hcu.trans (Zp.modPow_intCast.2 (Int.dvd_of_emod_eq_zero (by omega))))
    refine ⟨1, 0, ofZp X, Or.inl one_ne_zero', ?_⟩
    rw [← ofZp_mul, hX]; grind
  · -- `u + 4 v` is a square
    have hw : Zp.ModPow 3 (u + ((4 : Int) : Zp 2) * v) ((1 : Int) : Zp 2) := by
      have h1 := hcu.add ((Zp.ModPow.refl 3 ((4 : Int) : Zp 2)).mul (Zp.modPow_rep 3 v))
      rw [← Ring.intCast_mul, ← Ring.intCast_add] at h1
      exact h1.trans (Zp.modPow_intCast.2 (Int.dvd_of_emod_eq_zero (by omega)))
    obtain ⟨Z, hZ⟩ := Zp.exists_sq_of_modPow_eight hw
    refine ⟨1, ofZp ((2 : Int) : Zp 2), ofZp Z, Or.inl one_ne_zero', ?_⟩
    rw [← ofZp_mul, hZ, ofZp_add, ofZp_mul, ← ofZp_mul ((2 : Int) : Zp 2), ← Ring.intCast_mul,
      show ((2 * 2 : Int) : Zp 2) = ((4 : Int) : Zp 2) from rfl]
    grind

/-- If `u ≡ v ≡ 3 (mod 4)`, then `(u, v)₂ = −1`. -/
theorem hilbert_two_of_three_mod_four {u v : Zp 2} (hu : Zp.ModPow 2 u ((3 : Int) : Zp 2))
    (hv : Zp.ModPow 2 v ((3 : Int) : Zp 2)) : hilbert (ofZp u) (ofZp v) = -1 := by
  apply (hilbert_eq_neg_one_iff _ _).2
  intro hs
  obtain ⟨X, Y, Z, hprim, h⟩ := exists_primitive hs
  have hX := Zp.modPow_rep 2 X
  have hY := Zp.modPow_rep 2 Y
  have hZ := Zp.modPow_rep 2 Z
  have H : Zp.ModPow 2 (Z * Z) (((3 : Int) : Zp 2) * (((Zp.rep X).seq 2 : Int) * ((Zp.rep X).seq 2 : Int))
      + ((3 : Int) : Zp 2) * (((Zp.rep Y).seq 2 : Int) * ((Zp.rep Y).seq 2 : Int))) := by
    rw [h]; exact (hu.mul hX.sq).add (hv.mul hY.sq)
  have H2 := hZ.sq.symm.trans H
  simp only [← Ring.intCast_mul, ← Ring.intCast_add] at H2
  have H3 := Zp.modPow_intCast.1 H2
  obtain ⟨ha, hb, hc⟩ := even_of_four_dvd H3
  apply hprim
  refine ⟨(hX.mono (by omega)).trans (Zp.modPow_intCast_zero (Int.dvd_of_emod_eq_zero ha)),
    (hY.mono (by omega)).trans (Zp.modPow_intCast_zero (Int.dvd_of_emod_eq_zero hb)),
    (hZ.mono (by omega)).trans (Zp.modPow_intCast_zero (Int.dvd_of_emod_eq_zero hc))⟩

open Classical in
/-- **The Hilbert symbol at `2` on units.** For units `u, v` of ℤ₂, `(u, v)₂ = −1` iff
`u ≡ 3` and `v ≡ 3 (mod 4)`, and `(u, v)₂ = 1` otherwise. -/
theorem hilbert_two_units {u v : Zp 2} (hu : Zp.IsPUnit u) (hv : Zp.IsPUnit v) :
    hilbert (ofZp u) (ofZp v) =
      if Zp.ModPow 2 u ((3 : Int) : Zp 2) ∧ Zp.ModPow 2 v ((3 : Int) : Zp 2) then -1 else 1 := by
  by_cases h : Zp.ModPow 2 u ((3 : Int) : Zp 2) ∧ Zp.ModPow 2 v ((3 : Int) : Zp 2)
  · simp only [h, and_self, ite_true]; exact hilbert_two_of_three_mod_four h.1 h.2
  · simp only [h, ite_false]
    rcases Zp.unit_mod_four hu with hu1 | hu3
    · exact hilbert_two_of_one_mod_four hu1 hv
    · rcases Zp.unit_mod_four hv with hv1 | hv3
      · rw [hilbert_comm]; exact hilbert_two_of_one_mod_four hv1 hu
      · exact absurd ⟨hu3, hv3⟩ h

end Qp

end Foundations.Langlands.Padic
