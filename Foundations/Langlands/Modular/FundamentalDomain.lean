import Foundations.Langlands.Modular.Action

/-!
# The fundamental domain of SL₂(ℤ)

Gauss already knew, in the language of binary quadratic forms (*Disquisitiones*, 1801), that
every positive definite form is equivalent to a *reduced* one. Translated into the action of
SL₂(ℤ) on the upper half-plane by Dedekind (1877) and Klein (1879), this becomes the
statement that the curvilinear triangle

  `F = { τ ∈ ℍ : |Re τ| ≤ 1/2, |τ| ≥ 1 }`

meets every orbit: Klein's "modular figure" is the tessellation of ℍ by the images `γF`.
Poincaré turned such fundamental polygons into the main tool for constructing automorphic
functions for arbitrary Fuchsian groups.

## The argument formalised here (`exists_mem_F`)

Fix `τ = x + iy ∈ ℍ`. By `Action.im_mob`, `Im (γτ) = y / |cτ + d|²`, so making `Im` large
means making `|cτ + d|² = (cx + d)² + (cy)²` small.

1. **Finiteness** (`bounds`). If `|cτ + d|² ≤ 1` then `|cy| ≤ 1` and `|cx + d| ≤ 1`, so `c`
   and then `d` lie in a box `[−N, N] × [−M, M]` depending only on `τ`. Only finitely many
   bottom rows `(c, d)` can therefore beat the identity.
2. **A maximum exists** (`exists_max_im`). Minimising `|cτ + d|²` over the finite list of
   pairs in the box that occur as bottom rows (`list_argmin`) gives `γ₀` with
   `Im (γτ) ≤ Im (γ₀τ)` for **every** `γ ∈ SL₂(ℤ)`.
3. **Translate** by `T⁻ᵐ`, `m = ⌊Re(γ₀τ) + 1/2⌋`, to get `|Re| ≤ 1/2`; the imaginary part,
   and hence maximality, is unchanged.
4. **Invert.** If the result `τ'` had `|τ'| < 1`, then `Im (Sτ') = Im τ' / |τ'|² > Im τ'`
   would contradict maximality. So `|τ'| ≥ 1` and `τ' ∈ F`.

The conditions are stated with the squared modulus `|τ|² = normSq τ` (`|τ| ≥ 1 ⟺ |τ|² ≥ 1`,
`one_le_cabs_iff`). The uniqueness half (two interior points of `F` are equivalent only if
equal) is in `FundamentalDomainUnique`.
-/

namespace Foundations.Langlands.Modular

open Foundations.Numbers Foundations.Algebra Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

namespace SL2Z

/-- **The fundamental domain F.** `τ ∈ F` iff `|Re τ| ≤ 1/2` and `|τ|² ≥ 1`. -/
def InF (z : C) : Prop := OF.abs z.re ≤ 1 / 2 ∧ 1 ≤ C.normSq z

/-- `|τ| ≥ 1` iff `|τ|² ≥ 1`, so `InF` is the usual condition `|τ| ≥ 1`. -/
theorem one_le_cabs_iff (z : C) : 1 ≤ C.cabs z ↔ 1 ≤ C.normSq z := by
  have h0 := C.cabs_nonneg z
  have hm := C.cabs_mul_self z
  constructor
  · intro h
    have := OrderedRing.mul_le_mul_of_nonneg_left h h0
    have := OrderedRing.mul_le_mul_of_nonneg_right h (by grind : (0 : R) ≤ 1)
    grind
  · intro h
    exact R.le_of_mul_self_le h0 (by grind)

/-- Comparison of quotients: if `0 < y` and `0 < a ≤ b` then `y / b ≤ y / a`. -/
theorem div_le_div_left {y a b : R} (hy : 0 < y) (ha : 0 < a) (hab : a ≤ b) : y / b ≤ y / a := by
  have hb : 0 < b := by grind
  have ha0 : a ≠ 0 := by grind
  have hb0 : b ≠ 0 := by grind
  have e : y / a - y / b = (y * (b - a)) * (1 / (a * b)) := by grind
  have h1 : 0 ≤ y * (b - a) := OrderedRing.mul_nonneg (by grind) (by grind)
  have h2 : 0 < 1 / (a * b) := OF.div_pos (by grind) (OrderedRing.mul_pos ha hb)
  have := OrderedRing.mul_nonneg h1 (by grind : (0 : R) ≤ 1 / (a * b))
  grind

/-- If `0 < y` and `0 < N < 1` then `y < y / N`. -/
theorem lt_div_self {y N : R} (hy : 0 < y) (hN : 0 < N) (h1 : N < 1) : y < y / N := by
  have hN0 : N ≠ 0 := by grind
  have e : y / N - y = (y * (1 - N)) * (1 / N) := by grind
  have := OrderedRing.mul_pos (OrderedRing.mul_pos hy (by grind : (0 : R) < 1 - N))
    (OF.div_pos (by grind : (0 : R) < 1) hN)
  grind

/-- Integer casts into `ℝ` reflect `≤`. -/
theorem intCast_le {m n : Int} (h : (m : R) ≤ (n : R)) : m ≤ n := by
  apply Classical.byContradiction; intro hmn
  have := (OF.intCast_lt (K := R)).2 (by omega : n < m); grind

/-- Integer casts into `ℝ` preserve `≤`. -/
theorem intCast_le_of_le {m n : Int} (h : m ≤ n) : (m : R) ≤ (n : R) := by
  rcases Int.lt_or_eq_of_le h with h | h
  · have := (OF.intCast_lt (K := R)).2 h; grind
  · rw [h]; grind

/-- The quantity `|cτ + d|² = (cx + d)² + (cy)²` as a function of the bottom row `(c, d)`. -/
def Q (z : C) (c d : Int) : R :=
  ((c : R) * z.re + d) * ((c : R) * z.re + d) + ((c : R) * z.im) * ((c : R) * z.im)

/-- `|j(γ, τ)|² = Q τ c d`. -/
theorem normSq_denom_eq_Q (g : SL2Z) (z : C) : C.normSq (denom g z) = Q z g.c g.d :=
  normSq_denom g z

/-- **Finiteness of small automorphy factors.** For `τ ∈ ℍ` there are bounds `N`, `M` such
that `|cτ + d|² ≤ 1` forces `|c| ≤ N` and `|d| ≤ M`. -/
theorem bounds (z : C) (hz : 0 < z.im) : ∃ N M : Nat, 1 ≤ M ∧ ∀ c d : Int, Q z c d ≤ 1 →
    (-(N : Int) ≤ c ∧ c ≤ N) ∧ (-(M : Int) ≤ d ∧ d ≤ M) := by
  obtain ⟨n, hn⟩ := R.archimedean (1 / z.im)
  have hn' : 1 < ((n : Int) : R) * z.im := by
    rw [Ring.intCast_natCast]
    have := OrderedRing.mul_lt_mul_of_pos_right hn hz
    have e : 1 / z.im * z.im = 1 := by have : z.im ≠ 0 := by grind
                                       grind
    grind
  have hn0 : (0 : R) ≤ ((n : Int) : R) := by
    have := intCast_le_of_le (m := 0) (n := (n : Int)) (by omega)
    rw [Ring.intCast_zero] at this; exact this
  obtain ⟨m, hm⟩ := R.archimedean (1 + ((n : Int) : R) * OF.abs z.re)
  have hm' : 1 + ((n : Int) : R) * OF.abs z.re < ((m : Int) : R) := by
    rw [Ring.intCast_natCast]; exact hm
  have hax := OF.abs_nonneg z.re
  have hm1 : 1 ≤ m := by
    have := OrderedRing.mul_nonneg hn0 hax
    have : ((1 : Int) : R) ≤ ((m : Int) : R) := by rw [Ring.intCast_one]; grind
    have := intCast_le this; omega
  refine ⟨n, m, hm1, fun c d hQ => ?_⟩
  unfold Q at hQ
  have hs1 := C.mul_self_nonneg ((c : R) * z.re + d)
  have hs2 := C.mul_self_nonneg ((c : R) * z.im)
  obtain ⟨hcy1, hcy2⟩ := R.abs_le_one_of_sq (x := (c : R) * z.im) (by grind)
  obtain ⟨hd1, hd2⟩ := R.abs_le_one_of_sq (x := (c : R) * z.re + d) (by grind)
  have hcN : c ≤ n := by
    apply Classical.byContradiction; intro h
    have h' := intCast_le_of_le (by omega : (n : Int) ≤ c)
    have := OrderedRing.mul_le_mul_of_nonneg_right h' (by grind : (0 : R) ≤ z.im)
    grind
  have hcN' : -(n : Int) ≤ c := by
    apply Classical.byContradiction; intro h
    have h' := intCast_le_of_le (by omega : c ≤ -(n : Int))
    rw [Ring.intCast_neg] at h'
    have := OrderedRing.mul_le_mul_of_nonneg_right h' (by grind : (0 : R) ≤ z.im)
    grind
  have hcabs : OF.abs (c : R) ≤ ((n : Int) : R) := by
    have h1 := intCast_le_of_le hcN
    have h2 := intCast_le_of_le hcN'
    rw [Ring.intCast_neg] at h2
    exact OF.abs_le.2 ⟨h2, h1⟩
  have hcx : OF.abs ((c : R) * z.re) ≤ ((n : Int) : R) * OF.abs z.re := by
    rw [OF.abs_mul]; exact OrderedRing.mul_le_mul_of_nonneg_right hcabs hax
  have hle := OF.le_abs ((c : R) * z.re)
  refine ⟨⟨hcN', hcN⟩, ?_, ?_⟩
  · have : ((-(m : Int) : Int) : R) ≤ (d : R) := by rw [Ring.intCast_neg]; grind
    exact intCast_le this
  · have : (d : R) ≤ ((m : Int) : R) := by grind
    exact intCast_le this

/-- The finite box `[−N, N] × [−M, M]` of integer pairs, as a list. -/
def box (N M : Nat) : List (Int × Int) :=
  (List.range (2 * N + 1)).flatMap fun (i : Nat) =>
    (List.range (2 * M + 1)).map fun (j : Nat) => ((i : Int) - N, (j : Int) - M)

/-- Every pair with `|c| ≤ N`, `|d| ≤ M` lies in `box N M`. -/
theorem mem_box {N M : Nat} {c d : Int} (hc : -(N : Int) ≤ c ∧ c ≤ N)
    (hd : -(M : Int) ≤ d ∧ d ≤ M) : (c, d) ∈ box N M := by
  simp only [box, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨(c + N).toNat, by omega, (d + M).toNat, by omega, ?_⟩
  simp only [Prod.mk.injEq]; omega

/-- **Minimum over a finite list.** If some element of a list satisfies `P`, then one such
element minimises `f` among all elements of the list satisfying `P`. -/
theorem list_argmin {α : Type} (f : α → R) (P : α → Prop) :
    ∀ L : List α, (∃ x ∈ L, P x) → ∃ x ∈ L, P x ∧ ∀ y ∈ L, P y → f x ≤ f y
  | [], ⟨_, h, _⟩ => by simp at h
  | a :: t, hex => by
    by_cases ht : ∃ x ∈ t, P x
    · obtain ⟨m, hm, hPm, hmin⟩ := list_argmin f P t ht
      by_cases hPa : P a ∧ f a ≤ f m
      · refine ⟨a, List.mem_cons_self, hPa.1, fun y hy hPy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · grind
        · have := hmin y hy hPy; grind
      · refine ⟨m, List.mem_cons_of_mem a hm, hPm, fun y hy hPy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · grind
        · exact hmin y hy hPy
    · have hPa : P a := by
        obtain ⟨x, hx, hPx⟩ := hex
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hPx
        · exact absurd ⟨x, hx, hPx⟩ ht
      refine ⟨a, List.mem_cons_self, hPa, fun y hy hPy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · grind
      · exact absurd ⟨y, hy, hPy⟩ ht

/-- `Q τ c d > 0` whenever `(c, d)` is the bottom row of an element of SL₂(ℤ) and `τ ∈ ℍ`. -/
theorem Q_pos (g : SL2Z) {z : C} (hz : 0 < z.im) : 0 < Q z g.c g.d := by
  rw [← normSq_denom_eq_Q]; exact normSq_denom_pos g hz

/-- **The imaginary part attains its maximum on every orbit.** For `τ ∈ ℍ` there is
`γ₀ ∈ SL₂(ℤ)` with `Im (γτ) ≤ Im (γ₀τ)` for all `γ ∈ SL₂(ℤ)`. -/
theorem exists_max_im (p : UHP) : ∃ g₀ : SL2Z, ∀ g : SL2Z, (g • p).z.im ≤ (g₀ • p).z.im := by
  have hz := p.pos
  obtain ⟨N, M, hM, hb⟩ := bounds p.z hz
  let P : Int × Int → Prop := fun cd => ∃ g : SL2Z, g.c = cd.1 ∧ g.d = cd.2
  let f : Int × Int → R := fun cd => Q p.z cd.1 cd.2
  have hQ01 : f (0, 1) = 1 := by
    show Q p.z 0 1 = 1
    unfold Q; rw [Ring.intCast_zero, Ring.intCast_one]; grind
  have h01 : (0, 1) ∈ box N M := mem_box ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  obtain ⟨⟨c₀, d₀⟩, _, ⟨g₀, hc₀, hd₀⟩, hmin⟩ :=
    list_argmin f P (box N M) ⟨(0, 1), h01, ⟨1, rfl, rfl⟩⟩
  simp only at hc₀ hd₀
  have hle1 : f (c₀, d₀) ≤ 1 := by rw [← hQ01]; exact hmin (0, 1) h01 ⟨1, rfl, rfl⟩
  refine ⟨g₀, fun g => ?_⟩
  have key : Q p.z g₀.c g₀.d ≤ Q p.z g.c g.d := by
    rw [hc₀, hd₀]
    by_cases hh : Q p.z g.c g.d ≤ 1
    · obtain ⟨hc, hd⟩ := hb g.c g.d hh
      exact hmin (g.c, g.d) (mem_box hc hd) ⟨g, rfl, rfl⟩
    · show f (c₀, d₀) ≤ _; grind
  rw [im_smul, im_smul, normSq_denom_eq_Q, normSq_denom_eq_Q]
  exact div_le_div_left hz (Q_pos g₀ hz) key

/-- `|τ|² > 0` on ℍ. -/
theorem normSq_pos_of_im {z : C} (hz : 0 < z.im) : 0 < C.normSq z := by
  have := C.mul_self_nonneg z.re
  have := OrderedRing.mul_pos hz hz
  unfold C.normSq; grind

/-- **Every point of ℍ is equivalent to a point of F.** For every `τ ∈ ℍ` there is
`γ ∈ SL₂(ℤ)` with `|Re (γτ)| ≤ 1/2` and `|γτ| ≥ 1`. -/
theorem exists_mem_F (p : UHP) : ∃ g : SL2Z, InF (g • p).z := by
  obtain ⟨g₀, hmax⟩ := exists_max_im p
  obtain ⟨m, hm1, hm2⟩ := OF.exists_floor (K := R) R.archimedean ((g₀ • p).z.re + 1 / 2)
  refine ⟨Tn (-m) * g₀, ?_, ?_⟩
  · rw [MulAction.mul_smul, smul_z, re_mob_Tn, Ring.intCast_neg]
    exact OF.abs_le.2 ⟨by grind, by grind⟩
  · apply Classical.byContradiction; intro hlt
    have hlt' : C.normSq (Tn (-m) • g₀ • p).z < 1 := by
      rw [MulAction.mul_smul] at hlt; grind
    have hpos := (Tn (-m) • g₀ • p).pos
    have hS := hmax (S * Tn (-m) * g₀)
    rw [MulAction.mul_smul, MulAction.mul_smul, smul_z S, im_mob_S] at hS
    have him : (Tn (-m) • g₀ • p).z.im = (g₀ • p).z.im := im_mob_Tn _ _
    have := lt_div_self hpos (normSq_pos_of_im hpos) hlt'
    grind

/-- **Fundamental domain, orbit form.** Every SL₂(ℤ)-orbit in ℍ meets `F`. -/
theorem orbit_meets_F (p : UHP) : ∃ q : UHP, MulAction.orbit SL2Z p q ∧ InF q.z := by
  obtain ⟨g, hg⟩ := exists_mem_F p
  exact ⟨g • p, ⟨g, rfl⟩, hg⟩

end SL2Z

end Foundations.Langlands.Modular
