import Foundations.Algebra.RootsOfUnity

/-!
# Kummer theory in commutation form: why radicals give abelian steps

The engine of Galois's criterion is a simple observation about how automorphisms act on a
newly adjoined radical. Let `M` be a field containing `K`, and let `a, b` be automorphisms of
`M` fixing every element of `K`. Let `x ∈ M` be a **radical of prime degree `p` over `K`** in
one of two forms:

1. **A root of unity**: `x^p = 1`. Then `a(x)` is again a `p`-th root of unity, so (if `x ≠ 1`)
   `a(x) = x^i` for some `i` (`RootsOfUnity`); likewise `b(x) = x^j`. Hence
   `a(b(x)) = x^{ij} = b(a(x))`.
2. **A Kummer radical**: `x^p = c ∈ K`, where `K` already contains a root of unity `ζ ≠ 1` of
   order `p`. Then `a(x)^p = a(c) = c = x^p`, so (if `x ≠ 0`) `a(x) = ζ^i x`; likewise
   `b(x) = ζ^j x`. Since `a, b` fix `ζ ∈ K`, `a(b(x)) = ζ^{i+j} x = b(a(x))`.

In both cases **`a` and `b` commute on `x`**, and therefore their commutator
`[a, b] = a b a⁻¹ b⁻¹` fixes `x` as well as `K`. This is the classical statement that
`Aut(K(x)/K)` is abelian (it embeds into `(ℤ/p)ˣ` in case 1 and into the cyclic group `μ_p` in
case 2), phrased without quotient groups: what the proof of Galois's criterion needs is exactly
that commutators of automorphisms fixing `K` also fix `K(x)` (proved in `GaloisCriterion`, from
`commutator_fixes_step` below).
-/

namespace Foundations.Algebra

open Group

universe u

variable {Ω : Type u} [CommRing Ω]

/-! ## Automorphisms fixing a subfield -/

/-- An automorphism `σ` of `M` **fixes** the subfield `K` if `σ(y) = y` for every `y ∈ M` that
lies in `K`. -/
def FieldAut.Fixes {F M : Subfield Ω} (σ : FieldAut F M) (K : Subfield Ω) : Prop :=
  ∀ y : M, y.1 ∈ K → σ.toFun y = y

/-- If `σ` fixes `y`, so does `σ⁻¹`. -/
theorem FieldAut.inv_fix {F M : Subfield Ω} (σ : FieldAut F M) {y : M} (h : σ.toFun y = y) :
    (σ⁻¹).toFun y = y :=
  σ.injective (by show σ.toFun (σ.invFun y) = σ.toFun y; rw [σ.right_inv, h])

/-- If `σ` fixes `K`, so does `σ⁻¹`. -/
theorem FieldAut.Fixes.inv {F M K : Subfield Ω} {σ : FieldAut F M} (h : σ.Fixes K) :
    (σ⁻¹).Fixes K :=
  fun y hy => σ.inv_fix (h y hy)

/-- If `σ` and `τ` fix `K`, so does `στ`. -/
theorem FieldAut.Fixes.mul {F M K : Subfield Ω} {σ τ : FieldAut F M} (hσ : σ.Fixes K)
    (hτ : τ.Fixes K) : (σ * τ).Fixes K :=
  fun y hy => by show σ.toFun (τ.toFun y) = y; rw [hτ y hy, hσ y hy]

/-- The identity fixes everything. -/
theorem FieldAut.fixes_one {F M : Subfield Ω} (K : Subfield Ω) : (1 : FieldAut F M).Fixes K :=
  fun _ _ => rfl

/-- **Commuting on `x` makes the commutator fix `x`.** If `a⁻¹` and `b⁻¹` commute on `x`, then
`[a, b] = a b a⁻¹ b⁻¹` fixes `x`. -/
theorem commutator_fix_of_commute {F M : Subfield Ω} (a b : FieldAut F M) (x : M)
    (h : (a⁻¹).toFun ((b⁻¹).toFun x) = (b⁻¹).toFun ((a⁻¹).toFun x)) :
    (commutator a b).toFun x = x := by
  show a.toFun (b.toFun ((a⁻¹).toFun ((b⁻¹).toFun x))) = x
  rw [h]
  show a.toFun (b.toFun (b.invFun (a.invFun x))) = x
  rw [b.right_inv, a.right_inv]

/-! ## Automorphisms commute on radicals -/

variable (hΩ : IsField Ω)
include hΩ

/-- **Roots of unity.** Any two automorphisms commute on a `p`-th root of unity (`p` prime):
each acts on it by raising to a power. -/
theorem unity_commute {p : Nat} (hp : IsPrime p) {F M : Subfield Ω} (x : M) (hx : rpow x.1 p = 1)
    (a b : FieldAut F M) : a.toFun (b.toFun x) = b.toFun (a.toFun x) := by
  by_cases h1 : x.1 = 1
  · have : x = 1 := Subtype.ext h1
    rw [this, a.map_one, b.map_one, a.map_one]
  · have hX : rpow x p = 1 := Subtype.ext (by rw [Subfield.coe_rpow, hx]; rfl)
    have hpow : ∀ c : FieldAut F M, ∃ k, c.toFun x = rpow x k := by
      intro c
      have hc : rpow (c.toFun x).1 p = 1 := by
        rw [← Subfield.coe_rpow, ← FieldAut.map_rpow, hX, c.map_one]; rfl
      obtain ⟨k, _, hk⟩ := eq_rpow_of_rpow_eq_one hΩ hp hx h1 hc
      exact ⟨k, Subtype.ext (by rw [hk, Subfield.coe_rpow])⟩
    obtain ⟨i, hi⟩ := hpow a
    obtain ⟨j, hj⟩ := hpow b
    rw [hj, FieldAut.map_rpow, hi, FieldAut.map_rpow, hj, ← rpow_mul', ← rpow_mul',
      Nat.mul_comm]

/-- **Kummer radicals.** Let `K ⊆ M` contain a `p`-th root of unity `ζ ≠ 1` (`p` prime), and let
`x ∈ M` with `x^p ∈ K`. Any two automorphisms of `M` fixing `K` commute on `x`: each multiplies
`x` by a power of `ζ`. -/
theorem kummer_commute {p : Nat} (hp : IsPrime p) {F M K : Subfield Ω} (hKM : K.le M) {ζ : Ω}
    (hζK : ζ ∈ K) (hζp : rpow ζ p = 1) (hζ1 : ζ ≠ 1) (x : M) (hxK : rpow x.1 p ∈ K)
    (a b : FieldAut F M) (ha : a.Fixes K) (hb : b.Fixes K) :
    a.toFun (b.toFun x) = b.toFun (a.toFun x) := by
  by_cases h0 : x.1 = 0
  · have : x = 0 := Subtype.ext h0
    rw [this, b.map_zero, a.map_zero, b.map_zero]
  · let Z : M := ⟨ζ, hKM _ hζK⟩
    have hmul : ∀ c : FieldAut F M, c.Fixes K → ∃ k, c.toFun x = rpow Z k * x := by
      intro c hc
      have e : rpow (c.toFun x) p = rpow x p := by
        rw [← FieldAut.map_rpow]
        exact hc _ (by rw [Subfield.coe_rpow]; exact hxK)
      have e' : rpow (c.toFun x).1 p = rpow x.1 p := by
        rw [← Subfield.coe_rpow, ← Subfield.coe_rpow, e]
      obtain ⟨k, hk⟩ := eq_mul_of_rpow_eq hΩ hp hζp hζ1 h0 e'
      exact ⟨k, Subtype.ext (by rw [Subfield.coe_mul, Subfield.coe_rpow]; exact hk)⟩
    have hZa : a.toFun Z = Z := ha Z hζK
    have hZb : b.toFun Z = Z := hb Z hζK
    obtain ⟨i, hi⟩ := hmul a ha
    obtain ⟨j, hj⟩ := hmul b hb
    rw [hj, a.map_mul, FieldAut.map_rpow, hZa, hi, b.map_mul, FieldAut.map_rpow, hZb, hj]
    ac_rfl

/-- **A radical step of prime degree** over `K`: `p` is prime, and either `x` is a `p`-th root
of unity, or `K` contains a `p`-th root of unity `ζ ≠ 1` and `x^p ∈ K`. -/
def KummerStep (K : Subfield Ω) (x : Ω) (p : Nat) : Prop :=
  IsPrime p ∧ (rpow x p = 1 ∨ ((∃ ζ, ζ ∈ K ∧ rpow ζ p = 1 ∧ ζ ≠ 1) ∧ rpow x p ∈ K))

omit hΩ in
/-- In a radical step, `x^p` lies in `K`. -/
theorem KummerStep.rpow_mem {K : Subfield Ω} {x : Ω} {p : Nat} (h : KummerStep K x p) :
    rpow x p ∈ K := by
  rcases h.2 with h1 | ⟨_, h2⟩
  · rw [h1]; exact K.one_mem
  · exact h2

/-- **Automorphisms fixing `K` commute on a radical step.** -/
theorem step_commute {K M F : Subfield Ω} {x : Ω} {p : Nat} (hs : KummerStep K x p)
    (hKM : K.le M) (hx : x ∈ M) (a b : FieldAut F M) (ha : a.Fixes K) (hb : b.Fixes K) :
    a.toFun (b.toFun ⟨x, hx⟩) = b.toFun (a.toFun ⟨x, hx⟩) := by
  rcases hs.2 with h1 | ⟨⟨ζ, hζK, hζp, hζ1⟩, h2⟩
  · exact unity_commute hΩ hs.1 ⟨x, hx⟩ h1 a b
  · exact kummer_commute hΩ hs.1 hKM hζK hζp hζ1 ⟨x, hx⟩ h2 a b ha hb

/-- **Commutators fix a radical step.** If `a, b` fix `K` and `x` is a radical step over `K`,
then the commutator `[a, b]` fixes `K` and `x`. (Hence, once we know that automorphisms fixing
`K` and `x` fix `K(x)`, commutators of automorphisms over `K` are automorphisms over `K(x)`:
the abelian character of `Aut(K(x)/K)`.) -/
theorem commutator_fixes_step {K M F : Subfield Ω} {x : Ω} {p : Nat} (hs : KummerStep K x p)
    (hKM : K.le M) (hx : x ∈ M) (a b : FieldAut F M) (ha : a.Fixes K) (hb : b.Fixes K) :
    (commutator a b).Fixes K ∧ (commutator a b).toFun ⟨x, hx⟩ = ⟨x, hx⟩ :=
  ⟨((ha.mul hb).mul ha.inv).mul hb.inv,
    commutator_fix_of_commute a b _ (step_commute hΩ hs hKM hx _ _ ha.inv hb.inv)⟩

end Foundations.Algebra
