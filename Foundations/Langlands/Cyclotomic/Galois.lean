import Foundations.Langlands.Cyclotomic.Field
import Foundations.Langlands.Cyclotomic.Reciprocity
import Foundations.NumberTheory.DirichletCharacters

/-!
# `Gal(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)ˣ`, Frobenius, and Dirichlet characters

**Theorem.** For a prime `p`, the automorphisms of `ℚ(ζ_p)` are exactly the maps `σ_a` with
`σ_a(ζ_p) = ζ_p^a`, one for each unit `a mod p`, and `a ↦ σ_a` is a group isomorphism
`(ℤ/p)ˣ ≅ Aut(ℚ(ζ_p)/ℚ)`.

* **Existence of `σ_a`.** A rational polynomial vanishing at `ζ_p` is a multiple of `Φ_p`
  (irreducibility), so it also vanishes at the root `ζ_p^a`. By the extension lemma of the
  algebra part, `p(ζ_p) ↦ p(ζ_p^a)` is a well-defined ring homomorphism `ℚ(ζ_p) → ℂ`. Its
  values lie in `ℚ(ζ_p)`, and an injective endomorphism of a finite extension is an
  automorphism.
* **Rigidity.** An automorphism fixing `ℚ` is determined by its value at `ζ_p`, because the
  fixed field of `τ⁻¹σ` contains `ℚ` and `ζ_p`, hence all of `ℚ(ζ_p)`.
* **Surjectivity.** `σ(ζ_p)` is a `p`-th root of unity other than `1`, hence `ζ_p^a` for some
  `0 < a < p`.

So the Galois group of `ℚ(ζ_p)/ℚ` is abelian and "is" the group of residues. This is the
first case of the dictionary of class field theory. The automorphism `σ_q` attached to a prime
`q ≠ p` is the automorphism `ζ ↦ ζ^q`, which classical theory identifies with the **Frobenius element**
at `q`; that identification (through `ℤ[ζ_p]/(q)`) is not formalised here, and the previous file
computes `g^q` in `𝔽_q[x]/(Φ_p)` instead. Here we see it acting on the Gauss sum,
`σ_a(g) = (a/p) g` (`galAut_gaussSum`). So `σ_q` fixes `√p* = g` exactly when `(q/p) = 1`,
which by Gauss's congruence happens exactly when `(p*)^((q-1)/2) ≡ 1 (mod q)`, i.e. when `p*` is
a square modulo `q` (`frobenius_fixes_sqrt_iff`). This is quadratic reciprocity read as a
statement about how Frobenius elements act in `ℚ(√p*) ⊆ ℚ(ζ_p)`.

**Dirichlet characters as Galois characters.** Composing with the isomorphism, every
character `χ` of `(ℤ/p)ˣ` becomes a character of `Gal(ℚ(ζ_p)/ℚ)`, and its value at the
Frobenius element `σ_q` is the Dirichlet character value `χ(q)` (`galChar_frobenius`). This is
the `GL(1)` dictionary in miniature: Artin's reciprocity law (1927) identifies characters of
Galois groups of abelian extensions with characters of idèle class groups (here, Dirichlet
characters), matching Frobenius elements with primes. Langlands' programme (1967) conjectures
a non-abelian generalisation, relating `n`-dimensional Galois representations to automorphic
representations of `GL(n)`. We prove only the cyclotomic dictionary, with `σ_q` defined as `ζ ↦ ζ^q`, for prime `p`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield Foundations.Algebra.Group

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

section Galois

variable {p : Nat} (hp : IsPrime p)

/-- `ζ_p` as an element of `ℚ(ζ_p)`. -/
noncomputable def zetaK : cycloField hp := ⟨zeta p, zeta_mem hp⟩

include hp in
/-- **The automorphisms `σ_a` exist.** For `p ∤ a` there is an automorphism of `ℚ(ζ_p)` over `ℚ`
sending `ζ_p` to `ζ_p^a`. -/
theorem exists_galAut {a : Nat} (ha : ¬ p ∣ a) :
    ∃ σ : FieldAut Qc (cycloField hp), (σ.toFun (zetaK hp)).1 = rpow (zeta p) a := by
  obtain ⟨τ, hτQ, hτζ, hτp⟩ := extend C.isField Qc (zeta p) (zeta_isAlgebraic hp) Qc.incl
    (rpow (zeta p) a) (fun f hf => aeval_zeta_pow_eq_zero hp ha hf)
  have hmem : ∀ y : cycloField hp, τ.toFun y ∈ cycloField hp := by
    intro y
    obtain ⟨f, hf⟩ := y.2
    have hy : y = ⟨aeval Qc (zeta p) f,
        (⟨f, rfl⟩ : aeval Qc (zeta p) f ∈ adjoin C.isField Qc (zeta p) (zeta_isAlgebraic hp))⟩ :=
      Subtype.ext hf.symm
    have e : τ.toFun y = eval (rpow (zeta p) a) (mapPoly Qc.incl f) :=
      (congrArg τ.toFun hy).trans (hτp f)
    rw [e]
    exact aeval_mem Qc (rpow (zeta p) a) (Qc_le_cycloField hp) (rpow_mem (zeta_mem hp) a) f
  let τ' : RingHom (cycloField hp) (cycloField hp) :=
    { toFun := fun y => ⟨τ.toFun y, hmem y⟩
      map_add := fun x y => Subtype.ext (τ.map_add x y)
      map_mul := fun x y => Subtype.ext (τ.map_mul x y)
      map_one := Subtype.ext τ.map_one }
  have hfix : ∀ x : cycloField hp, x.1 ∈ Qc → τ'.toFun x = x := by
    intro x hx
    apply Subtype.ext
    show τ.toFun x = x.1
    exact hτQ ⟨x.1, hx⟩
  exact ⟨autOfRingHom C.isField (Qc_le_cycloField hp) (cycloField_finite hp) τ' hfix, hτζ⟩

/-- **The Galois automorphism `σ_a`** of `ℚ(ζ_p)`, for `p ∤ a`: the automorphism with
`σ_a(ζ_p) = ζ_p^a`. -/
noncomputable def galAut {a : Nat} (ha : ¬ p ∣ a) : FieldAut Qc (cycloField hp) :=
  Classical.choose (exists_galAut hp ha)

/-- `σ_a(ζ_p) = ζ_p^a`. -/
theorem galAut_zeta {a : Nat} (ha : ¬ p ∣ a) :
    ((galAut hp ha).toFun (zetaK hp)).1 = rpow (zeta p) a :=
  Classical.choose_spec (exists_galAut hp ha)

/-- **Rigidity.** Two automorphisms of `ℚ(ζ_p)` over `ℚ` that agree at `ζ_p` are equal. -/
theorem aut_ext_zeta {σ τ : FieldAut Qc (cycloField hp)}
    (h : σ.toFun (zetaK hp) = τ.toFun (zetaK hp)) : σ = τ := by
  let ρ := τ⁻¹ * σ
  have hfix : ρ.toFun (zetaK hp) = zetaK hp := by
    rw [FieldAut.mul_apply, h]
    show τ.invFun (τ.toFun (zetaK hp)) = zetaK hp
    exact τ.left_inv _
  have hL := adjoin_le C.isField Qc (zeta p) (zeta_isAlgebraic hp)
    (M := fixedField (cycloField hp) (fun φ => φ = ρ)) (le_fixedField (Qc_le_cycloField hp) _)
    ⟨zeta_mem hp, fun φ hφ => by rw [hφ]; exact hfix⟩
  have hρ : ρ = 1 := FieldAut.ext fun x => by
    obtain ⟨_, hx⟩ := hL x.1 x.2
    exact hx ρ rfl
  calc σ = τ * (τ⁻¹ * σ) := by rw [← Group.mul_assoc, Group.mul_inv_cancel, Group.one_mul]
    _ = τ := by rw [show τ⁻¹ * σ = 1 from hρ, Group.mul_one]

/-- `ζ_p^p = 1` in `ℚ(ζ_p)`. -/
theorem rpow_zetaK_self : rpow (zetaK hp) p = 1 :=
  Subtype.ext (by rw [Subfield.coe_rpow]; exact zeta_rpow_self (by have := hp.1; omega))

/-- `σ_a = σ_b` when `a ≡ b (mod p)`. -/
theorem galAut_congr {a b : Nat} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) (hab : a % p = b % p) :
    galAut hp ha = galAut hp hb := by
  apply aut_ext_zeta
  apply Subtype.ext
  rw [galAut_zeta, galAut_zeta]
  have hζ : rpow (zeta p) p = 1 := zeta_rpow_self (by have := hp.1; omega)
  exact (pow_mod_of_pow_eq_one (R := ℂ) hζ a).trans
    (by rw [hab]; exact (pow_mod_of_pow_eq_one (R := ℂ) hζ b).symm)

/-- `σ_a σ_b = σ_{ab}`. -/
theorem galAut_mul {a b : Nat} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) (hab : ¬ p ∣ a * b) :
    galAut hp hab = galAut hp ha * galAut hp hb := by
  apply aut_ext_zeta
  apply Subtype.ext
  rw [galAut_zeta, FieldAut.mul_apply]
  have e : (galAut hp hb).toFun (zetaK hp) = rpow (zetaK hp) b :=
    Subtype.ext (by rw [galAut_zeta, Subfield.coe_rpow]; rfl)
  rw [e, FieldAut.map_rpow, Subfield.coe_rpow, galAut_zeta, rpow_mul']

variable [NeZero p]

omit [NeZero p] in
include hp in
/-- A unit modulo `p` is not divisible by `p`. -/
theorem not_dvd_of_unit (u : ZModUnits p) : ¬ p ∣ u.1.val := by
  intro h
  have h1 : Nat.gcd u.1.val p = p := Nat.gcd_eq_right h
  have h2 : Nat.gcd u.1.val p = 1 := u.2
  have := hp.1; omega

/-- **The Galois representation of the units**: `a ↦ σ_a`, a homomorphism
`(ℤ/p)ˣ → Aut(ℚ(ζ_p)/ℚ)`. -/
noncomputable def galHom : ZModUnits p →* FieldAut Qc (cycloField hp) where
  toFun u := galAut hp (not_dvd_of_unit hp u)
  map_mul u v := by
    haveI : NeZero p := ⟨by have := hp.1; omega⟩
    have hmul : ¬ p ∣ u.1.val * v.1.val := fun h =>
      (hp.dvd_mul h).elim (not_dvd_of_unit hp u) (not_dvd_of_unit hp v)
    show galAut hp (not_dvd_of_unit hp (u * v)) = _
    rw [galAut_congr hp (not_dvd_of_unit hp (u * v)) hmul
      (by rw [ZModUnits.val_mul, Nat.mod_mod]), galAut_mul hp _ _ hmul]

/-- `galHom` is injective: `σ_a = σ_b` forces `ζ_p^a = ζ_p^b`, so `a ≡ b`. -/
theorem galHom_injective : ∀ u v : ZModUnits p, galHom hp u = galHom hp v → u = v := by
  intro u v h
  have h1 := congrArg (fun σ : FieldAut Qc (cycloField hp) => (σ.toFun (zetaK hp)).1) h
  change ((galAut hp (not_dvd_of_unit hp u)).toFun (zetaK hp)).1 =
    ((galAut hp (not_dvd_of_unit hp v)).toFun (zetaK hp)).1 at h1
  rw [galAut_zeta, galAut_zeta] at h1
  exact ZModUnits.ext (rpow_injective_of_lt C.isField hp
    (zeta_rpow_self (by have := hp.1; omega)) (zeta_ne_one hp.1) u.1.isLt v.1.isLt h1)

/-- `galHom` is surjective: every automorphism sends `ζ_p` to some `ζ_p^a`, `0 < a < p`. -/
theorem galHom_surjective : ∀ σ : FieldAut Qc (cycloField hp), ∃ u, galHom hp u = σ := by
  intro σ
  have h2 := hp.1
  have hζp : rpow (zeta p) p = 1 := zeta_rpow_self (by omega)
  have hω : rpow (σ.toFun (zetaK hp)).1 p = 1 := by
    rw [← Subfield.coe_rpow, ← FieldAut.map_rpow, rpow_zetaK_self, FieldAut.map_one]; rfl
  have hω1 : (σ.toFun (zetaK hp)).1 ≠ 1 := by
    intro h
    have : σ.toFun (zetaK hp) = σ.toFun 1 := by rw [FieldAut.map_one]; exact Subtype.ext h
    exact zeta_ne_one hp.1 (congrArg Subtype.val (σ.injective this))
  obtain ⟨k, hk, hkω⟩ := eq_rpow_of_rpow_eq_one C.isField hp hζp (zeta_ne_one hp.1) hω
  have hk0 : k ≠ 0 := by rintro rfl; exact hω1 hkω
  have hcop : Nat.Coprime k p := by
    show Nat.gcd k p = 1
    rcases hp.2 _ (Nat.gcd_dvd_right k p) with h | h
    · exact h
    · have := Nat.le_of_dvd (by omega) (h ▸ Nat.gcd_dvd_left k p); omega
  refine ⟨⟨⟨k, hk⟩, hcop⟩, aut_ext_zeta hp (Subtype.ext ?_)⟩
  show ((galAut hp (not_dvd_of_unit hp _)).toFun (zetaK hp)).1 = _
  rw [galAut_zeta, hkω]

/-- **The Galois group of the cyclotomic field.** For a prime `p`,
`Aut(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)ˣ`, the residue `a` acting by `ζ_p ↦ ζ_p^a`. -/
noncomputable def cycloGaloisIso : ZModUnits p ≃* FieldAut Qc (cycloField hp) :=
  Iso.ofBijective (galHom hp) (galHom_injective hp) (galHom_surjective hp)

/-- The isomorphism sends `a` to the automorphism `ζ_p ↦ ζ_p^a`. -/
theorem cycloGaloisIso_zeta (u : ZModUnits p) :
    (((cycloGaloisIso hp) u).toFun (zetaK hp)).1 = rpow (zeta p) u.1.val :=
  galAut_zeta hp (not_dvd_of_unit hp u)

/-- **The Galois group of `ℚ(ζ_p)/ℚ` is abelian.** -/
theorem cycloGalois_comm (σ τ : FieldAut Qc (cycloField hp)) : σ * τ = τ * σ := by
  obtain ⟨u, rfl⟩ := galHom_surjective hp σ
  obtain ⟨v, rfl⟩ := galHom_surjective hp τ
  rw [← (galHom hp).map_mul, ← (galHom hp).map_mul, CommGroup.mul_comm]

end Galois

/-! ## Frobenius on the Gauss sum -/

section Frobenius

variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

/-- The Gauss sum `g = √p*` as an element of `ℚ(ζ_p)`. -/
noncomputable def gaussK : cycloField hp := ⟨gaussSum p (zeta p), gaussSum_mem hp⟩

/-- Coercions of finite sums out of a subfield. -/
theorem coe_rsum' (K : Subfield ℂ) (t : Nat → K) :
    ∀ n, (rsum t n).1 = rsum (fun k => (t k).1) n
  | 0 => rfl
  | n + 1 => by
    show (rsum t n).1 + (t n).1 = _
    rw [coe_rsum' K t n]; rfl

include hodd in
/-- **How `σ_a` acts on `√p*`.** `σ_a(g) = (a/p) · g` for the Gauss sum `g`. -/
theorem galAut_gaussSum {a : Nat} (ha : ¬ p ∣ a) :
    ((galAut hp ha).toFun (gaussK hp)).1 = icast (legendre a p) * gaussSum p (zeta p) := by
  let σ := galAut hp ha
  have hg : gaussK hp = rsum (fun b => (icast (legendre b p) : cycloField hp) *
      rpow (zetaK hp) b) p := by
    apply Subtype.ext
    rw [coe_rsum']
    apply rsum_congr; intro b _
    show _ = ((icast (legendre b p) : cycloField hp)).1 * (rpow (zetaK hp) b).1
    rw [Subfield.coe_rpow]
    exact congrArg (· * _) (Subfield.coe_intCast _ _).symm
  rw [hg]
  have hσ : σ.toFun (rsum (fun b => (icast (legendre b p) : cycloField hp) *
      rpow (zetaK hp) b) p) = rsum (fun b => (icast (legendre b p) : cycloField hp) *
      rpow (σ.toFun (zetaK hp)) b) p := by
    show σ.toRingHom.toFun _ = _
    rw [RingHom.map_rsum]
    apply rsum_congr; intro b _
    rw [σ.toRingHom.map_mul]
    show σ.toRingHom.toFun (Int.cast _) * σ.toFun (rpow (zetaK hp) b) = _
    rw [RingHom.map_intCast, FieldAut.map_rpow]; rfl
  rw [hσ, coe_rsum']
  have hζ : rpow (zeta p) p = 1 := zeta_rpow_self (by have := hp.1; omega)
  refine Eq.trans ?_ (gaussSum_twist (R := ℂ) hp hodd hζ ha)
  apply rsum_congr; intro b _
  show ((icast (legendre b p) : cycloField hp)).1 * (rpow (σ.toFun (zetaK hp)) b).1 = _
  rw [Subfield.coe_rpow, galAut_zeta]
  exact congrArg (· * _) (Subfield.coe_intCast _ _)

include hp hodd in
/-- The Gauss sum is not zero: its square is `p* ≠ 0`. -/
theorem gaussSum_ne_zero : gaussSum p (zeta p) ≠ 0 := by
  intro h
  have h2 := gaussSum_sq_complex hp hodd
  rw [h, Ring.zero_mul] at h2
  have hz := C.charZero (pstar p) h2.symm
  unfold pstar at hz
  rw [neg_one_pow_int] at hz
  have := hp.1
  split at hz <;> omega

include hodd in
/-- **Frobenius and the quadratic subfield.** For an odd prime `q ≠ p`, the Frobenius
automorphism `σ_q` of `ℚ(ζ_p)` fixes `√p* = g` if and only if `(p*)^((q-1)/2) ≡ 1 (mod q)`, i.e.
(by Euler's criterion) if and only if `p*` is a square modulo `q`. -/
theorem frobenius_fixes_sqrt_iff {q : Nat} (hq : IsPrime q) (hqo : q % 2 = 1) (hpq : p ≠ q)
    (hpq' : ¬ p ∣ q) :
    (galAut hp hpq').toFun (gaussK hp) = gaussK hp ↔ (q : Int) ∣ (pstar p) ^ half q - 1 := by
  have hcong := legendre_eq_pstar_pow_mod hp hodd hq hqo hpq
  have hg0 := gaussSum_ne_zero hp hodd
  have hq3 : 3 ≤ q := by have := hq.1; omega
  have hvals := legendre_cases hp hodd hpq'
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [galAut_gaussSum hp hodd] at h1
    rcases hvals with ⟨hl, _⟩ | ⟨hl, _⟩
    · rw [hl] at hcong
      have := Int.dvd_neg.2 hcong
      rwa [Int.neg_sub] at this
    · exfalso
      rw [hl] at h1
      have h2 : (gaussSum p (zeta p) : ℂ) + gaussSum p (zeta p) = 0 := by
        have e : (icast (-1 : Int) : ℂ) = -1 := rfl
        rw [e] at h1
        have h1' : -1 * gaussSum p (zeta p) = gaussSum p (zeta p) := h1
        clear h1 h hcong
        generalize gaussSum p (zeta p) = g at h1' ⊢
        grind
      have h3 : (icast (2 : Int) : ℂ) * gaussSum p (zeta p) = 0 := by
        rw [← h2]; show (ncast 2 : ℂ) * _ = _; show ((1 : ℂ) + 1) * _ = _; grind
      rcases C.isDomain.2 _ _ h3 with h4 | h4
      · exact absurd (C.charZero 2 h4) (by decide)
      · exact hg0 h4
  · intro hd
    have h3 := Int.dvd_add hcong hd
    rw [show legendre q p - pstar p ^ half q + (pstar p ^ half q - 1) = legendre q p - 1 by
      omega] at h3
    have hl : legendre q p = 1 := by
      rcases hvals with ⟨hl, _⟩ | ⟨hl, _⟩
      · exact hl
      · exfalso
        rw [hl] at h3
        have h4 := Int.dvd_neg.2 h3
        rw [show -((-1 : Int) - 1) = 2 by decide] at h4
        have := Int.le_of_dvd (by decide) h4
        omega
    apply Subtype.ext
    rw [galAut_gaussSum hp hodd, hl]
    show (icast (1 : Int) : ℂ) * _ = _
    exact Ring.one_mul _

end Frobenius

/-! ## Dirichlet characters as characters of the Galois group -/

section Characters

variable {p : Nat} (hp : IsPrime p) [NeZero p]

/-- **The Galois character attached to a Dirichlet character.** A character `χ` of `(ℤ/p)ˣ`,
transported along `Aut(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)ˣ`, gives a function on the Galois group. -/
noncomputable def galChar (χ : Character (ZModUnits p)) (σ : FieldAut Qc (cycloField hp)) : ℂ :=
  χ.1 ((cycloGaloisIso hp).invFun σ)

/-- `galChar χ` is multiplicative: a character of the Galois group. -/
theorem galChar_mul (χ : Character (ZModUnits p)) (σ τ : FieldAut Qc (cycloField hp)) :
    galChar hp χ (σ * τ) = galChar hp χ σ * galChar hp χ τ := by
  unfold galChar
  rw [← χ.2.map_mul]
  apply congrArg χ.1
  apply galHom_injective hp
  show (cycloGaloisIso hp).toFun _ = (cycloGaloisIso hp).toFun _
  rw [(cycloGaloisIso hp).right_inv, (cycloGaloisIso hp).map_mul,
    (cycloGaloisIso hp).right_inv, (cycloGaloisIso hp).right_inv]

/-- `galChar χ` sends the identity to `1`. -/
theorem galChar_one (χ : Character (ZModUnits p)) : galChar hp χ 1 = 1 := by
  unfold galChar
  have : (cycloGaloisIso hp).invFun 1 = 1 := by
    apply galHom_injective hp
    show (cycloGaloisIso hp).toFun _ = (cycloGaloisIso hp).toFun _
    rw [(cycloGaloisIso hp).right_inv]
    exact ((cycloGaloisIso hp).toHom.map_one).symm
  rw [this]; exact χ.2.map_one

/-- **Frobenius and Dirichlet characters.** For `q` not divisible by `p`, the Galois character
attached to `χ` takes the value `χ(q)` at the automorphism `σ_q`: Dirichlet characters are the
characters of `Gal(ℚ(ζ_p)/ℚ)` evaluated at Frobenius elements. -/
theorem galChar_frobenius (χ : Character (ZModUnits p)) {q : Nat} (hq : ¬ p ∣ q)
    (hcop : Nat.Coprime q p) : galChar hp χ (galAut hp hq) = dchar χ q := by
  rw [dchar_of_coprime χ hcop]
  unfold galChar
  congr 1
  have e : galAut hp hq = galHom hp (toUnit p q hcop) :=
    galAut_congr hp hq (not_dvd_of_unit hp _) (by show q % p = (Fin.ofNat p q).val % p; rw [Fin.val_ofNat, Nat.mod_mod])
  rw [e]
  exact congrArg χ.1 ((cycloGaloisIso hp).left_inv _)

end Characters

end Foundations.Langlands
