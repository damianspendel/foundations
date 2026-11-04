import Foundations.Langlands.Cyclotomic.IrreducibleN

/-!
# `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/n)ˣ` and `[ℚ(ζ_n) : ℚ] = φ(n)` for every `n ≥ 1`

This file repeats the Galois theory of `PrimePowerGalois.lean` for an arbitrary `n ≥ 1`. The
minimal polynomial of `ζ_n = e^{2πi/n}` is now the general cyclotomic polynomial `Φ_n`
(`IrreducibleN.lean`), whose roots are exactly the primitive roots `ζ_n^a`, `gcd(a, n) = 1`.

* For each `a` prime to `n` there is an automorphism `σ_a` of `ℚ(ζ_n)` with `σ_a(ζ_n) = ζ_n^a`
  (extension of embeddings, using that `ζ_n^a` is a root of every rational polynomial vanishing
  at `ζ_n`). It is determined by this value, depends only on `a mod n`, and `σ_a σ_b = σ_{ab}`.
* Every automorphism sends `ζ_n` to a root of `Φ_n`, that is, to some `ζ_n^j` with
  `gcd(j, n) = 1`.

**Headlines.** `cycloGaloisIsoN : (ℤ/n)ˣ ≃* Aut(ℚ(ζ_n)/ℚ)` and
`deg_cycloFieldN : [ℚ(ζ_n) : ℚ] = φ(n)`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield Foundations.Algebra.Group

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

section FieldN

variable {n : Nat} (hn : 1 ≤ n)

include hn in
/-- `ζ_n` is algebraic over `ℚ`. -/
theorem zetaN_isAlgebraic : IsAlgebraic Qc (zeta n) :=
  ⟨cycloQ n, (monic_cycloQ hn).ne_zero (Qc.isField C.isField).1, aeval_cycloQ_zeta hn⟩

/-- **The cyclotomic field `ℚ(ζ_n)`** inside `ℂ`, for `n ≥ 1`. -/
noncomputable def cycloFieldN : Subfield ℂ :=
  adjoin C.isField Qc (zeta n) (zetaN_isAlgebraic hn)

/-- `ℚ ⊆ ℚ(ζ_n)`. -/
theorem Qc_le_cycloFieldN : Qc.le (cycloFieldN hn) := le_adjoin _ _ _ _

/-- `ζ_n ∈ ℚ(ζ_n)`. -/
theorem zetaN_mem : zeta n ∈ cycloFieldN hn := mem_adjoin_self _ _ _ _

/-- `ℚ(ζ_n)` is finite over `ℚ`. -/
theorem cycloFieldN_finite : FiniteExt Qc (cycloFieldN hn) (Qc_le_cycloFieldN hn) :=
  adjoin_finite _ _ _ _

/-- `ζ_n` as an element of `ℚ(ζ_n)`. -/
noncomputable def zetaKN : cycloFieldN hn := ⟨zeta n, zetaN_mem hn⟩

/-- **The automorphisms `σ_a` of `ℚ(ζ_n)` exist** for `gcd(a, n) = 1`. -/
theorem exists_galAutN {a : Nat} (ha : Nat.Coprime a n) :
    ∃ σ : FieldAut Qc (cycloFieldN hn), (σ.toFun (zetaKN hn)).1 = rpow (zeta n) a := by
  obtain ⟨τ, hτQ, hτζ, hτp⟩ := extend C.isField Qc (zeta n) (zetaN_isAlgebraic hn)
    Qc.incl (rpow (zeta n) a) (fun f hf => aeval_zeta_pow_of_coprime hn hf a ha)
  have hmem : ∀ y : cycloFieldN hn, τ.toFun y ∈ cycloFieldN hn := by
    intro y
    obtain ⟨f, hf⟩ := y.2
    have hy : y = ⟨aeval Qc (zeta n) f, (⟨f, rfl⟩ : aeval Qc (zeta n) f ∈
        adjoin C.isField Qc (zeta n) (zetaN_isAlgebraic hn))⟩ := Subtype.ext hf.symm
    have e : τ.toFun y = eval (rpow (zeta n) a) (mapPoly Qc.incl f) :=
      (congrArg τ.toFun hy).trans (hτp f)
    rw [e]
    exact aeval_mem Qc _ (Qc_le_cycloFieldN hn) (rpow_mem (zetaN_mem hn) a) f
  let τ' : RingHom (cycloFieldN hn) (cycloFieldN hn) :=
    { toFun := fun y => ⟨τ.toFun y, hmem y⟩
      map_add := fun x y => Subtype.ext (τ.map_add x y)
      map_mul := fun x y => Subtype.ext (τ.map_mul x y)
      map_one := Subtype.ext τ.map_one }
  have hfix : ∀ x : cycloFieldN hn, x.1 ∈ Qc → τ'.toFun x = x := by
    intro x hx
    apply Subtype.ext
    show τ.toFun x = x.1
    exact hτQ ⟨x.1, hx⟩
  exact ⟨autOfRingHom C.isField (Qc_le_cycloFieldN hn) (cycloFieldN_finite hn) τ' hfix, hτζ⟩

/-- **The Galois automorphism `σ_a` of `ℚ(ζ_n)`**: `ζ_n ↦ ζ_n^a` (`gcd(a, n) = 1`). -/
noncomputable def galAutN {a : Nat} (ha : Nat.Coprime a n) : FieldAut Qc (cycloFieldN hn) :=
  Classical.choose (exists_galAutN hn ha)

/-- `σ_a(ζ_n) = ζ_n^a`. -/
theorem galAutN_zeta {a : Nat} (ha : Nat.Coprime a n) :
    ((galAutN hn ha).toFun (zetaKN hn)).1 = rpow (zeta n) a :=
  Classical.choose_spec (exists_galAutN hn ha)

/-- **Rigidity**: automorphisms of `ℚ(ζ_n)` agreeing at `ζ_n` are equal. -/
theorem aut_ext_zetaN {σ τ : FieldAut Qc (cycloFieldN hn)}
    (h : σ.toFun (zetaKN hn) = τ.toFun (zetaKN hn)) : σ = τ := by
  let ρ := τ⁻¹ * σ
  have hfix : ρ.toFun (zetaKN hn) = zetaKN hn := by
    rw [FieldAut.mul_apply, h]
    show τ.invFun (τ.toFun (zetaKN hn)) = zetaKN hn
    exact τ.left_inv _
  have hL := adjoin_le C.isField Qc (zeta n) (zetaN_isAlgebraic hn)
    (M := fixedField (cycloFieldN hn) (fun φ => φ = ρ)) (le_fixedField (Qc_le_cycloFieldN hn) _)
    ⟨zetaN_mem hn, fun φ hφ => by rw [hφ]; exact hfix⟩
  have hρ : ρ = 1 := FieldAut.ext fun x => by
    obtain ⟨_, hx⟩ := hL x.1 x.2
    exact hx ρ rfl
  calc σ = τ * (τ⁻¹ * σ) := by rw [← Group.mul_assoc, Group.mul_inv_cancel, Group.one_mul]
    _ = τ := by rw [show τ⁻¹ * σ = 1 from hρ, Group.mul_one]

/-- `σ_a = σ_b` when `a ≡ b (mod n)`. -/
theorem galAutN_congr {a b : Nat} (ha : Nat.Coprime a n) (hb : Nat.Coprime b n)
    (hab : a % n = b % n) : galAutN hn ha = galAutN hn hb := by
  apply aut_ext_zetaN
  apply Subtype.ext
  rw [galAutN_zeta, galAutN_zeta]
  have hζ : rpow (zeta n) n = 1 := zeta_rpow_self hn
  exact (pow_mod_of_pow_eq_one (R := ℂ) hζ a).trans
    (by rw [hab]; exact (pow_mod_of_pow_eq_one (R := ℂ) hζ b).symm)

/-- `σ_a σ_b = σ_{ab}`. -/
theorem galAutN_mul {a b : Nat} (ha : Nat.Coprime a n) (hb : Nat.Coprime b n)
    (hab : Nat.Coprime (a * b) n) : galAutN hn hab = galAutN hn ha * galAutN hn hb := by
  apply aut_ext_zetaN
  apply Subtype.ext
  rw [galAutN_zeta, FieldAut.mul_apply]
  have e : (galAutN hn hb).toFun (zetaKN hn) = rpow (zetaKN hn) b :=
    Subtype.ext (by rw [galAutN_zeta, Subfield.coe_rpow]; rfl)
  rw [e, FieldAut.map_rpow, Subfield.coe_rpow, galAutN_zeta, rpow_mul']

/-- Automorphisms send roots of rational polynomials to roots: `σ(f(ζ_n)) = f(σ ζ_n)`. -/
theorem aut_aevalN (σ : FieldAut Qc (cycloFieldN hn)) (f : Polynomial Qc) :
    (σ.toFun ⟨aeval Qc (zeta n) f, aeval_mem Qc _ (Qc_le_cycloFieldN hn) (zetaN_mem hn) f⟩).1 =
      aeval Qc (σ.toFun (zetaKN hn)).1 f := by
  let φ : RingHom (Polynomial Qc) ℂ :=
    { toFun := fun f => (σ.toFun ⟨aeval Qc (zeta n) f,
        aeval_mem Qc _ (Qc_le_cycloFieldN hn) (zetaN_mem hn) f⟩).1
      map_add := fun f g => by
        show _ = (σ.toFun _ + σ.toFun _).1
        rw [← σ.map_add]; congr 2; apply Subtype.ext; exact aeval_add Qc _ f g
      map_mul := fun f g => by
        show _ = (σ.toFun _ * σ.toFun _).1
        rw [← σ.map_mul]; congr 2; apply Subtype.ext; exact aeval_mul Qc _ f g
      map_one := by
        show _ = ((1 : cycloFieldN hn)).1
        rw [← σ.map_one]; congr 2; apply Subtype.ext; exact aeval_one Qc _ }
  exact polyHom_ext φ (aevalHom Qc (σ.toFun (zetaKN hn)).1)
    (fun c => by
      show (σ.toFun _).1 = aeval Qc _ (C c)
      have hmem : aeval Qc (zeta n) (C c) ∈ Qc := by rw [aeval_C]; exact c.2
      rw [σ.fix _ hmem]; exact (aeval_C Qc _ c).trans (aeval_C Qc _ c).symm)
    (by
      show (σ.toFun _).1 = aeval Qc _ X
      have e : (⟨aeval Qc (zeta n) X, aeval_mem Qc _ (Qc_le_cycloFieldN hn)
          (zetaN_mem hn) X⟩ : cycloFieldN hn) = zetaKN hn := Subtype.ext (aeval_X Qc _)
      rw [e, aeval_X]) f

variable [NeZero n]

/-- **The Galois representation** `(ℤ/n)ˣ → Aut(ℚ(ζ_n)/ℚ)`, `a ↦ σ_a`. -/
noncomputable def galHomN : ZModUnits n →* FieldAut Qc (cycloFieldN hn) where
  toFun u := galAutN hn u.2
  map_mul u v := by
    have hmul : Nat.Coprime (u.1.val * v.1.val) n := Nat.coprime_mul_iff_left.2 ⟨u.2, v.2⟩
    show galAutN hn (u * v).2 = _
    rw [galAutN_congr hn (u * v).2 hmul (by rw [ZModUnits.val_mul, Nat.mod_mod]),
      galAutN_mul hn _ _ hmul]

/-- `galHomN` is injective. -/
theorem galHomN_injective : ∀ u v : ZModUnits n, galHomN hn u = galHomN hn v → u = v := by
  intro u v h
  have h1 := congrArg (fun σ : FieldAut Qc (cycloFieldN hn) => (σ.toFun (zetaKN hn)).1) h
  change ((galAutN hn u.2).toFun (zetaKN hn)).1 = ((galAutN hn v.2).toFun (zetaKN hn)).1 at h1
  rw [galAutN_zeta, galAutN_zeta] at h1
  exact ZModUnits.ext (zeta_rpow_inj hn u.1.isLt v.1.isLt h1)

/-- `galHomN` is surjective: every automorphism sends `ζ_n` to a primitive root `ζ_n^j`. -/
theorem galHomN_surjective : ∀ σ : FieldAut Qc (cycloFieldN hn), ∃ u, galHomN hn u = σ := by
  intro σ
  let ω := (σ.toFun (zetaKN hn)).1
  have hΦ : aeval Qc ω (cycloQ n) = 0 := by
    rw [← aut_aevalN hn σ]
    have h0 : (⟨aeval Qc (zeta n) (cycloQ n), aeval_mem Qc _ (Qc_le_cycloFieldN hn)
        (zetaN_mem hn) _⟩ : cycloFieldN hn) = 0 := Subtype.ext (aeval_cycloQ_zeta hn)
    rw [h0, FieldAut.map_zero]; rfl
  obtain ⟨j, hj, hjc, hjω⟩ := (aeval_cycloQ_eq_zero_iff hn ω).1 hΦ
  refine ⟨⟨⟨j, hj⟩, hjc⟩, aut_ext_zetaN hn (Subtype.ext ?_)⟩
  show ((galAutN hn hjc).toFun (zetaKN hn)).1 = _
  rw [galAutN_zeta]
  exact hjω.symm

/-- **The Galois group of the `n`-th cyclotomic field.** For every `n ≥ 1`,
`Aut(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ`, the unit `a` acting by `ζ_n ↦ ζ_n^a`. -/
noncomputable def cycloGaloisIsoN : ZModUnits n ≃* FieldAut Qc (cycloFieldN hn) :=
  Iso.ofBijective (galHomN hn) (galHomN_injective hn) (galHomN_surjective hn)

/-- The isomorphism sends `a` to the automorphism `ζ_n ↦ ζ_n^a`. -/
theorem cycloGaloisIsoN_zeta (u : ZModUnits n) :
    (((cycloGaloisIsoN hn) u).toFun (zetaKN hn)).1 = rpow (zeta n) u.1.val :=
  galAutN_zeta hn u.2

end FieldN

/-! ## The degree -/

/-- **The degree of the `n`-th cyclotomic field.** `[ℚ(ζ_n) : ℚ] = φ(n)` for every `n ≥ 1`. -/
theorem deg_cycloFieldN {n : Nat} (hn : 1 ≤ n) :
    deg Qc (cycloFieldN hn) (Qc_le_cycloFieldN hn) = totient n := by
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  have hdeg := (monic_cycloQ hn).natDegree_eq hD.1
  rw [← hdeg]
  have hΦ0 := (monic_cycloQ hn).ne_zero hD.1
  apply deg_adjoin_eq _ _ hΦ0 (aeval_cycloQ_zeta hn)
  intro r hr hrz
  obtain ⟨e, he⟩ := (aeval_zetaN_eq_zero_iff hn r).1 hrz
  apply Classical.byContradiction; intro hne
  have he0 : e ≠ 0 := by intro h; rw [h, Ring.mul_zero] at he; exact hne he
  have h1 := natDegree_mul hD hΦ0 he0
  rw [← he] at h1
  have := natDegree_lt_of_degLT hne hr
  omega

/-- **The order of the Galois group equals the degree.** `|(ℤ/n)ˣ| = φ(n) = [ℚ(ζ_n) : ℚ]`. -/
theorem card_zmodUnits_eq_deg {n : Nat} (hn : 1 ≤ n) [NeZero n] :
    FiniteType.card (ZModUnits n) = deg Qc (cycloFieldN hn) (Qc_le_cycloFieldN hn) := by
  rw [card_zmodUnits, deg_cycloFieldN hn]

end Foundations.Langlands
