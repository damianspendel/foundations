import Foundations.Langlands.Cyclotomic.FrobeniusN
import Foundations.NumberTheory.Dirichlet

/-!
# The `GL(1)` dictionary over `ℚ(ζ_n)`: Dirichlet characters are Galois characters

This file states the abelian case of the Langlands correspondence over `ℚ` in its most classical
form, for the cyclotomic field `ℚ(ζ_n)` and every `n ≥ 1`.

**The two sides.** On the *automorphic* side of `GL(1)` over `ℚ` stand the Dirichlet characters
modulo `n`, i.e. the characters `χ : (ℤ/n)ˣ → ℂ` (`Character (ZModUnits n)`). (In general one has
Hecke characters, i.e. characters of the idèle class group; over `ℚ` the Hecke characters of
finite order are exactly the Dirichlet characters, but that identification is not formalised
here.) On the *Galois* side stand the one-dimensional representations of the Galois group, here
the characters `ρ : Gal(ℚ(ζ_n)/ℚ) → ℂ` (`Character (FieldAut Qc (cycloFieldN hn))`). A
character of a finite group takes values in the unit circle, so this is the same as a
homomorphism into `ℂˣ`.

**The dictionary.** Transporting characters along `cycloGaloisIsoN : (ℤ/n)ˣ ≅ Gal(ℚ(ζ_n)/ℚ)`
gives an isomorphism of groups of characters (`dirichletGaloisN`), and the defining property of
the dictionary is the match at Frobenius elements: for a prime `q ∤ n`,

  `ρ_χ(σ_q) = χ(q)`   (`dirichletGaloisN_frobenius`),

where `σ_q : ζ_n ↦ ζ_n^q` is the automorphism shown to reduce to the `q`-th power map modulo `q`
in `FrobeniusN.lean` (`reduceN_galAut`). This is what makes the Artin `L`-function
`L(s, ρ_χ) = ∏_q (1 - ρ_χ(Frob_q) q^{-s})⁻¹` and the Dirichlet `L`-function
`L(s, χ) = ∏_q (1 - χ(q) q^{-s})⁻¹` have the same Euler factors at the unramified primes; see
`EulerFactors.lean`.

**Frobenius elements fill the group.** Using Dirichlet's theorem on primes in progressions
(`Foundations.NumberTheory.dirichlet`), every element of `Gal(ℚ(ζ_n)/ℚ)` is `σ_q` for
infinitely many primes `q` (`exists_frobenius_eq`), a qualitative form of the Chebotarev
density theorem for `ℚ(ζ_n)/ℚ`. Hence a Galois character is determined by its values at the
Frobenius elements, and `ρ_χ` is the *unique* Galois character with `ρ(σ_q) = χ(q)` for all primes
`q ∤ n` (`dirichletGaloisN_unique`).

**What is not claimed.** This is `GL(1)` Langlands for the single abelian extension `ℚ(ζ_n)/ℚ`.
The passage to all abelian extensions of `ℚ` needs the Kronecker–Weber theorem, and the passage
to other base fields needs class field theory; neither is formalised. Prime ideals of `ℤ[ζ_n]`
are not formalised either: "Frobenius at `q`" always means the automorphism `σ_q` together with
the congruence `σ_q(α) ≡ α^q (mod q)` on `ℤ[ζ_n]`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield Foundations.Algebra.Group Foundations.Algebra.FiniteType

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

universe u v

/-! ## The character group of a commutative group -/

section CharGroup

variable {G : Type u} [CommGroup G]

/-- The inverse of a character, `χ⁻¹(a) = χ(a⁻¹)`, is a character. -/
theorem isChar_inv {χ : G → ℂ} (hχ : IsChar χ) : IsChar (fun a => χ a⁻¹) :=
  ⟨by show χ 1⁻¹ = 1; rw [Group.inv_one]; exact hχ.map_one,
   fun a b => by
    show χ (a * b)⁻¹ = χ a⁻¹ * χ b⁻¹
    rw [Group.mul_inv_rev, CommGroup.mul_comm' b⁻¹ a⁻¹, hχ.map_mul]⟩

/-- **The dual group is a commutative group.** The characters of a commutative group `G` form
a commutative group under pointwise multiplication, with unit the trivial character and inverse
`χ⁻¹(a) = χ(a⁻¹)`. -/
instance characterCommGroup : CommGroup (Character G) where
  mul χ ψ := ⟨fun a => χ.1 a * ψ.1 a, χ.2.mul ψ.2⟩
  one := ⟨fun _ => 1, ⟨rfl, fun _ _ => by grind⟩⟩
  inv χ := ⟨fun a => χ.1 a⁻¹, isChar_inv χ.2⟩
  mul_assoc _ _ _ := Character.ext fun _ => by
    show _ * _ * _ = _ * (_ * _); grind
  one_mul _ := Character.ext fun _ => by show 1 * _ = _; grind
  inv_mul_cancel χ := Character.ext fun a => by
    show χ.1 a⁻¹ * χ.1 a = 1
    rw [← χ.2.map_mul, Group.inv_mul_cancel, χ.2.map_one]
  mul_comm _ _ := Character.ext fun _ => by show _ * _ = _ * _; grind

/-- Characters multiply pointwise. -/
theorem character_mul_apply (χ ψ : Character G) (a : G) : (χ * ψ).1 a = χ.1 a * ψ.1 a := rfl

/-- The unit of the dual group is the trivial character. -/
theorem character_one_apply (a : G) : (1 : Character G).1 a = 1 := rfl

/-- The inverse character is `a ↦ χ(a⁻¹)`. -/
theorem character_inv_apply (χ : Character G) (a : G) : (χ⁻¹).1 a = χ.1 a⁻¹ := rfl

variable {H : Type v} [CommGroup H]

/-- Pulling a character back along a homomorphism: `ψ ↦ ψ ∘ f`. -/
def charComp (f : G →* H) (ψ : Character H) : Character G :=
  ⟨fun a => ψ.1 (f a),
   ⟨by show ψ.1 (f 1) = 1; rw [Hom.map_one]; exact ψ.2.map_one,
    fun a b => by show ψ.1 (f (a * b)) = _; rw [Hom.map_mul', ψ.2.map_mul]⟩⟩

/-- **Duality turns isomorphisms around.** A group isomorphism `e : G ≅ H` induces an
isomorphism of character groups `Ĥ ≅ Ĝ`, `ψ ↦ ψ ∘ e`. -/
def dualIso (e : G ≃* H) : Character H ≃* Character G where
  toFun := charComp e.toHom
  map_mul _ _ := rfl
  invFun := charComp e.symm.toHom
  left_inv ψ := Character.ext fun b => by
    show ψ.1 (e.toFun (e.invFun b)) = ψ.1 b
    rw [e.right_inv]
  right_inv χ := Character.ext fun a => by
    show χ.1 (e.invFun (e.toFun a)) = χ.1 a
    rw [e.left_inv]

/-- `dualIso e ψ = ψ ∘ e`. -/
theorem dualIso_apply (e : G ≃* H) (ψ : Character H) (a : G) :
    ((dualIso e) ψ).1 a = ψ.1 (e a) := rfl

/-- A group isomorphic to a finite group is finite (the census is transported along `e`). -/
@[reducible] def finiteTypeOfIso [FiniteType G] (e : G ≃* H) : FiniteType H where
  elems := (elems : List G).map e.toFun
  nodup := List.Pairwise.map e.toFun (fun _ _ hab h => hab (e.injective h)) FiniteType.nodup
  complete y := List.mem_map.2 ⟨e.invFun y, FiniteType.complete _, e.right_inv y⟩

/-- Isomorphic finite groups have the same number of elements. -/
theorem card_finiteTypeOfIso [FiniteType G] (e : G ≃* H) :
    @card H (finiteTypeOfIso e) = card G := List.length_map _

end CharGroup

/-! ## `Gal(ℚ(ζ_n)/ℚ)` is a finite commutative group -/

section GalN

variable {n : Nat} (hn : 1 ≤ n)

/-- **The Frobenius element `σ_q`** at a prime `q ∤ n` (more generally at any `q` prime to
`n`): the automorphism `ζ_n ↦ ζ_n^q`. For prime `q` it reduces to the `q`-th power map modulo
`q` (`reduceN_galAut`); prime ideals are not formalised, so this is our meaning of
"`Frob_q`". For `q` not prime to `n` we set `frobN hn q = 1` (a placeholder never used at such
`q`). -/
noncomputable def frobN (q : Nat) : FieldAut Qc (cycloFieldN hn) :=
  if h : Nat.Coprime q n then galAutN hn h else 1

/-- `frobN hn q` is `σ_q = galAutN` when `q` is prime to `n`. -/
theorem frobN_eq {q : Nat} (h : Nat.Coprime q n) : frobN hn q = galAutN hn h := dite_eq_left h

/-- `σ_q` depends only on `q mod n` (here for `q` prime to `n`, as an equality of `frobN`). -/
theorem frobN_congr {a b : Nat} (ha : Nat.Coprime a n) (hab : a % n = b % n) :
    frobN hn a = frobN hn b := by
  have hb : Nat.Coprime b n := by rw [← coprime_mod_iff, ← hab, coprime_mod_iff]; exact ha
  rw [frobN_eq hn ha, frobN_eq hn hb]; exact galAutN_congr hn ha hb hab

variable [NeZero n]

/-- `σ_q` is the image of the residue class of `q` under `(ℤ/n)ˣ ≅ Gal(ℚ(ζ_n)/ℚ)`. -/
theorem galAutN_eq_iso {q : Nat} (h : Nat.Coprime q n) :
    galAutN hn h = cycloGaloisIsoN hn (toUnit n q h) :=
  galAutN_congr hn h (toUnit n q h).2
    (by show q % n = (Fin.ofNat n q).val % n; rw [Fin.val_ofNat, Nat.mod_mod])


/-- **`Gal(ℚ(ζ_n)/ℚ)` is abelian.** Transport `ab = ba` from `(ℤ/n)ˣ`. -/
theorem cycloGaloisN_comm (σ τ : FieldAut Qc (cycloFieldN hn)) : σ * τ = τ * σ := by
  obtain ⟨u, rfl⟩ := (cycloGaloisIsoN hn).surjective σ
  obtain ⟨v, rfl⟩ := (cycloGaloisIsoN hn).surjective τ
  rw [← Hom.map_mul' (cycloGaloisIsoN hn).toHom, ← Hom.map_mul' (cycloGaloisIsoN hn).toHom,
    CommGroup.mul_comm' u v]

/-- The commutative group structure on `Gal(ℚ(ζ_n)/ℚ)`, extending its group structure. -/
noncomputable instance cycloGaloisN_commGroup : CommGroup (FieldAut Qc (cycloFieldN hn)) :=
  { (inferInstance : Group (FieldAut Qc (cycloFieldN hn))) with
    mul_comm := cycloGaloisN_comm hn }

/-- `Gal(ℚ(ζ_n)/ℚ)` is finite, listed as the images of `(ℤ/n)ˣ`. -/
noncomputable instance cycloGaloisN_finite : FiniteType (FieldAut Qc (cycloFieldN hn)) :=
  finiteTypeOfIso (cycloGaloisIsoN hn)

/-- `|Gal(ℚ(ζ_n)/ℚ)| = φ(n)`. -/
theorem card_cycloGaloisN : card (FieldAut Qc (cycloFieldN hn)) = totient n :=
  (card_finiteTypeOfIso (cycloGaloisIsoN hn)).trans (card_zmodUnits n)

end GalN

/-! ## The dictionary -/

section Dictionary

variable {n : Nat} (hn : 1 ≤ n) [NeZero n]

/-- **The `GL(1)` dictionary over `ℚ(ζ_n)`.** For every `n ≥ 1`, the Dirichlet characters
modulo `n` and the characters of `Gal(ℚ(ζ_n)/ℚ)` form isomorphic groups: `χ ↦ ρ_χ = χ ∘ e⁻¹`,
where `e : (ℤ/n)ˣ ≅ Gal(ℚ(ζ_n)/ℚ)` is `cycloGaloisIsoN`. -/
noncomputable def dirichletGaloisN :
    Character (ZModUnits n) ≃* Character (FieldAut Qc (cycloFieldN hn)) :=
  dualIso (cycloGaloisIsoN hn).symm

/-- `ρ_χ(σ_a) = χ(a)` for every unit `a` of `ℤ/n`. -/
theorem dirichletGaloisN_iso (χ : Character (ZModUnits n)) (u : ZModUnits n) :
    ((dirichletGaloisN hn) χ).1 (cycloGaloisIsoN hn u) = χ.1 u := by
  show χ.1 ((cycloGaloisIsoN hn).invFun ((cycloGaloisIsoN hn).toFun u)) = χ.1 u
  rw [(cycloGaloisIsoN hn).left_inv]

/-- `ρ_χ(σ_a) = χ(a)` for every `a` prime to `n`. -/
theorem dirichletGaloisN_galAutN (χ : Character (ZModUnits n)) {a : Nat} (ha : Nat.Coprime a n) :
    ((dirichletGaloisN hn) χ).1 (galAutN hn ha) = dchar χ a := by
  rw [galAutN_eq_iso hn ha, dirichletGaloisN_iso, dchar_of_coprime χ ha]

/-- **Frobenius matches Dirichlet characters.** For every `n ≥ 1`, every Dirichlet character
`χ` modulo `n` and every prime `q ∤ n`, the corresponding Galois character `ρ_χ` takes the
value `χ(q)` at the Frobenius element `σ_q` (the automorphism `ζ_n ↦ ζ_n^q`, which reduces to
the `q`-th power map modulo `q` by `reduceN_galAut`). -/
theorem dirichletGaloisN_frobenius (χ : Character (ZModUnits n)) {q : Nat} (hq : IsPrime q)
    (hqn : ¬ q ∣ n) :
    ((dirichletGaloisN hn) χ).1 (galAutN hn (coprime_of_prime_not_dvd hq hqn)) = dchar χ q :=
  dirichletGaloisN_galAutN hn χ _

/-- The same with `frobN`: `ρ_χ(Frob_q) = χ(q)` for primes `q ∤ n`. -/
theorem dirichletGaloisN_frobN (χ : Character (ZModUnits n)) {q : Nat} (hq : IsPrime q)
    (hqn : ¬ q ∣ n) : ((dirichletGaloisN hn) χ).1 (frobN hn q) = dchar χ q := by
  rw [frobN_eq hn (coprime_of_prime_not_dvd hq hqn)]
  exact dirichletGaloisN_frobenius hn χ hq hqn

/-- **The dictionary read backwards.** Every character `ρ` of `Gal(ℚ(ζ_n)/ℚ)` comes from the
Dirichlet character `χ_ρ = ρ ∘ e`, and `χ_ρ(q) = ρ(σ_q)` for primes `q ∤ n`. -/
theorem galoisDirichletN_frobenius (ρ : Character (FieldAut Qc (cycloFieldN hn))) {q : Nat}
    (hq : IsPrime q) (hqn : ¬ q ∣ n) :
    dchar ((dirichletGaloisN hn).invFun ρ) q =
      ρ.1 (galAutN hn (coprime_of_prime_not_dvd hq hqn)) := by
  have h := dirichletGaloisN_frobenius hn ((dirichletGaloisN hn).invFun ρ) hq hqn
  rw [(dirichletGaloisN hn).right_inv] at h
  exact h.symm

/-- The dictionary respects products: `ρ_{χψ} = ρ_χ ρ_ψ`. -/
theorem dirichletGaloisN_mul (χ ψ : Character (ZModUnits n)) :
    (dirichletGaloisN hn) (χ * ψ) = (dirichletGaloisN hn) χ * (dirichletGaloisN hn) ψ :=
  Hom.map_mul' (dirichletGaloisN hn).toHom χ ψ

/-- The trivial Dirichlet character corresponds to the trivial Galois character. -/
theorem dirichletGaloisN_one : (dirichletGaloisN hn) 1 = 1 :=
  Hom.map_one (dirichletGaloisN hn).toHom

/-- **There are `φ(n)` Galois characters of `ℚ(ζ_n)`**, as many as Dirichlet characters
modulo `n`. -/
theorem card_galoisCharacterN : card (Character (FieldAut Qc (cycloFieldN hn))) = totient n := by
  rw [card_character, card_cycloGaloisN]

/-! ## Frobenius elements fill the Galois group -/

/-- **Every element of `Gal(ℚ(ζ_n)/ℚ)` is a Frobenius element, infinitely often.** For every
`σ` and every bound `N` there is a prime `q ≥ N`, `q ∤ n`, with `σ = σ_q`. This is the
qualitative Chebotarev density theorem for `ℚ(ζ_n)/ℚ`; here it is Dirichlet's theorem on primes
in arithmetic progressions, applied to the class `a mod n` with `σ = σ_a`. -/
theorem exists_frobenius_eq (σ : FieldAut Qc (cycloFieldN hn)) (N : Nat) :
    ∃ q, N ≤ q ∧ ∃ (hq : IsPrime q) (hqn : ¬ q ∣ n),
      σ = galAutN hn (coprime_of_prime_not_dvd hq hqn) := by
  obtain ⟨u, rfl⟩ := (cycloGaloisIsoN hn).surjective σ
  obtain ⟨q, hNq, hq, hqu⟩ := dirichlet (by omega : 0 < n) u.2 (N + n + 1)
  have hq' : IsPrime q := hq
  have hcop : Nat.Coprime q n := by rw [← coprime_mod_iff, hqu, coprime_mod_iff]; exact u.2
  have hqn : ¬ q ∣ n := fun h => by
    have := Nat.le_of_dvd (by omega) h; omega
  refine ⟨q, by omega, hq', hqn, ?_⟩
  have e : cycloGaloisIsoN hn u = galAutN hn u.2 := rfl
  rw [e]
  exact galAutN_congr hn _ _ (by rw [hqu])

/-- **Galois characters are determined by their Frobenius values.** Two characters of
`Gal(ℚ(ζ_n)/ℚ)` agreeing at `σ_q` for every prime `q ∤ n` are equal. -/
theorem galoisChar_ext_frobenius {ρ ρ' : Character (FieldAut Qc (cycloFieldN hn))}
    (h : ∀ q (hq : IsPrime q) (hqn : ¬ q ∣ n),
      ρ.1 (galAutN hn (coprime_of_prime_not_dvd hq hqn)) =
        ρ'.1 (galAutN hn (coprime_of_prime_not_dvd hq hqn))) : ρ = ρ' :=
  Character.ext fun σ => by
    obtain ⟨q, _, hq, hqn, rfl⟩ := exists_frobenius_eq hn σ 0
    exact h q hq hqn

/-- **Uniqueness in the dictionary.** `ρ_χ` is the only character `ρ` of `Gal(ℚ(ζ_n)/ℚ)` with
`ρ(σ_q) = χ(q)` for every prime `q ∤ n`. -/
theorem dirichletGaloisN_unique (χ : Character (ZModUnits n))
    (ρ : Character (FieldAut Qc (cycloFieldN hn)))
    (h : ∀ q (hq : IsPrime q) (hqn : ¬ q ∣ n),
      ρ.1 (galAutN hn (coprime_of_prime_not_dvd hq hqn)) = dchar χ q) :
    ρ = (dirichletGaloisN hn) χ :=
  galoisChar_ext_frobenius hn fun q hq hqn => by
    rw [h q hq hqn, dirichletGaloisN_frobenius hn χ hq hqn]

include hn in
/-- **Dirichlet characters are determined by their values at primes `q ∤ n`** (a consequence of
Dirichlet's theorem, read through the dictionary). -/
theorem dchar_ext_primes {χ ψ : Character (ZModUnits n)}
    (h : ∀ q, IsPrime q → ¬ q ∣ n → dchar χ q = dchar ψ q) : χ = ψ := by
  apply (dirichletGaloisN hn).injective
  apply galoisChar_ext_frobenius hn
  intro q hq hqn
  rw [dirichletGaloisN_frobenius hn χ hq hqn, dirichletGaloisN_frobenius hn ψ hq hqn, h q hq hqn]

end Dictionary

end Foundations.Langlands
