import Foundations.Langlands.Rep.Monomial

/-!
# The character table of `S₃`

The symmetric group on three letters is the smallest non-abelian group. Here it is built
directly as the semidirect product `C₃ ⋊ C₂`, the dihedral group of the triangle: an element
`⟨a, b⟩` with `a : Fin 3`, `b : Fin 2` stands for `r^a s^b`, where `r` is a rotation of order 3
and `s` a reflection with `s r s⁻¹ = r⁻¹`. (Its faithful action on the three vertices,
identifying it with the full permutation group of `Fin 3`, is not formalised here.)

It has three irreducible complex representations, all given by explicit monomial matrices:

* the trivial representation `𝟙` and the sign representation `ε` (`r ↦ 1`, `s ↦ -1`);
* the 2-dimensional standard representation `V`, written in a basis of eigenvectors of the
  rotation: `r ↦ diag(ω, ω²)` and `s ↦ (0 1; 1 0)`, with `ω` a primitive cube root of unity.

Each is irreducible by the criterion `Σ_g χ(g) χ(g⁻¹) = |G|`, they are pairwise
non-isomorphic, and since `1² + 1² + 2² = 6 = |S₃|` the completeness criterion of
`Completeness` shows that every irreducible complex representation of `S₃` is isomorphic to one
of them (`S3.irreducibles_complete`). The character table (`S3.character_table`), on the classes
of `1`, `r` and `s`, is

| | `1` | `r` | `s` |
|---|---|---|---|
| `𝟙` | 1 | 1 | 1 |
| `ε` | 1 | 1 | −1 |
| `V` | 2 | −1 | 0 |
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

/-- **The group `S₃`**, as `C₃ ⋊ C₂`: the element `⟨a, b⟩` is `r^a s^b`, with `r` of order 3,
`s` of order 2 and `s r = r⁻¹ s`. -/
structure S3 where
  /-- The rotation exponent. -/
  a : Fin 3
  /-- The reflection exponent. -/
  b : Fin 2
deriving DecidableEq

namespace S3

/-- Multiplication: `r^a s^b · r^c s^d = r^(a ± c) s^(b + d)`, with sign `+` iff `b = 0`. -/
def mul (x y : S3) : S3 := ⟨x.a + (if x.b = 0 then y.a else -y.a), x.b + y.b⟩

/-- Inversion: rotations are inverted, reflections are their own inverses. -/
def inv (x : S3) : S3 := ⟨if x.b = 0 then -x.a else x.a, x.b⟩

/-- **`S₃` is a group** (all axioms checked by evaluation). -/
instance : Group S3 where
  mul := mul
  one := ⟨0, 0⟩
  inv := inv
  mul_assoc := by
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    show mul (mul _ _) _ = mul _ (mul _ _)
    revert a b c d e f; decide
  one_mul := by
    intro ⟨a, b⟩; show mul _ _ = _; revert a b; decide
  inv_mul_cancel := by
    intro ⟨a, b⟩; show mul (inv _) _ = ⟨0, 0⟩; revert a b; decide

/-- The census of the six elements. -/
def elems6 : List S3 := [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]

/-- `S₃` is finite. -/
instance : FiniteType S3 where
  elems := elems6
  nodup := by decide
  complete := by intro ⟨a, b⟩; revert a b; decide

/-- `|S₃| = 6`. -/
theorem card_S3 : card S3 = 6 := rfl

/-- A sum over `S₃`, written out. -/
theorem isum_S3 {A : Type} [AddAbGroup A] (f : S3 → A) :
    isum f = f ⟨0, 0⟩ + (f ⟨1, 0⟩ + (f ⟨2, 0⟩ + (f ⟨0, 1⟩ + (f ⟨1, 1⟩ + (f ⟨2, 1⟩ + 0))))) :=
  rfl

/-- A pairing over `S₃`, written out (`r^a` is inverted to `r^(-a)`, reflections to themselves). -/
theorem pairing_S3 (χ ψ : S3 → C) :
    pairing χ ψ = χ ⟨0, 0⟩ * ψ ⟨0, 0⟩ + (χ ⟨1, 0⟩ * ψ ⟨2, 0⟩ + (χ ⟨2, 0⟩ * ψ ⟨1, 0⟩ +
      (χ ⟨0, 1⟩ * ψ ⟨0, 1⟩ + (χ ⟨1, 1⟩ * ψ ⟨1, 1⟩ + (χ ⟨2, 1⟩ * ψ ⟨2, 1⟩ + 0))))) :=
  rfl

/-- The rotation `r`. -/
def r : S3 := ⟨1, 0⟩

/-- The reflection `s`. -/
def s : S3 := ⟨0, 1⟩

/-- **Conjugacy classes of `S₃`.** Every element is conjugate to `1`, `r` or `s` (these three
are pairwise non-conjugate, as the character table below separates them and characters
are class functions; that last step is not stated as a theorem). -/
theorem conj_rep (g : S3) : ∃ h : S3, h * g * h⁻¹ = ⟨0, 0⟩ ∨ h * g * h⁻¹ = ⟨1, 0⟩ ∨
    h * g * h⁻¹ = ⟨0, 1⟩ := by
  obtain ⟨a, b⟩ := g
  have : ∃ c d, mul (mul ⟨c, d⟩ ⟨a, b⟩) (inv ⟨c, d⟩) = ⟨0, 0⟩ ∨
      mul (mul ⟨c, d⟩ ⟨a, b⟩) (inv ⟨c, d⟩) = ⟨1, 0⟩ ∨
      mul (mul ⟨c, d⟩ ⟨a, b⟩) (inv ⟨c, d⟩) = ⟨0, 1⟩ := by
    revert a b; decide
  obtain ⟨c, d, h⟩ := this
  exact ⟨⟨c, d⟩, h⟩

/-! ## The three representations -/

/-- `1¹ = 1`. -/
theorem one_pow_one : cpow (1 : C) 1 = 1 := Ring.one_mul 1

/-- The **trivial representation** of `S₃`, as a monomial representation of degree 1. -/
noncomputable def triv : Rep S3 C (Fin 1) :=
  monoRep (1 : C) one_pow_one (fun _ j => j) (fun _ _ => (0 : Fin 1))
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩)

/-- The exponent data of the sign representation. -/
def signE (g : S3) (_ : Fin 1) : Fin 2 := g.b

/-- The **sign representation** `ε` of `S₃`: rotations act by `1`, reflections by `-1`. -/
noncomputable def sign : Rep S3 C (Fin 1) :=
  monoRep (-1 : C) neg_one_sq_C (fun _ j => j) signE
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩)

/-- The basis permutation of the standard representation: reflections swap `e₀`, `e₁`. -/
def stdP (g : S3) (j : Fin 2) : Fin 2 := j + g.b

/-- The exponents of the standard representation: `r^a` acts as `diag(ω^a, ω^(2a))`. -/
def stdE (g : S3) (j : Fin 2) : Fin 3 := if stdP g j = 0 then g.a else g.a + g.a

/-- The cocycle rules for the standard representation. -/
theorem std_cocycle (g h : S3) (j : Fin 2) :
    stdP (g * h) j = stdP g (stdP h j) ∧ stdE (g * h) j = stdE g (stdP h j) + stdE h j := by
  obtain ⟨a, b⟩ := g; obtain ⟨c, d⟩ := h
  show stdP (mul _ _) j = _ ∧ stdE (mul _ _) j = _
  revert a b c d j; decide

/-- The **standard representation** `V` of `S₃`, of degree 2: `r ↦ diag(ω, ω²)` and
`s ↦ (0 1; 1 0)`, where `ω` is a primitive cube root of unity. -/
noncomputable def std : Rep S3 C (Fin 2) :=
  monoRep omega3 omega3_cube stdP stdE (fun j => by revert j; decide) std_cocycle

/-! ## Characters -/

/-- `kd` on `Fin n` is decided by equality. -/
theorem kd_fin {n : Nat} (i j : Fin n) : (kd i j : C) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; rw [kd_self, if_pos rfl]
  · rw [kd_ne h, if_neg h]

/-- The character of the trivial representation. -/
theorem character_triv (g : S3) : character triv g = 1 := by
  rw [triv, character_monoRep, isum_fin_succ, isum_fin_zero, kd_fin, if_pos rfl]
  show (1 : C) * 1 + 0 = 1
  grind

/-- The character of the sign representation: `(-1)^b` at `r^a s^b`. -/
theorem character_sign (g : S3) : character sign g = cpow (-1 : C) g.b.val := by
  rw [sign, character_monoRep, isum_fin_succ, isum_fin_zero, kd_fin, if_pos rfl]
  show (1 : C) * cpow (-1) g.b.val + 0 = _
  grind

/-- The character of the standard representation: `ω^a + ω^(2a)` at the rotation `r^a`, and
`0` at every reflection. -/
theorem character_std (g : S3) :
    character std g = if g.b = 0 then cpow omega3 g.a.val + cpow omega3 (g.a + g.a).val else 0 := by
  rw [std, character_monoRep, isum_fin2, kd_fin, kd_fin]
  obtain ⟨a, b⟩ := g
  revert b; intro b
  match b with
  | 0 =>
    simp only [stdP, stdE, Fin.add_zero, ↓reduceIte]
    rw [Ring.one_mul, Ring.one_mul]
    rfl
  | 1 =>
    simp only [stdP, stdE]
    simp (config := { decide := true }) only [↓reduceIte, Ring.zero_mul, Ring.add_zero]

/-- `χ_V(1) = 2`. -/
theorem character_std_one : character std ⟨0, 0⟩ = 1 + 1 := by
  rw [character_std]; show (1 : C) + 1 = 1 + 1; rfl

/-- `χ_V(r) = ω + ω² = -1`. -/
theorem character_std_r : character std ⟨1, 0⟩ = -1 := by
  rw [character_std]
  show cpow omega3 1 + cpow omega3 2 = -1
  have h := omega3_spec
  simp only [cpow]; grind

/-- `χ_V(r²) = ω² + ω⁴ = -1`. -/
theorem character_std_r2 : character std ⟨2, 0⟩ = -1 := by
  rw [character_std]
  show cpow omega3 2 + cpow omega3 1 = -1
  have h := omega3_spec
  simp only [cpow]; grind

/-- `χ_V` vanishes on reflections. -/
theorem character_std_refl (a : Fin 3) : character std ⟨a, 1⟩ = 0 := by
  rw [character_std]; rfl

/-- `1 ≠ -1` in `ℂ`. -/
theorem one_ne_neg_one_C : (1 : C) ≠ -1 := by
  intro h
  have := C.ncast_succ_ne_zero 1
  apply this
  show (1 : C) + 1 = 0
  grind

/-! ## Irreducibility, distinctness, completeness -/

/-- The trivial representation is irreducible. -/
theorem triv_irreducible : Irreducible triv := by
  rw [irreducible_iff_pairing]
  rw [pairing_S3]
  simp only [character_triv, card_S3]
  show _ = (1 + 1 + 1 + 1 + 1 + 1 : C)
  grind

/-- The sign representation is irreducible. -/
theorem sign_irreducible : Irreducible sign := by
  rw [irreducible_iff_pairing]
  rw [pairing_S3]
  simp only [character_sign]
  show _ = (1 + 1 + 1 + 1 + 1 + 1 : C)
  simp only [cpow]
  grind

/-- The standard representation is irreducible. -/
theorem std_irreducible : Irreducible std := by
  rw [irreducible_iff_pairing]
  rw [pairing_S3]
  rw [character_std_one, character_std_r, character_std_r2, character_std_refl,
    character_std_refl, character_std_refl]
  show _ = (1 + 1 + 1 + 1 + 1 + 1 : C)
  grind

/-- The degrees of the irreducibles of `S₃`: `1, 1, 2`. -/
def dims : Fin 3 → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2

/-- The list `𝟙, ε, V` of irreducible complex representations of `S₃`. -/
noncomputable def irr : ∀ k : Fin 3, Rep S3 C (Fin (dims k))
  | 0 => triv
  | 1 => sign
  | 2 => std

/-- Each representation in the list is irreducible. -/
theorem irr_irreducible : ∀ k, Irreducible (irr k)
  | 0 => triv_irreducible
  | 1 => sign_irreducible
  | 2 => std_irreducible

/-- The trivial and sign representations are not isomorphic: their characters differ at `s`. -/
theorem triv_not_iso_sign : ¬ Iso triv sign := fun h => by
  have e := congrFun (character_eq_of_iso h) s
  rw [character_triv, character_sign] at e
  exact one_ne_neg_one_C (e.trans (Ring.one_mul _))

/-- Representations of different degrees are not isomorphic. -/
theorem not_iso_of_card {ι κ : Type} [FiniteType ι] [FiniteType κ] {ρ : Rep S3 C ι}
    {σ : Rep S3 C κ} (h : card ι ≠ card κ) : ¬ Iso ρ σ := fun hi => h hi.card_eq

/-- **The three representations are pairwise non-isomorphic.** -/
theorem irr_distinct : ∀ k k', k ≠ k' → ¬ Iso (irr k) (irr k')
  | 0, 0, h => absurd rfl h
  | 0, 1, _ => triv_not_iso_sign
  | 0, 2, _ => not_iso_of_card (by decide)
  | 1, 0, _ => fun h => triv_not_iso_sign h.symm
  | 1, 1, h => absurd rfl h
  | 1, 2, _ => not_iso_of_card (by decide)
  | 2, 0, _ => not_iso_of_card (by decide)
  | 2, 1, _ => not_iso_of_card (by decide)
  | 2, 2, h => absurd rfl h

/-- `1² + 1² + 2² = 6 = |S₃|`. -/
theorem sum_sq_dims : natSum (fun k => card (Fin (dims k)) * card (Fin (dims k))) = card S3 := by
  decide

/-- **The irreducible representations of `S₃`.** Every irreducible complex representation of
`S₃` is isomorphic to the trivial, the sign or the standard representation. -/
theorem irreducibles_complete {κ : Type} [FiniteType κ] (τ : Rep S3 C κ) (hτ : Irreducible τ) :
    Iso τ triv ∨ Iso τ sign ∨ Iso τ std := by
  obtain ⟨k, hk⟩ := complete_of_sum_sq irr irr_irreducible irr_distinct sum_sq_dims τ hτ
  match k, hk with
  | 0, hk => exact .inl hk
  | 1, hk => exact .inr (.inl hk)
  | 2, hk => exact .inr (.inr hk)

/-- **Character table of `S₃`.** On the class representatives `1`, `r`, `s`: the trivial
character is `1, 1, 1`, the sign character `1, 1, -1`, and the standard character
`2, -1, 0`. -/
theorem character_table :
    (character triv 1 = 1 ∧ character triv r = 1 ∧ character triv s = 1) ∧
    (character sign 1 = 1 ∧ character sign r = 1 ∧ character sign s = -1) ∧
    (character std 1 = 1 + 1 ∧ character std r = -1 ∧ character std s = 0) := by
  refine ⟨⟨character_triv _, character_triv _, character_triv _⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [character_sign]; rfl
  · rw [character_sign]; rfl
  · rw [character_sign]; exact Ring.one_mul _
  · exact character_std_one
  · exact character_std_r
  · exact character_std_refl 0

end S3

end Foundations.Langlands
