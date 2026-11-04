import Foundations.Langlands.Rep.S3

/-!
# The character table of `A₄`

The alternating group `A₄`, the rotation group of the tetrahedron, is built here directly as the
semidirect product `V ⋊ C₃` of the Klein four-group `V = (ℤ/2)²` (the double transpositions)
by a cyclic group of order 3 (a 3-cycle) acting on `V` through the order-3 automorphism
`φ(x, y) = (y, x + y)`. An element `⟨x, y, a⟩` stands for `v · c^a` with `v = (x, y) ∈ V`.
(The identification with the even permutations of four letters is not formalised here.)

Its irreducible complex representations, all monomial:

* three of degree 1, `λ_k(v c^a) = ω^{k a}` for `k = 0, 1, 2`, pulled back along `A₄ → C₃`
  (`lin k`), with `ω` a primitive cube root of unity;
* one of degree 3 (`three`): `V` acts diagonally by its three non-trivial characters
  (`±1` entries), and `c` permutes the three coordinate axes cyclically (classically, the rotation
  representation of the tetrahedron).

Each is irreducible by the criterion `Σ_g χ(g) χ(g⁻¹) = |G|`, they are pairwise non-isomorphic,
and `1 + 1 + 1 + 9 = 12 = |A₄|`, so they are all the irreducibles (`A4.irreducibles_complete`).
The character table (`A4.character_table`), on the classes of `1`, a double transposition `t`, a
3-cycle `c` and `c²`:

| | `1` | `t` | `c` | `c²` |
|---|---|---|---|---|
| `λ₀` | 1 | 1 | 1 | 1 |
| `λ₁` | 1 | 1 | ω | ω² |
| `λ₂` | 1 | 1 | ω² | ω |
| `ρ₃` | 3 | −1 | 0 | 0 |
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

/-- **The group `A₄`**, as `V ⋊ C₃`: the element `⟨x, y, a⟩` is `v c^a` with `v = (x, y)` in
the Klein four-group and `c` of order 3. -/
structure A4 where
  /-- First coordinate of the Klein four-group part. -/
  x : Fin 2
  /-- Second coordinate of the Klein four-group part. -/
  y : Fin 2
  /-- The exponent of the 3-cycle. -/
  a : Fin 3
deriving DecidableEq

namespace A4

/-- The automorphism `φ^a` of `V = (ℤ/2)²`, where `φ(x, y) = (y, x + y)` has order 3. -/
def rot : Fin 3 → Fin 2 → Fin 2 → Fin 2 × Fin 2
  | 0, x, y => (x, y)
  | 1, x, y => (y, x + y)
  | 2, x, y => (x + y, x)

/-- Multiplication: `(v c^a)(w c^b) = (v + φ^a w) c^(a + b)`. -/
def mul (g h : A4) : A4 :=
  ⟨g.x + (rot g.a h.x h.y).1, g.y + (rot g.a h.x h.y).2, g.a + h.a⟩

/-- Inversion: `(v c^a)⁻¹ = φ^(-a)(v) c^(-a)`. -/
def inv (g : A4) : A4 := ⟨(rot (-g.a) g.x g.y).1, (rot (-g.a) g.x g.y).2, -g.a⟩

/-- **`A₄` is a group** (all axioms checked by evaluation). -/
instance : Group A4 where
  mul := mul
  one := ⟨0, 0, 0⟩
  inv := inv
  mul_assoc := by
    intro ⟨x₁, y₁, a₁⟩ ⟨x₂, y₂, a₂⟩ ⟨x₃, y₃, a₃⟩
    show mul (mul _ _) _ = mul _ (mul _ _)
    revert x₁ y₁ a₁ x₂ y₂ a₂ x₃ y₃ a₃; decide
  one_mul := by
    intro ⟨x, y, a⟩; show mul _ _ = _; revert x y a; decide
  inv_mul_cancel := by
    intro ⟨x, y, a⟩; show mul (inv _) _ = ⟨0, 0, 0⟩; revert x y a; decide

/-- The census of the twelve elements. -/
def elems12 : List A4 :=
  [⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, 1, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 1⟩,
    ⟨0, 0, 2⟩, ⟨1, 0, 2⟩, ⟨0, 1, 2⟩, ⟨1, 1, 2⟩]

/-- `A₄` is finite. -/
instance : FiniteType A4 where
  elems := elems12
  nodup := by decide
  complete := by intro ⟨x, y, a⟩; revert x y a; decide

/-- `|A₄| = 12`. -/
theorem card_A4 : card A4 = 12 := rfl

/-- A pairing over `A₄`, written out with the inverses computed. -/
theorem pairing_A4 (χ ψ : A4 → C) :
    pairing χ ψ = χ ⟨0, 0, 0⟩ * ψ ⟨0, 0, 0⟩ + (χ ⟨1, 0, 0⟩ * ψ ⟨1, 0, 0⟩ +
      (χ ⟨0, 1, 0⟩ * ψ ⟨0, 1, 0⟩ + (χ ⟨1, 1, 0⟩ * ψ ⟨1, 1, 0⟩ +
      (χ ⟨0, 0, 1⟩ * ψ ⟨0, 0, 2⟩ + (χ ⟨1, 0, 1⟩ * ψ ⟨1, 1, 2⟩ +
      (χ ⟨0, 1, 1⟩ * ψ ⟨1, 0, 2⟩ + (χ ⟨1, 1, 1⟩ * ψ ⟨0, 1, 2⟩ +
      (χ ⟨0, 0, 2⟩ * ψ ⟨0, 0, 1⟩ + (χ ⟨1, 0, 2⟩ * ψ ⟨0, 1, 1⟩ +
      (χ ⟨0, 1, 2⟩ * ψ ⟨1, 1, 1⟩ + (χ ⟨1, 1, 2⟩ * ψ ⟨1, 0, 1⟩ + 0))))))))))) :=
  rfl

/-- A double transposition `t`. -/
def t : A4 := ⟨1, 0, 0⟩

/-- A 3-cycle `c`. -/
def c : A4 := ⟨0, 0, 1⟩

/-- The 3-cycle `c²`. -/
def c2 : A4 := ⟨0, 0, 2⟩

/-- **Conjugacy classes of `A₄`.** Every element is conjugate to `1`, `t`, `c` or `c²` (these
four are pairwise non-conjugate, as the character table below separates them and characters
are class functions; that last step is not stated as a theorem). -/
theorem conj_rep (g : A4) : ∃ h : A4, h * g * h⁻¹ = ⟨0, 0, 0⟩ ∨ h * g * h⁻¹ = ⟨1, 0, 0⟩ ∨
    h * g * h⁻¹ = ⟨0, 0, 1⟩ ∨ h * g * h⁻¹ = ⟨0, 0, 2⟩ := by
  obtain ⟨x, y, a⟩ := g
  have : ∃ x' y' b, mul (mul ⟨x', y', b⟩ ⟨x, y, a⟩) (inv ⟨x', y', b⟩) = ⟨0, 0, 0⟩ ∨
      mul (mul ⟨x', y', b⟩ ⟨x, y, a⟩) (inv ⟨x', y', b⟩) = ⟨1, 0, 0⟩ ∨
      mul (mul ⟨x', y', b⟩ ⟨x, y, a⟩) (inv ⟨x', y', b⟩) = ⟨0, 0, 1⟩ ∨
      mul (mul ⟨x', y', b⟩ ⟨x, y, a⟩) (inv ⟨x', y', b⟩) = ⟨0, 0, 2⟩ := by
    revert x y a; decide
  obtain ⟨x', y', b, h⟩ := this
  exact ⟨⟨x', y', b⟩, h⟩

/-! ## The one-dimensional representations -/

/-- The **one-dimensional representation** `λ_k : v c^a ↦ ω^{k a}`, for `k : Fin 3`. -/
noncomputable def lin (k : Fin 3) : Rep A4 C (Fin 1) :=
  monoRep omega3 omega3_cube (fun _ j => j) (fun g _ => k * g.a)
    (fun _ => ⟨rfl, by revert k; decide⟩)
    (fun g h _ => ⟨rfl, by
      obtain ⟨x, y, a⟩ := g; obtain ⟨x', y', b⟩ := h
      show k * (a + b) = k * a + k * b
      revert k a b; decide⟩)

/-- The character of `λ_k`: `λ_k(v c^a) = ω^{k a}`. -/
theorem character_lin (k : Fin 3) (g : A4) : character (lin k) g = cpow omega3 (k * g.a).val := by
  rw [lin, character_monoRep, isum_fin_succ, isum_fin_zero, S3.kd_fin, if_pos rfl]
  show (1 : C) * _ + 0 = _
  grind

/-- `λ_k(g) λ_k(g⁻¹) = 1`. -/
theorem character_lin_mul_inv (k : Fin 3) (g : A4) :
    character (lin k) g * character (lin k) g⁻¹ = 1 := by
  rw [character_lin, character_lin, ← cpow_fin_add omega3_cube]
  have e : k * g.a + k * g⁻¹.a = 0 := by
    obtain ⟨x, y, a⟩ := g
    show k * a + k * (-a) = 0
    revert k a; decide
  rw [e]; rfl

/-- Each `λ_k` is irreducible. -/
theorem lin_irreducible (k : Fin 3) : Irreducible (lin k) := by
  rw [irreducible_iff_pairing]
  unfold pairing
  rw [isum_congr (character_lin_mul_inv k), isum_const, Ring.mul_one]

/-- The values `1, ω, ω²` of `λ₀, λ₁, λ₂` at `c`. -/
theorem character_lin_c (k : Fin 3) : character (lin k) c = cpow omega3 k.val := by
  rw [character_lin]
  show cpow omega3 (k * 1).val = _
  rw [Fin.mul_one]

/-- The `λ_k` are pairwise non-isomorphic: their values `ω^k` at `c` are distinct. -/
theorem lin_distinct (k k' : Fin 3) (h : k ≠ k') : ¬ Iso (lin k) (lin k') := fun hi => by
  have e := congrFun (character_eq_of_iso hi) c
  rw [character_lin_c, character_lin_c] at e
  have e1 : cpow omega3 1 = omega3 := Ring.one_mul _
  have e2 : cpow omega3 2 = omega3 * omega3 := by
    show 1 * omega3 * omega3 = _; rw [Ring.one_mul]
  revert h e
  match k, k' with
  | 0, 0 => exact fun h => absurd rfl h
  | 0, 1 => exact fun _ e => omega3_ne_one (e1.symm.trans e.symm)
  | 0, 2 => exact fun _ e => omega3_sq_ne_one (e2.symm.trans e.symm)
  | 1, 0 => exact fun _ e => omega3_ne_one (e1.symm.trans e)
  | 1, 1 => exact fun h => absurd rfl h
  | 1, 2 => exact fun _ e => omega3_ne_sq (e1.symm.trans (e.trans e2))
  | 2, 0 => exact fun _ e => omega3_sq_ne_one (e2.symm.trans e)
  | 2, 1 => exact fun _ e => omega3_ne_sq (e1.symm.trans (e.symm.trans e2))
  | 2, 2 => exact fun h => absurd rfl h

/-! ## The three-dimensional representation -/

/-- The three non-trivial characters of `V`, as exponents of `-1`:
`(x, y) ↦ x`, `y`, `x + y`. -/
def lam : Fin 3 → Fin 2 → Fin 2 → Fin 2
  | 0, x, _ => x
  | 1, _, y => y
  | 2, x, y => x + y

/-- The basis permutation of `ρ₃`: `c^a` sends the axis `e_j` to `e_{j-a}`. -/
def threeP (g : A4) (j : Fin 3) : Fin 3 := j - g.a

/-- The signs of `ρ₃`: `v c^a` sends `e_j` to `±e_{j - a}`, the sign being the value of the
`(j - a)`-th character of `V` at `v`. -/
def threeE (g : A4) (j : Fin 3) : Fin 2 := lam (threeP g j) g.x g.y

/-- The cocycle rules for `ρ₃` (checked by evaluation). -/
theorem three_cocycle (g h : A4) (j : Fin 3) :
    threeP (g * h) j = threeP g (threeP h j) ∧
      threeE (g * h) j = threeE g (threeP h j) + threeE h j := by
  obtain ⟨x, y, a⟩ := g; obtain ⟨x', y', b⟩ := h
  show threeP (mul _ _) j = _ ∧ threeE (mul _ _) j = _
  revert x y a x' y' b j; decide

/-- The **three-dimensional representation** `ρ₃` of `A₄` by signed permutation matrices:
`V` acts by the diagonal matrices `diag(±1, ±1, ±1)` of determinant `1`, and `c` permutes the
coordinates cyclically. -/
noncomputable def three : Rep A4 C (Fin 3) :=
  monoRep (-1 : C) neg_one_sq_C threeP threeE (fun j => by revert j; decide) three_cocycle

/-- The character of `ρ₃` at `v ∈ V`: `(-1)^x + (-1)^y + (-1)^(x+y)`. -/
theorem character_three_V (x y : Fin 2) :
    character three ⟨x, y, 0⟩ =
      cpow (-1 : C) x.val + cpow (-1 : C) y.val + cpow (-1 : C) (x + y).val := by
  rw [three, character_monoRep, isum_fin3, S3.kd_fin, S3.kd_fin, S3.kd_fin]
  show (if (0 : Fin 3) = 0 then (1 : C) else 0) * _ + (if (1 : Fin 3) = 1 then (1 : C) else 0) * _
    + (if (2 : Fin 3) = 2 then (1 : C) else 0) * _ = _
  rw [if_pos rfl, if_pos rfl, if_pos rfl, Ring.one_mul, Ring.one_mul, Ring.one_mul]
  rfl

/-- The character of `ρ₃` vanishes off `V`. -/
theorem character_three_off (x y : Fin 2) (a : Fin 3) (ha : a ≠ 0) :
    character three ⟨x, y, a⟩ = 0 := by
  rw [three, character_monoRep, isum_fin3, S3.kd_fin, S3.kd_fin, S3.kd_fin]
  have h : ∀ j : Fin 3, j ≠ j - a := by revert a; decide
  show (if (0 : Fin 3) = 0 - a then (1 : C) else 0) * _ +
    (if (1 : Fin 3) = 1 - a then (1 : C) else 0) * _ +
    (if (2 : Fin 3) = 2 - a then (1 : C) else 0) * _ = _
  rw [if_neg (h 0), if_neg (h 1), if_neg (h 2), Ring.zero_mul, Ring.zero_mul, Ring.zero_mul,
    Ring.add_zero, Ring.add_zero]

/-- `χ₃(1) = 3`. -/
theorem character_three_one : character three ⟨0, 0, 0⟩ = 1 + 1 + 1 := by
  rw [character_three_V]; rfl

/-- `χ₃(v) = -1` for `v ≠ 1` in `V`. -/
theorem character_three_V_ne (x y : Fin 2) (h : (x, y) ≠ (0, 0)) :
    character three ⟨x, y, 0⟩ = -1 := by
  rw [character_three_V]
  have e1 : cpow (-1 : C) 1 = -1 := Ring.one_mul _
  revert h
  match x, y with
  | 0, 0 => exact fun h => absurd rfl h
  | 1, 0 => intro _; show cpow (-1 : C) 1 + cpow (-1 : C) 0 + cpow (-1 : C) 1 = -1
            rw [e1, cpow_zero]; grind
  | 0, 1 => intro _; show cpow (-1 : C) 0 + cpow (-1 : C) 1 + cpow (-1 : C) 1 = -1
            rw [e1, cpow_zero]; grind
  | 1, 1 => intro _; show cpow (-1 : C) 1 + cpow (-1 : C) 1 + cpow (-1 : C) 0 = -1
            rw [e1, cpow_zero]; grind

/-- `ρ₃` is irreducible: `Σ_g χ₃(g) χ₃(g⁻¹) = 9 + 1 + 1 + 1 = 12`. -/
theorem three_irreducible : Irreducible three := by
  rw [irreducible_iff_pairing, pairing_A4, character_three_one,
    character_three_V_ne 1 0 (by decide), character_three_V_ne 0 1 (by decide),
    character_three_V_ne 1 1 (by decide)]
  simp only [character_three_off _ _ 1 (by decide), character_three_off _ _ 2 (by decide)]
  show _ = (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : C)
  grind

/-! ## Completeness and the character table -/

/-- The degrees of the irreducibles of `A₄`: `1, 1, 1, 3`. -/
def dims : Fin 4 → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 3

/-- The list `λ₀, λ₁, λ₂, ρ₃` of irreducible complex representations of `A₄`. -/
noncomputable def irr : ∀ k : Fin 4, Rep A4 C (Fin (dims k))
  | 0 => lin 0
  | 1 => lin 1
  | 2 => lin 2
  | 3 => three

/-- Each representation in the list is irreducible. -/
theorem irr_irreducible : ∀ k, Irreducible (irr k)
  | 0 => lin_irreducible 0
  | 1 => lin_irreducible 1
  | 2 => lin_irreducible 2
  | 3 => three_irreducible

/-- Representations of different degrees are not isomorphic. -/
theorem not_iso_of_card {ι κ : Type} [FiniteType ι] [FiniteType κ] {ρ : Rep A4 C ι}
    {σ : Rep A4 C κ} (h : card ι ≠ card κ) : ¬ Iso ρ σ := fun hi => h hi.card_eq

/-- **The four representations are pairwise non-isomorphic.** -/
theorem irr_distinct : ∀ k k', k ≠ k' → ¬ Iso (irr k) (irr k')
  | 0, 0, h => absurd rfl h
  | 0, 1, _ => lin_distinct 0 1 (by decide)
  | 0, 2, _ => lin_distinct 0 2 (by decide)
  | 0, 3, _ => not_iso_of_card (by decide)
  | 1, 0, _ => lin_distinct 1 0 (by decide)
  | 1, 1, h => absurd rfl h
  | 1, 2, _ => lin_distinct 1 2 (by decide)
  | 1, 3, _ => not_iso_of_card (by decide)
  | 2, 0, _ => lin_distinct 2 0 (by decide)
  | 2, 1, _ => lin_distinct 2 1 (by decide)
  | 2, 2, h => absurd rfl h
  | 2, 3, _ => not_iso_of_card (by decide)
  | 3, 0, _ => not_iso_of_card (by decide)
  | 3, 1, _ => not_iso_of_card (by decide)
  | 3, 2, _ => not_iso_of_card (by decide)
  | 3, 3, h => absurd rfl h

/-- `1 + 1 + 1 + 3² = 12 = |A₄|`. -/
theorem sum_sq_dims : natSum (fun k => card (Fin (dims k)) * card (Fin (dims k))) = card A4 := by
  decide

/-- **The irreducible representations of `A₄`.** Every irreducible complex representation of
`A₄` is isomorphic to one of `λ₀, λ₁, λ₂` or `ρ₃`. -/
theorem irreducibles_complete {κ : Type} [FiniteType κ] (τ : Rep A4 C κ) (hτ : Irreducible τ) :
    Iso τ (lin 0) ∨ Iso τ (lin 1) ∨ Iso τ (lin 2) ∨ Iso τ three := by
  obtain ⟨k, hk⟩ := complete_of_sum_sq irr irr_irreducible irr_distinct sum_sq_dims τ hτ
  match k, hk with
  | 0, hk => exact .inl hk
  | 1, hk => exact .inr (.inl hk)
  | 2, hk => exact .inr (.inr (.inl hk))
  | 3, hk => exact .inr (.inr (.inr hk))

/-- **Character table of `A₄`.** On the class representatives `1`, `t`, `c`, `c²`:
`λ₀ = 1, 1, 1, 1`; `λ₁ = 1, 1, ω, ω²`; `λ₂ = 1, 1, ω², ω`; `χ₃ = 3, -1, 0, 0`. -/
theorem character_table :
    (character (lin 0) 1 = 1 ∧ character (lin 0) t = 1 ∧ character (lin 0) c = 1 ∧
      character (lin 0) c2 = 1) ∧
    (character (lin 1) 1 = 1 ∧ character (lin 1) t = 1 ∧ character (lin 1) c = omega3 ∧
      character (lin 1) c2 = omega3 * omega3) ∧
    (character (lin 2) 1 = 1 ∧ character (lin 2) t = 1 ∧
      character (lin 2) c = omega3 * omega3 ∧ character (lin 2) c2 = omega3) ∧
    (character three 1 = 1 + 1 + 1 ∧ character three t = -1 ∧ character three c = 0 ∧
      character three c2 = 0) := by
  have e1 : cpow omega3 1 = omega3 := Ring.one_mul _
  have e2 : cpow omega3 2 = omega3 * omega3 := by
    show 1 * omega3 * omega3 = _; rw [Ring.one_mul]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  all_goals first
    | exact character_three_one
    | exact character_three_V_ne 1 0 (by decide)
    | exact character_three_off 0 0 1 (by decide)
    | exact character_three_off 0 0 2 (by decide)
    | (rw [character_lin]; first | rfl | exact e1 | exact e2)

end A4

end Foundations.Langlands
