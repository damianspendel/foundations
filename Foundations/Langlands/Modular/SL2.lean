import Foundations.Algebra.Group

/-!
# The modular group SL₂(ℤ)

In 1877–1880 Felix Klein and, independently and from a different direction, Henri Poincaré
put a single group at the centre of nineteenth-century analysis: the group of integer
`2 × 2` matrices of determinant one,

  `SL₂(ℤ) = { (a b; c d) : a, b, c, d ∈ ℤ, ad − bc = 1 }`.

Klein met it through the icosahedron, elliptic modular functions and the "modular
figure" (the tessellation of the upper half-plane by copies of a curvilinear triangle);
Poincaré met it through Fuchsian functions and recognised that its action on the upper
half-plane is an action by isometries of the hyperbolic plane. Both saw that the functions
invariant (or nearly invariant) under this group — *modular functions* and *modular forms* —
carry arithmetic information: Jacobi's theta functions, Eisenstein series, the `j`-invariant
classifying elliptic curves.

This file builds the group itself, from Lean's built-in integers. A matrix is a structure
with four integer entries and a proof that the determinant is `1`; multiplication is the
usual matrix product (the determinant is multiplicative), and the inverse of `(a b; c d)` is
`(d −b; −c a)`. We register it as a `Group` in the sense of `Foundations.Algebra.Group`.

We then define the two classical generators

  `S = (0 −1; 1 0)`  (the inversion `τ ↦ −1/τ`),  `T = (1 1; 0 1)`  (the translation `τ ↦ τ + 1`),

and verify the defining relations of the modular group: `S² = −I` and `(ST)³ = −I`. (That
these relations, together with `−I` being central of order two, give a *presentation* of
`SL₂(ℤ)` is a classical theorem not proved here; the file `Generation` proves the weaker
statement that `S` and `T` generate.)
-/

namespace Foundations.Langlands.Modular

open Foundations.Algebra

/-- **The modular group SL₂(ℤ).** An element is an integer matrix `(a b; c d)` together with
a proof that its determinant `ad − bc` equals `1`. -/
structure SL2Z where
  /-- Top-left entry. -/
  a : Int
  /-- Top-right entry. -/
  b : Int
  /-- Bottom-left entry. -/
  c : Int
  /-- Bottom-right entry. -/
  d : Int
  /-- The determinant is one. -/
  det : a * d - b * c = 1

namespace SL2Z

/-- Two elements of SL₂(ℤ) with the same entries are equal (the determinant proof is
irrelevant). -/
theorem ext {g h : SL2Z} (ha : g.a = h.a) (hb : g.b = h.b) (hc : g.c = h.c) (hd : g.d = h.d) :
    g = h := by
  cases g; cases h; simp only at ha hb hc hd; subst ha hb hc hd; rfl

/-- The matrix product `(a b; c d)(a' b'; c' d')`; the determinant is multiplicative. -/
def mul (g h : SL2Z) : SL2Z where
  a := g.a * h.a + g.b * h.c
  b := g.a * h.b + g.b * h.d
  c := g.c * h.a + g.d * h.c
  d := g.c * h.b + g.d * h.d
  det := by
    have e : (g.a * h.a + g.b * h.c) * (g.c * h.b + g.d * h.d) -
        (g.a * h.b + g.b * h.d) * (g.c * h.a + g.d * h.c) =
        (g.a * g.d - g.b * g.c) * (h.a * h.d - h.b * h.c) := by grind
    rw [e, g.det, h.det]; rfl

/-- The identity matrix. -/
def one : SL2Z := ⟨1, 0, 0, 1, by decide⟩

/-- The inverse `(a b; c d)⁻¹ = (d −b; −c a)` (adjugate, since the determinant is `1`). -/
def inv (g : SL2Z) : SL2Z := ⟨g.d, -g.b, -g.c, g.a, by have := g.det; grind⟩

/-- Matrix multiplication. -/
instance : Mul SL2Z := ⟨mul⟩
/-- The identity. -/
instance : One SL2Z := ⟨one⟩
/-- The inverse. -/
instance : Inv SL2Z := ⟨inv⟩

/-- Entries of a product. -/
@[simp] theorem mul_a (g h : SL2Z) : (g * h).a = g.a * h.a + g.b * h.c := rfl
/-- Entries of a product. -/
@[simp] theorem mul_b (g h : SL2Z) : (g * h).b = g.a * h.b + g.b * h.d := rfl
/-- Entries of a product. -/
@[simp] theorem mul_c (g h : SL2Z) : (g * h).c = g.c * h.a + g.d * h.c := rfl
/-- Entries of a product. -/
@[simp] theorem mul_d (g h : SL2Z) : (g * h).d = g.c * h.b + g.d * h.d := rfl
/-- Entries of the identity. -/
@[simp] theorem one_a : (1 : SL2Z).a = 1 := rfl
/-- Entries of the identity. -/
@[simp] theorem one_b : (1 : SL2Z).b = 0 := rfl
/-- Entries of the identity. -/
@[simp] theorem one_c : (1 : SL2Z).c = 0 := rfl
/-- Entries of the identity. -/
@[simp] theorem one_d : (1 : SL2Z).d = 1 := rfl
/-- Entries of the inverse. -/
@[simp] theorem inv_a (g : SL2Z) : g⁻¹.a = g.d := rfl
/-- Entries of the inverse. -/
@[simp] theorem inv_b (g : SL2Z) : g⁻¹.b = -g.b := rfl
/-- Entries of the inverse. -/
@[simp] theorem inv_c (g : SL2Z) : g⁻¹.c = -g.c := rfl
/-- Entries of the inverse. -/
@[simp] theorem inv_d (g : SL2Z) : g⁻¹.d = g.a := rfl

/-- **SL₂(ℤ) is a group.** Matrix multiplication is associative, `I` is an identity and the
adjugate is an inverse. -/
instance instGroup : Group SL2Z where
  mul_assoc g h k := by apply ext <;> simp only [mul_a, mul_b, mul_c, mul_d] <;> grind
  one_mul g := by apply ext <;> simp only [mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c,
    one_d] <;> grind
  inv_mul_cancel g := by
    have := g.det
    apply ext <;> simp only [mul_a, mul_b, mul_c, mul_d, inv_a, inv_b, inv_c, inv_d, one_a,
      one_b, one_c, one_d] <;> grind

/-- The matrix `−I = (−1 0; 0 −1)`, the non-trivial central element of SL₂(ℤ). -/
def negOne : SL2Z := ⟨-1, 0, 0, -1, by decide⟩

/-- The negative `−g = (−a −b; −c −d)`; equal to `(−I) g`. -/
def neg (g : SL2Z) : SL2Z := ⟨-g.a, -g.b, -g.c, -g.d, by have := g.det; grind⟩

/-- **The generator S.** `S = (0 −1; 1 0)`, acting as `τ ↦ −1/τ`. -/
def S : SL2Z := ⟨0, -1, 1, 0, by decide⟩

/-- **The generator T.** `T = (1 1; 0 1)`, acting as `τ ↦ τ + 1`. -/
def T : SL2Z := ⟨1, 1, 0, 1, by decide⟩

/-- The integer translation matrix `(1 n; 0 1)`, acting as `τ ↦ τ + n`; it equals `Tⁿ`
(`Generation.T_zpow_eq`). -/
def Tn (n : Int) : SL2Z := ⟨1, n, 0, 1, by grind⟩

/-- **S² = −I.** -/
theorem S_mul_S : S * S = negOne := by apply ext <;> rfl

/-- **(ST)³ = −I.** -/
theorem ST_cube : S * T * (S * T) * (S * T) = negOne := by apply ext <;> rfl

/-- `S⁴ = I`: `S` has order four. -/
theorem S_pow_four : S * S * (S * S) = 1 := by apply ext <;> rfl

/-- `−I` is central: it commutes with every element. -/
theorem negOne_mul_comm (g : SL2Z) : negOne * g = g * negOne := by
  apply ext <;> simp only [mul_a, mul_b, mul_c, mul_d] <;> simp [negOne] <;> grind

/-- `(−I) g = −g`. -/
theorem negOne_mul (g : SL2Z) : negOne * g = neg g := by
  apply ext <;> simp only [mul_a, mul_b, mul_c, mul_d] <;> simp [negOne, neg]

/-- `(−I)² = I`. -/
theorem negOne_mul_negOne : negOne * negOne = 1 := by apply ext <;> rfl

/-- `−I ≠ I`, so `−I` has order exactly two. -/
theorem negOne_ne_one : negOne ≠ 1 := fun h => by
  have := congrArg SL2Z.a h; simp [negOne] at this

/-- The inverse of `S` is `−S = S³`. -/
theorem S_inv : S⁻¹ = negOne * S := by apply ext <;> rfl

/-- The inverse of `T` is `(1 −1; 0 1)`. -/
theorem T_inv : T⁻¹ = Tn (-1) := by apply ext <;> rfl

/-- `Tₘ Tₙ = Tₘ₊ₙ`. -/
theorem Tn_mul (m n : Int) : Tn m * Tn n = Tn (m + n) := by
  apply ext <;> simp [Tn] <;> grind

/-- `T₁ = T`. -/
theorem Tn_one : Tn 1 = T := rfl

/-- `T₀ = I`. -/
theorem Tn_zero : Tn 0 = 1 := rfl

/-- The effect of left multiplication by `Tₙ`: it adds `n` times the bottom row to the top
row, leaving the bottom row unchanged. -/
theorem Tn_mul_entries (n : Int) (g : SL2Z) :
    (Tn n * g).a = g.a + n * g.c ∧ (Tn n * g).b = g.b + n * g.d ∧
      (Tn n * g).c = g.c ∧ (Tn n * g).d = g.d := by
  simp [Tn]

/-- The effect of left multiplication by `S`: `(a b; c d) ↦ (−c −d; a b)`. -/
theorem S_mul_entries (g : SL2Z) :
    (S * g).a = -g.c ∧ (S * g).b = -g.d ∧ (S * g).c = g.a ∧ (S * g).d = g.b := by
  simp [S]

end SL2Z

end Foundations.Langlands.Modular
