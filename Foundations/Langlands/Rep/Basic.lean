import Foundations.Langlands.Rep.Matrix

/-!
# Representations of a group

A **representation** of a group `G` of degree `n` over a field `K` is a homomorphism
`ρ : G → GL_n(K)`: every group element becomes an invertible matrix, and composition in `G`
becomes matrix multiplication. Frobenius introduced the notion in 1896–97, in the papers
*Über Gruppencharaktere* and *Über die Darstellung der endlichen Gruppen durch lineare
Substitutionen*, after Dedekind had told him about the curious factorisation of the group
determinant `det(x_{gh⁻¹})`. Burnside, independently and soon after, made representations a
working tool of finite group theory (his `pᵃqᵇ` theorem of 1904 was proved with characters),
and Schur in 1905 rebuilt the theory on the simple lemma that now bears his name.

Why does this matter for the Langlands programme? Langlands' conjectures (1967) relate two
kinds of representations: *Galois representations*, homomorphisms from the absolute Galois
group of a number field into `GL_n`, and *automorphic representations*, which live on spaces
of functions on adelic groups. Both sides speak the language of this chapter: a homomorphism
of a group into matrices, broken into irreducible pieces, recorded by its character (on the
Galois side, by traces of Frobenius elements, which are the coefficients of `L`-functions).
The case `n = 1` is class field theory, and its finite shadow, the characters of a finite
abelian group, was built in `NumberTheory/DualGroup`.

This file provides the vocabulary over a commutative ring `K`:

* `Rep G K ι`, a representation on `K^ι` (degree `card ι`);
* subspaces of `K^ι`, invariant subspaces (*subrepresentations*), complements, and
  irreducibility;
* `IsGMap ρ σ T`, matrices intertwining two representations (*`G`-maps*), and isomorphism;
* the direct sum `ρ ⊕ σ` on `K^(ι ⊕ κ)`;
* the **character** `χ_ρ(g) = tr ρ(g)`, a class function, additive on direct sums and equal for
  isomorphic representations.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat

set_option linter.unusedSectionVars false

universe u v w

/-- **Representation.** A representation of the group `G` on `K^ι` is a map `ρ : G → Mat ι ι K`
with `ρ(1) = 1` and `ρ(gh) = ρ(g) ρ(h)`. Each `ρ(g)` is then invertible with inverse
`ρ(g⁻¹)`, so `ρ` is a homomorphism `G → GL(K^ι)`. Its *degree* is `card ι`. -/
structure Rep (G : Type u) [Group G] (K : Type w) [CommRing K] (ι : Type v) [FiniteType ι] where
  /-- The matrix of each group element. -/
  toFun : G → Mat ι ι K
  /-- The identity acts as the identity matrix. -/
  map_one : toFun 1 = 1
  /-- Products go to products. -/
  map_mul : ∀ g h, toFun (g * h) = toFun g * toFun h

namespace Rep

variable {G : Type u} [Group G] {K : Type w} [CommRing K] {ι κ : Type v} [FiniteType ι]
  [FiniteType κ]

/-- A representation can be applied to group elements. -/
instance : CoeFun (Rep G K ι) (fun _ => G → Mat ι ι K) := ⟨Rep.toFun⟩

variable (ρ : Rep G K ι)

/-- `ρ(gh) x = ρ(g) (ρ(h) x)`. -/
theorem act_mul (g h : G) (x : Vec ι K) : ρ (g * h) *ᵥ x = ρ g *ᵥ (ρ h *ᵥ x) := by
  show ρ.toFun (g * h) *ᵥ x = _; rw [ρ.map_mul, mulVec_mulVec]

/-- `ρ(1) x = x`. -/
theorem act_one (x : Vec ι K) : ρ 1 *ᵥ x = x := by
  show ρ.toFun 1 *ᵥ x = x; rw [ρ.map_one, one_mulVec]

/-- `ρ(g⁻¹) ρ(g) = 1`. -/
theorem inv_mul (g : G) : ρ g⁻¹ * ρ g = 1 := by
  show ρ.toFun g⁻¹ * ρ.toFun g = 1; rw [← ρ.map_mul, Group.inv_mul_cancel, ρ.map_one]

/-- `ρ(g) ρ(g⁻¹) = 1`. -/
theorem mul_inv (g : G) : ρ g * ρ g⁻¹ = 1 := by
  show ρ.toFun g * ρ.toFun g⁻¹ = 1; rw [← ρ.map_mul, Group.mul_inv_cancel, ρ.map_one]

/-- `ρ(g⁻¹) (ρ(g) x) = x`. -/
theorem act_inv_act (g : G) (x : Vec ι K) : ρ g⁻¹ *ᵥ (ρ g *ᵥ x) = x := by
  rw [mulVec_mulVec, inv_mul, one_mulVec]

/-- `ρ(g) (ρ(g⁻¹) x) = x`. -/
theorem act_act_inv (g : G) (x : Vec ι K) : ρ g *ᵥ (ρ g⁻¹ *ᵥ x) = x := by
  rw [mulVec_mulVec, mul_inv, one_mulVec]

/-- The **degree** (dimension) of a representation. -/
def degree (_ : Rep G K ι) : Nat := card ι

/-- The **trivial representation** on `K^ι`: every group element acts as the identity. -/
noncomputable def trivial (G : Type u) [Group G] (K : Type w) [CommRing K] (ι : Type v)
    [FiniteType ι] : Rep G K ι where
  toFun _ := 1
  map_one := rfl
  map_mul _ _ := (one_mul 1).symm

/-- A sum over the one-element type. -/
theorem isum_unit {A : Type w} [AddAbGroup A] (f : Unit → A) : isum f = f () :=
  AddAbGroup.add_zero (f ())

/-- **One-dimensional representations.** A multiplicative function `χ : G → K` with
`χ(1) = 1` is a representation of degree one (on `K^Unit`). -/
noncomputable def ofHom (χ : G → K) (h1 : χ 1 = 1) (hmul : ∀ g h, χ (g * h) = χ g * χ h) :
    Rep G K Unit where
  toFun g _ _ := χ g
  map_one := ext fun i j => by cases i; cases j; rw [one_apply, kd_self]; exact h1
  map_mul g h := ext fun i j => by
    cases i; cases j
    show χ (g * h) = isum (fun _ : Unit => χ g * χ h)
    rw [isum_unit]; exact hmul g h

end Rep

/-! ## Subspaces and subrepresentations -/

/-- A **subspace** of `K^ι`: a set of vectors containing `0` and closed under addition and
scalar multiplication. -/
structure Subspace (ι : Type v) (K : Type w) [CommRing K] where
  /-- Membership predicate. -/
  carrier : Vec ι K → Prop
  /-- `0` belongs to the subspace. -/
  zero_mem : carrier 0
  /-- Closed under addition. -/
  add_mem : ∀ {x y}, carrier x → carrier y → carrier (x + y)
  /-- Closed under scalar multiplication. -/
  smul_mem : ∀ (c : K) {x}, carrier x → carrier (c • x)

namespace Subspace

variable {K : Type w} [CommRing K] {ι κ : Type v}

/-- Membership in a subspace. -/
instance : Membership (Vec ι K) (Subspace ι K) := ⟨fun W x => W.carrier x⟩

/-- Closed under negation. -/
theorem neg_mem (W : Subspace ι K) {x : Vec ι K} (hx : x ∈ W) : -x ∈ W := by
  have := W.smul_mem (-1) hx
  rwa [VectorSpace.neg_smul, VectorSpace.one_smul] at this

/-- Closed under finite sums. -/
theorem isum_mem {α : Type u} [FiniteType α] (W : Subspace ι K) {f : α → Vec ι K}
    (hf : ∀ a, f a ∈ W) : isum f ∈ W := by
  unfold isum
  have : ∀ l : List α, lsum (l.map f) ∈ W := by
    intro l
    induction l with
    | nil => exact W.zero_mem
    | cons a l ih => exact W.add_mem (hf a) ih
  exact this _

/-- `W` is the **zero subspace**. -/
def IsZero (W : Subspace ι K) : Prop := ∀ x, x ∈ W → x = 0

/-- `W` is the **whole space**. -/
def IsTop (W : Subspace ι K) : Prop := ∀ x, x ∈ W

/-- `W` and `W'` are **complementary**: `W ∩ W' = 0` and `W + W' = K^ι`, i.e. `K^ι = W ⊕ W'`. -/
def IsCompl (W W' : Subspace ι K) : Prop :=
  (∀ x, x ∈ W → x ∈ W' → x = 0) ∧ ∀ x, ∃ w w', w ∈ W ∧ w' ∈ W' ∧ x = w + w'

variable [FiniteType ι]

/-- The **kernel** `{x | T x = 0}` of a matrix `T`. -/
def ker (T : Mat κ ι K) : Subspace ι K where
  carrier x := T *ᵥ x = 0
  zero_mem := mulVec_zero T
  add_mem hx hy := by
    show T *ᵥ (_ + _) = 0
    rw [mulVec_add, hx, hy]; exact AddAbGroup.zero_add 0
  smul_mem c x hx := by
    show T *ᵥ (c • _) = 0
    rw [mulVec_smul, hx]; exact VectorSpace.smul_zero c

/-- The **image** `{T x}` of a matrix `T`. -/
def range (T : Mat κ ι K) : Subspace κ K where
  carrier y := ∃ x, y = T *ᵥ x
  zero_mem := ⟨0, (mulVec_zero T).symm⟩
  add_mem := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, (mulVec_add T x y).symm⟩
  smul_mem c := by
    rintro _ ⟨x, rfl⟩; exact ⟨c • x, (mulVec_smul T c x).symm⟩

end Subspace

open Subspace

variable {G : Type u} [Group G] {K : Type w} [CommRing K] {ι κ μ : Type v} [FiniteType ι]
  [FiniteType κ] [FiniteType μ]

/-- `W` is **`ρ`-invariant**, i.e. a *subrepresentation* of `ρ`: `ρ(g) W ⊆ W` for all `g`. -/
def Invariant (ρ : Rep G K ι) (W : Subspace ι K) : Prop :=
  ∀ g x, x ∈ W → ρ g *ᵥ x ∈ W

/-- **Irreducible representation.** `ρ` is irreducible if its space is non-zero and its only
invariant subspaces are `0` and the whole space. -/
def Irreducible (ρ : Rep G K ι) : Prop :=
  Nonempty ι ∧ ∀ W : Subspace ι K, Invariant ρ W → W.IsZero ∨ W.IsTop

/-! ## `G`-maps -/

/-- **`G`-map (intertwiner).** A matrix `T : K^ι → K^κ` is a `G`-map from `ρ` to `σ` if
`T ρ(g) = σ(g) T` for every `g`. -/
def IsGMap (ρ : Rep G K ι) (σ : Rep G K κ) (T : Mat κ ι K) : Prop :=
  ∀ g, T * ρ g = σ g * T

/-- A `G`-map commutes with the actions: `T (ρ(g) x) = σ(g) (T x)`. -/
theorem IsGMap.act {ρ : Rep G K ι} {σ : Rep G K κ} {T : Mat κ ι K} (hT : IsGMap ρ σ T)
    (g : G) (x : Vec ι K) : T *ᵥ (ρ g *ᵥ x) = σ g *ᵥ (T *ᵥ x) := by
  rw [mulVec_mulVec, mulVec_mulVec, hT g]

/-- A matrix commuting with the actions on all vectors is a `G`-map. -/
theorem IsGMap.of_act {ρ : Rep G K ι} {σ : Rep G K κ} {T : Mat κ ι K}
    (h : ∀ g x, T *ᵥ (ρ g *ᵥ x) = σ g *ᵥ (T *ᵥ x)) : IsGMap ρ σ T := fun g =>
  ext_mulVec fun x => by rw [← mulVec_mulVec, ← mulVec_mulVec, h]

/-- The identity is a `G`-map. -/
theorem IsGMap.id (ρ : Rep G K ι) : IsGMap ρ ρ 1 := fun g => by rw [one_mul, mul_one]

/-- A composite of `G`-maps is a `G`-map. -/
theorem IsGMap.comp {ρ : Rep G K ι} {σ : Rep G K κ} {τ : Rep G K μ} {T : Mat κ ι K}
    {U : Mat μ κ K} (hT : IsGMap ρ σ T) (hU : IsGMap σ τ U) : IsGMap ρ τ (U * T) := fun g => by
  rw [mul_assoc, hT g, ← mul_assoc, hU g, mul_assoc]

/-- The kernel of a `G`-map is a subrepresentation of the source. -/
theorem IsGMap.ker_invariant {ρ : Rep G K ι} {σ : Rep G K κ} {T : Mat κ ι K}
    (hT : IsGMap ρ σ T) : Invariant ρ (ker T) := fun g x hx => by
  show T *ᵥ (ρ g *ᵥ x) = 0
  rw [hT.act, show T *ᵥ x = 0 from hx, mulVec_zero]

/-- The image of a `G`-map is a subrepresentation of the target. -/
theorem IsGMap.range_invariant {ρ : Rep G K ι} {σ : Rep G K κ} {T : Mat κ ι K}
    (hT : IsGMap ρ σ T) : Invariant σ (range T) := by
  rintro g _ ⟨x, rfl⟩; exact ⟨ρ g *ᵥ x, (hT.act g x).symm⟩

/-- **Isomorphic representations.** `ρ ≅ σ` if there is an invertible `G`-map between them:
matrices `T`, `S` with `T` a `G`-map, `S T = 1` and `T S = 1`. -/
def Iso (ρ : Rep G K ι) (σ : Rep G K κ) : Prop :=
  ∃ T : Mat κ ι K, ∃ S : Mat ι κ K, IsGMap ρ σ T ∧ S * T = 1 ∧ T * S = 1

/-- Every representation is isomorphic to itself. -/
theorem Iso.refl (ρ : Rep G K ι) : Iso ρ ρ := ⟨1, 1, IsGMap.id ρ, one_mul 1, one_mul 1⟩

/-- The inverse of an invertible `G`-map is a `G`-map. -/
theorem IsGMap.inverse {ρ : Rep G K ι} {σ : Rep G K κ} {T : Mat κ ι K} {S : Mat ι κ K}
    (hT : IsGMap ρ σ T) (hST : S * T = 1) (hTS : T * S = 1) : IsGMap σ ρ S := fun g => by
  calc S * σ g = S * σ g * (T * S) := by rw [hTS, mul_one]
    _ = S * (σ g * T) * S := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = S * T * ρ g * S := by rw [← hT g, mul_assoc S T]
    _ = ρ g * S := by rw [hST, one_mul]

/-- Isomorphism is symmetric. -/
theorem Iso.symm {ρ : Rep G K ι} {σ : Rep G K κ} (h : Iso ρ σ) : Iso σ ρ := by
  obtain ⟨T, S, hT, hST, hTS⟩ := h
  exact ⟨S, T, hT.inverse hST hTS, hTS, hST⟩

/-! ## Direct sums -/

/-- The block-diagonal matrix `diag(A, B)` on `ι ⊕ κ`. -/
def blockDiag (A : Mat ι ι K) (B : Mat κ κ K) : Mat (ι ⊕ κ) (ι ⊕ κ) K
  | .inl i, .inl j => A i j
  | .inr k, .inr l => B k l
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0

/-- Block-diagonal matrices multiply blockwise. -/
theorem blockDiag_mul (A C : Mat ι ι K) (B D : Mat κ κ K) :
    blockDiag A B * blockDiag C D = blockDiag (A * C) (B * D) := by
  apply ext; intro a b
  rw [mul_apply, isum_sum]
  cases a <;> cases b <;>
    simp only [blockDiag, Ring.zero_mul, Ring.mul_zero, isum_zero, AddAbGroup.add_zero,
      AddAbGroup.zero_add] <;> rfl

/-- The identity is block diagonal. -/
theorem blockDiag_one : blockDiag (1 : Mat ι ι K) (1 : Mat κ κ K) = 1 := by
  apply ext; intro a b
  cases a <;> cases b <;> simp only [blockDiag, one_apply]
  · exact (kd_map Sum.inl (fun _ _ h => Sum.inl.inj h) _ _).symm
  · exact (kd_ne Sum.inl_ne_inr).symm
  · exact (kd_ne Sum.inr_ne_inl).symm
  · exact (kd_map Sum.inr (fun _ _ h => Sum.inr.inj h) _ _).symm

/-- The trace of a block-diagonal matrix is the sum of the traces of the blocks. -/
theorem trace_blockDiag (A : Mat ι ι K) (B : Mat κ κ K) :
    trace (blockDiag A B) = trace A + trace B := isum_sum _

/-- **Direct sum** `ρ ⊕ σ`: the representation on `K^(ι ⊕ κ)` acting by `diag(ρ(g), σ(g))`. -/
noncomputable def Rep.dsum (ρ : Rep G K ι) (σ : Rep G K κ) : Rep G K (ι ⊕ κ) where
  toFun g := blockDiag (ρ g) (σ g)
  map_one := by
    show blockDiag (ρ.toFun 1) (σ.toFun 1) = 1
    rw [ρ.map_one, σ.map_one, blockDiag_one]
  map_mul g h := by
    show blockDiag (ρ.toFun _) (σ.toFun _) = _
    rw [ρ.map_mul, σ.map_mul, blockDiag_mul]

/-- The first summand `K^ι ⊆ K^(ι ⊕ κ)`: vectors vanishing on `κ`. -/
def leftSummand (ι κ : Type v) (K : Type w) [CommRing K] : Subspace (ι ⊕ κ) K where
  carrier x := ∀ k, x (.inr k) = 0
  zero_mem _ := rfl
  add_mem hx hy k := by
    show _ + _ = (0 : K); rw [hx k, hy k, Ring.add_zero]
  smul_mem c x hx k := by show c * _ = (0 : K); rw [hx k, Ring.mul_zero]

/-- The second summand `K^κ ⊆ K^(ι ⊕ κ)`: vectors vanishing on `ι`. -/
def rightSummand (ι κ : Type v) (K : Type w) [CommRing K] : Subspace (ι ⊕ κ) K where
  carrier x := ∀ i, x (.inl i) = 0
  zero_mem _ := rfl
  add_mem hx hy i := by
    show _ + _ = (0 : K); rw [hx i, hy i, Ring.add_zero]
  smul_mem c x hx i := by show c * _ = (0 : K); rw [hx i, Ring.mul_zero]

/-- The two summands of `K^(ι ⊕ κ)` are complementary. -/
theorem summands_isCompl : IsCompl (leftSummand ι κ K) (rightSummand ι κ K) := by
  refine ⟨fun x h1 h2 => Vec.ext fun a => ?_, fun x => ?_⟩
  · cases a with
    | inl i => exact h2 i
    | inr k => exact h1 k
  · refine ⟨fun a => Sum.elim (fun i => x (.inl i)) (fun _ => 0) a,
      fun a => Sum.elim (fun _ => 0) (fun k => x (.inr k)) a, fun _ => rfl, fun _ => rfl,
      Vec.ext fun a => ?_⟩
    cases a with
    | inl i => exact (Ring.add_zero _).symm
    | inr k => exact (Ring.zero_add _).symm

/-- `(diag(A, B) x)` on `ι` only sees `x` on `ι`, and on `κ` only `x` on `κ`. -/
theorem blockDiag_mulVec_inl (A : Mat ι ι K) (B : Mat κ κ K) (x : Vec (ι ⊕ κ) K) (i : ι) :
    (blockDiag A B *ᵥ x) (.inl i) = isum (fun j => A i j * x (.inl j)) := by
  rw [mulVec_apply, isum_sum]
  have h0 : isum (fun l : κ => blockDiag A B (.inl i) (.inr l) * x (.inr l)) = 0 :=
    isum_eq_zero fun l => Ring.zero_mul _
  rw [h0, AddAbGroup.add_zero]; rfl

/-- See `blockDiag_mulVec_inl`. -/
theorem blockDiag_mulVec_inr (A : Mat ι ι K) (B : Mat κ κ K) (x : Vec (ι ⊕ κ) K) (k : κ) :
    (blockDiag A B *ᵥ x) (.inr k) = isum (fun l => B k l * x (.inr l)) := by
  rw [mulVec_apply, isum_sum]
  have h0 : isum (fun i : ι => blockDiag A B (.inr k) (.inl i) * x (.inl i)) = 0 :=
    isum_eq_zero fun i => Ring.zero_mul _
  rw [h0, AddAbGroup.zero_add]; rfl

/-- **The summands of a direct sum are subrepresentations.** Both `K^ι` and `K^κ` are
invariant under `ρ ⊕ σ`, and they are complementary. -/
theorem dsum_summands_invariant (ρ : Rep G K ι) (σ : Rep G K κ) :
    Invariant (ρ.dsum σ) (leftSummand ι κ K) ∧ Invariant (ρ.dsum σ) (rightSummand ι κ K) := by
  refine ⟨fun g x hx k => ?_, fun g x hx i => ?_⟩
  · show (blockDiag (ρ g) (σ g) *ᵥ x) (.inr k) = 0
    rw [blockDiag_mulVec_inr, isum_eq_zero fun l => by rw [hx l, Ring.mul_zero]]
  · show (blockDiag (ρ g) (σ g) *ᵥ x) (.inl i) = 0
    rw [blockDiag_mulVec_inl, isum_eq_zero fun j => by rw [hx j, Ring.mul_zero]]

/-! ## Characters -/

/-- **Character** of a representation (Frobenius 1896): `χ_ρ(g) = tr ρ(g)`. -/
def character (ρ : Rep G K ι) (g : G) : K := trace (ρ g)

/-- A **class function**: a function constant on conjugacy classes, `f(h g h⁻¹) = f(g)`. -/
def IsClassFunction {α : Type w} (f : G → α) : Prop := ∀ g h, f (h * g * h⁻¹) = f g

/-- The value of a character at `1` is the degree: `χ_ρ(1) = card ι` (in `K`). -/
theorem character_one (ρ : Rep G K ι) : character ρ 1 = ncast (card ι) := by
  show trace (ρ.toFun 1) = _; rw [ρ.map_one, trace_one]

/-- **Characters are class functions.** -/
theorem character_isClassFunction (ρ : Rep G K ι) : IsClassFunction (character ρ) := by
  intro g h
  show trace (ρ.toFun (h * g * h⁻¹)) = trace (ρ.toFun g)
  rw [ρ.map_mul, ρ.map_mul]
  exact trace_conj _ _ _ (ρ.inv_mul h)

/-- **The character of a direct sum is the sum of the characters.** -/
theorem character_dsum (ρ : Rep G K ι) (σ : Rep G K κ) (g : G) :
    character (ρ.dsum σ) g = character ρ g + character σ g :=
  trace_blockDiag _ _

/-- **Isomorphic representations have the same character.** -/
theorem character_eq_of_iso {ρ : Rep G K ι} {σ : Rep G K κ} (h : Iso ρ σ) :
    character ρ = character σ := by
  obtain ⟨T, S, hT, hST, hTS⟩ := h
  funext g
  show trace (ρ g) = trace (σ g)
  rw [← trace_conj T (ρ g) S hST, hT g, mul_assoc, hTS, mul_one]

end Foundations.Langlands
