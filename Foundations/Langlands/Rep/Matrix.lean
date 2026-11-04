import Foundations.Algebra.ComplexField
import Foundations.Algebra.GaloisCorrespondence

/-!
# Vectors, matrices and traces

Part XV, *Toward Langlands*, begins with the most basic layer of the programme: the
representation theory of finite groups. When Frobenius created the theory in 1896, answering
a question of Dedekind about the factorisation of the *group determinant*, his objects were
matrices: a representation of a group `G` assigns to every element `g` an invertible matrix
`ρ(g)`, multiplicatively. His great invention was the **character** `χ(g) = tr ρ(g)`, the trace
of the matrix, which forgets almost everything about `ρ` and yet, as it turned out, determines
it completely.

This file sets up the concrete linear algebra that the rest of the chapter needs, over an
arbitrary commutative ring `K` (a field where it matters):

* `Vec ι K`, the column vectors `ι → K` indexed by a finite type `ι`, with their pointwise
  operations (an `AddAbGroup` and a `VectorSpace` in the sense of `Algebra/VectorSpace`);
* `Mat κ ι K`, the `κ × ι` matrices, with matrix product, the product `A *ᵥ x` of a matrix
  and a vector, the identity matrix, sums and scalar multiples;
* the Kronecker delta `kd i j` and the standard basis vectors `basisVec j`;
* the **trace** `tr A = Σᵢ Aᵢᵢ`, with the cyclic identity `tr (A B) = tr (B A)` (valid also
  for rectangular `A` and `B`), the identity on which character theory rests.

Matrices are indexed by arbitrary finite types rather than by `Fin n`; this makes direct sums
(indexed by `ι ⊕ κ`) painless. The degree of a representation is the size `card ι`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType

set_option linter.unusedSectionVars false

universe u v w

/-! ## Finite sums in a commutative ring -/

section Sums

variable {K : Type u} [CommRing K]

/-- The **Kronecker delta** `kd i j`: `1` if `i = j` and `0` otherwise. -/
noncomputable def kd {ι : Type v} (i j : ι) : K := by
  classical exact if i = j then 1 else 0

/-- `kd i i = 1`. -/
theorem kd_self {ι : Type v} (i : ι) : (kd i i : K) = 1 := by
  unfold kd; simp

/-- `kd i j = 0` for `i ≠ j`. -/
theorem kd_ne {ι : Type v} {i j : ι} (h : i ≠ j) : (kd i j : K) = 0 := by
  unfold kd; simp [h]

/-- The Kronecker delta is symmetric. -/
theorem kd_comm {ι : Type v} (i j : ι) : (kd i j : K) = kd j i := by
  by_cases h : i = j
  · subst h; rfl
  · rw [kd_ne h, kd_ne (Ne.symm h)]

/-- The Kronecker delta is unchanged by an injective map. -/
theorem kd_map {ι : Type v} {κ : Type w} (e : ι → κ) (inj : ∀ a b, e a = e b → a = b) (i j : ι) :
    (kd (e i) (e j) : K) = kd i j := by
  by_cases h : i = j
  · subst h; rw [kd_self, kd_self]
  · rw [kd_ne h, kd_ne (fun h' => h (inj _ _ h'))]

variable {ι : Type v} [FiniteType ι]

/-- **Sifting property** of the Kronecker delta: `Σₐ δₐⱼ f(a) = f(j)`. -/
theorem isum_kd_mul (j : ι) (f : ι → K) : isum (fun a => kd a j * f a) = f j := by
  rw [isum_single' _ j (fun a h => by rw [kd_ne h, Ring.zero_mul]), kd_self, Ring.one_mul]

/-- **Sifting property**, other orientation: `Σₐ δⱼₐ f(a) = f(j)`. -/
theorem isum_kd_mul' (j : ι) (f : ι → K) : isum (fun a => kd j a * f a) = f j := by
  rw [← isum_kd_mul j f]; congr 1; funext a; rw [kd_comm]

/-- **Sifting property** with the delta on the right. -/
theorem isum_mul_kd (j : ι) (f : ι → K) : isum (fun a => f a * kd a j) = f j := by
  rw [← isum_kd_mul j f]; congr 1; funext a; exact CommRing.mul_comm _ _

/-- A sum of a constant: `Σₐ c = |ι| · c`. -/
theorem isum_const (c : K) : isum (fun _ : ι => c) = ncast (card ι) * c := by
  unfold isum card
  induction (elems : List ι) with
  | nil => exact (Ring.zero_mul c).symm
  | cons a l ih =>
    show c + lsum (l.map _) = ncast (l.length + 1) * c
    rw [ih, ncast_succ, Ring.right_distrib, Ring.one_mul, Ring.add_comm]

/-- Sums respect pointwise equality. -/
theorem isum_congr {A : Type w} [AddAbGroup A] {f g : ι → A} (h : ∀ a, f a = g a) :
    isum f = isum g := by
  rw [show f = g from funext h]

end Sums

/-! ## Sums over a disjoint union -/

/-- The disjoint union of two finite types is finite. -/
instance FiniteType.instSum {ι κ : Type v} [FiniteType ι] [FiniteType κ] :
    FiniteType (ι ⊕ κ) where
  elems := (elems : List ι).map Sum.inl ++ (elems : List κ).map Sum.inr
  nodup := by
    rw [List.nodup_append]
    refine ⟨nodup_map_of_injective (fun a b h => Sum.inl.inj h) nodup,
      nodup_map_of_injective (fun a b h => Sum.inr.inj h) nodup, ?_⟩
    intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    exact Sum.inl_ne_inr
  complete := by
    intro x
    cases x with
    | inl a => exact List.mem_append_left _ (List.mem_map_of_mem (complete a))
    | inr b => exact List.mem_append_right _ (List.mem_map_of_mem (complete b))

/-- A sum over `ι ⊕ κ` splits into a sum over `ι` and a sum over `κ`. -/
theorem isum_sum {A : Type w} [AddAbGroup A] {ι κ : Type v} [FiniteType ι] [FiniteType κ]
    (f : ι ⊕ κ → A) : isum f = isum (fun i => f (Sum.inl i)) + isum (fun k => f (Sum.inr k)) := by
  show lsum (((elems : List ι).map Sum.inl ++ (elems : List κ).map Sum.inr).map f) = _
  rw [List.map_append, lsum_append, List.map_map, List.map_map]; rfl

/-- The size of a disjoint union is the sum of the sizes. -/
theorem card_sum {ι κ : Type v} [FiniteType ι] [FiniteType κ] :
    card (ι ⊕ κ) = card ι + card κ := by
  show ((elems : List ι).map Sum.inl ++ (elems : List κ).map Sum.inr).length = _
  rw [List.length_append, List.length_map, List.length_map]; rfl

/-! ## Column vectors -/

/-- **Column vectors** with entries in `K`, indexed by `ι`: the space `K^ι`. -/
def Vec (ι : Type v) (K : Type u) : Type (max v u) := ι → K

namespace Vec

variable {ι : Type v} {K : Type u} [CommRing K]

/-- Pointwise addition of vectors. -/
instance : Add (Vec ι K) := ⟨fun x y i => x i + y i⟩
/-- The zero vector. -/
instance : Zero (Vec ι K) := ⟨fun _ => 0⟩
/-- Pointwise negation. -/
instance : Neg (Vec ι K) := ⟨fun x i => -x i⟩
/-- Scalar multiplication. -/
instance : SMul K (Vec ι K) := ⟨fun c x i => c * x i⟩

/-- Entries of a sum. -/
theorem add_apply (x y : Vec ι K) (i : ι) : (x + y) i = x i + y i := rfl
/-- Entries of the zero vector. -/
theorem zero_apply (i : ι) : (0 : Vec ι K) i = 0 := rfl
/-- Entries of a negative. -/
theorem neg_apply (x : Vec ι K) (i : ι) : (-x) i = -x i := rfl
/-- Entries of a scalar multiple. -/
theorem smul_apply (c : K) (x : Vec ι K) (i : ι) : (c • x) i = c * x i := rfl

/-- Vectors with the same entries are equal. -/
theorem ext {x y : Vec ι K} (h : ∀ i, x i = y i) : x = y := funext h

/-- Vectors form an additive abelian group. -/
instance : AddAbGroup (Vec ι K) where
  add_assoc x y z := ext fun i => Ring.add_assoc (x i) (y i) (z i)
  add_comm x y := ext fun i => Ring.add_comm (x i) (y i)
  zero_add x := ext fun i => Ring.zero_add (x i)
  neg_add_cancel x := ext fun i => Ring.neg_add_cancel (x i)

/-- **`K^ι` is a vector space over `K`.** -/
instance : VectorSpace K (Vec ι K) where
  smul_add c x y := ext fun i => Ring.left_distrib c (x i) (y i)
  add_smul c d x := ext fun i => Ring.right_distrib c d (x i)
  mul_smul c d x := ext fun i => Ring.mul_assoc c d (x i)
  one_smul x := ext fun i => Ring.one_mul (x i)

/-- Entries of a finite sum of vectors are the sums of the entries. -/
theorem isum_apply {α : Type w} [FiniteType α] (f : α → Vec ι K) (i : ι) :
    (isum f) i = isum (fun a => f a i) := by
  unfold isum
  induction (elems : List α) with
  | nil => rfl
  | cons a l ih => show f a i + (lsum (l.map f)) i = f a i + lsum _; rw [ih]

/-- The **standard basis vector** `eⱼ`, with entries `δᵢⱼ`. -/
noncomputable def basisVec (j : ι) : Vec ι K := fun i => kd i j

/-- **Every vector is a combination of standard basis vectors**: `x = Σⱼ xⱼ eⱼ`. -/
theorem eq_isum_basisVec [FiniteType ι] (x : Vec ι K) :
    x = isum (fun j => x j • basisVec j) := by
  apply ext; intro i
  rw [isum_apply]
  refine (isum_mul_kd i (fun j => x j)).symm.trans (isum_congr fun j => ?_)
  show x j * kd j i = x j * kd i j
  rw [kd_comm]

end Vec

/-! ## Matrices -/

/-- **Matrices** `κ × ι` with entries in `K` (rows indexed by `κ`, columns by `ι`). -/
def Mat (κ : Type v) (ι : Type w) (K : Type u) : Type (max v w u) := κ → ι → K

namespace Mat

variable {K : Type u} [CommRing K] {ι κ μ ν : Type v}

/-- Matrices with the same entries are equal. -/
theorem ext {A B : Mat κ ι K} (h : ∀ k i, A k i = B k i) : A = B :=
  funext fun k => funext fun i => h k i

/-- **Matrix product** `(A B)ₖₘ = Σᵢ Aₖᵢ Bᵢₘ`. -/
def mul [FiniteType ι] (A : Mat κ ι K) (B : Mat ι μ K) : Mat κ μ K :=
  fun k m => isum (fun i => A k i * B i m)

/-- Matrix product written `A * B`. -/
instance [FiniteType ι] : HMul (Mat κ ι K) (Mat ι μ K) (Mat κ μ K) := ⟨mul⟩

/-- Entries of a matrix product. -/
theorem mul_apply [FiniteType ι] (A : Mat κ ι K) (B : Mat ι μ K) (k : κ) (m : μ) :
    (A * B) k m = isum (fun i => A k i * B i m) := rfl

/-- **Matrix times vector**: `(A x)ₖ = Σᵢ Aₖᵢ xᵢ`. -/
def mulVec [FiniteType ι] (A : Mat κ ι K) (x : Vec ι K) : Vec κ K :=
  fun k => isum (fun i => A k i * x i)

@[inherit_doc] scoped infixr:73 " *ᵥ " => Mat.mulVec

/-- The **identity matrix** `(δᵢⱼ)`. -/
noncomputable instance : One (Mat ι ι K) := ⟨fun i j => kd i j⟩

/-- Entries of the identity matrix. -/
theorem one_apply (i j : ι) : (1 : Mat ι ι K) i j = kd i j := rfl

/-- Entrywise sum of matrices. -/
instance : Add (Mat κ ι K) := ⟨fun A B k i => A k i + B k i⟩
/-- The zero matrix. -/
instance : Zero (Mat κ ι K) := ⟨fun _ _ => 0⟩
/-- Entrywise negation. -/
instance : Neg (Mat κ ι K) := ⟨fun A k i => -A k i⟩
/-- Scalar multiple of a matrix. -/
instance : SMul K (Mat κ ι K) := ⟨fun c A k i => c * A k i⟩

/-- Entries of a sum of matrices. -/
theorem add_apply (A B : Mat κ ι K) (k : κ) (i : ι) : (A + B) k i = A k i + B k i := rfl
/-- Entries of the zero matrix. -/
theorem zero_apply (k : κ) (i : ι) : (0 : Mat κ ι K) k i = 0 := rfl
/-- Entries of a negated matrix. -/
theorem neg_apply (A : Mat κ ι K) (k : κ) (i : ι) : (-A) k i = -A k i := rfl
/-- Entries of a scalar multiple of a matrix. -/
theorem smul_apply (c : K) (A : Mat κ ι K) (k : κ) (i : ι) : (c • A) k i = c * A k i := rfl

variable [FiniteType ι]

/-- **Matrix multiplication is associative.** -/
theorem mul_assoc [FiniteType μ] (A : Mat κ ι K) (B : Mat ι μ K) (C : Mat μ ν K) :
    A * B * C = A * (B * C) := by
  apply ext; intro k m
  show isum (fun b => isum (fun a => A k a * B a b) * C b m) =
    isum (fun a => A k a * isum (fun b => B a b * C b m))
  simp only [isum_mul_right, isum_mul_left]
  rw [isum_comm]
  exact isum_congr fun a => isum_congr fun b => Ring.mul_assoc _ _ _

/-- `1 · A = A`. -/
theorem one_mul [FiniteType κ] (A : Mat κ ι K) : (1 : Mat κ κ K) * A = A :=
  ext fun k i => isum_kd_mul' k (fun a => A a i)

/-- `A · 1 = A`. -/
theorem mul_one (A : Mat κ ι K) : A * (1 : Mat ι ι K) = A :=
  ext fun k i => isum_mul_kd i (fun a => A k a)

/-- `(A x)ₖ = Σᵢ Aₖᵢ xᵢ`. -/
theorem mulVec_apply (A : Mat κ ι K) (x : Vec ι K) (k : κ) :
    (A *ᵥ x) k = isum (fun i => A k i * x i) := rfl

/-- `A (B x) = (A B) x`. -/
theorem mulVec_mulVec [FiniteType μ] (A : Mat κ ι K) (B : Mat ι μ K) (x : Vec μ K) :
    A *ᵥ (B *ᵥ x) = (A * B) *ᵥ x := by
  apply Vec.ext; intro k
  show isum (fun a => A k a * isum (fun b => B a b * x b)) =
    isum (fun b => isum (fun a => A k a * B a b) * x b)
  simp only [isum_mul_right, isum_mul_left]
  rw [isum_comm]
  exact isum_congr fun b => isum_congr fun a => (Ring.mul_assoc _ _ _).symm

/-- `1 x = x`. -/
theorem one_mulVec [FiniteType κ] (x : Vec κ K) : (1 : Mat κ κ K) *ᵥ x = x :=
  Vec.ext fun k => isum_kd_mul' k x

/-- A matrix maps sums to sums. -/
theorem mulVec_add (A : Mat κ ι K) (x y : Vec ι K) : A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y := by
  apply Vec.ext; intro k
  show isum (fun i => A k i * (x i + y i)) = isum (fun i => A k i * x i) + isum (fun i => A k i * y i)
  rw [← isum_add]; exact isum_congr fun i => Ring.left_distrib _ _ _

/-- A matrix commutes with scalars. -/
theorem mulVec_smul (A : Mat κ ι K) (c : K) (x : Vec ι K) : A *ᵥ (c • x) = c • (A *ᵥ x) := by
  apply Vec.ext; intro k
  show isum (fun i => A k i * (c * x i)) = c * isum (fun i => A k i * x i)
  rw [isum_mul_left]; exact isum_congr fun i => by grind

/-- A matrix maps `0` to `0`. -/
theorem mulVec_zero (A : Mat κ ι K) : A *ᵥ (0 : Vec ι K) = 0 := by
  have := mulVec_smul A 0 0
  rw [VectorSpace.zero_smul, VectorSpace.zero_smul] at this; exact this

/-- A matrix maps negatives to negatives. -/
theorem mulVec_neg (A : Mat κ ι K) (x : Vec ι K) : A *ᵥ (-x) = -(A *ᵥ x) := by
  apply AddAbGroup.eq_neg_of_add_eq_zero
  rw [← mulVec_add, AddAbGroup.add_neg_cancel, mulVec_zero]

/-- A matrix maps finite sums to finite sums. -/
theorem mulVec_isum {α : Type w} [FiniteType α] (A : Mat κ ι K) (f : α → Vec ι K) :
    A *ᵥ isum f = isum (fun a => A *ᵥ f a) := by
  apply Vec.ext; intro k
  rw [Vec.isum_apply, mulVec_apply]
  simp only [Vec.isum_apply, isum_mul_left, mulVec_apply]
  exact isum_comm _

/-- `(A + B) x = A x + B x`. -/
theorem add_mulVec (A B : Mat κ ι K) (x : Vec ι K) : (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x := by
  apply Vec.ext; intro k
  show isum (fun i => (A k i + B k i) * x i) = isum (fun i => A k i * x i) + isum (fun i => B k i * x i)
  rw [← isum_add]; exact isum_congr fun i => Ring.right_distrib _ _ _

/-- `(c A) x = c (A x)`. -/
theorem smul_mulVec (c : K) (A : Mat κ ι K) (x : Vec ι K) : (c • A) *ᵥ x = c • (A *ᵥ x) := by
  apply Vec.ext; intro k
  show isum (fun i => c * A k i * x i) = c * isum (fun i => A k i * x i)
  rw [isum_mul_left]; exact isum_congr fun i => Ring.mul_assoc _ _ _

/-- `(-A) x = -(A x)`. -/
theorem neg_mulVec (A : Mat κ ι K) (x : Vec ι K) : (-A) *ᵥ x = -(A *ᵥ x) := by
  apply Vec.ext; intro k
  show isum (fun i => -A k i * x i) = -isum (fun i => A k i * x i)
  rw [← isum_neg]; exact isum_congr fun i => Ring.neg_mul _ _

/-- `A eⱼ` is the `j`-th column of `A`. -/
theorem mulVec_basisVec (A : Mat κ ι K) (j : ι) (k : κ) : (A *ᵥ Vec.basisVec j) k = A k j :=
  isum_mul_kd j (fun i => A k i)

/-- **Matrices are determined by their action on vectors.** -/
theorem ext_mulVec {A B : Mat κ ι K} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B :=
  ext fun k j => by rw [← mulVec_basisVec A j k, ← mulVec_basisVec B j k, h]

/-- A matrix killing every vector is the zero matrix. -/
theorem eq_zero_of_mulVec {A : Mat κ ι K} (h : ∀ x, A *ᵥ x = 0) : A = 0 :=
  ext_mulVec fun x => by
    rw [h x]; apply Vec.ext; intro k
    show 0 = isum (fun i => (0 : K) * x i)
    exact (isum_eq_zero fun i => Ring.zero_mul _).symm

/-! ## The trace -/

/-- The **trace** of a square matrix: the sum of its diagonal entries. -/
def trace (A : Mat ι ι K) : K := isum (fun i => A i i)

/-- **The trace is cyclic**: `tr (A B) = tr (B A)`, for `A : κ × ι` and `B : ι × κ`. -/
theorem trace_mul_comm [FiniteType κ] (A : Mat κ ι K) (B : Mat ι κ K) : trace (A * B) = trace (B * A) := by
  show isum (fun k => isum (fun i => A k i * B i k)) = isum (fun i => isum (fun k => B i k * A k i))
  rw [isum_comm]
  exact isum_congr fun i => isum_congr fun k => CommRing.mul_comm _ _

/-- **Trace of a conjugate**: if `S T = 1` then `tr (T A S) = tr A`. -/
theorem trace_conj [FiniteType κ] (T : Mat κ ι K) (A : Mat ι ι K) (S : Mat ι κ K) (h : S * T = 1) :
    trace (T * A * S) = trace A := by
  rw [trace_mul_comm, ← mul_assoc, h, one_mul]

/-- The trace of the identity is the size of the index type. -/
theorem trace_one : trace (1 : Mat ι ι K) = ncast (card ι) := by
  show isum (fun i => (kd i i : K)) = _
  rw [isum_congr (fun i => kd_self (K := K) i), isum_const, Ring.mul_one]

/-- The trace of a scalar multiple. -/
theorem trace_smul (c : K) (A : Mat ι ι K) : trace (c • A) = c * trace A := by
  show isum (fun i => c * A i i) = c * isum (fun i => A i i)
  rw [isum_mul_left]

end Mat

end Foundations.Langlands
