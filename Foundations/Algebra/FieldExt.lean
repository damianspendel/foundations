import Foundations.Algebra.VectorSpace

/-!
# Field extensions and the tower law

Dedekind's great idea (1871, in his supplements to Dirichlet's lectures) was to regard a
field `L` containing a smaller field `K` as a *vector space* over `K`. The dimension of this
space is the **degree** `[L : K]`. Thus `ℚ(√2) = {a + b√2}` has degree `2` over `ℚ`, and
`ℚ(∛2) = {a + b∛2 + c∛4}` has degree `3`.

Degrees multiply along towers: if `K ⊆ L ⊆ M` then `[M : K] = [M : L] · [L : K]`. The proof
is the most natural one imaginable: if `e₁, …, eₐ` is a basis of `L` over `K` and
`f₁, …, f_b` one of `M` over `L`, then the `a · b` products `eᵢ fⱼ` form a basis of `M` over
`K`. This **tower law** is the arithmetic heart of Wantzel's impossibility proofs.

To keep all fields comparable we work, as the classical theory did, inside one ambient field
`Ω` (think of `ℝ` or `ℂ`): a *subfield* is a subset of `Ω` closed under the field
operations, and a `K`-*subspace* is a subset closed under addition and under multiplication
by elements of `K`. Every subfield containing `K` is a `K`-subspace, hence a `K`-vector space
in the sense of the previous file.
-/

namespace Foundations.Algebra

open Ring FiniteType VectorSpace

universe u v

variable {Ω : Type u} [CommRing Ω]

/-- **Subfield** of `Ω`: a subset containing `0` and `1`, closed under addition, negation,
multiplication, and inverses of non-zero elements. -/
structure Subfield (Ω : Type u) [CommRing Ω] where
  /-- The elements of the subfield. -/
  carrier : Ω → Prop
  /-- Contains `0`. -/
  zero_mem : carrier 0
  /-- Contains `1`. -/
  one_mem : carrier 1
  /-- Closed under addition. -/
  add_mem : ∀ {a b}, carrier a → carrier b → carrier (a + b)
  /-- Closed under negation. -/
  neg_mem : ∀ {a}, carrier a → carrier (-a)
  /-- Closed under multiplication. -/
  mul_mem : ∀ {a b}, carrier a → carrier b → carrier (a * b)
  /-- Contains inverses of its non-zero elements. -/
  inv_mem : ∀ {a}, carrier a → a ≠ 0 → ∃ b, carrier b ∧ a * b = 1

namespace Subfield

/-- Membership in a subfield. -/
instance : Membership Ω (Subfield Ω) := ⟨fun K x => K.carrier x⟩

/-- Inclusion of subfields. -/
def le (K L : Subfield Ω) : Prop := ∀ x, x ∈ K → x ∈ L

/-- Inclusion is reflexive. -/
theorem le_refl (K : Subfield Ω) : K.le K := fun _ h => h

/-- Inclusion is transitive. -/
theorem le_trans {K L M : Subfield Ω} (h1 : K.le L) (h2 : L.le M) : K.le M :=
  fun x h => h2 x (h1 x h)

/-- A subfield, viewed as a subring. -/
def toSubring (K : Subfield Ω) : Subring Ω :=
  ⟨K.carrier, K.zero_mem, K.one_mem, K.add_mem, K.neg_mem, K.mul_mem⟩

/-- A subfield viewed as a type. -/
instance : CoeSort (Subfield Ω) (Type u) := ⟨fun K => {x : Ω // x ∈ K}⟩

/-- A subfield is a commutative ring. -/
instance (K : Subfield Ω) : CommRing K := Subring.toCommRing K.toSubring

/-- Values of sums of elements of a subfield. -/
@[simp] theorem coe_add (K : Subfield Ω) (a b : K) : (a + b).1 = a.1 + b.1 := rfl

/-- Values of products of elements of a subfield. -/
@[simp] theorem coe_mul (K : Subfield Ω) (a b : K) : (a * b).1 = a.1 * b.1 := rfl

/-- **A subfield of a field is a field.** -/
theorem isField (hΩ : IsField Ω) (K : Subfield Ω) : IsField K := by
  refine ⟨fun h => hΩ.1 (congrArg Subtype.val h), fun a ha => ?_⟩
  have ha' : a.1 ≠ 0 := fun h => ha (Subtype.ext h)
  obtain ⟨b, hb, hab⟩ := K.inv_mem a.2 ha'
  exact ⟨⟨b, hb⟩, Subtype.ext hab⟩

end Subfield

/-- A **`K`-subspace** of `Ω`: a subset containing `0`, closed under addition and negation,
and under multiplication by elements of the subfield `K`. -/
structure KSubspace (K : Subfield Ω) where
  /-- The elements. -/
  carrier : Ω → Prop
  /-- Contains `0`. -/
  zero_mem : carrier 0
  /-- Closed under addition. -/
  add_mem : ∀ {a b}, carrier a → carrier b → carrier (a + b)
  /-- Closed under negation. -/
  neg_mem : ∀ {a}, carrier a → carrier (-a)
  /-- Closed under scaling by `K`. -/
  smul_mem : ∀ {k x}, k ∈ K → carrier x → carrier (k * x)

namespace KSubspace

variable {K : Subfield Ω}

/-- A subspace viewed as a type. -/
instance : CoeSort (KSubspace K) (Type u) := ⟨fun S => {x : Ω // S.carrier x}⟩

/-- A subspace is an additive abelian group. -/
instance (S : KSubspace K) : AddAbGroup S where
  add a b := ⟨a.1 + b.1, S.add_mem a.2 b.2⟩
  zero := ⟨0, S.zero_mem⟩
  neg a := ⟨-a.1, S.neg_mem a.2⟩
  add_assoc a b c := Subtype.ext (Ring.add_assoc a.1 b.1 c.1)
  add_comm a b := Subtype.ext (Ring.add_comm a.1 b.1)
  zero_add a := Subtype.ext (Ring.zero_add a.1)
  neg_add_cancel a := Subtype.ext (Ring.neg_add_cancel a.1)

/-- **A `K`-subspace is a `K`-vector space**, scaling by multiplication in `Ω`. -/
instance (S : KSubspace K) : VectorSpace K S where
  smul k x := ⟨k.1 * x.1, S.smul_mem k.2 x.2⟩
  smul_add c x y := Subtype.ext (Ring.left_distrib c.1 x.1 y.1)
  add_smul c d x := Subtype.ext (Ring.right_distrib c.1 d.1 x.1)
  mul_smul c d x := Subtype.ext (Ring.mul_assoc c.1 d.1 x.1)
  one_smul x := Subtype.ext (Ring.one_mul x.1)

/-- Values of scalar multiples. -/
@[simp] theorem coe_smul (S : KSubspace K) (k : K) (x : S) : (k • x).1 = k.1 * x.1 := rfl

/-- Values of sums. -/
@[simp] theorem coe_add (S : KSubspace K) (x y : S) : (x + y).1 = x.1 + y.1 := rfl

/-- Values of finite sums: the value of `∑ xᵢ` is `∑ (value of xᵢ)`. -/
theorem coe_isum (S : KSubspace K) {ι : Type v} [FiniteType ι] (f : ι → S) :
    (isum f).1 = isum (fun i => (f i).1) := by
  unfold isum
  induction (elems : List ι) with
  | nil => rfl
  | cons a l ih =>
    show (f a).1 + (lsum (l.map f)).1 = (f a).1 + lsum (l.map fun i => (f i).1)
    rw [ih]

end KSubspace

namespace Subfield

/-- A subfield `M` containing `K`, viewed as a `K`-subspace (hence a `K`-vector space). -/
def over (M K : Subfield Ω) (h : K.le M) : KSubspace K where
  carrier := M.carrier
  zero_mem := M.zero_mem
  add_mem := M.add_mem
  neg_mem := M.neg_mem
  smul_mem hk hx := M.mul_mem (h _ hk) hx

/-- The **degree** `[M : K]`: the dimension of `M` as a `K`-vector space. -/
noncomputable def deg (K M : Subfield Ω) (h : K.le M) : Nat := dim K (M.over K h)

/-- `M` is a **finite extension** of `K`. -/
def FiniteExt (K M : Subfield Ω) (h : K.le M) : Prop := FinDim K (M.over K h)

end Subfield

open Subfield KSubspace

/-- Multiplying a sum on the right (in a commutative ring). -/
theorem isum_mul_right {R : Type u} [CommRing R] {ι : Type v} [FiniteType ι] (f : ι → R) (c : R) :
    isum f * c = isum (fun i => f i * c) := by
  rw [CommRing.mul_comm, isum_mul_left]; congr 1; funext i; exact CommRing.mul_comm _ _

/-- A finite extension of `K` is also finite over any intermediate field `L`. -/
theorem finiteExt_of_tower {K L M : Subfield Ω} (hKL : K.le L) (hLM : L.le M)
    (hfin : FiniteExt K M (le_trans hKL hLM)) : FiniteExt L M hLM := by
  obtain ⟨n, w, hw⟩ := hfin
  refine ⟨n, fun i => ⟨(w i).1, (w i).2⟩, fun x => ?_⟩
  obtain ⟨c, hc⟩ := hw ⟨x.1, x.2⟩
  refine ⟨fun i => ⟨(c i).1, hKL _ (c i).2⟩, Subtype.ext ?_⟩
  have := congrArg Subtype.val hc
  rw [coe_isum] at this ⊢
  exact this

/-- **The tower law.** For subfields `K ⊆ L ⊆ M` of a field `Ω` with `L` finite over `K` and
`M` finite over `L`, the extension `M / K` is finite and `[M : K] = [M : L] · [L : K]`. -/
theorem tower_law (hΩ : IsField Ω) {K L M : Subfield Ω} (hKL : K.le L) (hLM : L.le M)
    (h1 : FiniteExt K L hKL) (h2 : FiniteExt L M hLM) :
    FiniteExt K M (le_trans hKL hLM) ∧
      deg K M (le_trans hKL hLM) = deg L M hLM * deg K L hKL := by
  have hFK := K.isField hΩ
  have hFL := L.isField hΩ
  obtain ⟨e, he⟩ := exists_basis hFK h1
  obtain ⟨f, hf⟩ := exists_basis hFL h2
  let a := deg K L hKL
  let b := deg L M hLM
  let g : Fin (dim K (L.over K hKL)) × Fin (dim L (M.over L hLM)) → M.over K (le_trans hKL hLM) :=
    fun p => ⟨(e p.1).1 * (f p.2).1, M.mul_mem (hLM _ (e p.1).2) (f p.2).2⟩
  have hspan : Spans K g := by
    intro x
    obtain ⟨d, hd⟩ := hf.2 ⟨x.1, x.2⟩
    have hd' : x.1 = isum (fun j => (d j).1 * (f j).1) := by
      have := congrArg Subtype.val hd; rw [coe_isum] at this; exact this
    let c : Fin (dim L (M.over L hLM)) → Fin (dim K (L.over K hKL)) → K := fun j =>
      Classical.choose (he.2 (⟨(d j).1, (d j).2⟩ : L.over K hKL))
    have hc : ∀ j, (d j).1 = isum (fun i => (c j i).1 * (e i).1) := by
      intro j
      have := congrArg Subtype.val
        (Classical.choose_spec (he.2 (⟨(d j).1, (d j).2⟩ : L.over K hKL)))
      rw [coe_isum] at this; exact this
    refine ⟨fun p => c p.2 p.1, Subtype.ext ?_⟩
    rw [coe_isum, isum_prod, hd', isum_comm]
    congr 1; funext j
    rw [hc j, isum_mul_right]
    congr 1; funext i
    show (c j i).1 * (e i).1 * (f j).1 = (c j i).1 * ((e i).1 * (f j).1)
    rw [Ring.mul_assoc]
  have hind : LinIndep K g := by
    intro c hc
    have h0 : isum (fun p => (c p).1 * (g p).1) = 0 := by
      have := congrArg Subtype.val hc; rw [coe_isum] at this; exact this
    rw [isum_prod, isum_comm] at h0
    -- The coefficient of `f j` over `L`.
    let d : Fin (dim L (M.over L hLM)) → L := fun j =>
      ⟨isum (fun i => (c (i, j)).1 * (e i).1),
        (isum (fun i => c (i, j) • e i) : L.over K hKL).2 |> fun h => by
          rw [coe_isum] at h; exact h⟩
    have hdj : ∀ j, d j = 0 := by
      apply hf.1 d
      apply Subtype.ext
      rw [coe_isum]
      show isum (fun j => isum (fun i => (c (i, j)).1 * (e i).1) * (f j).1) = 0
      rw [← h0]
      congr 1; funext j
      rw [isum_mul_right]
      congr 1; funext i
      show (c (i, j)).1 * (e i).1 * (f j).1 = (c (i, j)).1 * ((e i).1 * (f j).1)
      rw [Ring.mul_assoc]
    intro p
    have := he.1 (fun i => c (i, p.2)) (by
      apply Subtype.ext
      rw [coe_isum]
      exact congrArg Subtype.val (hdj p.2)) p.1
    exact this
  have hfin : FiniteExt K M (le_trans hKL hLM) := finDim_of_spans hspan
  refine ⟨hfin, ?_⟩
  have := card_eq_dim hFK hfin ⟨hind, hspan⟩
  rw [card_prod, card_fin, card_fin] at this
  show dim K (M.over K _) = dim L (M.over L hLM) * dim K (L.over K hKL)
  rw [← this, Nat.mul_comm]

end Foundations.Algebra
