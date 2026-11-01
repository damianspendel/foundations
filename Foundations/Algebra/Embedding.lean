import Foundations.Algebra.Adjoin

/-!
# Extending embeddings, and automorphisms from embeddings

The previous file built the simple extension `F(γ)`. Here we prove the two facts that turn
embeddings into Galois automorphisms.

* **Extension of embeddings** (`extend`). A ring homomorphism `σ : F → E` extends to
  `τ : F(γ) → E` with `τ(γ) = δ` whenever `δ` is a root of every `σ(q)` with `q(γ) = 0`. The
  formula is forced: `τ(p(γ)) = (σ p)(δ)`. It is well defined because `p(γ) = p'(γ)` puts
  `p - p'` among the polynomials killed by `δ`. Over `E = ℂ` a suitable `δ` always exists
  (`exists_root_C`): the minimal polynomial `m` of `γ` is non-constant, so `σ(m)` has a complex
  root by the fundamental theorem of algebra, and every `q` with `q(γ) = 0` is a multiple of `m`.
* **Injective endomorphisms of finite extensions are onto**
  (`ringHom_surjective_of_finite`). A ring homomorphism `τ : L → L` fixing `K`, with `[L : K]`
  finite, is a `K`-linear injection of a finite-dimensional space into itself. It maps a basis
  to an independent family of the same size, hence to a basis, so it is onto. Such a `τ` is
  therefore an element of `Aut(L/K)` (`autOfRingHom`).
* Ring homomorphisms fix the prime field (`ringHom_fix_ratField`).
-/

namespace Foundations.Algebra

open Polynomial Subfield KSubspace VectorSpace FiniteType

universe u v w

/-! ## Basic facts on ring homomorphisms -/

/-- A ring homomorphism out of a field into a non-zero ring kills only `0`. -/
theorem RingHom.eq_zero_of_isField {K : Type u} [CommRing K] (hK : IsField K) {E : Type v}
    [CommRing E] (h01 : (0 : E) ≠ 1) (σ : RingHom K E) {x : K} (h : σ.toFun x = 0) : x = 0 := by
  apply Classical.byContradiction; intro hx
  obtain ⟨y, hy⟩ := hK.2 x hx
  apply h01
  rw [← σ.map_one, ← hy, σ.map_mul, h, Ring.zero_mul]

/-- **Ring homomorphisms out of a field are injective.** -/
theorem RingHom.injective_of_isField {K : Type u} [CommRing K] (hK : IsField K) {E : Type v}
    [CommRing E] (h01 : (0 : E) ≠ 1) (σ : RingHom K E) {x y : K} (h : σ.toFun x = σ.toFun y) :
    x = y := by
  have : σ.toFun (x + -y) = 0 := by rw [σ.map_add, σ.map_neg, h]; grind
  have := RingHom.eq_zero_of_isField hK h01 σ this
  grind

/-- Ring homomorphisms preserve the images of natural numbers. -/
theorem RingHom.map_ncast {A : Type u} {B : Type v} [CommRing A] [CommRing B] (σ : RingHom A B) :
    ∀ n : Nat, σ.toFun (ncast n) = ncast n
  | 0 => σ.map_zero
  | 1 => σ.map_one
  | n + 2 => by
    show σ.toFun (ncast (n + 1) + 1) = ncast (n + 1) + 1
    rw [σ.map_add, RingHom.map_ncast σ (n + 1), σ.map_one]

/-- Ring homomorphisms preserve the images of integers. -/
theorem RingHom.map_intCast {A : Type u} {B : Type v} [CommRing A] [CommRing B] (σ : RingHom A B)
    (z : Int) : σ.toFun (Int.cast z) = (Int.cast z : B) := by
  show σ.toFun (icast z) = icast z
  match z with
  | .ofNat n => exact RingHom.map_ncast σ n
  | .negSucc n => show σ.toFun (-(ncast (n + 1))) = -(ncast (n + 1))
                  rw [σ.map_neg, RingHom.map_ncast]

/-- Ring homomorphisms preserve finite sums over finite types. -/
theorem RingHom.map_isum {A : Type u} {B : Type v} [CommRing A] [CommRing B] (σ : RingHom A B)
    {ι : Type w} [FiniteType ι] (f : ι → A) : σ.toFun (isum f) = isum (fun i => σ.toFun (f i)) := by
  unfold isum
  induction (elems : List ι) with
  | nil => exact σ.map_zero
  | cons a l ih =>
    show σ.toFun (f a + lsum (l.map f)) = σ.toFun (f a) + lsum (l.map fun i => σ.toFun (f i))
    rw [σ.map_add, ih]

/-- **Ring homomorphisms fix the prime field.** A ring homomorphism `τ : L → L` of a subfield
containing `ℚ` fixes every rational number. -/
theorem ringHom_fix_ratField {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω) (hc : CharZero Ω)
    {L : Subfield Ω} (τ : RingHom L L) (x : L) (hx : x.1 ∈ ratField hΩ hc) : τ.toFun x = x := by
  obtain ⟨a, b, hb, hab⟩ := hx
  have hbL : (Int.cast b : L) ≠ 0 := by
    intro h; apply hb; apply hc
    have := congrArg Subtype.val h
    rw [Subfield.coe_intCast] at this; exact this
  have e : x * Int.cast b = Int.cast a := Subtype.ext (by
    rw [Subfield.coe_mul, Subfield.coe_intCast, Subfield.coe_intCast]; exact hab)
  have e' : τ.toFun x * Int.cast b = Int.cast a := by
    rw [← RingHom.map_intCast τ b, ← τ.map_mul, e, RingHom.map_intCast]
  have hD := (L.isField hΩ).isDomain
  have : (τ.toFun x + -x) * Int.cast b = 0 := by grind
  rcases hD.2 _ _ this with h | h
  · grind
  · exact absurd h hbL

/-! ## Extension of embeddings -/

section Extend

variable {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω) (F : Subfield Ω) (γ : Ω)
  (hγ : IsAlgebraic F γ) {E : Type v} [CommRing E]

/-- `p ↦ (σ p)(δ)` as a ring homomorphism `F[x] → E`. -/
def evalMapHom (σ : RingHom F E) (δ : E) : RingHom (Polynomial F) E :=
  (evalHom δ).comp (mapHom σ)

/-- **Extension of embeddings.** Let `σ : F → E` be a ring homomorphism and `δ ∈ E` a root of
`σ(q)` for every `q ∈ F[x]` with `q(γ) = 0`. Then `σ` extends to a ring homomorphism
`τ : F(γ) → E` with `τ(γ) = δ`, given by `τ(p(γ)) = (σ p)(δ)`. -/
theorem extend (σ : RingHom F E) (δ : E)
    (hδ : ∀ q, aeval F γ q = 0 → eval δ (mapPoly σ q) = 0) :
    ∃ τ : RingHom (adjoin hΩ F γ hγ) E,
      (∀ x : F, τ.toFun ⟨x.1, le_adjoin hΩ F γ hγ x.1 x.2⟩ = σ.toFun x) ∧
      τ.toFun ⟨γ, mem_adjoin_self hΩ F γ hγ⟩ = δ ∧
      (∀ p, τ.toFun ⟨aeval F γ p, p, rfl⟩ = eval δ (mapPoly σ p)) := by
  let ev := evalMapHom F σ δ
  have key : ∀ p q, aeval F γ p = aeval F γ q → ev.toFun p = ev.toFun q := by
    intro p q h
    have h0 : aeval F γ (p + -q) = 0 := by rw [aeval_add, aeval_neg, h]; grind
    have h1 : ev.toFun (p + -q) = 0 := hδ _ h0
    rw [ev.map_add, ev.map_neg] at h1
    grind
  let f : adjoin hΩ F γ hγ → E := fun y => ev.toFun (Classical.choose y.2)
  have hf : ∀ (y : adjoin hΩ F γ hγ) p, aeval F γ p = y.1 → f y = ev.toFun p := fun y p hp =>
    key _ _ ((Classical.choose_spec y.2).trans hp.symm)
  have hadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    obtain ⟨p, hp⟩ : ∃ p, aeval F γ p = a.1 := a.2
    obtain ⟨q, hq⟩ : ∃ q, aeval F γ q = b.1 := b.2
    rw [hf a p hp, hf b q hq, hf (a + b) (p + q) (by rw [aeval_add, hp, hq]; rfl), ev.map_add]
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    obtain ⟨p, hp⟩ : ∃ p, aeval F γ p = a.1 := a.2
    obtain ⟨q, hq⟩ : ∃ q, aeval F γ q = b.1 := b.2
    rw [hf a p hp, hf b q hq, hf (a * b) (p * q) (by rw [aeval_mul, hp, hq]; rfl), ev.map_mul]
  have hone : f 1 = 1 := by rw [hf 1 1 (aeval_one F γ), ev.map_one]
  refine ⟨⟨f, hadd, hmul, hone⟩, fun x => ?_, ?_, fun p => hf _ p rfl⟩
  · show f _ = _
    rw [hf _ (C x) (aeval_C F γ x)]
    show eval δ (mapPoly σ (C x)) = _
    rw [mapPoly_C, eval_C]
  · show f _ = _
    rw [hf _ X (aeval_X F γ)]
    show eval δ (mapPoly σ X) = _
    rw [mapPoly_X, eval_X]

include hΩ hγ in
/-- **Roots in `ℂ` for extending embeddings.** For any ring homomorphism `σ : F → ℂ` there is
`δ ∈ ℂ` killed by `σ(q)` for every `q` with `q(γ) = 0`: a complex root of `σ(m)`, `m` the
minimal polynomial of `γ`, which exists by the fundamental theorem of algebra. -/
theorem exists_root_C (σ : RingHom F Foundations.Numbers.C) :
    ∃ δ : Foundations.Numbers.C, ∀ q, aeval F γ q = 0 → eval δ (mapPoly σ q) = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_minpoly F γ hΩ hγ
  have hFF := F.isField hΩ
  have hmz : aeval F γ m = 0 := (hm m).2 ⟨1, (Ring.mul_one m).symm⟩
  have hdeg : natDegree m ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := isUnit_of_natDegree_zero hFF hm0 h0
    have := congrArg (aeval F γ) hu
    rw [aeval_mul, hmz, Ring.zero_mul, aeval_one] at this
    exact hΩ.1 this
  have hlead : coeff (mapPoly σ m) (natDegree m) ≠ 0 := by
    rw [coeff_mapPoly]; intro h
    exact leadingCoeff_ne_zero hm0 (RingHom.eq_zero_of_isField hFF C.isField.1 σ h)
  obtain ⟨δ, hδ⟩ := C.fta' (mapPoly σ m) (Nat.pos_of_ne_zero hdeg) hlead
  refine ⟨δ, fun q hq => ?_⟩
  obtain ⟨c, rfl⟩ := (hm q).1 hq
  show (evalMapHom F σ δ).toFun (m * c) = 0
  rw [(evalMapHom F σ δ).map_mul]
  show eval δ (mapPoly σ m) * _ = 0
  rw [hδ, Ring.zero_mul]

end Extend

/-! ## Injective endomorphisms of finite extensions -/

section Surjective

variable {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω)

include hΩ in
/-- **An injective endomorphism of a finite extension is onto.** If `τ : L → L` is a ring
homomorphism fixing `K` and `[L : K]` is finite, every element of `L` is a value of `τ`. -/
theorem ringHom_surjective_of_finite {K L : Subfield Ω} (hKL : K.le L)
    (hfin : FiniteExt K L hKL) (τ : RingHom L L) (hfix : ∀ x : L, x.1 ∈ K → τ.toFun x = x) :
    ∀ y : L, ∃ x, τ.toFun x = y := by
  have hFK := K.isField hΩ
  have hFL := L.isField hΩ
  obtain ⟨e, he⟩ := exists_basis hFK hfin
  let V := L.over K hKL
  let eL : Fin (dim K V) → L := fun i => ⟨(e i).1, (e i).2⟩
  let f : Fin (dim K V) → V := fun i => ⟨(τ.toFun (eL i)).1, (τ.toFun (eL i)).2⟩
  let cL : (Fin (dim K V) → K) → Fin (dim K V) → L := fun c i => ⟨(c i).1, hKL _ (c i).2⟩
  -- `τ` commutes with `K`-linear combinations
  have hcomb : ∀ c : Fin (dim K V) → K,
      τ.toFun (isum (fun i => cL c i * eL i)) = isum (fun i => cL c i * τ.toFun (eL i)) := by
    intro c
    rw [RingHom.map_isum]
    congr 1; funext i
    rw [τ.map_mul, hfix (cL c i) (c i).2]
  have hval : ∀ (c : Fin (dim K V) → K) (v : Fin (dim K V) → L),
      (isum (fun i => cL c i * v i)).1 = isum (fun i => (c i).1 * (v i).1) := by
    intro c v; rw [Subfield.coe_isum]; rfl
  have hind : LinIndep K f := by
    intro c hc
    apply he.1 c
    apply Subtype.ext
    have h1 := congrArg Subtype.val hc
    rw [KSubspace.coe_isum] at h1 ⊢
    have h2 : (τ.toFun (isum (fun i => cL c i * eL i))).1 = 0 := by
      rw [hcomb, hval]; exact h1
    have h3 : τ.toFun (isum (fun i => cL c i * eL i)) = 0 := Subtype.ext h2
    have h4 := RingHom.eq_zero_of_isField hFL hFL.1 τ h3
    have h5 := congrArg Subtype.val h4
    rw [hval] at h5
    exact h5
  have hspan := spans_of_card_eq_dim hFK hfin hind (card_fin _)
  intro y
  obtain ⟨c, hc⟩ := hspan ⟨y.1, y.2⟩
  refine ⟨isum (fun i => cL c i * eL i), Subtype.ext ?_⟩
  rw [hcomb, hval]
  have := congrArg Subtype.val hc
  rw [KSubspace.coe_isum] at this
  exact this.symm

/-- **An automorphism from an endomorphism.** A ring homomorphism `τ : L → L` fixing `K`, with
`[L : K]` finite, is an element of `Aut(L/K)`. -/
noncomputable def autOfRingHom {K L : Subfield Ω} (hKL : K.le L) (hfin : FiniteExt K L hKL)
    (τ : RingHom L L) (hfix : ∀ x : L, x.1 ∈ K → τ.toFun x = x) : FieldAut K L where
  toFun := τ.toFun
  invFun y := Classical.choose (ringHom_surjective_of_finite hΩ hKL hfin τ hfix y)
  left_inv x := RingHom.injective_of_isField (L.isField hΩ) (L.isField hΩ).1 τ
    (Classical.choose_spec (ringHom_surjective_of_finite hΩ hKL hfin τ hfix (τ.toFun x)))
  right_inv y := Classical.choose_spec (ringHom_surjective_of_finite hΩ hKL hfin τ hfix y)
  map_add := τ.map_add
  map_mul := τ.map_mul
  fix := hfix

/-- The automorphism built from `τ` acts as `τ`. -/
theorem autOfRingHom_apply {K L : Subfield Ω} (hKL : K.le L) (hfin : FiniteExt K L hKL)
    (τ : RingHom L L) (hfix : ∀ x : L, x.1 ∈ K → τ.toFun x = x) (x : L) :
    (autOfRingHom hΩ hKL hfin τ hfix).toFun x = τ.toFun x := rfl

end Surjective

end Foundations.Algebra
