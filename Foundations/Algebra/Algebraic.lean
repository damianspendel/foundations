import Foundations.Algebra.FieldExt

/-!
# Algebraic numbers: quadratic and cubic extensions

An element `α` of a field `Ω` is *algebraic* over a subfield `K` if it is a root of a
polynomial with coefficients in `K`; the smallest field `K(α)` containing `K` and `α` then
has finite degree over `K`, equal to the degree of the minimal polynomial of `α`. For the
impossibility proofs only two cases matter, and we treat them concretely:

* **square roots.** If `s² ∈ K`, then `K(s) = {a + b s : a, b ∈ K}` is a field of degree `1`
  or `2` over `K`. (Inverses: `(a + bs)⁻¹ = (a - bs)/(a² - b² s²)`.)
* **roots of irreducible cubics.** If `α` is a root of a cubic over `K` that has *no root in
  `K`* (for a cubic this is the same as irreducibility), then
  `K(α) = {u + vα + wα² : u, v, w ∈ K}` is a field of degree exactly `3` over `K`. The key
  step is that `1, α, α²` are linearly independent: a quadratic relation would split the
  cubic and give it a root in `K`. That `K(α)` is closed under inverses is pure linear
  algebra — multiplication by a non-zero element is an injective linear map of a
  three-dimensional space to itself, hence surjective, so it hits `1`.

**The rationals.** The base field of the classical problems is `ℚ`. Since this Part may not
use the Numbers part, we do not construct `ℚ` as a separate type; instead we work inside an
arbitrary ambient field `Ω` of **characteristic zero** (one in which the canonical map
`ℤ → Ω` is injective — think of `ℝ` or `ℂ`), and take for `ℚ` its *prime field*
`{a/b : a, b ∈ ℤ, b ≠ 0}`, which is isomorphic to `ℚ` in every such field. The rational root
tests for `x³ - 2` and `8x³ - 6x - 1` are then honest statements about integers, proved by
infinite descent on the denominator.

To calculate comfortably in an abstract commutative ring we register every `CommRing` as a
commutative ring for Lean's `grind` tactic, which then decides polynomial identities.
-/

namespace Foundations.Algebra

open Ring FiniteType VectorSpace Subfield KSubspace

universe u

/-! ## `grind` for abstract commutative rings -/

section GrindBridge

variable {R : Type u} [CommRing R]

/-- The image of a natural number in a ring: `n ↦ 1 + ⋯ + 1`. -/
def ncast : Nat → R
  | 0 => 0
  | 1 => 1
  | n + 2 => ncast (n + 1) + 1

/-- The image of an integer in a ring. -/
def icast : Int → R
  | .ofNat n => ncast n
  | .negSucc n => -(ncast (n + 1))

/-- Natural-number powers in a ring. -/
def rpow (a : R) : Nat → R
  | 0 => 1
  | n + 1 => rpow a n * a

/-- `ncast (n + 1) = ncast n + 1`. -/
theorem ncast_succ (n : Nat) : (ncast (n + 1) : R) = ncast n + 1 := by
  cases n with
  | zero => show (1 : R) = 0 + 1; rw [Ring.zero_add]
  | succ n => rfl

/-- `icast (-i) = -icast i`. -/
theorem icast_neg (i : Int) : (icast (-i) : R) = -icast i := by
  match i with
  | .ofNat 0 => show (0 : R) = -0; rw [neg_zero]
  | .ofNat (n + 1) => rfl
  | .negSucc n => show (ncast (n + 1) : R) = -(-(ncast (n + 1))); rw [neg_neg]

/-- **Every commutative ring is a commutative ring for `grind`.** This lets the `grind`
tactic decide polynomial identities in abstract rings. -/
instance (priority := low) CommRing.toGrindCommRing : Lean.Grind.CommRing R where
  sub a b := a + -b
  natCast := ⟨ncast⟩
  ofNat n := ⟨ncast n⟩
  nsmul := ⟨fun n a => ncast n * a⟩
  npow := ⟨rpow⟩
  intCast := ⟨icast⟩
  zsmul := ⟨fun n a => icast n * a⟩
  add_zero := Ring.add_zero
  add_comm := Ring.add_comm
  add_assoc := Ring.add_assoc
  mul_assoc := Ring.mul_assoc
  mul_one := Ring.mul_one
  one_mul := Ring.one_mul
  left_distrib := Ring.left_distrib
  right_distrib := Ring.right_distrib
  zero_mul := Ring.zero_mul
  mul_zero := Ring.mul_zero
  pow_zero := by intro a; rfl
  pow_succ := by intro a n; rfl
  ofNat_succ := ncast_succ
  neg_add_cancel := Ring.neg_add_cancel
  sub_eq_add_neg := by intro a b; rfl
  neg_zsmul := by intro i a; show icast (-i) * a = -(icast i * a); rw [icast_neg, neg_mul]
  intCast_neg := icast_neg
  mul_comm := CommRing.mul_comm

/-- The canonical map `ℤ → R` as a coercion (the same map `grind` uses). -/
instance (priority := low) CommRing.toIntCast : IntCast R := ⟨icast⟩

end GrindBridge

/-! ## Characteristic zero and the prime field -/

section PrimeField

variable {Ω : Type u} [CommRing Ω]

/-- A ring has **characteristic zero** if the canonical map `ℤ → Ω` is injective. -/
def CharZero (Ω : Type u) [CommRing Ω] : Prop := ∀ z : Int, (Int.cast z : Ω) = 0 → z = 0

/-- In characteristic zero, integers with equal images are equal. -/
theorem CharZero.cast_inj (hc : CharZero Ω) {a b : Int} (h : (Int.cast (a) : Ω) = (Int.cast (b) : Ω)) : a = b := by
  have := hc (a - b) (by rw [Lean.Grind.Ring.intCast_sub, h]; grind)
  omega

/-- **The prime field** `ℚ ⊆ Ω` of a field of characteristic zero: the quotients `a / b` of
integers with `b ≠ 0`. -/
def ratField (hΩ : IsField Ω) (hc : CharZero Ω) : Subfield Ω where
  carrier x := ∃ a b : Int, b ≠ 0 ∧ x * (Int.cast (b) : Ω) = (Int.cast (a) : Ω)
  zero_mem := ⟨0, 1, by decide, by grind⟩
  one_mem := ⟨1, 1, by decide, by grind⟩
  add_mem := by
    intro x y ⟨a, b, hb, hx⟩ ⟨c, d, hd, hy⟩
    refine ⟨a * d + c * b, b * d, Int.mul_ne_zero hb hd, ?_⟩
    rw [Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_add, Lean.Grind.Ring.intCast_mul,
      Lean.Grind.Ring.intCast_mul, ← hx, ← hy]
    grind
  neg_mem := by
    intro x ⟨a, b, hb, hx⟩
    refine ⟨-a, b, hb, ?_⟩
    rw [Lean.Grind.Ring.intCast_neg, ← hx]; grind
  mul_mem := by
    intro x y ⟨a, b, hb, hx⟩ ⟨c, d, hd, hy⟩
    refine ⟨a * c, b * d, Int.mul_ne_zero hb hd, ?_⟩
    rw [Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, ← hx, ← hy]
    grind
  inv_mem := by
    intro x ⟨a, b, hb, hx⟩ hx0
    have hb' : (Int.cast (b) : Ω) ≠ 0 := fun h => hb (hc b h)
    have ha : (Int.cast (a) : Ω) ≠ 0 := by
      intro h
      rw [h] at hx
      rcases hΩ.isDomain.2 _ _ hx with h1 | h1
      · exact hx0 h1
      · exact hb' h1
    have ha' : a ≠ 0 := fun h => ha (by rw [h]; grind)
    obtain ⟨t, ht⟩ := hΩ.2 _ ha
    refine ⟨(Int.cast (b) : Ω) * t, ⟨b, a, ha', ?_⟩, ?_⟩
    · grind
    · grind

/-- Integers lie in the prime field. -/
theorem intCast_mem_ratField (hΩ : IsField Ω) (hc : CharZero Ω) (n : Int) :
    (Int.cast (n) : Ω) ∈ ratField hΩ hc :=
  ⟨n, 1, by decide, by grind⟩

end PrimeField

/-! ## Adjoining a square root -/

section Quadratic

variable {Ω : Type u} [CommRing Ω]

/-- **Adjoining a square root.** If `s² ∈ F`, then `F(s) = {a + b s : a, b ∈ F}` is a field. -/
def adjoinSqrt (hΩ : IsField Ω) (F : Subfield Ω) (s : Ω) (hs : s * s ∈ F) : Subfield Ω where
  carrier x := ∃ a b, a ∈ F ∧ b ∈ F ∧ x = a + b * s
  zero_mem := ⟨0, 0, F.zero_mem, F.zero_mem, by grind⟩
  one_mem := ⟨1, 0, F.one_mem, F.zero_mem, by grind⟩
  add_mem := by
    intro x y ⟨a, b, ha, hb, hx⟩ ⟨c, d, hc, hd, hy⟩
    exact ⟨a + c, b + d, F.add_mem ha hc, F.add_mem hb hd, by rw [hx, hy]; grind⟩
  neg_mem := by
    intro x ⟨a, b, ha, hb, hx⟩
    exact ⟨-a, -b, F.neg_mem ha, F.neg_mem hb, by rw [hx]; grind⟩
  mul_mem := by
    intro x y ⟨a, b, ha, hb, hx⟩ ⟨c, d, hc, hd, hy⟩
    exact ⟨a * c + b * d * (s * s), a * d + b * c,
      F.add_mem (F.mul_mem ha hc) (F.mul_mem (F.mul_mem hb hd) hs),
      F.add_mem (F.mul_mem ha hd) (F.mul_mem hb hc), by rw [hx, hy]; grind⟩
  inv_mem := by
    intro x ⟨a, b, ha, hb, hx⟩ hx0
    let N := a * a + -(b * b * (s * s))
    have hN : N ∈ F := F.add_mem (F.mul_mem ha ha) (F.neg_mem (F.mul_mem (F.mul_mem hb hb) hs))
    by_cases hN0 : N = 0
    · -- Then `a - b s = 0`, so `s ∈ F` (or `x = 0`) and `x ∈ F`.
      have hprod : (a + b * s) * (a + -(b * s)) = 0 := by rw [← hN0]; grind
      rcases hΩ.isDomain.2 _ _ hprod with h | h
      · exact absurd (hx.trans h) hx0
      · by_cases hb0 : b = 0
        · exfalso; apply hx0; rw [hx, hb0]; grind
        · obtain ⟨b', hb', hbb'⟩ := F.inv_mem hb hb0
          have hsF : s ∈ F := by
            have : s = a * b' := by grind
            rw [this]; exact F.mul_mem ha hb'
          have hxF : x ∈ F := by rw [hx]; exact F.add_mem ha (F.mul_mem hb hsF)
          obtain ⟨y, hy, hxy⟩ := F.inv_mem hxF hx0
          exact ⟨y, ⟨y, 0, hy, F.zero_mem, by grind⟩, hxy⟩
    · obtain ⟨t, ht, hNt⟩ := F.inv_mem hN hN0
      refine ⟨a * t + -(b * t) * s, ⟨a * t, -(b * t), F.mul_mem ha ht,
        F.neg_mem (F.mul_mem hb ht), rfl⟩, ?_⟩
      rw [hx]
      have : N * t = 1 := hNt
      grind

/-- `F ⊆ F(s)`. -/
theorem le_adjoinSqrt (hΩ : IsField Ω) (F : Subfield Ω) (s : Ω) (hs : s * s ∈ F) : F.le (adjoinSqrt hΩ F s hs) :=
  fun x hx => ⟨x, 0, hx, F.zero_mem, by grind⟩

/-- `s ∈ F(s)`. -/
theorem mem_adjoinSqrt_self (hΩ : IsField Ω) (F : Subfield Ω) (s : Ω) (hs : s * s ∈ F) :
    s ∈ adjoinSqrt hΩ F s hs :=
  ⟨0, 1, F.zero_mem, F.one_mem, by grind⟩

/-- Adjoining the same square root to a larger field gives a larger field. -/
theorem adjoinSqrt_mono (hΩ : IsField Ω) {F G : Subfield Ω} (hFG : F.le G) (s : Ω) (hs : s * s ∈ F)
    (hs' : s * s ∈ G) : (adjoinSqrt hΩ F s hs).le (adjoinSqrt hΩ G s hs') :=
  fun _ ⟨a, b, ha, hb, hx⟩ => ⟨a, b, hFG a ha, hFG b hb, hx⟩

/-- Sums over `Fin 2`. -/
theorem isum_fin2 {A : Type u} [AddAbGroup A] (f : Fin 2 → A) : isum f = f 0 + f 1 := by
  rw [isum_fin_succ, isum_fin_succ, isum_fin_zero, AddAbGroup.add_zero]; rfl

/-- Sums over `Fin 3`. -/
theorem isum_fin3 {A : Type u} [AddAbGroup A] (f : Fin 3 → A) : isum f = f 0 + f 1 + f 2 := by
  rw [isum_fin_succ, isum_fin_succ, isum_fin_succ, isum_fin_zero, AddAbGroup.add_zero,
    AddAbGroup.add_assoc]; rfl

/-- **`[F(s) : F]` is `1` or `2`.** -/
theorem deg_adjoinSqrt (hΩ : IsField Ω) (F : Subfield Ω) (s : Ω) (hs : s * s ∈ F) :
    FiniteExt F (adjoinSqrt hΩ F s hs) (le_adjoinSqrt hΩ F s hs) ∧
      (deg F (adjoinSqrt hΩ F s hs) (le_adjoinSqrt hΩ F s hs) = 1 ∨
       deg F (adjoinSqrt hΩ F s hs) (le_adjoinSqrt hΩ F s hs) = 2) := by
  have hF := F.isField hΩ
  let V := (adjoinSqrt hΩ F s hs).over F (le_adjoinSqrt hΩ F s hs)
  let u : Fin 2 → V := fun i =>
    if i.val = 0 then ⟨1, (adjoinSqrt hΩ F s hs).one_mem⟩ else ⟨s, mem_adjoinSqrt_self hΩ F s hs⟩
  have hspan : Spans F u := by
    intro x
    obtain ⟨a, b, ha, hb, hx⟩ := x.2
    refine ⟨fun i => if i.val = 0 then ⟨a, ha⟩ else ⟨b, hb⟩, Subtype.ext ?_⟩
    rw [coe_isum, isum_fin2]
    show x.1 = a * 1 + b * s
    rw [hx]; grind
  have hfin : FinDim F V := finDim_of_spans hspan
  refine ⟨hfin, ?_⟩
  have h2 := dim_le_card hF hfin hspan
  rw [card_fin] at h2
  let one : Fin 1 → V := fun _ => ⟨1, (adjoinSqrt hΩ F s hs).one_mem⟩
  have hone : LinIndep F one := by
    intro c hc i
    have := congrArg Subtype.val hc
    rw [coe_isum, isum_fin_succ, isum_fin_zero] at this
    have h0 : (c 0).1 = 0 := by
      have e : (c 0).1 * 1 + 0 = 0 := this
      grind
    have : c i = c 0 := congrArg c (Fin.ext (by have := i.isLt; omega))
    rw [this]; exact Subtype.ext h0
  have h1 := card_le_dim hF hfin hone
  rw [card_fin] at h1
  show dim F V = 1 ∨ dim F V = 2
  omega

end Quadratic

/-! ## Adjoining a root of an irreducible cubic -/

section Cubic

variable {Ω : Type u} [CommRing Ω] (K : Subfield Ω)

/-- Hypotheses for a root `α` of a cubic `d x³ + a x² + b x + c` over `K` (with `d ≠ 0`) that
has no root in `K`. -/
structure CubicRoot (α : Ω) where
  /-- Leading coefficient. -/
  d : Ω
  /-- Coefficient of `x²`. -/
  a : Ω
  /-- Coefficient of `x`. -/
  b : Ω
  /-- Constant coefficient. -/
  c : Ω
  /-- The leading coefficient lies in `K`. -/
  hd : d ∈ K
  /-- The coefficient of `x²` lies in `K`. -/
  ha : a ∈ K
  /-- The coefficient of `x` lies in `K`. -/
  hb : b ∈ K
  /-- The constant coefficient lies in `K`. -/
  hc : c ∈ K
  /-- The leading coefficient is non-zero. -/
  d_ne : d ≠ 0
  /-- `α` is a root. -/
  root : d * α * α * α + a * α * α + b * α + c = 0
  /-- The cubic has no root in `K`. -/
  no_root : ∀ x, x ∈ K → d * x * x * x + a * x * x + b * x + c ≠ 0

variable {K} {α : Ω}

/-- The monic form: coefficients `A, B, D ∈ K` with `α³ + A α² + B α + D = 0`, and the same
cubic has no root in `K`. -/
theorem CubicRoot.monic (C : CubicRoot K α) : ∃ A B D, A ∈ K ∧ B ∈ K ∧ D ∈ K ∧
    α * α * α + A * (α * α) + B * α + D = 0 ∧
    ∀ x, x ∈ K → x * x * x + A * (x * x) + B * x + D ≠ 0 := by
  obtain ⟨e, he, hde⟩ := K.inv_mem C.hd C.d_ne
  refine ⟨C.a * e, C.b * e, C.c * e, K.mul_mem C.ha he, K.mul_mem C.hb he, K.mul_mem C.hc he,
    ?_, fun x hx h => C.no_root x hx ?_⟩
  · have := C.root; grind
  · grind

/-- **`1, α, α²` are linearly independent over `K`.** A relation of degree `≤ 2` would split
the cubic and produce a root in `K`. -/
theorem CubicRoot.indep (hΩ : IsField Ω) (C : CubicRoot K α) {u v w : Ω} (hu : u ∈ K) (hv : v ∈ K) (hw : w ∈ K)
    (h : u + v * α + w * (α * α) = 0) : u = 0 ∧ v = 0 ∧ w = 0 := by
  have hD := hΩ.isDomain
  obtain ⟨A, B, D, hA, hB, hD', hmon, hno⟩ := C.monic
  have hαK : α ∉ K := fun hα => hno α hα hmon
  by_cases hw0 : w = 0
  · by_cases hv0 : v = 0
    · refine ⟨?_, hv0, hw0⟩; rw [hv0, hw0] at h; grind
    · exfalso
      obtain ⟨v', hv', hvv'⟩ := K.inv_mem hv hv0
      apply hαK
      have : α = -(u * v') := by rw [hw0] at h; grind
      rw [this]; exact K.neg_mem (K.mul_mem hu hv')
  · exfalso
    obtain ⟨w', hw', hww'⟩ := K.inv_mem hw hw0
    let r := -(v * w')
    let s := -(u * w')
    have hr : r ∈ K := K.neg_mem (K.mul_mem hv hw')
    have hs : s ∈ K := K.neg_mem (K.mul_mem hu hw')
    have hsq : α * α = r * α + s := by grind
    let B' := r * r + s + A * r + B
    let A' := r * s + A * s + D
    have hlin : B' * α + A' = 0 := by grind
    have hB'K : B' ∈ K :=
      K.add_mem (K.add_mem (K.add_mem (K.mul_mem hr hr) hs) (K.mul_mem hA hr)) hB
    have hA'K : A' ∈ K := K.add_mem (K.add_mem (K.mul_mem hr hs) (K.mul_mem hA hs)) hD'
    by_cases hB0 : B' = 0
    · have hA0 : A' = 0 := by rw [hB0] at hlin; grind
      let t := -(r + A)
      have ht : t ∈ K := K.neg_mem (K.add_mem hr hA)
      apply hno t ht
      have e1 : B' = 0 := hB0
      have e2 : A' = 0 := hA0
      grind
    · obtain ⟨b', hb', hbb'⟩ := K.inv_mem hB'K hB0
      apply hαK
      have : α = -(A' * b') := by grind
      rw [this]; exact K.neg_mem (K.mul_mem hA'K hb')

/-- The `K`-subspace `{u + v α + w α²}` spanned by `1, α, α²`. -/
def CubicRoot.space (_C : CubicRoot K α) : KSubspace K where
  carrier x := ∃ u v w, u ∈ K ∧ v ∈ K ∧ w ∈ K ∧ x = u + v * α + w * (α * α)
  zero_mem := ⟨0, 0, 0, K.zero_mem, K.zero_mem, K.zero_mem, by grind⟩
  add_mem := by
    intro x y ⟨u, v, w, hu, hv, hw, hx⟩ ⟨u', v', w', hu', hv', hw', hy⟩
    exact ⟨u + u', v + v', w + w', K.add_mem hu hu', K.add_mem hv hv', K.add_mem hw hw',
      by rw [hx, hy]; grind⟩
  neg_mem := by
    intro x ⟨u, v, w, hu, hv, hw, hx⟩
    exact ⟨-u, -v, -w, K.neg_mem hu, K.neg_mem hv, K.neg_mem hw, by rw [hx]; grind⟩
  smul_mem := by
    intro k x hk ⟨u, v, w, hu, hv, hw, hx⟩
    exact ⟨k * u, k * v, k * w, K.mul_mem hk hu, K.mul_mem hk hv, K.mul_mem hk hw,
      by rw [hx]; grind⟩

/-- The space `{u + v α + w α²}` is closed under multiplication. -/
theorem CubicRoot.space_mul (C : CubicRoot K α) {x y : Ω} (hx : C.space.carrier x) (hy : C.space.carrier y) :
    C.space.carrier (x * y) := by
  obtain ⟨A, B, D, hA, hB, hD, hmon, _⟩ := C.monic
  obtain ⟨u, v, w, hu, hv, hw, rfl⟩ := hx
  obtain ⟨u', v', w', hu', hv', hw', rfl⟩ := hy
  let p0 := u * u'
  let p1 := u * v' + v * u'
  let p2 := u * w' + v * v' + w * u'
  let p3 := v * w' + w * v'
  let p4 := w * w'
  have h0 : p0 ∈ K := K.mul_mem hu hu'
  have h1 : p1 ∈ K := K.add_mem (K.mul_mem hu hv') (K.mul_mem hv hu')
  have h2 : p2 ∈ K := K.add_mem (K.add_mem (K.mul_mem hu hw') (K.mul_mem hv hv')) (K.mul_mem hw hu')
  have h3 : p3 ∈ K := K.add_mem (K.mul_mem hv hw') (K.mul_mem hw hv')
  have h4 : p4 ∈ K := K.mul_mem hw hw'
  refine ⟨p0 + -(p3 * D) + p4 * (A * D), p1 + -(p3 * B) + p4 * (A * B + -D),
    p2 + -(p3 * A) + p4 * (A * A + -B),
    K.add_mem (K.add_mem h0 (K.neg_mem (K.mul_mem h3 hD))) (K.mul_mem h4 (K.mul_mem hA hD)),
    K.add_mem (K.add_mem h1 (K.neg_mem (K.mul_mem h3 hB)))
      (K.mul_mem h4 (K.add_mem (K.mul_mem hA hB) (K.neg_mem hD))),
    K.add_mem (K.add_mem h2 (K.neg_mem (K.mul_mem h3 hA)))
      (K.mul_mem h4 (K.add_mem (K.mul_mem hA hA) (K.neg_mem hB))), ?_⟩
  grind

/-- The basis `1, α, α²` of the space. -/
def CubicRoot.basis (C : CubicRoot K α) : Fin 3 → C.space := fun i =>
  if i.val = 0 then ⟨1, 1, 0, 0, K.one_mem, K.zero_mem, K.zero_mem, by grind⟩
  else if i.val = 1 then ⟨α, 0, 1, 0, K.zero_mem, K.one_mem, K.zero_mem, by grind⟩
  else ⟨α * α, 0, 0, 1, K.zero_mem, K.zero_mem, K.one_mem, by grind⟩

/-- `1, α, α²` is a basis of the space. -/
theorem CubicRoot.isBasis (hΩ : IsField Ω) (C : CubicRoot K α) : IsBasis K C.basis := by
  constructor
  · intro c hc
    have h := congrArg Subtype.val hc
    rw [coe_isum, isum_fin3] at h
    have h' : (c 0).1 + (c 1).1 * α + (c 2).1 * (α * α) = 0 := by
      have e : (c 0).1 * 1 + (c 1).1 * α + (c 2).1 * (α * α) = 0 := h
      grind
    obtain ⟨e0, e1, e2⟩ := C.indep hΩ (c 0).2 (c 1).2 (c 2).2 h'
    intro i
    apply Subtype.ext
    match i with
    | ⟨0, _⟩ => exact e0
    | ⟨1, _⟩ => exact e1
    | ⟨2, _⟩ => exact e2
  · intro x
    obtain ⟨u, v, w, hu, hv, hw, hx⟩ := x.2
    refine ⟨fun i => if i.val = 0 then ⟨u, hu⟩ else if i.val = 1 then ⟨v, hv⟩ else ⟨w, hw⟩,
      Subtype.ext ?_⟩
    rw [coe_isum, isum_fin3]
    show x.1 = u * 1 + v * α + w * (α * α)
    rw [hx]; grind

/-- The space has dimension `3` over `K`. -/
theorem CubicRoot.dim_space (hΩ : IsField Ω) (C : CubicRoot K α) : FinDim K C.space ∧ dim K C.space = 3 := by
  have hfin : FinDim K C.space := finDim_of_spans (C.isBasis hΩ).2
  refine ⟨hfin, ?_⟩
  rw [← card_eq_dim (K.isField hΩ) hfin (C.isBasis hΩ), card_fin]

/-- **Inverses.** Every non-zero element of the space has an inverse in the space:
multiplication by it is an injective linear map of a `3`-dimensional space, hence onto. -/
theorem CubicRoot.space_inv (hΩ : IsField Ω) (C : CubicRoot K α) {β : Ω} (hβ : C.space.carrier β) (hβ0 : β ≠ 0) :
    ∃ γ, C.space.carrier γ ∧ β * γ = 1 := by
  have hF := K.isField hΩ
  obtain ⟨hfin, hdim⟩ := C.dim_space hΩ
  let f : Fin 3 → C.space := fun i => ⟨β * (C.basis i).1, C.space_mul hβ (C.basis i).2⟩
  have hind : LinIndep K f := by
    intro c hc
    apply (C.isBasis hΩ).1 c
    apply Subtype.ext
    have h := congrArg Subtype.val hc
    rw [coe_isum] at h ⊢
    have e : isum (fun i => (c i • f i).1) = β * isum (fun i => (c i • C.basis i).1) := by
      rw [isum_mul_left]; congr 1; funext i
      show (c i).1 * (β * (C.basis i).1) = β * ((c i).1 * (C.basis i).1)
      grind
    rw [e] at h
    rcases hΩ.isDomain.2 _ _ h with h1 | h1
    · exact absurd h1 hβ0
    · exact h1
  have hspan := spans_of_card_eq_dim hF hfin hind (by rw [card_fin, hdim])
  obtain ⟨c, hc⟩ := hspan ⟨1, (C.basis 0).2⟩
  refine ⟨(isum (fun i => c i • C.basis i)).1, (isum (fun i => c i • C.basis i)).2, ?_⟩
  have h : (1 : Ω) = isum (fun i => (c i • f i).1) := by
    have := congrArg Subtype.val hc; rw [coe_isum] at this; exact this
  calc β * (isum (fun i => c i • C.basis i)).1 = isum (fun i => (c i • f i).1) := by
        rw [coe_isum, isum_mul_left]; congr 1; funext i
        show β * ((c i).1 * (C.basis i).1) = (c i).1 * (β * (C.basis i).1)
        grind
    _ = 1 := h.symm

/-- **The field `K(α)`** generated by a root of a cubic without roots in `K`. -/
def CubicRoot.field (hΩ : IsField Ω) (C : CubicRoot K α) : Subfield Ω where
  carrier := C.space.carrier
  zero_mem := C.space.zero_mem
  one_mem := ⟨1, 0, 0, K.one_mem, K.zero_mem, K.zero_mem, by grind⟩
  add_mem := C.space.add_mem
  neg_mem := C.space.neg_mem
  mul_mem := C.space_mul
  inv_mem := C.space_inv hΩ

/-- `K ⊆ K(α)`. -/
theorem CubicRoot.le_field (hΩ : IsField Ω) (C : CubicRoot K α) : K.le (C.field hΩ) :=
  fun x hx => ⟨x, 0, 0, hx, K.zero_mem, K.zero_mem, by grind⟩

/-- `α ∈ K(α)`. -/
theorem CubicRoot.mem_field (hΩ : IsField Ω) (C : CubicRoot K α) : α ∈ C.field hΩ :=
  ⟨0, 1, 0, K.zero_mem, K.one_mem, K.zero_mem, by grind⟩

/-- `K(α)` lies in every subfield containing `K` and `α`. -/
theorem CubicRoot.field_le (hΩ : IsField Ω) (C : CubicRoot K α) {F : Subfield Ω} (hKF : K.le F) (hαF : α ∈ F) : (C.field hΩ).le F := by
  intro x ⟨u, v, w, hu, hv, hw, hx⟩
  rw [hx]
  exact F.add_mem (F.add_mem (hKF u hu) (F.mul_mem (hKF v hv) hαF))
    (F.mul_mem (hKF w hw) (F.mul_mem hαF hαF))

/-- **`[K(α) : K] = 3`** for a root `α` of a cubic with no root in `K`. -/
theorem CubicRoot.deg_field (hΩ : IsField Ω) (C : CubicRoot K α) :
    FiniteExt K (C.field hΩ) (C.le_field hΩ) ∧ deg K (C.field hΩ) (C.le_field hΩ) = 3 :=
  C.dim_space hΩ

end Cubic

/-! ## Rational root tests -/

section RationalRoots

/-- If `n³` is even then `n` is even. -/
theorem even_of_cube_even {n : Int} (h : n * n * n % 2 = 0) : n % 2 = 0 := by
  rcases Int.emod_two_eq n with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have : (2 * k + 1) * (2 * k + 1) * (2 * k + 1) = 2 * (4 * k * k * k + 6 * k * k + 3 * k) + 1 := by
      grind
    omega

/-- **`∛2` is irrational**: `a³ = 2 b³` has no integer solution with `b ≠ 0` (descent). -/
theorem no_int_cube_two : ∀ (n : Nat) (a b : Int), b.natAbs = n → b ≠ 0 → a * a * a ≠ 2 * (b * b * b) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a b hn hb h
    have ha : a % 2 = 0 := even_of_cube_even (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
    have h2 : b * b * b = 2 * (2 * (k * k * k)) := by grind
    have hb2 : b % 2 = 0 := even_of_cube_even (by omega)
    obtain ⟨l, rfl⟩ : ∃ l, b = 2 * l := ⟨b / 2, by omega⟩
    have h3 : k * k * k = 2 * (l * l * l) := by grind
    have hl : l ≠ 0 := by intro h; apply hb; rw [h]; rfl
    exact ih l.natAbs (by omega) k l rfl hl h3

/-- `a³ - 3 a c² - c³ = 0` has no integer solution with `c ≠ 0` (descent). -/
theorem no_int_trisect_aux : ∀ (n : Nat) (a c : Int), c.natAbs = n → c ≠ 0 →
    a * a * a - 3 * a * (c * c) - c * c * c ≠ 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a c hn hc h
    rcases Int.emod_two_eq a with ha | ha <;> rcases Int.emod_two_eq c with hc2 | hc2
    · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
      obtain ⟨l, rfl⟩ : ∃ l, c = 2 * l := ⟨c / 2, by omega⟩
      have hl : l ≠ 0 := by intro h; apply hc; rw [h]; rfl
      have : k * k * k - 3 * k * (l * l) - l * l * l = 0 := by grind
      exact ih l.natAbs (by omega) k l rfl hl this
    · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
      obtain ⟨l, rfl⟩ : ∃ l, c = 2 * l + 1 := ⟨c / 2, by omega⟩
      have : (2 * k) * (2 * k) * (2 * k) - 3 * (2 * k) * ((2 * l + 1) * (2 * l + 1)) -
          (2 * l + 1) * (2 * l + 1) * (2 * l + 1) =
          2 * (4 * k * k * k - 3 * k * (4 * l * l + 4 * l + 1) - (4 * l * l * l + 6 * l * l + 3 * l)) - 1 := by
        grind
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
      obtain ⟨l, rfl⟩ : ∃ l, c = 2 * l := ⟨c / 2, by omega⟩
      have : (2 * k + 1) * (2 * k + 1) * (2 * k + 1) - 3 * (2 * k + 1) * ((2 * l) * (2 * l)) -
          (2 * l) * (2 * l) * (2 * l) =
          2 * (4 * k * k * k + 6 * k * k + 3 * k - 3 * (2 * k + 1) * (2 * l * l) - 4 * l * l * l) + 1 := by
        grind
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
      obtain ⟨l, rfl⟩ : ∃ l, c = 2 * l + 1 := ⟨c / 2, by omega⟩
      have : (2 * k + 1) * (2 * k + 1) * (2 * k + 1) - 3 * (2 * k + 1) * ((2 * l + 1) * (2 * l + 1)) -
          (2 * l + 1) * (2 * l + 1) * (2 * l + 1) =
          2 * (4 * k * k * k + 6 * k * k + 3 * k - 3 * (2 * k + 1) * (2 * l * l + 2 * l) - 3 * k
            - (4 * l * l * l + 6 * l * l + 3 * l) - 1) + 1 := by
        grind
      omega

/-- **The rational root test for `8x³ - 6x - 1`**: `8a³ - 6ab² - b³ = 0` has no integer
solution with `b ≠ 0`. -/
theorem no_int_trisect (a b : Int) (hb : b ≠ 0) : 8 * (a * a * a) - 6 * a * (b * b) - b * b * b ≠ 0 := by
  intro h
  have e : b * b * b = 2 * (4 * (a * a * a) - 3 * (a * (b * b))) := by grind
  have hb2 : b % 2 = 0 := even_of_cube_even (by omega)
  obtain ⟨c, rfl⟩ : ∃ c, b = 2 * c := ⟨b / 2, by omega⟩
  have hc : c ≠ 0 := by intro h; apply hb; rw [h]; rfl
  exact no_int_trisect_aux c.natAbs a c rfl hc (by grind)

variable {Ω : Type u} [CommRing Ω]

/-- **`x³ - 2` has no root in `ℚ`.** -/
theorem cube_two_no_rat_root (hΩ : IsField Ω) (hc : CharZero Ω) :
    ∀ x, x ∈ ratField hΩ hc → (1 : Ω) * x * x * x + 0 * x * x + 0 * x + -((2 : Int) : Ω) ≠ 0 := by
  intro x ⟨a, b, hb, hx⟩ h
  apply no_int_cube_two b.natAbs a b rfl hb
  apply hc.cast_inj
  rw [Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul,
    Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, ← hx]
  grind

/-- **`8x³ - 6x - 1` has no root in `ℚ`.** -/
theorem trisect_no_rat_root (hΩ : IsField Ω) (hc : CharZero Ω) :
    ∀ x, x ∈ ratField hΩ hc →
      ((8 : Int) : Ω) * x * x * x + 0 * x * x + ((-6 : Int) : Ω) * x + ((-1 : Int) : Ω) ≠ 0 := by
  intro x ⟨a, b, hb, hx⟩ h
  apply no_int_trisect a b hb
  apply hc
  rw [Lean.Grind.Ring.intCast_sub, Lean.Grind.Ring.intCast_sub, Lean.Grind.Ring.intCast_mul,
    Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul,
    Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul,
    Lean.Grind.Ring.intCast_mul, ← hx]
  grind

end RationalRoots

end Foundations.Algebra
