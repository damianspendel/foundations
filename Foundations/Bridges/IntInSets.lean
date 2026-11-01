import Foundations.Bridges.ZFQuotient
import Foundations.Numbers.Int

/-!
# The integers as a set

Part II built the integers `Z` as a quotient *type*: an integer is the class of a
formal difference `a − b` of natural numbers. Here we carry out the same
construction *inside the ZF universe of Part I*, as a set theorist would:

* a formal difference is a Kuratowski pair `⟪a, b⟫` of von Neumann naturals,
  i.e. a member of the cartesian product `ω × ω`;
* two pairs are equivalent, `⟪a, b⟫ ~ ⟪c, d⟫`, when `a +ω d = c +ω b`, using the
  set-theoretic addition `+ω` defined by the recursion theorem;
* an integer is an equivalence class — a subset of `ω × ω` — and **the set ℤ** is
  the set of all classes, separated out of `𝒫(ω × ω)`;
* sum, product and negation of classes are defined *on representatives*, using the
  set-theoretic projections of pairs and `+ω`, `*ω`, then lifted to classes by
  separation; the order is `⟪a, b⟫ ≤ ⟪c, d⟫ ↔ a +ω d ⊆ c +ω b`.

Every ingredient here is a set built from `∅` by the ZF axioms: no type of
integers is presupposed. We then prove that this set-theoretic ℤ is *the same
structure* as Part II's `Z` (and hence, by Part II's bridge, as Lean's `Int`): the
comparison map `Z → ℤ_ZF` is a bijection onto the members of the set ℤ which
preserves `0`, `1`, `+`, `−`, `·` and `≤`.

So the integers do not merely have a model in set theory "in principle": the
model is constructed, and the identification is a theorem.
-/

namespace Foundations.Bridges

open Foundations.Sets Foundations.Sets.ZFSet Foundations.Numbers

/-! ## Pairs of von Neumann naturals -/

/-- The Kuratowski pair `⟪vn a, vn b⟫` of two von Neumann naturals. -/
noncomputable def npair (a b : Nat) : ZFSet := ⟪vn a, vn b⟫

/-- `npair` is injective in both arguments. -/
theorem npair_inj {a b c d : Nat} : npair a b = npair c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := kpair_inj.1 h
    exact ⟨vn_injective h₁, vn_injective h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The members of `ω × ω` are exactly the pairs `npair a b`. -/
theorem mem_prod_omega {p : ZFSet} : p ∈ prod ω ω ↔ ∃ a b, p = npair a b := by
  rw [mem_prod]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := mem_omega.1 hx
    obtain ⟨b, rfl⟩ := mem_omega.1 hy
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨vn a, vn_mem_omega a, vn b, vn_mem_omega b, rfl⟩

/-! ## The set-theoretic integers -/

/-- The **equivalence of formal differences**, stated purely set-theoretically:
`⟪a, b⟫ ~ ⟪c, d⟫` iff `a, b, c, d ∈ ω` and `a +ω d = c +ω b`. -/
def ZRel (p q : ZFSet) : Prop :=
  ∃ a b c d : ZFSet, a ∈ ω ∧ b ∈ ω ∧ c ∈ ω ∧ d ∈ ω ∧ p = ⟪a, b⟫ ∧ q = ⟪c, d⟫ ∧
    a +ω d = c +ω b

/-- `ZRel` in terms of Lean's natural numbers. -/
theorem zrel_iff {p q : ZFSet} :
    ZRel p q ↔ ∃ a b c d : Nat, p = npair a b ∧ q = npair c d ∧ a + d = c + b := by
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, rfl, rfl, h⟩
    obtain ⟨a, rfl⟩ := mem_omega.1 ha
    obtain ⟨b, rfl⟩ := mem_omega.1 hb
    obtain ⟨c, rfl⟩ := mem_omega.1 hc
    obtain ⟨d, rfl⟩ := mem_omega.1 hd
    rw [← vn_add, ← vn_add] at h
    exact ⟨a, b, c, d, rfl, rfl, vn_injective h⟩
  · rintro ⟨a, b, c, d, rfl, rfl, h⟩
    refine ⟨vn a, vn b, vn c, vn d, vn_mem_omega a, vn_mem_omega b, vn_mem_omega c,
      vn_mem_omega d, rfl, rfl, ?_⟩
    rw [← vn_add, ← vn_add, h]

/-- The ZF integers as a set-theoretic model of Part II's quotient type `Z`:
representatives `ω × ω`, relation `ZRel`, and encoding `(a, b) ↦ ⟪vn a, vn b⟫`. -/
noncomputable def ZModel : ZFModel (Nat × Nat) where
  S := prod ω ω
  R := ZRel
  enc p := npair p.1 p.2
  enc_mem p := mem_prod_omega.2 ⟨p.1, p.2, rfl⟩
  enc_surj p hp := by
    obtain ⟨a, b, rfl⟩ := mem_prod_omega.1 hp
    exact ⟨(a, b), rfl⟩
  rel_iff p q := by
    rw [zrel_iff, rel_iff]
    constructor
    · rintro ⟨a, b, c, d, h₁, h₂, h⟩
      obtain ⟨rfl, rfl⟩ := npair_inj.1 h₁
      obtain ⟨rfl, rfl⟩ := npair_inj.1 h₂
      exact h
    · intro h
      exact ⟨_, _, _, _, rfl, rfl, h⟩
  rel_mem p q h := by
    obtain ⟨a, b, c, d, rfl, rfl, _⟩ := zrel_iff.1 h
    exact ⟨mem_prod_omega.2 ⟨a, b, rfl⟩, mem_prod_omega.2 ⟨c, d, rfl⟩⟩

/-- **The set ℤ** of Zermelo–Fraenkel integers: the equivalence classes of `ω × ω`. -/
noncomputable def ZInt : ZFSet := ZModel.carrier

/-- Sum of representatives: `⟪a, b⟫ + ⟪c, d⟫ = ⟪a +ω c, b +ω d⟫`. -/
noncomputable def zaddP (p q : ZFSet) : ZFSet := ⟪pfst p +ω pfst q, psnd p +ω psnd q⟫

/-- Product of representatives: `⟪a, b⟫ · ⟪c, d⟫ = ⟪ac + bd, ad + bc⟫` (with `+ω`, `*ω`). -/
noncomputable def zmulP (p q : ZFSet) : ZFSet :=
  ⟪pfst p *ω pfst q +ω psnd p *ω psnd q, pfst p *ω psnd q +ω psnd p *ω pfst q⟫

/-- Negation of a representative: `−⟪a, b⟫ = ⟪b, a⟫`. -/
noncomputable def znegP (p : ZFSet) : ZFSet := ⟪psnd p, pfst p⟫

/-- Order of representatives: `⟪a, b⟫ ≤ ⟪c, d⟫ ↔ a +ω d ⊆ c +ω b`. -/
def zleP (p q : ZFSet) : Prop := pfst p +ω psnd q ⊆ pfst q +ω psnd p

/-- Addition of ZF integers (lifted to classes by separation). -/
noncomputable def zadd : ZFSet → ZFSet → ZFSet := ZModel.lift2 zaddP

/-- Multiplication of ZF integers. -/
noncomputable def zmul : ZFSet → ZFSet → ZFSet := ZModel.lift2 zmulP

/-- Negation of ZF integers. -/
noncomputable def zneg : ZFSet → ZFSet := ZModel.lift1 znegP

/-- The order on ZF integers. -/
def zle : ZFSet → ZFSet → Prop := liftRel zleP

/-- The ZF integer zero: the class of `⟪∅, ∅⟫`. -/
noncomputable def zzero : ZFSet := ZModel.cls ⟪∅, ∅⟫

/-- The ZF integer one: the class of `⟪{∅}, ∅⟫` (that is, `⟪vn 1, vn 0⟫`). -/
noncomputable def zone : ZFSet := ZModel.cls ⟪vn 1, ∅⟫

/-! ## The comparison with Part II -/

/-- The **comparison map** from Part II's integers to the ZF integers: the class of
`(a, b)` goes to the set-theoretic class of `⟪vn a, vn b⟫`. -/
noncomputable def zToSet (x : Z) : ZFSet := ZModel.toSet x

/-- Computation rule for `zToSet`. -/
theorem zToSet_mk (a b : Nat) : zToSet (Z.mk a b) = ZModel.cls (npair a b) := rfl

/-- The comparison map lands in the set ℤ. -/
theorem zToSet_mem (x : Z) : zToSet x ∈ ZInt := ZModel.toSet_mem x

/-- The comparison map is injective. -/
theorem zToSet_injective : Function.Injective zToSet := ZModel.toSet_injective

/-- Every member of the set ℤ comes from a Part II integer. -/
theorem zToSet_surj {x : ZFSet} (hx : x ∈ ZInt) : ∃ y : Z, zToSet y = x := ZModel.toSet_surj hx

/-- The comparison map preserves zero. -/
theorem zToSet_zero : zToSet 0 = zzero := rfl

/-- The comparison map preserves one. -/
theorem zToSet_one : zToSet 1 = zone := rfl

/-- Congruence for a binary operation on `Z`. -/
theorem Z_congr2 (op : Z → Z → Z) {x x' y y' : Z} (h₁ : x = x') (h₂ : y = y') :
    op x y = op x' y' := by rw [h₁, h₂]

/-- The comparison map preserves addition. -/
theorem zToSet_add (x y : Z) : zToSet (x + y) = zadd (zToSet x) (zToSet y) := by
  induction x using Z.ind with
  | _ a b =>
  induction y using Z.ind with
  | _ c d =>
  exact ZModel.toSet_lift2 zaddP (fun p q => (p.1 + q.1, p.2 + q.2))
    (fun p p' q q' h₁ h₂ => Z.mk_eq_mk.1 (Z_congr2 (· + ·)
      ((Z.mk_eq_mk (a := p.1) (b := p.2) (c := p'.1) (d := p'.2)).2 h₁)
      ((Z.mk_eq_mk (a := q.1) (b := q.2) (c := q'.1) (d := q'.2)).2 h₂)))
    (fun p q => by simp [ZModel, zaddP, npair, vn_add]) (a, b) (c, d)

/-- The comparison map preserves multiplication. -/
theorem zToSet_mul (x y : Z) : zToSet (x * y) = zmul (zToSet x) (zToSet y) := by
  induction x using Z.ind with
  | _ a b =>
  induction y using Z.ind with
  | _ c d =>
  exact ZModel.toSet_lift2 zmulP
    (fun p q => (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1))
    (fun p p' q q' h₁ h₂ => Z.mk_eq_mk.1 (Z_congr2 (· * ·)
      ((Z.mk_eq_mk (a := p.1) (b := p.2) (c := p'.1) (d := p'.2)).2 h₁)
      ((Z.mk_eq_mk (a := q.1) (b := q.2) (c := q'.1) (d := q'.2)).2 h₂)))
    (fun p q => by simp [ZModel, zmulP, npair, vn_add, vn_mul]) (a, b) (c, d)

/-- The comparison map preserves negation. -/
theorem zToSet_neg (x : Z) : zToSet (-x) = zneg (zToSet x) := by
  induction x using Z.ind with
  | _ a b =>
  exact (ZModel.lift1_enc znegP (fun p => (p.2, p.1))
    (fun p p' h => Z.mk_eq_mk.1 (congrArg (- ·)
      ((Z.mk_eq_mk (a := p.1) (b := p.2) (c := p'.1) (d := p'.2)).2 h)))
    (fun p => by simp [ZModel, znegP, npair]) (a, b)).symm

/-- The comparison map preserves and reflects the order. -/
theorem zToSet_le (x y : Z) : x ≤ y ↔ zle (zToSet x) (zToSet y) := by
  induction x using Z.ind with
  | _ a b =>
  induction y using Z.ind with
  | _ c d =>
  refine (ZModel.liftRel_enc zleP (fun p q => p.1 + q.2 ≤ q.1 + p.2) ?_ ?_ (a, b) (c, d)).symm
  · intro p p' q q' h₁ h₂
    simp only [rel_iff] at h₁ h₂
    omega
  · intro p q
    simp only [ZModel, zleP, npair, pfst_kpair, psnd_kpair, ← vn_add]
    exact vn_subset_vn_iff

/-- **The integers live in the set-theoretic universe.** The comparison map from
Part II's integers `Z` to the ZF set `ℤ` of equivalence classes of pairs in `ω × ω`
is a bijection onto the members of `ℤ` that preserves `0`, `1`, addition, negation,
multiplication and order — all of which are defined on the set side by the ZF
axioms alone (pairs, products, separation, power set, and `+ω`, `*ω`). -/
theorem int_in_sets :
    Bijective (fun x : Z => (⟨zToSet x, zToSet_mem x⟩ : {s : ZFSet // s ∈ ZInt})) ∧
    zToSet 0 = zzero ∧ zToSet 1 = zone ∧
    (∀ x y, zToSet (x + y) = zadd (zToSet x) (zToSet y)) ∧
    (∀ x, zToSet (-x) = zneg (zToSet x)) ∧
    (∀ x y, zToSet (x * y) = zmul (zToSet x) (zToSet y)) ∧
    (∀ x y, x ≤ y ↔ zle (zToSet x) (zToSet y)) :=
  ⟨ZModel.bij.bijective, rfl, rfl, zToSet_add, zToSet_neg, zToSet_mul, zToSet_le⟩

/-! ## Lean's integers inside the sets -/

/-- The ZF integer corresponding to a Lean integer, via Part II's `Z`. -/
noncomputable def intToSet (i : Int) : ZFSet := zToSet (Z.ofInt i)

/-- `Z.toInt` is injective. -/
theorem Z_toInt_inj {x y : Z} (h : Z.toInt x = Z.toInt y) : x = y := by
  rw [← Z.equivInt.left_inv x, ← Z.equivInt.left_inv y]
  exact congrArg Z.ofInt h

/-- `Z.toInt` undoes `Z.ofInt`. -/
theorem Z_toInt_ofInt (i : Int) : Z.toInt (Z.ofInt i) = i := Z.equivInt.right_inv i

/-- `ofInt` preserves addition. -/
theorem Z_ofInt_add (m n : Int) : Z.ofInt (m + n) = Z.ofInt m + Z.ofInt n :=
  Z_toInt_inj (by rw [Z.toInt_add, Z_toInt_ofInt, Z_toInt_ofInt, Z_toInt_ofInt])

/-- `ofInt` preserves multiplication. -/
theorem Z_ofInt_mul (m n : Int) : Z.ofInt (m * n) = Z.ofInt m * Z.ofInt n :=
  Z_toInt_inj (by rw [Z.toInt_mul, Z_toInt_ofInt, Z_toInt_ofInt, Z_toInt_ofInt])

/-- `ofInt` preserves negation. -/
theorem Z_ofInt_neg (m : Int) : Z.ofInt (-m) = -Z.ofInt m :=
  Z_toInt_inj (by rw [Z.toInt_neg, Z_toInt_ofInt, Z_toInt_ofInt])

/-- `ofInt` preserves and reflects the order. -/
theorem Z_ofInt_le (m n : Int) : Z.ofInt m ≤ Z.ofInt n ↔ m ≤ n := by
  rw [Z.toInt_le, Z_toInt_ofInt, Z_toInt_ofInt]

/-- `intToSet` preserves addition. -/
theorem intToSet_add (m n : Int) : intToSet (m + n) = zadd (intToSet m) (intToSet n) := by
  rw [intToSet, Z_ofInt_add, zToSet_add]; rfl

/-- `intToSet` preserves multiplication. -/
theorem intToSet_mul (m n : Int) : intToSet (m * n) = zmul (intToSet m) (intToSet n) := by
  rw [intToSet, Z_ofInt_mul, zToSet_mul]; rfl

/-- `intToSet` preserves negation. -/
theorem intToSet_neg (m : Int) : intToSet (-m) = zneg (intToSet m) := by
  rw [intToSet, Z_ofInt_neg, zToSet_neg]; rfl

/-- `intToSet` preserves and reflects the order. -/
theorem intToSet_le (m n : Int) : zle (intToSet m) (intToSet n) ↔ m ≤ n := by
  rw [intToSet, intToSet, ← zToSet_le, Z_ofInt_le]

/-- `intToSet` lands in ℤ. -/
theorem intToSet_mem (i : Int) : intToSet i ∈ ZInt := zToSet_mem _

/-- `intToSet` is injective. -/
theorem intToSet_injective : Function.Injective intToSet := fun m n h => by
  have := zToSet_injective h
  rw [← Z_toInt_ofInt m, ← Z_toInt_ofInt n, this]

/-- Every member of ℤ is `intToSet i` for some Lean integer `i`. -/
theorem intToSet_surj {x : ZFSet} (hx : x ∈ ZInt) : ∃ i, intToSet i = x := by
  obtain ⟨y, rfl⟩ := zToSet_surj hx
  exact ⟨Z.toInt y, congrArg zToSet (Z.equivInt.left_inv y)⟩

/-- A natural number, as a ZF integer, is the class of `⟪vn k, ∅⟫`. -/
theorem intToSet_natCast (k : Nat) : intToSet (k : Int) = ZModel.cls ⟪vn k, ∅⟫ := by
  have : Z.ofInt (k : Int) = Z.mk k 0 := by
    rw [Z.ofInt, Z.mk_eq_mk]; omega
  rw [intToSet, this, zToSet_mk]; rfl

/-- **Lean's `Int` inside the sets.** The composite `Int → Z → ℤ_ZF` is a bijection
onto the members of the set `ℤ`, preserving addition, negation, multiplication and
order. -/
theorem lean_int_in_sets :
    Bijective (fun i : Int => (⟨intToSet i, intToSet_mem i⟩ : {s : ZFSet // s ∈ ZInt})) ∧
    (∀ m n, intToSet (m + n) = zadd (intToSet m) (intToSet n)) ∧
    (∀ m, intToSet (-m) = zneg (intToSet m)) ∧
    (∀ m n, intToSet (m * n) = zmul (intToSet m) (intToSet n)) ∧
    (∀ m n, zle (intToSet m) (intToSet n) ↔ m ≤ n) :=
  ⟨⟨fun _ _ h => intToSet_injective (congrArg Subtype.val h),
    fun ⟨_, hx⟩ => let ⟨i, hi⟩ := intToSet_surj hx; ⟨i, Subtype.ext hi⟩⟩,
   intToSet_add, intToSet_neg, intToSet_mul, intToSet_le⟩

end Foundations.Bridges
