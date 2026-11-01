import Foundations.Bridges.NatBridges

/-!
# Quotients inside the set-theoretic universe

Part II built the integers, the rationals and the reals in Lean's type theory:
`Z` is a *quotient type* of `Nat × Nat`, `Q` a quotient type of fractions. A set
theorist does the same thing differently: an integer *is* an equivalence class,
that is, a particular set of ordered pairs, and "the set of integers" is a
particular set of such classes, cut out of a power set by the axiom of
separation. This is the textbook construction of every set-theory course
(e.g. Enderton, *Elements of Set Theory*, ch. 5).

This file provides the general machinery, once and for all, for carrying out
such a construction inside Part I's ZF model and comparing the result with a
quotient type. We fix:

* a set `S` (the *representatives*, e.g. `ω × ω`) and a relation `R` between
  sets (the equivalence, e.g. `⟪a, b⟫ R ⟪c, d⟫ ↔ a +ω d = c +ω b`);
* the *class* of `p ∈ S`, `cls p = {q ∈ S | p R q}` — a set, by separation;
* the *quotient set* `{x ∈ 𝒫(S) | ∃ p ∈ S, x = cls p}` — a set, by power set and
  separation.

To compare with a quotient type `Quotient s` on some type `α`, we ask for an
*encoding* `enc : α → ZFSet` of the type-theoretic representatives as members of
`S`, hitting every member of `S` and translating `≈` into `R`. Then the quotient
type and the members of the quotient set are in canonical bijection, and
operations defined on representatives on either side correspond, as soon as they
correspond on representatives. All set-theoretic operations are defined
*without choosing representatives*: the sum of two classes `X`, `Y` is the set of
all `r ∈ S` equivalent to `p ⊕ q` for *some* `p ∈ X`, `q ∈ Y` — again just
separation.

We also need the two **projections** of a Kuratowski pair as set operations;
they are defined by union and separation, without any choice.
-/

namespace Foundations.Bridges

open Foundations.Sets Foundations.Sets.ZFSet

/-! ## Projections of Kuratowski pairs -/

/-- The **first projection** of a set: `⋃ {z ∈ ⋃ p | ∃ b, p = ⟪z, b⟫}`. For a pair
`⟪a, b⟫` the inner set is `{a}`, so the result is `a`. Defined by union and
separation only. -/
noncomputable def pfst (p : ZFSet) : ZFSet := ⋃₀ (sep (fun z => ∃ b, p = ⟪z, b⟫) (⋃₀ p))

/-- The **second projection** of a set: `⋃ {z ∈ ⋃ p | ∃ a, p = ⟪a, z⟫}`. -/
noncomputable def psnd (p : ZFSet) : ZFSet := ⋃₀ (sep (fun z => ∃ a, p = ⟪a, z⟫) (⋃₀ p))

/-- `pfst ⟪a, b⟫ = a`. -/
@[simp] theorem pfst_kpair (a b : ZFSet) : pfst ⟪a, b⟫ = a := by
  apply ext
  intro w
  simp only [pfst, mem_sUnion, mem_sep]
  constructor
  · rintro ⟨y, ⟨_, b', hb'⟩, hw⟩
    rw [(kpair_inj.1 hb').1]
    exact hw
  · intro hw
    refine ⟨a, ⟨⟨{a}, mem_kpair.2 (Or.inl rfl), mem_singleton.2 rfl⟩, b, rfl⟩, hw⟩

/-- `psnd ⟪a, b⟫ = b`. -/
@[simp] theorem psnd_kpair (a b : ZFSet) : psnd ⟪a, b⟫ = b := by
  apply ext
  intro w
  simp only [psnd, mem_sUnion, mem_sep]
  constructor
  · rintro ⟨y, ⟨_, a', ha'⟩, hw⟩
    rw [(kpair_inj.1 ha').2]
    exact hw
  · intro hw
    refine ⟨b, ⟨⟨{a, b}, mem_kpair.2 (Or.inr rfl), mem_pair.2 (Or.inr rfl)⟩, a, rfl⟩, hw⟩

/-! ## Set-theoretic models of quotient types -/

/-- A **set-theoretic model of a quotient type** `Quotient s`: a set `S` of
representatives with a relation `R`, and an encoding of the type-theoretic
representatives as members of `S` that is onto and turns `≈` into `R`; moreover
`R` only relates members of `S`. -/
structure ZFModel (α : Type) [s : Setoid α] where
  /-- The set of representatives. -/
  S : ZFSet
  /-- The equivalence relation between representatives (a relation between sets). -/
  R : ZFSet → ZFSet → Prop
  /-- Encoding of type-theoretic representatives as sets. -/
  enc : α → ZFSet
  /-- Encoded representatives lie in `S`. -/
  enc_mem : ∀ a, enc a ∈ S
  /-- Every member of `S` encodes some representative. -/
  enc_surj : ∀ p ∈ S, ∃ a, p = enc a
  /-- The encoding turns `≈` into `R`. -/
  rel_iff : ∀ a b, R (enc a) (enc b) ↔ a ≈ b
  /-- `R` only relates members of `S`. -/
  rel_mem : ∀ p q, R p q → p ∈ S ∧ q ∈ S

namespace ZFModel

variable {α : Type} [s : Setoid α] (M : ZFModel α)

/-- `R` is reflexive on `S`. -/
theorem R_refl {p : ZFSet} (hp : p ∈ M.S) : M.R p p := by
  obtain ⟨a, rfl⟩ := M.enc_surj p hp
  exact (M.rel_iff a a).2 (Setoid.refl a)

/-- `R` is symmetric. -/
theorem R_symm {p q : ZFSet} (h : M.R p q) : M.R q p := by
  obtain ⟨a, rfl⟩ := M.enc_surj p (M.rel_mem p q h).1
  obtain ⟨b, rfl⟩ := M.enc_surj q (M.rel_mem _ q h).2
  exact (M.rel_iff b a).2 (Setoid.symm ((M.rel_iff a b).1 h))

/-- `R` is transitive. -/
theorem R_trans {p q r : ZFSet} (h₁ : M.R p q) (h₂ : M.R q r) : M.R p r := by
  obtain ⟨a, rfl⟩ := M.enc_surj p (M.rel_mem p q h₁).1
  obtain ⟨b, rfl⟩ := M.enc_surj q (M.rel_mem _ q h₁).2
  obtain ⟨c, rfl⟩ := M.enc_surj r (M.rel_mem _ r h₂).2
  exact (M.rel_iff a c).2 (Setoid.trans ((M.rel_iff a b).1 h₁) ((M.rel_iff b c).1 h₂))

/-- The **equivalence class** of `p`: `{q ∈ S | p R q}`, by separation. -/
noncomputable def cls (p : ZFSet) : ZFSet := sep (fun q => M.R p q) M.S

/-- The **quotient set**: the classes, separated out of the power set of `S`. -/
noncomputable def carrier : ZFSet := sep (fun x => ∃ p ∈ M.S, x = M.cls p) (powerset M.S)

/-- Membership in a class. -/
theorem mem_cls {p q : ZFSet} : q ∈ M.cls p ↔ q ∈ M.S ∧ M.R p q := mem_sep

/-- Every representative lies in its own class. -/
theorem self_mem_cls {p : ZFSet} (hp : p ∈ M.S) : p ∈ M.cls p := M.mem_cls.2 ⟨hp, M.R_refl hp⟩

/-- Two classes are equal exactly when their representatives are related. -/
theorem cls_eq_iff {p q : ZFSet} (_hp : p ∈ M.S) (hq : q ∈ M.S) : M.cls p = M.cls q ↔ M.R p q := by
  constructor
  · intro h
    have : q ∈ M.cls p := h ▸ M.self_mem_cls hq
    exact (M.mem_cls.1 this).2
  · intro h
    apply ext
    intro r
    simp only [mem_cls]
    exact ⟨fun ⟨hr, h'⟩ => ⟨hr, M.R_trans (M.R_symm h) h'⟩,
      fun ⟨hr, h'⟩ => ⟨hr, M.R_trans h h'⟩⟩

/-- Membership in the quotient set: being the class of some representative. -/
theorem mem_carrier {x : ZFSet} : x ∈ M.carrier ↔ ∃ p ∈ M.S, x = M.cls p := by
  simp only [carrier, mem_sep, mem_powerset]
  constructor
  · exact fun h => h.2
  · rintro ⟨p, hp, rfl⟩
    exact ⟨sep_subset _ _, p, hp, rfl⟩

/-- The class of a representative is a member of the quotient set. -/
theorem cls_mem {p : ZFSet} (hp : p ∈ M.S) : M.cls p ∈ M.carrier := M.mem_carrier.2 ⟨p, hp, rfl⟩

/-- Classes of encoded representatives are equal iff the representatives are equivalent. -/
theorem cls_enc_eq_iff {a b : α} : M.cls (M.enc a) = M.cls (M.enc b) ↔ a ≈ b := by
  rw [M.cls_eq_iff (M.enc_mem a) (M.enc_mem b), M.rel_iff]

/-! ## The comparison map -/

/-- The **comparison map** from the quotient type to sets: the class of `a` goes to
the set-theoretic class of the encoding of `a`. -/
noncomputable def toSet : Quotient s → ZFSet :=
  Quotient.lift (fun a => M.cls (M.enc a)) (fun _ _ h => M.cls_enc_eq_iff.2 h)

/-- Computation rule for `toSet`. -/
theorem toSet_mk (a : α) : M.toSet (Quotient.mk s a) = M.cls (M.enc a) := rfl

/-- `toSet` lands in the quotient set. -/
theorem toSet_mem (x : Quotient s) : M.toSet x ∈ M.carrier := by
  induction x using Quotient.ind with
  | _ a => exact M.cls_mem (M.enc_mem a)

/-- `toSet` is injective. -/
theorem toSet_injective : Function.Injective M.toSet := by
  intro x y h
  induction x using Quotient.ind with
  | _ a =>
  induction y using Quotient.ind with
  | _ b => exact Quotient.sound (M.cls_enc_eq_iff.1 h)

/-- Every member of the quotient set is hit by `toSet`. -/
theorem toSet_surj {x : ZFSet} (hx : x ∈ M.carrier) : ∃ y, M.toSet y = x := by
  obtain ⟨p, hp, rfl⟩ := M.mem_carrier.1 hx
  obtain ⟨a, rfl⟩ := M.enc_surj p hp
  exact ⟨Quotient.mk s a, rfl⟩

/-- The **canonical bijection** between the quotient type and the members of the
quotient set. -/
noncomputable def bij : Bij (Quotient s) {x : ZFSet // x ∈ M.carrier} where
  toFun x := ⟨M.toSet x, M.toSet_mem x⟩
  invFun y := Classical.choose (M.toSet_surj y.2)
  left_inv x := M.toSet_injective (Classical.choose_spec (M.toSet_surj (M.toSet_mem x)))
  right_inv y := Subtype.ext (Classical.choose_spec (M.toSet_surj y.2))

/-- The forward map of `bij` is `toSet`. -/
theorem bij_val (x : Quotient s) : (M.bij.toFun x).1 = M.toSet x := rfl

/-! ## Lifting operations and relations to classes -/

/-- A binary operation on representatives, lifted to classes *without choosing
representatives*: `X ⊕ Y = {r ∈ S | ∃ p ∈ X, ∃ q ∈ Y, (p ⊕ q) R r}`. -/
noncomputable def lift2 (op : ZFSet → ZFSet → ZFSet) (X Y : ZFSet) : ZFSet :=
  sep (fun r => ∃ p ∈ X, ∃ q ∈ Y, M.R (op p q) r) M.S

/-- A unary operation on representatives, lifted to classes. -/
noncomputable def lift1 (op : ZFSet → ZFSet) (X : ZFSet) : ZFSet :=
  sep (fun r => ∃ p ∈ X, M.R (op p) r) M.S

/-- A relation on representatives, lifted to classes: some representatives are related. -/
def _root_.Foundations.Bridges.liftRel (L : ZFSet → ZFSet → Prop) (X Y : ZFSet) : Prop :=
  ∃ p ∈ X, ∃ q ∈ Y, L p q

/-- If a set operation `op` mirrors a type-level operation `f` on representatives, and
`f` respects `≈`, then the lifted operation computes classes correctly:
`cls a ⊕ cls b = cls (f a b)`. -/
theorem lift2_enc (op : ZFSet → ZFSet → ZFSet) (f : α → α → α)
    (hf : ∀ a a' b b', a ≈ a' → b ≈ b' → f a b ≈ f a' b')
    (hop : ∀ a b, op (M.enc a) (M.enc b) = M.enc (f a b)) (a b : α) :
    M.lift2 op (M.cls (M.enc a)) (M.cls (M.enc b)) = M.cls (M.enc (f a b)) := by
  apply ext
  intro r
  simp only [lift2, mem_sep, mem_cls]
  constructor
  · rintro ⟨hr, p, ⟨hp, hap⟩, q, ⟨hq, hbq⟩, hpq⟩
    obtain ⟨a', rfl⟩ := M.enc_surj p hp
    obtain ⟨b', rfl⟩ := M.enc_surj q hq
    rw [hop] at hpq
    have := (M.rel_iff _ _).2 (hf a a' b b' ((M.rel_iff _ _).1 hap) ((M.rel_iff _ _).1 hbq))
    exact ⟨hr, M.R_trans this hpq⟩
  · rintro ⟨hr, h⟩
    refine ⟨hr, M.enc a, ⟨M.enc_mem a, M.R_refl (M.enc_mem a)⟩, M.enc b,
      ⟨M.enc_mem b, M.R_refl (M.enc_mem b)⟩, ?_⟩
    rw [hop]
    exact h

/-- Unary version of `lift2_enc`. -/
theorem lift1_enc (op : ZFSet → ZFSet) (f : α → α) (hf : ∀ a a', a ≈ a' → f a ≈ f a')
    (hop : ∀ a, op (M.enc a) = M.enc (f a)) (a : α) :
    M.lift1 op (M.cls (M.enc a)) = M.cls (M.enc (f a)) := by
  apply ext
  intro r
  simp only [lift1, mem_sep, mem_cls]
  constructor
  · rintro ⟨hr, p, ⟨hp, hap⟩, hpr⟩
    obtain ⟨a', rfl⟩ := M.enc_surj p hp
    rw [hop] at hpr
    exact ⟨hr, M.R_trans ((M.rel_iff _ _).2 (hf a a' ((M.rel_iff _ _).1 hap))) hpr⟩
  · rintro ⟨hr, h⟩
    exact ⟨hr, M.enc a, ⟨M.enc_mem a, M.R_refl (M.enc_mem a)⟩, by rw [hop]; exact h⟩

/-- If a set relation `L` mirrors a type-level relation `P` on representatives, and `P`
respects `≈`, then the lifted relation holds between classes exactly when `P` holds. -/
theorem liftRel_enc (L : ZFSet → ZFSet → Prop) (P : α → α → Prop)
    (hP : ∀ a a' b b', a ≈ a' → b ≈ b' → (P a b ↔ P a' b'))
    (hL : ∀ a b, L (M.enc a) (M.enc b) ↔ P a b) (a b : α) :
    liftRel L (M.cls (M.enc a)) (M.cls (M.enc b)) ↔ P a b := by
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    obtain ⟨hp, hap⟩ := M.mem_cls.1 hp
    obtain ⟨hq, hbq⟩ := M.mem_cls.1 hq
    obtain ⟨a', rfl⟩ := M.enc_surj p hp
    obtain ⟨b', rfl⟩ := M.enc_surj q hq
    exact (hP a a' b b' ((M.rel_iff _ _).1 hap) ((M.rel_iff _ _).1 hbq)).2 ((hL _ _).1 hpq)
  · intro h
    exact ⟨M.enc a, M.self_mem_cls (M.enc_mem a), M.enc b, M.self_mem_cls (M.enc_mem b),
      (hL a b).2 h⟩

/-- The lifted operation transported along `toSet`. -/
theorem toSet_lift2 (op : ZFSet → ZFSet → ZFSet) (f : α → α → α)
    (hf : ∀ a a' b b', a ≈ a' → b ≈ b' → f a b ≈ f a' b')
    (hop : ∀ a b, op (M.enc a) (M.enc b) = M.enc (f a b)) (a b : α) :
    M.toSet (Quotient.mk s (f a b)) =
      M.lift2 op (M.toSet (Quotient.mk s a)) (M.toSet (Quotient.mk s b)) :=
  (M.lift2_enc op f hf hop a b).symm

end ZFModel

end Foundations.Bridges
