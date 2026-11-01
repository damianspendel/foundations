import Foundations.Algebra.Sylow

/-!
# Ring homomorphisms, the first isomorphism theorem for rings, and the Chinese remainder
theorem

The structuralist moral of the group-theory files — study the maps, not just the objects —
applies equally to rings. A **ring homomorphism** preserves addition, multiplication and
`1`; its kernel is an ideal (Dedekind's notion, introduced in `Ring.lean`), and Noether's
**first isomorphism theorem** holds verbatim: `R ⧸ ker f` is isomorphic to the image of
`f`. Every homomorphic image of a ring is a quotient ring.

The second half of the file proves the oldest theorem of this whole Part. Around the
fourth century CE the Chinese mathematician Sunzi asked for a number leaving remainders
2, 3 and 2 on division by 3, 5 and 7; the general method, perfected by Qin Jiushao in 1247,
is the **Chinese remainder theorem**: when `m` and `n` are coprime, a residue modulo `mn` is
the same thing as a pair of residues modulo `m` and modulo `n`. In structural language:
`ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ` *as rings*. The proof here is pleasingly economical: the reduction
map is an injective ring homomorphism (by coprimality) between two finite sets of the same
size `mn`, hence a bijection — the pigeonhole principle doing the work of Qin's
algorithm.
-/

namespace Foundations.Algebra

open Ring FiniteType

universe u v w

/-! ## Homomorphisms, subrings and isomorphisms -/

namespace RingHom

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- The identity ring homomorphism. -/
def id (R : Type u) [Ring R] : RingHom R R where
  toFun x := x
  map_add _ _ := rfl
  map_mul _ _ := rfl
  map_one := rfl

/-- The composite of two ring homomorphisms. -/
def comp (g : RingHom S T) (f : RingHom R S) : RingHom R T where
  toFun x := g.toFun (f.toFun x)
  map_add a b := by rw [f.map_add, g.map_add]
  map_mul a b := by rw [f.map_mul, g.map_mul]
  map_one := by rw [f.map_one, g.map_one]

/-- A ring homomorphism is injective iff its kernel is `{0}`. -/
theorem injective_iff_ker {R : Type u} [CommRing R] (f : RingHom R S) :
    (∀ a b, f.toFun a = f.toFun b → a = b) ↔ (∀ x, f.toFun x = 0 → x = 0) := by
  constructor
  · intro h x hx; exact h x 0 (by rw [hx, f.map_zero])
  · intro h a b hab
    have : f.toFun (-a + b) = 0 := by rw [f.map_add, f.map_neg, hab, neg_add_cancel]
    have h0 := h _ this
    have := congrArg (a + ·) h0
    simp only [add_neg_cancel_left, add_zero] at this
    exact this.symm

end RingHom

/-- **Subring.** A subset of a ring containing `0` and `1` and closed under addition,
negation and multiplication. -/
structure Subring (S : Type v) [CommRing S] where
  /-- The elements of the subring. -/
  carrier : S → Prop
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

namespace Subring

variable {S : Type v} [CommRing S]

/-- Membership in a subring. -/
instance : Membership S (Subring S) := ⟨fun A x => A.carrier x⟩

/-- A subring viewed as a type. -/
instance : CoeSort (Subring S) (Type v) := ⟨fun A => {x : S // x ∈ A}⟩

/-- **A subring is a ring** under the inherited operations. -/
instance toCommRing (A : Subring S) : CommRing A where
  add a b := ⟨a.1 + b.1, A.add_mem a.2 b.2⟩
  mul a b := ⟨a.1 * b.1, A.mul_mem a.2 b.2⟩
  neg a := ⟨-a.1, A.neg_mem a.2⟩
  zero := ⟨0, A.zero_mem⟩
  one := ⟨1, A.one_mem⟩
  add_assoc a b c := Subtype.ext (Ring.add_assoc a.1 b.1 c.1)
  add_comm a b := Subtype.ext (Ring.add_comm a.1 b.1)
  zero_add a := Subtype.ext (Ring.zero_add a.1)
  neg_add_cancel a := Subtype.ext (Ring.neg_add_cancel a.1)
  mul_assoc a b c := Subtype.ext (Ring.mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (Ring.one_mul a.1)
  mul_one a := Subtype.ext (Ring.mul_one a.1)
  left_distrib a b c := Subtype.ext (Ring.left_distrib a.1 b.1 c.1)
  right_distrib a b c := Subtype.ext (Ring.right_distrib a.1 b.1 c.1)
  mul_comm a b := Subtype.ext (CommRing.mul_comm a.1 b.1)

end Subring

/-- The **image** of a ring homomorphism is a subring of the codomain. -/
def RingHom.range {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : RingHom R S) :
    Subring S where
  carrier y := ∃ x, f.toFun x = y
  zero_mem := ⟨0, f.map_zero⟩
  one_mem := ⟨1, f.map_one⟩
  add_mem := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by rw [f.map_add, hx, hy]⟩
  neg_mem := fun ⟨x, hx⟩ => ⟨-x, by rw [f.map_neg, hx]⟩
  mul_mem := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, by rw [f.map_mul, hx, hy]⟩

/-- **Ring isomorphism.** A ring homomorphism with a two-sided inverse function. -/
structure RingIso (R : Type u) (S : Type v) [Ring R] [Ring S] extends RingHom R S where
  /-- The inverse function. -/
  invFun : S → R
  /-- `invFun` undoes `toFun`. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun` undoes `invFun`. -/
  right_inv : ∀ y, toFun (invFun y) = y

/-- Notation `R ≃+* S` for ring isomorphisms. -/
scoped infix:25 " ≃+* " => RingIso

namespace RingIso

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- **Bijective ring homomorphisms are isomorphisms** (the inverse is chosen classically). -/
noncomputable def ofBijective (f : RingHom R S) (inj : ∀ a b, f.toFun a = f.toFun b → a = b)
    (surj : ∀ y, ∃ x, f.toFun x = y) : R ≃+* S :=
  { f with
    invFun := fun y => Classical.choose (surj y)
    left_inv := fun x => inj _ _ (Classical.choose_spec (surj (f.toFun x)))
    right_inv := fun y => Classical.choose_spec (surj y) }

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
def symm (e : R ≃+* S) : S ≃+* R where
  toFun := e.invFun
  map_add a b := by
    have h := congrArg e.invFun (show e.toFun (e.invFun a + e.invFun b) = a + b by
      rw [e.map_add, e.right_inv, e.right_inv])
    rw [e.left_inv] at h; exact h.symm
  map_mul a b := by
    have h := congrArg e.invFun (show e.toFun (e.invFun a * e.invFun b) = a * b by
      rw [e.map_mul, e.right_inv, e.right_inv])
    rw [e.left_inv] at h; exact h.symm
  map_one := by
    have h := congrArg e.invFun e.map_one
    rw [e.left_inv] at h; exact h.symm
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

end RingIso

/-! ## The first isomorphism theorem -/

namespace QuotientRing

variable {R : Type u} [CommRing R] {I : Ideal R} {S : Type v} [CommRing S]

/-- **Universal property of the quotient ring.** A ring homomorphism vanishing on `I`
factors through `R ⧸ I`. -/
def lift (f : RingHom R S) (hf : ∀ x, x ∈ I → f.toFun x = 0) : RingHom (QuotientRing I) S where
  toFun := Quotient.lift f.toFun (fun a b (h : -a + b ∈ I) => by
    have := hf _ h
    rw [f.map_add, f.map_neg] at this
    have h2 := congrArg (f.toFun a + ·) this
    simp only [add_neg_cancel_left, add_zero] at h2
    exact h2.symm)
  map_add a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact f.map_add _ _
  map_mul a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact f.map_mul _ _
  map_one := f.map_one

/-- The lift agrees with `f` on representatives. -/
theorem lift_mk (f : RingHom R S) (hf : ∀ x, x ∈ I → f.toFun x = 0) (a : R) :
    (lift f hf).toFun (mk I a) = f.toFun a := rfl

/-- **The isomorphism principle for rings.** A surjective ring homomorphism whose kernel is
exactly `I` induces an isomorphism `R ⧸ I ≃+* S`. -/
noncomputable def isoOfSurjective (f : RingHom R S) (hker : ∀ x, x ∈ I ↔ f.toFun x = 0)
    (surj : ∀ y, ∃ x, f.toFun x = y) : QuotientRing I ≃+* S :=
  RingIso.ofBijective (lift f fun x hx => (hker x).1 hx)
    (by
      intro p q
      induction p using Quotient.ind with | _ a => ?_
      induction q using Quotient.ind with | _ b => ?_
      intro h
      apply Quotient.sound
      show -a + b ∈ I
      rw [hker, f.map_add, f.map_neg]
      have h' : f.toFun a = f.toFun b := h
      rw [h', neg_add_cancel])
    (fun y => by
      obtain ⟨x, hx⟩ := surj y
      exact ⟨mk I x, hx⟩)

end QuotientRing

/-- **First isomorphism theorem for rings.** For a ring homomorphism `f : R → S` between
commutative rings, `R ⧸ ker f ≃+* image f`, via `a + ker f ↦ f a`. -/
noncomputable def ringFirstIsoTheorem {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : RingHom R S) : QuotientRing f.ker ≃+* f.range :=
  QuotientRing.isoOfSurjective (S := f.range)
    { toFun := fun x => ⟨f.toFun x, x, rfl⟩
      map_add := fun a b => Subtype.ext (f.map_add a b)
      map_mul := fun a b => Subtype.ext (f.map_mul a b)
      map_one := Subtype.ext f.map_one }
    (fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
    (fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩)

/-- The first isomorphism theorem sends the class of `a` to `f a`. -/
theorem ringFirstIsoTheorem_mk {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : RingHom R S) (a : R) :
    ((ringFirstIsoTheorem f).toFun (QuotientRing.mk f.ker a)).1 = f.toFun a := rfl

/-- **First isomorphism theorem, surjective form.** A surjective ring homomorphism exhibits
its codomain as a quotient: `R ⧸ ker f ≃+* S`. -/
noncomputable def ringFirstIsoTheorem' {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : RingHom R S) (surj : ∀ y, ∃ x, f.toFun x = y) : QuotientRing f.ker ≃+* S :=
  QuotientRing.isoOfSurjective f (fun _ => Iff.rfl) surj

/-! ## Products of rings -/

/-- **Product ring.** `R × S` is a commutative ring under componentwise operations. -/
instance prodCommRing {R : Type u} {S : Type v} [CommRing R] [CommRing S] : CommRing (R × S) where
  add a b := (a.1 + b.1, a.2 + b.2)
  mul a b := (a.1 * b.1, a.2 * b.2)
  neg a := (-a.1, -a.2)
  zero := (0, 0)
  one := (1, 1)
  add_assoc _ _ _ := Prod.ext (Ring.add_assoc _ _ _) (Ring.add_assoc _ _ _)
  add_comm _ _ := Prod.ext (Ring.add_comm _ _) (Ring.add_comm _ _)
  zero_add _ := Prod.ext (Ring.zero_add _) (Ring.zero_add _)
  neg_add_cancel _ := Prod.ext (Ring.neg_add_cancel _) (Ring.neg_add_cancel _)
  mul_assoc _ _ _ := Prod.ext (Ring.mul_assoc _ _ _) (Ring.mul_assoc _ _ _)
  one_mul _ := Prod.ext (Ring.one_mul _) (Ring.one_mul _)
  mul_one _ := Prod.ext (Ring.mul_one _) (Ring.mul_one _)
  left_distrib _ _ _ := Prod.ext (Ring.left_distrib _ _ _) (Ring.left_distrib _ _ _)
  right_distrib _ _ _ := Prod.ext (Ring.right_distrib _ _ _) (Ring.right_distrib _ _ _)
  mul_comm _ _ := Prod.ext (CommRing.mul_comm _ _) (CommRing.mul_comm _ _)

/-- **Products of finite types are finite**, with `|α × β| = |α| · |β|`. -/
instance FiniteType.instProd {α : Type u} {β : Type v} [FiniteType α] [FiniteType β] :
    FiniteType (α × β) where
  elems := (elems : List α).flatMap (fun a => (elems : List β).map (fun b => (a, b)))
  nodup := by
    apply nodup_flatMap nodup
    · intro a
      exact nodup_map_of_injective (fun b b' h => congrArg Prod.snd h) nodup
    · intro a a' hne x hx hx'
      rw [List.mem_map] at hx hx'
      obtain ⟨b, _, rfl⟩ := hx
      obtain ⟨b', _, hb'⟩ := hx'
      exact hne (congrArg Prod.fst hb').symm
  complete x := by
    rw [List.mem_flatMap]
    exact ⟨x.1, complete _, List.mem_map.2 ⟨x.2, complete _, rfl⟩⟩

/-- `|α × β| = |α| · |β|`. -/
theorem FiniteType.card_prod {α : Type u} {β : Type v} [FiniteType α] [FiniteType β] :
    card (α × β) = card α * card β := by
  show ((elems : List α).flatMap _).length = _
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [sum_map_const]; rfl

/-- **Injective maps between finite sets of the same size are surjective.** -/
theorem FiniteType.surjective_of_injective_card {α : Type u} {β : Type v} [FiniteType α]
    [FiniteType β] (f : α → β) (inj : ∀ a b, f a = f b → a = b) (hc : card α = card β) :
    ∀ y, ∃ x, f x = y := by
  have hL := nodup_map_of_injective inj (nodup (α := α))
  have h : count (fun y => y ∈ (elems : List α).map f) = card β := by
    rw [count_eq_length hL (fun _ => Iff.rfl), List.length_map]; exact hc
  intro y
  obtain ⟨x, _, hx⟩ := List.mem_map.1 (count_eq_card.1 h y)
  exact ⟨x, hx⟩

/-! ## The Chinese remainder theorem -/

section CRT

variable (m n : Nat) [NeZero m] [NeZero n]

/-- The value of the residue `Fin.ofNat k a`. -/
theorem fin_ofNat_val (k a : Nat) [NeZero k] : (Fin.ofNat k a).val = a % k := Fin.val_ofNat _ _

/-- The **reduction map** `ℤ/mnℤ → ℤ/mℤ × ℤ/nℤ`, `a ↦ (a mod m, a mod n)`, is a ring
homomorphism. -/
def crtHom : RingHom (Fin (m * n)) (Fin m × Fin n) where
  toFun a := (Fin.ofNat m a.val, Fin.ofNat n a.val)
  map_add a b := by
    apply Prod.ext <;> apply Fin.ext
    · show (Fin.ofNat m (a + b).val).val = (Fin.ofNat m a.val + Fin.ofNat m b.val).val
      rw [Fin.val_add, Fin.val_add, fin_ofNat_val, fin_ofNat_val, fin_ofNat_val,
        Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right m n), ← Nat.add_mod]
    · show (Fin.ofNat n (a + b).val).val = (Fin.ofNat n a.val + Fin.ofNat n b.val).val
      rw [Fin.val_add, Fin.val_add, fin_ofNat_val, fin_ofNat_val, fin_ofNat_val,
        Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left n m), ← Nat.add_mod]
  map_mul a b := by
    apply Prod.ext <;> apply Fin.ext
    · show (Fin.ofNat m (a * b).val).val = (Fin.ofNat m a.val * Fin.ofNat m b.val).val
      rw [Fin.val_mul, Fin.val_mul, fin_ofNat_val, fin_ofNat_val, fin_ofNat_val,
        Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right m n), ← Nat.mul_mod]
    · show (Fin.ofNat n (a * b).val).val = (Fin.ofNat n a.val * Fin.ofNat n b.val).val
      rw [Fin.val_mul, Fin.val_mul, fin_ofNat_val, fin_ofNat_val, fin_ofNat_val,
        Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left n m), ← Nat.mul_mod]
  map_one := by
    apply Prod.ext <;> apply Fin.ext
    · show (Fin.ofNat m (Fin.ofNat (m * n) 1).val).val = (Fin.ofNat m 1).val
      rw [fin_ofNat_val, fin_ofNat_val, fin_ofNat_val,
        Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right m n)]
    · show (Fin.ofNat n (Fin.ofNat (m * n) 1).val).val = (Fin.ofNat n 1).val
      rw [fin_ofNat_val, fin_ofNat_val, fin_ofNat_val,
        Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left n m)]

/-- For coprime `m`, `n`, the reduction map is injective: a number below `mn` is determined by
its remainders modulo `m` and `n`. -/
theorem crtHom_injective (h : Nat.Coprime m n) :
    ∀ a b, (crtHom m n).toFun a = (crtHom m n).toFun b → a = b := by
  intro a b hab
  have hm : a.val % m = b.val % m := by
    have := congrArg (fun p : Fin m × Fin n => p.1.val) hab
    simpa only [crtHom, fin_ofNat_val] using this
  have hn : a.val % n = b.val % n := by
    have := congrArg (fun p : Fin m × Fin n => p.2.val) hab
    simpa only [crtHom, fin_ofNat_val] using this
  have key : ∀ x y : Nat, x < m * n → y < m * n → x % m = y % m → x % n = y % n → x - y = 0 := by
    intro x y _ hx hxm hxn
    apply Nat.eq_zero_of_dvd_of_lt
    · exact h.mul_dvd_of_dvd_of_dvd
        (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxm))
        (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxn))
    · omega
  have e1 := key a.val b.val a.isLt b.isLt hm hn
  have e2 := key b.val a.val b.isLt a.isLt hm.symm hn.symm
  apply Fin.ext; omega

/-- **Chinese remainder theorem.** For coprime `m` and `n`,
`ℤ/mnℤ ≃+* ℤ/mℤ × ℤ/nℤ` as rings, via `a ↦ (a mod m, a mod n)`. -/
noncomputable def chineseRemainder (h : Nat.Coprime m n) : Fin (m * n) ≃+* Fin m × Fin n :=
  RingIso.ofBijective (crtHom m n) (crtHom_injective m n h)
    (surjective_of_injective_card _ (crtHom_injective m n h)
      (by rw [card_prod, card_fin, card_fin, card_fin]))

/-- **Chinese remainder theorem, elementary form.** If `m` and `n` are coprime, then for any
residues `a < m` and `b < n` there is a unique `x < mn` with `x ≡ a (mod m)` and
`x ≡ b (mod n)`. -/
theorem chinese_remainder_exists_unique (h : Nat.Coprime m n) (a b : Nat) (ha : a < m)
    (hb : b < n) : ∃ x, x < m * n ∧ x % m = a ∧ x % n = b ∧
      ∀ y, y < m * n → y % m = a → y % n = b → y = x := by
  obtain ⟨x, hx⟩ := surjective_of_injective_card _ (crtHom_injective m n h)
    (by rw [card_prod, card_fin, card_fin, card_fin]) (⟨a, ha⟩, ⟨b, hb⟩)
  have h1 := congrArg (fun p : Fin m × Fin n => p.1.val) hx
  have h2 := congrArg (fun p : Fin m × Fin n => p.2.val) hx
  simp only [crtHom, fin_ofNat_val] at h1 h2
  refine ⟨x.val, x.isLt, h1, h2, fun y hy hya hyb => ?_⟩
  have := crtHom_injective m n h ⟨y, hy⟩ x (by
    apply Prod.ext <;> apply Fin.ext
    · show y % m = x.val % m; rw [hya, h1]
    · show y % n = x.val % n; rw [hyb, h2])
  exact congrArg Fin.val this

/-- Sunzi's problem: the number `23` leaves remainders 2, 3, 2 on division by 3, 5, 7, and
it is the only such number below `105`. -/
example : 23 % 3 = 2 ∧ 23 % 5 = 3 ∧ 23 % 7 = 2 := by decide

end CRT

/-! ## `ℤ ⧸ (n)` is `Fin n`

Throughout this Part we have modelled `ℤ/nℤ` concretely as `Fin n` with arithmetic modulo
`n`. The first isomorphism theorem justifies this: reduction modulo `n` is a surjective ring
homomorphism `ℤ → Fin n` whose kernel is the principal ideal `(n)`, so the abstract quotient
ring `ℤ ⧸ (n)` is isomorphic to `Fin n`. -/

section IntMod

variable (n : Nat) [NeZero n]

/-- Two naturals with equal integer casts are equal. -/
theorem nat_eq_of_intCast_eq {x y : Nat} (h : (x : Int) = (y : Int)) : x = y := by omega

/-- **Reduction modulo `n`** as a ring homomorphism `ℤ → Fin n`. -/
def intReduce : RingHom Int (Fin n) where
  toFun a := ⟨(a % (n : Int)).toNat, by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have h0 := Int.emod_nonneg a (b := (n : Int)) (by omega)
    have h1 := Int.emod_lt_of_pos a (b := (n : Int)) (by omega)
    omega⟩
  map_add a b := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    apply Fin.ext
    show ((a + b) % (n : Int)).toNat = (((a % (n : Int)).toNat + (b % (n : Int)).toNat) % n)
    apply nat_eq_of_intCast_eq
    have h1 := Int.emod_nonneg (a + b) (b := (n : Int)) (by omega)
    have h2 := Int.emod_nonneg a (b := (n : Int)) (by omega)
    have h3 := Int.emod_nonneg b (b := (n : Int)) (by omega)
    rw [Int.toNat_of_nonneg h1, Int.natCast_emod, Int.natCast_add, Int.toNat_of_nonneg h2,
      Int.toNat_of_nonneg h3, ← Int.add_emod]
  map_mul a b := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    apply Fin.ext
    show ((a * b) % (n : Int)).toNat = (((a % (n : Int)).toNat * (b % (n : Int)).toNat) % n)
    apply nat_eq_of_intCast_eq
    have h1 := Int.emod_nonneg (a * b) (b := (n : Int)) (by omega)
    have h2 := Int.emod_nonneg a (b := (n : Int)) (by omega)
    have h3 := Int.emod_nonneg b (b := (n : Int)) (by omega)
    rw [Int.toNat_of_nonneg h1, Int.natCast_emod, Int.natCast_mul, Int.toNat_of_nonneg h2,
      Int.toNat_of_nonneg h3, ← Int.mul_emod]
  map_one := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    apply Fin.ext
    show ((1 : Int) % (n : Int)).toNat = (Fin.ofNat n 1).val
    rw [fin_ofNat_val]
    apply nat_eq_of_intCast_eq
    have h1 := Int.emod_nonneg 1 (b := (n : Int)) (by omega)
    rw [Int.toNat_of_nonneg h1, Int.natCast_emod]; rfl

/-- **`ℤ ⧸ (n) ≃+* Fin n`.** The quotient of the integers by the principal ideal `(n)` is
isomorphic to the ring of residues modulo `n` — justifying the model of `ℤ/nℤ` used
throughout. -/
noncomputable def intQuotientIso : QuotientRing (Ideal.span (n : Int)) ≃+* Fin n :=
  QuotientRing.isoOfSurjective (intReduce n)
    (by
      intro a
      have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      have h0 := Int.emod_nonneg a (b := (n : Int)) (by omega)
      show (∃ r, a = r * (n : Int)) ↔ (⟨(a % (n : Int)).toNat, _⟩ : Fin n) = Fin.ofNat n 0
      rw [Fin.ext_iff, fin_ofNat_val, Nat.zero_mod]
      show (∃ r, a = r * (n : Int)) ↔ (a % (n : Int)).toNat = 0
      constructor
      · intro ⟨r, hr⟩
        have : a % (n : Int) = 0 := Int.emod_eq_zero_of_dvd ⟨r, by rw [hr, Int.mul_comm]⟩
        rw [this]; rfl
      · intro h
        have h' : a % (n : Int) = 0 := by omega
        obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero h'
        exact ⟨c, by rw [hc, Int.mul_comm]⟩)
    (fun ⟨k, hk⟩ => ⟨(k : Int), by
      apply Fin.ext
      show ((k : Int) % (n : Int)).toNat = k
      rw [← Int.natCast_emod, Nat.mod_eq_of_lt hk]; rfl⟩)

end IntMod

end Foundations.Algebra
