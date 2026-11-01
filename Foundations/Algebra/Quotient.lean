import Foundations.Algebra.Cayley

/-!
# Normal subgroups, quotient groups and the isomorphism theorems

Galois discovered that the solvability of an equation by radicals depends on whether its
group can be broken down in a particular way, and the key notion in that analysis — he
called it a *proper decomposition* — is what we now call a **normal subgroup**: a subgroup
`N` such that `g N g⁻¹ = N` for every `g`. For such `N`, the cosets of `N` can themselves
be multiplied, `(aN)(bN) = (ab)N`, and form a new group, the **quotient group** `G ⧸ N`.

The quotient construction is an instance of a pattern that runs through all of modern
mathematics and that philosophers will recognise as *definition by abstraction*: we
declare `a` and `b` equivalent when `a⁻¹ * b ∈ N`, and pass to the equivalence classes —
exactly as Frege obtained directions from parallel lines, or numbers from equinumerous
concepts. Lean supplies this operation primitively, as `Quotient`.

The **isomorphism theorems**, distilled by Emmy Noether in the 1920s from work of Dedekind,
Hölder and others, describe how quotients interact with homomorphisms:

* **First isomorphism theorem.** For any homomorphism `f : G →* H`,
  `G ⧸ ker f ≃* image f`. Every homomorphic image is a quotient, and vice versa.
* **Second isomorphism theorem.** For a subgroup `H` and normal subgroup `N`,
  `H ⧸ (H ∩ N) ≃* HN ⧸ N`.
* **Third isomorphism theorem.** For normal subgroups `N ≤ M`,
  `(G ⧸ N) ⧸ (M ⧸ N) ≃* G ⧸ M`.

All three follow from a single principle proved here first: a surjective homomorphism
whose kernel is exactly `N` induces an isomorphism out of `G ⧸ N`. Noether's insight was
that the theorems are really about the homomorphisms, not about the elements — the
structuralist turn in miniature.
-/

namespace Foundations.Algebra

open Group

universe u v w

variable {G : Type u} [Group G]

/-! ## Normal subgroups -/

/-- **Normal subgroup.** A subgroup `N` is normal if it is closed under conjugation: whenever
`n ∈ N`, every conjugate `g * n * g⁻¹` is in `N`. -/
class Subgroup.Normal (N : Subgroup G) : Prop where
  /-- Closure under conjugation. -/
  conj_mem : ∀ n, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N

namespace Subgroup

/-- One subgroup is contained in another. -/
def le (H K : Subgroup G) : Prop := ∀ x, x ∈ H → x ∈ K

/-- In a commutative group every subgroup is normal. -/
theorem normal_of_comm {G : Type u} [CommGroup G] (N : Subgroup G) : N.Normal :=
  ⟨fun n hn g => by rw [CommGroup.mul_comm g n, mul_inv_cancel_right]; exact hn⟩

/-- The trivial subgroup is normal. -/
instance normal_bot : (bot : Subgroup G).Normal :=
  ⟨fun n hn g => by
    show g * n * g⁻¹ = 1
    rw [show n = 1 from hn, mul_one, mul_inv_cancel]⟩

/-- The whole group is a normal subgroup of itself. -/
instance normal_top : (top : Subgroup G).Normal := ⟨fun _ _ _ => trivial⟩

/-- The **preimage** of a subgroup under a homomorphism is a subgroup. -/
def comap {K : Type v} [Group K] (f : G →* K) (N : Subgroup K) : Subgroup G where
  carrier x := f x ∈ N
  one_mem := by show f 1 ∈ N; rw [f.map_one]; exact N.one_mem
  mul_mem := by intro a b ha hb; show f (a * b) ∈ N; rw [f.map_mul']; exact N.mul_mem ha hb
  inv_mem := by intro a ha; show f a⁻¹ ∈ N; rw [f.map_inv]; exact N.inv_mem ha

/-- The preimage of a normal subgroup is normal. -/
instance comap_normal {K : Type v} [Group K] (f : G →* K) (N : Subgroup K) [hN : N.Normal] :
    (comap f N).Normal :=
  ⟨fun n hn g => by
    show f (g * n * g⁻¹) ∈ N
    rw [f.map_mul', f.map_mul', f.map_inv]
    exact hN.conj_mem _ hn _⟩

/-- The **image** of a subgroup under a homomorphism is a subgroup. -/
def map {K : Type v} [Group K] (f : G →* K) (M : Subgroup G) : Subgroup K where
  carrier y := ∃ x, x ∈ M ∧ f x = y
  one_mem := ⟨1, M.one_mem, f.map_one⟩
  mul_mem := by
    intro a b ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩
    exact ⟨x * y, M.mul_mem hx hy, by rw [f.map_mul', hxa, hyb]⟩
  inv_mem := by
    intro a ⟨x, hx, hxa⟩
    exact ⟨x⁻¹, M.inv_mem hx, by rw [f.map_inv, hxa]⟩

/-- The image of a normal subgroup under a surjective homomorphism is normal. -/
theorem map_normal {K : Type v} [Group K] (f : G →* K) (surj : ∀ y, ∃ x, f x = y)
    (M : Subgroup G) [hM : M.Normal] : (map f M).Normal :=
  ⟨fun n ⟨x, hx, hxn⟩ g => by
    obtain ⟨a, rfl⟩ := surj g
    exact ⟨a * x * a⁻¹, hM.conj_mem x hx a, by rw [f.map_mul', f.map_mul', f.map_inv, hxn]⟩⟩

end Subgroup

/-- **Kernels are normal.** The kernel of any homomorphism is a normal subgroup. -/
instance Hom.ker_normal {K : Type v} [Group K] (f : G →* K) : f.ker.Normal :=
  ⟨fun n hn g => by
    show f (g * n * g⁻¹) = 1
    rw [f.map_mul', f.map_mul', show f n = 1 from hn, mul_one, ← f.map_mul', mul_inv_cancel,
      f.map_one]⟩

/-! ## The quotient group -/

/-- The relation "`a` and `b` lie in the same left coset of `N`", i.e. `a⁻¹ * b ∈ N`. It is an
equivalence relation. -/
def cosetSetoid (N : Subgroup G) : Setoid G where
  r a b := a⁻¹ * b ∈ N
  iseqv := {
    refl := fun a => by show a⁻¹ * a ∈ N; rw [inv_mul_cancel]; exact N.one_mem
    symm := fun {a b} h => by
      show b⁻¹ * a ∈ N
      have := N.inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
    trans := fun {a b c} h1 h2 => by
      show a⁻¹ * c ∈ N
      have := N.mul_mem h1 h2
      rwa [mul_assoc, mul_inv_cancel_left] at this }

/-- **Quotient group.** `G ⧸ N` is the type of left cosets of `N`, obtained by abstraction
from the relation `a⁻¹ * b ∈ N`. -/
def QuotientGroup (N : Subgroup G) : Type u := Quotient (cosetSetoid N)

/-- Notation `G ⧸ N` for the quotient of `G` by `N`. -/
scoped notation:35 G " ⧸ " N:34 => @QuotientGroup G _ N

namespace QuotientGroup

variable (N : Subgroup G)

/-- The coset `aN` of an element `a`. -/
def mk (a : G) : G ⧸ N := Quotient.mk (cosetSetoid N) a

variable {N}

/-- **When are two cosets equal?** `aN = bN` iff `a⁻¹ * b ∈ N`. -/
theorem mk_eq_mk {a b : G} : mk N a = mk N b ↔ a⁻¹ * b ∈ N :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- Every coset is the coset of some element. -/
theorem mk_surjective (q : G ⧸ N) : ∃ a, mk N a = q := Quotient.exists_rep q

/-- Induction principle: to prove something for all cosets, prove it for all `mk N a`. -/
theorem ind {P : G ⧸ N → Prop} (h : ∀ a, P (mk N a)) (q : G ⧸ N) : P q :=
  Quotient.ind h q

variable [hN : N.Normal]

/-- Multiplication of cosets is well defined when `N` is normal. -/
theorem mul_wd {a a' b b' : G} (ha : a⁻¹ * a' ∈ N) (hb : b⁻¹ * b' ∈ N) :
    (a * b)⁻¹ * (a' * b') ∈ N := by
  have h1 : b⁻¹ * (a⁻¹ * a') * b⁻¹⁻¹ ∈ N := hN.conj_mem _ ha _
  have := N.mul_mem h1 hb
  have e : (a * b)⁻¹ * (a' * b') = b⁻¹ * (a⁻¹ * a') * b⁻¹⁻¹ * (b⁻¹ * b') := by
    rw [inv_inv, mul_inv_rev]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e]; exact this

/-- Inversion of cosets is well defined when `N` is normal. -/
theorem inv_wd {a a' : G} (ha : a⁻¹ * a' ∈ N) : a⁻¹⁻¹ * a'⁻¹ ∈ N := by
  have := hN.conj_mem _ (N.inv_mem ha) a
  have e : a⁻¹⁻¹ * a'⁻¹ = a * (a⁻¹ * a')⁻¹ * a⁻¹ := by
    rw [inv_inv, mul_inv_rev, inv_inv]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [e]; exact this

/-- **The quotient group.** For a normal subgroup `N`, the cosets form a group under
`(aN)(bN) = (ab)N`, with identity `N = 1N` and `(aN)⁻¹ = a⁻¹N`. -/
instance : Group (G ⧸ N) where
  mul := Quotient.lift₂ (fun a b => mk N (a * b))
    (fun _ _ _ _ ha hb => Quotient.sound (mul_wd ha hb))
  one := mk N 1
  inv := Quotient.lift (fun a => mk N a⁻¹) (fun _ _ ha => Quotient.sound (inv_wd ha))
  mul_assoc a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Group.mul_assoc _ _ _)
  one_mul a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Group.one_mul _)
  inv_mul_cancel a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Group.inv_mul_cancel _)

/-- Cosets multiply representative-wise: `(aN)(bN) = (ab)N`. -/
@[simp] theorem mk_mul (a b : G) : mk N a * mk N b = mk N (a * b) := rfl

/-- The identity coset is `N = 1N`. -/
@[simp] theorem mk_one : mk N (1 : G) = 1 := rfl

/-- `(aN)⁻¹ = a⁻¹N`. -/
@[simp] theorem mk_inv (a : G) : (mk N a)⁻¹ = mk N a⁻¹ := rfl

/-- `aN` is the identity coset iff `a ∈ N`. -/
theorem mk_eq_one {a : G} : mk N a = 1 ↔ a ∈ N := by
  rw [← mk_one, mk_eq_mk, mul_one, N.inv_mem_iff]

variable (N)

/-- The **canonical projection** `G →* G ⧸ N`, `a ↦ aN`. -/
def proj : G →* G ⧸ N where
  toFun := mk N
  map_mul _ _ := rfl

/-- **Every normal subgroup is a kernel**: `N` is the kernel of the projection `G →* G ⧸ N`. -/
theorem ker_proj (a : G) : a ∈ (proj N).ker ↔ a ∈ N := by
  show mk N a = 1 ↔ a ∈ N; exact mk_eq_one

/-- The projection is surjective. -/
theorem proj_surjective (q : G ⧸ N) : ∃ a, proj N a = q := Quotient.exists_rep q

variable {N}

/-- **Universal property of the quotient.** A homomorphism `f : G →* K` that sends every
element of `N` to `1` factors through `G ⧸ N`: `f̄ (aN) = f a`. -/
def lift {K : Type v} [Group K] (f : G →* K) (hf : ∀ x, x ∈ N → f x = 1) : G ⧸ N →* K where
  toFun := Quotient.lift f.toFun (fun a b (h : a⁻¹ * b ∈ N) => by
    have := hf _ h
    rw [f.map_mul', f.map_inv, inv_mul_eq_one] at this
    exact this)
  map_mul a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact f.map_mul _ _

/-- The lift agrees with `f` on representatives. -/
@[simp] theorem lift_mk {K : Type v} [Group K] (f : G →* K) (hf : ∀ x, x ∈ N → f x = 1)
    (a : G) : lift f hf (mk N a) = f a := rfl

/-- **The isomorphism principle.** If `f : G →* K` is surjective and its kernel is exactly
`N`, then `f` induces an isomorphism `G ⧸ N ≃* K`. All three isomorphism theorems are
instances of this. -/
noncomputable def isoOfSurjective {K : Type v} [Group K] (f : G →* K)
    (hker : ∀ x, x ∈ N ↔ f x = 1) (surj : ∀ y, ∃ x, f x = y) : G ⧸ N ≃* K :=
  Iso.ofBijective (lift f fun x hx => (hker x).1 hx)
    (by
      intro p q
      induction p using Quotient.ind
      induction q using Quotient.ind
      intro h
      apply Quotient.sound
      show _ ∈ N
      rw [hker, f.map_mul', f.map_inv, inv_mul_eq_one]
      exact h)
    (fun y => by
      obtain ⟨x, hx⟩ := surj y
      exact ⟨mk N x, hx⟩)

/-- The isomorphism of `isoOfSurjective` sends `aN` to `f a`. -/
theorem isoOfSurjective_mk {K : Type v} [Group K] (f : G →* K)
    (hker : ∀ x, x ∈ N ↔ f x = 1) (surj : ∀ y, ∃ x, f x = y) (a : G) :
    isoOfSurjective f hker surj (mk N a) = f a := rfl

end QuotientGroup

open QuotientGroup

/-! ## The isomorphism theorems -/

/-- **First isomorphism theorem.** For any homomorphism `f : G →* K`, the quotient of `G` by
the kernel of `f` is isomorphic to the image of `f`: `G ⧸ ker f ≃* range f`, via
`a · ker f ↦ f a`. -/
noncomputable def firstIsoTheorem {K : Type v} [Group K] (f : G →* K) :
    G ⧸ f.ker ≃* f.range :=
  isoOfSurjective f.rangeRestrict
    (fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
    (fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩)

/-- The first isomorphism theorem's isomorphism sends the coset of `a` to `f a`. -/
theorem firstIsoTheorem_mk {K : Type v} [Group K] (f : G →* K) (a : G) :
    (firstIsoTheorem f (mk f.ker a)).1 = f a := rfl

/-- **First isomorphism theorem, surjective form.** A surjective homomorphism `f : G →* K`
exhibits `K` as a quotient: `G ⧸ ker f ≃* K`. -/
noncomputable def firstIsoTheorem' {K : Type v} [Group K] (f : G →* K)
    (surj : ∀ y, ∃ x, f x = y) : G ⧸ f.ker ≃* K :=
  isoOfSurjective f (fun _ => Iff.rfl) surj

section Second

variable (H N : Subgroup G) [hN : N.Normal]

/-- The **product** `HN = {h * n | h ∈ H, n ∈ N}` of a subgroup and a normal subgroup is a
subgroup. -/
def Subgroup.prodNormal : Subgroup G where
  carrier x := ∃ h, h ∈ H ∧ ∃ n, n ∈ N ∧ h * n = x
  one_mem := ⟨1, H.one_mem, 1, N.one_mem, one_mul 1⟩
  mul_mem := by
    intro a b ⟨h, hh, n, hn, ha⟩ ⟨h', hh', n', hn', hb⟩
    refine ⟨h * h', H.mul_mem hh hh', h'⁻¹ * n * h'⁻¹⁻¹ * n',
      N.mul_mem (hN.conj_mem n hn h'⁻¹) hn', ?_⟩
    rw [← ha, ← hb, inv_inv]
    simp only [mul_assoc, mul_inv_cancel_left]
  inv_mem := by
    intro a ⟨h, hh, n, hn, ha⟩
    refine ⟨h⁻¹, H.inv_mem hh, h * n⁻¹ * h⁻¹, hN.conj_mem _ (N.inv_mem hn) h, ?_⟩
    rw [← ha, mul_inv_rev, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]

/-- `H` sits inside `HN`. -/
def Subgroup.inclProdNormal : H →* Subgroup.prodNormal H N where
  toFun h := ⟨h.1, h.1, h.2, 1, N.one_mem, mul_one _⟩
  map_mul _ _ := rfl

/-- **Second isomorphism theorem** (the "diamond" isomorphism). For a subgroup `H` and a
normal subgroup `N` of `G`, `H ⧸ (H ∩ N) ≃* HN ⧸ N`. Here `H ∩ N` and `N` are viewed as
(normal) subgroups of `H` and of `HN` respectively, via preimages under the inclusions. -/
noncomputable def secondIsoTheorem :
    H ⧸ Subgroup.comap (Hom.subtype H) N ≃*
      Subgroup.prodNormal H N ⧸ Subgroup.comap (Hom.subtype (Subgroup.prodNormal H N)) N :=
  isoOfSurjective ((proj _).comp (Subgroup.inclProdNormal H N))
    (fun h => by
      show h.1 ∈ N ↔ QuotientGroup.mk _ _ = 1
      rw [mk_eq_one]; exact Iff.rfl)
    (fun q => by
      obtain ⟨⟨x, h, hh, n, hn, hx⟩, rfl⟩ := mk_surjective q
      refine ⟨⟨h, hh⟩, ?_⟩
      show QuotientGroup.mk _ _ = QuotientGroup.mk _ _
      apply mk_eq_mk.2
      show h⁻¹ * x ∈ N
      rw [← hx, inv_mul_cancel_left]; exact hn)

end Second

section Third

variable (N M : Subgroup G) [hN : N.Normal] [hM : M.Normal]

/-- `M ⧸ N`: the image of `M` in `G ⧸ N`. It is a normal subgroup of `G ⧸ N`. -/
def Subgroup.quotientMap : Subgroup (G ⧸ N) := Subgroup.map (proj N) M

/-- `M ⧸ N` is normal in `G ⧸ N`. -/
instance Subgroup.quotientMap_normal : (Subgroup.quotientMap N M).Normal :=
  Subgroup.map_normal (proj N) (proj_surjective N) M

/-- **Third isomorphism theorem** ("cancelling" quotients). If `N ≤ M` are normal subgroups
of `G`, then `(G ⧸ N) ⧸ (M ⧸ N) ≃* G ⧸ M`. -/
noncomputable def thirdIsoTheorem (hle : N.le M) :
    (G ⧸ N) ⧸ Subgroup.quotientMap N M ≃* G ⧸ M :=
  isoOfSurjective (lift (proj M) fun x hx => mk_eq_one.2 (hle x hx))
    (fun q => by
      induction q using QuotientGroup.ind with
      | h a =>
        show (∃ x, x ∈ M ∧ QuotientGroup.mk N x = QuotientGroup.mk N a) ↔ QuotientGroup.mk M a = 1
        rw [mk_eq_one]
        constructor
        · intro ⟨x, hx, hxa⟩
          have h1 := hle _ (mk_eq_mk.1 hxa)
          have := M.mul_mem hx h1
          rwa [mul_inv_cancel_left] at this
        · intro ha; exact ⟨a, ha, rfl⟩)
    (fun q => by
      obtain ⟨a, rfl⟩ := mk_surjective q
      exact ⟨QuotientGroup.mk N a, rfl⟩)

end Third

end Foundations.Algebra
