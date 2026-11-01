/-!
# Groups

This file opens Part IV of the project: abstract algebra. Parts I–III built sets, the
number systems and logic; here we change perspective. Instead of constructing one
particular object, we single out a *pattern* that many objects share and study the
pattern itself.

The pattern is that of a **group**: a collection of things that can be combined, where
combining is associative, there is a "do nothing" element, and every element can be
undone. The idea grew out of Lagrange's (1770) and Galois's (1830s) study of how the
roots of a polynomial can be permuted, and was given its abstract form by Cayley (1854),
who first wrote down "a set of symbols ... such that the product of any two of them
belongs to the set". Its triumph is a philosophical one as much as a mathematical one:
the *structuralist turn*, crystallised in Emmy Noether's school in the 1920s, in which a
mathematical object is identified with the web of operations it supports, and two
objects with the same web (isomorphic ones) are, for mathematical purposes, the same.

We take the economical one-sided axioms (associativity, a left identity, left inverses)
and derive the two-sided versions — a small demonstration that axioms can say more than
they seem to. Then come the basic tools of the structuralist: substructures (subgroups),
structure-preserving maps (homomorphisms), their kernels and images, and isomorphisms.
Finally we exhibit examples: the integers under addition, the integers modulo `n` on
`Fin n`, the permutations of any type, and the trivial group.

Since this project uses Lean's core library only, all of these notions are defined here
from scratch; Lean's built-in `Int`, `Nat` and `Fin` serve as raw material.
-/

namespace Foundations.Algebra

universe u v w

/-- **Group.** A group is a type `G` with a multiplication, a distinguished element `1`
and an inversion `a ↦ a⁻¹`, such that multiplication is associative, `1` is a left
identity and `a⁻¹` is a left inverse of `a`. (The right-handed versions are theorems,
proved below.) -/
class Group (G : Type u) extends Mul G, One G, Inv G where
  /-- Multiplication is associative. -/
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  /-- `1` is a left identity. -/
  one_mul : ∀ a : G, 1 * a = a
  /-- `a⁻¹` is a left inverse of `a`. -/
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

/-- A group is **commutative** (or *abelian*, after Niels Henrik Abel) when the order of
multiplication never matters. -/
class CommGroup (G : Type u) extends Group G where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ a b : G, a * b = b * a

namespace Group

variable {G : Type u} [Group G]

/-- If `a * a = a` then `a` is the identity: the only idempotent in a group is `1`. -/
theorem eq_one_of_mul_self (a : G) (h : a * a = a) : a = 1 := by
  calc a = 1 * a := (one_mul a).symm
    _ = (a⁻¹ * a) * a := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * a) := mul_assoc _ _ _
    _ = a⁻¹ * a := by rw [h]
    _ = 1 := inv_mul_cancel a

/-- **Right inverses.** In a group the left inverse `a⁻¹` is also a right inverse:
`a * a⁻¹ = 1`. This follows from the one-sided axioms. -/
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  apply eq_one_of_mul_self
  calc a * a⁻¹ * (a * a⁻¹) = a * (a⁻¹ * a * a⁻¹) := by simp only [mul_assoc]
    _ = a * a⁻¹ := by rw [inv_mul_cancel, one_mul]

/-- **Right identity.** `1` is also a right identity: `a * 1 = a`. -/
theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Left cancellation: `a * b = a * c` implies `b = c`. -/
theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := by
  calc b = a⁻¹ * (a * b) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = c := by rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- Right cancellation: `b * a = c * a` implies `b = c`. -/
theorem mul_right_cancel {a b c : G} (h : b * a = c * a) : b = c := by
  calc b = b * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = c * a * a⁻¹ := by rw [h]
    _ = c := by rw [mul_assoc, mul_inv_cancel, mul_one]

/-- `a⁻¹ * (a * b) = b`. -/
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- `a * (a⁻¹ * b) = b`. -/
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- `a * b * b⁻¹ = a`. -/
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

/-- `a * b⁻¹ * b = a`. -/
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- **Uniqueness of inverses.** If `a * b = 1` then `b` is the inverse of `a`. -/
theorem inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  apply mul_left_cancel (a := a)
  rw [mul_inv_cancel, h]

/-- **Uniqueness of the identity.** If `e * a = a` for some `a`, then `e = 1`. -/
theorem eq_one_of_mul_left {e a : G} (h : e * a = a) : e = 1 := by
  apply mul_right_cancel (a := a)
  rw [h, one_mul]

/-- Inverting twice gives back the original element. -/
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  inv_eq_of_mul_eq_one (inv_mul_cancel a)

/-- The identity is its own inverse. -/
theorem inv_one : (1 : G)⁻¹ = 1 :=
  inv_eq_of_mul_eq_one (one_mul 1)

/-- **Shoes and socks.** The inverse of a product is the product of the inverses in the
reverse order: `(a * b)⁻¹ = b⁻¹ * a⁻¹`. -/
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply inv_eq_of_mul_eq_one
  rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]

/-- Inversion is injective. -/
theorem inv_injective {a b : G} (h : a⁻¹ = b⁻¹) : a = b := by
  rw [← inv_inv a, h, inv_inv]

/-- `a⁻¹ * b = 1` exactly when `a = b`. -/
theorem inv_mul_eq_one {a b : G} : a⁻¹ * b = 1 ↔ a = b := by
  constructor
  · intro h
    have := inv_eq_of_mul_eq_one h
    rwa [inv_inv] at this
  · intro h; rw [h, inv_mul_cancel]

/-- `a * b⁻¹ = 1` exactly when `a = b`. -/
theorem mul_inv_eq_one {a b : G} : a * b⁻¹ = 1 ↔ a = b := by
  constructor
  · intro h
    exact inv_injective (inv_eq_of_mul_eq_one h)
  · intro h; rw [h, mul_inv_cancel]

/-- An element whose inverse is `1` is itself `1`. -/
theorem inv_eq_one {a : G} : a⁻¹ = 1 ↔ a = 1 := by
  constructor
  · intro h; rw [← inv_inv a, h, inv_one]
  · intro h; rw [h, inv_one]

/-! ## Powers -/

/-- Natural-number powers: `a ^ 0 = 1` and `a ^ (n+1) = a ^ n * a`. -/
def npow (a : G) : Nat → G
  | 0 => 1
  | n + 1 => npow a n * a

/-- The notation `a ^ n` for natural-number powers in a group. -/
instance (priority := low) instPowNat : Pow G Nat := ⟨npow⟩

/-- `a ^ 0 = 1`. -/
@[simp] theorem pow_zero (a : G) : a ^ 0 = 1 := rfl

/-- `a ^ (n+1) = a ^ n * a`. -/
theorem pow_succ (a : G) (n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

/-- `a ^ 1 = a`. -/
@[simp] theorem pow_one (a : G) : a ^ 1 = a := by
  rw [pow_succ, pow_zero, one_mul]

/-- **Law of exponents.** `a ^ (m + n) = a ^ m * a ^ n`. -/
theorem pow_add (a : G) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ n ih => rw [← Nat.add_assoc, pow_succ, ih, pow_succ, mul_assoc]

/-- `a ^ (n+1) = a * a ^ n`: powers of `a` commute with `a`. -/
theorem pow_succ' (a : G) (n : Nat) : a ^ (n + 1) = a * a ^ n := by
  rw [Nat.add_comm, pow_add, pow_one]

/-- **Law of exponents.** `a ^ (m * n) = (a ^ m) ^ n`. -/
theorem pow_mul (a : G) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, pow_add, ih, pow_succ]

/-- Powers of the identity are the identity. -/
@[simp] theorem one_pow (n : Nat) : (1 : G) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, one_mul]

/-- The inverse of a power: `(a ^ n)⁻¹ * a ^ n = 1` is automatic, and more usefully
`a ^ n * (a⁻¹) ^ n = 1`. -/
theorem pow_mul_inv_pow (a : G) (n : Nat) : a ^ n * a⁻¹ ^ n = 1 := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc a, mul_inv_cancel, one_mul, ih]

end Group

open Group

/-- In a commutative group, multiplication can be reordered. -/
theorem CommGroup.mul_comm' {G : Type u} [CommGroup G] (a b : G) : a * b = b * a :=
  CommGroup.mul_comm a b

/-! ## Subgroups -/

/-- **Subgroup.** A subgroup of `G` is a property of elements of `G` (its *carrier*) that
holds of `1` and is preserved by multiplication and inversion. Subgroups are the
substructures of group theory. -/
structure Subgroup (G : Type u) [Group G] where
  /-- The elements belonging to the subgroup. -/
  carrier : G → Prop
  /-- The identity belongs to the subgroup. -/
  one_mem : carrier 1
  /-- The subgroup is closed under multiplication. -/
  mul_mem : ∀ {a b : G}, carrier a → carrier b → carrier (a * b)
  /-- The subgroup is closed under inversion. -/
  inv_mem : ∀ {a : G}, carrier a → carrier a⁻¹

namespace Subgroup

variable {G : Type u} [Group G]

/-- Membership in a subgroup: `x ∈ H` means `H.carrier x`. -/
instance : Membership G (Subgroup G) := ⟨fun H x => H.carrier x⟩

/-- Unfolding membership. -/
theorem mem_def (H : Subgroup G) (x : G) : x ∈ H ↔ H.carrier x := Iff.rfl

/-- Two subgroups with the same elements are equal. -/
theorem ext {H K : Subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := by
  cases H with
  | mk c1 o1 m1 i1 =>
    cases K with
    | mk c2 o2 m2 i2 =>
      have : c1 = c2 := funext fun x => propext (h x)
      subst this
      rfl

/-- `1 ∈ H`. -/
theorem one_mem' (H : Subgroup G) : (1 : G) ∈ H := H.one_mem

/-- Closure under multiplication, stated with `∈`. -/
theorem mul_mem' (H : Subgroup G) {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  H.mul_mem ha hb

/-- Closure under inversion, stated with `∈`. -/
theorem inv_mem' (H : Subgroup G) {a : G} (ha : a ∈ H) : a⁻¹ ∈ H := H.inv_mem ha

/-- `a⁻¹ ∈ H` iff `a ∈ H`. -/
theorem inv_mem_iff (H : Subgroup G) {a : G} : a⁻¹ ∈ H ↔ a ∈ H :=
  ⟨fun h => inv_inv a ▸ H.inv_mem' h, H.inv_mem'⟩

/-- If `a ∈ H`, then `a * b ∈ H` iff `b ∈ H`. -/
theorem mul_mem_left_iff (H : Subgroup G) {a b : G} (ha : a ∈ H) : a * b ∈ H ↔ b ∈ H :=
  ⟨fun h => by
    have := H.mul_mem' (H.inv_mem' ha) h
    rwa [inv_mul_cancel_left] at this,
   fun h => H.mul_mem' ha h⟩

/-- Subgroups are closed under natural-number powers. -/
theorem pow_mem (H : Subgroup G) {a : G} (ha : a ∈ H) (n : Nat) : a ^ n ∈ H := by
  induction n with
  | zero => exact H.one_mem
  | succ n ih => exact H.mul_mem ih ha

/-- The **trivial subgroup** `{1}`. -/
def bot : Subgroup G where
  carrier x := x = 1
  one_mem := rfl
  mul_mem := by intro a b ha hb; rw [ha, hb, one_mul]
  inv_mem := by intro a ha; rw [ha, inv_one]

/-- The **whole group** as a subgroup of itself. -/
def top : Subgroup G where
  carrier _ := True
  one_mem := trivial
  mul_mem := fun _ _ => trivial
  inv_mem := fun _ => trivial

/-- The **intersection** of two subgroups is a subgroup. -/
def inter (H K : Subgroup G) : Subgroup G where
  carrier x := x ∈ H ∧ x ∈ K
  one_mem := ⟨H.one_mem, K.one_mem⟩
  mul_mem := fun ha hb => ⟨H.mul_mem ha.1 hb.1, K.mul_mem ha.2 hb.2⟩
  inv_mem := fun ha => ⟨H.inv_mem ha.1, K.inv_mem ha.2⟩

/-- Membership in the trivial subgroup. -/
@[simp] theorem mem_bot {x : G} : x ∈ (bot : Subgroup G) ↔ x = 1 := Iff.rfl

/-- Membership in the whole group. -/
@[simp] theorem mem_top {x : G} : x ∈ (top : Subgroup G) := trivial

/-- A subgroup, viewed as a type: the elements of `G` that belong to `H`. -/
instance : CoeSort (Subgroup G) (Type u) := ⟨fun H => {x : G // x ∈ H}⟩

/-- A subgroup is itself a group under the inherited operations. -/
instance toGroup (H : Subgroup G) : Group H where
  mul a b := ⟨a.1 * b.1, H.mul_mem a.2 b.2⟩
  one := ⟨1, H.one_mem⟩
  inv a := ⟨a.1⁻¹, H.inv_mem a.2⟩
  mul_assoc a b c := Subtype.ext (Group.mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (Group.one_mul a.1)
  inv_mul_cancel a := Subtype.ext (Group.inv_mul_cancel a.1)

/-- Multiplication in a subgroup is multiplication in `G`. -/
@[simp] theorem coe_mul (H : Subgroup G) (a b : H) : (a * b).1 = a.1 * b.1 := rfl

/-- The identity of a subgroup is the identity of `G`. -/
@[simp] theorem coe_one (H : Subgroup G) : (1 : H).1 = 1 := rfl

/-- Inversion in a subgroup is inversion in `G`. -/
@[simp] theorem coe_inv (H : Subgroup G) (a : H) : (a⁻¹).1 = a.1⁻¹ := rfl

end Subgroup

/-! ## Homomorphisms -/

/-- **Group homomorphism.** A map between groups that preserves multiplication. These are
the structure-preserving maps — the "arrows" — of group theory. -/
structure Hom (G : Type u) (H : Type v) [Group G] [Group H] where
  /-- The underlying function. -/
  toFun : G → H
  /-- The function turns products into products. -/
  map_mul : ∀ a b : G, toFun (a * b) = toFun a * toFun b

/-- Notation `G →* H` for the type of group homomorphisms. -/
scoped infixr:25 " →* " => Hom

namespace Hom

variable {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]

/-- A homomorphism can be applied like a function. -/
instance : CoeFun (G →* H) (fun _ => G → H) := ⟨Hom.toFun⟩

/-- Two homomorphisms with the same values are equal. -/
theorem ext {f g : G →* H} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  have := funext h
  simp only at this
  subst this; rfl

/-- Multiplicativity, applied form. -/
theorem map_mul' (f : G →* H) (a b : G) : f (a * b) = f a * f b := f.map_mul a b

/-- **Homomorphisms preserve the identity.** This need not be assumed: it follows from
preservation of products. -/
theorem map_one (f : G →* H) : f 1 = 1 := by
  apply eq_one_of_mul_self
  rw [← f.map_mul', one_mul]

/-- **Homomorphisms preserve inverses.** -/
theorem map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one
  rw [← f.map_mul', mul_inv_cancel, f.map_one]

/-- Homomorphisms preserve powers. -/
theorem map_pow (f : G →* H) (a : G) (n : Nat) : f (a ^ n) = f a ^ n := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => rw [pow_succ, f.map_mul', ih, pow_succ]

/-- The identity homomorphism. -/
def id (G : Type u) [Group G] : G →* G where
  toFun x := x
  map_mul _ _ := rfl

/-- The composite of two homomorphisms is a homomorphism. -/
def comp (g : H →* K) (f : G →* H) : G →* K where
  toFun x := g (f x)
  map_mul a b := by rw [f.map_mul', g.map_mul']

/-- The **kernel** of `f`: the elements sent to the identity. It is a subgroup of the
domain. -/
def ker (f : G →* H) : Subgroup G where
  carrier x := f x = 1
  one_mem := f.map_one
  mul_mem := by intro a b ha hb; show f (a * b) = 1; rw [f.map_mul', ha, hb, one_mul]
  inv_mem := by intro a ha; show f a⁻¹ = 1; rw [f.map_inv, ha, inv_one]

/-- The **image** (range) of `f`: the elements of the codomain hit by `f`. It is a
subgroup of the codomain. -/
def range (f : G →* H) : Subgroup H where
  carrier y := ∃ x, f x = y
  one_mem := ⟨1, f.map_one⟩
  mul_mem := by
    intro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [f.map_mul', hx, hy]⟩
  inv_mem := by
    intro a ⟨x, hx⟩
    exact ⟨x⁻¹, by rw [f.map_inv, hx]⟩

/-- Membership in the kernel. -/
theorem mem_ker (f : G →* H) {x : G} : x ∈ f.ker ↔ f x = 1 := Iff.rfl

/-- Membership in the image. -/
theorem mem_range (f : G →* H) {y : H} : y ∈ f.range ↔ ∃ x, f x = y := Iff.rfl

/-- `f a = f b` exactly when `a⁻¹ * b` lies in the kernel. -/
theorem eq_iff_inv_mul_mem_ker (f : G →* H) {a b : G} : f a = f b ↔ a⁻¹ * b ∈ f.ker := by
  rw [mem_ker, map_mul', map_inv, inv_mul_eq_one]

/-- **Injectivity via the kernel.** A homomorphism is injective exactly when its kernel is
trivial — one only needs to check what is sent to `1`. -/
theorem injective_iff_ker_trivial (f : G →* H) :
    (∀ a b, f a = f b → a = b) ↔ (∀ x, f x = 1 → x = 1) := by
  constructor
  · intro h x hx
    exact h x 1 (by rw [hx, f.map_one])
  · intro h a b hab
    have := h _ ((f.eq_iff_inv_mul_mem_ker).1 hab)
    exact inv_mul_eq_one.1 this

/-- The homomorphism from `G` onto its image, obtained by restricting the codomain. -/
def rangeRestrict (f : G →* H) : G →* f.range where
  toFun x := ⟨f x, x, rfl⟩
  map_mul a b := Subtype.ext (f.map_mul' a b)

/-- The inclusion of a subgroup into the ambient group is a homomorphism. -/
def subtype (S : Subgroup G) : S →* G where
  toFun x := x.1
  map_mul _ _ := rfl

end Hom

/-! ## Isomorphisms -/

/-- **Group isomorphism.** A homomorphism with a two-sided inverse function. Isomorphic
groups are indistinguishable by anything expressible in terms of multiplication: this is
the structuralist's notion of sameness. -/
structure Iso (G : Type u) (H : Type v) [Group G] [Group H] extends Hom G H where
  /-- The inverse function. -/
  invFun : H → G
  /-- `invFun` undoes `toFun`. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun` undoes `invFun`. -/
  right_inv : ∀ y, toFun (invFun y) = y

/-- Notation `G ≃* H` for the type of group isomorphisms. -/
scoped infix:25 " ≃* " => Iso

namespace Iso

variable {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]

/-- An isomorphism can be applied like a function. -/
instance : CoeFun (G ≃* H) (fun _ => G → H) := ⟨fun e => e.toFun⟩

/-- Every group is isomorphic to itself. -/
def refl (G : Type u) [Group G] : G ≃* G :=
  { Hom.id G with invFun := fun x => x, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-- The inverse of an isomorphism is an isomorphism. -/
def symm (e : G ≃* H) : H ≃* G where
  toFun := e.invFun
  map_mul a b := by
    have h : e.toFun (e.invFun (a * b)) = e.toFun (e.invFun a * e.invFun b) := by
      rw [e.map_mul, e.right_inv, e.right_inv, e.right_inv]
    have h2 := congrArg e.invFun h
    rwa [e.left_inv, e.left_inv] at h2
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Composition of isomorphisms. -/
def trans (e : G ≃* H) (e' : H ≃* K) : G ≃* K :=
  { Hom.comp e'.toHom e.toHom with
    invFun := fun z => e.invFun (e'.invFun z)
    left_inv := fun x => by
      show e.invFun (e'.invFun (e'.toFun (e.toFun x))) = x
      rw [e'.left_inv, e.left_inv]
    right_inv := fun z => by
      show e'.toFun (e.toFun (e.invFun (e'.invFun z))) = z
      rw [e.right_inv, e'.right_inv] }

/-- An isomorphism is injective. -/
theorem injective (e : G ≃* H) {a b : G} (h : e a = e b) : a = b := by
  rw [← e.left_inv a, ← e.left_inv b]
  exact congrArg e.invFun h

/-- An isomorphism is surjective. -/
theorem surjective (e : G ≃* H) (y : H) : ∃ x, e x = y := ⟨e.invFun y, e.right_inv y⟩

/-- **Bijective homomorphisms are isomorphisms.** A homomorphism that is injective and
surjective has an inverse function, which is automatically a homomorphism. (The inverse
is chosen using the axiom of choice, so this construction is noncomputable.) -/
noncomputable def ofBijective (f : G →* H) (inj : ∀ a b, f a = f b → a = b)
    (surj : ∀ y, ∃ x, f x = y) : G ≃* H :=
  { f with
    invFun := fun y => Classical.choose (surj y)
    left_inv := fun x => inj _ _ (Classical.choose_spec (surj (f x)))
    right_inv := fun y => Classical.choose_spec (surj y) }

/-- **Injective homomorphisms embed.** An injective homomorphism `f : G →* H` is an
isomorphism of `G` onto its image `f.range`. -/
noncomputable def ofInjective (f : G →* H) (inj : ∀ a b, f a = f b → a = b) :
    G ≃* f.range :=
  ofBijective f.rangeRestrict
    (fun a b h => inj a b (congrArg Subtype.val h))
    (fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩)

end Iso

/-! ## Examples

Abstraction earns its keep only if it has instances. We give four: the integers under
addition, the integers modulo `n`, the permutations of an arbitrary type (the historical
origin of the subject), and the trivial group.

Because our groups are written multiplicatively, we place the additive groups on *type
synonyms*: `IntAdd` is a copy of `Int` whose "multiplication" is addition. -/

/-- The integers, regarded as a group under **addition**. (A synonym of `Int`, so that the
group operation, written `*`, can be integer addition.) -/
def IntAdd : Type := Int

namespace IntAdd

/-- View an integer as an element of the additive group `IntAdd`. -/
def of (a : Int) : IntAdd := a

/-- The underlying integer of an element of `IntAdd`. -/
def val (a : IntAdd) : Int := a

/-- **The additive group of integers** `(ℤ, +)`: the operation is `+`, the identity is
`0`, the inverse of `a` is `-a`. It is commutative. -/
instance : CommGroup IntAdd where
  mul a b := of (val a + val b)
  one := of 0
  inv a := of (- val a)
  mul_assoc a b c := Int.add_assoc (val a) (val b) (val c)
  one_mul a := Int.zero_add (val a)
  inv_mul_cancel a := Int.add_left_neg (val a)
  mul_comm a b := Int.add_comm (val a) (val b)

/-- The group operation of `IntAdd` is integer addition. -/
theorem val_mul (a b : IntAdd) : val (a * b) = val a + val b := rfl

/-- **Doubling is a homomorphism** `(ℤ,+) → (ℤ,+)`, `a ↦ 2a`; its kernel is trivial and its
image is the subgroup of even integers. -/
def double : IntAdd →* IntAdd where
  toFun a := of (2 * val a)
  map_mul a b := Int.mul_add 2 (val a) (val b)

/-- The doubling homomorphism is injective. -/
theorem double_injective : ∀ a b, double a = double b → a = b := by
  intro a b h
  have h' : 2 * val a = 2 * val b := h
  show val a = val b
  omega

end IntAdd

/-- The **integers modulo `n`**, `ℤ/nℤ`, realised on `Fin n = {0, 1, …, n-1}` with addition
modulo `n` as the group operation. (A synonym of `Fin n`; we require `n ≠ 0`.) -/
def ZMod (n : Nat) : Type := Fin n

namespace ZMod

variable {n : Nat} [NeZero n]

/-- View a residue in `Fin n` as an element of `ZMod n`. -/
def of (a : Fin n) : ZMod n := a

/-- The underlying residue in `Fin n`. -/
def val (a : ZMod n) : Fin n := a

/-- **The cyclic group `ℤ/nℤ`.** Residues modulo `n` under addition modulo `n` form a
commutative group with identity `0`. -/
instance : CommGroup (ZMod n) where
  mul a b := of (val a + val b)
  one := of 0
  inv a := of (- val a)
  mul_assoc a b c := by show val a + val b + val c = val a + (val b + val c); grind
  one_mul a := by show 0 + val a = val a; grind
  inv_mul_cancel a := by show -val a + val a = 0; grind
  mul_comm a b := by show val a + val b = val b + val a; grind

/-- The group operation of `ZMod n` is addition modulo `n`. -/
theorem val_mul (a b : ZMod n) : (val (a * b)).val = ((val a).val + (val b).val) % n :=
  Fin.val_add _ _

/-- The generator `1` of `ℤ/nℤ`: every element is a power of it (`ZMod.pow_gen`). -/
def gen : ZMod n := of (Fin.ofNat n 1)

/-- In `ℤ/nℤ`, the `k`-th "power" of the generator is the residue `k mod n`. -/
theorem pow_gen (k : Nat) : (val (gen ^ k : ZMod n)).val = k % n := by
  induction k with
  | zero => show (0 : Fin n).val = 0 % n; simp
  | succ k ih =>
    rw [Group.pow_succ, val_mul, ih]
    show (k % n + (Fin.ofNat n 1).val) % n = (k + 1) % n
    simp only [Fin.val_ofNat]
    rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]

/-- **`ℤ/nℤ` is cyclic**: every element is a power of the generator `1`. -/
theorem cyclic (a : ZMod n) : ∃ k : Nat, gen ^ k = a := by
  refine ⟨(val a).val, ?_⟩
  apply Fin.ext
  show (val (gen ^ (val a).val : ZMod n)).val = (val a).val
  rw [pow_gen, Nat.mod_eq_of_lt (val a).isLt]

end ZMod

/-- **Permutation.** A permutation of a type `α` is a bijection `α → α`, recorded together
with its inverse. Permutations of the roots of an equation were the groups studied by
Lagrange and Galois. -/
structure Perm (α : Type u) where
  /-- The permutation as a function. -/
  toFun : α → α
  /-- Its inverse function. -/
  invFun : α → α
  /-- `invFun` undoes `toFun`. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun` undoes `invFun`. -/
  right_inv : ∀ x, toFun (invFun x) = x

namespace Perm

variable {α : Type u}

/-- A permutation can be applied like a function. -/
instance : CoeFun (Perm α) (fun _ => α → α) := ⟨Perm.toFun⟩

/-- Two permutations with the same values are equal (the inverse is then determined). -/
theorem ext {σ τ : Perm α} (h : ∀ x, σ x = τ x) : σ = τ := by
  cases σ with
  | mk f g l r =>
    cases τ with
    | mk f' g' l' r' =>
      have hf : f = f' := funext h
      subst hf
      have hg : g = g' := funext fun x => by
        have := l (g' x); rw [r' x] at this; exact this
      subst hg; rfl

/-- **The symmetric group** on `α`: permutations under composition. The product `σ * τ`
means "first `τ`, then `σ`". -/
instance : Group (Perm α) where
  mul σ τ := ⟨fun x => σ (τ x), fun x => τ.invFun (σ.invFun x),
    fun x => by simp only [σ.left_inv, τ.left_inv],
    fun x => by show σ.toFun (τ.toFun (τ.invFun (σ.invFun x))) = x; rw [τ.right_inv, σ.right_inv]⟩
  one := ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
  inv σ := ⟨σ.invFun, σ.toFun, σ.right_inv, σ.left_inv⟩
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  inv_mul_cancel σ := ext fun x => σ.left_inv x

/-- Applying a product of permutations: `(σ * τ) x = σ (τ x)`. -/
@[simp] theorem mul_apply (σ τ : Perm α) (x : α) : (σ * τ) x = σ (τ x) := rfl

/-- The identity permutation fixes everything. -/
@[simp] theorem one_apply (x : α) : (1 : Perm α) x = x := rfl

/-- Applying the inverse permutation. -/
theorem inv_apply_self (σ : Perm α) (x : α) : σ⁻¹ (σ x) = x := σ.left_inv x

/-- A **transposition** on a type with decidable equality: `swap a b` exchanges `a` and `b` and fixes everything else. -/
def swap [DecidableEq α] (a b : α) : Perm α where
  toFun x := if x = a then b else if x = b then a else x
  invFun x := if x = a then b else if x = b then a else x
  left_inv x := by by_cases h1 : x = a <;> by_cases h2 : x = b <;> simp_all
  right_inv x := by by_cases h1 : x = a <;> by_cases h2 : x = b <;> simp_all

/-- **Permutation groups need not commute.** On a type with three distinct elements, two
transpositions fail to commute. -/
theorem swap_mul_swap_ne [DecidableEq α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : swap a b * swap b c ≠ swap b c * swap a b := by
  intro h
  have := congrArg (fun σ : Perm α => σ a) h
  simp only [mul_apply, swap] at this
  simp_all

end Perm

/-- **The trivial group.** The one-element type `Unit` is a group in exactly one way. -/
instance : CommGroup Unit where
  mul _ _ := ()
  one := ()
  inv _ := ()
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  inv_mul_cancel _ := rfl
  mul_comm _ _ := rfl

/-- Any two groups' trivial homomorphism: send everything to `1`. -/
def Hom.trivial (G : Type u) (H : Type v) [Group G] [Group H] : G →* H where
  toFun _ := 1
  map_mul _ _ := (Group.one_mul 1).symm

end Foundations.Algebra
