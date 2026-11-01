import Foundations.Algebra.Lagrange

/-!
# Cayley's theorem

Groups were born as groups of permutations: Lagrange and Galois studied rearrangements of
the roots of equations, and for decades "group" meant "a collection of substitutions
closed under composition". When Arthur Cayley proposed the abstract definition in 1854 —
any set with an associative multiplication, identity and inverses — the natural worry was
that the abstraction might admit strange new objects unlike anything Galois had seen.

**Cayley's theorem** answers that worry: nothing has been lost and nothing strange has been
gained. Every group is isomorphic to a group of permutations — namely, each element `g`
can be identified with the permutation `x ↦ g * x` that it induces on the group itself
(the *left regular representation*). Abstract groups are therefore exactly the
permutation groups, viewed "up to isomorphism".

There is a philosophical moral that the structuralists liked to draw. The abstract
definition does not change *which* structures we study; it changes what we consider
essential about them. A permutation group carries incidental information (what is being
permuted); the abstract group retains only the pattern of composition.

For a finite group of order `n` we sharpen the statement: `G` embeds in the symmetric group
on `n` letters, `Perm (Fin n)`.
-/

namespace Foundations.Algebra

open Group FiniteType

universe u v

variable {G : Type u} [Group G]

/-- The **left regular representation**: the element `g` acts on `G` as the permutation
`x ↦ g * x` (with inverse `x ↦ g⁻¹ * x`). This is a homomorphism `G →* Perm G`. -/
def leftRegular (G : Type u) [Group G] : G →* Perm G where
  toFun g := ⟨fun x => g * x, fun x => g⁻¹ * x, inv_mul_cancel_left g, mul_inv_cancel_left g⟩
  map_mul a b := Perm.ext fun x => mul_assoc a b x

/-- The permutation induced by `g` sends `x` to `g * x`. -/
@[simp] theorem leftRegular_apply (g x : G) : leftRegular G g x = g * x := rfl

/-- The left regular representation is faithful: distinct elements induce distinct
permutations (look at where they send `1`). -/
theorem leftRegular_injective : ∀ a b : G, leftRegular G a = leftRegular G b → a = b := by
  intro a b h
  have := congrArg (fun σ : Perm G => σ 1) h
  simp only [leftRegular_apply, mul_one] at this
  exact this

/-- **Cayley's theorem.** Every group `G` embeds into the group of permutations of some set
(namely of `G` itself): there is an injective homomorphism `G →* Perm G`. -/
theorem cayley : ∃ f : G →* Perm G, ∀ a b, f a = f b → a = b :=
  ⟨leftRegular G, leftRegular_injective⟩

/-- **Cayley's theorem (isomorphism form).** Every group is isomorphic to a subgroup of a
permutation group: `G ≃* (image of the left regular representation)`. -/
noncomputable def cayleyIso (G : Type u) [Group G] : G ≃* (leftRegular G).range :=
  Iso.ofInjective (leftRegular G) leftRegular_injective

/-! ## Transport of permutations along a bijection -/

/-- A bijection `e : α → β` (with inverse `e'`) transports permutations of `α` to
permutations of `β`: `σ ↦ e ∘ σ ∘ e'`. This is a homomorphism of permutation groups. -/
def Perm.conjHom {α : Type u} {β : Type v} (e : α → β) (e' : β → α)
    (h1 : ∀ x, e' (e x) = x) (h2 : ∀ y, e (e' y) = y) : Perm α →* Perm β where
  toFun σ := ⟨fun y => e (σ (e' y)), fun y => e (σ.invFun (e' y)),
    fun y => by
      show e (σ.invFun (e' (e (σ.toFun (e' y))))) = y
      rw [h1, σ.left_inv, h2],
    fun y => by
      show e (σ.toFun (e' (e (σ.invFun (e' y))))) = y
      rw [h1, σ.right_inv, h2]⟩
  map_mul σ τ := Perm.ext fun y => by
    show e (σ (τ (e' y))) = e (σ (e' (e (τ (e' y)))))
    rw [h1]

/-- Transport along a bijection is injective. -/
theorem Perm.conjHom_injective {α : Type u} {β : Type v} (e : α → β) (e' : β → α)
    (h1 : ∀ x, e' (e x) = x) (h2 : ∀ y, e (e' y) = y) :
    ∀ σ τ, Perm.conjHom e e' h1 h2 σ = Perm.conjHom e e' h1 h2 τ → σ = τ := by
  intro σ τ h
  apply Perm.ext
  intro x
  have := congrArg (fun π : Perm β => e' (π (e x))) h
  simp only [Perm.conjHom, h1] at this
  exact this

/-- **Cayley's theorem for finite groups.** A finite group of order `n` embeds into the
symmetric group `Sₙ = Perm (Fin n)`: there is an injective homomorphism
`G →* Perm (Fin (card G))`. -/
theorem cayley_finite [FiniteType G] :
    ∃ f : G →* Perm (Fin (card G)), ∀ a b, f a = f b → a = b := by
  let T := Perm.conjHom (toFin (α := G)) ofFin ofFin_toFin toFin_ofFin
  refine ⟨T.comp (leftRegular G), ?_⟩
  intro a b h
  exact leftRegular_injective a b
    (Perm.conjHom_injective _ _ ofFin_toFin toFin_ofFin _ _ h)

/-- **Cayley's theorem for finite groups (isomorphism form).** A finite group of order `n` is
isomorphic to a subgroup of `Sₙ`. -/
theorem cayley_finite_iso [FiniteType G] :
    ∃ f : G →* Perm (Fin (card G)), Nonempty (G ≃* f.range) := by
  obtain ⟨f, hf⟩ := cayley_finite (G := G)
  exact ⟨f, ⟨Iso.ofInjective f hf⟩⟩

end Foundations.Algebra
