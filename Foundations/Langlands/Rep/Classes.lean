import Foundations.Langlands.Rep.ClassFunctions

/-!
# The number of irreducibles is the number of conjugacy classes

For a finite group `G` the number of irreducible complex representations (up to
isomorphism) equals the number of conjugacy classes of `G` (Frobenius 1896). Here
`ConjClasses G` is the quotient of `G` by conjugacy, and `card_irr_eq_card_conjClasses` proves
`r = |ConjClasses G|` for every complete list `ρ₀, …, ρ_{r−1}` of pairwise non-isomorphic
irreducibles. Such a list exists by `exists_complete_irrList`, which gives
`exists_card_irr_eq_card_conjClasses`.

Both inequalities are dimension counts, using that `n` linearly independent vectors in `ℂ^m`
have `n ≤ m` (`card_le_of_linIndep`).

* `r ≤ #classes`: the vectors `(χ_k(g_q))_q` of character values on class representatives are
  linearly independent in `ℂ^{classes}`. A relation `Σ_k c_k χ_k = 0` pairs with `χ_j` to
  `c_j |G| = 0`, by orthogonality.
* `#classes ≤ r`: the vectors `u_q = (Σ_{g ∈ q} χ_k(g))_k` are linearly independent in `ℂ^r`.
  A relation `Σ_q a_q u_q = 0` says that the class function `g ↦ a_{[g]}` is orthogonal to every
  irreducible character, so it vanishes by `classFunction_eq_zero`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u

/-! ## Conjugacy classes -/

/-- **Conjugacy**: `x ~ y` if `h x h⁻¹ = y` for some `h`. It is an equivalence relation. -/
def conjSetoid (G : Type u) [Group G] : Setoid G where
  r x y := ∃ h : G, h * x * h⁻¹ = y
  iseqv := {
    refl := fun x => ⟨1, by rw [Group.one_mul, Group.inv_one, Group.mul_one]⟩
    symm := fun {x y} ⟨h, e⟩ => ⟨h⁻¹, by
      subst e
      simp only [Group.inv_inv, Group.mul_assoc, Group.inv_mul_cancel, Group.mul_one,
        Group.inv_mul_cancel_left]⟩
    trans := fun {x y z} ⟨h, e⟩ ⟨k, e'⟩ => ⟨k * h, by
      subst e; subst e'
      simp only [Group.mul_inv_rev, Group.mul_assoc]⟩ }

/-- The **conjugacy classes** of `G`. -/
def ConjClasses (G : Type u) [Group G] : Type u := Quotient (conjSetoid G)

/-- A finite group has finitely many conjugacy classes. -/
noncomputable instance ConjClasses.instFinite (G : Type u) [Group G] [FiniteType G] :
    FiniteType (ConjClasses G) :=
  instFiniteQuotient (conjSetoid G)

variable {G : Type u} [Group G]

/-- The conjugacy class of `g`. -/
def conjClass (g : G) : ConjClasses G := Quotient.mk (conjSetoid G) g

/-- Conjugate elements have the same class. -/
theorem conjClass_conj (g h : G) : conjClass (h * g * h⁻¹) = conjClass g :=
  (Quotient.sound ⟨h, rfl⟩ : conjClass g = conjClass (h * g * h⁻¹)).symm

/-- A chosen representative of each class. -/
noncomputable def classRep (q : ConjClasses G) : G :=
  Classical.choose (Quotient.exists_rep (s := conjSetoid G) q)

/-- The representative of `q` lies in `q`. -/
theorem conjClass_classRep (q : ConjClasses G) : conjClass (classRep q) = q :=
  Classical.choose_spec (Quotient.exists_rep (s := conjSetoid G) q)

/-- A class function takes the same value at `g` and at the representative of its class. -/
theorem classFunction_classRep {α : Type} {f : G → α} (hf : IsClassFunction f) (g : G) :
    f (classRep (conjClass g)) = f g := by
  obtain ⟨h, e⟩ := Quotient.exact (s := conjSetoid G) (conjClass_classRep (conjClass g))
  exact (hf _ h).symm.trans (congrArg f e)

/-! ## The two inequalities -/

variable [FiniteType G]

/-- **At most as many irreducibles as classes.** A list of `r` pairwise non-isomorphic
irreducible complex representations of `G` has `r ≤ |ConjClasses G|`. -/
theorem card_irr_le_card_conjClasses {G : Type} [Group G] [FiniteType G] {r : Nat}
    {ιs : Fin r → Type} [∀ k, FiniteType (ιs k)] {ρs : ∀ k, Rep G C (ιs k)}
    (hl : IsIrrList r ρs) : r ≤ card (ConjClasses G) := by
  let v : Fin r → Vec (ConjClasses G) C := fun k q => character (ρs k) (classRep q)
  have hv : LinIndep C v := by
    intro c hc j
    have hF : ∀ g, isum (fun k => c k * character (ρs k) g) = 0 := fun g => by
      have e := congrFun hc (conjClass g)
      rw [Vec.isum_apply] at e
      refine Eq.trans (isum_congr fun k => ?_) e
      show _ = c k * character (ρs k) (classRep (conjClass g))
      rw [classFunction_classRep (character_isClassFunction (ρs k))]
    have hp := pairing_isum_left (fun k g => c k * character (ρs k) g) (character (ρs j))
    simp only [pairing_smul_left] at hp
    rw [isum_single' _ j (fun k hk => by
      rw [orthogonality_complex (hl.1 j) (hl.1 k), if_neg (hl.2 j k (Ne.symm hk)),
        Ring.mul_zero])] at hp
    rw [orthogonality_complex (hl.1 j) (hl.1 j), if_pos (Iso.refl _)] at hp
    have h0 : pairing (fun g => isum (fun k => c k * character (ρs k) g)) (character (ρs j)) =
        0 * ncast (card G) := by
      unfold pairing
      rw [Ring.zero_mul]
      exact isum_eq_zero fun g => (congrArg (· * character (ρs j) g⁻¹) (hF g)).trans
        (Ring.zero_mul _)
    exact cancel_card (hp.symm.trans h0)
  have := card_le_of_linIndep C.isField hv
  rwa [card_fin] at this

open Classical in
/-- **At most as many classes as irreducibles.** If `ρ₀, …, ρ_{r−1}` is a complete list of
irreducible complex representations of `G` (every irreducible is isomorphic to a member), then
`|ConjClasses G| ≤ r`. -/
theorem card_conjClasses_le {G : Type} [Group G] [FiniteType G] {r : Nat}
    {ιs : Fin r → Type} [∀ k, FiniteType (ιs k)] {ρs : ∀ k, Rep G C (ιs k)}
    (hc : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k)) :
    card (ConjClasses G) ≤ r := by
  let u : ConjClasses G → Vec (Fin r) C := fun q k =>
    isum (fun g => if conjClass g = q then character (ρs k) g else 0)
  have hu : LinIndep C u := by
    intro a ha q
    have hk : ∀ k, isum (fun g => a (conjClass g) * character (ρs k) g) = 0 := fun k => by
      have e := congrFun ha k
      rw [Vec.isum_apply] at e
      refine Eq.trans ?_ e
      have e1 : ∀ q', (a q' • u q') k =
          isum (fun g => a q' * if conjClass g = q' then character (ρs k) g else 0) :=
        fun q' => isum_mul_left _ _
      rw [isum_congr e1, isum_comm]
      apply isum_congr; intro g
      rw [isum_single' _ (conjClass g) (fun q' hq' => by
        rw [if_neg (fun h => hq' h.symm), Ring.mul_zero]), if_pos rfl]
    have hf : IsClassFunction (fun g => a (conjClass g)) := fun g h => by
      show a (conjClass (h * g * h⁻¹)) = a (conjClass g)
      rw [conjClass_conj]
    have hz := classFunction_eq_zero hf (fun τ hτ => by
      obtain ⟨k, hik⟩ := hc τ hτ
      rw [character_eq_of_iso hik]; exact hk k) (classRep q)
    rwa [conjClass_classRep] at hz
  have := card_le_of_linIndep C.isField hu
  rwa [card_fin] at this

/-! ## The count -/

/-- **The number of irreducible representations is the number of conjugacy classes.** If
`ρ₀, …, ρ_{r−1}` are pairwise non-isomorphic irreducible complex representations of a finite
group `G` and every irreducible complex representation is isomorphic to one of them, then
`r = |ConjClasses G|`. -/
theorem card_irr_eq_card_conjClasses {G : Type} [Group G] [FiniteType G] {r : Nat}
    {ιs : Fin r → Type} [∀ k, FiniteType (ιs k)] {ρs : ∀ k, Rep G C (ιs k)}
    (hl : IsIrrList r ρs)
    (hc : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k)) :
    r = card (ConjClasses G) :=
  Nat.le_antisymm (card_irr_le_card_conjClasses hl) (card_conjClasses_le hc)

/-- **Frobenius' count, unconditionally.** Every finite group `G` has a complete list of
pairwise non-isomorphic irreducible complex representations, and its length is the number of
conjugacy classes of `G`. -/
theorem exists_card_irr_eq_card_conjClasses {G : Type} [Group G] [FiniteType G] :
    ∃ (r : Nat) (ιs : Fin r → Type) (_ : ∀ k, FiniteType (ιs k)) (ρs : ∀ k, Rep G C (ιs k)),
      IsIrrList r ρs ∧
      (∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k)) ∧
      r = card (ConjClasses G) := by
  obtain ⟨r, ιs, _, ρs, hl, hc⟩ := exists_complete_irrList (G := G)
  exact ⟨r, ιs, inferInstance, ρs, hl, hc, card_irr_eq_card_conjClasses hl hc⟩

end Foundations.Langlands
