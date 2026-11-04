import Foundations.Langlands.Rep.Classes

/-!
# Characters span the class functions; second orthogonality

Let `χ₀, …, χ_{r−1}` be the characters of a complete list of pairwise non-isomorphic
irreducible complex representations of a finite group `G`.

* **Expansion of class functions** (`classFunction_expansion`): every class function `f` is a
  combination of the functions `g ↦ χ_k(g⁻¹)`, namely
  `|G| f(g) = Σ_k (Σ_x f(x) χ_k(x)) χ_k(g⁻¹)`. Subtracting the right-hand side from `|G| f`
  leaves a class function orthogonal to every irreducible character (by first orthogonality),
  which vanishes by `classFunction_eq_zero`.
* **Second orthogonality** (`second_orthogonality`): applying the expansion to the indicator
  function of the class of `h` gives
  `|cl(h)| · Σ_k χ_k(h) χ_k(g⁻¹) = |G|` if `g` is conjugate to `h`, and `0` otherwise. Here
  `|cl(h)|` is the number of conjugates of `h` (its relation `|G| / |cl(h)| = |C_G(h)|` with the
  centraliser is not formalised). In particular the columns of the character table at
  non-conjugate elements are orthogonal (`second_orthogonality_of_not_conj`).
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [FiniteType G]
variable {r : Nat} {ιs : Fin r → Type} [∀ k, FiniteType (ιs k)] {ρs : ∀ k, Rep G C (ιs k)}

/-- `g ↦ χ(g⁻¹)` is a class function. -/
theorem character_inv_isClassFunction {ι : Type} [FiniteType ι] (ρ : Rep G C ι) :
    IsClassFunction (fun g => character ρ g⁻¹) := fun g h => by
  show character ρ (h * g * h⁻¹)⁻¹ = character ρ g⁻¹
  rw [Group.mul_inv_rev, Group.mul_inv_rev, Group.inv_inv, ← Group.mul_assoc]
  exact character_isClassFunction ρ g⁻¹ h

/-- **Characters span the class functions.** For a complete list of pairwise non-isomorphic
irreducible complex characters `χ_k` and a class function `f`:
`|G| f(g) = Σ_k (Σ_x f(x) χ_k(x)) χ_k(g⁻¹)`. -/
theorem classFunction_expansion (hl : IsIrrList r ρs)
    (hc : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k))
    {f : G → C} (hf : IsClassFunction f) (g : G) :
    ncast (card G) * f g = isum (fun k => isum (fun x => f x * character (ρs k) x) *
      character (ρs k) g⁻¹) := by
  obtain ⟨t, ht⟩ := C.isField.2 _ (ncast_ne_zero_complex (card_group_pos (G := G)))
  let S : Fin r → C := fun k => isum (fun x => f x * character (ρs k) x)
  let F : G → C := fun y => f y + -isum (fun k => t * S k * character (ρs k) y⁻¹)
  have hF : IsClassFunction F := fun y h => by
    show f (h * y * h⁻¹) + _ = f y + _
    rw [hf]
    congr 2; apply isum_congr; intro k
    exact congrArg (t * S k * ·) (character_inv_isClassFunction (ρs k) y h)
  have horth : ∀ m, isum (fun y => F y * character (ρs m) y) = 0 := fun m => by
    have e1 : ∀ y, F y * character (ρs m) y = f y * character (ρs m) y +
        -isum (fun k => t * S k * (character (ρs m) y * character (ρs k) y⁻¹)) := fun y => by
      show (f y + _) * _ = _
      rw [Ring.right_distrib, Ring.neg_mul, isum_mul_right]
      congr 2; apply isum_congr; intro k; grind
    rw [isum_congr e1, isum_add, isum_neg, isum_comm]
    have e2 : ∀ k, isum (fun y => t * S k * (character (ρs m) y * character (ρs k) y⁻¹)) =
        t * S k * pairing (character (ρs m)) (character (ρs k)) := fun k => by
      unfold pairing; exact (isum_mul_left _ _).symm
    rw [isum_congr e2, isum_single' _ m (fun k hk => by
      rw [orthogonality_complex (hl.1 k) (hl.1 m), if_neg (hl.2 k m hk), Ring.mul_zero]),
      orthogonality_complex (hl.1 m) (hl.1 m), if_pos (Iso.refl _)]
    show S m + -(t * S m * ncast (card G)) = 0
    have : ncast (card G) * t = 1 := ht
    grind
  have hz := classFunction_eq_zero hF (fun τ hτ => by
    obtain ⟨k, hk⟩ := hc τ hτ
    rw [character_eq_of_iso hk]; exact horth k) g
  have e : f g = isum (fun k => t * S k * character (ρs k) g⁻¹) := by
    have hz' : f g + -isum (fun k => t * S k * character (ρs k) g⁻¹) = 0 := hz
    grind
  rw [e, isum_mul_left]
  apply isum_congr; intro k
  show ncast (card G) * (t * S k * _) = S k * _
  have : ncast (card G) * t = 1 := ht
  grind

open Classical in
/-- A sum of a constant over the elements satisfying `P` is `#P` times the constant. -/
theorem isum_ite_const (P : G → Prop) (c : C) :
    isum (fun x => if P x then c else 0) = ncast (count P) * c := by
  rw [count_eq_countP]
  unfold isum
  induction (elems : List G) with
  | nil => exact (Ring.zero_mul _).symm
  | cons a l ih =>
    show (if P a then c else 0) + lsum (l.map _) = _
    rw [ih, List.countP_cons]
    by_cases h : P a
    · rw [if_pos h, if_pos (decide_eq_true h), ncast_add_C]
      have e : (ncast 1 : C) = 1 := rfl
      rw [e]; grind
    · rw [if_neg h, if_neg (by simpa using h), Nat.add_zero]
      exact Ring.zero_add _

open Classical in
/-- **Second orthogonality.** For a complete list of pairwise non-isomorphic irreducible
complex characters `χ_k` of a finite group `G` and `g, h ∈ G`:
`|cl(h)| · Σ_k χ_k(h) χ_k(g⁻¹) = |G|` if `g` is conjugate to `h`, and `0` otherwise, where
`|cl(h)|` is the number of conjugates of `h`. -/
theorem second_orthogonality (hl : IsIrrList r ρs)
    (hc : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k))
    (g h : G) :
    ncast (count (fun x => conjClass x = conjClass h)) *
        isum (fun k => character (ρs k) h * character (ρs k) g⁻¹) =
      if conjClass g = conjClass h then ncast (card G) else 0 := by
  let f : G → C := fun x => if conjClass x = conjClass h then 1 else 0
  have hf : IsClassFunction f := fun x y => by
    show (if conjClass (y * x * y⁻¹) = _ then _ else _) = _
    rw [conjClass_conj]
  have hexp := classFunction_expansion hl hc hf g
  have hS : ∀ k, isum (fun x => f x * character (ρs k) x) =
      ncast (count (fun x => conjClass x = conjClass h)) * character (ρs k) h := fun k => by
    rw [← isum_ite_const]
    apply isum_congr; intro x
    show (if conjClass x = conjClass h then (1 : C) else 0) * _ = _
    by_cases hx : conjClass x = conjClass h
    · rw [if_pos hx, if_pos hx, Ring.one_mul]
      obtain ⟨y, e⟩ := Quotient.exact (s := conjSetoid G) hx
      rw [← e, character_isClassFunction]
    · rw [if_neg hx, if_neg hx, Ring.zero_mul]
  have hexp2 : isum (fun k => isum (fun x => f x * character (ρs k) x) *
      character (ρs k) g⁻¹) = ncast (count (fun x => conjClass x = conjClass h)) *
        isum (fun k => character (ρs k) h * character (ρs k) g⁻¹) := by
    rw [isum_mul_left]; apply isum_congr; intro k; rw [hS k, Ring.mul_assoc]
  rw [← hexp2, ← hexp]
  show ncast (card G) * (if conjClass g = conjClass h then (1 : C) else 0) = _
  by_cases hg : conjClass g = conjClass h
  · rw [if_pos hg, if_pos hg, Ring.mul_one]
  · rw [if_neg hg, if_neg hg, Ring.mul_zero]

/-- **Columns at non-conjugate elements are orthogonal**: if `g` is not conjugate to `h`, then
`Σ_k χ_k(h) χ_k(g⁻¹) = 0`. -/
theorem second_orthogonality_of_not_conj (hl : IsIrrList r ρs)
    (hc : ∀ {κ : Type} [FiniteType κ] (τ : Rep G C κ), Irreducible τ → ∃ k, Iso τ (ρs k))
    {g h : G} (hgh : conjClass g ≠ conjClass h) :
    isum (fun k => character (ρs k) h * character (ρs k) g⁻¹) = 0 := by
  classical
  have e := second_orthogonality hl hc g h
  rw [if_neg hgh] at e
  have hpos : 0 < count (fun x => conjClass x = conjClass h) := count_pos.2 ⟨h, rfl⟩
  obtain ⟨t, ht⟩ := C.isField.2 _ (ncast_ne_zero_complex hpos)
  calc _ = t * ncast (count (fun x => conjClass x = conjClass h)) *
        isum (fun k => character (ρs k) h * character (ρs k) g⁻¹) := by
          rw [CommRing.mul_comm t, ht, Ring.one_mul]
    _ = 0 := by rw [Ring.mul_assoc, e, Ring.mul_zero]

end Foundations.Langlands
