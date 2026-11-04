import Foundations.Langlands.Rep.Induction

/-!
# Induced representations

Frobenius defined induced characters in 1898 by the formula of `Induction`. The induced
*representation* behind them is the following block-matrix construction. Given a representation `σ` of a subgroup `H`
on `K^ι`, choose one representative `t` in each left coset `tH`. Every `g ∈ G` permutes the
cosets, `g · sH = tH`, and on the way picks up an element `t⁻¹ g s` of `H`. The induced
representation `Ind^G_H σ` acts on `K^(T × ι)`, one copy of `K^ι` per coset representative `t`,
by the block matrix

`Ind σ(g)_{(t,i),(s,j)} = σ(t⁻¹ g s)_{ij}` if `t⁻¹ g s ∈ H`, and `0` otherwise,

so each block row and column has exactly one non-zero block: a "monomial matrix of matrices".
Induction is the prototype of Langlands functoriality (see `Induction`): an operation that
produces representations of a large group from representations of a smaller one, with an
explicit effect on characters.

This file constructs:

* canonical **coset representatives** `cosetRep H g`, chosen classically (by Hilbert's
  `ε`-operator) as a function of the coset `gH` alone, and the finite type
  `CosetReps H = {t // cosetRep H t = t}` of chosen representatives; every element factors
  uniquely as `t h` with `t ∈ CosetReps H` and `h ∈ H` (`isum_cosetReps_mul`);
* the **induced representation** `indRep H σ : Rep G K (CosetReps H × ι)`, over any commutative
  ring `K`, as the block matrices above (`indRep_apply`);
* its **character**: over `ℂ`, `χ_{Ind σ} = Ind χ_σ` (`character_indRep`), the induced class
  function of `Induction`;
* **Frobenius reciprocity for representations** (`frobenius_reciprocity_indRep`):
  `⟨χ_{Ind σ}, χ_ρ⟩_G = ⟨χ_σ, χ_{Res ρ}⟩_H`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u v w

variable {G : Type u} [Group G] (H : Subgroup G)

/-! ## Coset representatives -/

/-- The **coset representative** of `gH`: an element of the coset `gH`, chosen by Hilbert's
`ε`-operator from the coset itself, so that it depends only on the coset. -/
noncomputable def cosetRep (g : G) : G := @Classical.epsilon G ⟨g⟩ (leftCoset g H)

/-- The representative of `gH` lies in `gH`: `g⁻¹ · rep(g) ∈ H`. -/
theorem cosetRep_mem (g : G) : g⁻¹ * cosetRep H g ∈ H :=
  Classical.epsilon_spec (p := leftCoset g H) ⟨g, mem_leftCoset_self g H⟩

/-- `rep(g)⁻¹ · g ∈ H`. -/
theorem cosetRep_inv_mul_mem (g : G) : (cosetRep H g)⁻¹ * g ∈ H := by
  have := H.inv_mem (cosetRep_mem H g)
  rwa [Group.mul_inv_rev, Group.inv_inv] at this

/-- **Representatives depend only on the coset.** If `a⁻¹ b ∈ H`, i.e. `aH = bH`, then
`rep(a) = rep(b)`. -/
theorem cosetRep_eq {a b : G} (h : a⁻¹ * b ∈ H) : cosetRep H a = cosetRep H b := by
  have hc : leftCoset a H = leftCoset b H := by
    funext x
    apply propext
    rcases leftCoset_eq_or_disjoint H a b with e | e
    · exact e x
    · exact absurd ⟨h, mem_leftCoset_self b H⟩ (e b)
  unfold cosetRep
  rw [hc]

/-- The representative of a representative is itself. -/
theorem cosetRep_cosetRep (g : G) : cosetRep H (cosetRep H g) = cosetRep H g :=
  (cosetRep_eq H (cosetRep_mem H g)).symm

/-- The type of **chosen coset representatives**: elements `t` with `rep(t) = t`, one in each
left coset of `H`. -/
abbrev CosetReps : Type u := {t : G // cosetRep H t = t}

/-- The chosen representative of the coset `gH`, as an element of `CosetReps H`. -/
noncomputable def toRep (g : G) : CosetReps H := ⟨cosetRep H g, cosetRep_cosetRep H g⟩

/-- **Distinct representatives lie in distinct cosets.** If `t⁻¹ s ∈ H` for chosen
representatives `t`, `s`, then `t = s`. -/
theorem CosetReps.eq_of_mem {t s : CosetReps H} (h : t.1⁻¹ * s.1 ∈ H) : t = s :=
  Subtype.ext (by rw [← t.2, ← s.2]; exact cosetRep_eq H h)

/-- If `t⁻¹ x ∈ H` for a chosen representative `t`, then `t` is the representative of `x`. -/
theorem CosetReps.eq_toRep {t : CosetReps H} {x : G} (h : t.1⁻¹ * x ∈ H) : t = toRep H x :=
  Subtype.ext (by show t.1 = cosetRep H x; rw [← cosetRep_eq H h, t.2])

variable [FiniteType G]

/-- The chosen representatives form a finite type. -/
noncomputable instance CosetReps.instFinite : FiniteType (CosetReps H) :=
  inferInstanceAs (FiniteType {t : G // cosetRep H t = t})

/-- **Every element is uniquely `t h`.** A sum over `G` is a sum over pairs `(t, h)` of a chosen
representative and an element of `H`, via `(t, h) ↦ t h`. -/
theorem isum_cosetReps_mul {A : Type} [AddAbGroup A] (F : G → A) :
    isum (fun p : CosetReps H × H => F (p.1.1 * p.2.1)) = isum F := by
  apply isum_comp_bij (fun p : CosetReps H × H => p.1.1 * p.2.1)
  · rintro ⟨t, h⟩ ⟨t', h'⟩ e
    have e' : t.1 * h.1 = t'.1 * h'.1 := e
    have ht : t = t' := by
      apply CosetReps.eq_of_mem
      have : t.1⁻¹ * t'.1 = h.1 * h'.1⁻¹ :=
        calc t.1⁻¹ * t'.1 = t.1⁻¹ * (t'.1 * h'.1 * h'.1⁻¹) := by rw [Group.mul_inv_cancel_right]
          _ = t.1⁻¹ * (t.1 * h.1 * h'.1⁻¹) := by rw [← e']
          _ = h.1 * h'.1⁻¹ := by rw [Group.mul_assoc t.1, Group.inv_mul_cancel_left]
      rw [this]; exact H.mul_mem h.2 (H.inv_mem h'.2)
    subst ht
    have hh : h = h' := Subtype.ext (Group.mul_left_cancel e')
    rw [hh]
  · intro g
    refine ⟨(toRep H g, ⟨(cosetRep H g)⁻¹ * g, cosetRep_inv_mul_mem H g⟩), ?_⟩
    show cosetRep H g * ((cosetRep H g)⁻¹ * g) = g
    exact Group.mul_inv_cancel_left _ _

/-! ## The induced representation -/

variable {K : Type w} [CommRing K] {ι : Type v} [FiniteType ι]

/-- The matrix `σ°(x)`: `σ(x)` for `x ∈ H`, and the zero matrix otherwise. -/
noncomputable def matExt (σ : Rep H K ι) (x : G) : Mat ι ι K := by
  classical exact if h : x ∈ H then σ ⟨x, h⟩ else 0

/-- `σ°(x) = σ(x)` on `H`. -/
theorem matExt_mem (σ : Rep H K ι) {x : G} (hx : x ∈ H) : matExt H σ x = σ ⟨x, hx⟩ := by
  unfold matExt; simp only [hx, ↓reduceDIte]

/-- `σ°(x) = 0` off `H`. -/
theorem matExt_not_mem (σ : Rep H K ι) {x : G} (hx : x ∉ H) : matExt H σ x = 0 := by
  unfold matExt; simp only [hx, ↓reduceDIte]

/-- `σ°(a) σ°(b) = σ°(a b)` whenever `b ∈ H`. -/
theorem matExt_mul (σ : Rep H K ι) (a : G) {b : G} (hb : b ∈ H) :
    matExt H σ a * matExt H σ b = matExt H σ (a * b) := by
  by_cases ha : a ∈ H
  · rw [matExt_mem H σ ha, matExt_mem H σ hb, matExt_mem H σ (H.mul_mem ha hb)]
    exact (σ.map_mul ⟨a, ha⟩ ⟨b, hb⟩).symm
  · have hab : a * b ∉ H := fun h => ha (by
      have := H.mul_mem h (H.inv_mem hb)
      rwa [Group.mul_inv_cancel_right] at this)
    rw [matExt_not_mem H σ ha, matExt_not_mem H σ hab]
    apply ext; intro i k
    exact isum_eq_zero fun j => Ring.zero_mul _

/-- `kd (t, i) (s, j) = kd t s · kd i j`. -/
theorem kd_prod {α β : Type _} (t s : α) (i j : β) :
    (kd (t, i) (s, j) : K) = kd t s * kd i j := by
  by_cases h : t = s
  · subst h; rw [kd_self, Ring.one_mul]; exact kd_map (Prod.mk t) (fun _ _ e => by cases e; rfl) i j
  · rw [kd_ne h, Ring.zero_mul]; exact kd_ne (fun e => h (congrArg Prod.fst e))

/-- **Induced representation** `Ind^G_H σ`, on `K^(T × ι)` with `T` the chosen coset
representatives: `Ind σ(g)_{(t,i),(s,j)} = σ°(t⁻¹ g s)_{ij}`, where `σ°(x) = σ(x)` for
`x ∈ H` and `0` otherwise. -/
noncomputable def indRep (σ : Rep H K ι) : Rep G K (CosetReps H × ι) where
  toFun g := fun p q => matExt H σ (p.1.1⁻¹ * g * q.1.1) p.2 q.2
  map_one := by
    apply ext; rintro ⟨t, i⟩ ⟨s, j⟩
    show matExt H σ (t.1⁻¹ * 1 * s.1) i j = kd (t, i) (s, j)
    rw [kd_prod, Group.mul_one]
    by_cases h : t = s
    · subst h
      rw [kd_self, Ring.one_mul, Group.inv_mul_cancel, matExt_mem H σ H.one_mem]
      show σ.toFun 1 i j = _
      rw [σ.map_one]; rfl
    · rw [kd_ne h, Ring.zero_mul, matExt_not_mem H σ (fun hm => h (CosetReps.eq_of_mem H hm))]
      rfl
  map_mul g g' := by
    apply ext; rintro ⟨t, i⟩ ⟨u, k⟩
    show matExt H σ (t.1⁻¹ * (g * g') * u.1) i k =
      isum (fun q : CosetReps H × ι =>
        matExt H σ (t.1⁻¹ * g * q.1.1) i q.2 * matExt H σ (q.1.1⁻¹ * g' * u.1) q.2 k)
    rw [isum_prod]
    have h0 := cosetRep_inv_mul_mem H (g' * u.1)
    rw [isum_single' _ (toRep H (g' * u.1)) (fun s hs => isum_eq_zero fun j => by
      show _ * matExt H σ (s.1⁻¹ * g' * u.1) j k = 0
      rw [matExt_not_mem H σ (x := s.1⁻¹ * g' * u.1) (fun hm => hs (CosetReps.eq_toRep H (by
        rwa [Group.mul_assoc] at hm))), zero_apply, Ring.mul_zero])]
    show _ = (matExt H σ (t.1⁻¹ * g * cosetRep H (g' * u.1)) *
      matExt H σ ((cosetRep H (g' * u.1))⁻¹ * g' * u.1)) i k
    rw [matExt_mul H σ _ (by rw [Group.mul_assoc]; exact h0)]
    have e : t.1⁻¹ * g * cosetRep H (g' * u.1) * ((cosetRep H (g' * u.1))⁻¹ * g' * u.1) =
        t.1⁻¹ * (g * g') * u.1 := by
      simp only [Group.mul_assoc, Group.mul_inv_cancel_left]
    rw [e]

/-- The entries of the induced representation. -/
theorem indRep_apply (σ : Rep H K ι) (g : G) (t s : CosetReps H) (i j : ι) :
    indRep H σ g (t, i) (s, j) = matExt H σ (t.1⁻¹ * g * s.1) i j := rfl

/-! ## The character of an induced representation -/

/-- `tr σ°(x) = χ_σ°(x)`: the trace of the extended matrix is the extended character. -/
theorem trace_matExt {ι : Type} [FiniteType ι] (σ : Rep H C ι) (x : G) :
    trace (matExt H σ x) = ext0 H (character σ) x := by
  by_cases hx : x ∈ H
  · rw [matExt_mem H σ hx, ext0_mem H _ hx]; rfl
  · rw [matExt_not_mem H σ hx, ext0_not_mem H _ hx]
    exact isum_zero

/-- The extension by zero of a class function on `H` is invariant under conjugation by `H`. -/
theorem ext0_conj {f : H → C} (hf : IsClassFunction f) (x : G) {h : G} (hh : h ∈ H) :
    ext0 H f (h⁻¹ * x * h) = ext0 H f x := by
  by_cases hx : x ∈ H
  · have hc : h⁻¹ * x * h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh
    rw [ext0_mem H f hx, ext0_mem H f hc]
    have := hf ⟨x, hx⟩ ⟨h, hh⟩⁻¹
    rw [← this]
    congr 1
    apply Subtype.ext
    show h⁻¹ * x * h = h⁻¹ * x * h⁻¹⁻¹
    rw [Group.inv_inv]
  · have hc : h⁻¹ * x * h ∉ H := fun hm => hx (by
      have key : h * (h⁻¹ * x * h) * h⁻¹ = x := by
        simp only [Group.mul_assoc, Group.mul_inv_cancel_left, Group.mul_inv_cancel,
          Group.mul_one]
      rw [← key]; exact H.mul_mem (H.mul_mem hh hm) (H.inv_mem hh))
    rw [ext0_not_mem H f hx, ext0_not_mem H f hc]

/-- The induced character is a sum over coset representatives:
`Ind f(g) = Σ_t f°(t⁻¹ g t)` for a class function `f` on `H`. -/
theorem indFun_eq_isum_reps {f : H → C} (hf : IsClassFunction f) (g : G) :
    indFun H f g = isum (fun t : CosetReps H => ext0 H f (t.1⁻¹ * g * t.1)) := by
  unfold indFun
  have hinv : isum (fun x : G => ext0 H f (x * g * x⁻¹)) =
      isum (fun y : G => ext0 H f (y⁻¹ * g * y)) := by
    rw [← isum_comp_bij (fun y : G => y⁻¹) (fun a b e => Group.inv_injective e)
      (fun y => ⟨y⁻¹, Group.inv_inv y⟩) (fun x : G => ext0 H f (x * g * x⁻¹))]
    apply isum_congr; intro y
    show ext0 H f (y⁻¹ * g * y⁻¹⁻¹) = _
    rw [Group.inv_inv]
  rw [hinv, ← isum_cosetReps_mul H (fun y : G => ext0 H f (y⁻¹ * g * y)), isum_prod]
  have hin : ∀ t : CosetReps H, isum (fun h : H =>
      ext0 H f ((t.1 * h.1)⁻¹ * g * (t.1 * h.1))) =
      ncast (card H) * ext0 H f (t.1⁻¹ * g * t.1) := fun t => by
    rw [← isum_const]
    apply isum_congr; intro h
    rw [← ext0_conj H hf (t.1⁻¹ * g * t.1) h.2, Group.mul_inv_rev]
    simp only [Group.mul_assoc]
  show natInv (card H) * isum (fun t : CosetReps H => isum (fun h : H =>
      ext0 H f ((t.1 * h.1)⁻¹ * g * (t.1 * h.1)))) = _
  rw [isum_congr hin, ← isum_mul_left, ← Ring.mul_assoc, CommRing.mul_comm (natInv _),
    ncast_mul_natInv (card_group_pos (G := H)), Ring.one_mul]

/-- **Character of an induced representation.** For a complex representation `σ` of `H`,
`χ_{Ind^G_H σ} = Ind χ_σ`: the character of the induced representation is the induced class
function `g ↦ (1/|H|) Σ_{x ∈ G} χ_σ°(x g x⁻¹)`. -/
theorem character_indRep {ι : Type} [FiniteType ι] (σ : Rep H C ι) :
    character (indRep H σ) = indFun H (character σ) := by
  funext g
  rw [indFun_eq_isum_reps H (character_isClassFunction σ)]
  show isum (fun p : CosetReps H × ι => matExt H σ (p.1.1⁻¹ * g * p.1.1) p.2 p.2) = _
  rw [isum_prod]
  exact isum_congr fun t => by
    show trace (matExt H σ (t.1⁻¹ * g * t.1)) = _
    exact trace_matExt H σ _

/-- **Frobenius reciprocity for induced representations.** For complex representations `σ` of
`H` and `ρ` of `G`, `⟨χ_{Ind σ}, χ_ρ⟩_G = ⟨χ_σ, χ_{Res ρ}⟩_H`, with
`⟨χ, ψ⟩_G = (1/|G|) Σ_g χ(g) ψ(g⁻¹)`. -/
theorem frobenius_reciprocity_indRep {ι κ : Type} [FiniteType ι] [FiniteType κ]
    (σ : Rep H C ι) (ρ : Rep G C κ) :
    natInv (card G) * pairing (character (indRep H σ)) (character ρ) =
      natInv (card H) * pairing (character σ) (character (ρ.res H)) := by
  rw [character_indRep]; exact frobenius_reciprocity_character H σ ρ

end Foundations.Langlands
