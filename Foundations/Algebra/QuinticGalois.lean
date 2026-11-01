import Foundations.Algebra.SplittingField

/-!
# The Galois group of `x⁵ - 6x + 3` is `S₅`, which is not solvable

This file assembles the classical argument (Galois, as presented by Artin and in every
textbook since) for the polynomial `f = x⁵ - 6x + 3` over `ℚ`, with splitting field
`L = ℚ(β₀, …, β₄) ⊆ ℂ` from the previous file.

1. **The permutation representation** (`galRep`). An automorphism `σ ∈ Aut(L/ℚ)` permutes the
   five roots, since `f` has rational coefficients. Writing `σ(βᵢ) = β_{π(i)}` gives a
   homomorphism `Aut(L/ℚ) → S₅`. It is injective (`galRep_injective`): an automorphism fixing
   every root fixes the field `L` they generate.
2. **A transposition** (`galRep_conj`). Complex conjugation fixes the three real roots and swaps
   the two non-real ones, so it maps to the transposition `(3 4)`.
3. **A 5-cycle.** The image `H` of `galRep` acts transitively on the five roots
   (`exists_aut_root`, which uses the irreducibility of `f`). By the orbit–stabiliser theorem
   `5 ∣ |H|`, and by Cauchy's theorem `H` has an element of order `5`.
4. **`H = S₅`.** A transposition and an element of order `5` generate `S₅`
   (`S5_generated_of_transposition`). So `galRep` is onto, hence an isomorphism
   `Aut(L/ℚ) ≅ S₅` (`galoisGroup_iso_S5`).
5. **Not solvable.** `S₅` is not solvable, so neither is `Aut(L/ℚ)`
   (`quintic_galois_not_solvable`).

**Galois groups.** Here the Galois group is `Aut(L/ℚ)`, the group `FieldAut Qc L` of field
automorphisms of the splitting field `L ⊆ ℂ`. The argument does not use `|Aut(L/ℚ)| = [L : ℚ]`:
the factor `5` in the group order comes from transitivity on the roots instead. The project
does not prove that `L/ℚ` is Galois in the sense of `IsGalois`, or compute `[L : ℚ] = 120`.

**What remains.** *Galois's criterion* (solvable by radicals ⇒ solvable Galois group) is not
formalised in this project. The theorem proved is therefore the group-theoretic statement
"the Galois group of `x⁵ - 6x + 3` over `ℚ` is `S₅` and is not solvable", not the
statement that the roots cannot be expressed by radicals. The full Galois correspondence
(every intermediate field is a fixed field) is also not formalised; see
`GaloisCorrespondence.lean`.
-/

namespace Foundations.Algebra

open Polynomial Subfield Group Perm

universe u v

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## A finite type structure on permutations -/

/-- A type that injects into a finite type is finite. -/
@[instance_reducible] noncomputable def FiniteType.ofInjective {α : Type u} {β : Type v} [FiniteType β] (e : α → β)
    (he : ∀ a b, e a = e b → a = b) : FiniteType α where
  elems := (FiniteType.elems : List {b : β // ∃ a, e a = b}).map (fun s => Classical.choose s.2)
  nodup := FiniteType.nodup_map_of_injective (fun s t h => by
      apply Subtype.ext
      rw [← Classical.choose_spec s.2, ← Classical.choose_spec t.2, h]) FiniteType.nodup
  complete a := by
    refine List.mem_map.2 ⟨⟨e a, a, rfl⟩, FiniteType.complete _, ?_⟩
    exact he _ _ (Classical.choose_spec (⟨a, rfl⟩ : ∃ a', e a' = e a))

/-- **The symmetric group `Sₙ` is finite.** -/
noncomputable instance Perm.instFinite (n : Nat) : FiniteType (Perm (Fin n)) :=
  FiniteType.ofInjective (fun σ : Perm (Fin n) => σ.toFun) (fun _ _ h =>
    Perm.ext fun x => congrFun h x)

/-- Powers in a subgroup are powers in the group. -/
theorem Subgroup.coe_pow {G : Type u} [Group G] (H : Subgroup G) (g : H) :
    ∀ n : Nat, (g ^ n).1 = g.1 ^ n
  | 0 => rfl
  | n + 1 => by
    show (g ^ n * g).1 = g.1 ^ n * g.1
    rw [Subgroup.coe_mul, Subgroup.coe_pow H g n]

/-- A subgroup of `Perm α` acts on `α`. -/
instance Subgroup.permAction {α : Type u} (H : Subgroup (Perm α)) : MulAction H α where
  smul g x := g.1 x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-! ## The permutation representation -/

/-- An automorphism of `L` viewed as a ring homomorphism. -/
def FieldAut.toRingHom {Ω : Type u} [CommRing Ω] {K L : Subfield Ω} (σ : FieldAut K L) :
    RingHom L L where
  toFun := σ.toFun
  map_add := σ.map_add
  map_mul := σ.map_mul
  map_one := σ.map_one

/-- The root `βᵢ` as an element of `L`. -/
noncomputable def rootL (i : Fin 5) : L := ⟨qβ i, qβ_mem i⟩

/-- **Automorphisms permute the roots**: `σ(βᵢ)` is again a root of `f`. -/
theorem aut_root (σ : FieldAut Qc L) (i : Fin 5) :
    eval (σ.toFun (rootL i)).1 (quinticPoly ℂ) = 0 :=
  RingHom.map_quintic_root L.incl (RingHom.map_quintic_root σ.toRingHom
    (root_in_L (x := rootL i) (qβ_spec.2.1 i)))

/-- The index `π(i)` with `σ(βᵢ) = β_{π(i)}`. -/
noncomputable def permFun (σ : FieldAut Qc L) (i : Fin 5) : Fin 5 :=
  Classical.choose (qβ_enum _ (aut_root σ i))

/-- `β_{π(i)} = σ(βᵢ)`. -/
theorem permFun_spec (σ : FieldAut Qc L) (i : Fin 5) : qβ (permFun σ i) = (σ.toFun (rootL i)).1 :=
  Classical.choose_spec (qβ_enum _ (aut_root σ i))

/-- `π` is injective. -/
theorem permFun_injective (σ : FieldAut Qc L) : ∀ i j, permFun σ i = permFun σ j → i = j := by
  intro i j h
  have := congrArg qβ h
  rw [permFun_spec, permFun_spec] at this
  have e := σ.injective (Subtype.ext this)
  exact qβ_spec.1 i j (congrArg Subtype.val e)

/-- The permutation of the roots induced by `σ`. -/
noncomputable def permOf (σ : FieldAut Qc L) : Perm (Fin 5) :=
  permOfInjective (permFun σ) (permFun_injective σ)

/-- `σ(βᵢ) = β_{π(i)}`, in `L`. -/
theorem permOf_spec (σ : FieldAut Qc L) (i : Fin 5) : σ.toFun (rootL i) = rootL (permOf σ i) :=
  Subtype.ext (permFun_spec σ i).symm

/-- **The permutation representation** `Aut(L/ℚ) → S₅` on the five roots. -/
noncomputable def galRep : FieldAut Qc L →* Perm (Fin 5) where
  toFun := permOf
  map_mul σ τ := by
    apply Perm.ext; intro i
    apply qβ_spec.1
    show qβ (permFun (σ * τ) i) = qβ (permFun σ (permFun τ i))
    rw [permFun_spec, permFun_spec, FieldAut.mul_apply]
    show (σ.toFun (τ.toFun (rootL i))).1 = _
    rw [permOf_spec τ i]; rfl

/-- **The representation is faithful.** An automorphism fixing every root is the identity. -/
theorem galRep_injective : ∀ σ τ, galRep σ = galRep τ → σ = τ := by
  intro σ τ h
  have hfix : ∀ i, (τ⁻¹ * σ).toFun (rootL i) = rootL i := by
    intro i
    rw [FieldAut.mul_apply, permOf_spec σ i]
    show τ.invFun (rootL (galRep σ i)) = rootL i
    rw [h]
    change τ.invFun (rootL (permOf τ i)) = rootL i
    rw [← permOf_spec τ i]; exact τ.left_inv _
  -- the fixed field of `τ⁻¹ σ` contains `ℚ` and every root, hence all of `L`
  let ρ := τ⁻¹ * σ
  have hL := L_le (M := fixedField L (fun φ => φ = ρ)) (le_fixedField Qc_le_L _)
    (fun i => ⟨qβ_mem i, fun φ hφ => by rw [hφ]; exact hfix i⟩)
  have hρ : ρ = 1 := FieldAut.ext fun x => by
    obtain ⟨_, hx⟩ := hL x.1 x.2
    exact hx ρ rfl
  calc σ = τ * (τ⁻¹ * σ) := by rw [← Group.mul_assoc, Group.mul_inv_cancel, Group.one_mul]
    _ = τ := by rw [show τ⁻¹ * σ = 1 from hρ, Group.mul_one]

/-- **Complex conjugation acts as the transposition `(3 4)`**: it fixes the three real roots
and swaps the two non-real ones. -/
theorem galRep_conj : galRep conjAut = swap 3 4 := by
  obtain ⟨_, _, h0, h1, h2, _, h4⟩ := qβ_spec
  have hc : ∀ i, qβ (galRep conjAut i) = Foundations.Numbers.C.conj (qβ i) := by
    intro i; rw [show qβ (galRep conjAut i) = (conjAut.toFun (rootL i)).1 from permFun_spec _ i]
    rfl
  have real : ∀ i : Fin 5, (qβ i).im = 0 → galRep conjAut i = i := fun i hi =>
    qβ_spec.1 _ _ (by rw [hc]; exact (conj_eq_self_iff _).2 hi)
  apply Perm.ext; intro i
  obtain ⟨i, hi⟩ := i
  match i, hi with
  | 0, _ => show galRep conjAut 0 = swap 3 4 0; rw [real 0 h0]; rfl
  | 1, _ => show galRep conjAut 1 = swap 3 4 1; rw [real 1 h1]; rfl
  | 2, _ => show galRep conjAut 2 = swap 3 4 2; rw [real 2 h2]; rfl
  | 3, _ =>
    show galRep conjAut 3 = swap 3 4 3
    exact qβ_spec.1 _ _ (by rw [hc, ← h4]; rfl)
  | 4, _ =>
    show galRep conjAut 4 = swap 3 4 4
    exact qβ_spec.1 _ _ (by
      rw [hc]; show _ = qβ 3; rw [h4]; exact Foundations.Numbers.C.conj_conj _)

/-! ## The image is all of `S₅` -/

/-- The image of the Galois group in `S₅`. -/
noncomputable def galImage : Subgroup (Perm (Fin 5)) := Subgroup.map galRep Subgroup.top

/-- **The image acts transitively on the roots.** -/
theorem galImage_transitive (j : Fin 5) : ∃ g : galImage, g • (0 : Fin 5) = j := by
  obtain ⟨σ, hσ⟩ := exists_aut_root j
  refine ⟨⟨galRep σ, σ, trivial, rfl⟩, ?_⟩
  apply qβ_spec.1
  show qβ (permFun σ 0) = qβ j
  rw [permFun_spec]; exact hσ

/-- **`5` divides the order of the image** (orbit–stabiliser). -/
theorem five_dvd_card_galImage : 5 ∣ FiniteType.card galImage := by
  have h := MulAction.count_orbit_dvd (G := galImage) (X := Fin 5) 0
  have hc : FiniteType.count (MulAction.orbit galImage (0 : Fin 5)) = 5 := by
    rw [(FiniteType.count_eq_card (P := MulAction.orbit galImage (0 : Fin 5))).2
      (fun y => galImage_transitive y), FiniteType.card_fin]
  rw [hc] at h; exact h

/-- `5` is prime. -/
theorem prime_five : IsPrime 5 := ⟨by decide, fun d hd => by
  have : d ≤ 5 := Nat.le_of_dvd (by decide) hd
  match d, this, hd with
  | 0, _, h => exact absurd h (by decide)
  | 1, _, _ => exact Or.inl rfl
  | 2, _, h => exact absurd h (by decide)
  | 3, _, h => exact absurd h (by decide)
  | 4, _, h => exact absurd h (by decide)
  | 5, _, _ => exact Or.inr rfl⟩

/-- **The Galois group contains a 5-cycle**: by Cauchy's theorem the image has an element of
order `5`. -/
theorem galImage_five_cycle : ∃ g : Perm (Fin 5), g ∈ galImage ∧ g ^ 5 = 1 ∧ g ≠ 1 := by
  obtain ⟨g, hg⟩ := cauchy prime_five five_dvd_card_galImage
  refine ⟨g.1, g.2, ?_, ?_⟩
  · have h5 := pow_orderOf g
    rw [hg] at h5
    rw [← Subgroup.coe_pow, h5]; rfl
  · intro h
    have h1 : g ^ 1 ≠ 1 := pow_ne_one_of_lt_orderOf g (by decide) (by rw [hg]; decide)
    apply h1; rw [Group.pow_one]; exact Subtype.ext h

/-- **The representation is onto `S₅`.** -/
theorem galRep_surjective : ∀ π : Perm (Fin 5), ∃ σ, galRep σ = π := by
  obtain ⟨g, hg, h5, h1⟩ := galImage_five_cycle
  have ht : swap (3 : Fin 5) 4 ∈ galImage := ⟨conjAut, trivial, galRep_conj⟩
  intro π
  obtain ⟨σ, _, hσ⟩ := S5_generated_of_transposition galImage (a := 3) (b := 4) (by decide) ht hg
    h5 h1 π
  exact ⟨σ, hσ⟩

/-- **The Galois group of `x⁵ - 6x + 3` over `ℚ` is `S₅`.** The action on the five complex roots
is an isomorphism `Aut(L/ℚ) ≅ S₅`, where `L ⊆ ℂ` is the splitting field. -/
noncomputable def galoisGroup_iso_S5 : FieldAut Qc L ≃* Perm (Fin 5) :=
  Iso.ofBijective galRep galRep_injective galRep_surjective

/-- **The Galois group of `x⁵ - 6x + 3` over `ℚ` is not solvable.** The group `Aut(L/ℚ)` of
automorphisms of the splitting field `L = ℚ(β₀, …, β₄) ⊆ ℂ` maps onto `S₅`, which is not
solvable. (With Galois's criterion, which is not formalised here, this means the roots of
`x⁵ - 6x + 3` cannot be expressed by radicals.) -/
theorem quintic_galois_not_solvable : ¬ IsSolvable (FieldAut Qc L) :=
  not_solvable_of_surjective_S5 galRep galRep_surjective

end Foundations.Algebra
