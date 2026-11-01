import Foundations.Algebra.Quintic

/-!
# A transposition and a 5-cycle generate `S₅`

The previous file proved that the particular pair `(0 1)`, `(0 1 2 3 4)` generates `S₅`. In
the Galois-theoretic argument for `x⁵ - 6x + 3` we do not get to choose the labels: complex
conjugation gives *some* transposition `(a b)` of the five roots, and Cauchy's theorem gives
*some* element `g` of order `5`. This file removes the normalisation.

The argument is a relabelling. An element `g` of `S₅` with `g⁵ = 1` and `g ≠ 1` moves some
point; its orbit then consists of five distinct points, so `g` is a 5-cycle and every point
lies on it. Replacing `g` by a suitable power `h = gᵏ` we may assume `h a = b`. Listing the
points as `a, h a, h² a, h³ a, h⁴ a` defines a permutation `π` with `π i = hⁱ a`, and
conjugating by `π` turns `(a b)` into `(0 1)` and `h` into `(0 1 2 3 4)`. The normalised result
applies to the conjugated subgroup.

**Headline.** `S5_generated_of_transposition`: a subgroup of `S₅` containing a transposition
and an element `g` with `g⁵ = 1`, `g ≠ 1` is all of `S₅`; and `not_solvable_of_transposition`:
such a subgroup is not solvable.
-/

namespace Foundations.Algebra

open Group Perm

universe u

section Orbits

variable {α : Type u}

/-- Applying a power: `gᵐ⁺ⁿ x = gᵐ (gⁿ x)`. -/
theorem perm_pow_add_apply (g : Perm α) (m n : Nat) (x : α) :
    (g ^ (m + n)) x = (g ^ m) ((g ^ n) x) := by
  rw [pow_add]; rfl

/-- Powers of `g` commute with `g` when applied: `gⁿ (g x) = g (gⁿ x)`. -/
theorem perm_pow_comm_apply (g : Perm α) (n : Nat) (x : α) : (g ^ n) (g x) = g ((g ^ n) x) := by
  show (g ^ n * g) x = (g * g ^ n) x
  rw [← pow_succ, pow_succ']

/-- If `g⁵ = 1`, exponents only matter modulo `5`. -/
theorem pow_mod_five {G : Type u} [Group G] {g : G} (h5 : g ^ 5 = 1) (m : Nat) :
    g ^ m = g ^ (m % 5) := by
  conv => lhs; rw [← Nat.div_add_mod m 5]
  rw [pow_add, pow_mul, h5, one_pow, one_mul]

/-- If `g⁵ = 1` and some power `gᵏ` with `0 < k < 5` fixes `x`, then `g` fixes `x`: since `5` is
prime, `g` is itself a power of `gᵏ`. -/
theorem fix_of_pow_fix {g : Perm α} (h5 : g ^ 5 = 1) {k : Nat} (hk0 : 0 < k) (hk : k < 5)
    {x : α} (hx : (g ^ (k : Nat)) x = x) : g x = x := by
  have hiter : ∀ n : Nat, ((g ^ k) ^ n) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => show ((g ^ k) ^ n) ((g ^ k) x) = x; rw [hx, ih]
  obtain ⟨n, hn⟩ : ∃ n, (k * n) % 5 = 1 := by
    match k, hk0, hk with
    | 1, _, _ => exact ⟨1, rfl⟩
    | 2, _, _ => exact ⟨3, rfl⟩
    | 3, _, _ => exact ⟨2, rfl⟩
    | 4, _, _ => exact ⟨4, rfl⟩
  have := hiter n
  rw [← pow_mul, pow_mod_five h5, hn, pow_one] at this
  exact this

/-- The orbit of a moved point has five distinct members: if `g⁵ = 1` and `g x ≠ x`, then
`gⁱ x ≠ gʲ x` for `i < j < 5`. -/
theorem orbit_distinct {g : Perm α} (h5 : g ^ 5 = 1) {x : α} (hx : g x ≠ x) {i j : Nat}
    (hij : i < j) (hj : j < 5) : (g ^ i) x ≠ (g ^ j) x := by
  intro h
  have e : (g ^ (j - i)) ((g ^ i) x) = (g ^ i) x := by
    rw [← perm_pow_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hij), h]
  have hfix := fix_of_pow_fix h5 (by omega) (by omega) e
  rw [← perm_pow_comm_apply] at hfix
  exact hx ((g ^ i).injective hfix)

end Orbits

/-! ## Orbits in `Fin 5` -/

/-- The orbit map `i ↦ gⁱ x` of a moved point. -/
def orbitMap (g : Perm (Fin 5)) (x : Fin 5) (i : Fin 5) : Fin 5 := (g ^ i.val) x

/-- The orbit map of a moved point is injective. -/
theorem orbitMap_injective {g : Perm (Fin 5)} (h5 : g ^ 5 = 1) {x : Fin 5} (hx : g x ≠ x) :
    ∀ i j, orbitMap g x i = orbitMap g x j → i = j := by
  intro i j h
  apply Fin.ext
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact absurd h (orbit_distinct h5 hx hlt j.isLt)
  · exact heq
  · exact absurd h.symm (orbit_distinct h5 hx hgt i.isLt)

/-- **A moved point's orbit is everything.** If `g⁵ = 1` and `g x ≠ x` in `S₅`, every point is
`gⁱ x` for some `i < 5`: `g` is a 5-cycle. -/
theorem orbit_all {g : Perm (Fin 5)} (h5 : g ^ 5 = 1) {x : Fin 5} (hx : g x ≠ x) (y : Fin 5) :
    ∃ i : Fin 5, (g ^ i.val) x = y :=
  FiniteType.surjective_of_injective _ (orbitMap_injective h5 hx) y

/-- If `g⁵ = 1` and `g ≠ 1` in `S₅`, then `g` moves every point. -/
theorem moves_all {g : Perm (Fin 5)} (h5 : g ^ 5 = 1) (h1 : g ≠ 1) (a : Fin 5) : g a ≠ a := by
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ x := Classical.byContradiction fun hno =>
    h1 (ext fun y => Classical.byContradiction fun hy => hno ⟨y, hy⟩)
  obtain ⟨i, rfl⟩ := orbit_all h5 hx a
  intro h
  rw [← perm_pow_comm_apply] at h
  exact hx ((g ^ i.val).injective h)

/-- A permutation of a finite type built from an injective map (whose inverse is chosen using
surjectivity). -/
noncomputable def permOfInjective {n : Nat} (f : Fin n → Fin n)
    (hf : ∀ a b, f a = f b → a = b) : Perm (Fin n) where
  toFun := f
  invFun y := Classical.choose (FiniteType.surjective_of_injective f hf y)
  left_inv x := hf _ _ (Classical.choose_spec (FiniteType.surjective_of_injective f hf (f x)))
  right_inv y := Classical.choose_spec (FiniteType.surjective_of_injective f hf y)

/-- The 5-cycle `c5` is `i ↦ i + 1 (mod 5)`. -/
theorem c5_apply : ∀ i : Fin 5, c5 i = ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ := by decide

/-- **`S₅` is generated by any transposition and any element of order `5`.** A subgroup `H` of
`S₅` containing a transposition `(a b)` and an element `g` with `g⁵ = 1`, `g ≠ 1` (that is, a
5-cycle) contains every permutation of five letters. -/
theorem S5_generated_of_transposition (H : Subgroup (Perm (Fin 5))) {a b : Fin 5} (hab : a ≠ b)
    (ht : swap a b ∈ H) {g : Perm (Fin 5)} (hg : g ∈ H) (h5 : g ^ 5 = 1) (h1 : g ≠ 1) :
    ∀ σ, σ ∈ H := by
  -- a power `h = gᵏ` sends `a` to `b`
  obtain ⟨k, hk⟩ := orbit_all h5 (moves_all h5 h1 a) b
  let h := g ^ k.val
  have hH : h ∈ H := H.pow_mem hg _
  have hh5 : h ^ 5 = 1 := by
    show (g ^ k.val) ^ 5 = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, h5, one_pow]
  have hha : h a ≠ a := by
    show (g ^ k.val) a ≠ a; rw [hk]; exact fun e => hab e.symm
  -- the relabelling `π i = hⁱ a`
  let π := permOfInjective (orbitMap h a) (orbitMap_injective hh5 hha)
  have hπ : ∀ i, π i = (h ^ i.val) a := fun _ => rfl
  have hπ0 : π 0 = a := rfl
  have hπ1 : π 1 = b := by rw [hπ]; show (g ^ k.val * 1) a = b; rw [Group.mul_one]; exact hk
  -- conjugation by `π` normalises the generators
  have hc : π * c5 * π⁻¹ = h := by
    apply ext; intro y
    obtain ⟨i, rfl⟩ := FiniteType.surjective_of_injective _ (fun _ _ e => π.injective e) y
    rw [Group.mul_assoc, mul_apply, mul_apply, Perm.inv_apply_self, c5_apply, hπ, hπ]
    show (h ^ ((i.val + 1) % 5)) a = h ((h ^ i.val) a)
    rw [← pow_mod_five hh5, ← perm_pow_comm_apply]; rfl
  have hs : π * swap 0 1 * π⁻¹ = swap a b := by rw [conj_swap, hπ0, hπ1]
  -- the conjugate subgroup contains the normalised generators
  let K : Subgroup (Perm (Fin 5)) :=
    { carrier := fun σ => π * σ * π⁻¹ ∈ H
      one_mem := by
        show π * 1 * π⁻¹ ∈ H
        rw [Group.mul_one, Group.mul_inv_cancel]; exact H.one_mem
      mul_mem := fun {σ τ} hσ hτ => by
        show π * (σ * τ) * π⁻¹ ∈ H
        have e : π * (σ * τ) * π⁻¹ = (π * σ * π⁻¹) * (π * τ * π⁻¹) := by
          simp only [Group.mul_assoc, Group.inv_mul_cancel_left]
        rw [e]; exact H.mul_mem hσ hτ
      inv_mem := fun {σ} hσ => by
        show π * σ⁻¹ * π⁻¹ ∈ H
        have e : π * σ⁻¹ * π⁻¹ = (π * σ * π⁻¹)⁻¹ := by
          simp only [Group.mul_inv_rev, Group.inv_inv, Group.mul_assoc]
        rw [e]; exact H.inv_mem hσ }
  have hall := S5_generated K (show π * swap 0 1 * π⁻¹ ∈ H by rw [hs]; exact ht)
    (show π * c5 * π⁻¹ ∈ H by rw [hc]; exact hH)
  intro σ
  have := hall (π⁻¹ * σ * π)
  have e : π * (π⁻¹ * σ * π) * π⁻¹ = σ := by
    simp only [Group.mul_assoc, Group.mul_inv_cancel_left, Group.mul_inv_cancel, Group.mul_one]
  have h' : π * (π⁻¹ * σ * π) * π⁻¹ ∈ H := this
  rw [e] at h'; exact h'

/-- **A permutation group of degree `5` containing a transposition and a 5-cycle is not
solvable.** This is the group-theoretic endgame of the insolvability of `x⁵ - 6x + 3`. -/
theorem not_solvable_of_transposition (H : Subgroup (Perm (Fin 5))) {a b : Fin 5} (hab : a ≠ b)
    (ht : swap a b ∈ H) {g : Perm (Fin 5)} (hg : g ∈ H) (h5 : g ^ 5 = 1) (h1 : g ≠ 1) :
    ¬ IsSolvable H := by
  have hall := S5_generated_of_transposition H hab ht hg h5 h1
  exact not_solvable_of_surjective_S5 (Hom.subtype H) fun y => ⟨⟨y, hall y⟩, rfl⟩

end Foundations.Algebra
