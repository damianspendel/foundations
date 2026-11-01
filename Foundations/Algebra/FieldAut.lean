import Foundations.Algebra.Reciprocity

/-!
# Automorphisms of field extensions

Galois's decisive idea (1830) was to study an equation through the group of permutations of
its roots that preserve every algebraic relation among them. In Dedekind's and Artin's modern
form this becomes the group `Aut(L/K)` of **automorphisms of a field extension**: bijections
`σ : L → L` respecting `+` and `×` and fixing every element of the base field `K`.

As in the chapter on constructibility, all fields here are subfields of one ambient field `Ω`.
This file sets up

* the group `Aut(L/K)`, written `FieldAut K L`;
* the **fixed field** of a set of automorphisms;
* **Dedekind's lemma** (1894): distinct multiplicative maps `χ₁, …, χₙ : F → F` are linearly
  independent over `F`;
* and its first consequence: **`Aut(L/K)` has at most `[L : K]` elements.** Concretely, any
  family of pairwise distinct automorphisms has at most `[L : K]` members. (For `n` distinct
  automorphisms with `n > [L : K]`, a linear system with fewer equations than unknowns yields a
  non-trivial linear relation among them, which Dedekind's lemma forbids.)
-/

namespace Foundations.Algebra

open Ring FiniteType VectorSpace Subfield KSubspace

universe u v

variable {Ω : Type u} [CommRing Ω]

/-- Values of finite sums in a subfield: the value of `∑ xᵢ` is `∑ (value of xᵢ)`. -/
theorem Subfield.coe_isum (L : Subfield Ω) {ι : Type v} [FiniteType ι] (f : ι → L) :
    (isum f).1 = isum (fun i => (f i).1) := by
  unfold isum
  induction (elems : List ι) with
  | nil => rfl
  | cons a l ih =>
    show (f a).1 + (lsum (l.map f)).1 = (f a).1 + lsum (l.map fun i => (f i).1)
    rw [ih]

/-- **Automorphism of a field extension** `L/K` (subfields of `Ω`): a bijection `L → L` that
preserves addition and multiplication and fixes every element of `K`. -/
structure FieldAut (K L : Subfield Ω) where
  /-- The map. -/
  toFun : L → L
  /-- Its inverse. -/
  invFun : L → L
  /-- `invFun` undoes `toFun`. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun` undoes `invFun`. -/
  right_inv : ∀ x, toFun (invFun x) = x
  /-- Additivity. -/
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Multiplicativity. -/
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  /-- Elements of `K` are fixed. -/
  fix : ∀ x : L, x.1 ∈ K → toFun x = x

namespace FieldAut

variable {K L : Subfield Ω}

/-- An automorphism is injective. -/
theorem injective (σ : FieldAut K L) {x y : L} (h : σ.toFun x = σ.toFun y) : x = y := by
  rw [← σ.left_inv x, ← σ.left_inv y, h]

/-- Automorphisms with the same values are equal. -/
theorem ext {σ τ : FieldAut K L} (h : ∀ x, σ.toFun x = τ.toFun x) : σ = τ := by
  cases σ with
  | mk f g l r a m fx =>
    cases τ with
    | mk f' g' l' r' a' m' fx' =>
      have hf : f = f' := funext h
      subst hf
      have hg : g = g' := funext fun x => by
        have := l (g' x); rw [r' x] at this; exact this
      subst hg; rfl

/-- Automorphisms fix `0`. -/
theorem map_zero (σ : FieldAut K L) : σ.toFun 0 = 0 := σ.fix 0 K.zero_mem

/-- Automorphisms fix `1`. -/
theorem map_one (σ : FieldAut K L) : σ.toFun 1 = 1 := σ.fix 1 K.one_mem

/-- Automorphisms preserve negation. -/
theorem map_neg (σ : FieldAut K L) (x : L) : σ.toFun (-x) = -σ.toFun x := by
  symm; apply neg_eq_of_add_eq_zero
  rw [← σ.map_add, Ring.add_neg_cancel, σ.map_zero]

/-- Automorphisms preserve finite sums. -/
theorem map_isum (σ : FieldAut K L) {ι : Type v} [FiniteType ι] (f : ι → L) :
    σ.toFun (isum f) = isum (fun i => σ.toFun (f i)) := by
  unfold isum
  induction (elems : List ι) with
  | nil => exact σ.map_zero
  | cons a l ih =>
    show σ.toFun (f a + lsum (l.map f)) = σ.toFun (f a) + lsum (l.map fun i => σ.toFun (f i))
    rw [σ.map_add, ih]

/-- **The Galois group** `Aut(L/K)`: automorphisms under composition. `σ * τ` means "first `τ`,
then `σ`". -/
instance : Group (FieldAut K L) where
  mul σ τ :=
    { toFun := fun x => σ.toFun (τ.toFun x)
      invFun := fun x => τ.invFun (σ.invFun x)
      left_inv := fun x => by simp only [σ.left_inv, τ.left_inv]
      right_inv := fun x => by simp only [σ.right_inv, τ.right_inv]
      map_add := fun x y => by simp only [τ.map_add, σ.map_add]
      map_mul := fun x y => by simp only [τ.map_mul, σ.map_mul]
      fix := fun x hx => by simp only [τ.fix x hx, σ.fix x hx] }
  one :=
    { toFun := fun x => x, invFun := fun x => x, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add := fun _ _ => rfl, map_mul := fun _ _ => rfl,
      fix := fun _ _ => rfl }
  inv σ :=
    { toFun := σ.invFun, invFun := σ.toFun, left_inv := σ.right_inv, right_inv := σ.left_inv
      map_add := fun x y => σ.injective (by rw [σ.right_inv, σ.map_add, σ.right_inv, σ.right_inv])
      map_mul := fun x y => σ.injective (by rw [σ.right_inv, σ.map_mul, σ.right_inv, σ.right_inv])
      fix := fun x hx => σ.injective (by rw [σ.right_inv, σ.fix x hx]) }
  mul_assoc _ _ _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  inv_mul_cancel σ := ext fun x => σ.left_inv x

/-- Applying a composite. -/
@[simp] theorem mul_apply (σ τ : FieldAut K L) (x : L) : (σ * τ).toFun x = σ.toFun (τ.toFun x) :=
  rfl

/-- The identity automorphism. -/
@[simp] theorem one_apply (x : L) : (1 : FieldAut K L).toFun x = x := rfl

/-- An automorphism over `K` that also fixes a larger subfield `M` is an automorphism over `M`. -/
def toOver {M : Subfield Ω} (σ : FieldAut K L) (h : ∀ x : L, x.1 ∈ M → σ.toFun x = x) :
    FieldAut M L :=
  { σ with fix := h }

end FieldAut

/-! ## Fixed fields -/

/-- The **fixed field** of a set `S` of automorphisms of `L`: the elements of `L` fixed by every
member of `S`. -/
def fixedField {K : Subfield Ω} (L : Subfield Ω) (S : FieldAut K L → Prop) : Subfield Ω where
  carrier x := ∃ h : x ∈ L, ∀ σ, S σ → σ.toFun ⟨x, h⟩ = ⟨x, h⟩
  zero_mem := ⟨L.zero_mem, fun σ _ => σ.map_zero⟩
  one_mem := ⟨L.one_mem, fun σ _ => σ.map_one⟩
  add_mem := fun ⟨ha, hfa⟩ ⟨hb, hfb⟩ => ⟨L.add_mem ha hb, fun σ hσ => by
    have := σ.map_add ⟨_, ha⟩ ⟨_, hb⟩
    rw [hfa σ hσ, hfb σ hσ] at this; exact this⟩
  neg_mem := fun ⟨ha, hfa⟩ => ⟨L.neg_mem ha, fun σ hσ => by
    have := σ.map_neg ⟨_, ha⟩
    rw [hfa σ hσ] at this; exact this⟩
  mul_mem := fun ⟨ha, hfa⟩ ⟨hb, hfb⟩ => ⟨L.mul_mem ha hb, fun σ hσ => by
    have := σ.map_mul ⟨_, ha⟩ ⟨_, hb⟩
    rw [hfa σ hσ, hfb σ hσ] at this; exact this⟩
  inv_mem := by
    intro a ⟨ha, hfa⟩ ha0
    obtain ⟨b, hb, hab⟩ := L.inv_mem ha ha0
    refine ⟨b, ⟨hb, fun σ hσ => ?_⟩, hab⟩
    let aL : L := ⟨a, ha⟩
    let bL : L := ⟨b, hb⟩
    have h2 : aL * bL = 1 := Subtype.ext hab
    have h1 : aL * σ.toFun bL = 1 := by
      have := σ.map_mul aL bL
      rw [h2, σ.map_one, hfa σ hσ] at this; exact this.symm
    calc σ.toFun bL = σ.toFun bL * (aL * bL) := by rw [h2, Ring.mul_one]
      _ = (aL * σ.toFun bL) * bL := by ac_rfl
      _ = bL := by rw [h1, Ring.one_mul]

/-- The fixed field lies in `L`. -/
theorem fixedField_le {K L : Subfield Ω} (S : FieldAut K L → Prop) : (fixedField L S).le L :=
  fun _ ⟨h, _⟩ => h

/-- The base field is fixed by everything: `K ⊆ Fix(S)`. -/
theorem le_fixedField {K L : Subfield Ω} (hKL : K.le L) (S : FieldAut K L → Prop) :
    K.le (fixedField L S) :=
  fun x hx => ⟨hKL x hx, fun σ _ => σ.fix _ hx⟩

/-- **Galois connection, order reversal**: more automorphisms fix less. -/
theorem fixedField_anti {K L : Subfield Ω} {S T : FieldAut K L → Prop} (h : ∀ σ, S σ → T σ) :
    (fixedField L T).le (fixedField L S) :=
  fun _ ⟨hx, hf⟩ => ⟨hx, fun σ hσ => hf σ (h σ hσ)⟩

/-! ## Dedekind's lemma -/

/-- **Dedekind's lemma on the independence of characters.** Pairwise distinct maps
`χ₁, …, χₙ : F → F` into a field that are multiplicative (`χ(xy) = χ(x)χ(y)`, `χ(1) = 1`) are
linearly independent over `F`: if `∑ cᵢ χᵢ(x) = 0` for all `x`, then every `cᵢ = 0`. -/
theorem dedekind {F : Type u} [CommRing F] (hF : IsField F) :
    ∀ (n : Nat) (χ : Fin n → F → F), (∀ i x y, χ i (x * y) = χ i x * χ i y) →
      (∀ i, χ i 1 = 1) → (∀ i j, χ i = χ j → i = j) → ∀ c : Fin n → F,
      (∀ x, isum (fun i => c i * χ i x) = 0) → ∀ i, c i = 0 := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ i; exact absurd i.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    intro χ hmul hone hdist c hrel
    have htail : ∀ j : Fin m, c j.succ = 0 := by
      intro j
      have hne : χ j.succ ≠ χ 0 := fun h => absurd (hdist _ _ h) (Fin.succ_ne_zero j)
      obtain ⟨y, hy⟩ : ∃ y, χ j.succ y ≠ χ 0 y := Classical.byContradiction fun hno =>
        hne (funext fun y => Classical.byContradiction fun h => hno ⟨y, h⟩)
      have hrel' : ∀ x, isum (fun i : Fin m => (c i.succ * (χ i.succ y + -χ 0 y)) * χ i.succ x) = 0 := by
        intro x
        have h1 : c 0 * χ 0 (x * y) + isum (fun i : Fin m => c i.succ * χ i.succ (x * y)) = 0 := by
          have := hrel (x * y); rw [isum_fin_succ] at this; exact this
        have h2 : c 0 * χ 0 x + isum (fun i : Fin m => c i.succ * χ i.succ x) = 0 := by
          have := hrel x; rw [isum_fin_succ] at this; exact this
        simp only [hmul] at h1
        have e : isum (fun i : Fin m => (c i.succ * (χ i.succ y + -χ 0 y)) * χ i.succ x) =
            isum (fun i : Fin m => c i.succ * (χ i.succ x * χ i.succ y)) +
              -(isum (fun i : Fin m => c i.succ * χ i.succ x) * χ 0 y) := by
          rw [isum_mul_right, ← isum_neg, ← isum_add]
          congr 1; funext i; grind
        rw [e]
        grind
      have := ih (fun i => χ i.succ) (fun i => hmul i.succ) (fun i => hone i.succ)
        (fun i j h => Fin.succ_inj.1 (hdist _ _ h)) _ hrel' j
      rcases hF.isDomain.2 _ _ this with h | h
      · exact h
      · exact absurd (eq_of_sub_eq_zero h) hy
    have ht : isum (fun i : Fin m => c i.succ * χ i.succ 1) = 0 :=
      isum_eq_zero fun i => by rw [htail i, Ring.zero_mul]
    have hc0 : c 0 = 0 := by
      have e : c 0 * χ 0 1 + isum (fun i : Fin m => c i.succ * χ i.succ 1) = 0 := by
        have := hrel 1; rw [isum_fin_succ] at this; exact this
      rw [ht, hone] at e; grind
    intro i
    cases i using Fin.cases with
    | zero => exact hc0
    | succ j => exact htail j

/-! ## The order of the Galois group -/

/-- **`|Aut(L/K)| ≤ [L : K]`.** For a finite extension `L/K`, any family of pairwise distinct
automorphisms of `L` over `K` has at most `[L : K]` members. -/
theorem card_aut_le (hΩ : IsField Ω) {K L : Subfield Ω} (hKL : K.le L) (hfin : FiniteExt K L hKL)
    {n : Nat} (σ : Fin n → FieldAut K L) (hσ : ∀ i j, σ i = σ j → i = j) : n ≤ deg K L hKL := by
  apply Nat.le_of_not_lt
  intro hlt
  have hFK := K.isField hΩ
  have hFL := L.isField hΩ
  obtain ⟨e, he⟩ := exists_basis hFK hfin
  let eL : Fin (deg K L hKL) → L := fun j => ⟨(e j).1, (e j).2⟩
  let A : Fin (deg K L hKL) → Fin n → L := fun j i => (σ i).toFun (eL j)
  obtain ⟨x, ⟨i0, hi0⟩, hx⟩ := exists_nontrivial_solution hFL n _ A hlt
  have hrel : ∀ l : L, isum (fun i => x i * (σ i).toFun l) = 0 := by
    intro l
    obtain ⟨k, hk⟩ := he.2 ⟨l.1, l.2⟩
    let kL : Fin (deg K L hKL) → L := fun j => ⟨(k j).1, hKL _ (k j).2⟩
    have hl : l = isum (fun j => kL j * eL j) := by
      apply Subtype.ext
      rw [Subfield.coe_isum]
      have := congrArg Subtype.val hk
      rw [KSubspace.coe_isum] at this
      exact this
    have hσl : ∀ i, (σ i).toFun l = isum (fun j => kL j * A j i) := by
      intro i
      rw [hl, FieldAut.map_isum]
      congr 1; funext j
      rw [(σ i).map_mul, (σ i).fix (kL j) (k j).2]
    calc isum (fun i => x i * (σ i).toFun l)
        = isum (fun i => isum (fun j => x i * (kL j * A j i))) := by
          congr 1; funext i; rw [hσl, isum_mul_left]
      _ = isum (fun j => isum (fun i => x i * (kL j * A j i))) := isum_comm _
      _ = isum (fun j => kL j * isum (fun i => A j i * x i)) := by
          congr 1; funext j; rw [isum_mul_left]; congr 1; funext i; grind
      _ = 0 := isum_eq_zero fun j => by rw [hx j, Ring.mul_zero]
  exact hi0 (dedekind hFL n (fun i => (σ i).toFun) (fun i => (σ i).map_mul)
    (fun i => (σ i).map_one) (fun i j h => hσ i j (FieldAut.ext fun y => congrFun h y)) x hrel i0)

end Foundations.Algebra
