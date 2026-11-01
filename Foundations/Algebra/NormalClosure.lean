import Foundations.Algebra.RadicalTower

/-!
# The normal closure of a radical tower

A radical tower `ℚ ⊆ K₁ ⊆ ⋯ ⊆ Kₘ` need not be symmetric: `∛2` generates `ℚ(∛2) ⊆ ℝ`, while its
conjugates `ω∛2, ω²∛2` are not real. Galois's argument needs a tower whose top field `M` is
**stable**: every embedding `M → ℂ` maps `M` into itself, so that embeddings of `M` are
automorphisms of `M` and automorphisms of subfields extend to automorphisms of `M`. The cure is
to adjoin, along with each radical, all of its conjugates, together with enough roots of unity.

This file carries out that construction, refining the tower into a **Kummer chain** (steps of
prime degree, see `Kummer`) along the way.

* **Enumerating automorphisms** (`exists_aut_enum`). Since `|Aut(M/ℚ)| ≤ [M : ℚ]`
  (`card_aut_le`), a family of distinct automorphisms cannot be extended forever, so some finite
  family `σ₁, …, σᵣ` lists them all.
* **One prime step** (`closure_prime`). Let `M = gen ℚ m` be stable, `c ∈ M`, `p` prime. Adjoin a
  primitive `p`-th root of unity `ζ`, and then a `p`-th root `yᵢ` of each conjugate `σᵢ(c)`. The new
  field `M'` contains **every** `p`-th root of `c` (each is `ζᵏ y`, by `RootsOfUnity`), the new
  steps are Kummer steps, and `M'` is again stable: an embedding `τ` of `M'` restricts to an
  automorphism `ρ = σⱼ` of `M`, sends `ζ` to a power of `ζ`, and sends `yᵢ` to a `p`-th root of
  `ρ(σᵢ(c)) = σₖ(c)`, which is `ζˡ yₖ ∈ M'`.
* **One radical** (`closure_root`). An `n`-th root with `n = p · k` is a `k`-th root of a `p`-th
  root; strong induction on `n` reduces to prime steps.
* **The whole tower** (`exists_stable_kummer`): every radical tower lies in the field of a Kummer
  chain whose field is stable.
-/

namespace Foundations.Algebra

open Polynomial Subfield

universe u

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Enumerating the automorphisms of a finite extension -/

/-- Extend a family `σ : Fin k → G` by one more member `τ`. -/
def snocFam {G : Type u} {k : Nat} (σ : Fin k → G) (τ : G) : Fin (k + 1) → G :=
  fun i => if h : i.val < k then σ ⟨i.val, h⟩ else τ

/-- Extending an injective family by a new member keeps it injective. -/
theorem snocFam_injective {G : Type u} {k : Nat} (σ : Fin k → G) (τ : G)
    (hσ : ∀ i j, σ i = σ j → i = j) (hτ : ∀ i, σ i ≠ τ) :
    ∀ i j, snocFam σ τ i = snocFam σ τ j → i = j := by
  intro i j h
  unfold snocFam at h
  by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp only [hi, hj, dite_true,
    dite_false] at h
  · have := congrArg Fin.val (hσ _ _ h); exact Fin.ext this
  · exact absurd h (hτ _)
  · exact absurd h.symm (hτ _)
  · exact Fin.ext (by omega)

/-- **The automorphisms of a finite extension can be listed.** If `M/K` is finite, there is a
finite family `σ₁, …, σᵣ` containing every element of `Aut(M/K)`. -/
theorem exists_aut_enum {K M : Subfield ℂ} (hKM : K.le M) (hfin : FiniteExt K M hKM) :
    ∃ (r : Nat) (σ : Fin r → FieldAut K M), ∀ τ, ∃ i, σ i = τ := by
  have key : ∀ k, (∃ σ : Fin k → FieldAut K M, ∀ i j, σ i = σ j → i = j) ∨
      (∃ (r : Nat) (σ : Fin r → FieldAut K M), ∀ τ, ∃ i, σ i = τ) := by
    intro k
    induction k with
    | zero => exact Or.inl ⟨fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      rcases ih with ⟨σ, hσ⟩ | h
      · by_cases hs : ∀ τ, ∃ i, σ i = τ
        · exact Or.inr ⟨k, σ, hs⟩
        · obtain ⟨τ, hτ⟩ := Classical.not_forall.1 hs
          exact Or.inl ⟨snocFam σ τ, snocFam_injective σ τ hσ fun i hi => hτ ⟨i, hi⟩⟩
      · exact Or.inr h
  rcases key (deg K M hKM + 1) with ⟨σ, hσ⟩ | h
  · have := card_aut_le C.isField hKM hfin σ hσ; omega
  · exact h

/-! ## Stable fields -/

/-- A subfield `M ⊆ ℂ` is **stable** if every embedding `M → ℂ` maps `M` into itself. -/
def Stable (M : Subfield ℂ) : Prop := ∀ (τ : RingHom M ℂ) (y : M), τ.toFun y ∈ M

/-- `ℚ` is stable: embeddings fix the rationals. -/
theorem stable_Qc : Stable Qc := fun τ y => by rw [ringHom_fix_Qc τ y y.2]; exact y.2

/-- **Embeddings of a stable tower are automorphisms.** An embedding `τ : gen ℚ m → ℂ` of a
stable field is (the restriction of) an automorphism of `gen ℚ m` over `ℚ`. -/
noncomputable def genAut {m : List ℂ} (hst : Stable (gen Qc m)) (τ : RingHom (gen Qc m) ℂ) :
    FieldAut Qc (gen Qc m) :=
  autOfRingHom C.isField (le_gen Qc m) (gen_finite Qc m)
    { toFun := fun y => ⟨τ.toFun y, hst τ y⟩
      map_add := fun a b => Subtype.ext (τ.map_add a b)
      map_mul := fun a b => Subtype.ext (τ.map_mul a b)
      map_one := Subtype.ext τ.map_one }
    (fun x hx => Subtype.ext (ringHom_fix_Qc τ x hx))

/-- The automorphism `genAut τ` acts as `τ`. -/
theorem genAut_apply {m : List ℂ} (hst : Stable (gen Qc m)) (τ : RingHom (gen Qc m) ℂ)
    (y : gen Qc m) : ((genAut hst τ).toFun y).1 = τ.toFun y := rfl

/-! ## One prime step -/

/-- Appending Kummer radicals over `ζ :: m`: if every `y` in `ys` has `y^p ∈ gen ℚ m`, and `ζ` is
a `p`-th root of unity `≠ 1`, then `ys ++ ζ :: m` is a Kummer chain. -/
theorem kummerChain_append {m : List ℂ} (hm : KummerChain m) {p : Nat} (hp : IsPrime p) {ζ : ℂ}
    (hζp : rpow ζ p = 1) (hζ1 : ζ ≠ 1) :
    ∀ ys : List ℂ, (∀ y, y ∈ ys → rpow y p ∈ gen Qc m) → KummerChain (ys ++ ζ :: m)
  | [], _ => KummerChain.cons p ⟨hp, Or.inl hζp⟩ hm
  | y :: ys, h => by
    have hrest := kummerChain_append hm hp hζp hζ1 ys fun z hz => h z (List.mem_cons_of_mem y hz)
    have hζmem : ζ ∈ gen Qc (ys ++ ζ :: m) :=
      gen_le_append Qc ys _ _ (KummerChain.mem (KummerChain.of_append [] (l := ζ :: m)
        (KummerChain.of_append ys hrest)) ζ List.mem_cons_self)
    have hmle : (gen Qc m).le (gen Qc (ys ++ ζ :: m)) :=
      le_trans (gen_le_cons Qc ζ m) (gen_le_append Qc ys _)
    exact KummerChain.cons p ⟨hp, Or.inr ⟨⟨ζ, hζmem, hζp, hζ1⟩, hmle _ (h y List.mem_cons_self)⟩⟩
      hrest

/-- **One prime step of the closure.** If `gen ℚ m` is stable, `c ∈ gen ℚ m` and `p` is prime,
the chain can be extended so that the new field is still stable and contains **every** `p`-th
root of `c`. -/
theorem closure_prime (m : List ℂ) (hm : KummerChain m) (hst : Stable (gen Qc m)) {c : ℂ}
    (hc : c ∈ gen Qc m) {p : Nat} (hp : IsPrime p) :
    ∃ a, KummerChain (a ++ m) ∧ Stable (gen Qc (a ++ m)) ∧
      ∀ y, rpow y p = c → y ∈ gen Qc (a ++ m) := by
  have hp0 : 0 < p := by have := hp.1; omega
  obtain ⟨r, σ, hσ⟩ := exists_aut_enum (le_gen Qc m) (gen_finite Qc m)
  obtain ⟨ζ, hζp, hζ1⟩ := exists_root_of_unity hp
  let C0 : gen Qc m := ⟨c, hc⟩
  let cs : Fin r → ℂ := fun i => ((σ i).toFun C0).1
  have hcs : ∀ i, cs i ∈ gen Qc m := fun i => ((σ i).toFun C0).2
  let ys : Fin r → ℂ := fun i => Classical.choose (exists_rpow_eq (cs i) hp0)
  have hys : ∀ i, rpow (ys i) p = cs i := fun i => Classical.choose_spec (exists_rpow_eq (cs i) hp0)
  let a : List ℂ := List.ofFn ys ++ [ζ]
  have ha : a ++ m = List.ofFn ys ++ ζ :: m := by simp [a]
  have hchain : KummerChain (a ++ m) := by
    rw [ha]
    refine kummerChain_append hm hp hζp hζ1 _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    rw [hys]; exact hcs i
  have hmem : ∀ x, x ∈ a ++ m → x ∈ gen Qc (a ++ m) := KummerChain.mem hchain
  have hζM : ζ ∈ gen Qc (a ++ m) := hmem ζ (by simp [a])
  have hysM : ∀ i, ys i ∈ gen Qc (a ++ m) := fun i => hmem _ (by simp [a, List.mem_ofFn])
  have hMM : (gen Qc m).le (gen Qc (a ++ m)) := gen_le_append Qc a m
  -- every `p`-th root of a conjugate `cs j` lies in the new field
  have hroots : ∀ j y, rpow y p = cs j → y ∈ gen Qc (a ++ m) := by
    intro j y hy
    by_cases h0 : ys j = 0
    · have : y = 0 := by
        apply eq_zero_of_rpow_eq_zero C.isField.isDomain (n := p)
        rw [hy, ← hys j, h0]
        obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        rw [hq, zero_rpow_succ]
      rw [this]; exact Subfield.zero_mem _
    · obtain ⟨k, hk⟩ := eq_mul_of_rpow_eq C.isField hp hζp hζ1 h0 (by rw [hy, hys])
      rw [hk]; exact Subfield.mul_mem _ (rpow_mem hζM k) (hysM j)
  refine ⟨a, hchain, ?_, ?_⟩
  · -- stability
    intro τ y
    let ρ : RingHom (gen Qc m) ℂ := τ.comp (Subfield.inclusion hMM)
    have hpow : ∀ (x : ℂ) (hx : x ∈ gen Qc (a ++ m)),
        rpow (τ.toFun ⟨x, hx⟩) p = τ.toFun ⟨rpow x p, rpow_mem hx p⟩ := by
      intro x hx
      rw [← RingHom.map_rpow]; congr 1; exact Subtype.ext (Subfield.coe_rpow _ _ _)
    have hζP : τ.toFun ⟨ζ, hζM⟩ ∈ gen Qc (a ++ m) := by
      have hu : rpow (τ.toFun ⟨ζ, hζM⟩) p = 1 := by
        rw [hpow]
        have e1 : (⟨rpow ζ p, rpow_mem hζM p⟩ : gen Qc (a ++ m)) = 1 := Subtype.ext hζp
        rw [e1, τ.map_one]
      obtain ⟨k, _, hk⟩ := eq_rpow_of_rpow_eq_one C.isField hp hζp hζ1 hu
      rw [hk]; exact rpow_mem hζM k
    have hP : (gen (gen Qc m) a).le (preimage τ (gen Qc (a ++ m))) := by
      apply gen_le
      · intro z hz
        exact ⟨hMM z hz, hMM _ (hst ρ ⟨z, hz⟩)⟩
      · intro x hx
        refine ⟨hmem x (List.mem_append_left m hx), ?_⟩
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
          -- `τ(yᵢ)` is a `p`-th root of `ρ(σᵢ c) = σⱼ c`
          obtain ⟨j, hj⟩ := hσ (genAut hst ρ * σ i)
          apply hroots j
          rw [hpow]
          have e1 : (⟨rpow (ys i) p, rpow_mem (hysM i) p⟩ : gen Qc (a ++ m)) =
              ⟨cs i, hMM _ (hcs i)⟩ := Subtype.ext (hys i)
          rw [e1]
          show ρ.toFun ((σ i).toFun C0) = ((σ j).toFun C0).1
          rw [hj]; rfl
        · have hxζ : x = ζ := List.mem_singleton.1 hx
          subst hxζ
          exact hζP
    have hy : y.1 ∈ gen (gen Qc m) a := by rw [← gen_append]; exact y.2
    obtain ⟨_, h⟩ := hP y.1 hy
    exact h
  · -- every `p`-th root of `c = cs i₀` (with `σ i₀ = 1`)
    intro y hy
    obtain ⟨i0, hi0⟩ := hσ 1
    exact hroots i0 y (by rw [hy]; show c = ((σ i0).toFun C0).1; rw [hi0]; rfl)

/-! ## Arbitrary radicals and whole towers -/

/-- **One radical step of the closure.** If `gen ℚ m` is stable and `xⁿ ∈ gen ℚ m` (`n ≥ 1`), the
Kummer chain can be extended to a stable one containing `x`. -/
theorem closure_root (n : Nat) : ∀ (m : List ℂ), KummerChain m → Stable (gen Qc m) →
    ∀ x : ℂ, 0 < n → rpow x n ∈ gen Qc m →
      ∃ a, KummerChain (a ++ m) ∧ Stable (gen Qc (a ++ m)) ∧ x ∈ gen Qc (a ++ m) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m hm hst x hn hx
    by_cases h1 : n = 1
    · subst h1; rw [rpow_one'] at hx
      exact ⟨[], hm, hst, hx⟩
    obtain ⟨p, hp, k, rfl⟩ := exists_prime_factor (m := n) (by omega)
    have hp2 := hp.1
    have hk : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; simp at hn
    have hkn : k < p * k := by
      calc k = 1 * k := (Nat.one_mul k).symm
        _ < p * k := Nat.mul_lt_mul_of_pos_right (by omega) hk
    rw [Nat.mul_comm, rpow_mul'] at hx
    obtain ⟨a₁, hc₁, hs₁, hr₁⟩ := closure_prime m hm hst hx hp
    obtain ⟨a₂, hc₂, hs₂, hx₂⟩ := ih k hkn (a₁ ++ m) hc₁ hs₁ x hk (hr₁ _ rfl)
    refine ⟨a₂ ++ a₁, ?_, ?_, ?_⟩ <;> rw [List.append_assoc]
    · exact hc₂
    · exact hs₂
    · exact hx₂

/-- **The normal closure of a radical tower.** Every radical tower over `ℚ` lies in the field of
a Kummer chain that is stable under all embeddings into `ℂ`. -/
theorem exists_stable_kummer {l : List ℂ} (hl : RadicalChain l) :
    ∃ m, KummerChain m ∧ Stable (gen Qc m) ∧ (gen Qc l).le (gen Qc m) := by
  induction hl with
  | nil => exact ⟨[], KummerChain.nil, stable_Qc, le_refl _⟩
  | @cons x l n hn hx _ ih =>
    obtain ⟨m, hm, hst, hle⟩ := ih
    obtain ⟨a, hc, hs, hxa⟩ := closure_root n m hm hst x hn (hle _ hx)
    exact ⟨a ++ m, hc, hs, adj_le (le_trans hle (gen_le_append Qc a m)) fun _ => hxa⟩

end Foundations.Algebra
