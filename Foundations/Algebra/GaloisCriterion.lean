import Foundations.Algebra.NormalClosure

/-!
# Galois's criterion: radicals force a solvable group

This file proves the direction of Galois's criterion needed for the quintic: **if a root of
`f = x⁵ - 6x + 3` is expressible by radicals, then the Galois group `Aut(L/ℚ)` of its splitting
field is solvable.** The argument has three parts.

1. **Kummer chains have solvable automorphism groups** (`kummer_aut_solvable`). Let
   `M = ℚ(x₁, …, xₘ)` be the field of a Kummer chain and `G = Aut(M/ℚ)`, with derived series
   `G = G⁽⁰⁾ ⊇ G⁽¹⁾ ⊇ ⋯`. By induction on `i`, **every element of `G⁽ⁱ⁾` fixes
   `Kᵢ = ℚ(x₁, …, xᵢ)`**: elements of `G⁽ⁱ⁺¹⁾` are products of commutators `[a, b]` with `a, b ∈ G⁽ⁱ⁾`;
   such `a, b` fix `Kᵢ`, so by `Kummer` their commutator fixes `Kᵢ` and `xᵢ₊₁`, hence all of
   `Kᵢ₊₁ = Kᵢ(xᵢ₊₁)` (`fixes_adj`). At `i = m`, `G⁽ᵐ⁾` fixes `M` and so is trivial. Notice that
   no quotient groups, normal subgroups or intermediate-field correspondence are needed: the
   derived series is tracked directly through the tower.
2. **Restriction onto `Aut(L/ℚ)`** (`restrictHom`, `restrictHom_surjective`). If `L ⊆ M` and `M` is
   stable, restricting automorphisms of `M` to `L` (they map `L` into `L` by
   `embedding_maps_L`) is a group homomorphism `Aut(M/ℚ) → Aut(L/ℚ)`. It is **onto**: an
   automorphism of `L` is an embedding `L → ℂ`, which extends to an embedding `M → ℂ`
   (`extend_to`), which is an automorphism of `M` because `M` is stable (`genAut`).
3. **The splitting field lies in the closure** (`L_le_of_root_mem`). If one root `β` of `f` lies in
   the stable field `M`, so do all of them: by irreducibility the assignment `β ↦ βⱼ` defines an
   embedding `ℚ(β) → ℂ`, which extends to `M → ℂ` and maps `M` into `M`.

Since homomorphic images of solvable groups are solvable (`isSolvable_of_surjective`), the
criterion follows (`galois_criterion`). Parts 1 and 2 are stated for any stable Kummer chain
containing `L`; only part 3 is specific to the quintic (the general form of Galois's criterion
for an arbitrary polynomial is not formalised here).
-/

namespace Foundations.Algebra

open Polynomial Subfield Group

universe u

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Kummer chains have solvable automorphism groups -/

/-- **The derived series descends the tower.** For a Kummer chain `m = m₁ ++ m₂`, every element of
the `|m₂|`-th derived subgroup of `Aut(gen ℚ m / ℚ)` fixes the subfield `gen ℚ m₂`. -/
theorem derived_fixes {m : List ℂ} (hm : KummerChain m) :
    ∀ (m₂ m₁ : List ℂ), m = m₁ ++ m₂ →
      ∀ σ, σ ∈ derivedSeries (FieldAut Qc (gen Qc m)) m₂.length → σ.Fixes (gen Qc m₂) := by
  intro m₂
  induction m₂ with
  | nil => intro _ _ σ _ y hy; exact σ.fix y hy
  | cons x m₃ ih =>
    intro m₁ e σ hσ
    have e' : m = (m₁ ++ [x]) ++ m₃ := by rw [e]; simp
    have ihK := ih (m₁ ++ [x]) e'
    have hchain : KummerChain (x :: m₃) := KummerChain.of_append m₁ (e ▸ hm)
    obtain ⟨p, hs⟩ : ∃ p, KummerStep (gen Qc m₃) x p := by
      cases hchain with | cons p hs _ => exact ⟨p, hs⟩
    have hle : (gen Qc (x :: m₃)).le (gen Qc m) := by rw [e]; exact gen_le_append Qc m₁ _
    have hKM : (gen Qc m₃).le (gen Qc m) := le_trans (gen_le_cons Qc x m₃) hle
    have hxM : x ∈ gen Qc m :=
      hle _ (KummerChain.mem hchain x List.mem_cons_self)
    have hσ' : Closure (fun z => ∃ a b, a ∈ derivedSeries _ m₃.length ∧
        b ∈ derivedSeries _ m₃.length ∧ z = commutator a b) σ := hσ
    clear hσ
    induction hσ' with
    | of h =>
      obtain ⟨a, b, ha, hb, rfl⟩ := h
      obtain ⟨hK, hx⟩ := commutator_fixes_step C.isField hs hKM hxM a b (ihK a ha) (ihK b hb)
      exact fixes_adj _ hKM hxM hK hx
    | one => exact FieldAut.fixes_one _
    | mul _ _ h1 h2 => exact h1.mul h2
    | inv _ h1 => exact h1.inv

/-- **The automorphism group of a Kummer chain is solvable.** For a Kummer chain `m`, the group
`Aut(ℚ(x₁, …, xₘ)/ℚ)` is solvable: its `m`-th derived subgroup fixes everything. -/
theorem kummer_aut_solvable {m : List ℂ} (hm : KummerChain m) :
    IsSolvable (FieldAut Qc (gen Qc m)) :=
  ⟨m.length, fun σ hσ => FieldAut.ext fun y => derived_fixes hm m [] rfl σ hσ y y.2⟩

/-! ## Restriction to the splitting field -/

section Restriction

variable {m : List ℂ} (hLM : L.le (gen Qc m))

/-- **Restriction** `Aut(M/ℚ) → Aut(L/ℚ)` for `L ⊆ M = gen ℚ m`: an automorphism of `M`, viewed as
an embedding `L → ℂ`, maps `L` onto itself. -/
noncomputable def restrictHom : FieldAut Qc (gen Qc m) →* FieldAut Qc L where
  toFun σ := autOfEmbedding ((gen Qc m).incl.comp (σ.toRingHom.comp (Subfield.inclusion hLM)))
  map_mul _ _ := FieldAut.ext fun _ => rfl

/-- The restriction acts as the original automorphism. -/
theorem restrictHom_apply (σ : FieldAut Qc (gen Qc m)) (y : L) :
    ((restrictHom hLM σ).toFun y).1 = (σ.toFun ⟨y.1, hLM _ y.2⟩).1 := rfl

/-- **Restriction is onto** when `M` is stable: every automorphism of `L` extends to `M`. -/
theorem restrictHom_surjective (hst : Stable (gen Qc m)) :
    ∀ σ : FieldAut Qc L, ∃ ρ, restrictHom hLM ρ = σ := by
  intro σ
  obtain ⟨τ, hτ⟩ := extend_to m Qc_le_L hLM (L.incl.comp σ.toRingHom)
  exact ⟨genAut hst τ, FieldAut.ext fun y => Subtype.ext (hτ y)⟩

/-- **Solvability descends to `Aut(L/ℚ)`.** If `L` lies in the field of a stable Kummer chain,
then `Aut(L/ℚ)` is solvable, being a homomorphic image of a solvable group. -/
theorem aut_L_solvable_of_le {m : List ℂ} (hm : KummerChain m) (hst : Stable (gen Qc m))
    (hLM : L.le (gen Qc m)) : IsSolvable (FieldAut Qc L) :=
  isSolvable_of_surjective (restrictHom hLM) (restrictHom_surjective hLM hst)
    (kummer_aut_solvable hm)

end Restriction

/-! ## The splitting field inside a stable field -/

/-- **One root brings all the others.** If a stable field `gen ℚ m` contains one root `β` of
`x⁵ - 6x + 3`, it contains the whole splitting field `L`. -/
theorem L_le_of_root_mem {m : List ℂ} (hst : Stable (gen Qc m)) {β : ℂ}
    (hβ : eval β (quinticPoly ℂ) = 0) (hβM : β ∈ gen Qc m) : L.le (gen Qc m) := by
  apply L_le (le_gen Qc m)
  intro j
  have halg := quintic_isAlgebraic Qc hβ
  obtain ⟨σ₀, _, hσ₀, _⟩ := extend C.isField Qc β halg Qc.incl (qβ j)
    (fun q hq => minpoly_roots hβ (qβ_spec.2.1 j) q hq)
  have hFM : (adjoin C.isField Qc β halg).le (gen Qc m) :=
    adjoin_le _ _ _ _ (le_gen Qc m) hβM
  obtain ⟨τ, hτ⟩ := extend_to m (le_adjoin _ _ _ _) hFM σ₀
  have := hst τ ⟨β, hβM⟩
  rw [show τ.toFun ⟨β, hβM⟩ = qβ j from (hτ ⟨β, mem_adjoin_self _ _ _ _⟩).trans hσ₀] at this
  exact this

/-- **Galois's criterion for `x⁵ - 6x + 3`.** If some root of `x⁵ - 6x + 3` is expressible by
radicals over `ℚ`, then the Galois group `Aut(L/ℚ)` of its splitting field is solvable. -/
theorem galois_criterion {β : ℂ} (hβ : eval β (quinticPoly ℂ) = 0)
    (hrad : ExpressibleByRadicals β) : IsSolvable (FieldAut Qc L) := by
  obtain ⟨l, hl, hβl⟩ := hrad
  obtain ⟨m, hm, hst, hle⟩ := exists_stable_kummer hl
  exact aut_L_solvable_of_le hm hst (L_le_of_root_mem hst hβ (hle _ hβl))

end Foundations.Algebra
