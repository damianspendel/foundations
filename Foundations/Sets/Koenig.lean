import Foundations.Sets.CardinalOrder

/-!
# Beyond: the tower of powers and Kőnig's theorem

Cantor's theorem `α < 𝒫(α)` (`Cardinality.lean`) can be applied again and again:
starting from the natural numbers we get an endless tower of ever larger
infinities

  `ℕ < 𝒫(ℕ) < 𝒫(𝒫(ℕ)) < 𝒫(𝒫(𝒫(ℕ))) < ⋯`

(`𝒫(ℕ)` has the size of the continuum, the real line). So the infinite is not
one thing but an unbounded hierarchy.

**Kőnig's theorem** (Julius Kőnig, 1905) is the most general form of Cantor's
diagonal argument. If for every index `i` the size `κᵢ` is strictly smaller than
`μᵢ`, then the sum `Σᵢ κᵢ` is strictly smaller than the product `Πᵢ μᵢ`. The
proof is a diagonal argument in many coordinates at once: given any map from the
sum to the product, at coordinate `i` the `κᵢ`-many functions coming from the
`i`-th summand cannot exhaust `μᵢ`, so we may choose a value they all miss; the
function made of these choices is hit by nothing. Cantor's theorem is the case
where all `κᵢ = 1` and all `μᵢ = 2`. (Kőnig used the theorem — erroneously — at
the 1904 Heidelberg congress to "refute" the continuum hypothesis' cousin, that
the continuum can be well-ordered; Zermelo's well-ordering theorem followed weeks
later.)
-/

namespace Foundations.Sets

universe u v

/-! ## The tower of power types -/

/-- The **tower of power types** over `ℕ`: `ℕ, 𝒫(ℕ), 𝒫(𝒫(ℕ)), …`, with `𝒫(β) = β → Prop`. -/
def powTower : Nat → Type
  | 0 => Nat
  | n + 1 => powTower n → Prop

/-- A strictly smaller type followed by a no-smaller one gives strictly smaller. -/
theorem CardLT.trans_le {α β γ : Type _} (h₁ : CardLT α β) (h₂ : CardLE β γ) : CardLT α γ :=
  ⟨h₁.1.trans h₂, fun h => h₁.2 (h₂.trans h)⟩

/-- Each storey of the tower is strictly smaller than the next (Cantor). -/
theorem powTower_lt_succ (n : Nat) : CardLT (powTower n) (powTower (n + 1)) :=
  lt_powerType (powTower n)

/-- The tower only grows. -/
theorem powTower_le {m n : Nat} (h : m ≤ n) : CardLE (powTower m) (powTower n) := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]; exact CardLE.refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · exact (ih (Nat.le_of_lt_succ hlt)).trans (powTower_lt_succ n).1
    · rw [heq]; exact CardLE.refl _

/-- **ℕ < 𝒫(ℕ) < 𝒫(𝒫(ℕ)) < ⋯.** Every storey of the tower of power types is strictly
smaller than every higher one. -/
theorem powTower_lt {m n : Nat} (h : m < n) : CardLT (powTower m) (powTower n) :=
  (powTower_lt_succ m).trans_le (powTower_le h)

/-! ## Kőnig's theorem -/

/-- **Kőnig's theorem, surjection form** (no choice of values is needed beyond one per
coordinate). If no `κ i` maps onto `μ i`, then the sum `Σ i, κ i` does not map onto
the product `Π i, μ i`. -/
theorem koenig_surj {ι : Type u} {κ μ : ι → Type v}
    (h : ∀ i, ¬ ∃ f : κ i → μ i, Function.Surjective f) :
    ¬ ∃ F : (Σ i, κ i) → (∀ i, μ i), Function.Surjective F := by
  rintro ⟨F, hF⟩
  -- at each coordinate, a value missed by all functions from the `i`-th summand
  have miss : ∀ i, ∃ y : μ i, ∀ x : κ i, F ⟨i, x⟩ i ≠ y := fun i =>
    Classical.byContradiction fun hn => h i ⟨fun x => F ⟨i, x⟩ i, fun y =>
      Classical.byContradiction fun hy => hn ⟨y, fun x hx => hy ⟨x, hx⟩⟩⟩
  let d : ∀ i, μ i := fun i => Classical.choose (miss i)
  obtain ⟨⟨i, x⟩, hx⟩ := hF d
  exact Classical.choose_spec (miss i) x (congrFun hx i)

/-- If `α` is strictly smaller than `β`, no map `α → β` is surjective (choice gives a
right inverse, which would be an injection `β → α`). -/
theorem not_surjective_of_cardLT {α β : Type _} (h : CardLT α β) :
    ¬ ∃ f : α → β, Function.Surjective f := by
  rintro ⟨f, hf⟩
  refine h.2 ⟨fun b => Classical.choose (hf b), fun b b' hbb' => ?_⟩
  rw [← Classical.choose_spec (hf b), ← Classical.choose_spec (hf b')]
  simp only at hbb'
  rw [hbb']

/-- **Kőnig's theorem.** If `κ i < μ i` for every index `i`, then
`Σ i, κ i < Π i, μ i`: the sum injects into the product, but not conversely. -/
theorem koenig {ι : Type u} {κ μ : ι → Type v} (h : ∀ i, CardLT (κ i) (μ i)) :
    CardLT (Σ i, κ i) (∀ i, μ i) := by
  classical
  -- injections `gᵢ : κ i → μ i`, and points `yᵢ` they miss
  have hg : ∀ i, ∃ g : κ i → μ i, Function.Injective g := fun i => (h i).1
  let g : ∀ i, κ i → μ i := fun i => Classical.choose (hg i)
  have ginj : ∀ i, Function.Injective (g i) := fun i => Classical.choose_spec (hg i)
  have hy : ∀ i, ∃ y : μ i, ∀ x, g i x ≠ y := fun i =>
    Classical.byContradiction fun hn => not_surjective_of_cardLT (h i) ⟨g i, fun y =>
      Classical.byContradiction fun hy => hn ⟨y, fun x hx => hy ⟨x, hx⟩⟩⟩
  let y : ∀ i, μ i := fun i => Classical.choose (hy i)
  have hymiss : ∀ i x, g i x ≠ y i := fun i => Classical.choose_spec (hy i)
  refine ⟨?_, fun hle => ?_⟩
  · -- `⟨i, x⟩ ↦` the function equal to `gᵢ x` at `i` and to `y` elsewhere
    let F : (Σ i, κ i) → ∀ j, μ j := fun s j => if h : s.1 = j then h ▸ g s.1 s.2 else y j
    refine ⟨F, ?_⟩
    rintro ⟨i, x⟩ ⟨i', x'⟩ hF
    have hi := congrFun hF i
    by_cases hii : i' = i
    · subst hii
      simp only [F, ↓reduceDIte] at hi
      rw [ginj _ hi]
    · simp only [F, hii, ↓reduceDIte] at hi
      exact absurd hi (hymiss i x)
  · -- an injection back would give a surjection, contradicting the surjection form
    obtain ⟨e, he⟩ := hle
    obtain ⟨F, hF⟩ := exists_surjective_of_injective he y
    exact koenig_surj (fun i => not_surjective_of_cardLT (h i)) ⟨F, hF⟩

end Foundations.Sets
