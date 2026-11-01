import Foundations.Topology.FixedPoint

/-!
# Tychonoff's theorem for two factors

Andrey **Tychonoff** proved in 1930 (for products of intervals) and 1935 (in general) that any
product of compact spaces is compact; for infinitely many factors this is equivalent to the axiom
of choice (Kelley 1950). We prove the case of **two factors**: if `K ⊆ X` and `L ⊆ Y` are
compact, so is `K × L` in the product topology.

The proof is the **tube lemma** argument. Fix `x ∈ K`. Each point `(x, y)` of the slice
`{x} × L` lies in an open box `U × V` inside some member of the cover; finitely many of the `V`s
cover `L`, and the intersection of the corresponding `U`s is an open set `Uₓ ∋ x` whose "tube"
`Uₓ × L` is covered by finitely many members. Finitely many tubes then cover `K × L`.
-/

namespace Foundations.Topology

open Foundations.Numbers Lean.Grind

variable {X Y : Type}

/-- A finite intersection `⋂_{a ∈ l} U a` of open sets is open. -/
theorem isOpen_list_inter {α : Type} (τ : Topology X) (U : α → X → Prop)
    (hU : ∀ a, τ.IsOpen (U a)) (l : List α) : τ.IsOpen (fun z => ∀ a, a ∈ l → U a z) := by
  induction l with
  | nil => exact τ.isOpen_congr τ.isOpen_univ fun _ => ⟨fun _ a ha => (by cases ha), fun _ => trivial⟩
  | cons b l ih =>
    refine τ.isOpen_congr (τ.isOpen_inter _ _ (hU b) ih) fun z => ⟨fun ⟨h1, h2⟩ a ha => ?_,
      fun h => ⟨h b List.mem_cons_self, fun a ha => h a (List.mem_cons_of_mem b ha)⟩⟩
    rcases List.mem_cons.1 ha with e | e
    · exact e ▸ h1
    · exact h2 a e

/-- **Tychonoff's theorem for two factors.** The product `K × L` of compact sets is compact in the
product topology. -/
theorem isCompact_prod {τ : Topology X} {σ : Topology Y} {K : X → Prop} {L : Y → Prop}
    (hK : IsCompact τ K) (hL : IsCompact σ L) :
    IsCompact (Topology.prod τ σ) (fun p => K p.1 ∧ L p.2) := by
  intro ι W hW hcov
  -- Boxes around every point of `K × L`, each inside some `W i`.
  have hbox : ∀ x : {x // K x}, ∀ y : {y // L y}, ∃ i : ι, ∃ U V, τ.IsOpen U ∧ σ.IsOpen V ∧
      U x.1 ∧ V y.1 ∧ ∀ q : X × Y, U q.1 → V q.2 → W i q := fun x y => by
    obtain ⟨i, hi⟩ := hcov (x.1, y.1) ⟨x.2, y.2⟩
    obtain ⟨U, V, hU, hV, h1, h2, h⟩ := hW i _ hi
    exact ⟨i, U, V, hU, hV, h1, h2, h⟩
  let idx : {x // K x} → {y // L y} → ι := fun x y => (hbox x y).choose
  let BU : {x // K x} → {y // L y} → X → Prop := fun x y => (hbox x y).choose_spec.choose
  let BV : {x // K x} → {y // L y} → Y → Prop := fun x y => (hbox x y).choose_spec.choose_spec.choose
  have hB : ∀ x y, τ.IsOpen (BU x y) ∧ σ.IsOpen (BV x y) ∧ BU x y x.1 ∧ BV x y y.1 ∧
      ∀ q : X × Y, BU x y q.1 → BV x y q.2 → W (idx x y) q :=
    fun x y => (hbox x y).choose_spec.choose_spec.choose_spec
  -- For each `x`, finitely many boxes cover the slice `{x} × L`.
  have hslice : ∀ x : {x // K x}, ∃ ly : List {y // L y}, ∀ y, L y → ∃ y', y' ∈ ly ∧ BV x y' y :=
    fun x => hL {y // L y} (BV x) (fun y => (hB x y).2.1)
      (fun y hy => ⟨⟨y, hy⟩, (hB x ⟨y, hy⟩).2.2.2.1⟩)
  let ly : {x // K x} → List {y // L y} := fun x => (hslice x).choose
  have hly : ∀ x y, L y → ∃ y', y' ∈ ly x ∧ BV x y' y := fun x => (hslice x).choose_spec
  -- The tubes `Uₓ × L` with `Uₓ = ⋂_{y ∈ ly x} BU x y`; finitely many cover `K × L`.
  let T : {x // K x} → X → Prop := fun x z => ∀ y, y ∈ ly x → BU x y z
  obtain ⟨lx, hlx⟩ := hK {x // K x} T
    (fun x => isOpen_list_inter τ (BU x) (fun y => (hB x y).1) (ly x))
    (fun z hz => ⟨⟨z, hz⟩, fun y _ => (hB ⟨z, hz⟩ y).2.2.1⟩)
  refine ⟨lx.flatMap (fun x => (ly x).map (idx x)), fun p hp => ?_⟩
  obtain ⟨x, hx, hTx⟩ := hlx p.1 hp.1
  obtain ⟨y, hy, hVy⟩ := hly x p.2 hp.2
  exact ⟨idx x y, List.mem_flatMap.2 ⟨x, hx, List.mem_map.2 ⟨y, hy, rfl⟩⟩,
    (hB x y).2.2.2.2 p (hTx y hy) hVy⟩

end Foundations.Topology
