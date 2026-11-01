import Foundations.Topology.Metric

/-!
# Topological spaces

The last theorem of the previous file shows that continuity can be expressed through open sets
alone, without mentioning distances. Felix **Hausdorff** (*Grundzüge der Mengenlehre*, 1914)
took the decisive step of making the open sets the primitive notion; the modern axioms, due to
Kuratowski and others in the 1920s, say that a **topology** on a set `X` is a family of subsets
— the open sets — containing `X` itself and closed under **finite intersections** and
**arbitrary unions**.

Every metric space carries its *metric topology*; continuity of maps between metric spaces in
the ε-δ sense coincides with topological continuity. But there are many more topologies:

* the **discrete** topology (every set open) and the **indiscrete** topology (only `∅` and `X`);
* the **Sierpiński space** on two points `{0, 1}`, whose open sets are `∅`, `{1}`, `{0, 1}`;
* **subspace** and **product** topologies.

Hausdorff's own separation axiom — distinct points have disjoint neighbourhoods — holds in metric
spaces and guarantees unique limits, but fails for the indiscrete and Sierpiński spaces.

A topology is represented as a structure (not a class), so that one type can carry several.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

/-- A **topology** on `X`: a family of "open" subsets containing `X`, closed under binary (hence
finite) intersections and under arbitrary unions. -/
structure Topology (X : Type) where
  /-- The predicate "`U` is open". -/
  IsOpen : (X → Prop) → Prop
  /-- The whole space is open. -/
  isOpen_univ : IsOpen (fun _ => True)
  /-- The intersection of two open sets is open. -/
  isOpen_inter : ∀ U V, IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
  /-- Any union of open sets is open. -/
  isOpen_sUnion : ∀ S : (X → Prop) → Prop, (∀ U, S U → IsOpen U) → IsOpen (fun x => ∃ U, S U ∧ U x)

namespace Topology

variable {X Y Z : Type}

/-- Open sets are determined extensionally: a set with the same points as an open set is open. -/
theorem isOpen_congr (τ : Topology X) {U V : X → Prop} (hU : τ.IsOpen U) (h : ∀ x, U x ↔ V x) :
    τ.IsOpen V := by
  have : U = V := funext fun x => propext (h x)
  exact this ▸ hU

/-- The empty set is open (the union of the empty family). -/
theorem isOpen_empty (τ : Topology X) : τ.IsOpen (fun _ => False) :=
  τ.isOpen_congr (τ.isOpen_sUnion (fun _ => False) fun _ h => h.elim)
    fun _ => ⟨fun ⟨_, h, _⟩ => h, fun h => h.elim⟩

/-- The union of two open sets is open. -/
theorem isOpen_union (τ : Topology X) {U V : X → Prop} (hU : τ.IsOpen U) (hV : τ.IsOpen V) :
    τ.IsOpen (fun x => U x ∨ V x) :=
  τ.isOpen_congr (τ.isOpen_sUnion (fun W => W = U ∨ W = V) fun W h => by
    rcases h with h | h <;> rw [h] <;> assumption)
    fun x => ⟨fun ⟨W, hW, hx⟩ => by rcases hW with h | h <;> subst h <;> simp [hx],
      fun h => by rcases h with h | h
                  · exact ⟨U, Or.inl rfl, h⟩
                  · exact ⟨V, Or.inr rfl, h⟩⟩

/-- A set is **closed** if its complement is open. -/
def IsClosed (τ : Topology X) (F : X → Prop) : Prop := τ.IsOpen (fun x => ¬ F x)

/-- A map is **continuous** if preimages of open sets are open. -/
def Continuous (τ : Topology X) (σ : Topology Y) (f : X → Y) : Prop :=
  ∀ V, σ.IsOpen V → τ.IsOpen (fun x => V (f x))

/-- The identity map is continuous. -/
theorem continuous_id (τ : Topology X) : Continuous τ τ (fun x => x) := fun _ h => h

/-- Compositions of continuous maps are continuous. -/
theorem Continuous.comp {τ : Topology X} {σ : Topology Y} {ρ : Topology Z} {g : Y → Z}
    {f : X → Y} (hg : Continuous σ ρ g) (hf : Continuous τ σ f) :
    Continuous τ ρ (fun x => g (f x)) := fun V hV => hf _ (hg V hV)

/-- Constant maps are continuous. -/
theorem continuous_const (τ : Topology X) (σ : Topology Y) (c : Y) :
    Continuous τ σ (fun _ => c) := fun V _ => by
  by_cases h : V c
  · exact τ.isOpen_congr τ.isOpen_univ fun _ => ⟨fun _ => h, fun _ => trivial⟩
  · exact τ.isOpen_congr τ.isOpen_empty fun _ => ⟨fun e => e.elim, fun e => h e⟩

/-- A **homeomorphism**: a continuous bijection with continuous inverse. -/
structure Homeomorph (τ : Topology X) (σ : Topology Y) where
  /-- The map. -/
  toFun : X → Y
  /-- Its inverse. -/
  invFun : Y → X
  /-- `invFun ∘ toFun = id`. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun ∘ invFun = id`. -/
  right_inv : ∀ y, toFun (invFun y) = y
  /-- The map is continuous. -/
  continuous_toFun : Continuous τ σ toFun
  /-- The inverse is continuous. -/
  continuous_invFun : Continuous σ τ invFun

/-! ## The metric topology -/

/-- **The metric topology** of a metric space: the open sets in the ε-ball sense. -/
def metric (X : Type) [MetricSpace X] : Topology X where
  IsOpen := Foundations.Topology.IsOpen
  isOpen_univ := fun _ _ => ⟨1, by grind, fun _ _ => trivial⟩
  isOpen_inter U V hU hV x hx := by
    obtain ⟨ε₁, h₁, k₁⟩ := hU x hx.1
    obtain ⟨ε₂, h₂, k₂⟩ := hV x hx.2
    obtain ⟨ε, hε, e1, e2⟩ := exists_pos_le_both h₁ h₂
    exact ⟨ε, hε, fun y hy => ⟨k₁ y (by grind), k₂ y (by grind)⟩⟩
  isOpen_sUnion S hS x := fun ⟨U, hU, hx⟩ => by
    obtain ⟨ε, hε, k⟩ := hS U hU x hx
    exact ⟨ε, hε, fun y hy => ⟨U, hU, k y hy⟩⟩

/-- **Metric continuity is topological continuity** for the metric topologies. -/
theorem continuous_metric_iff [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Foundations.Topology.Continuous f ↔ Continuous (metric X) (metric Y) f :=
  continuous_iff_isOpen_preimage f

/-! ## Examples -/

/-- The **discrete topology**: every set is open. -/
def discrete (X : Type) : Topology X where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

/-- The **indiscrete topology**: only `∅` and `X` are open. -/
def indiscrete (X : Type) : Topology X where
  IsOpen U := (∀ x, ¬ U x) ∨ (∀ x, U x)
  isOpen_univ := Or.inr fun _ => trivial
  isOpen_inter U V hU hV := by
    rcases hU with hU | hU
    · exact Or.inl fun x h => hU x h.1
    · rcases hV with hV | hV
      · exact Or.inl fun x h => hV x h.2
      · exact Or.inr fun x => ⟨hU x, hV x⟩
  isOpen_sUnion S hS := by
    by_cases h : ∃ U, S U ∧ ∀ x, U x
    · obtain ⟨U, hU, hU'⟩ := h; exact Or.inr fun x => ⟨U, hU, hU' x⟩
    · refine Or.inl fun x ⟨U, hU, hx⟩ => ?_
      rcases hS U hU with h' | h'
      · exact h' x hx
      · exact h ⟨U, hU, h'⟩

/-- **Sierpiński space**: the two points `false, true`, with open sets `∅`, `{true}`, and
everything — a set is open if it contains `true` whenever it contains `false`. -/
def sierpinski : Topology Bool where
  IsOpen U := U false → U true
  isOpen_univ := fun _ => trivial
  isOpen_inter _ _ hU hV := fun h => ⟨hU h.1, hV h.2⟩
  isOpen_sUnion _ hS := fun ⟨U, hU, h⟩ => ⟨U, hU, hS U hU h⟩

/-- In Sierpiński space `{true}` is open but `{false}` is not. -/
theorem sierpinski_open : sierpinski.IsOpen (fun b => b = true) ∧
    ¬ sierpinski.IsOpen (fun b => b = false) :=
  ⟨fun h => absurd h (by decide), fun h => absurd (h rfl) (by decide)⟩

/-- Every map out of a discrete space is continuous. -/
theorem continuous_of_discrete (σ : Topology Y) (f : X → Y) : Continuous (discrete X) σ f :=
  fun _ _ => trivial

/-- Every map into an indiscrete space is continuous. -/
theorem continuous_to_indiscrete (τ : Topology X) (f : X → Y) :
    Continuous τ (indiscrete Y) f := fun V hV => by
  rcases hV with h | h
  · exact τ.isOpen_congr τ.isOpen_empty fun x => ⟨fun e => e.elim, fun e => h _ e⟩
  · exact τ.isOpen_congr τ.isOpen_univ fun x => ⟨fun _ => h _, fun _ => trivial⟩

/-! ## Subspaces and products -/

/-- The **subspace topology** on a subset `A ⊆ X` (as the subtype `{x // A x}`): the open sets
are the traces `U ∩ A` of open sets `U` of `X`. -/
def subspace (τ : Topology X) (A : X → Prop) : Topology {x // A x} where
  IsOpen V := ∃ U, τ.IsOpen U ∧ ∀ x : {x // A x}, V x ↔ U x.1
  isOpen_univ := ⟨_, τ.isOpen_univ, fun _ => Iff.rfl⟩
  isOpen_inter V W := fun ⟨U, hU, h⟩ ⟨U', hU', h'⟩ =>
    ⟨_, τ.isOpen_inter U U' hU hU', fun x => by show V x ∧ W x ↔ _; rw [h x, h' x]⟩
  isOpen_sUnion S hS := by
    refine ⟨fun y => ∃ U, (τ.IsOpen U ∧ ∃ V, S V ∧ ∀ x : {x // A x}, V x ↔ U x.1) ∧ U y,
      τ.isOpen_sUnion _ fun U h => h.1, fun x => ⟨fun ⟨V, hV, hx⟩ => ?_, fun ⟨U, ⟨hU, V, hV, h⟩, hx⟩ =>
        ⟨V, hV, (h x).2 hx⟩⟩⟩
    obtain ⟨U, hU, h⟩ := hS V hV
    exact ⟨U, ⟨hU, V, hV, h⟩, (h x).1 hx⟩

/-- The inclusion of a subspace is continuous. -/
theorem continuous_subtype_val (τ : Topology X) (A : X → Prop) :
    Continuous (subspace τ A) τ (fun x => x.1) := fun V hV => ⟨V, hV, fun _ => Iff.rfl⟩

/-- The **product topology** on `X × Y`: a set is open if around each of its points it contains an
open "box" `U × V`. -/
def prod (τ : Topology X) (σ : Topology Y) : Topology (X × Y) where
  IsOpen W := ∀ p, W p → ∃ U V, τ.IsOpen U ∧ σ.IsOpen V ∧ U p.1 ∧ V p.2 ∧
    ∀ q : X × Y, U q.1 → V q.2 → W q
  isOpen_univ := fun _ _ => ⟨_, _, τ.isOpen_univ, σ.isOpen_univ, trivial, trivial, fun _ _ _ => trivial⟩
  isOpen_inter W W' hW hW' p hp := by
    obtain ⟨U, V, hU, hV, h1, h2, h⟩ := hW p hp.1
    obtain ⟨U', V', hU', hV', h1', h2', h'⟩ := hW' p hp.2
    exact ⟨_, _, τ.isOpen_inter U U' hU hU', σ.isOpen_inter V V' hV hV', ⟨h1, h1'⟩, ⟨h2, h2'⟩,
      fun q hq1 hq2 => ⟨h q hq1.1 hq2.1, h' q hq1.2 hq2.2⟩⟩
  isOpen_sUnion S hS p := fun ⟨W, hW, hp⟩ => by
    obtain ⟨U, V, hU, hV, h1, h2, h⟩ := hS W hW p hp
    exact ⟨U, V, hU, hV, h1, h2, fun q hq1 hq2 => ⟨W, hW, h q hq1 hq2⟩⟩

/-- The first projection is continuous. -/
theorem continuous_fst (τ : Topology X) (σ : Topology Y) :
    Continuous (prod τ σ) τ (fun p => p.1) := fun U hU _ hp =>
  ⟨U, fun _ => True, hU, σ.isOpen_univ, hp, trivial, fun _ h _ => h⟩

/-- The second projection is continuous. -/
theorem continuous_snd (τ : Topology X) (σ : Topology Y) :
    Continuous (prod τ σ) σ (fun p => p.2) := fun V hV _ hp =>
  ⟨fun _ => True, V, τ.isOpen_univ, hV, trivial, hp, fun _ _ h => h⟩

/-- **Universal property of the product**: a map into `X × Y` is continuous when both of its
components are. -/
theorem continuous_pair {ρ : Topology Z} {τ : Topology X} {σ : Topology Y} {f : Z → X} {g : Z → Y}
    (hf : Continuous ρ τ f) (hg : Continuous ρ σ g) :
    Continuous ρ (prod τ σ) (fun z => (f z, g z)) := fun W hW => by
  -- The preimage is the union of the preimages of the boxes inside `W`.
  refine ρ.isOpen_congr (ρ.isOpen_sUnion (fun O => ∃ U V, τ.IsOpen U ∧ σ.IsOpen V ∧
      (∀ q : X × Y, U q.1 → V q.2 → W q) ∧ O = fun z => U (f z) ∧ V (g z)) ?_) fun z => ?_
  · rintro O ⟨U, V, hU, hV, -, rfl⟩
    exact ρ.isOpen_inter _ _ (hf U hU) (hg V hV)
  · constructor
    · rintro ⟨O, ⟨U, V, -, -, hUV, rfl⟩, h1, h2⟩; exact hUV _ h1 h2
    · intro hz
      obtain ⟨U, V, hU, hV, h1, h2, h⟩ := hW _ hz
      exact ⟨_, ⟨U, V, hU, hV, h, rfl⟩, h1, h2⟩

/-! ## The Hausdorff property -/

/-- A space is **Hausdorff** if distinct points have disjoint open neighbourhoods (Hausdorff's
separation axiom, 1914). -/
def IsHausdorff (τ : Topology X) : Prop :=
  ∀ x y, x ≠ y → ∃ U V, τ.IsOpen U ∧ τ.IsOpen V ∧ U x ∧ V y ∧ ∀ z, U z → V z → False

/-- **Metric spaces are Hausdorff**: balls of radius `d(x, y)/2` separate `x` and `y`. -/
theorem isHausdorff_metric (X : Type) [MetricSpace X] : IsHausdorff (metric X) := by
  intro x y hxy
  have hpos : 0 < dist x y := by
    rcases (by have := dist_nonneg x y; grind : dist x y = 0 ∨ 0 < dist x y) with h | h
    · exact absurd (eq_of_dist_eq_zero h) hxy
    · exact h
  refine ⟨ball x (dist x y / 2), ball y (dist x y / 2), isOpen_ball _ _, isOpen_ball _ _,
    ?_, ?_, fun z hz1 hz2 => ?_⟩
  · show dist x x < _; rw [dist_self]; grind
  · show dist y y < _; rw [dist_self]; grind
  · unfold ball at hz1 hz2
    have := dist_triangle x z y; have := dist_comm y z; grind

/-- Discrete spaces are Hausdorff. -/
theorem isHausdorff_discrete (X : Type) : IsHausdorff (discrete X) := fun x y hxy =>
  ⟨fun z => z = x, fun z => z = y, trivial, trivial, rfl, rfl, fun _ h1 h2 => hxy (h1 ▸ h2)⟩

/-- The indiscrete topology on two points is **not** Hausdorff. -/
theorem not_isHausdorff_indiscrete : ¬ IsHausdorff (indiscrete Bool) := by
  intro h
  obtain ⟨U, V, hU, hV, hx, hy, hd⟩ := h false true (by decide)
  rcases hU with hU | hU
  · exact hU _ hx
  · rcases hV with hV | hV
    · exact hV _ hy
    · exact hd true (hU true) (hV true)

/-- **Sierpiński space is not Hausdorff**: every open set containing `false` contains `true`. -/
theorem not_isHausdorff_sierpinski : ¬ IsHausdorff sierpinski := by
  intro h
  obtain ⟨U, V, hU, hV, hx, hy, hd⟩ := h false true (by decide)
  exact hd true (hU hx) hy

/-- A sequence **converges** to `L` in a topological space if it eventually enters every open
neighbourhood of `L`. -/
def Converges (τ : Topology X) (s : Nat → X) (L : X) : Prop :=
  ∀ U, τ.IsOpen U → U L → ∃ N, ∀ n, N ≤ n → U (s n)

/-- **Limits are unique in Hausdorff spaces.** -/
theorem Converges.unique {τ : Topology X} (hτ : IsHausdorff τ) {s : Nat → X} {L M : X}
    (hL : Converges τ s L) (hM : Converges τ s M) : L = M := by
  apply Classical.byContradiction; intro hne
  obtain ⟨U, V, hU, hV, hLU, hMV, hd⟩ := hτ L M hne
  obtain ⟨N₁, h₁⟩ := hL U hU hLU
  obtain ⟨N₂, h₂⟩ := hM V hV hMV
  exact hd _ (h₁ (max N₁ N₂) (by omega)) (h₂ (max N₁ N₂) (by omega))

/-- In Sierpiński space limits are **not** unique: the constant sequence `true` converges both to
`true` and to `false`. -/
theorem sierpinski_nonunique_limit :
    Converges sierpinski (fun _ => true) true ∧ Converges sierpinski (fun _ => true) false :=
  ⟨fun _ _ h => ⟨0, fun _ _ => h⟩, fun _ hU h => ⟨0, fun _ _ => hU h⟩⟩

end Topology

end Foundations.Topology
