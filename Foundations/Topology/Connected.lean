import Foundations.Topology.Compact

/-!
# Connectedness

A space is **connected** if it cannot be split into two disjoint non-empty open pieces. The
notion goes back to Cantor (who called a set "zusammenhängend" in 1883, in a metric sense) and
reached its modern form with Hausdorff (1914) and Lennes and Knaster–Kuratowski (1921).

* Every interval `[a, b]` is connected — once again a supremum argument, i.e. completeness.
* The **continuous image of a connected set is connected**.
* Together they give the **intermediate value theorem**, re-derived topologically: the image of
  `[a, b]` is a connected set of reals, hence contains everything between `f a` and `f b`.
* The real line is connected, but `ℝ ∖ {0}` is not; hence the two are **not homeomorphic**.
* The rationals, at the other extreme, are **totally disconnected**: any set of rational numbers
  with two points falls apart, because an irrational number lies between any two reals.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

variable {X Y : Type}

/-- `A` is **connected** in the topology `τ`: there are no open sets `U`, `V` covering `A`, each
meeting `A`, and disjoint on `A`. -/
def IsConnected (τ : Topology X) (A : X → Prop) : Prop :=
  ¬ ∃ U V, τ.IsOpen U ∧ τ.IsOpen V ∧ (∀ x, A x → U x ∨ V x) ∧ (∃ x, A x ∧ U x) ∧
    (∃ x, A x ∧ V x) ∧ (∀ x, A x → U x → V x → False)

/-- **The continuous image of a connected set is connected.** -/
theorem IsConnected.image {τ : Topology X} {σ : Topology Y} {A : X → Prop}
    (hA : IsConnected τ A) {f : X → Y} (hf : Topology.Continuous τ σ f) :
    IsConnected σ (fun y => ∃ x, A x ∧ f x = y) := by
  rintro ⟨U, V, hU, hV, hcov, ⟨_, ⟨x, hx, rfl⟩, hxU⟩, ⟨_, ⟨y, hy, rfl⟩, hyV⟩, hdis⟩
  exact hA ⟨_, _, hf U hU, hf V hV, fun z hz => hcov _ ⟨z, hz, rfl⟩, ⟨x, hx, hxU⟩, ⟨y, hy, hyV⟩,
    fun z hz h1 h2 => hdis _ ⟨z, hz, rfl⟩ h1 h2⟩

/-- Connectedness depends only on the points of the set. -/
theorem IsConnected.congr {τ : Topology X} {A B : X → Prop} (hA : IsConnected τ A)
    (h : ∀ x, A x ↔ B x) : IsConnected τ B := by
  have : A = B := funext fun x => propext (h x)
  exact this ▸ hA

/-! ## Intervals are connected -/

/-- The key step: if open `U`, `V` cover `[a, b]`, are disjoint on it, and `a ∈ U`, then `U`
contains all of `[a, b]`. -/
theorem interval_in_open {a b : R} (hab : a ≤ b) {U V : R → Prop} (hU : IsOpen U)
    (hV : IsOpen V) (hcov : ∀ x, a ≤ x → x ≤ b → U x ∨ V x)
    (hdis : ∀ x, a ≤ x → x ≤ b → U x → V x → False) (ha : U a) :
    ∀ x, a ≤ x → x ≤ b → U x := by
  let S : R → Prop := fun x => a ≤ x ∧ x ≤ b ∧ ∀ y, a ≤ y → y ≤ x → U y
  have hSa : S a := ⟨Std.le_refl a, hab, fun y h1 h2 => by rw [show y = a by grind]; exact ha⟩
  obtain ⟨c, hc1, hc2⟩ := exists_lub S ⟨a, hSa⟩ ⟨b, fun x hx => hx.2.1⟩
  have hac : a ≤ c := hc1 a hSa
  have hcb : c ≤ b := hc2 b fun x hx => hx.2.1
  -- Below `c`, everything is in `U`.
  have hbelow : ∀ y, a ≤ y → y < c → U y := fun y hy1 hy2 => by
    apply Classical.byContradiction; intro hy
    have := hc2 y fun x hx => by
      apply Classical.byContradiction; intro hxy; exact hy (hx.2.2 y hy1 (by grind))
    grind
  rcases hcov c hac hcb with hcU | hcV
  · obtain ⟨ε, hε, hball⟩ := hU c hcU
    have hall : ∀ y, a ≤ y → y ≤ c → U y := fun y h1 h2 => by
      rcases (by grind : y < c ∨ y = c) with h | h
      · exact hbelow y h1 h
      · rw [h]; exact hcU
    rcases (by grind : c = b ∨ c < b) with h | h
    · intro x h1 h2; exact hall x h1 (by grind)
    · -- Otherwise `S` would contain a point beyond `c`.
      exfalso
      obtain ⟨c', h1, h2, h3⟩ : ∃ c', c < c' ∧ c' ≤ b ∧ c' ≤ c + ε / 2 := by
        rcases (by grind : c + ε / 2 ≤ b ∨ b < c + ε / 2) with h' | h'
        · exact ⟨c + ε / 2, by grind, h', Std.le_refl _⟩
        · exact ⟨b, h, Std.le_refl b, Std.le_of_lt h'⟩
      have := hc1 c' ⟨by grind, h2, fun y hy1 hy2 => by
        rcases (by grind : y ≤ c ∨ c < y) with h'' | h''
        · exact hall y hy1 h''
        · exact hball y (show abs (c - y) < ε from abs_lt.2 ⟨by grind, by grind⟩)⟩
      grind
  · -- `c ∈ V`: points just below `c` would lie in both `U` and `V`.
    exfalso
    obtain ⟨ε, hε, hball⟩ := hV c hcV
    have hac' : a < c := by
      rcases (by grind : a = c ∨ a < c) with h | h
      · exact absurd (h ▸ hcV) (fun h' => hdis a (Std.le_refl a) hab ha h')
      · exact h
    obtain ⟨y, h1, h2, h3⟩ : ∃ y, a ≤ y ∧ y < c ∧ c - y < ε := by
      rcases (by grind : a ≤ c - ε / 2 ∨ c - ε / 2 < a) with h' | h'
      · exact ⟨c - ε / 2, h', by grind, by grind⟩
      · exact ⟨a, Std.le_refl a, hac', by grind⟩
    exact hdis y h1 (by grind) (hbelow y h1 h2)
      (hball y (show abs (c - y) < ε from abs_lt.2 ⟨by grind, by grind⟩))

/-- **Closed intervals are connected.** -/
theorem isConnected_interval (a b : R) : IsConnected (Topology.metric R) (fun x => a ≤ x ∧ x ≤ b) := by
  rintro ⟨U, V, hU, hV, hcov, ⟨x, hx, hxU⟩, ⟨y, hy, hyV⟩, hdis⟩
  have hab : a ≤ b := Std.le_trans hx.1 hx.2
  have cov : ∀ z, a ≤ z → z ≤ b → U z ∨ V z := fun z h1 h2 => hcov z ⟨h1, h2⟩
  have dis : ∀ z, a ≤ z → z ≤ b → U z → V z → False := fun z h1 h2 => hdis z ⟨h1, h2⟩
  rcases cov a (Std.le_refl a) hab with ha | ha
  · exact dis y hy.1 hy.2 (interval_in_open hab hU hV cov dis ha y hy.1 hy.2) hyV
  · exact dis x hx.1 hx.2 hxU (interval_in_open hab hV hU (fun z h1 h2 => (cov z h1 h2).symm)
      (fun z h1 h2 h3 h4 => dis z h1 h2 h4 h3) ha x hx.1 hx.2)

/-- **The real line is connected.** -/
theorem isConnected_univ_R : IsConnected (Topology.metric R) (fun _ => True) := by
  rintro ⟨U, V, hU, hV, hcov, ⟨x, -, hxU⟩, ⟨y, -, hyV⟩, hdis⟩
  -- A separation of `ℝ` would separate the interval between `x` and `y`.
  have key : ∀ a b, U a → V b → a ≤ b → False := fun a b ha hb hab =>
    isConnected_interval a b ⟨U, V, hU, hV, fun z _ => hcov z trivial,
      ⟨a, ⟨Std.le_refl a, hab⟩, ha⟩, ⟨b, ⟨hab, Std.le_refl b⟩, hb⟩, fun z _ => hdis z trivial⟩
  rcases (by grind : x ≤ y ∨ y ≤ x) with h | h
  · exact key x y hxU hyV h
  · exact isConnected_interval y x ⟨V, U, hV, hU, fun z _ => (hcov z trivial).symm,
      ⟨y, ⟨Std.le_refl y, h⟩, hyV⟩, ⟨x, ⟨h, Std.le_refl x⟩, hxU⟩,
      fun z _ h1 h2 => hdis z trivial h2 h1⟩

/-! ## The intermediate value theorem, topologically -/

variable [MetricSpace X] [MetricSpace Y]

/-- The image of a connected set under a map continuous at each of its points is connected. -/
theorem IsConnected.image_of_continuousAt {A : X → Prop} (hA : IsConnected (Topology.metric X) A)
    {f : X → Y} (hf : ∀ x, A x → ContinuousAt f x) :
    IsConnected (Topology.metric Y) (fun y => ∃ x, A x ∧ f x = y) := by
  rintro ⟨U, V, hU, hV, hcov, ⟨_, ⟨x, hx, rfl⟩, hxU⟩, ⟨_, ⟨y, hy, rfl⟩, hyV⟩, hdis⟩
  -- Pull back along the interiors of the preimages.
  let int : (Y → Prop) → X → Prop := fun W x => ∃ δ : R, 0 < δ ∧ ∀ z, dist z x < δ → W (f z)
  have hint : ∀ W, IsOpen (int W) := by
    intro W x hx
    obtain ⟨δ, hδ, h⟩ := hx
    exact ⟨δ / 2, by grind, fun y hy => ⟨δ / 2, by grind, fun z hz => h z (by
      have := dist_triangle z y x; have := dist_comm x y; grind)⟩⟩
  have hmem : ∀ W, IsOpen W → ∀ x, A x → W (f x) → int W x := fun W hW x hx hWx => by
    obtain ⟨ε, hε, hball⟩ := hW (f x) hWx
    obtain ⟨δ, hδ, hδ'⟩ := hf x hx ε hε
    exact ⟨δ, hδ, fun z hz => hball _ (by rw [dist_comm]; exact hδ' z hz)⟩
  have hin : ∀ W x, int W x → W (f x) := fun W x ⟨δ, hδ, h⟩ => h x (by rw [dist_self]; exact hδ)
  exact hA ⟨int U, int V, hint U, hint V,
    fun z hz => (hcov _ ⟨z, hz, rfl⟩).elim (fun h => Or.inl (hmem U hU z hz h))
      (fun h => Or.inr (hmem V hV z hz h)),
    ⟨x, hx, hmem U hU x hx hxU⟩, ⟨y, hy, hmem V hV y hy hyV⟩,
    fun z hz h1 h2 => hdis _ ⟨z, hz, rfl⟩ (hin U z h1) (hin V z h2)⟩

/-- **Connected sets of reals are intervals**: if a connected set contains `u ≤ w`, it contains
every `v` between them. -/
theorem IsConnected.mem_of_between {A : R → Prop} (hA : IsConnected (Topology.metric R) A)
    {u v w : R} (hu : A u) (hw : A w) (huv : u ≤ v) (hvw : v ≤ w) : A v := by
  apply Classical.byContradiction; intro hv
  have hlt : ∀ y, A y → y < v ∨ v < y := fun y hy => by
    rcases (by grind : y < v ∨ y = v ∨ v < y) with h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hy) hv
    · exact Or.inr h
  have hu' : u < v := by rcases hlt u hu with h | h <;> grind
  have hw' : v < w := by rcases hlt w hw with h | h <;> grind
  exact hA ⟨fun y => y < v, fun y => v < y,
    fun y hy => ⟨v - y, by grind, fun z hz => by have := abs_lt.1 hz; grind⟩,
    fun y hy => ⟨y - v, by grind, fun z hz => by have := abs_lt.1 hz; grind⟩,
    hlt, ⟨u, hu, hu'⟩, ⟨w, hw, hw'⟩, fun y _ h1 h2 => by grind⟩

/-- **Intermediate value theorem** (from connectedness). A function continuous on `[a, b]` takes
every value between `f a` and `f b` — the statement of `R.intermediate_value'` from
`Numbers/Continuity`, now a corollary of the connectedness of `[a, b]`. -/
theorem intermediate_value_connected {f : R → R} {a b v : R} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → R.ContinuousAt f x) (ha : f a ≤ v) (hb : v ≤ f b) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ f c = v := by
  have hcon := (isConnected_interval a b).image_of_continuousAt (f := f)
    (fun x hx => hf x hx.1 hx.2)
  obtain ⟨c, hc, hcv⟩ := hcon.mem_of_between ⟨a, ⟨Std.le_refl a, hab⟩, rfl⟩
    ⟨b, ⟨hab, Std.le_refl b⟩, rfl⟩ ha hb
  exact ⟨c, hc.1, hc.2, hcv⟩

/-! ## ℝ is not homeomorphic to ℝ ∖ {0} -/

/-- `ℝ ∖ {0}` (as a subspace of `ℝ`) is **not connected**: negatives and positives separate it. -/
theorem not_isConnected_punctured :
    ¬ IsConnected (Topology.subspace (Topology.metric R) (fun x => x ≠ 0)) (fun _ => True) := by
  intro h
  apply h
  refine ⟨fun x => x.1 < 0, fun x => 0 < x.1,
    ⟨fun y => y < 0, fun y hy => ⟨-y, by grind, fun z hz => by have := abs_lt.1 hz; grind⟩,
      fun _ => Iff.rfl⟩,
    ⟨fun y => 0 < y, fun y hy => ⟨y, hy, fun z hz => by have := abs_lt.1 hz; grind⟩,
      fun _ => Iff.rfl⟩,
    fun x _ => by have := x.2; rcases (by grind : x.1 < 0 ∨ x.1 = 0 ∨ 0 < x.1) with h | h | h
                  · exact Or.inl h
                  · exact absurd h x.2
                  · exact Or.inr h,
    ⟨⟨-1, by grind⟩, trivial, by show (-1 : R) < 0; grind⟩,
    ⟨⟨1, by grind⟩, trivial, by show (0 : R) < 1; grind⟩, fun x _ h1 h2 => by grind⟩

/-- **ℝ is not homeomorphic to ℝ ∖ {0}**: a homeomorphism would carry the connected line onto the
disconnected punctured line. -/
theorem not_homeomorphic_punctured :
    Topology.Homeomorph (Topology.metric R) (Topology.subspace (Topology.metric R) (fun x => x ≠ 0))
      → False := fun e =>
  not_isConnected_punctured ((isConnected_univ_R.image e.continuous_toFun).congr fun y =>
    ⟨fun _ => trivial, fun _ => ⟨e.invFun y, trivial, e.right_inv y⟩⟩)

/-! ## The rationals are totally disconnected -/

/-- `x` is a rational number (the image of some `q : Q` in `R`). -/
def IsRational (x : R) : Prop := ∃ q : Q, x = OF.ofRat q

/-- **√2 is irrational** (in `R`): no rational real squares to `2`. -/
theorem sqrt_two_not_rational {r : R} (hr : r * r = 2) : ¬ IsRational r := by
  rintro ⟨q, rfl⟩
  apply Q.sqrt_two_irrational
  refine ⟨q, OF.ofRat_inj (K := R) ?_⟩
  rw [OF.ofRat_mul, hr, show (2 : Q) = OfNat.ofNat 2 from rfl, OF.ofRat_ofNat]

/-- **Irrational numbers are dense**: between any two reals lies an irrational one. -/
theorem exists_irrational_between {x y : R} (h : x < y) : ∃ z, x < z ∧ z < y ∧ ¬ IsRational z := by
  obtain ⟨r, -, hr⟩ := exists_sqrt_two
  obtain ⟨q, h1, h2⟩ := OF.exists_rat_between (K := R) archimedean (by grind : x - r < y - r)
  refine ⟨OF.ofRat q + r, by grind, by grind, ?_⟩
  rintro ⟨p, hp⟩
  apply sqrt_two_not_rational hr
  exact ⟨p - q, by rw [OF.ofRat_sub]; grind⟩

/-- **The rationals are totally disconnected**: a set of rational numbers containing two distinct
points is not connected. -/
theorem rationals_totally_disconnected {A : R → Prop} (hA : ∀ x, A x → IsRational x)
    {x y : R} (hx : A x) (hy : A y) (hxy : x < y) : ¬ IsConnected (Topology.metric R) A := by
  obtain ⟨z, h1, h2, hz⟩ := exists_irrational_between hxy
  intro hc
  exact hz (hA z (hc.mem_of_between hx hy (Std.le_of_lt h1) (Std.le_of_lt h2)))

end Foundations.Topology
