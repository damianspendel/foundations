import Foundations.Topology.Topological

/-!
# Compactness

Why does a continuous function on `[a, b]` attain a maximum, while `x ↦ x` on `(0, 1)` does not?
The answer, extracted by Borel (1895), Lebesgue and finally Alexandrov and Urysohn (1920s), is
**compactness**: every cover of the set by open sets has a finite subcover. It is the
topological substitute for finiteness.

* **Heine–Borel theorem**: every closed interval `[a, b]` is compact. The proof is a "creeping
  along" argument: the supremum of the points `x` for which `[a, x]` is finitely covered must be
  `b` — completeness of `ℝ` once more.
* In metric spaces, **compact ⇔ sequentially compact** (every sequence in `K` has a subsequence
  converging in `K`). One direction is a direct covering argument; the other needs the
  **Lebesgue number** of a cover and **total boundedness** (finite `δ`-nets).
* The **continuous image of a compact set is compact**, and a non-empty compact set of reals has
  a largest element. Together: the **extreme value theorem**, re-derived from compactness. The
  earlier proof (`R.extreme_value` in `Numbers/Continuity`) used Bolzano–Weierstrass directly; we
  recover exactly its statement.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

variable {X Y : Type}

/-- `K` is **compact** in the topology `τ`: every cover of `K` by open sets `U i` (indexed by any
type `ι`) has a finite subcover, given by a list of indices. -/
def IsCompact (τ : Topology X) (K : X → Prop) : Prop :=
  ∀ (ι : Type) (U : ι → X → Prop), (∀ i, τ.IsOpen (U i)) → (∀ x, K x → ∃ i, U i x) →
    ∃ l : List ι, ∀ x, K x → ∃ i, i ∈ l ∧ U i x

/-- **The continuous image of a compact set is compact.** -/
theorem IsCompact.image {τ : Topology X} {σ : Topology Y} {K : X → Prop} (hK : IsCompact τ K)
    {f : X → Y} (hf : Topology.Continuous τ σ f) :
    IsCompact σ (fun y => ∃ x, K x ∧ f x = y) := by
  intro ι U hU hcov
  obtain ⟨l, hl⟩ := hK ι (fun i x => U i (f x)) (fun i => hf _ (hU i))
    (fun x hx => hcov _ ⟨x, hx, rfl⟩)
  exact ⟨l, fun y ⟨x, hx, hxy⟩ => by obtain ⟨i, hi, h⟩ := hl x hx; exact ⟨i, hi, hxy ▸ h⟩⟩

/-- The maximum of `f` over a list of natural numbers dominates each value. -/
theorem le_foldr_max {α : Type} (f : α → Nat) (l : List α) {a : α} (ha : a ∈ l) :
    f a ≤ l.foldr (fun b m => max (f b) m) 0 := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    rcases List.mem_cons.1 ha with h | h
    · subst h; show f a ≤ max (f a) _; omega
    · have := ih h; show f a ≤ max (f b) _; omega

/-! ## Heine–Borel -/

/-- **Heine–Borel theorem.** Every closed interval `[a, b]` of real numbers is compact. -/
theorem heine_borel (a b : R) : IsCompact (Topology.metric R) (fun x => a ≤ x ∧ x ≤ b) := by
  intro ι U hU hcov
  by_cases hab' : ¬ a ≤ b
  · exact ⟨[], fun x hx => absurd (Std.le_trans hx.1 hx.2) hab'⟩
  have hab : a ≤ b := Classical.not_not.1 hab'
  -- `P x`: `[a, x]` is covered by finitely many `U i`.
  let P : R → Prop := fun x => a ≤ x ∧ x ≤ b ∧
    ∃ l : List ι, ∀ y, a ≤ y → y ≤ x → ∃ i, i ∈ l ∧ U i y
  have hPa : P a := by
    obtain ⟨i, hi⟩ := hcov a ⟨Std.le_refl a, hab⟩
    exact ⟨Std.le_refl a, hab, [i], fun y h1 h2 => ⟨i, List.mem_singleton.2 rfl,
      by rw [show y = a by grind]; exact hi⟩⟩
  obtain ⟨c, hc1, hc2⟩ := exists_lub P ⟨a, hPa⟩ ⟨b, fun x hx => hx.2.1⟩
  have hac : a ≤ c := hc1 a hPa
  have hcb : c ≤ b := hc2 b fun x hx => hx.2.1
  obtain ⟨i, hi⟩ := hcov c ⟨hac, hcb⟩
  obtain ⟨ε, hε, hball⟩ := hU i c hi
  -- Some `x` with `P x` lies within `ε` of `c`.
  obtain ⟨x, hPx, hx⟩ : ∃ x, P x ∧ c - ε < x := by
    apply Classical.byContradiction; intro hno
    have := hc2 (c - ε) fun y hy => by
      apply Classical.byContradiction; intro h; exact hno ⟨y, hy, by grind⟩
    grind
  have hxc : x ≤ c := hc1 x hPx
  obtain ⟨-, -, l, hl⟩ := hPx
  -- Then `[a, c']` is covered for `c' = min (c + ε/2) b`.
  have hext : ∀ c', c' ≤ b → c' ≤ c + ε / 2 → a ≤ c' → P c' := fun c' h1 h2 h3 =>
    ⟨h3, h1, i :: l, fun y hy1 hy2 => by
      rcases (by grind : y ≤ x ∨ x < y) with h | h
      · obtain ⟨j, hj, hj'⟩ := hl y hy1 h; exact ⟨j, List.mem_cons_of_mem i hj, hj'⟩
      · exact ⟨i, List.mem_cons_self, hball y (by
          show abs (c - y) < ε; exact abs_lt.2 ⟨by grind, by grind⟩)⟩⟩
  rcases (by grind : c + ε / 2 ≤ b ∨ b < c + ε / 2) with h | h
  · have := hc1 _ (hext (c + ε / 2) h (Std.le_refl _) (by grind)); grind
  · obtain ⟨-, -, l', hl'⟩ := hext b (Std.le_refl b) (Std.le_of_lt h) hab
    exact ⟨l', fun y hy => hl' y hy.1 hy.2⟩

/-! ## Compact ⇔ sequentially compact (metric spaces) -/

variable [MetricSpace X] [MetricSpace Y]

/-- `K` is **sequentially compact**: every sequence in `K` has a subsequence converging to a point
of `K`. -/
def IsSeqCompact (K : X → Prop) : Prop :=
  ∀ s : Nat → X, (∀ n, K (s n)) →
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ L, K L ∧ Converges (fun k => s (φ k)) L

/-- Recursively chosen indices `φ 0 < φ 1 < ⋯` with `d(s (φ k), L) < 1/(k+1)`, given that terms
arbitrarily close to `L` occur arbitrarily late. -/
noncomputable def chooseIdx (s : Nat → X) (L : X)
    (h : ∀ ε : R, 0 < ε → ∀ N, ∃ n, N ≤ n ∧ dist (s n) L < ε) : Nat → Nat
  | 0 => Classical.choose (h (1 / ((0 : Nat) + 1)) (eps_pos 0) 0)
  | k + 1 => Classical.choose (h (1 / ((k + 1 : Nat) + 1)) (eps_pos (k + 1)) (chooseIdx s L h k + 1))

/-- If terms arbitrarily close to `L` occur arbitrarily late, a subsequence converges to `L`. -/
theorem exists_subseq_converges {s : Nat → X} {L : X}
    (h : ∀ ε : R, 0 < ε → ∀ N, ∃ n, N ≤ n ∧ dist (s n) L < ε) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ Converges (fun k => s (φ k)) L := by
  have spec : ∀ k, dist (s (chooseIdx s L h k)) L < 1 / ((k : R) + 1) := fun k => by
    cases k with
    | zero => exact (Classical.choose_spec (h (1 / ((0 : Nat) + 1)) (eps_pos 0) 0)).2
    | succ k => exact (Classical.choose_spec (h (1 / ((k + 1 : Nat) + 1)) (eps_pos (k + 1))
        (chooseIdx s L h k + 1))).2
  refine ⟨chooseIdx s L h, fun k => ?_, converges_of_dist_lt spec⟩
  exact (Classical.choose_spec (h (1 / ((k + 1 : Nat) + 1)) (eps_pos (k + 1))
    (chooseIdx s L h k + 1))).1

/-- **Compact implies sequentially compact** (in a metric space). -/
theorem IsCompact.isSeqCompact {K : X → Prop} (hK : IsCompact (Topology.metric X) K) :
    IsSeqCompact K := by
  intro s hs
  -- Some point of `K` has terms of the sequence arbitrarily close to it, arbitrarily late.
  suffices ∃ L, K L ∧ ∀ ε : R, 0 < ε → ∀ N, ∃ n, N ≤ n ∧ dist (s n) L < ε by
    obtain ⟨L, hL, h⟩ := this
    obtain ⟨φ, hφ, hc⟩ := exists_subseq_converges h
    exact ⟨φ, hφ, L, hL, hc⟩
  apply Classical.byContradiction; intro hno
  have hfar : ∀ x : {x // K x}, ∃ ε : R, 0 < ε ∧ ∃ N : Nat, ∀ n, N ≤ n → ε ≤ dist (s n) x.1 := by
    intro ⟨x, hx⟩
    apply Classical.byContradiction; intro h
    apply hno; refine ⟨x, hx, fun ε hε N => ?_⟩
    apply Classical.byContradiction; intro h'
    exact h ⟨ε, hε, N, fun n hn => by
      apply Classical.byContradiction; intro h''; exact h' ⟨n, hn, by grind⟩⟩
  let ε : {x // K x} → R := fun x => (hfar x).choose
  let N : {x // K x} → Nat := fun x => (hfar x).choose_spec.2.choose
  have hεpos : ∀ x, 0 < ε x := fun x => (hfar x).choose_spec.1
  have hN : ∀ x n, N x ≤ n → ε x ≤ dist (s n) x.1 := fun x => (hfar x).choose_spec.2.choose_spec
  obtain ⟨l, hl⟩ := hK {x // K x} (fun x => ball x.1 (ε x)) (fun x => isOpen_ball _ _)
    (fun y hy => ⟨⟨y, hy⟩, by show dist y y < _; rw [dist_self]; exact hεpos _⟩)
  let M := l.foldr (fun b m => max (N b) m) 0
  obtain ⟨x, hxl, hx⟩ := hl (s M) (hs M)
  have := hN x M (le_foldr_max N l hxl)
  have : dist x.1 (s M) < ε x := hx
  have := dist_comm x.1 (s M)
  grind

/-- **Lebesgue number lemma.** For an open cover of a sequentially compact set `K` there is
`δ > 0` such that every `δ`-ball around a point of `K` lies in a single member of the cover. -/
theorem lebesgue_number {K : X → Prop} (hK : IsSeqCompact K) {ι : Type} {U : ι → X → Prop}
    (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x, K x → ∃ i, U i x) :
    ∃ δ : R, 0 < δ ∧ ∀ x, K x → ∃ i, ∀ y, dist x y < δ → U i y := by
  apply Classical.byContradiction; intro hno
  have hx : ∀ n : Nat, ∃ x, K x ∧ ∀ i, ∃ y, dist x y < 1 / ((n : R) + 1) ∧ ¬ U i y := fun n => by
    apply Classical.byContradiction; intro h
    apply hno; refine ⟨1 / ((n : R) + 1), eps_pos n, fun x hx => ?_⟩
    apply Classical.byContradiction; intro h'
    apply h; refine ⟨x, hx, fun i => ?_⟩
    apply Classical.byContradiction; intro h''
    exact h' ⟨i, fun y hy => by apply Classical.byContradiction; intro h3; exact h'' ⟨y, hy, h3⟩⟩
  let s : Nat → X := fun n => (hx n).choose
  have hs : ∀ n, K (s n) ∧ ∀ i, ∃ y, dist (s n) y < 1 / ((n : R) + 1) ∧ ¬ U i y :=
    fun n => (hx n).choose_spec
  obtain ⟨φ, hφ, L, hL, hconv⟩ := hK s fun n => (hs n).1
  obtain ⟨i, hi⟩ := hcov L hL
  obtain ⟨ε, hε, hball⟩ := hU i L hi
  obtain ⟨N₁, hN₁⟩ := hconv (ε / 2) (by grind)
  obtain ⟨N₂, hN₂⟩ := eps_small (by grind : (0 : R) < ε / 2)
  let k := max N₁ N₂
  obtain ⟨y, hy1, hy2⟩ := (hs (φ k)).2 i
  have k1 := hN₁ k (by omega)
  have k2 := hN₂ (φ k) (by have := le_of_strictMono hφ k; omega)
  apply hy2; apply hball
  have := dist_triangle L (s (φ k)) y
  have := dist_comm L (s (φ k))
  simp only at k1
  grind

omit [MetricSpace X] [MetricSpace Y] in
/-- The values of a list of points of `K` lie in `K`. -/
theorem mem_map_val {K : X → Prop} (l : List {x // K x}) : ∀ p, p ∈ l.map Subtype.val → K p :=
  fun p hp => by obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp; exact q.2

/-- Given finitely many points of `K`, a point of `K` at distance `≥ δ` from all of them (when
such points always exist). -/
noncomputable def farNext (K : X → Prop) (δ : R)
    (h : ∀ l : List X, (∀ p, p ∈ l → K p) → ∃ x, K x ∧ ∀ p, p ∈ l → δ ≤ dist p x)
    (l : List {x // K x}) : {x // K x} :=
  ⟨(h _ (mem_map_val l)).choose, (h _ (mem_map_val l)).choose_spec.1⟩

/-- The new point is far from all the given ones. -/
theorem farNext_far (K : X → Prop) (δ : R)
    (h : ∀ l : List X, (∀ p, p ∈ l → K p) → ∃ x, K x ∧ ∀ p, p ∈ l → δ ≤ dist p x)
    (l : List {x // K x}) (p : {x // K x}) (hp : p ∈ l) : δ ≤ dist p.1 (farNext K δ h l).1 :=
  (h _ (mem_map_val l)).choose_spec.2 _ (List.mem_map.2 ⟨p, hp, rfl⟩)

/-- Points chosen greedily, each at distance `≥ δ` from all earlier ones (used to prove total
boundedness). -/
noncomputable def farPts (K : X → Prop) (δ : R)
    (h : ∀ l : List X, (∀ p, p ∈ l → K p) → ∃ x, K x ∧ ∀ p, p ∈ l → δ ≤ dist p x) :
    Nat → List {x // K x}
  | 0 => []
  | n + 1 => farPts K δ h n ++ [farNext K δ h (farPts K δ h n)]

/-- **Total boundedness.** A sequentially compact set is covered, for every `δ > 0`, by finitely
many `δ`-balls centred at points of the set. -/
theorem IsSeqCompact.totallyBounded {K : X → Prop} (hK : IsSeqCompact K) {δ : R} (hδ : 0 < δ) :
    ∃ l : List X, (∀ p, p ∈ l → K p) ∧ ∀ x, K x → ∃ p, p ∈ l ∧ dist p x < δ := by
  apply Classical.byContradiction; intro hno
  have h : ∀ l : List X, (∀ p, p ∈ l → K p) → ∃ x, K x ∧ ∀ p, p ∈ l → δ ≤ dist p x := by
    intro l hl
    apply Classical.byContradiction; intro h'
    apply hno; refine ⟨l, hl, fun x hx => ?_⟩
    apply Classical.byContradiction; intro h''
    exact h' ⟨x, hx, fun p hp => by
      apply Classical.byContradiction; intro h3; exact h'' ⟨p, hp, by grind⟩⟩
  -- The greedy sequence: its `n`-th point is far from all earlier points.
  let pick : Nat → {x // K x} := fun n => farNext K δ h (farPts K δ h n)
  have hmem : ∀ m n, m < n → pick m ∈ farPts K δ h n := by
    intro m n hmn
    induction n with
    | zero => omega
    | succ n ih =>
      show pick m ∈ farPts K δ h n ++ [farNext K δ h (farPts K δ h n)]
      by_cases e : m = n
      · subst e; exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ (ih (by omega))
  have hfar : ∀ m n, m < n → δ ≤ dist (pick m).1 (pick n).1 := fun m n hmn =>
    farNext_far K δ h _ _ (hmem m n hmn)
  obtain ⟨φ, hφ, L, -, hconv⟩ := hK (fun n => (pick n).1) fun n => (pick n).2
  obtain ⟨N, hN⟩ := hconv (δ / 2) (by grind)
  have k1 : dist (pick (φ N)).1 L < δ / 2 := hN N (Nat.le_refl N)
  have k2 : dist (pick (φ (N + 1))).1 L < δ / 2 := hN (N + 1) (by omega)
  have := hfar (φ N) (φ (N + 1)) (hφ N)
  have := dist_triangle (pick (φ N)).1 L (pick (φ (N + 1))).1
  have := dist_comm (pick (φ (N + 1))).1 L
  grind

/-- **Sequentially compact implies compact** (in a metric space). -/
theorem IsSeqCompact.isCompact {K : X → Prop} (hK : IsSeqCompact K) :
    IsCompact (Topology.metric X) K := by
  intro ι U hU hcov
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number hK hU hcov
  obtain ⟨l, hlK, hl⟩ := hK.totallyBounded hδ
  have hidx : ∀ p : {p // p ∈ l}, ∃ i, ∀ y, dist p.1 y < δ → U i y :=
    fun p => hleb p.1 (hlK p.1 p.2)
  refine ⟨l.attach.map (fun p => (hidx p).choose), fun x hx => ?_⟩
  obtain ⟨p, hp, hpx⟩ := hl x hx
  exact ⟨(hidx ⟨p, hp⟩).choose, List.mem_map.2 ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩,
    (hidx ⟨p, hp⟩).choose_spec x hpx⟩

/-- **Compact ⇔ sequentially compact** in metric spaces. -/
theorem isCompact_iff_isSeqCompact (K : X → Prop) :
    IsCompact (Topology.metric X) K ↔ IsSeqCompact K :=
  ⟨IsCompact.isSeqCompact, IsSeqCompact.isCompact⟩

/-! ## The extreme value theorem from compactness -/

/-- The image of a compact set under a map continuous at each of its points is compact. -/
theorem IsCompact.image_of_continuousAt {K : X → Prop} (hK : IsCompact (Topology.metric X) K)
    {f : X → Y} (hf : ∀ x, K x → ContinuousAt f x) :
    IsCompact (Topology.metric Y) (fun y => ∃ x, K x ∧ f x = y) := by
  intro ι V hV hcov
  -- `W i` = interior of the preimage of `V i`.
  let W : ι → X → Prop := fun i x => ∃ δ : R, 0 < δ ∧ ∀ z, dist z x < δ → V i (f z)
  have hW : ∀ i, IsOpen (W i) := by
    intro i x hx
    obtain ⟨δ, hδ, h⟩ := hx
    exact ⟨δ / 2, by grind, fun y hy => ⟨δ / 2, by grind, fun z hz => h z (by
      have := dist_triangle z y x; have := dist_comm x y; grind)⟩⟩
  obtain ⟨l, hl⟩ := hK ι W hW fun x hx => by
    obtain ⟨i, hi⟩ := hcov (f x) ⟨x, hx, rfl⟩
    obtain ⟨ε, hε, hball⟩ := hV i (f x) hi
    obtain ⟨δ, hδ, hδ'⟩ := hf x hx ε hε
    exact ⟨i, δ, hδ, fun z hz => hball _ (by rw [dist_comm]; exact hδ' z hz)⟩
  refine ⟨l, fun y ⟨x, hx, hxy⟩ => ?_⟩
  obtain ⟨i, hi, δ, hδ, h⟩ := hl x hx
  exact ⟨i, hi, hxy ▸ h x (by rw [dist_self]; exact hδ)⟩

/-- **A non-empty compact set of reals has a largest element.** -/
theorem IsCompact.exists_max {K : R → Prop} (hK : IsCompact (Topology.metric R) K)
    (hne : ∃ x, K x) : ∃ s, K s ∧ ∀ y, K y → y ≤ s := by
  -- Bounded above: cover by the open sets `(−∞, n)`.
  obtain ⟨l, hl⟩ := hK Nat (fun n y => y < (n : R)) (fun n y hy =>
      ⟨(n : R) - y, by grind, fun z hz => by have := (abs_lt.1 hz); grind⟩)
    (fun y _ => archimedean y)
  let M := l.foldr (fun b m => max ((fun k : Nat => k) b) m) 0
  have hbdd : ∀ y, K y → y ≤ (M : R) := fun y hy => by
    obtain ⟨n, hn, h⟩ := hl y hy
    have := OrderedRing.natCast_le_natCast_of_le (R := R) n M (le_foldr_max (fun k => k) l hn)
    grind
  obtain ⟨s, hs1, hs2⟩ := exists_lub K hne ⟨_, hbdd⟩
  refine ⟨s, ?_, hs1⟩
  -- If `s ∉ K`, the open sets `(−∞, s − 1/(n+1))` cover `K`, so `K` stays below some `s − 1/(N+1)`.
  apply Classical.byContradiction; intro hsK
  obtain ⟨l', hl'⟩ := hK Nat (fun n y => y < s - 1 / ((n : R) + 1)) (fun n y hy =>
      ⟨s - 1 / ((n : R) + 1) - y, by grind, fun z hz => by have := (abs_lt.1 hz); grind⟩)
    (fun y hy => by
      have hys : y < s := by
        rcases (by have := hs1 y hy; grind : y < s ∨ y = s) with h | h
        · exact h
        · exact absurd (h ▸ hy) hsK
      obtain ⟨N, hN⟩ := eps_small (by grind : 0 < s - y)
      exact ⟨N, by have := hN N (Nat.le_refl N); grind⟩)
  let N := l'.foldr (fun b m => max ((fun k : Nat => k) b) m) 0
  have := hs2 (s - 1 / ((N : R) + 1)) fun y hy => by
    obtain ⟨n, hn, h⟩ := hl' y hy
    have hnN := OrderedRing.natCast_le_natCast_of_le (R := R) n N (le_foldr_max (fun k => k) l' hn)
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    have := one_div_le_one_div (by grind : (0 : R) < (n : R) + 1) (by grind : (n : R) + 1 ≤ (N : R) + 1)
    grind
  have := eps_pos N
  grind

/-- **Extreme value theorem** (from compactness). A real function continuous at every point of a
non-empty compact set attains a maximum on it. -/
theorem extreme_value_compact {K : X → Prop} (hK : IsCompact (Topology.metric X) K)
    (hne : ∃ x, K x) {f : X → R} (hf : ∀ x, K x → ContinuousAt f x) :
    ∃ c, K c ∧ ∀ x, K x → f x ≤ f c := by
  obtain ⟨s, ⟨c, hc, rfl⟩, hs⟩ := (hK.image_of_continuousAt hf).exists_max
    (by obtain ⟨x, hx⟩ := hne; exact ⟨f x, x, hx, rfl⟩)
  exact ⟨c, hc, fun x hx => hs _ ⟨x, hx, rfl⟩⟩

/-- **Extreme value theorem on `[a, b]`**, re-derived from Heine–Borel; this is exactly the
statement of `R.extreme_value` from `Numbers/Continuity`, now as a corollary of compactness. -/
theorem extreme_value_interval {f : R → R} {a b : R} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → R.ContinuousAt f x) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x → x ≤ b → f x ≤ f c := by
  obtain ⟨c, hc, h⟩ := extreme_value_compact (heine_borel a b) ⟨a, Std.le_refl a, hab⟩
    (f := f) (fun x hx => hf x hx.1 hx.2)
  exact ⟨c, hc.1, hc.2, fun x h1 h2 => h x ⟨h1, h2⟩⟩

end Foundations.Topology
