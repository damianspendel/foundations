import Foundations.Numbers

/-!
# Part VIII: Topology — metric spaces

The ε-δ arguments of real analysis use only one feature of the real line: the *distance*
`|x − y|`. Maurice **Fréchet** (1906) isolated this feature: a **metric space** is a set with a
distance function that is non-negative, symmetric, zero exactly on the diagonal, and satisfies the
triangle inequality. Everything in the analysis files that speaks of "nearness" — convergence,
continuity, open sets — makes sense in any metric space.

We define metric spaces (with distances in our real numbers `R`), show that `ℝ` (with `|x − y|`)
and `ℂ` (with the modulus `|z − w|`) are examples, and prove the equivalence of three notions of
continuity of a map `f : X → Y` at all points:

* **ε-δ continuity** (Cauchy, Weierstrass);
* **sequential continuity**: `xₙ → x` implies `f xₙ → f x` (Heine);
* **topological continuity**: preimages of open sets are open — the formulation that will become
  the *definition* of continuity in a general topological space (next file).

Subsets of a space `X` are represented by predicates `X → Prop`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

/-- A **metric space**: a type `X` with a distance `dist : X → X → R` that vanishes exactly on the
diagonal, is symmetric, and satisfies the triangle inequality (Fréchet 1906, named by Hausdorff
1914). -/
class MetricSpace (X : Type) where
  /-- The distance between two points. -/
  dist : X → X → R
  /-- A point has distance `0` from itself. -/
  dist_self : ∀ x, dist x x = 0
  /-- Distinct points have non-zero distance. -/
  eq_of_dist_eq_zero : ∀ {x y}, dist x y = 0 → x = y
  /-- Distance is symmetric. -/
  dist_comm : ∀ x y, dist x y = dist y x
  /-- The **triangle inequality**. -/
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

export MetricSpace (dist dist_self eq_of_dist_eq_zero dist_comm dist_triangle)

variable {X Y Z : Type} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-- Distances are non-negative. -/
theorem dist_nonneg (x y : X) : 0 ≤ dist x y := by
  have := dist_triangle x y x; rw [dist_self, dist_comm y x] at this; grind

/-! ## Examples -/

/-- **The real line** as a metric space, with `d(x, y) = |x − y|`. -/
noncomputable instance instMetricR : MetricSpace R where
  dist x y := abs (x - y)
  dist_self x := by rw [show x - x = 0 by grind]; exact R.abs_zero
  eq_of_dist_eq_zero h := by have := eq_zero_of_abs_le (Std.le_of_eq h); grind
  dist_comm x y := abs_sub_comm x y
  dist_triangle x y z := by
    have := OF.abs_add (x - y) (y - z); rw [show x - y + (y - z) = x - z by grind] at this; exact this

/-- The distance on `R` is `|x − y|`. -/
theorem dist_R (x y : R) : dist x y = abs (x - y) := rfl

/-- **The complex plane** as a metric space, with `d(z, w) = |z − w|` (the Euclidean distance of
the plane `ℝ²`). -/
noncomputable instance instMetricC : MetricSpace C where
  dist z w := C.cabs (z - w)
  dist_self z := by rw [show z - z = 0 by grind]; exact C.cabs_zero
  eq_of_dist_eq_zero h := by have := C.eq_zero_of_cabs h; grind
  dist_comm z w := C.cabs_sub_comm z w
  dist_triangle x y z := by
    have := C.cabs_add (x - y) (y - z); rw [show x - y + (y - z) = x - z by grind] at this
    exact this

/-! ## Open and closed sets -/

/-- The **open ball** `B(x, r) = {y | d(x, y) < r}`. -/
def ball (x : X) (r : R) : X → Prop := fun y => dist x y < r

/-- A set `U` is **open** if around each of its points it contains a ball. -/
def IsOpen (U : X → Prop) : Prop := ∀ x, U x → ∃ ε : R, 0 < ε ∧ ∀ y, dist x y < ε → U y

/-- A set is **closed** if its complement is open. -/
def IsClosed (F : X → Prop) : Prop := IsOpen (fun x => ¬ F x)

/-- **Open balls are open.** -/
theorem isOpen_ball (x : X) (r : R) : IsOpen (ball x r) := fun y hy =>
  ⟨r - dist x y, by unfold ball at hy; grind, fun z hz => by
    unfold ball; have := dist_triangle x y z; grind⟩

/-! ## Convergence -/

/-- The sequence `s` **converges** to `L`. -/
def Converges (s : Nat → X) (L : X) : Prop := ∀ ε : R, 0 < ε → ∃ N, ∀ n, N ≤ n → dist (s n) L < ε

/-- **Limits are unique** in a metric space. -/
theorem Converges.unique {s : Nat → X} {L M : X} (hL : Converges s L) (hM : Converges s M) :
    L = M := by
  apply Classical.byContradiction; intro hne
  have hpos : 0 < dist L M := by
    rcases (by have := dist_nonneg L M; grind : dist L M = 0 ∨ 0 < dist L M) with h | h
    · exact absurd (eq_of_dist_eq_zero h) hne
    · exact h
  obtain ⟨N₁, h₁⟩ := hL (dist L M / 2) (by grind)
  obtain ⟨N₂, h₂⟩ := hM (dist L M / 2) (by grind)
  have k1 := h₁ (max N₁ N₂) (by omega)
  have k2 := h₂ (max N₁ N₂) (by omega)
  have := dist_triangle L (s (max N₁ N₂)) M
  have := dist_comm L (s (max N₁ N₂)); grind

/-- On `R`, convergence is the convergence of the analysis files. -/
theorem converges_iff_tendsto (s : Nat → R) (L : R) : Converges s L ↔ R.Tendsto s L := Iff.rfl

/-- **Closed sets are sequentially closed**: limits of sequences in a closed set stay in it. -/
theorem IsClosed.mem_of_converges {F : X → Prop} (hF : IsClosed F) {s : Nat → X} {L : X}
    (hs : ∀ n, F (s n)) (hL : Converges s L) : F L := by
  apply Classical.byContradiction; intro hL'
  obtain ⟨ε, hε, h⟩ := hF L hL'
  obtain ⟨N, hN⟩ := hL ε hε
  exact h (s N) (by rw [dist_comm]; exact hN N (Nat.le_refl N)) (hs N)

/-- Points `1/(n+1)`-close to `x` converge to `x`. -/
theorem converges_of_dist_lt {s : Nat → X} {x : X} (h : ∀ n, dist (s n) x < 1 / ((n : R) + 1)) :
    Converges s x := fun ε hε => by
  obtain ⟨N, hN⟩ := eps_small hε
  exact ⟨N, fun n hn => Std.lt_trans (h n) (hN n hn)⟩

/-- Conversely, a set containing the limits of all its convergent sequences is closed. -/
theorem isClosed_of_seq {F : X → Prop}
    (h : ∀ (s : Nat → X) (L : X), (∀ n, F (s n)) → Converges s L → F L) : IsClosed F := by
  intro x hx
  apply Classical.byContradiction; intro hno
  have hpt : ∀ n : Nat, ∃ y, dist x y < 1 / ((n : R) + 1) ∧ F y := fun n => by
    apply Classical.byContradiction; intro h'
    exact hno ⟨1 / ((n : R) + 1), eps_pos n, fun y hy => fun hy' => h' ⟨y, hy, hy'⟩⟩
  let s : Nat → X := fun n => (hpt n).choose
  have hs : ∀ n, dist x (s n) < 1 / ((n : R) + 1) ∧ F (s n) := fun n => (hpt n).choose_spec
  exact hx (h s x (fun n => (hs n).2) (converges_of_dist_lt fun n => by
    rw [dist_comm]; exact (hs n).1))

/-! ## Three faces of continuity -/

/-- `f` is **continuous at `x`** (ε-δ). -/
def ContinuousAt (f : X → Y) (x : X) : Prop :=
  ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧ ∀ y, dist y x < δ → dist (f y) (f x) < ε

/-- On `R`, ε-δ continuity is that of the analysis files. -/
theorem continuousAt_iff_R (f : R → R) (x : R) : ContinuousAt f x ↔ R.ContinuousAt f x := Iff.rfl

/-- `f` is **sequentially continuous at `x`**: `xₙ → x` implies `f xₙ → f x`. -/
def SeqContinuousAt (f : X → Y) (x : X) : Prop :=
  ∀ s : Nat → X, Converges s x → Converges (fun n => f (s n)) (f x)

/-- **ε-δ continuity ⇔ sequential continuity** (Heine). -/
theorem continuousAt_iff_seq (f : X → Y) (x : X) : ContinuousAt f x ↔ SeqContinuousAt f x := by
  constructor
  · intro hf s hs ε hε
    obtain ⟨δ, hδ, h⟩ := hf ε hε
    obtain ⟨N, hN⟩ := hs δ hδ
    exact ⟨N, fun n hn => h _ (hN n hn)⟩
  · intro hf
    apply Classical.byContradiction; intro hno
    -- Otherwise some `ε` defeats every `δ = 1/(n+1)`.
    have : ∃ ε : R, 0 < ε ∧ ∀ n : Nat, ∃ y, dist y x < 1 / ((n : R) + 1) ∧ ε ≤ dist (f y) (f x) := by
      apply Classical.byContradiction; intro h'
      apply hno; intro ε hε
      apply Classical.byContradiction; intro h''
      apply h'; refine ⟨ε, hε, fun n => ?_⟩
      apply Classical.byContradiction; intro h3
      exact h'' ⟨1 / ((n : R) + 1), eps_pos n, fun y hy => by
        apply Classical.byContradiction; intro h4; exact h3 ⟨y, hy, by grind⟩⟩
    obtain ⟨ε, hε, hy⟩ := this
    let s : Nat → X := fun n => (hy n).choose
    have hs : ∀ n, dist (s n) x < 1 / ((n : R) + 1) ∧ ε ≤ dist (f (s n)) (f x) :=
      fun n => (hy n).choose_spec
    obtain ⟨N, hN⟩ := hf s (converges_of_dist_lt fun n => (hs n).1) ε hε
    have := hN N (Nat.le_refl N); have := (hs N).2; grind

/-- `f` is **continuous** if it is continuous at every point. -/
def Continuous (f : X → Y) : Prop := ∀ x, ContinuousAt f x

/-- **Continuity ⇔ preimages of open sets are open.** -/
theorem continuous_iff_isOpen_preimage (f : X → Y) :
    Continuous f ↔ ∀ V : Y → Prop, IsOpen V → IsOpen (fun x => V (f x)) := by
  constructor
  · intro hf V hV x hx
    obtain ⟨ε, hε, h⟩ := hV (f x) hx
    obtain ⟨δ, hδ, hδ'⟩ := hf x ε hε
    exact ⟨δ, hδ, fun y hy => h _ (by rw [dist_comm]; exact hδ' y (by rw [dist_comm]; exact hy))⟩
  · intro hf x ε hε
    obtain ⟨δ, hδ, h⟩ := hf (ball (f x) ε) (isOpen_ball _ _) x (by
      show dist (f x) (f x) < ε; rw [dist_self]; exact hε)
    exact ⟨δ, hδ, fun y hy => by
      have := h y (by rw [dist_comm]; exact hy); unfold ball at this; rw [dist_comm]; exact this⟩

/-- **Three equivalent definitions of continuity**: ε-δ, sequential, and open preimages. -/
theorem continuous_tfae (f : X → Y) :
    (Continuous f ↔ ∀ x, SeqContinuousAt f x) ∧
    (Continuous f ↔ ∀ V : Y → Prop, IsOpen V → IsOpen (fun x => V (f x))) :=
  ⟨⟨fun h x => (continuousAt_iff_seq f x).1 (h x), fun h x => (continuousAt_iff_seq f x).2 (h x)⟩,
    continuous_iff_isOpen_preimage f⟩

/-- Compositions of continuous maps are continuous. -/
theorem Continuous.comp {g : Y → Z} {f : X → Y} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) := fun x ε hε => by
  obtain ⟨η, hη, h1⟩ := hg (f x) ε hε
  obtain ⟨δ, hδ, h2⟩ := hf x η hη
  exact ⟨δ, hδ, fun y hy => h1 _ (h2 y hy)⟩

/-- A map that does not increase distances by more than a factor `K` (a **Lipschitz map**) is
continuous. -/
theorem continuous_of_lipschitz {f : X → Y} {K : R} (hK : 0 ≤ K)
    (h : ∀ x y, dist (f x) (f y) ≤ K * dist x y) : Continuous f := fun x ε hε => by
  refine ⟨ε / (K + 1), div_pos hε (by grind), fun y hy => ?_⟩
  have k1 := h y x
  have k2 := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt hy) hK
  have k3 := OrderedRing.mul_lt_mul_of_pos_left hy (by grind : 0 < K + 1)
  have e : (K + 1) * (ε / (K + 1)) = ε := by grind
  have := dist_nonneg y x
  have := OrderedRing.mul_nonneg hK this
  grind

end Foundations.Topology
