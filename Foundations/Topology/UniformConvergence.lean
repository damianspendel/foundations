import Foundations.Topology.OuterMeasure

/-!
# Uniform convergence and the space `C[a, b]`

A sequence of functions `fₙ` converges **uniformly** to `g` on a set `S` if one index `N` makes
`|fₙ(x) − g(x)| < ε` for *all* `x ∈ S` at once. Cauchy believed (1821) that pointwise limits of
continuous functions are continuous; Abel noticed counterexamples (Fourier series), and Seidel and
Stokes (1847), and above all Weierstrass in his lectures, isolated uniform convergence as the
condition that makes the limit well-behaved:

* the **uniform limit of continuous functions is continuous** (the "ε/3 argument");
* the **integral of a uniform limit is the limit of the integrals**;
* the space `C[a, b]` of continuous functions with the **sup metric**
  `d(f, g) = sup_{a ≤ x ≤ b} |f(x) − g(x)|` is a **complete metric space** (Fréchet 1906) — uniform
  convergence is convergence in this metric.

The last fact turns problems about functions into problems about *points* of a metric space; the
next file uses it with Banach's fixed-point theorem to solve differential equations.

We represent an element of `C[a, b]` as a continuous function `ℝ → ℝ` that is constant to the left
of `a` and to the right of `b` (it factors through the clamping map `x ↦ max a (min b x)`); then two
elements are equal exactly when they agree on `[a, b]`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

/-! ## Clamping -/

/-- The **clamp** of `x` to `[a, b]`: `a` if `x < a`, `b` if `x > b`, and `x` otherwise. -/
noncomputable def clamp (a b x : R) : R :=
  open Classical in if x < a then a else if b < x then b else x

/-- The three cases of the clamp. -/
theorem clamp_cases (a b x : R) :
    (x < a ∧ clamp a b x = a) ∨ (a ≤ x ∧ x ≤ b ∧ clamp a b x = x) ∨ (b < x ∧ clamp a b x = b) := by
  unfold clamp
  by_cases h1 : x < a
  · left; exact ⟨h1, by simp [h1]⟩
  · by_cases h2 : b < x
    · right; right; exact ⟨h2, by simp [h1, h2]⟩
    · right; left; exact ⟨by grind, by grind, by simp [h1, h2]⟩

/-- The clamp lies in `[a, b]`. -/
theorem clamp_mem {a b : R} (hab : a ≤ b) (x : R) : a ≤ clamp a b x ∧ clamp a b x ≤ b := by
  rcases clamp_cases a b x with h | h | h <;> grind

/-- The clamp fixes the points of `[a, b]`. -/
theorem clamp_of_mem {a b x : R} (_hab : a ≤ b) (h1 : a ≤ x) (h2 : x ≤ b) : clamp a b x = x := by
  rcases clamp_cases a b x with h | h | h <;> grind

/-- Clamping twice is clamping once. -/
theorem clamp_clamp {a b : R} (hab : a ≤ b) (x : R) : clamp a b (clamp a b x) = clamp a b x :=
  clamp_of_mem hab (clamp_mem hab x).1 (clamp_mem hab x).2

/-- The clamp does not increase distances. -/
theorem abs_clamp_sub_le {a b : R} (hab : a ≤ b) (x y : R) :
    abs (clamp a b x - clamp a b y) ≤ abs (x - y) := by
  have := le_abs (x - y)
  apply abs_le.2
  rcases clamp_cases a b x with h | h | h <;> rcases clamp_cases a b y with h' | h' | h' <;>
    (constructor <;> grind)

/-! ## Uniform convergence -/

/-- `f` is **continuous on `S`** (within `S`): nearby points of `S` have nearby values. -/
def ContOn (f : R → R) (S : R → Prop) : Prop :=
  ∀ x, S x → ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧ ∀ y, S y → abs (y - x) < δ → abs (f y - f x) < ε

/-- `fₙ → g` **uniformly on `S`**. -/
def UnifOn (fs : Nat → R → R) (g : R → R) (S : R → Prop) : Prop :=
  ∀ ε : R, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ x, S x → abs (fs n x - g x) < ε

/-- Continuity at every point of `S` implies continuity on `S`. -/
theorem contOn_of_continuousAt {f : R → R} {S : R → Prop} (h : ∀ x, S x → R.ContinuousAt f x) :
    ContOn f S := fun x hx ε hε => by
  obtain ⟨δ, hδ, h'⟩ := h x hx ε hε
  exact ⟨δ, hδ, fun y _ hy => h' y hy⟩

/-- The triangle inequality for three steps. -/
theorem abs_sub_le3 (p q r s : R) : abs (p - s) ≤ abs (p - q) + abs (q - r) + abs (r - s) := by
  have h1 := OF.abs_add (p - q) (q - r)
  have h2 := OF.abs_add (p - q + (q - r)) (r - s)
  rw [show p - q + (q - r) = p - r by grind] at h1
  rw [show p - q + (q - r) + (r - s) = p - s by grind] at h2
  grind

/-- **The uniform limit of continuous functions is continuous** (the ε/3 argument). -/
theorem UnifOn.contOn {fs : Nat → R → R} {g : R → R} {S : R → Prop} (hf : ∀ n, ContOn (fs n) S)
    (hu : UnifOn fs g S) : ContOn g S := fun x hx ε hε => by
  obtain ⟨N, hN⟩ := hu (ε / 3) (by grind)
  obtain ⟨δ, hδ, h⟩ := hf N x hx (ε / 3) (by grind)
  refine ⟨δ, hδ, fun y hy hxy => ?_⟩
  have k1 := hN N (Nat.le_refl N) y hy
  have k2 := h y hy hxy
  have k3 := hN N (Nat.le_refl N) x hx
  have := abs_sub_le3 (g y) (fs N y) (fs N x) (g x)
  rw [abs_sub_comm (g y) (fs N y)] at this
  grind

/-- A function continuous on `[a, b]` becomes continuous everywhere after clamping. -/
theorem continuousAt_comp_clamp {g : R → R} {a b : R} (hab : a ≤ b)
    (hg : ContOn g (fun x => a ≤ x ∧ x ≤ b)) (x : R) : R.ContinuousAt (fun x => g (clamp a b x)) x :=
  fun ε hε => by
  obtain ⟨δ, hδ, h⟩ := hg _ (clamp_mem hab x) ε hε
  exact ⟨δ, hδ, fun y hy => h _ (clamp_mem hab y)
    (Std.lt_of_le_of_lt (abs_clamp_sub_le hab y x) hy)⟩

/-- Riemann sums only see the values on `[a, b]`. -/
theorem rsum_congr_on {f g : R → R} {a b : R} (h : ∀ x, a ≤ x → x ≤ b → f x = g x) :
    ∀ (l : List (R × R)) (a' : R), a ≤ a' → IsTagged a' l b → rsum f a' l = rsum g a' l := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons p l ih =>
    intro a' ha hl
    obtain ⟨t, x⟩ := p
    obtain ⟨h1, h2, h3⟩ := hl
    have := h3.le
    show f t * (x - a') + rsum f x l = g t * (x - a') + rsum g x l
    rw [h t (by grind) (by grind), ih x (by grind) h3]

/-- The integral only depends on the values on `[a, b]`. -/
theorem HasIntegral.congr_on {f g : R → R} {a b I : R} (hf : HasIntegral f a b I)
    (h : ∀ x, a ≤ x → x ≤ b → f x = g x) : HasIntegral g a b I :=
  ⟨hf.1, fun ε hε => by
    obtain ⟨δ, hδ, k⟩ := hf.2 ε hε
    exact ⟨δ, hδ, fun l hl hm => by
      rw [← rsum_congr_on h l a (Std.le_refl a) hl]; exact k l hl hm⟩⟩

/-- **Integral of a uniform limit.** If continuous functions `fₙ` converge uniformly to `g` on
`[a, b]`, then `g` is integrable and `∫ₐᵇ fₙ → ∫ₐᵇ g`. -/
theorem integral_unif_limit {fs : Nat → R → R} {g : R → R} {a b : R} (hab : a ≤ b)
    (hf : ∀ n x, a ≤ x → x ≤ b → R.ContinuousAt (fs n) x)
    (hu : UnifOn fs g (fun x => a ≤ x ∧ x ≤ b)) :
    HasIntegral g a b (integral g a b) ∧ Tendsto (fun n => integral (fs n) a b) (integral g a b) := by
  have hg := hu.contOn fun n => contOn_of_continuousAt fun x hx => hf n x hx.1 hx.2
  obtain ⟨J, hJ'⟩ := integrable_of_continuous hab fun x _ _ => continuousAt_comp_clamp hab hg x
  have hJ : HasIntegral g a b J := HasIntegral.congr_on hJ' fun x h1 h2 => by rw [clamp_of_mem hab h1 h2]
  rw [hJ.integral_eq hab]
  refine ⟨hJ, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hu (ε / (b - a + 1)) (div_pos hε (by grind))
  refine ⟨N, fun n hn => ?_⟩
  have hI := hasIntegral_integral hab fun x h1 h2 => hf n x h1 h2
  have hD := hI.add (hJ.const_mul (-1))
  have k := hD.abs_sub_le (c := 0) (ε := ε / (b - a + 1)) hab fun t h1 h2 => by
    have := hN n hn t ⟨h1, h2⟩
    rw [show fs n t + -1 * g t - 0 = fs n t - g t by grind]; exact Std.le_of_lt this
  rw [show integral (fs n) a b + -1 * J - 0 * (b - a) = integral (fs n) a b - J by grind] at k
  have k2 := OrderedRing.mul_le_mul_of_nonneg_left (by grind : b - a ≤ b - a + 1)
    (Std.le_of_lt (div_pos hε (by grind : 0 < b - a + 1)))
  have e : ε / (b - a + 1) * (b - a + 1) = ε := by grind
  have k3 := OrderedRing.mul_lt_mul_of_pos_left (by grind : b - a < b - a + 1)
    (div_pos hε (by grind : 0 < b - a + 1))
  grind

/-! ## The space `C[a, b]` -/

/-- A witness that `a ≤ b`, supplied as an instance. -/
class LeFact (a b : R) : Prop where
  /-- `a ≤ b`. -/
  le : a ≤ b

/-- **The space `C[a, b]`** of continuous functions on `[a, b]`, each represented by its continuous
extension that is constant outside `[a, b]`. -/
abbrev CFun (a b : R) : Type := {f : R → R // (∀ x, f (clamp a b x) = f x) ∧ ∀ x, R.ContinuousAt f x}

namespace CFun

variable {a b : R} [LeFact a b]

/-- Two continuous functions on `[a, b]` differ by a bounded amount. -/
theorem bounded (f g : CFun a b) : ∃ M, ∀ x, abs (f.1 x - g.1 x) ≤ M := by
  have hab := LeFact.le (a := a) (b := b)
  have hc : ∀ x, R.ContinuousAt (fun x => f.1 x - g.1 x) x := fun x =>
    continuousAt_sub (f.2.2 x) (g.2.2 x)
  obtain ⟨c₁, -, -, h₁⟩ := extreme_value (f := fun x => f.1 x - g.1 x) hab fun x _ _ => hc x
  obtain ⟨c₂, -, -, h₂⟩ := extreme_value (f := fun x => 0 - (f.1 x - g.1 x)) hab
    fun x _ _ => continuousAt_sub (continuousAt_const 0 x) (hc x)
  refine ⟨abs (f.1 c₁ - g.1 c₁) + abs (0 - (f.1 c₂ - g.1 c₂)), fun x => ?_⟩
  have m := clamp_mem hab x
  have k1 := h₁ _ m.1 m.2
  have k2 := h₂ _ m.1 m.2
  rw [f.2.1, g.2.1] at k1 k2
  have := le_abs (f.1 c₁ - g.1 c₁); have := le_abs (0 - (f.1 c₂ - g.1 c₂))
  have := abs_nonneg (f.1 c₁ - g.1 c₁); have := abs_nonneg (0 - (f.1 c₂ - g.1 c₂))
  exact abs_le.2 ⟨by grind, by grind⟩

/-- The **sup distance** `sup_x |f(x) − g(x)|`. -/
noncomputable def supDist (f g : CFun a b) : R :=
  Classical.choose (exists_lub (fun t => ∃ x, t = abs (f.1 x - g.1 x)) ⟨_, 0, rfl⟩
    (by obtain ⟨M, hM⟩ := bounded f g; exact ⟨M, fun t ⟨x, hx⟩ => hx ▸ hM x⟩))

/-- Every value `|f(x) − g(x)|` is at most the sup distance. -/
theorem le_supDist (f g : CFun a b) (x : R) : abs (f.1 x - g.1 x) ≤ supDist f g :=
  (Classical.choose_spec (exists_lub (fun t => ∃ x, t = abs (f.1 x - g.1 x)) ⟨_, 0, rfl⟩
    (by obtain ⟨M, hM⟩ := bounded f g; exact ⟨M, fun t ⟨x, hx⟩ => hx ▸ hM x⟩))).1 _ ⟨x, rfl⟩

/-- A uniform bound on `|f(x) − g(x)|` bounds the sup distance. -/
theorem supDist_le {f g : CFun a b} {M : R} (h : ∀ x, abs (f.1 x - g.1 x) ≤ M) :
    supDist f g ≤ M :=
  (Classical.choose_spec (exists_lub (fun t => ∃ x, t = abs (f.1 x - g.1 x)) ⟨_, 0, rfl⟩
    (by obtain ⟨M, hM⟩ := bounded f g; exact ⟨M, fun t ⟨x, hx⟩ => hx ▸ hM x⟩))).2 M
    fun t ⟨x, hx⟩ => hx ▸ h x

/-- **`C[a, b]` with the sup metric is a metric space.** -/
noncomputable instance instMetric : MetricSpace (CFun a b) where
  dist := supDist
  dist_self f := by
    have h1 := supDist_le (f := f) (g := f) (M := 0) fun x => by
      rw [show f.1 x - f.1 x = 0 by grind, R.abs_zero]; exact Std.le_refl 0
    have h2 := le_supDist f f 0
    have := abs_nonneg (f.1 0 - f.1 0)
    grind
  eq_of_dist_eq_zero {f g} h := by
    apply Subtype.ext; funext x
    have := le_supDist f g x
    have := eq_zero_of_abs_le (x := f.1 x - g.1 x) (by grind)
    grind
  dist_comm f g := by
    have h1 := supDist_le (f := f) (g := g) (M := supDist g f) fun x => by
      rw [abs_sub_comm]; exact le_supDist g f x
    have h2 := supDist_le (f := g) (g := f) (M := supDist f g) fun x => by
      rw [abs_sub_comm]; exact le_supDist f g x
    grind
  dist_triangle f g h := supDist_le fun x => by
    have := OF.abs_add (f.1 x - g.1 x) (g.1 x - h.1 x)
    rw [show f.1 x - g.1 x + (g.1 x - h.1 x) = f.1 x - h.1 x by grind] at this
    have := le_supDist f g x; have := le_supDist g h x
    grind

/-- The distance in `C[a, b]` is the sup distance. -/
theorem dist_eq (f g : CFun a b) : dist f g = supDist f g := rfl

/-- **`C[a, b]` is complete**: a Cauchy sequence for the sup metric converges uniformly to a
continuous function. -/
theorem complete : Complete (CFun a b) := by
  intro s hs
  have hab := LeFact.le (a := a) (b := b)
  -- Pointwise Cauchy, hence pointwise convergent.
  have hpt : ∀ x, ∃ L, Tendsto (fun n => (s n).1 x) L := fun x => cauchy_complete fun ε hε => by
    obtain ⟨N, hN⟩ := hs ε hε
    exact ⟨N, fun m n hm hn => Std.lt_of_le_of_lt (le_supDist _ _ x) (hN m n hm hn)⟩
  let g : R → R := fun x => (hpt x).choose
  have hg : ∀ x, Tendsto (fun n => (s n).1 x) (g x) := fun x => (hpt x).choose_spec
  -- The convergence is uniform.
  have hunif : ∀ ε : R, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ x, abs ((s n).1 x - g x) ≤ ε / 2 := by
    intro ε hε
    obtain ⟨N, hN⟩ := hs (ε / 2) (by grind)
    refine ⟨N, fun n hn x => ?_⟩
    apply Classical.byContradiction; intro hlt
    obtain ⟨M, hM⟩ := hg x (abs ((s n).1 x - g x) - ε / 2) (by grind)
    have k1 := hM (max M N) (by omega)
    have k2 : abs ((s n).1 x - (s (max M N)).1 x) < ε / 2 :=
      Std.lt_of_le_of_lt (le_supDist _ _ x) (hN n (max M N) hn (by omega))
    have := OF.abs_add ((s n).1 x - (s (max M N)).1 x) ((s (max M N)).1 x - g x)
    rw [show (s n).1 x - (s (max M N)).1 x + ((s (max M N)).1 x - g x) = (s n).1 x - g x by
      grind] at this
    grind
  have hu : UnifOn (fun n => (s n).1) g (fun _ => True) := fun ε hε => by
    obtain ⟨N, hN⟩ := hunif ε hε
    exact ⟨N, fun n hn x _ => Std.lt_of_le_of_lt (hN n hn x) (by grind)⟩
  have hcont := hu.contOn fun n => contOn_of_continuousAt fun x _ => (s n).2.2 x
  have hgc : ∀ x, g (clamp a b x) = g x := fun x =>
    tendsto_unique (hg (clamp a b x)) (by
      have : (fun n => (s n).1 (clamp a b x)) = (fun n => (s n).1 x) :=
        funext fun n => (s n).2.1 x
      rw [this]; exact hg x)
  refine ⟨⟨g, hgc, fun x ε hε => by
    obtain ⟨δ, hδ, h⟩ := hcont x trivial ε hε; exact ⟨δ, hδ, fun y hy => h y trivial hy⟩⟩,
    fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hunif ε hε
  exact ⟨N, fun n hn => Std.lt_of_le_of_lt (supDist_le fun x => hN n hn x) (by grind)⟩

end CFun

end Foundations.Topology
