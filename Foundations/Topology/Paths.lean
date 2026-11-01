import Foundations.Topology.Compact
import Foundations.Algebra.Group

/-!
# Paths, homotopies and the fundamental group

With Henri **Poincaré**'s *Analysis Situs* (1895) topology acquired a new kind of invariant:
not a number or a property, but a **group**. Poincaré considered closed curves (*loops*) in a
space, starting and ending at a fixed base point, and declared two loops equivalent when one can
be continuously deformed into the other. Running one loop after another is a multiplication, and
the equivalence classes form the **fundamental group** `π₁(X, x₀)`. Two spaces with different
fundamental groups cannot be homeomorphic: an algebraic difference witnesses a geometric one.

The idea of a **homotopy** — a continuous one-parameter family of maps — is itself a structural
idea in the spirit of the twentieth century: one stops asking what a map *is* and asks only what
it can be *deformed into*. Many questions turn out to depend only on the homotopy class, and the
classes carry algebraic structure that the maps themselves do not have: concatenation of paths
is not associative on the nose (the parametrisations differ), but it is associative *up to
homotopy*, and that is all a group needs.

In this file:

* the **subspace metric** on a subset `{x // A x}` (so that the circle and the disc are metric
  spaces in their own right);
* **joint continuity** of functions of two variables (needed for homotopies), with a sequential
  criterion, closure properties and a **pasting lemma** for maps defined piecewise;
* **paths** (continuous maps from the parameter line, of which only `[0, 1]` matters), their
  **concatenation** `γ ⬝ δ` and **reverse** `γ⁻¹`;
* **homotopy rel endpoints**, an equivalence relation compatible with concatenation and reverse;
* the group laws up to homotopy, all derived from one **reparametrisation lemma**;
* the **fundamental group** `π₁(X, x₀)` as a quotient of loops, an instance of the project's
  `Group` class from Part IV.

Paths are represented by functions on all of `ℝ` which are continuous everywhere; only their values
on `[0, 1]` enter the notion of homotopy. This avoids relative continuity on a subinterval: any
path on `[0, 1]` extends to the whole line by composing with the **clamp** `t ↦ max 0 (min t 1)`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

variable {X Y Z : Type} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-! ## Subspaces -/

/-- **Subspace metric.** a subset `{x // A x}` of a metric space, with the distance of the
ambient space. -/
noncomputable instance instMetricSubtype (A : X → Prop) : MetricSpace {x // A x} where
  dist a b := dist a.1 b.1
  dist_self a := dist_self a.1
  eq_of_dist_eq_zero h := Subtype.ext (eq_of_dist_eq_zero h)
  dist_comm a b := dist_comm a.1 b.1
  dist_triangle a b c := dist_triangle a.1 b.1 c.1

/-- The distance in a subspace is the ambient distance. -/
theorem dist_subtype {A : X → Prop} (a b : {x // A x}) : dist a b = dist a.1 b.1 := rfl

/-- The inclusion of a subspace is continuous. -/
theorem continuous_val (A : X → Prop) : Continuous (fun a : {x // A x} => a.1) :=
  continuous_of_lipschitz (K := 1) (by grind) fun a b => by
    rw [dist_subtype]; grind

/-- A continuous map with values in `A` is continuous as a map into the subspace `A`. -/
theorem continuous_subtype_mk {A : X → Prop} {f : Y → X} (hf : Continuous f) (h : ∀ y, A (f y)) :
    Continuous (fun y => (⟨f y, h y⟩ : {x // A x})) := fun y ε hε => hf y ε hε

/-! ## The clamp onto `[0, 1]` -/

/-- The **clamp** `t ↦ max 0 (min t 1)`, retracting the line onto `[0, 1]`. -/
noncomputable def clamp01 (t : R) : R :=
  open Classical in if t ≤ 0 then 0 else if t ≤ 1 then t else 1

/-- The clamp takes values in `[0, 1]`. -/
theorem clamp01_mem (t : R) : 0 ≤ clamp01 t ∧ clamp01 t ≤ 1 := by
  unfold clamp01; split <;> (try split) <;> grind

/-- The clamp fixes `[0, 1]`. -/
theorem clamp01_of_mem {t : R} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clamp01 t = t := by
  unfold clamp01; split <;> (try split) <;> grind

/-- The clamp does not increase distances. -/
theorem abs_clamp01_sub (a b : R) : abs (clamp01 a - clamp01 b) ≤ abs (a - b) := by
  have := le_abs (a - b)
  apply abs_le.2
  unfold clamp01
  by_cases ha0 : a ≤ 0 <;> by_cases ha1 : a ≤ 1 <;> by_cases hb0 : b ≤ 0 <;>
    by_cases hb1 : b ≤ 1 <;> simp only [ha0, ha1, hb0, hb1, ↓reduceIte] <;> grind

/-- The clamp is continuous. -/
theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_of_lipschitz (K := 1) (by grind) fun a b => by
    rw [dist_R, dist_R]; have := abs_clamp01_sub a b; grind

/-- Affine maps `t ↦ a t + b` of the line are continuous. -/
theorem continuous_affine (a b : R) : Continuous (fun t : R => a * t + b) :=
  continuous_of_lipschitz (abs_nonneg a) fun x y => by
    rw [dist_R, dist_R, show a * x + b - (a * y + b) = a * (x - y) by grind, abs_mul]
    exact Std.le_refl _

/-- Continuity is a property of the function, not of its expression. -/
theorem Continuous.congr {f g : X → Y} (hf : Continuous f) (h : ∀ x, f x = g x) : Continuous g := by
  have : f = g := funext h
  exact this ▸ hf

/-- `t ↦ 2t` is continuous. -/
theorem continuous_two_mul : Continuous (fun t : R => 2 * t) :=
  (continuous_affine 2 0).congr fun t => by grind

/-- `t ↦ 2t − 1` is continuous. -/
theorem continuous_two_mul_sub_one : Continuous (fun t : R => 2 * t - 1) :=
  (continuous_affine 2 (-1)).congr fun t => by grind

/-- `t ↦ 1 − t` is continuous. -/
theorem continuous_one_sub : Continuous (fun t : R => 1 - t) :=
  (continuous_affine (-1) 1).congr fun t => by grind

/-! ## Joint continuity -/

variable {A B P Q : Type} [MetricSpace A] [MetricSpace B] [MetricSpace P] [MetricSpace Q]

/-- A function `H` of two variables is **jointly continuous**: `H a' b'` is close to `H a b`
whenever `a'` is close to `a` *and* `b'` is close to `b`. (Equivalently: continuity on the
product space.) -/
def Cont2 (H : A → B → X) : Prop :=
  ∀ a b, ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧
    ∀ a' b', dist a' a < δ → dist b' b < δ → dist (H a' b') (H a b) < ε

/-- Jointly continuous maps preserve limits of pairs of sequences. -/
theorem Cont2.seq {H : A → B → X} (hH : Cont2 H) {sa : Nat → A} {sb : Nat → B} {a : A}
    {b : B} (ha : Converges sa a) (hb : Converges sb b) :
    Converges (fun n => H (sa n) (sb n)) (H a b) := fun ε hε => by
  obtain ⟨δ, hδ, h⟩ := hH a b ε hε
  obtain ⟨N₁, h₁⟩ := ha δ hδ
  obtain ⟨N₂, h₂⟩ := hb δ hδ
  exact ⟨max N₁ N₂, fun n hn => h _ _ (h₁ n (by omega)) (h₂ n (by omega))⟩

/-- **Sequential criterion for joint continuity.** -/
theorem cont2_of_seq {H : A → B → X}
    (h : ∀ (sa : Nat → A) (sb : Nat → B) a b, Converges sa a → Converges sb b →
      Converges (fun n => H (sa n) (sb n)) (H a b)) : Cont2 H := by
  intro a b ε hε
  apply Classical.byContradiction; intro hno
  have hx : ∀ n : Nat, ∃ p : A × B, dist p.1 a < 1 / ((n : R) + 1) ∧
      dist p.2 b < 1 / ((n : R) + 1) ∧ ε ≤ dist (H p.1 p.2) (H a b) := fun n => by
    apply Classical.byContradiction; intro h'
    exact hno ⟨1 / ((n : R) + 1), eps_pos n, fun a' b' h1 h2 => by
      apply Classical.byContradiction; intro h3; exact h' ⟨(a', b'), h1, h2, by grind⟩⟩
  let p : Nat → A × B := fun n => (hx n).choose
  have hp : ∀ n, _ := fun n => (hx n).choose_spec
  obtain ⟨N, hN⟩ := h (fun n => (p n).1) (fun n => (p n).2) a b
    (converges_of_dist_lt fun n => (hp n).1) (converges_of_dist_lt fun n => (hp n).2.1) ε hε
  have := hN N (Nat.le_refl N); have := (hp N).2.2; grind

/-- A constant function of two variables is jointly continuous. -/
theorem cont2_const (c : X) : Cont2 (fun (_ : A) (_ : B) => c) :=
  fun _ _ _ hε => ⟨1, by grind, fun _ _ _ _ => by rw [dist_self]; exact hε⟩

/-- The first projection is jointly continuous. -/
theorem cont2_fst : Cont2 (fun (a : A) (_ : B) => a) :=
  fun _ _ ε hε => ⟨ε, hε, fun _ _ h _ => h⟩

/-- The second projection is jointly continuous. -/
theorem cont2_snd : Cont2 (fun (_ : A) (b : B) => b) :=
  fun _ _ ε hε => ⟨ε, hε, fun _ _ _ h => h⟩

/-- Post-composition with a continuous map. -/
theorem Cont2.comp_left {f : X → Y} (hf : Continuous f) {H : A → B → X} (hH : Cont2 H) :
    Cont2 (fun a b => f (H a b)) := cont2_of_seq fun _ _ _ _ ha hb =>
  (continuousAt_iff_seq f _).1 (hf _) _ (hH.seq ha hb)

/-- Substitution of jointly continuous functions into a jointly continuous function. -/
theorem Cont2.comp2 {H : A → B → X} (hH : Cont2 H) {F : P → Q → A} {G : P → Q → B}
    (hF : Cont2 F) (hG : Cont2 G) : Cont2 (fun p q => H (F p q) (G p q)) :=
  cont2_of_seq fun _ _ _ _ hp hq => hH.seq (hF.seq hp hq) (hG.seq hp hq)

/-- Exchanging the variables preserves joint continuity. -/
theorem Cont2.swap {H : A → B → X} (hH : Cont2 H) : Cont2 (fun b a => H a b) :=
  hH.comp2 cont2_snd cont2_fst

/-- A continuous function of the first variable is jointly continuous. -/
theorem Continuous.cont2_left {f : A → X} (hf : Continuous f) :
    Cont2 (fun a (_ : B) => f a) := cont2_fst.comp_left hf

/-- A continuous function of the second variable is jointly continuous. -/
theorem Continuous.cont2_right {f : B → X} (hf : Continuous f) :
    Cont2 (fun (_ : A) b => f b) := cont2_snd.comp_left hf

/-- Fixing the first variable of a jointly continuous function gives a continuous function. -/
theorem Cont2.slice {H : A → B → X} (hH : Cont2 H) (a : A) : Continuous (fun b => H a b) :=
  fun b ε hε => by
    obtain ⟨δ, hδ, h⟩ := hH a b ε hε
    exact ⟨δ, hδ, fun b' hb' => h a b' (by rw [dist_self]; exact hδ) hb'⟩

/-- Fixing the second variable of a jointly continuous function gives a continuous function. -/
theorem Cont2.slice' {H : A → B → X} (hH : Cont2 H) (b : B) : Continuous (fun a => H a b) :=
  hH.swap.slice b

/-- Addition of reals is jointly continuous. -/
theorem cont2_add : Cont2 (fun x y : R => x + y) :=
  cont2_of_seq fun _ _ _ _ ha hb => Tendsto.add ha hb

/-- Subtraction of reals is jointly continuous. -/
theorem cont2_sub : Cont2 (fun x y : R => x - y) :=
  cont2_of_seq fun _ _ _ _ ha hb => Tendsto.sub ha hb

/-- Multiplication of reals is jointly continuous. -/
theorem cont2_mul : Cont2 (fun x y : R => x * y) :=
  cont2_of_seq fun _ _ _ _ ha hb => Tendsto.mul ha hb

/-- Sums of jointly continuous real functions. -/
theorem Cont2.add {F G : A → B → R} (hF : Cont2 F) (hG : Cont2 G) :
    Cont2 (fun a b => F a b + G a b) := cont2_add.comp2 hF hG

/-- Differences of jointly continuous real functions. -/
theorem Cont2.sub {F G : A → B → R} (hF : Cont2 F) (hG : Cont2 G) :
    Cont2 (fun a b => F a b - G a b) := cont2_sub.comp2 hF hG

/-- Products of jointly continuous real functions. -/
theorem Cont2.mul {F G : A → B → R} (hF : Cont2 F) (hG : Cont2 G) :
    Cont2 (fun a b => F a b * G a b) := cont2_mul.comp2 hF hG

/-! ## The pasting lemma -/

/-- **Pasting lemma.** Two jointly continuous functions which agree on the line `t = c` glue to a
jointly continuous function: `F` for `t ≤ c`, `G` for `t > c`. -/
theorem Cont2.paste {F G : A → R → X} {c : R} (hF : Cont2 F) (hG : Cont2 G)
    (h : ∀ a, F a c = G a c) :
    Cont2 (fun a t => open Classical in if t ≤ c then F a t else G a t) := by
  intro a t ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hF a t ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hG a t ε hε
  rcases (by grind : t < c ∨ t = c ∨ c < t) with ht | ht | ht
  · obtain ⟨δ, hδ, e1, e2⟩ := exists_pos_le_both hδ₁ (by grind : 0 < c - t)
    refine ⟨δ, hδ, fun a' t' ha ht' => ?_⟩
    have : t' ≤ c := by rw [dist_R] at ht'; have := (abs_lt.1 ht'); grind
    simp only [this, Std.le_of_lt ht, ite_true]; exact h₁ a' t' (by grind) (by grind)
  · subst ht
    obtain ⟨δ, hδ, e1, e2⟩ := exists_pos_le_both hδ₁ hδ₂
    refine ⟨δ, hδ, fun a' t' ha ht' => ?_⟩
    simp only [Std.le_refl, ite_true]
    split
    · exact h₁ a' t' (by grind) (by grind)
    · rw [h a]; exact h₂ a' t' (by grind) (by grind)
  · obtain ⟨δ, hδ, e1, e2⟩ := exists_pos_le_both hδ₂ (by grind : 0 < t - c)
    refine ⟨δ, hδ, fun a' t' ha ht' => ?_⟩
    have : ¬ t' ≤ c := by rw [dist_R] at ht'; have := (abs_lt.1 ht'); grind
    have h' : ¬ t ≤ c := by grind
    simp only [this, h', ite_false]; exact h₂ a' t' (by grind) (by grind)

/-- The pasting lemma in the first variable. -/
theorem Cont2.paste' {F G : R → B → X} {c : R} (hF : Cont2 F) (hG : Cont2 G)
    (h : ∀ b, F c b = G c b) :
    Cont2 (fun s b => open Classical in if s ≤ c then F s b else G s b) :=
  (Cont2.paste hF.swap hG.swap h).swap

/-- **Pasting lemma, one variable.** Two continuous functions agreeing at `c` glue to a continuous
function. -/
theorem Continuous.paste {f g : R → X} {c : R} (hf : Continuous f) (hg : Continuous g)
    (h : f c = g c) : Continuous (fun t => open Classical in if t ≤ c then f t else g t) :=
  (Cont2.paste (A := R) hf.cont2_right hg.cont2_right (fun _ => h)).slice 0

/-! ## Paths -/

/-- A **path** from `x` to `y`: a continuous map `γ` of the parameter line into `X` with
`γ 0 = x` and `γ 1 = y`. (Only the values on `[0, 1]` matter.) -/
structure Path (x y : X) where
  /-- The parametrisation. -/
  toFun : R → X
  /-- It is continuous. -/
  cont : Continuous toFun
  /-- It starts at `x`. -/
  source : toFun 0 = x
  /-- It ends at `y`. -/
  target : toFun 1 = y

namespace Path

variable {x y z w : X}

/-- The **constant path** at `x`. -/
def const (x : X) : Path x x where
  toFun _ := x
  cont := fun _ ε hε => ⟨1, by grind, fun _ _ => by rw [dist_self]; exact hε⟩
  source := rfl
  target := rfl

/-- The **concatenation** `γ ⬝ δ`: run through `γ` at double speed, then through `δ`. -/
noncomputable def trans (γ : Path x y) (δ : Path y z) : Path x z where
  toFun t := open Classical in if t ≤ 1 / 2 then γ.toFun (2 * t) else δ.toFun (2 * t - 1)
  cont := Continuous.paste (γ.cont.comp continuous_two_mul)
    (δ.cont.comp continuous_two_mul_sub_one)
    (by rw [show 2 * (1 / 2 : R) = 1 by grind, show (1 : R) - 1 = 0 by grind, γ.target,
      δ.source])
  source := by rw [ite_eq_left (by grind), show 2 * (0 : R) = 0 by grind, γ.source]
  target := by
    rw [ite_eq_right (by grind), show 2 * (1 : R) - 1 = 1 by grind, δ.target]

/-- The **reverse** path `γ⁻¹`, run backwards. -/
def symm (γ : Path x y) : Path y x where
  toFun t := γ.toFun (1 - t)
  cont := γ.cont.comp continuous_one_sub
  source := by rw [show (1 : R) - 0 = 1 by grind, γ.target]
  target := by rw [show (1 : R) - 1 = 0 by grind, γ.source]

/-- Values of a concatenation. -/
theorem trans_apply (γ : Path x y) (δ : Path y z) (t : R) :
    (γ.trans δ).toFun t =
      (open Classical in if t ≤ 1 / 2 then γ.toFun (2 * t) else δ.toFun (2 * t - 1)) := rfl

/-! ## Homotopy rel endpoints -/

/-- Two paths `γ, δ` from `x` to `y` are **homotopic rel endpoints** if there is a jointly
continuous `H(s, t)` with `H(0, ·) = γ`, `H(1, ·) = δ` on `[0, 1]`, and every intermediate path
`H(s, ·)` also runs from `x` to `y`. -/
def Homotopic (γ δ : Path x y) : Prop :=
  ∃ H : R → R → X, Cont2 H ∧
    (∀ t, 0 ≤ t → t ≤ 1 → H 0 t = γ.toFun t) ∧ (∀ t, 0 ≤ t → t ≤ 1 → H 1 t = δ.toFun t) ∧
    (∀ s, 0 ≤ s → s ≤ 1 → H s 0 = x) ∧ (∀ s, 0 ≤ s → s ≤ 1 → H s 1 = y)

/-- Homotopy is reflexive. -/
theorem Homotopic.refl (γ : Path x y) : Homotopic γ γ :=
  ⟨fun _ t => γ.toFun t, γ.cont.cont2_right, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => γ.source, fun _ _ _ => γ.target⟩

/-- Paths that agree on `[0, 1]` are homotopic. -/
theorem Homotopic.of_eq {γ δ : Path x y} (h : ∀ t, 0 ≤ t → t ≤ 1 → γ.toFun t = δ.toFun t) :
    Homotopic γ δ :=
  ⟨fun _ t => γ.toFun t, γ.cont.cont2_right, fun _ _ _ => rfl, h,
    fun _ _ _ => γ.source, fun _ _ _ => γ.target⟩

/-- Homotopy is symmetric: run the deformation backwards. -/
theorem Homotopic.symm {γ δ : Path x y} (h : Homotopic γ δ) : Homotopic δ γ := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  refine ⟨fun s t => H (1 - s) t, hH.comp2 continuous_one_sub.cont2_left cont2_snd, fun t a b => ?_, fun t a b => ?_,
    fun s a b => hx _ (by grind) (by grind), fun s a b => hy _ (by grind) (by grind)⟩
  · (try simp only); rw [show (1 : R) - 0 = 1 by grind]; exact h1 t a b
  · (try simp only); rw [show (1 : R) - 1 = 0 by grind]; exact h0 t a b

/-- Homotopy is transitive: perform the two deformations one after the other. -/
theorem Homotopic.trans {γ δ ε : Path x y} (h₁ : Homotopic γ δ) (h₂ : Homotopic δ ε) :
    Homotopic γ ε := by
  obtain ⟨H₁, hH₁, a0, a1, ax, ay⟩ := h₁
  obtain ⟨H₂, hH₂, b0, b1, bx, by'⟩ := h₂
  have c1 : Cont2 (fun s t : R => H₁ (2 * s) (clamp01 t)) :=
    hH₁.comp2 continuous_two_mul.cont2_left
      continuous_clamp01.cont2_right
  have c2 : Cont2 (fun s t : R => H₂ (2 * s - 1) (clamp01 t)) :=
    hH₂.comp2 continuous_two_mul_sub_one.cont2_left
      continuous_clamp01.cont2_right
  refine ⟨_, Cont2.paste' (c := 1 / 2) c1 c2 fun t => ?_, fun t t0 t1 => ?_, fun t t0 t1 => ?_,
    fun s s0 s1 => ?_, fun s s0 s1 => ?_⟩
  · have := clamp01_mem t
    (try simp only); rw [show 2 * (1 / 2 : R) = 1 by grind, show (1 : R) - 1 = 0 by grind,
      a1 _ this.1 this.2, b0 _ this.1 this.2]
  · (try simp only); rw [ite_eq_left (by grind), show 2 * (0 : R) = 0 by grind, clamp01_of_mem t0 t1]
    exact a0 t t0 t1
  · (try simp only); rw [ite_eq_right (by grind), show 2 * (1 : R) - 1 = 1 by grind, clamp01_of_mem t0 t1]
    exact b1 t t0 t1
  · (try simp only); rw [clamp01_of_mem (Std.le_refl 0) (by grind)]
    split
    · exact ax _ (by grind) (by grind)
    · exact bx _ (by grind) (by grind)
  · (try simp only); rw [clamp01_of_mem (by grind) (Std.le_refl 1)]
    split
    · exact ay _ (by grind) (by grind)
    · exact by' _ (by grind) (by grind)

/-- **Concatenation respects homotopy.** -/
theorem Homotopic.trans_congr {γ γ' : Path x y} {δ δ' : Path y z} (h₁ : Homotopic γ γ')
    (h₂ : Homotopic δ δ') : Homotopic (γ.trans δ) (γ'.trans δ') := by
  obtain ⟨H₁, hH₁, a0, a1, ax, ay⟩ := h₁
  obtain ⟨H₂, hH₂, b0, b1, bx, by'⟩ := h₂
  have c1 : Cont2 (fun s t : R => H₁ (clamp01 s) (2 * t)) :=
    hH₁.comp2 continuous_clamp01.cont2_left
      continuous_two_mul.cont2_right
  have c2 : Cont2 (fun s t : R => H₂ (clamp01 s) (2 * t - 1)) :=
    hH₂.comp2 continuous_clamp01.cont2_left
      continuous_two_mul_sub_one.cont2_right
  refine ⟨_, Cont2.paste (c := 1 / 2) c1 c2 fun s => ?_, fun t t0 t1 => ?_, fun t t0 t1 => ?_,
    fun s s0 s1 => ?_, fun s s0 s1 => ?_⟩
  · have := clamp01_mem s
    (try simp only); rw [show 2 * (1 / 2 : R) = 1 by grind, show (1 : R) - 1 = 0 by grind,
      ay _ this.1 this.2, bx _ this.1 this.2]
  · (try simp only); rw [trans_apply, clamp01_of_mem (Std.le_refl 0) (by grind)]
    split
    · exact a0 _ (by grind) (by grind)
    · exact b0 _ (by grind) (by grind)
  · (try simp only); rw [trans_apply, clamp01_of_mem (by grind) (Std.le_refl 1)]
    split
    · exact a1 _ (by grind) (by grind)
    · exact b1 _ (by grind) (by grind)
  · have := clamp01_mem s
    (try simp only); rw [ite_eq_left (by grind), show 2 * (0 : R) = 0 by grind]; exact ax _ this.1 this.2
  · have := clamp01_mem s
    (try simp only); rw [ite_eq_right (by grind), show 2 * (1 : R) - 1 = 1 by grind]; exact by' _ this.1 this.2

/-- **Reversal respects homotopy.** -/
theorem Homotopic.symm_congr {γ γ' : Path x y} (h : Homotopic γ γ') :
    Homotopic γ.symm γ'.symm := by
  obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
  exact ⟨fun s t => H s (1 - t), hH.comp2 cont2_fst continuous_one_sub.cont2_right, fun t a b => h0 _ (by grind) (by grind),
    fun t a b => h1 _ (by grind) (by grind),
    fun s a b => by (try simp only); rw [show (1 : R) - 0 = 1 by grind]; exact hy s a b,
    fun s a b => by (try simp only); rw [show (1 : R) - 1 = 0 by grind]; exact hx s a b⟩

/-- **Reparametrisation lemma.** If `P = g ∘ φ` and `Q = g ∘ ψ` on `[0, 1]` for one continuous
`g` and continuous reparametrisations `φ, ψ` with the same values at `0` and `1`, then `P` and `Q`
are homotopic: slide linearly from `φ` to `ψ`. -/
theorem homotopic_of_reparam {g : R → X} (hg : Continuous g) {φ ψ : R → R} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h0 : φ 0 = ψ 0) (h1 : φ 1 = ψ 1) (P Q : Path x y)
    (hP : ∀ t, 0 ≤ t → t ≤ 1 → P.toFun t = g (φ t))
    (hQ : ∀ t, 0 ≤ t → t ≤ 1 → Q.toFun t = g (ψ t)) : Homotopic P Q := by
  have hs : Cont2 (fun s _ : R => s) := cont2_fst
  have hφ' : Cont2 (fun _ t : R => φ t) := hφ.cont2_right
  have hψ' : Cont2 (fun _ t : R => ψ t) := hψ.cont2_right
  refine ⟨fun s t => g ((1 - s) * φ t + s * ψ t),
    Cont2.comp_left hg ((((cont2_const 1).sub hs).mul hφ').add (hs.mul hψ')),
    fun t a b => ?_, fun t a b => ?_, fun s a b => ?_, fun s a b => ?_⟩
  · rw [hP t a b]; (try simp only); congr 1; grind
  · rw [hQ t a b]; (try simp only); congr 1; grind
  · have := hP 0 (Std.le_refl 0) (by grind); rw [P.source] at this
    rw [this]; (try simp only); congr 1; rw [← h0]; grind
  · have := hP 1 (by grind) (Std.le_refl 1); rw [P.target] at this
    rw [this]; (try simp only); congr 1; rw [← h1]; grind

end Path

end Foundations.Topology
