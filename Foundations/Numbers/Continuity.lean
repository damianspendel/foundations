import Foundations.Numbers.Analysis

/-!
# Analysis on the reals II: continuous functions

A function `f : ℝ → ℝ` is **continuous at `x`** if `f y` can be kept within any `ε > 0` of `f x`
by keeping `y` within some `δ > 0` of `x` — Weierstrass's ε-δ definition, which replaced the
intuitive "can be drawn without lifting the pen" by a statement about numbers only.

We prove the two classical theorems about continuous functions on a closed interval `[a, b]`:

* the **intermediate value theorem** (Bolzano, 1817): a continuous function that is `≤ 0` at `a`
  and `≥ 0` at `b` has a zero in between — proved by taking the supremum of the points where
  `f ≤ 0`. Over the rationals this fails: `x² − 2` changes sign on `[1, 2]` without a rational
  zero;
* the **extreme value theorem** (Weierstrass): a continuous function on `[a, b]` attains a
  maximum — proved with Bolzano–Weierstrass.

As an application, every non-negative real has an **`n`-th root** for every `n ≥ 1`.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-- `f` is **continuous at `x`** (ε-δ definition). -/
def ContinuousAt (f : R → R) (x : R) : Prop :=
  ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧ ∀ y, abs (y - x) < δ → abs (f y - f x) < ε

/-- Constant functions are continuous. -/
theorem continuousAt_const (c x : R) : ContinuousAt (fun _ => c) x := fun ε hε =>
  ⟨1, by grind, fun y _ => by
    have : c - c = 0 := by grind
    simp only [this]; rcases abs_cases (0 : R) with h | h <;> grind⟩

/-- The identity function is continuous. -/
theorem continuousAt_id (x : R) : ContinuousAt (fun y => y) x := fun ε hε =>
  ⟨ε, hε, fun _ hy => hy⟩

/-- The difference of continuous functions is continuous. -/
theorem continuousAt_sub {f g : R → R} {x : R} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y => f y - g y) x := fun ε hε => by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε / 2) (by grind)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε / 2) (by grind)
  have hδ : ∃ δ : R, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ := by
    rcases (by grind : δ₁ ≤ δ₂ ∨ δ₂ ≤ δ₁) with h | h
    · exact ⟨δ₁, hδ₁, by grind, h⟩
    · exact ⟨δ₂, hδ₂, h, by grind⟩
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := hδ
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have k1 := h₁ y (by grind)
  have k2 := h₂ y (by grind)
  have k3 := abs_add (f y - f x) (-(g y - g x))
  have e1 : f y - f x + -(g y - g x) = f y - g y - (f x - g x) := by grind
  have e2 : abs (-(g y - g x)) = abs (g y - g x) := by
    rw [show -(g y - g x) = g x - g y by grind, abs_sub_comm]
  rw [e1, e2] at k3
  grind

/-- The product of continuous functions is continuous. -/
theorem continuousAt_mul {f g : R → R} {x : R} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y => f y * g y) x := fun ε hε => by
  let A := abs (g x) + 1
  let B := abs (f x) + 1
  have hA : 0 < A := by have := abs_nonneg (g x); grind
  have hB : 0 < B := by have := abs_nonneg (f x); grind
  have hη : 0 < ε / (A + B) := div_pos hε (by grind)
  -- Shrink `η` to at most `1`, so that `|f y| ≤ |f x| + 1 = B`.
  have hη' : ∃ η : R, 0 < η ∧ η ≤ 1 ∧ η ≤ ε / (A + B) := by
    rcases (by grind : (1 : R) ≤ ε / (A + B) ∨ ε / (A + B) ≤ 1) with h | h
    · exact ⟨1, by grind, by grind, h⟩
    · exact ⟨ε / (A + B), hη, h, by grind⟩
  obtain ⟨η, hη0, hη1, hη2⟩ := hη'
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf η hη0
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg η hη0
  have hδ : ∃ δ : R, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ := by
    rcases (by grind : δ₁ ≤ δ₂ ∨ δ₂ ≤ δ₁) with h | h
    · exact ⟨δ₁, hδ₁, by grind, h⟩
    · exact ⟨δ₂, hδ₂, h, by grind⟩
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := hδ
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have kf := h₁ y (by grind)
  have kg := h₂ y (by grind)
  have hfy : abs (f y) ≤ B := by
    have := abs_add (f y - f x) (f x)
    rw [show f y - f x + f x = f y by grind] at this; grind
  have k1 := abs_mul_lt hfy hB (by grind : abs (g y - g x) < ε / (A + B))
  have k2 := abs_mul_lt (Std.le_of_lt (by grind : abs (g x) < A)) hA
    (by grind : abs (f y - f x) < ε / (A + B))
  have k3 := abs_add (f y * (g y - g x)) (g x * (f y - f x))
  have e : f y * (g y - g x) + g x * (f y - f x) = f y * g y - f x * g x := by grind
  rw [e] at k3
  have e2 : B * (ε / (A + B)) + A * (ε / (A + B)) = ε := by grind
  grind

/-- Powers `y ↦ yⁿ` are continuous. -/
theorem continuousAt_pow (n : Nat) (x : R) : ContinuousAt (fun y => y ^ n) x := by
  induction n with
  | zero => exact continuousAt_const 1 x
  | succ n ih => exact continuousAt_mul ih (continuousAt_id x)

/-- **Sequential continuity.** If `f` is continuous at `L` and `xₖ → L`, then `f xₖ → f L`. -/
theorem tendsto_comp {f : R → R} {L : R} {x : Nat → R} (hf : ContinuousAt f L)
    (hx : Tendsto x L) : Tendsto (fun k => f (x k)) (f L) := fun ε hε => by
  obtain ⟨δ, hδ, h⟩ := hf ε hε
  obtain ⟨N, hN⟩ := hx δ hδ
  exact ⟨N, fun n hn => h _ (hN n hn)⟩

/-! ## The intermediate value theorem -/

/-- **Intermediate value theorem.** A function continuous on `[a, b]` with `f a ≤ 0 ≤ f b` has a
zero in `[a, b]`. -/
theorem intermediate_value {f : R → R} {a b : R} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ f c = 0 := by
  let S : R → Prop := fun x => a ≤ x ∧ x ≤ b ∧ f x ≤ 0
  obtain ⟨c, hc1, hc2⟩ := exists_lub S ⟨a, by grind, hab, ha⟩ ⟨b, fun x hx => hx.2.1⟩
  have hac : a ≤ c := hc1 a ⟨by grind, hab, ha⟩
  have hcb : c ≤ b := hc2 b fun x hx => hx.2.1
  refine ⟨c, hac, hcb, ?_⟩
  rcases (by grind : f c < 0 ∨ f c = 0 ∨ 0 < f c) with h | h | h
  · -- Points slightly to the right of `c` still have `f < 0`.
    exfalso
    have hcb' : c < b := by
      apply Classical.byContradiction; intro h'; have : c = b := by grind
      rw [this] at h; grind
    obtain ⟨δ, hδ, hδf⟩ := hf c hac hcb (-f c) (by grind)
    have hy : ∃ y, c < y ∧ y ≤ b ∧ abs (y - c) < δ := by
      rcases (by grind : c + δ / 2 ≤ b ∨ b < c + δ / 2) with h' | h'
      · exact ⟨c + δ / 2, by grind, h', abs_lt.2 ⟨by grind, by grind⟩⟩
      · exact ⟨b, hcb', Std.le_refl b, abs_lt.2 ⟨by grind, by grind⟩⟩
    obtain ⟨y, hy1, hy2, hy3⟩ := hy
    have := abs_lt.1 (hδf y hy3)
    have := hc1 y ⟨by grind, hy2, by grind⟩
    grind
  · exact h
  · -- Points slightly to the left of `c` have `f > 0`, so `c − δ/2` is a smaller upper bound.
    exfalso
    obtain ⟨δ, hδ, hδf⟩ := hf c hac hcb (f c) h
    have := hc2 (c - δ / 2) fun x ⟨hx1, hx2, hx3⟩ => by
      apply Classical.byContradiction; intro hlt
      have hxc := hc1 x ⟨hx1, hx2, hx3⟩
      have := abs_lt.1 (hδf x (abs_lt.2 ⟨by grind, by grind⟩))
      grind
    grind

/-- **Intermediate value theorem (general form).** A continuous function on `[a, b]` takes every
value between `f a` and `f b`. -/
theorem intermediate_value' {f : R → R} {a b v : R} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) (ha : f a ≤ v) (hb : v ≤ f b) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ f c = v := by
  obtain ⟨c, h1, h2, h3⟩ := intermediate_value (f := fun x => f x - v) hab
    (fun x hx1 hx2 => continuousAt_sub (hf x hx1 hx2) (continuousAt_const v x))
    (by grind) (by grind)
  exact ⟨c, h1, h2, by grind⟩

/-! ## The extreme value theorem -/

/-- A sequence in `[a, b]` is bounded. -/
theorem bounded_of_mem {x : Nat → R} {a b : R} (h : ∀ n, a ≤ x n ∧ x n ≤ b) :
    ∃ B, ∀ n, abs (x n) ≤ B :=
  ⟨abs a + abs b, fun n => by
    have := h n; have := le_abs a; have := le_abs b; exact abs_le.2 ⟨by grind, by grind⟩⟩

/-- A continuous function on `[a, b]` is bounded above. -/
theorem bounded_above {f : R → R} {a b : R} (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) :
    ∃ M, ∀ x, a ≤ x → x ≤ b → f x ≤ M := by
  apply Classical.byContradiction
  intro hno
  have hx : ∀ n : Nat, ∃ x, (a ≤ x ∧ x ≤ b) ∧ (n : R) < f x := fun n => by
    apply Classical.byContradiction; intro h
    exact hno ⟨n, fun x h1 h2 => by
      apply Classical.byContradiction; intro h3; exact h ⟨x, ⟨h1, h2⟩, by grind⟩⟩
  let xs : Nat → R := fun n => (hx n).choose
  have hxs : ∀ n, (a ≤ xs n ∧ xs n ≤ b) ∧ (n : R) < f (xs n) := fun n => (hx n).choose_spec
  obtain ⟨φ, hφ, L, hL⟩ := bolzano_weierstrass (bounded_of_mem fun n => (hxs n).1)
  have haL : a ≤ L := le_of_tendsto hL fun k => (hxs (φ k)).1.1
  have hLb : L ≤ b := tendsto_le hL fun k => (hxs (φ k)).1.2
  obtain ⟨N, hN⟩ := tendsto_comp (hf L haL hLb) hL 1 (by grind)
  obtain ⟨m, hm⟩ := archimedean (f L + 1)
  let k := max N m
  have k1 := abs_lt.1 (hN k (by omega))
  have k2 := (hxs (φ k)).2
  have k3 : (m : R) ≤ (φ k : R) :=
    OrderedRing.natCast_le_natCast_of_le _ _ (by have := le_of_strictMono hφ k; omega)
  simp only at k1
  grind

/-- **Extreme value theorem.** A function continuous on `[a, b]` attains a maximum there. -/
theorem extreme_value {f : R → R} {a b : R} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x → x ≤ b → f x ≤ f c := by
  obtain ⟨M₀, hM₀⟩ := bounded_above hf
  let S : R → Prop := fun y => ∃ x, a ≤ x ∧ x ≤ b ∧ y = f x
  obtain ⟨M, hM1, hM2⟩ := exists_lub S ⟨f a, a, by grind, hab, rfl⟩
    ⟨M₀, fun y ⟨x, h1, h2, hy⟩ => hy ▸ hM₀ x h1 h2⟩
  -- Choose points where `f` exceeds `M − 1/(n+1)`.
  have hx : ∀ n : Nat, ∃ x, (a ≤ x ∧ x ≤ b) ∧ M - 1 / ((n : R) + 1) < f x := fun n => by
    apply Classical.byContradiction; intro h
    have := hM2 (M - 1 / ((n : R) + 1)) fun y ⟨x, h1, h2, hy⟩ => by
      apply Classical.byContradiction; intro h3; exact h ⟨x, ⟨h1, h2⟩, by grind⟩
    have := eps_pos n; grind
  let xs : Nat → R := fun n => (hx n).choose
  have hxs : ∀ n, (a ≤ xs n ∧ xs n ≤ b) ∧ M - 1 / ((n : R) + 1) < f (xs n) :=
    fun n => (hx n).choose_spec
  obtain ⟨φ, hφ, L, hL⟩ := bolzano_weierstrass (bounded_of_mem fun n => (hxs n).1)
  have haL : a ≤ L := le_of_tendsto hL fun k => (hxs (φ k)).1.1
  have hLb : L ≤ b := tendsto_le hL fun k => (hxs (φ k)).1.2
  -- `f (x_{φ k}) → f L` by continuity, and `f (x_{φ k}) → M` by construction.
  have h1 := tendsto_comp (hf L haL hLb) hL
  have h2 : Tendsto (fun k => f (xs (φ k))) M := fun ε hε => by
    obtain ⟨N, hN⟩ := eps_small hε
    refine ⟨N, fun k hk => abs_lt.2 ⟨?_, ?_⟩⟩
    · have := (hxs (φ k)).2
      have := hN (φ k) (by have := le_of_strictMono hφ k; omega)
      grind
    · have := hM1 _ ⟨xs (φ k), (hxs (φ k)).1.1, (hxs (φ k)).1.2, rfl⟩; grind
  have hfL : f L = M := tendsto_unique h1 h2
  exact ⟨L, haL, hLb, fun x h1 h2 => by rw [hfL]; exact hM1 _ ⟨x, h1, h2, rfl⟩⟩

/-! ## `n`-th roots -/

/-- Defining equation of powers. -/
theorem pow_succ' (x : R) (n : Nat) : x ^ (n + 1) = x ^ n * x := rfl

/-- Powers of a number `≥ 1` are `≥ 1`. -/
theorem one_le_pow {x : R} (hx : 1 ≤ x) (n : Nat) : 1 ≤ x ^ n := by
  induction n with
  | zero => show (1 : R) ≤ 1; grind
  | succ n ih =>
    rw [pow_succ']
    have := OrderedRing.mul_le_mul_of_nonneg_left hx (by grind : (0 : R) ≤ x ^ n)
    grind

/-- **Existence of `n`-th roots.** Every non-negative real `x` has a non-negative `n`-th root
for each `n ≥ 1`. -/
theorem exists_nth_root {x : R} (hx : 0 ≤ x) {n : Nat} (hn : 1 ≤ n) :
    ∃ r, 0 ≤ r ∧ r ^ n = x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 : (0 : R) ^ (m + 1) = 0 := by rw [pow_succ']; grind
  have h1 : x + 1 ≤ (x + 1) ^ (m + 1) := by
    rw [pow_succ']
    have := one_le_pow (by grind : (1 : R) ≤ x + 1) m
    have := OrderedRing.mul_le_mul_of_nonneg_right this (by grind : (0 : R) ≤ x + 1)
    grind
  obtain ⟨c, hc1, hc2, hc3⟩ := intermediate_value' (f := fun y => y ^ (m + 1)) (a := 0)
    (b := x + 1) (v := x) (by grind) (fun y _ _ => continuousAt_pow (m + 1) y)
    (by show (0 : R) ^ (m + 1) ≤ x; rw [h0]; exact hx) (by show x ≤ (x + 1) ^ (m + 1); grind)
  exact ⟨c, hc1, hc3⟩

end R

end Foundations.Numbers
