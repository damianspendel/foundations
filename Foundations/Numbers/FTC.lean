import Foundations.Numbers.Integral

/-!
# Analysis on the reals VII: the fundamental theorem of calculus

Differentiation (slopes of tangents) and integration (areas) look like unrelated problems; that
each undoes the other is the discovery of Newton and Leibniz which made the calculus a calculus.
With the definitions of the previous files both halves become theorems:

* **Part I** (Leibniz): if `f` is continuous on `[a, b]`, the area function
  `F x = ∫ₐˣ f` is differentiable inside `(a, b)` with `F' = f`. The proof uses only additivity of
  the integral and the estimate `|∫ₓʸ f − f x · (y − x)| ≤ ε |y − x|` when `f` stays within `ε` of
  `f x` on `[x, y]`.
* **Part II** (Newton): if `F' = f` on `[a, b]` and `f` is integrable, then `∫ₐᵇ f = F b − F a`.
  The proof is a pleasant application of the mean value theorem: given any tagged partition, move
  each tag to a mean value point `cᵢ` of its piece; the Riemann sum then telescopes to exactly
  `F b − F a`. No continuity of `f` is needed.

As illustrations we compute `∫ₐᵇ tⁿ dt = (bⁿ⁺¹ − aⁿ⁺¹)/(n + 1)` and `∫ₐᵇ exp = exp b − exp a`.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-! ## The integral as a number -/

/-- **The integral** `∫ₐᵇ f`: the Riemann integral of `f` over `[a, b]` if it exists. If it does
not exist — in particular whenever `b < a`, since `HasIntegral` requires `a ≤ b` — the value is
`0`, a value of no significance. -/
noncomputable def integral (f : R → R) (a b : R) : R :=
  open Classical in if h : ∃ I, HasIntegral f a b I then h.choose else 0

/-- If `f` has integral `I` over `[a, b]` (with `a ≤ b`), then `∫ₐᵇ f = I`. -/
theorem HasIntegral.integral_eq {f : R → R} {a b I : R} (hab : a ≤ b)
    (h : HasIntegral f a b I) : integral f a b = I := by
  have hex : ∃ I, HasIntegral f a b I := ⟨I, h⟩
  unfold integral
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec.unique hab h

/-- For continuous `f` on `[a, b]`, `∫ₐᵇ f` is its Riemann integral. -/
theorem hasIntegral_integral {f : R → R} {a b : R} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) : HasIntegral f a b (integral f a b) := by
  obtain ⟨I, hI⟩ := integrable_of_continuous hab hf
  rw [hI.integral_eq hab]; exact hI

/-- Additivity for continuous functions: `∫ₐᵛ f = ∫ₐᵘ f + ∫ᵤᵛ f` for `a ≤ u ≤ v`. -/
theorem integral_add_interval {f : R → R} {a u v : R} (hau : a ≤ u) (huv : u ≤ v)
    (hf : ∀ x, a ≤ x → x ≤ v → ContinuousAt f x) :
    integral f a v = integral f a u + integral f u v :=
  HasIntegral.add_interval hau huv
    (hasIntegral_integral hau fun x h1 h2 => hf x h1 (by grind))
    (hasIntegral_integral huv fun x h1 h2 => hf x (by grind) h2)
    (hasIntegral_integral (by grind) hf)

/-- **Estimate for integrals.** If `|f t − c| ≤ ε` on `[u, v]`, then `|∫ᵤᵛ f − c (v − u)| ≤
ε (v − u)`. -/
theorem HasIntegral.abs_sub_le {f : R → R} {u v c ε I : R} (huv : u ≤ v)
    (hI : HasIntegral f u v I) (hf : ∀ t, u ≤ t → t ≤ v → abs (f t - c) ≤ ε) :
    abs (I - c * (v - u)) ≤ ε * (v - u) := by
  apply Classical.byContradiction
  intro hlt
  obtain ⟨δ, hδ, h⟩ := hI.2 (abs (I - c * (v - u)) - ε * (v - u)) (by grind)
  obtain ⟨l, hl, hm⟩ := exists_tagged huv hδ
  have k1 := h l hl hm
  have k2 := abs_rsum_sub_le hl hf
  have k3 := abs_add (I - rsum f u l) (rsum f u l - c * (v - u))
  rw [show I - rsum f u l + (rsum f u l - c * (v - u)) = I - c * (v - u) by grind] at k3
  rw [abs_sub_comm] at k1
  grind

/-! ## The fundamental theorem, part I -/

/-- **Fundamental theorem of calculus, part I.** If `f` is continuous on `[a, b]`, then
`F x = ∫ₐˣ f` is differentiable at every interior point `x`, with derivative `f x`. -/
theorem ftc1 {f : R → R} {a b : R} (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) {x : R}
    (hax : a < x) (hxb : x < b) : HasDerivAt (fun y => integral f a y) (f x) x := fun ε hε => by
  obtain ⟨δ₀, hδ₀, h₀⟩ := hf x (Std.le_of_lt hax) (Std.le_of_lt hxb) ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := nhds_of_interior hax hxb
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_pos_le_both hδ₀ hδ₁
  refine ⟨δ, hδ, fun y hy => ?_⟩
  obtain ⟨hay, hyb⟩ := h₁ y (by grind)
  have hy' := abs_lt.1 hy
  -- `f` stays within `ε` of `f x` between `x` and `y`.
  have hclose : ∀ t, abs (t - x) ≤ abs (y - x) → abs (f t - f x) ≤ ε := fun t ht =>
    Std.le_of_lt (h₀ t (by grind))
  show abs (integral f a y - integral f a x - f x * (y - x)) ≤ ε * abs (y - x)
  rcases (by grind : x ≤ y ∨ y < x) with hxy | hxy
  · rw [integral_add_interval (Std.le_of_lt hax) hxy fun t h1 h2 => hf t h1 (by grind)]
    have hyx : abs (y - x) = y - x := abs_of_nonneg (by grind)
    have k := (hasIntegral_integral hxy fun t h1 h2 => hf t (by grind) (by grind)).abs_sub_le
      (c := f x) (ε := ε) hxy fun t h1 h2 => hclose t (by
        rw [hyx, abs_of_nonneg (by grind : (0 : R) ≤ t - x)]; grind)
    rw [hyx, show integral f a x + integral f x y - integral f a x - f x * (y - x) =
      integral f x y - f x * (y - x) by grind]
    exact k
  · rw [integral_add_interval (Std.le_of_lt hay) (Std.le_of_lt hxy)
      fun t h1 h2 => hf t h1 (by grind)]
    have hyx : abs (y - x) = x - y := by rw [abs_sub_comm]; exact abs_of_nonneg (by grind)
    have k := (hasIntegral_integral (Std.le_of_lt hxy)
      fun t h1 h2 => hf t (by grind) (by grind)).abs_sub_le
      (c := f x) (ε := ε) (Std.le_of_lt hxy) fun t h1 h2 => hclose t (by
        rw [hyx, abs_sub_comm, abs_of_nonneg (by grind : (0 : R) ≤ x - t)]; grind)
    rw [hyx, show integral f a y - (integral f a y + integral f y x) - f x * (y - x) =
      -(integral f y x - f x * (x - y)) by grind, abs_neg]
    exact k

/-! ## The fundamental theorem, part II -/

/-- On each piece `[a, x]` the increment of `F` is a value of `F'` times the length (mean value
theorem, also for degenerate pieces). -/
theorem exists_mvt_point {F f : R → R} {a x : R} (hax : a ≤ x)
    (hd : ∀ t, a ≤ t → t ≤ x → HasDerivAt F (f t) t) :
    ∃ c, a ≤ c ∧ c ≤ x ∧ F x - F a = f c * (x - a) := by
  rcases (by grind : a = x ∨ a < x) with h | h
  · subst h; exact ⟨a, Std.le_refl a, Std.le_refl a, by grind⟩
  · obtain ⟨c, h1, h2, h3⟩ := mean_value (f' := f) h
      (fun t h1 h2 => (hd t h1 h2).continuousAt) (fun t h1 h2 => hd t (by grind) (by grind))
    exact ⟨c, by grind, by grind, h3⟩

/-- Moving the tags of any tagged partition to mean value points makes the Riemann sum of `F'`
telescope to exactly `F b − F a`; the partition points (hence the mesh) are unchanged. -/
theorem exists_telescoping_tags {F f : R → R} {b : R} :
    ∀ (l : List (R × R)) (a : R), IsTagged a l b →
      (∀ t, a ≤ t → t ≤ b → HasDerivAt F (f t) t) →
      ∃ l', IsTagged a l' b ∧ (∀ δ, MeshLt δ a l → MeshLt δ a l') ∧ rsum f a l' = F b - F a := by
  intro l
  induction l with
  | nil =>
    intro a hl _
    have : a = b := hl; subst this
    exact ⟨[], rfl, fun _ _ => trivial, by show (0 : R) = F a - F a; grind⟩
  | cons p l ih =>
    intro a hl hd
    obtain ⟨t, x⟩ := p
    obtain ⟨h1, h2, h3⟩ := hl
    have hxb := h3.le
    obtain ⟨l'', k1, k2, k3⟩ := ih x h3 fun s hs1 hs2 => hd s (by grind) hs2
    obtain ⟨c, hc1, hc2, hc3⟩ := exists_mvt_point (F := F) (f := f) (Std.le_trans h1 h2)
      fun s hs1 hs2 => hd s hs1 (by grind)
    refine ⟨(c, x) :: l'', ⟨hc1, hc2, k1⟩, fun δ hm => ⟨hm.1, k2 δ hm.2⟩, ?_⟩
    show f c * (x - a) + rsum f x l'' = F b - F a
    rw [k3]; grind

/-- **Fundamental theorem of calculus, part II.** If `F' = f` on `[a, b]` and `f` has integral
`I` over `[a, b]`, then `I = F b − F a`. -/
theorem ftc2 {F f : R → R} {a b I : R} (hab : a ≤ b)
    (hd : ∀ t, a ≤ t → t ≤ b → HasDerivAt F (f t) t) (hI : HasIntegral f a b I) :
    I = F b - F a := by
  apply eq_of_abs_lt_all
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hI.2 ε hε
  obtain ⟨l, hl, hm⟩ := exists_tagged hab hδ
  obtain ⟨l', hl', hm', hsum⟩ := exists_telescoping_tags l a hl hd
  have := h l' hl' (hm' δ hm)
  rw [hsum, abs_sub_comm] at this
  exact this

/-- **Fundamental theorem of calculus, part II** (integral form). If `F' = f` on `[a, b]` with `f`
continuous, then `∫ₐᵇ f = F b − F a`. -/
theorem integral_eq_sub {F f : R → R} {a b : R} (hab : a ≤ b)
    (hd : ∀ t, a ≤ t → t ≤ b → HasDerivAt F (f t) t)
    (hf : ∀ t, a ≤ t → t ≤ b → ContinuousAt f t) : integral f a b = F b - F a :=
  ftc2 hab hd (hasIntegral_integral hab hf)

/-! ## Examples -/

/-- **Integral of a power.** `∫ₐᵇ tⁿ dt = (bⁿ⁺¹ − aⁿ⁺¹)/(n + 1)`. -/
theorem integral_pow (n : Nat) {a b : R} (hab : a ≤ b) :
    integral (fun t => t ^ n) a b = (b ^ (n + 1) - a ^ (n + 1)) / ((n : R) + 1) := by
  have hn : (0 : R) < (n : R) + 1 := by
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg; grind
  have hd : ∀ t, a ≤ t → t ≤ b →
      HasDerivAt (fun s => 1 / ((n : R) + 1) * s ^ (n + 1)) (t ^ n) t := fun t _ _ => by
    have := (hasDerivAt_pow n t).const_mul (1 / ((n : R) + 1))
    rw [show 1 / ((n : R) + 1) * (((n : R) + 1) * t ^ n) = t ^ n by grind] at this
    exact this
  rw [integral_eq_sub hab hd fun t _ _ => continuousAt_pow n t]
  grind

/-- **Integral of the exponential.** `∫ₐᵇ exp = exp b − exp a`. -/
theorem integral_exp {a b : R} (hab : a ≤ b) : integral exp a b = exp b - exp a :=
  integral_eq_sub hab (fun t _ _ => hasDerivAt_exp t)
    (fun t _ _ => (hasDerivAt_exp t).continuousAt)

end R

end Foundations.Numbers
