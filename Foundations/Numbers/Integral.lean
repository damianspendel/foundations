import Foundations.Numbers.Exp

/-!
# Analysis on the reals VI: the Riemann integral

The area under the graph of `f` between `a` and `b` is approximated by sums of rectangles. Cut
`[a, b]` into pieces `[x₀, x₁], [x₁, x₂], …, [xₙ₋₁, xₙ]` (with `x₀ = a`, `xₙ = b`), choose a
*tag* `tᵢ` in each piece, and form the **Riemann sum** `Σ f(tᵢ) (xᵢ₊₁ − xᵢ)`. Riemann (1854)
called `f` integrable with integral `I` if these sums approach `I` as the pieces get small,
however the tags are chosen:

  for every `ε > 0` there is `δ > 0` such that every tagged partition with all pieces shorter
  than `δ` has Riemann sum within `ε` of `I`.

We represent a tagged partition of `[a, b]` as a list of pairs `(tᵢ, xᵢ₊₁)` — tag and right end
point of each piece — starting from `a`. The main results of this file:

* the integral is **linear** and **monotone**, and **additive** over adjacent intervals;
* the **Heine–Cantor theorem**: a function continuous on `[a, b]` is *uniformly* continuous
  there (one `δ` serves for all points at once) — proved, like the extreme value theorem, with
  Bolzano–Weierstrass;
* **continuous functions are integrable**. The heart of the proof is a comparison lemma: for
  uniformly continuous `f`, the Riemann sums of any two sufficiently fine tagged partitions are
  close. We prove it by walking along both partitions at once, always cutting off the shorter of
  the two first pieces; this avoids the usual "common refinement" bookkeeping. The Riemann sums of
  the uniform partitions then form a Cauchy sequence, whose limit (completeness again!) is the
  integral.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace R

/-! ## Tagged partitions and Riemann sums -/

/-- `IsTagged a l b`: the list `l = [(t₁, x₁), …, (tₙ, xₙ)]` is a **tagged partition** of
`[a, b]`: the points `a = x₀ ≤ x₁ ≤ ⋯ ≤ xₙ = b` increase, and each tag lies in its piece,
`xᵢ₋₁ ≤ tᵢ ≤ xᵢ`. -/
def IsTagged : R → List (R × R) → R → Prop
  | a, [], b => a = b
  | a, (t, x) :: l, b => a ≤ t ∧ t ≤ x ∧ IsTagged x l b

/-- `MeshLt δ a l`: every piece of the partition `l` (starting at `a`) is shorter than `δ`. -/
def MeshLt (δ : R) : R → List (R × R) → Prop
  | _, [] => True
  | a, (_, x) :: l => x - a < δ ∧ MeshLt δ x l

/-- The **Riemann sum** `Σ f(tᵢ) (xᵢ − xᵢ₋₁)` of `f` over the tagged partition `l` starting
at `a`. -/
def rsum (f : R → R) : R → List (R × R) → R
  | _, [] => 0
  | a, (t, x) :: l => f t * (x - a) + rsum f x l

/-- `f` has **Riemann integral** `I` over `[a, b]` (where `a ≤ b`): Riemann sums over all
sufficiently fine tagged partitions are close to `I`. The condition `a ≤ b` is part of the
definition: for `b < a` there are no tagged partitions at all, and the approximation condition
alone would hold vacuously for every `I`. -/
def HasIntegral (f : R → R) (a b I : R) : Prop :=
  a ≤ b ∧ ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧
    ∀ l, IsTagged a l b → MeshLt δ a l → abs (rsum f a l - I) < ε

/-- An integral over `[a, b]` only exists for `a ≤ b`. -/
theorem HasIntegral.le {f : R → R} {a b I : R} (h : HasIntegral f a b I) : a ≤ b := h.1

/-- The partition points increase: a tagged partition of `[a, b]` has `a ≤ b`. -/
theorem IsTagged.le {a b : R} {l : List (R × R)} (h : IsTagged a l b) : a ≤ b := by
  induction l generalizing a with
  | nil => have : a = b := h; grind
  | cons p l ih => obtain ⟨t, x⟩ := p; obtain ⟨h1, h2, h3⟩ := h; have := ih h3; grind

/-- Concatenating tagged partitions of `[a, b]` and `[b, c]` gives one of `[a, c]`. -/
theorem IsTagged.append {a b c : R} {l₁ l₂ : List (R × R)} (h₁ : IsTagged a l₁ b)
    (h₂ : IsTagged b l₂ c) : IsTagged a (l₁ ++ l₂) c := by
  induction l₁ generalizing a with
  | nil => have : a = b := h₁; subst this; exact h₂
  | cons p l ih => obtain ⟨t, x⟩ := p; obtain ⟨k1, k2, k3⟩ := h₁; exact ⟨k1, k2, ih k3⟩

/-- Concatenation preserves the mesh bound. -/
theorem MeshLt.append {δ a b : R} {l₁ l₂ : List (R × R)} (h₁ : IsTagged a l₁ b)
    (m₁ : MeshLt δ a l₁) (m₂ : MeshLt δ b l₂) : MeshLt δ a (l₁ ++ l₂) := by
  induction l₁ generalizing a with
  | nil => have : a = b := h₁; subst this; exact m₂
  | cons p l ih => obtain ⟨t, x⟩ := p; exact ⟨m₁.1, ih h₁.2.2 m₁.2⟩

/-- Riemann sums over a concatenation add. -/
theorem rsum_append (f : R → R) {a b : R} {l₁ : List (R × R)} (l₂ : List (R × R))
    (h₁ : IsTagged a l₁ b) : rsum f a (l₁ ++ l₂) = rsum f a l₁ + rsum f b l₂ := by
  induction l₁ generalizing a with
  | nil => have : a = b := h₁; subst this; show rsum f a l₂ = 0 + rsum f a l₂; grind
  | cons p l ih =>
    obtain ⟨t, x⟩ := p
    show f t * (x - a) + rsum f x (l ++ l₂) = f t * (x - a) + rsum f x l + rsum f b l₂
    rw [ih h₁.2.2]; grind

/-- Riemann sums are additive in the function. -/
theorem rsum_add (f g : R → R) (a : R) (l : List (R × R)) :
    rsum (fun y => f y + g y) a l = rsum f a l + rsum g a l := by
  induction l generalizing a with
  | nil => show (0 : R) = 0 + 0; grind
  | cons p l ih =>
    obtain ⟨t, x⟩ := p
    show (f t + g t) * (x - a) + rsum (fun y => f y + g y) x l =
      f t * (x - a) + rsum f x l + (g t * (x - a) + rsum g x l)
    rw [ih]; grind

/-- Riemann sums commute with constant multiples. -/
theorem rsum_const_mul (c : R) (f : R → R) (a : R) (l : List (R × R)) :
    rsum (fun y => c * f y) a l = c * rsum f a l := by
  induction l generalizing a with
  | nil => show (0 : R) = c * 0; grind
  | cons p l ih =>
    obtain ⟨t, x⟩ := p
    show c * f t * (x - a) + rsum (fun y => c * f y) x l = c * (f t * (x - a) + rsum f x l)
    rw [ih]; grind

/-- An estimate for Riemann sums: if `|f t − c| ≤ ε` on `[a, b]`, every Riemann sum over a
tagged partition of `[a, b]` is within `ε (b − a)` of `c (b − a)`. -/
theorem abs_rsum_sub_le {f : R → R} {a b c ε : R} {l : List (R × R)} (hl : IsTagged a l b)
    (hf : ∀ t, a ≤ t → t ≤ b → abs (f t - c) ≤ ε) :
    abs (rsum f a l - c * (b - a)) ≤ ε * (b - a) := by
  induction l generalizing a with
  | nil =>
    have : a = b := hl; subst this
    show abs (0 - c * (a - a)) ≤ ε * (a - a)
    rw [show (0 : R) - c * (a - a) = 0 by grind, abs_zero]; grind
  | cons p l ih =>
    obtain ⟨t, x⟩ := p
    obtain ⟨h1, h2, h3⟩ := hl
    have hxb := h3.le
    have k1 := ih h3 fun s hs1 hs2 => hf s (by grind) hs2
    have k2 := hf t h1 (by grind)
    show abs (f t * (x - a) + rsum f x l - c * (b - a)) ≤ ε * (b - a)
    have k3 : abs ((f t - c) * (x - a)) ≤ ε * (x - a) := by
      rw [abs_mul, abs_of_nonneg (by grind : (0 : R) ≤ x - a)]
      exact OrderedRing.mul_le_mul_of_nonneg_right k2 (by grind)
    have k4 := abs_add ((f t - c) * (x - a)) (rsum f x l - c * (b - x))
    rw [show (f t - c) * (x - a) + (rsum f x l - c * (b - x)) =
      f t * (x - a) + rsum f x l - c * (b - a) by grind] at k4
    grind

/-- Riemann sums are monotone in the function (for genuine tagged partitions). -/
theorem rsum_le_rsum {f g : R → R} {a b : R} {l : List (R × R)} (hl : IsTagged a l b)
    (hfg : ∀ t, a ≤ t → t ≤ b → f t ≤ g t) : rsum f a l ≤ rsum g a l := by
  induction l generalizing a with
  | nil => show (0 : R) ≤ 0; grind
  | cons p l ih =>
    obtain ⟨t, x⟩ := p
    obtain ⟨h1, h2, h3⟩ := hl
    have hxb := h3.le
    have k1 := ih h3 fun s hs1 hs2 => hfg s (by grind) hs2
    have k2 := OrderedRing.mul_le_mul_of_nonneg_right (hfg t h1 (by grind)) (by grind : (0 : R) ≤ x - a)
    show f t * (x - a) + rsum f x l ≤ g t * (x - a) + rsum g x l
    grind

/-! ## Fine partitions exist -/

/-- The **uniform partition** of `[a, a + n h]` into `n` pieces of length `h`, tagged at the left
end points. -/
def unif (a h : R) : Nat → List (R × R)
  | 0 => []
  | n + 1 => (a, a + h) :: unif (a + h) h n

/-- The uniform partition is a tagged partition of `[a, a + n h]`. -/
theorem unif_isTagged {h : R} (hh : 0 ≤ h) (n : Nat) (a : R) :
    IsTagged a (unif a h n) (a + (n : R) * h) := by
  induction n generalizing a with
  | zero => show a = a + ((0 : Nat) : R) * h; grind
  | succ n ih =>
    refine ⟨Std.le_refl a, by grind, ?_⟩
    have := ih (a + h)
    rw [show a + h + (n : R) * h = a + ((n + 1 : Nat) : R) * h by grind] at this
    exact this

/-- The pieces of the uniform partition have length `h`. -/
theorem unif_meshLt {h δ : R} (hh : h < δ) (n : Nat) (a : R) : MeshLt δ a (unif a h n) := by
  induction n generalizing a with
  | zero => trivial
  | succ n ih => exact ⟨by grind, ih (a + h)⟩

/-- For `c ≥ 0` and `δ > 0`, eventually `c / (n + 1) < δ`. -/
theorem exists_div_lt {c δ : R} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∃ N : Nat, ∀ n, N ≤ n → c / ((n : R) + 1) < δ := by
  obtain ⟨N, hN⟩ := eps_small (div_pos hδ (by grind : 0 < c + 1))
  refine ⟨N, fun n hn => ?_⟩
  have k := hN n hn
  have hpos := eps_pos n
  have e1 : c / ((n : R) + 1) = c * (1 / ((n : R) + 1)) := by
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg; grind
  have k1 := OrderedRing.mul_le_mul_of_nonneg_right (by grind : c ≤ c + 1) (Std.le_of_lt hpos)
  have k2 := OrderedRing.mul_lt_mul_of_pos_left k (by grind : 0 < c + 1)
  have e2 : (c + 1) * (δ / (c + 1)) = δ := by grind
  grind

/-- Writing `b = a + (n+1) · ((b − a)/(n+1))`. -/
theorem unif_end (a b : R) (n : Nat) :
    a + ((n + 1 : Nat) : R) * ((b - a) / ((n : R) + 1)) = b := by
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  grind

/-- **Fine tagged partitions exist**: for `a ≤ b` and `δ > 0` there is a tagged partition of
`[a, b]` with all pieces shorter than `δ`. -/
theorem exists_tagged {a b δ : R} (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ l, IsTagged a l b ∧ MeshLt δ a l := by
  obtain ⟨N, hN⟩ := exists_div_lt (by grind : (0 : R) ≤ b - a) hδ
  have hh : (0 : R) ≤ (b - a) / ((N : R) + 1) := by
    have : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg
    rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg (by grind) (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 (by grind)))
  have := unif_isTagged hh (N + 1) a
  rw [unif_end] at this
  exact ⟨_, this, unif_meshLt (hN N (Nat.le_refl N)) _ a⟩

/-- A real number smaller in absolute value than every positive number is zero. -/
theorem eq_of_abs_lt_all {x y : R} (h : ∀ ε : R, 0 < ε → abs (x - y) < ε) : x = y := by
  apply Classical.byContradiction
  intro hne
  have hpos : 0 < abs (x - y) := by rcases abs_cases (x - y) with h | h <;> grind
  have := h _ hpos
  grind

/-- Mesh bounds can be weakened. -/
theorem MeshLt.mono {δ δ' a : R} {l : List (R × R)} (hle : δ ≤ δ') (hm : MeshLt δ a l) :
    MeshLt δ' a l := by
  induction l generalizing a with
  | nil => trivial
  | cons p l ih => obtain ⟨t, x⟩ := p; exact ⟨by have := hm.1; grind, ih hm.2⟩

/-- **Uniqueness of the integral** (for `a ≤ b`). -/
theorem HasIntegral.unique {f : R → R} {a b I J : R} (hab : a ≤ b) (hI : HasIntegral f a b I)
    (hJ : HasIntegral f a b J) : I = J := by
  apply eq_of_abs_lt_all
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hI.2 (ε / 2) (by grind)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hJ.2 (ε / 2) (by grind)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₁ hδ₂
  obtain ⟨l, hl, hm⟩ := exists_tagged hab hδ
  have k1 := h₁ l hl (hm.mono hδ1)
  have k2 := h₂ l hl (hm.mono hδ2)
  rw [abs_sub_comm] at k1
  have k3 := abs_add (I - rsum f a l) (rsum f a l - J)
  rw [show I - rsum f a l + (rsum f a l - J) = I - J by grind] at k3
  grind

/-! ## Linearity, monotonicity, additivity -/

/-- **Linearity I.** `∫ (f + g) = ∫ f + ∫ g`. -/
theorem HasIntegral.add {f g : R → R} {a b I J : R} (hf : HasIntegral f a b I)
    (hg : HasIntegral g a b J) : HasIntegral (fun y => f y + g y) a b (I + J) := ⟨hf.1, fun ε hε => by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf.2 (ε / 2) (by grind)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg.2 (ε / 2) (by grind)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₁ hδ₂
  refine ⟨δ, hδ, fun l hl hm => ?_⟩
  have k1 := h₁ l hl (hm.mono hδ1)
  have k2 := h₂ l hl (hm.mono hδ2)
  rw [rsum_add]
  have k3 := abs_add (rsum f a l - I) (rsum g a l - J)
  rw [show rsum f a l - I + (rsum g a l - J) = rsum f a l + rsum g a l - (I + J) by grind] at k3
  grind⟩

/-- **Linearity II.** `∫ c f = c ∫ f`. -/
theorem HasIntegral.const_mul (c : R) {f : R → R} {a b I : R} (hf : HasIntegral f a b I) :
    HasIntegral (fun y => c * f y) a b (c * I) := ⟨hf.1, fun ε hε => by
  obtain ⟨η, hη, hηc⟩ := exists_mul_le c (by grind : 0 < ε / 2)
  obtain ⟨δ, hδ, h⟩ := hf.2 η hη
  refine ⟨δ, hδ, fun l hl hm => ?_⟩
  rw [rsum_const_mul, show c * rsum f a l - c * I = c * (rsum f a l - I) by grind, abs_mul]
  have := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt (h l hl hm)) (abs_nonneg c)
  grind⟩

/-- The integral of a constant: `∫ₐᵇ c = c (b − a)`. -/
theorem hasIntegral_const (c : R) {a b : R} (hab : a ≤ b) :
    HasIntegral (fun _ => c) a b (c * (b - a)) :=
  ⟨hab, fun ε hε => ⟨1, by grind, fun l hl _ => by
    have := abs_rsum_sub_le (f := fun _ => c) (c := c) (ε := 0) hl fun t _ _ => by
      rw [show c - c = 0 by grind, abs_zero]; exact Std.le_refl _
    grind⟩⟩

/-- **Monotonicity of the integral.** If `f ≤ g` on `[a, b]` then `∫ f ≤ ∫ g`. -/
theorem HasIntegral.mono {f g : R → R} {a b I J : R} (hab : a ≤ b) (hf : HasIntegral f a b I)
    (hg : HasIntegral g a b J) (hfg : ∀ t, a ≤ t → t ≤ b → f t ≤ g t) : I ≤ J := by
  apply Classical.byContradiction
  intro hlt
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf.2 ((I - J) / 2) (by grind)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg.2 ((I - J) / 2) (by grind)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₁ hδ₂
  obtain ⟨l, hl, hm⟩ := exists_tagged hab hδ
  have k1 := abs_lt.1 (h₁ l hl (hm.mono hδ1))
  have k2 := abs_lt.1 (h₂ l hl (hm.mono hδ2))
  have := rsum_le_rsum hl hfg
  grind

/-- **Additivity over intervals.** `∫ₐᶜ f = ∫ₐᵇ f + ∫ᵇᶜ f` (when all three integrals exist and
`a ≤ b ≤ c`). -/
theorem HasIntegral.add_interval {f : R → R} {a b c I J K : R} (hab : a ≤ b) (hbc : b ≤ c)
    (hI : HasIntegral f a b I) (hJ : HasIntegral f b c J) (hK : HasIntegral f a c K) :
    K = I + J := by
  apply eq_of_abs_lt_all
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hI.2 (ε / 3) (by grind)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hJ.2 (ε / 3) (by grind)
  obtain ⟨δ₃, hδ₃, h₃⟩ := hK.2 (ε / 3) (by grind)
  obtain ⟨δ₄, hδ₄, h₄1, h₄2⟩ := exists_pos_le_both hδ₁ hδ₂
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both hδ₄ hδ₃
  obtain ⟨l₁, hl₁, hm₁⟩ := exists_tagged hab hδ
  obtain ⟨l₂, hl₂, hm₂⟩ := exists_tagged hbc hδ
  have k1 := abs_lt.1 (h₁ l₁ hl₁ (hm₁.mono (by grind)))
  have k2 := abs_lt.1 (h₂ l₂ hl₂ (hm₂.mono (by grind)))
  have k3 := abs_lt.1 (h₃ (l₁ ++ l₂) (hl₁.append hl₂) ((MeshLt.append hl₁ hm₁ hm₂).mono hδ2))
  rw [rsum_append f l₂ hl₁] at k3
  exact abs_lt.2 ⟨by grind, by grind⟩

/-! ## Uniform continuity -/

/-- **Heine–Cantor theorem.** A function continuous at every point of `[a, b]` is *uniformly*
continuous on `[a, b]`: for every `ε > 0` one `δ > 0` works for all pairs of points. -/
theorem uniform_continuous {f : R → R} {a b : R} (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x)
    {ε : R} (hε : 0 < ε) : ∃ δ : R, 0 < δ ∧ ∀ s t, a ≤ s → s ≤ b → a ≤ t → t ≤ b →
      abs (s - t) < δ → abs (f s - f t) < ε := by
  apply Classical.byContradiction
  intro hno
  -- Otherwise there are pairs `sₙ, tₙ` with `|sₙ − tₙ| < 1/(n+1)` but `|f sₙ − f tₙ| ≥ ε`.
  have hx : ∀ n : Nat, ∃ p : R × R, (a ≤ p.1 ∧ p.1 ≤ b) ∧ (a ≤ p.2 ∧ p.2 ≤ b) ∧
      abs (p.1 - p.2) < 1 / ((n : R) + 1) ∧ ε ≤ abs (f p.1 - f p.2) := fun n => by
    apply Classical.byContradiction; intro h
    exact hno ⟨1 / ((n : R) + 1), eps_pos n, fun s t h1 h2 h3 h4 h5 => by
      apply Classical.byContradiction; intro h6
      exact h ⟨(s, t), ⟨h1, h2⟩, ⟨h3, h4⟩, h5, by grind⟩⟩
  let p : Nat → R × R := fun n => (hx n).choose
  have hp : ∀ n, (a ≤ (p n).1 ∧ (p n).1 ≤ b) ∧ (a ≤ (p n).2 ∧ (p n).2 ≤ b) ∧
      abs ((p n).1 - (p n).2) < 1 / ((n : R) + 1) ∧ ε ≤ abs (f (p n).1 - f (p n).2) :=
    fun n => (hx n).choose_spec
  obtain ⟨φ, hφ, L, hL⟩ := bolzano_weierstrass (a := fun n => (p n).1)
    (bounded_of_mem fun n => (hp n).1)
  have haL : a ≤ L := le_of_tendsto hL fun k => (hp (φ k)).1.1
  have hLb : L ≤ b := tendsto_le hL fun k => (hp (φ k)).1.2
  -- The partners `t_{φ k}` converge to the same limit.
  have hL' : Tendsto (fun k => (p (φ k)).2) L := fun η hη => by
    obtain ⟨K, hK⟩ := hL (η / 2) (by grind)
    obtain ⟨N, hN⟩ := eps_small (by grind : (0 : R) < η / 2)
    refine ⟨max K N, fun k hk => ?_⟩
    have k1 := hK k (by omega)
    have k2 := (hp (φ k)).2.2.1
    have k3 := hN (φ k) (by have := le_of_strictMono hφ k; omega)
    have k4 := abs_add ((p (φ k)).2 - (p (φ k)).1) ((p (φ k)).1 - L)
    rw [show (p (φ k)).2 - (p (φ k)).1 + ((p (φ k)).1 - L) = (p (φ k)).2 - L by grind] at k4
    rw [abs_sub_comm] at k2
    show abs ((p (φ k)).2 - L) < η
    have k5 : abs ((p (φ k)).1 - L) < η / 2 := k1
    generalize abs ((p (φ k)).2 - L) = A at k4 ⊢
    generalize abs ((p (φ k)).2 - (p (φ k)).1) = B at k2 k4
    generalize abs ((p (φ k)).1 - L) = C at k4 k5
    grind
  have h1 := tendsto_comp (hf L haL hLb) hL
  have h2 := tendsto_comp (hf L haL hLb) hL'
  obtain ⟨K, hK⟩ := (h1.sub h2) ε hε
  have k1 := hK K (Nat.le_refl K)
  have k2 := (hp (φ K)).2.2.2
  simp only at k1
  rw [show f (p (φ K)).1 - f (p (φ K)).2 - (f L - f L) = f (p (φ K)).1 - f (p (φ K)).2 by grind]
    at k1
  grind

/-! ## Continuous functions are integrable -/

/-- `Fine A B δ a l b`: a loosened notion of `δ`-fine tagged partition of `[a, b]`, used only in
the proof below. The tags lie in `[A, B]` and each piece `[xᵢ₋₁, xᵢ]` lies within `δ` of its
tag `tᵢ` (but the tag need not lie in the piece). Shrinking a piece keeps it fine. -/
def Fine (A B δ : R) : R → List (R × R) → R → Prop
  | a, [], b => a = b
  | a, (t, x) :: l, b => a ≤ x ∧ A ≤ t ∧ t ≤ B ∧ t - δ < a ∧ x < t + δ ∧ Fine A B δ x l b

/-- Genuine tagged partitions of mesh `< δ` inside `[A, B]` are fine. -/
theorem fine_of_isTagged {A B δ a b : R} {l : List (R × R)} (hA : A ≤ a) (hB : b ≤ B)
    (hl : IsTagged a l b) (hm : MeshLt δ a l) : Fine A B δ a l b := by
  induction l generalizing a with
  | nil => exact hl
  | cons p l ih =>
    obtain ⟨t, x⟩ := p
    obtain ⟨h1, h2, h3⟩ := hl
    have := h3.le
    have := hm.1
    exact ⟨by grind, by grind, by grind, by grind, by grind, ih (by grind) h3 hm.2⟩

/-- Fine partitions go from left to right. -/
theorem Fine.le {A B δ a b : R} {l : List (R × R)} (h : Fine A B δ a l b) : a ≤ b := by
  induction l generalizing a with
  | nil => have : a = b := h; grind
  | cons p l ih => obtain ⟨t, x⟩ := p; have := ih h.2.2.2.2.2; have := h.1; grind

/-- A fine partition of a one-point interval has Riemann sum `0`. -/
theorem rsum_fine_self (f : R → R) {A B δ a : R} {l : List (R × R)} (h : Fine A B δ a l a) :
    rsum f a l = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨t, x⟩ := p
    obtain ⟨h1, -, -, -, -, h6⟩ := h
    have := h6.le
    have hx : x = a := by grind
    subst hx
    show f t * (x - x) + rsum f x l = 0
    rw [ih h6]; grind

/-- **Comparison lemma.** If `|f s − f s'| ≤ ε` whenever `s, s' ∈ [A, B]` are within `2δ`, then
the Riemann sums over any two `δ`-fine partitions of `[a, b]` differ by at most `ε (b − a)`.
Proof: walk along both partitions simultaneously, each time cutting off the shorter of the two
first pieces. -/
theorem abs_rsum_sub_rsum_le {f : R → R} {A B δ ε : R}
    (hf : ∀ s s', A ≤ s → s ≤ B → A ≤ s' → s' ≤ B → abs (s - s') < 2 * δ →
      abs (f s - f s') ≤ ε) :
    ∀ n : Nat, ∀ (a b : R) (P Q : List (R × R)), P.length + Q.length ≤ n →
      Fine A B δ a P b → Fine A B δ a Q b → abs (rsum f a P - rsum f a Q) ≤ ε * (b - a) := by
  intro n
  induction n with
  | zero =>
    intro a b P Q hlen hP hQ
    cases P with
    | cons _ _ => simp at hlen
    | nil =>
      cases Q with
      | cons _ _ => simp at hlen
      | nil =>
        have : a = b := hP; subst this
        show abs ((0 : R) - 0) ≤ ε * (a - a); rw [show (0 : R) - 0 = 0 by grind, abs_zero]; grind
  | succ n ih =>
    intro a b P Q hlen hP hQ
    match P, Q, hlen with
    | [], Q, _ =>
      have : a = b := hP; subst this
      rw [rsum_fine_self f hQ]
      show abs ((0 : R) - 0) ≤ ε * (a - a); rw [show (0 : R) - 0 = 0 by grind, abs_zero]; grind
    | (s, p) :: P', [], _ =>
      have : a = b := hQ; subst this
      rw [rsum_fine_self f hP]
      show abs ((0 : R) - 0) ≤ ε * (a - a); rw [show (0 : R) - 0 = 0 by grind, abs_zero]; grind
    | (s, p) :: P', (t, q) :: Q', hlen =>
      obtain ⟨hap, hsA, hsB, hs1, hs2, hP'⟩ := hP
      obtain ⟨haq, htA, htB, ht1, ht2, hQ'⟩ := hQ
      have hst : abs (f s - f t) ≤ ε := hf s t hsA hsB htA htB (abs_lt.2 ⟨by grind, by grind⟩)
      have hlen' : P'.length + Q'.length + 2 ≤ n + 1 := by simp at hlen; omega
      rcases (by grind : p ≤ q ∨ q ≤ p) with hpq | hqp
      · -- Cut the second partition at `p`.
        have hQ'' : Fine A B δ p ((t, q) :: Q') b := ⟨hpq, htA, htB, by grind, ht2, hQ'⟩
        have k := ih p b P' ((t, q) :: Q') (by simp; omega) hP' hQ''
        have hpb := hP'.le
        show abs (f s * (p - a) + rsum f p P' - (f t * (q - a) + rsum f q Q')) ≤ ε * (b - a)
        have e : rsum f p ((t, q) :: Q') = f t * (q - p) + rsum f q Q' := rfl
        rw [e] at k
        have k2 : abs ((f s - f t) * (p - a)) ≤ ε * (p - a) := by
          rw [abs_mul, abs_of_nonneg (by grind : (0 : R) ≤ p - a)]
          exact OrderedRing.mul_le_mul_of_nonneg_right hst (by grind)
        have k3 := abs_add ((f s - f t) * (p - a)) (rsum f p P' - (f t * (q - p) + rsum f q Q'))
        rw [show (f s - f t) * (p - a) + (rsum f p P' - (f t * (q - p) + rsum f q Q')) =
          f s * (p - a) + rsum f p P' - (f t * (q - a) + rsum f q Q') by grind] at k3
        grind
      · -- Cut the first partition at `q`.
        have hP'' : Fine A B δ q ((s, p) :: P') b := ⟨hqp, hsA, hsB, by grind, hs2, hP'⟩
        have k := ih q b ((s, p) :: P') Q' (by simp; omega) hP'' hQ'
        have hqb := hQ'.le
        show abs (f s * (p - a) + rsum f p P' - (f t * (q - a) + rsum f q Q')) ≤ ε * (b - a)
        have e : rsum f q ((s, p) :: P') = f s * (p - q) + rsum f p P' := rfl
        rw [e] at k
        have k2 : abs ((f s - f t) * (q - a)) ≤ ε * (q - a) := by
          rw [abs_mul, abs_of_nonneg (by grind : (0 : R) ≤ q - a)]
          exact OrderedRing.mul_le_mul_of_nonneg_right hst (by grind)
        have k3 := abs_add ((f s - f t) * (q - a)) (f s * (p - q) + rsum f p P' - rsum f q Q')
        rw [show (f s - f t) * (q - a) + (f s * (p - q) + rsum f p P' - rsum f q Q') =
          f s * (p - a) + rsum f p P' - (f t * (q - a) + rsum f q Q') by grind] at k3
        grind

/-- **Continuous functions are integrable.** A function continuous at every point of `[a, b]`
has a Riemann integral over `[a, b]`. -/
theorem integrable_of_continuous {f : R → R} {a b : R} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) : ∃ I, HasIntegral f a b I := by
  -- Uniform continuity, packaged for the comparison lemma.
  have huc : ∀ η : R, 0 < η → ∃ δ : R, 0 < δ ∧ ∀ (P Q : List (R × R)),
      IsTagged a P b → MeshLt δ a P → IsTagged a Q b → MeshLt δ a Q →
      abs (rsum f a P - rsum f a Q) ≤ η := fun η hη => by
    obtain ⟨δ, hδ, hδf⟩ := uniform_continuous hf (div_pos hη (by grind : 0 < b - a + 1))
    refine ⟨δ / 2, by grind, fun P Q hP hmP hQ hmQ => ?_⟩
    have k := abs_rsum_sub_rsum_le (f := f) (A := a) (B := b) (δ := δ / 2)
      (fun s s' h1 h2 h3 h4 h5 => Std.le_of_lt (hδf s s' h1 h2 h3 h4 (by grind)))
      _ a b P Q (Nat.le_refl _) (fine_of_isTagged (Std.le_refl a) (Std.le_refl b) hP hmP)
      (fine_of_isTagged (Std.le_refl a) (Std.le_refl b) hQ hmQ)
    have := OrderedRing.mul_le_mul_of_nonneg_left (by grind : b - a ≤ b - a + 1)
      (Std.le_of_lt (div_pos hη (by grind : 0 < b - a + 1)))
    have e : η / (b - a + 1) * (b - a + 1) = η := by grind
    grind
  -- The Riemann sums of the uniform partitions form a Cauchy sequence.
  let h : Nat → R := fun n => (b - a) / ((n : R) + 1)
  have hh : ∀ n, 0 ≤ h n := fun n => by
    have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
    show 0 ≤ (b - a) / ((n : R) + 1)
    rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg (by grind) (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 (by grind)))
  let P : Nat → List (R × R) := fun n => unif a (h n) (n + 1)
  have hP : ∀ n, IsTagged a (P n) b := fun n => by
    have := unif_isTagged (hh n) (n + 1) a; rw [unif_end] at this; exact this
  let S : Nat → R := fun n => rsum f a (P n)
  have hfine : ∀ δ : R, 0 < δ → ∃ N, ∀ n, N ≤ n → MeshLt δ a (P n) := fun δ hδ => by
    obtain ⟨N, hN⟩ := exists_div_lt (by grind : (0 : R) ≤ b - a) hδ
    exact ⟨N, fun n hn => unif_meshLt (hN n hn) _ a⟩
  have hS : IsCauchySeq S := fun ε hε => by
    obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (by grind)
    obtain ⟨N, hN⟩ := hfine δ hδ
    exact ⟨N, fun m n hm hn => by
      have := hδ' (P m) (P n) (hP m) (hN m hm) (hP n) (hN n hn); grind⟩
  obtain ⟨I, hI⟩ := cauchy_complete hS
  -- Its limit is the integral.
  refine ⟨I, hab, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (by grind)
  refine ⟨δ, hδ, fun l hl hm => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hfine δ hδ
  obtain ⟨N₂, hN₂⟩ := hI (ε / 2) (by grind)
  have k1 := hδ' l (P (max N₁ N₂)) hl hm (hP _) (hN₁ _ (by omega))
  have k2 := hN₂ (max N₁ N₂) (by omega)
  have k3 := abs_add (rsum f a l - S (max N₁ N₂)) (S (max N₁ N₂) - I)
  rw [show rsum f a l - S (max N₁ N₂) + (S (max N₁ N₂) - I) = rsum f a l - I by grind] at k3
  grind

end R

end Foundations.Numbers
