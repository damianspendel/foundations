import Foundations.Topology.LebesgueMeasure

/-!
# Simple functions and the integral of non-negative functions

Riemann (1854) cuts the *domain* `[a, b]` into small intervals; Lebesgue (1902, and in his 1901
note *Sur une généralisation de l'intégrale définie*) cuts the *range*. His own image: to count a
heap of coins, Riemann takes them in the order they come, Lebesgue first sorts them by value and
multiplies each value by the size of its pile. The "piles" are sets `{x | yᵢ ≤ f(x) < yᵢ₊₁}`,
which can be very irregular — and the theory of measure is exactly what is needed to give them a
size.

A **simple function** is a finite combination `Σ aᵢ · 1_{Aᵢ}` of indicator functions of
measurable sets. We represent one by the list of pairs `(aᵢ, Aᵢ)`, with the `Aᵢ` pairwise
disjoint and `aᵢ ≥ 0`; it lies **below** `f` if `aᵢ ≤ f` on `Aᵢ`. Its integral is
`Σ aᵢ μ(Aᵢ)`. The **Lebesgue integral** of a non-negative measurable `f` is the supremum of the
integrals of the simple functions below it:

  `∫ f dμ = sup { Σ aᵢ μ(Aᵢ) | Σ aᵢ 1_{Aᵢ} ≤ f }`.

Defining the integral as a supremum *over representations* sidesteps the usual chore of proving
that the integral of a simple function does not depend on how it is written. Everything we need
comes from one device, **common refinement**: two disjoint families can be intersected piece by
piece, and finite additivity of `μ` shows that the sums do not change.

Our measures are finite and our functions real-valued, so the supremum may be infinite; we
call `f` **integrable** when it is finite, and only then use `∫ f dμ`.

Main results: monotonicity, `∫ c = c μ(α)`, `∫ c f = c ∫ f`, and **additivity**
`∫ (f + g) = ∫ f + ∫ g` — the inequality `≥` by refinement, the inequality `≤` by cutting the
range of `f` into levels of width `δ`, exactly as in Lebesgue's coin-counting picture.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace MeasureTheory

/-! ## Finite sums over lists -/

/-- The sum `Σ_{b ∈ l} F b` over a list. -/
def lsum {β : Type} (F : β → R) : List β → R
  | [] => 0
  | b :: l => F b + lsum F l

section lsum

variable {β γ : Type}

/-- Sum over a concatenation. -/
theorem lsum_append (F : β → R) (l₁ l₂ : List β) : lsum F (l₁ ++ l₂) = lsum F l₁ + lsum F l₂ := by
  induction l₁ with
  | nil => show lsum F l₂ = 0 + _; grind
  | cons b l ih => show F b + lsum F (l ++ l₂) = F b + lsum F l + _; rw [ih]; grind

/-- Sums are additive. -/
theorem lsum_add (F G : β → R) (l : List β) :
    lsum (fun b => F b + G b) l = lsum F l + lsum G l := by
  induction l with
  | nil => show (0 : R) = 0 + 0; grind
  | cons b l ih => show _ + lsum _ l = (F b + lsum F l) + (G b + lsum G l); rw [ih]; grind

/-- Constants factor out of sums. -/
theorem lsum_mul_left (c : R) (F : β → R) (l : List β) :
    lsum (fun b => c * F b) l = c * lsum F l := by
  induction l with
  | nil => show (0 : R) = c * 0; grind
  | cons b l ih => show _ + lsum _ l = c * (F b + lsum F l); rw [ih]; grind

/-- Sums respect pointwise equality on the list. -/
theorem lsum_congr {F G : β → R} {l : List β} (h : ∀ b ∈ l, F b = G b) : lsum F l = lsum G l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show F b + lsum F l = G b + lsum G l
    rw [h b (List.mem_cons_self), ih fun c hc => h c (List.mem_cons_of_mem _ hc)]

/-- Sums are monotone. -/
theorem lsum_le {F G : β → R} {l : List β} (h : ∀ b ∈ l, F b ≤ G b) : lsum F l ≤ lsum G l := by
  induction l with
  | nil => exact Std.le_refl _
  | cons b l ih =>
    show F b + lsum F l ≤ G b + lsum G l
    have := h b (List.mem_cons_self); have := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    grind

/-- A sum of zeros is zero. -/
theorem lsum_zero (l : List β) : lsum (fun _ => (0 : R)) l = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih => show 0 + lsum _ l = 0; rw [ih]; grind

/-- Sums of non-negative terms are non-negative. -/
theorem lsum_nonneg {F : β → R} {l : List β} (h : ∀ b ∈ l, 0 ≤ F b) : 0 ≤ lsum F l := by
  have := lsum_le (F := fun _ => 0) (G := F) h
  rw [lsum_zero] at this; exact this

/-- Sum over a `map`. -/
theorem lsum_map (F : γ → R) (g : β → γ) (l : List β) : lsum F (l.map g) = lsum (fun b => F (g b)) l := by
  induction l with
  | nil => rfl
  | cons b l ih => show F (g b) + lsum F (l.map g) = _; rw [ih]; rfl

/-- Sum over a `flatMap`. -/
theorem lsum_flatMap (F : γ → R) (g : β → List γ) (l : List β) :
    lsum F (l.flatMap g) = lsum (fun b => lsum F (g b)) l := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, lsum_append, ih]; rfl

/-- **Fubini for finite sums.** The order of a double sum can be swapped. -/
theorem lsum_swap (H : β → γ → R) (l₁ : List β) (l₂ : List γ) :
    lsum (fun a => lsum (fun b => H a b) l₂) l₁ = lsum (fun b => lsum (fun a => H a b) l₁) l₂ := by
  induction l₁ with
  | nil => exact (lsum_zero l₂).symm
  | cons a l ih =>
    show lsum (fun b => H a b) l₂ + lsum _ l = _
    rw [ih, ← lsum_add]; rfl

/-- Limits of finite sums are finite sums of limits. -/
theorem lsum_tendsto {F : Nat → β → R} {G : β → R} {l : List β}
    (h : ∀ b ∈ l, Tendsto (fun n => F n b) (G b)) :
    Tendsto (fun n => lsum (F n) l) (lsum G l) := by
  induction l with
  | nil => exact tendsto_const 0
  | cons b l ih => exact (h b List.mem_cons_self).add (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

end lsum

/-! ## Finite disjoint families of sets -/

section families

variable {α β : Type} {S : SigmaAlgebra α}

/-- The union of the sets `set b`, `b ∈ l`. -/
def UnionOf (set : β → α → Prop) (l : List β) (x : α) : Prop := ∃ b ∈ l, set b x

/-- The sets `set b`, `b ∈ l`, are pairwise disjoint. -/
def DisjOn (set : β → α → Prop) (l : List β) : Prop :=
  l.Pairwise (fun b b' => ∀ x, set b x → set b' x → False)

/-- Finite unions of measurable sets are measurable. -/
theorem measurable_unionOf {set : β → α → Prop} {l : List β} (h : ∀ b ∈ l, S.M (set b)) :
    S.M (UnionOf set l) := by
  induction l with
  | nil => exact S.congr S.empty fun x => ⟨False.elim, fun ⟨_, hb, _⟩ => by cases hb⟩
  | cons b l ih =>
    exact S.congr (S.union (h b List.mem_cons_self) (ih fun c hc => h c (List.mem_cons_of_mem _ hc)))
      fun x => ⟨fun hx => hx.elim (fun hx => ⟨b, List.mem_cons_self, hx⟩)
        (fun ⟨c, hc, hx⟩ => ⟨c, List.mem_cons_of_mem _ hc, hx⟩),
        fun ⟨c, hc, hx⟩ => by
          rcases List.mem_cons.1 hc with rfl | hc
          · exact Or.inl hx
          · exact Or.inr ⟨c, hc, hx⟩⟩

/-- **Finite additivity over a list.** `Σ_{b ∈ l} μ(A ∩ B_b) = μ(A ∩ ⋃ B_b)` for disjoint
measurable `B_b`. -/
theorem lsum_measure_inter (m : Measure S) {A : α → Prop} (hA : S.M A) {set : β → α → Prop}
    {l : List β} (hm : ∀ b ∈ l, S.M (set b)) (hd : DisjOn set l) :
    lsum (fun b => m.μ (fun x => A x ∧ set b x)) l = m.μ (fun x => A x ∧ UnionOf set l x) := by
  induction l with
  | nil =>
    show (0 : R) = _; rw [← m.empty]; exact m.congr fun x => ⟨False.elim, fun ⟨_, _, hb, _⟩ => by cases hb⟩
  | cons b l ih =>
    have hm' : ∀ c ∈ l, S.M (set c) := fun c hc => hm c (List.mem_cons_of_mem _ hc)
    have hd' := (List.pairwise_cons.1 hd)
    show _ + lsum _ l = _
    rw [ih hm' hd'.2, ← m.union (S.inter hA (hm b List.mem_cons_self))
      (S.inter hA (measurable_unionOf hm')) (fun x ⟨_, h1⟩ ⟨_, c, hc, h2⟩ => hd'.1 c hc x h1 h2)]
    exact m.congr fun x => ⟨fun h => h.elim (fun ⟨h1, h2⟩ => ⟨h1, b, List.mem_cons_self, h2⟩)
      (fun ⟨h1, c, hc, h2⟩ => ⟨h1, c, List.mem_cons_of_mem _ hc, h2⟩),
      fun ⟨h1, c, hc, h2⟩ => by
        rcases List.mem_cons.1 hc with rfl | hc
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, c, hc, h2⟩⟩

/-- **Partitions.** If the disjoint measurable sets `B_b` cover `α`, then
`Σ_{b ∈ l} μ(A ∩ B_b) = μ(A)`. -/
theorem lsum_partition (m : Measure S) {A : α → Prop} (hA : S.M A) {set : β → α → Prop}
    {l : List β} (hm : ∀ b ∈ l, S.M (set b)) (hd : DisjOn set l) (hc : ∀ x, UnionOf set l x) :
    lsum (fun b => m.μ (fun x => A x ∧ set b x)) l = m.μ A := by
  rw [lsum_measure_inter m hA hm hd]; exact m.congr fun x => ⟨fun h => h.1, fun h => ⟨h, hc x⟩⟩

/-- Disjoint measurable sets have total measure at most `μ(α)`. -/
theorem lsum_measure_le (m : Measure S) {set : β → α → Prop} {l : List β}
    (hm : ∀ b ∈ l, S.M (set b)) (hd : DisjOn set l) :
    lsum (fun b => m.μ (set b)) l ≤ m.μ (fun _ => True) := by
  have := lsum_measure_inter m S.univ hm hd
  rw [lsum_congr (G := fun b => m.μ (set b)) fun b _ => m.congr fun x => by simp] at this
  rw [this]; exact m.le_univ (S.inter S.univ (measurable_unionOf hm))

end families

/-! ## Simple functions -/

section simple

variable {α : Type} {S : SigmaAlgebra α}

/-- A **simple function**, given as a list of pairs `(aᵢ, Aᵢ)` with `aᵢ ≥ 0` and the `Aᵢ`
pairwise disjoint measurable sets; it stands for `Σ aᵢ · 1_{Aᵢ}`. -/
def IsSimple (S : SigmaAlgebra α) (l : List (R × (α → Prop))) : Prop :=
  (∀ p ∈ l, 0 ≤ p.1 ∧ S.M p.2) ∧ DisjOn Prod.snd l

/-- The simple function `l` lies **below** `f`: `aᵢ ≤ f` on `Aᵢ`. -/
def Below (l : List (R × (α → Prop))) (f : α → R) : Prop := ∀ p ∈ l, ∀ x, p.2 x → p.1 ≤ f x

/-- The **integral of a simple function**: `Σ aᵢ μ(Aᵢ)`. -/
def sint (m : Measure S) (l : List (R × (α → Prop))) : R := lsum (fun p => p.1 * m.μ p.2) l

/-- Integrals of simple functions are non-negative. -/
theorem sint_nonneg (m : Measure S) {l : List (R × (α → Prop))} (hl : IsSimple S l) :
    0 ≤ sint m l := lsum_nonneg fun p hp =>
  OrderedRing.mul_nonneg (hl.1 p hp).1 (m.nonneg _ (hl.1 p hp).2)

/-- Completion of a simple function by the piece `(0, complement of the union)`, so that the
pieces cover `α`. -/
def complete (l : List (R × (α → Prop))) : List (R × (α → Prop)) :=
  l ++ [(0, fun x => ¬ UnionOf Prod.snd l x)]

/-- The completion is again simple. -/
theorem IsSimple.complete {l : List (R × (α → Prop))} (hl : IsSimple S l) :
    IsSimple S (MeasureTheory.complete l) := by
  refine ⟨fun p hp => ?_, ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact hl.1 p hp
    · rw [List.mem_singleton.1 hp]
      exact ⟨Std.le_refl 0, S.compl _ (measurable_unionOf fun p hp => (hl.1 p hp).2)⟩
  · exact List.pairwise_append.2 ⟨hl.2, List.pairwise_singleton _ _, fun p hp q hq x h1 h2 => by
      rw [List.mem_singleton.1 hq] at h2; exact h2 ⟨p, hp, h1⟩⟩

/-- The completion stays below any non-negative `f`. -/
theorem Below.complete {l : List (R × (α → Prop))} {f : α → R} (hb : Below l f)
    (hf : ∀ x, 0 ≤ f x) : Below (MeasureTheory.complete l) f := fun p hp x hx => by
  rcases List.mem_append.1 hp with hp | hp
  · exact hb p hp x hx
  · rw [List.mem_singleton.1 hp]; exact hf x

/-- The pieces of the completion cover `α`. -/
theorem complete_cover (l : List (R × (α → Prop))) (x : α) :
    UnionOf Prod.snd (MeasureTheory.complete l) x := by
  by_cases h : UnionOf Prod.snd l x
  · obtain ⟨p, hp, hx⟩ := h; exact ⟨p, List.mem_append_left _ hp, hx⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h⟩

/-- Completion does not change the integral. -/
theorem sint_complete (m : Measure S) (l : List (R × (α → Prop))) :
    sint m (MeasureTheory.complete l) = sint m l := by
  unfold sint MeasureTheory.complete; rw [lsum_append]
  show _ + ((0 : R) * _ + 0) = _; grind

/-- Common refinement of a simple function `l₁` with a disjoint family `l₂`, with new
coefficients `c p q` on the pieces `p.2 ∩ set q`. -/
def refine {β : Type} (l₁ : List (R × (α → Prop))) (l₂ : List β) (set : β → α → Prop)
    (c : R × (α → Prop) → β → R) : List (R × (α → Prop)) :=
  l₁.flatMap fun p => l₂.map fun q => (c p q, fun x => p.2 x ∧ set q x)

/-- The refinement is simple. -/
theorem IsSimple.refine {β : Type} {l₁ : List (R × (α → Prop))} (hl : IsSimple S l₁) {l₂ : List β}
    {set : β → α → Prop} (hm : ∀ q ∈ l₂, S.M (set q)) (hd : DisjOn set l₂)
    {c : R × (α → Prop) → β → R} (hc : ∀ p ∈ l₁, ∀ q ∈ l₂, 0 ≤ c p q) :
    IsSimple S (MeasureTheory.refine l₁ l₂ set c) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨p, hp, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    exact ⟨hc p hp q hq, S.inter (hl.1 p hp).2 (hm q hq)⟩
  · refine List.pairwise_flatMap.2 ⟨fun p _ => List.pairwise_map.2 (hd.imp fun h x h1 h2 =>
      h x h1.2 h2.2), hl.2.imp fun h r hr r' hr' x h1 h2 => ?_⟩
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hr
    obtain ⟨q', _, rfl⟩ := List.mem_map.1 hr'
    exact h x h1.1 h2.1

/-- The integral of a refinement: `Σ_p Σ_q c p q · μ(p.2 ∩ set q)`. -/
theorem sint_refine {β : Type} (m : Measure S) (l₁ : List (R × (α → Prop))) (l₂ : List β)
    (set : β → α → Prop) (c : R × (α → Prop) → β → R) :
    sint m (MeasureTheory.refine l₁ l₂ set c) =
      lsum (fun p => lsum (fun q => c p q * m.μ (fun x => p.2 x ∧ set q x)) l₂) l₁ := by
  unfold sint MeasureTheory.refine; rw [lsum_flatMap]
  exact lsum_congr fun p _ => by rw [lsum_map]

end simple

/-! ## The integral of a non-negative function -/

section integral

variable {α : Type} {S : SigmaAlgebra α} (m : Measure S)

/-- `s` is the integral of some simple function below `f`. -/
def LowerSum (f : α → R) (s : R) : Prop := ∃ l, IsSimple S l ∧ Below l f ∧ s = sint m l

/-- The integrals of simple functions below `f` are bounded. -/
def BddIntegral (f : α → R) : Prop := ∃ B, ∀ l, IsSimple S l → Below l f → sint m l ≤ B

/-- **Integrable non-negative function.** Measurable, non-negative, and the integrals of the
simple functions below it are bounded. -/
structure LIntegrable (f : α → R) : Prop where
  /-- Measurability. -/
  measurable : Measurable S f
  /-- Non-negativity. -/
  nonneg : ∀ x, 0 ≤ f x
  /-- Bounded lower sums. -/
  bdd : BddIntegral m f

/-- The empty simple function. -/
theorem isSimple_nil : IsSimple S ([] : List (R × (α → Prop))) :=
  ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩

/-- The empty simple function lies below everything. -/
theorem below_nil (f : α → R) : Below ([] : List (R × (α → Prop))) f :=
  fun _ h => absurd h List.not_mem_nil

/-- The lower sums of `f` form a non-empty set (the empty simple function). -/
theorem lowerSum_ne (f : α → R) : ∃ s, LowerSum m f s := ⟨0, [], isSimple_nil, below_nil f, rfl⟩

/-- Bounded lower sums. -/
theorem lowerSum_bdd {f : α → R} (h : BddIntegral m f) : ∃ M, ∀ s, LowerSum m f s → s ≤ M :=
  let ⟨B, hB⟩ := h; ⟨B, fun _ ⟨l, h1, h2, e⟩ => e ▸ hB l h1 h2⟩

/-- **The Lebesgue integral.** `∫ f dμ` is the supremum of the integrals of the simple functions
below `f` (and `0` if they are unbounded). -/
noncomputable def lintegral (f : α → R) : R :=
  open Classical in
  if h : BddIntegral m f then
    Classical.choose (exists_lub (LowerSum m f) (lowerSum_ne m f) (lowerSum_bdd m h))
  else 0

/-- The integral of a simple function below `f` is at most `∫ f`. -/
theorem le_lintegral {f : α → R} (hf : BddIntegral m f) {l : List (R × (α → Prop))}
    (hl : IsSimple S l) (hb : Below l f) : sint m l ≤ lintegral m f := by
  unfold lintegral; rw [dite_eq_left_of_eq_true (eq_true hf)]
  exact (Classical.choose_spec (exists_lub (LowerSum m f) (lowerSum_ne m f) (lowerSum_bdd m hf))).1
    _ ⟨l, hl, hb, rfl⟩

/-- `∫ f` is at most any common bound of the integrals of simple functions below `f`. -/
theorem lintegral_le {f : α → R} {B : R} (h : ∀ l, IsSimple S l → Below l f → sint m l ≤ B) :
    lintegral m f ≤ B := by
  have hf : BddIntegral m f := ⟨B, h⟩
  unfold lintegral; rw [dite_eq_left_of_eq_true (eq_true hf)]
  exact (Classical.choose_spec (exists_lub (LowerSum m f) (lowerSum_ne m f) (lowerSum_bdd m hf))).2
    B fun _ ⟨l, h1, h2, e⟩ => e ▸ h l h1 h2

/-- The integral is non-negative. -/
theorem lintegral_nonneg {f : α → R} (hf : BddIntegral m f) : 0 ≤ lintegral m f :=
  le_lintegral m hf isSimple_nil (below_nil f)

/-- **Monotonicity of the integral.** If `0 ≤ f ≤ g`, `f` is measurable and `g` integrable, then
`f` is integrable and `∫ f ≤ ∫ g`. -/
theorem lintegral_mono {f g : α → R} (hg : LIntegrable m g) (hf : Measurable S f)
    (hf0 : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    LIntegrable m f ∧ lintegral m f ≤ lintegral m g := by
  have h : ∀ l, IsSimple S l → Below l f → sint m l ≤ lintegral m g := fun l hl hb =>
    le_lintegral m hg.bdd hl fun p hp x hx => Std.le_trans (hb p hp x hx) (hfg x)
  exact ⟨⟨hf, hf0, _, h⟩, lintegral_le m h⟩

/-- A simple function below a constant `c` has integral at most `c · μ(α)`. -/
theorem sint_le_const {l : List (R × (α → Prop))} (hl : IsSimple S l) {c : R} (hc : 0 ≤ c)
    (hb : Below l (fun _ => c)) : sint m l ≤ c * m.μ (fun _ => True) := by
  have h1 : sint m l ≤ lsum (fun p => c * m.μ p.2) l := lsum_le fun p hp => by
    by_cases hne : ∃ x, p.2 x
    · obtain ⟨x, hx⟩ := hne
      exact OrderedRing.mul_le_mul_of_nonneg_right (hb p hp x hx) (m.nonneg _ (hl.1 p hp).2)
    · have : m.μ p.2 = 0 := by rw [← m.empty]; exact m.congr fun x => ⟨fun h => hne ⟨x, h⟩, False.elim⟩
      rw [this]; grind
  rw [lsum_mul_left] at h1
  have := lsum_measure_le m (set := Prod.snd) (fun p hp => (hl.1 p hp).2) hl.2
  have := OrderedRing.mul_le_mul_of_nonneg_left this hc
  grind

/-- **Integral of a constant.** `∫ c dμ = c · μ(α)` for `c ≥ 0`. -/
theorem lintegral_const {c : R} (hc : 0 ≤ c) :
    LIntegrable m (fun _ => c) ∧ lintegral m (fun _ => c) = c * m.μ (fun _ => True) := by
  have hb : BddIntegral m (fun _ => c) := ⟨_, fun l hl hb => sint_le_const m hl hc hb⟩
  refine ⟨⟨Measurable.const S c, fun _ => hc, hb⟩, Std.le_antisymm (lintegral_le m fun l hl hb =>
    sint_le_const m hl hc hb) ?_⟩
  have := le_lintegral m hb (l := [(c, fun _ => True)])
    ⟨fun p hp => by rw [List.mem_singleton.1 hp]; exact ⟨hc, S.univ⟩, List.pairwise_singleton _ _⟩
    fun p hp x _ => by rw [List.mem_singleton.1 hp]; exact Std.le_refl c
  unfold sint at this; simp only [lsum] at this; grind

/-- The zero function has integral `0`. -/
theorem lintegral_zero : LIntegrable m (fun _ => 0) ∧ lintegral m (fun _ => 0) = 0 := by
  have := lintegral_const m (Std.le_refl 0); rw [this.2]; exact ⟨this.1, by grind⟩

/-- **Homogeneity.** `∫ c f = c ∫ f` for `c ≥ 0`. -/
theorem lintegral_const_mul {f : α → R} (hf : LIntegrable m f) {c : R} (hc : 0 ≤ c) :
    LIntegrable m (fun x => c * f x) ∧ lintegral m (fun x => c * f x) = c * lintegral m f := by
  rcases (by grind : c = 0 ∨ 0 < c) with h0 | hpos
  · subst h0
    have e : (fun x => (0 : R) * f x) = fun _ => 0 := funext fun x => by grind
    rw [e, (lintegral_zero m).2]; exact ⟨(lintegral_zero m).1, by grind⟩
  -- Scaling a simple function by `c` or by `1/c`.
  let sc : R → List (R × (α → Prop)) → List (R × (α → Prop)) := fun t l => l.map fun p => (t * p.1, p.2)
  have hsc : ∀ {t} (l : List (R × (α → Prop))), 0 ≤ t → IsSimple S l → IsSimple S (sc t l) :=
    fun l ht hl => ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨OrderedRing.mul_nonneg ht (hl.1 q hq).1, (hl.1 q hq).2⟩,
      List.pairwise_map.2 (hl.2.imp fun h => h)⟩
  have hint : ∀ t (l : List (R × (α → Prop))), sint m (sc t l) = t * sint m l := fun t l => by
    unfold sint; rw [lsum_map, ← lsum_mul_left]; exact lsum_congr fun p _ => by grind
  have hcf : ∀ l, IsSimple S l → Below l (fun x => c * f x) → sint m l ≤ c * lintegral m f :=
    fun l hl hb => by
      have := le_lintegral m hf.bdd (hsc (t := 1 / c) l (Std.le_of_lt (div_pos (show (0 : R) < 1 by grind) hpos)) hl)
        fun p hp x hx => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          have := hb q hq x hx
          exact div_le_of_le_mul' hpos this
      rw [hint] at this
      have := OrderedRing.mul_le_mul_of_nonneg_left this (Std.le_of_lt hpos)
      have e : c * (1 / c * sint m l) = sint m l := by grind
      grind
  refine ⟨⟨hf.measurable.const_mul hc, fun x => OrderedRing.mul_nonneg hc (hf.nonneg x), _, hcf⟩,
    Std.le_antisymm (lintegral_le m hcf) ?_⟩
  have hb' : BddIntegral m (fun x => c * f x) := ⟨_, hcf⟩
  -- `c ∫ f ≤ ∫ c f`: every lower sum of `f`, scaled by `c`, is a lower sum of `c f`.
  have : lintegral m f ≤ 1 / c * lintegral m (fun x => c * f x) := lintegral_le m fun l hl hb => by
    have := le_lintegral m hb' (hsc l (Std.le_of_lt hpos) hl) fun p hp x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact OrderedRing.mul_le_mul_of_nonneg_left (hb q hq x hx) (Std.le_of_lt hpos)
    rw [hint] at this
    have := OrderedRing.mul_le_mul_of_nonneg_left this (Std.le_of_lt (div_pos (show (0 : R) < 1 by grind) hpos))
    have e : 1 / c * (c * sint m l) = sint m l := by grind
    grind
  have := OrderedRing.mul_le_mul_of_nonneg_left this (Std.le_of_lt hpos)
  have e : c * (1 / c * lintegral m fun x => c * f x) = lintegral m fun x => c * f x := by grind
  grind
where
  /-- `a ≤ c b` with `c > 0` gives `(1/c) a ≤ b`. -/
  div_le_of_le_mul' {a b c : R} (hc : 0 < c) (h : a ≤ c * b) : 1 / c * a ≤ b := by
    have := OrderedRing.mul_le_mul_of_nonneg_left h (Std.le_of_lt (div_pos (show (0 : R) < 1 by grind) hc))
    have e : 1 / c * (c * b) = b := by grind
    grind

end integral

end MeasureTheory

end Foundations.Topology
