import Foundations.Topology.SimpleFunctions

/-!
# The Lebesgue integral: additivity and monotone convergence

This file proves the two pillars of Lebesgue's integral for non-negative functions.

**Additivity**, `∫ (f + g) = ∫ f + ∫ g`. For `≥`, simple functions below `f` and `g` are
completed to partitions of the space and intersected piece by piece; their sum is a simple
function below `f + g` (finite additivity of `μ` does the bookkeeping). For `≤`, a simple
function `χ` below `f + g` is cut along the *levels* `{jδ ≤ f < (j+1)δ}` of `f` — Lebesgue's
partition of the range. On each piece `f ≥ jδ` and `g ≥ χ − (j+1)δ`, so `χ` is, up to `δ`, the
sum of a simple function below `f` and one below `g`.

**The monotone convergence theorem** (Beppo Levi, 1906; Lebesgue 1902 for bounded sequences). If
`0 ≤ f₀ ≤ f₁ ≤ ⋯` are integrable, `fₙ → f` pointwise and the integrals `∫ fₙ` are bounded, then
`f` is integrable and `∫ fₙ → ∫ f`. The proof is the classical one: for a simple `φ ≤ f` and
`c < 1`, the sets `Eₙ = {c φ ≤ fₙ}` increase to the whole space, so by continuity of the measure
from below, `lim ∫ fₙ ≥ c ∫ φ`. Here the representation of simple functions by *disjoint* pieces
pays off: on a piece `A` with value `a`, `Eₙ ∩ A = A ∩ {fₙ ≥ c a}` is measurable because `fₙ` is.

The theorem is where the Lebesgue integral decisively beats the Riemann integral: limits and
integrals may be interchanged under the mildest of hypotheses.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace MeasureTheory

/-- The positive part `max(x, 0)`. -/
noncomputable def pp (x : R) : R := open Classical in if 0 ≤ x then x else 0

/-- The positive part is non-negative. -/
theorem pp_nonneg (x : R) : 0 ≤ pp x := by unfold pp; split <;> grind

/-- The positive part dominates `x`. -/
theorem le_pp (x : R) : x ≤ pp x := by unfold pp; split <;> grind

/-- `pp x = x` for `x ≥ 0`. -/
theorem pp_of_nonneg {x : R} (h : 0 ≤ x) : pp x = x := by unfold pp; split <;> grind

/-- `pp x = 0` for `x ≤ 0`. -/
theorem pp_of_nonpos {x : R} (h : x ≤ 0) : pp x = 0 := by unfold pp; split <;> grind

variable {α : Type} {S : SigmaAlgebra α} (m : Measure S)

/-! ## Superadditivity -/

/-- **The sum of two simple functions.** Completing both and intersecting gives a simple function
below `f + g` whose integral is the sum of the two integrals. -/
theorem sint_add_le {f g : α → R} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {φ ψ : List (R × (α → Prop))} (hφ : IsSimple S φ) (hψ : IsSimple S ψ) (hbφ : Below φ f)
    (hbψ : Below ψ g) (hfg : BddIntegral m (fun x => f x + g x)) :
    sint m φ + sint m ψ ≤ lintegral m (fun x => f x + g x) := by
  have hφ' := hφ.complete; have hψ' := hψ.complete
  have hχ := hφ'.refine (fun q hq => (hψ'.1 q hq).2) hψ'.2 (c := fun p q => p.1 + q.1)
    fun p hp q hq => by have := (hφ'.1 p hp).1; have := (hψ'.1 q hq).1; grind
  have hb : Below (refine (complete φ) (complete ψ) Prod.snd fun p q => p.1 + q.1)
      (fun x => f x + g x) := fun r hr x hx => by
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    have := hbφ.complete hf0 p hp x hx.1; have := hbψ.complete hg0 q hq x hx.2
    show p.1 + q.1 ≤ f x + g x; grind
  have := le_lintegral m hfg hχ hb
  rw [sint_refine] at this
  rw [lsum_congr (G := fun p => lsum (fun q => p.1 * m.μ (fun x => p.2 x ∧ q.2 x)) (complete ψ) +
      lsum (fun q => q.1 * m.μ (fun x => p.2 x ∧ q.2 x)) (complete ψ)) fun p _ => by
        rw [← lsum_add]; exact lsum_congr fun q _ => by grind, lsum_add] at this
  have e1 : lsum (fun p => lsum (fun q => p.1 * m.μ (fun x => p.2 x ∧ q.2 x)) (complete ψ))
      (complete φ) = sint m φ := by
    rw [← sint_complete m φ]
    exact lsum_congr fun p hp => by
      rw [lsum_mul_left, lsum_partition m (hφ'.1 p hp).2 (fun q hq => (hψ'.1 q hq).2) hψ'.2
        (complete_cover ψ)]
  have e2 : lsum (fun p => lsum (fun q => q.1 * m.μ (fun x => p.2 x ∧ q.2 x)) (complete ψ))
      (complete φ) = sint m ψ := by
    rw [lsum_swap, ← sint_complete m ψ]
    exact lsum_congr fun q hq => by
      rw [lsum_mul_left]
      have e : lsum (fun p => m.μ (fun x => p.2 x ∧ q.2 x)) (complete φ) = m.μ q.2 := by
        rw [← lsum_partition m (hψ'.1 q hq).2 (fun p hp => (hφ'.1 p hp).2) hφ'.2 (complete_cover φ)]
        exact lsum_congr fun p _ => m.congr fun x => And.comm
      rw [e]
  grind

/-- **Superadditivity.** `∫ f + ∫ g ≤ ∫ (f + g)`. -/
theorem lintegral_add_ge {f g : α → R} (hf : LIntegrable m f) (hg : LIntegrable m g)
    (hfg : BddIntegral m (fun x => f x + g x)) :
    lintegral m f + lintegral m g ≤ lintegral m (fun x => f x + g x) := by
  have h1 : ∀ ψ, IsSimple S ψ → Below ψ g →
      lintegral m f ≤ lintegral m (fun x => f x + g x) - sint m ψ := fun ψ hψ hbψ =>
    lintegral_le m fun φ hφ hbφ => by
      have := sint_add_le m hf.nonneg hg.nonneg hφ hψ hbφ hbψ hfg; grind
  have : lintegral m g ≤ lintegral m (fun x => f x + g x) - lintegral m f :=
    lintegral_le m fun ψ hψ hbψ => by have := h1 ψ hψ hbψ; grind
  grind

/-! ## Subadditivity: cutting the range into levels -/

/-- The levels of `f`: pieces `{jδ ≤ f < (j+1)δ}` for `j < K` and `{Kδ ≤ f}`, each recorded with
its lower value `jδ` and upper value `(j+1)δ`. -/
noncomputable def levels (f : α → R) (δ : R) (K : Nat) : List (R × R × (α → Prop)) :=
  (List.range K).map (fun (j : Nat) => ((j : R) * δ, ((j : R) + 1) * δ,
    fun x => (j : R) * δ ≤ f x ∧ f x < ((j : R) + 1) * δ)) ++
  [((K : R) * δ, ((K : R) + 1) * δ, fun x => (K : R) * δ ≤ f x)]

/-- The properties of the levels. -/
theorem levels_spec {f : α → R} (hf : Measurable S f) (hf0 : ∀ x, 0 ≤ f x) {δ : R} (hδ : 0 < δ)
    (K : Nat) :
    (∀ l ∈ levels f δ K, S.M l.2.2) ∧ DisjOn (fun l => l.2.2) (levels f δ K) ∧
      (∀ x, UnionOf (fun l => l.2.2) (levels f δ K) x) ∧
      (∀ l ∈ levels f δ K, 0 ≤ l.1 ∧ l.2.1 = l.1 + δ ∧
        ∀ x, l.2.2 x → l.1 ≤ f x ∧ (f x < l.2.1 ∨ (K : R) * δ ≤ l.1)) := by
  have nn : ∀ j : Nat, (0 : R) ≤ (j : R) := fun j => OrderedRing.natCast_nonneg
  have mono : ∀ i j : Nat, i + 1 ≤ j → ((i : R) + 1) * δ ≤ (j : R) * δ := fun i j h => by
    have : ((i + 1 : Nat) : R) ≤ (j : R) := OrderedRing.natCast_le_natCast_of_le _ _ h
    exact OrderedRing.mul_le_mul_of_nonneg_right (by grind) (Std.le_of_lt hδ)
  refine ⟨fun l hl => ?_, ?_, fun x => ?_, fun l hl => ?_⟩
  · rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.1 hl; exact S.inter (hf.ge _) (hf.lt _)
    · rw [List.mem_singleton.1 hl]; exact hf.ge _
  · refine List.pairwise_append.2 ⟨List.pairwise_map.2 (List.nodup_range.imp fun {i j} hij x h1 h2 =>
      ?_), List.pairwise_singleton _ _, fun a ha b hb x h1 h2 => ?_⟩
    · rcases Nat.lt_or_gt_of_ne hij with h | h
      · have := mono i j h; grind
      · have := mono j i h; grind
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
      rw [List.mem_singleton.1 hb] at h2
      have := mono j K (List.mem_range.1 hj); grind
  · have key : ∀ K : Nat, (∃ j, j < K ∧ (j : R) * δ ≤ f x ∧ f x < ((j : R) + 1) * δ) ∨
        (K : R) * δ ≤ f x := by
      intro K
      induction K with
      | zero => right; have := hf0 x; show ((0 : Nat) : R) * δ ≤ f x; grind
      | succ K ih =>
        rcases ih with ⟨j, hj, h⟩ | h
        · exact Or.inl ⟨j, by omega, h⟩
        · by_cases h' : ((K + 1 : Nat) : R) * δ ≤ f x
          · exact Or.inr h'
          · exact Or.inl ⟨K, by omega, h, by grind⟩
    rcases key K with ⟨j, hj, h⟩ | h
    · exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩), h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h⟩
  · rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.1 hl
      exact ⟨OrderedRing.mul_nonneg (nn j) (Std.le_of_lt hδ), by grind,
        fun x hx => ⟨hx.1, Or.inl hx.2⟩⟩
    · rw [List.mem_singleton.1 hl]
      exact ⟨OrderedRing.mul_nonneg (nn K) (Std.le_of_lt hδ), by grind,
        fun x hx => ⟨hx, Or.inr (Std.le_refl _)⟩⟩

/-- **Cutting a simple function below `f + g`.** Up to `δ μ(α)`, it is bounded by `∫ f + ∫ g`. -/
theorem sint_le_add {f g : α → R} (hf : LIntegrable m f) (hg : LIntegrable m g)
    {χ : List (R × (α → Prop))} (hχ : IsSimple S χ) (hb : Below χ (fun x => f x + g x))
    {δ : R} (hδ : 0 < δ) :
    sint m χ - δ * m.μ (fun _ => True) ≤ lintegral m f + lintegral m g := by
  have hC := hχ.complete
  have hbC := hb.complete fun x => by have := hf.nonneg x; have := hg.nonneg x; grind
  -- A level `K` above all coefficients.
  let M := lsum (fun p => p.1) (complete χ)
  have hM : ∀ p ∈ complete χ, p.1 ≤ M := by
    have : ∀ (l : List (R × (α → Prop))), (∀ p ∈ l, 0 ≤ p.1) → ∀ p ∈ l, p.1 ≤ lsum (fun p => p.1) l := by
      intro l hl
      induction l with
      | nil => intro p hp; exact absurd hp List.not_mem_nil
      | cons q l ih =>
        intro p hp
        have h1 := lsum_nonneg fun r hr => hl r (List.mem_cons_of_mem _ hr)
        have h2 := hl q List.mem_cons_self
        show p.1 ≤ q.1 + lsum _ l
        rcases List.mem_cons.1 hp with rfl | hp
        · grind
        · have := ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)) p hp; grind
    exact this _ fun p hp => (hC.1 p hp).1
  obtain ⟨K, hK⟩ := archimedean (M / δ)
  have hKδ : M ≤ (K : R) * δ := by
    have := OrderedRing.mul_lt_mul_of_pos_right hK hδ
    have e : M / δ * δ = M := by grind
    grind
  obtain ⟨L1, L2, L3, L4⟩ := levels_spec hf.measurable hf.nonneg hδ K
  -- The two simple functions below `f` and below `g`.
  have hrf := hC.refine L1 L2 (c := fun _ l => l.1) fun _ _ l hl => (L4 l hl).1
  have hrg := hC.refine L1 L2 (c := fun p l => pp (p.1 - l.2.1)) fun _ _ _ _ => pp_nonneg _
  have hbf : Below (refine (complete χ) (levels f δ K) (fun l => l.2.2) fun _ l => l.1) f :=
    fun r hr x hx => by
      obtain ⟨p, hp, hr⟩ := List.mem_flatMap.1 hr
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
      exact ((L4 l hl).2.2 x hx.2).1
  have hbg : Below (refine (complete χ) (levels f δ K) (fun l => l.2.2)
      fun p l => pp (p.1 - l.2.1)) g := fun r hr x hx => by
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
    show pp (p.1 - l.2.1) ≤ g x
    have h1 := hbC p hp x hx.1
    obtain ⟨_, h2, h3⟩ := L4 l hl
    have h4 := hM p hp
    have := hg.nonneg x
    unfold pp; split
    · rcases (h3 x hx.2).2 with h | h <;> grind
    · exact this
  have i1 := le_lintegral m hf.bdd hrf hbf
  have i2 := le_lintegral m hg.bdd hrg hbg
  rw [sint_refine] at i1 i2
  -- The level-by-level estimate.
  have key : lsum (fun p => (p.1 - δ) * m.μ p.2) (complete χ) ≤
      lsum (fun p => lsum (fun l => l.1 * m.μ (fun x => p.2 x ∧ l.2.2 x)) (levels f δ K))
        (complete χ) +
      lsum (fun p => lsum (fun l => pp (p.1 - l.2.1) * m.μ (fun x => p.2 x ∧ l.2.2 x))
        (levels f δ K)) (complete χ) := by
    rw [← lsum_add]
    refine lsum_le fun p hp => ?_
    rw [← lsum_add, ← lsum_partition m (hC.1 p hp).2 L1 L2 L3, ← lsum_mul_left]
    refine lsum_le fun l hl => ?_
    have hμ := m.nonneg _ (S.inter (hC.1 p hp).2 (L1 l hl))
    have := le_pp (p.1 - l.2.1); have := (L4 l hl).2.1
    have := OrderedRing.mul_le_mul_of_nonneg_right
      (show p.1 - δ ≤ l.1 + pp (p.1 - l.2.1) by grind) hμ
    grind
  have e : lsum (fun p => (p.1 - δ) * m.μ p.2) (complete χ) =
      sint m χ - δ * lsum (fun p => m.μ p.2) (complete χ) := by
    rw [← sint_complete m χ, ← lsum_mul_left]; unfold sint
    have := lsum_add (fun p => p.1 * m.μ p.2) (fun p => -(δ * m.μ p.2)) (complete χ)
    have e2 : lsum (fun p => -(δ * m.μ p.2)) (complete χ) = -lsum (fun p => δ * m.μ p.2) (complete χ) := by
      have := lsum_mul_left (-1) (fun p => δ * m.μ p.2) (complete χ)
      rw [lsum_congr (G := fun p => -1 * (δ * m.μ p.2)) fun p _ => by grind, this]; grind
    rw [lsum_congr (G := fun p => p.1 * m.μ p.2 + -(δ * m.μ p.2)) fun p _ => by grind, this, e2]
    grind
  have hle := lsum_measure_le m (set := Prod.snd) (fun p hp => (hC.1 p hp).2) hC.2
  have := OrderedRing.mul_le_mul_of_nonneg_left hle (Std.le_of_lt hδ)
  grind

/-- **Subadditivity.** `f + g` is integrable and `∫ (f + g) ≤ ∫ f + ∫ g`. -/
theorem lintegral_add_le {f g : α → R} (hf : LIntegrable m f) (hg : LIntegrable m g) :
    BddIntegral m (fun x => f x + g x) ∧
      lintegral m (fun x => f x + g x) ≤ lintegral m f + lintegral m g := by
  have hμ := m.nonneg _ S.univ
  have h : ∀ χ, IsSimple S χ → Below χ (fun x => f x + g x) →
      sint m χ ≤ lintegral m f + lintegral m g := fun χ hχ hb => le_of_forall_eps fun ε hε => by
    have hd : 0 < ε / (m.μ (fun _ => True) + 1) := div_pos hε (by grind)
    have := sint_le_add m hf hg hχ hb hd
    have : ε / (m.μ (fun _ => True) + 1) * m.μ (fun _ => True) ≤ ε := by
      have e : ε / (m.μ (fun _ => True) + 1) * (m.μ (fun _ => True) + 1) = ε := by grind
      have := OrderedRing.mul_le_mul_of_nonneg_left (show m.μ (fun _ => True) ≤
        m.μ (fun _ => True) + 1 by grind) (Std.le_of_lt hd)
      grind
    grind
  exact ⟨⟨_, h⟩, lintegral_le m h⟩

/-- **Additivity of the Lebesgue integral.** For integrable `f, g ≥ 0`, `f + g` is integrable and
`∫ (f + g) dμ = ∫ f dμ + ∫ g dμ`. -/
theorem lintegral_add {f g : α → R} (hf : LIntegrable m f) (hg : LIntegrable m g) :
    LIntegrable m (fun x => f x + g x) ∧
      lintegral m (fun x => f x + g x) = lintegral m f + lintegral m g := by
  obtain ⟨hb, hle⟩ := lintegral_add_le m hf hg
  have h0 : ∀ x, 0 ≤ f x + g x := fun x => by have := hf.nonneg x; have := hg.nonneg x; grind
  exact ⟨⟨hf.measurable.add hg.measurable, h0, hb⟩, Std.le_antisymm hle (lintegral_add_ge m hf hg hb)⟩

/-! ## The monotone convergence theorem -/

/-- **Monotone convergence theorem (Lebesgue 1902, Beppo Levi 1906).** Let `0 ≤ f₀ ≤ f₁ ≤ ⋯` be
integrable with `fₙ → f` pointwise and `∫ fₙ ≤ B` for all `n`. Then `f` is integrable and
`∫ fₙ dμ → ∫ f dμ`. -/
theorem monotone_convergence {F : Nat → α → R} {f : α → R} (hF : ∀ n, LIntegrable m (F n))
    (hmono : ∀ n x, F n x ≤ F (n + 1) x) (hlim : ∀ x, Tendsto (fun n => F n x) (f x)) {B : R}
    (hB : ∀ n, lintegral m (F n) ≤ B) :
    LIntegrable m f ∧ Tendsto (fun n => lintegral m (F n)) (lintegral m f) := by
  have hfm : Measurable S f := Measurable.of_tendsto (fun n => (hF n).measurable) hlim
  have hFf : ∀ n x, F n x ≤ f x := fun n x => le_lim_of_mono (fun k => hmono k x) (hlim x) n
  have hf0 : ∀ x, 0 ≤ f x := fun x => Std.le_trans ((hF 0).nonneg x) (hFf 0 x)
  -- The integrals increase to a limit `L`.
  have hImono : ∀ n, lintegral m (F n) ≤ lintegral m (F (n + 1)) := fun n =>
    (lintegral_mono m (hF (n + 1)) (hF n).measurable (hF n).nonneg (hmono n)).2
  obtain ⟨L, hL⟩ := R.monotone_convergence hImono ⟨B, hB⟩
  have hIL : ∀ n, lintegral m (F n) ≤ L := le_lim_of_mono hImono hL
  -- Every simple function below `f` has integral `≤ L`.
  have key : ∀ φ, IsSimple S φ → Below φ f → sint m φ ≤ L := by
    intro φ hφ hbφ
    have hc : ∀ c : R, 0 < c → c < 1 → c * sint m φ ≤ L := by
      intro c hc0 hc1
      let E : Nat → R × (α → Prop) → α → Prop := fun n p x => p.2 x ∧ c * p.1 ≤ F n x
      have hψ : ∀ n, IsSimple S (φ.map fun p => (c * p.1, E n p)) := fun n =>
        ⟨fun r hr => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
          exact ⟨OrderedRing.mul_nonneg (Std.le_of_lt hc0) (hφ.1 p hp).1,
            S.inter (hφ.1 p hp).2 ((hF n).measurable.ge _)⟩,
          List.pairwise_map.2 (hφ.2.imp fun h x h1 h2 => h x h1.1 h2.1)⟩
      have hle : ∀ n, lsum (fun p => c * (p.1 * m.μ (E n p))) φ ≤ L := fun n => by
        have := le_lintegral m (hF n).bdd (hψ n) fun r hr x hx => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact hx.2
        unfold sint at this; rw [lsum_map] at this
        rw [lsum_congr (G := fun p => c * p.1 * m.μ (E n p)) fun p _ => by grind]
        exact Std.le_trans this (hIL n)
      have hlimE : ∀ p ∈ φ, Tendsto (fun n => c * (p.1 * m.μ (E n p))) (c * (p.1 * m.μ p.2)) := by
        intro p hp
        refine Tendsto.const_mul c (Tendsto.const_mul p.1 ?_)
        have h := m.tendsto_iUnion (A := fun n => E n p)
          (fun n => S.inter (hφ.1 p hp).2 ((hF n).measurable.ge _))
          fun n x hx => ⟨hx.1, Std.le_trans hx.2 (hmono n x)⟩
        rwa [m.congr (A := fun x => ∃ n, E n p x) (B := p.2) fun x => ⟨fun ⟨_, h, _⟩ => h,
          fun hx => by
            rcases (by have := (hφ.1 p hp).1; grind : p.1 = 0 ∨ 0 < p.1) with h0 | hpos
            · exact ⟨0, hx, by rw [h0]; have := (hF 0).nonneg x; grind⟩
            · have hfx := hbφ p hp x hx
              have : c * p.1 < p.1 := by
                have := OrderedRing.mul_lt_mul_of_pos_right hc1 hpos; grind
              obtain ⟨N, hN⟩ := hlim x (f x - c * p.1) (by grind)
              exact ⟨N, hx, by have := abs_lt.1 (hN N (Nat.le_refl N)); grind⟩⟩] at h
      have := tendsto_le (lsum_tendsto hlimE) hle
      rw [lsum_mul_left] at this; exact this
    apply Classical.byContradiction; intro hn
    have hL0 : 0 ≤ L := Std.le_trans (lintegral_nonneg m (hF 0).bdd) (hIL 0)
    have hs : 0 < sint m φ := by grind
    have := hc ((sint m φ + L) / (2 * sint m φ)) (div_pos (by grind) (by grind))
      (by apply div_lt_of_lt_mul (by grind); grind)
    have e : (sint m φ + L) / (2 * sint m φ) * sint m φ = (sint m φ + L) / 2 := by grind
    grind
  have hfi : LIntegrable m f := ⟨hfm, hf0, L, key⟩
  have h1 : lintegral m f ≤ L := lintegral_le m key
  have h2 : L ≤ lintegral m f :=
    tendsto_le hL fun n => (lintegral_mono m hfi (hF n).measurable (hF n).nonneg (hFf n)).2
  refine ⟨hfi, ?_⟩
  rw [show lintegral m f = L from Std.le_antisymm h1 h2]; exact hL

end MeasureTheory

end Foundations.Topology
