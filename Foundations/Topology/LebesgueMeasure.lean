import Foundations.Topology.Caratheodory

/-!
# Lebesgue measure

We now feed Lebesgue's outer measure `m*` (`OuterMeasure.lean`) into Carathéodory's machine.
Because our measures are finite, we work with the restrictions

  `ν_{a,b}(A) = m*(A ∩ [a, b])`,

which are outer measures in the sense of `Caratheodory.lean` (countable subadditivity is the
theorem `outer_iUnion_le`). A set `E ⊆ ℝ` is **Lebesgue measurable** if it is
Carathéodory-measurable for *every* `ν_{a,b}`. These sets form a σ-algebra, and for each bounded
window `[a, b]` we obtain a finite measure `λ_{a,b}(E) = m*(E ∩ [a, b])`.

**The intervals are measurable.** The heart of the matter is that a half-line `(−∞, c]` splits
every test set additively. Given a cover of `T` by open intervals, cut each interval at `c`: the
two halves cover `T ∩ (−∞, c)` and `T ∩ (c, ∞)`, and their lengths add up to the original
length. The single point `c` has outer measure zero. Since the measurable sets form a σ-algebra,
all intervals (and hence all **Borel sets**, the σ-algebra they generate — Borel 1898) are
measurable, and `λ([c, d]) = d − c` by `outer_interval`.

**Why measurability is forced.** Lebesgue measure is translation invariant: covers can be
translated. If the Vitali set `V` were measurable, its translates `V + q (mod 1)` would be
disjoint measurable sets of equal measure filling `[0, 1)`, and we would be back in the
contradiction of `Vitali.lean`. Hence **the Vitali set is not Lebesgue measurable** — the measure
problem has no solution on all sets, but Carathéodory's σ-algebra is a perfectly good home for
Lebesgue's measure.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind Outer

namespace MeasureTheory

/-! ## Splitting covers at a point -/

/-- The right end of the left half of `(lo, hi)` cut at `c`. -/
noncomputable def cutHi (c lo hi : R) : R :=
  open Classical in if hi ≤ c then hi else if lo ≤ c then c else lo

/-- The left end of the right half of `(lo, hi)` cut at `c`. -/
noncomputable def cutLo (c lo hi : R) : R :=
  open Classical in if c ≤ lo then lo else if c ≤ hi then c else hi

/-- The cut halves have non-negative lengths adding up to the original length. -/
theorem cut_spec {c lo hi : R} (h : lo ≤ hi) :
    lo ≤ cutHi c lo hi ∧ cutLo c lo hi ≤ hi ∧
      (cutHi c lo hi - lo) + (hi - cutLo c lo hi) = hi - lo := by
  unfold cutHi cutLo; split <;> split <;> (try split) <;> (try split) <;> grind

/-- A point of `(lo, hi)` left of `c` lies in the left half. -/
theorem lt_cutHi {c lo hi x : R} (h1 : x < hi) (h2 : x < c) : x < cutHi c lo hi := by
  unfold cutHi; split <;> (try split) <;> grind

/-- A point of `(lo, hi)` right of `c` lies in the right half. -/
theorem cutLo_lt {c lo hi x : R} (h1 : lo < x) (h2 : c < x) : cutLo c lo hi < x := by
  unfold cutLo; split <;> (try split) <;> grind

/-- **Cutting a cover.** For a coverable `T` and any `c`:
`m*(T ∩ (−∞, c)) + m*(T ∩ (c, ∞)) ≤ m*(T)`. -/
theorem outer_cut {T : R → Prop} (hT : Coverable T) (c : R) :
    outer (fun x => T x ∧ x < c) + outer (fun x => T x ∧ c < x) ≤ outer T :=
  le_of_forall_eps fun ε hε => by
    obtain ⟨S, ⟨lo, hi, hlh, hcov, hS⟩, hSlt⟩ := outer_approx hT hε
    have h1 : ∀ n, 0 ≤ cutHi c (lo n) (hi n) - lo n := fun n => by
      have := (cut_spec (c := c) (hlh n)).1; grind
    have h2 : ∀ n, 0 ≤ hi n - cutLo c (lo n) (hi n) := fun n => by
      have := (cut_spec (c := c) (hlh n)).2.1; grind
    obtain ⟨s1, hs1, -⟩ := comparison h1 (fun n => by have := cut_spec (c := c) (hlh n); grind) hS
    obtain ⟨s2, hs2, -⟩ := comparison h2 (fun n => by have := cut_spec (c := c) (hlh n); grind) hS
    have e : s1 + s2 = S := (hs1.add hs2).unique (hS.congr fun n => (cut_spec (hlh n)).2.2.symm)
    have c1 : CoverSum (fun x => T x ∧ x < c) s1 :=
      ⟨lo, fun n => cutHi c (lo n) (hi n), fun n => (cut_spec (hlh n)).1, fun x ⟨hx, hxc⟩ => by
        obtain ⟨n, a, b⟩ := hcov x hx
        exact ⟨n, a, lt_cutHi b hxc⟩, hs1⟩
    have c2 : CoverSum (fun x => T x ∧ c < x) s2 :=
      ⟨fun n => cutLo c (lo n) (hi n), hi, fun n => (cut_spec (hlh n)).2.1, fun x ⟨hx, hxc⟩ => by
        obtain ⟨n, a, b⟩ := hcov x hx
        exact ⟨n, cutLo_lt a hxc, b⟩, hs2⟩
    have := outer_le c1; have := outer_le c2; grind

/-- A single point has outer measure `0`. -/
theorem outer_point (c : R) : outer (fun x => x = c) = 0 := by
  rw [outer_congr (B := fun x => c ≤ x ∧ x ≤ c) fun x => by grind, outer_interval (Std.le_refl c)]
  grind

/-- **Half-lines split coverable sets additively.**
`m*(T ∩ (−∞, c]) + m*(T ∖ (−∞, c]) ≤ m*(T)`. -/
theorem outer_split_halfline {T : R → Prop} (hT : Coverable T) (c : R) :
    outer (fun x => T x ∧ x ≤ c) + outer (fun x => T x ∧ ¬ x ≤ c) ≤ outer T := by
  have hc := outer_cut hT c
  have hsub : ∀ {P : R → Prop}, Coverable (fun x => T x ∧ P x) := fun {P} =>
    let ⟨s, hs⟩ := hT; ⟨s, CoverSum.mono hs fun x h => h.1⟩
  have h1 : outer (fun x => T x ∧ x ≤ c) ≤ outer (fun x => T x ∧ x < c) := by
    have hu := outer_union_le' (hsub (P := fun x => x < c))
      (coverable_of_bdd (A := fun x => x = c) (a := c) (b := c) fun x h => by grind)
    rw [outer_point] at hu
    have := outer_mono hu.1 (A := fun x => T x ∧ x ≤ c) fun x ⟨h1, h2⟩ => by
      rcases (by grind : x < c ∨ x = c) with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr h
    grind
  rw [outer_congr (A := fun x => T x ∧ ¬ x ≤ c) (B := fun x => T x ∧ c < x) fun x => by grind]
  grind

/-! ## The outer measures `ν_{a,b}` -/

/-- The closed interval `[a, b]`. -/
def Icc (a b : R) (x : R) : Prop := a ≤ x ∧ x ≤ b

/-- Subsets of `[a, b]` are coverable. -/
theorem coverable_inter (A : R → Prop) (a b : R) : Coverable (fun x => A x ∧ Icc a b x) :=
  coverable_of_bdd fun _ h => h.2

/-- The outer measure `ν_{a,b}(A) = m*(A ∩ [a, b])`. -/
noncomputable def nu (a b : R) : OuterMeasure R where
  ν A := outer (fun x => A x ∧ Icc a b x)
  nonneg A := outer_nonneg _
  empty := by rw [outer_congr (B := fun _ => False) fun x => by simp, outer_empty]
  mono A B h := outer_mono (coverable_inter B a b) fun x hx => ⟨h x hx.1, hx.2⟩
  subadd A s hs := by
    have := (outer_iUnion_le (A := fun n x => A n x ∧ Icc a b x)
      (fun n => coverable_inter (A n) a b) hs).2
    rwa [outer_congr (A := fun x => ∃ n, A n x ∧ Icc a b x)
      (B := fun x => (∃ n, A n x) ∧ Icc a b x)
      fun x => ⟨fun ⟨n, h1, h2⟩ => ⟨⟨n, h1⟩, h2⟩, fun ⟨⟨n, h1⟩, h2⟩ => ⟨n, h1, h2⟩⟩] at this

/-- **Lebesgue measurability.** `E` is Carathéodory-measurable for every `ν_{a,b}`. -/
def LebesgueMeasurable (E : R → Prop) : Prop := ∀ a b : R, (nu a b).IsMeasurable E

/-- **The Lebesgue σ-algebra.** -/
def lebesgueSigma : SigmaAlgebra R where
  M := LebesgueMeasurable
  empty a b := (nu a b).sigma.empty
  compl A h a b := (nu a b).sigma.compl A (h a b)
  iUnion A h a b := (nu a b).sigma.iUnion A fun n => h n a b

/-- **Lebesgue measure on `[a, b]`.** `λ_{a,b}(E) = m*(E ∩ [a, b])` on the Lebesgue σ-algebra. -/
noncomputable def lebesgue (a b : R) : Measure lebesgueSigma :=
  (nu a b).measure.restrict fun _ h => h a b

/-- The defining formula of `λ_{a,b}`. -/
theorem lebesgue_apply (a b : R) (E : R → Prop) :
    (lebesgue a b).μ E = outer (fun x => E x ∧ Icc a b x) := rfl

/-- A measurable set splits any bounded test set additively. -/
theorem LebesgueMeasurable.split {E T : R → Prop} (hE : LebesgueMeasurable E) {a b : R}
    (hT : ∀ x, T x → Icc a b x) :
    outer T = outer (fun x => T x ∧ E x) + outer (fun x => T x ∧ ¬ E x) := by
  have h := hE a b T
  simp only [nu] at h
  rw [outer_congr (A := fun x => T x ∧ Icc a b x) (B := T) fun x => ⟨fun h => h.1,
    fun h => ⟨h, hT x h⟩⟩] at h
  rw [h]
  congr 1 <;> exact outer_congr fun x => ⟨fun h => h.1, fun h => ⟨h, hT x h.1⟩⟩

/-! ## Intervals are measurable -/

/-- **Half-lines `(−∞, c]` are Lebesgue measurable.** -/
theorem measurable_Iic (c : R) : LebesgueMeasurable (fun x => x ≤ c) := fun a b =>
  (nu a b).isMeasurable_of_le fun T => by
    simp only [nu]
    have := outer_split_halfline (coverable_inter T a b) c
    rw [outer_congr (A := fun x => (T x ∧ x ≤ c) ∧ Icc a b x)
        (B := fun x => (T x ∧ Icc a b x) ∧ x ≤ c) fun x => by grind,
      outer_congr (A := fun x => (T x ∧ ¬ x ≤ c) ∧ Icc a b x)
        (B := fun x => (T x ∧ Icc a b x) ∧ ¬ x ≤ c) fun x => by grind]
    exact this

/-- Open half-lines `(−∞, c) = ⋃ₙ (−∞, c − 1/(n+1)]` are measurable. -/
theorem measurable_Iio (c : R) : LebesgueMeasurable (fun x => x < c) :=
  lebesgueSigma.congr (lebesgueSigma.iUnion _ fun n => measurable_Iic (c - 1 / ((n : R) + 1)))
    fun x => ⟨fun ⟨n, h⟩ => by have := eps_pos n; grind, fun h => by
      obtain ⟨N, hN⟩ := eps_small (by grind : (0 : R) < c - x)
      exact ⟨N, by have := hN N (Nat.le_refl N); grind⟩⟩

/-- **Closed intervals `[c, d]` are Lebesgue measurable.** -/
theorem measurable_Icc (c d : R) : LebesgueMeasurable (Icc c d) :=
  lebesgueSigma.congr (lebesgueSigma.diff (measurable_Iic d) (measurable_Iio c))
    fun x => by unfold Icc; grind

/-- **Lebesgue measure of an interval is its length.** `λ_{a,b}([c, d]) = d − c` for
`[c, d] ⊆ [a, b]`. -/
theorem lebesgue_Icc {a b c d : R} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (lebesgue a b).μ (Icc c d) = d - c := by
  rw [lebesgue_apply, outer_congr (B := fun x => c ≤ x ∧ x ≤ d) fun x => by unfold Icc; grind,
    outer_interval hcd]

/-! ## Translation invariance -/

/-- Covers can be translated. -/
theorem coverSum_translate {A : R → Prop} {s : R} (r : R) (h : CoverSum A s) :
    CoverSum (fun x => A (x - r)) s := by
  obtain ⟨lo, hi, h1, h2, h3⟩ := h
  refine ⟨fun n => lo n + r, fun n => hi n + r, fun n => by have := h1 n; grind,
    fun x hx => ?_, h3.congr fun n => by grind⟩
  obtain ⟨n, a, b⟩ := h2 _ hx; exact ⟨n, by grind, by grind⟩

/-- **Translation invariance of the outer measure.** `m*(A + r) = m*(A)`. -/
theorem outer_translate (A : R → Prop) (r : R) : outer (fun x => A (x - r)) = outer A := by
  have back : ∀ s, CoverSum (fun x => A (x - r)) s → CoverSum A s := fun s h => by
    have := coverSum_translate (-r) h
    rwa [show (fun x => A (x - -r - r)) = A from funext fun x => by
      rw [show x - -r - r = x by grind]] at this
  by_cases hA : Coverable A
  · obtain ⟨s, hs⟩ := hA
    have hA' : Coverable (fun x => A (x - r)) := ⟨s, coverSum_translate r hs⟩
    exact Std.le_antisymm (outer_le_outer ⟨s, hs⟩ fun s h => coverSum_translate r h)
      (outer_le_outer hA' back)
  · have hA' : ¬ Coverable (fun x => A (x - r)) := fun ⟨s, hs⟩ => hA ⟨s, back s hs⟩
    unfold outer
    rw [dite_eq_right_of_eq_false (eq_false (show ¬ ∃ s, CoverSum A s from hA)),
      dite_eq_right_of_eq_false (eq_false (show ¬ ∃ s, CoverSum (fun x => A (x - r)) s from hA'))]

/-- **Translates of measurable sets are measurable.** -/
theorem LebesgueMeasurable.translate {E : R → Prop} (hE : LebesgueMeasurable E) (r : R) :
    LebesgueMeasurable (fun x => E (x - r)) := fun a b =>
  (nu a b).isMeasurable_of_le fun T => by
    simp only [nu]
    have h := hE (a - r) (b - r) (fun y => T (y + r))
    simp only [nu] at h
    have t : ∀ P : R → Prop, outer P = outer (fun y => P (y + r)) := fun P => by
      rw [← outer_translate (fun y => P (y + r)) r]
      exact outer_congr fun x => by rw [show x - r + r = x by grind]
    rw [t (fun x => T x ∧ Icc a b x), t (fun x => (T x ∧ E (x - r)) ∧ Icc a b x),
      t (fun x => (T x ∧ ¬ E (x - r)) ∧ Icc a b x)]
    have e1 : ∀ y, (T (y + r) ∧ Icc a b (y + r)) ↔ (T (y + r) ∧ Icc (a - r) (b - r) y) :=
      fun y => by unfold Icc; grind
    have e2 : ∀ y, ((T (y + r) ∧ E (y + r - r)) ∧ Icc a b (y + r)) ↔
        ((T (y + r) ∧ E y) ∧ Icc (a - r) (b - r) y) :=
      fun y => by rw [show y + r - r = y by grind]; unfold Icc; grind
    have e3 : ∀ y, ((T (y + r) ∧ ¬ E (y + r - r)) ∧ Icc a b (y + r)) ↔
        ((T (y + r) ∧ ¬ E y) ∧ Icc (a - r) (b - r) y) :=
      fun y => by rw [show y + r - r = y by grind]; unfold Icc; grind
    rw [outer_congr e1, outer_congr e2, outer_congr e3, h]
    exact Std.le_refl _

/-! ## The Vitali set is not Lebesgue measurable -/

section VitaliSet

open Vitali

/-- `[0, 1)` is Lebesgue measurable. -/
theorem measurable_I : LebesgueMeasurable I :=
  lebesgueSigma.congr (lebesgueSigma.diff (measurable_Iio 1) (measurable_Iio 0))
    fun x => by unfold I; grind

/-- `m*([0, 1)) = 1`: removing the point `1` from `[0, 1]` costs nothing. -/
theorem outer_I : outer I = 1 := by
  have h01 := outer_interval (show (0 : R) ≤ 1 by grind)
  apply Std.le_antisymm
  · have := outer_mono (coverable_of_bdd (A := fun x => 0 ≤ x ∧ x ≤ 1) (a := 0) (b := 1)
      fun _ h => h) (A := I) fun x h => ⟨h.1, Std.le_of_lt h.2⟩
    grind
  · have hu := outer_union_le' (coverable_of_bdd (A := I) (a := 0) (b := 1)
      fun x h => ⟨h.1, Std.le_of_lt h.2⟩)
      (coverable_of_bdd (A := fun x => x = 1) (a := 1) (b := 1) fun x h => by grind)
    have := outer_mono hu.1 (A := fun x => 0 ≤ x ∧ x ≤ 1) fun x ⟨h1, h2⟩ => by
      rcases (by grind : x < 1 ∨ x = 1) with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr h
    rw [outer_point] at hu
    grind

/-- If `V` were measurable, each translate `V + r (mod 1)` would have the outer measure of `V`. -/
theorem outer_shift (hV : LebesgueMeasurable V) {r : R} (hr : I r) :
    outer (shift V r) = outer V := by
  have hVI : ∀ x, V x → I x := fun x h => h.1
  have hP1 : LebesgueMeasurable (fun x => V (x - r)) := hV.translate r
  -- Split `shift V r` along the first translate.
  have s1 := hP1.split (T := shift V r) (a := 0) (b := 1) fun x h => ⟨h.1.1, Std.le_of_lt h.1.2⟩
  have e1 : outer (fun x => shift V r x ∧ V (x - r)) = outer (fun x => V (x - r) ∧ I x) :=
    outer_congr fun x => by unfold shift; grind
  have e2 : outer (fun x => shift V r x ∧ ¬ V (x - r)) = outer (fun x => I x ∧ V (x - r + 1)) :=
    outer_congr fun x => ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2.resolve_left h3⟩,
      fun ⟨h1, h2⟩ => ⟨⟨h1, Or.inr h2⟩, fun h3 => by
        have := hVI _ h2; have := hVI _ h3; unfold I at *; grind⟩⟩
  -- Split the first translate along `[0, 1)`.
  have s2 := measurable_I.split (T := fun x => V (x - r)) (a := 0) (b := 2) fun x h => by
    have := hVI _ h; unfold I at *; unfold Icc; grind
  -- The part of the first translate beyond `1` is a translate of the second piece.
  have e3 : outer (fun x => V (x - r) ∧ ¬ I x) = outer (fun x => I x ∧ V (x - r + 1)) := by
    rw [← outer_translate (fun x => V (x - r) ∧ ¬ I x) (-1)]
    exact outer_congr fun x => by
      rw [show x - -1 - r = x - r + 1 by grind]
      constructor
      · intro ⟨h1, h2⟩; have := hVI _ h1; unfold I at *; grind
      · intro ⟨h1, h2⟩; have := hVI _ h2; unfold I at *; grind
  rw [s1, e1, e2, ← e3, ← s2, outer_translate]

/-- **The Vitali set is not Lebesgue measurable.** Otherwise its countably many disjoint
translates `V + q (mod 1)`, all of the same measure, would fill `[0, 1)`, which has measure `1` —
impossible whether that common measure is zero or positive. -/
theorem vitali_not_measurable : ¬ LebesgueMeasurable V := by
  intro hV
  let L := lebesgue 0 1
  have hVI : ∀ x, V x → I x := fun x h => h.1
  have hsubI : ∀ {A : R → Prop}, (∀ x, A x → I x) → L.μ A = outer A := fun {A} h =>
    outer_congr fun x => ⟨fun h => h.1, fun hx => ⟨hx, (h x hx).1, Std.le_of_lt (h x hx).2⟩⟩
  have hmeas : ∀ r, LebesgueMeasurable (shift V r) := fun r =>
    lebesgueSigma.congr (lebesgueSigma.inter measurable_I
      (lebesgueSigma.union (hV.translate r) (lebesgueSigma.congr (hV.translate (r - 1))
        fun x => by rw [show x - (r - 1) = x - r + 1 by grind])))
      fun x => Iff.rfl
  have hsh : ∀ r, I r → L.μ (shift V r) = outer V := fun r hr => by
    rw [hsubI fun x h => h.1, outer_shift hV hr]
  have hI : L.μ I = 1 := by rw [hsubI fun x h => h, outer_I]
  rcases (by have := outer_nonneg V; grind : outer V = 0 ∨ 0 < outer V) with h0 | hpos
  · -- Countably many translates of measure `0` would fill `[0, 1)`.
    let A : Nat → R → Prop := fun n x => (∀ k, k < n → q k ≠ q n) ∧ shift V (q n) x
    have hA : ∀ n, LebesgueMeasurable (A n) := fun n => by
      by_cases hn : ∀ k, k < n → q k ≠ q n
      · exact lebesgueSigma.congr (hmeas (q n)) fun x => ⟨fun h => ⟨hn, h⟩, fun h => h.2⟩
      · exact lebesgueSigma.congr lebesgueSigma.empty fun x => ⟨False.elim, fun h => hn h.1⟩
    have h := L.additive A hA (fun m n hmn x h1 h2 => by
      rcases Nat.lt_or_gt_of_ne hmn with hlt | hlt
      · exact shift_disjoint (q_mem m) (q_mem n) (h2.1 m hlt) (q_rel m n) h1.2 h2.2
      · exact shift_disjoint (q_mem m) (q_mem n) (fun e => h1.1 n hlt e.symm) (q_rel m n)
          h1.2 h2.2)
    have e : (fun x => ∃ n, A n x) = I := funext fun x => propext
      ⟨fun ⟨n, h⟩ => h.2.1, fun hx => by
        obtain ⟨k, hk⟩ := shift_cover hx
        obtain ⟨k₀, hk₀, hmin⟩ := nat_least (fun j => q j = q k) ⟨k, rfl⟩
        exact ⟨k₀, fun j hj e => hmin j hj (e.trans hk₀), hk₀ ▸ hk⟩⟩
    rw [e, hI] at h
    have hz : ∀ n, L.μ (A n) = 0 := fun n => by
      by_cases hn : ∀ k, k < n → q k ≠ q n
      · have : A n = shift V (q n) := funext fun x => propext ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩
        rw [this, hsh _ (q_mem n), h0]
      · have : A n = fun _ => False := funext fun x => propext ⟨fun h => hn h.1, fun h => h.elim⟩
        rw [this, L.empty]
    have := h.unique (InvariantMeasure.hasSum_of_zero (m := 0) fun k _ => hz k)
    rw [fsum_zero] at this; grind
  · -- Finitely many disjoint translates would already have total measure `> 1`.
    obtain ⟨m, hm⟩ := archimedean (1 / outer V)
    have hmV : 1 < (m : R) * outer V := by
      have := OrderedRing.mul_lt_mul_of_pos_right hm hpos
      have : 1 / outer V * outer V = 1 := by grind
      grind
    let r : Nat → R := fun k => (k : R) / ((m : R) + 1)
    have hr : ∀ k, k < m → I (r k) := fun k hk => frac_mem (by omega)
    have hrinj : ∀ j k, r j = r k → j = k := fun j k e => by
      have hm := succ_pos m
      have : (j : R) = (k : R) := by
        have : (j : R) = r j * ((m : R) + 1) := by show _ = _ / _ * _; grind
        rw [this, e]; show _ / _ * _ = _; grind
      exact Nat.le_antisymm (OrderedRing.le_of_natCast_le_natCast (R := R) _ _ (by grind))
        (OrderedRing.le_of_natCast_le_natCast (R := R) _ _ (by grind))
    let A : Nat → R → Prop := fun k x => k < m ∧ shift V (r k) x
    have hA : ∀ k, LebesgueMeasurable (A k) := fun k => by
      by_cases hk : k < m
      · exact lebesgueSigma.congr (hmeas (r k)) fun x => ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
      · exact lebesgueSigma.congr lebesgueSigma.empty fun x => ⟨False.elim, fun h => hk h.1⟩
    have h := L.additive A hA (fun j k hjk x h1 h2 =>
      shift_disjoint (hr j h1.1) (hr k h2.1) (fun e => hjk (hrinj j k e))
        (rel_trans (rel_frac_zero j m) (rel_symm (rel_frac_zero k m))) h1.2 h2.2)
    have hz : ∀ k, m ≤ k → L.μ (A k) = 0 := fun k hk => by
      have : A k = fun _ => False := funext fun x => propext ⟨fun h => by omega, fun h => h.elim⟩
      rw [this, L.empty]
    have hsum := h.unique (InvariantMeasure.hasSum_of_zero hz)
    have hval : ∀ j, j ≤ m → fsum (fun k => L.μ (A k)) j = (j : R) * outer V := by
      intro j
      induction j with
      | zero => intro _; rw [fsum_zero]; grind
      | succ j ih =>
        intro hj
        have : A j = shift V (r j) := funext fun x => propext ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
        rw [fsum_succ, ih (by omega), this, hsh _ (hr j (by omega))]; grind
    rw [hval m (Nat.le_refl m)] at hsum
    have := L.mono (lebesgueSigma.iUnion A hA) measurable_I fun x ⟨n, h⟩ => h.2.1
    grind

end VitaliSet

end MeasureTheory

end Foundations.Topology
