import Foundations.Numbers.Completeness

/-!
# The reals are uncountable; the rationals are not complete

Two contrasts close the construction of the number line.

**Cantor's theorem on the continuum (1874).** The natural numbers, the integers and the
rationals can all be listed in a single infinite sequence. The reals cannot: given *any*
sequence `f 0, f 1, f 2, …` of reals, some real is missing from it. We follow Cantor's original
*nested intervals* argument. Start with `[0, 1]`. At step `n`, cut the current interval into
thirds; the number `f n` cannot lie in both the lower and the upper third, so keep a third
that avoids it. The intervals are nested, so by completeness (the least upper bound of the left
endpoints) there is a real `L` in all of them — and `L` differs from every `f n`. So there are
"more" reals than natural numbers: the infinite comes in different sizes.

**The rationals are not complete.** Conversely, the property proved in `Completeness.lean`
genuinely fails one level down: the set `{q ∈ ℚ | q² < 2}` is nonempty and bounded above, yet has
no least upper bound *in ℚ*. Its supremum "should" be `√2`, which is irrational. This is precisely
the gap that the passage from `Q` to `R` fills.
-/

namespace Foundations.Numbers

open Lean.Grind Q

namespace R

open CauSeq

/-- One step of Cantor's construction: of the interval `[a, b]`, keep the upper third if `y` lies
below it, and otherwise the lower third (which then lies below `y`). -/
noncomputable def avoidStep (y : R) (p : Q × Q) : Q × Q :=
  open Classical in
  if y < ofQ ((p.1 + 2 * p.2) / 3) then ((p.1 + 2 * p.2) / 3, p.2)
  else (p.1, (2 * p.1 + p.2) / 3)

/-- Cantor's nested intervals for a sequence `f`: the `(n+1)`-st interval avoids `f n`. -/
noncomputable def nest (f : Nat → R) : Nat → Q × Q
  | 0 => (0, 1)
  | n + 1 => avoidStep (f n) (nest f n)

/-- One step of Cantor's construction shrinks the interval and moves it away from `y`. -/
theorem avoidStep_spec (y : R) {p : Q × Q} (h : p.1 < p.2) :
    (avoidStep y p).1 < (avoidStep y p).2 ∧ p.1 ≤ (avoidStep y p).1 ∧
      (avoidStep y p).2 ≤ p.2 ∧ (y < ofQ (avoidStep y p).1 ∨ ofQ (avoidStep y p).2 < y) := by
  unfold avoidStep
  by_cases hy : y < ofQ ((p.1 + 2 * p.2) / 3)
  · rw [ite_eq_left hy]; exact ⟨by grind, by grind, by grind, Or.inl hy⟩
  · rw [ite_eq_right hy]
    refine ⟨by grind, by grind, by grind, Or.inr ?_⟩
    have : ofQ ((2 * p.1 + p.2) / 3) < ofQ ((p.1 + 2 * p.2) / 3) := ofQ_lt.2 (by grind)
    grind

/-- Cantor's intervals are non-degenerate. -/
theorem nest_lt (f : Nat → R) (n : Nat) : (nest f n).1 < (nest f n).2 := by
  induction n with
  | zero => show (0 : Q) < 1; grind
  | succ n ih => exact (avoidStep_spec (f n) ih).1

/-- Cantor's intervals are nested. -/
theorem nest_nested (f : Nat → R) {N m : Nat} (h : N ≤ m) :
    (nest f N).1 ≤ (nest f m).1 ∧ (nest f m).2 ≤ (nest f N).2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = N + k := ⟨m - N, by omega⟩
  induction k with
  | zero => exact ⟨Q.le_refl _, Q.le_refl _⟩
  | succ k ih =>
    have := ih (by omega)
    have := avoidStep_spec (f (N + k)) (nest_lt f (N + k))
    show _ ≤ (avoidStep (f (N + k)) (nest f (N + k))).1 ∧
      (avoidStep (f (N + k)) (nest f (N + k))).2 ≤ _
    grind

/-- Every left endpoint lies below every right endpoint. -/
theorem nest_lo_le_hi (f : Nat → R) (n m : Nat) : (nest f n).1 ≤ (nest f m).2 := by
  have := nest_nested f (Nat.le_max_left n m)
  have := nest_nested f (Nat.le_max_right n m)
  have := nest_lt f (max n m)
  grind

/-- **Cantor's theorem: every sequence of reals misses some real.** For any `f : ℕ → ℝ` there is
a real number `x` with `f n ≠ x` for all `n`. -/
theorem exists_not_mem_seq (f : Nat → R) : ∃ x : R, ∀ n, f n ≠ x := by
  let S : R → Prop := fun x => ∃ n, x = ofQ (nest f n).1
  obtain ⟨L, hL1, hL2⟩ := exists_lub S ⟨_, 0, rfl⟩ ⟨ofQ (nest f 0).2, fun x ⟨n, hn⟩ => by
    rw [hn]; exact ofQ_le.2 (nest_lo_le_hi f n 0)⟩
  have hlo : ∀ k, ofQ (nest f k).1 ≤ L := fun k => hL1 _ ⟨k, rfl⟩
  have hhi : ∀ k, L ≤ ofQ (nest f k).2 := fun k => hL2 _ fun x ⟨n, hn⟩ => by
    rw [hn]; exact ofQ_le.2 (nest_lo_le_hi f n k)
  refine ⟨L, fun n h => ?_⟩
  have hspec := (avoidStep_spec (f n) (nest_lt f n)).2.2.2
  have e : nest f (n + 1) = avoidStep (f n) (nest f n) := rfl
  have := hlo (n + 1)
  have := hhi (n + 1)
  rw [e] at *
  rcases hspec with h1 | h1 <;> grind

/-- **Uncountability of ℝ.** There is no surjection from the natural numbers onto the reals. -/
theorem uncountable : ¬ ∃ f : Nat → R, ∀ x : R, ∃ n, f n = x := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := exists_not_mem_seq f
  obtain ⟨n, hn⟩ := hf x
  exact hx n hn

end R

namespace Q

/-- **ℚ is not complete.** The set `{q ∈ ℚ | q² < 2}` is nonempty (it contains `1`) and bounded
above (by `2`), but it has no least upper bound in `ℚ`. -/
theorem not_complete :
    (∃ q : Q, q * q < 2) ∧ (∃ M : Q, ∀ q : Q, q * q < 2 → q ≤ M) ∧
    ¬ ∃ s : Q, (∀ q : Q, q * q < 2 → q ≤ s) ∧ ∀ M : Q, (∀ q : Q, q * q < 2 → q ≤ M) → s ≤ M := by
  refine ⟨⟨1, by grind⟩, ⟨2, fun q hq => ?_⟩, ?_⟩
  · apply Classical.byContradiction
    intro h
    have h2 : (2 : Q) < q := by grind
    have := OrderedRing.mul_le_mul_of_nonneg_left (Q.le_of_lt' h2) (by grind : (0 : Q) ≤ q)
    grind
  rintro ⟨s, hs1, hs2⟩
  have h1 : 1 ≤ s := hs1 1 (by grind)
  have hss : s * 1 ≤ s * s := OrderedRing.mul_le_mul_of_nonneg_left h1 (by grind)
  have hne : s * s ≠ 2 := fun h => sqrt_two_irrational ⟨s, h⟩
  rcases (by grind : s * s < 2 ∨ 2 < s * s) with hlt | hgt
  · -- `s` is too small: `s + h` is still in the set, for a suitable `h > 0`.
    let h := (2 - s * s) / (2 * s + 2)
    have hpos : 0 < h := div_pos (by grind) (by grind)
    have e : h * (2 * s + 2) = 2 - s * s := by grind
    have hle1 : h ≤ 1 := by
      apply Classical.byContradiction
      intro hc
      have := OrderedRing.mul_pos (by grind : (0 : Q) < h - 1) (by grind : (0 : Q) < 2 * s + 2)
      grind
    have hh : h * h ≤ h * 1 := OrderedRing.mul_le_mul_of_nonneg_left hle1 (Q.le_of_lt' hpos)
    have := hs1 (s + h) (by grind)
    grind
  · -- `s` is too big: `s − h` is still an upper bound, for a suitable `h > 0`.
    let h := (s * s - 2) / (2 * s)
    have hpos : 0 < h := div_pos (by grind) (by grind)
    have e : h * (2 * s) = s * s - 2 := by grind
    have ht : 0 < s - h := by
      apply Classical.byContradiction
      intro hc
      have := OrderedRing.mul_nonpos_of_nonpos_of_nonneg (by grind : s - h ≤ 0)
        (by grind : (0 : Q) ≤ 2 * s)
      grind
    have hh : 0 ≤ h * h := OrderedRing.mul_nonneg (Q.le_of_lt' hpos) (Q.le_of_lt' hpos)
    have hub : ∀ q : Q, q * q < 2 → q ≤ s - h := by
      intro q hq
      apply Classical.byContradiction
      intro hc
      have := OrderedRing.mul_pos (by grind : (0 : Q) < q - (s - h)) (by grind : (0 : Q) < q + (s - h))
      grind
    have := hs2 (s - h) hub
    grind

end Q

end Foundations.Numbers
