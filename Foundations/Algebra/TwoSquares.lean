import Foundations.Algebra.GaussianInt

/-!
# Fermat's two-squares theorem

On Christmas Day 1640 Fermat wrote to Mersenne that every prime of the form `4k + 1` is a
sum of two squares — `5 = 1 + 4`, `13 = 4 + 9`, `17 = 1 + 16`, `29 = 4 + 25` — and, as usual,
offered no proof. Euler found one in 1749 after years of effort. The classical modern route
goes through the Gaussian integers `ℤ[i]`: they form a Euclidean domain, hence a PID, and
a prime `p ≡ 1 (mod 4)` cannot remain prime there.

We formalise instead the astonishing **"one-sentence proof"** of Don Zagier (1990), itself a
distillation of an argument of Heath-Brown, which uses nothing but counting:

> The involution on the finite set `S = {(x, y, z) ∈ ℕ³ : x² + 4yz = p}` defined by
> `(x, y, z) ↦ (x + 2z, z, y − x − z)` if `x < y − z`,
> `(2y − x, y, x − y + z)` if `y − z < x < 2y`, and
> `(x − 2y, x − y + z, y)` if `x > 2y`
> has exactly one fixed point, so `|S|` is odd, and the involution `(x, y, z) ↦ (x, z, y)`
> also has a fixed point.

A fixed point of the second involution has `y = z`, so `p = x² + (2y)²`. The parity
principle — *an involution on a finite set has as many fixed points as the set has
elements, modulo 2* — is the case `p = 2` of the fixed-point congruence for `p`-group actions
proved in `Action.lean`, applied to the group `ℤ/2ℤ`. It is a striking illustration of the
structural method: a theorem of number theory obtained from a theorem about group actions,
via a set constructed for the purpose.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Algebra

open FiniteType

universe u

/-! ## The parity principle for involutions -/

/-- `2` is prime. -/
theorem isPrime_two : IsPrime 2 := by
  refine ⟨Nat.le_refl 2, fun d hd => ?_⟩
  have h := Nat.le_of_dvd (by decide) hd
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with h0 | h1 | h2
  · rw [h0] at hd; exact absurd (Nat.eq_zero_of_zero_dvd hd) (by decide)
  · exact Or.inl h1
  · exact Or.inr h2

/-- An involution `f` makes `ℤ/2ℤ` act: `0` acts trivially and `1` acts by `f`. -/
@[reducible] def involutionAction {α : Type u} (f : α → α) (hf : ∀ x, f (f x) = x) : MulAction (ZMod 2) α where
  smul k x := if (ZMod.val k).val = 0 then x else f x
  one_smul x := rfl
  mul_smul j k x := by
    obtain ⟨j, hj⟩ := j
    obtain ⟨k, hk⟩ := k
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rfl
    · rfl
    · rfl
    · show (if ((⟨1, hj⟩ : Fin 2) + ⟨1, hk⟩).val = 0 then x else f x) = f (f x)
      rw [hf]; rfl

/-- **Parity principle.** An involution `f` of a finite set `α` has as many fixed points as
`α` has elements, modulo `2`. -/
theorem involution_fixed_mod_two {α : Type u} [FiniteType α] (f : α → α) (hf : ∀ x, f (f x) = x) :
    count (fun x => f x = x) % 2 = card α % 2 := by
  letI := involutionAction f hf
  have h := MulAction.count_fixed_mod (G := ZMod 2) (X := α) isPrime_two (k := 1)
    (by rw [ZMod.card])
  rw [← h]
  congr 1
  apply count_congr
  intro x
  constructor
  · intro hx k
    show (if (ZMod.val k).val = 0 then x else f x) = x
    split
    · rfl
    · exact hx
  · intro hx
    have := hx (ZMod.of ⟨1, by decide⟩)
    exact this

/-! ## Zagier's set and involution -/

section Zagier

variable (p : Nat)

/-- Membership in Zagier's set: `x² + 4yz = p`. -/
def InS (t : Nat × Nat × Nat) : Prop := t.1 * t.1 + 4 * t.2.1 * t.2.2 = p

/-- **Zagier's involution** on triples of natural numbers. -/
def zagier (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  if t.1 + t.2.2 < t.2.1 then (t.1 + 2 * t.2.2, t.2.2, t.2.1 - t.1 - t.2.2)
  else if t.1 < 2 * t.2.1 then (2 * t.2.1 - t.1, t.2.1, t.1 + t.2.2 - t.2.1)
  else (t.1 - 2 * t.2.1, t.1 + t.2.2 - t.2.1, t.2.1)

/-- Zagier's map, first case. -/
theorem zagier_eq1 (x y z : Nat) (h : x + z < y) : zagier (x, y, z) = (x + 2 * z, z, y - x - z) := by
  unfold zagier; simp only; rw [ite_true_of h]

/-- Zagier's map, second case. -/
theorem zagier_eq2 (x y z : Nat) (h1 : ¬ x + z < y) (h2 : x < 2 * y) :
    zagier (x, y, z) = (2 * y - x, y, x + z - y) := by
  unfold zagier; simp only; rw [ite_false_of h1, ite_true_of h2]

/-- Zagier's map, third case. -/
theorem zagier_eq3 (x y z : Nat) (h1 : ¬ x + z < y) (h2 : ¬ x < 2 * y) :
    zagier (x, y, z) = (x - 2 * y, x + z - y, y) := by
  unfold zagier; simp only; rw [ite_false_of h1, ite_false_of h2]

variable {p}

/-- A square is never prime. -/
theorem not_prime_square {x : Nat} (hp : IsPrime (x * x)) : False := by
  have h2 := hp.1
  rcases hp.2 x ⟨x, rfl⟩ with h | h
  · rw [h] at h2; simp at h2
  · have hx : 2 ≤ x := by
      apply Classical.byContradiction; intro hlt
      have : x * x ≤ 1 * 1 := Nat.mul_le_mul (by omega) (by omega)
      omega
    have : 2 * x ≤ x * x := Nat.mul_le_mul_right x hx
    omega

/-- Facts about points of Zagier's set when `p ≡ 1 (mod 4)` is prime: all coordinates are
positive, and the boundary cases `x = y - z` and `x = 2y` do not occur. -/
theorem InS.facts (hp : IsPrime p) (h4 : p % 4 = 1) {x y z : Nat} (h : InS p (x, y, z)) :
    0 < x ∧ 0 < y ∧ 0 < z ∧ x + z ≠ y ∧ x ≠ 2 * y := by
  unfold InS at h
  simp only at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero; intro hx; subst hx
    have : p = 4 * (y * z) := by grind
    omega
  · apply Nat.pos_of_ne_zero; intro hy; subst hy
    exact not_prime_square (x := x) (by rw [show x * x = p by grind]; exact hp)
  · apply Nat.pos_of_ne_zero; intro hz; subst hz
    exact not_prime_square (x := x) (by rw [show x * x = p by grind]; exact hp)
  · intro hxy
    subst hxy
    exact not_prime_square (x := x + 2 * z) (by rw [show (x + 2 * z) * (x + 2 * z) = p by grind]; exact hp)
  · intro hx; subst hx
    have : p = 4 * (y * y + y * z) := by grind
    omega

/-- Zagier's map preserves the set `S`. -/
theorem zagier_mem {t : Nat × Nat × Nat} (h : InS p t) : InS p (zagier t) := by
  obtain ⟨x, y, z⟩ := t
  unfold InS at h ⊢
  simp only at h
  unfold zagier
  simp only
  by_cases h1 : x + z < y
  · rw [ite_true_of h1]
    obtain ⟨w, rfl⟩ : ∃ w, y = x + z + w := ⟨y - x - z, by omega⟩
    simp only
    rw [show x + z + w - x - z = w by omega]
    grind
  · rw [ite_false_of h1]
    by_cases h2 : x < 2 * y
    · rw [ite_true_of h2]
      obtain ⟨b, hb⟩ : ∃ b, x + b = 2 * y := ⟨2 * y - x, by omega⟩
      obtain ⟨c, hc⟩ : ∃ c, y + c = x + z := ⟨x + z - y, by omega⟩
      simp only
      rw [show 2 * y - x = b by omega, show x + z - y = c by omega]
      grind
    · rw [ite_false_of h2]
      obtain ⟨b, hb⟩ : ∃ b, x = 2 * y + b := ⟨x - 2 * y, by omega⟩
      simp only
      rw [show x - 2 * y = b by omega, show x + z - y = y + b + z by omega]
      subst hb
      grind

/-- **Zagier's map is an involution** on `S`. -/
theorem zagier_zagier (hp : IsPrime p) (h4 : p % 4 = 1) {t : Nat × Nat × Nat} (h : InS p t) :
    zagier (zagier t) = t := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨hx, hy, hz, _, _⟩ := h.facts hp h4
  by_cases h1 : x + z < y
  · rw [zagier_eq1 x y z h1, zagier_eq3 (x + 2 * z) z (y - x - z) (by omega) (by omega)]
    simp only [Prod.mk.injEq, and_true, true_and]; omega
  · by_cases h2 : x < 2 * y
    · rw [zagier_eq2 x y z h1 h2, zagier_eq2 (2 * y - x) y (x + z - y) (by omega) (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]; omega
    · rw [zagier_eq3 x y z h1 h2, zagier_eq1 (x - 2 * y) (x + z - y) y (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]; omega

/-- **Zagier's involution has exactly one fixed point**, namely `(1, 1, (p - 1)/4)`. -/
theorem zagier_fixed_iff (hp : IsPrime p) (h4 : p % 4 = 1) {t : Nat × Nat × Nat}
    (h : InS p t) : zagier t = t ↔ t = (1, 1, p / 4) := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨hx, hy, hz, hb1, hb2⟩ := h.facts hp h4
  have hS := h
  unfold InS at hS
  simp only at hS
  constructor
  · intro hfix
    by_cases h1 : x + z < y
    · rw [zagier_eq1 x y z h1] at hfix; simp only [Prod.mk.injEq, and_true, true_and] at hfix; omega
    · by_cases h2 : x < 2 * y
      · rw [zagier_eq2 x y z h1 h2] at hfix
        simp only [Prod.mk.injEq] at hfix
        have hxy : y = x := by omega
        subst hxy
        -- Now `p = y (y + 4z)`, so `y ∣ p`.
        have hdvd : y ∣ p := ⟨y + 4 * z, by grind⟩
        rcases hp.2 y hdvd with h1' | h1'
        · subst h1'
          simp only [Prod.mk.injEq, true_and]
          omega
        · exfalso
          have : y * y + 4 * y * z ≥ y * 1 + y * 4 := by
            have := Nat.mul_le_mul_left y (show 1 ≤ y by omega)
            have := Nat.mul_le_mul_left y (show 4 ≤ 4 * z by omega)
            grind
          omega
      · rw [zagier_eq3 x y z h1 h2] at hfix; simp only [Prod.mk.injEq, and_true, true_and] at hfix; omega
  · intro ht
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl⟩ := ht
    have hp5 : 5 ≤ p := by have := hp.1; omega
    rw [zagier_eq2 1 1 (p / 4) (by omega) (by omega)]
    simp only [Prod.mk.injEq, and_true, true_and]; omega

/-- The coordinate swap `(x, y, z) ↦ (x, z, y)` preserves `S`. -/
theorem swap_mem {x y z : Nat} (h : InS p (x, y, z)) : InS p (x, z, y) := by
  unfold InS at h ⊢; simp only at h ⊢; grind

/-! ## The finite set `S` -/

/-- Points of `S` have all coordinates at most `p`. -/
theorem InS.bound (hp : IsPrime p) (h4 : p % 4 = 1) {x y z : Nat} (h : InS p (x, y, z)) :
    x < p + 1 ∧ y < p + 1 ∧ z < p + 1 := by
  obtain ⟨_, hy, hz, _, _⟩ := h.facts hp h4
  unfold InS at h; simp only at h
  have h1 := Nat.le_mul_self x
  have h2 : y ≤ y * z := Nat.le_mul_of_pos_right y hz
  have h3 : z ≤ y * z := Nat.le_mul_of_pos_left z hy
  have h4' : 4 * y * z = 4 * (y * z) := Nat.mul_assoc 4 y z
  omega

variable (p)

/-- **Zagier's set** `S = {(x, y, z) : x² + 4yz = p}` as a finite type (coordinates are
bounded by `p`). -/
def ZSet : Type := {t : Fin (p + 1) × Fin (p + 1) × Fin (p + 1) //
  InS p (t.1.val, t.2.1.val, t.2.2.val)}

/-- Zagier's set is finite. -/
noncomputable instance : FiniteType (ZSet p) :=
  FiniteType.instSubtype (fun t : Fin (p + 1) × Fin (p + 1) × Fin (p + 1) =>
    InS p (t.1.val, t.2.1.val, t.2.2.val))

variable {p}

/-- The underlying triple of a point of `S`. -/
def ZSet.val (s : ZSet p) : Nat × Nat × Nat := (s.1.1.val, s.1.2.1.val, s.1.2.2.val)

/-- Points of `S` are determined by their triples. -/
theorem ZSet.val_injective {s s' : ZSet p} (h : s.val = s'.val) : s = s' := by
  simp only [ZSet.val, Prod.mk.injEq] at h
  apply Subtype.ext
  apply Prod.ext (Fin.ext h.1)
  exact Prod.ext (Fin.ext h.2.1) (Fin.ext h.2.2)

/-- Package a triple satisfying the equation as a point of `S`. -/
def ZSet.mk (hp : IsPrime p) (h4 : p % 4 = 1) (t : Nat × Nat × Nat) (h : InS p t) : ZSet p :=
  ⟨(⟨t.1, (InS.bound (x := t.1) (y := t.2.1) (z := t.2.2) hp h4 h).1⟩,
    ⟨t.2.1, (InS.bound (x := t.1) (y := t.2.1) (z := t.2.2) hp h4 h).2.1⟩,
    ⟨t.2.2, (InS.bound (x := t.1) (y := t.2.1) (z := t.2.2) hp h4 h).2.2⟩), h⟩

/-- The triple of `ZSet.mk`. -/
theorem ZSet.val_mk (hp : IsPrime p) (h4 : p % 4 = 1) (t : Nat × Nat × Nat) (h : InS p t) :
    (ZSet.mk hp h4 t h).val = t := rfl

end Zagier

/-! ## The theorem -/

/-- **Fermat's two-squares theorem.** Every prime `p ≡ 1 (mod 4)` is a sum of two squares:
`p = a² + b²` for some natural numbers `a`, `b`. (Zagier's one-sentence proof.) -/
theorem fermat_two_squares {p : Nat} (hp : IsPrime p) (h4 : p % 4 = 1) :
    ∃ a b : Nat, a * a + b * b = p := by
  -- Zagier's involution on `S`.
  let zS : ZSet p → ZSet p := fun s => ZSet.mk hp h4 (zagier s.val) (zagier_mem s.2)
  have hzS : ∀ s, zS (zS s) = s := fun s =>
    ZSet.val_injective (zagier_zagier hp h4 s.2)
  -- It has exactly one fixed point, so `|S|` is odd.
  have hp5 : 5 ≤ p := by have := hp.1; omega
  have h0 : InS p (1, 1, p / 4) := by unfold InS; simp only; omega
  let s0 : ZSet p := ZSet.mk hp h4 _ h0
  have hfix : count (fun s => zS s = s) = 1 := by
    rw [← count_eq_self s0]
    apply count_congr
    intro s
    constructor
    · intro h
      apply ZSet.val_injective
      exact (zagier_fixed_iff hp h4 s.2).1 (congrArg ZSet.val h)
    · intro h
      apply ZSet.val_injective
      show zagier s.val = s.val
      rw [h]
      exact (zagier_fixed_iff hp h4 h0).2 rfl
  have hodd := involution_fixed_mod_two zS hzS
  rw [hfix] at hodd
  -- So the swap `(x, y, z) ↦ (x, z, y)` has a fixed point.
  let τ : ZSet p → ZSet p := fun s =>
    ZSet.mk hp h4 (s.val.1, s.val.2.2, s.val.2.1) (swap_mem s.2)
  have hτ : ∀ s, τ (τ s) = s := fun s => ZSet.val_injective rfl
  have hodd' := involution_fixed_mod_two τ hτ
  rw [← hodd] at hodd'
  have hpos : 0 < count (fun s => τ s = s) := by omega
  obtain ⟨s, hs⟩ := count_pos.1 hpos
  have hyz : s.val.2.2 = s.val.2.1 := by
    exact congrArg (fun t : Nat × Nat × Nat => t.2.1)
      (show (s.val.1, s.val.2.2, s.val.2.1) = s.val from congrArg ZSet.val hs)
  refine ⟨s.val.1, 2 * s.val.2.1, ?_⟩
  have hS : InS p s.val := s.2
  unfold InS at hS
  rw [hyz] at hS
  grind

/-- Examples: `5 = 1² + 2²`, `13 = 2² + 3²`, `29 = 2² + 5²`. -/
example : 1 * 1 + 2 * 2 = 5 ∧ 2 * 2 + 3 * 3 = 13 ∧ 2 * 2 + 5 * 5 = 29 := by decide

end Foundations.Algebra
