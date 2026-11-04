import Foundations.Langlands.Padic.LegendreBasic

/-!
# Legendre's theorem, the easy half: necessity of the congruence conditions

For the conic `a x² + b y² + c z² = 0` with squarefree, pairwise coprime, non-zero integer
coefficients, Legendre (1785) found three congruence conditions and the sign condition, and
proved them necessary and sufficient for a non-trivial integer point. This file proves the
**necessity**: a non-trivial solution forces

* `−bc` to be a square modulo `|a|`, `−ca` modulo `|b|`, `−ab` modulo `|c|`
  (`legendre_necessary`), and
* `a, b, c` not to be all of the same sign (`not_same_sign_of_solution`).

The argument: first make the solution *primitive* (no prime divides all of `x, y, z`;
`exists_primitive`, by descent on `|x| + |y| + |z|`). Then for a prime `p ∣ a`, if `p ∣ z`
the equation gives `p ∣ b y²`, so `p ∣ y` (as `p ∤ b`), so `p² ∣ a x²`, so `p ∣ x` (as `a` is
squarefree) — contradicting primitivity. Hence `z` is invertible modulo `a`, and from
`b y² ≡ −c z² (mod a)` the integer `t = b y z⁻¹` satisfies `t² ≡ −bc (mod a)`.

These are the conditions that Hasse (1921) would read as solvability in ℚₚ for `p ∣ abc`, the
sign condition being solvability in ℝ; see `HasseConic`.
-/

namespace Foundations.Langlands.Padic

namespace Legendre

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Hypotheses and conclusions -/

/-- A triple `(x, y, z)` is **non-trivial** if it is not `(0, 0, 0)`. -/
def Nontriv (x y z : Int) : Prop := x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0

/-- The conic `a x² + b y² + c z² = 0` has a **non-trivial integer point**. -/
def ConicSolvableZ (a b c : Int) : Prop :=
  ∃ x y z : Int, Nontriv x y z ∧ a * (x * x) + b * (y * y) + c * (z * z) = 0

/-- Legendre's standing hypotheses on the coefficients: non-zero, squarefree and pairwise
coprime. -/
structure Admissible (a b c : Int) : Prop where
  /-- `a ≠ 0`. -/
  ha : a ≠ 0
  /-- `b ≠ 0`. -/
  hb : b ≠ 0
  /-- `c ≠ 0`. -/
  hc : c ≠ 0
  /-- `a` is squarefree. -/
  sa : Squarefree a
  /-- `b` is squarefree. -/
  sb : Squarefree b
  /-- `c` is squarefree. -/
  sc : Squarefree c
  /-- `gcd(a, b) = 1`. -/
  cab : Coprime a b
  /-- `gcd(b, c) = 1`. -/
  cbc : Coprime b c
  /-- `gcd(c, a) = 1`. -/
  cca : Coprime c a

/-- **Legendre's congruence conditions.** `−bc` is a square mod `|a|`, `−ca` mod `|b|`, and
`−ab` mod `|c|`. -/
def LegendreCond (a b c : Int) : Prop :=
  IsSqMod (-(b * c)) a ∧ IsSqMod (-(c * a)) b ∧ IsSqMod (-(a * b)) c

/-- The **sign condition**: `a, b, c` are not all positive and not all negative. -/
def MixedSigns (a b c : Int) : Prop :=
  ¬ (0 < a ∧ 0 < b ∧ 0 < c) ∧ ¬ (a < 0 ∧ b < 0 ∧ c < 0)

/-- Admissibility is invariant under the cyclic permutation `(a, b, c) ↦ (b, c, a)`. -/
theorem Admissible.rotate {a b c : Int} (h : Admissible a b c) : Admissible b c a :=
  ⟨h.hb, h.hc, h.ha, h.sb, h.sc, h.sa, h.cbc, h.cca, h.cab⟩

/-- Admissibility is invariant under the transposition `(a, b, c) ↦ (b, a, c)`. -/
theorem Admissible.swap {a b c : Int} (h : Admissible a b c) : Admissible b a c :=
  ⟨h.hb, h.ha, h.hc, h.sb, h.sa, h.sc, h.cab.symm, h.cca.symm, h.cbc.symm⟩

/-- Admissibility is invariant under changing all signs. -/
theorem Admissible.neg {a b c : Int} (h : Admissible a b c) : Admissible (-a) (-b) (-c) :=
  ⟨by have := h.ha; omega, by have := h.hb; omega, by have := h.hc; omega,
    h.sa.neg, h.sb.neg, h.sc.neg, h.cab.neg_left.neg_right, h.cbc.neg_left.neg_right,
    h.cca.neg_left.neg_right⟩

/-! ## Primitive solutions -/

/-- A solution is **primitive** if no prime divides all three coordinates. -/
def Primitive (x y z : Int) : Prop :=
  ∀ p, Prime p → (p : Int) ∣ x → (p : Int) ∣ y → (p : Int) ∣ z → False

/-- **Primitive solutions.** A non-trivial solution of `a x² + b y² + c z² = 0` can be replaced
by a primitive one (divide by common prime factors; descent on `|x| + |y| + |z|`). -/
theorem exists_primitive {a b c : Int} : ∀ (N : Nat) (x y z : Int),
    x.natAbs + y.natAbs + z.natAbs = N → Nontriv x y z →
    a * (x * x) + b * (y * y) + c * (z * z) = 0 →
    ∃ x' y' z', Nontriv x' y' z' ∧ Primitive x' y' z' ∧
      a * (x' * x') + b * (y' * y') + c * (z' * z') = 0 := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro x y z hN hnt heq
    by_cases hprim : Primitive x y z
    · exact ⟨x, y, z, hnt, hprim, heq⟩
    have : ∃ p, Prime p ∧ (p : Int) ∣ x ∧ (p : Int) ∣ y ∧ (p : Int) ∣ z :=
      Classical.byContradiction fun hno => hprim fun p hp h1 h2 h3 => hno ⟨p, hp, h1, h2, h3⟩
    obtain ⟨p, hp, ⟨x₁, rfl⟩, ⟨y₁, rfl⟩, ⟨z₁, rfl⟩⟩ := this
    have hp2 : 2 ≤ p := hp.1
    have hp0 : (p : Int) * p ≠ 0 := Int.mul_ne_zero (by omega) (by omega)
    have heq₁ : a * (x₁ * x₁) + b * (y₁ * y₁) + c * (z₁ * z₁) = 0 := by
      have : (p : Int) * p * (a * (x₁ * x₁) + b * (y₁ * y₁) + c * (z₁ * z₁)) = 0 := by
        rw [← heq]; grind
      rcases Int.mul_eq_zero.1 this with h | h
      · exact absurd h hp0
      · exact h
    have hnt₁ : Nontriv x₁ y₁ z₁ := by
      rcases hnt with h | h | h
      · exact Or.inl fun h0 => h (by rw [h0, Int.mul_zero])
      · exact Or.inr (Or.inl fun h0 => h (by rw [h0, Int.mul_zero]))
      · exact Or.inr (Or.inr fun h0 => h (by rw [h0, Int.mul_zero]))
    have hle : ∀ w : Int, 2 * w.natAbs ≤ ((p : Int) * w).natAbs := fun w => by
      rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_right _ hp2
    have hx := hle x₁; have hy := hle y₁; have hz := hle z₁
    have hpos : 0 < x₁.natAbs + y₁.natAbs + z₁.natAbs := by
      rcases hnt₁ with h | h | h <;> have := Int.natAbs_pos.2 h <;> omega
    exact ih (x₁.natAbs + y₁.natAbs + z₁.natAbs) (by omega) x₁ y₁ z₁ rfl hnt₁ heq₁

/-! ## The congruence conditions -/

/-- For a primitive solution and a squarefree `a` coprime to `b`, the coordinate `z` is coprime
to `a`. -/
theorem coprime_z {a b c x y z : Int} (ha : a ≠ 0) (sa : Squarefree a) (cab : Coprime a b)
    (hprim : Primitive x y z) (heq : a * (x * x) + b * (y * y) + c * (z * z) = 0) :
    Coprime a z := by
  apply coprime_of_no_prime ha
  intro p hp hpa hpz
  have hp0 : (p : Int) ≠ 0 := by have := hp.1; omega
  -- `p ∣ b y²`, hence `p ∣ y`
  have hby : (p : Int) ∣ b * (y * y) := by
    rw [show b * (y * y) = -(a * (x * x)) - c * (z * z) by omega]
    exact Int.dvd_sub (Int.dvd_neg.2 (Int.dvd_trans hpa (Int.dvd_mul_right _ _)))
      (Int.dvd_trans hpz (Int.dvd_trans (Int.dvd_mul_right _ _) (Int.dvd_mul_left _ _)))
  have hpy : (p : Int) ∣ y := by
    rcases prime_dvd_mul hp hby with h | h
    · exact absurd (cab.not_dvd hp hpa h) id
    · exact prime_dvd_of_dvd_sq hp h
  -- `p² ∣ a x²`, hence `p ∣ x`
  obtain ⟨a₁, rfl⟩ := hpa
  have hna₁ := sa.not_dvd_cofactor hp rfl
  have hax : (p : Int) * p ∣ p * (a₁ * (x * x)) := by
    rw [show (p : Int) * (a₁ * (x * x)) = -(b * (y * y)) - c * (z * z) by
      rw [← Int.mul_assoc]; omega]
    exact Int.dvd_sub (Int.dvd_neg.2 (Int.dvd_trans (Int.mul_dvd_mul hpy hpy)
      (Int.dvd_mul_left _ _)))
      (Int.dvd_trans (Int.mul_dvd_mul hpz hpz) (Int.dvd_mul_left _ _))
  have h1 := Int.dvd_of_mul_dvd_mul_left hp0 hax
  have hpx : (p : Int) ∣ x := by
    rcases prime_dvd_mul hp h1 with h | h
    · exact absurd h hna₁
    · exact prime_dvd_of_dvd_sq hp h
  exact hprim p hp hpx hpy hpz

/-- **The congruence condition at `a`.** A primitive solution of `a x² + b y² + c z² = 0`, with
`a` squarefree and coprime to `b`, makes `−bc` a square modulo `a`: with `z w ≡ 1 (mod a)`, the
integer `t = b y w` has `t² ≡ −bc`. -/
theorem isSqMod_of_primitive {a b c x y z : Int} (ha : a ≠ 0) (sa : Squarefree a)
    (cab : Coprime a b) (hprim : Primitive x y z)
    (heq : a * (x * x) + b * (y * y) + c * (z * z) = 0) : IsSqMod (-(b * c)) a := by
  obtain ⟨w, hw⟩ := exists_inv_mod (coprime_z ha sa cab hprim heq).symm
  refine ⟨b * y * w, ?_⟩
  have h1 : a ∣ b * (y * y) + c * (z * z) := ⟨-(x * x), by rw [Int.mul_neg]; omega⟩
  rw [show b * y * w * (b * y * w) - -(b * c) =
      b * (w * w) * (b * (y * y) + c * (z * z)) - b * c * ((z * w - 1) * (z * w + 1)) by grind]
  exact Int.dvd_sub (Int.dvd_trans h1 (Int.dvd_mul_left _ _))
    (Int.dvd_trans (Int.dvd_trans hw (Int.dvd_mul_right _ _)) (Int.dvd_mul_left _ _))

/-- **Legendre's theorem, necessity.** If `a, b, c` are non-zero, squarefree and pairwise
coprime and `a x² + b y² + c z² = 0` has a non-trivial integer solution, then `−bc` is a square
modulo `|a|`, `−ca` modulo `|b|`, and `−ab` modulo `|c|`. -/
theorem legendre_necessary {a b c : Int} (h : Admissible a b c) (hs : ConicSolvableZ a b c) :
    LegendreCond a b c := by
  obtain ⟨x₀, y₀, z₀, hnt, heq₀⟩ := hs
  obtain ⟨x, y, z, -, hprim, heq⟩ := exists_primitive _ x₀ y₀ z₀ rfl hnt heq₀
  refine ⟨isSqMod_of_primitive h.ha h.sa h.cab hprim heq, ?_, ?_⟩
  · exact isSqMod_of_primitive (x := y) (y := z) (z := x) h.hb h.sb h.cbc
      (fun p hp h1 h2 h3 => hprim p hp h3 h1 h2) (by rw [← heq]; grind)
  · exact isSqMod_of_primitive (x := z) (y := x) (z := y) h.hc h.sc h.cca
      (fun p hp h1 h2 h3 => hprim p hp h2 h3 h1) (by rw [← heq]; grind)

/-- A positive coefficient times a square is non-negative, and positive if the base is
non-zero. -/
theorem mul_sq_pos {a x : Int} (ha : 0 < a) : 0 ≤ a * (x * x) ∧ (x ≠ 0 → 0 < a * (x * x)) := by
  have h0 : 0 ≤ x * x := by rw [← Int.natAbs_mul_self']; exact Int.mul_nonneg (by omega) (by omega)
  refine ⟨Int.mul_nonneg (by omega) h0, fun hx => Int.mul_pos ha ?_⟩
  rw [← Int.natAbs_mul_self']
  have := Int.natAbs_pos.2 hx
  exact Int.mul_pos (by omega) (by omega)

/-- **The sign condition is necessary.** If `a, b, c > 0` (or all `< 0`), the conic
`a x² + b y² + c z² = 0` has no non-trivial integer point. -/
theorem not_same_sign_of_solution {a b c : Int} (hs : ConicSolvableZ a b c) :
    MixedSigns a b c := by
  obtain ⟨x, y, z, hnt, heq⟩ := hs
  constructor
  · rintro ⟨ha, hb, hc⟩
    have := mul_sq_pos (x := x) ha; have := mul_sq_pos (x := y) hb
    have := mul_sq_pos (x := z) hc
    rcases hnt with h | h | h <;> omega
  · rintro ⟨ha, hb, hc⟩
    have := mul_sq_pos (x := x) (show 0 < -a by omega)
    have := mul_sq_pos (x := y) (show 0 < -b by omega)
    have := mul_sq_pos (x := z) (show 0 < -c by omega)
    simp only [Int.neg_mul] at *
    rcases hnt with h | h | h <;> omega

end Legendre

end Foundations.Langlands.Padic
