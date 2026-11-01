import Foundations.Numbers.Compactness2D

/-!
# The fundamental theorem of algebra

**Every non-constant polynomial with complex coefficients has a complex root.** Gauss gave several
proofs; the one formalised here is the "minimum modulus" argument going back to d'Alembert (1746)
and Argand (1814), made rigorous by the completeness of ℝ:

1. `|p(z)| → ∞` as `|z| → ∞`, so outside a large square `|p(z)| ≥ |p(0)|`.
2. On the square, `|p|` attains a minimum at some `z*` (the two-dimensional extreme value
   theorem); by (1) it is a global minimum.
3. **d'Alembert's lemma**: if `p(z*) ≠ 0`, write `p(z* + w) = b₀ + bₖ wᵏ + (higher terms)` with
   `bₖ ≠ 0`. Choosing `ω` with `ωᵏ = −b₀/bₖ` (a `k`-th root, from the polar form) and `w = tω` with
   small `t > 0` gives `|p(z* + w)| ≈ (1 − tᵏ)|b₀| < |b₀|` — contradicting minimality.

Polynomials are represented by their **coefficient lists** `[c₀, c₁, …, c_d]`, evaluated by
Horner's rule `c₀ + z (c₁ + z (c₂ + ⋯))`. A polynomial `c₀ :: t` is non-constant when some
coefficient in `t` is non-zero.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace C

open R

/-! ## Polynomials as coefficient lists -/

/-- **Evaluation** of the polynomial with coefficient list `[c₀, c₁, …]` at `z` (Horner's rule). -/
def peval : List C → C → C
  | [], _ => 0
  | c :: cs, z => c + z * peval cs z

/-- Sum of polynomials, coefficientwise. -/
def padd : List C → List C → List C
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: padd l m

/-- Multiplying a polynomial by a constant. -/
def pscale (a : C) (l : List C) : List C := l.map (a * ·)

/-- Evaluation is additive. -/
theorem peval_padd (l m : List C) (z : C) : peval (padd l m) z = peval l z + peval m z := by
  induction l generalizing m with
  | nil => show peval m z = 0 + peval m z; grind
  | cons a l ih =>
    cases m with
    | nil => show peval (a :: l) z = peval (a :: l) z + 0; grind
    | cons b m => show (a + b) + z * peval (padd l m) z = (a + z * peval l z) + (b + z * peval m z)
                  rw [ih]; grind

/-- Evaluation commutes with scaling. -/
theorem peval_pscale (a : C) (l : List C) (z : C) : peval (pscale a l) z = a * peval l z := by
  induction l with
  | nil => show (0 : C) = a * 0; grind
  | cons c l ih => show a * c + z * peval (pscale a l) z = a * (c + z * peval l z); rw [ih]; grind

/-- The **shifted polynomial** `w ↦ p(z₀ + w)`, again as a coefficient list. -/
def pshift (z₀ : C) : List C → List C
  | [] => []
  | c :: cs => padd [c] (padd (pscale z₀ (pshift z₀ cs)) (0 :: pshift z₀ cs))

/-- `pshift z₀ p` evaluates to `p(z₀ + w)`. -/
theorem peval_pshift (z₀ : C) (l : List C) (w : C) : peval (pshift z₀ l) w = peval l (z₀ + w) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    show peval (padd [c] (padd (pscale z₀ (pshift z₀ l)) (0 :: pshift z₀ l))) w = _
    rw [peval_padd, peval_padd, peval_pscale]
    show c + w * 0 + (z₀ * peval (pshift z₀ l) w + (0 + w * peval (pshift z₀ l) w)) =
      c + (z₀ + w) * peval l (z₀ + w)
    rw [ih]; grind

/-- Some coefficient is non-zero. -/
def NonZero (l : List C) : Prop := ∃ a, a ∈ l ∧ a ≠ 0

/-- A list of zeros evaluates to `0`. -/
theorem peval_of_not_nonZero {l : List C} (h : ¬ NonZero l) (z : C) : peval l z = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a = 0 := by
      apply Classical.byContradiction; intro hne; exact h ⟨a, List.mem_cons_self, hne⟩
    have hl : ¬ NonZero l := fun ⟨b, hb, hb0⟩ => h ⟨b, List.mem_cons_of_mem a hb, hb0⟩
    show a + z * peval l z = 0; rw [ih hl, ha]; grind

/-- The sum of the moduli of the coefficients. -/
noncomputable def pnorm : List C → R
  | [] => 0
  | c :: cs => cabs c + pnorm cs

/-- On the unit disc, `|p(w)| ≤ Σ |cₖ|`. -/
theorem cabs_peval_le (l : List C) {w : C} (hw : cabs w ≤ 1) : cabs (peval l w) ≤ pnorm l := by
  induction l with
  | nil => show cabs 0 ≤ 0; rw [cabs_zero]; grind
  | cons c l ih =>
    show cabs (c + w * peval l w) ≤ cabs c + pnorm l
    have := cabs_add c (w * peval l w)
    rw [cabs_mul] at this
    have := OrderedRing.mul_le_mul_of_nonneg_right hw (cabs_nonneg (peval l w))
    grind

/-- **Lowest-order term.** A polynomial with a non-zero coefficient has the form
`wʲ (b + w r(w))` with `b ≠ 0`. -/
theorem exists_lowest (t : List C) (ht : NonZero t) :
    ∃ (j : Nat) (b : C) (rest : List C), b ≠ 0 ∧ ∀ w, peval t w = w ^ j * (b + w * peval rest w) := by
  induction t with
  | nil => obtain ⟨a, ha, _⟩ := ht; cases ha
  | cons a t ih =>
    by_cases ha : a = 0
    · have ht' : NonZero t := by
        obtain ⟨b, hb, hb0⟩ := ht
        rcases List.mem_cons.1 hb with e | e
        · exact absurd (e ▸ ha) hb0
        · exact ⟨b, e, hb0⟩
      obtain ⟨j, b, rest, hb, h⟩ := ih ht'
      refine ⟨j + 1, b, rest, hb, fun w => ?_⟩
      show a + w * peval t w = w ^ j * w * (b + w * peval rest w)
      rw [h, ha]; grind
    · exact ⟨0, a, t, ha, fun w => by show a + w * peval t w = 1 * _; grind⟩

/-! ## Continuity and growth -/

/-- Polynomials are locally Lipschitz: near `z₀`, `|p(z) − p(z₀)| ≤ K |z − z₀|`. -/
theorem peval_lipschitz (l : List C) (z₀ : C) :
    ∃ K, 0 ≤ K ∧ ∀ z, cabs (z - z₀) ≤ 1 → cabs (peval l z - peval l z₀) ≤ K * cabs (z - z₀) := by
  induction l with
  | nil => exact ⟨0, Std.le_refl 0, fun z _ => by
      show cabs (0 - 0) ≤ 0 * _; rw [show (0 : C) - 0 = 0 by grind, cabs_zero]; grind⟩
  | cons c l ih =>
    obtain ⟨K, hK, h⟩ := ih
    refine ⟨cabs (peval l z₀) + K + cabs z₀ * K, by
      have := cabs_nonneg (peval l z₀); have := OrderedRing.mul_nonneg (cabs_nonneg z₀) hK; grind,
      fun z hz => ?_⟩
    show cabs (c + z * peval l z - (c + z₀ * peval l z₀)) ≤ _
    rw [show c + z * peval l z - (c + z₀ * peval l z₀) =
      (z - z₀) * peval l z + z₀ * (peval l z - peval l z₀) by grind]
    have k1 := cabs_add ((z - z₀) * peval l z) (z₀ * (peval l z - peval l z₀))
    rw [cabs_mul, cabs_mul] at k1
    have k2 := h z hz
    have k3 : cabs (peval l z) ≤ cabs (peval l z₀) + K := by
      have := cabs_add (peval l z - peval l z₀) (peval l z₀)
      rw [show peval l z - peval l z₀ + peval l z₀ = peval l z by grind] at this
      have := OrderedRing.mul_le_mul_of_nonneg_left hz hK
      grind
    have k4 := OrderedRing.mul_le_mul_of_nonneg_left k3 (cabs_nonneg (z - z₀))
    have k5 := OrderedRing.mul_le_mul_of_nonneg_left k2 (cabs_nonneg z₀)
    grind

/-- `z ↦ |p(z)|` is continuous. -/
theorem continuous_cabs_peval (l : List C) (z₀ : C) :
    ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧ ∀ z, cabs (z - z₀) < δ →
      abs (cabs (peval l z) - cabs (peval l z₀)) < ε := fun ε hε => by
  obtain ⟨K, hK, h⟩ := peval_lipschitz l z₀
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_le_both (by grind : (0 : R) < 1)
    (div_pos hε (by grind : 0 < K + 1))
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have k := h z (by grind)
  have k1 := cabs_sub_le (peval l z) (peval l z₀)
  have k2 := cabs_sub_le (peval l z₀) (peval l z)
  rw [cabs_sub_comm (peval l z₀)] at k2
  have k3 := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt hz) hK
  have k4 := OrderedRing.mul_le_mul_of_nonneg_left hδ2 (by grind : 0 ≤ K + 1)
  have e : (K + 1) * (ε / (K + 1)) = ε := by grind
  exact abs_lt.2 ⟨by grind, by grind⟩

/-- **Growth.** For a polynomial `t` with a non-zero coefficient, `|z · t(z)| → ∞`. -/
theorem growth (t : List C) (ht : NonZero t) :
    ∀ B : R, ∃ ρ, 0 ≤ ρ ∧ ∀ z, ρ ≤ cabs z → B ≤ cabs (z * peval t z) := by
  induction t with
  | nil => obtain ⟨a, ha, _⟩ := ht; cases ha
  | cons a t ih =>
    intro B
    by_cases ht' : NonZero t
    · obtain ⟨ρ, hρ, h⟩ := ih ht' (abs B + cabs a)
      refine ⟨ρ + 1, by grind, fun z hz => ?_⟩
      have k := h z (by grind)
      show B ≤ cabs (z * (a + z * peval t z))
      rw [cabs_mul]
      have k1 := cabs_add (a + z * peval t z) (-a)
      rw [show a + z * peval t z + -a = z * peval t z by grind, cabs_neg] at k1
      have hB := le_abs B
      have hX : 0 ≤ cabs (a + z * peval t z) := cabs_nonneg _
      have := OrderedRing.mul_le_mul_of_nonneg_right (by grind : (1 : R) ≤ cabs z) hX
      grind
    · have ha : a ≠ 0 := by
        obtain ⟨b, hb, hb0⟩ := ht
        rcases List.mem_cons.1 hb with e | e
        · exact e ▸ hb0
        · exact absurd ⟨b, e, hb0⟩ ht'
      have hpa := cabs_pos ha
      have hρ : 0 ≤ abs B / cabs a := by
        rw [Field.div_eq_mul_inv]
        exact OrderedRing.mul_nonneg (abs_nonneg B)
          (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hpa))
      refine ⟨abs B / cabs a, hρ, fun z hz => ?_⟩
      show B ≤ cabs (z * (a + z * peval t z))
      rw [peval_of_not_nonZero ht' z, show a + z * 0 = a by grind, cabs_mul]
      have := OrderedRing.mul_le_mul_of_nonneg_right hz (cabs_nonneg a)
      have e : abs B / cabs a * cabs a = abs B := by grind
      have := le_abs B
      grind

/-! ## d'Alembert's lemma -/

/-- `(u v)ⁿ = uⁿ vⁿ` for reals. -/
theorem real_mul_pow (u v : R) (n : Nat) : (u * v) ^ n = u ^ n * v ^ n := by
  induction n with
  | zero => show (1 : R) = 1 * 1; grind
  | succ n ih => rw [pow_succ', pow_succ', pow_succ', ih]; grind

/-- `0 < x ⇒ 0 < xⁿ`. -/
theorem pow_pos_of_pos {x : R} (hx : 0 < x) (n : Nat) : 0 < x ^ n := by
  induction n with
  | zero => show (0 : R) < 1; grind
  | succ n ih => rw [pow_succ']; exact OrderedRing.mul_pos ih hx

/-- `ofReal (x − y) = ofReal x − ofReal y`. -/
theorem ofReal_sub (x y : R) : ofReal (x - y) = ofReal x - ofReal y := by
  apply ext
  · show x - y = x + -y; grind
  · show (0 : R) = 0 + -0; grind

/-- **d'Alembert's lemma.** If `b₀ ≠ 0`, `b ≠ 0`, `k ≥ 1`, and `r` is bounded on the unit disc,
then `|b₀ + wᵏ (b + w r(w))| < |b₀|` for some `w`: a polynomial does not have a local minimum of
its modulus at a non-zero value. -/
theorem dalembert {b₀ b : C} (hb₀ : b₀ ≠ 0) (hb : b ≠ 0) {k : Nat} (hk : 1 ≤ k) (r : C → C)
    {M : R} (hr : ∀ w, cabs w ≤ 1 → cabs (r w) ≤ M) :
    ∃ w, cabs (b₀ + w ^ k * (b + w * r w)) < cabs b₀ := by
  -- A direction `ω` in which `b wᵏ` points against `b₀`: `ωᵏ = −b₀/b`.
  obtain ⟨ω, hω⟩ := exists_pow_eq (-(b₀ * b⁻¹)) hk
  have hbinv : b * b⁻¹ = 1 := Field.mul_inv_cancel hb
  have hωne : ω ≠ 0 := fun h => by
    rw [h] at hω
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : (0 : C) ^ (j + 1) = 0 := by show (0 : C) ^ j * 0 = 0; grind
    rw [this] at hω
    have : b₀ = 0 := by
      have h2 : -(b₀ * b⁻¹) * b = -b₀ := by
        have : -(b₀ * b⁻¹) * b = -(b₀ * (b * b⁻¹)) := by grind
        rw [this, hbinv]; grind
      rw [← hω] at h2; grind
    exact hb₀ this
  have hA := cabs_pos hωne
  have hβ := cabs_pos hb₀
  have hM : 0 ≤ M := Std.le_trans (cabs_nonneg _) (hr 0 (by rw [cabs_zero]; grind))
  let A := cabs ω
  let Q := A ^ (k + 1) * M
  have hQ : 0 ≤ Q := OrderedRing.mul_nonneg (pow_le_pow_left.pow_nonneg (cabs_nonneg ω) _) hM
  -- A small step `t`: `t ≤ 1`, `t A ≤ 1`, `t Q < |b₀|`.
  obtain ⟨t₁, ht₁, ht₁a, ht₁b⟩ := exists_pos_le_both (by grind : (0 : R) < 1)
    (div_pos (by grind : (0 : R) < 1) hA)
  obtain ⟨t, ht, hta, htb⟩ := exists_pos_le_both ht₁ (div_pos hβ (by grind : 0 < Q + 1))
  have htA : t * A ≤ 1 := by
    have := OrderedRing.mul_le_mul_of_nonneg_right (Std.le_trans hta ht₁b) (cabs_nonneg ω)
    have : 1 / A * A = 1 := by have : A ≠ 0 := by grind
                               grind
    grind
  have htQ : t * Q < cabs b₀ := by
    have k1 := OrderedRing.mul_le_mul_of_nonneg_right htb hQ
    have e : cabs b₀ / (Q + 1) * (Q + 1) = cabs b₀ := by grind
    have k2 := OrderedRing.mul_le_mul_of_nonneg_left (by grind : Q ≤ Q + 1)
      (Std.le_of_lt (div_pos hβ (by grind : 0 < Q + 1)))
    have k3 := OrderedRing.mul_lt_mul_of_pos_left (by grind : Q < Q + 1)
      (div_pos hβ (by grind : 0 < Q + 1))
    grind
  have ht1 : t ≤ 1 := Std.le_trans hta ht₁a
  have htk : 0 < t ^ k := pow_pos_of_pos ht k
  have htk1 : t ^ k ≤ 1 := by have := pow_le_pow_left (Std.le_of_lt ht) ht1 k; rw [one_pow] at this; exact this
  let w := ofReal t * ω
  have hw : cabs w = t * A := by show cabs (ofReal t * ω) = _; rw [cabs_mul, cabs_ofReal (Std.le_of_lt ht)]
  have hrw := hr w (by rw [hw]; exact htA)
  clear hr
  have h1tk : (0 : R) ≤ 1 - t ^ k := by grind
  refine ⟨w, ?_⟩
  -- `b₀ + wᵏ (b + w r) = (1 − tᵏ) b₀ + wᵏ⁺¹ r`.
  have hwk : w ^ k = ofReal (t ^ k) * ω ^ k := by
    show (ofReal t * ω) ^ k = _; rw [mul_pow, ofReal_pow]
  have e : b₀ + w ^ k * (b + w * r w) = ofReal (1 - t ^ k) * b₀ + w ^ k * w * r w := by
    rw [ofReal_sub, hwk, hω]
    have : ofReal 1 = 1 := rfl
    rw [this]
    have : -(b₀ * b⁻¹) * b = -b₀ := by
      have : -(b₀ * b⁻¹) * b = -(b₀ * (b * b⁻¹)) := by grind
      rw [this, hbinv]; grind
    grind
  rw [e]
  have k1 := cabs_add (ofReal (1 - t ^ k) * b₀) (w ^ k * w * r w)
  rw [cabs_mul, cabs_mul, cabs_mul, cabs_pow, hw, cabs_ofReal h1tk] at k1
  -- `(tA)ᵏ (tA) |r w| ≤ tᵏ · t Q < tᵏ |b₀|`.
  have hp : (t * A) ^ k * (t * A) * cabs (r w) ≤ t ^ k * (t * Q) := by
    have htA0 : 0 ≤ t * A := OrderedRing.mul_nonneg (Std.le_of_lt ht) (cabs_nonneg ω)
    have h0 : 0 ≤ (t * A) ^ k * (t * A) :=
      OrderedRing.mul_nonneg (pow_le_pow_left.pow_nonneg htA0 _) htA0
    have := OrderedRing.mul_le_mul_of_nonneg_left hrw h0
    have e2 : (t * A) ^ k * (t * A) * M = t ^ k * (t * Q) := by
      show (t * A) ^ k * (t * A) * M = t ^ k * (t * (A ^ (k + 1) * M))
      rw [real_mul_pow, pow_succ']; grind
    grind
  have := OrderedRing.mul_lt_mul_of_pos_left htQ htk
  grind

/-! ## The fundamental theorem -/

/-- **The fundamental theorem of algebra.** Every non-constant polynomial with complex
coefficients has a complex root: if some coefficient of `t` is non-zero, the polynomial
`c₀ + z · t(z)` (coefficient list `c₀ :: t`) vanishes somewhere. -/
theorem fta (c : C) (t : List C) (ht : NonZero t) : ∃ z, peval (c :: t) z = 0 := by
  let g : C → R := fun z => cabs (peval (c :: t) z)
  have hpev : ∀ z, peval (c :: t) z = c + z * peval t z := fun _ => rfl
  -- Far out, `|p(z)| ≥ |z t(z)| − |c|` is large.
  have hfar : ∀ B : R, ∃ ρ, 0 ≤ ρ ∧ ∀ z, ρ ≤ cabs z → B ≤ g z := fun B => by
    obtain ⟨ρ, hρ, h⟩ := growth t ht (B + cabs c)
    refine ⟨ρ, hρ, fun z hz => ?_⟩
    have k := h z hz
    have k1 := cabs_add (c + z * peval t z) (-c)
    rw [show c + z * peval t z + -c = z * peval t z by grind, cabs_neg] at k1
    show B ≤ cabs (peval (c :: t) z); rw [hpev]; grind
  obtain ⟨ρ, hρ, hρ'⟩ := hfar (g 0)
  -- The minimum on the square is a global minimum.
  obtain ⟨zs, hzs, hmin⟩ := exists_min_on_square (g := g) hρ (fun z => cabs_nonneg _)
    (fun z₀ => continuous_cabs_peval (c :: t) z₀)
  have h0 : InSq ρ 0 := ⟨by rw [zero_re, R.abs_zero]; exact hρ, by rw [zero_im, R.abs_zero]; exact hρ⟩
  have hglob : ∀ z, g zs ≤ g z := fun z => by
    by_cases hz : InSq ρ z
    · exact hmin z hz
    · have : ρ ≤ cabs z := by
        unfold InSq at hz
        have := abs_re_le_cabs z; have := abs_im_le_cabs z
        rcases (by grind : ρ < abs z.re ∨ ρ < abs z.im) with h | h <;> grind
      have := hρ' z this; have := hmin 0 h0; grind
  refine ⟨zs, ?_⟩
  apply Classical.byContradiction
  intro hne
  -- Expand `p` around `zs`: `p(zs + w) = q(w)`.
  have hq := peval_pshift zs (c :: t)
  generalize hQ : pshift zs (c :: t) = q at hq
  cases q with
  | nil =>
    have := hq 0; rw [show zs + 0 = zs by grind] at this; exact hne this.symm
  | cons b₀ tq =>
    have hb₀ : b₀ = peval (c :: t) zs := by
      have := hq 0; rw [show zs + 0 = zs by grind] at this
      rw [← this]; show b₀ = b₀ + 0 * peval tq 0; grind
    -- `q` is not constant, because `p` is not.
    have htq : NonZero tq := by
      apply Classical.byContradiction; intro hno
      obtain ⟨ρ₂, hρ₂, h₂⟩ := hfar (cabs b₀ + 1)
      have k := h₂ (ofReal ρ₂) (by rw [cabs_ofReal hρ₂]; exact Std.le_refl _)
      have := hq (ofReal ρ₂ - zs)
      rw [show zs + (ofReal ρ₂ - zs) = ofReal ρ₂ by grind] at this
      have hv : peval (b₀ :: tq) (ofReal ρ₂ - zs) = b₀ := by
        show b₀ + _ * peval tq _ = b₀; rw [peval_of_not_nonZero hno]; grind
      rw [hv] at this
      have : g (ofReal ρ₂) = cabs b₀ := by show cabs (peval (c :: t) _) = _; rw [← this]
      grind
    obtain ⟨j, b, rest, hb, hdec⟩ := exists_lowest tq htq
    obtain ⟨w, hw⟩ := dalembert (b₀ := b₀) (b := b) (k := j + 1)
      (by rw [hb₀]; exact hne) hb (by omega) (fun w => peval rest w)
      (fun w hw => cabs_peval_le rest hw)
    have := hq w
    have e : peval (b₀ :: tq) w = b₀ + w ^ (j + 1) * (b + w * peval rest w) := by
      show b₀ + w * peval tq w = _; rw [hdec]; show _ = b₀ + w ^ j * w * _; grind
    rw [e] at this
    rw [this, hb₀] at hw
    have := hglob (zs + w)
    exact absurd hw (by show ¬ (g (zs + w) < g zs); grind)

end C

end Foundations.Numbers
