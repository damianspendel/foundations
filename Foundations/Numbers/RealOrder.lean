import Foundations.Numbers.Real

/-!
# The order on the reals, inverses, and the ordered field ℝ

When is a real number *positive*? A Cauchy sequence may wobble, so we cannot just ask that its
terms be positive. The right notion is that the sequence is **eventually bounded away from zero
from above**: from some point on, all its terms exceed some fixed positive rational `ε`. This
does not depend on the representative, so it defines positivity of real numbers, and we set
`x < y` iff `y − x` is positive.

The key fact is **trichotomy**: every real is positive, zero, or negative. Its proof uses
classical logic in an essential way — given a Cauchy sequence, we cannot in general *decide* in
finitely many steps whether it converges to `0` (a famous point of Brouwer's intuitionist
critique). Classically, though, if a sequence does *not* tend to zero then it is eventually
bounded away from zero, and so is eventually positive or eventually negative.

Next, inverses. If `x ≠ 0` its representing sequence is eventually bounded away from zero, so
inverting it term by term gives again a Cauchy sequence, which represents `1/x`. We then define
`x⁻¹` as "the" `y` with `x · y = 1` (chosen by the axiom of choice, the junk value `0⁻¹ = 0`
otherwise) — this avoids any need to check well-definedness by hand.

The upshot is that **ℝ is an ordered field**, registered with Lean's automation. We also prove
the **Archimedean property** of ℝ and a few lemmas relating reals and the rationals inside them
(the embedding `ofQ` preserves order; every positive real exceeds a positive rational; a Cauchy
sequence is approximated by its own terms), which prepare the proof of completeness.
-/

namespace Foundations.Numbers

open Lean.Grind

namespace CauSeq

open Q

/-- A Cauchy sequence is *positive* if its terms are eventually bounded below by some positive
rational `ε`. -/
def Pos (a : CauSeq) : Prop := ∃ ε : Q, 0 < ε ∧ ∃ N : Nat, ∀ n, N ≤ n → ε ≤ a n

/-- Positivity is invariant under equivalence. -/
theorem pos_of_equiv {a b : CauSeq} (h : a ≈ b) (ha : Pos a) : Pos b := by
  obtain ⟨ε, hε, N, hN⟩ := ha
  obtain ⟨M, hM⟩ := h (ε / 2) (by grind)
  refine ⟨ε / 2, by grind, max N M, fun n hn => ?_⟩
  have h1 := hN n (by omega)
  have h2 := abs_lt.1 (hM n (by omega))
  grind

end CauSeq

namespace R

open CauSeq Q

/-- A real number is *positive* if some (equivalently, every) representing Cauchy sequence is
eventually bounded below by a positive rational. -/
def Pos : R → Prop :=
  Quotient.lift CauSeq.Pos
    (fun _ _ h => propext ⟨pos_of_equiv h, pos_of_equiv (CauSeq.equiv_symm h)⟩)

/-- Positivity of a real, computed on a representing sequence. -/
theorem pos_mk (a : CauSeq) : Pos (mk a) ↔ CauSeq.Pos a := Iff.rfl

/-- The sum of positive reals is positive. -/
theorem pos_add {x y : R} : Pos x → Pos y → Pos (x + y) := by
  induction x using ind with | h a => ?_
  induction y using ind with | h b => ?_
  rintro ⟨ε₁, h₁, N₁, hN₁⟩ ⟨ε₂, h₂, N₂, hN₂⟩
  refine ⟨ε₁ + ε₂, by grind, max N₁ N₂, fun n hn => ?_⟩
  have := hN₁ n (by omega); have := hN₂ n (by omega)
  simp only [add_apply]; grind

/-- The product of positive reals is positive. -/
theorem pos_mul {x y : R} : Pos x → Pos y → Pos (x * y) := by
  induction x using ind with | h a => ?_
  induction y using ind with | h b => ?_
  rintro ⟨ε₁, h₁, N₁, hN₁⟩ ⟨ε₂, h₂, N₂, hN₂⟩
  refine ⟨ε₁ * ε₂, OrderedRing.mul_pos h₁ h₂, max N₁ N₂, fun n hn => ?_⟩
  have ha := hN₁ n (by omega); have hb := hN₂ n (by omega)
  simp only [mul_apply]
  have k1 := OrderedRing.mul_le_mul_of_nonneg_right ha (Q.le_of_lt' h₂)
  have k2 := OrderedRing.mul_le_mul_of_nonneg_left hb (by grind : (0 : Q) ≤ a n)
  grind

/-- Zero is not positive. -/
theorem not_pos_zero : ¬ Pos 0 := by
  rintro ⟨ε, hε, N, hN⟩
  have := hN N (Nat.le_refl _)
  simp only [const_apply] at this; grind

/-- A real and its negative are not both positive. -/
theorem not_pos_neg {x : R} : Pos x → ¬ Pos (-x) := by
  induction x using ind with | h a => ?_
  rintro ⟨ε₁, h₁, N₁, hN₁⟩ ⟨ε₂, h₂, N₂, hN₂⟩
  have := hN₁ (max N₁ N₂) (by omega); have := hN₂ (max N₁ N₂) (by omega)
  simp only [neg_apply] at *; grind

/-- **Trichotomy.** Every real number is positive, zero, or negative. (This uses classical
logic: it cannot be decided effectively.) -/
theorem trichotomy (x : R) : Pos x ∨ x = 0 ∨ Pos (-x) := by
  induction x using ind with | h a => ?_
  by_cases h0 : mk a = 0
  · exact Or.inr (Or.inl h0)
  -- If `a` does not tend to `0`, it is frequently at least `ε` away from `0`.
  have hfreq : ∃ ε : Q, 0 < ε ∧ ∀ N, ∃ n, N ≤ n ∧ ε ≤ abs (a n) := by
    apply Classical.byContradiction
    intro hne
    apply h0
    rw [zero_def, mk_eq_mk]
    intro ε hε
    apply Classical.byContradiction
    intro hN
    apply hne
    refine ⟨ε, hε, fun N => ?_⟩
    apply Classical.byContradiction
    intro hn
    apply hN
    refine ⟨N, fun n hn' => ?_⟩
    have h1 : ¬ ε ≤ abs (a n) := fun h => hn ⟨n, hn', h⟩
    have e : a n - const 0 n = a n := by simp only [const_apply]; grind
    rw [e]; grind
  obtain ⟨ε, hε, hfreq⟩ := hfreq
  obtain ⟨N, hN⟩ := a.isCauchy (ε / 2) (by grind)
  obtain ⟨n, hn, hεn⟩ := hfreq N
  rcases abs_cases (a n) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨ε / 2, by grind, N, fun m hm => ?_⟩
    have := abs_lt.1 (hN m n hm hn); grind
  · right; right
    refine ⟨ε / 2, by grind, N, fun m hm => ?_⟩
    have := abs_lt.1 (hN m n hm hn)
    simp only [neg_apply]; grind

/-! ## The order -/

/-- `x < y` iff `y − x` is positive. -/
instance : LT R := ⟨fun x y => Pos (y - x)⟩
/-- `x ≤ y` iff `x < y` or `x = y`. -/
instance : LE R := ⟨fun x y => x < y ∨ x = y⟩

/-- Unfolding the strict order: `x < y` iff `y − x` is positive. -/
theorem lt_def {x y : R} : x < y ↔ Pos (y - x) := Iff.rfl
/-- Unfolding the order: `x ≤ y` iff `x < y` or `x = y`. -/
theorem le_def {x y : R} : x ≤ y ↔ x < y ∨ x = y := Iff.rfl

/-- The strict order is irreflexive. -/
theorem lt_irrefl (x : R) : ¬ x < x := by
  rw [lt_def]
  have : x - x = 0 := by grind
  rw [this]; exact not_pos_zero

/-- The strict order is transitive. -/
theorem lt_trans {x y z : R} (h₁ : x < y) (h₂ : y < z) : x < z := by
  have := pos_add h₂ h₁
  have e : z - y + (y - x) = z - x := by grind
  rw [e] at this; exact this

/-- The strict order is asymmetric. -/
theorem lt_asymm {x y : R} (h₁ : x < y) : ¬ y < x := by
  intro h₂
  have e : x - y = -(y - x) := by grind
  rw [lt_def, e] at h₂
  exact not_pos_neg h₁ h₂

/-- Any two reals are comparable: `x < y`, `x = y` or `y < x`. -/
theorem lt_trichotomy (x y : R) : x < y ∨ x = y ∨ y < x := by
  rcases trichotomy (y - x) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by grind))
  · right; right
    have e : -(y - x) = x - y := by grind
    rw [lt_def, ← e]; exact h

/-- The strict order is compatible with addition. -/
theorem add_lt_add_iff {a b : R} (c : R) : a < b ↔ a + c < b + c := by
  simp only [lt_def]
  have e : b + c - (a + c) = b - a := by grind
  rw [e]

/-- `≤` on the reals is a linear order (registered for automation). -/
instance : Std.IsLinearOrder R where
  le_refl _ := Or.inr rfl
  le_trans _ _ _ h₁ h₂ := by
    rcases h₁ with h₁ | rfl
    · rcases h₂ with h₂ | rfl
      · exact Or.inl (lt_trans h₁ h₂)
      · exact Or.inl h₁
    · exact h₂
  le_antisymm _ _ h₁ h₂ := by
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · exact absurd h₂ (lt_asymm h₁)
      · exact h₂.symm
    · exact h₁
  le_total x y := by
    rcases lt_trichotomy x y with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- `<` on the reals agrees with `≤` (registered for automation). -/
instance : Std.LawfulOrderLT R where
  lt_iff x y := by
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (h' | h')
      · exact lt_asymm h h'
      · subst h'; exact lt_irrefl _ h
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd (Or.inr h.symm) h'

/-- The order on the reals is compatible with addition (registered for automation). -/
instance : OrderedAdd R where
  add_le_left_iff c := by
    simp only [le_def]
    rw [← add_lt_add_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by rw [h])
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by grind)

/-- `0 < 1` in the reals. -/
theorem zero_lt_one : (0 : R) < 1 :=
  ⟨1, by grind, 0, fun n _ => by simp only [add_apply, neg_apply, const_apply]; grind⟩

/-- Multiplying a strict inequality by a positive element preserves it. -/
theorem mul_lt_mul_of_pos_left {a b c : R} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  rw [lt_def] at *
  have := pos_mul hc h
  have e : (c - 0) * (b - a) = c * b - c * a := by grind
  rw [e] at this; exact this

/-- **ℝ is an ordered ring.** Registered with Lean's automation. -/
instance instOrderedRing : OrderedRing R where
  zero_lt_one := zero_lt_one
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right {a b c} h hc := by
    have := mul_lt_mul_of_pos_left h hc
    rwa [mul_comm c a, mul_comm c b] at this

/-! ## Inverses -/

/-- Zero and one are different reals: the structure is not trivial. -/
theorem zero_ne_one : (0 : R) ≠ 1 := by
  intro h
  obtain ⟨N, hN⟩ := mk_eq_mk.1 h (1 / 2) (by grind)
  have := abs_lt.1 (hN N (Nat.le_refl _))
  simp only [const_apply] at this; grind

/-- **Non-zero reals have inverses.** If `x ≠ 0` there is `y` with `x · y = 1`: invert a
representing sequence term by term (it is eventually bounded away from zero). -/
theorem exists_inv {x : R} (hx : x ≠ 0) : ∃ y, x * y = 1 := by
  induction x using ind with | h a => ?_
  have hpos : ∃ δ : Q, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ ≤ abs (a n) := by
    rcases trichotomy (mk a) with h | h | h
    · obtain ⟨δ, hδ, N, hN⟩ := h
      exact ⟨δ, hδ, N, fun n hn => by have := hN n hn; have := (le_abs (a n)).1; grind⟩
    · exact absurd h hx
    · obtain ⟨δ, hδ, N, hN⟩ := h
      exact ⟨δ, hδ, N, fun n hn => by
        have := hN n hn; simp only [neg_apply] at this
        have := (le_abs (a n)).2; grind⟩
  obtain ⟨δ, hδ, N, hN⟩ := hpos
  have hne : ∀ n, N ≤ n → a n ≠ 0 := fun n hn h => by
    have := hN n hn; rw [h, abs_zero] at this; grind
  let b : CauSeq := ⟨fun n => (a n)⁻¹, by
    intro ε hε
    have hδδ : 0 < δ * δ := OrderedRing.mul_pos hδ hδ
    obtain ⟨M, hM⟩ := a.isCauchy (ε * (δ * δ)) (OrderedRing.mul_pos hε hδδ)
    refine ⟨max N M, fun m n hm hn => ?_⟩
    have hm' := hN m (by omega)
    have hn' := hN n (by omega)
    have am := hne m (by omega)
    have an := hne n (by omega)
    have h4 := hM n m (by omega) (by omega)
    have h3 : abs ((a m)⁻¹ - (a n)⁻¹) * (abs (a m) * abs (a n)) = abs (a n - a m) := by
      rw [← abs_mul, ← abs_mul]; congr 1; grind
    have h1 : δ * δ ≤ abs (a m) * abs (a n) := by
      have := OrderedRing.mul_le_mul_of_nonneg_right hm' (Q.le_of_lt' hδ)
      have := OrderedRing.mul_le_mul_of_nonneg_left hn' (abs_nonneg (a m))
      grind
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left h1 (abs_nonneg ((a m)⁻¹ - (a n)⁻¹))
    have : abs ((a m)⁻¹ - (a n)⁻¹) * (δ * δ) < ε * (δ * δ) := by grind
    exact (Field.IsOrdered.mul_lt_mul_iff_of_pos_right hδδ).1 this⟩
  refine ⟨mk b, ?_⟩
  rw [one_def, mk_mul, mk_eq_mk]
  intro ε hε
  refine ⟨N, fun n hn => ?_⟩
  have := hne n hn
  have e : CauSeq.mul a b n - const 1 n = 0 := by
    simp only [mul_apply, const_apply, b]; grind
  rw [e, abs_zero]; exact hε

/-- The inverse of a real number: the `y` with `x · y = 1` if there is one (chosen by the axiom
of choice), and `0` otherwise (that is, for `x = 0`). -/
noncomputable def inv (x : R) : R :=
  open Classical in
  if h : ∃ y, x * y = 1 then Classical.choose h else 0

/-- Inversion on the reals. -/
noncomputable instance : Inv R := ⟨inv⟩
/-- Division on the reals: `x / y = x · y⁻¹`. -/
noncomputable instance : Div R := ⟨fun x y => x * inv y⟩

/-- A non-zero real times its inverse is one. -/
theorem mul_inv_cancel {x : R} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  have h := exists_inv hx
  show x * inv x = 1
  unfold inv; rw [dite_eq_left h]; exact Classical.choose_spec h

/-- The junk-value convention: the inverse of zero is zero. -/
theorem inv_zero : (0 : R)⁻¹ = 0 := by
  show inv 0 = 0
  unfold inv
  rw [dite_eq_right]
  rintro ⟨y, hy⟩
  rw [zero_mul] at hy; exact zero_ne_one hy

/-- Inversion is an involution: `(x⁻¹)⁻¹ = x`. -/
theorem inv_inv (x : R) : x⁻¹⁻¹ = x := by
  by_cases hx : x = 0
  · rw [hx, inv_zero, inv_zero]
  · have h1 := mul_inv_cancel hx
    have hx' : x⁻¹ ≠ 0 := by
      intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
    have h2 := mul_inv_cancel hx'
    calc x⁻¹⁻¹ = (x * x⁻¹) * x⁻¹⁻¹ := by rw [h1, one_mul]
      _ = x * (x⁻¹ * x⁻¹⁻¹) := mul_assoc _ _ _
      _ = x := by rw [h2, mul_one]

/-- The inverse of one is one. -/
theorem inv_one : (1 : R)⁻¹ = 1 := by
  have h := mul_inv_cancel (Ne.symm zero_ne_one)
  rw [one_mul] at h; exact h

/-- Integer powers. -/
noncomputable def zpow (x : R) : Int → R
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

/-- Powers on the reals. -/
noncomputable instance : HPow R Int R := ⟨zpow⟩

/-- **ℝ is a field.** Registered with Lean's automation as a `Lean.Grind.Field`. -/
noncomputable instance instField : Field R :=
  { instCommRing with
    inv := inv
    div := fun x y => x * inv y
    div_eq_mul_inv := fun _ _ => rfl
    zero_ne_one := zero_ne_one
    inv_zero := inv_zero
    mul_inv_cancel := mul_inv_cancel
    zpow_zero := fun _ => rfl
    zpow_succ := fun _ _ => rfl
    zpow_neg := fun a n => by
      cases n with
      | ofNat n =>
        cases n with
        | zero => show (1 : R) = 1⁻¹; rw [inv_one]
        | succ n => rfl
      | negSucc n => show a ^ (n + 1) = ((a ^ (n + 1))⁻¹)⁻¹; rw [inv_inv] }

/-- **ℝ is an ordered field.** The field laws hold, every non-zero real has an inverse, and `≤`
is a linear order compatible with addition and with multiplication by positive reals. -/
theorem ordered_field :
    (∀ x y z : R, x + y + z = x + (y + z)) ∧ (∀ x y : R, x + y = y + x) ∧
    (∀ x : R, x + 0 = x) ∧ (∀ x : R, -x + x = 0) ∧
    (∀ x y z : R, x * y * z = x * (y * z)) ∧ (∀ x y : R, x * y = y * x) ∧
    (∀ x : R, x * 1 = x) ∧ (∀ x y z : R, x * (y + z) = x * y + x * z) ∧ (0 : R) ≠ 1 ∧
    (∀ x : R, x ≠ 0 → x * x⁻¹ = 1) ∧
    (∀ x y z : R, x ≤ y → y ≤ z → x ≤ z) ∧ (∀ x y : R, x ≤ y → y ≤ x → x = y) ∧
    (∀ x y : R, x ≤ y ∨ y ≤ x) ∧ (∀ x y z : R, x ≤ y → x + z ≤ y + z) ∧
    (∀ x y z : R, x < y → 0 < z → z * x < z * y) :=
  ⟨add_assoc, add_comm, add_zero, neg_add_cancel, mul_assoc, mul_comm, mul_one, left_distrib,
    zero_ne_one, fun _ => mul_inv_cancel, fun _ _ _ => Std.IsPreorder.le_trans _ _ _,
    fun _ _ => Std.IsPartialOrder.le_antisymm _ _, Std.IsLinearPreorder.le_total,
    fun _ _ z => (OrderedAdd.add_le_left_iff z).1, fun _ _ _ => mul_lt_mul_of_pos_left⟩

/-! ## Rationals inside the reals -/

/-- The embedding `ofQ` preserves and reflects strict order. -/
theorem ofQ_lt {p q : Q} : ofQ p < ofQ q ↔ p < q := by
  constructor
  · rintro ⟨ε, hε, N, hN⟩
    have := hN N (Nat.le_refl _)
    simp only [add_apply, neg_apply, const_apply] at this; grind
  · intro h
    exact ⟨q - p, by grind, 0, fun n _ => by
      simp only [add_apply, neg_apply, const_apply]; grind⟩

/-- The embedding `ofQ` preserves and reflects order. -/
theorem ofQ_le {p q : Q} : ofQ p ≤ ofQ q ↔ p ≤ q := by
  have := (@ofQ_lt q p)
  constructor
  · intro h; grind
  · intro h; grind

/-- If a Cauchy sequence is eventually below another, the corresponding reals are ordered. -/
theorem le_of_eventually_le {a b : CauSeq} (h : ∃ N, ∀ n, N ≤ n → a n ≤ b n) : mk a ≤ mk b := by
  rcases lt_trichotomy (mk a) (mk b) with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    obtain ⟨ε, hε, M, hM⟩ := h1
    obtain ⟨N, hN⟩ := h
    have := hM (max N M) (by omega)
    have := hN (max N M) (by omega)
    simp only [add_apply, neg_apply] at *; grind

/-- A real number is positive iff it is at least some positive rational. -/
theorem pos_iff_rat {x : R} : 0 < x ↔ ∃ δ : Q, 0 < δ ∧ ofQ δ ≤ x := by
  constructor
  · induction x using ind with | h a => ?_
    rintro ⟨ε, hε, N, hN⟩
    refine ⟨ε, hε, le_of_eventually_le ⟨N, fun n hn => ?_⟩⟩
    have := hN n hn
    simp only [add_apply, neg_apply, const_apply] at *; grind
  · rintro ⟨δ, hδ, h⟩
    have := ofQ_lt.2 hδ
    have e : ofQ 0 = 0 := rfl
    rw [e] at this
    grind

/-- **Approximation.** A Cauchy sequence approximates the real number it defines: for every
rational `ε > 0`, eventually `aₙ − ε ≤ [a] ≤ aₙ + ε`. -/
theorem approx (a : CauSeq) {ε : Q} (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → ofQ (a n) - ofQ ε ≤ mk a ∧ mk a ≤ ofQ (a n) + ofQ ε := by
  obtain ⟨N, hN⟩ := a.isCauchy ε hε
  refine ⟨N, fun n hn => ⟨?_, ?_⟩⟩
  · rw [← ofQ_sub]
    exact le_of_eventually_le ⟨N, fun k hk => by
      have := abs_lt.1 (hN k n hk hn); simp only [const_apply]; grind⟩
  · rw [← ofQ_add]
    exact le_of_eventually_le ⟨N, fun k hk => by
      have := abs_lt.1 (hN k n hk hn); simp only [const_apply]; grind⟩

/-- **Archimedean property of ℝ.** Every real number is smaller than some natural number. -/
theorem archimedean (x : R) : ∃ n : Nat, x < (n : R) := by
  induction x using ind with | h a => ?_
  obtain ⟨B, hB, hB'⟩ := a.bounded
  obtain ⟨n, hn⟩ := Q.archimedean B
  refine ⟨n, n - B, by grind, 0, fun k _ => ?_⟩
  have := (abs_lt.1 (hB' k))
  show (n : Q) - B ≤ (n : Q) + -a k
  grind

end R

end Foundations.Numbers
