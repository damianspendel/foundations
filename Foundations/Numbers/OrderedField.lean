import Foundations.Numbers.Rat

/-!
# Ordered fields in general

So far we have built *particular* number systems. To ask whether the real numbers are unique
we must step back and speak about an *arbitrary* ordered field `K` — any structure satisfying the
ordered-field axioms, however it was constructed. This file collects the general facts we need,
stated for every ordered field at once (formally: every type carrying Lean's `Field`,
`IsLinearOrder` and `OrderedRing` structures, which our `Q` and `R` both do):

* the **absolute value** `|x|` and its basic laws (triangle inequality, multiplicativity);
* the **canonical copy of ℚ inside `K`**: every ordered field contains the rationals, via
  `n/d ↦ (n·1)/(d·1)`; this map preserves `+`, `×` and the order;
* the **Archimedean property** (every element is below some natural number), and its two
  consequences: integer parts (*floors*) exist, and the rationals are **dense** — between any two
  elements of `K` lies (the copy of) a rational.

Density is the bridge to categoricity: an element of an Archimedean ordered field is pinned down
by *which rationals lie below it*.
-/

namespace Foundations.Numbers

open Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

namespace OF

variable {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- A least element of a nonempty set of natural numbers (a convenient form of the
well-ordering principle `N.well_ordering`). -/
theorem nat_least (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  apply Classical.byContradiction
  intro hno
  have : ∀ n, ∀ m, m ≤ n → ¬ P m := by
    intro n
    induction n with
    | zero => intro m hm hP; exact hno ⟨m, hP, fun k hk => by omega⟩
    | succ n ih =>
      intro m hm hP
      by_cases h' : m ≤ n
      · exact ih m h' hP
      · exact hno ⟨m, hP, fun k hk => ih k (by omega)⟩
  obtain ⟨n, hn⟩ := h
  exact this n n (Nat.le_refl n) hn

/-! ## Absolute value -/

/-- The absolute value in an ordered field. -/
noncomputable def abs (x : K) : K :=
  open Classical in if 0 ≤ x then x else -x

/-- The two cases of the absolute value. -/
theorem abs_cases (x : K) : (0 ≤ x ∧ abs x = x) ∨ (x < 0 ∧ abs x = -x) := by
  by_cases h : 0 ≤ x
  · left; exact ⟨h, by unfold abs; exact ite_eq_left h⟩
  · right; exact ⟨by grind, by unfold abs; exact ite_eq_right h⟩

/-- Absolute values are non-negative. -/
theorem abs_nonneg (x : K) : 0 ≤ abs x := by rcases abs_cases x with h | h <;> grind

/-- `|x| < e ↔ -e < x < e`. -/
theorem abs_lt {x e : K} : abs x < e ↔ -e < x ∧ x < e := by
  rcases abs_cases x with h | h <;> grind

/-- `|x| ≤ e ↔ -e ≤ x ≤ e`. -/
theorem abs_le {x e : K} : abs x ≤ e ↔ -e ≤ x ∧ x ≤ e := by
  rcases abs_cases x with h | h <;> grind

/-- `x ≤ |x|` and `-x ≤ |x|`. -/
theorem le_abs (x : K) : x ≤ abs x ∧ -x ≤ abs x := by rcases abs_cases x with h | h <;> grind

/-- `|x − y| = |y − x|`. -/
theorem abs_sub_comm (x y : K) : abs (x - y) = abs (y - x) := by
  rcases abs_cases (x - y) with h | h <;> rcases abs_cases (y - x) with h' | h' <;> grind

/-- **Triangle inequality** in an ordered field. -/
theorem abs_add (x y : K) : abs (x + y) ≤ abs x + abs y := by
  rcases abs_cases x with h | h <;> rcases abs_cases y with h' | h' <;>
    rcases abs_cases (x + y) with h'' | h'' <;> grind

/-- The absolute value is multiplicative. -/
theorem abs_mul (x y : K) : abs (x * y) = abs x * abs y := by
  rcases abs_cases x with ⟨hx, ex⟩ | ⟨hx, ex⟩ <;> rcases abs_cases y with ⟨hy, ey⟩ | ⟨hy, ey⟩ <;>
    rcases abs_cases (x * y) with ⟨hxy, exy⟩ | ⟨hxy, exy⟩ <;> rw [ex, ey, exy]
  all_goals first
    | grind
    | (have := OrderedRing.mul_nonneg hx hy; grind)
    | (have := OrderedRing.mul_nonneg hx (by grind : 0 ≤ -y); grind)
    | (have := OrderedRing.mul_nonneg (by grind : 0 ≤ -x) hy; grind)
    | (have := OrderedRing.mul_nonneg (by grind : 0 ≤ -x) (by grind : 0 ≤ -y); grind)
    | (have := OrderedRing.mul_pos (by grind : 0 < -x) (by grind : 0 < -y); grind)

/-- Product estimate: `|x| ≤ A`, `A > 0`, `|y| < δ` give `|x y| < A δ`. -/
theorem abs_mul_lt {x y A δ : K} (hx : abs x ≤ A) (hA : 0 < A) (hy : abs y < δ) :
    abs (x * y) < A * δ := by
  rw [abs_mul]
  have h1 := OrderedRing.mul_le_mul_of_nonneg_right hx (abs_nonneg y)
  have h2 := OrderedRing.mul_lt_mul_of_pos_left hy hA
  grind

/-- The quotient of positive elements is positive. -/
theorem div_pos {a b : K} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Field.div_eq_mul_inv]
  exact OrderedRing.mul_pos ha (Field.IsOrdered.inv_pos_iff.2 hb)

/-! ## The rationals inside an ordered field -/

/-- The integer cast into an ordered field preserves and reflects `<`. -/
theorem intCast_lt {a b : Int} : (a : K) < (b : K) ↔ a < b :=
  ⟨OrderedRing.lt_of_intCast_lt_intCast a b, fun h => by
    have := OrderedRing.pos_intCast_of_pos (R := K) (b - a) (by omega); grind⟩

/-- Positive integers stay positive in `K`. -/
theorem intCast_pos {a : Int} (h : 0 < a) : (0 : K) < (a : K) := by
  have := (intCast_lt (K := K) (a := 0) (b := a)).2 h; grind

/-- **The canonical embedding of ℚ into an ordered field**: the fraction `n/d` goes to
`(n·1)/(d·1)`. It does not depend on the representing fraction. -/
def ofRat : Q → K :=
  Quotient.lift (fun p : Frac => (p.num : K) / (p.den : K)) (fun p q h => by
    have h : p.num * q.den = q.num * p.den := h
    have hp := intCast_pos (K := K) p.den_pos
    have hq := intCast_pos (K := K) q.den_pos
    have := congrArg (fun z : Int => (z : K)) h
    grind)

/-- The embedding computed on a fraction. -/
theorem ofRat_mk (n d : Int) (hd : 0 < d) : ofRat (K := K) (Q.mk n d hd) = (n : K) / (d : K) :=
  rfl

/-- The embedding preserves addition. -/
theorem ofRat_add (p q : Q) : ofRat (K := K) (p + q) = ofRat p + ofRat q := by
  induction p using Q.ind with | h a b hb => ?_
  induction q using Q.ind with | h c d hd => ?_
  have := intCast_pos (K := K) hb; have := intCast_pos (K := K) hd
  simp only [Q.mk_add, ofRat_mk]; grind

/-- The embedding preserves multiplication. -/
theorem ofRat_mul (p q : Q) : ofRat (K := K) (p * q) = ofRat p * ofRat q := by
  induction p using Q.ind with | h a b hb => ?_
  induction q using Q.ind with | h c d hd => ?_
  have := intCast_pos (K := K) hb; have := intCast_pos (K := K) hd
  simp only [Q.mk_mul, ofRat_mk]; grind

/-- The embedding preserves negation. -/
theorem ofRat_neg (p : Q) : ofRat (K := K) (-p) = -ofRat p := by
  induction p using Q.ind with | h a b hb => ?_
  have := intCast_pos (K := K) hb
  simp only [Q.mk_neg, ofRat_mk]; grind

/-- The embedding preserves subtraction. -/
theorem ofRat_sub (p q : Q) : ofRat (K := K) (p - q) = ofRat p - ofRat q := by
  have : p - q = p + -q := rfl
  rw [this, ofRat_add, ofRat_neg]; grind

/-- The embedding sends natural numbers to natural numbers. -/
theorem ofRat_natCast (n : Nat) : ofRat (K := K) (n : Q) = (n : K) := by
  rw [Q.natCast_def, ofRat_mk, Ring.intCast_natCast]; grind

/-- The embedding sends numerals to numerals. -/
theorem ofRat_ofNat (n : Nat) : ofRat (K := K) (OfNat.ofNat n) = (OfNat.ofNat n : K) := by
  rw [show (OfNat.ofNat n : Q) = (n : Q) from rfl, ofRat_natCast, Semiring.ofNat_eq_natCast]

/-- The embedding preserves and reflects `<`. -/
theorem ofRat_lt {p q : Q} : ofRat (K := K) p < ofRat q ↔ p < q := by
  induction p using Q.ind with | h a b hb => ?_
  induction q using Q.ind with | h c d hd => ?_
  rw [Q.mk_lt, ofRat_mk, ofRat_mk, ← intCast_lt (K := K)]
  have hb' := intCast_pos (K := K) hb
  have hd' := intCast_pos (K := K) hd
  have hbd := OrderedRing.mul_pos hb' hd'
  rw [← Field.IsOrdered.mul_lt_mul_iff_of_pos_right hbd]
  have e1 : (a : K) / (b : K) * ((b : K) * (d : K)) = ((a * d : Int) : K) := by grind
  have e2 : (c : K) / (d : K) * ((b : K) * (d : K)) = ((c * b : Int) : K) := by grind
  rw [e1, e2]

/-- The embedding preserves and reflects `≤`. -/
theorem ofRat_le {p q : Q} : ofRat (K := K) p ≤ ofRat q ↔ p ≤ q := by
  have := ofRat_lt (K := K) (p := q) (q := p)
  constructor <;> intro h <;> grind

/-- The embedding is injective. -/
theorem ofRat_inj {p q : Q} (h : ofRat (K := K) p = ofRat q) : p = q := by
  have h1 := (ofRat_le (K := K)).1 (by grind : ofRat (K := K) p ≤ ofRat q)
  have h2 := (ofRat_le (K := K)).1 (by grind : ofRat (K := K) q ≤ ofRat p)
  exact Q.le_antisymm h1 h2

/-- The embedding preserves zero. -/
theorem ofRat_zero : ofRat (K := K) 0 = 0 := by
  have := ofRat_ofNat (K := K) 0; grind

/-- The embedding preserves one. -/
theorem ofRat_one : ofRat (K := K) 1 = 1 := by
  have := ofRat_ofNat (K := K) 1; grind

/-! ## The Archimedean property and density of ℚ -/

/-- An ordered field is **Archimedean** if every element is below some natural number. -/
def Archimedean (K : Type) [Field K] [LE K] [LT K] : Prop := ∀ x : K, ∃ n : Nat, x < (n : K)

/-- **Integer parts.** In an Archimedean field every `x` lies in `[m, m + 1)` for some integer
`m`. -/
theorem exists_floor (hA : Archimedean K) (x : K) : ∃ m : Int, (m : K) ≤ x ∧ x < (m : K) + 1 := by
  obtain ⟨N₁, h₁⟩ := hA x
  obtain ⟨N₂, h₂⟩ := hA (-x)
  let N := N₁ + N₂
  have hN1 : x < (N : K) := by have : (N₁ : K) ≤ (N : K) := by grind
                               grind
  have hN2 : -x < (N : K) := by have : (N₂ : K) ≤ (N : K) := by grind
                                grind
  obtain ⟨k, hk, hmin⟩ := nat_least (fun k => x < (k : K) - (N : K)) ⟨2 * N, by grind⟩
  cases k with
  | zero => exfalso; grind
  | succ j =>
    have hj := hmin j (by omega)
    have e : (((j : Int) - (N : Int) : Int) : K) = (j : K) - (N : K) := by
      rw [Ring.intCast_sub, Ring.intCast_natCast, Ring.intCast_natCast]
    refine ⟨(j : Int) - (N : Int), ?_, ?_⟩ <;> rw [e] <;> grind

/-- **Density of the rationals.** In an Archimedean ordered field, between any two elements
lies a rational. -/
theorem exists_rat_between (hA : Archimedean K) {a b : K} (h : a < b) :
    ∃ q : Q, a < ofRat q ∧ ofRat q < b := by
  obtain ⟨n, hn⟩ := hA (1 / (b - a))
  have hba : 0 < b - a := by grind
  have h1 : 1 < (n : K) * (b - a) := by
    rw [Field.div_eq_mul_inv] at hn
    exact (Field.IsOrdered.mul_inv_lt_iff_lt_mul _ _ hba).1 hn
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exfalso; grind
    · exact h0
  have hnK : (0 : K) < (n : K) := OrderedRing.pos_natCast_of_pos n hnpos
  have e := Ring.intCast_natCast (α := K) n
  obtain ⟨m, hm1, hm2⟩ := exists_floor hA ((n : K) * a)
  refine ⟨Q.mk (m + 1) n (by omega), ?_, ?_⟩
  · rw [ofRat_mk]
    rw [← Field.IsOrdered.mul_lt_mul_iff_of_pos_right hnK]
    have : ((m + 1 : Int) : K) / ((n : Int) : K) * (n : K) = (m : K) + 1 := by grind
    rw [this]; grind
  · rw [ofRat_mk]
    rw [← Field.IsOrdered.mul_lt_mul_iff_of_pos_right hnK]
    have : ((m + 1 : Int) : K) / ((n : Int) : K) * (n : K) = (m : K) + 1 := by grind
    rw [this]; grind

/-- The **least upper bound property** of an ordered type: every nonempty set that is bounded
above has a least upper bound. -/
def LUBProperty (K : Type) [LE K] : Prop :=
  ∀ S : K → Prop, (∃ x, S x) → (∃ M, ∀ x, S x → x ≤ M) →
    ∃ L, (∀ x, S x → x ≤ L) ∧ ∀ M, (∀ x, S x → x ≤ M) → L ≤ M

/-- **Completeness implies the Archimedean property.** In an ordered field with the least upper
bound property, the natural numbers are unbounded. -/
theorem archimedean_of_lub (hL : LUBProperty K) : Archimedean K := by
  intro x
  apply Classical.byContradiction
  intro hno
  have hbd : ∀ n : Nat, (n : K) ≤ x := fun n => by
    apply Classical.byContradiction; intro h; exact hno ⟨n, by grind⟩
  obtain ⟨L, hL1, hL2⟩ := hL (fun y => ∃ n : Nat, y = n) ⟨_, 0, rfl⟩
    ⟨x, fun y ⟨n, hn⟩ => hn ▸ hbd n⟩
  -- `L − 1` is not an upper bound, so some `n > L − 1`; then `n + 1 > L`, a contradiction.
  have : ¬ ∀ y : K, (∃ n : Nat, y = n) → y ≤ L - 1 := fun h => by have := hL2 _ h; grind
  apply this
  intro y ⟨n, hn⟩
  have := hL1 ((n + 1 : Nat) : K) ⟨n + 1, rfl⟩
  rw [hn]; grind

end OF

end Foundations.Numbers
