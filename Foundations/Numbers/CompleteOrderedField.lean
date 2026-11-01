import Foundations.Numbers.OrderedField
import Foundations.Numbers.Uncountable

/-!
# Complete ordered fields, and why "the" real numbers are unique

We built the reals as classes of Cauchy sequences. Dedekind built them as *cuts* of rationals;
others use infinite decimals, or axiomatise them outright. Are these different "real numbers"?
This file proves the answer is **no**, in the strongest sense available:

* We define, for an arbitrary type `K`, what it means to be a **complete ordered field**: an
  ordered field in which every nonempty set bounded above has a least upper bound.
* Our `R` is one (`instCompleteOrderedFieldR`).
* **Categoricity**: any two complete ordered fields `F` and `G` are isomorphic — there is a
  bijection `F → G` preserving `+`, `×` and `≤` — and this isomorphism is **unique**.

So the axioms of a complete ordered field describe a *single* structure, up to a unique
renaming of its elements. Philosophically, this is the result that licenses talk of *the* real
numbers: what matters about them is the structure, and every construction realises the same one.
(It is also a classic illustration of the structuralist reading of mathematics.)

**How the isomorphism is found.** Both fields contain a copy of `ℚ` (`OF.ofRat`), and in both
the rationals are dense (completeness implies the Archimedean property). An element `x` of `F` is
therefore determined by its *cut* — the set of rationals below it — and we send `x` to the
element of `G` with the same cut, namely the supremum in `G` of those rationals. Showing that this
respects `+` is a density argument; for `×` we first treat squares and then use the identity
`4xy = (x + y)² − (x − y)²`.
-/

namespace Foundations.Numbers

open Lean.Grind OF

attribute [local instance] Semiring.natCast Ring.intCast

/-- **Complete ordered field.** An ordered field (given by Lean's `Field`, `IsLinearOrder` and
`OrderedRing` structures) is *complete* if it has the least upper bound property. -/
class CompleteOrderedField (K : Type) [Field K] [LE K] [LT K] [Std.IsLinearOrder K]
    [Std.LawfulOrderLT K] [OrderedRing K] : Prop where
  /-- Every nonempty set bounded above has a least upper bound. -/
  lub : LUBProperty K

/-- **ℝ is a complete ordered field.** -/
instance instCompleteOrderedFieldR : CompleteOrderedField R := ⟨R.exists_lub⟩

/-- An isomorphism of ordered fields: a bijection preserving addition, multiplication and
order. -/
structure OrderedFieldIso (F G : Type) [Add F] [Mul F] [LE F] [Add G] [Mul G] [LE G] where
  /-- The forward map. -/
  toFun : F → G
  /-- The inverse map. -/
  invFun : G → F
  /-- `invFun` undoes `toFun`. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun` undoes `invFun`. -/
  right_inv : ∀ y, toFun (invFun y) = y
  /-- Addition is preserved. -/
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Multiplication is preserved. -/
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  /-- Order is preserved and reflected. -/
  map_le : ∀ x y, x ≤ y ↔ toFun x ≤ toFun y

namespace Categoricity

variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]
variable {G : Type} [Field G] [LE G] [LT G] [Std.IsLinearOrder G] [Std.LawfulOrderLT G]
  [OrderedRing G]

/-- `a ∈ F` and `b ∈ G` *have the same cut* if exactly the same rationals lie below them. -/
def SameCut (a : F) (b : G) : Prop := ∀ q : Q, ofRat q < a ↔ ofRat q < b

/-- Having the same cut is symmetric. -/
theorem sameCut_symm {a : F} {b : G} (h : SameCut a b) : SameCut b a := fun q => (h q).symm

/-- Having the same cut is transitive (across three fields). -/
theorem sameCut_trans {H : Type} [Field H] [LE H] [LT H] [Std.IsLinearOrder H]
    [Std.LawfulOrderLT H] [OrderedRing H] {a : F} {b : G} {c : H}
    (h₁ : SameCut a b) (h₂ : SameCut b c) : SameCut a c := fun q => (h₁ q).trans (h₂ q)

/-- Every element has the same cut as itself. -/
theorem sameCut_refl (a : F) : SameCut a a := fun _ => Iff.rfl

/-- One half of `sameCut_upper`. -/
theorem upper_aux (hF : Archimedean F) {a : F} {b : G} (h : SameCut a b) (q : Q)
    (ha : a < ofRat q) : b < ofRat q := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_between hF ha
  have hrq := (ofRat_lt (K := F)).1 hr2
  have h1 : ¬ ofRat r < b := fun h' => by have := (h r).2 h'; grind
  have h2 := (ofRat_lt (K := G)).2 hrq
  grind

/-- Same cuts also have the same rationals *above* them. -/
theorem sameCut_upper (hF : Archimedean F) (hG : Archimedean G) {a : F} {b : G}
    (h : SameCut a b) (q : Q) : a < ofRat q ↔ b < ofRat q :=
  ⟨upper_aux hF h q, upper_aux hG (sameCut_symm h) q⟩

/-- An element of an Archimedean field is determined by its cut. -/
theorem sameCut_unique (hG : Archimedean G) {a : F} {b b' : G} (h : SameCut a b)
    (h' : SameCut a b') : b = b' := by
  apply Classical.byContradiction
  intro hne
  rcases (by grind : b < b' ∨ b' < b) with hlt | hlt
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_between hG hlt
    have := (h r).1 ((h' r).2 hr2); grind
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_between hG hlt
    have := (h' r).1 ((h r).2 hr2); grind

/-- One half of `sameCut_lt`. -/
theorem lt_aux (hF : Archimedean F) (hG : Archimedean G) {a a' : F} {b b' : G}
    (h : SameCut a b) (h' : SameCut a' b') (hlt : a < a') : b < b' := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_between hF hlt
  have := (sameCut_upper hF hG h r).1 hr1
  have := (h' r).1 hr2
  grind

/-- Same cuts are ordered alike. -/
theorem sameCut_lt (hF : Archimedean F) (hG : Archimedean G) {a a' : F} {b b' : G}
    (h : SameCut a b) (h' : SameCut a' b') : a < a' ↔ b < b' :=
  ⟨lt_aux hF hG h h', lt_aux hG hF (sameCut_symm h) (sameCut_symm h')⟩

/-- The zeros of two ordered fields have the same cut. -/
theorem sameCut_zero : SameCut (0 : F) (0 : G) := fun q => by
  have h1 := ofRat_lt (K := F) (p := q) (q := 0)
  have h2 := ofRat_lt (K := G) (p := q) (q := 0)
  rw [ofRat_zero] at h1 h2
  rw [h1, h2]

/-- The ones of two ordered fields have the same cut. -/
theorem sameCut_one : SameCut (1 : F) (1 : G) := fun q => by
  have h1 := ofRat_lt (K := F) (p := q) (q := 1)
  have h2 := ofRat_lt (K := G) (p := q) (q := 1)
  rw [ofRat_one] at h1 h2
  rw [h1, h2]

/-- Negatives of elements with the same cut have the same cut. -/
theorem sameCut_neg (hF : Archimedean F) (hG : Archimedean G) {a : F} {b : G}
    (h : SameCut a b) : SameCut (-a) (-b) := fun q => by
  have := sameCut_upper hF hG h (-q)
  have e1 := ofRat_neg (K := F) q
  have e2 := ofRat_neg (K := G) q
  constructor
  · intro h1; have := this.1 (by grind); grind
  · intro h1; have := this.2 (by grind); grind

/-- One half of `sameCut_add`, by a density argument. -/
theorem add_aux (hF : Archimedean F) {a a' : F} {b b' : G} (h : SameCut a b)
    (h' : SameCut a' b') (q : Q) (hq : ofRat q < a + a') : ofRat q < b + b' := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_between hF (by grind : ofRat q - a' < a)
  have e1 := ofRat_sub (K := F) q r
  have e2 := ofRat_sub (K := G) q r
  have k1 := (h r).1 hr2
  have k2 := (h' (q - r)).1 (by grind)
  grind

/-- Same cuts add to the same cut. -/
theorem sameCut_add (hF : Archimedean F) (hG : Archimedean G) {a a' : F} {b b' : G}
    (h : SameCut a b) (h' : SameCut a' b') : SameCut (a + a') (b + b') := fun q =>
  ⟨add_aux hF h h' q, add_aux hG (sameCut_symm h) (sameCut_symm h') q⟩

/-- Approximating a square from below by squares of rationals: if `0 < z` and `0 ≤ q < z²`
then some rational `r` with `0 ≤ r < z` has `q < r²`. -/
theorem exists_rat_sq_between {K : Type} [Field K] [LE K] [LT K] [Std.IsLinearOrder K]
    [Std.LawfulOrderLT K] [OrderedRing K] (hA : Archimedean K) {z : K} (hz : 0 < z) {q : Q}
    (_hq0 : (0 : K) ≤ ofRat q) (hq : ofRat q < z * z) :
    ∃ r : Q, (0 : K) < ofRat r ∧ ofRat r < z ∧ ofRat (K := K) q < ofRat r * ofRat r := by
  let δ := z * z - ofRat q
  have hδ : 0 < δ := by grind
  have h2z : 0 < 2 * z := by grind
  have hε : 0 < δ / (2 * z) := div_pos hδ h2z
  let t := z - δ / (2 * z)
  have hr : ∃ r : Q, t < ofRat r ∧ 0 < ofRat (K := K) r ∧ ofRat r < z := by
    by_cases ht : t ≤ z / 2
    · obtain ⟨r, h1, h2⟩ := exists_rat_between hA (by grind : z / 2 < z)
      exact ⟨r, by grind, by grind, h2⟩
    · obtain ⟨r, h1, h2⟩ := exists_rat_between hA (by grind : t < z)
      exact ⟨r, h1, by grind, h2⟩
  obtain ⟨r, hr1, hr2, hr3⟩ := hr
  refine ⟨r, hr2, hr3, ?_⟩
  have k1 : (z - ofRat r) * (z + ofRat r) < (z - ofRat r) * (2 * z) :=
    OrderedRing.mul_lt_mul_of_pos_left (by grind) (by grind)
  have k2 : (z - ofRat r) * (2 * z) < (δ / (2 * z)) * (2 * z) :=
    OrderedRing.mul_lt_mul_of_pos_right (by grind) h2z
  have k3 : (δ / (2 * z)) * (2 * z) = δ := by grind
  grind

/-- One half of `sameCut_sq`, using approximation of squares by rational squares. -/
theorem sq_aux (hF : Archimedean F) {a : F} {b : G} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : SameCut a b) (q : Q) (hq : ofRat q < a * a) : ofRat q < b * b := by
  by_cases hq0 : (0 : F) ≤ ofRat q
  · have hapos : 0 < a := by
      apply Classical.byContradiction; intro hc
      have : a = 0 := by grind
      rw [this] at hq; grind
    obtain ⟨r, hr1, hr2, hr3⟩ := exists_rat_sq_between hF hapos hq0 hq
    have hrb := (h r).1 hr2
    have hr0 : (0 : G) < ofRat r := by
      have := (ofRat_lt (K := F) (p := 0) (q := r)).1 (by rw [ofRat_zero]; exact hr1)
      have := (ofRat_lt (K := G) (p := 0) (q := r)).2 this
      rwa [ofRat_zero] at this
    have hqr : q < r * r := by
      rw [← ofRat_lt (K := F), ofRat_mul]; exact hr3
    have hqr' : ofRat (K := G) q < ofRat r * ofRat r := by
      rw [← ofRat_mul]; exact (ofRat_lt (K := G)).2 hqr
    have k1 := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt hrb) (Std.le_of_lt hr0)
    have k2 := OrderedRing.mul_lt_mul_of_pos_right hrb (by grind : (0 : G) < b)
    grind
  · have h1 : ofRat (K := G) q < 0 := by
      have := (ofRat_lt (K := F) (p := q) (q := 0)).1 (by rw [ofRat_zero]; grind)
      have := (ofRat_lt (K := G) (p := q) (q := 0)).2 this
      rwa [ofRat_zero] at this
    have := OrderedRing.mul_nonneg hb hb
    grind

/-- Non-negative elements with the same cut have squares with the same cut. -/
theorem sameCut_sq (hF : Archimedean F) (hG : Archimedean G) {a : F} {b : G} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h : SameCut a b) : SameCut (a * a) (b * b) := fun q =>
  ⟨sq_aux hF ha hb h q, sq_aux hG hb ha (sameCut_symm h) q⟩

/-- In a complete field, every element of an Archimedean field has a counterpart with the same
cut: the least upper bound of the rationals below it. -/
theorem exists_sameCut (hG : LUBProperty G) (hF : Archimedean F) (a : F) :
    ∃ b : G, SameCut a b := by
  have hAG := archimedean_of_lub hG
  let S : G → Prop := fun g => ∃ q : Q, g = ofRat q ∧ ofRat q < a
  obtain ⟨n, hn⟩ := hF (-a)
  obtain ⟨m, hm⟩ := hF a
  have hne : ∃ g, S g := ⟨ofRat (-(n : Q)), -(n : Q), rfl, by
    rw [ofRat_neg, ofRat_natCast]; grind⟩
  have hbdd : ∃ M, ∀ g, S g → g ≤ M := ⟨ofRat (m : Q), fun g ⟨q, hg, hq⟩ => by
    rw [hg]
    have : q < (m : Q) := (ofRat_lt (K := F)).1 (by rw [ofRat_natCast]; grind)
    exact Std.le_of_lt ((ofRat_lt (K := G)).2 this)⟩
  obtain ⟨L, hL1, hL2⟩ := hG S hne hbdd
  refine ⟨L, fun q => ⟨fun hq => ?_, fun hq => ?_⟩⟩
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_between hF hq
    have := hL1 _ ⟨r, rfl, hr2⟩
    have := (ofRat_lt (K := G)).2 ((ofRat_lt (K := F)).1 hr1)
    grind
  · -- `ofRat q` is not an upper bound of `S`, so some member exceeds it.
    have : ¬ ∀ g, S g → g ≤ ofRat q := fun h' => by have := hL2 _ h'; grind
    apply Classical.byContradiction
    intro hno
    apply this
    rintro g ⟨r, rfl, hr⟩
    apply Classical.byContradiction
    intro hc
    have := (ofRat_lt (K := F)).2 ((ofRat_lt (K := G)).1 (by grind : ofRat q < ofRat (K := G) r))
    exact hno (by grind)

/-! ## The canonical map -/

section Canon

variable [CompleteOrderedField F] [CompleteOrderedField G]

/-- A complete ordered field is Archimedean. -/
theorem archF : Archimedean F := archimedean_of_lub CompleteOrderedField.lub
/-- A complete ordered field is Archimedean. -/
theorem archG : Archimedean G := archimedean_of_lub CompleteOrderedField.lub

/-- The canonical map between complete ordered fields: `x` goes to the element with the same
cut. -/
noncomputable def canon (F G : Type) [Field F] [LE F] [LT F] [Std.IsLinearOrder F]
    [Std.LawfulOrderLT F] [OrderedRing F] [Field G] [LE G] [LT G] [Std.IsLinearOrder G]
    [Std.LawfulOrderLT G] [OrderedRing G] [CompleteOrderedField F] [CompleteOrderedField G]
    (x : F) : G :=
  Classical.choose (exists_sameCut (G := G) CompleteOrderedField.lub (archF (F := F)) x)

/-- `x` and its image under the canonical map have the same cut. -/
theorem canon_spec (x : F) : SameCut x (canon F G x) :=
  Classical.choose_spec (exists_sameCut (G := G) CompleteOrderedField.lub (archF (F := F)) x)

/-- The canonical map sends `x` to the unique element with the same cut. -/
theorem canon_eq {x : F} {y : G} (h : SameCut x y) : canon F G x = y :=
  sameCut_unique (archG (G := G)) (canon_spec x) h

/-- The canonical map preserves addition. -/
theorem canon_add (x y : F) : canon F G (x + y) = canon F G x + canon F G y :=
  canon_eq (sameCut_add (archF (F := F)) (archG (G := G)) (canon_spec x) (canon_spec y))

/-- The canonical map preserves negation. -/
theorem canon_neg (x : F) : canon F G (-x) = -canon F G x :=
  canon_eq (sameCut_neg (archF (F := F)) (archG (G := G)) (canon_spec x))

/-- The canonical map preserves zero. -/
theorem canon_zero : canon F G 0 = 0 := canon_eq sameCut_zero

/-- The canonical map preserves one. -/
theorem canon_one : canon F G 1 = 1 := canon_eq sameCut_one

/-- The canonical map preserves and reflects `<`. -/
theorem canon_lt (x y : F) : x < y ↔ canon F G x < canon F G y :=
  sameCut_lt (archF (F := F)) (archG (G := G)) (canon_spec x) (canon_spec y)

/-- The canonical map preserves and reflects `≤`. -/
theorem canon_le (x y : F) : x ≤ y ↔ canon F G x ≤ canon F G y := by
  have := canon_lt (G := G) y x
  constructor <;> intro h <;> grind

/-- The canonical map preserves subtraction. -/
theorem canon_sub (x y : F) : canon F G (x - y) = canon F G x - canon F G y := by
  have : x - y = x + -y := by grind
  rw [this, canon_add, canon_neg]; grind

/-- The canonical map preserves squares. -/
theorem canon_sq (x : F) : canon F G (x * x) = canon F G x * canon F G x := by
  by_cases hx : 0 ≤ x
  · have h0 : 0 ≤ canon F G x := by
      have := (canon_le (G := G) 0 x).1 hx; rwa [canon_zero] at this
    exact canon_eq (sameCut_sq (archF (F := F)) (archG (G := G)) hx h0 (canon_spec x))
  · have hx' : 0 ≤ -x := by grind
    have h0 : 0 ≤ canon F G (-x) := by
      have := (canon_le (G := G) 0 (-x)).1 hx'; rwa [canon_zero] at this
    have := canon_eq (sameCut_sq (archF (F := F)) (archG (G := G)) hx' h0 (canon_spec (G := G) (-x)))
    have e : -x * -x = x * x := by grind
    rw [e, canon_neg] at this
    rw [this]; grind

/-- The canonical map preserves multiplication, via `4xy = (x+y)² − (x−y)²`. -/
theorem canon_mul (x y : F) : canon F G (x * y) = canon F G x * canon F G y := by
  have e : x * y + x * y + x * y + x * y = (x + y) * (x + y) - (x - y) * (x - y) := by grind
  have h := congrArg (canon F G) e
  rw [canon_add, canon_add, canon_add, canon_sub, canon_sq, canon_sq, canon_add, canon_sub] at h
  grind

/-- The canonical maps `F → G` and `G → F` are mutually inverse. -/
theorem canon_canon (x : F) : canon G F (canon F G x) = x :=
  sameCut_unique (archF (F := F)) (sameCut_trans (canon_spec (G := G) x) (canon_spec _)) (sameCut_refl x)

end Canon

/-! ## Any isomorphism is the canonical one -/

section Unique

variable {ψ : F → G} (hadd : ∀ x y, ψ (x + y) = ψ x + ψ y)
  (hmul : ∀ x y, ψ (x * y) = ψ x * ψ y) (hone : ψ 1 = 1)

include hadd in
/-- An additive map sends `0` to `0`. -/
theorem map_zero : ψ 0 = 0 := by
  have := hadd 0 0; grind

include hadd in
/-- An additive map preserves negation. -/
theorem map_neg (x : F) : ψ (-x) = -ψ x := by
  have := hadd x (-x); have := map_zero hadd; grind

include hadd hone in
/-- A map preserving `+` and `1` fixes the natural numbers. -/
theorem map_natCast (n : Nat) : ψ (n : F) = (n : G) := by
  induction n with
  | zero => have := map_zero hadd; grind
  | succ n ih =>
    rw [Semiring.natCast_succ, hadd, ih, hone, Semiring.natCast_succ]

include hadd hone in
/-- A map preserving `+` and `1` fixes the integers. -/
theorem map_intCast (i : Int) : ψ (i : F) = (i : G) := by
  have e : i = (i.toNat : Int) - ((-i).toNat : Int) := by omega
  rw [e, Ring.intCast_sub, Ring.intCast_sub, Ring.intCast_natCast, Ring.intCast_natCast,
    Ring.intCast_natCast, Ring.intCast_natCast]
  have : (i.toNat : F) - ((-i).toNat : F) = (i.toNat : F) + -((-i).toNat : F) := by grind
  rw [this, hadd, map_neg hadd, map_natCast hadd hone, map_natCast hadd hone]; grind

include hadd hmul hone in
/-- A map preserving `+`, `×` and `1` fixes the rationals. -/
theorem map_ofRat (q : Q) : ψ (ofRat q) = ofRat q := by
  induction q using Q.ind with | h n d hd => ?_
  rw [ofRat_mk, ofRat_mk]
  have hdF := intCast_pos (K := F) hd
  have hdG := intCast_pos (K := G) hd
  have e : (n : F) / (d : F) * (d : F) = (n : F) := by grind
  have h := congrArg ψ e
  rw [hmul, map_intCast hadd hone, map_intCast hadd hone] at h
  grind

include hadd hmul hone in
/-- A map preserving `+`, `×`, `1` and order has `x` and `ψ x` with the same cut. -/
theorem sameCut_of_hom (hle : ∀ x y, x ≤ y ↔ ψ x ≤ ψ y) (x : F) : SameCut x (ψ x) := fun q => by
  have h1 := hle x (ofRat q)
  rw [map_ofRat hadd hmul hone] at h1
  constructor <;> intro h <;> grind

end Unique

end Categoricity

open Categoricity

variable {F : Type} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F] [CompleteOrderedField F]
variable {G : Type} [Field G] [LE G] [LT G] [Std.IsLinearOrder G] [Std.LawfulOrderLT G]
  [OrderedRing G] [CompleteOrderedField G]

/-- The canonical isomorphism between two complete ordered fields. -/
noncomputable def canonIso (F G : Type) [Field F] [LE F] [LT F] [Std.IsLinearOrder F]
    [Std.LawfulOrderLT F] [OrderedRing F] [CompleteOrderedField F] [Field G] [LE G] [LT G]
    [Std.IsLinearOrder G] [Std.LawfulOrderLT G] [OrderedRing G] [CompleteOrderedField G] :
    OrderedFieldIso F G where
  toFun := canon F G
  invFun := canon G F
  left_inv := canon_canon
  right_inv := canon_canon
  map_add := canon_add
  map_mul := canon_mul
  map_le := canon_le

/-- **Categoricity of the real numbers.** Any two complete ordered fields are isomorphic, and the
isomorphism is unique: there is an order- and field-preserving bijection between them, and any two
such bijections agree. -/
theorem categoricity :
    Nonempty (OrderedFieldIso F G) ∧
      ∀ e₁ e₂ : OrderedFieldIso F G, ∀ x, e₁.toFun x = e₂.toFun x := by
  refine ⟨⟨canonIso F G⟩, ?_⟩
  -- Every isomorphism sends `1` to `1`, hence agrees with the canonical map.
  have key : ∀ e : OrderedFieldIso F G, ∀ x, e.toFun x = canon F G x := by
    intro e x
    have hone : e.toFun 1 = 1 := by
      have := e.map_mul 1 (e.invFun 1)
      rw [show (1 : F) * e.invFun 1 = e.invFun 1 by grind, e.right_inv] at this; grind
    exact (canon_eq (sameCut_of_hom e.map_add e.map_mul hone e.map_le x)).symm
  intro e₁ e₂ x
  rw [key e₁, key e₂]

/-- **Every complete ordered field is (uniquely) isomorphic to our `R`.** -/
theorem iso_R : Nonempty (OrderedFieldIso F R) := (categoricity (F := F) (G := R)).1

end Foundations.Numbers
