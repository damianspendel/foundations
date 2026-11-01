import Foundations.Numbers.CompleteOrderedField

/-!
# A second construction: Dedekind cuts

In 1858 Richard Dedekind, preparing a lecture on the calculus, found that he could not prove that
an increasing bounded sequence converges, because nobody had said what a real number *is*. His
answer (published 1872 in *Stetigkeit und irrationale Zahlen*) is different from Cantor's. A
real number is a **cut**: a division of the rationals into a *lower* part and an *upper* part,
every lower rational being below every upper one. Formally, we record the lower part `L`, a set
of rationals that is

* nonempty, and not everything;
* closed downwards (with `q`, it contains every smaller rational);
* without a greatest element.

The rational `r` itself corresponds to the cut `{q | q < r}`; `√2` corresponds to the cut
`{q | q < 0 ∨ q² < 2}`, which no rational produces. Where Cantor's construction views a real
number as the limit of a *process*, Dedekind views it as a *place* in the rational order.

**What we do here.** We define cuts, their order (inclusion of lower parts), and
addition, negation and multiplication *directly on cuts*:

* `L + M = {q | q < a + b for some a ∈ L, b ∈ M}`;
* `−L = {q | q < r for some r with −r ∉ L}`;
* for non-negative cuts, `L · M = {q | q < 0, or q < a·b for some 0 ≤ a ∈ L, 0 ≤ b ∈ M}`, extended
  to all cuts by the rule of signs.

The **least upper bound** of a bounded set of cuts is simply the *union* of their lower parts —
completeness is almost built into Dedekind's definition. To obtain the field laws without
repeating all of algebra we use the bridge `ofR : R → Cut`, `x ↦ {q | q < x}`, which we show is a
bijection carrying the Cauchy-real operations to the cut operations just defined; every law then
transfers. So cuts form a **complete ordered field**, and the categoricity theorem of
`CompleteOrderedField.lean` yields, once more, a unique isomorphism with the Cauchy reals:
Dedekind's reals and Cantor's reals are *the same* reals.
-/

namespace Foundations.Numbers

open Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

/-- **Dedekind cuts.** A cut is given by its lower part: a nonempty, bounded-above, downward
closed set of rationals with no greatest element. -/
structure Cut where
  /-- The lower part of the cut. -/
  lower : Q → Prop
  /-- Some rational is in the lower part. -/
  nonempty : ∃ q, lower q
  /-- Some rational is not in the lower part. -/
  bounded : ∃ q, ¬ lower q
  /-- The lower part is closed downwards. -/
  down : ∀ {p q : Q}, lower q → p < q → lower p
  /-- The lower part has no greatest element. -/
  open_ : ∀ {q : Q}, lower q → ∃ r, q < r ∧ lower r

namespace Cut

/-- Cuts with the same lower part are equal. -/
theorem ext {A B : Cut} (h : ∀ q, A.lower q ↔ B.lower q) : A = B := by
  cases A; cases B
  have : ∀ q, _ = _ := fun q => propext (h q)
  simp only [Cut.mk.injEq]
  exact funext this

/-- Every member of the lower part is below every non-member. -/
theorem lt_of_mem {A : Cut} {a b : Q} (ha : A.lower a) (hb : ¬ A.lower b) : a < b := by
  apply Classical.byContradiction
  intro h
  rcases (by grind : b < a ∨ b = a) with h' | h'
  · exact hb (A.down ha h')
  · exact hb (h' ▸ ha)

/-- The cut of a rational `r`: all rationals below `r`. -/
def ratCut (r : Q) : Cut where
  lower q := q < r
  nonempty := ⟨r - 1, by grind⟩
  bounded := ⟨r, by grind⟩
  down h h' := by grind
  open_ {q} h := ⟨(q + r) / 2, by grind, by grind⟩

/-! ## Order and completeness -/

/-- Order on cuts: inclusion of lower parts. -/
instance : LE Cut := ⟨fun A B => ∀ q, A.lower q → B.lower q⟩
/-- Strict order on cuts. -/
instance : LT Cut := ⟨fun A B => A ≤ B ∧ ¬ B ≤ A⟩

/-- Unfolding the order on cuts. -/
theorem le_def {A B : Cut} : A ≤ B ↔ ∀ q, A.lower q → B.lower q := Iff.rfl

/-- The order on cuts is linear (this uses classical logic). -/
theorem le_total (A B : Cut) : A ≤ B ∨ B ≤ A := by
  by_cases h : A ≤ B
  · exact Or.inl h
  · right
    have : ∃ q, A.lower q ∧ ¬ B.lower q := by
      apply Classical.byContradiction; intro hno
      exact h fun q hq => Classical.byContradiction fun hb => hno ⟨q, hq, hb⟩
    obtain ⟨q, hqA, hqB⟩ := this
    intro b hb
    exact A.down hqA (lt_of_mem hb hqB)

/-- `≤` on cuts is a linear order. -/
instance : Std.IsLinearOrder Cut where
  le_refl _ _ h := h
  le_trans _ _ _ h₁ h₂ q h := h₂ q (h₁ q h)
  le_antisymm _ _ h₁ h₂ := ext fun q => ⟨h₁ q, h₂ q⟩
  le_total := le_total

/-- `<` on cuts agrees with `≤`. -/
instance : Std.LawfulOrderLT Cut where
  lt_iff _ _ := Iff.rfl

/-- **Completeness of the Dedekind reals.** A nonempty set of cuts which is bounded above has a
least upper bound: the union of the lower parts. -/
theorem lub (S : Cut → Prop) (hne : ∃ A, S A) (hbdd : ∃ M, ∀ A, S A → A ≤ M) :
    ∃ L, (∀ A, S A → A ≤ L) ∧ ∀ M, (∀ A, S A → A ≤ M) → L ≤ M := by
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨M, hM⟩ := hbdd
  let L : Cut :=
    { lower := fun q => ∃ A, S A ∧ A.lower q
      nonempty := by obtain ⟨q, hq⟩ := A₀.nonempty; exact ⟨q, A₀, hA₀, hq⟩
      bounded := by
        obtain ⟨q, hq⟩ := M.bounded
        exact ⟨q, fun ⟨A, hA, hAq⟩ => hq (hM A hA q hAq)⟩
      down := fun ⟨A, hA, hAq⟩ h => ⟨A, hA, A.down hAq h⟩
      open_ := fun ⟨A, hA, hAq⟩ => by
        obtain ⟨r, hr, hAr⟩ := A.open_ hAq
        exact ⟨r, hr, A, hA, hAr⟩ }
  exact ⟨L, fun A hA q hq => ⟨A, hA, hq⟩, fun M' hM' q ⟨A, hA, hAq⟩ => hM' A hA q hAq⟩

/-! ## Operations on cuts -/

/-- Sum of cuts: `{q | q < a + b, a ∈ A, b ∈ B}`. -/
def add (A B : Cut) : Cut where
  lower q := ∃ a b, A.lower a ∧ B.lower b ∧ q < a + b
  nonempty := by
    obtain ⟨a, ha⟩ := A.nonempty; obtain ⟨b, hb⟩ := B.nonempty
    exact ⟨a + b - 1, a, b, ha, hb, by grind⟩
  bounded := by
    obtain ⟨a₀, ha₀⟩ := A.bounded; obtain ⟨b₀, hb₀⟩ := B.bounded
    refine ⟨a₀ + b₀, fun ⟨a, b, ha, hb, h⟩ => ?_⟩
    have := lt_of_mem ha ha₀; have := lt_of_mem hb hb₀; grind
  down := fun ⟨a, b, ha, hb, h⟩ h' => ⟨a, b, ha, hb, by grind⟩
  open_ := fun {q} ⟨a, b, ha, hb, h⟩ => ⟨(q + (a + b)) / 2, by grind, a, b, ha, hb, by grind⟩

/-- Negation of a cut: `{q | q < r for some r with −r ∉ A}`. -/
def neg (A : Cut) : Cut where
  lower q := ∃ r, q < r ∧ ¬ A.lower (-r)
  nonempty := by
    obtain ⟨a₀, ha₀⟩ := A.bounded
    exact ⟨-a₀ - 1, -a₀, by grind, by rw [show -(-a₀) = a₀ by grind]; exact ha₀⟩
  bounded := by
    obtain ⟨a, ha⟩ := A.nonempty
    refine ⟨-a, fun ⟨r, hr, hnr⟩ => hnr (A.down ha (by grind))⟩
  down := fun ⟨r, hr, hnr⟩ h' => ⟨r, by grind, hnr⟩
  open_ := fun {q} ⟨r, hr, hnr⟩ => ⟨(q + r) / 2, by grind, r, by grind, hnr⟩

/-- Product of two cuts, meant for non-negative ones:
`{q | q < 0, or q < a·b with 0 ≤ a ∈ A and 0 ≤ b ∈ B}`. -/
def posMul (A B : Cut) : Cut where
  lower q := q < 0 ∨ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ A.lower a ∧ B.lower b ∧ q < a * b
  nonempty := ⟨-1, Or.inl (by grind)⟩
  bounded := by
    obtain ⟨a₀, ha₀⟩ := A.bounded; obtain ⟨b₀, hb₀⟩ := B.bounded
    refine ⟨Q.abs a₀ * Q.abs b₀, ?_⟩
    rintro (h | ⟨a, b, h0a, h0b, ha, hb, h⟩)
    · have := OrderedRing.mul_nonneg (Q.abs_nonneg a₀) (Q.abs_nonneg b₀); grind
    · have k1 := lt_of_mem ha ha₀; have k2 := lt_of_mem hb hb₀
      have := (Q.le_abs a₀).1; have := (Q.le_abs b₀).1
      have m1 := OrderedRing.mul_le_mul_of_nonneg_left (by grind : b ≤ Q.abs b₀) h0a
      have m2 := OrderedRing.mul_le_mul_of_nonneg_right (by grind : a ≤ Q.abs a₀)
        (Q.abs_nonneg b₀)
      grind
  down := fun h h' => by
    rcases h with h | ⟨a, b, h0a, h0b, ha, hb, h⟩
    · exact Or.inl (by grind)
    · exact Or.inr ⟨a, b, h0a, h0b, ha, hb, by grind⟩
  open_ := fun {q} h => by
    rcases h with h | ⟨a, b, h0a, h0b, ha, hb, h⟩
    · exact ⟨q / 2, by grind, Or.inl (by grind)⟩
    · exact ⟨(q + a * b) / 2, by grind, Or.inr ⟨a, b, h0a, h0b, ha, hb, by grind⟩⟩

/-- Addition of cuts. -/
instance : Add Cut := ⟨add⟩
/-- Negation of cuts. -/
instance : Neg Cut := ⟨neg⟩
/-- Subtraction of cuts. -/
instance : Sub Cut := ⟨fun A B => A + -B⟩
/-- Numerals: the cut of the rational numeral. -/
instance (n : Nat) : OfNat Cut n := ⟨ratCut (OfNat.ofNat n)⟩
/-- The canonical map from `Nat`. -/
instance : NatCast Cut := ⟨fun n => ratCut n⟩
/-- The canonical map from `Int`. -/
instance : IntCast Cut := ⟨fun i => ratCut i⟩

/-- Product of cuts, by the rule of signs from the product of non-negative cuts. -/
noncomputable def mul (A B : Cut) : Cut :=
  open Classical in
  if 0 ≤ A then (if 0 ≤ B then posMul A B else -posMul A (-B))
  else (if 0 ≤ B then -posMul (-A) B else posMul (-A) (-B))

/-- Multiplication. -/
noncomputable instance : Mul Cut := ⟨mul⟩

/-! ## The bridge to the Cauchy reals -/

/-- In `R`, the general embedding of `ℚ` is our `ofQ`. -/
theorem ofRat_R (q : Q) : OF.ofRat (K := R) q = R.ofQ q := by
  induction q using Q.ind with | h n d hd => ?_
  rw [OF.ofRat_mk]
  have e1 : ((n : Int) : R) = R.ofQ (n : Q) := rfl
  have e2 : ((d : Int) : R) = R.ofQ (d : Q) := rfl
  have h1 : R.ofQ (Q.mk n d hd) * R.ofQ (d : Q) = R.ofQ (n : Q) := by
    rw [← R.ofQ_mul]; congr 1
    rw [Q.intCast_def, Q.intCast_def, Q.mk_mul, Q.mk_eq_mk]; grind
  have h2 : (0 : R) < R.ofQ (d : Q) := by
    have := R.ofQ_lt.2 (show (0 : Q) < (d : Q) by rw [Q.intCast_def, Q.ofNat_def, Q.mk_lt]; simpa using hd)
    exact this
  rw [e1, e2]; grind

/-- **Density of ℚ in ℝ.** Between two reals lies a rational. -/
theorem R_density {x y : R} (h : x < y) : ∃ q : Q, x < R.ofQ q ∧ R.ofQ q < y := by
  obtain ⟨q, h1, h2⟩ := OF.exists_rat_between (K := R) R.archimedean h
  rw [ofRat_R] at h1 h2
  exact ⟨q, h1, h2⟩

/-- The cut of a Cauchy real `x`: the rationals below `x`. -/
def ofR (x : R) : Cut where
  lower q := R.ofQ q < x
  nonempty := by
    obtain ⟨n, hn⟩ := R.archimedean (-x)
    refine ⟨-(n : Q) - 1, ?_⟩
    have : R.ofQ (-(n : Q) - 1) = -(n : R) - 1 := rfl
    rw [this]; grind
  bounded := by
    obtain ⟨n, hn⟩ := R.archimedean x
    exact ⟨n, by have : R.ofQ (n : Q) = (n : R) := rfl
                 rw [this]; grind⟩
  down h h' := by have := R.ofQ_lt.2 h'; grind
  open_ h := by
    obtain ⟨r, h1, h2⟩ := R_density h
    exact ⟨r, R.ofQ_lt.1 h1, h2⟩

/-- Every cut is the cut of some Cauchy real (the supremum of its lower part). -/
theorem exists_real (A : Cut) : ∃ x : R, ∀ q, A.lower q ↔ R.ofQ q < x := by
  let S : R → Prop := fun y => ∃ q, A.lower q ∧ y = R.ofQ q
  obtain ⟨a, ha⟩ := A.nonempty
  obtain ⟨b, hb⟩ := A.bounded
  obtain ⟨L, hL1, hL2⟩ := R.exists_lub S ⟨_, a, ha, rfl⟩ ⟨R.ofQ b, fun y ⟨q, hq, hy⟩ => by
    rw [hy]; exact Std.le_of_lt (R.ofQ_lt.2 (lt_of_mem hq hb))⟩
  refine ⟨L, fun q => ⟨fun hq => ?_, fun hq => ?_⟩⟩
  · obtain ⟨r, hr, hAr⟩ := A.open_ hq
    have := hL1 _ ⟨r, hAr, rfl⟩
    have := R.ofQ_lt.2 hr
    grind
  · have : ¬ ∀ y, S y → y ≤ R.ofQ q := fun h => by have := hL2 _ h; grind
    apply Classical.byContradiction
    intro hno
    apply this
    rintro y ⟨r, hr, rfl⟩
    apply Classical.byContradiction
    intro hc
    exact hno (A.down hr (R.ofQ_lt.1 (by grind)))

/-- A real is determined by the rationals below it. -/
theorem R_eq_of_cut {x y : R} (h : ∀ q, R.ofQ q < x ↔ R.ofQ q < y) : x = y := by
  apply Classical.byContradiction
  intro hne
  rcases (by grind : x < y ∨ y < x) with hlt | hlt
  · obtain ⟨q, h1, h2⟩ := R_density hlt; have := (h q).2 h2; grind
  · obtain ⟨q, h1, h2⟩ := R_density hlt; have := (h q).1 h2; grind

/-- The Cauchy real corresponding to a cut. -/
noncomputable def toR (A : Cut) : R := Classical.choose (exists_real A)

/-- The real of a cut has exactly the cut's lower part below it. -/
theorem toR_spec (A : Cut) (q : Q) : A.lower q ↔ R.ofQ q < toR A :=
  Classical.choose_spec (exists_real A) q

/-- `ofR` undoes `toR`. -/
theorem ofR_toR (A : Cut) : ofR (toR A) = A := ext fun q => (toR_spec A q).symm

/-- `toR` undoes `ofR`. -/
theorem toR_ofR (x : R) : toR (ofR x) = x :=
  R_eq_of_cut fun q => (toR_spec (ofR x) q).symm

/-- Every cut is in the image of `ofR`. -/
theorem surj (A : Cut) : ∃ x, A = ofR x := ⟨toR A, (ofR_toR A).symm⟩

/-- `ofR` is injective. -/
theorem ofR_inj {x y : R} (h : ofR x = ofR y) : x = y := by
  rw [← toR_ofR x, ← toR_ofR y, h]

/-- The cut of a rational real is the rational cut. -/
theorem ofR_ofQ (r : Q) : ofR (R.ofQ r) = ratCut r := ext fun _ => R.ofQ_lt

/-- `ofR` preserves and reflects the order. -/
theorem ofR_le (x y : R) : x ≤ y ↔ ofR x ≤ ofR y := by
  constructor
  · intro h q hq; show R.ofQ q < y; have : R.ofQ q < x := hq; grind
  · intro h
    apply Classical.byContradiction
    intro hc
    obtain ⟨q, h1, h2⟩ := R_density (by grind : y < x)
    have := h q h2; have : R.ofQ q < y := this; grind

/-- `ofR` carries addition of reals to addition of cuts. -/
theorem ofR_add (x y : R) : ofR (x + y) = ofR x + ofR y := by
  apply ext; intro q
  show R.ofQ q < x + y ↔ ∃ a b, R.ofQ a < x ∧ R.ofQ b < y ∧ q < a + b
  constructor
  · intro h
    obtain ⟨a, ha1, ha2⟩ := R_density (by grind : R.ofQ q - y < x)
    obtain ⟨b, hb1, hb2⟩ := R_density (by rw [R.ofQ_sub]; grind : R.ofQ (q - a) < y)
    exact ⟨a, b, ha2, hb2, by have := R.ofQ_lt.1 hb1; grind⟩
  · rintro ⟨a, b, ha, hb, h⟩
    have := R.ofQ_lt.2 h; rw [R.ofQ_add] at this; grind

/-- `ofR` carries negation of reals to negation of cuts. -/
theorem ofR_neg (x : R) : ofR (-x) = -ofR x := by
  apply ext; intro q
  show R.ofQ q < -x ↔ ∃ r, q < r ∧ ¬ R.ofQ (-r) < x
  constructor
  · intro h
    obtain ⟨r, h1, h2⟩ := R_density h
    exact ⟨r, R.ofQ_lt.1 h1, by rw [R.ofQ_neg]; grind⟩
  · rintro ⟨r, h1, h2⟩
    have := R.ofQ_lt.2 h1; rw [R.ofQ_neg] at h2; grind

/-- `ofR` preserves zero. -/
theorem ofR_zero : ofR 0 = 0 := ofR_ofQ 0

/-- `ofR` preserves non-negativity. -/
theorem ofR_nonneg (x : R) : 0 ≤ ofR x ↔ 0 ≤ x := by
  rw [← ofR_zero, ← ofR_le]

/-- On non-negative reals, `ofR` carries multiplication to the product of cuts. -/
theorem ofR_mul_nonneg {x y : R} (hx : 0 ≤ x) (hy : 0 ≤ y) : ofR (x * y) = posMul (ofR x) (ofR y) := by
  apply ext; intro q
  show R.ofQ q < x * y ↔
    q < 0 ∨ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ R.ofQ a < x ∧ R.ofQ b < y ∧ q < a * b
  constructor
  · intro h
    by_cases hq : q < 0
    · exact Or.inl hq
    right
    have hq0 : (0 : R) ≤ R.ofQ q := (R.ofQ_le.2 (by grind : (0 : Q) ≤ q))
    have hxpos : 0 < x := by
      apply Classical.byContradiction; intro hc
      have : x = 0 := by grind
      rw [this] at h; grind
    have hypos : 0 < y := by
      apply Classical.byContradiction; intro hc
      have : y = 0 := by grind
      rw [this] at h; grind
    have h1 : R.ofQ q / y < x := by
      rw [← Field.IsOrdered.mul_lt_mul_iff_of_pos_right hypos]
      have : R.ofQ q / y * y = R.ofQ q := by grind
      rw [this]; exact h
    obtain ⟨a, ha1, ha2⟩ := R_density h1
    have hdiv : 0 ≤ R.ofQ q / y := by
      have := OF.div_pos (K := R) (by grind : (0 : R) < R.ofQ q + 1) hypos
      rcases (by grind : (0 : R) < R.ofQ q ∨ R.ofQ q = 0) with h' | h'
      · exact Std.le_of_lt (OF.div_pos h' hypos)
      · rw [h']; grind
    have hapos : (0 : R) < R.ofQ a := by grind
    have h2 : R.ofQ q / R.ofQ a < y := by
      rw [← Field.IsOrdered.mul_lt_mul_iff_of_pos_right hapos]
      have e : R.ofQ q / R.ofQ a * R.ofQ a = R.ofQ q := by grind
      rw [e]
      have := (Field.IsOrdered.mul_lt_mul_iff_of_pos_right hypos).2 ha1
      have e2 : R.ofQ q / y * y = R.ofQ q := by grind
      rw [e2] at this; grind
    obtain ⟨b, hb1, hb2⟩ := R_density h2
    have hbpos : (0 : R) < R.ofQ b := by
      have := Std.le_of_lt (OF.div_pos (K := R) (by grind : (0 : R) < R.ofQ q + 1) hapos)
      rcases (by grind : (0 : R) < R.ofQ q ∨ R.ofQ q = 0) with h' | h'
      · have := OF.div_pos h' hapos; grind
      · rw [h'] at hb1; grind
    refine ⟨a, b, R.ofQ_le.1 (by rw [show R.ofQ 0 = 0 from rfl]; grind),
      R.ofQ_le.1 (by rw [show R.ofQ 0 = 0 from rfl]; grind), ha2, hb2, ?_⟩
    rw [← R.ofQ_lt, R.ofQ_mul]
    have := (Field.IsOrdered.mul_lt_mul_iff_of_pos_left hapos).2 hb1
    have e : R.ofQ a * (R.ofQ q / R.ofQ a) = R.ofQ q := by grind
    rw [e] at this; exact this
  · rintro (hq | ⟨a, b, ha0, hb0, ha, hb, h⟩)
    · have := R.ofQ_lt.2 hq
      have := OrderedRing.mul_nonneg hx hy
      have e : R.ofQ 0 = 0 := rfl
      grind
    · have h1 := R.ofQ_lt.2 h
      rw [R.ofQ_mul] at h1
      have ha0' : (0 : R) ≤ R.ofQ a := R.ofQ_le.2 ha0
      have m1 := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt hb) ha0'
      have m2 := OrderedRing.mul_le_mul_of_nonneg_right (Std.le_of_lt ha) hy
      grind

/-- `ofR` carries multiplication of reals to multiplication of cuts. -/
theorem ofR_mul (x y : R) : ofR (x * y) = ofR x * ofR y := by
  show ofR (x * y) = mul (ofR x) (ofR y)
  unfold mul
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [ite_eq_left ((ofR_nonneg x).2 hx), ite_eq_left ((ofR_nonneg y).2 hy)]
    exact ofR_mul_nonneg hx hy
  · rw [ite_eq_left ((ofR_nonneg x).2 hx), ite_eq_right (fun h => hy ((ofR_nonneg y).1 h))]
    rw [← ofR_neg, ← ofR_mul_nonneg hx (by grind)]
    show _ = -ofR _
    rw [← ofR_neg]; congr 1; grind
  · rw [ite_eq_right (fun h => hx ((ofR_nonneg x).1 h)), ite_eq_left ((ofR_nonneg y).2 hy)]
    rw [← ofR_neg, ← ofR_mul_nonneg (by grind) hy]
    show _ = -ofR _
    rw [← ofR_neg]; congr 1; grind
  · rw [ite_eq_right (fun h => hx ((ofR_nonneg x).1 h)),
      ite_eq_right (fun h => hy ((ofR_nonneg y).1 h))]
    rw [← ofR_neg, ← ofR_neg, ← ofR_mul_nonneg (by grind) (by grind)]
    congr 1; grind

/-- `ofR` preserves natural numbers. -/
theorem ofR_natCast (n : Nat) : ofR (n : R) = (n : Cut) := ofR_ofQ _
/-- `ofR` preserves integers. -/
theorem ofR_intCast (i : Int) : ofR (i : R) = (i : Cut) := ofR_ofQ _
/-- `ofR` preserves numerals. -/
theorem ofR_ofNat (n : Nat) : ofR (OfNat.ofNat n : R) = (OfNat.ofNat n : Cut) := ofR_ofQ _

end Cut

end Foundations.Numbers
