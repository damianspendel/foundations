import Foundations.Langlands.Padic.HilbertReciprocity
import Foundations.Langlands.Padic.Legendre

/-!
# The Hasse principle for conics over ℚ

**The local–global principle.** A rational conic `a x² + b y² + c z² = 0` has a non-trivial
rational point iff it has one over ℝ and over every `p`-adic field ℚₚ. For quadratic forms
over ℚ this is the **Hasse–Minkowski theorem**: Minkowski (1890) gave the classification of
rational quadratic forms by local invariants, and Hasse (dissertation 1921, and 1923–24 for
equivalence and for number fields) recast it in terms of Hensel's `p`-adic numbers, the first
instance of what became the guiding principle of class field theory and, later, of the
Langlands programme: global objects over ℚ are controlled by their completions ℚ_v, `v = ∞, 2,
3, 5, …`. For *ternary* forms — conics — the principle is a reformulation of **Legendre's
theorem** (1785), and that is what is proved here (`hasse_conic`). Hasse–Minkowski for forms in
four or more variables is **not** proved here.

Throughout, `a, b, c` are non-zero, squarefree, pairwise coprime integers (`Admissible`); every
ternary form over ℚ is equivalent to a multiple of such a form, but that normalisation is not
formalised.

## Contents

* `ConicSolvableQ`, `ConicSolvableR`, `ConicSolvableQp p` — a non-trivial point of
  `a x² + b y² + c z² = 0` over ℚ, ℝ, ℚₚ.
* `conicQ_iff_Z` — over ℚ iff over ℤ (clearing denominators).
* `conicR_iff` — **over ℝ iff the signs are mixed**, via the library's `HilbertSolvableR`
  (`z² = A x² + B y²` with `A = −ab`, `B = −bc`, obtained by scaling).
* `isSqMod_of_Qp` — at an odd prime `p ∣ a`, a ℚₚ-point forces `−bc` to be a square mod `p`,
  via `Qp.hilbertSolvable_unit_pv_iff` (the conic becomes `z² = u x² + p v y²` with units `u, v`);
  `legendreCond_of_local` glues these by the Chinese remainder theorem (`Squarefree.glue`). At
  `p = 2` the condition is empty, since everything is a square modulo `2`.
* **`local_iff_legendre`**: solvability over ℝ and every ℚₚ ⟺ Legendre's sign and congruence
  conditions.
* **`hasse_conic`**: solvable over ℚ ⟺ solvable over ℝ and every ℚₚ.
* `conicQp_iff_hilbert`: the local condition at `p` is the Hilbert symbol condition
  `(−bc, −ab)ₚ = 1`; `hasse_conic_hilbert` restates Hasse's principle with Hilbert symbols.
* Examples: **`hasse_example_three`** — `x² + y² = 3 z²` has a real point but no 3-adic one,
  hence no rational one; **`hasse_example_five`** — `x² + y² = 5 z²` has rational points.
-/

namespace Foundations.Langlands.Padic

namespace Legendre

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-! ## Points over ℚ, ℝ and ℚₚ -/

/-- The conic `a x² + b y² + c z² = 0` has a **non-trivial rational point**. -/
def ConicSolvableQ (a b c : Int) : Prop :=
  ∃ x y z : Q, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    (a : Q) * (x * x) + (b : Q) * (y * y) + (c : Q) * (z * z) = 0

/-- The conic `a x² + b y² + c z² = 0` has a **non-trivial real point**. -/
def ConicSolvableR (a b c : Int) : Prop :=
  ∃ x y z : R, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    (a : R) * (x * x) + (b : R) * (y * y) + (c : R) * (z * z) = 0

/-- The conic `a x² + b y² + c z² = 0` has a **non-trivial point in ℚₚ**. -/
def ConicSolvableQp (p : Nat) [PrimeP p] (a b c : Int) : Prop :=
  ∃ x y z : Qp p, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    (a : Qp p) * (x * x) + (b : Qp p) * (y * y) + (c : Qp p) * (z * z) = 0

/-! ## Rational versus integer points -/

/-- The integer cast into ℚ is injective at `0`. -/
theorem Q_intCast_eq_zero {m : Int} (h : (m : Q) = 0) : m = 0 := by
  have : Q.mk m 1 Int.one_pos = Q.mk 0 1 Int.one_pos := h
  rw [Q.mk_eq_mk] at this; omega

/-- Every rational has a denominator: `d x = n` with `d > 0`. -/
theorem Q_exists_den (x : Q) : ∃ n d : Int, 0 < d ∧ (d : Q) * x = n := by
  induction x using Q.ind with
  | h n d hd =>
    refine ⟨n, d, hd, ?_⟩
    show Q.mk (d * n) (1 * d) _ = Q.mk n 1 _
    rw [Q.mk_eq_mk]; grind

/-- **Rational points are integer points.** Clearing denominators turns a rational point into an
integer one, and conversely. -/
theorem conicQ_iff_Z {a b c : Int} : ConicSolvableQ a b c ↔ ConicSolvableZ a b c := by
  constructor
  · rintro ⟨x, y, z, hnt, h⟩
    obtain ⟨n₁, d₁, hd₁, e₁⟩ := Q_exists_den x
    obtain ⟨n₂, d₂, hd₂, e₂⟩ := Q_exists_den y
    obtain ⟨n₃, d₃, hd₃, e₃⟩ := Q_exists_den z
    have hD : ((d₁ * d₂ * d₃ : Int) : Q) ≠ 0 := fun h0 => by
      have := Q_intCast_eq_zero h0
      have := Int.mul_pos (Int.mul_pos hd₁ hd₂) hd₃; omega
    have eX : ((n₁ * d₂ * d₃ : Int) : Q) = ((d₁ * d₂ * d₃ : Int) : Q) * x := by
      simp only [Ring.intCast_mul]; rw [← e₁]; grind
    have eY : ((d₁ * n₂ * d₃ : Int) : Q) = ((d₁ * d₂ * d₃ : Int) : Q) * y := by
      simp only [Ring.intCast_mul]; rw [← e₂]; grind
    have eZ : ((d₁ * d₂ * n₃ : Int) : Q) = ((d₁ * d₂ * d₃ : Int) : Q) * z := by
      simp only [Ring.intCast_mul]; rw [← e₃]; grind
    refine ⟨n₁ * d₂ * d₃, d₁ * n₂ * d₃, d₁ * d₂ * n₃, ?_, ?_⟩
    · have hne : ∀ (m : Int) (w : Q), (m : Q) = ((d₁ * d₂ * d₃ : Int) : Q) * w → w ≠ 0 →
          m ≠ 0 := fun m w hm hw h0 => by
        subst h0
        have : ((d₁ * d₂ * d₃ : Int) : Q) * w ≠ 0 := by grind
        exact this (by rw [← hm]; rfl)
      rcases hnt with h' | h' | h'
      · exact Or.inl (hne _ _ eX h')
      · exact Or.inr (Or.inl (hne _ _ eY h'))
      · exact Or.inr (Or.inr (hne _ _ eZ h'))
    · apply Q_intCast_eq_zero
      have e : ((a * ((n₁ * d₂ * d₃) * (n₁ * d₂ * d₃)) + b * ((d₁ * n₂ * d₃) * (d₁ * n₂ * d₃)) +
          c * ((d₁ * d₂ * n₃) * (d₁ * d₂ * n₃)) : Int) : Q) =
          (a : Q) * (((n₁ * d₂ * d₃ : Int) : Q) * ((n₁ * d₂ * d₃ : Int) : Q)) +
          (b : Q) * (((d₁ * n₂ * d₃ : Int) : Q) * ((d₁ * n₂ * d₃ : Int) : Q)) +
          (c : Q) * (((d₁ * d₂ * n₃ : Int) : Q) * ((d₁ * d₂ * n₃ : Int) : Q)) := by
        simp only [Ring.intCast_add, Ring.intCast_mul]
      rw [e, eX, eY, eZ]
      have : ((d₁ * d₂ * d₃ : Int) : Q) * ((d₁ * d₂ * d₃ : Int) : Q) *
          ((a : Q) * (x * x) + (b : Q) * (y * y) + (c : Q) * (z * z)) = 0 := by
        rw [h]; grind
      rw [← this]; grind
  · rintro ⟨x, y, z, hnt, h⟩
    refine ⟨x, y, z, ?_, ?_⟩
    · rcases hnt with h' | h' | h'
      · exact Or.inl fun h0 => h' (Q_intCast_eq_zero h0)
      · exact Or.inr (Or.inl fun h0 => h' (Q_intCast_eq_zero h0))
      · exact Or.inr (Or.inr fun h0 => h' (Q_intCast_eq_zero h0))
    · have := congrArg (fun m : Int => (m : Q)) h
      simp only [Ring.intCast_add, Ring.intCast_mul] at this
      rw [this]; rfl

/-! ## From ℚ to its completions -/

/-- A non-zero rational is non-zero in ℝ. -/
theorem R_ofQ_ne_zero {x : Q} (hx : x ≠ 0) : R.ofQ x ≠ 0 := fun h => by
  rcases Std.lt_trichotomy x 0 with h' | h' | h'
  · have := R.ofQ_lt.2 h'; rw [h] at this; exact R.lt_irrefl _ this
  · exact hx h'
  · have := R.ofQ_lt.2 h'; rw [h] at this; exact R.lt_irrefl _ this

/-- A rational point is a real point. -/
theorem conicR_of_Q {a b c : Int} (h : ConicSolvableQ a b c) : ConicSolvableR a b c := by
  obtain ⟨x, y, z, hnt, h⟩ := h
  refine ⟨R.ofQ x, R.ofQ y, R.ofQ z, ?_, congrArg R.ofQ h⟩
  rcases hnt with h' | h' | h'
  · exact Or.inl (R_ofQ_ne_zero h')
  · exact Or.inr (Or.inl (R_ofQ_ne_zero h'))
  · exact Or.inr (Or.inr (R_ofQ_ne_zero h'))

/-- A rational point is a `p`-adic point. -/
theorem conicQp_of_Q {a b c : Int} (p : Nat) [PrimeP p] (h : ConicSolvableQ a b c) :
    ConicSolvableQp p a b c := by
  obtain ⟨x, y, z, hnt, h⟩ := h
  refine ⟨Qp.ofQ x, Qp.ofQ y, Qp.ofQ z, ?_, ?_⟩
  · rcases hnt with h' | h' | h'
    · exact Or.inl (Qp.ofQ_ne_zero h')
    · exact Or.inr (Or.inl (Qp.ofQ_ne_zero h'))
    · exact Or.inr (Or.inr (Qp.ofQ_ne_zero h'))
  · have := congrArg (Qp.ofQ (p := p)) h
    rw [Qp.ofQ_add, Qp.ofQ_add, Qp.ofQ_mul, Qp.ofQ_mul, Qp.ofQ_mul, Qp.ofQ_mul, Qp.ofQ_mul,
      Qp.ofQ_mul, Qp.ofQ_intCast, Qp.ofQ_intCast, Qp.ofQ_intCast, Qp.ofQ_zero] at this
    exact this

/-! ## The real place -/

/-- A non-zero integer is non-zero in ℝ. -/
theorem R_intCast_ne_zero {m : Int} (hm : m ≠ 0) : (m : R) ≠ 0 :=
  R_ofQ_ne_zero fun h => hm (Q_intCast_eq_zero h)

/-- **Real points and the Hilbert conic.** For `b ≠ 0`, `a x² + b y² + c z² = 0` has a
non-trivial real point iff `w² = −ab x² − bc z²` does (`w = b y`). -/
theorem conicR_iff_hilbert {a b c : Int} (hb : b ≠ 0) :
    ConicSolvableR a b c ↔ HilbertSolvableR ((-(a * b) : Int) : R) ((-(b * c) : Int) : R) := by
  have hb' := R_intCast_ne_zero hb
  simp only [Ring.intCast_neg, Ring.intCast_mul]
  constructor
  · rintro ⟨x, y, z, hnt, h⟩
    refine ⟨x, z, (b : R) * y, ?_, ?_⟩
    · rcases hnt with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (by grind))
      · exact Or.inr (Or.inl h')
    · have : (b : R) * (y * y) = -((a : R) * (x * x)) - (c : R) * (z * z) := by grind
      grind
  · rintro ⟨x, z, w, hnt, h⟩
    refine ⟨x, w * (b : R)⁻¹, z, ?_, ?_⟩
    · rcases hnt with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inl (by grind))
    · have hi := Field.mul_inv_cancel hb'
      have : (b : R) * (w * (b : R)⁻¹ * (w * (b : R)⁻¹)) * (b : R) = w * w := by grind
      grind

/-- **Real points.** For non-zero integers `a, b, c`, the conic `a x² + b y² + c z² = 0` has a
non-trivial real point iff `a, b, c` are not all of the same sign. -/
theorem conicR_iff {a b c : Int} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ConicSolvableR a b c ↔ MixedSigns a b c := by
  rw [conicR_iff_hilbert hb, hilbertSolvableR_iff]
  have e1 : ((-(a * b) : Int) : R) < 0 ↔ -(a * b) < 0 := OF.intCast_lt (K := R) (b := 0)
  have e2 : ((-(b * c) : Int) : R) < 0 ↔ -(b * c) < 0 := OF.intCast_lt (K := R) (b := 0)
  rw [e1, e2]
  have hab := Int.mul_ne_zero ha hb
  have hbc := Int.mul_ne_zero hb hc
  constructor
  · intro h
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact h ⟨by have := Int.mul_pos h1 h2; omega, by have := Int.mul_pos h2 h3; omega⟩
    · rintro ⟨h1, h2, h3⟩
      have e3 := Int.mul_pos (Int.neg_pos.2 h1) (Int.neg_pos.2 h2)
      have e4 := Int.mul_pos (Int.neg_pos.2 h2) (Int.neg_pos.2 h3)
      rw [Int.neg_mul_neg] at e3 e4
      exact h ⟨by omega, by omega⟩
  · rintro ⟨hp, hn⟩ ⟨h1, h2⟩
    -- `ab > 0` and `bc > 0` force equal signs
    rcases Int.lt_or_lt_of_ne hb with hb' | hb'
    · have ha' : a < 0 := by
        apply Classical.byContradiction; intro h'
        have := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ a by omega) (Int.le_of_lt hb')
        omega
      have hc' : c < 0 := by
        apply Classical.byContradiction; intro h'
        have := Int.mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt hb') (show 0 ≤ c by omega)
        omega
      exact hn ⟨ha', hb', hc'⟩
    · have ha' : 0 < a := by
        apply Classical.byContradiction; intro h'
        have := Int.mul_nonpos_of_nonpos_of_nonneg (show a ≤ 0 by omega) (Int.le_of_lt hb')
        omega
      have hc' : 0 < c := by
        apply Classical.byContradiction; intro h'
        have := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hb') (show c ≤ 0 by omega)
        omega
      exact hp ⟨ha', hb', hc'⟩

/-! ## The `p`-adic places -/

/-- A non-zero integer is non-zero in ℚₚ. -/
theorem Qp_intCast_ne_zero {p : Nat} [PrimeP p] {m : Int} (hm : m ≠ 0) : (m : Qp p) ≠ 0 := by
  have e : (m : Qp p) = Qp.ofQ (m : Q) := (Qp.ofQ_intCast m).symm
  rw [e]; exact Qp.ofQ_ne_zero fun h => hm (Q_intCast_eq_zero h)

/-- ℚₚ-points are invariant under the cyclic permutation of the coefficients. -/
theorem ConicSolvableQp.rotate {p : Nat} [PrimeP p] {a b c : Int}
    (h : ConicSolvableQp p a b c) : ConicSolvableQp p b c a := by
  obtain ⟨x, y, z, hnt, h⟩ := h
  refine ⟨y, z, x, ?_, by rw [← h]; grind⟩
  rcases hnt with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- The Hilbert conic is symmetric: `z² = A x² + B y²` vs `z² = B x² + A y²`. -/
theorem hilbertSolvable_swap {p : Nat} [PrimeP p] {A B : Qp p} (h : Qp.HilbertSolvable A B) :
    Qp.HilbertSolvable B A := by
  obtain ⟨x, y, z, hne, h⟩ := h
  exact ⟨y, x, z, by rcases hne with h | h | h <;> simp_all, by rw [h]; grind⟩

/-- **ℚₚ-points and the Hilbert conic.** For `b ≠ 0`, `a x² + b y² + c z² = 0` has a
non-trivial point in ℚₚ iff `w² = −ab x² − bc z²` does (`w = b y`). -/
theorem conicQp_iff_hilbert {p : Nat} [PrimeP p] {a b c : Int} (hb : b ≠ 0) :
    ConicSolvableQp p a b c ↔
      Qp.HilbertSolvable ((-(a * b) : Int) : Qp p) ((-(b * c) : Int) : Qp p) := by
  have hb' := Qp_intCast_ne_zero (p := p) hb
  simp only [Ring.intCast_neg, Ring.intCast_mul]
  constructor
  · rintro ⟨x, y, z, hnt, h⟩
    refine ⟨x, z, (b : Qp p) * y, ?_, ?_⟩
    · rcases hnt with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (by grind))
      · exact Or.inr (Or.inl h')
    · have : (b : Qp p) * (y * y) = -((a : Qp p) * (x * x)) - (c : Qp p) * (z * z) := by grind
      grind
  · rintro ⟨x, z, w, hnt, h⟩
    refine ⟨x, w * (b : Qp p)⁻¹, z, ?_, ?_⟩
    · rcases hnt with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inl (by grind))
    · have hi := Field.mul_inv_cancel hb'
      have : (b : Qp p) * (w * (b : Qp p)⁻¹ * (w * (b : Qp p)⁻¹)) * (b : Qp p) = w * w := by grind
      grind

/-- **The local condition at an odd prime `p ∣ a`.** If `a` is squarefree, `p ∤ bc`, and
`a x² + b y² + c z² = 0` has a non-trivial point in ℚₚ, then `−bc` is a square modulo `p`.
Writing `a = p a₁`, the conic is equivalent to `w² = u x² + p v y²` with the `p`-adic units
`u = −bc`, `v = −a₁ b`, and `Qp.hilbertSolvable_unit_pv_iff` applies. -/
theorem isSqMod_of_Qp {p : Nat} [hP : PrimeP p] (hodd : p % 2 = 1) {a b c : Int}
    (hpa : (p : Int) ∣ a) (sa : Squarefree a) (hpb : ¬ (p : Int) ∣ b) (hpc : ¬ (p : Int) ∣ c)
    (h : ConicSolvableQp p a b c) : IsSqMod (-(b * c)) p := by
  have hb : b ≠ 0 := fun h0 => hpb (h0 ▸ Int.dvd_zero _)
  have hH := hilbertSolvable_swap ((conicQp_iff_hilbert hb).1 h)
  obtain ⟨a₁, rfl⟩ := hpa
  have hna₁ := sa.not_dvd_cofactor hP.prime rfl
  have hu : Zp.IsPUnit (((-(b * c)) : Int) : Zp p) := Qp.isPUnit_intCast (fun hd => by
    rcases prime_dvd_mul hP.prime (Int.dvd_neg.1 hd) with h' | h'
    · exact hpb h'
    · exact hpc h')
  have hv : Zp.IsPUnit (((-(a₁ * b)) : Int) : Zp p) := Qp.isPUnit_intCast (fun hd => by
    rcases prime_dvd_mul hP.prime (Int.dvd_neg.1 hd) with h' | h'
    · exact hna₁ h'
    · exact hpb h')
  have e2 : Qp.ofZp ((p : Zp p) * (((-(a₁ * b)) : Int) : Zp p)) =
      (((-((p : Int) * a₁ * b)) : Int) : Qp p) := by
    rw [Qp.ofZp_mul]
    show ((p : Int) : Qp p) * ((-(a₁ * b) : Int) : Qp p) = _
    simp only [Ring.intCast_neg, Ring.intCast_mul]; grind
  have e1 : Qp.ofZp (((-(b * c)) : Int) : Zp p) = (((-(b * c)) : Int) : Qp p) := rfl
  rw [← e1, ← e2] at hH
  obtain ⟨t, ht⟩ := (Qp.hilbertSolvable_unit_pv_iff hodd hu hv).1 hH
  have ht' := Zp.modPow_intCast.1 ht
  rw [Int.pow_one] at ht'
  exact ⟨t, by rw [show t * t - -(b * c) = -(-(b * c) - t * t) by omega]; exact Int.dvd_neg.2 ht'⟩

/-- Points over every ℚₚ give Legendre's condition at `a`: square modulo every odd prime factor
(`isSqMod_of_Qp`) and modulo `2` (always), then glued by the Chinese remainder theorem. -/
theorem isSqMod_of_local {a b c : Int} (h : Admissible a b c)
    (hloc : ∀ (p : Nat) [PrimeP p], ConicSolvableQp p a b c) : IsSqMod (-(b * c)) a :=
  Squarefree.glue _ rfl h.ha h.sa fun p hp hpa => by
    by_cases h2 : p = 2
    · subst h2; exact isSqMod_two _
    · haveI : PrimeP p := ⟨hp⟩
      exact isSqMod_of_Qp (prime_odd_of_ne_two hp h2) hpa h.sa
        (fun hpb => h.cab.not_dvd hp hpa hpb) (fun hpc => h.cca.not_dvd hp hpc hpa) (hloc p)

/-- **Local points give Legendre's congruences.** If the conic has a non-trivial point in every
ℚₚ, then `−bc`, `−ca`, `−ab` are squares modulo `|a|`, `|b|`, `|c|`. -/
theorem legendreCond_of_local {a b c : Int} (h : Admissible a b c)
    (hloc : ∀ (p : Nat) [PrimeP p], ConicSolvableQp p a b c) : LegendreCond a b c :=
  ⟨isSqMod_of_local h hloc, isSqMod_of_local h.rotate fun p _ => (hloc p).rotate,
    isSqMod_of_local h.rotate.rotate fun p _ => (hloc p).rotate.rotate⟩

/-! ## The local–global principle -/

/-- **Hasse's principle for conics over ℚ.** (Hasse 1921, from Legendre 1785.) For non-zero,
squarefree, pairwise coprime integers `a, b, c`, the conic `a x² + b y² + c z² = 0` has a
non-trivial rational point iff it has a non-trivial point over ℝ and over ℚₚ for every prime
`p`. -/
theorem hasse_conic {a b c : Int} (h : Admissible a b c) :
    ConicSolvableQ a b c ↔ ConicSolvableR a b c ∧ ∀ (p : Nat) [PrimeP p], ConicSolvableQp p a b c :=
  ⟨fun hq => ⟨conicR_of_Q hq, fun p _ => conicQp_of_Q p hq⟩,
    fun ⟨hr, hp⟩ => conicQ_iff_Z.2 (legendre_sufficient h ((conicR_iff h.ha h.hb h.hc).1 hr)
      (legendreCond_of_local h hp))⟩

/-- **The local conditions are Legendre's conditions.** For admissible `a, b, c`: a real point
and a point in every ℚₚ exist iff the signs are mixed and `−bc`, `−ca`, `−ab` are squares
modulo `|a|`, `|b|`, `|c|`. -/
theorem local_iff_legendre {a b c : Int} (h : Admissible a b c) :
    (ConicSolvableR a b c ∧ ∀ (p : Nat) [PrimeP p], ConicSolvableQp p a b c) ↔
      MixedSigns a b c ∧ LegendreCond a b c :=
  ⟨fun ⟨hr, hp⟩ => ⟨(conicR_iff h.ha h.hb h.hc).1 hr, legendreCond_of_local h hp⟩,
    fun hc => (hasse_conic h).1 (conicQ_iff_Z.2 ((legendre h).2 hc))⟩

/-- The real Hilbert symbol is `1` exactly on solvable Hilbert conics. -/
theorem hilbertInf_eq_one_iff_solvable (A B : R) : hilbertInf A B = 1 ↔ HilbertSolvableR A B :=
  (hilbertInf_eq_one_iff A B).trans (hilbertSolvableR_iff A B).symm

/-- **Hasse's principle for conics, with Hilbert symbols.** For admissible `a, b, c`, the conic
`a x² + b y² + c z² = 0` has a non-trivial rational point iff `(−ab, −bc)_v = 1` at every place
`v` of ℚ: at `∞` and at every prime `ℓ`. -/
theorem hasse_conic_hilbert {a b c : Int} (h : Admissible a b c) :
    ConicSolvableQ a b c ↔ hilbertInfQ ((-(a * b) : Int) : Q) ((-(b * c) : Int) : Q) = 1 ∧
      ∀ ℓ : Nat, hilbertAt ℓ ((-(a * b) : Int) : Q) ((-(b * c) : Int) : Q) = 1 := by
  rw [hasse_conic h]
  apply and_congr
  · exact (conicR_iff_hilbert h.hb).trans (hilbertInf_eq_one_iff_solvable _ _).symm
  · constructor
    · intro hp ℓ
      by_cases hℓ : Prime ℓ
      · haveI : PrimeP ℓ := ⟨hℓ⟩
        rw [hilbertAt_eq, Qp.ofQ_intCast, Qp.ofQ_intCast]
        exact (Qp.hilbert_eq_one_iff _ _).2 ((conicQp_iff_hilbert h.hb).1 (hp ℓ))
      · exact hilbertAt_of_not_prime hℓ _ _
    · intro hp ℓ hℓ
      have := hp ℓ
      rw [hilbertAt_eq, Qp.ofQ_intCast, Qp.ofQ_intCast] at this
      exact (conicQp_iff_hilbert h.hb).2 ((Qp.hilbert_eq_one_iff _ _).1 this)

/-! ## Examples -/

/-- `3` is prime. -/
theorem prime_three : Prime 3 :=
  ⟨by omega, fun d hd => by
    have := Nat.le_of_dvd (by omega) hd
    have key : ∀ d, d < 4 → d ∣ 3 → d = 1 ∨ d = 3 := by decide
    exact key d (by omega) hd⟩

/-- `3` as a prime, for ℚ₃. -/
instance primeP_three : PrimeP 3 := ⟨prime_three⟩

/-- **Example: `x² + y² = 3 z²` fails the Hasse test at `3`.** The conic has a real point, but
no non-trivial point in ℚ₃ (it would make `−1` a square modulo `3`), hence no non-trivial
rational point. -/
theorem hasse_example_three :
    ConicSolvableR 1 1 (-3) ∧ ¬ ConicSolvableQp 3 1 1 (-3) ∧ ¬ ConicSolvableQ 1 1 (-3) := by
  have h3 : ¬ ConicSolvableQp 3 1 1 (-3) := fun h => by
    have := isSqMod_of_Qp (p := 3) (by decide) (a := -3) (b := 1) (c := 1) ⟨-1, by decide⟩
      (squarefree_small (by decide) (by decide) (by decide)) (by decide) (by decide)
      h.rotate.rotate
    exact not_isSqMod_neg_one_three this
  refine ⟨(conicR_iff (by decide) (by decide) (by decide)).2 ⟨by decide, by decide⟩, h3,
    fun hq => h3 (conicQp_of_Q 3 hq)⟩

/-- **Example: `x² + y² = 5 z²` has a non-trivial rational point.** It comes from `(1, 2, 1)`, so by
`hasse_conic` it has points over ℝ and every ℚₚ. -/
theorem hasse_example_five : ConicSolvableQ 1 1 (-5) ∧ ConicSolvableR 1 1 (-5) ∧
    ∀ (p : Nat) [PrimeP p], ConicSolvableQp p 1 1 (-5) :=
  have hq := conicQ_iff_Z.2 legendre_example_five.1
  ⟨hq, conicR_of_Q hq, fun p _ => conicQp_of_Q p hq⟩

end Legendre

end Foundations.Langlands.Padic
