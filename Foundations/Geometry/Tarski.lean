/-!
# Tarski's axioms for plane geometry

Euclid's *Elements* (c. 300 BC) was for two thousand years the model of a
deductive science, yet its proofs rely on facts nowhere stated — that two
circles meet, that a line entering a triangle must leave it. Hilbert's
*Grundlagen der Geometrie* (1899) repaired this with twenty axioms in several
sorts (points, lines, planes) and primitive relations of incidence, order and
congruence. Alfred Tarski (lectures of 1926–27, published 1959; the definitive
system in Schwabhäuser–Szmielew–Tarski, *Metamathematische Methoden in der
Geometrie*, 1983) went further: **one sort** (points) and **two relations**,

* *betweenness* `B a b c` — "`b` lies on the segment from `a` to `c`" (endpoints
  allowed), and
* *equidistance* `a b ≡ c d` — "the segment `ab` is as long as `cd`".

Lines, circles, angles and triangles are all *defined*. The axioms below are
those of Tarski's system for the plane:

1. reflexivity of congruence `ab ≡ ba`; 2. its (pseudo-)transitivity;
3. identity: `ab ≡ cc` only if `a = b`; 4. **segment construction**: any
segment can be laid off on any ray; 5. the **five-segment axiom** (a form of
the side-angle-side congruence criterion); 6. identity of betweenness;
7. **Pasch's axiom** (inner form); 8.–9. lower and upper **dimension** axioms
(the space is exactly two-dimensional); 10. **Euclid's axiom** (in Tarski's
form, equivalent to the parallel postulate); 11. the **continuity** schema
(Dedekind cuts on lines have boundary points).

Tarski stated continuity as a schema of first-order formulas, so that his
*elementary geometry* is a first-order theory; he proved it **complete and
decidable** — every sentence about points, betweenness and equidistance is
either provable or refutable, and an algorithm decides which (by reduction to
the theory of real closed fields and quantifier elimination). We state
continuity more strongly, for arbitrary predicates (the second-order form, as
in Hilbert's completeness axiom); its models are, up to isomorphism, exactly
the planes over complete ordered fields, i.e. ℝ² (see `CartesianModel.lean`).

From the axioms we derive a few of the very first theorems of Tarski's
development: congruence is an equivalence relation, null segments are all
congruent, betweenness is symmetric, and so on — tiny facts, but here every
one must be *proved*, which is precisely the point.
-/

namespace Foundations.Geometry

/-- A **Tarski plane**: a type of points with betweenness `B` and equidistance
`Cong a b c d` (read `ab ≡ cd`) satisfying Tarski's axioms for plane Euclidean
geometry, with continuity in second-order form. -/
class TarskiPlane (P : Type) where
  /-- Betweenness: `B a b c` means `b` lies on the segment `ac` (endpoints allowed). -/
  B : P → P → P → Prop
  /-- Equidistance: `Cong a b c d` means segment `ab` is congruent to segment `cd`. -/
  Cong : P → P → P → P → Prop
  /-- (A1) **Reflexivity of congruence**: `ab ≡ ba`. -/
  cong_pseudo_refl : ∀ a b, Cong a b b a
  /-- (A2) **Transitivity of congruence** (in Tarski's form). -/
  cong_inner_trans : ∀ a b p q r s, Cong a b p q → Cong a b r s → Cong p q r s
  /-- (A3) **Identity of congruence**: only null segments are congruent to null segments. -/
  cong_identity : ∀ a b c, Cong a b c c → a = b
  /-- (A4) **Segment construction**: on the ray from `q` through `a`, beyond `a`, a segment
  congruent to `bc` can be laid off. -/
  segment_construction : ∀ q a b c, ∃ x, B q a x ∧ Cong a x b c
  /-- (A5) **Five-segment axiom**. -/
  five_segment : ∀ a b c d a' b' c' d', a ≠ b → B a b c → B a' b' c' →
    Cong a b a' b' → Cong b c b' c' → Cong a d a' d' → Cong b d b' d' → Cong c d c' d'
  /-- (A6) **Identity of betweenness**: `B a b a` only if `a = b`. -/
  bet_identity : ∀ a b, B a b a → a = b
  /-- (A7) **Pasch's axiom** (inner form): the two cevians of a triangle meet. -/
  pasch : ∀ a b c p q, B a p c → B b q c → ∃ x, B p x b ∧ B q x a
  /-- (A8) **Lower dimension**: there are three non-collinear points. -/
  lower_dim : ∃ a b c, ¬ B a b c ∧ ¬ B b c a ∧ ¬ B c a b
  /-- (A9) **Upper dimension**: three points each equidistant from two distinct points are
  collinear (so the space is at most two-dimensional). -/
  upper_dim : ∀ a b c p q, p ≠ q → Cong a p a q → Cong b p b q → Cong c p c q →
    B a b c ∨ B b c a ∨ B c a b
  /-- (A10) **Euclid's axiom** (Tarski's form of the parallel postulate): through any point
  inside an angle there is a segment meeting both arms. -/
  euclid : ∀ a b c d t, B a d t → B b d c → a ≠ d → ∃ x y, B a b x ∧ B a c y ∧ B x t y
  /-- (A11) **Continuity** (second-order form): if all `φ`-points precede all `ψ`-points as
  seen from some point `a`, then some point `b` separates them. -/
  continuity : ∀ φ ψ : P → Prop, (∃ a, ∀ x y, φ x → ψ y → B a x y) →
    ∃ b, ∀ x y, φ x → ψ y → B x b y

namespace TarskiPlane

variable {P : Type} [TarskiPlane P]

/-- Every segment is congruent to itself. -/
theorem cong_refl (a b : P) : Cong a b a b :=
  cong_inner_trans b a a b a b (cong_pseudo_refl b a) (cong_pseudo_refl b a)

/-- Congruence is symmetric. -/
theorem cong_symm {a b c d : P} (h : Cong a b c d) : Cong c d a b :=
  cong_inner_trans a b c d a b h (cong_refl a b)

/-- **Congruence is transitive.** -/
theorem cong_trans {a b c d e f : P} (h₁ : Cong a b c d) (h₂ : Cong c d e f) : Cong a b e f :=
  cong_inner_trans c d a b e f (cong_symm h₁) h₂

/-- The endpoints of the left segment can be swapped. -/
theorem cong_left_comm {a b c d : P} (h : Cong a b c d) : Cong b a c d :=
  cong_trans (cong_pseudo_refl b a) h

/-- The endpoints of the right segment can be swapped. -/
theorem cong_right_comm {a b c d : P} (h : Cong a b c d) : Cong a b d c :=
  cong_trans h (cong_pseudo_refl c d)

/-- **All null segments are congruent**: `aa ≡ bb`. -/
theorem cong_trivial (a b : P) : Cong a a b b := by
  obtain ⟨x, _, hx⟩ := segment_construction a a b b
  have : a = x := cong_identity a x b hx
  subst this
  exact hx

/-- A segment congruent to a null segment is null (the other way round). -/
theorem cong_reverse_identity {a c d : P} (h : Cong a a c d) : c = d :=
  cong_identity c d a (cong_symm h)

/-- `B a b b`: the endpoint of a segment lies on it. -/
theorem bet_trivial (a b : P) : B a b b := by
  obtain ⟨x, hb, hx⟩ := segment_construction a b b b
  have : b = x := cong_identity b x b hx
  subst this
  exact hb

/-- **Betweenness is symmetric**: `B a b c → B c b a`. Proved from Pasch's axiom. -/
theorem bet_symm {a b c : P} (h : B a b c) : B c b a := by
  obtain ⟨x, hx₁, hx₂⟩ := pasch a b c b c h (bet_trivial b c)
  have : b = x := bet_identity b x hx₁
  subst this
  exact hx₂

/-- `B a a b`: the initial point of a segment lies on it. -/
theorem bet_trivial' (a b : P) : B a a b := bet_symm (bet_trivial b a)

/-- If `b` is between `a` and `c` and `a` is between `b` and `c`, then `a = b`. -/
theorem bet_antisymm {a b c : P} (h₁ : B a b c) (h₂ : B b a c) : a = b := by
  obtain ⟨x, hx₁, hx₂⟩ := pasch a b c b a h₁ h₂
  have e₁ : b = x := bet_identity b x hx₁
  have e₂ : a = x := bet_identity a x hx₂
  rw [e₁, e₂]

/-- A point between `a` and `a` is `a`. -/
theorem bet_eq_of_bet_self {a b : P} (h : B a b a) : b = a := (bet_identity a b h).symm

/-- **There are two distinct points.** -/
theorem exists_ne : ∃ a b : P, a ≠ b := by
  obtain ⟨a, b, c, h, _, _⟩ := lower_dim (P := P)
  refine ⟨a, b, fun hab => h ?_⟩
  subst hab
  exact bet_trivial' a c

/-- **Segments can be prolonged by a non-null segment**: for any `q` and `a` there is
a point `x ≠ a` beyond `a` on the ray from `q`. -/
theorem exists_prolongation (q a : P) : ∃ x, B q a x ∧ a ≠ x := by
  obtain ⟨u, v, huv⟩ := exists_ne (P := P)
  obtain ⟨x, hb, hx⟩ := segment_construction q a u v
  refine ⟨x, hb, fun hax => huv ?_⟩
  subst hax
  exact cong_reverse_identity hx

end TarskiPlane

end Foundations.Geometry
