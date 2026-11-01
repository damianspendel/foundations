import Foundations.Geometry.KleinSegment

/-!
# The independence of the parallel postulate

Euclid's fifth postulate was, for two millennia, the one blemish on the
*Elements*: less evident than the others, it seemed a theorem awaiting proof.
Proclus, Ibn al-Haytham, Omar Khayyám, Nasir al-Din al-Tusi, Wallis, Saccheri
and Lambert all tried. The question was finally answered in the negative — the
postulate is **independent** of the other axioms — and the answer required a
new kind of argument: not a deduction *within* geometry, but the construction of
a **model**, a structure in which all the other axioms are true and the fifth is
false. If the postulate were provable from the others, it would be true in every
such structure.

Beltrami (1868) gave the first such model; Klein (1871) recast it projectively;
Hilbert's *Grundlagen* (1899) made the method of models the standard tool of
axiomatics. Here, with Tarski's axioms:

* the **Klein model** (`kleinNeutral`) satisfies every Tarski axiom except
  Euclid's — (A1)–(A9) and continuity (A11) — but **refutes Euclid's axiom**
  (`Klein.not_euclid`), and indeed through a point off a line there are two
  different lines which never meet it (`klein_playfair_fails`);
* the **Cartesian plane** `ℝ²` satisfies all of them, Euclid's axiom included.

Both models are built inside the real numbers of Part II, so the result is a
*relative* consistency statement: if the reals are consistent, then so are both
Euclidean and hyperbolic geometry, and neither the parallel postulate nor its
negation follows from the remaining axioms.

The philosophical consequences were profound. Kant had taught that Euclidean
geometry is *synthetic a priori*: true of space necessarily, as the form of our
outer intuition. After Gauss, Bolyai, Lobachevsky and Riemann, geometry split
in two: **pure geometry** became the study of axiom systems and their models —
hypothetical, "if these axioms, then these theorems" (Hilbert: one must be able to
say "tables, chairs and beer mugs" instead of points, lines and planes) — while
the geometry of *physical* space became an empirical question, which Einstein's
general relativity (1915) answered with a non-Euclidean geometry.
-/

namespace Foundations.Geometry

open Foundations.Numbers

/-- A **neutral (absolute) plane**: Tarski's axioms *without Euclid's axiom* — the
geometry common to the Euclidean and the hyperbolic plane. -/
structure NeutralPlane (P : Type) where
  /-- Betweenness. -/
  B : P → P → P → Prop
  /-- Equidistance. -/
  Cong : P → P → P → P → Prop
  /-- (A1) -/
  cong_pseudo_refl : ∀ a b, Cong a b b a
  /-- (A2) -/
  cong_inner_trans : ∀ a b p q r s, Cong a b p q → Cong a b r s → Cong p q r s
  /-- (A3) -/
  cong_identity : ∀ a b c, Cong a b c c → a = b
  /-- (A4) -/
  segment_construction : ∀ q a b c, ∃ x, B q a x ∧ Cong a x b c
  /-- (A5) -/
  five_segment : ∀ a b c d a' b' c' d', a ≠ b → B a b c → B a' b' c' →
    Cong a b a' b' → Cong b c b' c' → Cong a d a' d' → Cong b d b' d' → Cong c d c' d'
  /-- (A6) -/
  bet_identity : ∀ a b, B a b a → a = b
  /-- (A7) -/
  pasch : ∀ a b c p q, B a p c → B b q c → ∃ x, B p x b ∧ B q x a
  /-- (A8) -/
  lower_dim : ∃ a b c, ¬ B a b c ∧ ¬ B b c a ∧ ¬ B c a b
  /-- (A9) -/
  upper_dim : ∀ a b c p q, p ≠ q → Cong a p a q → Cong b p b q → Cong c p c q →
    B a b c ∨ B b c a ∨ B c a b
  /-- (A11) -/
  continuity : ∀ φ ψ : P → Prop, (∃ a, ∀ x y, φ x → ψ y → B a x y) →
    ∃ b, ∀ x y, φ x → ψ y → B x b y

/-- **Euclid's axiom** (A10) for a neutral plane. -/
def EuclidAxiom {P : Type} (N : NeutralPlane P) : Prop :=
  ∀ a b c d t, N.B a d t → N.B b d c → a ≠ d → ∃ x y, N.B a b x ∧ N.B a c y ∧ N.B x t y

/-- Every Tarski plane is a neutral plane. -/
def TarskiPlane.toNeutral (P : Type) [TarskiPlane P] : NeutralPlane P where
  B := TarskiPlane.B
  Cong := TarskiPlane.Cong
  cong_pseudo_refl := TarskiPlane.cong_pseudo_refl
  cong_inner_trans := TarskiPlane.cong_inner_trans
  cong_identity := TarskiPlane.cong_identity
  segment_construction := TarskiPlane.segment_construction
  five_segment := TarskiPlane.five_segment
  bet_identity := TarskiPlane.bet_identity
  pasch := TarskiPlane.pasch
  lower_dim := TarskiPlane.lower_dim
  upper_dim := TarskiPlane.upper_dim
  continuity := TarskiPlane.continuity

/-- A Tarski plane satisfies Euclid's axiom (by definition). -/
theorem TarskiPlane.toNeutral_euclid (P : Type) [TarskiPlane P] :
    EuclidAxiom (TarskiPlane.toNeutral P) :=
  TarskiPlane.euclid

/-- **The Klein model is a neutral plane**: it satisfies all of Tarski's axioms except
Euclid's. -/
noncomputable def kleinNeutral : NeutralPlane Klein.KPt where
  B := Klein.KBet
  Cong := Klein.KCong
  cong_pseudo_refl := Klein.cong_pseudo_refl
  cong_inner_trans := Klein.cong_inner_trans
  cong_identity := Klein.cong_identity
  segment_construction := Klein.segment_construction
  five_segment := Klein.five_segment
  bet_identity := Klein.bet_identity
  pasch := Klein.pasch
  lower_dim := Klein.lower_dim
  upper_dim := Klein.upper_dim
  continuity := Klein.continuity

/-- **In the Klein model Euclid's axiom fails.** -/
theorem klein_not_euclid : ¬ EuclidAxiom kleinNeutral := Klein.not_euclid

/-- **The independence of the parallel postulate.** There is a model of Tarski's axioms
(A1)–(A9) and (A11) in which Euclid's axiom (A10) fails — the Klein model — and one in
which it holds — the Cartesian plane `ℝ²`. Hence Euclid's axiom is neither provable nor
refutable from the other axioms (relative to the consistency of the real numbers). -/
theorem parallel_postulate_independent :
    (∃ (P : Type) (N : NeutralPlane P), ¬ EuclidAxiom N) ∧
    (∃ (P : Type) (N : NeutralPlane P), EuclidAxiom N) :=
  ⟨⟨Klein.KPt, kleinNeutral, klein_not_euclid⟩,
   ⟨Pt R, TarskiPlane.toNeutral (Pt R), TarskiPlane.toNeutral_euclid (Pt R)⟩⟩

/-- **Euclid's axiom is not a theorem of neutral geometry**: it does not hold in every
model of the other axioms. -/
theorem euclid_not_provable : ¬ ∀ (P : Type) (N : NeutralPlane P), EuclidAxiom N :=
  fun h => klein_not_euclid (h _ kleinNeutral)

/-- **Nor is its negation**: Euclid's axiom is consistent with neutral geometry. -/
theorem not_euclid_not_provable : ¬ ∀ (P : Type) (N : NeutralPlane P), ¬ EuclidAxiom N :=
  fun h => h _ (TarskiPlane.toNeutral (Pt R)) (TarskiPlane.toNeutral_euclid (Pt R))

/-! ## Two parallels through one point -/

/-- **Collinearity** in a neutral plane: one of the three points lies between the others. -/
def NeutralPlane.Col {P : Type} (N : NeutralPlane P) (a b c : P) : Prop :=
  N.B a b c ∨ N.B b c a ∨ N.B c a b

/-- In the Klein model, collinear points have vanishing cross product. -/
theorem Klein.col_cross {a b c : Klein.KPt} (h : kleinNeutral.Col a b c) :
    (b.1.x - a.1.x) * (c.1.y - a.1.y) - (b.1.y - a.1.y) * (c.1.x - a.1.x) = 0 := by
  rcases h with h | h | h
  · exact Pt.cross_of_bet h
  · have := Pt.cross_of_bet (show Pt.Bet b.1 c.1 a.1 from h); grind
  · have := Pt.cross_of_bet (show Pt.Bet c.1 a.1 b.1 from h); grind

/-- **Playfair's axiom fails in the Klein model.** The point `P = (0, ½)` lies off the
line `ℓ` through `O = (0, 0)` and `E = (½, 0)`; the lines `PQ₁` and `PQ₂`, with
`Q₁ = (½, ½)` and `Q₂ = (½, ¾)`, are different, and neither meets `ℓ` (the second would
meet it only at `(−1, 0)`, on the boundary circle — "at infinity"). -/
theorem klein_playfair_fails :
    ∃ O E P Q₁ Q₂ : Klein.KPt, ¬ kleinNeutral.Col O E P ∧ ¬ kleinNeutral.Col P Q₁ Q₂ ∧
      (∀ z, kleinNeutral.Col O E z → ¬ kleinNeutral.Col P Q₁ z) ∧
      (∀ z, kleinNeutral.Col O E z → ¬ kleinNeutral.Col P Q₂ z) := by
  refine ⟨⟨⟨0, 0⟩, by unfold Klein.n2; grind⟩, ⟨⟨1 / 2, 0⟩, by unfold Klein.n2; grind⟩,
    ⟨⟨0, 1 / 2⟩, by unfold Klein.n2; grind⟩, ⟨⟨1 / 2, 1 / 2⟩, by unfold Klein.n2; grind⟩,
    ⟨⟨1 / 2, 3 / 4⟩, by unfold Klein.n2; grind⟩, ?_, ?_, ?_, ?_⟩
  · intro h; have := Klein.col_cross h; dsimp only at this; grind
  · intro h; have := Klein.col_cross h; dsimp only at this; grind
  · intro z h₁ h₂
    have := Klein.col_cross h₁; have := Klein.col_cross h₂
    dsimp only at *; grind
  · intro z h₁ h₂
    have e₁ := Klein.col_cross h₁; have e₂ := Klein.col_cross h₂
    have hz := z.2
    unfold Klein.n2 at hz
    dsimp only at e₁ e₂
    have hy : z.1.y = 0 := by grind
    have hx : z.1.x = -1 := by grind
    rw [hx, hy] at hz
    grind

end Foundations.Geometry
