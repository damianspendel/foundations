import Foundations.Langlands.Elliptic.Weierstrass

/-!
# Negation is a homomorphism, and cancellation

Two special cases of associativity are needed before the general case: `−(P + Q) = −P + −Q`,
and the cancellation law `P + (−P + Q) = Q`. Geometrically the second one says that the line
through `−P` and `Q` meets `E` again at `−(−P + Q)`, and its mirror image is the line through
`P` and `−P + Q`, whose third point is therefore `−Q`.

The algebra is organised around one observation (`slope_eq_of_rel`): the slope used by the
addition law is *characterised* by the two chord relations
`y₂ − y₁ = λ(x₂ − x₁)` and `λ(y₁ + y₂) = x₁² + x₁x₂ + x₂² + a`, uniformly for chords and
tangents. So to compute a sum it suffices to exhibit some `λ` satisfying both relations, and
`chain_rel` produces the second relation for the next addition along the same line.

The cancellation law uses the hypothesis `4a³ + 27b² ≠ 0`: a line of finite slope meeting `E`
twice at a point `(x₁, 0)` would force `x₁` to be a double root of `x³ + ax + b`.
-/

namespace Foundations.Langlands.Elliptic

universe u

variable {K : Type u} [Lean.Grind.Field K]

namespace Curve

variable (E : Curve K)

/-- **The slope is characterised by the chord relations.** If the sum of `(x₁, y₁)` and
`(x₂, y₂)` is not `O` and `λ` satisfies `y₂ − y₁ = λ(x₂ − x₁)` and
`λ(y₁ + y₂) = x₁² + x₁x₂ + x₂² + a`, then `λ` is the slope used by the addition law. -/
theorem slope_eq_of_rel [DecidableEq K] {x₁ y₁ x₂ y₂ l : K} (h₁ : E.OnCurve x₁ y₁)
    (h₂ : E.OnCurve x₂ y₂) (hn : ¬ (x₁ = x₂ ∧ y₁ + y₂ = 0)) (r₁ : y₂ - y₁ = l * (x₂ - x₁))
    (r₂ : l * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a) : E.slope x₁ y₁ x₂ y₂ = l := by
  obtain ⟨s₁, s₂⟩ := E.slope_rel h₁ h₂ hn
  by_cases hx : x₁ = x₂
  · have hy : y₁ + y₂ ≠ 0 := fun h => hn ⟨hx, h⟩
    subst hx
    have : (E.slope x₁ y₁ x₁ y₂ - l) * (y₁ + y₂) = 0 := by grind
    grind
  · have d : x₂ - x₁ ≠ 0 := fun h => hx (by grind)
    have : (E.slope x₁ y₁ x₂ y₂ - l) * (x₂ - x₁) = 0 := by grind
    grind

/-- **Second chord relation along a line.** If `(x₃, y₃)` and `(x₄, y₄)` lie on a line of slope
`n` that satisfies the second chord relation for them, and `(x_Q, y_Q)` is the third point of
that line (`x_Q = n² − x₃ − x₄`, `y_Q = y₃ + n(x_Q − x₃)`), then `n` satisfies the second chord
relation for `(x_Q, y_Q)` and `(x₃, y₃)`. Pure algebra. -/
theorem chain_rel {n x₃ x₄ xQ y₃ y₄ yQ : K}
    (F₁ : n * (y₃ + y₄) = x₃ ^ 2 + x₃ * x₄ + x₄ ^ 2 + E.a) (F₂ : xQ = n ^ 2 - x₃ - x₄)
    (F₃ : yQ = y₃ + n * (xQ - x₃)) (F₅ : y₄ - y₃ = n * (x₄ - x₃)) :
    n * (yQ + y₃) = xQ ^ 2 + xQ * x₃ + x₃ ^ 2 + E.a := by
  subst F₂ F₃; grind

end Curve

namespace Point

variable {E : Curve K} [DecidableEq K]

/-- **Computing a sum from a slope.** If the sum of two affine points is not `O` and `λ`
satisfies the two chord relations, the sum is `(λ² − x₁ − x₂, λ(x₁ − x₃) − y₁)`. -/
theorem addSome_of_rel {x₁ y₁ x₂ y₂ l : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂)
    (hn : ¬ (x₁ = x₂ ∧ y₁ + y₂ = 0)) (r₁ : y₂ - y₁ = l * (x₂ - x₁))
    (r₂ : l * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a) :
    ∃ h, addSome x₁ y₁ h₁ x₂ y₂ h₂ =
      some (l ^ 2 - x₁ - x₂) (l * (x₁ - (l ^ 2 - x₁ - x₂)) - y₁) h := by
  have hs := E.slope_eq_of_rel h₁ h₂ hn r₁ r₂
  refine ⟨E.third_point_onCurve h₁ r₁ r₂, ?_⟩
  rw [addSome_of_not h₁ h₂ hn, some_eq_some, hs]
  exact ⟨rfl, rfl⟩

/-- The sum of two affine points is `O` exactly when they are mirror images. -/
theorem addSome_eq_zero_iff {x₁ y₁ x₂ y₂ : K} (h₁ : E.OnCurve x₁ y₁) (h₂ : E.OnCurve x₂ y₂) :
    addSome x₁ y₁ h₁ x₂ y₂ h₂ = zero ↔ (x₁ = x₂ ∧ y₁ + y₂ = 0) := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    rw [addSome_of_not h₁ h₂ hn] at h
    cases h
  · intro h
    unfold addSome; rw [dite_eq_left_of_eq_true (eq_true h)]

/-- **Negation is additive.** `−(P + Q) = −P + −Q`. -/
theorem neg_add (P Q : Point E) : -(P + Q) = -P + -Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      show neg (addSome x₁ y₁ h₁ x₂ y₂ h₂) =
        addSome x₁ (-y₁) (E.onCurve_neg h₁) x₂ (-y₂) (E.onCurve_neg h₂)
      by_cases hn : x₁ = x₂ ∧ y₁ + y₂ = 0
      · rw [(addSome_eq_zero_iff h₁ h₂).2 hn,
          (addSome_eq_zero_iff (E.onCurve_neg h₁) (E.onCurve_neg h₂)).2 ⟨hn.1, by grind⟩]
        rfl
      · have hn' : ¬ (x₁ = x₂ ∧ -y₁ + -y₂ = 0) := fun h => hn ⟨h.1, by grind⟩
        obtain ⟨r₁, r₂⟩ := E.slope_rel h₁ h₂ hn
        obtain ⟨h, e⟩ := addSome_of_rel (l := -E.slope x₁ y₁ x₂ y₂) (E.onCurve_neg h₁)
          (E.onCurve_neg h₂) hn' (by grind) (by grind)
        rw [e, addSome_of_not h₁ h₂ hn]
        show some _ _ _ = _
        rw [some_eq_some]
        exact ⟨by grind, by grind⟩

/-- **Cancellation.** `P + (−P + Q) = Q`. -/
theorem add_neg_add_cancel (P Q : Point E) : P + (-P + Q) = Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact add_neg_self _
    | some x₂ y₂ h₂ =>
      show some x₁ y₁ h₁ + addSome x₁ (-y₁) (E.onCurve_neg h₁) x₂ y₂ h₂ = some x₂ y₂ h₂
      by_cases hn : x₁ = x₂ ∧ -y₁ + y₂ = 0
      · rw [(addSome_eq_zero_iff _ _).2 hn]
        show some x₁ y₁ h₁ = some x₂ y₂ h₂
        rw [some_eq_some]; exact ⟨hn.1, by grind⟩
      · have h₁' := E.onCurve_neg h₁
        obtain ⟨r₁, r₂⟩ := E.slope_rel h₁' h₂ hn
        obtain ⟨hR, eR⟩ := addSome_of_rel (l := E.slope x₁ (-y₁) x₂ y₂) h₁' h₂ hn r₁ r₂
        rw [eR]
        -- abbreviations: `μ` the slope of `−P, Q`, and `R = −P + Q = (xR, yR)`
        generalize hμ : E.slope x₁ (-y₁) x₂ y₂ = μ at r₁ r₂ hR ⊢
        -- `P + R ≠ O`
        have hPR : ¬ (x₁ = μ ^ 2 - x₁ - x₂ ∧ y₁ + (μ * (x₁ - (μ ^ 2 - x₁ - x₂)) - -y₁) = 0) := by
          rintro ⟨hx, hy⟩
          have hy0 : y₁ = 0 := by
            have : (2 : K) * y₁ = 0 := by rw [← hx] at hy; grind
            have h2 := E.two_ne
            grind
          subst hy0
          have ha : 3 * x₁ ^ 2 + E.a = 0 := by grind
          apply E.disc_ne
          unfold Curve.OnCurve at h₁
          grind
        -- the slope of `P, R` is `−μ`
        have s₁ : (μ * (x₁ - (μ ^ 2 - x₁ - x₂)) - -y₁) - y₁ = -μ * ((μ ^ 2 - x₁ - x₂) - x₁) := by
          grind
        have s₂ := E.chain_rel (n := μ) (x₃ := x₁) (x₄ := x₂) (xQ := μ ^ 2 - x₁ - x₂)
          (y₃ := -y₁) (y₄ := y₂) (yQ := -(μ * (x₁ - (μ ^ 2 - x₁ - x₂)) - -y₁)) r₂ rfl (by grind)
          r₁
        obtain ⟨hS, eS⟩ := addSome_of_rel (l := -μ) h₁ hR hPR s₁ (by grind)
        rw [some_add_some, eS, some_eq_some]
        exact ⟨by grind, by grind⟩

end Point

end Foundations.Langlands.Elliptic
