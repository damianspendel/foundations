/-!
# Ordinals below ε₀ in Cantor normal form

Cantor discovered (1883) that the counting numbers can be continued into the
transfinite: after `0, 1, 2, …` comes `ω`, then `ω + 1, …, ω·2, …, ω², …, ω^ω, …`.
Every ordinal below the first fixed point `ε₀ = ω^ω^ω^…` of `α ↦ ω^α` can be written
uniquely in **Cantor normal form**

`α = ω^{α₁} + ω^{α₂} + ⋯ + ω^{αₖ}`,  with `α₁ ≥ α₂ ≥ ⋯ ≥ αₖ`,

where the exponents are again ordinals below ε₀ in Cantor normal form. These
*ordinal notations* are finite trees, and their order is a purely combinatorial
comparison — yet the statement that this order is a **well-order** (no infinite
descending sequences) is mathematically strong: Gentzen (1936) proved the
consistency of Peano arithmetic by transfinite induction up to ε₀, and showed that
PA itself cannot prove this well-ordering.

We work without any set-theoretic ordinals. A notation is either `zero` or
`oadd a b`, read `ω^a + b`. The comparison `cmp` is lexicographic (first the leading
exponent, then the rest), which is the correct ordinal order on *normal* notations —
those where the exponents are non-increasing (`NF`). The main theorem is that the
order is well-founded on normal notations. Its proof is a double transfinite
induction in Gentzen's style: show by induction on the accessible `a` and then on the
accessible `b` that `ω^a + b` is accessible, and conclude by structural induction.
-/

namespace Foundations.Logic.Ordinals

/-- **Ordinal notations below ε₀**: `zero`, or `oadd a b`, read `ω^a + b`. -/
inductive ON : Type where
  /-- The ordinal `0`. -/
  | zero : ON
  /-- `oadd a b` is `ω^a + b`. -/
  | oadd : ON → ON → ON
  deriving DecidableEq

namespace ON

/-- **Comparison of notations**, lexicographic: first the leading exponents, then the
remainders. -/
def cmp : ON → ON → Ordering
  | zero, zero => .eq
  | zero, oadd _ _ => .lt
  | oadd _ _, zero => .gt
  | oadd a b, oadd a' b' =>
      match cmp a a' with
      | .eq => cmp b b'
      | o => o

/-- The strict order of notations. -/
def lt (x y : ON) : Prop := cmp x y = .lt

/-- Comparing with itself gives `eq`. -/
theorem cmp_self : ∀ x, cmp x x = .eq
  | zero => rfl
  | oadd a b => by simp only [cmp, cmp_self a, cmp_self b]

/-- Comparison is antisymmetric: swapping the arguments swaps the result. -/
theorem cmp_swap : ∀ x y, cmp y x = (cmp x y).swap
  | zero, zero => rfl
  | zero, oadd _ _ => rfl
  | oadd _ _, zero => rfl
  | oadd a b, oadd a' b' => by
      simp only [cmp, cmp_swap a a']
      cases cmp a a' <;> simp [Ordering.swap, cmp_swap b b']

/-- `eq` means equality. -/
theorem eq_of_cmp_eq : ∀ {x y}, cmp x y = .eq → x = y
  | zero, zero, _ => rfl
  | zero, oadd _ _, h => by simp [cmp] at h
  | oadd _ _, zero, h => by simp [cmp] at h
  | oadd a b, oadd a' b', h => by
      simp only [cmp] at h
      cases h₁ : cmp a a' <;> rw [h₁] at h <;> simp at h
      rw [eq_of_cmp_eq h₁, eq_of_cmp_eq h]

/-- The order on `ω^a + b`, unfolded. -/
theorem lt_oadd {a b a' b' : ON} :
    lt (oadd a b) (oadd a' b') ↔ lt a a' ∨ (a = a' ∧ lt b b') := by
  simp only [lt, cmp]
  cases h : cmp a a'
  · simp
  · simp [eq_of_cmp_eq h]
  · simp only [reduceCtorEq, false_or, false_iff, not_and]
    rintro rfl; rw [cmp_self] at h; cases h

/-- `0` is below every `ω^a + b`. -/
theorem zero_lt_oadd (a b : ON) : lt zero (oadd a b) := rfl

/-- Nothing is below `0`. -/
theorem not_lt_zero : ∀ x, ¬ lt x zero
  | zero => by simp [lt, cmp]
  | oadd _ _ => by simp [lt, cmp]

/-- **Irreflexivity.** -/
theorem lt_irrefl (x : ON) : ¬ lt x x := by simp [lt, cmp_self]

/-- **Asymmetry.** -/
theorem lt_asymm {x y : ON} (h : lt x y) : ¬ lt y x := by
  unfold lt at h ⊢; rw [cmp_swap x y, h]; decide

/-- **Transitivity.** -/
theorem lt_trans : ∀ {x y z : ON}, lt x y → lt y z → lt x z
  | _, _, zero, _, h => absurd h (not_lt_zero _)
  | _, zero, _, h, _ => absurd h (not_lt_zero _)
  | zero, oadd _ _, oadd _ _, _, _ => rfl
  | oadd a b, oadd a' b', oadd a'' b'', h₁, h₂ => by
      rw [lt_oadd] at h₁ h₂ ⊢
      rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
      · exact Or.inl (lt_trans h₁ h₂)
      · exact Or.inl h₁
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, lt_trans h₁ h₂⟩

/-- **Trichotomy.** -/
theorem lt_trichotomy (x y : ON) : lt x y ∨ x = y ∨ lt y x := by
  cases h : cmp x y
  · exact Or.inl h
  · exact Or.inr (Or.inl (eq_of_cmp_eq h))
  · exact Or.inr (Or.inr (by simp [lt, cmp_swap x y, h, Ordering.swap]))

/-- If `x` is not below `y`, then `y` is below or equal to `x`. -/
theorem le_of_not_lt {x y : ON} (h : ¬ lt x y) : y = x ∨ lt y x := by
  rcases lt_trichotomy x y with h' | rfl | h'
  · exact absurd h' h
  · exact Or.inl rfl
  · exact Or.inr h'

/-! ## Cantor normal form -/

/-- **Cantor normal form**: in `ω^a + b`, the leading exponent of `b` is at most `a`,
and all exponents are themselves in normal form. -/
inductive NF : ON → Prop where
  /-- `0` is normal. -/
  | zero : NF zero
  /-- `ω^a + b` is normal if `a`, `b` are and `b`'s leading exponent is `≤ a`. -/
  | oadd {a b : ON} : NF a → NF b → (∀ a' b', b = oadd a' b' → ¬ lt a a') → NF (oadd a b)

/-- The order relation used for well-foundedness: `x < y` with `x` normal. -/
def R (x y : ON) : Prop := NF x ∧ lt x y

/-- `0` is accessible. -/
theorem acc_zero : Acc R zero := ⟨_, fun y ⟨_, h⟩ => absurd h (not_lt_zero y)⟩

/-- **The key lemma**: if `a` and `b` are accessible and `ω^a + b` is normal, then
`ω^a + b` is accessible. -/
theorem acc_oadd {a : ON} (ha : Acc R a) : ∀ {b}, Acc R b → NF (oadd a b) → Acc R (oadd a b) := by
  induction ha with
  | intro a _ iha =>
    intro b hb
    induction hb with
    | intro b hbacc ihb =>
      intro _
      -- every normal `y < ω^a + b` is accessible, by structural induction on `y`
      have key : ∀ y, NF y → lt y (oadd a b) → Acc R y := by
        intro y
        induction y with
        | zero => intro _ _; exact acc_zero
        | oadd a' b' _ ihb' =>
            intro hy hlt
            cases hy with
            | oadd ha' hb' hcond =>
              rcases lt_oadd.1 hlt with h | ⟨rfl, h⟩
              · -- leading exponent smaller
                have hb'acc : Acc R b' := by
                  refine ihb' hb' ?_
                  cases b' with
                  | zero => exact zero_lt_oadd _ _
                  | oadd a'' c =>
                      refine lt_oadd.2 (Or.inl ?_)
                      rcases le_of_not_lt (hcond a'' c rfl) with rfl | h'
                      · exact h
                      · exact lt_trans h' h
                exact iha a' ⟨ha', h⟩ hb'acc (NF.oadd ha' hb' hcond)
              · -- same exponent, smaller remainder
                exact ihb b' ⟨hb', h⟩ (NF.oadd ha' hb' hcond)
      exact ⟨_, fun y ⟨hy, hlt⟩ => key y hy hlt⟩

/-- Every normal notation is accessible. -/
theorem acc_of_NF : ∀ x, NF x → Acc R x
  | zero, _ => acc_zero
  | oadd a b, h => by
      cases h with
      | oadd ha hb hc => exact acc_oadd (acc_of_NF a ha) (acc_of_NF b hb) (NF.oadd ha hb hc)

/-- **ε₀ is well-ordered**: the order on normal notations is well-founded — there is
no infinite strictly descending sequence of ordinals below ε₀ in Cantor normal form. -/
theorem wellFounded_R : WellFounded R :=
  ⟨fun _ => ⟨_, fun y ⟨hy, _⟩ => acc_of_NF y hy⟩⟩

/-- **No infinite descent below ε₀.** -/
theorem no_infinite_descent (f : Nat → ON) (h : ∀ k, NF (f (k + 1)) ∧ lt (f (k + 1)) (f k)) :
    False := by
  have : ∀ x, Acc R x → ∀ k, f k ≠ x := by
    intro x hx
    induction hx with
    | intro _ _ ih => intro k hk; exact ih (f (k + 1)) (hk ▸ h k) (k + 1) rfl
  exact this (f 0) (wellFounded_R.apply _) 0 rfl

end ON

end Foundations.Logic.Ordinals
