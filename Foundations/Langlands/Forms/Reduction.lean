import Foundations.Langlands.Forms.Basic

/-!
# Gauss reduction of positive definite forms

A form `f = (a, b, c)` with negative discriminant `D = b² − 4ac < 0` and `a > 0` is
**positive definite**: it takes only positive values away from `(0, 0)`. Lagrange (1773)
showed that each such form can be moved by substitutions into one with `|b| ≤ a ≤ c`; Gauss
(*Disquisitiones*, art. 171–172) sharpened the normalisation so that every class contains
**exactly one** reduced form:

  `f` is **reduced** iff `|b| ≤ a ≤ c`, and `b ≥ 0` whenever `|b| = a` or `a = c`.

## The algorithm (`exists_reduced`)

Two substitutions suffice, and they are the same two that generate `SL₂(ℤ)`:

* the translation `Tⁿ = (1 n; 0 1)` sends `(a, b, c)` to `(a, b + 2an, an² + bn + c)`
  (`act_Tn`), so `b` can be moved into the window `−a < b ≤ a`;
* the inversion `S = (0 −1; 1 0)` sends `(a, b, c)` to `(c, −b, a)` (`act_S`), swapping the
  outer coefficients.

If after translating `a > c`, swap with `S`: the new leading coefficient `c` is a smaller
positive integer, so the process terminates (strong induction on `a`). If `a ≤ c`, the form is
reduced except possibly when `a = c` and `b < 0`, which one more `S` repairs.

## The dictionary with the fundamental domain

To a positive definite form attach its root `τ_f = (−b + i√|D|)/(2a)` in the upper
half-plane ℍ, the zero of `f(τ, 1)`. Substitution of forms corresponds to the Möbius action
on roots, `|Re τ_f| = |b|/(2a)` and `|τ_f|² = c/a`, so `f` is reduced exactly when `τ_f` lies
in the fundamental domain `F = {|Re τ| ≤ 1/2, |τ| ≥ 1}` of `Langlands.Modular.FundamentalDomain`
(with the boundary conventions above choosing the left half of the boundary). The theorem
`exists_mem_F` there is thus the analytic form of the theorem proved here; we prove the
arithmetic version directly, without square roots, and do not formalise the root map.
-/

namespace Foundations.Langlands.Forms

open Foundations.Algebra Foundations.Langlands.Modular

namespace Form

/-- **Reduced form.** `|b| ≤ a ≤ c`, and `b ≥ 0` whenever `|b| = a` or `a = c`. -/
def IsReduced (f : Form) : Prop :=
  (f.b.natAbs : Int) ≤ f.a ∧ f.a ≤ f.c ∧ ((f.b.natAbs : Int) = f.a ∨ f.a = f.c → 0 ≤ f.b)

/-- Being reduced is decidable. -/
instance (f : Form) : Decidable f.IsReduced := by unfold IsReduced; infer_instance

/-- **Positive definite form.** Negative discriminant and positive leading coefficient. -/
def PosDef (f : Form) : Prop := f.disc < 0 ∧ 0 < f.a

/-- Effect of the translation `Tⁿ`: `(a, b, c) ↦ (a, b + 2an, an² + bn + c)`. -/
theorem act_Tn (f : Form) (n : Int) :
    f.act (SL2Z.Tn n) = ⟨f.a, f.b + 2 * f.a * n, f.a * n * n + f.b * n + f.c⟩ := by
  apply ext <;> simp [act, SL2Z.Tn] <;> grind

/-- Effect of the inversion `S`: `(a, b, c) ↦ (c, −b, a)`. -/
theorem act_S (f : Form) : f.act SL2Z.S = ⟨f.c, -f.b, f.a⟩ := by
  apply ext <;> simp [act, SL2Z.S]

/-- An integer square is non-negative. -/
theorem sq_nonneg (b : Int) : 0 ≤ b * b := by rw [← Int.natAbs_mul_self]; omega

/-- If `b² − 4ac < 0` and `a > 0` then `c > 0`. -/
theorem c_pos_of {a b c : Int} (hD : b * b - 4 * a * c < 0) (ha : 0 < a) : 0 < c := by
  apply Classical.byContradiction; intro hc
  have h1 : a * c ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  have h2 : 0 ≤ b * b := sq_nonneg b
  have e : 4 * a * c = 4 * (a * c) := by grind
  omega

/-- A positive definite form also has `c > 0`. -/
theorem PosDef.c_pos {f : Form} (h : f.PosDef) : 0 < f.c := c_pos_of h.1 h.2

/-- **Translation into the window.** Every form with `a > 0` is equivalent, by a power of `T`,
to a form with the same `a` and `−a < b ≤ a`. -/
theorem exists_translate (f : Form) (ha : 0 < f.a) :
    ∃ n : Int, -f.a < (f.act (SL2Z.Tn n)).b ∧ (f.act (SL2Z.Tn n)).b ≤ f.a ∧
      (f.act (SL2Z.Tn n)).a = f.a := by
  obtain ⟨h1, h2, h3⟩ := (Int.ediv_emod_unique (a := f.b + f.a - 1) (by omega : 0 < 2 * f.a)).1
    ⟨rfl, rfl⟩
  generalize (f.b + f.a - 1) / (2 * f.a) = q at h1
  generalize (f.b + f.a - 1) % (2 * f.a) = r at h1 h2 h3
  refine ⟨-q, ?_⟩
  rw [act_Tn]
  have e : 2 * f.a * -q = -(2 * f.a * q) := by grind
  simp only [e, and_true]
  generalize 2 * f.a * q = P at h1 ⊢
  omega

/-- The reduction step, by strong induction on the leading coefficient. -/
theorem exists_reduced_aux (n : Nat) : ∀ f : Form, f.PosDef → f.a.toNat ≤ n →
    ∃ g : Form, Equiv f g ∧ g.IsReduced := by
  induction n with
  | zero => intro f hf hn; have := hf.2; omega
  | succ n ih =>
    intro f hf hn
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_translate f hf.2
    let f₁ := f.act (SL2Z.Tn k)
    have e₁ : Equiv f f₁ := ⟨_, rfl⟩
    have hk3' : f₁.a = f.a := hk3
    have hD₁ : f₁.disc < 0 := by rw [disc_act]; exact hf.1
    have ha₁ : 0 < f₁.a := by rw [hk3]; exact hf.2
    have hc₁ : 0 < f₁.c := c_pos_of hD₁ ha₁
    have hb₁ : -f₁.a < f₁.b ∧ f₁.b ≤ f₁.a := by rw [hk3]; exact ⟨hk1, hk2⟩
    by_cases hac : f₁.c < f₁.a
    · -- swap the outer coefficients and recurse
      let f₂ := f₁.act SL2Z.S
      have e₂ : Equiv f₁ f₂ := ⟨_, rfl⟩
      have h₂ : f₂ = ⟨f₁.c, -f₁.b, f₁.a⟩ := act_S f₁
      have hD₂ : f₂.disc < 0 := by rw [disc_act]; exact hD₁
      have hpd : f₂.PosDef := ⟨hD₂, by rw [h₂]; exact hc₁⟩
      have hlt : f₂.a.toNat ≤ n := by rw [h₂]; simp only; omega
      obtain ⟨g, eg, hg⟩ := ih f₂ hpd hlt
      exact ⟨g, e₁.trans (e₂.trans eg), hg⟩
    · by_cases hneg : f₁.a = f₁.c ∧ f₁.b < 0
      · refine ⟨f₁.act SL2Z.S, e₁.trans ⟨_, rfl⟩, ?_⟩
        rw [act_S]
        refine ⟨?_, ?_, fun _ => ?_⟩ <;> simp only <;> omega
      · refine ⟨f₁, e₁, ?_, by omega, fun h => ?_⟩
        · omega
        · rcases h with h | h <;> omega

/-- **Gauss reduction.** Every positive definite binary quadratic form is properly equivalent
to a reduced form. -/
theorem exists_reduced (f : Form) (hf : f.PosDef) : ∃ g : Form, Equiv f g ∧ g.IsReduced :=
  exists_reduced_aux _ f hf (Nat.le_refl _)

/-- A reduced form of negative discriminant is positive definite (`a = 0` would force
`b = 0` and `D = 0`). -/
theorem IsReduced.posDef {f : Form} (h : f.IsReduced) (hD : f.disc < 0) : f.PosDef := by
  refine ⟨hD, ?_⟩
  apply Classical.byContradiction; intro ha
  have h1 := h.1
  have hb : f.b = 0 := by omega
  have ha0 : f.a = 0 := by omega
  unfold disc at hD; rw [hb, ha0] at hD; simp at hD

end Form

end Foundations.Langlands.Forms
