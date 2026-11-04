import Foundations.Algebra.Action
import Foundations.Langlands.Modular.SL2

/-!
# Binary quadratic forms and the action of SL₂(ℤ)

A **binary quadratic form** is a homogeneous polynomial `f(x, y) = ax² + bxy + cy²` with
integer coefficients, written `f = (a, b, c)`. The question which integers such a form
represents is as old as Fermat's statement that an odd prime is a sum of two squares exactly
when it is `1 mod 4`. **Lagrange** (*Recherches d'arithmétique*, 1773–1775) found the key idea:
an invertible integral change of variables does not change the set of represented numbers, so
forms should be studied up to such substitutions, and every class contains a *reduced* form
with small coefficients. **Gauss**, in the fifth section of the *Disquisitiones Arithmeticae*
(1801), made this the centre of a whole theory: he distinguished *proper* equivalence
(substitutions of determinant `+1`), counted the classes of each discriminant — the
**class number** — and composed classes into what we now call the class group.

This file sets up the objects.

* `Form` is a triple `(a, b, c)`; `Form.eval` evaluates it and `Form.disc` is the
  **discriminant** `D = b² − 4ac`.
* A matrix `γ = (p q; r s) ∈ SL₂(ℤ)` acts by substitution, `(f·γ)(x, y) = f(px + qy, rx + sy)`
  (`Form.act`, `eval_act`). This is a right action: `f·I = f` and `(f·γ)·δ = f·(γδ)`
  (`act_one`, `act_mul`); turned into a left action by `γ • f = f·γ⁻¹` it is a **group action**
  in the sense of `Foundations.Algebra.MulAction` (`instMulAction`).
* The substitution **preserves the discriminant** (`disc_act`), because `D` gets multiplied by
  `(ps − qr)² = 1`, and **preserves primitivity**, i.e. `gcd(a, b, c)` (`content_act`).
* **Proper equivalence** `Equiv f g` is the orbit relation; it is an equivalence relation
  (`Equiv.refl`, `Equiv.symm`, `Equiv.trans`) and coincides with the orbits of the left action
  (`equiv_iff_orbit`).

The modular group used here is the from-scratch `SL2Z` of `Langlands.Modular.SL2`, the same
group that acts on the upper half-plane; the file `Reduction` explains the dictionary.
-/

namespace Foundations.Langlands.Forms

open Foundations.Algebra Foundations.Langlands.Modular

/-- **Binary quadratic form.** The triple `(a, b, c)` stands for `ax² + bxy + cy²`. -/
structure Form where
  /-- Coefficient of `x²`. -/
  a : Int
  /-- Coefficient of `xy`. -/
  b : Int
  /-- Coefficient of `y²`. -/
  c : Int
deriving DecidableEq, Repr

namespace Form

/-- Two forms with the same coefficients are equal. -/
theorem ext {f g : Form} (ha : f.a = g.a) (hb : f.b = g.b) (hc : f.c = g.c) : f = g := by
  cases f; cases g; simp only at ha hb hc; subst ha hb hc; rfl

/-- The value `f(x, y) = ax² + bxy + cy²`. -/
def eval (f : Form) (x y : Int) : Int := f.a * x * x + f.b * x * y + f.c * y * y

/-- **Discriminant.** `D = b² − 4ac`. -/
def disc (f : Form) : Int := f.b * f.b - 4 * f.a * f.c

/-- **Substitution by SL₂(ℤ).** For `γ = (p q; r s)`, `f·γ` is the form
`(x, y) ↦ f(px + qy, rx + sy)`; its coefficients are `f(p, r)`, `2apq + b(ps + qr) + 2crs`
and `f(q, s)`. -/
def act (f : Form) (g : SL2Z) : Form where
  a := f.a * g.a * g.a + f.b * g.a * g.c + f.c * g.c * g.c
  b := 2 * f.a * g.a * g.b + f.b * (g.a * g.d + g.b * g.c) + 2 * f.c * g.c * g.d
  c := f.a * g.b * g.b + f.b * g.b * g.d + f.c * g.d * g.d

/-- The leading coefficient of `f·γ` is `f(p, r)`, the value at the first column of `γ`. -/
theorem act_a (f : Form) (g : SL2Z) : (f.act g).a = f.eval g.a g.c := by
  simp only [act, eval]

/-- The last coefficient of `f·γ` is `f(q, s)`, the value at the second column of `γ`. -/
theorem act_c (f : Form) (g : SL2Z) : (f.act g).c = f.eval g.b g.d := by
  simp only [act, eval]

/-- **Substitution formula.** `(f·γ)(x, y) = f(px + qy, rx + sy)`. -/
theorem eval_act (f : Form) (g : SL2Z) (x y : Int) :
    (f.act g).eval x y = f.eval (g.a * x + g.b * y) (g.c * x + g.d * y) := by
  simp only [act, eval]; grind

/-- **The identity acts trivially.** `f·I = f`. -/
theorem act_one (f : Form) : f.act 1 = f := by
  apply ext <;> simp [act]

/-- **Compatibility with multiplication.** `(f·γ)·δ = f·(γδ)`. -/
theorem act_mul (f : Form) (g h : SL2Z) : (f.act g).act h = f.act (g * h) := by
  apply ext <;> simp only [act, SL2Z.mul_a, SL2Z.mul_b, SL2Z.mul_c, SL2Z.mul_d] <;> grind

/-- Acting by `γ` and then by `γ⁻¹` gives back the form. -/
theorem act_act_inv (f : Form) (g : SL2Z) : (f.act g).act g⁻¹ = f := by
  rw [act_mul, Group.mul_inv_cancel, act_one]

/-- Acting by `γ⁻¹` and then by `γ` gives back the form. -/
theorem act_inv_act (f : Form) (g : SL2Z) : (f.act g⁻¹).act g = f := by
  rw [act_mul, Group.inv_mul_cancel, act_one]

/-- **The discriminant is invariant.** `disc (f·γ) = (ps − qr)² · disc f = disc f`. -/
theorem disc_act (f : Form) (g : SL2Z) : (f.act g).disc = f.disc := by
  have hdet := g.det
  have e : (f.act g).disc = (g.a * g.d - g.b * g.c) * (g.a * g.d - g.b * g.c) * f.disc := by
    simp only [act, disc]; grind
  rw [e, hdet]; simp

/-- The left action `γ • f = f·γ⁻¹`. -/
instance : SMul SL2Z Form := ⟨fun g f => f.act g⁻¹⟩

/-- Unfolding the left action. -/
theorem smul_def (g : SL2Z) (f : Form) : g • f = f.act g⁻¹ := rfl

/-- **SL₂(ℤ) acts on binary quadratic forms.** With `γ • f = f·γ⁻¹`, substitution is a
group action: `I • f = f` and `(γδ) • f = γ • (δ • f)`. -/
instance instMulAction : MulAction SL2Z Form where
  one_smul f := by rw [smul_def, Group.inv_one, act_one]
  mul_smul g h f := by rw [smul_def, smul_def, smul_def, Group.mul_inv_rev, act_mul]

/-- **Proper equivalence.** `f ∼ g` iff `g = f·γ` for some `γ ∈ SL₂(ℤ)`. -/
def Equiv (f g : Form) : Prop := ∃ γ : SL2Z, f.act γ = g

/-- Every form is equivalent to itself. -/
theorem Equiv.refl (f : Form) : Equiv f f := ⟨1, act_one f⟩

/-- Proper equivalence is symmetric. -/
theorem Equiv.symm {f g : Form} (h : Equiv f g) : Equiv g f := by
  obtain ⟨γ, rfl⟩ := h; exact ⟨γ⁻¹, act_act_inv f γ⟩

/-- Proper equivalence is transitive. -/
theorem Equiv.trans {f g k : Form} (h₁ : Equiv f g) (h₂ : Equiv g k) : Equiv f k := by
  obtain ⟨γ, rfl⟩ := h₁; obtain ⟨δ, rfl⟩ := h₂; exact ⟨γ * δ, (act_mul f γ δ).symm⟩

/-- **Proper equivalence is the orbit relation.** `f ∼ g` iff `g` lies in the orbit of `f`
under the group action `instMulAction`. -/
theorem equiv_iff_orbit (f g : Form) : Equiv f g ↔ MulAction.orbit SL2Z f g := by
  constructor
  · rintro ⟨γ, rfl⟩; exact ⟨γ⁻¹, by rw [smul_def, Group.inv_inv]⟩
  · rintro ⟨γ, rfl⟩; exact ⟨γ⁻¹, rfl⟩

/-- Equivalent forms have the same discriminant. -/
theorem Equiv.disc_eq {f g : Form} (h : Equiv f g) : f.disc = g.disc := by
  obtain ⟨γ, rfl⟩ := h; exact (disc_act f γ).symm

/-- Equivalent forms represent the same integers. -/
theorem Equiv.represents {f g : Form} (h : Equiv f g) {n : Int} :
    (∃ x y, f.eval x y = n) ↔ (∃ x y, g.eval x y = n) := by
  obtain ⟨γ, rfl⟩ := h
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [← act_act_inv f γ, eval_act] at hxy
    exact ⟨_, _, hxy⟩
  · rintro ⟨x, y, hxy⟩
    exact ⟨_, _, by rw [← hxy, eval_act]⟩

/-- The **content** `gcd(a, b, c)` of a form, a natural number. -/
def content (f : Form) : Nat := Nat.gcd f.a.natAbs (Nat.gcd f.b.natAbs f.c.natAbs)

/-- **Primitive form.** `gcd(a, b, c) = 1`. -/
def Primitive (f : Form) : Prop := f.content = 1

/-- Primitivity is decidable (it is an equation between natural numbers). -/
instance (f : Form) : Decidable f.Primitive := inferInstanceAs (Decidable (f.content = 1))

/-- An integer `d` divides all coefficients iff `|d|` divides the content. -/
theorem dvd_content_iff (f : Form) (d : Int) :
    d.natAbs ∣ f.content ↔ d ∣ f.a ∧ d ∣ f.b ∧ d ∣ f.c := by
  simp only [content, Nat.dvd_gcd_iff, Int.natAbs_dvd_natAbs]

/-- The content divides every coefficient. -/
theorem content_dvd (f : Form) :
    (f.content : Int) ∣ f.a ∧ (f.content : Int) ∣ f.b ∧ (f.content : Int) ∣ f.c :=
  (dvd_content_iff f f.content).1 (by simp)

/-- A common divisor of `a`, `b`, `c` divides all coefficients of `f·γ`. -/
theorem dvd_act {f : Form} {d : Int} (h : d ∣ f.a ∧ d ∣ f.b ∧ d ∣ f.c) (g : SL2Z) :
    d ∣ (f.act g).a ∧ d ∣ (f.act g).b ∧ d ∣ (f.act g).c := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := h
  refine ⟨⟨u * g.a * g.a + v * g.a * g.c + w * g.c * g.c, ?_⟩,
    ⟨2 * u * g.a * g.b + v * (g.a * g.d + g.b * g.c) + 2 * w * g.c * g.d, ?_⟩,
    ⟨u * g.b * g.b + v * g.b * g.d + w * g.d * g.d, ?_⟩⟩ <;>
    simp only [act, hu, hv, hw] <;> grind

/-- **The content is invariant.** `gcd` of the coefficients of `f·γ` equals that of `f`; in
particular substitution preserves primitivity. -/
theorem content_act (f : Form) (g : SL2Z) : (f.act g).content = f.content := by
  apply Nat.dvd_antisymm
  · have h := dvd_act (content_dvd (f.act g)) g⁻¹
    rw [act_act_inv] at h
    have := (dvd_content_iff f _).2 h
    simpa using this
  · have := (dvd_content_iff (f.act g) _).2 (dvd_act (content_dvd f) g)
    simpa using this

/-- Equivalent forms have the same content, so one is primitive iff the other is. -/
theorem Equiv.primitive_iff {f g : Form} (h : Equiv f g) : f.Primitive ↔ g.Primitive := by
  obtain ⟨γ, rfl⟩ := h; unfold Primitive; rw [content_act]

end Form

end Foundations.Langlands.Forms
