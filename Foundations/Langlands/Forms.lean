import Foundations.Langlands.Forms.Basic
import Foundations.Langlands.Forms.Reduction
import Foundations.Langlands.Forms.Uniqueness
import Foundations.Langlands.Forms.ClassNumber
import Foundations.Langlands.Forms.Representation

/-!
# Part XV, chapter 5: binary quadratic forms, reduction and class numbers

This chapter is where the arithmetic side of the Langlands picture (integers, discriminants,
primes) meets the automorphic side (the modular group and its fundamental domain `F`).

## History

**Fermat** stated which primes are `x² + y²`, `x² + 2y²`, `x² + 3y²`; **Euler** proved these
and discovered that `x² + 5y²` needs a companion form. **Lagrange** (*Recherches
d'arithmétique*, 1773–1775) created the general theory: forms related by an invertible
integral substitution represent the same numbers, every form is equivalent to a *reduced* one,
there are finitely many reduced forms of each discriminant, and a prime `p` is represented by
some form of discriminant `D` exactly when `D` is a square modulo `4p`. **Gauss**, in section V
of the *Disquisitiones Arithmeticae* (1801), refined equivalence to *proper* equivalence
(determinant `+1`), fixed the reduction conditions so that the reduced form in each class is
unique, tabulated the **class numbers** `h(D)`, and introduced composition of forms, making the
classes a finite abelian group. Dirichlet (1839) found the analytic class number formula.

## The link with the fundamental domain

To a positive definite form `(a, b, c)` attach the root `τ = (−b + i√|D|)/(2a)` of `aτ² + bτ + c`
in the upper half-plane. Substitution of forms becomes the Möbius action of `SL₂(ℤ)`, and the
reduction conditions `|b| ≤ a ≤ c` say precisely `|Re τ| ≤ 1/2` and `|τ| ≥ 1`: Gauss's
reduction theory *is* the fundamental domain `F` of `Langlands.Modular.FundamentalDomain`
(Dedekind 1877, Klein 1879), the boundary conventions on `b` choosing one point from each pair
of identified boundary points. The library proves both theories independently; the root map
itself is described here in prose only.

## The link with class field theory (prose only)

For a fundamental discriminant `D < 0`, Gauss's class group is the ideal class group of
`ℚ(√D)`, and class field theory identifies it with the Galois group of the Hilbert class field
`H`. A prime `p ∤ D` is represented by the principal form iff it splits completely in `H`; values of
the modular function `j` at the roots `τ_f` generate `H` (complex multiplication). This is
the abelian (GL(1)) case of the reciprocity that Langlands generalises. Nothing in this
paragraph is formalised.

## What is proved

* `Basic`: forms `(a, b, c)`, the discriminant `b² − 4ac`; **SL₂(ℤ) acts by substitution**
  (`act_one`, `act_mul`, and as a left action `instMulAction`), **preserving the
  discriminant** (`disc_act`) and the content `gcd(a, b, c)` (`content_act`); proper
  equivalence `Equiv` is the orbit relation (`equiv_iff_orbit`), and equivalent forms
  represent the same integers (`Equiv.represents`).
* `Reduction`: **every positive definite form is properly equivalent to a reduced form**
  (`exists_reduced`), by the translation/inversion algorithm with strong induction on `a`.
* `Uniqueness`: a reduced form has minimum `a` on `ℤ² ∖ 0` (`le_eval`); **two properly
  equivalent reduced forms of negative discriminant are equal** (`reduced_unique`) — the
  full statement, boundary cases included; so each class has exactly one reduced form
  (`existsUnique_reduced`).
* `ClassNumber`: **`3a² ≤ |D|`** for reduced forms (`three_mul_sq_le`, i.e. `a ≤ √(|D|/3)`);
  the explicit duplicate-free list `reducedForms D` of all reduced forms of discriminant `D < 0`
  (`mem_reducedForms`, `reducedForms_nodup`); the **class number** `classNumber D`, the number
  of primitive reduced forms, with `classNumber_spec` showing it counts proper equivalence
  classes of primitive positive definite forms; and **`h(−3) = 1`, `h(−4) = 1`, `h(−20) = 2`,
  `h(−23) = 3`** (`classNumber_neg3`, …), with explicit representatives and the class
  statements `classes_neg3`, `classes_neg4`, `classes_neg20`, `classes_neg23`.
* `Representation`: **Lagrange's criterion** — a prime `p` is represented by some form of
  discriminant `D` iff `D` is a square mod `4p` (`prime_rep_iff`, for every prime `p`); for
  odd primes `p ≠ 5`, **`p = x² + 5y²` ⇒ `p ≡ 1, 9 (mod 20)`** (`prime_x2_5y2_mod20`); and,
  using `h(−20) = 2`, the converse **under the hypothesis that `−20` is a square mod `4p`**
  (`rep_x2_5y2_of_square`).

## Not formalised

The root map `f ↦ τ_f` and its equivariance; indefinite forms (`D > 0`), cycles of reduced
forms and Pell's equation; Gauss composition and the group structure on classes; genus theory;
the class number formula; the passage from `p ≡ 1, 9 (mod 20)` to "`−20` is a square mod `4p`"
(quadratic reciprocity, available elsewhere in the library but not connected here); ideal
classes, the Hilbert class field and complex multiplication.
-/
