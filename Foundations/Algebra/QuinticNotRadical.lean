import Foundations.Algebra.GaloisCriterion

/-!
# The insolvability of the quintic

For three centuries after the Renaissance solutions of the cubic and quartic, mathematicians
looked for a formula expressing the roots of the general quintic through the coefficients by
`+, −, ×, ÷` and root extractions. Ruffini (1799) and Abel (1824) showed that no such formula
exists; Galois (1830) explained why, and gave a criterion deciding, for each particular equation,
whether its roots are expressible by radicals.

This file draws the conclusion for one specific equation with rational coefficients:

  **No root of `x⁵ - 6x + 3` is expressible by radicals over `ℚ`.**

The proof assembles the whole chapter.

* The Galois group of `x⁵ - 6x + 3` over `ℚ` is `S₅` (`galoisGroup_iso_S5`): the polynomial is
  irreducible (Eisenstein at `3`), has exactly three real roots (so complex conjugation acts as a
  transposition), and a transposition together with a `5`-cycle generates `S₅`.
* `S₅` is not solvable, since every 3-cycle is a commutator of 3-cycles
  (`quintic_galois_not_solvable`).
* If one root were expressible by radicals, the radical tower could be enlarged to a stable tower of
  Kummer steps (`exists_stable_kummer`), whose automorphism group is solvable
  (`kummer_aut_solvable`) and maps onto the Galois group (`restrictHom_surjective`), so the Galois
  group would be solvable (`galois_criterion`). Contradiction.

Everything is checked from the axioms of the foundations upward; the complex numbers, the
fundamental theorem of algebra, the polynomial algebra, and the group theory are those built
earlier in the project.

This is a statement about **one** quintic. That no formula can work for **all** quintics follows,
since such a formula would in particular express the roots of `x⁵ - 6x + 3`. What remains
unformalised is the converse half of Galois's criterion (a solvable group implies solvability by
radicals) and the criterion for arbitrary polynomials.
-/

namespace Foundations.Algebra

open Polynomial

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-- **The insolvability of the quintic (Abel–Ruffini, Galois).** No complex root of
`x⁵ - 6x + 3` is expressible by radicals over `ℚ`: it lies in no tower
`ℚ ⊆ ℚ(x₁) ⊆ ⋯ ⊆ ℚ(x₁, …, xₘ) ⊆ ℂ` in which each `xᵢ` has a positive power in the field before it. -/
theorem quintic_not_solvable_by_radicals (β : ℂ) (hβ : eval β (quinticPoly ℂ) = 0) :
    ¬ ExpressibleByRadicals β :=
  fun hrad => quintic_galois_not_solvable (galois_criterion hβ hrad)

/-- **There is no formula by radicals for the quintic.** The polynomial `x⁵ - 6x + 3`, with
rational coefficients, has a complex root (indeed five) that is not expressible by radicals over
`ℚ`. -/
theorem exists_quintic_root_not_radical :
    ∃ β : ℂ, eval β (quinticPoly ℂ) = 0 ∧ ¬ ExpressibleByRadicals β :=
  ⟨qβ 0, qβ_spec.2.1 0, quintic_not_solvable_by_radicals _ (qβ_spec.2.1 0)⟩

end Foundations.Algebra
