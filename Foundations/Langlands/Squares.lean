import Foundations.Langlands.Squares.Identities
import Foundations.Langlands.Squares.FourSquares
import Foundations.Langlands.Squares.ThreeSquares
import Foundations.Langlands.Squares.TwoSquares
import Foundations.Langlands.Squares.DavenportCassels
import Foundations.Langlands.Squares.Symbols
import Foundations.Langlands.Squares.ThreeSquaresSuff

/-!
# Sums of squares

Which numbers are sums of `k` squares? The question is as old as number theory, and it is the
prototype of the arithmetic of quadratic forms: the form `x₁² + ⋯ + x_k²` is the simplest positive
definite form, and asking which integers it represents is asking for its *values*.

**Diophantus** (*Arithmetica*, c. 250 AD) knew that a product of sums of two squares is a sum of
two squares, and seems to have taken for granted that every number is a sum of four squares.
**Fermat** (1640) announced that the primes `≡ 1 (mod 4)` are sums of two squares, gave the
complete answer for two squares, and claimed the four-square theorem by descent, without
publishing proofs. **Euler** proved the two-square results (1749–58), found the four-square
identity (1748) and the congruence `x² + y² + 1 ≡ 0 (mod p)`, but not the descent; **Lagrange**
completed the four-square theorem in 1770. For three squares, **Legendre** (1798) stated and
nearly proved that `n` is a sum of three squares iff `n ≠ 4ᵃ(8b + 7)`; **Gauss** (1801) gave the
first complete proof via ternary quadratic forms.

## What this sub-part proves

* `Identities` — Brahmagupta's two-square and **Euler's four-square identity**
  (`euler_four_square_identity`), packaged as closure of `IsSum2` and `IsSum4` under products.
* `FourSquares` — **Lagrange's four-square theorem** (`lagrange_four_squares`): every natural
  number is a sum of four squares. Euler's congruence by pigeonhole, then Lagrange's descent.
* `ThreeSquares` — the **necessary condition** in Legendre's three-square theorem
  (`not_sum_three_squares`): no `4ᵃ(8b + 7)` is a sum of three squares (a congruence mod 8).
* `TwoSquares` — the **two-squares theorem** (`two_squares_iff`): `n` is a sum of two squares
  iff every prime `p ≡ 3 (mod 4)` divides `n` to an even exact power. Sufficiency uses Fermat's
  theorem `Foundations.Algebra.fermat_two_squares` (Zagier's proof) and Brahmagupta's identity;
  necessity uses Fermat's criterion for `−1` (`Foundations.Algebra.neg_one_qr_iff`).
* `DavenportCassels` — the **Davenport–Cassels lemma** for `x² + y² + z²` (`davenport_cassels`):
  if `k t²` is a sum of three integer squares with `t ≥ 1`, so is `k`.
* `Symbols` — the Legendre-symbol computations needed below: `(k/q) = χ₄(k)` or `χ₈(k)` for odd
  `k` and an auxiliary prime `q ≡ 1 (mod 4)` with `q ≡ −1` or `2q ≡ −1 (mod k)`, by quadratic
  reciprocity and multiplicativity (`legendre_eq_char`).
* `ThreeSquaresSuff` — **Legendre's three-square theorem** in full (`three_squares_iff`): `n` is a
  sum of three squares iff `n` is not of the form `4ᵃ(8b + 7)`. Sufficiency: reduce to squarefree
  `k ≡ 1, 2, 3, 5, 6 (mod 8)`; pick a prime `q` by **Dirichlet's theorem**
  (`Foundations.NumberTheory.dirichlet`); show by **Legendre's theorem**
  (`Padic.Legendre.legendre_sufficient`) that `x² + b y² = k z²` has a non-trivial solution for
  `b = q` or `b = 2q`; write `b` as a sum of two squares (Fermat), so `k z²` is a sum of three
  squares; and clear `z` by Davenport–Cassels. This replaces the Hasse–Minkowski theorem for the
  quaternary form `x² + y² + z² − k t²`, which is not formalised, by the two theorems the library
  does have; Gauss's own route through reduction of ternary forms is not formalised either.

## Representation numbers, and the road to modular forms

Beyond *whether* `n` is a sum of `k` squares one can ask *in how many ways*: let `r_k(n)` count the
integer vectors `(x₁, …, x_k)` with `x₁² + ⋯ + x_k² = n` (signs and order counted). Then
`r₂(n) = 4 (d₁(n) − d₃(n))`, where `d_i(n)` counts the divisors of `n` that are `≡ i (mod 4)`
(a formula found by Jacobi, and implicit in Gauss), and **Jacobi's four-square formula** reads
`r₄(n) = 8 · Σ_{d ∣ n, 4 ∤ d} d`, which is positive for every `n ≥ 1` and so re-proves Lagrange.
Gauss expressed `r₃(n)` through class numbers of binary quadratic forms. Jacobi found these
formulas by studying the theta series `θ(q) = Σ_{x ∈ ℤ} q^{x²}`, whose `k`-th power is
`Σ_n r_k(n) qⁿ`: in modern language `θ(τ)^k` is a **modular form** of weight `k/2` for the group
`Γ₀(4)`, and the divisor-sum formulas say that for `k = 4` it equals an Eisenstein series. That is
the bridge from sums of squares to modular forms, and through them to the automorphic side of
the Langlands programme. None of this — `r_k`, the formulas of Jacobi and Gauss, theta series,
modular forms — is formalised here; it is recorded only as the direction in which the subject
continues.
-/
