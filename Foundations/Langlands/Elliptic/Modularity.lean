import Foundations.Langlands.Elliptic.Examples

/-!
# A finite modularity check for the conductor-11 curve

**Eichler** (1954) observed that the coefficients of the `q`-series

  `f(q) = q ∏_{n ≥ 1} (1 − qⁿ)² (1 − q¹¹ⁿ)² = q − 2q² − q³ + 2q⁴ + q⁵ + 2q⁶ − 2q⁷ − ⋯`,

a cusp form of weight `2` for `Γ₀(11)`, are at every prime `p ≠ 11` the numbers
`a_p = p + 1 − #E(𝔽_p)` of the curve `E : y² + y = x³ − x²`; **Shimura** (1958) extended this
to a general construction (the Eichler–Shimura relation). The **Taniyama–Shimura–Weil
conjecture** predicted that every elliptic curve over `ℚ` arises in this way from a modular
form. **Frey**, **Serre** and **Ribet** (1986) showed that it would imply **Fermat's Last
Theorem**; **Wiles** (1995), with **Taylor**, proved enough of it (semistable curves) to settle
Fermat, and **Breuil, Conrad, Diamond and Taylor** (2001) completed the proof.

None of that theory is formalised here. This file contains **only a finite computation**: we
expand the finite product

  `q · ∏_{n=1}^{29} (1 − qⁿ)² · ∏_{11n < 30} (1 − q¹¹ⁿ)²`

as a polynomial truncated below degree `30` (`etaProduct`), and check by `decide` that its
coefficient of `q^p` equals the point-count `ap11 p` of `y² + y = x³ − x²` for every prime
`p < 30` (`modularity_check_lt_30`), including the bad prime `p = 11` with the
multiplicative-reduction convention.

The factors with `n ≥ 30` are `≡ 1` modulo `q³⁰`, so the coefficients of degree `< 30` of the
finite product are those of the infinite one; this remark is not formalised, since power series
are not. So the theorem is exactly: *the conductor-11 modularity correspondence holds at the ten
primes below 30*, as a checked finite instance, and nothing more.
-/

namespace Foundations.Langlands.Elliptic

/-- Truncated multiplication by `1 − qᵏ`: the coefficient list `c` (of length `N`) becomes
`d` with `dᵢ = cᵢ − c_{i−k}`. -/
def mulOneSubPow (N k : Nat) (c : List Int) : List Int :=
  (List.range N).map fun i => c.getD i 0 - (if k ≤ i then c.getD (i - k) 0 else 0)

/-- **The eta product, truncated.** The coefficients of `q⁰, …, q^{N−1}` in
`q · ∏_{n=1}^{N−1} (1 − qⁿ)² · ∏_{1 ≤ n, 11n < N} (1 − q¹¹ⁿ)²`. -/
def etaProduct (N : Nat) : List Int :=
  (List.range N).foldl
    (fun c n =>
      if n = 0 then c
      else
        let c := mulOneSubPow N n (mulOneSubPow N n c)
        if 11 * n < N then mulOneSubPow N (11 * n) (mulOneSubPow N (11 * n) c) else c)
    ((List.range N).map fun i => if i = 1 then 1 else 0)

set_option maxRecDepth 20000 in
/-- **The `q`-expansion to order 30.** The first thirty coefficients of
`q ∏ (1 − qⁿ)² (1 − q¹¹ⁿ)²` are
`0, 1, −2, −1, 2, 1, 2, −2, 0, −2, −2, 1, −2, 4, 4, −1, −4, −2, 4, 0, 2, 2, −2, −1, 0, −4, −8, 5, −4, 0`. -/
theorem etaProduct_30 :
    etaProduct 30 = [0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2, 4, 4, -1, -4, -2, 4, 0, 2, 2,
      -2, -1, 0, -4, -8, 5, -4, 0] := by
  decide

/-- **Modularity of the conductor-11 curve, checked at the primes below 30.** For every prime
`p < 30`, the coefficient of `q^p` in `q ∏ (1 − qⁿ)² (1 − q¹¹ⁿ)²` equals
`a_p = p + 1 − #E(𝔽_p)` for `E : y² + y = x³ − x²`. A finite check at ten primes; the general
statement (Eichler–Shimura) is not proved. -/
theorem modularity_check_lt_30 :
    (etaProduct 30).getD 2 0 = ap11 2 ∧ (etaProduct 30).getD 3 0 = ap11 3 ∧
    (etaProduct 30).getD 5 0 = ap11 5 ∧ (etaProduct 30).getD 7 0 = ap11 7 ∧
    (etaProduct 30).getD 11 0 = ap11 11 ∧ (etaProduct 30).getD 13 0 = ap11 13 ∧
    (etaProduct 30).getD 17 0 = ap11 17 ∧ (etaProduct 30).getD 19 0 = ap11 19 ∧
    (etaProduct 30).getD 23 0 = ap11 23 ∧ (etaProduct 30).getD 29 0 = ap11 29 := by
  rw [etaProduct_30]
  exact ⟨ap11_values.1.symm, ap11_values.2.1.symm, ap11_values.2.2.1.symm,
    ap11_values.2.2.2.1.symm, ap11_values.2.2.2.2.1.symm, ap11_values.2.2.2.2.2.1.symm,
    ap11_values.2.2.2.2.2.2.1.symm, ap11_values.2.2.2.2.2.2.2.1.symm,
    ap11_values.2.2.2.2.2.2.2.2.1.symm, ap11_values.2.2.2.2.2.2.2.2.2.symm⟩

/-- **Hecke relations, checked on the `q`-expansion.** The coefficients `b_n` of
`q ∏ (1 − qⁿ)² (1 − q¹¹ⁿ)²` satisfy, for `n < 30`, the relations expected of a normalised Hecke
eigenform of level 11: `b_{mn} = b_m b_n` for the coprime pairs `(2,3), (2,5), (3,5), (2,7),
(2,13), (3,7)`, and `b_{p²} = b_p² − p` for `p = 2, 3, 5`, and `b_{p³} = b_p b_{p²} − p b_p`
for `p = 2, 3`. (Finitely many checked instances.) -/
theorem etaProduct_hecke :
    let b := fun n => (etaProduct 30).getD n 0
    b 6 = b 2 * b 3 ∧ b 10 = b 2 * b 5 ∧ b 15 = b 3 * b 5 ∧ b 14 = b 2 * b 7 ∧
    b 26 = b 2 * b 13 ∧ b 21 = b 3 * b 7 ∧
    b 4 = b 2 ^ 2 - 2 ∧ b 9 = b 3 ^ 2 - 3 ∧ b 25 = b 5 ^ 2 - 5 ∧
    b 8 = b 2 * b 4 - 2 * b 2 ∧ b 27 = b 3 * b 9 - 3 * b 3 := by
  intro b
  simp only [b, etaProduct_30]
  decide

end Foundations.Langlands.Elliptic
