import Foundations.Langlands.Cyclotomic.CyclotomicPoly

/-!
# Eisenstein's criterion in general

Gotthold Eisenstein published his irreducibility criterion in 1850 (Schönemann had found it
in 1846). Let `f = xⁿ + aₙ₋₁xⁿ⁻¹ + ⋯ + a₀` have integer coefficients, and let `p` be a prime
dividing every `aₖ` (`k < n`) such that `p²` does not divide `a₀`. Then `f` is irreducible over
`ℚ`. Eisenstein's motivating example was the cyclotomic polynomial `Φ_p`, after the
substitution `x ↦ x + 1`.

The algebra part proved the special case `x⁵ - 6x + 3` at `p = 3`, together with the general
tools: Gauss's lemma by descent (`gauss_descent`), clearing denominators over the prime field
`ℚ` of a field of characteristic zero, and the coefficient formula for products. Here we give
the criterion for an arbitrary monic integer polynomial, first for integer coefficient
sequences (`eisenstein_conv`) and then over `ℚ` (`eisenstein_irreducible`). The proof is
Eisenstein's. In a factorisation `f = G · H` over `ℤ`, look at the lowest coefficients of `G` and
`H` not divisible by `p`. Their product is the lowest coefficient of `f` not divisible by
`p`, which must be the leading one. So `p` divides both constant terms, and `p²` divides
`a₀`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial

universe u

/-! ## The criterion for integer coefficient sequences -/

/-- The coefficient of `xⁿ` in a product of polynomials of degrees at most `d` and `n - d`. -/
theorem conv_top' {G H : Nat → Int} {n d : Nat} (hd : d ≤ n) (hG : SuppLE G d)
    (hH : SuppLE H (n - d)) : conv G H n = G d * H (n - d) := by
  unfold conv
  apply zsum_single _ (n + 1) (by omega)
  intro k hk hkd
  rcases Nat.lt_or_gt_of_ne hkd with h | h
  · rw [hH (n - k) (by omega), Int.mul_zero]
  · rw [hG k h, Int.zero_mul]

/-- **Eisenstein's criterion over `ℤ`.** Let `F` be the coefficient sequence of a monic integer
polynomial of degree `n`, and `p` a prime dividing `F₀, …, F_{n-1}` with `p² ∤ F₀`. Then `F` is
not a product of integer polynomials of degrees `d` and `n - d` with `1 ≤ d < n`. -/
theorem eisenstein_conv {p : Nat} (hp : IsPrime p) {F : Nat → Int} {n : Nat} (hFn : F n = 1)
    (hlow : ∀ k, k < n → (p : Int) ∣ F k) (h0 : ¬ ((p : Int) * p) ∣ F 0)
    {G H : Nat → Int} {d : Nat} (hd1 : 1 ≤ d) (hdn : d < n)
    (hF : ∀ m, F m = conv G H m) (hG : SuppLE G d) (hH : SuppLE H (n - d)) : False := by
  have hp1 : ¬ (p : Int) ∣ 1 := fun h => by
    have := Int.le_of_dvd (by decide) h; have := hp.1; omega
  have htop : G d * H (n - d) = 1 := by rw [← conv_top' (by omega) hG hH, ← hF n, hFn]
  have hGd : ¬ (p : Int) ∣ G d := fun h => by
    have := dvd_mul_of_left (b := H (n - d)) h
    rw [htop] at this; exact hp1 this
  have hHd : ¬ (p : Int) ∣ H (n - d) := fun h => by
    have := dvd_mul_of_right (a := G d) h
    rw [htop] at this; exact hp1 this
  obtain ⟨i, hi, himin⟩ := FiniteType.exists_least (fun i => ¬ (p : Int) ∣ G i) ⟨d, hGd⟩
  obtain ⟨j, hj, hjmin⟩ := FiniteType.exists_least (fun j => ¬ (p : Int) ∣ H j) ⟨n - d, hHd⟩
  have hid : i ≤ d := Nat.le_of_not_lt fun h => himin d h hGd
  have hje : j ≤ n - d := Nat.le_of_not_lt fun h => hjmin (n - d) h hHd
  -- the coefficient at `i + j` is not divisible by `p`
  have hnd : ¬ (p : Int) ∣ conv G H (i + j) := by
    intro hdvd
    have hsub : (p : Int) ∣ conv G H (i + j) - G i * H (i + j - i) := by
      apply dvd_zsum_sub _ _ _ (by omega)
      intro k hk hki
      rcases Nat.lt_or_gt_of_ne hki with hlt | hgt
      · exact dvd_mul_of_left (Classical.byContradiction fun h => himin k hlt h)
      · exact dvd_mul_of_right
          (Classical.byContradiction fun h => hjmin (i + j - k) (by omega) h)
    rw [show i + j - i = j by omega] at hsub
    have : (p : Int) ∣ G i * H j := by
      have e : G i * H j = conv G H (i + j) - (conv G H (i + j) - G i * H j) := by omega
      rw [e]; exact Int.dvd_sub hdvd hsub
    rcases int_prime_dvd_mul hp this with h | h
    · exact hi h
    · exact hj h
  -- so `i + j = n`, i.e. `i = d` and `j = n - d`
  have hn : i + j = n := by
    apply Classical.byContradiction; intro hne
    apply hnd; rw [← hF]; exact hlow _ (by omega)
  have hG0 : (p : Int) ∣ G 0 := Classical.byContradiction fun h => himin 0 (by omega) h
  have hH0 : (p : Int) ∣ H 0 := Classical.byContradiction fun h => hjmin 0 (by omega) h
  have hF0 : F 0 = G 0 * H 0 := by
    rw [hF 0]; unfold conv; simp [zsum]
  exact h0 (hF0 ▸ Int.mul_dvd_mul hG0 hH0)

/-! ## The criterion over `ℚ` -/

section OverQ

variable {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω) (hc : CharZero Ω)

include hΩ hc in
/-- **Eisenstein's criterion.** Let `f ∈ ℚ[x]` (`ℚ` the prime field of a field `Ω` of
characteristic zero) have integer coefficients `F₀, …, Fₙ` with `Fₙ = 1` and `n ≥ 1`. If a prime
`p` divides `F₀, …, F_{n-1}` and `p² ∤ F₀`, then `f` is irreducible in `ℚ[x]`. -/
theorem eisenstein_irreducible {p : Nat} (hp : IsPrime p) (f : Polynomial (ratField hΩ hc))
    {F : Nat → Int} {n : Nat} (hn : 1 ≤ n) (hcoeff : ∀ k, (coeff f k).1 = (Int.cast (F k) : Ω))
    (hsupp : SuppLE F n) (hFn : F n = 1) (hlow : ∀ k, k < n → (p : Int) ∣ F k)
    (h0 : ¬ ((p : Int) * p) ∣ F 0) : Irreducible f := by
  let K := ratField hΩ hc
  have hFK : IsField K := K.isField hΩ
  have hD := hFK.isDomain
  have hdeg : natDegree f = n := by
    apply natDegree_eq_of
    · intro k hk
      apply Subtype.ext
      rw [hcoeff, hsupp k (by omega)]
      exact icast_zero'
    · intro h
      have := hcoeff n
      rw [h, hFn] at this
      exact hΩ.1 (this.trans icast_one')
  have hf0 : f ≠ 0 := by
    intro h; rw [h] at hdeg
    have h0 : natDegree (0 : Polynomial K) = 0 := by
      unfold natDegree; rw [len_eq_zero.2 rfl]
    omega
  refine ⟨hf0, not_isUnit_of_natDegree_pos hD hf0 (by omega), fun g h hgh => ?_⟩
  apply Classical.byContradiction
  intro hno
  have hg0 : g ≠ 0 := by intro e; rw [e, Ring.zero_mul] at hgh; exact hf0 hgh
  have hh0 : h ≠ 0 := by intro e; rw [e, Ring.mul_zero] at hgh; exact hf0 hgh
  have hsum := natDegree_mul hD hg0 hh0
  rw [← hgh, hdeg] at hsum
  have hgd : natDegree g ≠ 0 := fun e => hno (Or.inl (isUnit_of_natDegree_zero hFK hg0 e))
  have hhd : natDegree h ≠ 0 := fun e => hno (Or.inr (isUnit_of_natDegree_zero hFK hh0 e))
  -- clear denominators
  obtain ⟨N, hN, G, hGs, hG⟩ := clear_denominators hΩ hc g (degLT_natDegree hg0)
  obtain ⟨M, hM, H, hHs, hH⟩ := clear_denominators hΩ hc h (degLT_natDegree hh0)
  have heq : ∀ m, ((N * M).toNat : Int) * F m = conv G H m := by
    intro m
    rw [Int.toNat_of_nonneg (Int.le_of_lt (Int.mul_pos hN hM))]
    apply hc.cast_inj
    have hcoef := congrArg Subtype.val (coeff_mul_sum g h m)
    rw [← hgh, hcoeff, Subfield.coe_rsum] at hcoef
    unfold conv
    rw [intCast_zsum, Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, hcoef,
      mul_rsum]
    apply rsum_congr
    intro k _
    rw [Lean.Grind.Ring.intCast_mul, ← hG k, ← hH (m - k)]
    show (Int.cast N : Ω) * (Int.cast M : Ω) * ((coeff g k).1 * (coeff h (m - k)).1) = _
    grind
  have hpos : 0 < (N * M).toNat := by
    have := Int.mul_pos hN hM; omega
  obtain ⟨G', H', hF, hG', hH'⟩ := gauss_descent F (natDegree g) (natDegree h)
    _ G H hpos heq hGs hHs
  have he : natDegree h = n - natDegree g := by omega
  rw [he] at hH'
  exact eisenstein_conv hp hFn hlow h0 (by omega) (by omega) hF hG' hH'

end OverQ

end Foundations.Langlands
