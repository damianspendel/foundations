import Foundations.Algebra.Eisenstein

/-!
# `x⁵ - 6x + 3` is irreducible over `ℚ`

The previous file proved Gauss's lemma and Eisenstein's criterion for integer coefficient
sequences. Here we transfer them to the polynomial ring `ℚ[x]` of the algebra part, where `ℚ`
is the prime field `ratField` of an arbitrary field `Ω` of characteristic zero (in the
application, `Ω = ℂ`).

Suppose `x⁵ - 6x + 3 = g · h` in `ℚ[x]` with neither factor a unit. Then `g` and `h` have
degrees `d` and `5 - d` with `1 ≤ d ≤ 4`. Multiplying `g` and `h` by common denominators
`N, M > 0` produces integer sequences `G, H` with `N M · f = G · H`. Gauss's descent removes
`N M`, and Eisenstein's criterion rules out the result.

The bridge needs the **coefficient formula for products**,
`coeff (p · q) n = ∑_{k ≤ n} coeff p k · coeff q (n - k)`, which the list-based definition of
multiplication gives by induction. It also needs the fact that the canonical map `ℤ → Ω` is an
injective ring homomorphism (characteristic zero).

**Headline.** `quinticPoly_irreducible`: `x⁵ - 6x + 3` is irreducible in `ℚ[x]`.
-/

namespace Foundations.Algebra

open Polynomial

universe u

/-! ## The coefficient formula for products -/

section CoeffMul

variable {R : Type u} [CommRing R]

/-- The sum `t 0 + ⋯ + t (n - 1)` in a commutative ring. -/
def rsum (t : Nat → R) : Nat → R
  | 0 => 0
  | n + 1 => rsum t n + t n

/-- Peeling off the first term: `∑_{k < n+1} tₖ = t₀ + ∑_{k < n} t_{k+1}`. -/
theorem rsum_succ' (t : Nat → R) : ∀ n, rsum t (n + 1) = t 0 + rsum (fun k => t (k + 1)) n
  | 0 => by show 0 + t 0 = t 0 + 0; rw [Ring.zero_add, Ring.add_zero]
  | n + 1 => by
    show rsum t (n + 1) + t (n + 1) = t 0 + (rsum (fun k => t (k + 1)) n + t (n + 1))
    rw [rsum_succ' t n, Ring.add_assoc]

/-- Sums of termwise equal sequences agree. -/
theorem rsum_congr {s t : Nat → R} : ∀ n, (∀ k, k < n → s k = t k) → rsum s n = rsum t n
  | 0, _ => rfl
  | n + 1, h => by
    show rsum s n + s n = rsum t n + t n
    rw [rsum_congr n (fun k hk => h k (by omega)), h n (by omega)]

/-- A sum of zeros is zero. -/
theorem rsum_zero {t : Nat → R} : ∀ n, (∀ k, k < n → t k = 0) → rsum t n = 0
  | 0, _ => rfl
  | n + 1, h => by
    show rsum t n + t n = 0
    rw [rsum_zero n (fun k hk => h k (by omega)), h n (by omega), Ring.add_zero]

/-- Scaling a sum. -/
theorem mul_rsum (c : R) (t : Nat → R) : ∀ n, c * rsum t n = rsum (fun k => c * t k) n
  | 0 => Ring.mul_zero c
  | n + 1 => by
    show c * (rsum t n + t n) = rsum (fun k => c * t k) n + c * t n
    rw [Ring.left_distrib, mul_rsum c t n]

/-- The coefficient formula for products of coefficient lists. -/
theorem PolyList.coeff_mul_sum (l q : List R) (n : Nat) :
    PolyList.coeff (PolyList.mul l q) n =
      rsum (fun k => PolyList.coeff l k * PolyList.coeff q (n - k)) (n + 1) := by
  induction l generalizing n with
  | nil =>
    show PolyList.coeff ([] : List R) n = _
    rw [PolyList.coeff_nil, rsum_zero]
    intro k _; rw [PolyList.coeff_nil, Ring.zero_mul]
  | cons a p ih =>
    rw [PolyList.coeff_mul_cons, rsum_succ']
    cases n with
    | zero =>
      show a * PolyList.coeff q 0 + 0 = a * PolyList.coeff q (0 - 0) + 0
      rfl
    | succ n =>
      rw [PolyList.coeff_cons_succ, ih n]
      show a * PolyList.coeff q (n + 1) + _ = a * PolyList.coeff q (n + 1 - 0) + _
      congr 1
      exact rsum_congr _ fun k _ => by
        show _ = PolyList.coeff (a :: p) (k + 1) * PolyList.coeff q (n + 1 - (k + 1))
        rw [PolyList.coeff_cons_succ, Nat.add_sub_add_right]

/-- **The coefficient formula for products**:
`coeff (p · q) n = ∑_{k ≤ n} coeff p k · coeff q (n - k)`. -/
theorem coeff_mul_sum (p q : Polynomial R) (n : Nat) :
    coeff (p * q) n = rsum (fun k => coeff p k * coeff q (n - k)) (n + 1) := by
  induction p using Quotient.ind; induction q using Quotient.ind
  exact PolyList.coeff_mul_sum _ _ n

/-- The degree of a polynomial with `deg < n + 1` and non-zero coefficient at `n` is `n`. -/
theorem natDegree_eq_of {p : Polynomial R} {n : Nat} (h1 : DegLT p (n + 1)) (h2 : coeff p n ≠ 0) :
    natDegree p = n := by
  have hle := len_le h1
  have hge : n + 1 ≤ len p := Nat.le_of_not_lt fun hlt => h2 (degLT_len p n (by omega))
  unfold natDegree; omega

end CoeffMul

/-! ## Polynomials with integer coefficients -/

section IntPoly

variable {R : Type u} [CommRing R]

/-- Coefficients of a list are its entries (zero beyond the end). -/
theorem PolyList.coeff_eq_getD (l : List R) (n : Nat) : PolyList.coeff l n = l.getD n 0 := by
  induction l generalizing n with
  | nil => rw [PolyList.coeff_nil]; rfl
  | cons a l ih => cases n with
    | zero => rfl
    | succ n => rw [PolyList.coeff_cons_succ, ih]; rfl

/-- The polynomial `x⁵ - 6x + 3` over any commutative ring. -/
def quinticPoly (R : Type u) [CommRing R] : Polynomial R :=
  mk [Int.cast 3, Int.cast (-6), 0, 0, 0, 1]

/-- The canonical image of `0 : ℤ` is `0`. -/
theorem icast_zero' : (Int.cast (0 : Int) : R) = 0 := Lean.Grind.Ring.intCast_zero

/-- The canonical image of `1 : ℤ` is `1`. -/
theorem icast_one' : (Int.cast (1 : Int) : R) = 1 := Lean.Grind.Ring.intCast_one

/-- The coefficients of `x⁵ - 6x + 3` are the images of `quinticCoeffs`. -/
theorem coeff_quinticPoly (n : Nat) : coeff (quinticPoly R) n = Int.cast (quinticCoeffs n) := by
  unfold quinticPoly
  rw [coeff_mk, PolyList.coeff_eq_getD]
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => exact icast_zero'.symm
  | 3 => exact icast_zero'.symm
  | 4 => exact icast_zero'.symm
  | 5 => exact icast_one'.symm
  | n + 6 => exact icast_zero'.symm

/-- `x⁵ - 6x + 3` has degree `5` (over a ring with `0 ≠ 1`). -/
theorem natDegree_quinticPoly (h01 : (0 : R) ≠ 1) : natDegree (quinticPoly R) = 5 := by
  apply natDegree_eq_of
  · intro n hn
    rw [coeff_quinticPoly]
    match n, hn with
    | n + 6, _ => exact icast_zero'
  · rw [coeff_quinticPoly]; show (Int.cast (1 : Int) : R) ≠ 0
    rw [icast_one']; exact fun h => h01 h.symm

end IntPoly

/-! ## Irreducibility over the prime field -/

section Irreducible

variable {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω) (hc : CharZero Ω)

/-- Values of integers in a subfield: `(n : K)` has value `(n : Ω)`. -/
theorem Subfield.coe_ncast (K : Subfield Ω) : ∀ n : Nat, ((ncast n : K) : Ω) = ncast n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show ((ncast (n + 1) : K) : Ω) + 1 = ncast (n + 1) + 1
    rw [Subfield.coe_ncast K (n + 1)]

/-- Values of integers in a subfield: `(z : K)` has value `(z : Ω)`. -/
theorem Subfield.coe_intCast (K : Subfield Ω) (z : Int) : ((Int.cast z : K) : Ω) = Int.cast z := by
  show ((icast z : K) : Ω) = icast z
  match z with
  | .ofNat n => exact Subfield.coe_ncast K n
  | .negSucc n => show -((ncast (n + 1) : K) : Ω) = -(ncast (n + 1)); rw [Subfield.coe_ncast K]

/-- Values of finite sums in a subfield. -/
theorem Subfield.coe_rsum (K : Subfield Ω) (t : Nat → K) :
    ∀ n, ((rsum t n : K) : Ω) = rsum (fun k => (t k : Ω)) n
  | 0 => rfl
  | n + 1 => by
    show ((rsum t n : K) : Ω) + (t n : Ω) = _
    rw [Subfield.coe_rsum K t n]; rfl

/-- The image of a sum of integers: `(∑ tₖ : Ω) = ∑ (tₖ : Ω)`. -/
theorem intCast_zsum (t : Nat → Int) :
    ∀ n, (Int.cast (zsum t n) : Ω) = rsum (fun k => (Int.cast (t k) : Ω)) n
  | 0 => icast_zero'
  | n + 1 => by
    show (Int.cast (zsum t n + t n) : Ω) = rsum _ n + _
    rw [Lean.Grind.Ring.intCast_add, intCast_zsum t n]

/-- **Common denominators.** Finitely many elements of `ℚ` become integers after
multiplication by a suitable positive integer. -/
theorem common_denominator (c : Nat → (ratField hΩ hc)) :
    ∀ n, ∃ N : Int, 0 < N ∧ ∀ k, k < n → ∃ a : Int, (Int.cast N : Ω) * (c k).1 = Int.cast a := by
  intro n
  induction n with
  | zero => exact ⟨1, by decide, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    obtain ⟨N, hN, hk⟩ := ih
    obtain ⟨a, b, hb, hab⟩ := (c n).2
    -- make the denominator positive
    obtain ⟨a', b', hb', hab'⟩ : ∃ a' b' : Int, 0 < b' ∧ (c n).1 * Int.cast b' = (Int.cast a' : Ω) := by
      rcases Int.lt_or_gt_of_ne hb with h | h
      · refine ⟨-a, -b, by omega, ?_⟩
        rw [Lean.Grind.Ring.intCast_neg, Lean.Grind.Ring.intCast_neg, ← hab]; grind
      · exact ⟨a, b, h, hab⟩
    refine ⟨N * b', Int.mul_pos hN hb', fun k hkn => ?_⟩
    rcases Nat.lt_or_ge k n with hlt | hge
    · obtain ⟨e, he⟩ := hk k hlt
      refine ⟨e * b', ?_⟩
      rw [Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, ← he]; grind
    · have : k = n := by omega
      subst this
      refine ⟨N * a', ?_⟩
      rw [Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, ← hab']; grind

/-- Clearing the denominators of a polynomial over `ℚ` of degree at most `d`: there are `N > 0` and
an integer sequence `G` supported in `[0, d]` with `N · gₖ = Gₖ` for all `k`. -/
theorem clear_denominators (g : Polynomial (ratField hΩ hc)) {d : Nat} (hg : DegLT g (d + 1)) :
    ∃ N : Int, 0 < N ∧ ∃ G : Nat → Int, SuppLE G d ∧
      ∀ k, (Int.cast N : Ω) * (coeff g k).1 = Int.cast (G k) := by
  obtain ⟨N, hN, hk⟩ := common_denominator hΩ hc (coeff g) (d + 1)
  have hall : ∀ k, ∃ a : Int, (Int.cast N : Ω) * (coeff g k).1 = Int.cast a ∧ (d < k → a = 0) := by
    intro k
    rcases Nat.lt_or_ge k (d + 1) with h | h
    · obtain ⟨a, ha⟩ := hk k h; exact ⟨a, ha, fun h' => absurd h' (by omega)⟩
    · refine ⟨0, ?_, fun _ => rfl⟩
      rw [hg k h, icast_zero']; exact Ring.mul_zero _
  refine ⟨N, hN, fun k => Classical.choose (hall k), fun k hk => ?_, fun k => ?_⟩
  · exact (Classical.choose_spec (hall k)).2 hk
  · exact (Classical.choose_spec (hall k)).1

/-- **`x⁵ - 6x + 3` is irreducible over `ℚ`.** In the polynomial ring over the prime field of
any field of characteristic zero, `x⁵ - 6x + 3` is a non-zero non-unit that admits no
factorisation into two non-units. (Eisenstein's criterion at `3`, via Gauss's lemma.) -/
theorem quinticPoly_irreducible : Irreducible (quinticPoly (ratField hΩ hc)) := by
  let K := ratField hΩ hc
  have hFK : IsField K := K.isField hΩ
  have hD := hFK.isDomain
  have hdeg := natDegree_quinticPoly (R := K) hFK.1
  have hf0 : quinticPoly K ≠ 0 := by
    intro h; have := natDegree_quinticPoly (R := K) hFK.1
    rw [h] at this
    have h0 : natDegree (0 : Polynomial K) = 0 := by
      unfold natDegree; rw [len_eq_zero.2 rfl]
    rw [h0] at this; exact absurd this (by decide)
  -- a non-zero non-unit has positive degree
  have hunit : ∀ p : Polynomial K, p ≠ 0 → IsUnit p → natDegree p = 0 := by
    intro p hp ⟨q, hq⟩
    have hq0 : q ≠ 0 := by
      intro h; rw [h, Ring.mul_zero] at hq
      exact hD.1 (congrArg (fun r => coeff r 0) hq)
    have := natDegree_mul hD hp hq0
    rw [hq] at this
    have h1 : natDegree (1 : Polynomial K) = 0 := by
      apply natDegree_eq_of
      · intro n hn; show PolyList.coeff [1] n = 0; cases n with
        | zero => omega
        | succ n => rfl
      · show (1 : K) ≠ 0; exact fun h => hFK.1 h.symm
    omega
  refine ⟨hf0, fun hu => by have := hunit _ hf0 hu; omega, fun g h hgh => ?_⟩
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
  have heq : ∀ n, ((N * M).toNat : Int) * quinticCoeffs n = conv G H n := by
    intro n
    rw [Int.toNat_of_nonneg (Int.le_of_lt (Int.mul_pos hN hM))]
    apply hc.cast_inj
    have hcoef := congrArg Subtype.val (coeff_mul_sum g h n)
    rw [← hgh, coeff_quinticPoly, Subfield.coe_intCast, Subfield.coe_rsum] at hcoef
    unfold conv
    rw [intCast_zsum, Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul, hcoef,
      mul_rsum]
    apply rsum_congr
    intro k _
    rw [Lean.Grind.Ring.intCast_mul, ← hG k, ← hH (n - k)]
    show (Int.cast N : Ω) * (Int.cast M : Ω) * ((coeff g k).1 * (coeff h (n - k)).1) = _
    grind
  have hpos : 0 < (N * M).toNat := by
    have := Int.mul_pos hN hM; omega
  obtain ⟨G', H', hF, hG', hH'⟩ := gauss_descent quinticCoeffs (natDegree g) (natDegree h)
    _ G H hpos heq hGs hHs
  have he : natDegree h = 5 - natDegree g := by omega
  rw [he] at hH'
  exact quintic_eisenstein (by omega) (by omega) hF hG' hH'

end Irreducible

end Foundations.Algebra
