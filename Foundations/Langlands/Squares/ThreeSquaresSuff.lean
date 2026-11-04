import Foundations.Langlands.Squares.DavenportCassels
import Foundations.Langlands.Squares.ThreeSquares
import Foundations.Langlands.Squares.TwoSquares
import Foundations.Langlands.Squares.Symbols
import Foundations.Langlands.Padic.Legendre
import Foundations.NumberTheory.Dirichlet

/-!
# Three squares: sufficiency (Legendre 1798, Gauss 1801)

Every natural number that is not of the form `4ᵃ(8b + 7)` is a sum of three squares. Legendre
stated this in 1798; his argument assumed that suitable arithmetic progressions contain primes,
which Dirichlet proved only in 1837. Gauss gave the first complete proof (*Disquisitiones*, art. 291–292)
through his reduction theory of ternary forms. The proof formalised here is a modern hybrid, in
the spirit of the treatment in Serre's *Cours d'arithmétique*, but with the Hasse–Minkowski
theorem for the quaternary form `x² + y² + z² − k t²` replaced by **Legendre's theorem on
conics** (`Padic.Legendre.legendre_sufficient`) and **Dirichlet's theorem**
(`NumberTheory.dirichlet`), all of which this library already proves:

1. *Reduction to squarefree `k`.* Remove factors of `4`, and write what remains as `s² k` with `k`
   squarefree; then `s` is odd and `k ≡ 1, 2, 3, 5, 6 (mod 8)`.
2. *An auxiliary prime.* By Dirichlet, choose a prime `q > k`, `q ≡ 1 (mod 4)`, in a residue
   class modulo `4k` arranged so that `q ≡ −1 (mod k)` (if `k ≢ 3 mod 8`) or `2q ≡ −1 (mod k)`
   (if `k ≡ 3 mod 8`). Quadratic reciprocity (`Symbols`) then shows that `k` is a square
   modulo `q`; this is where `k ≢ 7 (mod 8)` is used.
3. *A conic.* With `b = q` or `b = 2q`, Legendre's conditions hold for `x² + b y² − k z² = 0`,
   which therefore has a non-trivial integer point, necessarily with `z ≠ 0`. As `b` is a sum of
   two squares (Fermat), `k z²` is a sum of three integer squares.
4. *Clearing the denominator.* By the Davenport–Cassels lemma (`DavenportCassels`), `k` itself is a
   sum of three integer squares.
-/

namespace Foundations.Langlands.Squares

open Foundations.Numbers.Arith
open Foundations.Langlands.Padic.Legendre

/-- The Legendre symbol `(a/p)` of Part IV (`Foundations.Algebra.legendre`). -/
local notation "ls" => Foundations.Algebra.legendre

/-! ## Small lemmas -/

/-- `(k/q) = 1` makes `k` a square modulo `q`, in the sense of `IsSqMod`. -/
theorem isSqMod_of_ls {k q : Nat} (h : ls k q = 1) : IsSqMod (k : Int) (q : Int) := by
  classical
  unfold Foundations.Algebra.legendre at h
  by_cases h1 : q ∣ k
  · simp [h1] at h
  by_cases h2 : Foundations.Algebra.IsQR k q
  · obtain ⟨x, hx⟩ := h2
    refine ⟨x, ((x * x / q : Nat) : Int) - ((k / q : Nat) : Int), ?_⟩
    have e1 : ((x * x % q : Nat) : Int) + (q : Int) * ((x * x / q : Nat) : Int) = (x : Int) * x := by
      exact_mod_cast Nat.mod_add_div (x * x) q
    have e2 : ((k % q : Nat) : Int) + (q : Int) * ((k / q : Nat) : Int) = (k : Int) := by
      exact_mod_cast Nat.mod_add_div k q
    rw [hx] at e1
    rw [Int.mul_sub]
    omega
  · simp [h1, h2] at h

/-- A prime is squarefree. -/
theorem squarefree_prime {q : Nat} (hq : Prime q) : Squarefree (q : Int) := by
  intro p hp hd
  have hd' : p * p ∣ q := Int.natCast_dvd_natCast.1 (by push_cast; exact hd)
  have hp2 := hp.1
  rcases hq.2 p (Nat.dvd_trans (Nat.dvd_mul_right p p) hd') with h | h
  · omega
  · subst h
    have := Nat.le_of_dvd (by omega) hd'
    have : p * 2 ≤ p * p := Nat.mul_le_mul_left p hp2
    omega

/-- An odd `a` sharing with `m` only divisors of `4` is coprime to `m`. -/
theorem coprime_of_dvd_four {a m : Nat} (ha : a % 2 = 1)
    (h : ∀ g, g ∣ a → g ∣ m → g ∣ 4) : Nat.Coprime a m := by
  have hg := h _ (Nat.gcd_dvd_left a m) (Nat.gcd_dvd_right a m)
  have hga := Nat.gcd_dvd_left a m
  have hle := Nat.le_of_dvd (by decide) hg
  unfold Nat.Coprime
  generalize Nat.gcd a m = g at hg hga hle
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4) with h0 | h0 | h0 | h0 | h0
  · subst h0; obtain ⟨c, hc⟩ := hga; omega
  · exact h0
  · subst h0; obtain ⟨c, hc⟩ := hga; omega
  · subst h0; exact absurd hg (by decide)
  · subst h0; obtain ⟨c, hc⟩ := hga; omega

/-- If `q > k > 0` is prime then `q ∤ k` (integer form). -/
theorem not_dvd_of_lt {k q : Nat} (hk0 : 0 < k) (hqk : k < q) : ¬ ((q : Int) ∣ (k : Int)) :=
  fun h => by have := Nat.le_of_dvd hk0 (Int.natCast_dvd_natCast.1 h); omega

/-! ## From the conic to three squares -/

/-- **From a conic point to three squares.** If `b > 0` is a sum of two squares and
`x² + b y² − k z² = 0` has a non-trivial integer point, then `k` is a sum of three integer squares
(the point has `z ≠ 0`; then apply Davenport–Cassels to `k z² = x² + (cy)² + (dy)²`). -/
theorem three_sq_of_conic {k b : Int} (hb : 0 < b) (hb2 : IsSum2 b) (h : ConicSolvableZ 1 b (-k)) :
    ∃ x y z : Int, x * x + y * y + z * z = k := by
  obtain ⟨x, y, z, hnt, he⟩ := h
  obtain ⟨c, d, rfl⟩ := hb2
  by_cases hz : z = 0
  · exfalso
    subst hz
    have sx := sq_nonneg' x
    have hby : 0 ≤ (c * c + d * d) * (y * y) := Int.mul_nonneg (by omega) (sq_nonneg' y)
    have e : x * x + (c * c + d * d) * (y * y) = 0 := by grind
    have hx0 := eq_zero_of_sq_eq_zero (t := x) (by omega)
    have hy0 : y = 0 := by
      rcases Int.mul_eq_zero.1 (show (c * c + d * d) * (y * y) = 0 by omega) with h | h
      · omega
      · exact eq_zero_of_sq_eq_zero h
    unfold Nontriv at hnt
    omega
  · exact davenport_cassels_int hz (x1 := x) (x2 := c * y) (x3 := d * y) (by grind)

/-- **Case `b = q`.** Let `k > 0` be squarefree and `q > k` a prime `≡ 1 (mod 4)` with `k ∣ q + 1`
and `k` a square modulo `q`. Then `k` is a sum of three squares. -/
theorem three_sq_of_aux_q {k q : Nat} (hk : Squarefree (k : Int)) (hk0 : 0 < k) (hq : Prime q)
    (hq4 : q % 4 = 1) (hqk : k < q) (hd : k ∣ q + 1) (hs : IsSqMod (k : Int) (q : Int)) :
    ∃ x y z : Int, x * x + y * y + z * z = k := by
  have hq2 := hq.1
  have hadm : Admissible 1 (q : Int) (-(k : Int)) :=
    { ha := by decide, hb := by omega, hc := by omega,
      sa := squarefree_small (by decide) (by decide) (by decide),
      sb := squarefree_prime hq, sc := hk.neg,
      cab := coprime_one_left _, cbc := (coprime_prime hq (not_dvd_of_lt hk0 hqk)).neg_right,
      cca := coprime_one_right _ }
  have hL : LegendreCond 1 (q : Int) (-(k : Int)) := by
    refine ⟨isSqMod_of_natAbs_one rfl, ?_, ?_⟩
    · rw [show -(-(k : Int) * 1) = k by omega]; exact hs
    · apply IsSqMod.neg_mod
      refine ⟨1, ?_⟩
      have : ((k : Nat) : Int) ∣ ((q + 1 : Nat) : Int) := Int.natCast_dvd_natCast.2 hd
      rw [show (1 : Int) * 1 - -(1 * (q : Int)) = ((q + 1 : Nat) : Int) by push_cast; omega]
      exact this
  have hc := legendre_sufficient hadm (by unfold MixedSigns; omega) hL
  exact three_sq_of_conic (by omega) (isSum2_prime_ne_three hq (by omega)) hc

/-- **Case `b = 2q`.** Let `k > 0` be odd and squarefree and `q > k` a prime `≡ 1 (mod 4)` with
`k ∣ 2q + 1` and `k` a square modulo `q`. Then `k` is a sum of three squares. -/
theorem three_sq_of_aux_2q {k q : Nat} (hk : Squarefree (k : Int)) (hk0 : 0 < k) (hko : k % 2 = 1)
    (hq : Prime q) (hq4 : q % 4 = 1) (hqk : k < q) (hd : k ∣ 2 * q + 1)
    (hs : IsSqMod (k : Int) (q : Int)) : ∃ x y z : Int, x * x + y * y + z * z = k := by
  have hq2 := hq.1
  have c2q : Coprime 2 (q : Int) :=
    coprime_prime (p := 2) Foundations.Algebra.isPrime_two (fun h => by omega)
  have hadm : Admissible 1 (2 * (q : Int)) (-(k : Int)) :=
    { ha := by decide, hb := by omega, hc := by omega,
      sa := squarefree_small (by decide) (by decide) (by decide),
      sb := Squarefree.mul c2q (squarefree_small (by decide) (by decide) (by decide))
        (squarefree_prime hq),
      sc := hk.neg,
      cab := coprime_one_left _,
      cbc := coprime_of_no_prime (by omega) (fun p hp h1 h2 => by
        have hp2 := hp.1
        rcases prime_dvd_mul hp h1 with h | h
        · have h' : p ∣ 2 := Int.natCast_dvd_natCast.1 h
          have := Nat.le_of_dvd (by decide) h'
          have hp2' : p = 2 := by omega
          subst hp2'
          omega
        · have h' : p ∣ q := Int.natCast_dvd_natCast.1 h
          rcases hq.2 p h' with e | e
          · omega
          · subst e
            exact not_dvd_of_lt hk0 hqk (Int.dvd_neg.1 h2)),
      cca := coprime_one_right _ }
  have hL : LegendreCond 1 (2 * (q : Int)) (-(k : Int)) := by
    refine ⟨isSqMod_of_natAbs_one rfl, ?_, ?_⟩
    · rw [show -(-(k : Int) * 1) = k by omega]
      exact IsSqMod.mul c2q (isSqMod_two _) hs
    · apply IsSqMod.neg_mod
      refine ⟨1, ?_⟩
      have : ((k : Nat) : Int) ∣ ((2 * q + 1 : Nat) : Int) := Int.natCast_dvd_natCast.2 hd
      rw [show (1 : Int) * 1 - -(1 * (2 * (q : Int))) = ((2 * q + 1 : Nat) : Int) by
        push_cast; omega]
      exact this
  have hc := legendre_sufficient hadm (by unfold MixedSigns; omega) hL
  have h2q : IsSum2 (2 * (q : Int)) :=
    IsSum2.mul (⟨1, 1, rfl⟩ : IsSum2 2) (isSum2_prime_ne_three hq (by omega))
  exact three_sq_of_conic (by omega) h2q hc

/-! ## Choosing the auxiliary prime -/

/-- Write `q = a + m J` from `q % m = a` with `a < m`. -/
theorem eq_of_mod_eq {q m a : Nat} (h : q % m = a % m) (ham : a < m) : ∃ J, q = a + m * J := by
  refine ⟨q / m, ?_⟩
  have := Nat.mod_add_div q m
  rw [h, Nat.mod_eq_of_lt ham] at this
  omega

/-- **Squarefree `k ≡ 1 (mod 4)`** is a sum of three squares. Auxiliary prime:
`q ≡ 2k − 1 (mod 4k)`. -/
theorem three_sq_of_sf_one_mod_four {k : Nat} (hk : Squarefree (k : Int)) (h4 : k % 4 = 1) :
    ∃ x y z : Int, x * x + y * y + z * z = k := by
  have hcop : Nat.Coprime (2 * k - 1) (4 * k) := coprime_of_dvd_four (by omega) (fun g h1 h2 => by
    have h3 : g ∣ 4 * k - 2 * (2 * k - 1) := Nat.dvd_sub h2 (Nat.dvd_mul_left_of_dvd h1 2)
    rw [show 4 * k - 2 * (2 * k - 1) = 2 by omega] at h3
    exact Nat.dvd_trans h3 (by decide))
  obtain ⟨q, hqk, hq, hqm⟩ := Foundations.NumberTheory.dirichlet (by omega : 0 < 4 * k) hcop (k + 1)
  obtain ⟨J, rfl⟩ := eq_of_mod_eq hqm (by omega)
  have hq4 : (2 * k - 1 + 4 * k * J) % 4 = 1 := by rw [Nat.mul_assoc]; omega
  have hd : k ∣ 2 * k - 1 + 4 * k * J + 1 := ⟨2 + 4 * J, by
    rw [show 2 * k - 1 + 4 * k * J + 1 = 2 * k + 4 * k * J by omega]; grind⟩
  have hls := ls_eq_chi4 hq hq4 (by omega) (by omega) hd
  have hs : ls k (2 * k - 1 + 4 * k * J) = 1 := by rw [hls]; unfold chi4; simp [h4]
  exact three_sq_of_aux_q hk (by omega) hq hq4 (by omega) hd (isSqMod_of_ls hs)

/-- **Squarefree `k ≡ 3 (mod 8)`** is a sum of three squares. Auxiliary prime:
`q ≡ (k − 1)/2 (mod 4k)`, so that `2q ≡ −1 (mod k)`. -/
theorem three_sq_of_sf_three_mod_eight {k : Nat} (hk : Squarefree (k : Int)) (h8 : k % 8 = 3) :
    ∃ x y z : Int, x * x + y * y + z * z = k := by
  have hcop : Nat.Coprime ((k - 1) / 2) (4 * k) := coprime_of_dvd_four (by omega) (fun g h1 h2 => by
    have h3 : g ∣ 4 * k - 8 * ((k - 1) / 2) := Nat.dvd_sub h2 (Nat.dvd_mul_left_of_dvd h1 8)
    rwa [show 4 * k - 8 * ((k - 1) / 2) = 4 by omega] at h3)
  obtain ⟨q, hqk, hq, hqm⟩ := Foundations.NumberTheory.dirichlet (by omega : 0 < 4 * k) hcop (k + 1)
  obtain ⟨J, rfl⟩ := eq_of_mod_eq hqm (by omega)
  have hq4 : ((k - 1) / 2 + 4 * k * J) % 4 = 1 := by rw [Nat.mul_assoc]; omega
  have hd : k ∣ 2 * ((k - 1) / 2 + 4 * k * J) + 1 := ⟨1 + 8 * J, by
    rw [show 2 * ((k - 1) / 2 + 4 * k * J) + 1 = k + 8 * (k * J) by rw [Nat.mul_assoc]; omega]
    grind⟩
  have hls := ls_eq_chi8 hq hq4 (by omega) (by omega) hd
  have hs : ls k ((k - 1) / 2 + 4 * k * J) = 1 := by rw [hls]; unfold chi8; simp [h8]
  exact three_sq_of_aux_2q hk (by omega) (by omega) hq hq4 (by omega) hd (isSqMod_of_ls hs)

/-- **Squarefree `k ≡ 2 (mod 4)`** is a sum of three squares. Auxiliary prime:
`q ≡ k − 1 (mod 4k)`; then `q ≡ 1` or `5 (mod 8)` according as `k/2 ≡ 1` or `3 (mod 4)`, which
makes `(2/q) = (k/2 / q)` and hence `(k/q) = 1`. -/
theorem three_sq_of_sf_two_mod_four {k : Nat} (hk : Squarefree (k : Int)) (h4 : k % 4 = 2) :
    ∃ x y z : Int, x * x + y * y + z * z = k := by
  have hcop : Nat.Coprime (k - 1) (4 * k) := coprime_of_dvd_four (by omega) (fun g h1 h2 => by
    have h3 : g ∣ 4 * k - 4 * (k - 1) := Nat.dvd_sub h2 (Nat.dvd_mul_left_of_dvd h1 4)
    rwa [show 4 * k - 4 * (k - 1) = 4 by omega] at h3)
  obtain ⟨q, hqk, hq, hqm⟩ := Foundations.NumberTheory.dirichlet (by omega : 0 < 4 * k) hcop (k + 1)
  obtain ⟨J, rfl⟩ := eq_of_mod_eq hqm (by omega)
  have hq4 : (k - 1 + 4 * k * J) % 4 = 1 := by rw [Nat.mul_assoc]; omega
  have hd : k ∣ k - 1 + 4 * k * J + 1 := ⟨1 + 4 * J, by
    rw [show k - 1 + 4 * k * J + 1 = k + 4 * k * J by omega]; grind⟩
  -- `k = 2 k'` with `k'` odd.
  obtain ⟨k', rfl⟩ : ∃ k', k = 2 * k' := ⟨k / 2, by omega⟩
  have hd' : k' ∣ 2 * k' - 1 + 4 * (2 * k') * J + 1 :=
    Nat.dvd_trans (Nat.dvd_mul_left k' 2) hd
  have hls' := ls_eq_chi4 hq hq4 (by omega) (by omega) hd'
  have hq8 : (2 * k' - 1 + 4 * (2 * k') * J) % 8 = (2 * k' - 1) % 8 := by
    rw [show 4 * (2 * k') * J = 8 * (k' * J) by grind]; omega
  have hls2 := ls_two hq (by omega)
  rw [hq8] at hls2
  have hs : ls (2 * k') (2 * k' - 1 + 4 * (2 * k') * J) = 1 := by
    rw [Foundations.Algebra.legendre_mul hq (by omega), hls2, hls']
    unfold chi4
    have : k' % 8 = 1 ∨ k' % 8 = 3 ∨ k' % 8 = 5 ∨ k' % 8 = 7 := by omega
    rcases this with h | h | h | h
    · rw [show (2 * k' - 1) % 8 = 1 by omega, show k' % 4 = 1 by omega]; decide
    · rw [show (2 * k' - 1) % 8 = 5 by omega, show k' % 4 = 3 by omega]; decide
    · rw [show (2 * k' - 1) % 8 = 1 by omega, show k' % 4 = 1 by omega]; decide
    · rw [show (2 * k' - 1) % 8 = 5 by omega, show k' % 4 = 3 by omega]; decide
  exact three_sq_of_aux_q hk (by omega) hq hq4 (by omega) hd (isSqMod_of_ls hs)

/-- **Squarefree numbers `k ≡ 1, 2, 3, 5, 6 (mod 8)` are sums of three squares.** -/
theorem three_sq_of_squarefree {k : Nat} (hk : Squarefree (k : Int))
    (h8 : k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 6) :
    ∃ x y z : Int, x * x + y * y + z * z = k := by
  rcases h8 with h | h | h | h | h
  · exact three_sq_of_sf_one_mod_four hk (by omega)
  · exact three_sq_of_sf_two_mod_four hk (by omega)
  · exact three_sq_of_sf_three_mod_eight hk h
  · exact three_sq_of_sf_one_mod_four hk (by omega)
  · exact three_sq_of_sf_two_mod_four hk (by omega)

/-! ## Reduction to the squarefree case -/

/-- Every positive integer is `s² k` with `k` squarefree. -/
theorem exists_sq_mul_squarefree (n : Nat) (hn : 0 < n) :
    ∃ s k : Nat, n = s * s * k ∧ Squarefree (k : Int) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  by_cases hsf : Squarefree (n : Int)
  · exact ⟨1, n, by simp, hsf⟩
  have : ∃ p, Prime p ∧ (p : Int) * p ∣ (n : Int) := by
    apply Classical.byContradiction; intro hne
    exact hsf (fun p hp hd => hne ⟨p, hp, hd⟩)
  obtain ⟨p, hp, hd⟩ := this
  have hd' : p * p ∣ n := Int.natCast_dvd_natCast.1 (by push_cast; exact hd)
  obtain ⟨m, rfl⟩ := hd'
  have hp2 := hp.1
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hn
    · exact h
  have hlt : m < p * p * m := by
    have : 4 ≤ p * p := Nat.mul_le_mul hp2 hp2
    have := Nat.mul_lt_mul_of_pos_right (show 1 < p * p by omega) hm0
    omega
  obtain ⟨s, k, rfl, hk⟩ := ih m hlt hm0
  exact ⟨p * s, k, by grind, hk⟩

/-- **Sufficiency in Legendre's three-square theorem.** Every natural number not of the form
`4ᵃ(8b + 7)` is a sum of three squares of natural numbers. -/
theorem three_squares_of_not_form (n : Nat) (h : ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : Nat, x * x + y * y + z * z = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  by_cases hn0 : n = 0
  · subst hn0; exact ⟨0, 0, 0, rfl⟩
  by_cases h4 : 4 ∣ n
  · obtain ⟨m, rfl⟩ := h4
    have hm : ¬ ∃ a b : Nat, m = 4 ^ a * (8 * b + 7) := by
      rintro ⟨a, b, rfl⟩
      exact h ⟨a + 1, b, by rw [Nat.pow_succ]; grind⟩
    obtain ⟨x, y, z, hxyz⟩ := ih m (by omega) hm
    exact ⟨2 * x, 2 * y, 2 * z, by rw [← hxyz]; grind⟩
  have h7 : n % 8 ≠ 7 := fun h7 => h ⟨0, n / 8, by rw [Nat.pow_zero]; omega⟩
  obtain ⟨s, k, rfl, hk⟩ := exists_sq_mul_squarefree n (by omega)
  have hs : s % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one s with hs | hs
    · exfalso; apply h4
      obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
      exact ⟨t * t * k, by grind⟩
    · exact hs
  have hss : s * s % 8 = 1 := by
    rcases sq_mod_eight s with ⟨h1, _⟩ | ⟨_, h2⟩
    · omega
    · exact h2
  have hk8 : s * s * k % 8 = k % 8 := by rw [Nat.mul_mod, hss, Nat.one_mul, Nat.mod_mod]
  have hk4 : ¬ 4 ∣ k := fun hk4 => h4 (Nat.dvd_trans hk4 (Nat.dvd_mul_left k (s * s)))
  obtain ⟨x, y, z, hxyz⟩ := three_sq_of_squarefree hk (by omega)
  refine ⟨s * x.natAbs, s * y.natAbs, s * z.natAbs, ?_⟩
  have hx := @Int.natAbs_mul_self x
  have hy := @Int.natAbs_mul_self y
  have hz := @Int.natAbs_mul_self z
  have e : x.natAbs * x.natAbs + y.natAbs * y.natAbs + z.natAbs * z.natAbs = k := by omega
  rw [← e]; grind

/-- **Legendre's three-square theorem** (Legendre 1798; first complete proof by Gauss, 1801). A
natural number is a sum of three squares if and only if it is not of the form `4ᵃ(8b + 7)`. -/
theorem three_squares_iff (n : Nat) :
    (∃ x y z : Nat, x * x + y * y + z * z = n) ↔ ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7) := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact sum_three_squares_not_form h
  · exact three_squares_of_not_form n

end Foundations.Langlands.Squares
