import Foundations.Langlands.Padic.Compact
import Foundations.Langlands.Padic.Hensel

/-!
# Squares in ℤₚ and sums of two squares modulo `p`

Two ingredients for the Hilbert symbol at an odd prime `p` (next file).

**Square roots of `p`-adic units.** If `u ∈ ℤₚ` is congruent modulo `p` to the square `a²` of an
integer prime to `p`, then `u` is a square in ℤₚ (`Zp.exists_sq_of_modPow`). Hensel's lemma in
`Hensel` is stated for polynomials with *integer* coefficients, while `X² − u` has a `p`-adic
coefficient. We get around this with compactness: for each `N` the integer approximation
`c_N ≡ u (mod p^(N+1))` has a square root `x_N` in ℤₚ by Hensel (`X² − c_N` with simple root
`a` modulo `p`, as `2a ≢ 0` for odd `p`); a subsequence of `(x_N)` converges (`Zp.seqCompact`),
and its limit `x` satisfies `x² ≡ u` modulo every `pᵏ`, hence `x² = u`.

**Sums of two squares modulo `p`.** For an odd prime `p` and integers `c, d` prime to `p`, the
congruence `c x² + d y² ≡ 1 (mod p)` has a solution (`exists_sum_sq_eq_one_mod`). The
`(p+1)/2` numbers `c x²` (`0 ≤ x ≤ (p−1)/2`) are pairwise incongruent, and so are the `(p+1)/2`
numbers `1 − d y²`; together these are `p + 1` residues in `p` classes, so by the finite
pigeonhole principle (`Combinatorics.pigeonhole`) one of each family coincide.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Combinatorics

/-! ## Integer lemmas -/

/-- **Euclid's lemma for integers.** A prime dividing a product of integers divides a factor. -/
theorem int_euclid {p : Nat} (hp : Prime p) {a b : Int} (h : (p : Int) ∣ a * b) :
    (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  rcases euclid_lemma hp h with h | h
  · exact Or.inl (Int.ofNat_dvd_left.2 h)
  · exact Or.inr (Int.ofNat_dvd_left.2 h)

/-- An odd prime does not divide `2a` unless it divides `a`. -/
theorem not_dvd_two_mul {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) {a : Int}
    (ha : ¬ (p : Int) ∣ a) : ¬ (p : Int) ∣ 2 * a := fun h => by
  rcases int_euclid hp h with h | h
  · have := Int.le_of_dvd (by decide) h; have := hp.1; omega
  · exact ha h

/-- Equal residues (`toNat` of `emod`) modulo `n > 0` mean `n ∣ a − b`. -/
theorem dvd_sub_of_toNat_emod_eq {n a b : Int} (hn : 0 < n)
    (h : (a % n).toNat = (b % n).toNat) : n ∣ a - b := by
  have ha := Int.mul_ediv_add_emod a n
  have hb := Int.mul_ediv_add_emod b n
  have h1 := Int.emod_nonneg a (Int.ne_of_gt hn)
  have h2 := Int.emod_nonneg b (Int.ne_of_gt hn)
  have hab : a % n = b % n := by omega
  refine ⟨a / n - b / n, ?_⟩
  rw [Int.mul_sub]
  generalize n * (a / n) = A at ha
  generalize n * (b / n) = B at hb
  omega

/-- The residue `(a mod n).toNat` is `< n` for `n > 0`. -/
theorem toNat_emod_lt {n : Int} (hn : 0 < n) (a : Int) : (a % n).toNat < n.toNat := by
  have h1 := Int.emod_nonneg a (Int.ne_of_gt hn)
  have h2 := Int.emod_lt_of_pos a hn
  omega

/-- For `0 ≤ i < j ≤ (p−1)/2`, an odd prime `p` divides neither `j − i` nor `j + i`; hence
`c i² ≢ c j² (mod p)` when `p ∤ c`. -/
theorem sq_ne_mod {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) {c : Int} (hc : ¬ (p : Int) ∣ c)
    {i j : Nat} (hij : i < j) (hj : j ≤ (p - 1) / 2) (h : (p : Int) ∣ c * i * i - c * j * j) :
    False := by
  rw [show c * i * i - c * j * j = c * (((j : Int) - i) * ((j : Int) + i)) * (-1) by grind] at h
  rcases int_euclid hp h with h | h
  · rcases int_euclid hp h with h | h
    · exact hc h
    · rcases int_euclid hp h with h | h
      · have := Int.le_of_dvd (by omega) h; omega
      · have := Int.le_of_dvd (by omega) h; omega
  · have := Int.le_of_dvd (by decide) (Int.dvd_neg.2 h); have := hp.1; omega

/-- **Sums of two squares modulo `p`.** For an odd prime `p` and integers `c, d` prime to `p`
there are integers `x, y` with `c x² + d y² ≡ 1 (mod p)`. -/
theorem exists_sum_sq_eq_one_mod {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) {c d : Int}
    (hc : ¬ (p : Int) ∣ c) (hd : ¬ (p : Int) ∣ d) :
    ∃ x y : Int, (p : Int) ∣ c * x * x + d * y * y - 1 := by
  have hp2 := hp.1
  have hpos : (0 : Int) < p := by omega
  let h := (p - 1) / 2
  have hh : 2 * h + 1 = p := by omega
  let f : Nat → Nat := fun i =>
    if i < h + 1 then ((c * i * i) % (p : Int)).toNat
    else ((1 - d * ((i - (h + 1) : Nat) : Int) * ((i - (h + 1) : Nat) : Int)) % (p : Int)).toNat
  have hf : ∀ i, i < p + 1 → f i < p := by
    intro i _
    have h1 := toNat_emod_lt hpos (c * i * i)
    have h2 := toNat_emod_lt hpos
      (1 - d * ((i - (h + 1) : Nat) : Int) * ((i - (h + 1) : Nat) : Int))
    simp only [Int.toNat_natCast] at h1 h2
    show (if i < h + 1 then _ else _) < p
    split <;> omega
  obtain ⟨i, j, hij, hj, he⟩ := pigeonhole p (p + 1) f hf (by omega)
  by_cases hi1 : i < h + 1
  · by_cases hj1 : j < h + 1
    · -- two squares `c i²`, `c j²` coincide: impossible
      have he' : ((c * i * i) % (p : Int)).toNat = ((c * j * j) % (p : Int)).toNat := by
        have := he; simp only [f, hi1, hj1, ite_true] at this; exact this
      exact (sq_ne_mod hp hodd hc hij (by omega) (dvd_sub_of_toNat_emod_eq hpos he')).elim
    · -- the solution
      have he' : ((c * i * i) % (p : Int)).toNat =
          ((1 - d * ((j - (h + 1) : Nat) : Int) * ((j - (h + 1) : Nat) : Int)) % (p : Int)).toNat := by
        have := he; simp only [f, hi1, hj1, ite_true, ite_false] at this; exact this
      refine ⟨i, ((j - (h + 1) : Nat) : Int), ?_⟩
      have := dvd_sub_of_toNat_emod_eq hpos he'
      rw [show c * (i : Int) * i + d * ((j - (h + 1) : Nat) : Int) * ((j - (h + 1) : Nat) : Int) - 1
        = c * i * i - (1 - d * ((j - (h + 1) : Nat) : Int) * ((j - (h + 1) : Nat) : Int)) by grind]
      exact this
  · have hj1 : ¬ j < h + 1 := by omega
    have he' : ((1 - d * ((i - (h + 1) : Nat) : Int) * ((i - (h + 1) : Nat) : Int)) % (p : Int)).toNat
        = ((1 - d * ((j - (h + 1) : Nat) : Int) * ((j - (h + 1) : Nat) : Int)) % (p : Int)).toNat := by
      have := he; simp only [f, hi1, hj1, ite_false] at this; exact this
    have hd' := dvd_sub_of_toNat_emod_eq hpos he'
    refine (sq_ne_mod hp hodd hd (i := i - (h + 1)) (j := j - (h + 1)) (by omega) (by omega) ?_).elim
    rw [show d * ((i - (h + 1) : Nat) : Int) * ((i - (h + 1) : Nat) : Int) - d * ((j - (h + 1) : Nat) : Int) * ((j - (h + 1) : Nat) : Int) =
      -((1 - d * ((i - (h + 1) : Nat) : Int) * ((i - (h + 1) : Nat) : Int)) - (1 - d * ((j - (h + 1) : Nat) : Int) * ((j - (h + 1) : Nat) : Int))) by grind]
    exact Int.dvd_neg.2 hd'

/-! ## Congruences in ℤₚ -/

namespace Zp

variable {p : Nat}

/-- Congruence modulo `pᵏ` is reflexive. -/
theorem ModPow.refl (k : Nat) (x : Zp p) : ModPow k x x := by
  rw [← mk_rep x]; apply modPow_mk.2; rw [Int.sub_self]; exact Int.dvd_zero _

/-- Congruence modulo `pᵏ` is symmetric. -/
theorem ModPow.symm {k : Nat} {x y : Zp p} (h : ModPow k x y) : ModPow k y x := by
  rw [← mk_rep x, ← mk_rep y] at *
  have h := modPow_mk.1 h
  apply modPow_mk.2
  rw [show (rep y).seq k - (rep x).seq k = -((rep x).seq k - (rep y).seq k) by omega]
  exact Int.dvd_neg.2 h

/-- Congruence modulo `pᵏ` is transitive. -/
theorem ModPow.trans {k : Nat} {x y z : Zp p} (h : ModPow k x y) (h' : ModPow k y z) :
    ModPow k x z := by
  rw [← mk_rep x, ← mk_rep y, ← mk_rep z] at *
  have h := modPow_mk.1 h
  have h' := modPow_mk.1 h'
  apply modPow_mk.2
  rw [show (rep x).seq k - (rep z).seq k =
    ((rep x).seq k - (rep y).seq k) + ((rep y).seq k - (rep z).seq k) by omega]
  exact Int.dvd_add h h'

/-- Congruences modulo `pᵏ` can be multiplied. -/
theorem ModPow.mul {k : Nat} {a b c d : Zp p} (h : ModPow k a b) (h' : ModPow k c d) :
    ModPow k (a * c) (b * d) := by
  rw [← mk_rep a, ← mk_rep b, ← mk_rep c, ← mk_rep d] at *
  have h := modPow_mk.1 h
  have h' := modPow_mk.1 h'
  rw [mk_mul, mk_mul]
  apply modPow_mk.2
  show _ ∣ (rep a).seq k * (rep c).seq k - (rep b).seq k * (rep d).seq k
  exact PSeq.dvd_mul_sub h h'

/-- Congruence of integer constants: `a ≡ b (mod pᵏ)` in ℤₚ iff `pᵏ ∣ a − b`. -/
theorem modPow_intCast {k : Nat} {a b : Int} :
    ModPow k (a : Zp p) (b : Zp p) ↔ (p : Int) ^ k ∣ a - b := Iff.rfl

/-- An integer approximation of `x` to precision `pᵏ`: `x ≡ xₖ (mod pᵏ)` where `xₖ` is the
`k`-th term of a representative. -/
theorem modPow_rep (k : Nat) (x : Zp p) : ModPow k x ((rep x).seq k : Zp p) := by
  conv => lhs; rw [← mk_rep x]
  apply modPow_mk.2
  show _ ∣ (rep x).seq k - (rep x).seq k
  rw [Int.sub_self]; exact Int.dvd_zero _

/-- The square of an element is congruent to the square of anything it is congruent to. -/
theorem ModPow.sq {k : Nat} {x y : Zp p} (h : ModPow k x y) : ModPow k (x * x) (y * y) :=
  h.mul h

/-- **Square roots of `p`-adic units.** For an odd prime `p`, if `u ∈ ℤₚ` is congruent modulo
`p` to `a²` with `a` an integer prime to `p`, then `u = x²` for some `x ∈ ℤₚ`. (Hensel's lemma
for the integer approximations of `u`, then compactness of ℤₚ.) -/
theorem exists_sq_of_modPow (hp : Prime p) (hodd : p % 2 = 1) {u : Zp p} {a : Int}
    (ha : ¬ (p : Int) ∣ a) (h : ModPow 1 u ((a * a : Int) : Zp p)) : ∃ x : Zp p, x * x = u := by
  let c : Nat → Int := fun N => (rep u).seq (N + 1)
  -- `c N ≡ a² (mod p)`
  have hc : ∀ N, (p : Int) ∣ c N - a * a := by
    intro N
    have h1 : ModPow 1 ((c N : Int) : Zp p) ((a * a : Int) : Zp p) :=
      ((modPow_rep (N + 1) u).mono (by omega)).symm.trans h
    have := modPow_intCast.1 h1
    rwa [Int.pow_one] at this
  -- Hensel: a square root of each `c N`
  have hroot : ∀ N, ∃ x : Zp p, x * x = ((c N : Int) : Zp p) := by
    intro N
    obtain ⟨x, hx, -⟩ := hensel hp [-(c N), 0, 1] a
      (by
        show (p : Int) ∣ -(c N) + a * (0 + a * (1 + a * 0))
        rw [show -(c N) + a * (0 + a * (1 + a * 0)) = -(c N - a * a) by grind]
        exact Int.dvd_neg.2 (hc N))
      (by
        show ¬ (p : Int) ∣ (0 + a * (1 + a * 0)) + a * ((1 + a * 0) + a * (0 + a * 0))
        rw [show (0 + a * (1 + a * 0)) + a * ((1 + a * 0) + a * (0 + a * 0)) = 2 * a by grind]
        exact not_dvd_two_mul hp hodd ha)
    refine ⟨x, ?_⟩
    rw [peval_sq_sub] at hx
    have := congrArg (· + ((c N : Int) : Zp p)) hx
    rw [show x * x - ((c N : Int) : Zp p) + ((c N : Int) : Zp p) = x * x by grind,
      show (0 : Zp p) + ((c N : Int) : Zp p) = ((c N : Int) : Zp p) by grind] at this
    exact this
  let xs : Nat → Zp p := fun N => Classical.choose (hroot N)
  have hxs : ∀ N, xs N * xs N = ((c N : Int) : Zp p) := fun N => Classical.choose_spec (hroot N)
  -- `x_N² ≡ u (mod p^(N+1))`
  have hxu : ∀ N, ModPow (N + 1) (xs N * xs N) u := fun N => by
    rw [hxs N]; exact (modPow_rep (N + 1) u).symm
  obtain ⟨φ, hφ, L, hL⟩ := seqCompact hp xs
  have hφge : ∀ i, i ≤ φ i := by
    intro i; induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := hφ i; omega
  refine ⟨L, eq_iff_modPow.2 fun k => ?_⟩
  obtain ⟨N, hN⟩ := hL k
  have h1 := (hN (max N k) (Nat.le_max_left _ _)).sq
  have h2 := (hxu (φ (max N k))).mono (show k ≤ φ (max N k) + 1 by
    have := hφge (max N k); omega)
  exact h1.symm.trans h2

end Zp

end Foundations.Langlands.Padic
