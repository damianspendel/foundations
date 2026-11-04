import Foundations.Langlands.Squares.Identities
import Foundations.Combinatorics.Pigeonhole

/-!
# Lagrange's four-square theorem

Diophantus seems to have assumed, without comment, that every number is a sum of four squares
(in problems of Book IV of the *Arithmetica*), and Bachet stated it explicitly in his 1621
edition. Fermat claimed a
proof by infinite descent but never published one. Euler worked on it for forty years: he found
the four-square identity (1748, see `Identities`) and showed that `x² + y² + 1 ≡ 0 (mod p)` is
always solvable, but could not close the descent. Lagrange did, in 1770, explicitly building on
Euler's work; Euler soon gave a simpler version of the descent. We follow that classical route.

1. **Euler's congruence** (`exists_sq_add_sq_add_one`). For an odd prime `p` the `(p + 1)/2`
   values `x² mod p` (`0 ≤ x ≤ (p − 1)/2`) are distinct, and so are the `(p + 1)/2` values
   `−1 − y² mod p`; as `p + 1 > p`, the pigeonhole principle forces a coincidence between the two
   families, i.e. `x² + y² + 1 ≡ 0 (mod p)`. Hence `m₀ p = x² + y² + 1² + 0²` with `0 < m₀ < p`.
2. **Descent** (`descent`). If `m p` is a sum of four squares with `1 < m < p`, so is `r p` for
   some `0 < r < m`: reduce the four numbers modulo `m` into `(−m/2, m/2]`, write the sum of the
   residues' squares as `m r`, and divide the Euler product `(m p)(m r)` by `m²`. The two
   degenerate cases `r = 0` and `r = m` would make `m` divide `p`.
3. **Lagrange's theorem** (`lagrange_four_squares`) follows from the prime case by Euler's
   identity and induction on the number of prime factors.
-/

namespace Foundations.Langlands.Squares

open Foundations.Numbers.Arith

/-! ## Euler's congruence `x² + y² + 1 ≡ 0 (mod p)` -/

/-- For an odd prime `p = 2h + 1`, the squares `i²` with `0 ≤ i ≤ h` are pairwise incongruent
modulo `p`. -/
theorem sq_mod_inj {p h i j : Nat} (hp : Prime p) (hph : p = 2 * h + 1) (hij : i < j) (hj : j ≤ h)
    (e : i * i % p = j * j % p) : False := by
  have h0 : (j * j - i * i) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq e.symm
  rw [Nat.mul_self_sub_mul_self_eq] at h0
  rcases euclid_lemma hp (Nat.dvd_of_mod_eq_zero h0) with h1 | h1
  · have := Nat.le_of_dvd (by omega) h1; omega
  · have := Nat.le_of_dvd (by omega) h1; omega

/-- **Euler's congruence.** For an odd prime `p = 2h + 1` there are `x, y ≤ h` with
`p ∣ x² + y² + 1`. (Pigeonhole on the `p + 1` residues `x²` and `−1 − y²`.) -/
theorem exists_sq_add_sq_add_one {p h : Nat} (hp : Prime p) (hph : p = 2 * h + 1) :
    ∃ x y : Nat, x ≤ h ∧ y ≤ h ∧ p ∣ x * x + y * y + 1 := by
  let f : Nat → Nat := fun i =>
    if i ≤ h then i * i % p else p - 1 - (i - (h + 1)) * (i - (h + 1)) % p
  have hp0 : 0 < p := by omega
  have hf : ∀ i, i < p + 1 → f i < p := by
    intro i _
    show (if i ≤ h then i * i % p else p - 1 - (i - (h + 1)) * (i - (h + 1)) % p) < p
    split
    · exact Nat.mod_lt _ hp0
    · omega
  obtain ⟨i, j, hij, hj, he⟩ := Foundations.Combinatorics.pigeonhole p (p + 1) f hf (by omega)
  simp only [f] at he
  by_cases hi' : i ≤ h
  · by_cases hj' : j ≤ h
    · simp only [hi', hj', ↓reduceIte] at he
      exact absurd (sq_mod_inj hp hph hij hj' he) id
    · simp only [hi', hj', ↓reduceIte] at he
      refine ⟨i, j - (h + 1), hi', by omega, ?_⟩
      have hl := Nat.mod_lt ((j - (h + 1)) * (j - (h + 1))) hp0
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, Nat.add_mod (i * i), he]
      have hm : (p - 1 - (j - (h + 1)) * (j - (h + 1)) % p +
          (j - (h + 1)) * (j - (h + 1)) % p) = p - 1 := by omega
      rw [hm, ← Nat.add_mod, show p - 1 + 1 = p by omega, Nat.mod_self]
  · have hj' : ¬ j ≤ h := by omega
    simp only [hi', hj', ↓reduceIte] at he
    have hl1 := Nat.mod_lt ((i - (h + 1)) * (i - (h + 1))) hp0
    have hl2 := Nat.mod_lt ((j - (h + 1)) * (j - (h + 1))) hp0
    exact absurd (sq_mod_inj (i := i - (h + 1)) (j := j - (h + 1)) hp hph (by omega) (by omega)
      (by omega)) id

/-! ## The descent -/

/-- Reduction to a symmetric residue: every integer `x` is `y + M k` with `−M < 2y ≤ M`. -/
theorem exists_symm_residue (x M : Int) (hM : 0 < M) :
    ∃ y k : Int, x = y + M * k ∧ -M < 2 * y ∧ 2 * y ≤ M := by
  refine ⟨(x + (M - 1) / 2) % M - (M - 1) / 2, (x + (M - 1) / 2) / M, ?_, ?_, ?_⟩
  all_goals
    have e := Int.emod_add_mul_ediv (x + (M - 1) / 2) M
    have h1 := Int.emod_nonneg (x + (M - 1) / 2) (b := M) (by omega)
    have h2 := Int.emod_lt_of_pos (x + (M - 1) / 2) hM
    omega

/-- A divisor `m` of the prime `p` with `1 < m < p` cannot exist (integer form). -/
theorem not_int_dvd_prime {p m : Nat} (hp : Prime p) (h1 : 1 < m) (h2 : m < p) (c : Int)
    (h : (p : Int) = (m : Int) * c) : False := by
  have hd : (m : Int) ∣ (p : Int) := ⟨c, h⟩
  rcases hp.2 m (Int.natCast_dvd_natCast.1 hd) with h | h <;> omega

/-- `4 y² ≤ M²` from `−M < 2y ≤ M`. -/
theorem four_sq_le {y M : Int} (h1 : -M < 2 * y) (h2 : 2 * y ≤ M) : 4 * (y * y) ≤ M * M := by
  have := sq_le_sq_of_abs_le (t := 2 * y) (M := M) (by omega) h2
  have e : 2 * y * (2 * y) = 4 * (y * y) := by grind
  omega

/-- If moreover `4 y² = M²`, then `2y = M`. -/
theorem two_mul_eq_of_four_sq {y M : Int} (h1 : -M < 2 * y) (h2 : 2 * y ≤ M)
    (h : 4 * (y * y) = M * M) : 2 * y = M := by
  apply Classical.byContradiction
  intro hne
  have := sq_lt_sq_of_abs_lt (t := 2 * y) (M := M) h1 (by omega)
  have e : 2 * y * (2 * y) = 4 * (y * y) := by grind
  omega

/-- **The descent step.** If `m p` is a sum of four squares with `0 < m < p`, then so is `p`.
(Strong induction on `m`: from `m > 1` we produce `0 < r < m` with `r p` a sum of four squares.) -/
theorem descent {p : Nat} (hp : Prime p) :
    ∀ m : Nat, 0 < m → m < p → IsSum4 ((m : Int) * p) → IsSum4 (p : Int) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro hm0 hmp hS
  by_cases hm1 : m = 1
  · subst hm1; simpa using hS
  have hm2 : 1 < m := by omega
  obtain ⟨x1, x2, x3, x4, hx⟩ := hS
  have hM : (0 : Int) < (m : Int) := by omega
  obtain ⟨y1, k1, e1, a1, b1⟩ := exists_symm_residue x1 m hM
  obtain ⟨y2, k2, e2, a2, b2⟩ := exists_symm_residue x2 m hM
  obtain ⟨y3, k3, e3, a3, b3⟩ := exists_symm_residue x3 m hM
  obtain ⟨y4, k4, e4, a4, b4⟩ := exists_symm_residue x4 m hM
  generalize hMdef : (m : Int) = M at *
  -- `r` is the quotient `(Σ yᵢ²)/M`, written explicitly.
  let r : Int := (p : Int) - 2 * (y1 * k1 + y2 * k2 + y3 * k3 + y4 * k4)
    - M * (k1 * k1 + k2 * k2 + k3 * k3 + k4 * k4)
  have hy : y1 * y1 + y2 * y2 + y3 * y3 + y4 * y4 = M * r := by
    subst e1 e2 e3 e4; grind
  have q1 := four_sq_le a1 b1
  have q2 := four_sq_le a2 b2
  have q3 := four_sq_le a3 b3
  have q4 := four_sq_le a4 b4
  have s1 := sq_nonneg' y1
  have s2 := sq_nonneg' y2
  have s3 := sq_nonneg' y3
  have s4 := sq_nonneg' y4
  have hr0 : 0 ≤ r := Int.le_of_mul_le_mul_left (a := M) (by omega) hM
  have hrM : r ≤ M := Int.le_of_mul_le_mul_left (a := M) (by omega) hM
  -- Degenerate case `r = 0`: all `yᵢ = 0`, so `M ∣ p`.
  by_cases hr0' : r = 0
  · have hz : y1 * y1 + y2 * y2 + y3 * y3 + y4 * y4 = 0 := by rw [hy, hr0', Int.mul_zero]
    have z1 := eq_zero_of_sq_eq_zero (t := y1) (by omega)
    have z2 := eq_zero_of_sq_eq_zero (t := y2) (by omega)
    have z3 := eq_zero_of_sq_eq_zero (t := y3) (by omega)
    have z4 := eq_zero_of_sq_eq_zero (t := y4) (by omega)
    subst z1 z2 z3 z4
    exact absurd (not_int_dvd_prime hp hm2 hmp (k1 * k1 + k2 * k2 + k3 * k3 + k4 * k4)
      (by rw [hMdef]; grind)) id
  -- Degenerate case `r = M`: all `2yᵢ = M`, so again `M ∣ p`.
  by_cases hrM' : r = M
  · have hz : y1 * y1 + y2 * y2 + y3 * y3 + y4 * y4 = M * M := by rw [hy, hrM']
    have t1 := two_mul_eq_of_four_sq a1 b1 (by omega)
    have t2 := two_mul_eq_of_four_sq a2 b2 (by omega)
    have t3 := two_mul_eq_of_four_sq a3 b3 (by omega)
    have t4 := two_mul_eq_of_four_sq a4 b4 (by omega)
    exact absurd (not_int_dvd_prime hp hm2 hmp
      (1 + (k1 + k2 + k3 + k4) + (k1 * k1 + k2 * k2 + k3 * k3 + k4 * k4))
      (by rw [hMdef]; grind)) id
  -- Main case `0 < r < M`: divide Euler's product by `M²`.
  have hlt : r.toNat < m := by omega
  apply ih r.toNat hlt (by omega) (by omega)
  rw [Int.toNat_of_nonneg hr0]
  let w1 := r + (k1 * y1 + k2 * y2 + k3 * y3 + k4 * y4)
  let w2 := k1 * y2 - k2 * y1 + k3 * y4 - k4 * y3
  let w3 := k1 * y3 - k3 * y1 + k4 * y2 - k2 * y4
  let w4 := k1 * y4 - k4 * y1 + k2 * y3 - k3 * y2
  refine ⟨w1, w2, w3, w4, ?_⟩
  have hE := euler_four_square_identity x1 x2 x3 x4 y1 y2 y3 y4
  rw [hx, hy] at hE
  have z1 : x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 = M * w1 := by
    subst e1 e2 e3 e4; grind
  have z2 : x1 * y2 - x2 * y1 + x3 * y4 - x4 * y3 = M * w2 := by
    subst e1 e2 e3 e4; grind
  have z3 : x1 * y3 - x3 * y1 + x4 * y2 - x2 * y4 = M * w3 := by
    subst e1 e2 e3 e4; grind
  have z4 : x1 * y4 - x4 * y1 + x2 * y3 - x3 * y2 = M * w4 := by
    subst e1 e2 e3 e4; grind
  rw [z1, z2, z3, z4] at hE
  have hMM : M * M ≠ 0 := by
    intro h; rcases Int.mul_eq_zero.1 h with h | h <;> omega
  apply Int.eq_of_mul_eq_mul_left hMM
  grind

/-! ## Primes, then everything -/

/-- **Every prime is a sum of four squares.** -/
theorem prime_isSum4 {p : Nat} (hp : Prime p) : IsSum4 (p : Int) := by
  have h2 := hp.1
  rcases Nat.mod_two_eq_zero_or_one p with hh | hh
  · -- `p` even, so `p = 2 = 1² + 1²`.
    have : p = 2 := by
      rcases hp.2 2 ⟨p / 2, by omega⟩ with h' | h' <;> omega
    subst this
    exact ⟨1, 1, 0, 0, rfl⟩
  · have hh : p = 2 * (p / 2) + 1 := by omega
    generalize p / 2 = h at hh
    obtain ⟨x, y, hx, hy, ⟨m, hm⟩⟩ := exists_sq_add_sq_add_one hp hh
    have hxx : x * x ≤ h * h := Nat.mul_le_mul hx hx
    have hyy : y * y ≤ h * h := Nat.mul_le_mul hy hy
    have hpp : p * p = 4 * (h * h) + 4 * h + 1 := by subst hh; grind
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp at hm
      · exact h0
    have hmp : m < p := Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
    apply descent hp m hm0 hmp
    refine ⟨x, y, 1, 0, ?_⟩
    have : ((x * x + y * y + 1 : Nat) : Int) = ((p * m : Nat) : Int) := by rw [hm]
    push_cast at this
    grind

/-- Every natural number is a sum of four integer squares. -/
theorem isSum4_nat (n : Nat) : IsSum4 (n : Int) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with h | h | h
  · subst h; exact isSum4_zero
  · subst h; exact isSum4_one
  · obtain ⟨p, hp, c, rfl⟩ := exists_prime_dvd h
    have hc : c < p * c := by
      have := hp.1
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0; simp at h
      · have := Nat.mul_lt_mul_of_pos_right (show 1 < p by omega) h0
        omega
    have := (prime_isSum4 hp).mul (ih c hc)
    push_cast
    exact this

/-- **Lagrange's four-square theorem** (1770). Every natural number is a sum of four squares
of natural numbers. -/
theorem lagrange_four_squares (n : Nat) : ∃ a b c d : Nat, a * a + b * b + c * c + d * d = n :=
  nat_of_isSum4 (isSum4_nat n)

/-- Examples: `7 = 2² + 1² + 1² + 1²` needs all four squares; `310 = 17² + 4² + 2² + 1²`. -/
example : 2 * 2 + 1 * 1 + 1 * 1 + 1 * 1 = 7 ∧ 17 * 17 + 4 * 4 + 2 * 2 + 1 * 1 = 310 := by decide

end Foundations.Langlands.Squares
