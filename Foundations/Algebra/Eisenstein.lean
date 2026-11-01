import Foundations.Algebra.QuinticReal

/-!
# Gauss's lemma and Eisenstein's criterion for `x⁵ - 6x + 3`

To show that the Galois group of `x⁵ - 6x + 3` has order divisible by `5`, one needs that the
polynomial is **irreducible over `ℚ`**. Eisenstein's criterion (1850) at the prime `3` gives
this at once: `3` divides every coefficient except the leading one, and `9` does not divide the
constant term `3`.

The criterion is a statement about integer factorisations. The passage from rational to
integer factorisations is **Gauss's lemma** (*Disquisitiones*, art. 42): if `m · f = G · H` with
integer polynomials `G, H` and a positive integer `m`, then every prime `p ∣ m` divides all
coefficients of `G` or all coefficients of `H`. So `p` can be cancelled, and by descent on `m`
one reaches a factorisation `f = G' · H'` over `ℤ` with the same degrees.

Both steps rest on one observation about **lowest coefficients**. Let `i` be the least index
with `p ∤ Gᵢ` and `j` the least with `p ∤ Hⱼ`. In the coefficient
`∑ₖ Gₖ H_{i+j-k}` of `x^{i+j}` in `G · H`, every term except `Gᵢ Hⱼ` has a factor divisible by
`p`, so the coefficient is not divisible by `p`.

This file works with integer polynomials as coefficient sequences `ℕ → ℤ`, multiplied by the
convolution `conv`. The bridge to polynomials over the prime field of a field of
characteristic zero is in the next file.
-/

namespace Foundations.Algebra

/-! ## Finite sums of integers -/

/-- The sum `t 0 + t 1 + ⋯ + t (n - 1)` of integers. -/
def zsum (t : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => zsum t n + t n

/-- Sums of termwise equal sequences agree. -/
theorem zsum_congr {s t : Nat → Int} : ∀ n, (∀ k, k < n → s k = t k) → zsum s n = zsum t n
  | 0, _ => rfl
  | n + 1, h => by
    show zsum s n + s n = zsum t n + t n
    rw [zsum_congr n (fun k hk => h k (by omega)), h n (by omega)]

/-- A sum with only one possibly non-zero term equals that term. -/
theorem zsum_single (t : Nat → Int) {i : Nat} :
    ∀ n, i < n → (∀ k, k < n → k ≠ i → t k = 0) → zsum t n = t i
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, hi, h => by
    show zsum t n + t n = t i
    by_cases hin : i = n
    · subst hin
      have : zsum t i = 0 := by
        have key : ∀ m, m ≤ i → zsum t m = 0 := by
          intro m
          induction m with
          | zero => intro _; rfl
          | succ m ih => intro hm; show zsum t m + t m = 0; rw [ih (by omega), h m (by omega) (by omega)]; rfl
        exact key i (Nat.le_refl i)
      rw [this, Int.zero_add]
    · rw [zsum_single t n (by omega) (fun k hk hki => h k (by omega) hki), h n (by omega) (Ne.symm hin),
        Int.add_zero]

/-- If every term but the `i`-th is divisible by `p`, the sum is congruent to the `i`-th term. -/
theorem dvd_zsum_sub (t : Nat → Int) (p : Int) {i : Nat} :
    ∀ n, i < n → (∀ k, k < n → k ≠ i → p ∣ t k) → p ∣ zsum t n - t i
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, hi, h => by
    show p ∣ zsum t n + t n - t i
    by_cases hin : i = n
    · subst hin
      have key : ∀ m, m ≤ i → p ∣ zsum t m := by
        intro m
        induction m with
        | zero => intro _; exact Int.dvd_zero p
        | succ m ih => intro hm; exact Int.dvd_add (ih (by omega)) (h m (by omega) (by omega))
      have := key i (Nat.le_refl i)
      rw [show zsum t i + t i - t i = zsum t i by omega]; exact this
    · have h1 := dvd_zsum_sub t p n (by omega) (fun k hk hki => h k (by omega) hki)
      have h2 := h n (by omega) (Ne.symm hin)
      rw [show zsum t n + t n - t i = (zsum t n - t i) + t n by omega]
      exact Int.dvd_add h1 h2

/-- Every term divisible by `p` makes the sum divisible by `p`. -/
theorem dvd_zsum (t : Nat → Int) (p : Int) : ∀ n, (∀ k, k < n → p ∣ t k) → p ∣ zsum t n
  | 0, _ => Int.dvd_zero p
  | n + 1, h => Int.dvd_add (dvd_zsum t p n fun k hk => h k (by omega)) (h n (by omega))

/-- Scaling a sum: `c · ∑ tₖ = ∑ c tₖ`. -/
theorem mul_zsum (c : Int) (t : Nat → Int) : ∀ n, c * zsum t n = zsum (fun k => c * t k) n
  | 0 => Int.mul_zero c
  | n + 1 => by
    show c * (zsum t n + t n) = zsum (fun k => c * t k) n + c * t n
    rw [Int.mul_add, mul_zsum c t n]

/-! ## Integer polynomials as coefficient sequences -/

/-- A divisor of `a` divides `a * b`. -/
theorem dvd_mul_of_left {p a b : Int} (h : p ∣ a) : p ∣ a * b :=
  Int.dvd_trans h (Int.dvd_mul_right a b)

/-- A divisor of `b` divides `a * b`. -/
theorem dvd_mul_of_right {p a b : Int} (h : p ∣ b) : p ∣ a * b :=
  Int.dvd_trans h (Int.dvd_mul_left a b)

/-- The **product** of integer polynomials given by coefficient sequences: the coefficient of
`xⁿ` in `G · H` is `∑_{k ≤ n} Gₖ H_{n-k}`. -/
def conv (G H : Nat → Int) (n : Nat) : Int := zsum (fun k => G k * H (n - k)) (n + 1)

/-- A primality fact for integers: if a prime `p` divides `a * b` (in `ℤ`), it divides `a` or
`b`. -/
theorem int_prime_dvd_mul {p : Nat} (hp : IsPrime p) {a b : Int} (h : (p : Int) ∣ a * b) :
    (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  rcases hp.dvd_mul h with h' | h'
  · exact Or.inl (Int.ofNat_dvd_left.2 h')
  · exact Or.inr (Int.ofNat_dvd_left.2 h')

/-- **The lowest-coefficient lemma.** If a prime `p` fails to divide some coefficient of `G` and
some coefficient of `H`, then it fails to divide some coefficient of `G · H`: namely the one at
`i + j`, where `i` and `j` are the least such indices. -/
theorem not_dvd_conv {p : Nat} (hp : IsPrime p) {G H : Nat → Int}
    (hG : ∃ i, ¬ (p : Int) ∣ G i) (hH : ∃ j, ¬ (p : Int) ∣ H j) :
    ∃ n, ¬ (p : Int) ∣ conv G H n := by
  obtain ⟨i, hi, himin⟩ := FiniteType.exists_least _ hG
  obtain ⟨j, hj, hjmin⟩ := FiniteType.exists_least _ hH
  refine ⟨i + j, fun hdvd => ?_⟩
  have hsub : (p : Int) ∣ conv G H (i + j) - G i * H (i + j - i) := by
    apply dvd_zsum_sub _ _ _ (by omega)
    intro k hk hki
    rcases Nat.lt_or_gt_of_ne hki with hlt | hgt
    · have := Classical.byContradiction fun h => himin k hlt h
      exact dvd_mul_of_left this
    · have := Classical.byContradiction fun h => hjmin (i + j - k) (by omega) h
      exact dvd_mul_of_right this
  rw [show i + j - i = j by omega] at hsub
  have : (p : Int) ∣ G i * H j := by
    have e : G i * H j = conv G H (i + j) - (conv G H (i + j) - G i * H j) := by omega
    rw [e]; exact Int.dvd_sub hdvd hsub
  rcases int_prime_dvd_mul hp this with h | h
  · exact hi h
  · exact hj h

/-- `G` has no coefficient at index above `d`. -/
def SuppLE (G : Nat → Int) (d : Nat) : Prop := ∀ k, d < k → G k = 0

/-- Every natural number `m ≥ 2` has a prime factor. -/
theorem exists_prime_factor {m : Nat} (hm : 2 ≤ m) : ∃ p, IsPrime p ∧ p ∣ m := by
  obtain ⟨p, ⟨hp2, hpm⟩, hmin⟩ := FiniteType.exists_least (fun d => 2 ≤ d ∧ d ∣ m) ⟨m, hm, Nat.dvd_refl m⟩
  refine ⟨p, ⟨hp2, fun d hd => ?_⟩, hpm⟩
  have hp0 : 0 < p := by omega
  have hdle : d ≤ p := Nat.le_of_dvd hp0 hd
  by_cases h1 : d = 1
  · exact Or.inl h1
  · right
    have hd0 : d ≠ 0 := by rintro rfl; rw [Nat.zero_dvd] at hd; omega
    apply Classical.byContradiction; intro hne
    exact hmin d (by omega) ⟨by omega, Nat.dvd_trans hd hpm⟩

/-- **Gauss's lemma** (by descent). If `m · F = G · H` for a positive integer `m` and integer
polynomials `G, H` with `deg G ≤ d`, `deg H ≤ e`, then `F = G' · H'` for integer polynomials with
`deg G' ≤ d`, `deg H' ≤ e`. -/
theorem gauss_descent (F : Nat → Int) (d e : Nat) :
    ∀ (m : Nat) (G H : Nat → Int), 0 < m → (∀ n, (m : Int) * F n = conv G H n) →
      SuppLE G d → SuppLE H e →
      ∃ G' H' : Nat → Int, (∀ n, F n = conv G' H' n) ∧ SuppLE G' d ∧ SuppLE H' e := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro G H hm hF hG hH
    by_cases h1 : m = 1
    · subst h1; exact ⟨G, H, fun n => by rw [← hF n]; simp, hG, hH⟩
    obtain ⟨p, hp, hpm⟩ := exists_prime_factor (m := m) (by omega)
    obtain ⟨m', rfl⟩ := hpm
    have hp0 : 0 < p := by have := hp.1; omega
    have hm' : 0 < m' := Nat.pos_of_mul_pos_left hm
    have hlt : m' < p * m' := by
      have := hp.1
      calc m' = 1 * m' := (Nat.one_mul m').symm
        _ < p * m' := Nat.mul_lt_mul_of_pos_right (by omega) hm'
    -- `p` divides every coefficient of `G` or every coefficient of `H`
    have hall : (∀ k, (p : Int) ∣ G k) ∨ (∀ k, (p : Int) ∣ H k) := by
      apply Classical.byContradiction; intro hno
      have hG' : ∃ i, ¬ (p : Int) ∣ G i :=
        Classical.byContradiction fun h => hno (Or.inl fun k =>
          Classical.byContradiction fun hk => h ⟨k, hk⟩)
      have hH' : ∃ j, ¬ (p : Int) ∣ H j :=
        Classical.byContradiction fun h => hno (Or.inr fun k =>
          Classical.byContradiction fun hk => h ⟨k, hk⟩)
      obtain ⟨n, hn⟩ := not_dvd_conv hp hG' hH'
      apply hn; rw [← hF n, Int.natCast_mul, Int.mul_assoc]
      exact Int.dvd_mul_right _ _
    have hpz : (p : Int) ≠ 0 := by omega
    rcases hall with hdiv | hdiv
    · let G' : Nat → Int := fun k => G k / p
      have hGG : ∀ k, G k = p * G' k := fun k => (Int.mul_ediv_cancel' (hdiv k)).symm
      refine ih m' hlt G' H hm' (fun n => ?_) (fun k hk => ?_) hH
      · apply Int.eq_of_mul_eq_mul_left hpz
        have e1 : (p : Int) * conv G' H n = conv G H n := by
          unfold conv; rw [mul_zsum]
          exact zsum_congr _ fun k _ => by rw [hGG k, Int.mul_assoc]
        rw [e1, ← hF n, Int.natCast_mul, Int.mul_assoc]
      · show G k / p = 0; rw [hG k hk]; exact Int.zero_ediv _
    · let H' : Nat → Int := fun k => H k / p
      have hHH : ∀ k, H k = p * H' k := fun k => (Int.mul_ediv_cancel' (hdiv k)).symm
      refine ih m' hlt G H' hm' (fun n => ?_) hG (fun k hk => ?_)
      · apply Int.eq_of_mul_eq_mul_left hpz
        have e1 : (p : Int) * conv G H' n = conv G H n := by
          unfold conv; rw [mul_zsum]
          exact zsum_congr _ fun k _ => by rw [hHH (n - k)]; ac_rfl
        rw [e1, ← hF n, Int.natCast_mul, Int.mul_assoc]
      · show H k / p = 0; rw [hH k hk]; exact Int.zero_ediv _

/-! ## Eisenstein's criterion for `x⁵ - 6x + 3` -/

/-- The coefficient sequence of `x⁵ - 6x + 3`. -/
def quinticCoeffs : Nat → Int
  | 0 => 3
  | 1 => -6
  | 5 => 1
  | _ => 0

/-- The top coefficient of a product of polynomials of degrees at most `d` and `5 - d`. -/
theorem conv_top {G H : Nat → Int} {d : Nat} (hd : d ≤ 5) (hG : SuppLE G d) (hH : SuppLE H (5 - d)) :
    conv G H 5 = G d * H (5 - d) := by
  unfold conv
  apply zsum_single _ 6 (by omega)
  intro k hk hkd
  rcases Nat.lt_or_gt_of_ne hkd with h | h
  · rw [hH (5 - k) (by omega), Int.mul_zero]
  · rw [hG k h, Int.zero_mul]

/-- **Eisenstein at `3`.** `x⁵ - 6x + 3` is not a product of integer polynomials of degrees
`d` and `5 - d` with `1 ≤ d ≤ 4`. -/
theorem quintic_eisenstein {G H : Nat → Int} {d : Nat} (hd1 : 1 ≤ d) (hd4 : d ≤ 4)
    (hF : ∀ n, quinticCoeffs n = conv G H n) (hG : SuppLE G d) (hH : SuppLE H (5 - d)) : False := by
  have htop : G d * H (5 - d) = 1 := by rw [← conv_top (by omega) hG hH, ← hF 5]; rfl
  have hGd : ¬ (3 : Int) ∣ G d := fun h => by
    have := dvd_mul_of_left (b := H (5 - d)) h
    rw [htop] at this; exact absurd this (by decide)
  have hHd : ¬ (3 : Int) ∣ H (5 - d) := fun h => by
    have := dvd_mul_of_right (a := G d) h
    rw [htop] at this; exact absurd this (by decide)
  obtain ⟨i, hi, himin⟩ := FiniteType.exists_least (fun i => ¬ (3 : Int) ∣ G i) ⟨d, hGd⟩
  obtain ⟨j, hj, hjmin⟩ := FiniteType.exists_least (fun j => ¬ (3 : Int) ∣ H j) ⟨5 - d, hHd⟩
  have hid : i ≤ d := Nat.le_of_not_lt fun h => himin d h hGd
  have hje : j ≤ 5 - d := Nat.le_of_not_lt fun h => hjmin (5 - d) h hHd
  -- the coefficient at `i + j` is not divisible by `3`
  have hnd : ¬ (3 : Int) ∣ conv G H (i + j) := by
    intro hdvd
    have hsub : (3 : Int) ∣ conv G H (i + j) - G i * H (i + j - i) := by
      apply dvd_zsum_sub _ _ _ (by omega)
      intro k hk hki
      rcases Nat.lt_or_gt_of_ne hki with hlt | hgt
      · exact dvd_mul_of_left (Classical.byContradiction fun h => himin k hlt h)
      · exact dvd_mul_of_right
          (Classical.byContradiction fun h => hjmin (i + j - k) (by omega) h)
    rw [show i + j - i = j by omega] at hsub
    have : (3 : Int) ∣ G i * H j := by
      have e : G i * H j = conv G H (i + j) - (conv G H (i + j) - G i * H j) := by omega
      rw [e]; exact Int.dvd_sub hdvd hsub
    rcases int_prime_dvd_mul (p := 3) ⟨by decide, fun d hd => by
      have : d ≤ 3 := Nat.le_of_dvd (by decide) hd
      match d, this, hd with
      | 0, _, h => exact absurd h (by decide)
      | 1, _, _ => exact Or.inl rfl
      | 2, _, h => exact absurd h (by decide)
      | 3, _, _ => exact Or.inr rfl⟩ this with h | h
    · exact hi h
    · exact hj h
  -- but all coefficients of `x⁵ - 6x + 3` except the leading one are divisible by `3`
  have h5 : i + j = 5 := by
    apply Classical.byContradiction; intro hne
    apply hnd; rw [← hF]
    match h : i + j with
    | 0 => exact ⟨1, rfl⟩
    | 1 => exact ⟨-2, rfl⟩
    | 2 => exact ⟨0, rfl⟩
    | 3 => exact ⟨0, rfl⟩
    | 4 => exact ⟨0, rfl⟩
    | 5 => exact absurd h hne
    | n + 6 => exact ⟨0, rfl⟩
  have hG0 : (3 : Int) ∣ G 0 := Classical.byContradiction fun h => himin 0 (by omega) h
  have hH0 : (3 : Int) ∣ H 0 := Classical.byContradiction fun h => hjmin 0 (by omega) h
  have h0 : G 0 * H 0 = 3 := by
    have := hF 0; unfold conv at this; simp [zsum] at this; exact this.symm
  have : (9 : Int) ∣ G 0 * H 0 := Int.mul_dvd_mul hG0 hH0
  rw [h0] at this; exact absurd this (by decide)

end Foundations.Algebra
