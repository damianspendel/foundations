import Foundations.NumberTheory.PrimePowers

/-!
# Twisted Chebyshev sums `Σ_{n ≤ N} χ(n) Λ(n)/n`

The prime-counting device of the whole proof is the sum

  `S_χ(N) = Σ_{n ≤ N} χ(n) Λ(n) / n`,

the "logarithmic derivative" `−L'/L(1, χ)` cut off at `N`. Dirichlet's sieve (file
`DirichletCharacters`) turns these into the sum over one residue class:

  `Σ_χ conj χ(a) · S_χ(N) = φ(q) · Σ_{n ≤ N, n ≡ a (q)} Λ(n)/n`.

For the principal character, `S_{χ₀}(N)` is Mertens' sum with the finitely many primes dividing
`q` removed, so it is at least `log N − 1 − 2q`. For the other characters we prove the **key
identity**

  `Σ_{n ≤ N} χ(n) log n / n = Σ_{d ≤ N} χ(d) Λ(d)/d · Σ_{m ≤ N/d} χ(m)/m`,

which is `log n = Σ_{d ∣ n} Λ(d)` summed against `χ(n)/n` (with `χ(dm) = χ(d)χ(m)`). The left
side is bounded (file `LFunction`); on the right the inner sums are `L(1, χ)` up to an error
`2q d/N`, and `Σ Λ(d)/d · 2qd/N = 2q ψ(N)/N` is bounded by Chebyshev. Hence

  `|L(1, χ) · S_χ(N)| ≤ 4 + 2q + 2q log 1024`,

so **if `L(1, χ) ≠ 0` then `S_χ(N)` stays bounded** — the analytic heart of the argument,
which reduces Dirichlet's theorem to the non-vanishing of `L(1, χ)`.
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Numbers Foundations.Numbers.Arith Lean.Grind
open Foundations.Numbers.C (ofReal)

attribute [local instance] Classical.propDecidable

variable {q : Nat} [NeZero q]

/-- The **twisted Chebyshev sum** `S_χ(N) = Σ_{n ≤ N} χ(n) Λ(n)/n`. -/
noncomputable def chebSum (χ : Character (ZModUnits q)) (N : Nat) : C :=
  gsum (fun n => dchar χ n * ofReal (vonMangoldt n / (n : R))) (N + 1)

/-- `x / 0 = 0` in `R`. -/
theorem div_natCast_zero (x : R) : x / ((0 : Nat) : R) = 0 := by
  rw [show ((0 : Nat) : R) = 0 by grind, Field.div_eq_mul_inv, Field.inv_zero]; grind

/-- **The key identity.** `Σ_{n ≤ N} χ(n) log n / n = Σ_{d ≤ N} χ(d) Λ(d)/d · Σ_{m ≤ N/d} χ(m)/m`. -/
theorem key_identity (χ : Character (ZModUnits q)) (N : Nat) :
    gsum (fun n => dchar χ n * ofReal (lnat n / (n : R))) (N + 1) =
      gsum (fun d => dchar χ d * ofReal (vonMangoldt d / (d : R)) * lpart (dchar χ) (N / d + 1))
        (N + 1) := by
  let F : Nat → Nat → C := fun d m =>
    dchar χ d * ofReal (vonMangoldt d / (d : R)) * (dchar χ m * ofReal (1 / (m : R)))
  have h0 : ∀ m, F 0 m = 0 := fun m => by
    show dchar χ 0 * ofReal (vonMangoldt 0 / ((0 : Nat) : R)) * _ = 0
    rw [div_natCast_zero, ofReal_zero']; grind
  have h0' : ∀ d, F d 0 = 0 := fun d => by
    show _ * (dchar χ 0 * ofReal (1 / ((0 : Nat) : R))) = 0
    rw [div_natCast_zero, ofReal_zero']; grind
  have e1 : ∀ n, n < N + 1 → dchar χ n * ofReal (lnat n / (n : R)) =
      gsum (fun d => if d ∣ n then F d (n / d) else 0) (n + 1) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [gsum_succ, gsum_nil, ite_eq_left (Nat.dvd_zero 0), h0, div_natCast_zero, ofReal_zero']
      grind
    · have e2 : ∀ d, d < n + 1 → (if d ∣ n then F d (n / d) else 0) =
          dchar χ n * ofReal ((if d ∣ n then vonMangoldt d else 0) / (n : R)) := by
        intro d _
        by_cases hd : d ∣ n
        · rw [ite_eq_left hd, ite_eq_left hd]
          obtain ⟨m, hm⟩ := hd
          have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
          have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
          have hnd : n / d = m := by rw [hm, Nat.mul_div_cancel_left m hd0]
          show dchar χ d * ofReal (vonMangoldt d / (d : R)) *
            (dchar χ (n / d) * ofReal (1 / ((n / d : Nat) : R))) = _
          rw [hnd, hm, dchar_mul]
          have hdR : (d : R) ≠ 0 := by have := natCast_pos' hd0; grind
          have hmR : (m : R) ≠ 0 := by have := natCast_pos' hm0; grind
          have : vonMangoldt d / ((d * m : Nat) : R) = vonMangoldt d / (d : R) * (1 / (m : R)) := by
            rw [show ((d * m : Nat) : R) = (d : R) * (m : R) by grind]; grind
          rw [this, ofReal_mul']; grind
        · rw [ite_eq_right hd, ite_eq_right hd,
            show (0 : R) / (n : R) = 0 by rw [Field.div_eq_mul_inv]; grind, ofReal_zero']
          grind
      rw [gsum_congr e2, gsum_mul_left, ← ofReal_gsum]
      congr 2
      rw [show (fun d => (if d ∣ n then vonMangoldt d else 0) / (n : R)) =
        fun d => (if d ∣ n then vonMangoldt d else 0) * (1 / (n : R)) from funext fun d => by grind,
        gsum_mul_right]
      have := dsum_vonMangoldt n
      unfold dsum at this; rw [this]; grind
  rw [gsum_congr e1, gsum_divisors_eq F h0 h0' N]
  apply gsum_congr; intro d _
  unfold lpart
  rw [← gsum_mul_left]

/-- `1/(d (⌊N/d⌋ + 1)) ≤ 1/N`, as used for the error terms. -/
theorem one_div_mul_le {N d : Nat} (hN : 0 < N) (hd : 0 < d) :
    1 / (d : R) * (1 / (((N / d + 1 : Nat)) : R)) ≤ 1 / (N : R) := by
  have h1 := natCast_pos' hd
  have h2 := natCast_pos' (Nat.succ_pos (N / d))
  have h3 := natCast_pos' hN
  have hle : (N : R) ≤ (d : R) * ((N / d + 1 : Nat) : R) := by
    have := div_le_natDiv_add_one N hd
    have := OrderedRing.mul_le_mul_of_nonneg_left this (Std.le_of_lt h1)
    have hdne : (d : R) ≠ 0 := by grind
    rw [show (d : R) * ((N : R) / (d : R)) = (N : R) by grind] at this
    rw [show ((N / d + 1 : Nat) : R) = ((N / d : Nat) : R) + 1 by grind]; exact this
  rw [show 1 / (d : R) * (1 / ((N / d + 1 : Nat) : R)) = 1 / ((d : R) * ((N / d + 1 : Nat) : R)) by
    have : (d : R) ≠ 0 := by grind
    have : ((N / d + 1 : Nat) : R) ≠ 0 := by grind
    grind]
  apply le_div_of_mul_le h3
  rw [show 1 / ((d : R) * ((N / d + 1 : Nat) : R)) * (N : R) =
    (N : R) / ((d : R) * ((N / d + 1 : Nat) : R)) by grind]
  apply div_le_of_le_mul (OrderedRing.mul_pos h1 h2)
  grind

/-- **The key estimate.** For non-principal `χ` and `N ≥ 1`:
`|L(1, χ) · S_χ(N)| ≤ 4 + 2q + 2q log 1024`. -/
theorem cabs_Lone_mul_chebSum_le (χ : Character (ZModUnits q)) (hχ : χ ≠ Character.one)
    {N : Nat} (hN : 0 < N) :
    C.cabs (Lone χ * chebSum χ N) ≤ 4 + 2 * (q : R) + 2 * (q : R) * chebC := by
  obtain ⟨_, htail⟩ := Lone_spec χ hχ
  let c : Nat → C := fun d => dchar χ d * ofReal (vonMangoldt d / (d : R))
  let T : Nat → C := fun d => Lone χ - lpart (dchar χ) (N / d + 1)
  have hkey := key_identity χ N
  have e : Lone χ * chebSum χ N =
      gsum (fun n => dchar χ n * ofReal (lnat n / (n : R))) (N + 1) +
        gsum (fun d => c d * T d) (N + 1) := by
    rw [hkey]; unfold chebSum
    rw [← gsum_add, ← gsum_mul_left]; apply gsum_congr; intro d _
    show _ = c d * lpart (dchar χ) (N / d + 1) + c d * (Lone χ - lpart (dchar χ) (N / d + 1))
    show Lone χ * (dchar χ d * ofReal (vonMangoldt d / (d : R))) = _
    grind
  rw [e]
  have h1 := cabs_gsum_log_le (cabs_gsum_dchar_le χ hχ) (cabs_dchar_le χ) (N + 1)
  have h2 : C.cabs (gsum (fun d => c d * T d) (N + 1)) ≤
      gsum (fun d => 2 * (q : R) * (vonMangoldt d * (1 / (N : R)))) (N + 1) := by
    apply Std.le_trans (cabs_gsum_le _ _)
    apply gsum_le_gsum; intro d _
    rw [C.cabs_mul]
    have hΛ := vonMangoldt_nonneg d
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      show C.cabs (dchar χ 0 * ofReal (vonMangoldt 0 / ((0 : Nat) : R))) * _ ≤ _
      rw [div_natCast_zero, ofReal_zero', show dchar χ 0 * (0 : C) = 0 by grind, C.cabs_zero,
        vonMangoldt_zero]; grind
    · have hc : C.cabs (c d) ≤ vonMangoldt d * (1 / (d : R)) := by
        show C.cabs (dchar χ d * ofReal (vonMangoldt d / (d : R))) ≤ _
        have hnn : 0 ≤ vonMangoldt d / (d : R) := by
          have := div_le_div_of_le hΛ (natCast_pos' hd)
          rw [show (0 : R) / (d : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this; exact this
        rw [cabs_mul_ofReal hnn]
        have := OrderedRing.mul_le_mul_of_nonneg_right (cabs_dchar_le χ d) hnn
        grind
      have hT : C.cabs (T d) ≤ 2 * (q : R) / ((N / d + 1 : Nat) : R) := htail _ (Nat.succ_pos _)
      have hTn : 0 ≤ C.cabs (T d) := C.cabs_nonneg _
      have hcn : 0 ≤ C.cabs (c d) := C.cabs_nonneg _
      have h3 := OrderedRing.mul_le_mul_of_nonneg_right hc hTn
      have h4 := OrderedRing.mul_le_mul_of_nonneg_left hT
        (OrderedRing.mul_nonneg hΛ (one_div_nonneg' d))
      have h5 := one_div_mul_le hN hd
      have h6 := OrderedRing.mul_le_mul_of_nonneg_left h5
        (show 0 ≤ 2 * (q : R) * vonMangoldt d by
          have := natCast_le' (Nat.zero_le q); have := OrderedRing.mul_nonneg
            (show (0 : R) ≤ 2 * (q : R) by grind) hΛ; grind)
      have e2 : vonMangoldt d * (1 / (d : R)) * (2 * (q : R) / ((N / d + 1 : Nat) : R)) =
          2 * (q : R) * vonMangoldt d * (1 / (d : R) * (1 / ((N / d + 1 : Nat) : R))) := by grind
      grind
  rw [gsum_mul_left, gsum_mul_right] at h2
  have h3 := psi_le hN
  have h4 : gsum vonMangoldt (N + 1) * (1 / (N : R)) ≤ chebC := by
    have hNp := natCast_pos' hN
    have h7 := div_le_div_of_le h3 hNp
    have : (N : R) ≠ 0 := by grind
    rw [show (N : R) * chebC / (N : R) = chebC by grind] at h7
    grind
  have h5 := OrderedRing.mul_le_mul_of_nonneg_left h4
    (show (0 : R) ≤ 2 * (q : R) by have := natCast_le' (Nat.zero_le q); grind)
  have h6 := C.cabs_add (gsum (fun n => dchar χ n * ofReal (lnat n / (n : R))) (N + 1))
    (gsum (fun d => c d * T d) (N + 1))
  grind

/-- **Non-vanishing implies bounded twisted sums.** If `L(1, χ) ≠ 0` for a non-principal `χ`,
then `S_χ(N)` is bounded. -/
theorem chebSum_bounded (χ : Character (ZModUnits q)) (hχ : χ ≠ Character.one)
    (hL : Lone χ ≠ 0) : ∃ B : R, ∀ N, 0 < N → C.cabs (chebSum χ N) ≤ B := by
  have hpos := C.cabs_pos hL
  refine ⟨(4 + 2 * (q : R) + 2 * (q : R) * chebC) / C.cabs (Lone χ), fun N hN => ?_⟩
  have := cabs_Lone_mul_chebSum_le χ hχ hN
  rw [C.cabs_mul] at this
  apply le_div_of_mul_le hpos
  grind

/-! ## The principal character -/

/-- `S_{χ₀}(N) = Σ_{n ≤ N, gcd(n, q) = 1} Λ(n)/n`. -/
theorem chebSum_one (N : Nat) :
    chebSum (Character.one : Character (ZModUnits q)) N =
      ofReal (gsum (fun n => if Nat.Coprime n q then vonMangoldt n / (n : R) else 0) (N + 1)) := by
  unfold chebSum; rw [ofReal_gsum]; apply gsum_congr; intro n _
  rw [dchar_one_char]
  by_cases h : Nat.Coprime n q
  · rw [ite_eq_left h, ite_eq_left h]; grind
  · rw [ite_eq_right h, ite_eq_right h, ofReal_zero']; grind

/-- **Mertens' estimate for the principal character.**
`Σ_{n ≤ N, gcd(n, q) = 1} Λ(n)/n ≥ log N − 1 − 2q`. -/
theorem principal_lower {N : Nat} (hN : 0 < N) :
    lnat N - 1 - 2 * (q : R) ≤
      gsum (fun n => if Nat.Coprime n q then vonMangoldt n / (n : R) else 0) (N + 1) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hM := mertens_lower hN
  have split : gsum (fun d => vonMangoldt d / (d : R)) (N + 1) =
      gsum (fun n => if Nat.Coprime n q then vonMangoldt n / (n : R) else 0) (N + 1) +
        gsum (fun n => vonMangoldt n * (if Nat.Coprime n q then 0 else 1 / (n : R))) (N + 1) := by
    rw [← gsum_add]; apply gsum_congr; intro n _
    by_cases h : Nat.Coprime n q
    · rw [ite_eq_left h, ite_eq_left h]; grind
    · rw [ite_eq_right h, ite_eq_right h]; grind
  have hE : gsum (fun n => vonMangoldt n * (if Nat.Coprime n q then 0 else 1 / (n : R))) (N + 1) ≤
      2 * (q : R) := by
    rw [gsum_vonMangoldt_mul]
    apply Std.le_trans _ (prime_dvd_sum_le hq N)
    apply gsum_le_gsum; intro p _; apply gsum_le_gsum; intro k _
    by_cases h : Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N
    · rw [ite_eq_left h]
      by_cases hc : Nat.Coprime (p ^ k) q
      · rw [ite_eq_left hc]
        have : 0 ≤ (if (Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N) ∧ p ∣ q then lnat p / ((p ^ k : Nat) : R)
            else 0) := by
          split
          · have := div_le_div_of_le (lnat_nonneg p) (natCast_pos' (Nat.pow_pos (n := k)
              (show 0 < p by have := h.1.1; omega)))
            rw [show (0 : R) / ((p ^ k : Nat) : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this
            exact this
          · grind
        grind
      · rw [ite_eq_right hc]
        have hpq : p ∣ q := by
          apply Classical.byContradiction; intro hpq
          apply hc
          have : Nat.Coprime p q := by
            rcases h.1.2 _ (Nat.gcd_dvd_left p q) with h1 | h1
            · exact h1
            · exact absurd (h1 ▸ Nat.gcd_dvd_right p q) hpq
          exact Nat.Coprime.pow_left k this
        rw [ite_eq_left ⟨h, hpq⟩]; grind
    · rw [ite_eq_right h]
      split
      · next h' => exact absurd h'.1 h
      · grind
  grind

omit [NeZero q] in
/-- **Mertens' upper estimate for the principal character.**
`Σ_{n ≤ N, gcd(n, q) = 1} Λ(n)/n ≤ log N + log 1024`. -/
theorem principal_upper {N : Nat} (hN : 0 < N) :
    gsum (fun n => if Nat.Coprime n q then vonMangoldt n / (n : R) else 0) (N + 1) ≤
      lnat N + chebC := by
  apply Std.le_trans _ (mertens_upper hN)
  apply gsum_le_gsum; intro n _
  split
  · grind
  · rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [div_natCast_zero]; grind
    · have := div_le_div_of_le (vonMangoldt_nonneg n) (natCast_pos' h)
      rw [show (0 : R) / (n : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this; exact this

/-! ## The sieve -/

/-- **Dirichlet's sieve applied to the twisted sums.** For `a` coprime to `q`,
`Σ_χ conj χ(a) · S_χ(N) = φ(q) · Σ_{n ≤ N, n ≡ a (q)} Λ(n)/n`. -/
theorem sum_conj_mul_chebSum (a : Nat) (ha : Nat.Coprime a q) (N : Nat) :
    sumOver (fun χ : Character (ZModUnits q) => C.conj (dchar χ a) * chebSum χ N) =
      ofReal ((totient q : R) *
        gsum (fun n => if n % q = a % q then vonMangoldt n / (n : R) else 0) (N + 1)) := by
  unfold sumOver chebSum
  rw [lsum_congr (g := fun χ => gsum (fun n => C.conj (dchar χ a) *
    (dchar χ n * ofReal (vonMangoldt n / (n : R)))) (N + 1)) (fun χ _ => (gsum_mul_left _ _ _).symm),
    lsum_gsum, ← gsum_mul_left, ofReal_gsum]
  apply gsum_congr; intro n _
  rw [lsum_congr (g := fun χ => (C.conj (dchar χ a) * dchar χ n) * ofReal (vonMangoldt n / (n : R)))
    (fun χ _ => by grind)]
  have := sum_conj_dchar_mul a ha n
  unfold sumOver at this
  rw [show (fun χ : Character (ZModUnits q) => (C.conj (dchar χ a) * dchar χ n) *
    ofReal (vonMangoldt n / (n : R))) = fun χ => ofReal (vonMangoldt n / (n : R)) *
    (C.conj (dchar χ a) * dchar χ n) from funext fun χ => by grind, lsum_mul_left, this]
  by_cases h : n % q = a % q
  · rw [ite_eq_left h, ite_eq_left h, ofReal_mul']
    have : ofReal (totient q : R) = ((totient q : Nat) : C) := C.ext rfl rfl
    rw [this]; grind
  · rw [ite_eq_right h, ite_eq_right h, ofReal_mul', ofReal_zero']; grind

end Foundations.NumberTheory
