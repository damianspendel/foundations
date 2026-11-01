import Foundations.NumberTheory.ArithmeticFunctions

/-!
# Chebyshev's `ψ` and Mertens' estimate `Σ_{n ≤ N} Λ(n)/n = log N + O(1)`

Euler (1737) proved that `Σ 1/p` diverges — the analytic form of the infinitude of primes.
Mertens (1874) made this quantitative: `Σ_{p ≤ x} log p / p = log x + O(1)`. The weighted form
with the von Mangoldt function,

  `log N − 1 ≤ Σ_{n ≤ N} Λ(n)/n ≤ log N + log 1024`,

is proved here by the classical route through `log N!`:

1. `Σ_{d ∣ n} Λ(d) = log n` (unique factorisation, via `log n = Σ_p vₚ(n) log p`);
2. summing over `n ≤ N` and counting multiples: `log N! = Σ_{d ≤ N} Λ(d) ⌊N/d⌋`
   (Chebyshev's identity, a weighted Legendre formula);
3. `N log N − N ≤ log N! ≤ N log N` (from `Nᴺ/N! ≤ eᴺ`, a single term of the exponential series);
4. **Chebyshev's bound** `ψ(N) = Σ_{n ≤ N} Λ(n) ≤ π(N) log N ≤ N log 1024`, from the upper bound
   of the previous file `Chebyshev`.

Replacing `⌊N/d⌋` by `N/d` costs at most `ψ(N)`, which gives both bounds. In particular
`Σ_{n ≤ N} Λ(n)/n → ∞`: this is the case `q = 1` of Dirichlet's theorem in Mertens' form, and
the model for the general case, where the sum is restricted to `n ≡ a (mod q)`.

We also bound two error terms needed later: the contribution of the prime powers `pᵏ` with
`k ≥ 2` (at most `4`), and that of the primes dividing a fixed `q` (at most `2q`).
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-! ## Real inequalities used repeatedly -/

/-- Non-negative summands give a non-negative sum. -/
theorem gsum_nonneg {f : Nat → R} (h : ∀ k, 0 ≤ f k) (n : Nat) : 0 ≤ gsum f n := by
  induction n with
  | zero => show (0 : R) ≤ 0; grind
  | succ n ih => rw [gsum_succ]; have := h n; grind

/-- Sums are monotone in the summands. -/
theorem gsum_le_gsum {f g : Nat → R} {n : Nat} (h : ∀ k, k < n → f k ≤ g k) : gsum f n ≤ gsum g n := by
  induction n with
  | zero => show (0 : R) ≤ 0; grind
  | succ n ih => rw [gsum_succ, gsum_succ]; have := ih fun k hk => h k (by omega); have := h n (by omega); grind

/-- The sum of a constant. -/
theorem gsum_const_R (c : R) (n : Nat) : gsum (fun _ => c) n = (n : R) * c := by
  induction n with
  | zero => show (0 : R) = ((0 : Nat) : R) * c; grind
  | succ n ih => rw [gsum_succ, ih]; grind

/-- Partial sums of non-negative terms increase. -/
theorem gsum_mono_of_nonneg {f : Nat → R} (h : ∀ k, 0 ≤ f k) {m n : Nat} (hmn : m ≤ n) :
    gsum f m ≤ gsum f n := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [gsum_split]; have := gsum_nonneg (fun k => h (m + k)) c; grind

/-- Dividing an inequality by a positive number. -/
theorem div_le_div_of_le {a b c : R} (hab : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  have hc' : c ≠ 0 := by grind
  have hinv : 0 < c⁻¹ := by
    have := OrderedRing.mul_pos hc hc
    rcases (by grind : c⁻¹ ≤ 0 ∨ 0 < c⁻¹) with h | h
    · have := OrderedRing.mul_le_mul_of_nonneg_left h (Std.le_of_lt hc)
      rw [Field.mul_inv_cancel hc'] at this; grind
    · exact h
  have := OrderedRing.mul_le_mul_of_nonneg_right hab (Std.le_of_lt hinv)
  rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; exact this

/-- `x c ≤ y` with `c > 0` gives `x ≤ y / c`. -/
theorem le_div_of_mul_le {x y c : R} (hc : 0 < c) (h : x * c ≤ y) : x ≤ y / c := by
  have := div_le_div_of_le h hc
  have hc' : c ≠ 0 := by grind
  rw [show x * c / c = x by grind] at this; exact this

/-- `y ≤ x c` with `c > 0` gives `y / c ≤ x`. -/
theorem div_le_of_le_mul {x y c : R} (hc : 0 < c) (h : y ≤ x * c) : y / c ≤ x := by
  have := div_le_div_of_le h hc
  have hc' : c ≠ 0 := by grind
  rw [show x * c / c = x by grind] at this; exact this

/-- From `0 < c` and `0 ≤ c a`, conclude `0 ≤ a`. -/
theorem nonneg_of_mul_nonneg_left' {a c : R} (hc : 0 < c) (h : 0 ≤ c * a) : 0 ≤ a := by
  rcases (by grind : a < 0 ∨ 0 ≤ a) with ha | ha
  · have := OrderedRing.mul_lt_mul_of_pos_left ha hc; grind
  · exact ha

/-- `log y ≤ y − 1` for `y ≥ 1` (from `1 + x ≤ eˣ`). -/
theorem log_le_sub_one {y : R} (hy : 1 ≤ y) : R.log y ≤ y - 1 := by
  have h := R.one_add_le_exp (x := y - 1) (by grind)
  have := log_le_log (by grind) (show y ≤ R.exp (y - 1) by grind)
  rw [R.log_exp] at this; exact this

/-- `⌊N/d⌋ ≤ N/d`. -/
theorem natDiv_le (N : Nat) {d : Nat} (hd : 0 < d) : ((N / d : Nat) : R) ≤ (N : R) / (d : R) := by
  apply le_div_of_mul_le (natCast_pos' hd)
  have := natCast_le' (Nat.div_mul_le_self N d)
  rw [show (((N / d) * d : Nat) : R) = ((N / d : Nat) : R) * (d : R) by grind] at this; exact this

/-- `N/d ≤ ⌊N/d⌋ + 1`. -/
theorem div_le_natDiv_add_one (N : Nat) {d : Nat} (hd : 0 < d) :
    (N : R) / (d : R) ≤ ((N / d : Nat) : R) + 1 := by
  apply div_le_of_le_mul (natCast_pos' hd)
  have h : N ≤ (N / d + 1) * d := by
    have := Nat.lt_div_mul_add (a := N) hd
    rw [Nat.add_mul, Nat.one_mul]; omega
  have := natCast_le' h
  rw [show (((N / d + 1) * d : Nat) : R) = (((N / d : Nat) : R) + 1) * (d : R) by grind] at this
  exact this

/-- `log` is monotone on the positive integers. -/
theorem lnat_le_lnat {m n : Nat} (hm : 0 < m) (h : m ≤ n) : lnat m ≤ lnat n := by
  unfold lnat
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact log_le_log (natCast_pos' hm) (natCast_le' h)

/-- `log n ≤ n − 1`. -/
theorem lnat_le (n : Nat) : lnat n ≤ (n : R) - 1 + (if n = 0 then 1 else 0) := by
  unfold lnat
  split
  · next h => subst h; show (0 : R) ≤ ((0 : Nat) : R) - 1 + 1; grind
  · next h =>
    have := log_le_sub_one (y := (n : R)) (by have := natCast_le' (show 1 ≤ n by omega); grind)
    grind

/-! ## `Σ_{d ∣ n} Λ(d) = log n` -/

/-- For primes `r`, `p`: `v_r(p) = 1` if `r = p` and `0` otherwise. -/
theorem vp_prime {r p : Nat} (hr : Prime r) (hp : Prime p) : vp r p = if r = p then 1 else 0 := by
  split
  · next h => subst h; exact vp_eq (r := 1) hr.1 (by simp) (fun h => by
      have := Nat.le_of_dvd (by omega) h; have := hr.1; omega)
  · next h =>
    exact vp_eq (r := p) hr.1 (by simp) (fun hd => by
      rcases hp.2 r hd with h1 | h1
      · have := hr.1; omega
      · exact h h1)

/-- **Unique factorisation, additively.** `log n = Σ_{p ≤ n prime} vₚ(n) log p` for `n ≥ 1`. -/
theorem sum_vp_lnat : ∀ n : Nat, 0 < n →
    gsum (fun r => if Prime r then (vp r n : R) * lnat r else 0) (n + 1) = lnat n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1
      rw [lnat_one]
      apply (gsum_congr (g := fun _ => 0) (fun r _ => ?_)).trans (gsum_zero' _)
      split
      · next hr => rw [vp_one hr.1]; grind
      · rfl
    · obtain ⟨p, hp, m, rfl⟩ := exists_prime_dvd (show 2 ≤ n by omega)
      have hp2 : 2 ≤ p := hp.1
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hmlt : m < p * m := by
        have : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp2
        omega
      rw [lnat_mul (by omega) hm, ← ih m hmlt hm]
      have e : ∀ r, (if Prime r then (vp r (p * m) : R) * lnat r else 0) =
          (if r = p then lnat p else 0) + (if Prime r then (vp r m : R) * lnat r else 0) := by
        intro r
        by_cases hr : Prime r
        · rw [ite_eq_left hr, ite_eq_left hr, vp_mul hr (by omega) hm, vp_prime hr hp]
          by_cases hrp : r = p
          · subst hrp; rw [ite_eq_left rfl, ite_eq_left rfl]; grind
          · rw [ite_eq_right hrp, ite_eq_right hrp]; grind
        · rw [ite_eq_right hr, ite_eq_right hr, ite_eq_right (fun h => hr (by rw [h]; exact hp))]; grind
      rw [gsum_congr (fun r _ => e r), gsum_add, gsum_ite_eq,
        ite_eq_left (by have := Nat.le_mul_of_pos_right p hm; omega)]
      congr 1
      apply gsum_extend (by omega)
      intro r hr _
      split
      · next hpr =>
        have : vp r m = 0 := by
          apply Classical.byContradiction; intro h0
          have := (pow_dvd_iff_le_vp hpr.1 hm).2 (show 1 ≤ vp r m by omega)
          rw [Nat.pow_one] at this
          have := Nat.le_of_dvd hm this; omega
        rw [this]; grind
      · rfl

/-- Counting `k` with `1 ≤ k ≤ v` among `k < j`, for `j ≤ v + 1`. -/
theorem gsum_count_le_aux (v : Nat) : ∀ j, j ≤ v + 1 →
    gsum (fun k => if 1 ≤ k ∧ k ≤ v then (1 : R) else 0) j = if j = 0 then 0 else (j : R) - 1
  | 0, _ => rfl
  | j + 1, h => by
    rw [gsum_succ, gsum_count_le_aux v j (by omega), ite_eq_right (show ¬ (j + 1 = 0) by omega)]
    by_cases hj : j = 0
    · subst hj; rw [ite_eq_left rfl, ite_eq_right (show ¬ (1 ≤ 0 ∧ 0 ≤ v) by omega)]; grind
    · rw [ite_eq_right hj, ite_eq_left (show 1 ≤ j ∧ j ≤ v by omega)]; grind

/-- `#{k : 1 ≤ k ≤ v} = v` (counted among `k < B`, for `v < B`). -/
theorem gsum_count_le (v : Nat) (B : Nat) (h : v < B) :
    gsum (fun k => if 1 ≤ k ∧ k ≤ v then (1 : R) else 0) B = (v : R) := by
  rw [gsum_extend (A := v + 1) (by omega) (fun k hk _ => ite_eq_right (by omega)),
    gsum_count_le_aux v (v + 1) (Nat.le_refl _), ite_eq_right (by omega)]
  grind

/-- `Λ(0) = 0`. -/
theorem vonMangoldt_zero : vonMangoldt 0 = 0 := by
  unfold vonMangoldt
  rw [gsum_succ, gsum_nil, gsum_succ, gsum_nil, ite_eq_right (fun h => by have := h.1.1; omega)]
  grind

/-- **`Σ_{d ∣ n} Λ(d) = log n`** for every `n` (both sides vanish at `n = 0`). -/
theorem dsum_vonMangoldt (n : Nat) : dsum vonMangoldt n = lnat n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; unfold dsum lnat
    rw [gsum_succ, gsum_nil, ite_eq_left (Nat.dvd_zero 0), vonMangoldt_zero]; grind
  unfold dsum
  have e0 : ∀ d, (if d ∣ n then vonMangoldt d else 0) =
      vonMangoldt d * (if d ∣ n then 1 else 0) := fun d => by split <;> grind
  rw [gsum_congr (fun d _ => e0 d), gsum_vonMangoldt_mul, ← sum_vp_lnat n hn]
  apply gsum_congr; intro p _
  by_cases hp : Prime p
  · rw [ite_eq_left hp]
    have hvn : vp p n < n + 1 := by
      have := (pow_dvd_iff_le_vp hp.1 hn).2 (Nat.le_refl (vp p n))
      have h1 := Nat.le_of_dvd hn this
      have h2 := Nat.lt_pow_self (n := vp p n) hp.1
      omega
    rw [← gsum_count_le (vp p n) (n + 1) hvn, ← gsum_mul_right]
    apply gsum_congr; intro k _
    by_cases hk : 1 ≤ k ∧ k ≤ vp p n
    · have hdvd := (pow_dvd_iff_le_vp hp.1 hn).2 hk.2
      rw [ite_eq_left ⟨hp, hk.1, Nat.le_of_dvd hn hdvd⟩, ite_eq_left hdvd, ite_eq_left hk]; grind
    · rw [ite_eq_right hk]
      by_cases h2 : Prime p ∧ 1 ≤ k ∧ p ^ k ≤ n
      · rw [ite_eq_left h2, ite_eq_right (fun hd => hk ⟨h2.2.1, (pow_dvd_iff_le_vp hp.1 hn).1 hd⟩)]
        grind
      · rw [ite_eq_right h2]; grind
  · rw [ite_eq_right hp]
    exact (gsum_congr (g := fun _ => 0) (fun k _ => ite_eq_right (fun h => hp h.1))).trans
      (gsum_zero' _)

/-! ## Chebyshev's identity for `log N!` -/

/-- `log N! = Σ_{n ≤ N} log n`. -/
theorem lnat_fact (N : Nat) : lnat (R.fact N) = gsum lnat (N + 1) := by
  induction N with
  | zero => show lnat 1 = 0 + lnat 0; rw [lnat_one]; unfold lnat; grind
  | succ N ih =>
    rw [gsum_succ, ← ih]
    show lnat ((N + 1) * R.fact N) = _
    rw [lnat_mul (by omega) (R.fact_pos N)]; grind

/-- `Σ_{1 ≤ m ≤ K} c = K c`. -/
theorem gsum_ite_one_le (c : R) (K : Nat) : gsum (fun m => if 1 ≤ m then c else 0) (K + 1) = (K : R) * c := by
  induction K with
  | zero => rw [gsum_succ, gsum_nil, ite_eq_right (by omega)]; grind
  | succ K ih => rw [gsum_succ, ih, ite_eq_left (by omega)]; grind

/-- **Chebyshev's identity.** `log N! = Σ_{d ≤ N} Λ(d) ⌊N/d⌋`. -/
theorem lnat_fact_eq (N : Nat) :
    lnat (R.fact N) = gsum (fun d => vonMangoldt d * ((N / d : Nat) : R)) (N + 1) := by
  rw [lnat_fact]
  let F : Nat → Nat → R := fun d m => if 1 ≤ m then vonMangoldt d else 0
  have e1 : ∀ n, n < N + 1 → lnat n =
      gsum (fun d => if d ∣ n then F d (n / d) else 0) (n + 1) := by
    intro n _
    rw [← dsum_vonMangoldt]; unfold dsum
    apply gsum_congr; intro d _
    by_cases hd : d ∣ n
    · rw [ite_eq_left hd, ite_eq_left hd]
      show vonMangoldt d = if 1 ≤ n / d then vonMangoldt d else 0
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have : d = 0 := by rcases Nat.eq_zero_or_pos d with h | h; exact h; omega
        subst this; rw [vonMangoldt_zero]; grind
      · have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
        rw [ite_eq_left (show 1 ≤ n / d from Nat.div_pos (Nat.le_of_dvd hn hd) hd0)]
    · rw [ite_eq_right hd, ite_eq_right hd]
  rw [gsum_congr e1, gsum_divisors_eq F (fun m => by show (if 1 ≤ m then _ else _) = _; rw [vonMangoldt_zero]; grind)
    (fun d => ite_eq_right (by omega))]
  apply gsum_congr; intro d _
  rw [gsum_ite_one_le]; grind

/-- `log N! ≤ N log N`. -/
theorem lnat_fact_le (N : Nat) : lnat (R.fact N) ≤ (N : R) * lnat N := by
  rw [lnat_fact, gsum_succ', show lnat 0 = 0 by unfold lnat; grind]
  have := gsum_le_gsum (n := N) (f := fun k => lnat (k + 1)) (g := fun _ => lnat N)
    (fun k hk => lnat_le_lnat (by omega) (by omega))
  rw [gsum_const_R] at this; grind

/-- `N log N − N ≤ log N!`, from `Nᴺ / N! ≤ eᴺ` (one term of the exponential series). -/
theorem lnat_fact_ge {N : Nat} (hN : 0 < N) : (N : R) * lnat N - N ≤ lnat (R.fact N) := by
  have hx : (0 : R) < (N : R) := natCast_pos' hN
  have hF : (0 : R) < (R.fact N : R) := natCast_pos' (R.fact_pos N)
  have h1 : R.expTerm (N : R) N ≤ R.exp (N : R) := by
    have h2 := R.fsum_le_of_hasSum (R.expTerm_nonneg (Std.le_of_lt hx)) (R.hasSum_exp (N : R)) (N + 1)
    rw [R.fsum_succ] at h2
    have := R.fsum_nonneg (R.expTerm_nonneg (Std.le_of_lt hx)) N
    grind
  have h3 : (N : R) ^ N ≤ R.exp (N : R) * (R.fact N : R) := by
    unfold R.expTerm at h1
    have := OrderedRing.mul_le_mul_of_nonneg_right h1 (Std.le_of_lt hF)
    have hF' : (R.fact N : R) ≠ 0 := by grind
    rw [show (N : R) ^ N / (R.fact N : R) * (R.fact N : R) = (N : R) ^ N by grind] at this
    exact this
  obtain ⟨hpow, hlog⟩ := pow_pos_and_log_pow hx N
  have h4 := log_le_log hpow h3
  rw [hlog, R.log_mul (R.exp_pos _) hF, R.log_exp] at h4
  unfold lnat
  rw [ite_eq_right (by omega), ite_eq_right (Nat.pos_iff_ne_zero.1 (R.fact_pos N))]
  grind

/-! ## Chebyshev's bound for `ψ` -/

/-- The constant `log 1024 = 10 log 2` of Chebyshev's upper bound. -/
noncomputable def chebC : R := R.log ((1024 : Nat) : R)

/-- `log 1024 ≥ 0`. -/
theorem chebC_nonneg : 0 ≤ chebC := by
  have := lnat_nonneg 1024; unfold lnat at this; rw [ite_eq_right (by omega)] at this; exact this

/-- For a prime `p` and `N ≥ 1`: `Σ_{k ≥ 1, pᵏ ≤ N} log p ≤ log N`. -/
theorem gsum_prime_pow_le {p N : Nat} (hp : Prime p) (M : Nat) :
    gsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then lnat p * 1 else 0) (M + 1) ≤ lnat N := by
  have hp0 : 0 < p := by have := hp.1; omega
  have key : ∀ M, (p ^ M ≤ N → gsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then lnat p * 1
      else 0) (M + 1) = (M : R) * lnat p) ∧
      gsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then lnat p * 1 else 0) (M + 1) ≤ lnat N := by
    intro M
    induction M with
    | zero =>
      rw [gsum_succ, gsum_nil, ite_eq_right (by omega)]
      exact ⟨fun _ => by grind, by have := lnat_nonneg N; grind⟩
    | succ M ih =>
      rw [gsum_succ]
      by_cases h : p ^ (M + 1) ≤ N
      · have hM : p ^ M ≤ N := Nat.le_trans (Nat.pow_le_pow_right hp0 (by omega)) h
        rw [ite_eq_left ⟨hp, by omega, h⟩, ih.1 hM]
        have := lnat_le_lnat (Nat.pow_pos hp0) h
        rw [lnat_pow hp0] at this
        exact ⟨fun _ => by grind, by grind⟩
      · rw [ite_eq_right (fun h' => h h'.2.2)]
        exact ⟨fun h' => absurd h' h, by have := ih.2; grind⟩
  exact (key M).2

/-- `Σ_{p ≤ N prime} c = π(N) c`. -/
theorem gsum_ite_prime (c : R) : ∀ B : Nat,
    gsum (fun p => if Prime p then c else 0) B = (countBelow Prime B : R) * c
  | 0 => by show (0 : R) = ((0 : Nat) : R) * c; grind
  | B + 1 => by
    rw [gsum_succ, gsum_ite_prime c B]
    show _ = ((countBelow Prime B + if Prime B then 1 else 0 : Nat) : R) * c
    by_cases h : Prime B
    · rw [ite_eq_left h, ite_eq_left h]; grind
    · rw [ite_eq_right h, ite_eq_right h]; grind

/-- **Chebyshev's bound.** `ψ(N) = Σ_{n ≤ N} Λ(n) ≤ N log 1024`. -/
theorem psi_le {N : Nat} (hN : 0 < N) : gsum vonMangoldt (N + 1) ≤ (N : R) * chebC := by
  have e : gsum vonMangoldt (N + 1) = gsum (fun n => vonMangoldt n * 1) (N + 1) :=
    gsum_congr fun n _ => by grind
  rw [e, gsum_vonMangoldt_mul]
  have h1 := gsum_le_gsum (n := N + 1) (g := fun p => if Prime p then lnat N else 0)
    (f := fun p => gsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then lnat p * 1 else 0) (N + 1))
    (fun p _ => by
      by_cases hp : Prime p
      · rw [ite_eq_left hp]; exact gsum_prime_pow_le hp N
      · rw [ite_eq_right hp]
        exact Std.le_of_eq ((gsum_congr (g := fun _ => 0) (fun k _ => ite_eq_right
          (fun h => hp h.1))).trans (gsum_zero' _)))
  rw [gsum_ite_prime] at h1
  have h2 := log_ineq_of_pow_le hN (by omega : 0 < 1024) (chebyshev_upper hN)
  have h3 : lnat N = R.log (N : R) := by unfold lnat; rw [ite_eq_right (by omega)]
  show _ ≤ (N : R) * R.log ((1024 : Nat) : R)
  have : (countBelow Prime (N + 1) : R) = (primeCount N : R) := rfl
  rw [this, h3] at h1
  grind

/-! ## Mertens' estimate -/

/-- **Mertens' lower bound.** `Σ_{n ≤ N} Λ(n)/n ≥ log N − 1`. -/
theorem mertens_lower {N : Nat} (hN : 0 < N) :
    lnat N - 1 ≤ gsum (fun d => vonMangoldt d / (d : R)) (N + 1) := by
  have hx : (0 : R) < (N : R) := natCast_pos' hN
  have h1 := lnat_fact_ge hN
  rw [lnat_fact_eq] at h1
  have h2 : gsum (fun d => vonMangoldt d * ((N / d : Nat) : R)) (N + 1) ≤
      gsum (fun d => (N : R) * (vonMangoldt d / (d : R))) (N + 1) := by
    apply gsum_le_gsum; intro d _
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; rw [vonMangoldt_zero]; grind
    · have := OrderedRing.mul_le_mul_of_nonneg_left (natDiv_le N hd) (vonMangoldt_nonneg d)
      have hd' : (d : R) ≠ 0 := by have := natCast_pos' hd; grind
      grind
  rw [gsum_mul_left] at h2
  generalize gsum (fun d => vonMangoldt d / (d : R)) (N + 1) = M at h2 ⊢
  have h4 : 0 ≤ (N : R) * (M - (lnat N - 1)) := by grind
  have := nonneg_of_mul_nonneg_left' hx h4; grind

/-- **Mertens' upper bound.** `Σ_{n ≤ N} Λ(n)/n ≤ log N + log 1024`. -/
theorem mertens_upper {N : Nat} (hN : 0 < N) :
    gsum (fun d => vonMangoldt d / (d : R)) (N + 1) ≤ lnat N + chebC := by
  have hx : (0 : R) < (N : R) := natCast_pos' hN
  have h1 := lnat_fact_le N
  rw [lnat_fact_eq] at h1
  have h2 : gsum (fun d => (N : R) * (vonMangoldt d / (d : R))) (N + 1) ≤
      gsum (fun d => vonMangoldt d * ((N / d : Nat) : R) + vonMangoldt d) (N + 1) := by
    apply gsum_le_gsum; intro d _
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; rw [vonMangoldt_zero]; grind
    · have := OrderedRing.mul_le_mul_of_nonneg_left (div_le_natDiv_add_one N hd)
        (vonMangoldt_nonneg d)
      have hd' : (d : R) ≠ 0 := by have := natCast_pos' hd; grind
      grind
  rw [gsum_mul_left, gsum_add] at h2
  have h3 := psi_le hN
  generalize gsum (fun d => vonMangoldt d / (d : R)) (N + 1) = M at h2 ⊢
  have h4 : 0 ≤ (N : R) * (lnat N + chebC - M) := by grind
  have := nonneg_of_mul_nonneg_left' hx h4; grind

end Foundations.NumberTheory
