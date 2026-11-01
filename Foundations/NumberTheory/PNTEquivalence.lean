import Foundations.NumberTheory.PNTChebyshevFunctions

/-!
# Toward the prime number theorem III: three equivalent forms

The prime number theorem can be stated in three ways, and this file proves that they are
equivalent:

  `π(N) · log N / N → 1`   ⇔   `θ(N) / N → 1`   ⇔   `ψ(N) / N → 1`.

The first is Gauss's and Legendre's conjecture — the primes up to `N` number about `N / log N`.
The last is the form in which the theorem is actually *proved*, both in the complex-analytic
proofs of Hadamard and de la Vallée Poussin (1896) and in the elementary proof of Selberg and
Erdős (1949): `ψ` is the function that interacts well with multiplication, through
`Σ_{d ∣ n} Λ(d) = log n`.

* `ψ ↔ θ`: the difference `ψ(N) − θ(N) ≤ √N · log N` (previous file) is `o(N)`, because
  `log N` grows more slowly than any power of `N` — here we only need `log m ≤ 2√m`.
* `θ ↔ π`: trivially `θ(N) ≤ π(N) log N`. Conversely, cutting at `M = ⌊N/k⌋`, the primes in
  `(M, N]` each contribute at least `log M ≥ log N − log 2k`, and there are at most
  `π(M) ≤ M log 1024 / log M` primes below `M` (Chebyshev). So
  `π(N) log N − θ(N) ≤ (log 1024 / k) · N + π(N) log 2k`, and the right side is at most `εN`
  once `k` is large and then `N` is large (since `π(N) ≤ N log 1024 / log N` and
  `log N → ∞`). This replaces the usual partial summation `π(x) = θ(x)/log x + ∫ θ(t)/(t log² t)`.

The statements are about sequences indexed by natural numbers `N`, with limits in the sense of
Part II (`Tendsto`).
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-! ## Small real-number tools -/

/-- To show `aₙ → L` it suffices that eventually `|aₙ − L| ≤ ε` for every `ε > 0`. -/
theorem tendsto_of_le_eps {a : Nat → R} {L : R}
    (h : ∀ ε : R, 0 < ε → ∃ N, ∀ n, N ≤ n → abs (a n - L) ≤ ε) : Tendsto a L := fun ε hε => by
  obtain ⟨N, hN⟩ := h (ε / 2) (by grind)
  exact ⟨N, fun n hn => by have := hN n hn; grind⟩

/-- If `aₙ − bₙ → 0` then `aₙ → L ↔ bₙ → L`. -/
theorem tendsto_iff_of_sub {a b : Nat → R} {L : R} (h : Tendsto (fun n => a n - b n) 0) :
    Tendsto a L ↔ Tendsto b L := by
  constructor
  · intro ha
    have h1 := ha.sub h
    rw [show L - 0 = L by grind] at h1
    intro ε hε
    obtain ⟨N, hN⟩ := h1 ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h2 := hN n hn
    simp only [show a n - (a n - b n) = b n by grind] at h2
    exact h2
  · intro hb
    have h1 := hb.add h
    rw [show L + 0 = L by grind] at h1
    intro ε hε
    obtain ⟨N, hN⟩ := h1 ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h2 := hN n hn
    simp only [show b n + (a n - b n) = a n by grind] at h2
    exact h2

/-- Cancelling a positive factor: `a · C ≤ b · C` with `C > 0` gives `a ≤ b`. -/
theorem le_of_mul_le_mul_right' {a b C : R} (h : a * C ≤ b * C) (hC : 0 < C) : a ≤ b := by
  apply Classical.byContradiction; intro hab
  have := OrderedRing.mul_pos (show 0 < a - b by grind) hC
  grind

/-- Dividing a bound: `0 ≤ x ≤ ε · N` with `N > 0` gives `|x / N| ≤ ε`. -/
theorem abs_div_le_of_le {x ε N : R} (hN : 0 < N) (h0 : 0 ≤ x) (h : x ≤ ε * N) :
    abs (x / N) ≤ ε := by
  have hN0 : N ≠ 0 := by grind
  have hi : 0 ≤ N⁻¹ := by
    have := div_pos (show (0 : R) < 1 by grind) hN; grind
  have h1 := OrderedRing.mul_le_mul_of_nonneg_right h hi
  have h2 := OrderedRing.mul_le_mul_of_nonneg_right h0 hi
  have e : ε * N * N⁻¹ = ε := by grind
  rw [abs_of_nonneg (by grind)]
  grind

/-- For `ε > 0` and any `c`, some natural `k ≥ 1` has `c ≤ ε · k`. -/
theorem exists_nat_mul_ge (c : R) {ε : R} (hε : 0 < ε) : ∃ k : Nat, 1 ≤ k ∧ c ≤ ε * (k : R) := by
  obtain ⟨n, hn⟩ := archimedean (c / ε)
  refine ⟨n + 1, by omega, ?_⟩
  have h1 : c / ε ≤ ((n + 1 : Nat) : R) := by grind
  have := OrderedRing.mul_le_mul_of_nonneg_left h1 (Std.le_of_lt hε)
  have e : ε * (c / ε) = c := by have : ε ≠ 0 := by grind
                                 grind
  grind

/-- **`log N → ∞`.** For every `C` there is `N₀` with `C ≤ log N` for all `N ≥ N₀`. -/
theorem log_eventually_ge (C : R) : ∃ N₀ : Nat, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N → C ≤ R.log (N : R) := by
  obtain ⟨n, hn⟩ := archimedean (exp C)
  have hn1 : 1 ≤ n := by
    apply Classical.byContradiction; intro h
    obtain rfl : n = 0 := by omega
    have := exp_pos C; have : ((0 : Nat) : R) = 0 := by grind
    grind
  refine ⟨n, hn1, fun N hN => ?_⟩
  have h1 := R.log_strictMono (exp_pos C) hn
  rw [log_exp] at h1
  have := log_le_log (natCast_pos' (show 0 < n by omega)) (natCast_le' hN)
  grind

/-- **The logarithm is small.** For `T ≥ 1` and `m ≥ T²`: `T · log m ≤ 2m`. (With `t = ⌊√m⌋`:
`log m ≤ 2 log (t + 1) ≤ 2t` and `T · t ≤ t² ≤ m`.) -/
theorem log_mul_le {T m : Nat} (hT : 1 ≤ T) (hm : T * T ≤ m) :
    R.log (m : R) * (T : R) ≤ 2 * (m : R) := by
  obtain ⟨t, ht1, ht2⟩ := exists_sqrt m
  have hTt : T ≤ t := by
    apply Classical.byContradiction; intro h
    have : (t + 1) * (t + 1) ≤ T * T := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hm1 : 1 ≤ m := Nat.le_trans (Nat.mul_le_mul hT hT) hm
  -- `log m ≤ 2 log (t + 1) ≤ 2t`.
  have hl1 : R.log (m : R) ≤ 2 * R.log ((t + 1 : Nat) : R) := by
    have := log_ineq_of_pow_le (a := m) (b := t + 1) (k := 1) (l := 2) (by omega) (by omega)
      (by rw [Nat.pow_one, Nat.pow_two]; omega)
    grind
  have hl2 : R.log ((t + 1 : Nat) : R) ≤ (t : R) := by
    have := log_le_sub_one (one_le_natCast (n := t + 1) (by omega)); grind
  have hlog0 := log_natCast_nonneg hm1
  have k1 := OrderedRing.mul_le_mul_of_nonneg_left (show (T : R) ≤ (t : R) from natCast_le' hTt)
    hlog0
  have k2 := OrderedRing.mul_le_mul_of_nonneg_right (show R.log (m : R) ≤ 2 * (t : R) by grind)
    (natCast_nonneg' t)
  have k3 : ((t * t : Nat) : R) ≤ (m : R) := natCast_le' ht1
  rw [natCast_mul'] at k3
  grind

/-! ## ψ versus θ -/

/-- **`ψ(N) − θ(N) = o(N)`.** For every `ε > 0`, eventually `ψ(N) − θ(N) ≤ ε N`. -/
theorem psi_sub_theta_small {ε : R} (hε : 0 < ε) :
    ∃ N₀, ∀ N, N₀ ≤ N → psi N - theta N ≤ ε * (N : R) := by
  obtain ⟨T, hT, hTε⟩ := exists_nat_mul_ge 8 hε
  refine ⟨T * T * (T * T), fun N hN => ?_⟩
  have hTT : 1 ≤ T * T := Nat.mul_le_mul hT hT
  have hN1 : 1 ≤ N := Nat.le_trans (Nat.mul_le_mul hTT hTT) hN
  obtain ⟨s, hs1, hs2⟩ := exists_sqrt N
  have hs : 1 ≤ s := by
    apply Classical.byContradiction; intro h
    obtain rfl : s = 0 := by omega
    omega
  have hsT : T * T ≤ s + 1 := by
    apply Classical.byContradiction; intro h
    have : (s + 1) * (s + 1) ≤ T * T * (T * T) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hmain := psi_sub_theta_le hN1 hs1 hs2
  -- `log N ≤ 2 log (s + 1)` and `T log (s + 1) ≤ 2 (s + 1)`.
  have hl1 : R.log (N : R) ≤ 2 * R.log ((s + 1 : Nat) : R) := by
    have := log_ineq_of_pow_le (a := N) (b := s + 1) (k := 1) (l := 2) (by omega) (by omega)
      (by rw [Nat.pow_one, Nat.pow_two]; omega)
    grind
  have hl2 := log_mul_le hT hsT
  have hT0 : (0 : R) < (T : R) := natCast_pos' (by omega)
  have hs0 := natCast_nonneg' s
  -- `s · log N · T ≤ 2 s · (T log (s + 1)) ≤ 4 s (s + 1) ≤ 8 s² ≤ 8 N`.
  have k1 := OrderedRing.mul_le_mul_of_nonneg_left hl1 hs0
  have k1' := OrderedRing.mul_le_mul_of_nonneg_right k1 (Std.le_of_lt hT0)
  have k2 := OrderedRing.mul_le_mul_of_nonneg_left hl2 hs0
  have hss : ((s * s : Nat) : R) ≤ (N : R) := natCast_le' hs1
  rw [natCast_mul'] at hss
  have hs1' : (1 : R) ≤ (s : R) := one_le_natCast hs
  have k3 := OrderedRing.mul_le_mul_of_nonneg_left hs1' hs0
  have key : (s : R) * R.log (N : R) * (T : R) ≤ 8 * (N : R) := by
    have e : ((s + 1 : Nat) : R) = (s : R) + 1 := by grind
    rw [e] at k2
    grind
  have hN0 := natCast_nonneg' N
  have k4 := OrderedRing.mul_le_mul_of_nonneg_left hTε hN0
  have : (s : R) * R.log (N : R) ≤ ε * (N : R) :=
    le_of_mul_le_mul_right' (by grind) hT0
  grind

/-- **`ψ(N)/N − θ(N)/N → 0`.** -/
theorem tendsto_psi_sub_theta :
    Tendsto (fun N => psi N / (N : R) - theta N / (N : R)) 0 := by
  apply tendsto_of_le_eps; intro ε hε
  obtain ⟨N₀, hN₀⟩ := psi_sub_theta_small hε
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN : (0 : R) < (N : R) := natCast_pos' (by omega)
  rw [show psi N / (N : R) - theta N / (N : R) - 0 = (psi N - theta N) / (N : R) by grind]
  exact abs_div_le_of_le hN (by have := theta_le_psi N; grind) (hN₀ N (by omega))

/-! ## θ versus π -/

/-- **`θ(N) ≤ π(N) · log N`.** -/
theorem theta_le_primeCount_mul_log (N : Nat) :
    theta N ≤ (primeCount N : R) * R.log (N : R) := by
  unfold theta; rw [← fsum_prime_const]
  apply fsum_le_fsum'; intro p hp
  by_cases hpr : Prime p
  · simp only [hpr, ↓reduceIte]
    exact log_le_log (natCast_pos' (by have := hpr.1; omega)) (natCast_le' (by omega))
  · simp only [hpr, ↓reduceIte]; grind

/-- **Primes above `M` weigh at least `log M`.** For `1 ≤ M ≤ N`:
`π(N) · log M ≤ θ(N) + π(M) · log M`. -/
theorem primeCount_mul_log_le_theta {M N : Nat} (hM : 1 ≤ M) (hMN : M ≤ N) :
    (primeCount N : R) * R.log (M : R) ≤ theta N + (primeCount M : R) * R.log (M : R) := by
  have hlM := log_natCast_nonneg hM
  have e : fsum (fun p => if Prime p ∧ p ≤ M then R.log (M : R) else 0) (N + 1) =
      (primeCount M : R) * R.log (M : R) := by
    rw [← fsum_congr_bound (show M + 1 ≤ N + 1 by omega) (fun p h1 _ => by
      have : ¬ (Prime p ∧ p ≤ M) := fun h => by omega
      simp only [this, ↓reduceIte])]
    rw [← fsum_prime_const]
    apply fsum_congr; intro p hp
    simp only [show p ≤ M by omega, and_true]
  rw [← e, ← fsum_prime_const]; unfold theta; rw [← fsum_add]
  apply fsum_le_fsum'; intro p _
  by_cases hpr : Prime p
  · have hp1 : 1 ≤ p := by have := hpr.1; omega
    have hlp := log_natCast_nonneg hp1
    simp only [hpr, true_and, ↓reduceIte]
    by_cases hpM : p ≤ M
    · simp only [hpM, ↓reduceIte]; grind
    · simp only [hpM, ↓reduceIte]
      have := log_le_log (natCast_pos' (by omega)) (natCast_le' (show M ≤ p by omega))
      grind
  · simp only [hpr, false_and, ↓reduceIte]; grind

/-- **`π(N) log N − θ(N) = o(N)`.** For every `ε > 0`, eventually
`π(N) · log N − θ(N) ≤ ε N`. -/
theorem primeCount_log_sub_theta_small {ε : R} (hε : 0 < ε) :
    ∃ N₀, ∀ N, N₀ ≤ N → (primeCount N : R) * R.log (N : R) - theta N ≤ ε * (N : R) := by
  let c : R := R.log 1024
  have hε2 : 0 < ε / 2 := by grind
  obtain ⟨k, hk, hkc⟩ := exists_nat_mul_ge c hε2
  let L : R := R.log ((2 * k : Nat) : R)
  have hL : 0 ≤ L := log_natCast_nonneg (by omega)
  obtain ⟨C', -, hC'⟩ := exists_nat_mul_ge (c * L) hε2
  let C : R := (C' : R) + 1
  have hC : 0 < C := by have := natCast_nonneg' C'; grind
  have hcL : c * L ≤ ε / 2 * C := by
    have := OrderedRing.mul_le_mul_of_nonneg_left (show (C' : R) ≤ C by grind)
      (Std.le_of_lt hε2)
    grind
  obtain ⟨N₁, hN₁1, hN₁⟩ := log_eventually_ge C
  refine ⟨max N₁ k, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNk : k ≤ N := by omega
  -- The cut `M = ⌊N/k⌋`.
  let M := N / k
  have hM1 : 1 ≤ M := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hMN : M ≤ N := Nat.div_le_self N k
  have hMk : M * k ≤ N := Nat.div_mul_le_self N k
  have hN2kM : N ≤ 2 * k * M := by
    have := Nat.lt_div_mul_add (a := N) (b := k) (by omega)
    have : N < k * M + k := by
      have e : N / k * k = k * M := Nat.mul_comm _ _
      omega
    have : k ≤ k * M := Nat.le_mul_of_pos_right k (by omega)
    have e2 : 2 * k * M = k * M + k * M := by grind
    omega
  -- Step 1: `π(N) log M ≤ θ(N) + M · c ≤ θ(N) + (ε/2) N`.
  have s1 := primeCount_mul_log_le_theta hM1 hMN
  have s2 := primeCount_mul_log_le hM1
  have hM0 := natCast_nonneg' M
  have s3 : (M : R) * c ≤ ε / 2 * (N : R) := by
    have k1 := OrderedRing.mul_le_mul_of_nonneg_left hkc hM0
    have k2 : ((M * k : Nat) : R) ≤ (N : R) := natCast_le' hMk
    rw [natCast_mul'] at k2
    have k3 := OrderedRing.mul_le_mul_of_nonneg_left k2 (Std.le_of_lt hε2)
    grind
  -- Step 2: `log N ≤ L + log M`.
  have s4 : R.log (N : R) ≤ L + R.log (M : R) := by
    have h1 := log_le_log (natCast_pos' hN1) (natCast_le' hN2kM)
    rw [natCast_mul', R.log_mul (natCast_pos' (by omega)) (natCast_pos' hM1)] at h1
    exact h1
  have hpi0 := natCast_nonneg' (primeCount N)
  have s5 := OrderedRing.mul_le_mul_of_nonneg_left s4 hpi0
  -- Step 3: `π(N) · L ≤ (ε/2) N`, because `π(N) log N ≤ N c` and `log N ≥ C`.
  have s6 : (primeCount N : R) * L ≤ ε / 2 * (N : R) := by
    have h1 := primeCount_mul_log_le hN1
    have h2 := hN₁ N (by omega)
    have hpL : 0 ≤ (primeCount N : R) * L := OrderedRing.mul_nonneg hpi0 hL
    have k1 := OrderedRing.mul_le_mul_of_nonneg_left h2 hpL
    have k2 := OrderedRing.mul_le_mul_of_nonneg_right h1 hL
    have k3 := OrderedRing.mul_le_mul_of_nonneg_left hcL (natCast_nonneg' N)
    apply le_of_mul_le_mul_right' (C := C) _ hC
    grind
  grind

/-- **`π(N) log N / N − θ(N)/N → 0`.** -/
theorem tendsto_primeCount_sub_theta :
    Tendsto (fun N => (primeCount N : R) * R.log (N : R) / (N : R) - theta N / (N : R)) 0 := by
  apply tendsto_of_le_eps; intro ε hε
  obtain ⟨N₀, hN₀⟩ := primeCount_log_sub_theta_small hε
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN : (0 : R) < (N : R) := natCast_pos' (by omega)
  rw [show (primeCount N : R) * R.log (N : R) / (N : R) - theta N / (N : R) - 0 =
    ((primeCount N : R) * R.log (N : R) - theta N) / (N : R) by grind]
  exact abs_div_le_of_le hN (by have := theta_le_primeCount_mul_log N; grind)
    (hN₀ N (by omega))

/-! ## The three forms of the prime number theorem -/

/-- **The prime number theorem** (statement): `π(N) · log N / N → 1`, i.e. `π(N) ∼ N / log N`. -/
def PrimeNumberTheorem : Prop :=
  Tendsto (fun N => (primeCount N : R) * R.log (N : R) / (N : R)) 1

/-- **PNT ⇔ θ(N) ∼ N.** The prime number theorem holds iff `θ(N)/N → 1`. -/
theorem pnt_iff_theta : PrimeNumberTheorem ↔ Tendsto (fun N => theta N / (N : R)) 1 :=
  tendsto_iff_of_sub tendsto_primeCount_sub_theta

/-- **ψ(N) ∼ N ⇔ θ(N) ∼ N.** -/
theorem psi_iff_theta :
    Tendsto (fun N => psi N / (N : R)) 1 ↔ Tendsto (fun N => theta N / (N : R)) 1 :=
  tendsto_iff_of_sub tendsto_psi_sub_theta

/-- **PNT ⇔ ψ(N) ∼ N.** The prime number theorem is equivalent to `ψ(N)/N → 1` — the form in
which it is proved, analytically or elementarily. -/
theorem pnt_iff_psi : PrimeNumberTheorem ↔ Tendsto (fun N => psi N / (N : R)) 1 :=
  pnt_iff_theta.trans psi_iff_theta.symm

end Foundations.NumberTheory.PNT
