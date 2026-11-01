import Foundations.NumberTheory.Unify

/-!
# Corollaries: Euler's divergence and a consequence of the prime number theorem

With the two blocks of this part unified (file `Unify`), we harvest two classical consequences.

**Euler (1737): `Σ 1/p` diverges.** Euler deduced it from his product formula; we deduce it from
Mertens' second theorem (`PNT.mertens_primes`), `Σ_{p ≤ N} log p / p = log N + O(1)`. Comparing the
values at `M` and `M²`, the primes in `(M, M²]` contribute about `log M` to `Σ log p / p`; each of
them has `log p ≤ 2 log M`, so they contribute at least about `1/2` to `Σ 1/p` — at least `1/4`
once `log M` is large (`primeRecip_block`). Squaring again and again (`M, M², M⁴, …`) adds `1/4`
each time, so `Σ_{p ≤ N} 1/p` is unbounded (`euler_sum_reciprocal_primes`). This replaces the
partial summation one would otherwise use.

**`π(2N) ∼ 2 π(N)`.** From the prime number theorem `π(N) log N / N → 1`, applied at `N` and at
`2N`, together with `log N / log 2N → 1`, the ratio `π(2N) / π(N)` tends to `2`
(`primeCount_two_mul_div_tendsto`): asymptotically there are as many primes in `(N, 2N]` as in
`[1, N]` — a quantitative refinement of Bertrand's postulate, and the reason the primes in
`(N, 2N]` become ever more numerous (`primeCount_two_mul_sub_unbounded`).

**Dirichlet in Euler's form.** Re-running the sieve argument of `DirichletConditional` with the
non-vanishing `L(1, χ) ≠ 0` now available, the sum `Σ_{n ≤ N, n ≡ a} Λ(n)/n` is unbounded; the
prime powers `pᵏ`, `k ≥ 2`, contribute at most `4`, so `Σ_{p ≤ N, p ≡ a (q)} log p / p` is
unbounded too (`dirichlet_euler`).
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-! ## Euler: the sum of the reciprocals of the primes diverges -/

/-- `Σ_{p ≤ N} 1/p`, the sum of the reciprocals of the primes up to `N`. -/
noncomputable def primeRecip (N : Nat) : R := fsum (fun p => if Prime p then 1 / (p : R) else 0) (N + 1)

/-- `Σ_{p ≤ N} 1/p ≥ 0`. -/
theorem primeRecip_nonneg (N : Nat) : 0 ≤ primeRecip N := by
  apply fsum_nonneg; intro p
  by_cases hp : Prime p
  · rw [ite_eq_left hp]
    exact Std.le_of_lt (div_pos (by grind) (natCast_pos' (by have := hp.1; omega)))
  · rw [ite_eq_right hp]; grind

/-- Comparing increments: if `a k ≤ b k` for `M ≤ k < N`, then
`Σ_{k<N} a − Σ_{k<M} a ≤ Σ_{k<N} b − Σ_{k<M} b`. -/
theorem fsum_diff_le {a b : Nat → R} {M N : Nat} (hMN : M ≤ N)
    (h : ∀ k, M ≤ k → k < N → a k ≤ b k) : fsum a N - fsum a M ≤ fsum b N - fsum b M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN
  clear hMN
  induction d with
  | zero => grind
  | succ d ih =>
    rw [← Nat.add_assoc, fsum_succ, fsum_succ]
    have := ih (fun k h1 h2 => h k h1 (by omega))
    have := h (M + d) (by omega) (by omega)
    grind

/-- The constant `c = 3 + log 1024` of Mertens' second theorem (lower error `3`, upper `log 1024`). -/
theorem mertens_const_pos : 0 < 3 + R.log 1024 := by
  have := PNT.log_nonneg' (y := (1024 : R)) (by grind)
  grind

/-- **One block of primes contributes `1/4`.** If `M ≥ 1` and `log M ≥ 2 (3 + log 1024)`, then
`Σ_{M < p ≤ M²} 1/p ≥ 1/4`. -/
theorem primeRecip_block {M : Nat} (hM : 1 ≤ M) (hlog : 2 * (3 + R.log 1024) ≤ R.log (M : R)) :
    1 / 4 ≤ primeRecip (M * M) - primeRecip M := by
  have hMM : 1 ≤ M * M := Nat.mul_le_mul hM hM
  have hMle : M ≤ M * M := Nat.le_mul_of_pos_left M (by omega)
  have hM0 : (0 : R) < (M : R) := natCast_pos' hM
  have hA2 := (PNT.mertens_primes hMM).1
  have hA1 := (PNT.mertens_primes hM).2
  have hlogMM : R.log ((M * M : Nat) : R) = R.log (M : R) + R.log (M : R) := by
    rw [PNT.natCast_mul', R.log_mul hM0 hM0]
  rw [hlogMM] at hA2
  have hdiff := fsum_diff_le (M := M + 1) (N := M * M + 1)
    (a := fun p => if Prime p then R.log (p : R) * (1 / (p : R)) else 0)
    (b := fun p => (R.log (M : R) + R.log (M : R)) * (if Prime p then 1 / (p : R) else 0))
    (by omega) (fun k _ hk2 => by
      by_cases hp : Prime k
      · rw [ite_eq_left hp, ite_eq_left hp]
        have hk0 : (0 : R) < (k : R) := natCast_pos' (by have := hp.1; omega)
        have hle : R.log (k : R) ≤ R.log ((M * M : Nat) : R) :=
          log_le_log hk0 (PNT.natCast_le_iff.2 (by omega))
        rw [hlogMM] at hle
        exact OrderedRing.mul_le_mul_of_nonneg_right hle (Std.le_of_lt (div_pos (by grind) hk0))
      · rw [ite_eq_right hp, ite_eq_right hp]; grind)
  rw [R.fsum_const_mul, R.fsum_const_mul] at hdiff
  unfold primeRecip
  generalize fsum (fun p => if Prime p then 1 / (p : R) else 0) (M * M + 1) = P2 at hdiff ⊢
  generalize fsum (fun p => if Prime p then 1 / (p : R) else 0) (M + 1) = P1 at hdiff ⊢
  generalize fsum (fun p => if Prime p then R.log (p : R) * (1 / (p : R)) else 0) (M * M + 1) = A2
    at hdiff hA2
  generalize fsum (fun p => if Prime p then R.log (p : R) * (1 / (p : R)) else 0) (M + 1) = A1
    at hdiff hA1
  have hc := mertens_const_pos
  generalize R.log (M : R) = x at hdiff hA1 hA2 hlog
  generalize R.log 1024 = c at hA1 hc hlog
  have hx : 0 < 2 * x := by grind
  have key : 0 ≤ (2 * x) * ((P2 - P1) - 1 / 4) := by grind
  have := nonneg_of_mul_nonneg_left' hx key
  grind

/-- **Repeated squaring.** Under the hypotheses of `primeRecip_block`,
`Σ_{p ≤ M^(2^j)} 1/p ≥ j/4` for every `j`. -/
theorem primeRecip_iter {M : Nat} (hM : 1 ≤ M) (hlog : 2 * (3 + R.log 1024) ≤ R.log (M : R)) :
    ∀ j : Nat, (j : R) / 4 ≤ primeRecip (M ^ (2 ^ j))
  | 0 => by
    have := primeRecip_nonneg (M ^ (2 ^ 0))
    have e : ((0 : Nat) : R) / 4 = 0 := by rw [Field.div_eq_mul_inv]; grind
    rw [e]; exact this
  | j + 1 => by
    have ih := primeRecip_iter hM hlog j
    have hK : 1 ≤ M ^ (2 ^ j) := Nat.pow_pos (by omega)
    have hMK : M ≤ M ^ (2 ^ j) := Nat.le_self_pow (by have := Nat.pow_pos (n := j) (show 0 < 2 by omega); omega) M
    have hlogK : 2 * (3 + R.log 1024) ≤ R.log ((M ^ (2 ^ j) : Nat) : R) :=
      Std.le_trans hlog (log_le_log (natCast_pos' hM) (PNT.natCast_le_iff.2 hMK))
    have hb := primeRecip_block hK hlogK
    have e : M ^ (2 ^ (j + 1)) = M ^ (2 ^ j) * M ^ (2 ^ j) := by
      rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]
    rw [e]
    have e2 : ((j + 1 : Nat) : R) / 4 = (j : R) / 4 + 1 / 4 := by
      rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
    rw [e2]; grind

/-- **Euler's theorem (1737).** The sum of the reciprocals of the primes diverges: for every bound
`B` there is `N` with `Σ_{p ≤ N} 1/p ≥ B`. -/
theorem euler_sum_reciprocal_primes (B : R) :
    ∃ N : Nat, B ≤ fsum (fun p => if Prime p then 1 / (p : R) else 0) (N + 1) := by
  obtain ⟨M, hM1, hM⟩ := PNT.log_eventually_ge (2 * (3 + R.log 1024))
  obtain ⟨j, -, hj⟩ := PNT.exists_nat_mul_ge B (ε := 1 / 4) (by grind)
  refine ⟨M ^ (2 ^ j), ?_⟩
  have := primeRecip_iter hM1 (hM M (Nat.le_refl M)) j
  have e : (j : R) / 4 = 1 / 4 * (j : R) := by rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
  unfold primeRecip at this
  grind

/-- **`Σ 1/p` is unbounded.** No real number bounds all the partial sums `Σ_{p ≤ N} 1/p`. -/
theorem not_bounded_sum_reciprocal_primes :
    ¬ ∃ B : R, ∀ N : Nat, fsum (fun p => if Prime p then 1 / (p : R) else 0) (N + 1) ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨N, hN⟩ := euler_sum_reciprocal_primes (B + 1)
  have := hB N
  grind

/-! ## `π(2N) / π(N) → 2` -/

/-- If `aₙ → 1` then `1/aₙ → 1`. -/
theorem tendsto_one_div_of_one {a : Nat → R} (h : Tendsto a 1) : Tendsto (fun n => 1 / a n) 1 := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := h (1 / 2) (by grind)
  obtain ⟨N₂, h₂⟩ := h (ε / 2) (by grind)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have k1 := OF.abs_lt.1 (h₁ n (by omega))
  have k2 := OF.abs_lt.1 (h₂ n (by omega))
  have ha : 1 / 2 < a n := by grind
  have ha0 : a n ≠ 0 := by grind
  have hb0 : 0 < 1 / a n := div_pos (by grind) (by grind)
  have hab : a n * (1 / a n) = 1 := by grind
  have hb2 : 1 / a n < 2 := by
    have := OrderedRing.mul_lt_mul_of_pos_left ha hb0
    grind
  show abs (1 / a n - 1) < ε
  apply OF.abs_lt.2
  have e : 1 / a n - 1 = (1 / a n) * (1 - a n) := by grind
  rw [e]
  have u1 := OrderedRing.mul_lt_mul_of_pos_left (show 1 - a n < ε / 2 by grind) hb0
  have u2 := OrderedRing.mul_lt_mul_of_pos_left (show -(ε / 2) < 1 - a n by grind) hb0
  have u3 := OrderedRing.mul_lt_mul_of_pos_left hb2 (show 0 < ε / 2 by grind)
  constructor <;> grind

/-- `log N / log 2N → 1`. -/
theorem log_div_log_two_mul_tendsto :
    Tendsto (fun N => R.log (N : R) / R.log ((2 * N : Nat) : R)) 1 := by
  apply PNT.tendsto_of_le_eps; intro ε hε
  have hl2 : 0 < R.log (2 : R) := PNT.log_pos' (by grind)
  obtain ⟨N₀, hN₀1, hN₀⟩ := PNT.log_eventually_ge (R.log (2 : R) / ε)
  refine ⟨N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : R) < (N : R) := natCast_pos' (by omega)
  have hlN := hN₀ N hN
  have hdiv : 0 < R.log (2 : R) / ε := div_pos hl2 hε
  have e2 : R.log ((2 * N : Nat) : R) = R.log (2 : R) + R.log (N : R) := by
    rw [PNT.natCast_mul', show ((2 : Nat) : R) = 2 by grind, R.log_mul (by grind) hN0]
  rw [e2]
  generalize R.log (N : R) = y at hlN ⊢
  generalize R.log (2 : R) = l at hl2 hdiv hlN ⊢
  have hL : 0 < l + y := by grind
  have e : y / (l + y) - 1 = -(l / (l + y)) := by
    rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]
    have : (l + y) * (l + y)⁻¹ = 1 := Field.mul_inv_cancel (by grind)
    grind
  rw [e]
  have h0 : 0 ≤ l / (l + y) := Std.le_of_lt (div_pos hl2 hL)
  have hle : l / (l + y) ≤ ε := by
    apply div_le_of_le_mul hL
    have : l = (l / ε) * ε := by
      rw [Field.div_eq_mul_inv]
      have : ε * ε⁻¹ = 1 := Field.mul_inv_cancel (by grind)
      grind
    have := OrderedRing.mul_le_mul_of_nonneg_left (show l / ε ≤ l + y by grind) (Std.le_of_lt hε)
    grind
  rcases OF.abs_cases (-(l / (l + y))) with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> grind

/-- `π(N) ≥ 1` for `N ≥ 2`. -/
theorem one_le_primeCount {N : Nat} (hN : 2 ≤ N) : 1 ≤ primeCount N := by
  have h2 : primeCount 2 = 1 := by decide
  have := primeCount_mono hN
  omega

/-- **`π(2N) ∼ 2 π(N)`.** As a consequence of the prime number theorem,
`π(2N) / π(N) → 2`: asymptotically, `(N, 2N]` contains as many primes as `[1, N]`. -/
theorem primeCount_two_mul_div_tendsto :
    Tendsto (fun N => (primeCount (2 * N) : R) / (primeCount N : R)) 2 := by
  have hP : Tendsto (fun N => (primeCount N : R) * R.log (N : R) / (N : R)) 1 :=
    PNT.prime_number_theorem
  have hP2 : Tendsto (fun N => (primeCount (2 * N) : R) * R.log ((2 * N : Nat) : R) /
      ((2 * N : Nat) : R)) 1 := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hP ε hε
    exact ⟨N₀, fun N hN => hN₀ (2 * N) (by omega)⟩
  have hinv := tendsto_one_div_of_one hP
  have hprod := Tendsto.const_mul 2 ((hP2.mul hinv).mul log_div_log_two_mul_tendsto)
  rw [show (2 : R) * (1 * 1 * 1) = 2 by grind] at hprod
  apply Tendsto.congr_eventually hprod 2
  intro N hN
  have hp1 : (0 : R) < (primeCount N : R) := natCast_pos' (one_le_primeCount hN)
  have hn : (0 : R) < (N : R) := natCast_pos' (by omega)
  have hl1 : 0 < R.log (N : R) := PNT.log_pos' (by
    have := PNT.natCast_le_iff.2 hN; rw [show ((2 : Nat) : R) = 2 by grind] at this; grind)
  have hl2 : 0 < R.log ((2 * N : Nat) : R) := PNT.log_pos' (by
    have := PNT.natCast_le_iff.2 (show 2 ≤ 2 * N by omega)
    rw [show ((2 : Nat) : R) = 2 by grind] at this; grind)
  rw [PNT.natCast_mul' 2 N, show ((2 : Nat) : R) = 2 by grind] at *
  generalize (primeCount N : R) = p1 at *
  generalize (primeCount (2 * N) : R) = p2
  generalize R.log (N : R) = l1 at *
  generalize R.log (2 * (N : R)) = l2 at *
  generalize (N : R) = n at *
  have : p1 ≠ 0 := by grind
  have : l1 ≠ 0 := by grind
  have : l2 ≠ 0 := by grind
  have : n ≠ 0 := by grind
  have : p1 * l1 / n ≠ 0 := fun h => by
    have := div_pos (OrderedRing.mul_pos hp1 hl1) hn; grind
  grind

/-- `π(N)` is unbounded (Euclid): for every `k` there is `N` with `π(N) ≥ k`. -/
theorem primeCount_unbounded : ∀ k : Nat, ∃ N, k ≤ primeCount N
  | 0 => ⟨0, Nat.zero_le _⟩
  | k + 1 => by
    obtain ⟨N, hN⟩ := primeCount_unbounded k
    obtain ⟨p, hp1, hp⟩ := exists_prime_ge (N + 1)
    refine ⟨p, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    rw [primeCount_succ, ite_eq_left hp]
    have := primeCount_mono (show N ≤ m by omega)
    omega

/-- **More and more primes between `N` and `2N`.** `π(2N) − π(N)` is unbounded: for every `B`
there is `N` with more than `B` primes in `(N, 2N]`. Proof: eventually `π(2N)/π(N) > 3/2`
(`primeCount_two_mul_div_tendsto`), so `π(2N) − π(N) > π(N)/2`, and `π(N) → ∞`. -/
theorem primeCount_two_mul_sub_unbounded (B : Nat) :
    ∃ N, B < primeCount (2 * N) - primeCount N := by
  obtain ⟨N₁, hN₁⟩ := primeCount_two_mul_div_tendsto (1 / 2) (by grind)
  obtain ⟨N₂, hN₂⟩ := primeCount_unbounded (2 * B + 2)
  let N := max (max N₁ N₂) 2
  refine ⟨N, ?_⟩
  have hbig : 2 * B + 2 ≤ primeCount N := Nat.le_trans hN₂ (primeCount_mono (by omega))
  have hr := OF.abs_lt.1 (hN₁ N (by omega))
  have hp1 : (0 : R) < (primeCount N : R) := natCast_pos' (by omega)
  have hlt : 3 / 2 < (primeCount (2 * N) : R) / (primeCount N : R) := by grind
  have hm := OrderedRing.mul_lt_mul_of_pos_left hlt hp1
  have e : (primeCount N : R) * ((primeCount (2 * N) : R) / (primeCount N : R)) =
      (primeCount (2 * N) : R) := by
    have : (primeCount N : R) ≠ 0 := by grind
    rw [Field.div_eq_mul_inv]
    have : (primeCount N : R) * (primeCount N : R)⁻¹ = 1 := Field.mul_inv_cancel this
    grind
  rw [e] at hm
  have key : 3 * primeCount N + 1 ≤ 2 * primeCount (2 * N) := by
    apply Classical.byContradiction; intro hc
    have := PNT.natCast_le_iff.2 (show 2 * primeCount (2 * N) ≤ 3 * primeCount N by omega)
    rw [PNT.natCast_mul', PNT.natCast_mul'] at this
    rw [show ((2 : Nat) : R) = 2 by grind, show ((3 : Nat) : R) = 3 by grind] at this
    grind
  omega

/-! ## Dirichlet's theorem in Euler's form -/

section DirichletEuler

open Foundations.Algebra Foundations.Algebra.FiniteType
open Foundations.Numbers.C (ofReal)

attribute [local instance] Classical.propDecidable

variable {q : Nat} [NeZero q]

/-- **The `Λ`-sum over a residue class is unbounded.** For `a` coprime to `q`,
`Σ_{n ≤ N, n ≡ a (q)} Λ(n)/n` exceeds every bound. This is the quantitative content of the proof
of `dirichlet_of_nonvanishing` (with `L(1, χ) ≠ 0` now proved, `Lone_ne_zero`): by the sieve,
`φ(q)` times this sum is at least `log N − 1 − 2q − (number of characters) · B`. -/
theorem residue_vonMangoldt_unbounded (a : Nat) (ha : Nat.Coprime a q) (X : R) :
    ∃ N, X ≤ gsum (fun n => if n % q = a % q then vonMangoldt n / (n : R) else 0) (N + 1) := by
  obtain ⟨B, hB⟩ := exists_uniform_bound (FiniteType.elems : List (Character (ZModUnits q)))
    (fun χ N => if χ = Character.one then 0 else C.cabs (chebSum χ N)) (fun χ _ => by
      by_cases hχ : χ = Character.one
      · exact ⟨0, fun N _ => by rw [ite_eq_left hχ]; grind⟩
      · obtain ⟨B, hB⟩ := chebSum_bounded χ hχ (Lone_ne_zero χ hχ)
        exact ⟨B, fun N hN => by rw [ite_eq_right hχ]; exact hB N hN⟩)
  have hB0 : 0 ≤ B := by
    have := hB Character.one (FiniteType.complete _) 1 (by omega)
    rw [ite_eq_left rfl] at this; exact this
  obtain ⟨N, hN, hlog⟩ := exists_lnat_gt ((totient q : R) * X + 1 + 2 * (q : R) +
    (card (Character (ZModUnits q)) : R) * B)
  refine ⟨N, ?_⟩
  let F : Character (ZModUnits q) → C := fun χ => C.conj (dchar χ a) * chebSum χ N
  let F₁ : Character (ZModUnits q) → C := fun χ => if χ = Character.one then 0 else F χ
  have hsieve := sum_conj_mul_chebSum a ha N
  have hdec : sumOver F = F Character.one + sumOver F₁ := by
    have e : sumOver F = sumOver (fun χ => (if χ = Character.one then F Character.one else 0) + F₁ χ) := by
      unfold sumOver; apply lsum_congr; intro χ _
      by_cases hχ : χ = Character.one
      · subst hχ; show F _ = (if _ then _ else _) + (if _ then _ else _)
        rw [ite_eq_left rfl, ite_eq_left rfl]; grind
      · show F χ = (if _ then _ else _) + (if _ then _ else _)
        rw [ite_eq_right hχ, ite_eq_right hχ]; grind
    rw [e]; unfold sumOver; rw [lsum_add]
    have := sumOver_single (Character.one : Character (ZModUnits q))
      (fun χ => if χ = Character.one then F Character.one else 0)
      (fun χ hχ => ite_eq_right hχ)
    unfold sumOver at this; rw [this, ite_eq_left rfl]
  have hone : F Character.one = ofReal (gsum (fun n => if Nat.Coprime n q then
      vonMangoldt n / (n : R) else 0) (N + 1)) := by
    show C.conj (dchar Character.one a) * chebSum Character.one N = _
    rw [chebSum_one, dchar_one_char, ite_eq_left ha]
    show C.conj 1 * _ = _
    rw [show C.conj 1 = 1 from C.ext rfl (by show -(0 : R) = 0; grind)]; grind
  have hF₁ : C.cabs (sumOver F₁) ≤ (card (Character (ZModUnits q)) : R) * B := by
    apply cabs_lsum_le; intro χ _
    show C.cabs (if χ = Character.one then 0 else F χ) ≤ B
    by_cases hχ : χ = Character.one
    · rw [ite_eq_left hχ, C.cabs_zero]; exact hB0
    · rw [ite_eq_right hχ]
      show C.cabs (C.conj (dchar χ a) * chebSum χ N) ≤ B
      rw [C.cabs_mul, cabs_conj]
      have h1 := cabs_dchar_le χ a
      have h2 := hB χ (FiniteType.complete _) N hN
      rw [ite_eq_right hχ] at h2
      have := OrderedRing.mul_le_mul_of_nonneg_right h1 (C.cabs_nonneg (chebSum χ N))
      grind
  have hre := congrArg C.re hsieve
  rw [show sumOver (fun χ : Character (ZModUnits q) => C.conj (dchar χ a) * chebSum χ N) =
    sumOver F from rfl, hdec, C.add_re, hone] at hre
  have hre1 : (ofReal (gsum (fun n => if Nat.Coprime n q then vonMangoldt n / (n : R) else 0)
      (N + 1))).re = gsum (fun n => if Nat.Coprime n q then vonMangoldt n / (n : R) else 0) (N + 1) := rfl
  have hre2 : (ofReal ((totient q : R) * gsum (fun n => if n % q = a % q then vonMangoldt n / (n : R)
      else 0) (N + 1))).re = (totient q : R) * gsum (fun n => if n % q = a % q then
      vonMangoldt n / (n : R) else 0) (N + 1) := rfl
  rw [hre1, hre2] at hre
  have h1 := principal_lower (q := q) hN
  have h2 := OF.le_abs (sumOver F₁).re
  have h3 := C.abs_re_le_cabs (sumOver F₁)
  apply Classical.byContradiction; intro hlt
  have h5 := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt (Std.not_le.1 hlt))
    (OrderedRing.natCast_nonneg : (0 : R) ≤ (totient q : R))
  grind

omit [NeZero q] in
/-- **Prime powers add at most `4`.** The `Λ`-sum over a residue class exceeds the corresponding
sum over primes, `Σ_{p ≤ N, p ≡ a (q)} log p / p`, by at most `4`. -/
theorem residue_sum_le_primes (a N : Nat) :
    gsum (fun n => if n % q = a % q then vonMangoldt n / (n : R) else 0) (N + 1) ≤
      gsum (fun p => if Prime p ∧ p % q = a % q then lnat p / (p : R) else 0) (N + 1) + 4 := by
  have e : gsum (fun n => if n % q = a % q then vonMangoldt n / (n : R) else 0) (N + 1) =
      gsum (fun n => vonMangoldt n * (if n % q = a % q then 1 / (n : R) else 0)) (N + 1) :=
    gsum_congr fun n _ => by split <;> grind
  rw [e, gsum_vonMangoldt_mul]
  have hdivnn : ∀ p, 0 ≤ lnat p / (p : R) := fun p => by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; unfold lnat; rw [ite_eq_left rfl, Field.div_eq_mul_inv]; grind
    · have := div_le_div_of_le (lnat_nonneg p) (natCast_pos' h)
      rw [show (0 : R) / (p : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this
      exact this
  let A : Nat → Nat → R := fun p k =>
    if k = 1 then (if Prime p ∧ p % q = a % q then lnat p / (p : R) else 0) else 0
  let Bt : Nat → Nat → R := fun p k =>
    if Prime p ∧ 2 ≤ k ∧ p ^ k ≤ N then lnat p / ((p ^ k : Nat) : R) else 0
  have hterm : ∀ p k, (if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then
      lnat p * (if p ^ k % q = a % q then 1 / ((p ^ k : Nat) : R) else 0) else 0) ≤ A p k + Bt p k := by
    intro p k
    have hA : 0 ≤ A p k := by
      show 0 ≤ (if k = 1 then _ else _); split
      · split
        · exact hdivnn p
        · grind
      · grind
    have hB : 0 ≤ Bt p k := by
      show 0 ≤ (if Prime p ∧ 2 ≤ k ∧ p ^ k ≤ N then _ else _)
      split
      · next hc =>
        have := div_le_div_of_le (lnat_nonneg p) (natCast_pos' (Nat.pow_pos (n := k)
          (show 0 < p by have := hc.1.1; omega)))
        rw [show (0 : R) / ((p ^ k : Nat) : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this
        exact this
      · grind
    by_cases hc : Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N
    · rw [ite_eq_left hc]
      by_cases hm : p ^ k % q = a % q
      · rw [ite_eq_left hm]
        by_cases hk : k = 1
        · subst hk
          rw [Nat.pow_one] at hm ⊢
          have : A p 1 = lnat p / (p : R) := by
            show (if 1 = 1 then (if Prime p ∧ p % q = a % q then lnat p / (p : R) else 0) else 0) = _
            rw [ite_eq_left rfl, ite_eq_left ⟨hc.1, hm⟩]
          rw [this]
          have : lnat p * (1 / (p : R)) = lnat p / (p : R) := by
            rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
          grind
        · have : Bt p k = lnat p / ((p ^ k : Nat) : R) := ite_eq_left ⟨hc.1, by omega, hc.2.2⟩
          rw [this]
          have : lnat p * (1 / ((p ^ k : Nat) : R)) = lnat p / ((p ^ k : Nat) : R) := by
            rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]; grind
          grind
      · rw [ite_eq_right hm]; grind
    · rw [ite_eq_right hc]; grind
  have h1 := gsum_le_gsum (n := N + 1) (fun p _ => gsum_le_gsum (n := N + 1) (fun k _ => hterm p k))
  simp only [gsum_add] at h1
  have h2 : gsum (fun p => gsum (fun k => A p k) (N + 1)) (N + 1) =
      gsum (fun p => if Prime p ∧ p % q = a % q then lnat p / (p : R) else 0) (N + 1) := by
    apply gsum_congr; intro p _
    show gsum (fun k => if k = 1 then (if Prime p ∧ p % q = a % q then lnat p / (p : R) else 0)
      else 0) (N + 1) = _
    rw [gsum_ite_eq 1 (N + 1) (fun _ => if Prime p ∧ p % q = a % q then lnat p / (p : R) else 0)]
    by_cases hN : 1 < N + 1
    · rw [ite_eq_left hN]
    · have hp0 : ¬ (Prime p ∧ p % q = a % q) := fun h => by have := h.1.1; omega
      rw [ite_eq_right hN, ite_eq_right hp0]
  have h3 := prime_power_sum_le N
  have e2 : gsum (fun p => gsum (fun k => A p k + Bt p k) (N + 1)) (N + 1) =
      gsum (fun p => gsum (fun k => A p k) (N + 1)) (N + 1) +
        gsum (fun p => gsum (fun k => Bt p k) (N + 1)) (N + 1) := by
    rw [← gsum_add]; apply gsum_congr; intro p _; rw [gsum_add]
  grind

end DirichletEuler

/-- **Dirichlet's theorem in Euler's form.** For `q ≥ 1` and `a` coprime to `q`, the sum
`Σ_{p ≤ N, p ≡ a (mod q)} log p / p` is unbounded — the primes in the progression are not only
infinite in number but, weighted by `log p / p`, as plentiful as Mertens' theorem allows
(compare Euler's `Σ 1/p = ∞` for `q = 1`). -/
theorem dirichlet_euler {q : Nat} (hq : 0 < q) {a : Nat} (ha : Nat.Coprime a q) (X : R) :
    ∃ N : Nat, X ≤ fsum (fun p => if Prime p ∧ p % q = a % q then
      R.log (p : R) / (p : R) else 0) (N + 1) := by
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨N, hN⟩ := residue_vonMangoldt_unbounded a ha (X + 4)
  refine ⟨N, ?_⟩
  have h := residue_sum_le_primes (q := q) a N
  have e : fsum (fun p => if Prime p ∧ p % q = a % q then R.log (p : R) / (p : R) else 0) (N + 1) =
      gsum (fun p => if Prime p ∧ p % q = a % q then lnat p / (p : R) else 0) (N + 1) := by
    rw [fsum_eq_gsum]; apply gsum_congr; intro p _
    by_cases hp : Prime p ∧ p % q = a % q
    · rw [ite_eq_left hp, ite_eq_left hp, lnat_prime hp.1]
    · rw [ite_eq_right hp, ite_eq_right hp]
  rw [e]; grind

end Foundations.NumberTheory
