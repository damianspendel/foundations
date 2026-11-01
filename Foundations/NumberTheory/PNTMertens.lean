import Foundations.NumberTheory.PNTEquivalence

/-!
# Toward the prime number theorem IV: Mertens' theorems

Franz **Mertens** proved in 1874, by elementary means, that the primes are distributed "on
average" exactly as the prime number theorem predicts, when weighted by `1/p`:

  `Σ_{n ≤ N} Λ(n)/n = log N + O(1)`   and   `Σ_{p ≤ N} log p / p = log N + O(1)`.

These are much weaker than `ψ(N) ∼ N` (they would follow from it by partial summation, but not
conversely), yet they are the foundation of every elementary approach, including Selberg's.

The proof rests on one identity and one estimate.

* **The identity** `log N! = Σ_{pᵏ ≤ N} ⌊N/pᵏ⌋ · log p`, i.e. `log N! = Σ_{d ≤ N} Λ(d) ⌊N/d⌋`.
  It combines unique factorisation in additive form, `log m = Σ_p vₚ(m) log p`, with
  **Legendre's formula** `vₚ(N!) = Σ_k ⌊N/pᵏ⌋` from the `Binomial` file.
* **The estimate** `N log N − N ≤ log N! ≤ N log N` (a crude form of Stirling's formula, from
  `N! ≤ Nᴺ` and `Nᴺ/N! ≤ eᴺ`).

Replacing `⌊N/d⌋` by `N/d` costs at most `Σ_{d ≤ N} Λ(d) = ψ(N) ≤ N log 1024` (previous files).
Dividing by `N`: `−1 ≤ Σ_{n ≤ N} Λ(n)/n − log N ≤ log 1024`.

For the second theorem one removes the higher prime powers: their contribution
`Σ_p Σ_{k ≥ 2} log p / pᵏ ≤ Σ_p log p / (p(p−1))` is bounded by `2`, by comparison with the
telescoping sum of `(2 + log n)/n`.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-! ## Prime power sums -/

/-- Prime power sums are additive. -/
theorem ppSum_add (f g : Nat → Nat → R) (N : Nat) :
    ppSum (fun p k => f p k + g p k) N = ppSum f N + ppSum g N := by
  unfold ppSum; rw [← fsum_add]
  apply fsum_congr; intro p _; rw [← fsum_add]
  apply fsum_congr; intro k _
  split <;> grind

/-- Prime power sums of differences. -/
theorem ppSum_sub (f g : Nat → Nat → R) (N : Nat) :
    ppSum (fun p k => f p k - g p k) N = ppSum f N - ppSum g N := by
  unfold ppSum; rw [← fsum_sub]
  apply fsum_congr; intro p _; rw [← fsum_sub]
  apply fsum_congr; intro k _
  split <;> grind

/-- Prime power sums are monotone (only the prime powers `pᵏ ≤ N` matter). -/
theorem ppSum_le {f g : Nat → Nat → R} {N : Nat}
    (h : ∀ p k, Prime p → 1 ≤ k → p ^ k ≤ N → f p k ≤ g p k) : ppSum f N ≤ ppSum g N := by
  unfold ppSum
  apply fsum_le_fsum'; intro p _; apply fsum_le_fsum'; intro k _
  split
  · next hh => exact h p k hh.1 hh.2.1 hh.2.2
  · grind

/-- **Prime power sums as sums over `n`.** `Σ_{pᵏ ≤ N} log p · g(pᵏ) = Σ_{n ≤ N} Λ(n) g(n)`. -/
theorem ppSum_eq_sum_vonMangoldt (g : Nat → R) (N : Nat) :
    ppSum (fun p k => R.log (p : R) * g (p ^ k)) N = fsum (fun n => vonMangoldt n * g n) (N + 1) := by
  let G : Nat → Nat → Nat → R := fun n p k =>
    if Prime p ∧ 1 ≤ k ∧ p ^ k = n then R.log (p : R) * g n else 0
  have ext : ∀ n, n < N + 1 → vonMangoldt n * g n =
      fsum (fun p => fsum (fun k => G n p k) (N + 1)) (N + 1) := by
    intro n hn
    unfold vonMangoldt
    rw [← fsum_mul_const]
    have hvan : ∀ p k, n + 1 ≤ p ∨ n + 1 ≤ k → G n p k = 0 := by
      intro p k hpk
      simp only [G]
      split
      · next h =>
        exfalso
        have hp2 := h.1.1
        have h1 : p ≤ p ^ k := by
          have := Nat.pow_le_pow_right (show 0 < p by omega) h.2.1; rwa [Nat.pow_one] at this
        have := lt_pow_self' hp2 k
        omega
      · rfl
    have inner : ∀ p, fsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k = n then R.log (p : R) else 0)
        (n + 1) * g n = fsum (fun k => G n p k) (n + 1) := by
      intro p; rw [← fsum_mul_const]
      apply fsum_congr; intro k _; simp only [G]; split <;> grind
    rw [fsum_congr (fun p _ => inner p)]
    rw [fsum_congr_bound (show n + 1 ≤ N + 1 by omega) (fun p h1 _ => by
      rw [fsum_congr (b := fun _ => 0) (fun k _ => hvan p k (Or.inl h1)), fsum_zeros])]
    apply fsum_congr; intro p _
    exact fsum_congr_bound (show n + 1 ≤ N + 1 by omega) (fun k h1 _ => hvan p k (Or.inr h1))
  rw [fsum_congr ext, fsum_swap]
  unfold ppSum
  apply fsum_congr; intro p _
  rw [fsum_swap]
  apply fsum_congr; intro k _
  rw [fsum_congr (b := fun n => if n = p ^ k then
      (if Prime p ∧ 1 ≤ k then R.log (p : R) * g (p ^ k) else 0) else 0) (fun n _ => by
    simp only [G]
    by_cases h : n = p ^ k
    · subst h; by_cases h' : Prime p ∧ 1 ≤ k <;> simp [h']
    · have : ¬ (Prime p ∧ 1 ≤ k ∧ p ^ k = n) := fun h' => h h'.2.2.symm
      simp only [this, h, ↓reduceIte])]
  rw [fsum_ite_eq]
  by_cases h1 : Prime p ∧ 1 ≤ k <;> by_cases h2 : p ^ k ≤ N <;>
    simp [h1, h2, show (p ^ k < N + 1) ↔ p ^ k ≤ N by omega]

/-! ## Unique factorisation, additively -/

/-- `vₚ(q)` for primes: `1` if `p = q`, else `0`. -/
theorem vp_prime {p q : Nat} (hp : Prime p) (hq : Prime q) : vp p q = if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst h; simp only [↓reduceIte]
    exact vp_eq (r := 1) hp.1 (by simp) (fun h => by
      have := Nat.le_of_dvd (by omega) h; have := hp.1; omega)
  · simp only [h, ↓reduceIte]
    exact vp_eq (r := q) hp.1 (by simp) (fun hd => by
      rcases hq.2 p hd with h1 | h1
      · have := hp.1; omega
      · exact h h1)

/-- **Unique factorisation, additive form.** For `1 ≤ m < B`: `log m = Σ_{p < B} vₚ(m) log p`. -/
theorem log_eq_sum_vp (B : Nat) : ∀ m, 1 ≤ m → m < B →
    R.log (m : R) = fsum (fun p => if Prime p then (vp p m : R) * R.log (p : R) else 0) B := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm hmB
    by_cases h1 : m = 1
    · subst h1
      rw [show ((1 : Nat) : R) = 1 by grind, R.log_one]
      rw [fsum_congr (b := fun _ => 0) (fun p _ => by
        split
        · next hp => rw [vp_one hp.1]; grind
        · rfl), fsum_zeros]
    · obtain ⟨q, hq, hqm⟩ := exists_prime_dvd (show 2 ≤ m by omega)
      obtain ⟨m', rfl⟩ := hqm
      have hq2 := hq.1
      have hm' : 1 ≤ m' := by
        rcases Nat.eq_zero_or_pos m' with h | h
        · subst h; omega
        · exact h
      have hlt : m' < q * m' := by
        have : 2 * m' ≤ q * m' := Nat.mul_le_mul_right m' hq2
        omega
      have ihm := ih m' hlt hm' (by omega)
      rw [natCast_mul', R.log_mul (natCast_pos' (by omega)) (natCast_pos' hm'), ihm]
      have hqB : q < B := by
        have : q ≤ q * m' := Nat.le_mul_of_pos_right q hm'
        omega
      have hq_sum : R.log (q : R) =
          fsum (fun p => if Prime p then (vp p q : R) * R.log (p : R) else 0) B := by
        rw [fsum_congr (b := fun p => if p = q then R.log (q : R) else 0) (fun p _ => by
          by_cases hp : Prime p
          · simp only [hp, ↓reduceIte, vp_prime hp hq]
            by_cases hpq : p = q
            · subst hpq; simp only [↓reduceIte]; grind
            · simp only [hpq, ↓reduceIte]; grind
          · have : p ≠ q := fun h => hp (h ▸ hq)
            simp only [hp, this, ↓reduceIte])]
        rw [fsum_ite_eq]; simp only [hqB, ↓reduceIte]
      rw [hq_sum, ← fsum_add]
      apply fsum_congr; intro p _
      by_cases hp : Prime p
      · simp only [hp, ↓reduceIte]
        rw [vp_mul hp (by omega) hm', natCast_add']; grind
      · simp only [hp, ↓reduceIte]; grind

/-! ## The logarithm of `N!` -/

/-- The Legendre sum as a real sum: `Σ_{1 ≤ k ≤ K} ⌊n/pᵏ⌋`. -/
theorem natCast_legendreSum (p n : Nat) : ∀ K,
    (legendreSum p n K : R) = fsum (fun k => if 1 ≤ k then ((n / p ^ k : Nat) : R) else 0) (K + 1)
  | 0 => by
    show ((0 : Nat) : R) = fsum _ 0 + _
    simp only [Nat.le_zero, Nat.one_ne_zero, ↓reduceIte, fsum_zero]; grind
  | K + 1 => by
    rw [fsum_succ, ← natCast_legendreSum p n K]
    simp only [legendreSum, show 1 ≤ K + 1 by omega, ↓reduceIte]
    grind

/-- **`log N! = Σ_{pᵏ ≤ N} ⌊N/pᵏ⌋ · log p`** (unique factorisation plus Legendre's formula). -/
theorem log_fact_eq (N : Nat) :
    R.log (Arith.fact N : R) = ppSum (fun p k => ((N / p ^ k : Nat) : R) * R.log (p : R)) N := by
  rw [log_eq_sum_vp (Arith.fact N + 1) (Arith.fact N) (Arith.fact_pos N) (by omega)]
  -- Primes above `N` do not divide `N!`.
  have hle : N + 1 ≤ Arith.fact N + 1 := by
    have : N ≤ Arith.fact N := by
      induction N with
      | zero => simp [Arith.fact]
      | succ n ih =>
        show n + 1 ≤ (n + 1) * Arith.fact n
        have := Arith.fact_pos n
        exact Nat.le_mul_of_pos_right _ this
    omega
  rw [← fsum_congr_bound hle (fun p h1 _ => by
    split
    · next hp =>
      have : vp p (Arith.fact N) = 0 := by
        apply Classical.byContradiction; intro h0
        have hd := (pow_dvd_iff_le_vp (e := 1) hp.1 (Arith.fact_pos N)).2 (by omega)
        rw [Nat.pow_one] at hd
        have := prime_le_of_dvd_fact hp hd
        omega
      rw [this]; grind
    · rfl)]
  unfold ppSum
  apply fsum_congr; intro p _
  by_cases hp : Prime p
  · simp only [hp, true_and, ↓reduceIte]
    rw [legendre' hp N, natCast_legendreSum, ← fsum_mul_const]
    apply fsum_congr; intro k _
    by_cases hk : 1 ≤ k
    · simp only [hk, true_and, ↓reduceIte]
      by_cases hpk : p ^ k ≤ N
      · simp only [hpk, ↓reduceIte]
      · simp only [hpk, ↓reduceIte]
        rw [Nat.div_eq_of_lt (by omega)]; grind
    · simp only [hk, false_and, ↓reduceIte]; grind
  · simp only [hp, false_and, ↓reduceIte]
    exact (fsum_zeros _).symm

/-! ## Mertens' first theorem -/

/-- The fractional part `N/d − ⌊N/d⌋` lies in `[0, 1)`. -/
theorem div_sub_floor {N d : Nat} (hd : 0 < d) :
    0 ≤ (N : R) / (d : R) - ((N / d : Nat) : R) ∧ (N : R) / (d : R) - ((N / d : Nat) : R) ≤ 1 := by
  have hdm := Nat.div_add_mod N d
  have hlt := Nat.mod_lt N hd
  have hd0 : (0 : R) < (d : R) := natCast_pos' hd
  have hdne : (d : R) ≠ 0 := by grind
  have e : (N : R) = (d : R) * ((N / d : Nat) : R) + ((N % d : Nat) : R) := by
    rw [← natCast_mul', ← natCast_add', hdm]
  have hr0 := natCast_nonneg' (N % d)
  have hr1 : ((N % d : Nat) : R) ≤ (d : R) := natCast_le' (by omega)
  have e2 : (N : R) / (d : R) - ((N / d : Nat) : R) = ((N % d : Nat) : R) / (d : R) := by
    rw [e]; grind
  rw [e2]
  have hi : 0 ≤ (d : R)⁻¹ := by have := div_pos (show (0 : R) < 1 by grind) hd0; grind
  have k1 := OrderedRing.mul_le_mul_of_nonneg_right hr1 hi
  have k2 := OrderedRing.mul_le_mul_of_nonneg_right hr0 hi
  constructor <;> grind

/-- **Mertens' first theorem.** For `N ≥ 1`,
`−1 ≤ Σ_{n ≤ N} Λ(n)/n − log N ≤ log 1024`, i.e. `Σ_{n ≤ N} Λ(n)/n = log N + O(1)`. -/
theorem mertens_vonMangoldt {N : Nat} (hN : 1 ≤ N) :
    -1 ≤ fsum (fun n => vonMangoldt n * (1 / (n : R))) (N + 1) - R.log (N : R) ∧
      fsum (fun n => vonMangoldt n * (1 / (n : R))) (N + 1) - R.log (N : R) ≤ R.log 1024 := by
  rw [← ppSum_eq_sum_vonMangoldt]
  have hN0 : (0 : R) < (N : R) := natCast_pos' hN
  let S := ppSum (fun p k => R.log (p : R) * (1 / ((p ^ k : Nat) : R))) N
  -- `N · S − log N! = Σ (N/pᵏ − ⌊N/pᵏ⌋) log p ∈ [0, ψ(N)]`.
  have eNS : (N : R) * S = ppSum (fun p k => (N : R) / ((p ^ k : Nat) : R) * R.log (p : R)) N := by
    show (N : R) * ppSum _ N = _
    unfold ppSum; rw [← fsum_const_mul]
    apply fsum_congr; intro p _; rw [← fsum_const_mul]
    apply fsum_congr; intro k _
    split <;> grind
  have hE := ppSum_sub (fun p k => (N : R) / ((p ^ k : Nat) : R) * R.log (p : R))
    (fun p k => ((N / p ^ k : Nat) : R) * R.log (p : R)) N
  rw [← eNS, ← log_fact_eq] at hE
  have hE0 : ppSum (fun _ _ => (0 : R)) N ≤ (N : R) * S - R.log (Arith.fact N : R) := by
    rw [← hE]
    apply ppSum_le; intro p k hp hk _
    have := (div_sub_floor (N := N) (Nat.pow_pos (n := k) (show 0 < p by have := hp.1; omega))).1
    have hl := log_natCast_nonneg (n := p) (by have := hp.1; omega)
    have := OrderedRing.mul_nonneg this hl
    grind
  have hz : ppSum (fun _ _ => (0 : R)) N = 0 := by
    unfold ppSum
    rw [fsum_congr (b := fun _ => 0) (fun p _ => by
      rw [fsum_congr (b := fun _ => 0) (fun k _ => by split <;> rfl), fsum_zeros]), fsum_zeros]
  rw [hz] at hE0
  have hE1 : (N : R) * S - R.log (Arith.fact N : R) ≤ psi N := by
    rw [← hE]; unfold psi
    apply ppSum_le; intro p k hp hk _
    have := (div_sub_floor (N := N) (Nat.pow_pos (n := k) (show 0 < p by have := hp.1; omega))).2
    have hl := log_natCast_nonneg (n := p) (by have := hp.1; omega)
    have := OrderedRing.mul_le_mul_of_nonneg_right this hl
    grind
  have hpsi := psi_le N
  have hs1 := log_fact_le N
  have hs2 := log_fact_ge N
  rw [arith_fact_eq] at hs1 hs2 hE0 hE1
  -- Divide `−N ≤ N S − N log N ≤ N log 1024` by `N`.
  have h1 : (N : R) * (-1) ≤ (N : R) * (S - R.log (N : R)) := by grind
  have h2 : (N : R) * (S - R.log (N : R)) ≤ (N : R) * R.log 1024 := by grind
  constructor
  · exact le_of_mul_le_mul_right' (by grind) hN0
  · exact le_of_mul_le_mul_right' (by grind) hN0

/-! ## Mertens' second theorem -/

/-- `(1/a)ᵏ = 1/aᵏ`. -/
theorem one_div_pow' {a : R} (ha : 0 < a) : ∀ k : Nat, (1 / a) ^ k = 1 / a ^ k
  | 0 => by show (1 : R) = 1 / 1; grind
  | k + 1 => by
    show (1 / a) ^ k * (1 / a) = 1 / (a ^ k * a)
    rw [one_div_pow' ha k]
    have := (pow_pos_and_log_pow ha k).1
    have : a ^ k ≠ 0 := by grind
    have : a ≠ 0 := by grind
    grind

/-- A geometric tail: `(1 − x) Σ_{2 ≤ k < K} xᵏ = x² − x^K` for `K ≥ 2`. -/
theorem geom_tail (x : R) : ∀ K, (1 - x) * fsum (fun k => if 2 ≤ k then x ^ k else 0) K =
    if 2 ≤ K then x ^ 2 - x ^ K else 0
  | 0 => by simp only [fsum_zero]; grind
  | K + 1 => by
    rw [fsum_succ]
    have ih := geom_tail x K
    by_cases hK : 2 ≤ K
    · simp only [hK, show 2 ≤ K + 1 by omega, ↓reduceIte] at ih ⊢
      have e : x ^ (K + 1) = x ^ K * x := rfl
      grind
    · by_cases hK1 : K = 1
      · subst hK1
        simp only [show ¬ 2 ≤ 1 by omega, ↓reduceIte] at ih ⊢
        simp only [Nat.reduceAdd, Nat.le_refl, ↓reduceIte]; grind
      · simp only [hK, show ¬ 2 ≤ K + 1 by omega, ↓reduceIte] at ih ⊢; grind

/-- For a prime `p`, the higher powers contribute little:
`Σ_{2 ≤ k ≤ N} 1/pᵏ ≤ 1/(p(p−1))`, in the form `p (p − 1) Σ ≤ 1`. -/
theorem prime_pow_tail_le {p : Nat} (hp : 2 ≤ p) (K : Nat) :
    (p : R) * ((p : R) - 1) *
      fsum (fun k => if 2 ≤ k then 1 / ((p ^ k : Nat) : R) else 0) K ≤ 1 := by
  have hp0 : (0 : R) < (p : R) := natCast_pos' (by omega)
  have hp1 : (2 : R) ≤ (p : R) := by
    have := show ((2 : Nat) : R) ≤ (p : R) from natCast_le' hp; grind
  obtain ⟨x, hxd⟩ : ∃ x : R, x = 1 / (p : R) := ⟨_, rfl⟩
  have hx : (p : R) * x = 1 := by
    have : (p : R) ≠ 0 := by grind
    rw [hxd]; grind
  have hx0 : 0 < x := by rw [hxd]; exact div_pos (show (0 : R) < 1 by grind) hp0
  have e : fsum (fun k => if 2 ≤ k then 1 / ((p ^ k : Nat) : R) else 0) K =
      fsum (fun k => if 2 ≤ k then x ^ k else 0) K := by
    apply fsum_congr; intro k _
    rw [natCast_pow', hxd, one_div_pow' hp0]
  rw [e]
  have g := geom_tail x K
  generalize fsum (fun k => if 2 ≤ k then x ^ k else 0) K = F at g ⊢
  have hxK : 0 ≤ x ^ K := by have := (pow_pos_and_log_pow hx0 K).1; grind
  have e2 : x ^ 2 = x * x := by show 1 * x * x = x * x; grind
  have hgx : (1 - x) * F ≤ x * x := by
    rw [g]; split
    · grind
    · have := OrderedRing.mul_nonneg (Std.le_of_lt hx0) (Std.le_of_lt hx0); grind
  have hpp : 0 ≤ (p : R) * (p : R) := OrderedRing.mul_nonneg (Std.le_of_lt hp0) (Std.le_of_lt hp0)
  have := OrderedRing.mul_le_mul_of_nonneg_left hgx hpp
  have e3 : (p : R) * (p : R) * ((1 - x) * F) = (p : R) * ((p : R) - 1) * F := by grind
  have e4 : (p : R) * (p : R) * (x * x) = 1 := by grind
  grind

/-- The comparison function `g(n) = (2 + log n)/n` of the telescoping argument. -/
noncomputable def mertensG (n : Nat) : R := (2 + R.log (n : R)) / (n : R)

/-- `g(n) ≥ 0` for `n ≥ 1`. -/
theorem mertensG_nonneg {n : Nat} (hn : 1 ≤ n) : 0 ≤ mertensG n := by
  unfold mertensG
  have := log_natCast_nonneg hn
  exact Std.le_of_lt (div_pos (by grind) (natCast_pos' hn))

/-- **The telescoping estimate.** For `m ≥ 1`: `log(m+1) ≤ (m+1) m (g(m) − g(m+1))`, i.e.
`log(m+1)/((m+1)m) ≤ g(m) − g(m+1)`. It reduces to `(m+1)(log(m+1) − log m) ≤ 2`, which follows
from `log y ≤ y − 1` at `y = (m+1)/m`. -/
theorem log_le_mertensG {m : Nat} (hm : 1 ≤ m) :
    R.log ((m + 1 : Nat) : R) ≤ ((m + 1 : Nat) : R) * (m : R) * (mertensG m - mertensG (m + 1)) := by
  have hu0 : (0 : R) < (m : R) := natCast_pos' hm
  have hu1 : (1 : R) ≤ (m : R) := one_le_natCast hm
  have ec : ((m + 1 : Nat) : R) = (m : R) + 1 := by grind
  have hv0 : (0 : R) < (m : R) + 1 := by grind
  have hD : R.log ((m + 1 : Nat) : R) - R.log (m : R) ≤ 1 / (m : R) := by
    have hy : (1 : R) ≤ ((m + 1 : Nat) : R) / (m : R) := by
      rw [ec]; have : (m : R) ≠ 0 := by grind
      have e : ((m : R) + 1) / (m : R) = 1 + 1 / (m : R) := by grind
      rw [e]; have := div_pos (show (0 : R) < 1 by grind) hu0; grind
    have := log_le_sub_one hy
    rw [log_div' (natCast_pos' (by omega)) hu0] at this
    have e : ((m + 1 : Nat) : R) / (m : R) - 1 = 1 / (m : R) := by
      rw [ec]; have : (m : R) ≠ 0 := by grind
      grind
    grind
  have hD0 : 0 ≤ R.log ((m + 1 : Nat) : R) - R.log (m : R) := by
    have := log_le_log hu0 (show (m : R) ≤ ((m + 1 : Nat) : R) by rw [ec]; grind); grind
  -- `m · D ≤ 1`, hence `(m + 1) D ≤ 2`.
  have hmD : (m : R) * (R.log ((m + 1 : Nat) : R) - R.log (m : R)) ≤ 1 := by
    have := OrderedRing.mul_le_mul_of_nonneg_left hD (Std.le_of_lt hu0)
    have e : (m : R) * (1 / (m : R)) = 1 := by have : (m : R) ≠ 0 := by grind
                                               grind
    grind
  have hD1 : R.log ((m + 1 : Nat) : R) - R.log (m : R) ≤ 1 := by
    have := OrderedRing.mul_le_mul_of_nonneg_right hu1 hD0; grind
  have key : ((m + 1 : Nat) : R) * (m : R) * (mertensG m - mertensG (m + 1)) =
      ((m : R) + 1) * (2 + R.log (m : R)) - (m : R) * (2 + R.log ((m + 1 : Nat) : R)) := by
    unfold mertensG; rw [ec]
    have : (m : R) ≠ 0 := by grind
    have : (m : R) + 1 ≠ 0 := by grind
    grind
  rw [key]; grind

/-- The telescoping sum: `Σ_{2 ≤ n ≤ N} (g(n−1) − g(n)) = g(1) − g(N)` for `N ≥ 1`. -/
theorem fsum_mertensG {N : Nat} (hN : 1 ≤ N) :
    fsum (fun n => if 2 ≤ n then mertensG (n - 1) - mertensG n else 0) (N + 1) =
      mertensG 1 - mertensG N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN'
    · simp only [fsum_succ, fsum_zero]
      simp only [show ¬ 2 ≤ 0 by omega, show ¬ 2 ≤ 1 by omega, ↓reduceIte]; grind
    · rw [fsum_succ, ih hN']
      simp only [show 2 ≤ N + 1 by omega, ↓reduceIte, show N + 1 - 1 = N by omega]; grind

/-- `g(1) = 2`. -/
theorem mertensG_one : mertensG 1 = 2 := by
  unfold mertensG; rw [show ((1 : Nat) : R) = 1 by grind, R.log_one]; grind

/-- **Mertens' second theorem.** For `N ≥ 1`,
`−3 ≤ Σ_{p ≤ N} log p / p − log N ≤ log 1024`, i.e. `Σ_{p ≤ N} log p / p = log N + O(1)`. -/
theorem mertens_primes {N : Nat} (hN : 1 ≤ N) :
    -3 ≤ fsum (fun p => if Prime p then R.log (p : R) * (1 / (p : R)) else 0) (N + 1) - R.log (N : R) ∧
      fsum (fun p => if Prime p then R.log (p : R) * (1 / (p : R)) else 0) (N + 1) - R.log (N : R)
        ≤ R.log 1024 := by
  have hM := mertens_vonMangoldt hN
  rw [← ppSum_eq_sum_vonMangoldt] at hM
  -- Per prime: the prime-power terms lie between `log p / p` and `log p / p + (g(p−1) − g(p))`.
  let tail : Nat → R := fun p => fsum (fun k => if 2 ≤ k then 1 / ((p ^ k : Nat) : R) else 0) (N + 1)
  have per : ∀ p, p < N + 1 → Prime p →
      R.log (p : R) * (1 / (p : R)) ≤
        fsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then
          R.log (p : R) * (1 / ((p ^ k : Nat) : R)) else 0) (N + 1) ∧
      fsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then
          R.log (p : R) * (1 / ((p ^ k : Nat) : R)) else 0) (N + 1) ≤
        R.log (p : R) * (1 / (p : R)) + (mertensG (p - 1) - mertensG p) := by
    intro p hp hpr
    have hp2 := hpr.1
    have hp0 : (0 : R) < (p : R) := natCast_pos' (by omega)
    have hl := log_natCast_nonneg (n := p) (by omega)
    have hterm : ∀ k, 0 ≤ R.log (p : R) * (1 / ((p ^ k : Nat) : R)) := fun k =>
      OrderedRing.mul_nonneg hl (Std.le_of_lt (div_pos (by grind) (natCast_pos' (Nat.pow_pos (by omega)))))
    have e1 : fsum (fun k => if k = 1 then R.log (p : R) * (1 / ((p ^ k : Nat) : R)) else 0) (N + 1)
        = R.log (p : R) * (1 / (p : R)) := by
      rw [fsum_ite_eq]; simp only [show 1 < N + 1 by omega, ↓reduceIte, Nat.pow_one]
    -- The tail bound `log p · tail ≤ g(p−1) − g(p)`.
    have htail0 : 0 ≤ tail p := by
      apply fsum_nonneg; intro k; split
      · exact Std.le_of_lt (div_pos (by grind) (natCast_pos' (Nat.pow_pos (by omega))))
      · grind
    have ht := prime_pow_tail_le hp2 (N + 1)
    have hg := log_le_mertensG (m := p - 1) (by omega)
    rw [show p - 1 + 1 = p by omega] at hg
    have ec : ((p - 1 : Nat) : R) = (p : R) - 1 := by
      have : ((p - 1 + 1 : Nat) : R) = ((p - 1 : Nat) : R) + 1 := by grind
      rw [show p - 1 + 1 = p by omega] at this; grind
    rw [ec] at hg
    have hG0 : 0 ≤ mertensG (p - 1) - mertensG p := by
      apply Classical.byContradiction; intro h
      have hpp : 0 < (p : R) * ((p : R) - 1) :=
        OrderedRing.mul_pos hp0 (by
          have : ((2 : Nat) : R) ≤ (p : R) := natCast_le' (show 2 ≤ p by omega)
          grind)
      have := OrderedRing.mul_pos hpp (show 0 < -(mertensG (p - 1) - mertensG p) by grind)
      grind
    have hlt : R.log (p : R) * tail p ≤ mertensG (p - 1) - mertensG p := by
      have k1 := OrderedRing.mul_le_mul_of_nonneg_right hg htail0
      have k2 := OrderedRing.mul_le_mul_of_nonneg_left ht hG0
      grind
    constructor
    · rw [← e1]
      apply fsum_le_fsum'; intro k _
      by_cases hk : k = 1
      · subst hk; simp only [hpr, Nat.le_refl, Nat.pow_one, show p ≤ N by omega, and_self,
          ↓reduceIte]; grind
      · simp only [hk, ↓reduceIte]; split
        · exact hterm k
        · grind
    · have : fsum (fun k => if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then
          R.log (p : R) * (1 / ((p ^ k : Nat) : R)) else 0) (N + 1) ≤
          fsum (fun k => if k = 1 then R.log (p : R) * (1 / ((p ^ k : Nat) : R)) else 0) (N + 1) +
          R.log (p : R) * tail p := by
        simp only [tail]; rw [← fsum_const_mul, ← fsum_add]
        apply fsum_le_fsum'; intro k _
        by_cases hk : k = 1
        · subst hk; simp only [↓reduceIte, show ¬ 2 ≤ 1 by omega]; split <;> grind
        · by_cases hk2 : 2 ≤ k
          · simp only [hk, hk2, ↓reduceIte]; split <;> grind
          · have : k = 0 := by omega
            subst this; simp only [show ¬ 1 ≤ 0 by omega, false_and, and_false, ↓reduceIte,
              show ¬ 2 ≤ 0 by omega]; grind
      rw [e1] at this; grind
  -- Sum over the primes.
  let P := fsum (fun p => if Prime p then R.log (p : R) * (1 / (p : R)) else 0) (N + 1)
  have hlow : P ≤ ppSum (fun p k => R.log (p : R) * (1 / ((p ^ k : Nat) : R))) N := by
    unfold ppSum; apply fsum_le_fsum'; intro p hp
    by_cases hpr : Prime p
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hpr)]; exact (per p hp hpr).1
    · simp only [hpr, ↓reduceIte, false_and]; rw [fsum_zeros]; grind
  have hup : ppSum (fun p k => R.log (p : R) * (1 / ((p ^ k : Nat) : R))) N ≤ P + 2 := by
    have h1 : ppSum (fun p k => R.log (p : R) * (1 / ((p ^ k : Nat) : R))) N ≤
        P + fsum (fun n => if 2 ≤ n then mertensG (n - 1) - mertensG n else 0) (N + 1) := by
      unfold ppSum; simp only [P]; rw [← fsum_add]
      apply fsum_le_fsum'; intro p hp
      by_cases hpr : Prime p
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hpr), ite_eq_left_of_eq_true _ _ (eq_true hpr.1)]; exact (per p hp hpr).2
      · simp only [hpr, ↓reduceIte, false_and]; rw [fsum_zeros]
        split
        · next h2 =>
          have := log_le_mertensG (m := p - 1) (by omega)
          rw [show p - 1 + 1 = p by omega] at this
          have hpp : 0 < ((p : Nat) : R) * ((p - 1 : Nat) : R) :=
            OrderedRing.mul_pos (natCast_pos' (by omega)) (natCast_pos' (by omega))
          have hl := log_natCast_nonneg (n := p) (by omega)
          apply Classical.byContradiction; intro h
          have := OrderedRing.mul_pos hpp (show 0 < -(mertensG (p - 1) - mertensG p) by grind)
          grind
        · grind
    rw [fsum_mertensG hN, mertensG_one] at h1
    have := mertensG_nonneg hN
    grind
  constructor <;> grind

end Foundations.NumberTheory.PNT
