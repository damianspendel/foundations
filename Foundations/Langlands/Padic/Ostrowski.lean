import Foundations.Langlands.Padic.OstrowskiBound

/-!
# Ostrowski's theorem, II: the classification

**Ostrowski's theorem** (1916): every nontrivial absolute value on ℚ is equivalent to the
ordinary absolute value `|·|_∞` or to the `p`-adic absolute value `|·|ₚ` for exactly one
prime `p`.

So the *completions* of ℚ — the fields in which Cauchy sequences for some absolute value converge
— are ℝ and the fields ℚₚ, and nothing else. This is why number theory speaks of the *places*
`2, 3, 5, 7, …, ∞` of ℚ, and why the local–global principle (Hasse, 1921: a quadratic form over
ℚ represents `0` iff it does so over ℝ and over every ℚₚ) quantifies over exactly these fields.
In the Langlands programme the same list reappears: the adèle ring of ℚ is a restricted product
over all places, automorphic representations factor as tensor products of local representations,
one at each place, and the *local* Langlands correspondence is a statement about each ℚₚ and ℝ
separately.

The proof splits according to the dichotomy supplied by the digit bound of `OstrowskiBound`:

* **Archimedean case.** If `φ(n₀) > 1` for some natural `n₀`, then `φ(n) > 1` for every `n ≥ 2`,
  and the digit bound applied in both directions gives `log φ(m) / log m = log φ(n) / log n`;
  calling the common value `s`, we get `φ = |·|_∞^s`.
* **Non-archimedean case.** If `φ(n) ≤ 1` for all naturals `n`, some prime `p` has `φ(p) < 1`
  (otherwise `φ` would be trivial), and no other prime `q` can: from Bézout,
  `1 = a pᵏ + b qᵏ` would give `1 ≤ φ(p)ᵏ + φ(q)ᵏ < 1` for large `k`. Unique factorisation then
  gives `φ(x) = φ(p)^(vₚ(x))`, i.e. `φ = |·|ₚ^s` with `s = −log φ(p) / log p`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Foundations.NumberTheory Lean.Grind R

namespace AbsVal

variable (φ : AbsVal)

/-- If `log φ` agrees with `s · log` on all naturals `≥ 1`, through any per-integer formula,
then it agrees on all nonzero rationals: the passage from `ℕ` to `ℚ`. -/
theorem equiv_of_nat (ψ : AbsVal) {s : R} (hs : 0 < s)
    (h : ∀ n : Nat, 1 ≤ n → log (ψ.f (n : Q)) = s * log (φ.f (n : Q))) : φ.Equiv ψ := by
  refine ⟨s, hs, fun x hx => ?_⟩
  induction x using Q.ind with | h n d hd => ?_
  have hn : n ≠ 0 := fun h => hx ((mk_eq_zero_iff hd).2 h)
  rw [ψ.log_mk hd hn, φ.log_mk hd hn, h _ (by omega), h _ (by omega)]
  grind

/-! ## The archimedean case -/

/-- If `φ(n₀) > 1` for one natural number, then `φ(m) > 1` for every `m ≥ 2`. -/
theorem one_lt_of_exists {n₀ : Nat} (h₀ : 1 < φ.f (n₀ : Q)) {m : Nat} (hm : 2 ≤ m) :
    1 < φ.f (m : Q) := by
  have hn₀ : 2 ≤ n₀ := by
    have := φ.map_nat_le n₀
    have : ((1 : Nat) : R) < (n₀ : R) := by grind
    have := OrderedRing.lt_of_natCast_lt_natCast _ _ this; omega
  apply Classical.byContradiction
  intro hle
  have hb := φ.digit_bound hn₀ hm (B := 1) (Std.le_refl _) (by grind)
  rw [log_one, Semiring.mul_zero] at hb
  have h1 := log_pos h₀
  have h2 : (1 : R) < (m : R) := by
    have : ((1 : Nat) : R) < (m : R) := OrderedRing.natCast_lt_natCast_of_lt _ _ (by omega)
    grind
  have := OrderedRing.mul_pos h1 (log_pos h2)
  grind

/-- **Archimedean case of Ostrowski.** If `φ(n₀) > 1` for some natural `n₀`, then `φ` is
equivalent to `|·|_∞`, i.e. `φ = |·|_∞^s` for some `s > 0`. -/
theorem equiv_absInf {n₀ : Nat} (h₀ : 1 < φ.f (n₀ : Q)) : absInf.Equiv φ := by
  have two : (1 : R) < (2 : Nat) := by
    have : ((1 : Nat) : R) < ((2 : Nat) : R) := OrderedRing.natCast_lt_natCast_of_lt _ _ (by omega)
    grind
  have hl2 := log_pos two
  have hφ2 := φ.one_lt_of_exists h₀ (m := 2) (Nat.le_refl _)
  have hinv : log ((2 : Nat) : R) * (log ((2 : Nat) : R))⁻¹ = 1 := Field.mul_inv_cancel (by grind)
  refine equiv_of_nat absInf φ (s := log (φ.f ((2 : Nat) : Q)) * (log ((2 : Nat) : R))⁻¹)
    (OrderedRing.mul_pos (log_pos hφ2) (inv_pos' hl2)) (fun m hm => ?_)
  rw [show absInf.f (m : Q) = (m : R) by
    show ofQ (Q.abs (m : Q)) = _; rw [Q.abs_of_nonneg OrderedRing.natCast_nonneg]; rfl]
  by_cases h1 : m = 1
  · subst h1
    rw [show ((1 : Nat) : Q) = 1 from rfl, φ.map_one, show ((1 : Nat) : R) = 1 from rfl, log_one]
    grind
  · have hm2 : 2 ≤ m := by omega
    have hφm := φ.one_lt_of_exists h₀ hm2
    have b1 := φ.digit_bound hm2 (Nat.le_refl 2) (Std.le_of_lt hφ2) (Std.le_refl _)
    have b2 := φ.digit_bound (Nat.le_refl 2) hm2 (Std.le_of_lt hφm) (Std.le_refl _)
    have e : log (φ.f (m : Q)) * log ((2 : Nat) : R) = log (m : R) * log (φ.f ((2 : Nat) : Q)) :=
      by grind
    have : log (φ.f (m : Q)) * log ((2 : Nat) : R) * (log ((2 : Nat) : R))⁻¹ =
        log (φ.f (m : Q)) := by rw [Semiring.mul_assoc, hinv, Semiring.mul_one]
    grind

/-! ## The non-archimedean case -/

/-- For `0 ≤ c < 1` some power of `c` is below `1/2`. -/
theorem exists_pow_lt_half {c : R} (hc0 : 0 ≤ c) (hc1 : c < 1) : ∃ k : Nat, c ^ k < 2⁻¹ := by
  have h2 : (0 : R) < 2⁻¹ := inv_pos' (by grind)
  rcases (by grind : c = 0 ∨ 0 < c) with h | h
  · exact ⟨1, by rw [h]; show (1 : R) * 0 < _; grind⟩
  · have hlc := log_neg h hc1
    obtain ⟨k, hk⟩ := archimedean (log 2 * (-log c)⁻¹)
    have hi := inv_pos' (show 0 < -log c by grind)
    have hinv : (-log c) * (-log c)⁻¹ = 1 := Field.mul_inv_cancel (by grind)
    refine ⟨k, ?_⟩
    apply Classical.byContradiction
    intro hle
    have hle' : 2⁻¹ ≤ c ^ k := by grind
    have := log_le_log h2 hle'
    rw [log_inv (by grind), log_npow h] at this
    have h3 := OrderedRing.mul_lt_mul_of_pos_right hk (show 0 < -log c by grind)
    rw [Semiring.mul_assoc, show (-log c)⁻¹ * -log c = (-log c) * (-log c)⁻¹ from
      CommSemiring.mul_comm _ _, hinv, Semiring.mul_one] at h3
    grind

/-- A prime dividing a power of a prime `p` is `p`. -/
theorem prime_dvd_prime_pow {r p : Nat} (hr : Prime r) (hp : Prime p) :
    ∀ k : Nat, r ∣ p ^ k → r = p
  | 0, h => by rw [Nat.pow_zero] at h; have := Nat.le_of_dvd (by omega) h; have := hr.1; omega
  | k + 1, h => by
    rw [Nat.pow_succ] at h
    rcases euclid_lemma hr h with h | h
    · exact prime_dvd_prime_pow hr hp k h
    · rcases hp.2 r h with h | h
      · have := hr.1; omega
      · exact h

/-- Powers of distinct primes are coprime: `gcd(pᵏ, qᵏ) = 1`. -/
theorem gcd_prime_pow {p q : Nat} (hp : Prime p) (hq : Prime q) (hpq : p ≠ q) (k : Nat) :
    gcd (p ^ k) (q ^ k) = 1 := by
  have ⟨h1, h2⟩ := gcd_dvd (p ^ k) (q ^ k)
  apply Classical.byContradiction
  intro hne
  have hpos : 0 < p ^ k := Nat.pow_pos (by have := hp.1; omega)
  have hg0 : gcd (p ^ k) (q ^ k) ≠ 0 := fun h0 => by
    rw [h0] at h1; have := Nat.eq_zero_of_zero_dvd h1; omega
  obtain ⟨r, hr, hrg⟩ := exists_prime_dvd (show 2 ≤ gcd (p ^ k) (q ^ k) by omega)
  have := prime_dvd_prime_pow hr hp k (Nat.dvd_trans hrg h1)
  have := prime_dvd_prime_pow hr hq k (Nat.dvd_trans hrg h2)
  omega

/-- If `φ ≤ 1` on naturals then `φ ≤ 1` on integers. -/
theorem map_int_le_one (hle : ∀ n : Nat, φ.f (n : Q) ≤ 1) (z : Int) : φ.f (z : Q) ≤ 1 := by
  rcases Int.natAbs_eq z with h | h
  · rw [show (z : Q) = ((z.natAbs : Nat) : Q) by
      rw [show ((z.natAbs : Nat) : Q) = (((z.natAbs : Nat) : Int) : Q) from rfl, ← h]]
    exact hle _
  · rw [show (z : Q) = -((z.natAbs : Nat) : Q) by
      rw [show ((z.natAbs : Nat) : Q) = (((z.natAbs : Nat) : Int) : Q) from rfl]
      conv => lhs; rw [h]
      grind, φ.map_neg]
    exact hle _

/-- In the non-archimedean case, two distinct primes cannot both have `φ < 1`. -/
theorem not_both_lt_one (hle : ∀ n : Nat, φ.f (n : Q) ≤ 1) {p q : Nat} (hp : Prime p)
    (hq : Prime q) (hpq : p ≠ q) (h1 : φ.f (p : Q) < 1) (h2 : φ.f (q : Q) < 1) : False := by
  have hp0 := φ.nonneg (p : Q)
  have hq0 := φ.nonneg (q : Q)
  have hp0' : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  have hq0' : (q : Q) ≠ 0 := by have := one_le_prime hq; grind
  -- the larger of the two values
  have ⟨c, hc0, hc1, hpc, hqc⟩ : ∃ c : R, 0 ≤ c ∧ c < 1 ∧ φ.f (p : Q) ≤ c ∧ φ.f (q : Q) ≤ c := by
    rcases Std.le_total (a := φ.f (p : Q)) (b := φ.f (q : Q)) with h | h
    · exact ⟨_, hq0, h2, h, Std.le_refl _⟩
    · exact ⟨_, hp0, h1, Std.le_refl _, h⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_half hc0 hc1
  obtain ⟨a, b, hab⟩ := bezout (p ^ k) (q ^ k)
  rw [gcd_prime_pow hp hq hpq k] at hab
  have e : (1 : Q) = ((p ^ k : Nat) : Q) * (a : Q) + ((q ^ k : Nat) : Q) * (b : Q) := by
    have h3 := congrArg (fun z : Int => (z : Q)) hab
    rw [Ring.intCast_add, Ring.intCast_mul, Ring.intCast_mul, Ring.intCast_natCast,
      Ring.intCast_natCast, Ring.intCast_natCast] at h3
    rw [← h3]; grind
  have ht := φ.triangle (((p ^ k : Nat) : Q) * (a : Q)) (((q ^ k : Nat) : Q) * (b : Q))
  rw [← e, φ.map_one, φ.mul, φ.mul, map_natCast_pow, map_natCast_pow] at ht
  have ha := φ.map_int_le_one hle a
  have hb := φ.map_int_le_one hle b
  have hpk := pow_le_pow_left hp0 hpc k
  have hqk := pow_le_pow_left hq0 hqc k
  have hpk0 := Std.le_of_lt (npow_pos (φ.pos hp0') k)
  have hqk0 := Std.le_of_lt (npow_pos (φ.pos hq0') k)
  have e1 := OrderedRing.mul_le_mul_of_nonneg_left ha hpk0
  have e2 := OrderedRing.mul_le_mul_of_nonneg_left hb hqk0
  have hhalf : (2 : R) * 2⁻¹ = 1 := Field.mul_inv_cancel (by grind)
  grind

/-- In the non-archimedean case, `φ(m) = φ(p)^(vₚ(m))` for every `m ≥ 1`, where `p` is the
unique prime with `φ(p) < 1`. -/
theorem map_nat_eq_pow (hle : ∀ n : Nat, φ.f (n : Q) ≤ 1) {p : Nat} (hp : Prime p)
    (hp1 : φ.f (p : Q) < 1) : ∀ m : Nat, 1 ≤ m → φ.f (m : Q) = φ.f (p : Q) ^ (vp p m) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro hm
  by_cases h1 : m = 1
  · subst h1; rw [vp_one hp.1, Semiring.pow_zero]; exact φ.map_one
  · obtain ⟨q, hq, k, rfl⟩ := exists_prime_dvd (show 2 ≤ m by omega)
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    have hq2 := hq.1
    have hkm : k < q * k := by have := Nat.mul_le_mul_right k hq2; omega
    rw [map_natCast_mul, ih k hkm hk, vp_mul hp (by omega) (by omega), vp_prime hp hq,
      Semiring.pow_add]
    by_cases hpq : p = q
    · subst hpq; simp only [↓reduceIte, Semiring.pow_one]
    · simp only [hpq, ↓reduceIte, Semiring.pow_zero]
      have : φ.f (q : Q) = 1 := by
        have := hle q
        apply Classical.byContradiction; intro hne
        exact φ.not_both_lt_one hle hp hq hpq hp1 (by grind)
      rw [this]

/-- If `φ ≤ 1` on naturals and `φ(q) = 1` for every prime `q`, then `φ` is trivial. -/
theorem trivial_of_primes (_hle : ∀ n : Nat, φ.f (n : Q) ≤ 1)
    (h : ∀ q, Prime q → φ.f (q : Q) = 1) : ¬ φ.Nontrivial := by
  have hnat : ∀ m : Nat, 1 ≤ m → φ.f (m : Q) = 1 := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
    intro hm
    by_cases h1 : m = 1
    · subst h1; exact φ.map_one
    · obtain ⟨q, hq, k, rfl⟩ := exists_prime_dvd (show 2 ≤ m by omega)
      have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; omega
        · exact h
      have hkm : k < q * k := by have := Nat.mul_le_mul_right k hq.1; omega
      rw [map_natCast_mul, ih k hkm hk, h q hq]; grind
  rintro ⟨x, hx, hne⟩
  induction x using Q.ind with | h n d hd => ?_
  have hn : n ≠ 0 := fun h => hx ((mk_eq_zero_iff hd).2 h)
  have := φ.log_mk hd hn
  rw [hnat _ (by omega), hnat _ (by omega), log_one] at this
  apply hne
  apply log_injective (φ.pos hx) (by grind)
  rw [this, log_one]; grind

/-- **Non-archimedean case of Ostrowski.** If `φ` is nontrivial and `φ(n) ≤ 1` for every
natural `n`, then `φ` is equivalent to `|·|ₚ` for some prime `p`. -/
theorem equiv_absP (hnt : φ.Nontrivial) (hle : ∀ n : Nat, φ.f (n : Q) ≤ 1) :
    ∃ p, ∃ hp : Prime p, (absP hp).Equiv φ := by
  have ⟨p, hp, hp1⟩ : ∃ p, Prime p ∧ φ.f (p : Q) < 1 := by
    apply Classical.byContradiction; intro hno
    apply φ.trivial_of_primes hle _ hnt
    intro q hq
    have := hle q
    apply Classical.byContradiction; intro hne
    exact hno ⟨q, hq, by grind⟩
  refine ⟨p, hp, ?_⟩
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  have hc := φ.pos hp0
  have hlc := log_neg hc hp1
  have hlp := log_pos (one_lt_prime_real hp)
  have hinv : log (p : R) * (log (p : R))⁻¹ = 1 := Field.mul_inv_cancel (by grind)
  refine ⟨-log (φ.f (p : Q)) * (log (p : R))⁻¹,
    OrderedRing.mul_pos (by grind) (inv_pos' hlp), fun x hx => ?_⟩
  induction x using Q.ind with | h n d hd => ?_
  have hn : n ≠ 0 := fun h => hx ((mk_eq_zero_iff hd).2 h)
  rw [φ.log_mk hd hn, φ.map_nat_eq_pow hle hp hp1 n.natAbs (by omega),
    φ.map_nat_eq_pow hle hp hp1 d.natAbs (by omega), log_npow hc, log_npow hc, log_absP hp hx,
    vQ_mk hp hd hn]
  unfold vZ
  rw [Ring.intCast_sub, Ring.intCast_natCast, Ring.intCast_natCast]
  generalize ((vp p n.natAbs : Nat) : R) = a
  generalize ((vp p d.natAbs : Nat) : R) = b
  have : -log (φ.f (p : Q)) * (log (p : R))⁻¹ * (-(a - b) * log (p : R)) =
      (a - b) * log (φ.f (p : Q)) * (log (p : R) * (log (p : R))⁻¹) := by grind
  rw [this, hinv]; grind

end AbsVal

/-! ## Ostrowski's theorem -/

/-- **Ostrowski's theorem.** Every nontrivial absolute value `φ` on ℚ is equivalent to the
archimedean absolute value `|·|_∞` or to a `p`-adic absolute value `|·|ₚ` for some prime `p`. -/
theorem ostrowski (φ : AbsVal) (hφ : φ.Nontrivial) :
    absInf.Equiv φ ∨ ∃ p, ∃ hp : Prime p, (absP hp).Equiv φ := by
  by_cases h : ∃ n : Nat, 1 < φ.f (n : Q)
  · obtain ⟨n, hn⟩ := h
    exact Or.inl (φ.equiv_absInf hn)
  · right
    exact φ.equiv_absP hφ (fun n => by
      apply Classical.byContradiction; intro hne; exact h ⟨n, by grind⟩)

/-- **Ostrowski's theorem, with uniqueness.** For every nontrivial absolute value `φ` on ℚ,
exactly one of the following holds:
* `φ` is equivalent to `|·|_∞` and to no `|·|ₚ`; or
* `φ` is not equivalent to `|·|_∞`, and is equivalent to `|·|ₚ` for exactly one prime `p`. -/
theorem ostrowski_unique (φ : AbsVal) (hφ : φ.Nontrivial) :
    (absInf.Equiv φ ∧ ∀ p (hp : Prime p), ¬ (absP hp).Equiv φ) ∨
    (¬ absInf.Equiv φ ∧ ∃ p, ∃ hp : Prime p, (absP hp).Equiv φ ∧
      ∀ q (hq : Prime q), (absP hq).Equiv φ → q = p) := by
  rcases ostrowski φ hφ with h | ⟨p, hp, h⟩
  · exact Or.inl ⟨h, fun p hp h' => not_equiv_absInf_absP hp φ h h'⟩
  · refine Or.inr ⟨fun h' => not_equiv_absInf_absP hp φ h' h, p, hp, h, fun q hq h' => ?_⟩
    apply Classical.byContradiction; intro hqp
    exact not_equiv_absP_absP hq hp hqp φ h' h

end Foundations.Langlands.Padic
