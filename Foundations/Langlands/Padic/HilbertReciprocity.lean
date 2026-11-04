import Foundations.Langlands.Padic.HilbertLocal

/-!
# Hilbert's product formula

**`hilbert_product_formula`.** For non-zero rationals `a, b`, the local Hilbert symbols
`(a, b)_ℓ` are `1` at all but finitely many primes `ℓ`, and

  `∏_v (a, b)_v = (∏_ℓ (a, b)_ℓ) · (a, b)_∞ = 1`,

stated, as `product_formula` and `hilbert_product_formula_primes'`, with a finite product: there
is `N` with `(a, b)_ℓ = 1` for `ℓ ≥ N` and `(∏_{ℓ < M prime} (a, b)_ℓ) · (a, b)_∞ = 1` for every
`M ≥ N`. Hilbert (*Zahlbericht*, 1897) saw that this single identity contains quadratic
reciprocity and both of its supplements.

We call the conclusion `HilbertPF a b`. The proof:

1. `HilbertPF` is symmetric (`HilbertPF.comm`), only depends on the local symbols
   (`HilbertPF.congr`), and is multiplicative in each argument (`HilbertPF.mul_left`), because
   every local symbol is bilinear (`hilbertAt_mul_left`, `hilbertInfQ_mul_left`): only finitely
   many places are non-trivial for each factor, so one takes the larger bound `N`.
2. Since `(c² a, b)_v = (a, b)_v`, a rational `n/d` may be replaced by the integer `n d`, and
   every non-zero integer is `±` a product of primes. So it suffices to treat the generators
   `−1, 2` and odd primes `p, q` (`HilbertPF.of_generators`).
3. The generator pairs, place by place (all other places give `1`, the arguments being units
   there):
   * `(−1, −1)`: `−1` at `∞` and at `2`;
   * `(−1, 2)`: `1` everywhere;
   * `(−1, p)`: `(−1)^((p−1)/2)` at `2` and at `p` — the **first supplement**;
   * `(2, p)`: `(−1)^((p²−1)/8)` at `2` and at `p` — the **second supplement**;
   * `(2, 2) ~ (2, −1)` and `(p, p) ~ (p, −1)`, via `(a, a)_v = (a, −1)_v`;
   * `(p, q)`: `hilbert_product_formula_primes` — **quadratic reciprocity**.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- **The product formula for `(a, b)`**: there is `N` such that `(a, b)_ℓ = 1` for all
`ℓ ≥ N` and `(∏_{ℓ < M prime} (a, b)_ℓ) · (a, b)_∞ = 1` for all `M ≥ N`. -/
def HilbertPF (a b : Q) : Prop :=
  ∃ N, (∀ ℓ, N ≤ ℓ → hilbertAt ℓ a b = 1) ∧
    ∀ M, N ≤ M → primeProd (fun ℓ => ((hilbertAt ℓ a b : Int) : Q)) M *
      ((hilbertInfQ a b : Int) : Q) = 1

namespace HilbertPF

/-- The product formula only depends on the local symbols. -/
theorem congr {a b a' b' : Q} (h : ∀ ℓ, hilbertAt ℓ a b = hilbertAt ℓ a' b')
    (hi : hilbertInfQ a b = hilbertInfQ a' b') (H : HilbertPF a b) : HilbertPF a' b' := by
  obtain ⟨N, h1, h2⟩ := H
  refine ⟨N, fun ℓ hℓ => by rw [← h ℓ]; exact h1 ℓ hℓ, fun M hM => ?_⟩
  have e : (fun ℓ => ((hilbertAt ℓ a' b' : Int) : Q)) = fun ℓ => ((hilbertAt ℓ a b : Int) : Q) :=
    funext fun ℓ => by rw [h ℓ]
  rw [e, ← hi]; exact h2 M hM

/-- The product formula for `(a, b)` gives it for `(b, a)`. -/
theorem comm {a b : Q} (H : HilbertPF a b) : HilbertPF b a :=
  H.congr (fun ℓ => hilbertAt_comm ℓ a b) (hilbertInfQ_comm a b)

/-- **Multiplicativity.** The product formula for `(a, b)` and `(a', b)` gives it for
`(a a', b)` (non-zero arguments), by bilinearity at every place. -/
theorem mul_left {a a' b : Q} (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) (H : HilbertPF a b)
    (H' : HilbertPF a' b) : HilbertPF (a * a') b := by
  obtain ⟨N, h1, h2⟩ := H
  obtain ⟨N', h1', h2'⟩ := H'
  refine ⟨max N N', fun ℓ hℓ => ?_, fun M hM => ?_⟩
  · rw [hilbertAt_mul_left ℓ ha ha' hb, h1 ℓ (by omega), h1' ℓ (by omega)]; rfl
  · have e : (fun ℓ => ((hilbertAt ℓ (a * a') b : Int) : Q)) =
        fun ℓ => ((hilbertAt ℓ a b : Int) : Q) * ((hilbertAt ℓ a' b : Int) : Q) :=
      funext fun ℓ => by rw [hilbertAt_mul_left ℓ ha ha' hb, Ring.intCast_mul]
    rw [e, primeProd_mul, hilbertInfQ_mul_left ha ha', Ring.intCast_mul]
    have k := h2 M (by omega)
    have k' := h2' M (by omega)
    generalize primeProd (fun ℓ => ((hilbertAt ℓ a b : Int) : Q)) M = P at k ⊢
    generalize primeProd (fun ℓ => ((hilbertAt ℓ a' b : Int) : Q)) M = P' at k' ⊢
    generalize ((hilbertInfQ a b : Int) : Q) = I at k ⊢
    generalize ((hilbertInfQ a' b : Int) : Q) = I' at k' ⊢
    rw [show P * P' * (I * I') = (P * I) * (P' * I') by grind, k, k']; grind

/-- The product formula for `(1, b)`: all symbols are `1`. -/
theorem one_left (b : Q) : HilbertPF 1 b := by
  refine ⟨0, fun ℓ _ => hilbertAt_one_left ℓ b, fun M _ => ?_⟩
  have e : (fun ℓ => ((hilbertAt ℓ 1 b : Int) : Q)) = fun _ => 1 :=
    funext fun ℓ => by rw [hilbertAt_one_left]; rfl
  rw [e, primeProd_one, hilbertInfQ_one_left]; rfl

/-- Cast of an identity `x · y = 1` between integers into ℚ. -/
theorem cast_mul_eq_one {x y : Int} (h : x * y = 1) : (x : Q) * (y : Q) = 1 := by
  rw [← Ring.intCast_mul, h]; rfl

/-- **Support `{∞, 2}`.** If `(a, b)_ℓ = 1` at every odd prime and `(a, b)_∞ (a, b)_2 = 1`,
the product formula holds for `(a, b)`. -/
theorem of_two {a b : Q} (hodd : ∀ ℓ, Prime ℓ → ℓ ≠ 2 → hilbertAt ℓ a b = 1)
    (h : hilbertInfQ a b * hilbertAt 2 a b = 1) : HilbertPF a b := by
  refine ⟨3, fun ℓ hℓ => ?_, fun M hM => ?_⟩
  · by_cases hp : Prime ℓ
    · exact hodd ℓ hp (by omega)
    · exact hilbertAt_of_not_prime hp a b
  · let c2 : Q := ((hilbertAt 2 a b : Int) : Q)
    rw [primeProd_congr (h := fun ℓ => open Classical in if ℓ = 2 then c2 else 1) (fun ℓ hℓ _ => by
      by_cases e2 : ℓ = 2
      · subst e2; simp [c2]
      · simp only [e2, ite_false]; rw [hodd ℓ hℓ e2]; rfl),
      primeProd_single prime_two c2 (by omega)]
    have := cast_mul_eq_one h
    show c2 * _ = 1
    grind

/-- **Support `{∞, 2, p}`.** If `(a, b)_ℓ = 1` at every odd prime `ℓ ≠ p` (`p` an odd prime) and
`(a, b)_∞ (a, b)_2 (a, b)_p = 1`, the product formula holds for `(a, b)`. -/
theorem of_two_p {a b : Q} {p : Nat} (hp : Prime p) (hp2 : p ≠ 2)
    (hodd : ∀ ℓ, Prime ℓ → ℓ ≠ 2 → ℓ ≠ p → hilbertAt ℓ a b = 1)
    (h : hilbertInfQ a b * hilbertAt 2 a b * hilbertAt p a b = 1) : HilbertPF a b := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  refine ⟨p + 1, fun ℓ hℓ => ?_, fun M hM => ?_⟩
  · by_cases hl : Prime ℓ
    · exact hodd ℓ hl (by omega) (by omega)
    · exact hilbertAt_of_not_prime hl a b
  · let c2 : Q := ((hilbertAt 2 a b : Int) : Q)
    let cp : Q := ((hilbertAt p a b : Int) : Q)
    rw [primeProd_congr (h := fun ℓ => (open Classical in if ℓ = 2 then c2 else 1) *
        (open Classical in if ℓ = p then cp else 1)) (fun ℓ hℓ _ => by
      by_cases e2 : ℓ = 2
      · subst e2; simp [hp2.symm, c2]; grind
      · by_cases ep : ℓ = p
        · subst ep; simp [e2, cp]; grind
        · simp only [e2, ep, ite_false]; rw [hodd ℓ hℓ e2 ep]; grind),
      primeProd_mul, primeProd_single prime_two c2 (by omega), primeProd_single hp cp (by omega)]
    have := congrArg (fun n : Int => (n : Q)) h
    simp only [Ring.intCast_mul, Ring.intCast_one] at this
    show c2 * cp * _ = 1
    grind

end HilbertPF

/-! ## The generators -/

/-- A prime does not divide `−1`. -/
theorem prime_not_dvd_neg_one {ℓ : Nat} (hℓ : Prime ℓ) : ¬ (ℓ : Int) ∣ -1 := fun h => by
  have := Int.le_of_dvd (by decide) (Int.dvd_neg.1 h); have := hℓ.1; omega

/-- An odd prime does not divide `2`. -/
theorem prime_not_dvd_two {ℓ : Nat} (hℓ : Prime ℓ) (h2 : ℓ ≠ 2) : ¬ (ℓ : Int) ∣ 2 := fun h => by
  have := Int.le_of_dvd (by decide) h; have := hℓ.1
  rcases (by omega : ℓ = 2) with rfl; exact h2 rfl

/-- A prime `ℓ` does not divide a different prime `p`, as integers. -/
theorem prime_not_dvd_int {ℓ p : Nat} (hℓ : Prime ℓ) (hp : Prime p) (h : ℓ ≠ p) :
    ¬ (ℓ : Int) ∣ (p : Int) := fun hd => prime_not_dvd hℓ hp h (Int.ofNat_dvd.1 hd)

/-- `(2 : ℚ)` is the cast of the integer `2`. -/
theorem Q_two_eq : (2 : Q) = ((2 : Int) : Q) := rfl

/-- `(−1, −1)`: the symbol is `−1` at `∞` and at `2`, and `1` elsewhere. -/
theorem hilbertPF_neg_one_neg_one : HilbertPF (-1) (-1) := by
  refine HilbertPF.of_two (fun ℓ hℓ h2 => ?_) ?_
  · rw [Q_neg_one_eq]
    exact hilbertAt_int_units hℓ h2 (prime_not_dvd_neg_one hℓ) (prime_not_dvd_neg_one hℓ)
  · have h1 : (-1 : Q) < 0 := by grind
    rw [hilbertInfQ_eq, Foundations.Algebra.ite_true_of ⟨h1, h1⟩, Q_neg_one_eq,
      hilbertAt_two_units_int (by decide) (by decide)]
    decide

/-- `(−1, 2)`: the symbol is `1` at every place. -/
theorem hilbertPF_neg_one_two : HilbertPF (-1) 2 := by
  refine HilbertPF.of_two (fun ℓ hℓ h2 => ?_) ?_
  · rw [Q_neg_one_eq, Q_two_eq]
    exact hilbertAt_int_units hℓ h2 (prime_not_dvd_neg_one hℓ) (prime_not_dvd_two hℓ h2)
  · have h1 : ¬ (2 : Q) < 0 := by grind
    rw [hilbertInfQ_eq, Foundations.Algebra.ite_false_of (fun h => h1 h.2), Q_neg_one_eq, hilbertAt_two_int_two (by decide)]
    decide

/-- For odd `p`, `(−1)^((p−1)/2) = −1` iff `p ≡ 3 (mod 4)`. -/
theorem neg_one_pow_half {p : Nat} (hp : p % 2 = 1) :
    (-1 : Int) ^ Foundations.Algebra.half p = if p % 4 = 3 then -1 else 1 := by
  rw [Foundations.Algebra.neg_one_pow_int]
  unfold Foundations.Algebra.half
  by_cases h : p % 4 = 3
  · rw [Foundations.Algebra.ite_false_of (by omega), Foundations.Algebra.ite_true_of h]
  · rw [Foundations.Algebra.ite_true_of (by omega), Foundations.Algebra.ite_false_of h]

/-- For odd `p`, `(−1)^((p²−1)/8) = −1` iff `p ≡ ±3 (mod 8)`. -/
theorem neg_one_pow_sq_eighth {p : Nat} (hp : p % 2 = 1) :
    (-1 : Int) ^ ((p * p - 1) / 8) = omega2 (p % 8) := by
  rw [Foundations.Algebra.neg_one_pow_int]
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 8 ∧ p = 8 * m + r :=
    ⟨p / 8, p % 8, Nat.mod_lt _ (by decide), by omega⟩
  have hsq : (8 * m + r) * (8 * m + r) = 64 * (m * m) + 16 * (m * r) + r * r := by grind
  rw [hsq, show (8 * m + r) % 8 = r by omega]
  rcases odd_lt_eight hr (by omega) with rfl | rfl | rfl | rfl
  · rw [Foundations.Algebra.ite_true_of (by omega)]; decide
  · rw [Foundations.Algebra.ite_false_of (by omega)]; decide
  · rw [Foundations.Algebra.ite_false_of (by omega)]; decide
  · rw [Foundations.Algebra.ite_true_of (by omega)]; decide

/-- `(−1, p)` for an odd prime `p`: `(−1)^((p−1)/2)` at `2` and at `p` — the first supplement. -/
theorem hilbertPF_neg_one_prime {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) :
    HilbertPF (-1) (p : Q) := by
  have hp2 : p ≠ 2 := by omega
  refine HilbertPF.of_two_p hp hp2 (fun ℓ hℓ h2 hlp => ?_) ?_
  · rw [Q_neg_one_eq, Q_natCast_eq]
    exact hilbertAt_int_units hℓ h2 (prime_not_dvd_neg_one hℓ) (prime_not_dvd_int hℓ hp hlp)
  · have h1 : ¬ (p : Q) < 0 := by
      have := OrderedRing.pos_natCast_of_pos (R := Q) p (by have := hp.1; omega); grind
    rw [hilbertInfQ_eq, Foundations.Algebra.ite_false_of (fun h => h1 h.2), hilbertAt_neg_one_self hp hodd,
      neg_one_pow_half hodd, Q_neg_one_eq, Q_natCast_eq,
      hilbertAt_two_units_int (by decide) (by omega),
      show ((p : Int) % 8).toNat = p % 8 by omega]
    have := odd_lt_eight (Nat.mod_lt p (by decide : 8 > 0)) (by omega : p % 8 % 2 = 1)
    rcases this with h | h | h | h <;> rw [h] <;>
      simp only [show p % 4 = p % 8 % 4 by omega, h] <;> decide

/-- `(2, p)` for an odd prime `p`: `(−1)^((p²−1)/8)` at `2` and at `p` — the second
supplement. -/
theorem hilbertPF_two_prime {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) :
    HilbertPF 2 (p : Q) := by
  have hp2 : p ≠ 2 := by omega
  refine HilbertPF.of_two_p hp hp2 (fun ℓ hℓ h2 hlp => ?_) ?_
  · rw [Q_two_eq, Q_natCast_eq]
    exact hilbertAt_int_units hℓ h2 (prime_not_dvd_two hℓ h2) (prime_not_dvd_int hℓ hp hlp)
  · rw [hilbertInfQ_of_pos (by grind), hilbertAt_two_self hp hodd, neg_one_pow_sq_eighth hodd,
      hilbertAt_comm, Q_natCast_eq, hilbertAt_two_int_two (by omega),
      show ((p : Int) % 8).toNat = p % 8 by omega]
    have := odd_lt_eight (Nat.mod_lt p (by decide : 8 > 0)) (by omega : p % 8 % 2 = 1)
    rcases this with h | h | h | h <;> rw [h] <;> decide

/-- `(2, 2)`: as `(2, 2)_v = (2, −1)_v`, this is the case `(−1, 2)`. -/
theorem hilbertPF_two_two : HilbertPF 2 2 :=
  hilbertPF_neg_one_two.comm.congr (fun ℓ => (hilbertAt_self ℓ (by grind)).symm)
    (hilbertInfQ_self 2).symm

/-- `(p, p)` for an odd prime: as `(p, p)_v = (p, −1)_v`, this is the case `(−1, p)`. -/
theorem hilbertPF_prime_self {p : Nat} (hp : Prime p) (hodd : p % 2 = 1) :
    HilbertPF (p : Q) (p : Q) := by
  have hp0 : (p : Q) ≠ 0 := by
    have := OrderedRing.pos_natCast_of_pos (R := Q) p (by have := hp.1; omega); grind
  exact (hilbertPF_neg_one_prime hp hodd).comm.congr (fun ℓ => (hilbertAt_self ℓ hp0).symm)
    (hilbertInfQ_self _).symm

/-- `(p, q)` for distinct odd primes: quadratic reciprocity (`hilbert_product_formula_primes`). -/
theorem hilbertPF_primes {p q : Nat} (hp : Prime p) (hq : Prime q) (hpo : p % 2 = 1)
    (hqo : q % 2 = 1) (hpq : p ≠ q) : HilbertPF (p : Q) (q : Q) := by
  obtain ⟨hother, -⟩ := hilbert_product_formula_primes hp hq hpo hqo hpq
  refine ⟨p + q + 1, fun ℓ hℓ => ?_, fun M hM =>
    hilbert_product_formula_primes' hp hq hpo hqo hpq (by omega) (by omega)⟩
  by_cases hl : Prime ℓ
  · exact hother ℓ hl (by omega) (by omega) (by omega)
  · exact hilbertAt_of_not_prime hl _ _

/-- The **generators** of ℚˣ: `−1` and the primes. -/
def IsGen (x : Q) : Prop := x = -1 ∨ ∃ p, Prime p ∧ x = (p : Q)

/-- **The product formula on generators.** It holds for every pair of generators. -/
theorem hilbertPF_gen {g h : Q} (hg : IsGen g) (hh : IsGen h) : HilbertPF g h := by
  rcases hg with rfl | ⟨p, hp, rfl⟩ <;> rcases hh with rfl | ⟨q, hq, rfl⟩
  · exact hilbertPF_neg_one_neg_one
  · by_cases hq2 : q = 2
    · subst hq2; exact hilbertPF_neg_one_two
    · exact hilbertPF_neg_one_prime hq (prime_odd_of_ne_two hq hq2)
  · by_cases hp2 : p = 2
    · subst hp2; exact hilbertPF_neg_one_two.comm
    · exact (hilbertPF_neg_one_prime hp (prime_odd_of_ne_two hp hp2)).comm
  · by_cases hp2 : p = 2 <;> by_cases hq2 : q = 2
    · subst hp2 hq2; exact hilbertPF_two_two
    · subst hp2; exact hilbertPF_two_prime hq (prime_odd_of_ne_two hq hq2)
    · subst hq2; exact (hilbertPF_two_prime hp (prime_odd_of_ne_two hp hp2)).comm
    · by_cases hpq : p = q
      · subst hpq; exact hilbertPF_prime_self hp (prime_odd_of_ne_two hp hp2)
      · exact hilbertPF_primes hp hq (prime_odd_of_ne_two hp hp2)
          (prime_odd_of_ne_two hq hq2) hpq

/-! ## Reduction to generators -/

/-- A positive natural number is non-zero in ℚ. -/
theorem Q_natCast_ne_zero {n : Nat} (hn : 1 ≤ n) : (n : Q) ≠ 0 := by
  have := OrderedRing.pos_natCast_of_pos (R := Q) n (by omega); grind

/-- A generator is non-zero. -/
theorem IsGen.ne_zero {g : Q} (hg : IsGen g) : g ≠ 0 := by
  rcases hg with rfl | ⟨p, hp, rfl⟩
  · grind
  · exact Q_natCast_ne_zero (by have := hp.1; omega)

/-- **Reduction to generators in the first argument.** If `b ≠ 0` and the product formula
holds for `(g, b)` for every generator `g`, it holds for `(a, b)` for every non-zero `a`:
positive integers are products of primes, non-zero integers are `±` such products, and
`n/d` has the square class of `n d`. -/
theorem HilbertPF.of_generators {b : Q} (hb : b ≠ 0) (hgen : ∀ g, IsGen g → HilbertPF g b) :
    ∀ a : Q, a ≠ 0 → HilbertPF a b := by
  -- positive integers
  have hnat : ∀ n : Nat, 1 ≤ n → HilbertPF (n : Q) b := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro hn
      by_cases h1 : n = 1
      · subst h1; exact HilbertPF.one_left b
      · obtain ⟨p, hp, k, rfl⟩ := exists_prime_dvd (show 2 ≤ n by omega)
        have hp2 := hp.1
        have hk : 1 ≤ k := by
          apply Classical.byContradiction; intro h
          rw [show k = 0 by omega, Nat.mul_zero] at hn; omega
        rw [Semiring.natCast_mul]
        exact HilbertPF.mul_left (Q_natCast_ne_zero (by omega)) (Q_natCast_ne_zero hk) hb
          (hgen _ (Or.inr ⟨p, hp, rfl⟩))
          (ih k (by
            have : 1 * k < p * k := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
            omega) hk)
  -- non-zero integers
  have hint : ∀ m : Int, m ≠ 0 → HilbertPF (m : Q) b := by
    intro m hm
    have hk : 1 ≤ m.natAbs := by omega
    rcases Int.natAbs_eq m with h | h
    · rw [h]; exact hnat _ hk
    · rw [h, Ring.intCast_neg, show -((m.natAbs : Int) : Q) = -1 * (m.natAbs : Q) by
        rw [show ((m.natAbs : Int) : Q) = (m.natAbs : Q) from rfl]; grind]
      exact HilbertPF.mul_left (by grind) (Q_natCast_ne_zero hk) hb (hgen _ (Or.inl rfl))
        (hnat _ hk)
  -- rationals
  intro a ha
  induction a using Q.ind with | h n d hd => ?_
  have hn : n ≠ 0 := fun h => ha ((mk_eq_zero_iff hd).2 h)
  have hd0 : (d : Q) ≠ 0 := fun h => by have := (mk_eq_zero_iff Int.one_pos).1 h; omega
  have e : (d : Q) * (d : Q) * Q.mk n d hd = ((n * d : Int) : Q) := by
    rw [mk_eq_mul_inv, Ring.intCast_mul]
    have := Field.mul_inv_cancel hd0
    grind
  have H := hint (n * d) (Int.mul_ne_zero hn (by omega))
  rw [← e] at H
  exact H.congr (fun ℓ => hilbertAt_mul_sq_left ℓ hd0 _ b) (hilbertInfQ_mul_sq_left hd0 _ b)

/-! ## The product formula -/

/-- **Hilbert's product formula.** For non-zero rationals `a, b`, `∏_v (a, b)_v = 1` over all
places `v` of ℚ: there is `N` such that `(a, b)_ℓ = 1` for every `ℓ ≥ N`, and
`(∏_{ℓ < M prime} (a, b)_ℓ) · (a, b)_∞ = 1` for every `M ≥ N` (values in ℚ). -/
theorem hilbert_product_formula {a b : Q} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ N, (∀ ℓ, N ≤ ℓ → hilbertAt ℓ a b = 1) ∧
      ∀ M, N ≤ M → primeProd (fun ℓ => ((hilbertAt ℓ a b : Int) : Q)) M *
        ((hilbertInfQ a b : Int) : Q) = 1 := by
  -- first: every generator `g` against every non-zero `x`
  have step : ∀ g, IsGen g → ∀ x : Q, x ≠ 0 → HilbertPF g x := fun g hg x hx =>
    (HilbertPF.of_generators hg.ne_zero (fun h hh => hilbertPF_gen hh hg) x hx).comm
  exact HilbertPF.of_generators hb (fun g hg => step g hg b hb) a ha

/-- **Hilbert's product formula, finitely many non-trivial places.** For non-zero rationals
`a, b`, `(a, b)_ℓ = 1` for all but finitely many primes `ℓ`. -/
theorem hilbert_symbol_eventually_one {a b : Q} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ N, ∀ ℓ, N ≤ ℓ → hilbertAt ℓ a b = 1 :=
  let ⟨N, h, _⟩ := hilbert_product_formula ha hb; ⟨N, h⟩

end Foundations.Langlands.Padic
