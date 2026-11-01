import Foundations.NumberTheory.Mertens

/-!
# The Möbius function

The **Möbius function** (Möbius 1832; the notation `μ` is Mertens') is `μ(n) = (−1)^k` if `n` is
a product of `k` distinct primes, and `μ(n) = 0` if some square of a prime divides `n`. It is
the inverse of the constant function `1` for Dirichlet convolution:

  `Σ_{d ∣ n} μ(d) = 1` if `n = 1`, and `0` if `n > 1`,

which is the inclusion–exclusion principle in arithmetic form. Combined with
`Σ_{d ∣ n} Λ(d) = log n` it gives the inverse relation `Σ_{d ∣ n} μ(d) log d = −Λ(n)`. Both are
proved by peeling off one prime: the divisors of `pᵃ m` (`p ∤ m`) are the `pⁱ e` with `e ∣ m`,
and only `i = 0, 1` contribute, with `μ(p e) = −μ(e)`.

These identities let us *invert* `L(1, χ)` in the next file: they are the elementary shadow of
`1/L(s, χ) = Σ μ(n) χ(n) n⁻ˢ` and `−L'/L(s, χ) = Σ Λ(n) χ(n) n⁻ˢ`.
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

attribute [local instance] Classical.propDecidable

/-- The number `ω(n)` of distinct primes dividing `n`. -/
noncomputable def omega' (n : Nat) : Nat := countBelow (fun p => Prime p ∧ p ∣ n) (n + 1)

/-- `n` is **squarefree**: no square of a prime divides it. -/
def Squarefree' (n : Nat) : Prop := ∀ p, Prime p → ¬ p * p ∣ n

/-- The **Möbius function** `μ(n)`: `(−1)^ω(n)` for squarefree `n ≥ 1`, and `0` otherwise. -/
noncomputable def mobius (n : Nat) : R :=
  if n = 0 then 0 else if Squarefree' n then (-1) ^ omega' n else 0

/-- If a prime divides `pᵏ` (`p` prime) then it equals `p`. -/
theorem eq_of_prime_dvd_pow {r p : Nat} (hr : Prime r) (hp : Prime p) :
    ∀ k, r ∣ p ^ k → r = p
  | 0, h => by rw [Nat.pow_zero] at h; have := Nat.le_of_dvd (by omega) h; have := hr.1; omega
  | k + 1, h => by
    rw [Nat.pow_succ] at h
    rcases euclid_lemma hr h with h1 | h1
    · exact eq_of_prime_dvd_pow hr hp k h1
    · rcases hp.2 r h1 with h2 | h2
      · have := hr.1; omega
      · exact h2

/-- Counting below a bound that exceeds every witness. -/
theorem countBelow_eq_of_ge (P : Nat → Prop) [DecidablePred P] {A : Nat}
    (h : ∀ k, A ≤ k → ¬ P k) : ∀ B, A ≤ B → countBelow P B = countBelow P A := by
  intro B hB
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hB
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [← Nat.add_assoc]
    simp only [countBelow, ih (Nat.le_add_right A c), h (A + c) (Nat.le_add_right A c), ↓reduceIte,
      Nat.add_zero]

/-- Counting a disjoint union with one extra element. -/
theorem countBelow_or_eq (P : Nat → Prop) [DecidablePred P] (p : Nat) (hp : ¬ P p) :
    ∀ B, countBelow (fun r => P r ∨ r = p) B = countBelow P B + if p < B then 1 else 0
  | 0 => rfl
  | B + 1 => by
    have ih := countBelow_or_eq P p hp B
    simp only [countBelow, ih]
    by_cases hB : P B
    · have h1' : (p < B + 1) ↔ (p < B) := ⟨fun h => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
        · exact h
        · exact absurd (h ▸ hB) hp, Nat.lt_succ_of_lt⟩
      simp only [hB, true_or, ↓reduceIte, h1']; split <;> omega
    · by_cases h2 : B = p
      · subst h2; simp only [hB, or_true, ↓reduceIte, Nat.lt_irrefl, Nat.lt_succ_self]
      · have h1' : (p < B + 1) ↔ (p < B) := by omega
        simp only [hB, h2, or_self, ↓reduceIte, h1']; split <;> omega

/-- Counting is invariant under replacing the property by an equivalent one. -/
theorem countBelow_congr {P Q : Nat → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ k, P k ↔ Q k) : ∀ B, countBelow P B = countBelow Q B
  | 0 => rfl
  | B + 1 => by
    simp only [countBelow, countBelow_congr h B]
    by_cases hB : P B
    · rw [ite_eq_left hB, ite_eq_left ((h B).1 hB)]
    · rw [ite_eq_right hB, ite_eq_right (fun h' => hB ((h B).2 h'))]

/-- Distinct primes are coprime. -/
theorem coprime_of_prime_ne {r p : Nat} (hr : Prime r) (hp : Prime p) (hne : r ≠ p) :
    Nat.Coprime r p := by
  rcases hp.2 _ (Nat.gcd_dvd_right r p) with h | h
  · exact h
  · have : p ∣ r := h ▸ Nat.gcd_dvd_left r p
    rcases hr.2 p this with h1 | h1
    · have := hp.1; omega
    · exact absurd h1.symm hne

/-- `ω(p e) = ω(e) + 1` for a prime `p ∤ e`, `e ≥ 1`. -/
theorem omega'_prime_mul {p e : Nat} (hp : Prime p) (hpe : ¬ p ∣ e) (he : 0 < e) :
    omega' (p * e) = omega' e + 1 := by
  unfold omega'
  have hp2 : 2 ≤ p := hp.1
  have hle : e + 1 ≤ p * e + 1 := by have := Nat.le_mul_of_pos_left e (show 0 < p by omega); omega
  have e1 : ∀ r, (Prime r ∧ r ∣ p * e) ↔ ((Prime r ∧ r ∣ e) ∨ r = p) := by
    intro r; constructor
    · rintro ⟨hr, hd⟩
      rcases euclid_lemma hr hd with h | h
      · right; rcases hp.2 r h with h1 | h1
        · have := hr.1; omega
        · exact h1
      · left; exact ⟨hr, h⟩
    · rintro (⟨hr, hd⟩ | hrp)
      · exact ⟨hr, Nat.dvd_trans hd (Nat.dvd_mul_left e p)⟩
      · rw [hrp]; exact ⟨hp, Nat.dvd_mul_right p e⟩
  rw [countBelow_congr e1, countBelow_or_eq _ p (fun h => hpe h.2),
    ite_eq_left (by have := Nat.le_mul_of_pos_right p he; omega)]
  congr 1
  apply countBelow_eq_of_ge _ (A := e + 1) (fun k hk h => by have := Nat.le_of_dvd he h.2; omega) _ hle

/-- `ω(1) = 0`. -/
theorem omega'_one : omega' 1 = 0 := by
  unfold omega'
  simp only [countBelow]
  rw [ite_eq_right (fun h => by have := h.1.1; omega), ite_eq_right (fun h => by have := h.1.1; omega)]

/-- `μ(1) = 1`. -/
theorem mobius_one : mobius 1 = 1 := by
  unfold mobius
  rw [ite_eq_right (by omega), ite_eq_left (show Squarefree' 1 from fun p hp h => by
    have := Nat.le_of_dvd (by omega) h; have := hp.1
    have : 2 * 2 ≤ p * p := Nat.mul_le_mul this this; omega), omega'_one]
  rfl

/-- `μ(p e) = −μ(e)` for a prime `p ∤ e`, `e ≥ 1`. -/
theorem mobius_prime_mul {p e : Nat} (hp : Prime p) (hpe : ¬ p ∣ e) (he : 0 < e) :
    mobius (p * e) = -mobius e := by
  have hp2 : 2 ≤ p := hp.1
  have hsq : Squarefree' (p * e) ↔ Squarefree' e := by
    constructor
    · intro h r hr hd; exact h r hr (Nat.dvd_trans hd (Nat.dvd_mul_left e p))
    · intro h r hr hd
      by_cases hrp : r = p
      · subst hrp
        exact hpe (Nat.dvd_of_mul_dvd_mul_left (show 0 < r by omega) hd)
      · apply h r hr
        have hc := coprime_of_prime_ne hr hp hrp
        have hcop : Nat.Coprime (r * r) p := Nat.coprime_mul_iff_left.2 ⟨hc, hc⟩
        exact hcop.dvd_of_dvd_mul_left hd
  have hpe0 : ¬ (p * e = 0) := Nat.pos_iff_ne_zero.1 (Nat.mul_pos (show 0 < p by omega) he)
  have he0 : ¬ (e = 0) := Nat.pos_iff_ne_zero.1 he
  unfold mobius
  rw [ite_eq_right (c := p * e = 0) hpe0, ite_eq_right (c := e = 0) he0]
  by_cases h : Squarefree' e
  · rw [ite_eq_left (hsq.2 h), ite_eq_left h, omega'_prime_mul hp hpe he]
    show (-1 : R) ^ omega' e * (-1) = _; grind
  · rw [ite_eq_right (fun h' => h (hsq.1 h')), ite_eq_right h]; grind

/-- `μ(pⁱ e) = 0` for `i ≥ 2`. -/
theorem mobius_prime_pow_mul {p e i : Nat} (hp : Prime p) (hi : 2 ≤ i) : mobius (p ^ i * e) = 0 := by
  unfold mobius
  by_cases h0 : p ^ i * e = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right]
    intro h
    apply h p hp
    exact Nat.dvd_trans (by rw [← Nat.pow_two]; exact Nat.pow_dvd_pow p hi) (Nat.dvd_mul_right _ e)

/-- `Σ (−f) = −Σ f`. -/
theorem gsum_neg' {α : Type} [Field α] (f : Nat → α) (n : Nat) :
    gsum (fun k => -f k) n = -gsum f n := by
  induction n with
  | zero => show (0 : α) = -0; grind
  | succ n ih => rw [gsum_succ, gsum_succ, ih]; grind

/-- `Σ (f − g) = Σ f − Σ g`. -/
theorem gsum_sub' {α : Type} [Field α] (f g : Nat → α) (n : Nat) :
    gsum (fun k => f k - g k) n = gsum f n - gsum g n := by
  induction n with
  | zero => show (0 : α) = 0 - 0; grind
  | succ n ih => rw [gsum_succ, gsum_succ, gsum_succ, ih]; grind

/-- A divisor sum of zeros vanishes. -/
theorem dsum_zero' {α : Type} [Field α] (n : Nat) : dsum (fun _ => (0 : α)) n = 0 := by
  unfold dsum
  exact (gsum_congr (g := fun _ => 0) (fun d _ => by split <;> rfl)).trans (gsum_zero' _)

/-- Splitting `n ≥ 2` as `pᵃ m` with `a ≥ 1` and `p ∤ m`. -/
theorem exists_prime_pow_mul {n : Nat} (hn : 2 ≤ n) :
    ∃ p a m, Prime p ∧ 1 ≤ a ∧ ¬ p ∣ m ∧ 0 < m ∧ n = p ^ a * m := by
  obtain ⟨p, hp, hpn⟩ := exists_prime_dvd hn
  obtain ⟨m, hm, hpm⟩ := vp_spec hp.1 (show 0 < n by omega)
  have ha : 1 ≤ vp p n := (pow_dvd_iff_le_vp hp.1 (by omega)).1 (by rw [Nat.pow_one]; exact hpn)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  exact ⟨p, vp p n, m, hp, ha, hpm, hm0, hm⟩

/-- Only the terms `i = 0, 1` of a sum over `i ≤ a` survive, if the others vanish. -/
theorem gsum_two_terms {α : Type} [Field α] {D : Nat → α} {a : Nat} (ha : 1 ≤ a)
    (h : ∀ i, 2 ≤ i → D i = 0) : gsum D (a + 1) = D 0 + D 1 := by
  rw [gsum_extend (A := 2) (by omega) (fun i hi _ => h i hi), gsum_succ, gsum_succ, gsum_nil]
  grind

/-- Divisors of `m` are not divisible by `p` when `p ∤ m`, and are positive. -/
theorem dvd_facts {p m e : Nat} (hpm : ¬ p ∣ m) (hm : 0 < m) (he : e ∣ m) : ¬ p ∣ e ∧ 0 < e :=
  ⟨fun h => hpm (Nat.dvd_trans h he), Nat.pos_of_ne_zero (by rintro rfl; simp at he; omega)⟩

/-- **The Möbius function inverts `1`.** `Σ_{d ∣ n} μ(d) = [n = 1]` for `n ≥ 1`. -/
theorem dsum_mobius {n : Nat} (hn : 0 < n) : dsum mobius n = if n = 1 then 1 else 0 := by
  by_cases h1 : n = 1
  · subst h1; rw [dsum_one, mobius_one, ite_eq_left rfl]
  · rw [ite_eq_right h1]
    obtain ⟨p, a, m, hp, ha, hpm, hm, rfl⟩ := exists_prime_pow_mul (show 2 ≤ n by omega)
    rw [dsum_prime_pow_mul mobius hp hpm hm a]
    rw [gsum_two_terms ha (fun i hi => (dsum_congr (g := fun _ => 0) (fun e _ =>
      mobius_prime_pow_mul hp hi)).trans (dsum_zero' m))]
    rw [dsum_congr (f := fun e => mobius (p ^ 1 * e)) (g := fun e => -mobius e) (fun e he => by
      rw [Nat.pow_one]; exact mobius_prime_mul hp (dvd_facts hpm hm he).1 (dvd_facts hpm hm he).2)]
    simp only [Nat.pow_zero, Nat.one_mul]
    unfold dsum
    rw [← gsum_add]
    exact (gsum_congr (g := fun _ => 0) (fun d _ => by split <;> grind)).trans (gsum_zero' _)

/-- `Λ(pᵃ) = log p` for a prime `p` and `a ≥ 1`. -/
theorem vonMangoldt_prime_pow {p a : Nat} (hp : Prime p) (ha : 1 ≤ a) : vonMangoldt (p ^ a) = lnat p := by
  unfold vonMangoldt
  have hp2 : 2 ≤ p := hp.1
  have huniq : ∀ r k, (Prime r ∧ 1 ≤ k ∧ r ^ k = p ^ a) ↔ (r = p ∧ k = a) := by
    intro r k; constructor
    · rintro ⟨hr, hk, he⟩
      have hrp : r = p := eq_of_prime_dvd_pow hr hp a
        (he ▸ ⟨r ^ (k - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩)
      subst hrp
      refine ⟨rfl, ?_⟩
      have h1 := vp_eq (p := r) (r := 1) hr.1 (m := r ^ k) (e := k) (by simp)
        (fun h => by have := Nat.le_of_dvd (by omega) h; omega)
      have h2 := vp_eq (p := r) (r := 1) hr.1 (m := r ^ a) (e := a) (by simp)
        (fun h => by have := Nat.le_of_dvd (by omega) h; omega)
      rw [he] at h1; omega
    · rintro ⟨rfl, rfl⟩; exact ⟨hp, ha, rfl⟩
  have hpa := le_of_prime_pow_eq hp ha rfl
  rw [gsum_congr (g := fun r => if r = p then lnat p else 0) (fun r _ => by
    by_cases hr : r = p
    · subst hr
      rw [ite_eq_left rfl, gsum_congr (g := fun k => if k = a then lnat r else 0) (fun k _ => by
        by_cases hk : k = a
        · rw [ite_eq_left ((huniq r k).2 ⟨rfl, hk⟩), ite_eq_left hk]
        · rw [ite_eq_right (fun h => hk ((huniq r k).1 h).2), ite_eq_right hk]),
        gsum_ite_eq, ite_eq_left (by omega)]
    · rw [ite_eq_right hr]
      exact (gsum_congr (g := fun _ => 0) (fun k _ => ite_eq_right (fun h => hr ((huniq r k).1 h).1))).trans
        (gsum_zero' _)), gsum_ite_eq, ite_eq_left (by omega)]

/-- `Λ(pᵃ m) = 0` if `p ∤ m` and `m > 1`: such a number is not a prime power. -/
theorem vonMangoldt_prime_pow_mul {p a m : Nat} (hp : Prime p) (ha : 1 ≤ a) (hpm : ¬ p ∣ m)
    (hm : 1 < m) : vonMangoldt (p ^ a * m) = 0 := by
  unfold vonMangoldt
  apply (gsum_congr (g := fun _ => 0) (fun r _ => ?_)).trans (gsum_zero' _)
  apply (gsum_congr (g := fun _ => 0) (fun k _ => ?_)).trans (gsum_zero' _)
  apply ite_eq_right
  rintro ⟨hr, hk, he⟩
  have hpr : p = r := eq_of_prime_dvd_pow hp hr k (he ▸ Nat.dvd_trans
    (show p ∣ p ^ a from ⟨p ^ (a - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩)
    (Nat.dvd_mul_right _ m))
  subst hpr
  have hp0 : 0 < p := by have := hp.1; omega
  have h1 := vp_eq (p := p) (r := 1) hp.1 (m := p ^ k) (e := k) (by simp)
    (fun h => by have := Nat.le_of_dvd (by omega) h; have := hp.1; omega)
  have h2 := vp_eq (p := p) (r := m) hp.1 (m := p ^ a * m) (e := a) rfl hpm
  rw [he] at h1
  have hka : k = a := by omega
  subst hka
  have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp0) (show p ^ k * m = p ^ k * 1 by
    rw [Nat.mul_one]; exact he.symm)
  omega

/-- **Möbius inversion of `log = 1 ∗ Λ`.** `Σ_{d ∣ n} μ(d) log d = −Λ(n)` for `n ≥ 1`. -/
theorem dsum_mobius_lnat {n : Nat} (hn : 0 < n) :
    dsum (fun d => mobius d * lnat d) n = -vonMangoldt n := by
  by_cases h1 : n = 1
  · subst h1; rw [dsum_one, lnat_one]
    have : vonMangoldt 1 = 0 := by
      have := vonMangoldt_prime_pow_mul (p := 2) (a := 0) (m := 1)
      unfold vonMangoldt
      apply (gsum_congr (g := fun _ => 0) (fun r _ => ?_)).trans (gsum_zero' _)
      apply (gsum_congr (g := fun _ => 0) (fun k _ => ?_)).trans (gsum_zero' _)
      apply ite_eq_right
      rintro ⟨hr, hk, he⟩
      have := le_of_prime_pow_eq hr hk he; have := hr.1; omega
    rw [this]; grind
  · obtain ⟨p, a, m, hp, ha, hpm, hm, rfl⟩ := exists_prime_pow_mul (show 2 ≤ n by omega)
    rw [dsum_prime_pow_mul _ hp hpm hm a]
    rw [gsum_two_terms ha (fun i hi => (dsum_congr (g := fun _ => 0) (fun e _ => by
      rw [mobius_prime_pow_mul hp hi]; grind)).trans (dsum_zero' m))]
    have hp0 : 0 < p := by have := hp.1; omega
    rw [dsum_congr (f := fun e => mobius (p ^ 1 * e) * lnat (p ^ 1 * e))
      (g := fun e => -(lnat p * mobius e) - mobius e * lnat e) (fun e he => by
      obtain ⟨h1, h2⟩ := dvd_facts hpm hm he
      rw [Nat.pow_one, mobius_prime_mul hp h1 h2, lnat_mul hp0 h2]; grind)]
    simp only [Nat.pow_zero, Nat.one_mul]
    have hsplit : dsum (fun e => mobius e * lnat e) m + dsum (fun e => -(lnat p * mobius e) -
        mobius e * lnat e) m = -(lnat p * dsum mobius m) := by
      unfold dsum
      rw [← gsum_add, ← gsum_mul_left, ← gsum_neg']
      apply gsum_congr; intro d _; split <;> grind
    rw [hsplit, dsum_mobius hm]
    by_cases hm1 : m = 1
    · subst hm1; rw [ite_eq_left rfl, Nat.mul_one, vonMangoldt_prime_pow hp ha]; grind
    · rw [ite_eq_right hm1, vonMangoldt_prime_pow_mul hp ha hpm (by omega)]; grind

end Foundations.NumberTheory
