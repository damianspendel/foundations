import Foundations.NumberTheory.PrimorialBound

/-!
# Bertrand's postulate

In 1845 Joseph Bertrand, checking tables up to three million, conjectured that for every
`n > 1` there is a prime between `n` and `2n`. He needed it for a theorem about permutation
groups. **Chebyshev** proved it in 1852, as a by-product of his estimates showing that the
number `π(x)` of primes up to `x` is of order `x / log x`. In 1919 **Ramanujan** gave a much
shorter proof using properties of the Gamma function, and in 1932 the nineteen-year-old
**Paul Erdős** made it entirely elementary — his first paper. That is the proof formalised here.

## Erdős's argument

Suppose there is no prime `p` with `n < p ≤ 2n`. Look at `C(2n, n)` and its prime
factorisation (file `Binomial`):

* no prime factor exceeds `2n`, and by assumption none lies in `(n, 2n]`;
* none lies in `(2n/3, n]` (Erdős's observation);
* primes `p > √(2n)` occur at most once, and every prime power factor is at most `2n`.

So `C(2n, n)` is at most `(2n)^(√(2n)+1)` (for the small primes) times the product of the primes
`≤ 2n/3`, which is at most `4^(2n/3)` by the primorial bound. But `C(2n, n) ≥ 4ⁿ / (2n + 1)`.
Hence `4^(n/3) ≤ (2n + 1) · (2n)^(√(2n)+1)`. The left side grows exponentially in `n`, the
right side only like `exp(c · √n · log n)`; for `n ≥ 1152` the inequality fails (we check this
with crude but fully elementary estimates: `a + 1 ≤ 2^(a/8)` for `a = ⌊√(2n)⌋ ≥ 48`).

For `n < 1152` we exhibit primes directly: `2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259`
— each less than twice its predecessor — so every interval `(n, 2n]` with `n < 1259` contains
one of them. Primality of each is checked by the Lean kernel (by `decide`, no `native_decide`).

## Beyond Bertrand

Bertrand's postulate is a weak form of the **prime number theorem**, `π(x) ∼ x / log x`,
conjectured by Gauss and Legendre around 1800 and proved in 1896 by Hadamard and de la Vallée
Poussin using complex analysis (the zeros of the Riemann zeta function); elementary proofs were
found by Selberg and Erdős in 1949. The prime number theorem gives a prime in `(n, (1 + ε) n]`
for every `ε > 0` and large `n`; whether there is always a prime between consecutive squares
(Legendre's conjecture) is still open.
-/

namespace Foundations.NumberTheory

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Bounding a number by its prime-power factors -/

/-- **Bounding a number by its prime-power divisors.** Suppose every prime factor of `m > 0`
is below `B`, and every prime power `pᵉ` dividing `m` is at most `f(p)`, where all `f(i) ≥ 1`.
Then `m ≤ ∏_{i<B} f(i)`. (Split off the full power of one prime factor and recurse.) -/
theorem le_bprod_of_pow_dvd {B : Nat} : ∀ (m : Nat) (f : Nat → Nat), 0 < m → (∀ i, 1 ≤ f i) →
    (∀ p e, Prime p → p ^ e ∣ m → p ^ e ≤ f p) → (∀ p, Prime p → p ∣ m → p < B) →
    m ≤ bprod f B := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro f hm hf hpow hB
    by_cases h1 : m = 1
    · subst h1; exact bprod_pos (fun i => hf i) B
    · obtain ⟨p, hp, hpm⟩ := exists_prime_dvd (n := m) (by omega)
      have hp1 : 1 < p := hp.1
      obtain ⟨r, hr, hpr⟩ := vp_spec hp1 hm
      have he : 1 ≤ vp p m := (pow_dvd_iff_le_vp hp1 hm).1 (by simpa using hpm)
      have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; exact hpr (Nat.dvd_zero p))
      have hpe : 2 ≤ p ^ vp p m := by
        have := Nat.pow_le_pow_right (show 0 < p by omega) he
        simp at this; omega
      have hrm : r < m := by
        have : 2 * r ≤ p ^ vp p m * r := Nat.mul_le_mul_right r hpe
        omega
      have hrdvd : r ∣ m := ⟨p ^ vp p m, by rw [Nat.mul_comm]; exact hr⟩
      have hrle := ih r hrm (fun i => if i = p then 1 else f i) hr0
        (fun i => by split <;> simp [hf i])
        (fun q k hq hqk => by
          by_cases hqp : q = p
          · subst hqp
            simp only [↓reduceIte]
            rcases Nat.eq_zero_or_pos k with hk | hk
            · subst hk; simp
            · exfalso; apply hpr
              exact Nat.dvd_trans (by simpa using Nat.pow_dvd_pow q hk) hqk
          · simp only [hqp, ↓reduceIte]
            exact hpow q k hq (Nat.dvd_trans hqk hrdvd))
        (fun q hq hqr => hB q hq (Nat.dvd_trans hqr hrdvd))
      have hpf := hpow p (vp p m) hp ⟨r, hr⟩
      rw [bprod_update f (hB p hp hpm)]
      calc m = p ^ vp p m * r := hr
        _ ≤ f p * bprod (fun i => if i = p then 1 else f i) B := Nat.mul_le_mul hpf hrle

/-! ## The analytic inequality, elementarily -/

/-- Every `N` has an integer square root: `a² ≤ N < (a + 1)²`. -/
theorem exists_sqrt (N : Nat) : ∃ a, a * a ≤ N ∧ N < (a + 1) * (a + 1) := by
  induction N with
  | zero => exact ⟨0, by omega, by omega⟩
  | succ N ih =>
    obtain ⟨a, h1, h2⟩ := ih
    by_cases h : N + 1 < (a + 1) * (a + 1)
    · exact ⟨a, by omega, h⟩
    · have e : (a + 1 + 1) * (a + 1 + 1) = (a + 1) * (a + 1) + 2 * a + 3 := by grind
      exact ⟨a + 1, by omega, by omega⟩

/-- `8j + 8 ≤ 2ʲ` for `j ≥ 6`. -/
theorem eight_mul_add_le_two_pow : ∀ j, 6 ≤ j → 8 * j + 8 ≤ 2 ^ j := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h6 : j = 5
    · subst h6; decide
    · have := ih (by omega); rw [Nat.pow_succ]; omega

/-- **The final inequality.** If `a = ⌊√(2n)⌋ ≥ 48`, then
`(2n + 1) · (2n)^(a+1) · 4^⌊2n/3⌋ < 4ⁿ`. -/
theorem final_inequality {a n : Nat} (ha : 48 ≤ a) (h1 : a * a ≤ 2 * n)
    (h2 : 2 * n < (a + 1) * (a + 1)) :
    (2 * n + 1) * ((2 * n) ^ (a + 1) * 4 ^ (2 * n / 3)) < 4 ^ n := by
  -- Step 1: `(a + 1)^(6a+12) < 2^(a²)`, via `a + 1 ≤ 2^j` with `j = ⌊a/8⌋`.
  have hj := eight_mul_add_le_two_pow (a / 8) (by omega)
  have ha1 : a + 1 ≤ 2 ^ (a / 8) := by omega
  have hexp : a / 8 * (6 * a + 12) < a * a := by
    have e1 : 8 * (a / 8 * (6 * a + 12)) ≤ a * (6 * a + 12) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
    have e2 : a * (6 * a + 12) = 6 * (a * a) + 12 * a := by grind
    have e3 : 48 * a ≤ a * a := Nat.mul_le_mul_right a ha
    omega
  have hA : (a + 1) ^ (6 * a + 12) < 2 ^ (a * a) :=
    calc (a + 1) ^ (6 * a + 12) ≤ (2 ^ (a / 8)) ^ (6 * a + 12) := Nat.pow_le_pow_left ha1 _
      _ = 2 ^ (a / 8 * (6 * a + 12)) := by rw [← Nat.pow_mul]
      _ < 2 ^ (a * a) := Nat.pow_lt_pow_right (by omega) hexp
  -- Step 2: `(a + 1)^(2a+4) < 4^t` with `t = n − ⌊2n/3⌋`, by taking cube roots.
  have hfour : ∀ k, 4 ^ k = 2 ^ (2 * k) := fun k => by
    rw [Nat.pow_mul]
  have hB : (a + 1) ^ (2 * a + 4) < 4 ^ (n - 2 * n / 3) := by
    have hc : ((a + 1) ^ (2 * a + 4)) ^ 3 < (4 ^ (n - 2 * n / 3)) ^ 3 := by
      rw [← Nat.pow_mul, ← Nat.pow_mul, hfour]
      calc (a + 1) ^ ((2 * a + 4) * 3) = (a + 1) ^ (6 * a + 12) := by congr 1; omega
        _ < 2 ^ (a * a) := hA
        _ ≤ 2 ^ (2 * ((n - 2 * n / 3) * 3)) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (Nat.pow_lt_pow_iff_left (by omega)).1 hc
  -- Step 3: assemble, using `2n + 1 ≤ (a + 1)²` and `2n ≤ (a + 1)²`.
  have hsq : (a + 1) * (a + 1) = (a + 1) ^ 2 := (Nat.pow_two _).symm
  have s1 : 2 * n + 1 ≤ (a + 1) ^ 2 := by omega
  have s2 : (2 * n) ^ (a + 1) ≤ (a + 1) ^ (2 * a + 2) := by
    calc (2 * n) ^ (a + 1) ≤ ((a + 1) ^ 2) ^ (a + 1) := Nat.pow_le_pow_left (by omega) _
      _ = (a + 1) ^ (2 * a + 2) := by rw [← Nat.pow_mul, show 2 * (a + 1) = 2 * a + 2 by omega]
  calc (2 * n + 1) * ((2 * n) ^ (a + 1) * 4 ^ (2 * n / 3))
      ≤ (a + 1) ^ 2 * ((a + 1) ^ (2 * a + 2) * 4 ^ (2 * n / 3)) :=
        Nat.mul_le_mul s1 (Nat.mul_le_mul_right _ s2)
    _ = (a + 1) ^ (2 * a + 4) * 4 ^ (2 * n / 3) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, show 2 + (2 * a + 2) = 2 * a + 4 by omega]
    _ < 4 ^ (n - 2 * n / 3) * 4 ^ (2 * n / 3) :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by omega))).2 hB
    _ = 4 ^ n := by rw [← Nat.pow_add]; congr 1; omega

/-! ## Large `n` -/

/-- **Bertrand's postulate for `n ≥ 1152`**, by Erdős's argument. -/
theorem bertrand_large {n : Nat} (hn : 1152 ≤ n) : ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n := by
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ p, Prime p → n < p → 2 * n < p := fun p hp h =>
    Classical.byContradiction fun h' => hno ⟨p, hp, h, by omega⟩
  obtain ⟨a, ha1, ha2⟩ := exists_sqrt (2 * n)
  have ha48 : 48 ≤ a := by
    apply Classical.byContradiction
    intro h
    have : (a + 1) * (a + 1) ≤ 48 * 48 := Nat.mul_le_mul (by omega) (by omega)
    omega
  -- The bounding function: `2n` for small primes, `p` for the other primes `≤ 2n/3`.
  let f : Nat → Nat := fun i =>
    if Prime i ∧ 3 * i ≤ 2 * n then (if i * i ≤ 2 * n then 2 * n else i) else 1
  have hf : ∀ i, 1 ≤ f i := fun i => by
    by_cases h : Prime i ∧ 3 * i ≤ 2 * n
    · have := h.1.1; simp only [f, h, and_self, ↓reduceIte]; split <;> omega
    · simp only [f, h, ↓reduceIte]; omega
  have hC : centralBinom n ≤ bprod f (2 * n + 1) := by
    apply le_bprod_of_pow_dvd _ f (centralBinom_pos n) hf
    · intro q e hq hqe
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he; simpa using hf q
      have hqC : q ∣ centralBinom n := Nat.dvd_trans (by simpa using Nat.pow_dvd_pow q he) hqe
      have hq2n := prime_dvd_centralBinom_le hq hqC
      have hqn : q ≤ n := Classical.byContradiction fun h => by have := hno' q hq (by omega); omega
      have hq3 : 3 * q ≤ 2 * n := Classical.byContradiction fun h =>
        not_dvd_centralBinom hq (by omega) hqn (by omega) hqC
      have hfq : f q = if q * q ≤ 2 * n then 2 * n else q := by
        simp only [f, hq, hq3, and_self, ↓reduceIte]
      rw [hfq]
      by_cases hsq : q * q ≤ 2 * n
      · simp only [hsq, ↓reduceIte]; exact pow_dvd_centralBinom_le hq he hqe
      · simp only [hsq, ↓reduceIte]
        have he1 : e = 1 := Classical.byContradiction fun h => by
          have h2 : q * q ∣ centralBinom n :=
            Nat.dvd_trans (by rw [← Nat.pow_two]; exact Nat.pow_dvd_pow q (by omega)) hqe
          exact hsq (sq_dvd_centralBinom_le hq h2)
        subst he1; simp
    · intro q hq hqC
      have := prime_dvd_centralBinom_le hq hqC; omega
  -- Split the bound into small primes and the primorial of `2n/3`.
  let g : Nat → Nat := fun i => if Prime i ∧ i * i ≤ 2 * n then 2 * n else 1
  let h : Nat → Nat := fun i => if Prime i ∧ 3 * i ≤ 2 * n then i else 1
  have hfgh : bprod f (2 * n + 1) ≤ bprod g (2 * n + 1) * bprod h (2 * n + 1) := by
    rw [← bprod_mul]
    apply bprod_le_bprod
    intro i _
    by_cases hp : Prime i
    · have := hp.1
      by_cases h3 : 3 * i ≤ 2 * n <;> by_cases hs : i * i ≤ 2 * n <;>
        simp only [f, g, h, hp, h3, hs, and_self, and_false, ↓reduceIte, Nat.one_mul,
          Nat.mul_one] <;> try omega
      exact Nat.le_mul_of_pos_right _ (by omega)
    · simp [f, g, h, hp]
  have hg : bprod g (2 * n + 1) ≤ (2 * n) ^ (a + 1) := by
    apply bprod_le_pow (by omega)
    · intro i hi
      simp only [g]
      split
      · next hh =>
        have : (a + 1) * (a + 1) ≤ i * i := Nat.mul_le_mul hi hi
        omega
      · rfl
    · intro i; simp only [g]; split <;> omega
  have hh : bprod h (2 * n + 1) = primorial (2 * n / 3) := by
    unfold primorial
    rw [bprod_eq_of_one (A := 2 * n / 3 + 1) (fun i hi => by
      simp only [h]; split
      · next hh => omega
      · rfl) (by omega)]
    apply bprod_congr
    intro i hi
    simp only [h, show 3 * i ≤ 2 * n by omega, and_true]
  have hprim := primorial_le_four_pow (2 * n / 3)
  have hlow := four_pow_le_centralBinom n
  have hfin := final_inequality ha48 ha1 ha2
  have : (2 * n + 1) * centralBinom n ≤ (2 * n + 1) * ((2 * n) ^ (a + 1) * 4 ^ (2 * n / 3)) := by
    apply Nat.mul_le_mul_left
    calc centralBinom n ≤ bprod g (2 * n + 1) * bprod h (2 * n + 1) := Nat.le_trans hC hfgh
      _ ≤ (2 * n) ^ (a + 1) * 4 ^ (2 * n / 3) := Nat.mul_le_mul hg (hh ▸ hprim)
  omega

/-! ## Small `n` -/

set_option maxRecDepth 20000 in
/-- The primes of the Bertrand chain, checked by the kernel. -/
theorem bertrand_chain_prime :
    Prime 2 ∧ Prime 3 ∧ Prime 5 ∧ Prime 7 ∧ Prime 13 ∧ Prime 23 ∧ Prime 43 ∧ Prime 83 ∧
      Prime 163 ∧ Prime 317 ∧ Prime 631 ∧ Prime 1259 := by
  decide

/-- **Bertrand's postulate for `1 ≤ n < 1152`**: each interval `(n, 2n]` contains one of the
primes `2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259`. -/
theorem bertrand_small {n : Nat} (h1 : 1 ≤ n) (h2 : n < 1152) :
    ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n := by
  obtain ⟨p2, p3, p5, p7, p13, p23, p43, p83, p163, p317, p631, p1259⟩ := bertrand_chain_prime
  by_cases c : n < 2;   · exact ⟨2, p2, by omega, by omega⟩
  by_cases c : n < 3;   · exact ⟨3, p3, by omega, by omega⟩
  by_cases c : n < 5;   · exact ⟨5, p5, by omega, by omega⟩
  by_cases c : n < 7;   · exact ⟨7, p7, by omega, by omega⟩
  by_cases c : n < 13;  · exact ⟨13, p13, by omega, by omega⟩
  by_cases c : n < 23;  · exact ⟨23, p23, by omega, by omega⟩
  by_cases c : n < 43;  · exact ⟨43, p43, by omega, by omega⟩
  by_cases c : n < 83;  · exact ⟨83, p83, by omega, by omega⟩
  by_cases c : n < 163; · exact ⟨163, p163, by omega, by omega⟩
  by_cases c : n < 317; · exact ⟨317, p317, by omega, by omega⟩
  by_cases c : n < 631; · exact ⟨631, p631, by omega, by omega⟩
  exact ⟨1259, p1259, by omega, by omega⟩

/-! ## The theorem -/

/-- **Bertrand's postulate** (conjectured by Bertrand 1845, proved by Chebyshev 1852; this is
Erdős's 1932 proof). For every `n ≥ 1` there is a prime `p` with `n < p ≤ 2n`. -/
theorem bertrand (n : Nat) (hn : 1 ≤ n) : ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n := by
  by_cases h : n < 1152
  · exact bertrand_small hn h
  · exact bertrand_large (by omega)

/-- A corollary: for every prime `p` the next prime is less than `2p` — more precisely, there is
a prime `q` with `p < q < 2p`. -/
theorem exists_prime_between_p_two_p {p : Nat} (hp : Prime p) : ∃ q, Prime q ∧ p < q ∧ q < 2 * p := by
  obtain ⟨q, hq, h1, h2⟩ := bertrand p (by have := hp.1; omega)
  refine ⟨q, hq, h1, ?_⟩
  rcases Nat.lt_or_ge q (2 * p) with h | h
  · exact h
  · exfalso
    have hq2 : q = 2 * p := by omega
    rcases hq.2 2 ⟨p, hq2⟩ with h' | h' <;> have := hp.1 <;> omega

end Foundations.NumberTheory
