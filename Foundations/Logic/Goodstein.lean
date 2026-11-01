import Foundations.Logic.Ordinals

/-!
# Goodstein's theorem

Write a number in **hereditary base `b`**: in base `b`, then write every exponent in
base `b`, and the exponents of the exponents, and so on. For example, in hereditary
base 2,

`266 = 2^8 + 2^3 + 2 = 2^(2^(2+1)) + 2^(2+1) + 2`.

The **Goodstein sequence** of `n` (Goodstein 1944) starts with `n` in hereditary base
2; each step replaces every `b` by `b + 1` ("bumps the base") and then subtracts `1`.
The numbers grow at first with breathtaking speed — the sequence of `4` exceeds
`10^{10^8}` before turning back — yet **Goodstein's theorem** says that every
Goodstein sequence eventually reaches `0`.

The proof is a beautiful use of transfinite ordinals. Replace the base `b`
everywhere by `ω`: the hereditary base-`b` representation of a number `n` becomes an
ordinal `ord_b(n)` below ε₀ in Cantor normal form. Bumping the base does **not**
change this ordinal (`ord_bump`), and subtracting `1` strictly decreases it (`ord_lt`).
So the Goodstein sequence induces a strictly decreasing sequence of ordinals below
ε₀, which must stop by the well-foundedness proved in `Ordinals`.

*The independence phenomenon.* Kirby and Paris (1982) proved that Goodstein's theorem,
although it is a statement about natural numbers expressible in the language of
arithmetic, is **not provable in Peano arithmetic** (we state this informally; it is
not formalised here). Our proof shows exactly where PA's strength runs out: we use the
well-foundedness of ε₀, the principle Gentzen (1936) showed sufficient for proving
PA consistent — and which PA itself therefore cannot prove. Goodstein's theorem is a
natural, concrete example of the incompleteness phenomenon of the previous files.

*Representation.* Our notations have no coefficients: a term `c·b^e` with `c < b` is
written as `c` equal summands `b^e`, i.e. `ω^e + ⋯ + ω^e`, which is exactly how the
ordinal `ω^e·c` is written in Cantor normal form. The base is always `c + 2 ≥ 2`.
-/

namespace Foundations.Logic.Ordinals

open ON

/-! ## Logarithms -/

/-- The integer logarithm: the largest `e` with `b^e ≤ n` (for `b ≥ 2`, `n ≥ 1`). -/
def lg (b n : Nat) : Nat := if h : 2 ≤ b ∧ b ≤ n then lg b (n / b) + 1 else 0
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- `b^lg(n) ≤ n`. -/
theorem pow_lg_le {b : Nat} (hb : 2 ≤ b) : ∀ n, 1 ≤ n → b ^ lg b n ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rw [lg]
    split
    · next h =>
        have hq : 1 ≤ n / b := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
        have := ih (n / b) (Nat.div_lt_self (by omega) (by omega)) hq
        rw [Nat.pow_succ]
        exact Nat.le_trans (Nat.mul_le_mul_right b this) (Nat.div_mul_le_self n b)
    · simpa using hn

/-- `n < b^(lg(n) + 1)`. -/
theorem lt_pow_lg {b : Nat} (hb : 2 ≤ b) : ∀ n, n < b ^ (lg b n + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [lg]
    split
    · next h =>
        have h₁ := ih (n / b) (Nat.div_lt_self (by omega) (by omega))
        have h₂ := Nat.lt_mul_div_succ n (show 0 < b by omega)
        calc n < b * (n / b + 1) := h₂
          _ ≤ b * b ^ (lg b (n / b) + 1) := Nat.mul_le_mul_left b h₁
          _ = b ^ (lg b (n / b) + 1 + 1) := by rw [Nat.mul_comm, ← Nat.pow_succ]
    · next h => simp; omega

/-- Comparing exponents through powers. -/
theorem exp_lt_of_pow {b f y x : Nat} (hb : 0 < b) (h₁ : b ^ f ≤ x) (h₂ : x < b ^ y) : f < y :=
  Classical.byContradiction fun h => by
    have := Nat.pow_le_pow_right hb (show y ≤ f by omega); omega

/-- The logarithm is characterised by its bounds. -/
theorem lg_eq_of {b e n : Nat} (hb : 2 ≤ b) (h₁ : b ^ e ≤ n) (h₂ : n < b ^ (e + 1)) :
    lg b n = e := by
  have hn : 1 ≤ n := Nat.le_trans (Nat.pow_pos (by omega)) h₁
  have a := exp_lt_of_pow (by omega) (pow_lg_le hb n hn) h₂
  have c := exp_lt_of_pow (by omega) h₁ (lt_pow_lg hb n)
  omega

/-- `k < b^k` for `b ≥ 2`. -/
theorem lt_pow_self' {b : Nat} (hb : 2 ≤ b) : ∀ k, k < b ^ k
  | 0 => by simp
  | k + 1 => by
      have := lt_pow_self' hb k
      rw [Nat.pow_succ]
      have : b ^ k * 2 ≤ b ^ k * b := Nat.mul_le_mul_left _ hb
      omega

/-- The logarithm of a positive number is smaller than it. -/
theorem lg_lt {b n : Nat} (hb : 2 ≤ b) (hn : n ≠ 0) : lg b n < n :=
  Nat.lt_of_lt_of_le (lt_pow_self' hb _) (pow_lg_le hb n (by omega))

/-! ## Hereditary base-`b` notation as an ordinal -/

/-- **The hereditary base-`(c+2)` representation** of `n`, as an ordinal notation:
`n = b^e + r` with `e = lg n` becomes `ω^{ord e} + ord r` — the base `b` is replaced by
`ω` throughout. -/
def ord (c n : Nat) : ON :=
  if h : n = 0 then .zero
  else .oadd (ord c (lg (c + 2) n)) (ord c (n - (c + 2) ^ lg (c + 2) n))
termination_by n
decreasing_by
  · exact lg_lt (by omega) h
  · have := Nat.pow_pos (n := lg (c + 2) n) (show 0 < c + 2 by omega); omega

/-- `ord` at `0`. -/
theorem ord_zero (c : Nat) : ord c 0 = .zero := by rw [ord]; simp

/-- `ord` at a positive number. -/
theorem ord_pos (c : Nat) {n : Nat} (h : n ≠ 0) :
    ord c n = .oadd (ord c (lg (c + 2) n)) (ord c (n - (c + 2) ^ lg (c + 2) n)) := by
  rw [ord]; simp [h]

/-- **Subtraction lowers the ordinal**: `ord` is strictly monotone. -/
theorem ord_lt (c : Nat) : ∀ n m, m < n → lt (ord c m) (ord c n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m hmn
    have hn : n ≠ 0 := by omega
    have hb : 2 ≤ c + 2 := by omega
    rw [ord_pos c hn]
    by_cases hm : m = 0
    · subst hm; rw [ord_zero]; exact zero_lt_oadd _ _
    rw [ord_pos c hm, lt_oadd]
    have he₁ := pow_lg_le hb n (by omega)
    have he₂ := lt_pow_lg hb n
    have hf₁ := pow_lg_le hb m (by omega)
    have hfe : lg (c + 2) m < lg (c + 2) n + 1 := exp_lt_of_pow (by omega) hf₁ (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hfe with h | h
    · exact Or.inl (ih _ (lg_lt hb hn) _ h)
    · refine Or.inr ⟨by rw [h], ?_⟩
      rw [h]
      exact ih _ (by have := Nat.pow_pos (n := lg (c+2) n) (show 0 < c + 2 by omega); omega) _
        (by rw [h] at hf₁; omega)

/-- **The hereditary representation is a Cantor normal form.** -/
theorem NF_ord (c : Nat) : ∀ n, NF (ord c n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have hb : 2 ≤ c + 2 := by omega
    by_cases hn : n = 0
    · subst hn; rw [ord_zero]; exact NF.zero
    rw [ord_pos c hn]
    have hpos := Nat.pow_pos (n := lg (c + 2) n) (show 0 < c + 2 by omega)
    refine NF.oadd (ih _ (lg_lt hb hn)) (ih _ (by omega)) fun a' b' he => ?_
    obtain ⟨r, hrdef⟩ : ∃ r, r = n - (c + 2) ^ lg (c + 2) n := ⟨_, rfl⟩
    rw [← hrdef] at he
    have hr : r ≠ 0 := by intro h0; rw [h0, ord_zero] at he; cases he
    rw [ord_pos c hr] at he
    injection he with ha' _
    subst ha'
    have hlr : lg (c + 2) r < lg (c + 2) n + 1 :=
      exp_lt_of_pow (by omega) (pow_lg_le hb r (by omega))
        (Nat.lt_of_le_of_lt (hrdef ▸ Nat.sub_le _ _) (lt_pow_lg hb n))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlr with h | h
    · exact lt_asymm (ord_lt c _ _ h)
    · rw [h]; exact lt_irrefl _

/-! ## Bumping the base -/

/-- Evaluating an ordinal notation at a base: `ω` is replaced by `B`. -/
def ev (B : Nat) : ON → Nat
  | .zero => 0
  | .oadd a b => B ^ ev B a + ev B b

/-- **Bumping the base**: write `n` in hereditary base `c + 2` and replace every
`c + 2` by `c + 3`. -/
def bump (c n : Nat) : Nat := ev (c + 3) (ord c n)

/-- Bumping `0`. -/
theorem bump_zero (c : Nat) : bump c 0 = 0 := by simp [bump, ord_zero, ev]

/-- Bumping a positive number. -/
theorem bump_pos (c : Nat) {n : Nat} (h : n ≠ 0) :
    bump c n = (c + 3) ^ bump c (lg (c + 2) n) + bump c (n - (c + 2) ^ lg (c + 2) n) := by
  simp only [bump]; rw [ord_pos c h]; rfl

/-- Arithmetic helper: `Z·(c+3) = (c+1)·Z + Z + Z`. -/
theorem mul_add_three (Z c : Nat) : Z * (c + 3) = (c + 1) * Z + Z + Z := by
  rw [Nat.mul_comm, show c + 3 = c + 1 + 1 + 1 from rfl, Nat.succ_mul, Nat.succ_mul]

/-- **The two key estimates on bumping**, proved by a joint strong induction:
bumping is strictly monotone, and if `r < k·b^e` with `k ≤ b` then
`bump r < k·(b+1)^{bump e}`. -/
theorem bump_main (c : Nat) : ∀ n, (∀ m, m < n → bump c m < bump c n) ∧
    (∀ r k, r < k * (c + 2) ^ n → k ≤ c + 2 → bump c r < k * (c + 3) ^ bump c n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hb : 2 ≤ c + 2 := by omega
  -- monotonicity at `n`
  have hM : ∀ m, m < n → bump c m < bump c n := by
    intro m hmn
    have hn : n ≠ 0 := by omega
    rw [bump_pos c hn]
    by_cases hm : m = 0
    · subst hm; rw [bump_zero]
      have := Nat.pow_pos (n := bump c (lg (c + 2) n)) (show 0 < c + 3 by omega); omega
    have he₁ := pow_lg_le hb n (by omega)
    have he₂ := lt_pow_lg hb n
    have hf₁ := pow_lg_le hb m (by omega)
    have hf₂ := lt_pow_lg hb m
    have hfe : lg (c + 2) m < lg (c + 2) n + 1 := exp_lt_of_pow (by omega) hf₁ (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hfe with h | h
    · -- smaller leading exponent
      have hm' : m < 1 * (c + 2) ^ lg (c + 2) n := by
        rw [Nat.one_mul]
        exact Nat.lt_of_lt_of_le hf₂ (Nat.pow_le_pow_right (by omega) h)
      have := (ih _ (lg_lt hb hn)).2 m 1 hm' (by omega)
      rw [Nat.one_mul] at this; omega
    · have hle : (c + 2) ^ lg (c + 2) n ≤ m := h ▸ hf₁
      have hpos := Nat.pow_pos (n := lg (c+2) n) (show 0 < c + 2 by omega)
      have := (ih (n - (c + 2) ^ lg (c + 2) n) (by omega)).1
        (m - (c + 2) ^ lg (c + 2) n) (Nat.sub_lt_sub_right hle hmn)
      rw [bump_pos c hm, h]
      omega
  refine ⟨hM, ?_⟩
  -- the bound at `n`, by induction on `r`
  intro r
  induction r using Nat.strongRecOn with
  | _ r ihr =>
  intro k hr hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hr
    · exact h
  have hYpos := Nat.pow_pos (n := bump c n) (show 0 < c + 3 by omega)
  by_cases hr0 : r = 0
  · subst hr0; rw [bump_zero]; exact Nat.mul_pos (by omega) hYpos
  have hf₁ := pow_lg_le hb r (by omega)
  have hf₂ := lt_pow_lg hb r
  have hkb : k * (c + 2) ^ n ≤ (c + 2) ^ (n + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm ((c + 2) ^ n)]; exact Nat.mul_le_mul_right _ hk
  have hfn : lg (c + 2) r < n + 1 := exp_lt_of_pow (by omega) hf₁ (by omega)
  rw [bump_pos c hr0]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hfn with h | h
  · -- leading exponent `f < n`
    have hs : r - (c + 2) ^ lg (c + 2) r < (c + 1) * (c + 2) ^ lg (c + 2) r := by
      rw [Nat.pow_succ, Nat.mul_succ] at hf₂
      rw [Nat.mul_comm]; omega
    have h₁ := (ih _ h).2 _ (c + 1) hs (by omega)
    have h₂ := hM _ h
    have h₃ : (c + 3) ^ (bump c (lg (c + 2) r) + 1) ≤ (c + 3) ^ bump c n :=
      Nat.pow_le_pow_right (by omega) h₂
    rw [Nat.pow_succ] at h₃
    have h₄ : (c + 3) ^ bump c n ≤ k * (c + 3) ^ bump c n := Nat.le_mul_of_pos_left _ hk1
    have h₅ := mul_add_three ((c + 3) ^ bump c (lg (c + 2) r)) c
    omega
  · -- leading exponent `f = n`
    rw [h]
    rw [h] at hf₁
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_mul] at hr ⊢
    have := ihr (r - (c + 2) ^ n)
      (by have := Nat.pow_pos (n := n) (show 0 < c + 2 by omega); omega) k' (by omega) (by omega)
    omega

/-- **Bumping the base does not change the ordinal.** The hereditary base-`(c+3)`
representation of `bump c n` is the hereditary base-`(c+2)` representation of `n`. -/
theorem ord_bump (c : Nat) : ∀ n, ord (c + 1) (bump c n) = ord c n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hb : 2 ≤ c + 2 := by omega
  by_cases hn : n = 0
  · subst hn; rw [bump_zero, ord_zero, ord_zero]
  have he₁ := pow_lg_le hb n (by omega)
  have he₂ := lt_pow_lg hb n
  have hpos := Nat.pow_pos (n := lg (c + 2) n) (show 0 < c + 2 by omega)
  have hr : n - (c + 2) ^ lg (c + 2) n < (c + 1) * (c + 2) ^ lg (c + 2) n := by
    rw [Nat.pow_succ, Nat.mul_succ] at he₂
    rw [Nat.mul_comm]; omega
  have hR := (bump_main c (lg (c + 2) n)).2 _ (c + 1) hr (by omega)
  have hm := bump_pos c hn
  have hYpos := Nat.pow_pos (n := bump c (lg (c + 2) n)) (show 0 < c + 3 by omega)
  have hlg : lg (c + 1 + 2) (bump c n) = bump c (lg (c + 2) n) := by
    refine lg_eq_of (by omega) (by rw [hm]; exact Nat.le_add_right _ _) ?_
    rw [hm]
    show _ < (c + 3) ^ (bump c (lg (c + 2) n) + 1)
    rw [Nat.pow_succ]
    have := mul_add_three ((c + 3) ^ bump c (lg (c + 2) n)) c
    omega
  have hbn : bump c n ≠ 0 := by omega
  rw [ord_pos (c + 1) hbn, hlg, ord_pos c hn]
  have hsub : bump c n - (c + 1 + 2) ^ bump c (lg (c + 2) n) =
      bump c (n - (c + 2) ^ lg (c + 2) n) := by
    rw [hm]; show (c + 3) ^ _ + _ - (c + 3) ^ _ = _; omega
  rw [hsub, ih _ (lg_lt hb hn), ih _ (by omega)]

/-! ## Goodstein's theorem -/

/-- **The Goodstein sequence** of `n`: start with `n`; at step `k` (current base
`k + 2`) bump the base to `k + 3` and subtract `1`. -/
def goodstein (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => bump k (goodstein n k) - 1

/-- A positive number bumps to a positive number. -/
theorem bump_ne_zero (c : Nat) {n : Nat} (h : n ≠ 0) : bump c n ≠ 0 := by
  rw [bump_pos c h]
  have := Nat.pow_pos (n := bump c (lg (c + 2) n)) (show 0 < c + 3 by omega); omega

/-- While the Goodstein sequence is positive, its ordinals strictly decrease. -/
theorem goodstein_ord_lt (n k : Nat) (h : goodstein n k ≠ 0) :
    lt (ord (k + 1) (goodstein n (k + 1))) (ord k (goodstein n k)) := by
  show lt (ord (k + 1) (bump k (goodstein n k) - 1)) _
  rw [← ord_bump k (goodstein n k)]
  exact ord_lt (k + 1) _ _ (by have := bump_ne_zero k h; omega)

/-- **Goodstein's theorem** (Goodstein 1944). Every Goodstein sequence eventually
reaches `0`. (By Kirby–Paris 1982 this is not provable in Peano arithmetic; our proof
uses the well-foundedness of ε₀ from `Ordinals`.) -/
theorem goodstein_terminates (n : Nat) : ∃ k, goodstein n k = 0 := by
  refine Classical.byContradiction fun hne => ?_
  have h : ∀ k, goodstein n k ≠ 0 := fun k hk => hne ⟨k, hk⟩
  exact no_infinite_descent (fun k => ord k (goodstein n k))
    fun k => ⟨NF_ord _ _, goodstein_ord_lt n k (h k)⟩

end Foundations.Logic.Ordinals
