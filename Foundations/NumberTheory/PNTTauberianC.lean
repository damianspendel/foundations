import Foundations.NumberTheory.PNTTauberianB

/-!
# The prime number theorem

This file completes the Erdős–Selberg proof. The engine is an **improvement lemma**:

  if `|V(n)| ≤ α` for all large `n`, where `ε ≤ α ≤ C₀`, then `|V(n)| ≤ α − δ` for all large `n`,

with `δ = δ(ε) > 0` independent of `α`. Iterating it finitely often brings the bound below any
`ε`, so `V(n) = ψ(n)/n − 1 → 0`: **`ψ(N) ∼ N`**, which by the equivalences of
`PNTEquivalence` is the prime number theorem `π(N) ∼ N / log N`.

The proof of the improvement lemma is the weighted-average argument. In

  `|V(N)| log² N ≤ Σ_{k ≤ N} (a(k)/k) |V(⌊N/k⌋)| + O(log N)`

every term has `|V(⌊N/k⌋)| ≤ α` except for `k > N/Y₀` (a tail of weight `O(log N)`). Choose
good intervals `[m_j, m_j + m_j/T]` (where `|V| ≤ ε/2`) inside the multiplicatively spaced
ranges `(Y_j, K Y_j]`, `Y_j = Y₀ (2K)^j`; for `j < J ≈ log N / (2 log 2K)` the corresponding
ranges of `k` are disjoint and each carries weight `≥ (log N)/(8T) − O(1)`. So a proportion
`≈ 1/(16 T log 2K)` of the total weight `log² N` sits on values `≤ ε/2 ≤ α − ε/2`, and the
average drops by about `ε/(32 T log 2K)`; after allowing for the error terms we take
`δ = ε/(32 T log (2K)²) = ε/(64 T log 2K)`.

## Historical note

This is, in substance, the argument of Selberg's 1949 paper, streamlined in the manner of
Levinson's "motivated account" (1969) and of the treatment in Hardy and Wright (ch. XXII).
It is elementary in the technical sense — no complex numbers, no Fourier analysis, no zeta
function — but it is not short: in this development it rests on fifteen files and some
5 000 lines, from Chebyshev's functions through Mertens' theorems, Möbius inversion, the
Tatuzawa–Iseki identity, Euler's constant and Stirling's formula to Selberg's formula and its
iteration. Hadamard and de la Vallée Poussin needed the zeros of `ζ(s)`; Erdős and Selberg showed
that the theorem is, after all, a statement about finite sums of logarithms.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- Sums restricted to `k > c`: `Σ_{k ≤ N} [c < k] f(k) = F(N) − F(c)` for `c ≤ N`. -/
theorem fsum_ite_gt (f : Nat → R) {c N : Nat} (hc : c ≤ N) :
    fsum (fun k => if c < k then f k else 0) (N + 1) = fsum f (N + 1) - fsum f (c + 1) := by
  have e1 : fsum (fun k => if c < k then f k else 0) (N + 1) =
      fsum (fun k => if c < k then f k else 0) (c + 1) +
        fsum (fun j => if c < c + 1 + j then f (c + 1 + j) else 0) (N - c) := by
    rw [← fsum_split]; congr 1; omega
  have e2 : fsum f (N + 1) = fsum f (c + 1) + fsum (fun j => f (c + 1 + j)) (N - c) := by
    rw [← fsum_split]; congr 1; omega
  rw [e1, e2]
  rw [fsum_congr (n := c + 1) (b := fun _ => 0) (fun k hk => by
    simp only [show ¬ c < k by omega, ↓reduceIte]), fsum_zeros]
  rw [fsum_congr (n := N - c) (b := fun j => f (c + 1 + j)) (fun j _ => by
    simp only [show c < c + 1 + j by omega, ↓reduceIte])]
  grind

/-- Comparing block sums: if `c f(k) ≤ g(k)` on `(lo, hi]` then
`c (F(hi) − F(lo)) ≤ G(hi) − G(lo)`. -/
theorem block_compare (f g : Nat → R) (c : R) {lo hi : Nat} (hlh : lo ≤ hi)
    (h : ∀ k, lo < k → k ≤ hi → c * f k ≤ g k) :
    c * (fsum f (hi + 1) - fsum f (lo + 1)) ≤ fsum g (hi + 1) - fsum g (lo + 1) := by
  have e1 : fsum f (hi + 1) = fsum f (lo + 1) + fsum (fun j => f (lo + 1 + j)) (hi - lo) := by
    rw [← fsum_split]; congr 1; omega
  have e2 : fsum g (hi + 1) = fsum g (lo + 1) + fsum (fun j => g (lo + 1 + j)) (hi - lo) := by
    rw [← fsum_split]; congr 1; omega
  rw [e1, e2]
  have := fsum_le_fsum' (a := fun j => c * f (lo + 1 + j)) (b := fun j => g (lo + 1 + j))
    (n := hi - lo) (fun j hj => h _ (by omega) (by omega))
  rw [fsum_const_mul] at this
  grind

/-- `log b > 0` for `b ≥ 2`. -/
theorem log_pos_nat {b : Nat} (hb : 2 ≤ b) : 0 < R.log (b : R) :=
  log_pos' (by have : (2 : R) ≤ (b : R) := by
                  have h : ((2 : Nat) : R) ≤ (b : R) := natCast_le' hb
                  grind
               grind)

/-- **The combinatorial core of the improvement.** Suppose `|V(n)| ≤ α` for `n ≥ N₀`, and
`m_j` (`j = 0, 1, …`) are left ends of good intervals (`|V| ≤ ε/2` on `[m_j, m_j + ⌊m_j/T⌋]`),
increasing fast enough (`m_{j+1} ≥ m_j + ⌊m_j/T⌋`), with `m_j ≥ Y₀ ≥ N₀`, `m_j ≥ 2T`, and
`64 T² m_j² ≤ N` for `j < J`. Then, with `S = Σ_{k ≤ N} (a(k)/k) |V(⌊N/k⌋)|`,
`8T (α F(N) + C₀ (F(N) − F(N/Y₀)) − S) ≥ J (α − ε/2)(log N − 16 T KA)`. -/
theorem good_weight {ε α : R} (hεα : ε ≤ α) (hε : 0 < ε) {N₀ Y₀ T N J : Nat} (hT : 1 ≤ T)
    (hY₀ : N₀ ≤ Y₀) (hY₁ : 1 ≤ Y₀)
    (hα : ∀ n, N₀ ≤ n → abs (vrem n) ≤ α) (m : Nat → Nat) (hmY : ∀ j, Y₀ ≤ m j)
    (hmT : ∀ j, 2 * T ≤ m j) (hminc : ∀ j, m j + m j / T ≤ m (j + 1))
    (hgood : ∀ j n, m j ≤ n → n ≤ m j + m j / T → abs (vrem n) ≤ ε / 2)
    (hJ : ∀ j, j < J → 64 * (T * T) * (m j * m j) ≤ N) :
    (J : R) * ((α - ε / 2) * (R.log (N : R) - 16 * (T : R) * KA)) ≤
      8 * (T : R) * (α * wsum N + C0 * (wsum N - wsum (N / Y₀)) -
        fsum (fun k => selA k * (1 / (k : R)) * abs (vrem (N / k))) (N + 1)) := by
  have hα0 : 0 ≤ α := by grind
  have hC0 := one_le_C0
  let g : Nat → R := fun k => selA k * (1 / (k : R)) *
    (α + (if N / Y₀ < k then C0 else 0) - abs (vrem (N / k)))
  -- `Σ g = α F(N) + C₀ (F(N) − F(N/Y₀)) − S`.
  have hG : fsum g (N + 1) = α * wsum N + C0 * (wsum N - wsum (N / Y₀)) -
      fsum (fun k => selA k * (1 / (k : R)) * abs (vrem (N / k))) (N + 1) := by
    have h1 := fsum_ite_gt (fun k => C0 * (selA k * (1 / (k : R)))) (Nat.div_le_self N Y₀)
    rw [fsum_const_mul, fsum_const_mul] at h1
    unfold wsum
    have h1' : C0 * (fsum (fun k => selA k * (1 / (k : R))) (N + 1) -
        fsum (fun k => selA k * (1 / (k : R))) (N / Y₀ + 1)) =
        fsum (fun k => if N / Y₀ < k then C0 * (selA k * (1 / (k : R))) else 0) (N + 1) := by
      rw [h1]; grind
    rw [h1', ← fsum_const_mul, ← fsum_add, ← fsum_sub]
    apply fsum_congr; intro k _
    simp only [g]; split <;> grind
  -- `g ≥ 0`.
  have hg0 : ∀ k, k ≤ N → 0 ≤ g k := by
    intro k _
    simp only [g]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [selA_zero]; grind
    · have hw : 0 ≤ selA k * (1 / (k : R)) :=
        OrderedRing.mul_nonneg (selA_nonneg k) (Std.le_of_lt (div_pos (by grind) (natCast_pos' hk)))
      apply OrderedRing.mul_nonneg hw
      split
      · have := abs_vrem_le (N / k); grind
      · next h =>
        have hkY : Y₀ ≤ N / k := (Nat.le_div_iff_mul_le hk).2 (by
          have := (Nat.le_div_iff_mul_le (show 0 < Y₀ by omega)).1 (show k ≤ N / Y₀ by omega)
          rw [Nat.mul_comm]; exact this)
        have := hα (N / k) (by omega); grind
  -- The blocks.
  let hi : Nat → Nat := fun j => N / m j
  let lo : Nat → Nat := fun j => N / (m j + m j / T)
  have hlh : ∀ j, lo j ≤ hi j := fun j =>
    Nat.div_le_div_left (Nat.le_add_right _ _) (by have := hmT j; omega)
  have hdec : ∀ j, hi (j + 1) ≤ lo j := fun j =>
    Nat.div_le_div_left (hminc j)
      (Nat.lt_of_lt_of_le (by have := hmT j; omega) (Nat.le_add_right _ _))
  have hpeel := peel_blocks g hg0 lo hi hlh hdec (Nat.div_le_self N (m 0)) J
  -- Each block: `8T (G(hi) − G(lo)) ≥ (α − ε/2)(log N − 16 T KA)`.
  have hblock : ∀ j, j < J → (α - ε / 2) * (R.log (N : R) - 16 * (T : R) * KA) ≤
      8 * (T : R) * (fsum g (hi j + 1) - fsum g (lo j + 1)) := by
    intro j hj
    have hbl := block_lower hT (hmT j) (hJ j hj)
    have hcmp := block_compare (fun k => selA k * (1 / (k : R))) g (α - ε / 2) (hlh j)
      (fun k hk1 hk2 => by
        have hk : 0 < k := by omega
        have hmj : 0 < m j := by have := hmT j; omega
        have hm'j : 0 < m j + m j / T := Nat.lt_of_lt_of_le hmj (Nat.le_add_right _ _)
        -- `⌊N/k⌋ ∈ [m_j, m_j + ⌊m_j/T⌋]`.
        have hl : m j ≤ N / k := (Nat.le_div_iff_mul_le hk).2 (by
          have := (Nat.le_div_iff_mul_le hmj).1 (show k ≤ N / m j from hk2)
          rw [Nat.mul_comm]; exact this)
        have hu : N / k ≤ m j + m j / T := by
          have h1 : N < k * (m j + m j / T) := (Nat.div_lt_iff_lt_mul hm'j).1 hk1
          have h2 : N / k < m j + m j / T := (Nat.div_lt_iff_lt_mul hk).2 (by
            rw [Nat.mul_comm]; exact h1)
          omega
        have hV := hgood j (N / k) hl hu
        have hnot : ¬ N / Y₀ < k := by
          have : N / m j ≤ N / Y₀ := Nat.div_le_div_left (hmY j) (by omega)
          have : k ≤ N / m j := hk2
          omega
        have hw : 0 ≤ selA k * (1 / (k : R)) :=
          OrderedRing.mul_nonneg (selA_nonneg k) (Std.le_of_lt (div_pos (by grind) (natCast_pos' hk)))
        simp only [g, hnot, ↓reduceIte]
        have := OrderedRing.mul_le_mul_of_nonneg_left
          (show α - ε / 2 ≤ α + 0 - abs (vrem (N / k)) by grind) hw
        grind)
    unfold wsum at hbl
    have k1 := OrderedRing.mul_le_mul_of_nonneg_left hbl (show 0 ≤ α - ε / 2 by grind)
    have k2 := OrderedRing.mul_le_mul_of_nonneg_left hcmp (show 0 ≤ 8 * (T : R) by
      have := natCast_nonneg' T; grind)
    generalize fsum (fun k => selA k * (1 / (k : R))) (hi j + 1) -
      fsum (fun k => selA k * (1 / (k : R))) (lo j + 1) = Δ at k1 k2
    grind
  have hsum := fsum_le_fsum' (a := fun _ => (α - ε / 2) * (R.log (N : R) - 16 * (T : R) * KA))
    (b := fun j => 8 * (T : R) * (fsum g (hi j + 1) - fsum g (lo j + 1))) (n := J) hblock
  rw [fsum_const, fsum_const_mul] at hsum
  have := OrderedRing.mul_le_mul_of_nonneg_left hpeel (show 0 ≤ 8 * (T : R) by
    have := natCast_nonneg' T; grind)
  rw [← hG]
  grind

/-- `log(D b^(J+1)) = log D + (J+1) log b`, giving `log N ≤ log D + (J+1) log b` when
`N ≤ D b^(J+1)`. -/
theorem log_le_of_le_mul_pow {N D b J : Nat} (hN : 1 ≤ N) (hD : 1 ≤ D) (hb : 1 ≤ b)
    (h : N ≤ D * b ^ (J + 1)) :
    R.log (N : R) ≤ R.log (D : R) + ((J : R) + 1) * R.log (b : R) := by
  have hb0 : (0 : R) < (b : R) := natCast_pos' hb
  have hp : 1 ≤ b ^ (J + 1) := Nat.pow_pos (by omega)
  have h1 := log_le_log (natCast_pos' hN) (show (N : R) ≤ ((D * b ^ (J + 1) : Nat) : R) from
    natCast_le' h)
  rw [natCast_mul', R.log_mul (natCast_pos' hD) (natCast_pos' hp), natCast_pow',
    log_pow' hb0] at h1
  rw [show ((J + 1 : Nat) : R) = (J : R) + 1 by grind] at h1
  exact h1

/-- The algebra of the drop: from the block count `J lam ≥ L − c₃` and the weight bound
`J (α − ε/2)(L − 16 T KA) ≤ 8T G`, deduce `G ≥ (ε/(16 T lam)) (L² − (16 T KA + c₃) L)`. -/
theorem drop_algebra {ε α L J lam T KA' c₃ G : R} (hε : 0 < ε) (hεα : ε ≤ α) (hlam : 0 < lam)
    (hT : 0 < T) (hKA : 0 ≤ KA') (hc₃ : 0 ≤ c₃) (hJ : 0 ≤ J) (hL : 16 * T * KA' ≤ L)
    (hJlam : L - c₃ ≤ J * lam) (hgw : J * ((α - ε / 2) * (L - 16 * T * KA')) ≤ 8 * T * G) :
    ε / (16 * T * lam) * (L * L - (16 * T * KA' + c₃) * L) ≤ G := by
  have hM : 0 ≤ L - 16 * T * KA' := by grind
  have hJM : 0 ≤ J * (L - 16 * T * KA') := OrderedRing.mul_nonneg hJ hM
  have p4 := OrderedRing.mul_le_mul_of_nonneg_right (show ε / 2 ≤ α - ε / 2 by grind) hJM
  have p5 := OrderedRing.mul_le_mul_of_nonneg_right hJlam
    (OrderedRing.mul_nonneg (show 0 ≤ ε / 2 by grind) hM)
  have p6 : 0 ≤ 16 * T * KA' * c₃ * (ε / 2) := by
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (show 0 ≤ 16 * T by grind) hKA) hc₃
    exact OrderedRing.mul_nonneg this (by grind)
  have p7 := OrderedRing.mul_le_mul_of_nonneg_left hgw (Std.le_of_lt hlam)
  have p4' := OrderedRing.mul_le_mul_of_nonneg_left p4 (Std.le_of_lt hlam)
  have hTl : 0 < 8 * T * lam := by have := OrderedRing.mul_pos hT hlam; grind
  apply le_of_mul_le_mul_right' (C := 8 * T * lam) _ hTl
  have e : ε / (16 * T * lam) * (L * L - (16 * T * KA' + c₃) * L) * (8 * T * lam) =
      ε / 2 * (L * L - (16 * T * KA' + c₃) * L) := by
    have : T * lam ≠ 0 := by have := OrderedRing.mul_pos hT hlam; grind
    grind
  rw [e]
  grind

/-- Splitting a lower bound `1 + x + y ≤ L` with `x, y ≥ 0`. -/
theorem split_bound {x y L : R} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 1 + x + y ≤ L) :
    1 ≤ L ∧ x ≤ L ∧ y ≤ L := by
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- `c₅ L + c₆ ≤ δ L²` once `L ≥ 1` and `L ≥ (c₅ + c₆)/δ`. -/
theorem cL_bound {c₅ c₆ δ L : R} (hc₆ : 0 ≤ c₆) (hδ : 0 < δ) (hL1 : 1 ≤ L)
    (h : (c₅ + c₆) / δ ≤ L) : c₅ * L + c₆ ≤ δ * (L * L) := by
  have hL0 : 0 ≤ L := by grind
  have r2 : c₅ + c₆ ≤ δ * L := by
    have := OrderedRing.mul_le_mul_of_nonneg_left h (Std.le_of_lt hδ)
    have e : δ * ((c₅ + c₆) / δ) = c₅ + c₆ := by
      have : δ ≠ 0 := by grind
      grind
    grind
  have r3 := OrderedRing.mul_le_mul_of_nonneg_right r2 hL0
  have r4 := OrderedRing.mul_le_mul_of_nonneg_left hL1 hc₆
  grind

/-- The final algebra of the improvement step. -/
theorem final_algebra {a α C L W W' S Y KA' K1' c δ δ₀ c₇ : R} (hL : 1 ≤ L) (hα0 : 0 ≤ α)
    (hαC : α ≤ C) (hC : 0 ≤ C) (hKA : 0 ≤ KA') (_hδ : 0 < δ) (hδδ : δ₀ = 2 * δ)
    (hni : a * (L * L) ≤ S + (2 * K1' * L + C * c))
    (hW : W ≤ L * L + (2 + KA') * L + 3 * KA' + 1)
    (htail : W - W' ≤ Y * (2 * L + KA'))
    (hG : δ₀ * (L * L - c₇ * L) ≤ α * W + C * (W - W') - S)
    (hcL : (C * (2 + KA') + 2 * C * Y + δ₀ * c₇ + 2 * K1') * L +
      (C * (3 * KA' + 1) + C * Y * KA' + C * c) ≤ δ * (L * L)) :
    a ≤ α - δ := by
  subst hδδ
  have q1 := OrderedRing.mul_le_mul_of_nonneg_left hW hα0
  have q2 := OrderedRing.mul_le_mul_of_nonneg_left htail hC
  have hL0 : 0 ≤ L := by grind
  have q3 := OrderedRing.mul_le_mul_of_nonneg_right hαC
    (show 0 ≤ (2 + KA') * L + 3 * KA' + 1 by
      have := OrderedRing.mul_nonneg (show 0 ≤ 2 + KA' by grind) hL0; grind)
  have hLL : 0 < L * L := OrderedRing.mul_pos (by grind) (by grind)
  apply le_of_mul_le_mul_right' (C := L * L) _ hLL
  grind

/-- **The improvement lemma.** For every `ε > 0` there is `δ > 0` such that: whenever
`ε ≤ α ≤ C₀` and `|V(n)| ≤ α` for all large `n`, then `|V(n)| ≤ α − δ` for all large `n`. -/
theorem improve {ε : R} (hε : 0 < ε) : ∃ δ : R, 0 < δ ∧ ∀ α : R, ε ≤ α → α ≤ C0 →
    ∀ N₀ : Nat, (∀ n, N₀ ≤ n → abs (vrem n) ≤ α) →
      ∃ N₁ : Nat, ∀ N, N₁ ≤ N → abs (vrem N) ≤ α - δ := by
  obtain ⟨K, T, y₀, hK, hT, hgood⟩ := good_interval hε
  have hb : 2 ≤ 2 * K * (2 * K) := by
    have := Nat.mul_le_mul (show 2 ≤ 2 * K by omega) (show 1 ≤ 2 * K by omega)
    omega
  have hlam := log_pos_nat hb
  have hT0 : (0 : R) < (T : R) := natCast_pos' hT
  have h16 : (0 : R) < 16 * (T : R) * R.log ((2 * K * (2 * K) : Nat) : R) := by
    have := OrderedRing.mul_pos hT0 hlam; grind
  refine ⟨ε / (32 * (T : R) * R.log ((2 * K * (2 * K) : Nat) : R)),
    div_pos hε (by grind), fun α hεα hαC N₀ hα => ?_⟩
  generalize hlamd : R.log ((2 * K * (2 * K) : Nat) : R) = lam at hlam h16
  -- The good intervals `m_j`.
  let Y₀ := N₀ + y₀ + 2 * T + 1
  let Ys : Nat → Nat := fun j => Y₀ * (2 * K) ^ j
  have hYs : ∀ j, Y₀ ≤ Ys j := fun j =>
    Nat.le_mul_of_pos_right Y₀ (Nat.pow_pos (by omega))
  have hex : ∀ j, ∃ m, Ys j < m ∧ m ≤ K * Ys j ∧
      ∀ n, m ≤ n → n ≤ m + m / T → abs (vrem n) ≤ ε / 2 := fun j =>
    hgood (Ys j) (by have := hYs j; omega)
  let m : Nat → Nat := fun j => Classical.choose (hex j)
  have hm : ∀ j, Ys j < m j ∧ m j ≤ K * Ys j ∧
      ∀ n, m j ≤ n → n ≤ m j + m j / T → abs (vrem n) ≤ ε / 2 :=
    fun j => Classical.choose_spec (hex j)
  have hmY : ∀ j, Y₀ ≤ m j := fun j => by have := hYs j; have := (hm j).1; omega
  have hmT : ∀ j, 2 * T ≤ m j := fun j => by have := hmY j; omega
  have hminc : ∀ j, m j + m j / T ≤ m (j + 1) := fun j => by
    have h1 : m j / T ≤ m j := Nat.div_le_self _ _
    have h2 := (hm j).2.1
    have h3 := (hm (j + 1)).1
    have e : Ys (j + 1) = 2 * (K * Ys j) := by
      show Y₀ * (2 * K) ^ (j + 1) = 2 * (K * (Y₀ * (2 * K) ^ j))
      rw [Nat.pow_succ]; grind
    omega
  have hmsq : ∀ j, m j * m j ≤ (2 * K * Y₀) * (2 * K * Y₀) * (2 * K * (2 * K)) ^ j := by
    intro j
    have h1 : m j ≤ 2 * K * Y₀ * (2 * K) ^ j := by
      have := (hm j).2.1
      have : K * Ys j ≤ 2 * K * Y₀ * (2 * K) ^ j := by
        show K * (Y₀ * (2 * K) ^ j) ≤ 2 * K * Y₀ * (2 * K) ^ j
        have : K * (Y₀ * (2 * K) ^ j) ≤ 2 * (K * (Y₀ * (2 * K) ^ j)) := by omega
        grind
      omega
    have := Nat.mul_le_mul h1 h1
    rw [Nat.mul_pow]; grind
  -- Constants.
  let D := 64 * (T * T) * ((2 * K * Y₀) * (2 * K * Y₀))
  have hD : 1 ≤ D := by
    have h1 : 1 ≤ T * T := Nat.mul_le_mul hT hT
    have h2 : 1 ≤ 2 * K * Y₀ := by
      have := Nat.mul_le_mul (show 1 ≤ 2 * K by omega) (show 1 ≤ Y₀ by omega)
      omega
    have h3 := Nat.mul_le_mul h2 h2
    have := Nat.mul_le_mul h1 h3
    show 1 ≤ 64 * (T * T) * ((2 * K * Y₀) * (2 * K * Y₀)); grind
  have hKA := KA_nonneg
  have hC0 := one_le_C0
  have hK1 : 0 ≤ K1 := by unfold K1; have := log1024_nonneg; grind
  have hlD : 0 ≤ R.log (D : R) := log_natCast_nonneg hD
  let c₃ : R := R.log (D : R) + lam
  let c₇ : R := 16 * (T : R) * KA + c₃
  let δ₀ : R := ε / (16 * (T : R) * lam)
  have hδ₀ : 0 < δ₀ := div_pos hε h16
  let c₅ : R := C0 * (2 + KA) + 2 * C0 * (Y₀ : R) + δ₀ * c₇ + 2 * K1
  let c₆ : R := C0 * (3 * KA + 1) + C0 * (Y₀ : R) * KA + C0 * R.log 1024
  have hY0 := natCast_nonneg' Y₀
  have hc₅ : 0 ≤ c₅ := by
    have := OrderedRing.mul_nonneg (show 0 ≤ C0 by grind) (show 0 ≤ 2 + KA by grind)
    have := OrderedRing.mul_nonneg (show 0 ≤ 2 * C0 by grind) hY0
    have := OrderedRing.mul_nonneg (Std.le_of_lt hδ₀) (show 0 ≤ c₇ by
      have := OrderedRing.mul_nonneg (show 0 ≤ 16 * (T : R) by grind) hKA; grind)
    grind
  have hc₆ : 0 ≤ c₆ := by
    have := OrderedRing.mul_nonneg (show 0 ≤ C0 by grind) (show 0 ≤ 3 * KA + 1 by grind)
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (show 0 ≤ C0 by grind) hY0) hKA
    have := OrderedRing.mul_nonneg (show 0 ≤ C0 by grind) log1024_nonneg
    grind
  let δ : R := ε / (32 * (T : R) * lam)
  have hδ : 0 < δ := div_pos hε (by grind)
  have hδδ : δ₀ = 2 * δ := by
    show ε / (16 * (T : R) * lam) = 2 * (ε / (32 * (T : R) * lam))
    have : (T : R) * lam ≠ 0 := by have := OrderedRing.mul_pos hT0 hlam; grind
    grind
  obtain ⟨N₂, hN₂, hN₂l⟩ := log_eventually_ge (1 + 16 * (T : R) * KA + (c₅ + c₆) / δ)
  have hcd : 0 ≤ (c₅ + c₆) / δ := by
    have := div_pos (show (0 : R) < 1 by grind) hδ
    have e : (c₅ + c₆) / δ = (c₅ + c₆) * (1 / δ) := by grind
    rw [e]; exact OrderedRing.mul_nonneg (by grind) (Std.le_of_lt this)
  refine ⟨N₂ + D, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨L, hLd⟩ : ∃ L, L = R.log (N : R) := ⟨_, rfl⟩
  have hL := hN₂l N (by omega)
  rw [← hLd] at hL
  -- Counting blocks.
  obtain ⟨J, hJ1, hJ2⟩ := pow_bracket hb (N / D) ((Nat.le_div_iff_mul_le (by omega)).2 (by omega))
  have hJ : ∀ j, j < J → 64 * (T * T) * (m j * m j) ≤ N := by
    intro j hj
    have h1 := Nat.mul_le_mul_left (64 * (T * T)) (hmsq j)
    have h2 : (2 * K * (2 * K)) ^ j ≤ (2 * K * (2 * K)) ^ J := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 := Nat.mul_le_mul_left D (Nat.le_trans h2 hJ1)
    have h4 : D * (N / D) ≤ N := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self N D
    have e : 64 * (T * T) * ((2 * K * Y₀) * (2 * K * Y₀) * (2 * K * (2 * K)) ^ j) =
        D * (2 * K * (2 * K)) ^ j := by show _ = 64 * (T * T) * ((2 * K * Y₀) * (2 * K * Y₀)) * _; grind
    omega
  have hJlam : L - c₃ ≤ (J : R) * lam := by
    have hlt : N ≤ D * (2 * K * (2 * K)) ^ (J + 1) := by
      have := Nat.div_add_mod N D; have := Nat.mod_lt N (show 0 < D by omega)
      have h5 := Nat.mul_le_mul_left D (show N / D + 1 ≤ (2 * K * (2 * K)) ^ (J + 1) from hJ2)
      have e : D * (N / D + 1) = D * (N / D) + D := by grind
      omega
    have := log_le_of_le_mul_pow hN1 hD (by omega) hlt
    rw [hlamd, ← hLd] at this
    show L - (R.log (D : R) + lam) ≤ _; grind
  -- The three estimates.
  have hgw := good_weight hεα hε hT (show N₀ ≤ Y₀ by omega) (show 1 ≤ Y₀ by omega) hα m hmY hmT
    hminc (fun j => (hm j).2.2) hJ
  have hni := normalized_ineq hN1
  have hW := sum_selA_div_le hN1
  have htail := tail_weight (show 1 ≤ Y₀ by omega) hN1
  rw [← hLd] at hgw hni hW htail
  unfold wsum at hgw htail
  generalize fsum (fun k => selA k * (1 / (k : R))) (N + 1) = W at hgw hW htail
  generalize fsum (fun k => selA k * (1 / (k : R))) (N / Y₀ + 1) = W' at hgw htail
  generalize fsum (fun k => selA k * (1 / (k : R)) * abs (vrem (N / k))) (N + 1) = S at hgw hni
  -- The weighted average drops: `G ≥ δ₀ (L² − c₇ L)`.
  have h16K : 0 ≤ 16 * (T : R) * KA :=
    OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (by grind) (Std.le_of_lt hT0)) hKA
  obtain ⟨hL1, hL16, hLc⟩ := split_bound h16K hcd
    (show 1 + 16 * (T : R) * KA + (c₅ + c₆) / δ ≤ L from hL)
  have hG := drop_algebra hε hεα hlam hT0 hKA (show 0 ≤ c₃ by show 0 ≤ R.log (D : R) + lam; grind)
    (natCast_nonneg' J) hL16 hJlam hgw
  have hcL := cL_bound hc₆ hδ hL1 hLc
  exact final_algebra (KA' := KA) (K1' := K1) (c := R.log 1024) (c₇ := c₇) hL1
    (by grind) hαC (by grind) hKA hδ hδδ hni hW htail hG hcL

end Foundations.NumberTheory.PNT
