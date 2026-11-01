import Foundations.Logic.PeanoArithmetic

/-!
# Gödel's β-function: finite sequences inside arithmetic

The language of arithmetic speaks only of numbers, with `0`, successor, `+` and `×`.
To express "there is a computation of length `m` with values `r₀, …, r_m`" we must
quantify over *finite sequences* — but there are no sequence variables. Gödel's
ingenious solution (1931) was to code a whole sequence by **two** numbers `A, B`,
reading off its terms with the remainder function

`β(A, B, i) = A mod (1 + (i + 1)·B)`,

which is definable using only `+` and `×` ("`z` is the remainder of `A` divided by
`d`" iff `∃q. A = q·d + z ∧ z < d`). The **β-lemma** says every finite sequence is so
coded. Its proof is a classical piece of number theory:

1. choose `B = M!` for `M` larger than the length and all terms of the sequence; then
   the moduli `dᵢ = 1 + (i + 1)·B` are **pairwise coprime** (a common divisor of `dᵢ`
   and `dⱼ` divides `(j − i)·B`, is coprime to `B`, hence divides `j − i`, which
   divides `B = M!` — so it is `1`);
2. by the **Chinese remainder theorem** some `A` leaves remainder `rᵢ` modulo each
   `dᵢ`. We prove the CRT by induction, adjusting `A` by multiples of the product of
   the earlier moduli; the needed modular inverse comes from **Bézout's identity**,
   proved by Euclid's algorithm.
-/

namespace Foundations.Logic.FO

/-- **Gödel's β-function** `β(A, B, i) = A mod (1 + (i + 1)·B)`. -/
def gbeta (A B i : Nat) : Nat := A % (1 + (i + 1) * B)

/-- **Bézout's identity.** The greatest common divisor of `a` and `b` is an integer
combination `x·a + y·b`. (Proof: Euclid's algorithm.) -/
theorem bezout : ∀ (a b : Nat), ∃ x y : Int, x * a + y * b = (Nat.gcd a b : Int) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b
    cases a with
    | zero => exact ⟨0, 1, by simp⟩
    | succ a =>
      obtain ⟨x, y, h⟩ := ih (b % (a + 1)) (Nat.mod_lt _ (by omega)) (a + 1)
      rw [Nat.gcd_rec]
      refine ⟨y - x * (b / (a + 1) : Nat), x, ?_⟩
      have hm := Nat.mod_add_div b (a + 1)
      have : ((b % (a + 1) : Nat) : Int) =
          (b : Int) - ((a + 1 : Nat) : Int) * ((b / (a + 1) : Nat) : Int) := by
        have := congrArg (fun n : Nat => (n : Int)) hm
        simp only [Int.natCast_add, Int.natCast_mul] at this
        omega
      rw [← h, this]
      grind

/-- Congruence in `ℤ` gives equal remainders in `ℕ`. -/
theorem mod_eq_of_int_dvd {A r d : Nat} (h : (d : Int) ∣ (A : Int) - r) : A % d = r % d := by
  rw [Int.dvd_iff_emod_eq_zero] at h
  have := Int.emod_eq_emod_iff_emod_sub_eq_zero.2 h
  exact_mod_cast this

/-- **Solving a linear congruence.** If `P` and `d` are coprime, then `a + t·P` can be
made congruent to any `r` modulo `d`. -/
theorem exists_add_mul_mod {P d : Nat} (hcop : Nat.Coprime P d) (hd : 0 < d) (a r : Nat) :
    ∃ t, (a + t * P) % d = r % d := by
  obtain ⟨x, y, h⟩ := bezout P d
  rw [hcop] at h
  let T : Int := ((r : Int) - a) * x
  have hnn : 0 ≤ T % d := Int.emod_nonneg _ (by omega)
  refine ⟨(T % d).toNat, mod_eq_of_int_dvd ⟨-((r : Int) - a) * y - (T / d) * P, ?_⟩⟩
  have ht : (((T % d).toNat : Nat) : Int) = T % d := Int.toNat_of_nonneg hnn
  have hdef : T % d = T - d * (T / d) := Int.emod_def T d
  push_cast
  rw [ht, hdef]
  have hx : x * P = 1 - y * d := by simp at h; omega
  show (a : Int) + (((r : Int) - a) * x - d * (T / d)) * P - r = _
  grind

/-- The product `d 0 · d 1 ⋯ d n`. -/
def prodUpTo (d : Nat → Nat) : Nat → Nat
  | 0 => d 0
  | n + 1 => prodUpTo d n * d (n + 1)

/-- Each factor divides the product. -/
theorem dvd_prodUpTo (d : Nat → Nat) : ∀ n j, j ≤ n → d j ∣ prodUpTo d n
  | 0, j, h => by rw [Nat.le_zero.1 h]; exact Nat.dvd_refl _
  | n + 1, j, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | rfl
      · exact Nat.dvd_trans (dvd_prodUpTo d n j (by omega)) (Nat.dvd_mul_right _ _)
      · exact Nat.dvd_mul_left _ _

/-- A number coprime to each factor is coprime to the product. -/
theorem coprime_prodUpTo {d : Nat → Nat} {k : Nat} :
    ∀ n, (∀ j, j ≤ n → Nat.Coprime k (d j)) → Nat.Coprime k (prodUpTo d n)
  | 0, h => h 0 (Nat.le_refl _)
  | n + 1, h => Nat.Coprime.mul_right (coprime_prodUpTo n fun j hj => h j (by omega)) (h _ (Nat.le_refl _))

/-- **Chinese remainder theorem.** If the moduli `d 0, …, d m` are positive and
pairwise coprime, then any remainders can be achieved simultaneously. -/
theorem crt (d r : Nat → Nat) (m : Nat) (hpos : ∀ i, 0 < d i)
    (hcop : ∀ i j, i < j → j ≤ m → Nat.Coprime (d i) (d j)) :
    ∀ n, n ≤ m → ∃ A, ∀ j, j ≤ n → A % d j = r j % d j := by
  intro n
  induction n with
  | zero => intro _; exact ⟨r 0, fun j hj => by rw [Nat.le_zero.1 hj]⟩
  | succ n ih =>
      intro hn
      obtain ⟨A, hA⟩ := ih (by omega)
      have hc : Nat.Coprime (prodUpTo d n) (d (n + 1)) :=
        Nat.Coprime.symm (coprime_prodUpTo n fun j hj => Nat.Coprime.symm (hcop j (n + 1) (by omega) hn))
      obtain ⟨t, ht⟩ := exists_add_mul_mod hc (hpos _) A (r (n + 1))
      refine ⟨A + t * prodUpTo d n, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with h | rfl
      · obtain ⟨c, hc⟩ := dvd_prodUpTo d n j (by omega)
        rw [hc, show t * (d j * c) = d j * (t * c) by rw [Nat.mul_left_comm], Nat.add_mul_mod_self_left]
        exact hA j (by omega)
      · exact ht

/-- Factorial. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Factorials are positive. -/
theorem fact_pos : ∀ n, 0 < fact n
  | 0 => Nat.one_pos
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- Every `1 ≤ k ≤ n` divides `n!`. -/
theorem dvd_fact : ∀ {k n : Nat}, 0 < k → k ≤ n → k ∣ fact n
  | _, 0, hk, h => absurd h (by omega)
  | k, n + 1, hk, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | rfl
      · exact Nat.dvd_trans (dvd_fact hk (by omega)) (Nat.dvd_mul_left _ _)
      · exact Nat.dvd_mul_right _ _

/-- `n ≤ n!`. -/
theorem self_le_fact : ∀ n, n ≤ fact n
  | 0 => Nat.zero_le _
  | n + 1 => by
      have := fact_pos n
      simp only [fact]
      exact Nat.le_mul_of_pos_right _ this

/-- The moduli `1 + (i + 1)·B` are pairwise coprime when every `1 ≤ k ≤ j - i`
divides `B`. -/
theorem coprime_moduli {B i j : Nat} (hij : i < j) (hB : (j - i) ∣ B) :
    Nat.Coprime (1 + (i + 1) * B) (1 + (j + 1) * B) := by
  let g := Nat.gcd (1 + (i + 1) * B) (1 + (j + 1) * B)
  have hgi : g ∣ 1 + (i + 1) * B := Nat.gcd_dvd_left _ _
  have hgj : g ∣ 1 + (j + 1) * B := Nat.gcd_dvd_right _ _
  have hdiff : (1 + (j + 1) * B) - (1 + (i + 1) * B) = (j - i) * B := by
    obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
    have : (i + k + 1) * B = (i + 1) * B + k * B := by
      rw [show i + k + 1 = (i + 1) + k by omega, Nat.add_mul]
    rw [show i + k - i = k by omega]; omega
  have hg1 : g ∣ (j - i) * B := hdiff ▸ Nat.dvd_sub hgj hgi
  -- `g` is coprime to `B`
  have hgB : Nat.Coprime g B := by
    show Nat.gcd g B = 1
    have h1 : Nat.gcd g B ∣ 1 + (i + 1) * B := Nat.dvd_trans (Nat.gcd_dvd_left _ _) hgi
    have h2 : Nat.gcd g B ∣ (i + 1) * B := Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.dvd_mul_left _ _)
    have : Nat.gcd g B ∣ 1 := by
      have := Nat.dvd_sub h1 h2
      rwa [show 1 + (i + 1) * B - (i + 1) * B = 1 by omega] at this
    exact Nat.eq_one_of_dvd_one this
  have hg2 : g ∣ j - i := Nat.Coprime.dvd_of_dvd_mul_right hgB hg1
  exact Nat.Coprime.eq_one_of_dvd hgB (Nat.dvd_trans hg2 hB)

/-- The sum `r 0 + ⋯ + r m`. -/
def sumUpTo (r : Nat → Nat) : Nat → Nat
  | 0 => r 0
  | m + 1 => sumUpTo r m + r (m + 1)

/-- Each term is at most the sum. -/
theorem le_sumUpTo (r : Nat → Nat) : ∀ m j, j ≤ m → r j ≤ sumUpTo r m
  | 0, j, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | m + 1, j, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | rfl
      · have := le_sumUpTo r m j (by omega); simp only [sumUpTo]; omega
      · simp only [sumUpTo]; omega

/-- **Gödel's β-lemma.** Every finite sequence `r 0, …, r m` of numbers is coded by two
numbers `A, B`: `β(A, B, j) = r j` for all `j ≤ m`. -/
theorem beta_lemma (m : Nat) (r : Nat → Nat) : ∃ A B, ∀ j, j ≤ m → gbeta A B j = r j := by
  let M := m + 1 + sumUpTo r m
  let B := fact M
  let d : Nat → Nat := fun i => 1 + (i + 1) * B
  have hMB : M ≤ B := self_le_fact M
  obtain ⟨A, hA⟩ := crt d r m (fun i => by simp [d]; omega)
    (fun i j hij hj => coprime_moduli hij (dvd_fact (by omega) (by omega))) m (Nat.le_refl _)
  refine ⟨A, B, fun j hj => ?_⟩
  have hr : r j < d j := by
    have h1 := le_sumUpTo r m j hj
    have h2 : B ≤ (j + 1) * B := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
    simp only [d]; omega
  rw [gbeta, show 1 + (j + 1) * B = d j from rfl, hA j hj, Nat.mod_eq_of_lt hr]

end Foundations.Logic.FO
