/-!
# The pigeonhole principle and the Erdős–Szekeres theorem

*If more than `n` pigeons sit in `n` holes, some hole holds two pigeons.* Dirichlet's
**drawer principle** (*Schubfachprinzip*, 1834) is the simplest statement of
combinatorics, and one of its most fruitful: it asserts that a map from a larger
finite set to a smaller one cannot be injective. Its infinite version — *if infinitely
many pigeons sit in finitely many holes, some hole holds infinitely many* — is the
seed of Ramsey theory (next file).

As an application we prove the **Erdős–Szekeres theorem** (1935): every sequence of
`n² + 1` distinct numbers contains a monotone (increasing or decreasing) subsequence
of length `n + 1`. The proof by Seidenberg (1959) labels each position `i` with the
pair `(inc i, dec i)` of lengths of the longest increasing and decreasing
subsequences ending at `i`. If all these were at most `n`, there would be only `n²`
labels for `n² + 1` positions, so two positions `i < j` would share a label — but if
`aᵢ < aⱼ`, any increasing subsequence ending at `i` extends to `j`, so `inc j > inc i`,
and symmetrically if `aᵢ > aⱼ`.

Finite sets are handled concretely: a "function on `m` points" is a function on `ℕ`
of which only the values at `0, …, m − 1` matter.
-/

namespace Foundations.Combinatorics

/-! ## The finite pigeonhole principle -/

/-- **The finite pigeonhole principle.** If `m` points are mapped into `k < m` holes
(values `< k`), two distinct points have the same image. -/
theorem pigeonhole : ∀ (k m : Nat) (f : Nat → Nat), (∀ i, i < m → f i < k) → k < m →
    ∃ i j, i < j ∧ j < m ∧ f i = f j := by
  intro k
  induction k with
  | zero => intro m f hf hm; exact absurd (hf 0 hm) (Nat.not_lt_zero _)
  | succ k ih =>
    intro m f hf hm
    by_cases hk : ∃ i, i < m ∧ f i = k
    · obtain ⟨i, hi, hfi⟩ := hk
      by_cases h2 : ∃ j, j < m ∧ j ≠ i ∧ f j = k
      · obtain ⟨j, hj, hji, hfj⟩ := h2
        rcases Nat.lt_or_gt_of_ne hji with h | h
        · exact ⟨j, i, h, hi, by rw [hfi, hfj]⟩
        · exact ⟨i, j, h, hj, by rw [hfi, hfj]⟩
      · -- remove the point `i`; all other values are `< k`
        let g : Nat → Nat := fun p => f (if p < i then p else p + 1)
        have hg : ∀ p, p < m - 1 → g p < k := by
          intro p hp
          have hne : (if p < i then p else p + 1) ≠ i := by split <;> omega
          have hlt : (if p < i then p else p + 1) < m := by split <;> omega
          have h₁ := hf _ hlt
          have h₂ : f (if p < i then p else p + 1) ≠ k := fun h => h2 ⟨_, hlt, hne, h⟩
          show f _ < k
          omega
        obtain ⟨p, q, hpq, hq, he⟩ := ih (m - 1) g hg (by omega)
        refine ⟨if p < i then p else p + 1, if q < i then q else q + 1, ?_, ?_, he⟩
        · split <;> split <;> omega
        · split <;> omega
    · have hf' : ∀ i, i < m → f i < k := by
        intro i hi
        have := hf i hi
        have : f i ≠ k := fun h => hk ⟨i, hi, h⟩
        omega
      exact ih m f hf' (by omega)

/-- **Pigeonhole for maps between finite types**: there is no injection
`Fin m → Fin k` when `k < m`. -/
theorem pigeonhole_fin {k m : Nat} (h : k < m) (f : Fin m → Fin k) :
    ∃ i j : Fin m, i ≠ j ∧ f i = f j := by
  obtain ⟨i, j, hij, hj, he⟩ := pigeonhole k m
    (fun p => if hp : p < m then (f ⟨p, hp⟩).val else 0)
    (fun p hp => by simp only [hp, dite_true]; exact (f _).isLt) h
  refine ⟨⟨i, by omega⟩, ⟨j, hj⟩, fun e => by simp [Fin.ext_iff] at e; omega, Fin.ext ?_⟩
  simpa [show i < m by omega, hj] using he

/-! ## The infinite pigeonhole principle -/

/-- A predicate on `ℕ` holds **infinitely often** if it holds beyond every bound. -/
def InfOften (P : Nat → Prop) : Prop := ∀ N, ∃ i, N ≤ i ∧ P i

/-- **The infinite pigeonhole principle.** If infinitely many points are mapped into
finitely many holes (values `< k`), some hole receives infinitely many points. -/
theorem infinite_pigeonhole (k : Nat) (f : Nat → Nat) (hf : ∀ i, f i < k) :
    ∃ c, c < k ∧ InfOften fun i => f i = c := by
  refine Classical.byContradiction fun hno => ?_
  -- every value `c < k` stops occurring beyond some bound; take a common bound
  have hbound : ∀ k', k' ≤ k → ∃ N, ∀ i, N ≤ i → k' ≤ f i := by
    intro k'
    induction k' with
    | zero => intro _; exact ⟨0, fun _ _ => Nat.zero_le _⟩
    | succ k' ih =>
      intro hk'
      obtain ⟨N₁, hN₁⟩ := ih (by omega)
      have hnot : ¬ InfOften fun i => f i = k' := fun h => hno ⟨k', by omega, h⟩
      obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ i, N₂ ≤ i → f i ≠ k' :=
        Classical.byContradiction fun hc => hnot fun N =>
          Classical.byContradiction fun hc' => hc ⟨N, fun i hi he => hc' ⟨i, hi, he⟩⟩
      refine ⟨max N₁ N₂, fun i hi => ?_⟩
      have h₁ := hN₁ i (by omega)
      have h₂ := hN₂ i (by omega)
      omega
  obtain ⟨N, hN⟩ := hbound k (Nat.le_refl _)
  have := hN N (Nat.le_refl _)
  have := hf N
  omega

/-- Infinite pigeonhole for two colours. -/
theorem infinite_pigeonhole_bool (f : Nat → Bool) : ∃ b, InfOften fun i => f i = b := by
  obtain ⟨c, hc, hinf⟩ := infinite_pigeonhole 2 (fun i => (f i).toNat)
    (fun i => by cases f i <;> decide)
  refine ⟨c == 1, fun N => ?_⟩
  obtain ⟨i, hi, he⟩ := hinf N
  refine ⟨i, hi, ?_⟩
  cases h : f i <;> simp [h] at he <;> subst he <;> simp [h]

/-- An infinitely-often predicate can be enumerated by a strictly increasing sequence. -/
theorem InfOften.enum {P : Nat → Prop} (h : InfOften P) :
    ∃ g : Nat → Nat, (∀ i, P (g i)) ∧ ∀ i j, i < j → g i < g j := by
  let next : Nat → Nat := fun N => Classical.choose (h N)
  have hnext : ∀ N, N ≤ next N ∧ P (next N) := fun N => Classical.choose_spec (h N)
  let g : Nat → Nat := fun i => Nat.rec (next 0) (fun _ x => next (x + 1)) i
  have hg : ∀ i, g (i + 1) = next (g i + 1) := fun _ => rfl
  refine ⟨g, fun i => ?_, fun i j hij => ?_⟩
  · cases i with
    | zero => exact (hnext 0).2
    | succ i => rw [hg]; exact (hnext _).2
  · induction hij with
    | refl => rw [hg]; have := (hnext (g i + 1)).1; omega
    | @step m _ ih => rw [hg]; have := (hnext (g m + 1)).1; omega

/-! ## Erdős–Szekeres -/

section ErdosSzekeres

variable (r : Nat → Nat → Prop) (a : Nat → Nat)

/-- A subsequence of length `k` that is `r`-monotone and ends at position `i`:
indices `s 0 < ⋯ < s (k-1) = i` with `r (a (s p)) (a (s q))` for `p < q`. -/
def MonoEnd (i k : Nat) : Prop :=
  ∃ s : Nat → Nat, s (k - 1) = i ∧ ∀ p q, p < q → q < k → s p < s q ∧ r (a (s p)) (a (s q))

/-- Every position ends a monotone subsequence of length `1`. -/
theorem monoEnd_one (i : Nat) : MonoEnd r a i 1 :=
  ⟨fun _ => i, rfl, fun p q hpq hq => absurd hpq (by omega)⟩

variable {r a}

/-- Earlier entries of a subsequence ending at `i` are at positions `≤ i`, and (for a
transitive `r`) are `r`-related to `a i` or equal to it. -/
theorem monoEnd_le {i k : Nat} {s : Nat → Nat} (hs : s (k - 1) = i)
    (h : ∀ p q, p < q → q < k → s p < s q ∧ r (a (s p)) (a (s q))) (p : Nat) (hp : p < k) :
    s p ≤ i ∧ (s p = i ∨ r (a (s p)) (a i)) := by
  by_cases hpk : p = k - 1
  · subst hpk; exact ⟨Nat.le_of_eq hs, Or.inl hs⟩
  · have := h p (k - 1) (by omega) (by omega)
    rw [hs] at this
    exact ⟨Nat.le_of_lt this.1, Or.inr this.2⟩

/-- **Extending a monotone subsequence.** -/
theorem monoEnd_extend (htrans : ∀ x y z, r x y → r y z → r x z) {i j k : Nat} (_hk : 1 ≤ k)
    (h : MonoEnd r a i k) (hij : i < j) (hr : r (a i) (a j)) : MonoEnd r a j (k + 1) := by
  obtain ⟨s, hs, hmono⟩ := h
  refine ⟨fun p => if p < k then s p else j, by simp, fun p q hpq hq => ?_⟩
  by_cases hqk : q < k
  · simp only [hqk, show p < k by omega, ite_true]; exact hmono p q hpq hqk
  · simp only [hqk, show p < k by omega, ite_true, ite_false]
    obtain ⟨h₁, h₂⟩ := monoEnd_le hs hmono p (by omega)
    refine ⟨by omega, ?_⟩
    rcases h₂ with h₂ | h₂
    · rw [h₂]; exact hr
    · exact htrans _ _ _ h₂ hr

/-- The greatest `k ≤ n` satisfying `P` (or `0`). -/
noncomputable def findGreatest (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => open Classical in if P (n + 1) then n + 1 else findGreatest P n

/-- `findGreatest` satisfies `P` if some value `≥ 1` up to `n` does... -/
theorem findGreatest_spec {P : Nat → Prop} : ∀ n m, 1 ≤ m → m ≤ n → P m → P (findGreatest P n)
  | 0, m, h₁, h₂, _ => absurd h₂ (by omega)
  | n + 1, m, h₁, h₂, hm => by
      simp only [findGreatest]
      split
      · assumption
      · next h =>
          refine findGreatest_spec n m h₁ ?_ hm
          rcases Nat.lt_or_ge m (n + 1) with h' | h'
          · omega
          · exact absurd (show m = n + 1 by omega ▸ hm) h
termination_by n => n

/-- ... and is at least every value satisfying `P`. -/
theorem le_findGreatest {P : Nat → Prop} : ∀ n m, m ≤ n → P m → m ≤ findGreatest P n
  | 0, m, h, _ => h
  | n + 1, m, h₁, hm => by
      simp only [findGreatest]
      split
      · exact h₁
      · next h =>
          refine le_findGreatest n m ?_ hm
          rcases Nat.lt_or_ge m (n + 1) with h' | h'
          · omega
          · exact absurd (show m = n + 1 by omega ▸ hm) h

/-- `findGreatest` is bounded. -/
theorem findGreatest_le (P : Nat → Prop) : ∀ n, findGreatest P n ≤ n
  | 0 => Nat.le_refl _
  | n + 1 => by
      simp only [findGreatest]; split
      · exact Nat.le_refl _
      · have := findGreatest_le P n; omega

/-- A monotone subsequence of length `n + 1` among the positions `≤ N`. -/
def HasMono (r : Nat → Nat → Prop) (a : Nat → Nat) (n N : Nat) : Prop :=
  ∃ s : Nat → Nat, (∀ p, p ≤ n → s p ≤ N) ∧ ∀ p q, p < q → q ≤ n → s p < s q ∧ r (a (s p)) (a (s q))

/-- A long monotone subsequence ending at `i ≤ N` contains one of length `n + 1`. -/
theorem hasMono_of_monoEnd {n N i k : Nat} (hiN : i ≤ N) (hk : n + 1 ≤ k)
    (h : MonoEnd r a i k) : HasMono r a n N := by
  obtain ⟨s, hs, hmono⟩ := h
  exact ⟨s, fun p hp => Nat.le_trans (monoEnd_le hs hmono p (by omega)).1 hiN,
    fun p q hpq hq => hmono p q hpq (by omega)⟩

/-- If there is no monotone subsequence of length `n + 1`, every monotone subsequence
ending at a position `≤ N` has length `≤ n`. -/
theorem monoEnd_bound {n N i k : Nat} (hno : ¬ HasMono r a n N) (hiN : i ≤ N)
    (h : MonoEnd r a i k) : k ≤ n :=
  Classical.byContradiction fun hk => hno (hasMono_of_monoEnd hiN (by omega) h)

end ErdosSzekeres

/-- Decoding a pair from `x·n + y`. -/
theorem pair_code_inj {n x y x' y' : Nat} (hy : y < n) (hy' : y' < n)
    (h : x * n + y = x' * n + y') : x = x' ∧ y = y' := by
  have hn : 0 < n := by omega
  have h₁ : (y + x * n) / n = (y' + x' * n) / n := by rw [Nat.add_comm y, Nat.add_comm y', h]
  rw [Nat.add_mul_div_right _ _ hn, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hy,
    Nat.div_eq_of_lt hy'] at h₁
  simp at h₁
  subst h₁
  exact ⟨rfl, by omega⟩

/-- **The Erdős–Szekeres theorem.** Among the first `n² + 1` terms `a 0, …, a (n²)` of a
sequence of pairwise distinct natural numbers there is a strictly increasing or a
strictly decreasing subsequence of length `n + 1`. -/
theorem erdos_szekeres (a : Nat → Nat) (n : Nat)
    (hinj : ∀ i j, i < j → j ≤ n * n → a i ≠ a j) :
    HasMono (· < ·) a n (n * n) ∨ HasMono (· > ·) a n (n * n) := by
  refine Classical.byContradiction fun hno => ?_
  simp only [not_or] at hno
  obtain ⟨hinc, hdec⟩ := hno
  let N := n * n
  -- the labels
  let inc : Nat → Nat := fun i => findGreatest (MonoEnd (· < ·) a i) n
  let dec : Nat → Nat := fun i => findGreatest (MonoEnd (· > ·) a i) n
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd ⟨fun _ => 0, fun _ _ => by simp [h], fun p q hpq hq => by omega⟩ hinc
    · exact h
  have inc_spec : ∀ i, MonoEnd (· < ·) a i (inc i) :=
    fun i => findGreatest_spec n 1 (by omega) hn (monoEnd_one _ a i)
  have dec_spec : ∀ i, MonoEnd (· > ·) a i (dec i) :=
    fun i => findGreatest_spec n 1 (by omega) hn (monoEnd_one _ a i)
  have inc_pos : ∀ i, 1 ≤ inc i := fun i => le_findGreatest n 1 hn (monoEnd_one _ a i)
  have dec_pos : ∀ i, 1 ≤ dec i := fun i => le_findGreatest n 1 hn (monoEnd_one _ a i)
  have inc_le : ∀ i, inc i ≤ n := fun i => findGreatest_le _ n
  have dec_le : ∀ i, dec i ≤ n := fun i => findGreatest_le _ n
  -- two positions with the same label
  obtain ⟨i, j, hij, hj, he⟩ := pigeonhole (n * n) (n * n + 1)
    (fun i => (inc i - 1) * n + (dec i - 1))
    (fun i _ => by
      have h₁ := inc_le i; have h₂ := dec_le i; have h₃ := inc_pos i; have h₄ := dec_pos i
      have : (inc i - 1) * n ≤ (n - 1) * n := Nat.mul_le_mul_right n (by omega)
      have : (n - 1) * n + n = n * n := by
        rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
      omega)
    (by omega)
  obtain ⟨hI, hD⟩ := pair_code_inj (by have := dec_le i; have := dec_pos i; omega)
    (by have := dec_le j; have := dec_pos j; omega) he
  have hI' : inc i = inc j := by have := inc_pos i; have := inc_pos j; omega
  have hD' : dec i = dec j := by have := dec_pos i; have := dec_pos j; omega
  rcases Nat.lt_or_gt_of_ne (hinj i j hij (by omega)) with h | h
  · have hext := monoEnd_extend (r := fun x y => x < y) (fun x y z => Nat.lt_trans) (inc_pos i) (inc_spec i) hij h
    have := le_findGreatest n _ (monoEnd_bound hinc (by omega) hext) hext
    show False
    have : inc i + 1 ≤ inc j := this
    omega
  · have hext := monoEnd_extend (r := fun x y => x > y) (fun x y z h₁ h₂ => Nat.lt_trans h₂ h₁) (dec_pos i) (dec_spec i)
      hij h
    have := le_findGreatest n _ (monoEnd_bound hdec (by omega) hext) hext
    have : dec i + 1 ≤ dec j := this
    omega

end Foundations.Combinatorics
