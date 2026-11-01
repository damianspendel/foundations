import Foundations.Logic.PAModels

/-!
# Coding finite sequences inside a model of PA

To reason about proofs inside a model `M` of PA we must be able to *build* coded
sequences there — in particular to **concatenate** two coded proofs, of possibly
non-standard lengths, and append one more line. Gödel's β-function codes a sequence
`y₀, …, y_{L-1}` by a pair `(c, d)` with `yᵢ = c mod (1 + (i+1)·d)`; that every
sequence has such a code is Gödel's lemma, proved for `ℕ` in `BetaFunction` by the
Chinese remainder theorem. Here we prove it **inside `M`**, for every sequence that
is *definable* (with parameters) — the restriction that makes induction applicable.

The proof is a direct internalisation:

1. choose `d` divisible by every `k ≤ L` and larger than all entries (by induction on
   `L`, multiplying in one factor at a time);
2. then the moduli `mᵢ = 1 + (i+1)·d` are pairwise coprime, in the strong "Bézout"
   form `mᵢ·x = mⱼ·y + 1`, by an explicit polynomial identity;
3. by induction on `k ≤ L` build `c` with the right remainders at all `i < k`,
   carrying along a common multiple `P` of `m₀, …, m_{k-1}` that is coprime to all
   later moduli; one step is the Chinese remainder theorem for two moduli,
   `c' = c + P·x·(y_k + (k+1)·d·c)`.

Coprimality is *defined* by the Bézout equation, so that its multiplicativity is a
one-line identity and no prime factorisation inside `M` is ever needed. The
**concatenation lemma** `concat_exists` — the only form in which the coding is used
later — follows by applying the general lemma to an explicitly definable sequence.
-/

set_option linter.unusedSimpArgs false

namespace Foundations.Logic.FO

namespace PAModel

variable {N : PAModel}

/-- **Coprimality in Bézout form.** `P·x = m·y + 1` for some `x, y`. -/
def Cop (P m : N.Dom) : Prop := ∃ x y, P * x = m * y + 1

/-- `1` is coprime to everything. -/
theorem cop_one (m : N.Dom) : Cop 1 m := ⟨1, 0, by grind⟩

/-- Coprimality is multiplicative. -/
theorem cop_mul {P Q m : N.Dom} (h₁ : Cop P m) (h₂ : Cop Q m) : Cop (P * Q) m := by
  obtain ⟨x, y, hx⟩ := h₁; obtain ⟨x', y', hx'⟩ := h₂
  exact ⟨x * x', m * y * y' + y + y', by grind⟩

/-- `a + 1 + b ≤ a` is impossible. -/
theorem not_succ_add_le (a b : N.Dom) : ¬ a + 1 + b ≤ a := by
  rintro ⟨z, hz⟩; exact add_succ_ne_self a (b + z) (by grind)

/-- From `i < j` obtain the difference. -/
theorem exists_of_lt {i j : N.Dom} (h : i < j) : ∃ δ, j = i + (δ + 1) := by
  obtain ⟨z, rfl⟩ := h; exact ⟨z, by grind⟩

/-- **The β-moduli are pairwise coprime.** This holds when `d` is divisible by their distance. -/
theorem cop_moduli {d i δ e : N.Dom} (hd : d = (δ + 1) * (e + 1)) :
    Cop (1 + (i + 1) * d) (1 + (i + (δ + 1) + 1) * d) := by
  subst hd
  refine ⟨(i + (δ + 1) + 1) * (i + (δ + 1) + 1) * (e + 1) * ((i + (δ + 1) + 1) * ((δ + 1) * (e + 1))),
    (i + 1) * (i + (δ + 1) + 1) * (e + 1) * ((i + (δ + 1) + 1) * ((δ + 1) * (e + 1)))
      + (i + (δ + 1) + 1) * (δ + 1) * e + (i + (δ + 1) + 1) * δ + (i + (δ + 1)), ?_⟩
  grind

/-- A number divisible by every `k` with `0 < k ≤ L`. -/
theorem exists_common_multiple (L : N.Dom) :
    ∃ d₀ : N.Dom, ∀ k, 0 < k → k ≤ L → ∃ t, d₀ + 1 = k * t := by
  refine induction (P := fun L _ => ∃ d₀ : N.Dom, ∀ k, 0 < k → k ≤ L → ∃ t, d₀ + 1 = k * t)
    (by dfn) (fun _ => 0) ⟨0, fun k hk hk0 => ?_⟩ ?_ L
  · exact absurd (lt_of_lt_of_le' hk hk0) (lt_irrefl' 0)
  · rintro x ⟨d₀, hd₀⟩
    refine ⟨d₀ * (x + 1) + x, fun k hk hkx => ?_⟩
    rcases eq_or_lt_of_le hkx with rfl | h
    · exact ⟨d₀ + 1, by grind⟩
    · obtain ⟨t, ht⟩ := hd₀ k hk (lt_succ_iff'.1 h)
      exact ⟨t * (x + 1), by grind⟩

/-- A definable relation `R(i, y; p)` stays definable when its two arguments and its
parameters are replaced by definable functions. -/
theorem Dfn.app3 {R : N.Dom → N.Dom → (Nat → N.Dom) → Prop}
    (hR : N.Dfn fun e => R (e 0) (e 1) (fun n => e (n + 2)))
    {f g : (Nat → N.Dom) → N.Dom} {σ : Nat → (Nat → N.Dom) → N.Dom}
    (hf : N.DfnT f) (hg : N.DfnT g) (hσ : ∀ n, N.DfnT (σ n)) :
    N.Dfn fun e => R (f e) (g e) (fun n => σ n e) :=
  hR.subst (σ := fun n => match n with | 0 => f | 1 => g | n + 2 => σ n)
    (fun n => match n with | 0 => hf | 1 => hg | n + 2 => hσ n)

/-- **Gödel's β-lemma inside a model of PA.** Let `R(i, y)` be definable (with
parameters `p`), and suppose that for every `i < L` there is some `y ≤ B` with
`R(i, y)`. Then there are `c ≥ K` and `d` such that, for every `i < L`, the `i`-th
entry of the β-sequence coded by `(c, d)` satisfies `R(i, ·)`. -/
theorem seq_exists {R : N.Dom → N.Dom → (Nat → N.Dom) → Prop}
    (hR : N.Dfn fun e => R (e 0) (e 1) (fun n => e (n + 2)))
    (p : Nat → N.Dom) (L B K : N.Dom) (hex : ∀ i, i < L → ∃ y, y ≤ B ∧ R i y p) :
    ∃ c d, K ≤ c ∧ ∀ i, i < L → ∃ y, BetaM c d i y ∧ R i y p := by
  obtain ⟨d₀, hd₀⟩ := exists_common_multiple L
  -- the common modulus parameter `d`
  obtain ⟨d, hd⟩ : ∃ d : N.Dom, d = (d₀ + 1) * (B + 1) := ⟨_, rfl⟩
  have hBd : B < d := ⟨d₀ * (B + 1), by grind⟩
  have hdiv : ∀ k, 0 < k → k ≤ L → ∃ t, d = k * (t + 1) := by
    intro k hk hkL
    obtain ⟨t, ht⟩ := hd₀ k hk hkL
    rcases zero_or_succ t with rfl | ⟨t', rfl⟩
    · exact absurd (by grind : d₀ + 1 = 0) (succ_ne_zero' d₀)
    · exact ⟨t' * (B + 1) + B, by grind⟩
  -- coprimality of the moduli below `L`
  have hcop : ∀ i j, i < j → j < L → Cop (1 + (i + 1) * d) (1 + (j + 1) * d) := by
    intro i j hij hjL
    obtain ⟨δ, rfl⟩ := exists_of_lt hij
    obtain ⟨t, ht⟩ := hdiv (δ + 1) ⟨δ, by grind⟩
      (le_trans' ⟨i, by grind⟩ (le_of_lt' hjL))
    exact cop_moduli (e := t) ht
  -- the inductive invariant, for `k ≤ L`
  let Q : N.Dom → Prop := fun k => k ≤ L → ∃ c P : N.Dom, (∃ P₀, P = P₀ + 1) ∧
      (∀ i, i < k → ∃ t, P = (1 + (i + 1) * d) * t) ∧
      (∀ j, j < L → k ≤ j → Cop P (1 + (j + 1) * d)) ∧
      (∀ i, i < k → ∃ y, BetaM c d i y ∧ R i y p)
  have hQ0 : Q 0 := fun _ =>
    ⟨0, 1, ⟨0, by grind⟩, fun i hi => absurd hi (not_lt_zero' i),
      fun j _ _ => cop_one _, fun i hi => absurd hi (not_lt_zero' i)⟩
  have hQs : ∀ k, Q k → Q (k + 1) := by
    intro k ih hk
    have hkL : k < L := hk
    obtain ⟨c, P, hP0, hP, hPc, hc⟩ := ih (le_of_lt' hkL)
    obtain ⟨yk, hykB, hRk⟩ := hex k hkL
    obtain ⟨x, y', hxy⟩ := hPc k hkL (le_refl' k)
    have hyk : yk < 1 + (k + 1) * d := by
      obtain ⟨a, ha⟩ := hykB; obtain ⟨b, hb⟩ := hBd
      exact ⟨a + b + 1 + k * d, by grind⟩
    refine ⟨c + P * x * (yk + (k + 1) * d * c), P * (1 + (k + 1) * d), ?_, ?_, ?_, ?_⟩
    · obtain ⟨P₀, rfl⟩ := hP0; exact ⟨P₀ * (1 + (k + 1) * d) + (k + 1) * d, by grind⟩
    · intro i hi
      rcases eq_or_lt_of_le (lt_succ_iff'.1 hi) with rfl | hi'
      · exact ⟨P, by grind⟩
      · obtain ⟨t, ht⟩ := hP i hi'; exact ⟨t * (1 + (k + 1) * d), by grind⟩
    · intro j hj hkj
      exact cop_mul (hPc j hj (le_of_lt' hkj)) (hcop k j hkj hj)
    · intro i hi
      rcases eq_or_lt_of_le (lt_succ_iff'.1 hi) with rfl | hi'
      · exact ⟨yk, ⟨c + y' * (yk + (i + 1) * d * c), by grind, hyk⟩, hRk⟩
      · obtain ⟨y, ⟨q, hq, hy⟩, hRy⟩ := hc i hi'
        obtain ⟨t, ht⟩ := hP i hi'
        exact ⟨y, ⟨q + t * x * (yk + (k + 1) * d * c), by grind, hy⟩, hRy⟩
  have hdfn : N.Dfn fun e => (fun k e => k ≤ e 0 → ∃ c P : N.Dom, (∃ P₀, P = P₀ + 1) ∧
      (∀ i, i < k → ∃ t, P = (1 + (i + 1) * e 1) * t) ∧
      (∀ j, j < e 0 → k ≤ j → ∃ x y, P * x = (1 + (j + 1) * e 1) * y + 1) ∧
      (∀ i, i < k → ∃ y, BetaM c (e 1) i y ∧ R i y (fun n => e (n + 2))))
      (e 0) (fun n => e (n + 1)) := by
    dfn
    exact Dfn.app3 hR (DfnT.var _) (DfnT.var _) (fun n => DfnT.var _)
  have key : ∃ c P : N.Dom, (∃ P₀, P = P₀ + 1) ∧
      (∀ i, i < L → ∃ t, P = (1 + (i + 1) * d) * t) ∧
      (∀ j, j < L → L ≤ j → Cop P (1 + (j + 1) * d)) ∧
      (∀ i, i < L → ∃ y, BetaM c d i y ∧ R i y p) := induction (P := fun k e => k ≤ e 0 → ∃ c P : N.Dom, (∃ P₀, P = P₀ + 1) ∧
      (∀ i, i < k → ∃ t, P = (1 + (i + 1) * e 1) * t) ∧
      (∀ j, j < e 0 → k ≤ j → ∃ x y, P * x = (1 + (j + 1) * e 1) * y + 1) ∧
      (∀ i, i < k → ∃ y, BetaM c (e 1) i y ∧ R i y (fun n => e (n + 2))))
    hdfn (Env.cons L (Env.cons d p)) hQ0 hQs L (le_refl' L)
  obtain ⟨c, P, ⟨P₀, rfl⟩, hP, -, hc⟩ := key
  refine ⟨c + (P₀ + 1) * K, d, ⟨c + P₀ * K, by grind⟩, fun i hi => ?_⟩
  obtain ⟨y, ⟨q, hq, hy⟩, hR⟩ := hc i hi
  obtain ⟨t, ht⟩ := hP i hi
  exact ⟨y, ⟨q + t * K, by grind, hy⟩, hR⟩

/-- The target sequence of a concatenation: the entries of the code `(c₁, d₁)` at
positions `≤ n₁`, then those of `(c₂, d₂)` (positions `n₁ + 1 + j`, `j ≤ n₂`), then `v`. -/
def ConcatR (n₁ c₁ d₁ n₂ c₂ d₂ v i y : N.Dom) : Prop :=
  (i ≤ n₁ ∧ BetaM c₁ d₁ i y) ∨ (∃ j, i = n₁ + 1 + j ∧ j ≤ n₂ ∧ BetaM c₂ d₂ j y) ∨
    (i = n₁ + n₂ + 2 ∧ y = v)

/-- `i ≤ n` and `n < i` exclude each other. -/
theorem not_le_of_lt'' {i n : N.Dom} (h : n < i) (h' : i ≤ n) : False :=
  lt_irrefl' n (lt_of_lt_of_le' h h')

/-- **Concatenation of β-coded sequences inside a model of PA.** Given codes of
sequences of lengths `n₁ + 1` and `n₂ + 1` (with arbitrary, possibly non-standard,
`n₁, n₂`) and an element `v`, there is a code (with `c` as large as desired) of the
sequence obtained by writing the two after each other and appending `v`. -/
theorem concat_exists (c₁ d₁ n₁ c₂ d₂ n₂ v K : N.Dom) : ∃ c d, K ≤ c ∧
    (∀ i y, i ≤ n₁ → BetaM c₁ d₁ i y → BetaM c d i y) ∧
    (∀ i y, i ≤ n₂ → BetaM c₂ d₂ i y → BetaM c d (n₁ + 1 + i) y) ∧
    BetaM c d (n₁ + n₂ + 2) v := by
  let p : Nat → N.Dom := Env.cons n₁ (Env.cons c₁ (Env.cons d₁ (Env.cons n₂ (Env.cons c₂
    (Env.cons d₂ (fun _ => v))))))
  have hR : N.Dfn fun e => (fun i y (p : Nat → N.Dom) =>
      ConcatR (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) i y) (e 0) (e 1) (fun n => e (n + 2)) := by
    unfold ConcatR; dfn
  have hex : ∀ i, i < n₁ + n₂ + 3 → ∃ y, y ≤ c₁ + c₂ + v ∧ ConcatR n₁ c₁ d₁ n₂ c₂ d₂ v i y := by
    intro i hi
    rcases le_or_lt' n₁ i with h | h
    · obtain ⟨y, hy⟩ := betaM_exists c₁ d₁ i
      exact ⟨y, le_trans' (betaM_le hy) ⟨c₂ + v, by grind⟩, Or.inl ⟨h, hy⟩⟩
    · obtain ⟨j, rfl⟩ := exists_of_lt h
      rcases le_or_lt' n₂ j with hj | hj
      · obtain ⟨y, hy⟩ := betaM_exists c₂ d₂ j
        exact ⟨y, le_trans' (betaM_le hy) ⟨c₁ + v, by grind⟩,
          Or.inr (Or.inl ⟨j, by grind, hj, hy⟩)⟩
      · obtain ⟨δ, rfl⟩ := exists_of_lt hj
        rcases zero_or_succ δ with rfl | ⟨δ', rfl⟩
        · exact ⟨v, ⟨c₁ + c₂, by grind⟩, Or.inr (Or.inr ⟨by grind, rfl⟩)⟩
        · exfalso
          obtain ⟨z, hz⟩ := hi
          exact add_succ_ne_self (n₁ + n₂ + 3) (δ' + z) (by grind)
  obtain ⟨c, d, hK, hc⟩ := seq_exists (R := fun i y (p : Nat → N.Dom) =>
      ConcatR (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) i y) hR p (n₁ + n₂ + 3) (c₁ + c₂ + v) K hex
  have hc' : ∀ i, i < n₁ + n₂ + 3 → ∃ y, BetaM c d i y ∧ ConcatR n₁ c₁ d₁ n₂ c₂ d₂ v i y := hc
  refine ⟨c, d, hK, fun i y hi hy => ?_, fun i y hi hy => ?_, ?_⟩
  · obtain ⟨y', hy', hR'⟩ := hc' i (lt_of_le_of_lt' hi ⟨n₂ + 2, by grind⟩)
    rcases hR' with ⟨-, h⟩ | ⟨j, rfl, -, -⟩ | ⟨rfl, -⟩
    · rwa [betaM_unique hy h]
    · exact absurd hi (not_succ_add_le _ _)
    · exact absurd hi (not_succ_add_le n₁ (n₂ + 1) |> fun h h' => h (by
        obtain ⟨z, hz⟩ := h'; exact ⟨z, by grind⟩))
  · obtain ⟨y', hy', hR'⟩ := hc' (n₁ + 1 + i) (by obtain ⟨z, hz⟩ := hi; exact ⟨z + 1, by grind⟩)
    rcases hR' with ⟨h, -⟩ | ⟨j, hj, -, h⟩ | ⟨h, -⟩
    · exact absurd h (not_succ_add_le _ _)
    · have : i = j := add_right_cancel' (by grind : i + (n₁ + 1) = j + (n₁ + 1))
      subst this; rwa [betaM_unique hy h]
    · have : i = n₂ + 1 := add_right_cancel' (by grind : i + (n₁ + 1) = n₂ + 1 + (n₁ + 1))
      subst this; exact absurd hi (not_succ_add_le n₂ 0 |> fun h h' => h (by
        obtain ⟨z, hz⟩ := h'; exact ⟨z, by grind⟩))
  · obtain ⟨y', hy', hR'⟩ := hc' (n₁ + n₂ + 2) ⟨0, by grind⟩
    rcases hR' with ⟨h, -⟩ | ⟨j, hj, hjn, -⟩ | ⟨-, rfl⟩
    · exact absurd h (not_succ_add_le n₁ (n₂ + 1) |> fun h h' => h (by
        obtain ⟨z, hz⟩ := h'; exact ⟨z, by grind⟩))
    · have : j = n₂ + 1 := add_right_cancel' (by grind : j + (n₁ + 1) = n₂ + 1 + (n₁ + 1))
      subst this; exact absurd hjn (not_succ_add_le n₂ 0 |> fun h h' => h (by
        obtain ⟨z, hz⟩ := h'; exact ⟨z, by grind⟩))
    · exact hy'

end PAModel

end Foundations.Logic.FO
