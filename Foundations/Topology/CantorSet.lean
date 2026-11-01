import Foundations.Topology.Baire

/-!
# The Cantor set

Remove the open middle third `(1/3, 2/3)` from `[0, 1]`, then the middle thirds of the two
remaining intervals, and so on forever. What remains is the **Cantor set** (Cantor 1883; found
earlier by H. J. S. Smith, 1874). It is a strange object:

* it is **closed** and **compact** (an intersection of finite unions of closed intervals inside
  `[0, 1]`);
* it has **empty interior** — it contains no interval at all, since at stage `n` every remaining
  piece has length `3⁻ⁿ`;
* yet it is **uncountable**: its points are exactly the numbers `Σ dₖ 3^{-(k+1)}` with ternary
  digits `dₖ ∈ {0, 2}`, and these correspond injectively to the infinite binary sequences
  `ℕ → Bool`, which Cantor's diagonal argument shows to be uncountable.

So "small" in the sense of topology (nowhere dense) and in the sense of length (total length
`(2/3)ⁿ → 0`) is compatible with being as large as the continuum.

The stages are defined by self-similarity: `C₀ = [0, 1]` and `x ∈ C_{n+1}` iff `3x ∈ Cₙ` or
`3x − 2 ∈ Cₙ`, i.e. `C_{n+1} = Cₙ/3 ∪ (2/3 + Cₙ/3)`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Cantor

/-- The `n`-th stage of the construction: `C₀ = [0, 1]`, `C_{n+1} = Cₙ/3 ∪ (2/3 + Cₙ/3)`. -/
def stage : Nat → R → Prop
  | 0, x => 0 ≤ x ∧ x ≤ 1
  | n + 1, x => stage n (3 * x) ∨ stage n (3 * x - 2)

/-- **The Cantor set**: the points belonging to every stage. -/
def C (x : R) : Prop := ∀ n, stage n x

/-- Every stage lies in `[0, 1]`. -/
theorem stage_sub (n : Nat) : ∀ x, stage n x → 0 ≤ x ∧ x ≤ 1 := by
  induction n with
  | zero => intro x h; exact h
  | succ n ih =>
    intro x h
    rcases h with h | h <;> (have := ih _ h; constructor <;> grind)

/-- The preimage of an open set under `x ↦ 3x − c` is open. -/
theorem isOpen_affine {U : R → Prop} (hU : IsOpen U) (c : R) : IsOpen (fun x => U (3 * x - c)) := by
  intro x hx
  obtain ⟨ε, hε, h⟩ := hU _ hx
  refine ⟨ε / 3, by grind, fun y hy => h _ ?_⟩
  have := abs_lt.1 hy
  show abs (3 * x - c - (3 * y - c)) < ε
  exact abs_lt.2 ⟨by grind, by grind⟩

/-- **Each stage is closed.** -/
theorem isClosed_stage (n : Nat) : IsClosed (stage n) := by
  induction n with
  | zero =>
    intro x hx
    have : x < 0 ∨ 1 < x := by
      rcases (by grind : x < 0 ∨ 1 < x ∨ (0 ≤ x ∧ x ≤ 1)) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hx
    rcases this with h | h
    · exact ⟨-x, by grind, fun y hy hy' => by have := abs_lt.1 hy; have := hy'.1; grind⟩
    · exact ⟨x - 1, by grind, fun y hy hy' => by have := abs_lt.1 hy; have := hy'.2; grind⟩
  | succ n ih =>
    intro x hx
    have h1 := isOpen_affine ih 0
    have h2 := isOpen_affine ih 2
    obtain ⟨ε₁, he₁, k₁⟩ := h1 x (by show ¬ stage n (3 * x - 0); rw [show 3 * x - 0 = 3 * x by grind]
                                     exact fun h => hx (Or.inl h))
    obtain ⟨ε₂, he₂, k₂⟩ := h2 x (fun h => hx (Or.inr h))
    obtain ⟨ε, he, e1, e2⟩ := exists_pos_le_both he₁ he₂
    refine ⟨ε, he, fun y hy hy' => ?_⟩
    have a := k₁ y (by grind)
    have b := k₂ y (by grind)
    simp only at a b
    rw [show 3 * y - 0 = 3 * y by grind] at a
    rcases hy' with h | h
    · exact a h
    · exact b h

/-- **The Cantor set is closed.** -/
theorem isClosed_C : IsClosed C := by
  intro x hx
  obtain ⟨n, hn⟩ : ∃ n, ¬ stage n x := by
    apply Classical.byContradiction; intro h
    exact hx fun n => by apply Classical.byContradiction; intro h'; exact h ⟨n, h'⟩
  obtain ⟨ε, hε, h⟩ := isClosed_stage n x hn
  exact ⟨ε, hε, fun y hy hy' => h y hy (hy' n)⟩

/-- The Cantor set lies in `[0, 1]`. -/
theorem C_sub {x : R} (h : C x) : 0 ≤ x ∧ x ≤ 1 := h 0

/-- **The Cantor set is compact.** -/
theorem isCompact_C : IsCompact (Topology.metric R) C := by
  apply IsSeqCompact.isCompact
  intro s hs
  obtain ⟨φ, hφ, L, -, hL⟩ := (heine_borel 0 1).isSeqCompact s fun n => C_sub (hs n)
  exact ⟨φ, hφ, L, isClosed_C.mem_of_converges (fun k => hs (φ k)) hL, hL⟩

/-! ## Empty interior -/

/-- Near every point of the `n`-th stage — within `3⁻ⁿ/2` — lies a point missing from the next
stage. -/
theorem exists_gap (n : Nat) : ∀ x, stage n x → ∃ y, abs (x - y) ≤ (1 / 3) ^ n / 2 ∧ ¬ stage (n + 1) y := by
  induction n with
  | zero =>
    intro x hx
    refine ⟨1 / 2, ?_, ?_⟩
    · obtain ⟨h0, h1⟩ := hx; show abs (x - 1 / 2) ≤ (1 / 3) ^ 0 / 2
      exact abs_le.2 ⟨by show _ ≤ _ - _; show -((1 : R) / 2) ≤ x - 1 / 2; grind, by show x - 1 / 2 ≤ (1 : R) / 2; grind⟩
    · show ¬ (stage 0 (3 * (1 / 2)) ∨ stage 0 (3 * (1 / 2) - 2))
      intro h; rcases h with h | h <;> (have := h.1; have := h.2; grind)
  | succ n ih =>
    intro x hx
    have hp : (0 : R) ≤ (1 / 3) ^ n := pow_le_pow_left.pow_nonneg (by grind) n
    have hp1 : (1 / 3 : R) ^ n ≤ 1 := by
      have := pow_le_pow_left (by grind : (0 : R) ≤ 1 / 3) (by grind : (1 / 3 : R) ≤ 1) n
      rw [one_pow] at this; exact this
    rw [pow_succ']
    rcases hx with hx | hx
    · obtain ⟨y', hy1, hy2⟩ := ih _ hx
      have := stage_sub n _ hx
      have := abs_le.1 hy1
      refine ⟨y' / 3, abs_le.2 ⟨by grind, by grind⟩, fun h => ?_⟩
      rcases h with h | h
      · exact hy2 (by rw [show 3 * (y' / 3) = y' by grind] at h; exact h)
      · have := stage_sub (n + 1) _ h; grind
    · obtain ⟨y', hy1, hy2⟩ := ih _ hx
      have := stage_sub n _ hx
      have := abs_le.1 hy1
      refine ⟨(y' + 2) / 3, abs_le.2 ⟨by grind, by grind⟩, fun h => ?_⟩
      rcases h with h | h
      · have := stage_sub (n + 1) _ h; grind
      · exact hy2 (by rw [show 3 * ((y' + 2) / 3) - 2 = y' by grind] at h; exact h)

/-- **The Cantor set has empty interior**: every ball around one of its points contains points
outside it. -/
theorem C_empty_interior {x : R} (hx : C x) {ε : R} (hε : 0 < ε) : ∃ y, abs (x - y) < ε ∧ ¬ C y := by
  obtain ⟨N, hN⟩ := tendsto_pow_zero (r := 1 / 3) (by grind) (by grind) ε hε
  have := abs_lt.1 (hN N (Nat.le_refl N))
  obtain ⟨y, h1, h2⟩ := exists_gap N x (hx N)
  have hp : (0 : R) ≤ (1 / 3) ^ N := pow_le_pow_left.pow_nonneg (by grind) N
  exact ⟨y, by simp only at this; grind, fun h => h2 (h (N + 1))⟩

/-! ## Uncountability -/

/-- The `k`-th term `dₖ / 3^{k+1}` (with `dₖ = 2` if `b k`, `0` otherwise). -/
noncomputable def term (b : Nat → Bool) (k : Nat) : R := (if b k then 2 else 0) * (1 / 3) ^ (k + 1)

/-- `0 ≤ dₖ 3^{-(k+1)} ≤ (2/3) 3^{-k}`. -/
theorem term_bounds (b : Nat → Bool) (k : Nat) :
    0 ≤ term b k ∧ term b k ≤ 2 / 3 * (1 / 3) ^ k := by
  have hp : (0 : R) ≤ (1 / 3) ^ k := pow_le_pow_left.pow_nonneg (by grind) k
  unfold term; rw [pow_succ']
  constructor
  · split
    · exact OrderedRing.mul_nonneg (by grind) (OrderedRing.mul_nonneg hp (by grind))
    · grind
  · split <;> grind

/-- `Σ (2/3) 3^{-k} = 1`. -/
theorem hasSum_bound : HasSum (fun k => 2 / 3 * (1 / 3 : R) ^ k) 1 := by
  have h := (hasSum_geometric (r := 1 / 3) (by rw [abs_of_nonneg (by grind)]; grind)).const_mul (2 / 3)
  rw [show (2 / 3 : R) * (1 / (1 - 1 / 3)) = 1 by grind] at h
  exact h

/-- The ternary series converges, to a number in `[0, 1]`. -/
theorem exists_val (b : Nat → Bool) : ∃ s, HasSum (term b) s ∧ s ≤ 1 :=
  comparison (fun k => (term_bounds b k).1) (fun k => (term_bounds b k).2) hasSum_bound

/-- The point `Σ dₖ 3^{-(k+1)}` of the Cantor set with "digits" `b`. -/
noncomputable def val (b : Nat → Bool) : R := (exists_val b).choose

/-- `val b` is the sum of the series. -/
theorem hasSum_val (b : Nat → Bool) : HasSum (term b) (val b) := (exists_val b).choose_spec.1

/-- `0 ≤ val b ≤ 1`. -/
theorem val_mem (b : Nat → Bool) : 0 ≤ val b ∧ val b ≤ 1 :=
  ⟨hasSum_nonneg (fun k => (term_bounds b k).1) (hasSum_val b), (exists_val b).choose_spec.2⟩

/-- Self-similarity: `3 · val b = d₀ + val (b ∘ succ)`. -/
theorem three_val (b : Nat → Bool) :
    3 * val b = (if b 0 then 2 else 0) + val (fun k => b (k + 1)) := by
  have h1 := hasSum_succ_iff.2 (hasSum_val b)
  have h2 := (hasSum_val (fun k => b (k + 1))).const_mul (1 / 3)
  have e : ∀ k, 1 / 3 * term (fun k => b (k + 1)) k = term b (k + 1) := fun k => by
    unfold term; rw [pow_succ' (1 / 3 : R) (k + 1)]; grind
  have := h1.unique (h2.congr e)
  have e0 : term b 0 = (if b 0 then 2 else 0) * (1 / 3) := by
    unfold term; rw [pow_succ']; show _ * (1 * _) = _; grind
  rw [e0] at this
  split at this <;> split <;> grind

/-- **Every such point lies in the Cantor set.** -/
theorem val_mem_C (b : Nat → Bool) : C (val b) := by
  intro n
  induction n generalizing b with
  | zero => exact val_mem b
  | succ n ih =>
    have h := three_val b
    cases hb : b 0
    · left; rw [hb] at h; rw [h, show (if false = true then (2 : R) else 0) = 0 from rfl]
      rw [show (0 : R) + val (fun k => b (k + 1)) = val (fun k => b (k + 1)) by grind]; exact ih _
    · right; rw [hb] at h; rw [h, show (if true = true then (2 : R) else 0) = 2 from rfl]
      rw [show (2 : R) + val (fun k => b (k + 1)) - 2 = val (fun k => b (k + 1)) by grind]; exact ih _

/-- Distinct first digits separate the points: one lies in `[0, 1/3]`, the other in `[2/3, 1]`. -/
theorem val_ne_of_head {b b' : Nat → Bool} (hne : b 0 ≠ b' 0) : val b ≠ val b' := by
  intro he
  have h := three_val b; have h' := three_val b'
  have m := val_mem (fun k => b (k + 1)); have m' := val_mem (fun k => b' (k + 1))
  cases hb : b 0 <;> cases hb' : b' 0 <;> rw [hb] at h hne <;> rw [hb'] at h' hne
  · exact hne rfl
  · simp only [Bool.false_eq_true, ite_false, ite_true] at h h'; grind
  · simp only [Bool.false_eq_true, ite_false, ite_true] at h h'; grind
  · exact hne rfl

/-- **Distinct digit sequences give distinct points.** -/
theorem val_injective : ∀ k (b b' : Nat → Bool), b k ≠ b' k → val b ≠ val b' := by
  intro k
  induction k with
  | zero => intro b b' hne; exact val_ne_of_head hne
  | succ k ih =>
    intro b b' hne he
    by_cases h0 : b 0 = b' 0
    · apply ih (fun j => b (j + 1)) (fun j => b' (j + 1)) hne
      have h := three_val b; have h' := three_val b'
      rw [h0] at h; grind
    · exact val_ne_of_head h0 he

/-- **The Cantor set is uncountable**: no sequence of reals lists all of its points. -/
theorem C_uncountable (s : Nat → R) : ∃ x, C x ∧ ∀ n, x ≠ s n := by
  -- Cantor's diagonal argument on the digit sequences.
  let code : Nat → Nat → Bool := fun n =>
    open Classical in if h : ∃ b, val b = s n then h.choose else fun _ => false
  let d : Nat → Bool := fun n => !(code n n)
  refine ⟨val d, val_mem_C d, fun n hn => ?_⟩
  have hex : ∃ b, val b = s n := ⟨d, hn⟩
  have hc : code n = hex.choose := by
    show (open Classical in if h : ∃ b, val b = s n then h.choose else fun _ => false) = _
    rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hval : val (code n) = val d := by rw [hc, hex.choose_spec, hn]
  apply val_injective n (code n) d _ hval
  show code n n ≠ !(code n n)
  cases code n n <;> decide

end Cantor

end Foundations.Topology
