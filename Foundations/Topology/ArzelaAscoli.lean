import Foundations.Topology.Weierstrass

/-!
# The Arzelà–Ascoli theorem

Bolzano–Weierstrass says that bounded sequences of *numbers* have convergent subsequences. For
sequences of *functions* boundedness is not enough (think of `sin(nx)`); Giulio Ascoli (1883) and
Cesare Arzelà (1889) found the missing condition, **equicontinuity**: one `δ` serves for every
function of the family at once. Their theorem — the compactness criterion for subsets of `C[a, b]`
— is:

  **A uniformly bounded, equicontinuous sequence of functions on `[a, b]` has a uniformly
  convergent subsequence.**

The proof is Cantor's **diagonal argument** again. Enumerate a dense countable set of points
`p₀, p₁, …` of `[a, b]` (the points `a + (b − a)·m/(n+1)`). By Bolzano–Weierstrass, extract a
subsequence converging at `p₀`, from it a further subsequence converging at `p₁`, and so on; the
diagonal sequence converges at every `pₖ`. Equicontinuity spreads convergence from a finite
`δ`-net of the `pₖ` to all of `[a, b]`, uniformly — and the uniform Cauchy property gives a
uniform limit by completeness of ℝ.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Ascoli

/-- Strictly increasing index sequences preserve `<`. -/
theorem smono_lt {φ : Nat → Nat} (hφ : ∀ k, φ k < φ (k + 1)) {i j : Nat} (h : i < j) : φ i < φ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases e : i = j
    · rw [e]; exact hφ j
    · have := ih (by omega); have := hφ j; omega

/-- Strictly increasing index sequences are monotone. -/
theorem smono_le {φ : Nat → Nat} (hφ : ∀ k, φ k < φ (k + 1)) {i j : Nat} (h : i ≤ j) : φ i ≤ φ j := by
  rcases (by omega : i = j ∨ i < j) with e | e
  · rw [e]; exact Nat.le_refl _
  · exact Nat.le_of_lt (smono_lt hφ e)

/-- The index `k` of the pair `tri k = (n, m)` is at most `n² + m`. -/
theorem tri_index (k : Nat) : k ≤ (Vitali.tri k).1 * (Vitali.tri k).1 + (Vitali.tri k).2 := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    have hle := Vitali.tri_le k
    show k + 1 ≤ (if (Vitali.tri k).2 < (Vitali.tri k).1 then ((Vitali.tri k).1, (Vitali.tri k).2 + 1)
      else ((Vitali.tri k).1 + 1, 0)).1 * (if (Vitali.tri k).2 < (Vitali.tri k).1 then
      ((Vitali.tri k).1, (Vitali.tri k).2 + 1) else ((Vitali.tri k).1 + 1, 0)).1 +
      (if (Vitali.tri k).2 < (Vitali.tri k).1 then ((Vitali.tri k).1, (Vitali.tri k).2 + 1)
      else ((Vitali.tri k).1 + 1, 0)).2
    generalize (Vitali.tri k).1 = n at ih hle ⊢
    generalize (Vitali.tri k).2 = m at ih hle ⊢
    split
    · simp only; omega
    · simp only
      have : m = n := by omega
      subst this
      have : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
      omega

/-- The `k`-th grid point `a + (b − a) qₖ` of `[a, b]`. -/
noncomputable def pt (a b : R) (k : Nat) : R := a + (b - a) * Vitali.q k

/-- **The grid is a finite `δ`-net**: every `x ∈ [a, b]` lies within `(b − a)/(n + 1)` of a grid
point `a + (b − a)·m/(n + 1)` with `m ≤ n`. -/
theorem grid_near {a b x : R} (hab : a ≤ b) (h1 : a ≤ x) (h2 : x ≤ b) (n : Nat) :
    ∃ m, m ≤ n ∧ abs (x - (a + (b - a) * ((m : R) / ((n : R) + 1)))) ≤ (b - a) / ((n : R) + 1) := by
  have hn := Vitali.succ_pos n
  let u : Nat → R := fun j => a + (b - a) * ((j : R) / ((n : R) + 1))
  have hstep : ∀ j : Nat, u (j + 1) = u j + (b - a) / ((n : R) + 1) := fun j => by
    show a + (b - a) * (((j + 1 : Nat) : R) / ((n : R) + 1)) = _
    have : ((j + 1 : Nat) : R) = (j : R) + 1 := by grind
    rw [this]; show _ = a + (b - a) * ((j : R) / ((n : R) + 1)) + _; grind
  have hend : u (n + 1) = b := by
    show a + (b - a) * (((n + 1 : Nat) : R) / ((n : R) + 1)) = b
    have : ((n + 1 : Nat) : R) = (n : R) + 1 := by grind
    rw [this]; grind
  have hd : 0 ≤ (b - a) / ((n : R) + 1) := by
    rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg (by grind) (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hn))
  obtain ⟨j, hj, hmin⟩ := nat_least (fun j => x ≤ u (j + 1)) ⟨n, by rw [hend]; exact h2⟩
  have hjn : j ≤ n := by
    apply Classical.byContradiction; intro h
    exact hmin n (by omega) (by rw [hend]; exact h2)
  cases j with
  | zero =>
    refine ⟨0, Nat.zero_le _, abs_le.2 ⟨?_, ?_⟩⟩
    · have : u 0 = a := by show a + (b - a) * (((0 : Nat) : R) / ((n : R) + 1)) = a; grind
      show -((b - a) / ((n : R) + 1)) ≤ x - u 0; grind
    · have := hstep 0
      have : u 0 = a := by show a + (b - a) * (((0 : Nat) : R) / ((n : R) + 1)) = a; grind
      show x - u 0 ≤ _; grind
  | succ i =>
    have hi := hmin i (by omega)
    have := hstep (i + 1)
    refine ⟨i + 1, hjn, abs_le.2 ⟨?_, ?_⟩⟩
    · show -((b - a) / ((n : R) + 1)) ≤ x - u (i + 1); grind
    · show x - u (i + 1) ≤ _; grind

/-- **Arzelà–Ascoli theorem.** A uniformly bounded, equicontinuous sequence of functions on
`[a, b]` has a subsequence converging uniformly on `[a, b]`. -/
theorem arzela_ascoli {fs : Nat → R → R} {a b : R} (hab : a ≤ b)
    (hbdd : ∃ B, ∀ n x, a ≤ x → x ≤ b → abs (fs n x) ≤ B)
    (heq : ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧ ∀ n x y, a ≤ x → x ≤ b → a ≤ y → y ≤ b →
      abs (x - y) < δ → abs (fs n x - fs n y) < ε) :
    ∃ φ : Nat → Nat, (∀ k, φ k < φ (k + 1)) ∧ ∃ g : R → R,
      UnifOn (fun k => fs (φ k)) g (fun x => a ≤ x ∧ x ≤ b) := by
  obtain ⟨B, hB⟩ := hbdd
  have hpt : ∀ k, a ≤ pt a b k ∧ pt a b k ≤ b := fun k => by
    have hq := Vitali.q_mem k; unfold Vitali.I at hq
    have := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt hq.2) (by grind : (0 : R) ≤ b - a)
    have := OrderedRing.mul_nonneg (by grind : (0 : R) ≤ b - a) hq.1
    unfold pt; constructor <;> grind
  -- Strictly increasing index sequences.
  let S := {φ : Nat → Nat // ∀ k, φ k < φ (k + 1)}
  have step : ∀ (k : Nat) (φ : S), ∃ ψ : S, ∃ L, Tendsto (fun n => fs (φ.1 (ψ.1 n)) (pt a b k)) L :=
    fun k φ => by
      obtain ⟨ψ, hψ, L, hL⟩ := bolzano_weierstrass (a := fun n => fs (φ.1 n) (pt a b k))
        ⟨B, fun n => hB _ _ (hpt k).1 (hpt k).2⟩
      exact ⟨⟨ψ, hψ⟩, L, hL⟩
  let nxt : Nat → S → S := fun k φ =>
    ⟨fun n => φ.1 ((step k φ).choose.1 n), fun n => smono_lt φ.2 ((step k φ).choose.2 n)⟩
  let Φ : Nat → S := fun k =>
    Nat.rec (motive := fun _ => S) ⟨fun n => n, fun n => Nat.lt_succ_self n⟩ (fun k φ => nxt k φ) k
  have hΦ : ∀ k, Φ (k + 1) = nxt k (Φ k) := fun _ => rfl
  -- `Φ (k+1)` converges at `pₖ`.
  have hconv : ∀ k, ∃ L, Tendsto (fun n => fs ((Φ (k + 1)).1 n) (pt a b k)) L := fun k => by
    rw [hΦ]; exact (step k (Φ k)).choose_spec
  -- Later sequences are subsequences of earlier ones.
  have hsub : ∀ i j, i ≤ j → ∃ σ : Nat → Nat, (∀ n, n ≤ σ n) ∧ ∀ n, (Φ j).1 n = (Φ i).1 (σ n) := by
    intro i j hij
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    induction d with
    | zero => exact ⟨fun n => n, fun n => Nat.le_refl n, fun n => rfl⟩
    | succ d ih =>
      obtain ⟨σ, hσ1, hσ2⟩ := ih (by omega)
      let ψ := (step (i + d) (Φ (i + d))).choose
      refine ⟨fun n => σ (ψ.1 n), fun n => Nat.le_trans (le_of_strictMono ψ.2 n) (hσ1 _),
        fun n => ?_⟩
      rw [← Nat.add_assoc, hΦ]; exact hσ2 _
  -- The diagonal sequence.
  let D : Nat → Nat := fun n => (Φ n).1 n
  have hD : ∀ n, D n < D (n + 1) := fun n => by
    obtain ⟨σ, hσ1, hσ2⟩ := hsub n (n + 1) (by omega)
    show (Φ n).1 n < (Φ (n + 1)).1 (n + 1)
    rw [hσ2]; exact Nat.lt_of_lt_of_le ((Φ n).2 n) (smono_le (Φ n).2 (hσ1 (n + 1)))
  -- The diagonal converges at every grid point, hence is Cauchy there.
  have hDc : ∀ k, ∀ ε : R, 0 < ε → ∃ N, ∀ m m', N ≤ m → N ≤ m' →
      abs (fs (D m) (pt a b k) - fs (D m') (pt a b k)) < ε := fun k ε hε => by
    obtain ⟨L, hL⟩ := hconv k
    obtain ⟨N, hN⟩ := hL (ε / 2) (by grind)
    have key : ∀ m, max (k + 1) N ≤ m → abs (fs (D m) (pt a b k) - L) < ε / 2 := fun m hm => by
      obtain ⟨σ, hσ1, hσ2⟩ := hsub (k + 1) m (by omega)
      show abs (fs ((Φ m).1 m) (pt a b k) - L) < ε / 2
      rw [hσ2]; exact hN _ (Nat.le_trans (by omega) (hσ1 m))
    refine ⟨max (k + 1) N, fun m m' hm hm' => ?_⟩
    have k1 := key m hm; have k2 := key m' hm'
    rw [abs_sub_comm] at k2
    have := OF.abs_add (fs (D m) (pt a b k) - L) (L - fs (D m') (pt a b k))
    rw [show fs (D m) (pt a b k) - L + (L - fs (D m') (pt a b k)) =
      fs (D m) (pt a b k) - fs (D m') (pt a b k) by grind] at this
    grind
  -- Uniformly Cauchy on `[a, b]`.
  have hunifC : ∀ ε : R, 0 < ε → ∃ N, ∀ m m', N ≤ m → N ≤ m' → ∀ x, a ≤ x → x ≤ b →
      abs (fs (D m) x - fs (D m') x) < ε := fun ε hε => by
    obtain ⟨δ, hδ, hδ'⟩ := heq (ε / 3) (by grind)
    obtain ⟨n₀, hn₀⟩ := exists_div_lt (by grind : (0 : R) ≤ b - a) hδ
    let K := (n₀ + 1) * (n₀ + 1)
    -- One `N` for all grid points of index `< K`.
    have hfin : ∀ K', ∃ N, ∀ k, k < K' → ∀ m m', N ≤ m → N ≤ m' →
        abs (fs (D m) (pt a b k) - fs (D m') (pt a b k)) < ε / 3 := by
      intro K'
      induction K' with
      | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      | succ K' ih =>
        obtain ⟨N₁, h₁⟩ := ih
        obtain ⟨N₂, h₂⟩ := hDc K' (ε / 3) (by grind)
        refine ⟨max N₁ N₂, fun k hk m m' hm hm' => ?_⟩
        rcases (by omega : k < K' ∨ k = K') with e | e
        · exact h₁ k e m m' (by omega) (by omega)
        · rw [e]; exact h₂ m m' (by omega) (by omega)
    obtain ⟨N, hN⟩ := hfin K
    refine ⟨N, fun m m' hm hm' x h1 h2 => ?_⟩
    obtain ⟨j, hj, hjx⟩ := grid_near hab h1 h2 n₀
    obtain ⟨k, hk⟩ := Vitali.tri_surj n₀ j hj
    have hkK : k < K := by
      have := tri_index k; rw [hk] at this; simp only at this
      have : n₀ * n₀ + j < (n₀ + 1) * (n₀ + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
      omega
    have hpk : pt a b k = a + (b - a) * ((j : R) / ((n₀ : R) + 1)) := by
      unfold pt Vitali.q; rw [hk]
    have hclose : abs (x - pt a b k) < δ := by
      rw [hpk]; exact Std.lt_of_le_of_lt hjx (hn₀ n₀ (Nat.le_refl _))
    have k1 := hδ' (D m) x (pt a b k) h1 h2 (hpt k).1 (hpt k).2 hclose
    have k2 := hδ' (D m') x (pt a b k) h1 h2 (hpt k).1 (hpt k).2 hclose
    have k3 := hN k hkK m m' hm hm'
    have := abs_sub_le3 (fs (D m) x) (fs (D m) (pt a b k)) (fs (D m') (pt a b k)) (fs (D m') x)
    rw [abs_sub_comm (fs (D m') (pt a b k)) (fs (D m') x)] at this
    grind
  -- The pointwise limits form the uniform limit.
  have hlim : ∀ x, a ≤ x → x ≤ b → ∃ L, Tendsto (fun m => fs (D m) x) L := fun x h1 h2 =>
    cauchy_complete fun ε hε => by
      obtain ⟨N, hN⟩ := hunifC ε hε
      exact ⟨N, fun m m' hm hm' => hN m m' hm hm' x h1 h2⟩
  let g : R → R := fun x =>
    open Classical in if h : ∃ L, Tendsto (fun m => fs (D m) x) L then h.choose else 0
  have hg : ∀ x, a ≤ x → x ≤ b → Tendsto (fun m => fs (D m) x) (g x) := fun x h1 h2 => by
    have h := hlim x h1 h2
    show Tendsto _ (open Classical in if h : ∃ L, Tendsto (fun m => fs (D m) x) L then h.choose else 0)
    rw [dite_eq_left_of_eq_true (eq_true h)]; exact h.choose_spec
  refine ⟨D, hD, g, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hunifC (ε / 2) (by grind)
  refine ⟨N, fun n hn x hx => ?_⟩
  -- Pass to the limit in `m` in `|f_{D n}(x) − f_{D m}(x)| < ε/2`.
  have : abs (fs (D n) x - g x) ≤ ε / 2 := by
    apply Classical.byContradiction; intro hlt
    obtain ⟨M, hM⟩ := hg x hx.1 hx.2 (abs (fs (D n) x - g x) - ε / 2) (by grind)
    have k1 := hM (max M N) (by omega)
    have k2 := hN n (max M N) hn (by omega) x hx.1 hx.2
    have := OF.abs_add (fs (D n) x - fs (D (max M N)) x) (fs (D (max M N)) x - g x)
    rw [show fs (D n) x - fs (D (max M N)) x + (fs (D (max M N)) x - g x) = fs (D n) x - g x by
      grind] at this
    grind
  show abs (fs (D n) x - g x) < ε
  grind

end Ascoli

end Foundations.Topology
