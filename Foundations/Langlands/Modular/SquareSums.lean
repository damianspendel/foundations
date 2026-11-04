import Foundations.Langlands.Modular.Forms

/-!
# Finite sums over squares of the lattice ℤ²

An Eisenstein series `Σ' (mτ + n)^{−k}` runs over the lattice `ℤ²`, which has no natural order.
We sum it over the **growing squares** `Q_N = {(m, n) : |m| ≤ N, |n| ≤ N}`, and this file
provides the finite combinatorics needed for that:

* interval sums `Σ_{a ≤ n < a + ℓ} h(n)` (`isum`) and square sums `Σ_{Q_N} g` (`sq`), built
  from the generic finite sums `gsum` of Part II;
* **embedding** a short interval into a longer one, padding with zeros (`isum_embed`), and
  its two-dimensional form, the **restriction** of a square sum to a smaller square
  (`sq_restrict`);
* the two **finite symmetries** of a square, `(m, n) ↦ (n, m)` (`sq_swap`) and
  `n ↦ −n` (`sq_neg_snd`), which are all the reindexing that the law under `τ ↦ −1/τ` needs;
* the **triangle inequality** for square sums (`cabs_sq_le`) and monotonicity of real ones;
* the **comparison lemma** `cabs_sq_ite_sub_le`, which is the heart of the rearrangement
  argument: if a finite region `P ⊆ Q_L` contains `Q_M`, then `Σ_P g` differs from `Σ_{Q_M} g` by
  at most `Σ_{Q_L} |g| − Σ_{Q_M} |g|`. When `Σ |g|` converges along squares, this difference is a
  tail and tends to zero; so any reasonable exhaustion of ℤ² gives the same sum;
* the **shell estimate** `sq_cabs_le`: counting the `8N` lattice points with `max(|m|, |n|) = N`,
  a bound `|g(m, n)| · max(|m|, |n|)³ ≤ B` gives `Σ_{Q_N} |g| ≤ 16 B` for every `N`;
* limits of complex sequences in the modulus (`CLim`), with uniqueness and the Cauchy criterion.
-/

namespace Foundations.Langlands.Modular

open Foundations.Numbers Foundations.Numbers.C Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

namespace Lattice

/-! ## Generic finite sums -/

section Generic

variable {α : Type} [Field α]

/-- Reduce an `if` whose condition holds. -/
theorem ite_t {β : Type} {p : Prop} [Decidable p] (h : p) (x y : β) : (if p then x else y) = x := by
  simp [h]

/-- Reduce an `if` whose condition fails. -/
theorem ite_f {β : Type} {p : Prop} [Decidable p] (h : ¬ p) (x y : β) :
    (if p then x else y) = y := by
  simp [h]

/-- A sum of zeros is zero. -/
theorem gsum_zero (n : Nat) : gsum (fun _ => (0 : α)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum_succ, ih]; grind

/-- Sums are compatible with subtraction. -/
theorem gsum_sub (f g : Nat → α) (n : Nat) :
    gsum (fun k => f k - g k) n = gsum f n - gsum g n := by
  induction n with
  | zero => show (0 : α) = 0 - 0; grind
  | succ n ih => rw [gsum_succ, gsum_succ, gsum_succ, ih]; grind

/-- **Reversing a finite sum.** `Σ_{i<n} f(n − 1 − i) = Σ_{i<n} f(i)`. -/
theorem gsum_reverse (f : Nat → α) (n : Nat) : gsum (fun i => f (n - 1 - i)) n = gsum f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gsum_succ', gsum_succ, ← ih]
    rw [show n + 1 - 1 - 0 = n by omega]
    rw [gsum_congr (g := fun i => f (n - 1 - i)) fun i hi => by congr 1; omega]
    grind

/-- **Finite Fubini.** The two iterated sums over a rectangle agree. -/
theorem gsum_comm (f : Nat → Nat → α) (m n : Nat) :
    gsum (fun i => gsum (fun j => f i j) m) n = gsum (fun j => gsum (fun i => f i j) n) m := by
  induction n with
  | zero => exact (gsum_zero m).symm
  | succ n ih => rw [gsum_succ, ih, ← gsum_add]; rfl

/-! ## Interval sums and square sums -/

/-- **Interval sum.** `isum a ℓ h = Σ_{a ≤ n < a + ℓ} h(n)` over integers. -/
def isum (a : Int) (len : Nat) (h : Int → α) : α := gsum (fun i => h (a + (i : Int))) len

/-- **Square sum.** `sq N g = Σ_{|m| ≤ N} Σ_{|n| ≤ N} g(m, n)`, the sum over the square `Q_N`. -/
def sq (N : Nat) (g : Int → Int → α) : α :=
  isum (-(N : Int)) (2 * N + 1) (fun m => isum (-(N : Int)) (2 * N + 1) (g m))

/-- Interval sums only depend on the values in the interval. -/
theorem isum_congr {a : Int} {len : Nat} {h h' : Int → α}
    (H : ∀ n, a ≤ n → n < a + len → h n = h' n) : isum a len h = isum a len h' :=
  gsum_congr fun i hi => H _ (by omega) (by omega)

/-- An interval sum of zeros vanishes. -/
theorem isum_zero (a : Int) (len : Nat) : isum a len (fun _ => (0 : α)) = 0 := gsum_zero len

/-- Interval sums are additive. -/
theorem isum_add (a : Int) (len : Nat) (h h' : Int → α) :
    isum a len (fun n => h n + h' n) = isum a len h + isum a len h' := gsum_add _ _ _

/-- Interval sums are compatible with subtraction. -/
theorem isum_sub (a : Int) (len : Nat) (h h' : Int → α) :
    isum a len (fun n => h n - h' n) = isum a len h - isum a len h' := gsum_sub _ _ _

/-- Constants factor out of interval sums. -/
theorem isum_mul_left (c : α) (a : Int) (len : Nat) (h : Int → α) :
    isum a len (fun n => c * h n) = c * isum a len h := gsum_mul_left _ _ _

/-- **Padding an interval with zeros.** If `[a, a + ℓ) ⊆ [b, b + ℓ')`, then summing `h` over the
small interval is the same as summing over the large one the function equal to `h` on the
small interval and to `0` elsewhere. -/
theorem isum_embed {a b : Int} {len len' : Nat} (hab : b ≤ a) (hlen : a + len ≤ b + len')
    (h : Int → α) :
    isum b len' (fun n => if a ≤ n ∧ n < a + len then h n else 0) = isum a len h := by
  obtain ⟨p, hp⟩ : ∃ p : Nat, (p : Int) = a - b := ⟨(a - b).toNat, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r : Nat, len' = p + (len + r) := ⟨len' - p - len, by omega⟩
  subst hr
  unfold isum
  rw [gsum_split, gsum_split]
  have h1 : gsum (fun i => (if a ≤ b + (i : Int) ∧ b + (i : Int) < a + len then h (b + i) else 0)) p
      = 0 := by
    rw [gsum_congr (g := fun _ => (0 : α)) fun i hi => by rw [ite_f (by omega)]]
    exact gsum_zero p
  have h2 : gsum (fun i => (if a ≤ b + ((p + i : Nat) : Int) ∧ b + ((p + i : Nat) : Int) < a + len
      then h (b + ((p + i : Nat) : Int)) else 0)) len = gsum (fun i => h (a + (i : Int))) len := by
    apply gsum_congr; intro i hi
    rw [ite_t (by omega)]; congr 1; omega
  have h3 : gsum (fun i => (if a ≤ b + ((p + (len + i) : Nat) : Int) ∧
      b + ((p + (len + i) : Nat) : Int) < a + len then h (b + ((p + (len + i) : Nat) : Int))
      else 0)) r = 0 := by
    rw [gsum_congr (g := fun _ => (0 : α)) fun i hi => by rw [ite_f (by omega)]]
    exact gsum_zero r
  simp only [] at h1 h2 h3 ⊢
  rw [h1, h2]
  have h3' : gsum (fun k => (if a ≤ b + ((p + (len + k) : Nat) : Int) ∧
      b + ((p + (len + k) : Nat) : Int) < a + len then h (b + ((p + (len + k) : Nat) : Int))
      else 0)) r = gsum (fun k => (fun i => (if a ≤ b + ((p + i : Nat) : Int) ∧
      b + ((p + i : Nat) : Int) < a + len then h (b + ((p + i : Nat) : Int)) else 0)) (len + k)) r
      := by
    apply gsum_congr; intro i hi; simp only []
  rw [← h3', h3]; grind

/-- **A one-point sum.** Summing over a longer interval a function supported at `c` gives its
value at `c`. -/
theorem isum_single {b c : Int} {len : Nat} (h1 : b ≤ c) (h2 : c < b + len) (x : α) :
    isum b len (fun n => if n = c then x else 0) = x := by
  have := isum_embed (a := c) (len := 1) (len' := len) h1 (by omega) (fun _ => x)
  rw [isum_congr (h' := fun n => if c ≤ n ∧ n < c + ((1 : Nat) : Int) then x else 0)
    fun n _ _ => by by_cases hn : n = c <;> simp [hn] <;> omega]
  rw [this]; show (0 : α) + x = x; grind

/-- **Reflection.** On a symmetric interval, `Σ_{|n| ≤ N} h(−n) = Σ_{|n| ≤ N} h(n)`. -/
theorem isum_neg (N : Nat) (h : Int → α) :
    isum (-(N : Int)) (2 * N + 1) (fun n => h (-n)) = isum (-(N : Int)) (2 * N + 1) h := by
  unfold isum
  rw [← gsum_reverse (fun i => h (-(N : Int) + (i : Int)))]
  apply gsum_congr; intro i hi; simp only []; congr 1; omega

/-- **Swapping coordinates.** `Σ_{Q_N} g(n, m) = Σ_{Q_N} g(m, n)`. -/
theorem sq_swap (N : Nat) (g : Int → Int → α) : sq N (fun m n => g n m) = sq N g :=
  gsum_comm (fun i j => g (-(N : Int) + (j : Int)) (-(N : Int) + (i : Int))) _ _

/-- **Reflecting the second coordinate.** `Σ_{Q_N} g(m, −n) = Σ_{Q_N} g(m, n)`. -/
theorem sq_neg_snd (N : Nat) (g : Int → Int → α) : sq N (fun m n => g m (-n)) = sq N g := by
  unfold sq; congr 1; funext m; exact isum_neg N (g m)

/-- Square sums only depend on the values on the square. -/
theorem sq_congr {N : Nat} {g g' : Int → Int → α}
    (H : ∀ m n, -(N : Int) ≤ m → m ≤ N → -(N : Int) ≤ n → n ≤ N → g m n = g' m n) :
    sq N g = sq N g' :=
  isum_congr fun m h1 h2 => isum_congr fun n h3 h4 => H m n h1 (by omega) h3 (by omega)

/-- Square sums are additive. -/
theorem sq_add (N : Nat) (g g' : Int → Int → α) :
    sq N (fun m n => g m n + g' m n) = sq N g + sq N g' := by
  unfold sq; rw [← isum_add]; congr 1; funext m; exact isum_add _ _ _ _

/-- Square sums are compatible with subtraction. -/
theorem sq_sub (N : Nat) (g g' : Int → Int → α) :
    sq N (fun m n => g m n - g' m n) = sq N g - sq N g' := by
  unfold sq; rw [← isum_sub]; congr 1; funext m; exact isum_sub _ _ _ _

/-- Constants factor out of square sums. -/
theorem sq_mul_left (c : α) (N : Nat) (g : Int → Int → α) :
    sq N (fun m n => c * g m n) = c * sq N g := by
  unfold sq; rw [← isum_mul_left]; congr 1; funext m; exact isum_mul_left _ _ _ _

/-- Membership in the square `Q_M`. -/
def InSq (M : Nat) (m n : Int) : Prop := -(M : Int) ≤ m ∧ m ≤ M ∧ -(M : Int) ≤ n ∧ n ≤ M

/-- Membership in a square is decidable. -/
instance (M : Nat) (m n : Int) : Decidable (InSq M m n) := by unfold InSq; infer_instance

/-- **Restriction to a smaller square.** For `M ≤ L`, summing over `Q_L` the function equal to `g`
on `Q_M` and to `0` elsewhere gives the sum of `g` over `Q_M`. -/
theorem sq_restrict {M L : Nat} (hML : M ≤ L) (g : Int → Int → α) :
    sq L (fun m n => if InSq M m n then g m n else 0) = sq M g := by
  unfold sq
  have inner : ∀ m : Int, isum (-(L : Int)) (2 * L + 1)
      (fun n => if InSq M m n then g m n else 0) =
      if -(M : Int) ≤ m ∧ m < -(M : Int) + ((2 * M + 1 : Nat) : Int)
      then isum (-(M : Int)) (2 * M + 1) (g m) else 0 := by
    intro m
    by_cases hm : -(M : Int) ≤ m ∧ m < -(M : Int) + ((2 * M + 1 : Nat) : Int)
    · rw [ite_t hm]
      refine Eq.trans ?_ (isum_embed (b := -(L : Int)) (len' := 2 * L + 1) (by omega) (by omega)
        (g m))
      apply isum_congr; intro n _ _
      by_cases hn : -(M : Int) ≤ n ∧ n < -(M : Int) + ((2 * M + 1 : Nat) : Int)
      · rw [ite_t (by unfold InSq; omega), ite_t hn]
      · rw [ite_f (by unfold InSq; omega), ite_f hn]
    · rw [ite_f hm]
      refine Eq.trans ?_ (isum_zero (-(L : Int)) (2 * L + 1))
      apply isum_congr; intro n _ _
      rw [ite_f (by unfold InSq; omega)]
  rw [show (fun m => isum (-(L : Int)) (2 * L + 1) (fun n => if InSq M m n then g m n else 0)) =
    _ from funext inner]
  exact isum_embed (by omega) (by omega) _

end Generic

/-! ## Real and complex estimates -/

/-- Real finite sums are monotone in their terms. -/
theorem gsum_le {f g : Nat → R} {n : Nat} (h : ∀ i, i < n → f i ≤ g i) : gsum f n ≤ gsum g n := by
  induction n with
  | zero => show (0 : R) ≤ 0; grind
  | succ n ih =>
    rw [gsum_succ, gsum_succ]; have := ih fun i hi => h i (by omega); have := h n (by omega)
    grind

/-- Real square sums are monotone in their terms (on the square). -/
theorem sq_le {N : Nat} {g g' : Int → Int → R}
    (H : ∀ m n, -(N : Int) ≤ m → m ≤ N → -(N : Int) ≤ n → n ≤ N → g m n ≤ g' m n) :
    sq N g ≤ sq N g' :=
  gsum_le fun i _ => gsum_le fun j _ => H _ _ (by omega) (by omega) (by omega) (by omega)

/-- Triangle inequality for finite sums, in the modulus. -/
theorem cabs_gsum_le (f : Nat → C) (n : Nat) : cabs (gsum f n) ≤ gsum (fun i => cabs (f i)) n := by
  induction n with
  | zero => show cabs 0 ≤ 0; rw [cabs_zero]; grind
  | succ n ih => rw [gsum_succ, gsum_succ]; have := cabs_add (gsum f n) (f n); grind

/-- **Triangle inequality for square sums.** `|Σ_{Q_N} g| ≤ Σ_{Q_N} |g|`. -/
theorem cabs_sq_le (N : Nat) (g : Int → Int → C) :
    cabs (sq N g) ≤ sq N (fun m n => cabs (g m n)) :=
  Std.le_trans (cabs_gsum_le _ _) (gsum_le fun _ _ => cabs_gsum_le _ _)

/-- A sum of `n` ones is `n`. -/
theorem gsum_one (n : Nat) : gsum (fun _ => (1 : R)) n = (n : R) := by
  induction n with
  | zero => show (0 : R) = ((0 : Nat) : R); grind
  | succ n ih => rw [gsum_succ, ih]; grind

/-- The square `Q_N` has `(2N + 1)²` points. -/
theorem sq_one (N : Nat) : sq N (fun _ _ => (1 : R)) = ((2 * N + 1 : Nat) : R) * ((2 * N + 1 : Nat) : R) := by
  show gsum (fun _ => gsum (fun _ => (1 : R)) (2 * N + 1)) (2 * N + 1) = _
  rw [gsum_one, gsum_congr (g := fun _ => ((2 * N + 1 : Nat) : R) * 1) fun _ _ => by grind,
    gsum_mul_left, gsum_one]

/-- **The comparison lemma.** Let `P` be a region containing the square `Q_M`, with `M ≤ L`.
Then the sum of `g` over `P ∩ Q_L` differs from its sum over `Q_M` by at most
`Σ_{Q_L} |g| − Σ_{Q_M} |g|`. -/
theorem cabs_sq_ite_sub_le {M L : Nat} (hML : M ≤ L) (P : Int → Int → Prop)
    [∀ m n, Decidable (P m n)] (hP : ∀ m n, InSq M m n → P m n) (g : Int → Int → C) :
    cabs (sq L (fun m n => if P m n then g m n else 0) - sq M g) ≤
      sq L (fun m n => cabs (g m n)) - sq M (fun m n => cabs (g m n)) := by
  rw [← sq_restrict hML g, ← sq_restrict hML (fun m n => cabs (g m n)), ← sq_sub, ← sq_sub]
  refine Std.le_trans (cabs_sq_le _ _) (sq_le fun m n _ _ _ _ => ?_)
  by_cases hQ : InSq M m n
  · rw [ite_t (hP m n hQ), ite_t hQ, ite_t hQ, show g m n - g m n = 0 by grind, cabs_zero]
    grind
  · rw [ite_f hQ, ite_f hQ, show (cabs (g m n) - 0 : R) = cabs (g m n) by grind]
    by_cases hp : P m n
    · rw [ite_t hp, show g m n - 0 = g m n by grind]; grind
    · rw [ite_f hp, show (0 : C) - 0 = 0 by grind, cabs_zero]; exact cabs_nonneg _

/-! ## Limits of complex sequences in the modulus -/

/-- **Convergence in ℂ.** `CLim s L`: for every `ε > 0`, eventually `|sₙ − L| < ε`. -/
def CLim (s : Nat → C) (L : C) : Prop :=
  ∀ ε : R, 0 < ε → ∃ N, ∀ n, N ≤ n → cabs (s n - L) < ε

/-- A complex number of arbitrarily small modulus is zero. -/
theorem eq_zero_of_cabs_lt {z : C} (h : ∀ ε : R, 0 < ε → cabs z < ε) : z = 0 := by
  apply eq_zero_of_cabs
  have := cabs_nonneg z
  rcases (by grind : cabs z = 0 ∨ 0 < cabs z) with e | e
  · exact e
  · have := h _ e; grind

/-- **Limits are unique.** -/
theorem CLim.unique {s : Nat → C} {L M : C} (hL : CLim s L) (hM : CLim s M) : L = M := by
  have : L - M = 0 := eq_zero_of_cabs_lt fun ε hε => by
    obtain ⟨N₁, h₁⟩ := hL (ε / 2) (by grind)
    obtain ⟨N₂, h₂⟩ := hM (ε / 2) (by grind)
    have k1 := h₁ (max N₁ N₂) (by omega)
    have k2 := h₂ (max N₁ N₂) (by omega)
    rw [cabs_sub_comm] at k1
    have := cabs_add (L - s (max N₁ N₂)) (s (max N₁ N₂) - M)
    rw [show L - s (max N₁ N₂) + (s (max N₁ N₂) - M) = L - M by grind] at this
    grind
  grind

/-- Limits are compatible with multiplication by a constant. -/
theorem CLim.const_mul (c : C) {s : Nat → C} {L : C} (h : CLim s L) :
    CLim (fun n => c * s n) (c * L) := fun ε hε => by
  have hc := cabs_nonneg c
  obtain ⟨N, hN⟩ := h (ε / (cabs c + 1)) (OF.div_pos hε (by grind))
  refine ⟨N, fun n hn => ?_⟩
  rw [show c * s n - c * L = c * (s n - L) by grind, cabs_mul]
  have k := hN n hn
  have k2 := OrderedRing.mul_le_mul_of_nonneg_right (by grind : cabs c ≤ cabs c + 1)
    (cabs_nonneg (s n - L))
  have k3 := OrderedRing.mul_lt_mul_of_pos_left k (by grind : (0 : R) < cabs c + 1)
  have e : (cabs c + 1) * (ε / (cabs c + 1)) = ε := by grind
  grind

/-- Two sequences whose distance tends to zero have the same limits. -/
theorem CLim.of_cabs_sub_le {s t : Nat → C} {L : C} (ht : CLim t L) {e : Nat → R}
    (he : ∀ ε : R, 0 < ε → ∃ N, ∀ n, N ≤ n → e n < ε) (hst : ∀ n, cabs (s n - t n) ≤ e n) :
    CLim s L := fun ε hε => by
  obtain ⟨N₁, h₁⟩ := ht (ε / 2) (by grind)
  obtain ⟨N₂, h₂⟩ := he (ε / 2) (by grind)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have k1 := h₁ n (by omega)
  have k2 := h₂ n (by omega)
  have k3 := hst n
  have := cabs_add (s n - t n) (t n - L)
  rw [show s n - t n + (t n - L) = s n - L by grind] at this
  grind

/-- **The Cauchy criterion in ℂ.** A sequence whose terms become arbitrarily close in modulus
converges (by the completeness of ℝ, applied to real and imaginary parts). -/
theorem exists_CLim {s : Nat → C}
    (hs : ∀ ε : R, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → cabs (s m - s n) < ε) :
    ∃ L, CLim s L := by
  have hre : R.IsCauchySeq (fun n => (s n).re) := fun ε hε => by
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    have := abs_re_le_cabs (s m - s n)
    have e : (s m - s n).re = (s m).re - (s n).re := by show (s m).re + -(s n).re = _; grind
    rw [e] at this; have := hN m n hm hn; grind
  have him : R.IsCauchySeq (fun n => (s n).im) := fun ε hε => by
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    have := abs_im_le_cabs (s m - s n)
    have e : (s m - s n).im = (s m).im - (s n).im := by show (s m).im + -(s n).im = _; grind
    rw [e] at this; have := hN m n hm hn; grind
  obtain ⟨a, ha⟩ := R.cauchy_complete hre
  obtain ⟨b, hb⟩ := R.cauchy_complete him
  refine ⟨⟨a, b⟩, fun ε hε => ?_⟩
  obtain ⟨N₁, h₁⟩ := ha (ε / 2) (by grind)
  obtain ⟨N₂, h₂⟩ := hb (ε / 2) (by grind)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have k1 := h₁ n (by omega)
  have k2 := h₂ n (by omega)
  have := cabs_le_nrm (s n - ⟨a, b⟩)
  have e1 : (s n - ⟨a, b⟩).re = (s n).re - a := by show (s n).re + -a = _; grind
  have e2 : (s n - ⟨a, b⟩).im = (s n).im - b := by show (s n).im + -b = _; grind
  unfold nrm at this; rw [e1, e2] at this
  grind

end Lattice

end Foundations.Langlands.Modular
