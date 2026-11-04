import Foundations.Langlands.Modular.LatticeSum

/-!
# Eisenstein series and their transformation law

For an integer `k ≥ 3` and `τ ∈ ℍ`, the **Eisenstein series** of weight `k` is

  `G_k(τ) = Σ'_{(m, n) ∈ ℤ²} (mτ + n)^{−k}`,

the prime meaning that `(0, 0)` is omitted. We define it as the limit of the partial sums over
the squares `Q_N = {|m|, |n| ≤ N}` (`partialG`, `G`), which exists because the double series
converges absolutely (`LatticeSum.abs_lattice_sum_converges`): the partial sums form a Cauchy
sequence (`exists_eisenstein_limit`).

We then prove the **weight-`k` transformation law** (`G_isModular`):

* `G_k(τ + 1) = G_k(τ)` (`G_T`). Here the substitution `(m, n) ↦ (m, m + n)` does **not**
  preserve the squares: it maps `Q_N` onto a parallelogram lying between `Q_{N/2}` and
  `Q_{2N}`. So a genuine **rearrangement** of the double series is needed, and it is justified
  by absolute convergence: by the comparison lemma `Lattice.cabs_sq_ite_sub_le`, the sum over
  the parallelogram differs from the sum over `Q_{N/2}` by at most a tail
  `Σ_{Q_{2N}} |·| − Σ_{Q_{N/2}} |·|` of the absolutely convergent series, which tends to zero
  (`sq_shear`, `partialG_T_close`).
* `G_k(−1/τ) = τ^k G_k(τ)` (`G_S`). From `m(−1/τ) + n = (nτ − m)/τ` each term is
  `τ^k (nτ − m)^{−k}`, and `(m, n) ↦ (n, −m)` is a rotation of the lattice which maps every
  square `Q_N` onto itself; so already the partial sums transform correctly (`partialG_S`).

Since `S` and `T` generate SL₂(ℤ) (`isModular_of_S_T`), `G_k` satisfies the weight-`k` law
`G_k(γτ) = (cτ + d)^k G_k(τ)` for all `γ`. (For odd `k` this forces `G_k = 0`, by
`eq_zero_of_odd`; the interesting weights are the even `k ≥ 4`.) Holomorphy, and the behaviour
at the cusp, are not formalised in this library, so we say that `G_k` *satisfies the weight-`k`
law*, not that it is a modular form. As a first corollary, `G_k(i) = 0` whenever
`k ≡ 2 (mod 4)` (`G_i_eq_zero`), since `i` is fixed by `S` and `i^k = −1`.

## History

Eisenstein (1847) introduced such double series in his "Genaue Untersuchung der unendlichen
Doppelproducte, aus welchen die elliptischen Functionen als Quotienten zusammengesetzt sind",
paying careful attention to the order of summation, precisely because for `k ≤ 2` the double
series is only conditionally convergent and its value depends on that order. Weierstrass then
made `G_4` and `G_6` the coefficients of his elliptic function `℘` with periods `1, τ`:
`℘'² = 4℘³ − g₂℘ − g₃` with `g₂ = 60 G_4` and `g₃ = 140 G_6` (not formalised here).

In the Langlands programme Eisenstein series are where the whole story began: Langlands' own
starting point (*On the Functional Equations Satisfied by Eisenstein Series*, 1960s) was the
analytic continuation of Eisenstein series for general reductive groups, which gives the
continuous spectrum of `L²(Γ\G)` and, via their constant terms, the first automorphic
`L`-functions. None of that theory is formalised here.
-/

namespace Foundations.Langlands.Modular

open Foundations.Numbers Foundations.Numbers.C Lean.Grind SL2Z

attribute [local instance] Semiring.natCast Ring.intCast

namespace Lattice

/-! ## Definition and convergence -/

/-- **Partial Eisenstein sum** `Σ_{(m,n) ∈ Q_N} (mτ + n)^{−k}` over the square `Q_N` (for `k ≥ 1` the
term at `(0, 0)` is `0`, by the convention `0⁻¹ = 0`). -/
noncomputable def partialG (k : Nat) (z : C) (N : Nat) : C := sq N (eterm k z)

/-- The partial sums `Σ_{Q_N} |mτ + n|^{−k}` of the absolute series. -/
noncomputable def absPartial (k : Nat) (z : C) (N : Nat) : R :=
  sq N (fun m n => cabs (eterm k z m n))

/-- `|P_L − P_M| ≤ A_L − A_M` for `M ≤ L`: partial sums move by at most the absolute tail. -/
theorem cabs_partialG_sub_le (k : Nat) (z : C) {M L : Nat} (h : M ≤ L) :
    cabs (partialG k z L - partialG k z M) ≤ absPartial k z L - absPartial k z M := by
  have := cabs_sq_ite_sub_le h (fun _ _ => True) (fun _ _ _ => trivial) (eterm k z)
  rw [sq_congr (g' := eterm k z) fun m n _ _ _ _ => ite_t trivial _ _] at this
  exact this

/-- The absolute partial sums are Cauchy, for `k ≥ 3`. -/
theorem absPartial_cauchy {k : Nat} (hk : 3 ≤ k) (p : UHP) : R.IsCauchySeq (absPartial k p.z) := by
  obtain ⟨L, hL⟩ := abs_lattice_sum_converges hk p
  exact hL.isCauchySeq

/-- **Convergence of the Eisenstein series.** For `k ≥ 3` and `τ ∈ ℍ` the partial sums over
squares `Σ_{Q_N} (mτ + n)^{−k}` converge. -/
theorem exists_eisenstein_limit {k : Nat} (hk : 3 ≤ k) (p : UHP) :
    ∃ L, CLim (partialG k p.z) L := by
  apply exists_CLim; intro ε hε
  obtain ⟨N, hN⟩ := absPartial_cauchy hk p ε hε
  refine ⟨N, fun m n hm hn => ?_⟩
  rcases Nat.le_total m n with h | h
  · have k1 := cabs_partialG_sub_le k p.z h
    have k2 := (OF.abs_lt.1 (hN n m hn hm)).2
    rw [cabs_sub_comm]; grind
  · have k1 := cabs_partialG_sub_le k p.z h
    have k2 := (OF.abs_lt.1 (hN m n hm hn)).2
    grind

/-- **The Eisenstein series** `G_k(τ) = Σ'_{(m,n)} (mτ + n)^{−k}`, summed over growing squares.
(Defined as `0` if the limit does not exist, which by `exists_eisenstein_limit` does not happen
for `k ≥ 3`.) -/
noncomputable def G (k : Nat) (p : UHP) : C :=
  open Classical in if h : ∃ L, CLim (partialG k p.z) L then Classical.choose h else 0

/-- **The square partial sums converge to `G_k(τ)`**, for `k ≥ 3`. -/
theorem tendsto_G {k : Nat} (hk : 3 ≤ k) (p : UHP) : CLim (partialG k p.z) (G k p) := by
  have h := exists_eisenstein_limit hk p
  unfold G; split
  · exact Classical.choose_spec ‹_›
  · contradiction

/-! ## Translation `τ ↦ τ + 1`: a rearrangement -/

/-- **Shearing a square.** The sum of `g(m, m + n)` over `Q_N` is the sum of `g` over the
parallelogram `{|m| ≤ N, |n − m| ≤ N}`, viewed inside the square `Q_{2N}`. -/
theorem sq_shear {α : Type} [Field α] (N : Nat) (g : Int → Int → α) :
    sq N (fun m n => g m (m + n)) =
      sq (2 * N) (fun m n => if (-(N : Int) ≤ m ∧ m < -(N : Int) + ((2 * N + 1 : Nat) : Int)) ∧
        (m - N ≤ n ∧ n < m - N + ((2 * N + 1 : Nat) : Int)) then g m n else 0) := by
  unfold sq
  -- inner sums: shift, then pad to `[−2N, 2N]`
  have inner : ∀ m, -(N : Int) ≤ m → m < -(N : Int) + ((2 * N + 1 : Nat) : Int) →
      isum (-(N : Int)) (2 * N + 1) (fun n => g m (m + n)) =
      isum (-((2 * N : Nat) : Int)) (2 * (2 * N) + 1)
        (fun n => if m - N ≤ n ∧ n < m - N + ((2 * N + 1 : Nat) : Int) then g m n else 0) := by
    intro m h1 h2
    rw [isum_embed (a := m - N) (b := -((2 * N : Nat) : Int)) (len := 2 * N + 1)
      (len' := 2 * (2 * N) + 1) (by omega) (by omega)]
    unfold isum; apply gsum_congr; intro i _; dsimp only; congr 1; omega
  rw [isum_congr (h' := fun m => isum (-((2 * N : Nat) : Int)) (2 * (2 * N) + 1)
      (fun n => if m - N ≤ n ∧ n < m - N + ((2 * N + 1 : Nat) : Int) then g m n else 0))
      fun m h1 h2 => inner m h1 h2]
  rw [← isum_embed (b := -((2 * N : Nat) : Int)) (len' := 2 * (2 * N) + 1) (by omega) (by omega)]
  apply isum_congr; intro m _ _
  dsimp only
  by_cases hm : -(N : Int) ≤ m ∧ m < -(N : Int) + ((2 * N + 1 : Nat) : Int)
  · rw [ite_t hm]; apply isum_congr; intro n _ _
    by_cases hn : m - N ≤ n ∧ n < m - N + ((2 * N + 1 : Nat) : Int)
    · rw [ite_t hn, ite_t ⟨hm, hn⟩]
    · rw [ite_f hn, ite_f (fun h => hn h.2)]
  · rw [ite_f hm]; refine Eq.trans (isum_zero _ _).symm (isum_congr fun n _ _ => ?_)
    rw [ite_f (fun h => hm h.1)]

/-- `m(τ + 1) + n = mτ + (m + n)`, so the terms at `τ + 1` are a shear of those at `τ`. -/
theorem eterm_add_one (k : Nat) (z : C) (m n : Int) :
    eterm k (z + ((1 : Int) : C)) m n = eterm k z m (m + n) := by
  unfold eterm lin
  rw [Ring.intCast_add, Ring.intCast_one]; congr 2; grind

/-- **The rearrangement estimate.** `|P_N(τ + 1) − P_{⌊N/2⌋}(τ)| ≤ A_{2N}(τ) − A_{⌊N/2⌋}(τ)`. -/
theorem partialG_T_close (k : Nat) (z : C) (N : Nat) :
    cabs (partialG k (z + ((1 : Int) : C)) N - partialG k z (N / 2)) ≤
      absPartial k z (2 * N) - absPartial k z (N / 2) := by
  unfold partialG
  rw [show eterm k (z + ((1 : Int) : C)) = fun m n => eterm k z m (m + n) from
    funext fun m => funext fun n => eterm_add_one k z m n, sq_shear]
  exact cabs_sq_ite_sub_le (by omega) _ (fun m n h => by unfold InSq at h; omega) _

/-- Passing to the subsequence `N ↦ ⌊N/2⌋` preserves limits. -/
theorem CLim.comp_half {s : Nat → C} {L : C} (h : CLim s L) : CLim (fun N => s (N / 2)) L :=
  fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨2 * N, fun n hn => hN (n / 2) (by omega)⟩

/-- **Periodicity.** `G_k(τ + 1) = G_k(τ)`, for `k ≥ 3`. -/
theorem G_T {k : Nat} (hk : 3 ≤ k) (p : UHP) : G k (T • p) = G k p := by
  have hz : (T • p).z = p.z + ((1 : Int) : C) := by rw [smul_z, ← Tn_one, mob_Tn]
  have h1 := tendsto_G hk (T • p)
  rw [hz] at h1
  have h2 : CLim (partialG k (p.z + ((1 : Int) : C))) (G k p) := by
    refine CLim.of_cabs_sub_le (CLim.comp_half (tendsto_G hk p)) (fun ε hε => ?_)
      (partialG_T_close k p.z)
    obtain ⟨N, hN⟩ := absPartial_cauchy hk p ε hε
    refine ⟨2 * N, fun n hn => ?_⟩
    have := (OF.abs_lt.1 (hN (2 * n) (n / 2) (by omega) (by omega))).2
    exact this
  exact h1.unique h2

/-! ## Inversion `τ ↦ −1/τ`: a rotation of the squares -/

/-- `(ab)⁻¹ = a⁻¹ b⁻¹` in ℂ. -/
theorem C_mul_inv (a b : C) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  by_cases ha : a = 0
  · rw [ha, C.zero_mul, C.inv_zero, C.zero_mul]
  by_cases hb : b = 0
  · rw [hb, C.mul_zero, C.inv_zero, C.mul_zero]
  have hab : a * b ≠ 0 := fun h => by
    have := congrArg (· * (a⁻¹ * b⁻¹)) h
    simp only [C.zero_mul] at this
    have e1 := C.mul_inv_cancel ha
    have e2 := C.mul_inv_cancel hb
    have : a * b * (a⁻¹ * b⁻¹) = 1 := by grind
    grind
  have e1 := C.mul_inv_cancel ha
  have e2 := C.mul_inv_cancel hb
  have e3 := C.mul_inv_cancel hab
  grind

/-- `((τ⁻¹)^k)⁻¹ = τ^k` for `τ ≠ 0`. -/
theorem inv_pow_inv {z : C} (hz : z ≠ 0) (k : Nat) : ((z⁻¹) ^ k)⁻¹ = z ^ k := by
  have e : z⁻¹ ^ k * z ^ k = 1 := by
    rw [← C.mul_pow, show z⁻¹ * z = 1 by rw [C.mul_comm]; exact C.mul_inv_cancel hz, one_pow]
  have hne : z⁻¹ ^ k ≠ 0 := fun h => by rw [h, C.zero_mul] at e; exact C.zero_ne_one e
  have := C.mul_inv_cancel hne
  grind

/-- `m(−1/τ) + n = (nτ − m)/τ`, so `(m(−1/τ) + n)^{−k} = τ^k (nτ − m)^{−k}`. -/
theorem eterm_S (k : Nat) {z : C} (hz : z ≠ 0) (m n : Int) :
    eterm k (-1 / z) m n = z ^ k * eterm k z n (-m) := by
  unfold eterm
  have e : lin (-1 / z) m n = lin z n (-m) * z⁻¹ := by
    unfold lin; rw [Ring.intCast_neg]
    have := C.mul_inv_cancel hz
    show (m : C) * (-1 * z⁻¹) + (n : C) = _
    grind
  rw [e, C.mul_pow, C_mul_inv, inv_pow_inv hz]; grind

/-- **The partial sums transform exactly.** `P_N(−1/τ) = τ^k P_N(τ)`, since the rotation
`(m, n) ↦ (n, −m)` maps the square `Q_N` onto itself. -/
theorem partialG_S (k : Nat) {z : C} (hz : z ≠ 0) (N : Nat) :
    partialG k (-1 / z) N = z ^ k * partialG k z N := by
  unfold partialG
  rw [show eterm k (-1 / z) = fun m n => z ^ k * eterm k z n (-m) from
    funext fun m => funext fun n => eterm_S k hz m n, sq_mul_left]
  congr 1
  rw [sq_swap N (fun n m => eterm k z n (-m)), sq_neg_snd]

/-- **Inversion.** `G_k(−1/τ) = τ^k G_k(τ)`, for `k ≥ 3`. -/
theorem G_S {k : Nat} (hk : 3 ≤ k) (p : UHP) : G k (S • p) = p.z ^ k * G k p := by
  have hz : p.z ≠ 0 := fun h => by have := p.pos; rw [h, C.zero_im] at this; grind
  have h1 := tendsto_G hk (S • p)
  rw [smul_z, mob_S] at h1
  have h2 : CLim (partialG k (-1 / p.z)) (p.z ^ k * G k p) := by
    rw [show partialG k (-1 / p.z) = fun N => p.z ^ k * partialG k p.z N from
      funext (partialG_S k hz)]
    exact (tendsto_G hk p).const_mul _
  exact h1.unique h2

/-- **The Eisenstein series satisfies the weight-k transformation law.** For `k ≥ 3`,
`G_k(γτ) = (cτ + d)^k G_k(τ)` for all `γ ∈ SL₂(ℤ)` and `τ ∈ ℍ`. (Holomorphy is not formalised,
so this is the transformation law only; and for odd `k` it forces `G_k = 0`.) -/
theorem G_isModular {k : Nat} (hk : 3 ≤ k) : IsModular k (G k) :=
  isModular_of_S_T (G_S hk) (G_T hk)

/-! ## A corollary: vanishing at `i` in weights `k ≡ 2 (mod 4)` -/

/-- `S` fixes the point `i`: `−1/i = i`. -/
theorem S_smul_i : S • iMul 1 (by grind) = iMul 1 (by grind) := by
  apply UHP.ext
  rw [smul_z, mob_S]
  apply C.ext
  · show ((-1 : C) * (iMul 1 _).z⁻¹).re = 0
    simp only [C.mul_re, C.inv_re, C.inv_im, C.neg_re, C.neg_im, C.one_re, C.one_im, iMul]
    grind
  · show ((-1 : C) * (iMul 1 _).z⁻¹).im = 1
    simp only [C.mul_im, C.inv_re, C.inv_im, C.neg_re, C.neg_im, C.one_re, C.one_im, iMul,
      C.normSq]
    grind

/-- `i^{4j+2} = −1`. -/
theorem I_pow (j : Nat) : (iMul 1 (by grind)).z ^ (4 * j + 2) = -1 := by
  have hI : (iMul 1 (by grind)).z = C.I := rfl
  rw [hI]
  induction j with
  | zero => show 1 * C.I * C.I = -1; have := C.I_sq; grind
  | succ j ih =>
    rw [show 4 * (j + 1) + 2 = 4 * j + 2 + 1 + 1 + 1 + 1 by omega]
    show C.I ^ (4 * j + 2) * C.I * C.I * C.I * C.I = -1
    rw [ih]; have := C.I_sq; grind

/-- **`G_k(i) = 0` for `k ≡ 2 (mod 4)`.** The law under `S` at its fixed point `i` reads
`G_k(i) = i^k G_k(i) = −G_k(i)`. (So `G_6`, `G_10`, … vanish at `i`.) -/
theorem G_i_eq_zero (j : Nat) (hj : 1 ≤ j) : G (4 * j + 2) (iMul 1 (by grind)) = 0 := by
  have h := G_S (k := 4 * j + 2) (by omega) (iMul 1 (by grind))
  rw [S_smul_i, I_pow] at h
  have h1 := congrArg C.re h
  have h2 := congrArg C.im h
  simp only [C.mul_re, C.mul_im, C.neg_re, C.neg_im, C.one_re, C.one_im] at h1 h2
  apply C.ext
  · show (G _ _).re = 0; grind
  · show (G _ _).im = 0; grind

end Lattice

end Foundations.Langlands.Modular
