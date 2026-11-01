import Foundations.NumberTheory.Mertens
import Foundations.NumberTheory.DirichletCharacters

/-!
# Dirichlet `L`-series at `s = 1`

For a Dirichlet character `χ` modulo `q`, Dirichlet's `L`-series is `L(s, χ) = Σ χ(n)/nˢ`. For the
proof of his theorem only the point `s = 1` matters, and there the series converges — though not
absolutely — whenever `χ` is not the principal character. The reason is cancellation: over each
period the values of `χ` sum to `0`, so the partial sums `Σ_{n<N} χ(n)` stay bounded (by `q`),
and **Abel's summation by parts** (1826) converts bounded partial sums and decreasing weights
`b(n) → 0` into convergence of `Σ χ(n) b(n)`, with an explicit tail bound:

  `|Σ_{M ≤ n < K} χ(n) b(n)| ≤ 2 q b(M)`.

Applied to `b(n) = 1/n` this gives the number `L(1, χ)` together with
`|L(1, χ) − Σ_{n<M} χ(n)/n| ≤ 2q/M`; applied to `b(n) = log n / n` (decreasing from `n = 4` on,
because `e ≤ 4`) it shows that the partial sums of `Σ χ(n) log n / n` — the series of `−L'(1, χ)` —
stay bounded. These two facts feed the key identity of the next file.

Complex sequences converge when their real and imaginary parts do (Part II); completeness of the
reals provides the limit.
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Numbers Foundations.Numbers.Arith Lean.Grind
open Foundations.Numbers.C (ofReal nrm CTendsto)

/-! ## Embedding the reals in `ℂ` -/

/-- `ofReal (x + y) = ofReal x + ofReal y`. -/
theorem ofReal_add' (x y : R) : ofReal (x + y) = ofReal x + ofReal y := C.ext rfl (by
  show (0 : R) = 0 + 0; grind)

/-- `ofReal (x y) = ofReal x · ofReal y`. -/
theorem ofReal_mul' (x y : R) : ofReal (x * y) = ofReal x * ofReal y := C.ext
  (by show x * y = x * y - 0 * 0; grind) (by show (0 : R) = x * 0 + 0 * y; grind)

/-- `ofReal (x − y) = ofReal x − ofReal y`. -/
theorem ofReal_sub' (x y : R) : ofReal (x - y) = ofReal x - ofReal y := C.ext
  (by show x - y = x + -y; grind) (by show (0 : R) = 0 + -0; grind)

/-- `ofReal 0 = 0`. -/
theorem ofReal_zero' : ofReal 0 = 0 := rfl

/-- `ofReal` commutes with finite sums. -/
theorem ofReal_gsum (f : Nat → R) (n : Nat) : ofReal (gsum f n) = gsum (fun k => ofReal (f k)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum_succ, gsum_succ, ofReal_add', ih]

/-- The real part of a finite sum. -/
theorem gsum_re' (f : Nat → C) (n : Nat) : (gsum f n).re = gsum (fun k => (f k).re) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum_succ, gsum_succ, C.add_re, ih]

/-- `|x| = |ofReal x|`. -/
theorem cabs_ofReal' (x : R) : C.cabs (ofReal x) = OF.abs x := by
  rcases OF.abs_cases x with ⟨h, e⟩ | ⟨h, e⟩
  · rw [e]; exact C.cabs_ofReal h
  · rw [e, show ofReal x = -ofReal (-x) from C.ext (by show x = -(-x); grind)
      (by show (0 : R) = -(0 : R); grind), C.cabs_neg]
    exact C.cabs_ofReal (by grind)

/-- **Triangle inequality for finite sums.** -/
theorem cabs_gsum_le (f : Nat → C) (n : Nat) : C.cabs (gsum f n) ≤ gsum (fun k => C.cabs (f k)) n := by
  induction n with
  | zero => show C.cabs 0 ≤ 0; rw [C.cabs_zero]; grind
  | succ n ih => rw [gsum_succ, gsum_succ]; have := C.cabs_add (gsum f n) (f n); grind

/-- `|z · x| = |z| x` for real `x ≥ 0`. -/
theorem cabs_mul_ofReal {z : C} {x : R} (hx : 0 ≤ x) : C.cabs (z * ofReal x) = C.cabs z * x := by
  rw [C.cabs_mul, C.cabs_ofReal hx]

/-! ## Bounded partial sums -/

/-- For a `q`-periodic sequence, the sum over any window of length `q` is the same. -/
theorem gsum_window {a : Nat → C} {q : Nat} (hper : ∀ n, a (n + q) = a n) :
    ∀ N, gsum (fun k => a (N + k)) q = gsum a q
  | 0 => by simp only [Nat.zero_add]
  | N + 1 => by
    rw [← gsum_window hper N]
    cases q with
    | zero => rfl
    | succ q =>
      rw [gsum_succ, gsum_succ' (fun k => a (N + k))]
      have e1 : a (N + 1 + q) = a (N + 0) := by
        rw [show N + 1 + q = N + (q + 1) by omega, hper, Nat.add_zero]
      have e2 : gsum (fun k => a (N + 1 + k)) q = gsum (fun k => a (N + (k + 1))) q :=
        gsum_congr fun k _ => by rw [show N + 1 + k = N + (k + 1) by omega]
      rw [e1, e2]; grind

/-- **Bounded partial sums.** If `a` is `q`-periodic with `|a(n)| ≤ 1` and `Σ_{n<q} a(n) = 0`,
then `|Σ_{n<N} a(n)| ≤ q` for every `N`. -/
theorem cabs_gsum_periodic_le {a : Nat → C} {q : Nat} (hq : 0 < q) (hper : ∀ n, a (n + q) = a n)
    (hbd : ∀ n, C.cabs (a n) ≤ 1) (hsum : gsum a q = 0) : ∀ N, C.cabs (gsum a N) ≤ (q : R) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    by_cases hN : N < q
    · have h1 := cabs_gsum_le a N
      have h2 := gsum_le_gsum (n := N) (f := fun k => C.cabs (a k)) (g := fun _ => (1 : R))
        (fun k _ => hbd k)
      rw [gsum_const_R] at h2
      have := natCast_le' (Std.le_of_lt hN); grind
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + q := ⟨N - q, by omega⟩
      rw [gsum_split, gsum_window hper, hsum, show gsum a M + 0 = gsum a M by grind]
      exact ih M (by omega)

/-! ## Abel summation -/

/-- **Abel's summation by parts.** If `|Σ_{n<N} a(n)| ≤ B` for all `N`, and `b ≥ 0` is
non-increasing from `M` on, then `|Σ_{M ≤ n < K} a(n) b(n)| ≤ 2 B b(M)`. -/
theorem abel_bound {a : Nat → C} {B : R} (hB : ∀ N, C.cabs (gsum a N) ≤ B) {b : Nat → R} {M : Nat}
    (hmono : ∀ n, M ≤ n → b (n + 1) ≤ b n) (hpos : ∀ n, M ≤ n → 0 ≤ b n) :
    ∀ K, M ≤ K → C.cabs (gsum (fun n => a n * ofReal (b n)) K - gsum (fun n => a n * ofReal (b n)) M)
      ≤ 2 * B * b M := by
  let S := fun K => gsum (fun n => a n * ofReal (b n)) K
  let A := fun K => gsum a K
  -- `E(K) = Σ_{M ≤ n < K} a(n) b(n) − A(K) b(K)` changes by `A(K+1)(b(K) − b(K+1))`.
  have inv : ∀ j, C.cabs (S (M + j) - S M - A (M + j) * ofReal (b (M + j))) ≤
      B * b M + B * (b M - b (M + j)) := by
    intro j
    induction j with
    | zero =>
      rw [Nat.add_zero, show S M - S M - A M * ofReal (b M) = -(A M * ofReal (b M)) by grind,
        C.cabs_neg, cabs_mul_ofReal (hpos M (Nat.le_refl M))]
      have := OrderedRing.mul_le_mul_of_nonneg_right (hB M) (hpos M (Nat.le_refl M))
      grind
    | succ j ih =>
      have hK : M ≤ M + j := Nat.le_add_right M j
      rw [← Nat.add_assoc]
      have e : S (M + j + 1) - S M - A (M + j + 1) * ofReal (b (M + j + 1)) =
          (S (M + j) - S M - A (M + j) * ofReal (b (M + j))) +
            A (M + j + 1) * ofReal (b (M + j) - b (M + j + 1)) := by
        simp only [S, A]
        rw [gsum_succ (fun n => a n * ofReal (b n)), gsum_succ a, ofReal_sub']; grind
      rw [e]
      have h1 := C.cabs_add (S (M + j) - S M - A (M + j) * ofReal (b (M + j)))
        (A (M + j + 1) * ofReal (b (M + j) - b (M + j + 1)))
      have hd : 0 ≤ b (M + j) - b (M + j + 1) := by have := hmono (M + j) hK; grind
      rw [cabs_mul_ofReal hd] at h1
      have := OrderedRing.mul_le_mul_of_nonneg_right (hB (M + j + 1)) hd
      grind
  intro K hK
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
  have h1 := inv j
  have h2 := C.cabs_add (S (M + j) - S M - A (M + j) * ofReal (b (M + j)))
    (A (M + j) * ofReal (b (M + j)))
  rw [show S (M + j) - S M - A (M + j) * ofReal (b (M + j)) + A (M + j) * ofReal (b (M + j)) =
    S (M + j) - S M by grind, cabs_mul_ofReal (hpos (M + j) hK)] at h2
  have := OrderedRing.mul_le_mul_of_nonneg_right (hB (M + j)) (hpos (M + j) hK)
  show C.cabs (S (M + j) - S M) ≤ _
  grind

/-! ## Limits of complex sequences -/

/-- If `x ≤ y + ε` for every `ε > 0`, then `x ≤ y`. -/
theorem le_of_forall_pos_le_add' {x y : R} (h : ∀ ε : R, 0 < ε → x ≤ y + ε) : x ≤ y := by
  apply Classical.byContradiction; intro hxy
  have := h ((x - y) / 2) (by
    have : (0 : R) < x - y := by grind
    have := OF.div_pos this (show (0 : R) < 2 by grind); exact this)
  grind

/-- For every `c` and `ε > 0` there is `M ≥ 1` with `c / M < ε`. -/
theorem exists_div_lt {c ε : R} (hε : 0 < ε) : ∃ M : Nat, 1 ≤ M ∧ c / (M : R) < ε := by
  obtain ⟨n, hn⟩ := R.archimedean (OF.abs c / ε)
  refine ⟨n + 1, by omega, ?_⟩
  have hpos : (0 : R) < ((n + 1 : Nat) : R) := natCast_pos' (by omega)
  have h1 : OF.abs c / ε < ((n + 1 : Nat) : R) := by
    have := natCast_le' (show n ≤ n + 1 by omega); grind
  have h2 : OF.abs c < ((n + 1 : Nat) : R) * ε := by
    have := OrderedRing.mul_lt_mul_of_pos_right h1 hε
    rw [show OF.abs c / ε * ε = OF.abs c by have : ε ≠ 0 := by grind
                                            grind] at this
    exact this
  have h3 : OF.abs c / ((n + 1 : Nat) : R) < ε := by
    apply Classical.byContradiction; intro h
    have := OrderedRing.mul_le_mul_of_nonneg_right (show ε ≤ OF.abs c / ((n + 1 : Nat) : R) by grind)
      (Std.le_of_lt hpos)
    rw [show OF.abs c / ((n + 1 : Nat) : R) * ((n + 1 : Nat) : R) = OF.abs c by
      have : ((n + 1 : Nat) : R) ≠ 0 := by grind
      grind] at this
    grind
  have := div_le_div_of_le (OF.le_abs c).1 hpos
  grind

/-- **Convergence with a rate.** If `|s_K − s_M| ≤ c / M` for all `1 ≤ M ≤ K`, then `s`
converges to some `L` with `|L − s_M| ≤ c / M`. -/
theorem exists_lim_of_cauchy_rate {s : Nat → C} {c : R}
    (h : ∀ M K, 1 ≤ M → M ≤ K → C.cabs (s K - s M) ≤ c / (M : R)) :
    ∃ L, CTendsto s L ∧ ∀ M, 1 ≤ M → C.cabs (L - s M) ≤ c / (M : R) := by
  have hc : ∀ M m n, 1 ≤ M → M ≤ m → M ≤ n → C.cabs (s m - s n) ≤ 2 * (c / (M : R)) := by
    intro M m n hM hm hn
    have h1 := h M m hM hm
    have h2 := h M n hM hn
    have := C.cabs_add (s m - s M) (s M - s n)
    rw [show s m - s M + (s M - s n) = s m - s n by grind, C.cabs_sub_comm (s M)] at this
    grind
  have cauchy : ∀ (f : C → R), (∀ z, OF.abs (f z) ≤ C.cabs z) → (∀ z w, f (z - w) = f z - f w) →
      R.IsCauchySeq (fun n => f (s n)) := by
    intro f hf hfs ε hε
    obtain ⟨M, hM1, hM⟩ := exists_div_lt (c := 2 * c) hε
    refine ⟨M, fun m n hm hn => ?_⟩
    have := hf (s m - s n); rw [hfs] at this
    have := hc M m n hM1 hm hn
    have : 2 * (c / (M : R)) = 2 * c / (M : R) := by grind
    grind
  obtain ⟨Lr, hLr⟩ := R.cauchy_complete (cauchy C.re C.abs_re_le_cabs (fun z w => rfl))
  obtain ⟨Li, hLi⟩ := R.cauchy_complete (cauchy C.im C.abs_im_le_cabs (fun z w => rfl))
  refine ⟨⟨Lr, Li⟩, ⟨hLr, hLi⟩, fun M hM => ?_⟩
  apply le_of_forall_pos_le_add'
  intro ε hε
  obtain ⟨K1, hK1⟩ := hLr (ε / 2) (by have := OF.div_pos hε (show (0 : R) < 2 by grind); exact this)
  obtain ⟨K2, hK2⟩ := hLi (ε / 2) (by have := OF.div_pos hε (show (0 : R) < 2 by grind); exact this)
  let K := M + K1 + K2
  have h1 := hK1 K (by omega)
  have h2 := hK2 K (by omega)
  have h3 := h M K hM (by omega)
  have h4 := C.cabs_add (⟨Lr, Li⟩ - s K) (s K - s M)
  rw [show (⟨Lr, Li⟩ : C) - s K + (s K - s M) = ⟨Lr, Li⟩ - s M by grind] at h4
  have h5 := C.cabs_le_nrm (⟨Lr, Li⟩ - s K)
  have h6 : nrm (⟨Lr, Li⟩ - s K) = OF.abs ((s K).re - Lr) + OF.abs ((s K).im - Li) := by
    unfold nrm
    rw [OF.abs_sub_comm ((s K).re), OF.abs_sub_comm ((s K).im)]; rfl
  grind

/-! ## `L(1, χ)` -/

/-- The partial sums `Σ_{n<N} a(n)/n` of the `L`-series at `s = 1`. -/
noncomputable def lpart (a : Nat → C) (N : Nat) : C := gsum (fun n => a n * ofReal (1 / (n : R))) N

/-- `1/n` is non-increasing for `n ≥ 1`. -/
theorem one_div_succ_le {n : Nat} (hn : 1 ≤ n) : 1 / ((n + 1 : Nat) : R) ≤ 1 / (n : R) := by
  have h1 := natCast_pos' (show 0 < n by omega)
  have h2 := natCast_pos' (show 0 < n + 1 by omega)
  apply le_div_of_mul_le h1
  rw [show 1 / ((n + 1 : Nat) : R) * (n : R) = (n : R) / ((n + 1 : Nat) : R) by grind]
  apply div_le_of_le_mul h2
  have := natCast_le' (show n ≤ n + 1 by omega); grind

/-- `1/n ≥ 0`. -/
theorem one_div_nonneg' (n : Nat) : 0 ≤ 1 / (n : R) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; show (0 : R) ≤ 1 / ((0 : Nat) : R); rw [show ((0 : Nat) : R) = 0 by grind]
    rw [Field.div_eq_mul_inv, Field.inv_zero]; grind
  · exact Std.le_of_lt (OF.div_pos (by grind) (natCast_pos' h))

/-- **Convergence of `Σ a(n)/n`** with tail bound `|L − Σ_{n<M} a(n)/n| ≤ 2B/M`, when the partial
sums of `a` are bounded by `B`. -/
theorem exists_L {a : Nat → C} {B : R} (hB : ∀ N, C.cabs (gsum a N) ≤ B) :
    ∃ L, CTendsto (lpart a) L ∧ ∀ M, 1 ≤ M → C.cabs (L - lpart a M) ≤ 2 * B / (M : R) := by
  apply exists_lim_of_cauchy_rate
  intro M K hM hMK
  have := abel_bound hB (b := fun n => 1 / (n : R)) (M := M) (fun n hn => one_div_succ_le (by omega))
    (fun n _ => one_div_nonneg' n) K hMK
  unfold lpart
  rw [show 2 * B / (M : R) = 2 * B * (1 / (M : R)) by grind]; exact this

section Dirichlet

variable {q : Nat} [NeZero q]

/-- **Partial sums of a non-principal character are bounded by `q`.** -/
theorem cabs_gsum_dchar_le (χ : Character (ZModUnits q)) (h : χ ≠ Character.one) (N : Nat) :
    C.cabs (gsum (dchar χ) N) ≤ (q : R) :=
  cabs_gsum_periodic_le (Nat.pos_of_ne_zero (NeZero.ne q)) (dchar_add_period χ) (cabs_dchar_le χ) (gsum_dchar_period χ h) N

open Classical in
/-- **`L(1, χ)`**, the sum of the series `Σ χ(n)/n` (defined as `0` if the series diverges, which
happens only for the principal character). -/
noncomputable def Lone (χ : Character (ZModUnits q)) : C :=
  if h : ∃ L, CTendsto (lpart (dchar χ)) L then Classical.choose h else 0

/-- For non-principal `χ`, `Σ χ(n)/n` converges to `L(1, χ)`, with
`|L(1, χ) − Σ_{n<M} χ(n)/n| ≤ 2q/M` for `M ≥ 1`. -/
theorem Lone_spec (χ : Character (ZModUnits q)) (h : χ ≠ Character.one) :
    CTendsto (lpart (dchar χ)) (Lone χ) ∧
      ∀ M, 1 ≤ M → C.cabs (Lone χ - lpart (dchar χ) M) ≤ 2 * (q : R) / (M : R) := by
  obtain ⟨L, hL, ht⟩ := exists_L (cabs_gsum_dchar_le χ h)
  have hex : ∃ L, CTendsto (lpart (dchar χ)) L := ⟨L, hL⟩
  have e : Lone χ = L := by
    unfold Lone; rw [dite_eq_left hex]
    exact C.CTendsto.unique (Classical.choose_spec hex) hL
  rw [e]; exact ⟨hL, ht⟩

end Dirichlet

/-! ## The series `Σ χ(n) log n / n` -/

/-- Powers of a non-negative real are non-negative. -/
theorem pow_nonneg' {x : R} (hx : 0 ≤ x) : ∀ n : Nat, 0 ≤ x ^ n
  | 0 => by show (0 : R) ≤ 1; grind
  | n + 1 => OrderedRing.mul_nonneg (pow_nonneg' hx n) hx

/-- `e^{1/2} ≤ 2`, comparing the exponential series with the geometric series `Σ 2⁻ⁿ`. -/
theorem exp_half_le_two : R.exp (1 / 2) ≤ 2 := by
  have hr : (0 : R) ≤ 1 / 2 := by grind
  have hgeo := R.hasSum_geometric (r := 1 / 2) (by rw [R.abs_of_nonneg hr]; grind)
  rw [show (1 : R) / (1 - 1 / 2) = 2 by grind] at hgeo
  have hle : ∀ n, R.expTerm (1 / 2) n ≤ (1 / 2 : R) ^ n := by
    intro n
    unfold R.expTerm
    have hf := natCast_le' (show 1 ≤ R.fact n from R.fact_pos n)
    have hp : (0 : R) ≤ (1 / 2 : R) ^ n := pow_nonneg' hr n
    apply div_le_of_le_mul (natCast_pos' (R.fact_pos n))
    have := OrderedRing.mul_le_mul_of_nonneg_left hf hp
    grind
  obtain ⟨s, hs, hst⟩ := R.comparison (R.expTerm_nonneg hr) hle hgeo
  rw [R.HasSum.unique (R.hasSum_exp _) hs]; exact hst

/-- `log 4 ≥ 1`, i.e. `e ≤ 4`. -/
theorem one_le_lnat_four : 1 ≤ lnat 4 := by
  have h2 : 1 / 2 ≤ lnat 2 := by
    have := log_le_log (R.exp_pos _) exp_half_le_two
    rw [R.log_exp] at this
    unfold lnat; rw [ite_eq_right (by omega)]
    rw [show ((2 : Nat) : R) = 2 by grind]; exact this
  have : lnat 4 = lnat 2 + lnat 2 := by rw [show 4 = 2 * 2 from rfl, lnat_mul (by omega) (by omega)]
  grind

/-- `log (n+1) − log n ≤ 1/n` for `n ≥ 1`. -/
theorem lnat_succ_sub_le {n : Nat} (hn : 1 ≤ n) : lnat (n + 1) - lnat n ≤ 1 / (n : R) := by
  have h1 := natCast_pos' (show 0 < n by omega)
  have hn' : (n : R) ≠ 0 := by grind
  have hq : (0 : R) < ((n + 1 : Nat) : R) / (n : R) := OF.div_pos (natCast_pos' (by omega)) h1
  have e : ((n + 1 : Nat) : R) = (n : R) * (((n + 1 : Nat) : R) / (n : R)) := by grind
  have hl : lnat (n + 1) = lnat n + R.log (((n + 1 : Nat) : R) / (n : R)) := by
    unfold lnat; rw [ite_eq_right (by omega), ite_eq_right (by omega), e, R.log_mul h1 hq]
    congr 1; grind
  have hge : (1 : R) ≤ ((n + 1 : Nat) : R) / (n : R) := by
    apply le_div_of_mul_le h1; have := natCast_le' (show n ≤ n + 1 by omega); grind
  have := log_le_sub_one hge
  rw [hl]
  have : ((n + 1 : Nat) : R) / (n : R) - 1 = 1 / (n : R) := by grind
  grind

/-- `log n / n` is non-increasing for `n ≥ 4`. -/
theorem lnat_div_succ_le {n : Nat} (hn : 4 ≤ n) :
    lnat (n + 1) / ((n + 1 : Nat) : R) ≤ lnat n / (n : R) := by
  have h1 := natCast_pos' (show 0 < n by omega)
  have h2 := natCast_pos' (show 0 < n + 1 by omega)
  have hd := lnat_succ_sub_le (show 1 ≤ n by omega)
  have h4 := lnat_le_lnat (show 0 < 4 by omega) hn
  have h5 := one_le_lnat_four
  -- `n (log (n+1) − log n) ≤ 1 ≤ log n`
  have h6 : (n : R) * (lnat (n + 1) - lnat n) ≤ 1 := by
    have := OrderedRing.mul_le_mul_of_nonneg_left hd (Std.le_of_lt h1)
    have hn' : (n : R) ≠ 0 := by grind
    rw [show (n : R) * (1 / (n : R)) = 1 by grind] at this; exact this
  apply le_div_of_mul_le h1
  rw [show lnat (n + 1) / ((n + 1 : Nat) : R) * (n : R) = lnat (n + 1) * (n : R) / ((n + 1 : Nat) : R)
    by grind]
  apply div_le_of_le_mul h2
  have : ((n + 1 : Nat) : R) = (n : R) + 1 := by grind
  rw [this]; grind

/-- `log n / n ≤ 1`. -/
theorem lnat_div_le_one (n : Nat) : lnat n / (n : R) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; unfold lnat; rw [ite_eq_left rfl]; rw [Field.div_eq_mul_inv]; grind
  · apply div_le_of_le_mul (natCast_pos' h)
    have := lnat_le n; rw [ite_eq_right (by omega)] at this; grind

/-- `log n / n ≥ 0`. -/
theorem lnat_div_nonneg (n : Nat) : 0 ≤ lnat n / (n : R) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; unfold lnat; rw [ite_eq_left rfl]; rw [Field.div_eq_mul_inv]; grind
  · have := div_le_div_of_le (lnat_nonneg n) (natCast_pos' h)
    rw [show (0 : R) / (n : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this; exact this

/-- **The partial sums of `Σ a(n) log n / n` are bounded** (by `4 + 2B`) when those of `a` are
bounded by `B` and `|a(n)| ≤ 1`. -/
theorem cabs_gsum_log_le {a : Nat → C} {B : R} (hB : ∀ N, C.cabs (gsum a N) ≤ B)
    (hbd : ∀ n, C.cabs (a n) ≤ 1) (N : Nat) :
    C.cabs (gsum (fun n => a n * ofReal (lnat n / (n : R))) N) ≤ 4 + 2 * B := by
  have hB0 : 0 ≤ B := by have := hB 0; rw [show gsum a 0 = 0 from rfl, C.cabs_zero] at this; exact this
  have small : ∀ M, M ≤ 4 → C.cabs (gsum (fun n => a n * ofReal (lnat n / (n : R))) M) ≤ (M : R) := by
    intro M _
    have h1 := cabs_gsum_le (fun n => a n * ofReal (lnat n / (n : R))) M
    have h2 := gsum_le_gsum (n := M) (f := fun n => C.cabs (a n * ofReal (lnat n / (n : R))))
      (g := fun _ => (1 : R)) (fun n _ => by
        rw [cabs_mul_ofReal (lnat_div_nonneg n)]
        have := OrderedRing.mul_le_mul_of_nonneg_right (hbd n) (lnat_div_nonneg n)
        have := lnat_div_le_one n; grind)
    rw [gsum_const_R] at h2; grind
  by_cases hN : N ≤ 4
  · have := small N hN; have := natCast_le' hN
    rw [show ((4 : Nat) : R) = 4 by grind] at this; grind
  · have h1 := abel_bound hB (b := fun n => lnat n / (n : R)) (M := 4)
      (fun n hn => lnat_div_succ_le hn) (fun n _ => lnat_div_nonneg n) N (by omega)
    have h2 := small 4 (Nat.le_refl 4)
    have h3 := C.cabs_add (gsum (fun n => a n * ofReal (lnat n / (n : R))) N -
      gsum (fun n => a n * ofReal (lnat n / (n : R))) 4) (gsum (fun n => a n * ofReal (lnat n / (n : R))) 4)
    rw [show ∀ x y : C, x - y + y = x from fun x y => by grind] at h3
    have h4 := lnat_div_le_one 4
    have h5 := OrderedRing.mul_le_mul_of_nonneg_left h4 (show 0 ≤ 2 * B by grind)
    rw [show ((4 : Nat) : R) = 4 by grind] at h2
    grind

end Foundations.NumberTheory
