import Foundations.Numbers.TrigIdentities
import Foundations.Numbers.Complex

/-!
# The complex exponential and Euler's formula

We define the exponential of a complex number by the same power series as for reals,

  `exp z = Σ zⁿ / n!`,

now summed in `C` (a series of complex numbers converges when its real and imaginary parts do).
Three facts are then proved, none of them by definition:

* the **functional equation** `exp (z + w) = exp z · exp w`. For complex arguments the
  derivative trick of the real case is not available, so we multiply the series (Cauchy). The
  partial sums satisfy `Pₙ(z) Pₙ(w) = Pₙ(z + w) + Tₙ(z, w)`, where — by the binomial theorem in
  the form `Σᵢ zⁱ/i! · wⁿ⁻ⁱ/(n−i)! = (z + w)ⁿ/n!` — the remainder `Tₙ` collects the products
  `zⁱ/i! · wʲ/j!` with `i, j < n ≤ i + j`. Its size is at most the same remainder for the
  non-negative reals `‖z‖, ‖w‖`, which is `Pₙ(‖z‖)Pₙ(‖w‖) − Pₙ(‖z‖ + ‖w‖) → 0` by the *real*
  functional equation;
* on the real axis it is the real exponential;
* **Euler's formula** `exp (iθ) = cos θ + i sin θ`: the powers `(iθ)ⁿ` cycle through
  `θⁿ, iθⁿ, −θⁿ, −iθⁿ`, exactly the coefficient pattern of the cosine and sine series.

Together: `exp (x + iy) = eˣ (cos y + i sin y)`, `|exp (iθ)| = 1`, and **Euler's identity**
`e^{iπ} + 1 = 0`, linking the five constants `0, 1, e, i, π` — each of which has been constructed
from nothing in this project.

The combinatorics (finite sums, the binomial identity, the triangle rearrangement) is done once
for an arbitrary field, and used for both `R` and `C`.
-/

namespace Foundations.Numbers

open Lean.Grind

/-! ## Finite sums in a field -/

section Generic

attribute [local instance] Semiring.natCast

variable {α : Type} [Field α]

/-- The finite sum `f 0 + ⋯ + f (n − 1)` in any field. -/
def gsum (f : Nat → α) : Nat → α
  | 0 => 0
  | n + 1 => gsum f n + f n

/-- Defining equation of `gsum`. -/
theorem gsum_succ (f : Nat → α) (n : Nat) : gsum f (n + 1) = gsum f n + f n := rfl

/-- Sums of termwise equal sequences agree. -/
theorem gsum_congr {f g : Nat → α} {n : Nat} (h : ∀ k, k < n → f k = g k) :
    gsum f n = gsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum_succ, gsum_succ, ih fun k hk => h k (by omega), h n (by omega)]

/-- Sums are additive. -/
theorem gsum_add (f g : Nat → α) (n : Nat) :
    gsum (fun k => f k + g k) n = gsum f n + gsum g n := by
  induction n with
  | zero => show (0 : α) = 0 + 0; grind
  | succ n ih => rw [gsum_succ, gsum_succ, gsum_succ, ih]; grind

/-- Constants factor out of sums. -/
theorem gsum_mul_left (c : α) (f : Nat → α) (n : Nat) :
    gsum (fun k => c * f k) n = c * gsum f n := by
  induction n with
  | zero => show (0 : α) = c * 0; grind
  | succ n ih => rw [gsum_succ, gsum_succ, ih]; grind

/-- Constants factor out of sums (on the right). -/
theorem gsum_mul_right (c : α) (f : Nat → α) (n : Nat) :
    gsum (fun k => f k * c) n = gsum f n * c := by
  induction n with
  | zero => show (0 : α) = 0 * c; grind
  | succ n ih => rw [gsum_succ, gsum_succ, ih]; grind

/-- Splitting off the first term. -/
theorem gsum_succ' (f : Nat → α) (n : Nat) :
    gsum f (n + 1) = f 0 + gsum (fun k => f (k + 1)) n := by
  induction n with
  | zero => show (0 : α) + f 0 = f 0 + 0; grind
  | succ n ih => rw [gsum_succ, ih, gsum_succ]; grind

/-- Splitting a sum into two consecutive blocks. -/
theorem gsum_split (f : Nat → α) (m n : Nat) :
    gsum f (m + n) = gsum f m + gsum (fun k => f (m + k)) n := by
  induction n with
  | zero => show gsum f m = gsum f m + 0; grind
  | succ n ih => rw [← Nat.add_assoc, gsum_succ, ih, gsum_succ]; grind

/-- **The binomial theorem for exponential terms.** If `e x 0 = 1` and
`(n + 1) · e x (n+1) = x · e x n` (as for `e x n = xⁿ/n!`), then
`Σ_{i ≤ n} e a i · e b (n − i) = e (a + b) n`. -/
theorem gsum_binomial (e : α → Nat → α) (he0 : ∀ x, e x 0 = 1)
    (hes : ∀ (x : α) (n : Nat), ((n : α) + 1) * e x (n + 1) = x * e x n) (hn : ∀ n : Nat, (n : α) + 1 ≠ 0)
    (a b : α) (n : Nat) :
    gsum (fun i => e a i * e b (n - i)) (n + 1) = e (a + b) n := by
  induction n with
  | zero =>
    show 0 + e a 0 * e b (0 - 0) = e (a + b) 0
    rw [Nat.sub_self, he0, he0, he0]; grind
  | succ n ih =>
    -- `(n + 2) Sₙ₊₁ = a Sₙ + b Sₙ`, split according to `n + 1 = i + (n + 1 − i)`.
    have hX : gsum (fun i => (i : α) * (e a i * e b (n + 1 - i))) (n + 1 + 1) =
        a * gsum (fun i => e a i * e b (n - i)) (n + 1) := by
      rw [gsum_succ', ← gsum_mul_left]
      have : ((0 : Nat) : α) = 0 := Semiring.natCast_zero
      rw [this]
      have : gsum (fun k => ((k + 1 : Nat) : α) * (e a (k + 1) * e b (n + 1 - (k + 1)))) (n + 1) =
          gsum (fun k => a * (e a k * e b (n - k))) (n + 1) := gsum_congr fun k _ => by
        rw [show n + 1 - (k + 1) = n - k by omega, Semiring.natCast_succ]
        have := hes a k; grind
      rw [this]; grind
    have hY : gsum (fun i => ((n + 1 - i : Nat) : α) * (e a i * e b (n + 1 - i))) (n + 1 + 1) =
        b * gsum (fun i => e a i * e b (n - i)) (n + 1) := by
      rw [gsum_succ, ← gsum_mul_left, Nat.sub_self]
      have : ((0 : Nat) : α) = 0 := Semiring.natCast_zero
      rw [this]
      have : gsum (fun i => ((n + 1 - i : Nat) : α) * (e a i * e b (n + 1 - i))) (n + 1) =
          gsum (fun k => b * (e a k * e b (n - k))) (n + 1) := gsum_congr fun k hk => by
        rw [show n + 1 - k = (n - k) + 1 by omega, Semiring.natCast_succ]
        have := hes b (n - k); grind
      rw [this]; grind
    have h3 : ((n + 1 : Nat) : α) = (n : α) + 1 := Semiring.natCast_succ n
    have hsum : ((n + 1 : Nat) : α) * gsum (fun i => e a i * e b (n + 1 - i)) (n + 1 + 1) =
        gsum (fun i => (i : α) * (e a i * e b (n + 1 - i))) (n + 1 + 1) +
        gsum (fun i => ((n + 1 - i : Nat) : α) * (e a i * e b (n + 1 - i))) (n + 1 + 1) := by
      rw [← gsum_add, ← gsum_mul_left]
      apply gsum_congr
      intro i hi
      have : ((n + 1 - i : Nat) : α) + (i : α) = ((n + 1 : Nat) : α) := by
        rw [← Semiring.natCast_add, show n + 1 - i + i = n + 1 by omega]
      clear hX hY ih hes he0 hn
      generalize e a i * e b (n + 1 - i) = T
      generalize ((n + 1 - i : Nat) : α) = u at this ⊢
      generalize ((i : Nat) : α) = v at this ⊢
      generalize ((n + 1 : Nat) : α) = w at this ⊢
      grind
    rw [hX, hY, ih, h3] at hsum
    have h1 := hes (a + b) n
    have hne := hn n
    -- Cancel the non-zero factor `n + 1`.
    have hinv := Field.mul_inv_cancel hne
    generalize gsum (fun i => e a i * e b (n + 1 - i)) (n + 1 + 1) = S at hsum ⊢
    generalize e (a + b) (n + 1) = E at h1 ⊢
    have : ((n : α) + 1)⁻¹ * (((n : α) + 1) * S) = ((n : α) + 1)⁻¹ * (((n : α) + 1) * E) := by
      rw [hsum, h1]; grind
    grind

/-- **Triangle rearrangement.** `Σ_{i<N} f i · (Σ_{j<N−i} g j) = Σ_{n<N} Σ_{i≤n} f i g (n−i)`. -/
theorem gsum_triangle (f g : Nat → α) (N : Nat) :
    gsum (fun i => f i * gsum g (N - i)) N =
      gsum (fun n => gsum (fun i => f i * g (n - i)) (n + 1)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [gsum_succ, gsum_succ, ← ih, gsum_succ (fun i => f i * g (N - i)), Nat.sub_self,
      show N + 1 - N = 1 by omega]
    have : gsum (fun i => f i * gsum g (N + 1 - i)) N =
        gsum (fun i => f i * gsum g (N - i)) N + gsum (fun i => f i * g (N - i)) N := by
      rw [← gsum_add]
      apply gsum_congr
      intro i hi
      rw [show N + 1 - i = (N - i) + 1 by omega, gsum_succ]; grind
    rw [this]
    have : gsum g 1 = g 0 := by show 0 + g 0 = g 0; grind
    rw [this]; grind

/-- **Product of partial sums.** `(Σ_{i<N} f i)(Σ_{j<N} g j)` is the "triangle" `i + j < N` plus
the remainder `Σ_{i<N} f i · Σ_{k<i} g (N − i + k)`. -/
theorem gsum_mul_gsum (f g : Nat → α) (N : Nat) :
    gsum f N * gsum g N = gsum (fun n => gsum (fun i => f i * g (n - i)) (n + 1)) N +
      gsum (fun i => f i * gsum (fun k => g (N - i + k)) i) N := by
  rw [← gsum_triangle, ← gsum_add, ← gsum_mul_right]
  apply gsum_congr
  intro i hi
  have := gsum_split g (N - i) i
  rw [show N - i + i = N by omega] at this
  rw [this]; grind

/-- **Cauchy product of exponential series**, finite form:
`Pₙ(a) Pₙ(b) = Pₙ(a + b) + Tₙ(a, b)` with `Pₙ(x) = Σ_{k<n} e x k`. -/
theorem gsum_exp_mul (e : α → Nat → α) (he0 : ∀ x, e x 0 = 1)
    (hes : ∀ (x : α) (n : Nat), ((n : α) + 1) * e x (n + 1) = x * e x n) (hn : ∀ n : Nat, (n : α) + 1 ≠ 0)
    (a b : α) (N : Nat) :
    gsum (e a) N * gsum (e b) N = gsum (e (a + b)) N +
      gsum (fun i => e a i * gsum (fun k => e b (N - i + k)) i) N := by
  rw [gsum_mul_gsum]
  congr 1
  exact gsum_congr fun n _ => gsum_binomial e he0 hes hn a b n

end Generic


/-! ## Real-side preliminaries -/

namespace R

open OF

/-- On `R`, the generic finite sum is the one used so far. -/
theorem gsum_eq_fsum (f : Nat → R) (n : Nat) : gsum f n = fsum f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum_succ, fsum_succ, ih]

/-- `x⁰/0! = 1`. -/
theorem expTerm_zero (x : R) : expTerm x 0 = 1 := by
  unfold expTerm; show (1 : R) / ((1 : Nat) : R) = 1; grind

/-- `(n + 1) · xⁿ⁺¹/(n+1)! = x · xⁿ/n!`. -/
theorem expTerm_rec (x : R) (n : Nat) : ((n : R) + 1) * expTerm x (n + 1) = x * expTerm x n := by
  rw [expTerm_succ]
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  grind

/-- **Limit of a product** is the product of the limits. -/
theorem Tendsto.mul {a b : Nat → R} {L M : R} (ha : Tendsto a L) (hb : Tendsto b M) :
    Tendsto (fun n => a n * b n) (L * M) := fun ε hε => by
  obtain ⟨B, hB⟩ := cauchy_bounded ha.isCauchySeq
  have hB0 : 0 ≤ B := Std.le_trans (abs_nonneg _) (hB 0)
  obtain ⟨η₁, hη₁, hη₁c⟩ := exists_mul_le B (by grind : 0 < ε / 3)
  obtain ⟨η₂, hη₂, hη₂c⟩ := exists_mul_le M (by grind : 0 < ε / 3)
  obtain ⟨N₁, h₁⟩ := hb η₁ hη₁
  obtain ⟨N₂, h₂⟩ := ha η₂ hη₂
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  rw [abs_of_nonneg hB0] at hη₁c
  have k1 := abs_mul_le (hB n) (Std.le_of_lt (h₁ n (by omega)))
  have k2 := abs_mul_le (Std.le_refl (abs M)) (Std.le_of_lt (h₂ n (by omega)))
  have k3 := abs_add (a n * (b n - M)) (M * (a n - L))
  rw [show a n * (b n - M) + M * (a n - L) = a n * b n - L * M by grind] at k3
  grind

/-- The remainder of the Cauchy product of two exponential series tends to `0`:
`Tₙ(α, β) = Pₙ(α) Pₙ(β) − Pₙ(α + β) → exp α · exp β − exp (α + β) = 0`. -/
theorem tendsto_exp_remainder (α β : R) :
    Tendsto (fun N => gsum (fun i => expTerm α i * gsum (fun k => expTerm β (N - i + k)) i) N) 0 := by
  have h := ((hasSum_exp α : Tendsto _ _).mul (hasSum_exp β : Tendsto _ _)).sub
    (hasSum_exp (α + β) : Tendsto _ _)
  rw [← exp_add, show exp (α + β) - exp (α + β) = 0 by grind] at h
  refine h.congr_eventually 0 fun N _ => ?_
  have := gsum_exp_mul (α := R) expTerm expTerm_zero expTerm_rec
    (fun n => by have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg; grind) α β N
  rw [gsum_eq_fsum, gsum_eq_fsum, gsum_eq_fsum] at this
  show fsum (expTerm α) N * fsum (expTerm β) N - fsum (expTerm (α + β)) N = _
  rw [this]; grind

end R

/-! ## Complex sequences and series -/

namespace C

open R OF

/-- The real number `x` as a complex number `x + 0i`. -/
def ofReal (x : R) : C := ⟨x, 0⟩

/-- The size `‖z‖ = |re z| + |im z|` (a convenient norm; `|z| ≤ ‖z‖ ≤ 2|z|`). -/
noncomputable def nrm (z : C) : R := abs z.re + abs z.im

/-- `‖z‖ ≥ 0`. -/
theorem nrm_nonneg (z : C) : 0 ≤ nrm z := by
  have := abs_nonneg z.re; have := abs_nonneg z.im; unfold nrm; grind

/-- Triangle inequality for `‖·‖`. -/
theorem nrm_add (z w : C) : nrm (z + w) ≤ nrm z + nrm w := by
  unfold nrm; simp only [add_re, add_im]
  have := OF.abs_add z.re w.re; have := OF.abs_add z.im w.im; grind

/-- `‖·‖` is submultiplicative. -/
theorem nrm_mul (z w : C) : nrm (z * w) ≤ nrm z * nrm w := by
  unfold nrm; simp only [mul_re, mul_im]
  have k1 := OF.abs_add (z.re * w.re) (-(z.im * w.im))
  have k2 := OF.abs_add (z.re * w.im) (z.im * w.re)
  rw [R.abs_neg, abs_mul, abs_mul] at k1
  rw [abs_mul, abs_mul] at k2
  rw [show z.re * w.re + -(z.im * w.im) = z.re * w.re - z.im * w.im by grind] at k1
  grind

/-- `‖z − w‖ = ‖w − z‖`. -/
theorem nrm_sub_comm (z w : C) : nrm (z - w) = nrm (w - z) := by
  unfold nrm
  show abs (z.re + -w.re) + abs (z.im + -w.im) = abs (w.re + -z.re) + abs (w.im + -z.im)
  rw [show z.re + -w.re = z.re - w.re by grind, show z.im + -w.im = z.im - w.im by grind,
    show w.re + -z.re = w.re - z.re by grind, show w.im + -z.im = w.im - z.im by grind,
    abs_sub_comm z.re, abs_sub_comm z.im]

/-- `|re z| ≤ ‖z‖`. -/
theorem abs_re_le (z : C) : abs z.re ≤ nrm z := by have := abs_nonneg z.im; unfold nrm; grind

/-- `|im z| ≤ ‖z‖`. -/
theorem abs_im_le (z : C) : abs z.im ≤ nrm z := by have := abs_nonneg z.re; unfold nrm; grind

/-- Real part of a finite sum. -/
theorem gsum_re (f : Nat → C) (n : Nat) : (gsum f n).re = fsum (fun k => (f k).re) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum_succ, fsum_succ, add_re, ih]

/-- Imaginary part of a finite sum. -/
theorem gsum_im (f : Nat → C) (n : Nat) : (gsum f n).im = fsum (fun k => (f k).im) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum_succ, fsum_succ, add_im, ih]

/-- Triangle inequality for finite sums. -/
theorem nrm_gsum_le (f : Nat → C) (n : Nat) : nrm (gsum f n) ≤ fsum (fun k => nrm (f k)) n := by
  induction n with
  | zero => show nrm 0 ≤ 0; unfold nrm; rw [zero_re, zero_im, R.abs_zero]; grind
  | succ n ih => rw [gsum_succ, fsum_succ]; have := nrm_add (gsum f n) (f n); grind

/-- A sequence of complex numbers **converges** to `L` if its real and imaginary parts do. -/
def CTendsto (s : Nat → C) (L : C) : Prop :=
  Tendsto (fun n => (s n).re) L.re ∧ Tendsto (fun n => (s n).im) L.im

/-- Limits of complex sequences are unique. -/
theorem CTendsto.unique {s : Nat → C} {L M : C} (hL : CTendsto s L) (hM : CTendsto s M) :
    L = M := ext (tendsto_unique hL.1 hM.1) (tendsto_unique hL.2 hM.2)

/-- Limit of a product of complex sequences. -/
theorem CTendsto.mul {s t : Nat → C} {L M : C} (hs : CTendsto s L) (ht : CTendsto t M) :
    CTendsto (fun n => s n * t n) (L * M) :=
  ⟨(hs.1.mul ht.1).sub (hs.2.mul ht.2), (hs.1.mul ht.2).add (hs.2.mul ht.1)⟩

/-- If `‖sₙ − tₙ‖ → 0` and `tₙ → L`, then `sₙ → L`. -/
theorem CTendsto.of_nrm_sub {s t : Nat → C} {L : C} (ht : CTendsto t L)
    (h : Tendsto (fun n => nrm (s n - t n)) 0) : CTendsto s L := by
  have hre : Tendsto (fun n => (s n - t n).re) 0 := tendsto_of_abs_le h fun n => by
    rw [show (s n - t n).re - 0 = (s n - t n).re by grind]; exact abs_re_le _
  have him : Tendsto (fun n => (s n - t n).im) 0 := tendsto_of_abs_le h fun n => by
    rw [show (s n - t n).im - 0 = (s n - t n).im by grind]; exact abs_im_le _
  constructor
  · have := hre.add ht.1
    rw [show (0 : R) + L.re = L.re by grind] at this
    exact this.congr_eventually 0 fun n _ => by
      show (s n + -t n).re + (t n).re = (s n).re; simp only [add_re, neg_re]; grind
  · have := him.add ht.2
    rw [show (0 : R) + L.im = L.im by grind] at this
    exact this.congr_eventually 0 fun n _ => by
      show (s n + -t n).im + (t n).im = (s n).im; simp only [add_im, neg_im]; grind

/-! ## The exponential series in `C` -/

/-- The `n`-th term `zⁿ / n!` of the complex exponential series. -/
noncomputable def cterm (z : C) (n : Nat) : C := z ^ n / ((fact n : Nat) : C)

/-- Real part of `w / r` for a real `r > 0`. -/
theorem div_natCast_re (w : C) {m : Nat} (hm : 0 < m) : (w / (m : C)).re = w.re / (m : R) := by
  have hpos : (0 : R) < (m : R) := OrderedRing.pos_natCast_of_pos _ hm
  show (w * (m : C)⁻¹).re = _
  rw [mul_re, inv_re, inv_im]
  show w.re * ((m : R) / ((m : R) * (m : R) + 0 * 0)) - w.im * (-0 / ((m : R) * (m : R) + 0 * 0)) = _
  grind

/-- Imaginary part of `w / r` for a real `r > 0`. -/
theorem div_natCast_im (w : C) {m : Nat} (hm : 0 < m) : (w / (m : C)).im = w.im / (m : R) := by
  have hpos : (0 : R) < (m : R) := OrderedRing.pos_natCast_of_pos _ hm
  show (w * (m : C)⁻¹).im = _
  rw [mul_im, inv_re, inv_im]
  show w.re * (-0 / ((m : R) * (m : R) + 0 * 0)) + w.im * ((m : R) / ((m : R) * (m : R) + 0 * 0)) = _
  grind

/-- `z⁰/0! = 1`. -/
theorem cterm_zero (z : C) : cterm z 0 = 1 := by
  unfold cterm
  apply ext
  · rw [div_natCast_re _ (fact_pos 0)]; show (1 : R) / ((1 : Nat) : R) = 1; grind
  · rw [div_natCast_im _ (fact_pos 0)]; show (0 : R) / ((1 : Nat) : R) = 0; grind

/-- `n + 1 ≠ 0` in `C`. -/
theorem natCast_add_one_ne_zero (n : Nat) : (n : C) + 1 ≠ 0 := fun h => by
  have := congrArg re h
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
  simp only [add_re, zero_re, one_re] at *
  have e : ((n : C)).re = (n : R) := rfl
  grind

/-- The recursion `(n + 1) · zⁿ⁺¹/(n+1)! = z · zⁿ/n!`. -/
theorem cterm_rec (z : C) (n : Nat) : ((n : C) + 1) * cterm z (n + 1) = z * cterm z n := by
  unfold cterm
  have h1 : ((fact (n + 1) : Nat) : C) = ((n : C) + 1) * ((fact n : Nat) : C) := by
    show (((n + 1) * fact n : Nat) : C) = _; grind
  have h2 : ((fact n : Nat) : C) ≠ 0 := fun h => by
    have h' := congrArg re h
    have e : (((fact n : Nat) : C)).re = ((fact n : Nat) : R) := rfl
    rw [e, zero_re] at h'
    have := fact_pos' n; grind
  have h3 := natCast_add_one_ne_zero n
  rw [h1, show z ^ (n + 1) = z ^ n * z from rfl]
  grind

/-- Powers and `‖·‖`: `‖zⁿ‖ ≤ ‖z‖ⁿ`. -/
theorem nrm_pow_le (z : C) (n : Nat) : nrm (z ^ n) ≤ nrm z ^ n := by
  induction n with
  | zero =>
    show nrm 1 ≤ 1; unfold nrm; rw [one_re, one_im, R.abs_zero, abs_of_nonneg (by grind)]; grind
  | succ n ih =>
    show nrm (z ^ n * z) ≤ nrm z ^ n * nrm z
    have := nrm_mul (z ^ n) z
    have := OrderedRing.mul_le_mul_of_nonneg_right ih (nrm_nonneg z)
    grind

/-- `‖zⁿ/n!‖ ≤ ‖z‖ⁿ/n!`. -/
theorem nrm_cterm_le (z : C) (n : Nat) : nrm (cterm z n) ≤ expTerm (nrm z) n := by
  unfold nrm cterm expTerm
  rw [div_natCast_re _ (fact_pos n), div_natCast_im _ (fact_pos n), abs_div_pos (fact_pos' n),
    abs_div_pos (fact_pos' n), Field.div_eq_mul_inv]
  have := OrderedRing.mul_le_mul_of_nonneg_right (nrm_pow_le z n)
    (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 (fact_pos' n)))
  unfold nrm at this
  grind

/-- The complex exponential series converges. -/
theorem exists_exp (z : C) : ∃ L, CTendsto (fun N => gsum (cterm z) N) L := by
  have hre : ∃ s, HasSum (fun n => (cterm z n).re) s := by
    obtain ⟨t, ht, -⟩ := comparison (fun n => abs_nonneg _)
      (fun n => Std.le_trans (abs_re_le _) (nrm_cterm_le z n)) (hasSum_exp (nrm z))
    obtain ⟨s, hs, -⟩ := summable_of_abs ht
    exact ⟨s, hs⟩
  have him : ∃ s, HasSum (fun n => (cterm z n).im) s := by
    obtain ⟨t, ht, -⟩ := comparison (fun n => abs_nonneg _)
      (fun n => Std.le_trans (abs_im_le _) (nrm_cterm_le z n)) (hasSum_exp (nrm z))
    obtain ⟨s, hs, -⟩ := summable_of_abs ht
    exact ⟨s, hs⟩
  obtain ⟨a, ha⟩ := hre
  obtain ⟨b, hb⟩ := him
  exact ⟨⟨a, b⟩, ha.congr_eventually 0 fun N _ => (gsum_re _ N).symm,
    hb.congr_eventually 0 fun N _ => (gsum_im _ N).symm⟩

/-- **The complex exponential** `exp z = Σ zⁿ / n!`. -/
noncomputable def exp (z : C) : C := Classical.choose (exists_exp z)

/-- The partial sums of the exponential series converge to `exp z`. -/
theorem tendsto_exp (z : C) : CTendsto (fun N => gsum (cterm z) N) (exp z) :=
  Classical.choose_spec (exists_exp z)

/-- **Functional equation of the complex exponential.** `exp (z + w) = exp z · exp w`. -/
theorem exp_add (z w : C) : exp (z + w) = exp z * exp w := by
  have hprod := (tendsto_exp z).mul (tendsto_exp w)
  -- `Pₙ(z + w)` differs from `Pₙ(z) Pₙ(w)` by `Tₙ(z, w)`, and `‖Tₙ(z, w)‖ ≤ Tₙ(‖z‖, ‖w‖) → 0`.
  have hbound : ∀ N, nrm (gsum (cterm (z + w)) N - gsum (cterm z) N * gsum (cterm w) N) ≤
      gsum (fun i => expTerm (nrm z) i * gsum (fun k => expTerm (nrm w) (N - i + k)) i) N := by
    intro N
    have hcp := gsum_exp_mul (α := C) cterm cterm_zero cterm_rec natCast_add_one_ne_zero z w N
    rw [hcp, show gsum (cterm (z + w)) N - (gsum (cterm (z + w)) N +
      gsum (fun i => cterm z i * gsum (fun k => cterm w (N - i + k)) i) N) =
      -gsum (fun i => cterm z i * gsum (fun k => cterm w (N - i + k)) i) N by grind]
    have hneg : ∀ u : C, nrm (-u) = nrm u := fun u => by
      unfold nrm; rw [neg_re, neg_im, R.abs_neg, R.abs_neg]
    rw [hneg, gsum_eq_fsum]
    refine Std.le_trans (nrm_gsum_le _ N) (fsum_le_fsum (fun i => ?_) N)
    refine Std.le_trans (nrm_mul _ _) ?_
    have k1 := nrm_cterm_le z i
    have k2 : nrm (gsum (fun k => cterm w (N - i + k)) i) ≤
        gsum (fun k => expTerm (nrm w) (N - i + k)) i := by
      rw [gsum_eq_fsum]
      exact Std.le_trans (nrm_gsum_le _ i) (fsum_le_fsum (fun k => nrm_cterm_le w _) i)
    have := OrderedRing.mul_le_mul_of_nonneg_right k1
      (nrm_nonneg (gsum (fun k => cterm w (N - i + k)) i))
    have := OrderedRing.mul_le_mul_of_nonneg_left k2 (expTerm_nonneg (nrm_nonneg z) i)
    grind
  have hzero : Tendsto (fun N => nrm (gsum (cterm (z + w)) N -
      gsum (cterm z) N * gsum (cterm w) N)) 0 :=
    tendsto_of_abs_le (tendsto_exp_remainder (nrm z) (nrm w)) fun N => by
      rw [show nrm (gsum (cterm (z + w)) N - gsum (cterm z) N * gsum (cterm w) N) - 0 =
        nrm (gsum (cterm (z + w)) N - gsum (cterm z) N * gsum (cterm w) N) by grind,
        abs_of_nonneg (nrm_nonneg _)]
      exact hbound N
  exact (tendsto_exp (z + w)).unique (CTendsto.of_nrm_sub hprod hzero)

/-! ## Euler's formula -/

/-- Powers of a real number stay real. -/
theorem ofReal_pow (x : R) (n : Nat) : ofReal x ^ n = ofReal (x ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ofReal x ^ n * ofReal x = _
    rw [ih]; apply ext
    · show x ^ n * x - 0 * 0 = x ^ (n + 1); rw [pow_succ']; grind
    · show x ^ n * 0 + 0 * x = 0; grind

/-- **On the real axis the complex exponential is the real one.** -/
theorem exp_ofReal (x : R) : exp (ofReal x) = ofReal (R.exp x) := by
  have h : CTendsto (fun N => gsum (cterm (ofReal x)) N) (ofReal (R.exp x)) := by
    constructor
    · refine (hasSum_exp x : Tendsto _ _).congr_eventually 0 fun N _ => ?_
      show fsum (expTerm x) N = (gsum (cterm (ofReal x)) N).re
      rw [gsum_re]; apply fsum_congr; intro k _
      unfold cterm expTerm; rw [div_natCast_re _ (fact_pos k), ofReal_pow]; rfl
    · refine (tendsto_const 0).congr_eventually 0 fun N _ => ?_
      show (0 : R) = (gsum (cterm (ofReal x)) N).im
      rw [gsum_im]
      have : ∀ n, fsum (fun k => (cterm (ofReal x) k).im) n = 0 := fun n => by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [fsum_succ, ih]; unfold cterm
          rw [div_natCast_im _ (fact_pos n), ofReal_pow]; show 0 + 0 / _ = (0 : R); grind
      rw [this]
  exact (tendsto_exp _).unique h

/-- The powers of `iθ` cycle through the coefficients of cosine and sine:
`(iθ)ⁿ = cₙ θⁿ + i sₙ θⁿ`. -/
theorem pow_I_mul (θ : R) (n : Nat) :
    (⟨0, θ⟩ : C) ^ n = ⟨cosCoeff n * θ ^ n, sinCoeff n * θ ^ n⟩ := by
  induction n with
  | zero => apply ext <;> show _ = _ * 1 <;> rfl
  | succ n ih =>
    show (⟨0, θ⟩ : C) ^ n * ⟨0, θ⟩ = _
    rw [ih, pow_succ']
    apply ext
    · show cosCoeff n * θ ^ n * 0 - sinCoeff n * θ ^ n * θ = -sinCoeff n * (θ ^ n * θ); grind
    · show cosCoeff n * θ ^ n * θ + sinCoeff n * θ ^ n * 0 = cosCoeff n * (θ ^ n * θ); grind

/-- **Euler's formula.** `exp (iθ) = cos θ + i sin θ`. -/
theorem exp_I_mul (θ : R) : exp (I * ofReal θ) = ofReal (cos θ) + I * ofReal (sin θ) := by
  have e1 : I * ofReal θ = ⟨0, θ⟩ := by
    apply ext
    · show 0 * θ - 1 * 0 = 0; grind
    · show 0 * 0 + 1 * θ = θ; grind
  have e2 : ofReal (cos θ) + I * ofReal (sin θ) = ⟨cos θ, sin θ⟩ := by
    apply ext
    · show cos θ + (0 * sin θ - 1 * 0) = cos θ; grind
    · show 0 + (0 * 0 + 1 * sin θ) = sin θ; grind
  rw [e1, e2]
  have hterm : ∀ k, (cterm ⟨0, θ⟩ k).re = pterm cosCoeff θ k ∧
      (cterm ⟨0, θ⟩ k).im = pterm sinCoeff θ k := fun k => by
    unfold cterm pterm expTerm
    rw [div_natCast_re _ (fact_pos k), div_natCast_im _ (fact_pos k), pow_I_mul]
    have := fact_pos' k
    constructor <;> (show _ * θ ^ k / _ = _ * (θ ^ k / _); grind)
  refine (tendsto_exp _).unique ⟨?_, ?_⟩
  · refine (hasSum_pser (fun n => (abs_coeff_le n).1) θ : Tendsto _ _).congr_eventually 0
      fun N _ => ?_
    show fsum (pterm cosCoeff θ) N = (gsum (cterm ⟨0, θ⟩) N).re
    rw [gsum_re]; exact fsum_congr fun k _ => (hterm k).1.symm
  · refine (hasSum_pser (fun n => (abs_coeff_le n).2) θ : Tendsto _ _).congr_eventually 0
      fun N _ => ?_
    show fsum (pterm sinCoeff θ) N = (gsum (cterm ⟨0, θ⟩) N).im
    rw [gsum_im]; exact fsum_congr fun k _ => (hterm k).2.symm

/-- **Polar form of the exponential.** `exp (x + iy) = eˣ (cos y + i sin y)`. -/
theorem exp_eq (z : C) :
    exp z = ofReal (R.exp z.re) * (ofReal (cos z.im) + I * ofReal (sin z.im)) := by
  have : z = ofReal z.re + I * ofReal z.im := by
    apply ext
    · show z.re = z.re + (0 * z.im - 1 * 0); grind
    · show z.im = 0 + (0 * 0 + 1 * z.im); grind
  conv => lhs; rw [this]
  rw [exp_add, exp_ofReal, exp_I_mul]

/-- **Euler's identity.** `e^{iπ} + 1 = 0`. -/
theorem euler_identity : exp (I * ofReal pi) + 1 = 0 := by
  rw [exp_I_mul, cos_pi, sin_pi]
  apply ext
  · show -1 + (0 * 0 - 1 * 0) + 1 = (0 : R); grind
  · show 0 + (0 * 0 + 1 * 0) + 0 = (0 : R); grind

/-- **`|exp (iθ)| = 1`**: the points `exp (iθ)` lie on the unit circle. -/
theorem normSq_exp_I_mul (θ : R) : normSq (exp (I * ofReal θ)) = 1 := by
  rw [exp_I_mul]
  show (cos θ + (0 * sin θ - 1 * 0)) * (cos θ + (0 * sin θ - 1 * 0)) +
    (0 + (0 * 0 + 1 * sin θ)) * (0 + (0 * 0 + 1 * sin θ)) = 1
  have := sin_sq_add_cos_sq θ; grind

/-- `e = exp 1` is the complex exponential at `1`, so `e^{iπ}` really is `e` to the power `iπ`
in the sense `exp (iπ)`. -/
theorem exp_one_eq : exp (ofReal 1) = ofReal R.e := exp_ofReal 1

end C

end Foundations.Numbers
