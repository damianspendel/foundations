import Foundations.NumberTheory.DirichletConditional
import Foundations.NumberTheory.Mobius

/-!
# `L(1, χ) ≠ 0` for characters that are not real

Suppose `L(1, χ) = 0` for a non-principal character. Inverting `L(1, χ)` with the Möbius
function shows that then the twisted Chebyshev sum is *large and negative*:

  `S_χ(N) = −log N + O(1)`.

Indeed `Σ_{d ∣ n} μ(d) log (N/d) = log N · [n = 1] + Λ(n)`, so summing against `χ(n)/n` gives

  `log N + S_χ(N) = Σ_{d ≤ N} μ(d) χ(d) log(N/d) / d · Σ_{m ≤ N/d} χ(m)/m`,

and if `L(1, χ) = 0` each inner sum is a tail of the series, of size `≤ 2qd/N`; the total is at
most `(2q/N) Σ_{d ≤ N} log (N/d) = (2q/N)(N log N − log N!) ≤ 2q`.

Now if `χ` is **not real**, then `χ̄ ≠ χ` and `L(1, χ̄) = conj L(1, χ) = 0` as well. But the sum of
all the `S_ψ(N)` over the characters is `φ(q) Σ_{n ≡ 1} Λ(n)/n ≥ 0`, while the principal character
contributes at most `log N + O(1)`, the two characters `χ, χ̄` contribute `−2 log N + O(1)`, and
every other character `O(1)` or less. For large `N` the total would be negative — a contradiction.
So a vanishing `L(1, χ)` can only come from a *real* character; that case needs a different idea
(next file).
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Algebra.FiniteType Foundations.Numbers Foundations.Numbers.Arith
open Lean.Grind
open Foundations.Numbers.C (ofReal CTendsto)

attribute [local instance] Classical.propDecidable

variable {q : Nat} [NeZero q]

/-- `|μ(n)| ≤ 1`. -/
theorem abs_mobius_le (n : Nat) : OF.abs (mobius n) ≤ 1 := by
  have hpow : ∀ k : Nat, OF.abs ((-1 : R) ^ k) = 1 := by
    intro k
    induction k with
    | zero => show OF.abs (1 : R) = 1; exact R.abs_of_nonneg (by grind)
    | succ k ih => show OF.abs ((-1 : R) ^ k * (-1)) = 1; rw [OF.abs_mul, ih]
                   rw [show OF.abs (-1 : R) = 1 by rw [R.abs_neg]; exact R.abs_of_nonneg (by grind)]
                   grind
  unfold mobius
  split
  · rw [R.abs_zero]; grind
  · split
    · rw [hpow]; grind
    · rw [R.abs_zero]; grind

/-- **The Möbius identity.** `log N + S_χ(N) = Σ_{d ≤ N} χ(d) μ(d) (log N − log d)/d · Σ_{m ≤ N/d} χ(m)/m`. -/
theorem mobius_identity (χ : Character (ZModUnits q)) (N : Nat) :
    ofReal (lnat N) + chebSum χ N =
      gsum (fun d => dchar χ d * ofReal (mobius d * (lnat N - lnat d) / (d : R)) *
        lpart (dchar χ) (N / d + 1)) (N + 1) := by
  let F : Nat → Nat → C := fun d m =>
    dchar χ d * ofReal (mobius d * (lnat N - lnat d) / (d : R)) * (dchar χ m * ofReal (1 / (m : R)))
  have h0 : ∀ m, F 0 m = 0 := fun m => by
    show dchar χ 0 * ofReal (_ / ((0 : Nat) : R)) * _ = 0
    rw [div_natCast_zero, ofReal_zero']; grind
  have h0' : ∀ d, F d 0 = 0 := fun d => by
    show _ * (dchar χ 0 * ofReal (1 / ((0 : Nat) : R))) = 0
    rw [div_natCast_zero, ofReal_zero']; grind
  -- the left side as a single sum
  have hL : ofReal (lnat N) + chebSum χ N = gsum (fun n => dchar χ n *
      ofReal (((if n = 1 then lnat N else 0) + vonMangoldt n) / (n : R))) (N + 1) := by
    unfold chebSum
    have e1 : gsum (fun n => dchar χ n * ofReal (((if n = 1 then lnat N else 0) + vonMangoldt n) /
        (n : R))) (N + 1) = gsum (fun n => if n = 1 then ofReal (lnat N) else 0) (N + 1) +
          gsum (fun n => dchar χ n * ofReal (vonMangoldt n / (n : R))) (N + 1) := by
      rw [← gsum_add]; apply gsum_congr; intro n _
      by_cases h : n = 1
      · subst h; rw [ite_eq_left rfl, ite_eq_left rfl, dchar_one]
        rw [show ((lnat N + vonMangoldt 1) / ((1 : Nat) : R)) =
          lnat N + vonMangoldt 1 / ((1 : Nat) : R) by grind, ofReal_add']; grind
      · rw [ite_eq_right h, ite_eq_right h]
        rw [show ((0 : R) + vonMangoldt n) = vonMangoldt n by grind]; grind
    rw [e1, gsum_ite_eq 1 (N + 1) (fun _ => ofReal (lnat N))]
    by_cases hN : 1 < N + 1
    · rw [ite_eq_left hN]
    · rw [ite_eq_right hN, show N = 0 by omega]; unfold lnat; rw [ite_eq_left rfl, ofReal_zero']
  rw [hL]
  have e2 : ∀ n, n < N + 1 → dchar χ n * ofReal (((if n = 1 then lnat N else 0) + vonMangoldt n) /
      (n : R)) = gsum (fun d => if d ∣ n then F d (n / d) else 0) (n + 1) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [gsum_succ, gsum_nil, ite_eq_left (Nat.dvd_zero 0), h0, div_natCast_zero, ofReal_zero']
      grind
    · have e3 : ∀ d, d < n + 1 → (if d ∣ n then F d (n / d) else 0) =
          dchar χ n * ofReal ((if d ∣ n then mobius d * (lnat N - lnat d) else 0) / (n : R)) := by
        intro d _
        by_cases hd : d ∣ n
        · rw [ite_eq_left hd, ite_eq_left hd]
          obtain ⟨m, hm⟩ := hd
          have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
          have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
          have hnd : n / d = m := by rw [hm, Nat.mul_div_cancel_left m hd0]
          show dchar χ d * ofReal (mobius d * (lnat N - lnat d) / (d : R)) *
            (dchar χ (n / d) * ofReal (1 / ((n / d : Nat) : R))) = _
          rw [hnd, hm, dchar_mul]
          have hdR : (d : R) ≠ 0 := by have := natCast_pos' hd0; grind
          have hmR : (m : R) ≠ 0 := by have := natCast_pos' hm0; grind
          have : mobius d * (lnat N - lnat d) / ((d * m : Nat) : R) =
              mobius d * (lnat N - lnat d) / (d : R) * (1 / (m : R)) := by
            rw [show ((d * m : Nat) : R) = (d : R) * (m : R) by grind]; grind
          rw [this, ofReal_mul']; grind
        · rw [ite_eq_right hd, ite_eq_right hd,
            show (0 : R) / (n : R) = 0 by rw [Field.div_eq_mul_inv]; grind, ofReal_zero']
          grind
      rw [gsum_congr e3, gsum_mul_left, ← ofReal_gsum]
      congr 2
      rw [show (fun d => (if d ∣ n then mobius d * (lnat N - lnat d) else 0) / (n : R)) =
        fun d => (if d ∣ n then mobius d * (lnat N - lnat d) else 0) * (1 / (n : R)) from
        funext fun d => by grind, gsum_mul_right]
      have h1 := dsum_mobius hn
      have h2 := dsum_mobius_lnat hn
      unfold dsum at h1 h2
      have e4 : gsum (fun d => if d ∣ n then mobius d * (lnat N - lnat d) else 0) (n + 1) =
          lnat N * gsum (fun d => if d ∣ n then mobius d else 0) (n + 1) -
            gsum (fun d => if d ∣ n then mobius d * lnat d else 0) (n + 1) := by
        rw [← gsum_mul_left, ← gsum_sub']
        apply gsum_congr; intro d _; split <;> grind
      rw [e4, h1, h2]
      by_cases hn1 : n = 1
      · rw [ite_eq_left hn1, ite_eq_left hn1]; grind
      · rw [ite_eq_right hn1, ite_eq_right hn1]; grind
  rw [gsum_congr e2, gsum_divisors_eq F h0 h0' N]
  apply gsum_congr; intro d _
  unfold lpart
  rw [← gsum_mul_left]

/-- **If `L(1, χ) = 0` then `S_χ(N) = −log N + O(1)`**: precisely `|log N + S_χ(N)| ≤ 2q`. -/
theorem cabs_lnat_add_chebSum_le (χ : Character (ZModUnits q)) (hχ : χ ≠ Character.one)
    (hL : Lone χ = 0) {N : Nat} (hN : 0 < N) :
    C.cabs (ofReal (lnat N) + chebSum χ N) ≤ 2 * (q : R) := by
  obtain ⟨_, htail⟩ := Lone_spec χ hχ
  rw [mobius_identity]
  have hq : (0 : R) ≤ 2 * (q : R) := by have : (0 : R) ≤ (q : R) := OrderedRing.natCast_nonneg; grind
  apply Std.le_trans (cabs_gsum_le _ _)
  have h1 : gsum (fun d => C.cabs (dchar χ d * ofReal (mobius d * (lnat N - lnat d) / (d : R)) *
      lpart (dchar χ) (N / d + 1))) (N + 1) ≤
      gsum (fun d => 2 * (q : R) * (1 / (N : R)) * (if 1 ≤ d then lnat N - lnat d else 0)) (N + 1) := by
    apply gsum_le_gsum; intro d hd
    rcases Nat.eq_zero_or_pos d with h0 | hd0
    · subst h0
      rw [div_natCast_zero, ofReal_zero', show dchar χ 0 * (0 : C) = 0 by grind,
        show (0 : C) * lpart (dchar χ) (N / 0 + 1) = 0 by grind, C.cabs_zero, ite_eq_right (by omega)]
      grind
    · rw [ite_eq_left (show 1 ≤ d by omega), C.cabs_mul, C.cabs_mul, cabs_ofReal']
      have hx : 0 ≤ lnat N - lnat d := by have := lnat_le_lnat hd0 (show d ≤ N by omega); grind
      have hT : C.cabs (lpart (dchar χ) (N / d + 1)) ≤ 2 * (q : R) / ((N / d + 1 : Nat) : R) := by
        have := htail (N / d + 1) (Nat.succ_pos _)
        rw [hL, show (0 : C) - lpart (dchar χ) (N / d + 1) = -lpart (dchar χ) (N / d + 1) by grind,
          C.cabs_neg] at this
        exact this
      have hdpos := natCast_pos' hd0
      have habs : OF.abs (mobius d * (lnat N - lnat d) / (d : R)) ≤ (lnat N - lnat d) * (1 / (d : R)) := by
        rw [Field.div_eq_mul_inv, OF.abs_mul, OF.abs_mul, R.abs_of_nonneg hx]
        have hinv : 0 < (d : R)⁻¹ := by
          have := OF.div_pos (show (0 : R) < 1 by grind) hdpos; rw [Field.div_eq_mul_inv] at this; grind
        rw [R.abs_of_nonneg (Std.le_of_lt hinv)]
        have := abs_mobius_le d
        have := OrderedRing.mul_le_mul_of_nonneg_right this hx
        have := OrderedRing.mul_le_mul_of_nonneg_right this (Std.le_of_lt hinv)
        grind
      have hc := cabs_dchar_le χ d
      have hn1 := C.cabs_nonneg (dchar χ d)
      have hn2 := OF.abs_nonneg (mobius d * (lnat N - lnat d) / (d : R))
      have hn3 := C.cabs_nonneg (lpart (dchar χ) (N / d + 1))
      have s1 := OrderedRing.mul_le_mul_of_nonneg_right hc hn2
      have s2 := OrderedRing.mul_le_mul_of_nonneg_right (show C.cabs (dchar χ d) *
        OF.abs (mobius d * (lnat N - lnat d) / (d : R)) ≤ (lnat N - lnat d) * (1 / (d : R)) by grind) hn3
      have s3 := OrderedRing.mul_le_mul_of_nonneg_left hT
        (OrderedRing.mul_nonneg hx (one_div_nonneg' d))
      have s4 := OrderedRing.mul_le_mul_of_nonneg_left (one_div_mul_le hN hd0)
        (OrderedRing.mul_nonneg hq hx)
      have e : (lnat N - lnat d) * (1 / (d : R)) * (2 * (q : R) / ((N / d + 1 : Nat) : R)) =
          2 * (q : R) * (lnat N - lnat d) * (1 / (d : R) * (1 / ((N / d + 1 : Nat) : R))) := by grind
      grind
  apply Std.le_trans h1
  rw [gsum_mul_left]
  -- `Σ_{1 ≤ d ≤ N} (log N − log d) = N log N − log N! ≤ N`
  have h2 : gsum (fun d => if 1 ≤ d then lnat N - lnat d else 0) (N + 1) ≤ (N : R) := by
    have e : gsum (fun d => if 1 ≤ d then lnat N - lnat d else 0) (N + 1) =
        gsum (fun d => if 1 ≤ d then lnat N else 0) (N + 1) - gsum lnat (N + 1) := by
      rw [← gsum_sub']; apply gsum_congr; intro d _
      by_cases h : 1 ≤ d
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h, show d = 0 by omega]; unfold lnat; grind
    rw [e, gsum_ite_one_le, ← lnat_fact]
    have := lnat_fact_ge hN; grind
  have hNp := natCast_pos' hN
  have h3 := OrderedRing.mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * (q : R) * (1 / (N : R)) from
    OrderedRing.mul_nonneg hq (one_div_nonneg' N))
  have : 2 * (q : R) * (1 / (N : R)) * (N : R) = 2 * (q : R) := by
    have : (N : R) ≠ 0 := by grind
    grind
  grind

/-! ## Conjugate characters -/

/-- The conjugate of a non-principal character is non-principal. -/
theorem conj_ne_one {χ : Character (ZModUnits q)} (hχ : χ ≠ Character.one) :
    Character.conj χ ≠ Character.one := by
  intro h; apply hχ
  apply Character.ext; intro x
  have := congrArg (fun ψ : Character (ZModUnits q) => C.conj (ψ.1 x)) h
  simp only [Character.conj, C.conj_conj] at this
  rw [this]; show C.conj 1 = 1; exact C.ext rfl (by show -(0 : R) = 0; grind)

/-- Conjugation commutes with finite sums. -/
theorem conj_gsum (f : Nat → C) (n : Nat) : C.conj (gsum f n) = gsum (fun k => C.conj (f k)) n := by
  induction n with
  | zero => exact C.ext rfl (by show -(0 : R) = 0; grind)
  | succ n ih => rw [gsum_succ, gsum_succ, C.conj_add, ih]

/-- `conj (ofReal x) = ofReal x`. -/
theorem conj_ofReal (x : R) : C.conj (ofReal x) = ofReal x := C.ext rfl (by show -(0 : R) = 0; grind)

/-- `L(1, χ̄) = conj L(1, χ)`. -/
theorem Lone_conj {χ : Character (ZModUnits q)} (hχ : χ ≠ Character.one) :
    Lone (Character.conj χ) = C.conj (Lone χ) := by
  obtain ⟨hL, _⟩ := Lone_spec χ hχ
  obtain ⟨hL', _⟩ := Lone_spec (Character.conj χ) (conj_ne_one hχ)
  apply C.CTendsto.unique hL'
  have e : lpart (dchar (Character.conj χ)) = fun N => C.conj (lpart (dchar χ) N) := by
    funext N; unfold lpart; rw [conj_gsum]; apply gsum_congr; intro n _
    rw [dchar_conj, C.conj_mul, conj_ofReal]
  rw [e]
  refine ⟨hL.1, ?_⟩
  have := hL.2.const_mul (-1)
  show R.Tendsto (fun N => -(lpart (dchar χ) N).im) (-(Lone χ).im)
  rw [show -(Lone χ).im = (-1) * (Lone χ).im by grind]
  exact this.congr_eventually 0 fun n _ => by grind

/-- `S_{χ̄}(N) = conj S_χ(N)`. -/
theorem chebSum_conj (χ : Character (ZModUnits q)) (N : Nat) :
    chebSum (Character.conj χ) N = C.conj (chebSum χ N) := by
  unfold chebSum; rw [conj_gsum]; apply gsum_congr; intro n _
  rw [dchar_conj, C.conj_mul, conj_ofReal]

/-! ## The counting argument -/

/-- Splitting off one term of a sum over a finite type. -/
theorem sumOver_split {α : Type} [FiniteType α] (a : α) (f : α → C) :
    sumOver f = f a + sumOver (fun x => if x = a then 0 else f x) := by
  have e : sumOver f = sumOver (fun x => (if x = a then f a else 0) + (if x = a then 0 else f x)) := by
    unfold sumOver; apply lsum_congr; intro x _
    by_cases hx : x = a
    · subst hx; rw [ite_eq_left rfl, ite_eq_left rfl]; grind
    · rw [ite_eq_right hx, ite_eq_right hx]; grind
  rw [e]; unfold sumOver; rw [lsum_add]
  have := sumOver_single a (fun x => if x = a then f a else 0) (fun x hx => ite_eq_right hx)
  unfold sumOver at this; rw [this, ite_eq_left rfl]

/-- If every term has real part at most `B`, the sum has real part at most `length · B`. -/
theorem re_lsum_le {α : Type} (l : List α) (f : α → C) {B : R} (h : ∀ a ∈ l, (f a).re ≤ B) :
    (lsum l f).re ≤ (l.length : R) * B := by
  induction l with
  | nil => show (0 : R) ≤ ((0 : Nat) : R) * B; grind
  | cons a l ih =>
    rw [lsum_cons, C.add_re, List.length_cons]
    have h2 := h a List.mem_cons_self
    have h3 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have : ((l.length + 1 : Nat) : R) = (l.length : R) + 1 := by grind
    rw [this]; grind

/-- **Non-vanishing for non-real characters.** If `χ ≠ χ₀` and `χ̄ ≠ χ`, then `L(1, χ) ≠ 0`. -/
theorem Lone_ne_zero_of_conj_ne (χ : Character (ZModUnits q)) (hχ : χ ≠ Character.one)
    (hconj : Character.conj χ ≠ χ) : Lone χ ≠ 0 := by
  intro hL
  have hL' : Lone (Character.conj χ) = 0 := by
    rw [Lone_conj hχ, hL]; exact C.ext rfl (by show -(0 : R) = 0; grind)
  have hχ' := conj_ne_one hχ
  -- every non-principal character has `re S_ψ(N)` bounded above
  obtain ⟨B, hB⟩ := exists_uniform_bound (FiniteType.elems : List (Character (ZModUnits q)))
    (fun ψ N => if ψ = Character.one then 0 else (chebSum ψ N).re) (fun ψ _ => by
      by_cases hψ : ψ = Character.one
      · exact ⟨0, fun N _ => by rw [ite_eq_left hψ]; grind⟩
      · by_cases hLψ : Lone ψ = 0
        · refine ⟨2 * (q : R), fun N hN => ?_⟩
          rw [ite_eq_right hψ]
          have h1 := cabs_lnat_add_chebSum_le ψ hψ hLψ hN
          have h2 := C.abs_re_le_cabs (ofReal (lnat N) + chebSum ψ N)
          have h3 := (OF.le_abs (ofReal (lnat N) + chebSum ψ N).re).1
          have h4 : (ofReal (lnat N) + chebSum ψ N).re = lnat N + (chebSum ψ N).re := rfl
          have := lnat_nonneg N
          grind
        · obtain ⟨B, hB⟩ := chebSum_bounded ψ hψ hLψ
          refine ⟨B, fun N hN => ?_⟩
          rw [ite_eq_right hψ]
          have := (OF.le_abs (chebSum ψ N).re).1
          have := C.abs_re_le_cabs (chebSum ψ N)
          have := hB N hN; grind)
  have hB0 : 0 ≤ B := by
    have := hB Character.one (FiniteType.complete _) 1 (by omega)
    rw [ite_eq_left rfl] at this; exact this
  obtain ⟨N, hN, hlog⟩ := exists_lnat_gt (chebC + 4 * (q : R) +
    (card (Character (ZModUnits q)) : R) * B)
  -- the sum over all characters is `φ(q) Σ_{n ≡ 1} Λ(n)/n ≥ 0`
  have hsieve := sum_conj_mul_chebSum (q := q) 1 (Nat.coprime_one_left q) N
  have e1 : sumOver (fun ψ : Character (ZModUnits q) => C.conj (dchar ψ 1) * chebSum ψ N) =
      sumOver (fun ψ : Character (ZModUnits q) => chebSum ψ N) := by
    unfold sumOver; apply lsum_congr; intro ψ _
    rw [dchar_one, show C.conj 1 = 1 from C.ext rfl (by show -(0 : R) = 0; grind)]; grind
  rw [e1] at hsieve
  have hpos : 0 ≤ (sumOver (fun ψ : Character (ZModUnits q) => chebSum ψ N)).re := by
    rw [hsieve]
    show 0 ≤ (totient q : R) * gsum (fun n => if n % q = 1 % q then vonMangoldt n / (n : R) else 0) (N + 1)
    apply OrderedRing.mul_nonneg OrderedRing.natCast_nonneg
    apply gsum_nonneg; intro n
    split
    · rcases Nat.eq_zero_or_pos n with h | h
      · subst h; rw [div_natCast_zero]; grind
      · have := div_le_div_of_le (vonMangoldt_nonneg n) (natCast_pos' h)
        rw [show (0 : R) / (n : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this; exact this
    · grind
  -- split off `χ₀`, `χ`, `χ̄`
  let f : Character (ZModUnits q) → C := fun ψ => chebSum ψ N
  let f1 : Character (ZModUnits q) → C := fun ψ => if ψ = Character.one then 0 else f ψ
  let f2 : Character (ZModUnits q) → C := fun ψ => if ψ = χ then 0 else f1 ψ
  let f3 : Character (ZModUnits q) → C := fun ψ => if ψ = Character.conj χ then 0 else f2 ψ
  have d1 := sumOver_split Character.one f
  have d2 := sumOver_split χ f1
  have d3 := sumOver_split (Character.conj χ) f2
  have v2 : f1 χ = f χ := ite_eq_right hχ
  have v3 : f2 (Character.conj χ) = f (Character.conj χ) := by
    show (if _ then _ else _) = _; rw [ite_eq_right hconj]; exact ite_eq_right hχ'
  have hrest : (sumOver f3).re ≤ (card (Character (ZModUnits q)) : R) * B := by
    apply re_lsum_le; intro ψ hψ
    show (if ψ = Character.conj χ then 0 else if ψ = χ then 0 else
      if ψ = Character.one then 0 else chebSum ψ N).re ≤ B
    split
    · exact hB0
    · split
      · exact hB0
      · split
        · exact hB0
        · next h => have := hB ψ hψ N hN; rw [ite_eq_right h] at this; exact this
  have hp0 : (f Character.one).re ≤ lnat N + chebC := by
    show (chebSum Character.one N).re ≤ _
    rw [chebSum_one]; exact principal_upper hN
  have hz : ∀ ψ : Character (ZModUnits q), ψ ≠ Character.one → Lone ψ = 0 →
      (f ψ).re ≤ -lnat N + 2 * (q : R) := by
    intro ψ hψ hLψ
    have h1 := cabs_lnat_add_chebSum_le ψ hψ hLψ hN
    have h2 := C.abs_re_le_cabs (ofReal (lnat N) + chebSum ψ N)
    have h3 := (OF.le_abs (ofReal (lnat N) + chebSum ψ N).re).1
    have h4 : (ofReal (lnat N) + chebSum ψ N).re = lnat N + (chebSum ψ N).re := rfl
    show (chebSum ψ N).re ≤ _; grind
  have hz1 := hz χ hχ hL
  have hz2 := hz (Character.conj χ) hχ' hL'
  have := congrArg C.re (d1.trans (congrArg _ (d2.trans (congrArg _ d3))))
  simp only [C.add_re] at this
  rw [v2, v3] at this
  grind

end Foundations.NumberTheory
