import Foundations.NumberTheory.ChebyshevSums

/-!
# Dirichlet's theorem, conditional on `L(1, χ) ≠ 0`

This file assembles the pieces into the reduction that Dirichlet himself made in 1837:

> *If `L(1, χ) ≠ 0` for every non-principal character `χ` modulo `q`, then for every `a` coprime
> to `q` there are infinitely many primes `p ≡ a (mod q)`.*

Indeed, by the sieve, `φ(q) · Σ_{n ≤ N, n ≡ a} Λ(n)/n = Σ_χ conj χ(a) S_χ(N)`. The principal
character contributes at least `log N − 1 − 2q` (Mertens), and each of the other characters a
bounded amount (since `L(1, χ) ≠ 0`, file `ChebyshevSums`). So `Σ_{n ≤ N, n ≡ a} Λ(n)/n → ∞`.
If there were only finitely many primes `p ≡ a`, all below `N₀`, this sum would be at most
`N₀ + 4`: the primes contribute `log p / p ≤ 1` each, and the higher prime powers at most `4`
(file `PrimePowers`). This contradiction proves the theorem — given the non-vanishing, which is
the subject of the next files.
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Algebra.FiniteType Foundations.Numbers Foundations.Numbers.Arith Lean.Grind
open Foundations.Numbers.C (ofReal)

attribute [local instance] Classical.propDecidable

/-- `|conj z| = |z|`. -/
theorem cabs_conj (z : C) : C.cabs (C.conj z) = C.cabs z := by
  unfold C.cabs C.normSq; rw [C.conj_re, C.conj_im]; congr 1; grind

/-- If every term of a list sum has modulus at most `B`, the sum has modulus at most `length · B`. -/
theorem cabs_lsum_le {α : Type} (l : List α) (f : α → C) {B : R} (h : ∀ a ∈ l, C.cabs (f a) ≤ B) :
    C.cabs (lsum l f) ≤ (l.length : R) * B := by
  induction l with
  | nil => show C.cabs 0 ≤ ((0 : Nat) : R) * B; rw [C.cabs_zero]; grind
  | cons a l ih =>
    rw [lsum_cons, List.length_cons]
    have h1 := C.cabs_add (f a) (lsum l f)
    have h2 := h a List.mem_cons_self
    have h3 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have : ((l.length + 1 : Nat) : R) = (l.length : R) + 1 := by grind
    rw [this]; grind

/-- A uniform bound for finitely many eventually-bounded families. -/
theorem exists_uniform_bound {α : Type} (l : List α) (f : α → Nat → R)
    (h : ∀ a ∈ l, ∃ B : R, ∀ N, 0 < N → f a N ≤ B) : ∃ B : R, ∀ a ∈ l, ∀ N, 0 < N → f a N ≤ B := by
  induction l with
  | nil => exact ⟨0, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a l ih =>
    obtain ⟨B₁, h₁⟩ := h a List.mem_cons_self
    obtain ⟨B₂, h₂⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨OF.abs B₁ + OF.abs B₂, fun b hb N hN => ?_⟩
    have a1 := OF.le_abs B₁; have a2 := OF.le_abs B₂
    have a3 := OF.abs_nonneg B₁; have a4 := OF.abs_nonneg B₂
    rcases List.mem_cons.1 hb with rfl | hb
    · have := h₁ N hN; grind
    · have := h₂ b hb N hN; grind

/-- `log 2 ≥ 1/2`. -/
theorem half_le_lnat_two : 1 / 2 ≤ lnat 2 := by
  have := log_le_log (R.exp_pos _) exp_half_le_two
  rw [R.log_exp] at this
  unfold lnat; rw [ite_eq_right (by omega)]
  rw [show ((2 : Nat) : R) = 2 by grind]; exact this

/-- **`log N` is unbounded.** For every real `X` there is `N ≥ 1` with `log N > X`. -/
theorem exists_lnat_gt (X : R) : ∃ N : Nat, 0 < N ∧ X < lnat N := by
  obtain ⟨k, hk⟩ := R.archimedean (2 * X)
  refine ⟨2 ^ k, Nat.pow_pos (by omega), ?_⟩
  rw [lnat_pow (by omega)]
  have := half_le_lnat_two
  have h0 : (0 : R) ≤ (k : R) := OrderedRing.natCast_nonneg
  have := OrderedRing.mul_le_mul_of_nonneg_left this h0
  grind

/-- `#{p < B : p < N₀} ≤ N₀`. -/
theorem gsum_lt_le (N₀ : Nat) : ∀ B, gsum (fun p => if p < N₀ then (1 : R) else 0) B ≤ (N₀ : R) := by
  have key : ∀ B, gsum (fun p => if p < N₀ then (1 : R) else 0) B = ((min B N₀ : Nat) : R) := by
    intro B
    induction B with
    | zero => show (0 : R) = ((min 0 N₀ : Nat) : R); rw [Nat.zero_min]; grind
    | succ B ih =>
      rw [gsum_succ, ih]
      by_cases h : B < N₀
      · rw [ite_eq_left h, show min (B + 1) N₀ = min B N₀ + 1 by omega]; grind
      · rw [ite_eq_right h, show min (B + 1) N₀ = min B N₀ by omega]; grind
  intro B; rw [key]; exact natCast_le' (Nat.min_le_right B N₀)

variable {q : Nat} [NeZero q]

omit [NeZero q] in
/-- **If the primes `≡ a (mod q)` are all below `N₀`**, then
`Σ_{n ≤ N, n ≡ a} Λ(n)/n ≤ N₀ + 4` for every `N`. -/
theorem residue_sum_le {a N₀ : Nat} (h : ∀ p, Prime p → p % q = a % q → p < N₀) (N : Nat) :
    gsum (fun n => if n % q = a % q then vonMangoldt n / (n : R) else 0) (N + 1) ≤ (N₀ : R) + 4 := by
  have e : gsum (fun n => if n % q = a % q then vonMangoldt n / (n : R) else 0) (N + 1) =
      gsum (fun n => vonMangoldt n * (if n % q = a % q then 1 / (n : R) else 0)) (N + 1) :=
    gsum_congr fun n _ => by split <;> grind
  rw [e, gsum_vonMangoldt_mul]
  let A : Nat → Nat → R := fun p k => if k = 1 then (if p < N₀ then 1 else 0) else 0
  let Bt : Nat → Nat → R := fun p k =>
    if Prime p ∧ 2 ≤ k ∧ p ^ k ≤ N then lnat p / ((p ^ k : Nat) : R) else 0
  have hterm : ∀ p k, (if Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N then
      lnat p * (if p ^ k % q = a % q then 1 / ((p ^ k : Nat) : R) else 0) else 0) ≤ A p k + Bt p k := by
    intro p k
    have hA : 0 ≤ A p k := by show 0 ≤ (if k = 1 then _ else _); split; split <;> grind; grind
    have hB : 0 ≤ Bt p k := by
      show 0 ≤ (if Prime p ∧ 2 ≤ k ∧ p ^ k ≤ N then _ else _)
      split
      · next hc =>
        have := div_le_div_of_le (lnat_nonneg p) (natCast_pos' (Nat.pow_pos (n := k)
          (show 0 < p by have := hc.1.1; omega)))
        rw [show (0 : R) / ((p ^ k : Nat) : R) = 0 by rw [Field.div_eq_mul_inv]; grind] at this
        exact this
      · grind
    by_cases hc : Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N
    · rw [ite_eq_left hc]
      by_cases hm : p ^ k % q = a % q
      · rw [ite_eq_left hm]
        by_cases hk : k = 1
        · subst hk
          have hp := h p hc.1 (by rw [Nat.pow_one] at hm; exact hm)
          have : A p 1 = 1 := by show (if 1 = 1 then (if p < N₀ then (1 : R) else 0) else 0) = 1
                                 rw [ite_eq_left rfl, ite_eq_left hp]
          rw [this, Nat.pow_one]
          have := lnat_div_le_one p
          grind
        · have : Bt p k = lnat p / ((p ^ k : Nat) : R) := ite_eq_left ⟨hc.1, by omega, hc.2.2⟩
          rw [this]; grind
      · rw [ite_eq_right hm]; grind
    · rw [ite_eq_right hc]; grind
  have h1 := gsum_le_gsum (n := N + 1) (fun p _ => gsum_le_gsum (n := N + 1) (fun k _ => hterm p k))
  simp only [gsum_add] at h1
  have h2 : gsum (fun p => gsum (fun k => A p k) (N + 1)) (N + 1) ≤ (N₀ : R) := by
    apply Std.le_trans _ (gsum_lt_le N₀ (N + 1))
    apply gsum_le_gsum; intro p _
    show gsum (fun k => if k = 1 then (if p < N₀ then (1 : R) else 0) else 0) (N + 1) ≤ _
    rw [gsum_ite_eq 1 (N + 1) (fun _ => if p < N₀ then (1 : R) else 0)]
    split
    · grind
    · split <;> grind
  have h3 := prime_power_sum_le N
  have e2 : gsum (fun p => gsum (fun k => A p k + Bt p k) (N + 1)) (N + 1) =
      gsum (fun p => gsum (fun k => A p k) (N + 1)) (N + 1) +
        gsum (fun p => gsum (fun k => Bt p k) (N + 1)) (N + 1) := by
    rw [← gsum_add]; apply gsum_congr; intro p _; rw [gsum_add]
  grind

/-- **Dirichlet's theorem, conditional on the non-vanishing of `L(1, χ)`.** If `L(1, χ) ≠ 0` for
every non-principal character `χ` modulo `q`, then for every `a` coprime to `q` and every `N₀`
there is a prime `p ≥ N₀` with `p ≡ a (mod q)`. -/
theorem dirichlet_of_nonvanishing
    (hL : ∀ χ : Character (ZModUnits q), χ ≠ Character.one → Lone χ ≠ 0)
    (a : Nat) (ha : Nat.Coprime a q) (N₀ : Nat) : ∃ p, N₀ ≤ p ∧ Prime p ∧ p % q = a % q := by
  apply Classical.byContradiction
  intro hno
  have h : ∀ p, Prime p → p % q = a % q → p < N₀ := fun p hp hpa =>
    Classical.byContradiction fun hlt => hno ⟨p, by omega, hp, hpa⟩
  -- a uniform bound for the non-principal characters
  obtain ⟨B, hB⟩ := exists_uniform_bound (FiniteType.elems : List (Character (ZModUnits q)))
    (fun χ N => if χ = Character.one then 0 else C.cabs (chebSum χ N)) (fun χ _ => by
      by_cases hχ : χ = Character.one
      · exact ⟨0, fun N _ => by rw [ite_eq_left hχ]; grind⟩
      · obtain ⟨B, hB⟩ := chebSum_bounded χ hχ (hL χ hχ)
        exact ⟨B, fun N hN => by rw [ite_eq_right hχ]; exact hB N hN⟩)
  have hB0 : 0 ≤ B := by
    have := hB Character.one (FiniteType.complete _) 1 (by omega)
    rw [ite_eq_left rfl] at this; exact this
  -- choose `N` with `log N` large
  obtain ⟨N, hN, hlog⟩ := exists_lnat_gt ((totient q : R) * ((N₀ : R) + 4) + 1 + 2 * (q : R) +
    (card (Character (ZModUnits q)) : R) * B)
  -- the sieve identity, real parts
  let F : Character (ZModUnits q) → C := fun χ => C.conj (dchar χ a) * chebSum χ N
  let F₁ : Character (ZModUnits q) → C := fun χ => if χ = Character.one then 0 else F χ
  have hsieve := sum_conj_mul_chebSum a ha N
  have hdec : sumOver F = F Character.one + sumOver F₁ := by
    have e : sumOver F = sumOver (fun χ => (if χ = Character.one then F Character.one else 0) + F₁ χ) := by
      unfold sumOver; apply lsum_congr; intro χ _
      by_cases hχ : χ = Character.one
      · subst hχ; show F _ = (if _ then _ else _) + (if _ then _ else _)
        rw [ite_eq_left rfl, ite_eq_left rfl]; grind
      · show F χ = (if _ then _ else _) + (if _ then _ else _)
        rw [ite_eq_right hχ, ite_eq_right hχ]; grind
    rw [e]; unfold sumOver; rw [lsum_add]
    have := sumOver_single (Character.one : Character (ZModUnits q))
      (fun χ => if χ = Character.one then F Character.one else 0)
      (fun χ hχ => ite_eq_right hχ)
    unfold sumOver at this; rw [this, ite_eq_left rfl]
  have hone : F Character.one = ofReal (gsum (fun n => if Nat.Coprime n q then
      vonMangoldt n / (n : R) else 0) (N + 1)) := by
    show C.conj (dchar Character.one a) * chebSum Character.one N = _
    rw [chebSum_one, dchar_one_char, ite_eq_left ha]
    show C.conj 1 * _ = _
    rw [show C.conj 1 = 1 from C.ext rfl (by show -(0 : R) = 0; grind)]; grind
  have hF₁ : C.cabs (sumOver F₁) ≤ (card (Character (ZModUnits q)) : R) * B := by
    apply cabs_lsum_le; intro χ _
    show C.cabs (if χ = Character.one then 0 else F χ) ≤ B
    by_cases hχ : χ = Character.one
    · rw [ite_eq_left hχ, C.cabs_zero]; exact hB0
    · rw [ite_eq_right hχ]
      show C.cabs (C.conj (dchar χ a) * chebSum χ N) ≤ B
      rw [C.cabs_mul, cabs_conj]
      have h1 := cabs_dchar_le χ a
      have h2 := hB χ (FiniteType.complete _) N hN
      rw [ite_eq_right hχ] at h2
      have := OrderedRing.mul_le_mul_of_nonneg_right h1 (C.cabs_nonneg (chebSum χ N))
      grind
  have hre := congrArg C.re hsieve
  rw [show sumOver (fun χ : Character (ZModUnits q) => C.conj (dchar χ a) * chebSum χ N) =
    sumOver F from rfl, hdec, C.add_re, hone] at hre
  have hre1 : (ofReal (gsum (fun n => if Nat.Coprime n q then vonMangoldt n / (n : R) else 0)
      (N + 1))).re = gsum (fun n => if Nat.Coprime n q then vonMangoldt n / (n : R) else 0) (N + 1) := rfl
  have hre2 : (ofReal ((totient q : R) * gsum (fun n => if n % q = a % q then vonMangoldt n / (n : R)
      else 0) (N + 1))).re = (totient q : R) * gsum (fun n => if n % q = a % q then
      vonMangoldt n / (n : R) else 0) (N + 1) := rfl
  rw [hre1, hre2] at hre
  have h1 := principal_lower (q := q) hN
  have h2 := OF.le_abs (sumOver F₁).re
  have h3 := C.abs_re_le_cabs (sumOver F₁)
  have h4 := residue_sum_le (q := q) h N
  have h5 := OrderedRing.mul_le_mul_of_nonneg_left h4
    (OrderedRing.natCast_nonneg : (0 : R) ≤ (totient q : R))
  grind

end Foundations.NumberTheory
