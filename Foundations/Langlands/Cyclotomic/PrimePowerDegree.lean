import Foundations.Langlands.Cyclotomic.PrimePowerGalois
import Foundations.Langlands.Cyclotomic.QuadraticFixed

/-!
# The degree `[ℚ(ζ_{p^{k+1}}) : ℚ] = (p - 1) p^k = φ(p^{k+1})`

`Φ_{p^{k+1}} = Σ_{j<p} x^{j p^k}` is monic of degree `(p - 1) p^k` and is the minimal
polynomial of `ζ_{p^{k+1}}` (`PrimePowerGalois.lean`). By the simple-extension degree lemma of
`QuadraticFixed.lean`, the powers `1, ζ, …, ζ^{(p-1)p^k - 1}` form a basis, so the degree is
`(p - 1) p^k`, which is Euler's `φ(p^{k+1})`, the order of the Galois group `(ℤ/p^{k+1})ˣ`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

universe u

/-- `X^e` has degree `≤ e` with coefficient `1` at `e`. -/
theorem X_pow_deg {R : Type u} [CommRing R] (e : Nat) :
    DegLT ((X : Polynomial R) ^ e) (e + 1) ∧ coeff ((X : Polynomial R) ^ e) e = 1 := by
  have hc : ∀ n, coeff ((X : Polynomial R) ^ e) n = if n = e then 1 else 0 := by
    intro n
    rw [X_pow_eq_Xpow, ← Ring.mul_one (Xpow _), coeff_Xpow_mul]
    by_cases h : e ≤ n
    · rw [ite_true_of h, coeff_one]
      by_cases h' : n = e
      · rw [ite_true_of (by omega), ite_true_of h']
      · rw [ite_false_of (by omega), ite_false_of h']
    · rw [ite_false_of h, ite_false_of (by omega)]
  exact ⟨fun n hn => by rw [hc, ite_false_of (by omega)], by rw [hc, ite_true_of rfl]⟩

/-- `Φ_{p^{k+1}}` has degree `(p - 1) p^k` (over a non-zero ring). -/
theorem natDegree_cycloPP {R : Type u} [CommRing R] (h01 : (0 : R) ≠ 1) {p : Nat} (hp : 2 ≤ p)
    (k : Nat) : natDegree (cycloPP R p k) = (p - 1) * p ^ k := by
  have hm : 1 ≤ p ^ k := Nat.pow_pos (by omega)
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  rw [show r + 1 - 1 = r by omega]
  have hlow : ∀ n, n ≤ r → DegLT (rsum (fun j => (X : Polynomial R) ^ (j * (r + 1) ^ k)) n)
      (r * (r + 1) ^ k) := by
    intro n
    induction n with
    | zero => intro _ m _; exact coeff_zero m
    | succ n ih =>
      intro hn
      refine degLT_add (ih (by omega)) ((X_pow_deg _).1.mono ?_)
      have : (n + 1) * (r + 1) ^ k ≤ r * (r + 1) ^ k := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
  have htop := X_pow_deg (R := R) (r * (r + 1) ^ k)
  apply natDegree_eq_of
  · show DegLT (rsum _ r + _) _
    exact degLT_add ((hlow r (Nat.le_refl r)).mono (by omega)) htop.1
  · show coeff (rsum _ r + _) _ ≠ 0
    rw [coeff_add, hlow r (Nat.le_refl r) _ (Nat.le_refl _), htop.2, Ring.zero_add]
    exact fun h => h01 h.symm

/-- **The degree of `ℚ(ζ_{p^{k+1}})`.** `[ℚ(ζ_{p^{k+1}}) : ℚ] = (p - 1) p^k`. -/
theorem deg_cycloFieldPP {p : Nat} (hp : IsPrime p) (k : Nat) :
    deg Qc (cycloFieldPP hp k) (Qc_le_cycloFieldPP hp k) = (p - 1) * p ^ k := by
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  have hdeg := natDegree_cycloPP hD.1 hp.1 k
  rw [← hdeg]
  have hΦ0 : cycloPP Qc p k ≠ 0 := fun h => by
    rw [h] at hdeg
    have h0 : natDegree (0 : Polynomial Qc) = 0 := by unfold natDegree; rw [len_eq_zero.2 rfl]
    rw [h0] at hdeg
    have := hp.1
    have := Nat.mul_pos (show 0 < p - 1 by omega) (Nat.pow_pos (show 0 < p by omega) (n := k))
    omega
  apply deg_adjoin_eq _ _ hΦ0 ((aeval_zetaPP_eq_zero_iff hp k _).2 ⟨1, (Ring.mul_one _).symm⟩)
  intro r hr hrz
  obtain ⟨e, he⟩ := (aeval_zetaPP_eq_zero_iff hp k r).1 hrz
  apply Classical.byContradiction; intro hne
  have he0 : e ≠ 0 := by intro h; rw [h, Ring.mul_zero] at he; exact hne he
  have h1 := natDegree_mul hD hΦ0 he0
  rw [← he] at h1
  have := natDegree_lt_of_degLT hne hr
  omega

end Foundations.Langlands
