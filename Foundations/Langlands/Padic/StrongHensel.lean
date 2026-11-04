import Foundations.Langlands.Padic.Hensel

/-!
# Hensel's lemma for non-simple roots

The simple form of Hensel's lemma (`Hensel`) needs `f'(a) ≢ 0 (mod p)`. That fails for `p = 2`
and `f = X² + 7`: every `f'(a) = 2a` is even. The **strong form** only asks that `f(a)` be small
compared with the *square* of `f'(a)`:

  `|f(a)|ₚ < |f'(a)|ₚ²`.

In integer terms, with `e = vₚ(f'(a))` (so `pᵉ ∣ f'(a)` but `pᵉ⁺¹ ∤ f'(a)`), the hypothesis is
`p^(2e+1) ∣ f(a)`, and the conclusion is a root `x ∈ ℤₚ` with `x ≡ a (mod pᵉ⁺¹)`. The proof is
Newton's method again. Writing `f'(s) = pᵉ w` with `w` a unit mod `p`, each step corrects `s` by a
multiple of `p^(e+1+n)`, which raises the power of `p` dividing `f(s)` from `p^(2e+1+n)` to
`p^(2e+2+n)`; the quadratic Taylor term is harmless because `(p^(e+1+n))²` is divisible enough.
The correction leaves `s ≡ a (mod pᵉ⁺¹)`, so `vₚ(f'(s)) = e` throughout.

Example: `√−7 ∈ ℤ₂`, from `a = 1`: `f(1) = 8 = 2³`, `f'(1) = 2`, `e = 1`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- One Newton step in the non-simple case. If `f'(s) = pᵉ w`, `p ∣ u w − 1` and
`p^(2e+1+n) ∣ f(s)`, then the corrected point `s + (−(f(s)/p^(2e+1+n)) u) p^(e+1+n)` satisfies
`p^(2e+2+n) ∣ f(s')`. -/
theorem newton_step_strong {p : Nat} (f : List Int) (s u w : Int) (e n : Nat)
    (hd : pderiv f s = (p : Int) ^ e * w) (hu : (p : Int) ∣ u * w - 1)
    (hs : (p : Int) ^ (2 * e + 1 + n) ∣ peval f s) :
    (p : Int) ^ (2 * e + 2 + n) ∣
      peval f (s + (-(peval f s / (p : Int) ^ (2 * e + 1 + n)) * u) * (p : Int) ^ (e + 1 + n)) := by
  generalize hq : peval f s / (p : Int) ^ (2 * e + 1 + n) = q
  have hfs : peval f s = q * (p : Int) ^ (2 * e + 1 + n) := by rw [← hq, Int.ediv_mul_cancel hs]
  obtain ⟨G, hG⟩ := taylor f s ((-q * u) * (p : Int) ^ (e + 1 + n))
  rw [hG, hfs, hd]
  obtain ⟨z, hz⟩ := hu
  have e1 : (p : Int) ^ (e + 1 + n) = (p : Int) ^ e * p * (p : Int) ^ n := by
    rw [Int.pow_add, Int.pow_succ]
  have e2 : (p : Int) ^ (2 * e + 1 + n) = (p : Int) ^ e * (p : Int) ^ e * p * (p : Int) ^ n := by
    rw [Int.pow_add, Int.pow_succ, show 2 * e = e + e by omega, Int.pow_add]
  have e3 : (p : Int) ^ (2 * e + 2 + n) =
      (p : Int) ^ e * (p : Int) ^ e * p * p * (p : Int) ^ n := by
    rw [Int.pow_add, show 2 * e + 2 = e + e + 1 + 1 by omega, Int.pow_succ, Int.pow_succ,
      Int.pow_add]
  rw [e1, e2, e3]
  have huw : u * w = p * z + 1 := by omega
  clear e1 e2 e3 hq hfs hG hs hd hz
  generalize (p : Int) ^ e = A
  generalize (p : Int) ^ n = B
  refine ⟨-q * z + q * q * u * u * B * G, ?_⟩
  grind

/-- **Hensel's lemma, strong form.** Let `p` be prime, `f` an integer polynomial and `a` an
integer with `vₚ(f'(a)) = e` (i.e. `pᵉ ∣ f'(a)`, `pᵉ⁺¹ ∤ f'(a)`) and `p^(2e+1) ∣ f(a)` — that is,
`|f(a)|ₚ < |f'(a)|ₚ²`. Then there is `x ∈ ℤₚ` with `f(x) = 0` and `x ≡ a (mod pᵉ⁺¹)`. -/
theorem hensel_strong {p : Nat} (hp : Prime p) (f : List Int) (a : Int) (e : Nat)
    (hd1 : (p : Int) ^ e ∣ pderiv f a) (hd2 : ¬ (p : Int) ^ (e + 1) ∣ pderiv f a)
    (hf : (p : Int) ^ (2 * e + 1) ∣ peval f a) :
    ∃ x : Zp p, Zp.peval f x = 0 ∧ Zp.ModPow (e + 1) x (a : Zp p) := by
  obtain ⟨w0, hw0⟩ := hd1
  have hpw0 : ¬ (p : Int) ∣ w0 := fun h => hd2 (by
    rw [hw0, Int.pow_succ]; exact Int.mul_dvd_mul_left _ h)
  obtain ⟨u, hu⟩ := exists_inv_mod hp hpw0
  let step : Nat → Int → Int := fun n s =>
    s + (-(peval f s / (p : Int) ^ (2 * e + 1 + n)) * u) * (p : Int) ^ (e + 1 + n)
  let s : Nat → Int := fun n => Nat.rec a (fun k acc => step k acc) n
  have hs_succ : ∀ n, s (n + 1) = step n (s n) := fun _ => rfl
  have hstep : ∀ n, (p : Int) ^ (e + 1 + n) ∣ s (n + 1) - s n := by
    intro n; rw [hs_succ]
    show _ ∣ s n + _ - s n
    rw [show ∀ a b : Int, a + b - a = b from fun _ _ => by omega]
    exact Int.dvd_mul_left _ _
  have inv : ∀ n, (p : Int) ^ (2 * e + 1 + n) ∣ peval f (s n) ∧
      (p : Int) ^ (e + 1) ∣ s n - a := by
    intro n
    induction n with
    | zero => exact ⟨hf, by show _ ∣ a - a; rw [Int.sub_self]; exact Int.dvd_zero _⟩
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · -- `f'(sₙ) = pᵉ (w₀ + p r)`
        obtain ⟨r, hr⟩ := Int.dvd_trans ih2 (sub_dvd_pderiv f (s n) a)
        have hd : pderiv f (s n) = (p : Int) ^ e * (w0 + p * r) := by
          rw [show pderiv f (s n) = (pderiv f (s n) - pderiv f a) + pderiv f a by omega, hr, hw0,
            Int.pow_succ]; grind
        have hu' : (p : Int) ∣ u * (w0 + p * r) - 1 := by
          rw [show u * (w0 + p * r) - 1 = (u * w0 - 1) + p * (u * r) by grind]
          exact Int.dvd_add hu (Int.dvd_mul_right _ _)
        rw [hs_succ, show 2 * e + 1 + (n + 1) = 2 * e + 2 + n by omega]
        exact newton_step_strong f (s n) u _ e n hd hu' ih1
      · rw [show s (n + 1) - a = (s (n + 1) - s n) + (s n - a) by omega]
        exact Int.dvd_add (Int.dvd_trans (Int.pow_dvd_pow_of_le' (by omega)) (hstep n)) ih2
  let x : PSeq p := ⟨s, fun n => Int.dvd_trans (Int.pow_dvd_pow_of_le' (by omega)) (hstep n)⟩
  refine ⟨Zp.mk x, ?_, ?_⟩
  · show Zp.mk (PSeq.peval f x) = Zp.mk (PSeq.const 0)
    apply Zp.mk_eq_mk.2
    intro n
    show _ ∣ peval f (s n) - 0
    rw [Int.sub_zero]
    exact Int.dvd_trans (Int.pow_dvd_pow_of_le' (by omega)) (inv n).1
  · show (p : Int) ^ (e + 1) ∣ s (e + 1) - a
    exact (inv (e + 1)).2

/-- `2` is prime. -/
theorem prime_two : Prime 2 :=
  ⟨by omega, fun d hd => by
    have := Nat.le_of_dvd (by omega) hd
    have key : ∀ d, d < 3 → d ∣ 2 → d = 1 ∨ d = 2 := by decide
    exact key d (by omega) hd⟩

/-- **`√−7 ∈ ℤ₂`.** There is a 2-adic integer `x` with `x² = −7` and `x ≡ 1 (mod 4)`. (The
simple Hensel lemma does not apply, since every derivative `2a` is even.) -/
theorem sqrt_neg_seven_Z2 : ∃ x : Zp 2, x * x = -7 ∧ Zp.ModPow 2 x (1 : Int) := by
  obtain ⟨x, hx, hx1⟩ := hensel_strong prime_two [7, 0, 1] 1 1 (by decide) (by decide)
    (by decide)
  refine ⟨x, ?_, hx1⟩
  have := peval_sq_sub (p := 2) (-7) x
  rw [show -(-7 : Int) = 7 by rfl] at this
  rw [this] at hx
  have : ((-7 : Int) : Zp 2) = -7 := by
    rw [Lean.Grind.Ring.intCast_neg]; rfl
  rw [this] at hx; grind

end Foundations.Langlands.Padic
