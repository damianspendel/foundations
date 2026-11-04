import Foundations.Numbers.Arithmetic
import Foundations.Langlands.Forms.ClassNumber

/-!
# Which primes does a form represent?

Fermat claimed, and Euler proved, that an odd prime is `x² + y²` iff `p ≡ 1 (mod 4)`, is
`x² + 2y²` iff `p ≡ 1, 3 (mod 8)` and is `x² + 3y²` iff `p = 3` or `p ≡ 1 (mod 3)`. Euler
also conjectured that `x² + 5y²` behaves differently: the primes it represents should be
those `≡ 1, 9 (mod 20)`, while primes `≡ 3, 7 (mod 20)` are represented by
`2x² + 2xy + 3y²` instead. **Lagrange** (1773–1775) explained the pattern by the following criterion, which
reduces the question "which forms of discriminant `D` represent `p`" to a congruence.

## Results

* **Lagrange's criterion** (`prime_rep_iff`). For a prime `p` and any integer `D`:
  `p` is represented by some form of discriminant `D` iff `D` is a square modulo `4p`.
  (One direction completes a primitive representation `p = f(x, y)` to a matrix
  `γ = (x q; y s) ∈ SL₂(ℤ)` by Bézout, making `p` the leading coefficient of `f·γ`, so that
  `D = b'² − 4pc'`; the other writes down `(p, b, (b² − D)/(4p))`.) The usual statement has
  `p` odd, to rephrase the condition with a Legendre symbol; the version proved here needs no
  such hypothesis.
* **Applied to `x² + 5y²`.** If an odd prime `p ≠ 5` is `x² + 5y²` then `−20` is a square mod
  `4p` (`neg20_square_of_rep`), and by congruences mod 4 and mod 5,
  **`p ≡ 1 or 9 (mod 20)`** (`prime_x2_5y2_mod20`).
* **A converse, via the class number.** Since `h(−20) = 2`, a prime represented by some
  form of discriminant `−20` is represented by `x² + 5y²` or by `2x² + 2xy + 3y²`; odd values
  of the latter are `≡ 3 (mod 4)`. Hence **if `p ≡ 1, 9 (mod 20)` and `−20` is a square
  mod `4p`, then `p = x² + 5y²`** (`rep_x2_5y2_of_square`). The square condition itself follows
  from `p ≡ 1, 9 (mod 20)` by quadratic reciprocity; that step is not formalised here.

In the language of class field theory (prose only), for primes `p ∤ 20`: `p` is represented by *some* form of
discriminant `−20` iff `p` splits in `ℚ(√−5)`, and by the *principal* form iff it splits
completely in the Hilbert class field `ℚ(√−5, i)`, a condition that here happens to be a
congruence because the class group has exponent 2 (Gauss's genus theory).
-/

namespace Foundations.Langlands.Forms

open Foundations.Algebra Foundations.Langlands.Modular Foundations.Numbers

namespace Form

/-- Scaling: `f(gx, gy) = g² f(x, y)`. -/
theorem eval_smul (f : Form) (g x y : Int) : f.eval (g * x) (g * y) = g * g * f.eval x y := by
  unfold eval; grind

/-- If `f(x, y)` is a prime `p`, then `gcd(|x|, |y|) = 1`: a representation of a prime is
primitive. -/
theorem gcd_eq_one_of_eval_prime {f : Form} {x y : Int} {p : Nat} (hp : Arith.Prime p)
    (h : f.eval x y = p) : Arith.gcd x.natAbs y.natAbs = 1 := by
  obtain ⟨hgx, hgy⟩ := Arith.gcd_dvd x.natAbs y.natAbs
  generalize Arith.gcd x.natAbs y.natAbs = g at hgx hgy
  obtain ⟨u, hu⟩ := Int.ofNat_dvd_left.2 hgx
  obtain ⟨v, hv⟩ := Int.ofNat_dvd_left.2 hgy
  have e : ((g * g : Nat) : Int) ∣ (p : Int) := by
    refine ⟨f.eval u v, ?_⟩
    rw [← h, hu, hv, eval_smul]; simp
  have e' : g * g ∣ p := Int.natCast_dvd_natCast.1 e
  have hg : g ∣ p := Nat.dvd_trans (Nat.dvd_mul_right g g) e'
  rcases hp.2 g hg with h1 | h1
  · exact h1
  · exfalso
    subst h1
    have hp2 := hp.1
    have := Nat.le_of_dvd (by omega) e'
    have : g * 2 ≤ g * g := Nat.mul_le_mul_left g hp2
    omega

/-- **Completing a primitive vector.** If `gcd(|x|, |y|) = 1` there is `γ ∈ SL₂(ℤ)` with
first column `(x, y)`. -/
theorem exists_sl2_col {x y : Int} (h : Arith.gcd x.natAbs y.natAbs = 1) :
    ∃ γ : SL2Z, γ.a = x ∧ γ.c = y := by
  obtain ⟨u, v, huv⟩ := Arith.bezout x.natAbs y.natAbs
  rw [h] at huv
  have ex : x * (if 0 ≤ x then u else -u) = (x.natAbs : Int) * u := by
    split <;> rename_i hx
    · rw [Int.natAbs_of_nonneg hx]
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]; grind
  have ey : (if 0 ≤ y then -v else v) * y = -((y.natAbs : Int) * v) := by
    split <;> rename_i hy
    · rw [Int.natAbs_of_nonneg hy]; grind
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]; grind
  exact ⟨⟨x, if 0 ≤ y then -v else v, y, if 0 ≤ x then u else -u, by
    rw [ex, ey]; simp at huv; omega⟩, rfl, rfl⟩

/-- **Lagrange's criterion.** A prime `p` is represented by some binary quadratic form of
discriminant `D` iff `D` is a square modulo `4p`. -/
theorem prime_rep_iff {p : Nat} (hp : Arith.Prime p) (D : Int) :
    (∃ f : Form, f.disc = D ∧ ∃ x y : Int, f.eval x y = p) ↔
      ∃ b : Int, 4 * (p : Int) ∣ b * b - D := by
  constructor
  · rintro ⟨f, hD, x, y, hxy⟩
    obtain ⟨γ, ha, hc⟩ := exists_sl2_col (gcd_eq_one_of_eval_prime hp hxy)
    have h1 : (f.act γ).a = p := by rw [act_a, ha, hc, hxy]
    have h2 : (f.act γ).disc = D := by rw [disc_act, hD]
    refine ⟨(f.act γ).b, (f.act γ).c, ?_⟩
    rw [← h2]; unfold disc; rw [h1]; grind
  · rintro ⟨b, k, hk⟩
    refine ⟨⟨p, b, k⟩, ?_, 1, 0, ?_⟩
    · unfold disc; simp only; grind
    · unfold eval; simp

/-- **Reduction of values modulo `n`.** `f(x, y) ≡ f(x mod n, y mod n) (mod n)`. -/
theorem eval_emod (f : Form) (n x y : Int) : f.eval x y % n = f.eval (x % n) (y % n) % n := by
  have hx : x = x % n + n * (x / n) := by rw [Int.emod_def]; omega
  have hy : y = y % n + n * (y / n) := by rw [Int.emod_def]; omega
  generalize x % n = r at hx ⊢
  generalize y % n = t at hy ⊢
  generalize x / n = u at hx
  generalize y / n = v at hy
  subst hx hy
  have e : f.eval (r + n * u) (t + n * v) = f.eval r t + n * (f.a * (2 * r * u + n * u * u) +
      f.b * (r * v + u * t + n * u * v) + f.c * (2 * t * v + n * v * v)) := by
    unfold eval; grind
  rw [e, Int.add_mul_emod_self_left]

/-- Transfer of a statement about residues checked on `Fin n × Fin n` (by `decide`) to all
integers `0 ≤ r, t < n`. -/
theorem of_fin {n : Nat} {P : Int → Int → Prop} (h : ∀ r t : Fin n, P (r.val : Int) (t.val : Int))
    {r t : Int} (hr0 : 0 ≤ r) (hr : r < n) (ht0 : 0 ≤ t) (ht : t < n) : P r t := by
  have := h ⟨r.toNat, by omega⟩ ⟨t.toNat, by omega⟩
  simp only at this
  rwa [Int.toNat_of_nonneg hr0, Int.toNat_of_nonneg ht0] at this

/-- Residues of `x² + 5y²` modulo 4 lie in `{0, 1, 2}`. -/
theorem principal20_mod4 (x y : Int) :
    (eval ⟨1, 0, 5⟩ x y) % 4 = 0 ∨ (eval ⟨1, 0, 5⟩ x y) % 4 = 1 ∨ (eval ⟨1, 0, 5⟩ x y) % 4 = 2 := by
  rw [eval_emod]
  exact of_fin (P := fun r t => (eval ⟨1, 0, 5⟩ r t) % 4 = 0 ∨ (eval ⟨1, 0, 5⟩ r t) % 4 = 1 ∨
    (eval ⟨1, 0, 5⟩ r t) % 4 = 2) (by decide) (Int.emod_nonneg _ (by decide))
    (Int.emod_lt_of_pos _ (by decide)) (Int.emod_nonneg _ (by decide))
    (Int.emod_lt_of_pos _ (by decide))

/-- Residues of `x² + 5y²` modulo 5 lie in `{0, 1, 4}` (the squares mod 5). -/
theorem principal20_mod5 (x y : Int) :
    (eval ⟨1, 0, 5⟩ x y) % 5 = 0 ∨ (eval ⟨1, 0, 5⟩ x y) % 5 = 1 ∨ (eval ⟨1, 0, 5⟩ x y) % 5 = 4 := by
  rw [eval_emod]
  exact of_fin (P := fun r t => (eval ⟨1, 0, 5⟩ r t) % 5 = 0 ∨ (eval ⟨1, 0, 5⟩ r t) % 5 = 1 ∨
    (eval ⟨1, 0, 5⟩ r t) % 5 = 4) (by decide) (Int.emod_nonneg _ (by decide))
    (Int.emod_lt_of_pos _ (by decide)) (Int.emod_nonneg _ (by decide))
    (Int.emod_lt_of_pos _ (by decide))

/-- Residues of `2x² + 2xy + 3y²` modulo 4 lie in `{0, 2, 3}`; so its odd values are
`≡ 3 (mod 4)`. -/
theorem nonprincipal20_mod4 (x y : Int) :
    (eval ⟨2, 2, 3⟩ x y) % 4 = 0 ∨ (eval ⟨2, 2, 3⟩ x y) % 4 = 2 ∨ (eval ⟨2, 2, 3⟩ x y) % 4 = 3 := by
  rw [eval_emod]
  exact of_fin (P := fun r t => (eval ⟨2, 2, 3⟩ r t) % 4 = 0 ∨ (eval ⟨2, 2, 3⟩ r t) % 4 = 2 ∨
    (eval ⟨2, 2, 3⟩ r t) % 4 = 3) (by decide) (Int.emod_nonneg _ (by decide))
    (Int.emod_lt_of_pos _ (by decide)) (Int.emod_nonneg _ (by decide))
    (Int.emod_lt_of_pos _ (by decide))

/-- `x² + 5y²` as the evaluation of the form `(1, 0, 5)`. -/
theorem eval_principal20 (x y : Int) : eval ⟨1, 0, 5⟩ x y = x * x + 5 * y * y := by
  unfold eval; simp only; grind

/-- An odd prime other than 5: `p mod 2 = 1` and `5 ∤ p`. -/
theorem prime_odd_ne5 {p : Nat} (hp : Arith.Prime p) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    p % 2 = 1 ∧ p % 5 ≠ 0 := by
  constructor
  · apply Classical.byContradiction; intro h
    rcases hp.2 2 (Nat.dvd_of_mod_eq_zero (by omega)) with h' | h' <;> omega
  · intro h
    rcases hp.2 5 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega

/-- **Lagrange's criterion applied to `x² + 5y²`.** If a prime `p` is `x² + 5y²` then `−20` is
a square modulo `4p`. -/
theorem neg20_square_of_rep {p : Nat} (hp : Arith.Prime p) {x y : Int}
    (h : x * x + 5 * y * y = p) : ∃ b : Int, 4 * (p : Int) ∣ b * b - (-20) :=
  (prime_rep_iff hp (-20)).1 ⟨⟨1, 0, 5⟩, by decide, x, y, by rw [eval_principal20, h]⟩

/-- **Primes of the form x² + 5y².** If an odd prime `p ≠ 5` is `x² + 5y²`, then
`p ≡ 1 or 9 (mod 20)`. -/
theorem prime_x2_5y2_mod20 {p : Nat} (hp : Arith.Prime p) (h2 : p ≠ 2) (h5 : p ≠ 5) {x y : Int}
    (h : x * x + 5 * y * y = p) : p % 20 = 1 ∨ p % 20 = 9 := by
  obtain ⟨hodd, h5'⟩ := prime_odd_ne5 hp h2 h5
  have m4 := principal20_mod4 x y
  have m5 := principal20_mod5 x y
  rw [eval_principal20, h] at m4 m5
  omega

/-- **A converse via h(−20) = 2.** If a prime `p ≡ 1, 9 (mod 20)` has `−20` a square modulo
`4p`, then `p = x² + 5y²` for some integers `x, y`. -/
theorem rep_x2_5y2_of_square {p : Nat} (hp : Arith.Prime p) (hmod : p % 20 = 1 ∨ p % 20 = 9)
    (hsq : ∃ b : Int, 4 * (p : Int) ∣ b * b - (-20)) : ∃ x y : Int, x * x + 5 * y * y = p := by
  obtain ⟨b, k, hk⟩ := hsq
  have hp2 := hp.1
  let f : Form := ⟨p, b, k⟩
  have hd : f.disc = -20 := by show b * b - 4 * (p : Int) * k = -20; grind
  have hpd : f.PosDef := ⟨by rw [hd]; decide, by show (0 : Int) < p; omega⟩
  have hrep : ∃ x y, f.eval x y = p := ⟨1, 0, by show (p : Int) * 1 * 1 + b * 1 * 0 + k * 0 * 0 = p; simp⟩
  rcases (classes_neg20 f hpd hd).1 with e | e
  · obtain ⟨x, y, hxy⟩ := e.represents.1 hrep
    exact ⟨x, y, by rw [← eval_principal20, hxy]⟩
  · obtain ⟨x, y, hxy⟩ := e.represents.1 hrep
    have := nonprincipal20_mod4 x y
    rw [hxy] at this
    omega

end Form

end Foundations.Langlands.Forms
