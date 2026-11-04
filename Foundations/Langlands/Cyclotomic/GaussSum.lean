import Foundations.Langlands.Cyclotomic.Basic
import Foundations.NumberTheory.Characters

/-!
# Gauss sums

Let `p` be an odd prime and `ζ` a `p`-th root of unity. The **quadratic Gauss sum** is

  `g = Σ_{a=0}^{p-1} (a/p) ζ^a`,

the sum of the quadratic residues' powers of `ζ` minus the non-residues' powers. Gauss
introduced it in the *Disquisitiones* (1801, art. 356), where he showed that `g² = ±p`, and he
spent four years (1801–1805) proving his conjecture about the *sign* of `g` when `ζ = e^{2πi/p}`:
`g = √p` for `p ≡ 1 (mod 4)` and `g = i√p` for `p ≡ 3 (mod 4)`. In 1808 he used `g` for his
sixth proof of quadratic reciprocity, the proof formalised in the next file. We prove the
square, not the sign.

**Theorem.** If `ζ^p = 1` and `1 + ζ + ⋯ + ζ^{p-1} = 0`, then
`g² = (-1/p) · p = p*`, where `p* = (-1)^((p-1)/2) p`.

The proof is a computation in any commutative ring. Multiplying `(a/p) ζ^a` by `g` and
substituting `b = a c` turns the double sum into `Σ_c (c/p) Σ_a ζ^{a(1+c)}`. The inner sum is
`p` when `c ≡ -1` and `0` otherwise, because multiplication by a unit permutes the
exponents. Only `c = p - 1` survives, leaving `(-1/p) · p`. The fact that the Legendre symbol
sums to zero over all residues (proved in the previous file) is what handles the term
`a = 0`.

Working in an abstract ring pays off twice. For `ζ = e^{2πi/p}` in `ℂ` it shows that the
square root of `p*` lies in `ℚ(ζ_p)`, the first glimpse of the fact (Kronecker–Weber) that
abelian extensions of `ℚ` live inside cyclotomic fields. In the next file the same identity is
used in a ring of characteristic `q`, where the Frobenius map acts on `g`.
-/

namespace Foundations.Langlands

open Foundations.Algebra

universe u

/-- The integer `p* = (-1)^((p-1)/2) p`: `p` if `p ≡ 1 (mod 4)` and `-p` if `p ≡ 3 (mod 4)`. -/
def pstar (p : Nat) : Int := (-1) ^ half p * (p : Int)

/-- **Inverses modulo a prime, by Fermat.** If `p ∤ a` then `a · a^(p-2) ≡ 1 (mod p)`. -/
theorem mul_inv_mod {p a : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) : a * a ^ (p - 2) % p = 1 := by
  rw [show a * a ^ (p - 2) = a ^ (p - 1) by
    rw [show p - 1 = (p - 2) + 1 by have := hp.1; omega, Nat.pow_succ, Nat.mul_comm]]
  exact fermat p a hp ha

section Generic

variable {R : Type u} [CommRing R]

/-- **The quadratic Gauss sum** `g = Σ_{a<p} (a/p) ζ^a` attached to an element `ζ` of a
commutative ring. -/
noncomputable def gaussSum (p : Nat) (ζ : R) : R :=
  rsum (fun a => ((legendre a p : Int) : R) * ζ ^ a) p

variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) {ζ : R} (hζ : ζ ^ p = 1)
  (hN : rsum (fun j => ζ ^ j) p = 0)

include hp hζ hN in
/-- **Orthogonality for roots of unity.** If `ζ^p = 1` and `Σ_{j<p} ζ^j = 0`, then
`Σ_{k<p} ζ^{mk}` is `p` when `p ∣ m` and `0` otherwise. -/
theorem rsum_root_pow (m : Nat) :
    rsum (fun k => ζ ^ (m * k)) p = if p ∣ m then (((p : Nat) : Int) : R) else 0 := by
  by_cases hm : p ∣ m
  · rw [ite_true_of hm]
    have : ∀ k, k < p → ζ ^ (m * k) = 1 := by
      intro k _
      rw [pow_mod_of_pow_eq_one hζ, Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd hm k)]
      rfl
    rw [rsum_congr p this, rsum_const]; grind
  · rw [ite_false_of hm]
    have hp0 : 0 < p := by have := hp.1; omega
    rw [← hN, ← rsum_mul_mod (fun j => ζ ^ j) hp0 (mul_inv_mod hp hm)]
    exact rsum_congr p fun k _ => pow_mod_of_pow_eq_one hζ _

include hp hodd hζ in
/-- **The Gauss sum is an eigenvector of `ζ ↦ ζ^a`.** If `ζ^p = 1` and `p ∤ a`, replacing `ζ` by
`ζ^a` in the Gauss sum multiplies it by `(a/p)`:
`Σ_b (b/p) (ζ^a)^b = (a/p) · g`. -/
theorem gaussSum_twist {a : Nat} (hpa : ¬ p ∣ a) :
    rsum (fun b => ((legendre b p : Int) : R) * (ζ ^ a) ^ b) p =
      ((legendre a p : Int) : R) * gaussSum p ζ := by
  have hp0 : 0 < p := by have := hp.1; omega
  have h1 : ∀ b, b < p → ((legendre b p : Int) : R) * (ζ ^ a) ^ b =
      ((legendre b p : Int) : R) * ζ ^ (a * b % p) := by
    intro b _
    rw [← pow_mul', pow_mod_of_pow_eq_one hζ (a * b)]
  rw [rsum_congr p h1]
  unfold gaussSum
  rw [mul_rsum, ← rsum_mul_mod (fun b => ((legendre a p : Int) : R) *
    (((legendre b p : Int) : R) * ζ ^ b)) hp0 (mul_inv_mod hp hpa)]
  apply rsum_congr; intro b _
  show _ = ((legendre a p : Int) : R) * (((legendre (a * b % p) p : Int) : R) * ζ ^ (a * b % p))
  rw [legendre_mod, legendre_mul hp hodd, Lean.Grind.Ring.intCast_mul]
  have hsq := legendre_sq hp hodd hpa
  have : ((legendre a p : Int) : R) * ((legendre a p : Int) : R) = 1 := by
    rw [← Lean.Grind.Ring.intCast_mul, hsq]; exact Lean.Grind.Ring.intCast_one
  grind

include hp hodd hζ in
/-- **The twisting step.** For every residue `a`, `(a/p) ζ^a · g = Σ_c (c/p) ζ^{a(1+c)}`. For
`p ∤ a` this is the substitution `b = a c`; for `a = 0` both sides vanish. -/
theorem legendre_mul_gaussSum {a : Nat} (ha : a < p) :
    ((legendre a p : Int) : R) * ζ ^ a * gaussSum p ζ =
      rsum (fun c => ((legendre c p : Int) : R) * ζ ^ (a * (1 + c))) p := by
  have hp0 : 0 < p := by have := hp.1; omega
  by_cases ha0 : a = 0
  · subst ha0
    rw [legendre_of_dvd (Nat.dvd_zero p)]
    have : ∀ c, c < p → ((legendre c p : Int) : R) * ζ ^ (0 * (1 + c)) =
        ((legendre c p : Int) : R) := fun c _ => by rw [Nat.zero_mul]; exact Ring.mul_one _
    rw [rsum_congr p this, ← intCast_rsum, legendre_sum hp hodd]
    show ((0 : Int) : R) * 1 * _ = ((0 : Int) : R)
    grind
  have hpa : ¬ p ∣ a := fun h => ha0 (Nat.eq_zero_of_dvd_of_lt h ha)
  -- expand the product
  let F : Nat → R := fun b => ((legendre (a * b) p : Int) : R) * ζ ^ (a + b)
  have h1 : ((legendre a p : Int) : R) * ζ ^ a * gaussSum p ζ = rsum F p := by
    unfold gaussSum; rw [mul_rsum]
    apply rsum_congr; intro b _
    show _ = ((legendre (a * b) p : Int) : R) * ζ ^ (a + b)
    rw [legendre_mul hp hodd, Lean.Grind.Ring.intCast_mul, pow_add']
    grind
  -- substitute `b = a c mod p`
  rw [h1, ← rsum_mul_mod F hp0 (mul_inv_mod hp hpa)]
  apply rsum_congr; intro c _
  show ((legendre (a * (a * c % p)) p : Int) : R) * ζ ^ (a + a * c % p) = _
  have e1 : legendre (a * (a * c % p)) p = legendre c p := by
    rw [← legendre_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, legendre_mod, ← Nat.mul_assoc,
      legendre_sq_mul hp hodd hpa]
  have e2 : ζ ^ (a + a * c % p) = ζ ^ (a * (1 + c)) := by
    rw [pow_mod_of_pow_eq_one hζ (a + a * c % p), pow_mod_of_pow_eq_one hζ (a * (1 + c)),
      Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mul_add, Nat.mul_one]
  rw [e1, e2]

include hp hodd hζ hN in
/-- **Gauss's theorem on the square of the Gauss sum.** If `ζ^p = 1` and
`1 + ζ + ⋯ + ζ^{p-1} = 0` in a commutative ring, then `g² = (-1/p) · p = p*`. -/
theorem gaussSum_sq : gaussSum p ζ * gaussSum p ζ = ((pstar p : Int) : R) := by
  have hp0 : 0 < p := by have := hp.1; omega
  have h3 := hp.1
  -- `g · g = Σ_a (a/p) ζ^a g = Σ_a Σ_c (c/p) ζ^{a(1+c)}`
  have h1 : gaussSum p ζ * gaussSum p ζ =
      rsum (fun a => rsum (fun c => ((legendre c p : Int) : R) * ζ ^ (a * (1 + c))) p) p := by
    conv => lhs; arg 1; unfold gaussSum
    rw [rsum_mul]
    exact rsum_congr p fun a ha => legendre_mul_gaussSum hp hodd hζ ha
  rw [h1, rsum_comm]
  -- the inner sums are orthogonality sums
  have h2 : ∀ c, c < p → rsum (fun a => ((legendre c p : Int) : R) * ζ ^ (a * (1 + c))) p =
      ((legendre c p : Int) : R) * (if p ∣ 1 + c then (((p : Nat) : Int) : R) else 0) := by
    intro c _
    rw [← mul_rsum, ← rsum_root_pow hp hζ hN (1 + c)]
    congr 1; apply rsum_congr; intro a _; rw [Nat.mul_comm]
  rw [rsum_congr p h2, rsum_single _ (i := p - 1) p (by omega)]
  · rw [ite_true_of (by rw [show 1 + (p - 1) = p by omega]; exact Nat.dvd_refl p),
      legendre_neg_one hp hodd]
    unfold pstar
    rw [Lean.Grind.Ring.intCast_mul]
  · intro c hc hcp
    rw [ite_false_of (fun h => hcp (by
      have := Nat.le_of_dvd (by omega) h
      rcases Nat.lt_or_ge (1 + c) p with h' | h'
      · omega
      · omega))]
    exact Ring.mul_zero _

end Generic

/-! ## The Gauss sum in `ℂ` -/

section Complex

open Foundations.NumberTheory

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-- The two notions of power on `ℂ` (from the field structure used in analysis and from the
algebraic ring structure) agree. -/
theorem C.pow_eq_rpow (z : ℂ) : ∀ n : Nat, z ^ n = rpow z n
  | 0 => rfl
  | n + 1 => by
    show z ^ n * z = rpow z n * z
    rw [C.pow_eq_rpow z n]

/-- Sums over `0, …, m-1` in `ℂ`: the list sum of `Characters` agrees with `rsum`. -/
theorem C.lsum_range_eq_rsum (f : Nat → ℂ) : ∀ m, lsum (List.range m) f = rsum f m
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, lsum_append, C.lsum_range_eq_rsum f m]
    show rsum f m + (f m + 0) = rsum f m + f m
    rw [Ring.add_zero]

/-- `ζ_p^p = 1` for the primitive `p`-th root of unity `ζ_p = e^{2πi/p}`. -/
theorem zeta_rpow_self {p : Nat} (hp : 1 ≤ p) : rpow (zeta p) p = 1 := by
  rw [← C.pow_eq_rpow]; exact zeta_pow_self hp

/-- `1 + ζ_p + ⋯ + ζ_p^{p-1} = 0` for `p ≥ 2`. -/
theorem rsum_zeta_pow {p : Nat} (hp : 2 ≤ p) : rsum (fun j => rpow (zeta p) j) p = 0 := by
  have := lsum_zeta_pow (m := p) (by omega) 1
  rw [ite_false_of (fun h => by have := Nat.le_of_dvd (by decide) h; omega)] at this
  rw [← this, C.lsum_range_eq_rsum]
  apply rsum_congr; intro j _
  rw [C.pow_eq_rpow, C.pow_eq_rpow, ← rpow_mul', Nat.mul_one]

/-- **Gauss's theorem in `ℂ`.** For an odd prime `p` and `ζ_p = e^{2πi/p}`, the Gauss sum
`g = Σ_a (a/p) ζ_p^a` satisfies `g² = p* = (-1)^((p-1)/2) p`. So `g` is a square root of `p*`
built from `p`-th roots of unity. (The integer `p*` is cast into `ℂ` by the ring-theoretic
cast `icast`.) -/
theorem gaussSum_sq_complex {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) :
    gaussSum p (zeta p) * gaussSum p (zeta p) = icast (pstar p) :=
  gaussSum_sq hp hodd (zeta_rpow_self (by have := hp.1; omega))
    (rsum_zeta_pow hp.1)

end Complex

end Foundations.Langlands
