import Foundations.Algebra.QuinticGalois

/-!
# Roots of unity and pure equations `yⁿ = c`

To say what "solving by radicals" means we must be able to take `n`-th roots, and to understand
how the symmetries of a field act on such roots we must know how many there are and how they
are related. This file collects the needed facts, first in any field and then in `ℂ`.

* **Powers.** Elementary laws for natural-number powers `rpow x n = xⁿ` in a commutative ring:
  `x^{mn} = (x^m)^n`, `(xy)ⁿ = xⁿ yⁿ`, and the fact that ring homomorphisms (in particular field
  automorphisms) preserve powers.
* **The binomial `x^{n+1} - c`.** An explicit polynomial with leading coefficient `1`; the root
  bound of `PolyDivision` gives it at most `n + 1` roots, and the fundamental theorem of algebra
  gives it a root in `ℂ`. So **every complex number has an `n`-th root** (`exists_rpow_eq`).
* **Roots of unity of prime order.** For a prime `p`, the factorisation
  `x^p - 1 = (x - 1)(1 + x + ⋯ + x^{p-1})` and the fundamental theorem of algebra give a complex
  `ζ ≠ 1` with `ζ^p = 1` (`exists_root_of_unity`); the value `p ≠ 0` of the second factor at
  `x = 1` is where characteristic zero enters. In any field such a `ζ` has order exactly `p`,
  since the exponents `k` with `ζ^k = 1` are closed under `gcd`, so `1, ζ, …, ζ^{p-1}` are `p`
  distinct roots of `x^p - 1`, and by the root bound they are **all** of them
  (`eq_rpow_of_rpow_eq_one`).
* **Kummer's observation.** Consequently, if `x ≠ 0`, every `y` with `y^p = x^p` is `ζ^k x` for some
  `k` (`eq_mul_of_rpow_eq`): two `p`-th roots of the same number differ by a root of unity.

We work with prime exponents only. The general radical `ⁿ√c` is reached through a chain of
prime roots, because `n = p · m` gives `ⁿ√c = ᵐ√(ᵖ√c)`; this reduction is carried out in
`NormalClosure`.
-/

namespace Foundations.Algebra

open Polynomial

universe u

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Laws of powers -/

section Powers

variable {R : Type u} [CommRing R]

/-- `x¹ = x`. -/
theorem rpow_one' (x : R) : rpow x 1 = x := Ring.one_mul x

/-- `1ⁿ = 1`. -/
theorem one_rpow' (n : Nat) : rpow (1 : R) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => show rpow (1 : R) n * 1 = 1; rw [ih, Ring.mul_one]

/-- `0^{n+1} = 0`. -/
theorem zero_rpow_succ (n : Nat) : rpow (0 : R) (n + 1) = 0 := Ring.mul_zero _

/-- **Powers multiply**: `x^{mn} = (x^m)^n`. -/
theorem rpow_mul' (x : R) (m n : Nat) : rpow x (m * n) = rpow (rpow x m) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, rpow_add, ih]; rfl

/-- **Powers of products**: `(xy)ⁿ = xⁿ yⁿ`. -/
theorem mul_rpow' (x y : R) (n : Nat) : rpow (x * y) n = rpow x n * rpow y n := by
  induction n with
  | zero => exact (Ring.mul_one 1).symm
  | succ n ih =>
    show rpow (x * y) n * (x * y) = rpow x n * x * (rpow y n * y)
    rw [ih]; ac_rfl

/-- **Ring homomorphisms preserve powers.** -/
theorem RingHom.map_rpow {A : Type u} {B : Type u} [CommRing A] [CommRing B] (φ : RingHom A B)
    (x : A) (n : Nat) : φ.toFun (rpow x n) = rpow (φ.toFun x) n := by
  induction n with
  | zero => exact φ.map_one
  | succ n ih => show φ.toFun (rpow x n * x) = rpow (φ.toFun x) n * φ.toFun x; rw [φ.map_mul, ih]

/-- Powers in a subfield are computed as in the ambient ring. -/
theorem Subfield.coe_rpow {Ω : Type u} [CommRing Ω] (K : Subfield Ω) (x : K) (n : Nat) :
    (rpow x n).1 = rpow x.1 n := by
  induction n with
  | zero => rfl
  | succ n ih => show (rpow x n).1 * x.1 = rpow x.1 n * x.1; rw [ih]

/-- **Field automorphisms preserve powers.** -/
theorem FieldAut.map_rpow {Ω : Type u} [CommRing Ω] {K L : Subfield Ω} (σ : FieldAut K L) (x : L)
    (n : Nat) : σ.toFun (rpow x n) = rpow (σ.toFun x) n :=
  RingHom.map_rpow σ.toRingHom x n

/-- In an integral domain a power vanishes only if the base does. -/
theorem eq_zero_of_rpow_eq_zero (hD : IsDomain R) {x : R} : ∀ {n : Nat}, rpow x n = 0 → x = 0
  | 0, h => absurd h.symm hD.1
  | n + 1, h => by
    rcases hD.2 _ _ h with h' | h'
    · exact eq_zero_of_rpow_eq_zero hD h'
    · exact h'

end Powers

/-! ## The binomial `x^{n+1} - c` and the geometric sum -/

section Binomial

variable {R : Type u} [CommRing R]

/-- **The binomial** `x^{n+1} - c`, as the coefficient list `[-c, 0, …, 0, 1]`. -/
def binomial (c : R) (n : Nat) : Polynomial R := mk (-c :: (List.replicate n 0 ++ [1]))

/-- `0 + 0·x + ⋯ + 0·x^{n-1} + xⁿ` evaluates to `xⁿ`. -/
theorem evalList_monomial (x : R) : ∀ n : Nat, evalList x (List.replicate n 0 ++ [1]) = rpow x n
  | 0 => by show (1 : R) + x * 0 = 1; rw [Ring.mul_zero, Ring.add_zero]
  | n + 1 => by
    show (0 : R) + x * evalList x (List.replicate n 0 ++ [1]) = rpow x n * x
    rw [evalList_monomial x n, Ring.zero_add, CommRing.mul_comm]

/-- The `n`-th coefficient of `[0, …, 0, 1]` (with `n` zeros) is `1`. -/
theorem coeff_monomial_list : ∀ n : Nat, PolyList.coeff (List.replicate n (0 : R) ++ [1]) n = 1
  | 0 => rfl
  | n + 1 => coeff_monomial_list n

/-- Evaluating the binomial: `x^{n+1} - c`. -/
theorem eval_binomial (c x : R) (n : Nat) : eval x (binomial c n) = rpow x (n + 1) + -c := by
  show -c + x * evalList x (List.replicate n 0 ++ [1]) = rpow x n * x + -c
  rw [evalList_monomial]; grind

/-- The leading coefficient of `x^{n+1} - c` is `1`. -/
theorem coeff_binomial (c : R) (n : Nat) : coeff (binomial c n) (n + 1) = 1 :=
  coeff_monomial_list n

/-- `x^{n+1} - c` has degree less than `n + 2`. -/
theorem degLT_binomial (c : R) (n : Nat) : DegLT (binomial c n) (n + 2) := by
  intro k hk
  apply PolyList.coeff_of_length_le
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

/-- The binomial is a non-zero polynomial (in a non-trivial ring). -/
theorem binomial_ne_zero (h01 : (0 : R) ≠ 1) (c : R) (n : Nat) : binomial c n ≠ 0 := by
  intro h
  have := coeff_binomial c n
  rw [h] at this
  exact h01 this

/-- The geometric sum `1 + x + ⋯ + x^{n-1}` evaluated at `x`, times `x - 1`, is `xⁿ - 1`. -/
theorem geom_identity (x : R) : ∀ n : Nat,
    (x + -1) * evalList x (List.replicate n 1) = rpow x n + -1
  | 0 => by show (x + -1) * 0 = 1 + -1; grind
  | n + 1 => by
    have ih := geom_identity x n
    show (x + -1) * (1 + x * evalList x (List.replicate n 1)) = rpow x n * x + -1
    grind

/-- The geometric sum `1 + 1 + ⋯ + 1` (`n` terms) at `x = 1` is `n`. -/
theorem geom_at_one : ∀ n : Nat, evalList (1 : R) (List.replicate n 1) = ncast n
  | 0 => rfl
  | n + 1 => by
    show (1 : R) + 1 * evalList 1 (List.replicate n 1) = ncast (n + 1)
    rw [geom_at_one n, ncast_succ]; grind

/-- The coefficients of `1 + x + ⋯ + x^{n-1}` below `n` are `1`. -/
theorem coeff_geom_list : ∀ (n k : Nat), k < n → PolyList.coeff (List.replicate n (1 : R)) k = 1
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, k + 1, h => coeff_geom_list n k (by omega)

end Binomial

/-! ## Orders of roots of unity in a field -/

section Order

variable {F : Type u} [CommRing F]

/-- **Exponents of `1` are closed under `gcd`.** If `x^a = 1` and `x^b = 1` then
`x^{gcd(a, b)} = 1` (Euclid's algorithm on the exponents). -/
theorem rpow_gcd_eq_one {x : F} {a b : Nat} (ha : rpow x a = 1) (hb : rpow x b = 1) :
    rpow x (Nat.gcd a b) = 1 := by
  induction a, b using Nat.gcd.induction with
  | H0 n => rw [Nat.gcd_zero_left]; exact hb
  | H1 m n hm ih =>
    rw [Nat.gcd_rec]
    apply ih _ ha
    have e := Nat.div_add_mod n m
    rw [← e, rpow_add, rpow_mul', ha, one_rpow', Ring.one_mul] at hb
    exact hb

/-- A `p`-th root of unity `ζ ≠ 1` (`p` prime) satisfies `ζ^k ≠ 1` for `0 < k < p`: its order
is exactly `p`. -/
theorem rpow_ne_one_of_lt {p : Nat} (hp : IsPrime p) {ζ : F} (hζp : rpow ζ p = 1) (hζ1 : ζ ≠ 1)
    {k : Nat} (hk0 : 0 < k) (hkp : k < p) : rpow ζ k ≠ 1 := by
  intro hk
  have hg := rpow_gcd_eq_one hk hζp
  rcases hp.2 _ (Nat.gcd_dvd_right k p) with h1 | h1
  · rw [h1, rpow_one'] at hg; exact hζ1 hg
  · have := Nat.gcd_le_left p hk0; omega

variable (hF : IsField F)
include hF

/-- **Distinct powers.** For a primitive `p`-th root of unity `ζ`, the powers
`ζ⁰, ζ¹, …, ζ^{p-1}` are pairwise distinct. -/
theorem rpow_injective_of_lt {p : Nat} (hp : IsPrime p) {ζ : F} (hζp : rpow ζ p = 1) (hζ1 : ζ ≠ 1)
    {i j : Nat} (hi : i < p) (hj : j < p) (h : rpow ζ i = rpow ζ j) : i = j := by
  have hD := hF.isDomain
  have hζ0 : ζ ≠ 0 := by
    intro h0; rw [h0] at hζp
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.1; omega⟩
    rw [hq, zero_rpow_succ] at hζp; exact hD.1 hζp
  have key : ∀ a b, a < b → b < p → rpow ζ a = rpow ζ b → False := by
    intro a b hab hb e
    have e2 : rpow ζ b = rpow ζ a * rpow ζ (b - a) := by rw [← rpow_add]; congr 1; omega
    rw [e2] at e
    have : rpow ζ a * (rpow ζ (b - a) + -1) = 0 := by grind
    rcases hD.2 _ _ this with h0 | h0
    · exact hζ0 (eq_zero_of_rpow_eq_zero hD h0)
    · exact rpow_ne_one_of_lt hp hζp hζ1 (k := b - a) (by omega) (by omega) (by grind)
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact (key i j h' hj h).elim
  · exact h'
  · exact (key j i h' hi h.symm).elim

/-- **All `p`-th roots of unity are powers of one of them.** If `ζ ≠ 1` and `ζ^p = 1` (`p`
prime), every `ω` with `ω^p = 1` equals `ζ^k` for some `k < p`: the `p` distinct powers of `ζ`
already exhaust the at most `p` roots of `x^p - 1`. -/
theorem eq_rpow_of_rpow_eq_one {p : Nat} (hp : IsPrime p) {ζ : F} (hζp : rpow ζ p = 1)
    (hζ1 : ζ ≠ 1) {ω : F} (hω : rpow ω p = 1) : ∃ k, k < p ∧ ω = rpow ζ k := by
  have hD := hF.isDomain
  apply Classical.byContradiction
  intro hne
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.1; omega⟩
  let Lst : List F := ω :: (List.range (q + 1)).map (rpow ζ)
  have hnd : Lst.Nodup := by
    rw [List.nodup_cons]
    constructor
    · intro hmem
      obtain ⟨k, hk, hk'⟩ := List.mem_map.1 hmem
      exact hne ⟨k, List.mem_range.1 hk, hk'.symm⟩
    · unfold List.Nodup
      rw [List.pairwise_map]
      exact (List.pairwise_lt_range (n := q + 1)).imp_of_mem fun {a b} ha hb hab e =>
        absurd (rpow_injective_of_lt hF hp hζp hζ1 (List.mem_range.1 ha) (List.mem_range.1 hb) e)
          (Nat.ne_of_lt hab)
  have hroots : ∀ a, a ∈ Lst → eval a (binomial 1 q) = 0 := by
    intro a ha
    rw [eval_binomial]
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [hω]; grind
    · obtain ⟨k, _, rfl⟩ := List.mem_map.1 ha
      rw [← rpow_mul', Nat.mul_comm, rpow_mul', hζp, one_rpow']; grind
  have := card_roots_le hD Lst (q + 1) (binomial 1 q) (binomial_ne_zero hD.1 1 q)
    (degLT_binomial 1 q) hnd hroots
  simp [Lst] at this
  omega

/-- **Two `p`-th roots of the same number differ by a root of unity.** If `x ≠ 0` and
`y^p = x^p`, then `y = ζ^k · x` for some `k`. -/
theorem eq_mul_of_rpow_eq {p : Nat} (hp : IsPrime p) {ζ : F} (hζp : rpow ζ p = 1) (hζ1 : ζ ≠ 1)
    {x y : F} (hx : x ≠ 0) (h : rpow y p = rpow x p) : ∃ k, y = rpow ζ k * x := by
  obtain ⟨b, hb⟩ := hF.2 x hx
  have hω : rpow (y * b) p = 1 := by
    rw [mul_rpow', h, ← mul_rpow', hb, one_rpow']
  obtain ⟨k, _, hk⟩ := eq_rpow_of_rpow_eq_one hF hp hζp hζ1 hω
  refine ⟨k, ?_⟩
  rw [← hk]
  calc y = y * (x * b) := by rw [hb, Ring.mul_one]
    _ = y * b * x := by ac_rfl

end Order

/-! ## Existence in `ℂ` -/

/-- **Every complex number has an `n`-th root** (`n ≥ 1`), by the fundamental theorem of
algebra applied to `x^n - c`. -/
theorem exists_rpow_eq (c : ℂ) {n : Nat} (hn : 0 < n) : ∃ y : ℂ, rpow y n = c := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hc : coeff (binomial c k) (k + 1) ≠ 0 := by
    rw [coeff_binomial]; exact fun h => C.isField.1 h.symm
  obtain ⟨y, hy⟩ := C.fta' (binomial c k) (by omega) hc
  refine ⟨y, ?_⟩
  rw [eval_binomial] at hy
  grind

/-- **Roots of unity of prime order exist in `ℂ`.** For every prime `p` there is a complex
number `ζ ≠ 1` with `ζ^p = 1`: a root of `1 + x + ⋯ + x^{p-1}`, which is not `1` because that
polynomial takes the value `p ≠ 0` at `1`. -/
theorem exists_root_of_unity {p : Nat} (hp : IsPrime p) : ∃ ζ : ℂ, rpow ζ p = 1 ∧ ζ ≠ 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.1; omega⟩
  have hc : coeff (mk (List.replicate (q + 2) (1 : ℂ))) (q + 1) ≠ 0 := by
    show PolyList.coeff _ _ ≠ 0
    rw [coeff_geom_list (q + 2) (q + 1) (by omega)]; exact fun h => C.isField.1 h.symm
  obtain ⟨ζ, hζ⟩ := C.fta' _ (by omega) hc
  have hζ' : evalList ζ (List.replicate (q + 2) 1) = 0 := hζ
  refine ⟨ζ, ?_, ?_⟩
  · have := geom_identity ζ (q + 2)
    rw [hζ', Ring.mul_zero] at this
    grind
  · intro h1
    rw [h1, geom_at_one] at hζ'
    exact C.ncast_succ_ne_zero (q + 1) hζ'

end Foundations.Algebra
