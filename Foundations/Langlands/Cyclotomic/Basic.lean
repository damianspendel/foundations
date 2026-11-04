import Foundations.Algebra
import Foundations.NumberTheory.Binomial

/-!
# Toward Langlands: tools for the cyclotomic story

Part XV begins with the oldest instance of what is now called the Langlands correspondence
for `GL(1)`: the arithmetic of the cyclotomic field `ℚ(ζ_p)`, where `ζ_p` is a primitive `p`-th
root of unity. Gauss met it twice. In the seventh section of the *Disquisitiones Arithmeticae*
(1801) he showed that the regular `17`-gon can be constructed with ruler and compass, by
splitting the roots of `x^17 - 1` into "periods" stable under the substitutions `ζ ↦ ζ^a`.
In 1808 he used the quadratic period, now called the **Gauss sum**
`g = Σ_a (a/p) ζ^a`, to give his sixth proof of the law of quadratic reciprocity. Kummer,
studying Fermat's last theorem in the 1840s, made `ℤ[ζ_p]` the main object of a new
arithmetic of ideals. The files of this chapter tell that story in the language of Galois
theory:

* `Gal(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)ˣ`, the residue `a` acting by `ζ ↦ ζ^a`;
* `g² = (-1/p) · p`, so `ℚ(ζ_p)` contains the square root of `p* = (-1)^((p-1)/2) p`;
* reducing modulo another prime `q`, the `q`-th power map (Frobenius) acts on `g` as the
  residue `q` does, and comparing two computations of `g^q` gives quadratic reciprocity.

This first file collects the elementary tools: finite sums `rsum` in a commutative ring and
their reindexing by multiplication modulo `p`, the **binomial theorem** with the
"freshman's dream" `(x + y)^q = x^q + y^q` in characteristic `q`, and three facts about the
Legendre symbol (it depends only on the residue, it is unchanged by square factors, and
it sums to zero over a full residue system).
-/

namespace Foundations.Langlands

open Foundations.Algebra
open Foundations.NumberTheory (choose choose_zero_right choose_succ_succ choose_eq_zero_of_lt
  choose_self choose_mul_fact)

universe u

/-! ## Finite sums -/

section Sums

variable {R : Type u} [CommRing R]

/-- **Sums of sums.** `Σ (sₖ + tₖ) = Σ sₖ + Σ tₖ`. -/
theorem rsum_add (s t : Nat → R) : ∀ n, rsum (fun k => s k + t k) n = rsum s n + rsum t n
  | 0 => by show (0 : R) = 0 + 0; grind
  | n + 1 => by
    show rsum (fun k => s k + t k) n + (s n + t n) = rsum s n + s n + (rsum t n + t n)
    rw [rsum_add s t n]; grind

/-- Scaling a sum on the right. -/
theorem rsum_mul (c : R) (t : Nat → R) (n : Nat) : rsum t n * c = rsum (fun k => t k * c) n := by
  rw [CommRing.mul_comm, mul_rsum]
  exact rsum_congr n fun k _ => CommRing.mul_comm _ _

/-- The sum of the negatives is the negative of the sum. -/
theorem rsum_neg (t : Nat → R) : ∀ n, rsum (fun k => -t k) n = -rsum t n
  | 0 => by show (0 : R) = -0; grind
  | n + 1 => by
    show rsum (fun k => -t k) n + -t n = -(rsum t n + t n)
    rw [rsum_neg t n]; grind

/-- **Interchanging a double sum.** -/
theorem rsum_comm (F : Nat → Nat → R) (m : Nat) :
    ∀ n, rsum (fun i => rsum (fun j => F i j) n) m = rsum (fun j => rsum (fun i => F i j) m) n
  | 0 => rsum_zero m fun _ _ => rfl
  | n + 1 => by
    show rsum (fun i => rsum (fun j => F i j) n + F i n) m = rsum _ n + rsum (fun i => F i n) m
    rw [rsum_add, rsum_comm F m n]

/-- A sum in which only the term at index `i` can be non-zero equals that term. -/
theorem rsum_single (t : Nat → R) {i : Nat} :
    ∀ n, i < n → (∀ k, k < n → k ≠ i → t k = 0) → rsum t n = t i
  | 0, h, _ => absurd h (Nat.not_lt_zero i)
  | n + 1, h, hz => by
    show rsum t n + t n = t i
    by_cases hi : i = n
    · subst hi
      rw [rsum_zero i fun k hk => hz k (by omega) (by omega), Ring.zero_add]
    · rw [rsum_single t n (by omega) fun k hk hki => hz k (by omega) hki, hz n (by omega)
        (Ne.symm hi), Ring.add_zero]

/-- A sum of a constant: `Σ_{k<n} c = n · c`. -/
theorem rsum_const (c : R) : ∀ n, rsum (fun _ => c) n = ((n : Int) : R) * c
  | 0 => by show (0 : R) = (((0 : Nat) : Int) : R) * c; grind
  | n + 1 => by
    show rsum (fun _ => c) n + c = (((n + 1 : Nat) : Int) : R) * c
    rw [rsum_const c n]; grind

/-- The list sum `l₀ + l₁ + ⋯` (an auxiliary notion for reindexing). -/
def lsumR (l : List R) : R := l.foldr (· + ·) 0

/-- The list sum of a concatenation. -/
theorem lsumR_append (l₁ l₂ : List R) : lsumR (l₁ ++ l₂) = lsumR l₁ + lsumR l₂ := by
  induction l₁ with
  | nil => show lsumR l₂ = 0 + lsumR l₂; grind
  | cons a l ih =>
    show a + lsumR (l ++ l₂) = a + lsumR l + lsumR l₂
    rw [ih]; grind

/-- `rsum` as a list sum over `0, 1, …, n - 1`. -/
theorem rsum_eq_lsumR (t : Nat → R) : ∀ n, rsum t n = lsumR ((List.range n).map t)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, lsumR_append, ← rsum_eq_lsumR t n]
    show rsum t n + t n = rsum t n + (t n + 0)
    rw [Ring.add_zero]

/-- **Reindexing a sum** by a map `e` that permutes `0, …, n - 1`. -/
theorem rsum_reindex (t : Nat → R) (n : Nat) (e : Nat → Nat)
    (hperm : ((List.range n).map e).Perm (List.range n)) :
    rsum (fun k => t (e k)) n = rsum t n := by
  rw [rsum_eq_lsumR, rsum_eq_lsumR,
    show (List.range n).map (fun k => t (e k)) = ((List.range n).map e).map t by
      rw [List.map_map]; rfl]
  exact List.Perm.foldr_eq' (hperm.map t) (fun _ _ _ _ _ => by grind) 0

/-- Multiplication by a unit modulo `p` permutes the residues `0, …, p - 1`. -/
theorem perm_mul_mod {p a b : Nat} (hp : 0 < p) (hab : a * b % p = 1) :
    ((List.range p).map (fun k => a * k % p)).Perm (List.range p) := by
  have hinv : ∀ k, k < p → a * (b * k % p) % p = k := by
    intro k hk
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_mod, hab,
      Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hk]
  have hinj : ∀ i j, i < p → j < p → a * i % p = a * j % p → i = j := by
    intro i j hi hj h
    have e1 : b * (a * i % p) % p = i := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm b a,
        Nat.mul_mod, hab, Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hi]
    have e2 : b * (a * j % p) % p = j := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm b a,
        Nat.mul_mod, hab, Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hj]
    rw [← e1, ← e2, h]
  rw [List.perm_ext_iff_of_nodup _ List.nodup_range]
  · intro x
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨k, _, rfl⟩; exact Nat.mod_lt _ hp
    · intro hx; exact ⟨b * x % p, Nat.mod_lt _ hp, hinv x hx⟩
  · unfold List.Nodup
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range (n := p)).imp_of_mem fun {i j} hi hj hij e =>
      absurd (hinj i j (List.mem_range.1 hi) (List.mem_range.1 hj) e) (Nat.ne_of_lt hij)

/-- **Reindexing by multiplication modulo `p`.** If `a b ≡ 1 (mod p)`, then
`Σ_{k<p} t(a k mod p) = Σ_{k<p} t(k)`. -/
theorem rsum_mul_mod (t : Nat → R) {p a b : Nat} (hp : 0 < p) (hab : a * b % p = 1) :
    rsum (fun k => t (a * k % p)) p = rsum t p :=
  rsum_reindex t p _ (perm_mul_mod hp hab)

/-- Casting a sum of integers into a ring. -/
theorem intCast_rsum (t : Nat → Int) : ∀ n, ((rsum t n : Int) : R) = rsum (fun k => (t k : R)) n
  | 0 => Lean.Grind.Ring.intCast_zero
  | n + 1 => by
    show ((rsum t n + t n : Int) : R) = rsum _ n + _
    rw [Lean.Grind.Ring.intCast_add, intCast_rsum t n]

/-- A ring homomorphism commutes with powers. -/
theorem RingHom.map_pow' {A : Type u} {B : Type u} [CommRing A] [CommRing B] (φ : RingHom A B)
    (x : A) : ∀ n : Nat, φ.toFun (x ^ n) = φ.toFun x ^ n
  | 0 => φ.map_one
  | n + 1 => by
    show φ.toFun (x ^ n * x) = φ.toFun x ^ n * φ.toFun x
    rw [φ.map_mul, RingHom.map_pow' φ x n]

end Sums

/-! ## Powers -/

section Powers

variable {R : Type u} [CommRing R]

/-- `x^(m+n) = x^m x^n`. -/
theorem pow_add' (x : R) (m n : Nat) : x ^ (m + n) = x ^ m * x ^ n := rpow_add x m n

/-- `x^(mn) = (x^m)^n`. -/
theorem pow_mul' (x : R) (m n : Nat) : x ^ (m * n) = (x ^ m) ^ n := rpow_mul' x m n

/-- `(xy)^n = x^n y^n`. -/
theorem mul_pow' (x y : R) (n : Nat) : (x * y) ^ n = x ^ n * y ^ n := mul_rpow' x y n

/-- `1^n = 1`. -/
theorem one_pow' (n : Nat) : (1 : R) ^ n = 1 := one_rpow' n

/-- If `ζ^p = 1`, powers of `ζ` only depend on the exponent modulo `p`. -/
theorem pow_mod_of_pow_eq_one {ζ : R} {p : Nat} (h : ζ ^ p = 1) (k : Nat) :
    ζ ^ k = ζ ^ (k % p) := by
  conv => lhs; rw [← Nat.div_add_mod k p]
  rw [pow_add', pow_mul', h, one_pow', Ring.one_mul]

end Powers

/-! ## The binomial theorem and the freshman's dream -/

section Binomial

variable {R : Type u} [CommRing R]

/-- The `k`-th term `C(n, k) xᵏ y^{n-k}` of the binomial expansion of `(x + y)ⁿ`. -/
def bterm (x y : R) (n k : Nat) : R := ((choose n k : Int) : R) * (x ^ k * y ^ (n - k))

/-- **The binomial theorem.** `(x + y)ⁿ = Σ_{k ≤ n} C(n, k) xᵏ y^{n-k}`. -/
theorem binomial_theorem (x y : R) : ∀ n, (x + y) ^ n = rsum (bterm x y n) (n + 1)
  | 0 => by
    show (1 : R) = 0 + ((choose 0 0 : Int) : R) * (x ^ 0 * y ^ 0)
    rw [choose_zero_right]; show (1 : R) = 0 + (((1 : Nat) : Int) : R) * (1 * 1); grind
  | n + 1 => by
    have hshift : ∀ k, k < n + 1 → bterm x y (n + 1) (k + 1) =
        x * bterm x y n k + y * bterm x y n (k + 1) := by
      intro k hk
      unfold bterm
      rw [choose_succ_succ]
      rcases Nat.lt_or_ge k n with hkn | hkn
      · rw [show n + 1 - (k + 1) = (n - (k + 1)) + 1 by omega, show n - k = (n - (k + 1)) + 1 by
          omega]
        show _ * (x ^ k * x * (y ^ (n - (k + 1)) * y)) =
          x * (_ * (x ^ k * (y ^ (n - (k + 1)) * y))) + y * (_ * (x ^ k * x * _))
        grind
      · have hk' : k = n := by omega
        subst hk'
        rw [choose_eq_zero_of_lt (Nat.lt_succ_self k), Nat.sub_self, Nat.sub_self]
        show _ * (x ^ k * x * 1) = x * (_ * (x ^ k * 1)) + y * (((0 : Nat) : Int) * (x ^ k * x * _))
        grind
    have h0 : bterm x y (n + 1) 0 = y * bterm x y n 0 := by
      unfold bterm; rw [choose_zero_right, choose_zero_right]
      show (((1 : Nat) : Int) : R) * (1 * (y ^ n * y)) = y * ((((1 : Nat) : Int) : R) * (1 * y ^ n))
      grind
    have htop : rsum (fun k => bterm x y n (k + 1)) (n + 1) =
        rsum (fun k => bterm x y n (k + 1)) n := by
      show rsum _ n + bterm x y n (n + 1) = _
      unfold bterm; rw [choose_eq_zero_of_lt (Nat.lt_succ_self n)]
      show _ + (((0 : Nat) : Int) : R) * _ = _
      grind
    have hfull : rsum (bterm x y n) (n + 1) = bterm x y n 0 +
        rsum (fun k => bterm x y n (k + 1)) n := rsum_succ' _ n
    have hR : rsum (bterm x y (n + 1)) (n + 1 + 1) = bterm x y (n + 1) 0 +
        rsum (fun k => bterm x y (n + 1) (k + 1)) (n + 1) := rsum_succ' _ (n + 1)
    rw [hR, rsum_congr _ hshift, rsum_add, ← mul_rsum, ← mul_rsum, h0, htop,
      show (x + y) ^ (n + 1) = (x + y) ^ n * (x + y) from rfl, binomial_theorem x y n, hfull]
    grind

/-- Factorials below a prime are prime to it. -/
theorem not_dvd_fact {p : Nat} (hp : IsPrime p) : ∀ m, m < p → ¬ p ∣ Foundations.Numbers.Arith.fact m
  | 0, _, h => by
    have h1 : p ∣ 1 := h
    have := Nat.le_of_dvd (by decide) h1; have := hp.1; omega
  | m + 1, hm, h => by
    rcases hp.dvd_mul h with h1 | h1
    · have := Nat.le_of_dvd (by omega) h1; omega
    · exact not_dvd_fact hp m (by omega) h1

/-- **`p` divides `C(p, k)` for `0 < k < p`.** From `C(p, k) · k! · (p - k)! = p!`: the prime `p`
divides `p!` but neither factorial on the left. -/
theorem prime_dvd_choose {p k : Nat} (hp : IsPrime p) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ choose p k := by
  have h := choose_mul_fact p k (p - k) (by omega)
  have hpf : p ∣ Foundations.Numbers.Arith.fact p := by
    obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
    rw [hm]; exact ⟨Foundations.Numbers.Arith.fact m, rfl⟩
  rw [← h] at hpf
  rcases hp.dvd_mul hpf with h1 | h1
  · rcases hp.dvd_mul h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_dvd_fact hp k hkp)
  · exact absurd h1 (not_dvd_fact hp (p - k) (by omega))

/-- **The freshman's dream.** In a commutative ring in which the prime `q` is zero,
`(x + y)^q = x^q + y^q`: the middle binomial coefficients are multiples of `q`. -/
theorem add_pow_char {q : Nat} (hq : IsPrime q) (hq0 : ((q : Int) : R) = 0) (x y : R) :
    (x + y) ^ q = x ^ q + y ^ q := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by have := hq.1; omega⟩
  have hmid : ∀ k, k < m → bterm x y (m + 1) (k + 1) = 0 := by
    intro k hk
    obtain ⟨c, hc⟩ := prime_dvd_choose hq (k := k + 1) (by omega) (by omega)
    unfold bterm
    rw [hc, Int.natCast_mul, Lean.Grind.Ring.intCast_mul, hq0]
    grind
  rw [binomial_theorem, rsum_succ']
  show _ + (rsum _ m + bterm x y (m + 1) (m + 1)) = _
  rw [rsum_zero m hmid]
  unfold bterm
  rw [choose_zero_right, choose_self, Nat.sub_self, Nat.sub_zero]
  show (((1 : Nat) : Int) : R) * (1 * _) + (0 + (((1 : Nat) : Int) : R) * (_ * 1)) = _
  grind

/-- **Frobenius is additive on finite sums.** If `q` is a prime with `q = 0` in `R`, then
`(Σ tₖ)^q = Σ tₖ^q`. -/
theorem rsum_pow_char {q : Nat} (hq : IsPrime q) (hq0 : ((q : Int) : R) = 0) (t : Nat → R) :
    ∀ n, (rsum t n) ^ q = rsum (fun k => t k ^ q) n
  | 0 => by
    obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by have := hq.1; omega⟩
    rw [hm]; show rpow (0 : R) (m + 1) = 0; exact zero_rpow_succ m
  | n + 1 => by
    show (rsum t n + t n) ^ q = rsum _ n + t n ^ q
    rw [add_pow_char hq hq0, rsum_pow_char hq hq0 t n]

end Binomial

/-! ## The Legendre symbol as a function of residues -/

section Legendre

variable {p : Nat}

/-- The Legendre symbol only depends on the residue: `(a mod p / p) = (a/p)`. -/
theorem legendre_mod (a p : Nat) : legendre (a % p) p = legendre a p := by
  classical
  unfold legendre
  have h1 : p ∣ a % p ↔ p ∣ a := by
    constructor
    · intro h; rw [← Nat.div_add_mod a p]; exact Nat.dvd_add (Nat.dvd_mul_right p _) h
    · intro h; rw [Nat.mod_eq_zero_of_dvd h]; exact Nat.dvd_zero p
  have h2 : IsQR (a % p) p ↔ IsQR a p := by
    unfold IsQR; rw [Nat.mod_mod]
  simp only [h1, h2]

/-- The Legendre symbol of a multiple of `p` is `0`. -/
theorem legendre_of_dvd {a : Nat} (h : p ∣ a) : legendre a p = 0 := by
  classical
  unfold legendre; simp [h]

/-- `(a/p)² = 1` for `p ∤ a`. -/
theorem legendre_sq (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (ha : ¬ p ∣ a) :
    legendre a p * legendre a p = 1 := by
  rcases legendre_cases hp hodd ha with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> rfl

/-- The Legendre symbol takes only the values `0, 1, -1`. -/
theorem legendre_values (hp : IsPrime p) (hodd : p % 2 = 1) (a : Nat) :
    legendre a p = 0 ∨ legendre a p = 1 ∨ legendre a p = -1 := by
  by_cases ha : p ∣ a
  · exact Or.inl (legendre_of_dvd ha)
  · rcases legendre_cases hp hodd ha with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- Square factors prime to `p` do not change the Legendre symbol: `(a² c/p) = (c/p)`. -/
theorem legendre_sq_mul (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (ha : ¬ p ∣ a) (c : Nat) :
    legendre (a * a * c) p = legendre c p := by
  rw [legendre_mul hp hodd, legendre_mul hp hodd, legendre_sq hp hodd ha, Int.one_mul]

/-- **A quadratic non-residue exists** modulo every odd prime: otherwise all `p - 1` non-zero
residues would be roots of `x^((p-1)/2) - 1` in the field `ℤ/pℤ`. -/
theorem exists_nonresidue (hp : IsPrime p) (hodd : p % 2 = 1) :
    ∃ n, 0 < n ∧ n < p ∧ legendre n p = -1 := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ c, 0 < c → c < p → c ^ half p % p = 1 := by
    intro c hc0 hcp
    have hc : ¬ p ∣ c := fun h => by have := Nat.le_of_dvd hc0 h; omega
    rcases legendre_cases hp hodd hc with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd ⟨c, hc0, hcp, h⟩ hno
  have ⟨_, h1, h3⟩ := half_spec hp hodd
  haveI : NeZero p := ⟨by omega⟩
  have hF : IsField (Fin p) := (fin_isField_iff_prime p).2 hp
  have hD := hF.isDomain
  let h := half p
  let f : Polynomial (Fin p) := Polynomial.Xpow h + -Polynomial.C 1
  have hXpow : ∀ n, Polynomial.coeff (Polynomial.Xpow h : Polynomial (Fin p)) n =
      if h ≤ n then (if n - h = 0 then 1 else 0) else 0 := by
    intro n
    rw [← Ring.mul_one (Polynomial.Xpow h), Polynomial.coeff_Xpow_mul, ← Polynomial.C_one,
      Polynomial.coeff_C]
  have hcoef : ∀ n, Polynomial.coeff f n =
      (if h ≤ n then (if n - h = 0 then 1 else 0) else 0) + -(if n = 0 then 1 else 0) := by
    intro n
    show Polynomial.coeff (Polynomial.Xpow h + -Polynomial.C 1) n = _
    rw [Polynomial.coeff_add, Polynomial.coeff_neg, hXpow, Polynomial.coeff_C]
  have hdeg : Polynomial.DegLT f (h + 1) := by
    intro n hn
    rw [hcoef, ite_true_of (by omega : h ≤ n), ite_false_of (by omega : ¬ n - h = 0),
      ite_false_of (by omega : ¬ n = 0), Ring.neg_zero, Ring.add_zero]
  have hf0 : f ≠ 0 := by
    intro hf
    have := hcoef h
    rw [hf, Polynomial.coeff_zero, ite_true_of (Nat.le_refl h), ite_true_of (Nat.sub_self h),
      ite_false_of (by omega : ¬ h = 0), Ring.neg_zero, Ring.add_zero] at this
    exact hF.1 this
  let L : List (Fin p) := (List.range (p - 1)).map (fun k => Fin.ofNat p (k + 1))
  have hnd : L.Nodup := by
    unfold List.Nodup L
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range (n := p - 1)).imp_of_mem fun {i j} hi hj hij e => ?_
    have := congrArg Fin.val e
    rw [Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt (by have := List.mem_range.1 hi; omega),
      Nat.mod_eq_of_lt (by have := List.mem_range.1 hj; omega)] at this
    omega
  have hroots : ∀ x, x ∈ L → Polynomial.eval x f = 0 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hk
    show Polynomial.eval _ (Polynomial.Xpow h + -Polynomial.C 1) = 0
    rw [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_C]
    have : Polynomial.eval (Fin.ofNat p (k + 1)) (Polynomial.Xpow h) = 1 := by
      apply Fin.ext
      rw [eval_Xpow_val, Fin.val_ofNat, Nat.mod_eq_of_lt (show k + 1 < p by omega),
        hall (k + 1) (by omega) (by omega)]
      show 1 = (Fin.ofNat p 1).val
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [this, Ring.add_neg_cancel]
  have := Polynomial.card_roots_le hD L h f hf0 hdeg hnd hroots
  simp [L] at this
  omega

/-- **The Legendre symbol sums to zero** over a full system of residues:
`Σ_{c<p} (c/p) = 0`. (Multiplying by a non-residue `n` permutes the residues and changes the
sign of the sum.) -/
theorem legendre_sum (hp : IsPrime p) (hodd : p % 2 = 1) :
    rsum (fun c => legendre c p) p = 0 := by
  obtain ⟨n, hn0, hnp, hn⟩ := exists_nonresidue hp hodd
  have hp0 : 0 < p := by have := hp.1; omega
  have hnd : ¬ p ∣ n := fun h => by have := Nat.le_of_dvd hn0 h; omega
  -- an inverse of `n` modulo `p`, by Fermat
  have hinv : n * n ^ (p - 2) % p = 1 := by
    rw [show n * n ^ (p - 2) = n ^ (p - 1) by
      rw [show p - 1 = (p - 2) + 1 by have := hp.1; omega, Nat.pow_succ, Nat.mul_comm]]
    exact fermat p n hp hnd
  have h1 := rsum_mul_mod (fun c => legendre c p) hp0 hinv
  have h2 : rsum (fun k => legendre (n * k % p) p) p = rsum (fun c => -legendre c p) p :=
    rsum_congr p fun k _ => by rw [legendre_mod, legendre_mul hp hodd, hn]; omega
  rw [h2, rsum_neg] at h1
  show rsum (fun c => legendre c p) p = 0
  generalize rsum (fun c => legendre c p) p = S at h1
  have : -S = S := h1
  omega

end Legendre

end Foundations.Langlands
