import Foundations.Langlands.Cyclotomic.GaussSum
import Foundations.Langlands.Cyclotomic.CyclotomicPoly

/-!
# Quadratic reciprocity from Gauss sums: Frobenius at work

In 1808 Gauss published his sixth proof of the law of quadratic reciprocity
(*Theorematis fundamentalis in doctrina de residuis quadraticis demonstrationes et
ampliationes novae*). It rests on the Gauss sum `g = Σ_a (a/p) ζ^a`, whose square is
`p* = (-1)^((p-1)/2) p`, and on a congruence modulo a second odd prime `q`. In modern language
the proof is about **Frobenius**. In characteristic `q` the map `x ↦ x^q` is a ring
homomorphism. On the roots of unity it acts as `ζ ↦ ζ^q`, which is the Galois automorphism
`σ_q` of `ℚ(ζ_p)` attached to the residue `q`. Computing `g^q` in two ways gives:

* `g^q = Σ_a (a/p) ζ^{aq} = (q/p) · g`, because Frobenius acts as `σ_q` and `σ_q` multiplies
  `g` by `(q/p)`;
* `g^q = g · (g²)^((q-1)/2) = g · (p*)^((q-1)/2) ≡ (p*/q) · g`, by Euler's criterion.

Since `g² = p*` is invertible modulo `q`, it follows that `(q/p) = (p*/q)`, which is
quadratic reciprocity. The theorem has become a statement about how the Frobenius element at
`q` acts on the quadratic subfield `ℚ(√p*)` of `ℚ(ζ_p)`. That is the shape of Artin's
reciprocity law (1927), the general form of class field theory: for an abelian extension of
`ℚ`, the Frobenius element at a prime depends only on the prime modulo the conductor. Langlands
reformulated this as a correspondence between characters of the Galois group and
automorphic representations of `GL(1)`, then conjectured analogues for `GL(n)`.

**Where to compute modulo `q`.** We need a ring of characteristic `q` containing a
`p`-th root of unity `ζ` with `1 + ζ + ⋯ + ζ^{p-1} = 0`. We take

  `A = 𝔽_q[x] / (Φ_p)`, with `ζ` the class of `x`.

(This ring is isomorphic to `ℤ[ζ_p]/(q)`, but we neither need nor prove that.) Then
`ζ^p = 1` because `(x - 1) Φ_p = x^p - 1`, and the general Gauss-sum identity of the previous
file gives `g² = p*` in `A`. Finally `𝔽_q` embeds in `A`, because `Φ_p` has positive degree
and so is not a unit. That is all we need to cancel `g` and read off a congruence between
integers.

**Headlines.** `frobenius_gaussSum` (`g^q = (q/p) g` in `A`), `gaussSum_pow_char`
(`g^q = (p*)^((q-1)/2) g`), `legendre_eq_pstar_pow_mod` (`(q/p) ≡ (p*)^((q-1)/2) (mod q)`), and
`quadratic_reciprocity_gauss`, the law itself, proved independently of Eisenstein's
lattice-point proof in `Algebra/Reciprocity.lean`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial

universe u

/-! ## Integers in `ℤ/qℤ` -/

section FinCast

variable {q : Nat} [NeZero q]

/-- The image of `n` in `ℤ/qℤ` is `n mod q`. -/
theorem fin_ncast_val : ∀ n : Nat, (ncast n : Fin q).val = n % q
  | 0 => by show (Fin.ofNat q 0).val = 0 % q; rw [Fin.val_ofNat]
  | 1 => by show (Fin.ofNat q 1).val = 1 % q; rw [Fin.val_ofNat]
  | n + 2 => by
    show ((ncast (n + 1) : Fin q) + Fin.ofNat q 1).val = (n + 2) % q
    rw [Fin.val_add, fin_ncast_val (n + 1), Fin.val_ofNat, ← Nat.add_mod]

/-- An integer whose image in `ℤ/qℤ` vanishes is divisible by `q`. -/
theorem dvd_of_fin_icast_eq_zero {z : Int} (h : (icast z : Fin q) = 0) : (q : Int) ∣ z := by
  match z, h with
  | .ofNat n, h =>
    have h1 : (ncast n : Fin q).val = (0 : Fin q).val := congrArg Fin.val h
    rw [fin_ncast_val] at h1
    have h2 : n % q = 0 := by rw [h1]; rfl
    exact Int.ofNat_dvd.2 (Nat.dvd_of_mod_eq_zero h2)
  | .negSucc n, h =>
    have h0 : (ncast (n + 1) : Fin q) = 0 := by
      have : -(ncast (n + 1) : Fin q) = 0 := h
      rw [← Ring.neg_neg (ncast (n + 1) : Fin q), this, Ring.neg_zero]
    have h1 : (ncast (n + 1) : Fin q).val = (0 : Fin q).val := congrArg Fin.val h0
    rw [fin_ncast_val] at h1
    have h2 : (n + 1) % q = 0 := by rw [h1]; rfl
    have h3 : (q : Int) ∣ ((n + 1 : Nat) : Int) := Int.ofNat_dvd.2 (Nat.dvd_of_mod_eq_zero h2)
    show (q : Int) ∣ -((n + 1 : Nat) : Int)
    exact (Int.dvd_neg).2 h3

/-- `q` is zero in `ℤ/qℤ`. -/
theorem fin_icast_self : (icast (q : Int) : Fin q) = 0 := by
  apply Fin.ext
  show (ncast q : Fin q).val = (0 : Fin q).val
  rw [fin_ncast_val, Nat.mod_self]; rfl

end FinCast

/-! ## The ring `𝔽_q[x]/(Φ_p)` -/

section ResRing

variable (q p : Nat) [NeZero q]

/-- The principal ideal `(Φ_p)` of `𝔽_q[x]`. -/
def cycloIdeal : Ideal (Polynomial (Fin q)) := Ideal.span (cyclo (Fin q) p)

/-- **The ring `A = 𝔽_q[x]/(Φ_p)`**, a ring of characteristic `q` in which the class of `x` is a
`p`-th root of unity. -/
abbrev ResRing : Type := QuotientRing (cycloIdeal q p)

/-- The class `ζ` of `x` in `𝔽_q[x]/(Φ_p)`. -/
def zetaRes : ResRing q p := QuotientRing.mk (cycloIdeal q p) X

/-- The structure map `𝔽_q → 𝔽_q[x]/(Φ_p)`, sending `c` to the class of the constant `c`. -/
def constHom : RingHom (Fin q) (ResRing q p) := RingHom.comp (QuotientRing.proj (cycloIdeal q p)) CHom

variable {q p}

/-- `1 + ζ + ⋯ + ζ^{p-1} = 0` in `𝔽_q[x]/(Φ_p)`: it is the class of `Φ_p`. -/
theorem rsum_zetaRes : rsum (fun j => zetaRes q p ^ j) p = 0 := by
  have h : (QuotientRing.proj (cycloIdeal q p)).toFun (cyclo (Fin q) p) = 0 :=
    QuotientRing.mk_eq_zero.2 ⟨1, (Ring.one_mul _).symm⟩
  rw [cyclo_eq_rsum, RingHom.map_rsum] at h
  rw [← h]
  apply rsum_congr; intro j _
  rw [RingHom.map_pow']; rfl

/-- `ζ^p = 1` in `𝔽_q[x]/(Φ_p)`. -/
theorem zetaRes_pow : zetaRes q p ^ p = 1 := by
  have h := geom_sum_mul (zetaRes q p) p
  rw [rsum_zetaRes, Ring.mul_zero] at h
  grind

/-- `q = 0` in `𝔽_q[x]/(Φ_p)`. -/
theorem resRing_char : (((q : Nat) : Int) : ResRing q p) = 0 := by
  have := RingHom.map_intCast (constHom q p) (q : Int)
  rw [← this]
  show (constHom q p).toFun (icast (q : Int)) = 0
  rw [fin_icast_self]; exact (constHom q p).map_zero

variable (hq : IsPrime q) (hp : 2 ≤ p)
include hq hp

/-- `𝔽_q[x]/(Φ_p)` is not the zero ring (for `p ≥ 2`): `Φ_p` has positive degree, so it is not
a unit of `𝔽_q[x]`. -/
theorem resRing_nontrivial : (0 : ResRing q p) ≠ 1 := by
  intro h
  have hF : IsField (Fin q) := (fin_isField_iff_prime q).2 hq
  have h1 : (1 : Polynomial (Fin q)) ∈ cycloIdeal q p := by
    apply QuotientRing.mk_eq_zero.1
    exact h.symm
  obtain ⟨r, hr⟩ := h1
  exact cyclo_not_isUnit hF.isDomain hp ⟨r, by rw [CommRing.mul_comm]; exact hr.symm⟩

/-- **Integers modulo `q` inside `A`.** An integer that vanishes in `𝔽_q[x]/(Φ_p)` is
divisible by `q`: the field `𝔽_q` embeds into `A`. -/
theorem dvd_of_resRing_eq_zero {z : Int} (h : ((z : Int) : ResRing q p) = 0) : (q : Int) ∣ z := by
  have hF : IsField (Fin q) := (fin_isField_iff_prime q).2 hq
  apply dvd_of_fin_icast_eq_zero
  apply RingHom.eq_zero_of_isField hF (resRing_nontrivial hq hp) (constHom q p)
  rw [show (icast z : Fin q) = Int.cast z from rfl, RingHom.map_intCast]
  exact h

end ResRing

/-! ## Two computations of `g^q` -/

section Frobenius

variable {R : Type u} [CommRing R]

/-- Integer casts commute with powers. -/
theorem intCast_pow (z : Int) : ∀ n : Nat, ((z ^ n : Int) : R) = (z : R) ^ n
  | 0 => by rw [Int.pow_zero]; exact Lean.Grind.Ring.intCast_one
  | n + 1 => by
    rw [Int.pow_succ, Lean.Grind.Ring.intCast_mul, intCast_pow z n]; rfl

/-- `ε^q = ε` for `ε ∈ {0, 1, -1}` and odd `q`. -/
theorem sign_pow_odd {ε : Int} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {q : Nat} (hq : q % 2 = 1) :
    ε ^ q = ε := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  rcases hε with rfl | rfl | rfl
  · rw [Int.pow_succ, Int.mul_zero]
  · exact Int.one_pow
  · rw [neg_one_pow_int, ite_false_of (by omega)]

variable {p q : Nat} (hp : IsPrime p) (hpo : p % 2 = 1) (hq : IsPrime q) (hqo : q % 2 = 1)
  (hpq : p ≠ q) {ζ : R} (hζ : ζ ^ p = 1) (hN : rsum (fun j => ζ ^ j) p = 0)
  (hchar : (((q : Nat) : Int) : R) = 0)

include hp hpo hq hqo hpq hζ hchar in
/-- **Frobenius acts on the Gauss sum as the residue `q`.** In a commutative ring of
characteristic `q` containing a `p`-th root of unity `ζ`, the Gauss sum satisfies
`g^q = (q/p) · g`: the `q`-th power map sends `ζ^a` to `ζ^{qa}` and the substitution
`a ↦ qa` multiplies the Legendre symbol by `(q/p)`. -/
theorem frobenius_gaussSum_general :
    gaussSum p ζ ^ q = ((legendre q p : Int) : R) * gaussSum p ζ := by
  have hpq' : ¬ p ∣ q := fun h => by
    rcases hq.2 p h with h1 | h1
    · have := hp.1; omega
    · exact hpq h1
  rw [← gaussSum_twist hp hpo hζ hpq']
  unfold gaussSum
  rw [rsum_pow_char hq hchar]
  apply rsum_congr; intro a _
  rw [mul_pow', ← intCast_pow, sign_pow_odd (legendre_values hp hpo a) hqo, ← pow_mul',
    ← pow_mul', Nat.mul_comm]

include hp hpo hqo hζ hN in
/-- **The second computation of `g^q`.** Since `g² = p*`, `g^q = g · (p*)^((q-1)/2)`. -/
theorem gaussSum_pow_odd :
    gaussSum p ζ ^ q = (((pstar p) ^ half q : Int) : R) * gaussSum p ζ := by
  obtain ⟨h, rfl⟩ : ∃ h, q = 2 * h + 1 := ⟨q / 2, by omega⟩
  have hh : half (2 * h + 1) = h := by unfold half; omega
  rw [hh, intCast_pow, ← gaussSum_sq hp hpo hζ hN, pow_add', pow_mul']
  have e2 : gaussSum p ζ ^ 2 = gaussSum p ζ * gaussSum p ζ := by
    show 1 * gaussSum p ζ * gaussSum p ζ = _; rw [Ring.one_mul]
  have e1 : gaussSum p ζ ^ 1 = gaussSum p ζ := by
    show 1 * gaussSum p ζ = _; rw [Ring.one_mul]
  rw [e2, e1]

include hp hpo hq hqo hpq hζ hN hchar in
/-- **Comparing the two computations.** `p* · ((q/p) - (p*)^((q-1)/2)) = 0` in `R`. -/
theorem pstar_mul_sub_eq_zero :
    ((pstar p * (legendre q p - (pstar p) ^ half q) : Int) : R) = 0 := by
  have e1 := frobenius_gaussSum_general hp hpo hq hqo hpq hζ hchar
  rw [gaussSum_pow_odd hp hpo hqo hζ hN] at e1
  have e2 := gaussSum_sq hp hpo hζ hN
  have : gaussSum p ζ * (gaussSum p ζ * ((legendre q p : Int) : R)) =
      gaussSum p ζ * (gaussSum p ζ * (((pstar p) ^ half q : Int) : R)) := by grind
  rw [← Ring.mul_assoc, ← Ring.mul_assoc, e2] at this
  rw [Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_sub]
  grind

end Frobenius

/-! ## The law of quadratic reciprocity -/

section Law

variable {p q : Nat} (hp : IsPrime p) (hpo : p % 2 = 1) (hq : IsPrime q) (hqo : q % 2 = 1)
  (hpq : p ≠ q)

include hp hpo hq hqo hpq in
/-- **Frobenius on the Gauss sum modulo `q`.** In `A = 𝔽_q[x]/(Φ_p)`, with `ζ` the class of `x`,
the Gauss sum `g = Σ_a (a/p) ζ^a` satisfies `g^q = (q/p) · g`. -/
theorem frobenius_gaussSum [NeZero q] :
    gaussSum p (zetaRes q p) ^ q = ((legendre q p : Int) : ResRing q p) * gaussSum p (zetaRes q p) :=
  frobenius_gaussSum_general hp hpo hq hqo hpq zetaRes_pow resRing_char

include hp hpo hqo in
/-- **The Gauss sum to the power `q`.** In `A = 𝔽_q[x]/(Φ_p)`, `g^q = (p*)^((q-1)/2) · g`. -/
theorem gaussSum_pow_char [NeZero q] :
    gaussSum p (zetaRes q p) ^ q =
      (((pstar p) ^ half q : Int) : ResRing q p) * gaussSum p (zetaRes q p) :=
  gaussSum_pow_odd hp hpo hqo zetaRes_pow rsum_zetaRes

include hp hpo hq hqo hpq in
/-- **Gauss's congruence.** `(q/p) ≡ (p*)^((q-1)/2) (mod q)`, where
`p* = (-1)^((p-1)/2) p`. By Euler's criterion the right side is `(p*/q)`, so this is
quadratic reciprocity in the form `(q/p) = (p*/q)`. -/
theorem legendre_eq_pstar_pow_mod : (q : Int) ∣ legendre q p - (pstar p) ^ half q := by
  haveI : NeZero q := ⟨by have := hq.1; omega⟩
  have h := dvd_of_resRing_eq_zero hq hp.1
    (pstar_mul_sub_eq_zero hp hpo hq hqo hpq zetaRes_pow rsum_zetaRes resRing_char)
  -- `q ∤ p*`
  have hqp : ¬ (q : Int) ∣ pstar p := by
    intro hd
    have : (q : Int) ∣ (p : Int) := by
      unfold pstar at hd
      rw [neg_one_pow_int] at hd
      split at hd
      · rw [Int.one_mul] at hd; exact hd
      · rw [Int.neg_one_mul] at hd; exact Int.dvd_neg.1 hd
    have h' : q ∣ p := Int.ofNat_dvd.1 this
    rcases hp.2 q h' with h1 | h1
    · have := hq.1; omega
    · exact hpq h1.symm
  rcases int_prime_dvd_mul hq h with h1 | h1
  · exact absurd h1 hqp
  · exact h1

include hp hpo hq hqo hpq in
/-- **The law of quadratic reciprocity, via Gauss sums** (Gauss's sixth proof, 1808). For
distinct odd primes `p` and `q`, `(q/p) · (p/q) = (-1)^(((p-1)/2) · ((q-1)/2))`. -/
theorem quadratic_reciprocity_gauss :
    legendre q p * legendre p q = (-1) ^ (half p * half q) := by
  have hcong := legendre_eq_pstar_pow_mod hp hpo hq hqo hpq
  have hqp : ¬ q ∣ p := fun h => by
    rcases hp.2 q h with h1 | h1
    · have := hq.1; omega
    · exact hpq h1.symm
  have hpq' : ¬ p ∣ q := fun h => by
    rcases hq.2 p h with h1 | h1
    · have := hp.1; omega
    · exact hpq h1
  have hq3 : 3 ≤ q := by have := hq.1; omega
  -- `(p*)^((q-1)/2) = (-1)^(hp·hq) · p^((q-1)/2)`, and `p^((q-1)/2) ≡ (p/q)` (Euler)
  have hps : (pstar p) ^ half q = (-1) ^ (half p * half q) * ((p ^ half q : Nat) : Int) := by
    unfold pstar
    rw [Int.mul_pow, ← Int.pow_mul, Int.natCast_pow]
  obtain ⟨k, hk⟩ : ∃ k : Int, ((p ^ half q : Nat) : Int) = legendre p q + q * k := by
    rcases legendre_cases hq hqo hqp with ⟨hl, he⟩ | ⟨hl, he⟩
    · refine ⟨((p ^ half q / q : Nat) : Int), ?_⟩
      have := Nat.div_add_mod (p ^ half q) q
      rw [he] at this; rw [hl]; omega
    · refine ⟨((p ^ half q / q : Nat) : Int) + 1, ?_⟩
      have := Nat.div_add_mod (p ^ half q) q
      rw [he] at this; rw [hl]
      have : (((p ^ half q) : Nat) : Int) = q * ((p ^ half q / q : Nat) : Int) + (q - 1 : Nat) := by
        omega
      rw [this, Int.mul_add, Int.mul_one]
      omega
  rw [hps, hk] at hcong
  -- now `q ∣ (q/p) - s · (p/q)` up to a multiple of `q`, with `s = ±1`
  have hsgn : ((-1 : Int) ^ (half p * half q) = 1 ∨ (-1 : Int) ^ (half p * half q) = -1) := by
    rw [neg_one_pow_int]; split <;> simp
  have hl1 := legendre_cases hp hpo hpq'
  have hl2 := legendre_cases hq hqo hqp
  have hd : (q : Int) ∣ legendre q p - (-1) ^ (half p * half q) * legendre p q := by
    have : legendre q p - (-1) ^ (half p * half q) * (legendre p q + q * k) =
        (legendre q p - (-1) ^ (half p * half q) * legendre p q) -
          q * ((-1) ^ (half p * half q) * k) := by
      rw [Int.mul_add]; grind
    rw [this] at hcong
    have := Int.dvd_add hcong (Int.dvd_mul_right (q : Int) ((-1) ^ (half p * half q) * k))
    rwa [Int.sub_add_cancel] at this
  -- a difference of two signs divisible by an odd prime vanishes
  have heq : legendre q p = (-1) ^ (half p * half q) * legendre p q := by
    obtain ⟨c, hc⟩ := hd
    rcases hsgn with hs | hs <;> rw [hs] at hc ⊢ <;>
      rcases hl1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases hl2 with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hc ⊢ <;> first
        | rfl
        | (exfalso
           have hc' : (q : Int) * c = 2 ∨ (q : Int) * c = -2 := by omega
           rcases hc' with hc' | hc'
           · have : (q : Int) ∣ 2 := ⟨c, hc'.symm⟩
             have := Int.le_of_dvd (by decide) this; omega
           · have : (q : Int) ∣ 2 := ⟨-c, by rw [Int.mul_neg, hc']; rfl⟩
             have := Int.le_of_dvd (by decide) this; omega)
  rw [heq, Int.mul_assoc, legendre_sq hq hqo hqp, Int.mul_one]

end Law

end Foundations.Langlands
