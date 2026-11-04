import Foundations.Langlands.Cyclotomic.PrimePowerDegree
import Foundations.Langlands.Cyclotomic.Degree

/-!
# Monic polynomials, Gauss's lemma, and separability of `xⁿ - 1`

This file collects the polynomial algebra needed for the irreducibility of every cyclotomic
polynomial `Φ_n` (Dedekind 1857, in the streamlined form of Landau and van der Waerden). None
of it mentions roots of unity in `ℂ`.

* **Monic polynomials.** `Monic f d` says that `f` has degree `≤ d` and coefficient `1` at
  `xᵈ`. Products of monic polynomials are monic, and over a domain a cofactor of a monic
  polynomial in a monic polynomial is monic.
* **Products of linear factors.** `prodLin L = ∏_{a ∈ L} (x - a)`. Over a domain, if the
  distinct elements of `L` are roots of `f` then `prodLin L ∣ f`
  (`prodLin_dvd`), and a non-constant divisor of `prodLin L` has a root in `L`
  (`exists_root_of_dvd_prodLin`).
* **Gauss's lemma for monic factors.** If a monic integer polynomial is the product of two
  monic rational polynomials, both have integer coefficients (`int_of_monic_factor`). The proof
  takes least common denominators `N, M` and shows `N M = 1`: a prime dividing `N M` would
  divide all coefficients of one of the two cleared factors, hence its leading coefficient,
  contradicting minimality.
* **Division by monic integer polynomials.** A monic integer polynomial dividing an integer
  polynomial over `ℚ` divides it over `ℤ` (`int_dvd_of_monic`).
* **Separability.** Over a field in which `n ≠ 0`, `xⁿ - 1` has no repeated factor:
  `π² ∣ xⁿ - 1` forces `π` to be a unit (`isUnit_of_sq_dvd_X_pow_sub_one`). Instead of a formal
  derivative we use the dual-number substitution `f(x) ↦ f(x + ε)` into `K[x][ε]`. Its
  `ε`-coefficient `c` of `xⁿ - 1` satisfies `x c = n xⁿ`, and a repeated factor `π` of `f`
  divides the `ε`-coefficient of `f(x + ε)`. So `π` divides `x c - n (xⁿ - 1) = n`, a unit.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

universe u

/-! ## Monic polynomials -/

section Monic

variable {R : Type u} [CommRing R]

/-- `f` is **monic of degree `d`**: all coefficients above `d` vanish and the coefficient at
`d` is `1`. -/
def Monic (f : Polynomial R) (d : Nat) : Prop := DegLT f (d + 1) ∧ coeff f d = 1

/-- The product of monic polynomials of degrees `d` and `e` is monic of degree `d + e`. -/
theorem Monic.mul {f g : Polynomial R} {d e : Nat} (hf : Monic f d) (hg : Monic g e) :
    Monic (f * g) (d + e) := by
  obtain ⟨h1, h2⟩ := mul_top hf.1 hg.1
  exact ⟨h2, by rw [h1, hf.2, hg.2, Ring.mul_one]⟩

/-- Mapping the coefficients of a monic polynomial gives a monic polynomial. -/
theorem Monic.map {S : Type u} [CommRing S] (φ : RingHom R S) {f : Polynomial R} {d : Nat}
    (hf : Monic f d) : Monic (mapPoly φ f) d :=
  ⟨degLT_mapPoly φ hf.1, by rw [coeff_mapPoly, hf.2]; exact φ.map_one⟩

/-- `x - a` is monic of degree `1`. -/
theorem monic_linear (a : R) : Monic (linear a) 1 := ⟨degLT_linear a, coeff_linear_one a⟩

/-- `1` is monic of degree `0`. -/
theorem monic_one : Monic (1 : Polynomial R) 0 :=
  ⟨fun n hn => by rw [coeff_one, ite_false_of (by omega)], by rw [coeff_one, ite_true_of rfl]⟩

/-- A monic polynomial of degree `d` has `natDegree` exactly `d` (in a non-zero ring). -/
theorem Monic.natDegree_eq (h01 : (0 : R) ≠ 1) {f : Polynomial R} {d : Nat} (hf : Monic f d) :
    natDegree f = d :=
  natDegree_eq_of hf.1 (by rw [hf.2]; exact fun h => h01 h.symm)

/-- A monic polynomial is non-zero (in a non-zero ring). -/
theorem Monic.ne_zero (h01 : (0 : R) ≠ 1) {f : Polynomial R} {d : Nat} (hf : Monic f d) :
    f ≠ 0 := fun h => h01 (by have := hf.2; rw [h, coeff_zero] at this; exact this)

/-- A monic polynomial of degree `0` is `1`. -/
theorem Monic.eq_one {f : Polynomial R} (hf : Monic f 0) : f = 1 := ext fun n => by
  rw [coeff_one]
  cases n with
  | zero => rw [ite_true_of rfl]; exact hf.2
  | succ n => rw [ite_false_of (by omega)]; exact hf.1 _ (by omega)

/-- **Monic cofactors.** Over a domain, if `f` is monic of degree `d`, `h` is monic of degree
`m` and `f g = h`, then `d ≤ m` and `g` is monic of degree `m - d`. -/
theorem Monic.of_mul (hD : IsDomain R) {f g h : Polynomial R} {d m : Nat} (hf : Monic f d)
    (hh : Monic h m) (hfg : f * g = h) : d ≤ m ∧ Monic g (m - d) := by
  have hf0 := hf.ne_zero hD.1
  have hg0 : g ≠ 0 := by
    intro e; rw [e, Ring.mul_zero] at hfg; exact hh.ne_zero hD.1 hfg.symm
  have hdeg := natDegree_mul hD hf0 hg0
  rw [hfg, hh.natDegree_eq hD.1, hf.natDegree_eq hD.1] at hdeg
  have hgd : DegLT g (m - d + 1) := by
    rw [show m - d + 1 = natDegree g + 1 by omega]; exact degLT_natDegree hg0
  refine ⟨by omega, hgd, ?_⟩
  have := (mul_top hf.1 hgd).1
  rw [hfg, show d + (m - d) = m by omega, hh.2, hf.2, Ring.one_mul] at this
  exact this.symm

/-- `xⁿ - 1` is monic of degree `n` for `n ≥ 1`. -/
theorem monic_X_pow_sub_one {n : Nat} (hn : 1 ≤ n) :
    Monic ((X : Polynomial R) ^ n + -1) n := by
  obtain ⟨h1, h2⟩ := X_pow_deg (R := R) n
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [coeff_add, coeff_neg, h1 k hk, coeff_one, ite_false_of (by omega), Ring.neg_zero,
      Ring.add_zero]
  · rw [coeff_add, coeff_neg, h2, coeff_one, ite_false_of (by omega), Ring.neg_zero,
      Ring.add_zero]

/-- `natDegree 0 = 0`. -/
theorem natDegree_zero' : natDegree (0 : Polynomial R) = 0 := by
  unfold natDegree; rw [len_eq_zero.2 rfl]

end Monic

/-! ## Products of linear factors -/

section ProdLin

variable {R : Type u} [CommRing R]

/-- **The product of linear factors** `∏_{a ∈ L} (x - a)`. -/
noncomputable def prodLin (L : List R) : Polynomial R := lprod (L.map linear)

/-- `∏_{a ∈ L} (x - a)` is monic of degree `|L|`. -/
theorem monic_prodLin : ∀ L : List R, Monic (prodLin L) L.length
  | [] => monic_one
  | a :: L => by
    show Monic (linear a * prodLin L) (L.length + 1)
    rw [Nat.add_comm]
    exact (monic_linear a).mul (monic_prodLin L)

/-- The product over a concatenation. -/
theorem prodLin_append (L M : List R) : prodLin (L ++ M) = prodLin L * prodLin M := by
  unfold prodLin; rw [List.map_append, lprod_append]

/-- The product does not depend on the order of the factors. -/
theorem prodLin_perm {L M : List R} (h : L.Perm M) : prodLin L = prodLin M :=
  lprod_perm (h.map linear)

/-- **Distinct roots give linear factors.** Over a domain, if the distinct elements of `L` are
roots of `f`, then `∏_{a ∈ L} (x - a)` divides `f`. -/
theorem prodLin_dvd (hD : IsDomain R) : ∀ (L : List R) (f : Polynomial R), L.Nodup →
    (∀ a, a ∈ L → eval a f = 0) → Divides (prodLin L) f
  | [], f, _, _ => ⟨f, (Ring.one_mul f).symm⟩
  | a :: L, f, hnd, hr => by
    rw [List.nodup_cons] at hnd
    obtain ⟨q, hq⟩ := (factor_theorem f a).1 (hr a List.mem_cons_self)
    have hq' : ∀ b, b ∈ L → eval b q = 0 := by
      intro b hb
      have h1 := hr b (List.mem_cons_of_mem a hb)
      rw [hq, eval_mul] at h1
      rcases hD.2 _ _ h1 with h | h
      · exfalso
        rw [linear, eval_add, eval_neg, eval_X, eval_C] at h
        exact hnd.1 (eq_of_sub_eq_zero h ▸ hb)
      · exact h
    obtain ⟨c, hc⟩ := prodLin_dvd hD L q hnd.2 hq'
    refine ⟨c, ?_⟩
    rw [hq, hc]
    exact (Ring.mul_assoc _ _ _).symm

/-- **A divisor of a product of linear factors has a root among them.** Over a domain, if
`f g = ∏_{a ∈ L} (x - a)` and `f` is not constant, then `f(a) = 0` for some `a ∈ L`. -/
theorem exists_root_of_dvd_prodLin (hD : IsDomain R) : ∀ (L : List R) (f g : Polynomial R),
    f * g = prodLin L → 0 < natDegree f → ∃ a, a ∈ L ∧ eval a f = 0
  | [], f, g, h, hd => by
    exfalso
    have hf0 : f ≠ 0 := fun e => by rw [e, natDegree_zero'] at hd; exact Nat.lt_irrefl 0 hd
    exact not_isUnit_of_natDegree_pos hD hf0 hd ⟨g, h⟩
  | a :: L, f, g, h, hd => by
    by_cases ha : eval a f = 0
    · exact ⟨a, List.mem_cons_self, ha⟩
    · have h1 := congrArg (eval a) h
      have e0 : eval a (prodLin (a :: L)) = 0 := by
        show eval a (linear a * prodLin L) = 0
        rw [eval_mul, eval_linear, Ring.zero_mul]
      rw [eval_mul, e0] at h1
      rcases hD.2 _ _ h1 with h2 | h2
      · exact absurd h2 ha
      · obtain ⟨g', hg'⟩ := (factor_theorem g a).1 h2
        have hl0 : linear a ≠ 0 := (monic_linear a).ne_zero hD.1
        have e : f * g' = prodLin L := by
          apply (Polynomial.isDomain hD).mul_left_cancel hl0
          rw [show linear a * (f * g') = f * (linear a * g') by grind, ← hg', h]
          rfl
        obtain ⟨b, hb, hb'⟩ := exists_root_of_dvd_prodLin hD L f g' e hd
        exact ⟨b, List.mem_cons_of_mem a hb, hb'⟩

end ProdLin

/-! ## Primes and irreducible factors in `K[x]` -/

section Primes

variable {R : Type u} [CommRing R]

/-- A prime element dividing a power divides the base. -/
theorem IsPrimeElt.dvd_of_dvd_pow {π a : R} (hπ : IsPrimeElt π) :
    ∀ k : Nat, Divides π (a ^ k) → Divides π a
  | 0, h => absurd (IsUnit.of_dvd ⟨1, Ring.mul_one 1⟩ h) hπ.2.1
  | k + 1, h => by
    rcases hπ.2.2 _ _ (show Divides π (a ^ k * a) from h) with h1 | h1
    · exact IsPrimeElt.dvd_of_dvd_pow hπ k h1
    · exact h1

/-- Over a field, a non-zero non-unit polynomial has an irreducible factor. -/
theorem exists_irreducible_factor {K : Type u} [CommRing K] (hF : IsField K) {f : Polynomial K}
    (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) : ∃ π, Irreducible π ∧ Divides π f := by
  obtain ⟨L, hL, hprod⟩ := exists_factorization hF (natDegree f) f rfl hf0 hfu
  cases L with
  | nil => exact absurd ⟨1, by rw [← hprod]; exact Ring.mul_one 1⟩ hfu
  | cons a L => exact ⟨a, hL a List.mem_cons_self, ⟨lprod L, hprod.symm⟩⟩

end Primes

/-! ## Gauss's lemma for monic factors -/

section Gauss

variable {Ω : Type} [CommRing Ω] (hΩ : IsField Ω) (hc : CharZero Ω)

/-- `N` clears the denominators of `f` up to degree `d`: `N > 0` and `N fₖ` is an integer `Gₖ`
for every `k`, with `Gₖ = 0` for `k > d`. -/
def Clears (f : Polynomial (ratField hΩ hc)) (d N : Nat) : Prop :=
  0 < N ∧ ∃ G : Nat → Int, SuppLE G d ∧ ∀ k, (((N : Int) : Ω)) * (coeff f k).1 = ((G k : Int) : Ω)

/-- Every polynomial of degree `≤ d` over `ℚ` has a common denominator. -/
theorem clears_exists {f : Polynomial (ratField hΩ hc)} {d : Nat} (hf : DegLT f (d + 1)) :
    ∃ N, Clears hΩ hc f d N := by
  obtain ⟨N, hN, G, hGs, hG⟩ := clear_denominators hΩ hc f hf
  refine ⟨N.toNat, by omega, G, hGs, fun k => ?_⟩
  rw [Int.toNat_of_nonneg (by omega)]
  exact hG k

/-- **Descent.** If `N` clears the denominators of a monic `f` and a prime `p` divides every
cleared coefficient, then `N / p` also clears them. -/
theorem clears_descend {f : Polynomial (ratField hΩ hc)} {d N : Nat} (hf : Monic f d) {p : Nat}
    (hp : IsPrime p) {G : Nat → Int} (hGs : SuppLE G d)
    (hG : ∀ k, (((N : Int) : Ω)) * (coeff f k).1 = ((G k : Int) : Ω)) (hN : 0 < N)
    (hdiv : ∀ k, (p : Int) ∣ G k) : ∃ N', N' < N ∧ Clears hΩ hc f d N' := by
  have h2 := hp.1
  -- the cleared leading coefficient is `N`
  have hGd : (N : Int) = G d := by
    apply hc.cast_inj
    have := hG d
    rw [hf.2] at this
    exact (Ring.mul_one _).symm.trans this
  have hpN : p ∣ N := Int.ofNat_dvd.1 (hGd ▸ hdiv d)
  obtain ⟨N', rfl⟩ := hpN
  have hN' : 0 < N' := Nat.pos_of_mul_pos_left hN
  have hpz : (p : Int) ≠ 0 := by omega
  have hpC : (((p : Int) : Ω)) ≠ 0 := fun h => hpz (hc _ h)
  refine ⟨N', ?_, hN', fun k => G k / p, fun k hk => by
    show G k / p = 0; rw [hGs k hk]; exact Int.zero_ediv _, fun k => ?_⟩
  · calc N' = 1 * N' := (Nat.one_mul N').symm
      _ < p * N' := Nat.mul_lt_mul_of_pos_right (by omega) hN'
  · apply hΩ.isDomain.mul_left_cancel hpC
    have hGG : G k = p * (G k / p) := (Int.mul_ediv_cancel' (hdiv k)).symm
    have := hG k
    rw [hGG, Int.natCast_mul, Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_mul] at this
    rw [← Ring.mul_assoc]
    exact this

/-- The coefficients of `N M F` are those of the product of the cleared factors. -/
theorem conv_of_clears {F : Polynomial Int} {f g : Polynomial (ratField hΩ hc)}
    (hF : mapPoly (icastHom (ratField hΩ hc)) F = f * g) {N M : Nat} {G H : Nat → Int}
    (hG : ∀ k, (((N : Int) : Ω)) * (coeff f k).1 = ((G k : Int) : Ω))
    (hH : ∀ k, (((M : Int) : Ω)) * (coeff g k).1 = ((H k : Int) : Ω)) :
    ∀ m, ((N * M : Nat) : Int) * coeff F m = conv G H m := by
  intro m
  apply hc.cast_inj
  have hcoef := congrArg Subtype.val (coeff_mul_sum f g m)
  rw [← hF, coeff_mapPoly, Subfield.coe_rsum] at hcoef
  have e1 : ((icastHom (ratField hΩ hc)).toFun (coeff F m)).1 = ((coeff F m : Int) : Ω) :=
    Subfield.coe_intCast (ratField hΩ hc) _
  rw [e1] at hcoef
  unfold conv
  rw [intCast_zsum, Lean.Grind.Ring.intCast_mul, Int.natCast_mul, Lean.Grind.Ring.intCast_mul,
    hcoef, mul_rsum]
  apply rsum_congr
  intro k _
  rw [Lean.Grind.Ring.intCast_mul, ← hG k, ← hH (m - k)]
  show (((N : Int) : Ω)) * (((M : Int) : Ω)) * ((coeff f k).1 * (coeff g (m - k)).1) =
    (((N : Int) : Ω)) * (coeff f k).1 * ((((M : Int) : Ω)) * (coeff g (m - k)).1)
  grind

/-- The integer polynomial `Σ_{k ≤ d} Gₖ xᵏ` maps to `f` if `Gₖ = fₖ` for all `k`. -/
theorem map_of_coeffs {f : Polynomial (ratField hΩ hc)} {d : Nat} (hf : DegLT f (d + 1)) {G : Nat → Int}
    (hG : ∀ k, (coeff f k).1 = ((G k : Int) : Ω)) :
    mapPoly (icastHom (ratField hΩ hc)) (rsum (fun k => C (G k) * X ^ k) (d + 1)) = f := by
  apply ext; intro k
  rw [coeff_mapPoly, coeff_rsum_monomial]
  apply Subtype.ext
  by_cases hk : k < d + 1
  · rw [ite_true_of hk, hG k]; exact Subfield.coe_intCast (ratField hΩ hc) _
  · rw [ite_false_of hk, hf k (by omega)]; rfl

/-- **Gauss's lemma for monic factors.** If a monic integer polynomial `F` factors over `ℚ` as
`F = f g` with `f`, `g` monic, then `f` has integer coefficients. -/
theorem int_of_monic_factor {F : Polynomial Int} {f g : Polynomial (ratField hΩ hc)} {d e : Nat}
    (hf : Monic f d) (hg : Monic g e) (hF : mapPoly (icastHom (ratField hΩ hc)) F = f * g) :
    ∃ F₁ : Polynomial Int, mapPoly (icastHom (ratField hΩ hc)) F₁ = f := by
  obtain ⟨N, ⟨hN0, G, hGs, hG⟩, hNmin⟩ := FiniteType.exists_least _ (clears_exists hΩ hc hf.1)
  obtain ⟨M, ⟨hM0, H, hHs, hH⟩, hMmin⟩ := FiniteType.exists_least _ (clears_exists hΩ hc hg.1)
  have hconv := conv_of_clears hΩ hc hF hG hH
  have hN1 : N = 1 := by
    apply Classical.byContradiction; intro hne
    have h2 : 2 ≤ N * M := by
      have : 1 ≤ M := hM0
      have : 2 ≤ N := by omega
      calc 2 = 2 * 1 := rfl
        _ ≤ N * M := Nat.mul_le_mul (by omega) (by omega)
    obtain ⟨p, hp, hpNM⟩ := exists_prime_factor h2
    have hall : ∀ k, (p : Int) ∣ conv G H k := fun k => by
      rw [← hconv k]; exact Int.dvd_trans (Int.ofNat_dvd.2 hpNM) (Int.dvd_mul_right _ _)
    by_cases hGall : ∀ k, (p : Int) ∣ G k
    · obtain ⟨N', hlt, hcl⟩ := clears_descend hΩ hc hf hp hGs hG hN0 hGall
      exact hNmin N' hlt hcl
    · by_cases hHall : ∀ k, (p : Int) ∣ H k
      · obtain ⟨M', hlt, hcl⟩ := clears_descend hΩ hc hg hp hHs hH hM0 hHall
        exact hMmin M' hlt hcl
      · have hG' : ∃ i, ¬ (p : Int) ∣ G i :=
          Classical.byContradiction fun h => hGall fun k =>
            Classical.byContradiction fun hk => h ⟨k, hk⟩
        have hH' : ∃ j, ¬ (p : Int) ∣ H j :=
          Classical.byContradiction fun h => hHall fun k =>
            Classical.byContradiction fun hk => h ⟨k, hk⟩
        obtain ⟨n, hn⟩ := not_dvd_conv hp hG' hH'
        exact hn (hall n)
  subst hN1
  refine ⟨_, map_of_coeffs hΩ hc hf.1 (G := G) fun k => ?_⟩
  have := hG k
  rw [show (((1 : Nat) : Int) : Ω) = 1 from Lean.Grind.Ring.intCast_one, Ring.one_mul] at this
  exact this

/-- Mapping integer polynomials to `ℚ[x]` is injective. -/
theorem mapPoly_icast_inj {A B : Polynomial Int}
    (h : mapPoly (icastHom (ratField hΩ hc)) A = mapPoly (icastHom (ratField hΩ hc)) B) : A = B := by
  apply ext; intro n
  have h1 := congrArg (fun f => (coeff f n).1) h
  simp only [coeff_mapPoly] at h1
  apply hc.cast_inj
  rw [← Subfield.coe_intCast (ratField hΩ hc), ← Subfield.coe_intCast (ratField hΩ hc)]
  exact h1

/-- **Division by a monic integer polynomial.** If a monic integer polynomial `P` divides an
integer polynomial `A` over `ℚ`, it divides `A` over `ℤ`. -/
theorem int_dvd_of_monic {P A : Polynomial Int} {d : Nat} (hP : Monic P d)
    (h : Divides (mapPoly (icastHom (ratField hΩ hc)) P) (mapPoly (icastHom (ratField hΩ hc)) A)) : ∃ T, A = P * T := by
  obtain ⟨T, r, hAr, hr⟩ := div_mod_aux P d 1 hP.1 (by rw [hP.2, Ring.mul_one]) (len A) A
    (degLT_len A)
  refine ⟨T, ?_⟩
  suffices hr0 : r = 0 by rw [hAr, hr0, Ring.add_zero, CommRing.mul_comm]
  obtain ⟨e, he⟩ := h
  have hD : IsDomain (ratField hΩ hc) := ((ratField hΩ hc).isField hΩ).isDomain
  let φ := mapHom (icastHom (ratField hΩ hc))
  have hrm : mapPoly (icastHom (ratField hΩ hc)) r = mapPoly (icastHom (ratField hΩ hc)) P * (e + -mapPoly (icastHom (ratField hΩ hc)) T) :=
    by
    have h1 : φ.toFun A = φ.toFun T * φ.toFun P + φ.toFun r := by
      rw [hAr, φ.map_add, φ.map_mul]
    change mapPoly (icastHom (ratField hΩ hc)) A = _ at h1
    rw [he] at h1
    change _ = mapPoly (icastHom (ratField hΩ hc)) T * mapPoly (icastHom (ratField hΩ hc)) P + mapPoly (icastHom (ratField hΩ hc)) r at h1
    grind
  have hmr : mapPoly (icastHom (ratField hΩ hc)) r = 0 := by
    apply Classical.byContradiction; intro hne
    have hc0 : e + -mapPoly (icastHom (ratField hΩ hc)) T ≠ 0 := by
      intro h0; rw [h0, Ring.mul_zero] at hrm; exact hne hrm
    have hP0 := (hP.map (icastHom (ratField hΩ hc))).ne_zero hD.1
    have hdeg := natDegree_mul hD hP0 hc0
    rw [← hrm, (hP.map (icastHom (ratField hΩ hc))).natDegree_eq hD.1] at hdeg
    have := natDegree_lt_of_degLT hne (degLT_mapPoly (icastHom (ratField hΩ hc)) hr)
    omega
  apply mapPoly_icast_inj hΩ hc
  rw [hmr]
  exact (mapHom (icastHom (ratField hΩ hc))).map_zero.symm

end Gauss

/-! ## Separability of `xⁿ - 1` -/

section Separable

variable {K : Type u} [CommRing K]

/-- `p(0)` is the constant coefficient. -/
theorem eval_zero_eq_coeff {R : Type u} [CommRing R] (p : Polynomial R) :
    eval 0 p = coeff p 0 := by
  induction p using Quotient.ind with
  | _ l =>
    cases l with
    | nil => rfl
    | cons a l =>
      show a + 0 * evalList 0 l = a
      rw [Ring.zero_mul, Ring.add_zero]

/-- The coefficient of `ε¹` in a product: `(ab)₁ = a₀ b₁ + a₁ b₀`. -/
theorem coeff_mul_one {R : Type u} [CommRing R] (a b : Polynomial R) :
    coeff (a * b) 1 = coeff a 0 * coeff b 1 + coeff a 1 * coeff b 0 := by
  rw [coeff_mul_sum]
  show 0 + coeff a 0 * coeff b 1 + coeff a 1 * coeff b 0 = _
  rw [Ring.zero_add]

/-- **The dual-number substitution** `f(x) ↦ f(x + ε)`, a ring homomorphism `K[x] → K[x][ε]`.
Its `ε`-coefficient is the formal derivative of `f`. -/
noncomputable def dualHom : RingHom (Polynomial K) (Polynomial (Polynomial K)) :=
  RingHom.comp (evalHom (C X + X)) (mapHom (RingHom.comp (CHom (R := Polynomial K)) CHom))

/-- The substitution fixes constants. -/
theorem dualHom_C (a : K) : dualHom.toFun (C a) = C (C a) := by
  show eval (C X + X) (mapPoly _ (C a)) = _
  rw [mapPoly_C, eval_C]; rfl

/-- The substitution sends `x` to `x + ε`. -/
theorem dualHom_X : (dualHom (K := K)).toFun X = C X + X := by
  show eval (C X + X) (mapPoly _ X) = _
  rw [mapPoly_X, eval_X]

/-- The `ε⁰`-coefficient of `f(x + ε)` is `f`. -/
theorem coeff_dualHom_zero (f : Polynomial K) : coeff (dualHom.toFun f) 0 = f := by
  rw [← eval_zero_eq_coeff]
  exact polyHom_ext (RingHom.comp (evalHom (0 : Polynomial K)) dualHom) (RingHom.id _)
    (fun a => by
      show eval 0 (dualHom.toFun (C a)) = C a
      rw [dualHom_C, eval_C])
    (by
      show eval 0 (dualHom.toFun X) = X
      rw [dualHom_X, eval_add, eval_C, eval_X, Ring.add_zero]) f

/-- **A repeated factor divides the derivative.** If `f = π² h`, then `π` divides the
`ε`-coefficient of `f(x + ε)`. -/
theorem dvd_coeff_dualHom (π h : Polynomial K) :
    Divides π (coeff (dualHom.toFun (π * π * h)) 1) := by
  rw [dualHom.map_mul, dualHom.map_mul, coeff_mul_one, coeff_mul_one,
    ← dualHom.map_mul, coeff_dualHom_zero, coeff_dualHom_zero, coeff_dualHom_zero]
  exact ⟨π * coeff (dualHom.toFun h) 1 + (coeff (dualHom.toFun π) 1 +
    coeff (dualHom.toFun π) 1) * h, by grind⟩

/-- **The derivative of `xᵐ`**: if `c` is the `ε`-coefficient of `(x + ε)ᵐ`, then
`x c = m xᵐ`. -/
theorem X_mul_coeff_pow (m : Nat) :
    (X : Polynomial K) * coeff ((C X + X : Polynomial (Polynomial K)) ^ m) 1 =
      (((m : Nat) : Int) : Polynomial K) * X ^ m := by
  induction m with
  | zero =>
    show X * coeff (1 : Polynomial (Polynomial K)) 1 = (((0 : Nat) : Int) : Polynomial K) * 1
    rw [coeff_one, ite_false_of (by omega)]
    grind
  | succ m ih =>
    show X * coeff ((C X + X : Polynomial (Polynomial K)) ^ m * (C X + X)) 1 = _
    rw [coeff_mul_one]
    have h0 : coeff ((C X + X : Polynomial (Polynomial K)) ^ m) 0 = X ^ m := by
      rw [← dualHom_X, ← RingHom.map_pow', coeff_dualHom_zero]
    have h1 : coeff (C X + X : Polynomial (Polynomial K)) 1 = 1 := by
      rw [coeff_add, coeff_C_succ, coeff_X, ite_true_of rfl, Ring.zero_add]
    have h2 : coeff (C X + X : Polynomial (Polynomial K)) 0 = X := by
      rw [coeff_add, coeff_C_zero, coeff_X, ite_false_of (by omega), Ring.add_zero]
    rw [h0, h1, h2, show ((m + 1 : Nat) : Int) = (m : Int) + 1 by omega,
      Lean.Grind.Ring.intCast_add, Lean.Grind.Ring.intCast_one]
    show _ = _ * (X ^ m * X)
    grind

/-- **`xⁿ - 1` is separable.** Over a field in which `n ≠ 0`, if `π² ∣ xⁿ - 1` then `π` is a
unit. -/
theorem isUnit_of_sq_dvd_X_pow_sub_one (hF : IsField K) {n : Nat}
    (hn : (((n : Nat) : Int) : K) ≠ 0) {π : Polynomial K}
    (h : Divides (π * π) ((X : Polynomial K) ^ n + -1)) : IsUnit π := by
  obtain ⟨h', hh'⟩ := h
  let c := coeff (dualHom.toFun ((X : Polynomial K) ^ n + -1)) 1
  have hc : c = coeff ((C X + X : Polynomial (Polynomial K)) ^ n) 1 := by
    show coeff (dualHom.toFun ((X : Polynomial K) ^ n + -1)) 1 = _
    rw [dualHom.map_add, RingHom.map_pow', dualHom.map_neg, dualHom.map_one, dualHom_X,
      coeff_add, coeff_neg, coeff_one, ite_false_of (by omega), Ring.neg_zero, Ring.add_zero]
  obtain ⟨a, ha⟩ : Divides π c := by
    show Divides π (coeff (dualHom.toFun ((X : Polynomial K) ^ n + -1)) 1)
    rw [hh']; exact dvd_coeff_dualHom π h'
  have hXc := X_mul_coeff_pow (K := K) n
  rw [← hc, ha] at hXc
  -- `π` divides the constant `n`
  have hdiv : (((n : Nat) : Int) : Polynomial K) = π * (X * a + -(((n : Nat) : Int) :
      Polynomial K) * (π * h')) := by
    have e : (((n : Nat) : Int) : Polynomial K) =
        X * (π * a) + -(((n : Nat) : Int) : Polynomial K) * ((X : Polynomial K) ^ n + -1) := by
      rw [hXc]; grind
    rw [e, hh']; grind
  obtain ⟨b, hb⟩ := hF.2 _ hn
  refine IsUnit.of_dvd ⟨C b, ?_⟩ ⟨_, hdiv⟩
  rw [← RingHom.map_intCast (CHom (R := K))]
  show C _ * C b = 1
  rw [← C_mul, hb, C_one]

end Separable

end Foundations.Langlands
