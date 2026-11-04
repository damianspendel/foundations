import Foundations.Langlands.Cyclotomic.DictionaryN

/-!
# Euler factors: Dirichlet `L`-functions and Artin `L`-functions over `ℚ(ζ_n)`

An **`L`-function** packages arithmetic data prime by prime into an Euler product.

* **Dirichlet** (1837), for a Dirichlet character `χ` modulo `n`:
  `L(s, χ) = Σ χ(m) m^{-s} = ∏_q (1 - χ(q) q^{-s})⁻¹`. The coefficient at `q` is `χ(q)`, which is
  `0` for `q ∣ n`. Hecke (1918) extended this to characters of idèle class groups of number
  fields, the automorphic objects of `GL(1)`.
* **Artin** (1923, 1930), for a representation `ρ` of `Gal(K/ℚ)`: at an unramified prime `q` the
  Euler factor is `det(1 - ρ(Frob_q) q^{-s})⁻¹`. For a character `ρ` this is
  `(1 - ρ(Frob_q) q^{-s})⁻¹`. (At ramified primes Artin uses the inertia invariants; we do not
  formalise inertia groups, and treat only the unramified primes, i.e. `q ∤ n` for
  `K = ℚ(ζ_n)`.)

`GL(1)` Langlands over `ℚ` says that every Artin `L`-function of a Galois character is a
Dirichlet `L`-function, factor by factor. For `ℚ(ζ_n)` this is formal once the dictionary
`χ ↔ ρ_χ` of `DictionaryN.lean` is known, since `ρ_χ(σ_q) = χ(q)` for primes `q ∤ n`:

* the local factors agree at every prime `q ∤ n` (`localFactor_match`);
* the finite partial Euler products agree: the Dirichlet product over *all* primes `q < N` equals
  the Artin product over the unramified primes `q < N` (`dirichletEuler_eq_artinEuler`), because
  the Dirichlet factors at `q ∣ n` are `(1 - 0)⁻¹ = 1`.

These are identities between finite products in `ℂ`, for every natural exponent `s` (the
interesting range being `s ≥ 2`, where the infinite products converge absolutely). **Nothing is
claimed about the analytic `L`-functions** themselves: no convergence, no limits, no analytic
continuation. Note also that for an imprimitive `χ` the Dirichlet factor at a prime `q ∣ n`
is `1`, while the full Artin factor there need not be; this is why the comparison is made on
the unramified primes.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.NumberTheory Foundations.Algebra.Group

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

attribute [local instance] Classical.propDecidable

/-! ## Local factors and finite Euler products -/

/-- **The local Euler factor** `(1 - c · q^{-s})⁻¹` with coefficient `c ∈ ℂ` at `q`. -/
noncomputable def localFactor (c : ℂ) (q s : Nat) : ℂ := (1 - c * ((q : ℂ) ^ s)⁻¹)⁻¹

/-- A zero coefficient gives the trivial factor `1`. -/
theorem localFactor_zero (q s : Nat) : localFactor 0 q s = 1 := by
  unfold localFactor
  rw [show (1 : ℂ) - 0 * ((q : ℂ) ^ s)⁻¹ = 1 by grind]
  exact Foundations.Numbers.C.inv_one

/-- **The finite Euler product** `∏_{q < N, P q, q prime} (1 - a(q) q^{-s})⁻¹`, over the primes
below `N` satisfying the condition `P`. -/
noncomputable def eulerProdOn (P : Nat → Prop) (a : Nat → ℂ) (s : Nat) : Nat → ℂ
  | 0 => 1
  | N + 1 => eulerProdOn P a s N * (if IsPrime N ∧ P N then localFactor (a N) N s else 1)

/-- Euler products with the same local factors at the selected primes are equal. -/
theorem eulerProdOn_congr {P P' : Nat → Prop} {a a' : Nat → ℂ} {s : Nat}
    (h : ∀ q, IsPrime q →
      (if P q then localFactor (a q) q s else 1) = (if P' q then localFactor (a' q) q s else 1)) :
    ∀ N, eulerProdOn P a s N = eulerProdOn P' a' s N
  | 0 => rfl
  | N + 1 => by
    show eulerProdOn P a s N * _ = eulerProdOn P' a' s N * _
    rw [eulerProdOn_congr h N]
    congr 1
    by_cases hN : IsPrime N
    · have := h N hN
      by_cases hP : P N <;> by_cases hP' : P' N <;> simp_all
    · simp [hN]

/-! ## The two sides -/

section Sides

variable {n : Nat} (hn : 1 ≤ n) [NeZero n]

/-- **The partial Dirichlet Euler product** `∏_{q < N prime} (1 - χ(q) q^{-s})⁻¹` of a Dirichlet
character `χ` modulo `n` (all primes; the factors at `q ∣ n` are `1`). -/
noncomputable def dirichletEuler (χ : Character (ZModUnits n)) (s N : Nat) : ℂ :=
  eulerProdOn (fun _ => True) (dchar χ) s N

/-- **The partial Artin Euler product** of a character `ρ` of `Gal(ℚ(ζ_n)/ℚ)` over the
unramified primes: `∏_{q < N prime, q ∤ n} (1 - ρ(Frob_q) q^{-s})⁻¹`, where `Frob_q = σ_q` is the
automorphism `ζ_n ↦ ζ_n^q` (`frobN`), the Frobenius in the sense of `reduceN_galAut`. -/
noncomputable def artinEuler (ρ : Character (FieldAut Qc (cycloFieldN hn))) (s N : Nat) : ℂ :=
  eulerProdOn (fun q => ¬ q ∣ n) (fun q => ρ.1 (frobN hn q)) s N

/-- **Euler coefficients match.** For a prime `q ∤ n`, the Dirichlet coefficient `χ(q)` equals
the Artin coefficient `ρ_χ(Frob_q)`. -/
theorem eulerCoeff_match (χ : Character (ZModUnits n)) {q : Nat} (hq : IsPrime q)
    (hqn : ¬ q ∣ n) : dchar χ q = ((dirichletGaloisN hn) χ).1 (frobN hn q) :=
  (dirichletGaloisN_frobN hn χ hq hqn).symm

/-- **Local factors match.** For a prime `q ∤ n` and every `s`,
`(1 - χ(q) q^{-s})⁻¹ = (1 - ρ_χ(Frob_q) q^{-s})⁻¹`. -/
theorem localFactor_match (χ : Character (ZModUnits n)) {q : Nat} (hq : IsPrime q)
    (hqn : ¬ q ∣ n) (s : Nat) :
    localFactor (dchar χ q) q s = localFactor (((dirichletGaloisN hn) χ).1 (frobN hn q)) q s := by
  rw [eulerCoeff_match hn χ hq hqn]

/-- At a prime dividing `n` the Dirichlet factor is `1`. -/
theorem localFactor_dchar_of_dvd (χ : Character (ZModUnits n)) {q : Nat} (hq : IsPrime q)
    (hqn : q ∣ n) (s : Nat) : localFactor (dchar χ q) q s = 1 := by
  have hnc : ¬ Nat.Coprime q n := fun h => by
    have h1 : Nat.gcd q n = q := Nat.gcd_eq_left hqn
    have := hq.1
    rw [Nat.Coprime] at h; omega
  rw [dchar_of_not_coprime χ hnc, localFactor_zero]

/-- **Partial Euler products match.** For a Dirichlet character `χ` modulo `n`, every `s` and
every `N`, the partial Dirichlet product over the primes `q < N` equals the partial Artin
product of `ρ_χ` over the unramified primes `q < N`:
`∏_{q<N} (1 - χ(q) q^{-s})⁻¹ = ∏_{q<N, q∤n} (1 - ρ_χ(Frob_q) q^{-s})⁻¹`. -/
theorem dirichletEuler_eq_artinEuler (χ : Character (ZModUnits n)) (s N : Nat) :
    dirichletEuler χ s N = artinEuler hn ((dirichletGaloisN hn) χ) s N := by
  apply eulerProdOn_congr
  intro q hq
  by_cases hqn : q ∣ n
  · rw [ite_eq_left trivial, ite_eq_right (fun h => h hqn), localFactor_dchar_of_dvd χ hq hqn]
  · rw [ite_eq_left trivial, ite_eq_left hqn, localFactor_match hn χ hq hqn]

/-- **Every Artin product of a character of `Gal(ℚ(ζ_n)/ℚ)` is a Dirichlet product.** For each
Galois character `ρ` there is a Dirichlet character `χ` modulo `n` (namely `ρ ∘ e`) whose
partial Euler products agree with those of `ρ` over the unramified primes, for all `s` and
`N`. -/
theorem artinEuler_eq_dirichletEuler (ρ : Character (FieldAut Qc (cycloFieldN hn))) :
    ∃ χ : Character (ZModUnits n), ∀ s N, artinEuler hn ρ s N = dirichletEuler χ s N := by
  refine ⟨(dirichletGaloisN hn).invFun ρ, fun s N => ?_⟩
  rw [dirichletEuler_eq_artinEuler hn, (dirichletGaloisN hn).right_inv]

end Sides

end Foundations.Langlands
