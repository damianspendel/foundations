import Foundations.Langlands.Cyclotomic.Galois

/-!
# `σ_q` is the Frobenius at `q`

The previous files treat `σ_q`, the automorphism of `ℚ(ζ_p)` with `ζ_p ↦ ζ_p^q`, and the
`q`-th power map of the characteristic-`q` ring `A = 𝔽_q[x]/(Φ_p)` separately. Here we connect
them. That `σ_q` reduces to the `q`-th power modulo `q` is what makes it the **Frobenius
element** at `q`.

* **The ring `ℤ[ζ_p]`.** It is the image of evaluation `ℤ[x] → ℂ`, `f ↦ f(ζ_p)`
  (`intZeta`). It lies in `ℚ(ζ_p)`.
* **Reduction modulo `q`.** Sending `f(ζ_p)` to the class of `f` (coefficients reduced
  mod `q`) in `A` is well defined. If `f(ζ_p) = 0`, divide `f` by the monic polynomial `Φ_p`
  over `ℤ`: `f = Q Φ_p + r` with `deg r < p - 1`. Then `r(ζ_p) = 0`, so `Φ_p ∣ r` over `ℚ`
  (minimal polynomial), forcing `r = 0`. Hence `f` is a multiple of `Φ_p`, and its class in
  `A` vanishes. This gives a ring homomorphism `ℤ[ζ_p] → A` with `ζ_p ↦ x` (`reduce`).
* **Frobenius.** For `α = f(ζ_p)`, `σ_q(α) = f(ζ_p^q)`. Reducing gives `f̄(x^q)`, which is
  `f̄(x)^q` because `c^q = c` in `𝔽_q` (Fermat) and `y ↦ y^q` is additive in characteristic
  `q`. So **`σ_q(α) ≡ α^q (mod q)`** for every `α ∈ ℤ[ζ_p]` (`reduce_galAut`).

The Gauss sum `g` lies in `ℤ[ζ_p]` and reduces to the Gauss sum of `A` (`reduce_gaussK`). So the
computation `g^q = (q/p) g` in `A` from `Reciprocity.lean` is the reduction of the identity
`σ_q(g) = (q/p) g` in `ℚ(ζ_p)` (`galAut_gaussSum`).

We do not prove that `A ≅ ℤ[ζ_p]/(q)`, i.e. that the kernel of `reduce` is exactly
`q ℤ[ζ_p]`. That is not needed for the congruence.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

universe u

/-- **The canonical ring homomorphism** `ℤ → R`. -/
def icastHom (R : Type u) [CommRing R] : RingHom Int R where
  toFun z := (z : R)
  map_add := Lean.Grind.Ring.intCast_add
  map_mul := Lean.Grind.Ring.intCast_mul
  map_one := Lean.Grind.Ring.intCast_one

/-- A non-zero polynomial with `deg < d` has `natDegree < d`. -/
theorem natDegree_lt_of_degLT {R : Type u} [CommRing R] {f : Polynomial R} (hf : f ≠ 0) {d : Nat}
    (h : DegLT f d) : natDegree f < d := by
  have h1 := len_le h
  have h2 : len f ≠ 0 := fun e => hf (len_eq_zero.1 e)
  unfold natDegree; omega

/-- Mapping coefficients preserves `deg < d`. -/
theorem degLT_mapPoly {A B : Type u} [CommRing A] [CommRing B] (φ : RingHom A B)
    {f : Polynomial A} {d : Nat} (h : DegLT f d) : DegLT (mapPoly φ f) d := fun n hn => by
  rw [coeff_mapPoly, h n hn]; exact φ.map_zero

section IntZeta

variable (p : Nat)

/-- Evaluation of integer polynomials at `ζ_p`: `f ↦ f(ζ_p)`. -/
noncomputable def evZeta : RingHom (Polynomial Int) ℂ :=
  RingHom.comp (evalHom (zeta p)) (mapHom (icastHom ℂ))

/-- **The ring `ℤ[ζ_p]`** of integer polynomial expressions in `ζ_p`. -/
noncomputable def intZeta : Subring ℂ := RingHom.range (evZeta p)

variable {p}

/-- `f(ζ_p)` computed through `ℚ`: it equals `aeval Qc ζ_p` of `f` with coefficients in `ℚ`. -/
theorem evZeta_eq_aeval (f : Polynomial Int) :
    (evZeta p).toFun f = aeval Qc (zeta p) (mapPoly (icastHom Qc) f) := by
  have := polyHom_ext (evZeta p) (RingHom.comp (aevalHom Qc (zeta p)) (mapHom (icastHom Qc)))
    (fun a => by
      show eval (zeta p) (mapPoly _ (C a)) = aeval Qc (zeta p) (mapPoly _ (C a))
      rw [mapPoly_C, mapPoly_C, eval_C, aeval_C]
      exact (Subfield.coe_intCast Qc a).symm)
    (by
      show eval (zeta p) (mapPoly _ X) = aeval Qc (zeta p) (mapPoly _ X)
      rw [mapPoly_X, mapPoly_X, eval_X, aeval_X]) f
  exact this

/-- `(evZeta p) X = ζ_p`. -/
theorem evZeta_X : (evZeta p).toFun X = zeta p := by
  show eval (zeta p) (mapPoly _ X) = _; rw [mapPoly_X, eval_X]

/-- `ℤ[ζ_p] ⊆ ℚ(ζ_p)`. -/
theorem intZeta_le (hp : IsPrime p) {α : ℂ} (hα : α ∈ intZeta p) : α ∈ cycloField hp := by
  obtain ⟨f, rfl⟩ := hα
  rw [evZeta_eq_aeval]
  exact aeval_mem Qc (zeta p) (Qc_le_cycloField hp) (zeta_mem hp) _

/-- **The kernel of evaluation at `ζ_p` consists of multiples of `Φ_p`.** If `f ∈ ℤ[x]` and
`f(ζ_p) = 0`, then `f = Q · Φ_p` for some `Q ∈ ℤ[x]` (division by the monic `Φ_p` and
minimality of `Φ_p` over `ℚ`). -/
theorem dvd_cyclo_of_evZeta (hp : IsPrime p) {f : Polynomial Int} (hf : (evZeta p).toFun f = 0) :
    ∃ Q, f = Q * cyclo Int p := by
  have h2 := hp.1
  obtain ⟨Q, r, hfr, hr⟩ := div_mod_aux (cyclo Int p) (p - 1) 1
    (by rw [show p - 1 + 1 = p by omega]; exact degLT_cyclo p)
    (by rw [coeff_cyclo, ite_true_of (by omega)]; rfl) (len f) f (degLT_len f)
  refine ⟨Q, ?_⟩
  suffices hr0 : r = 0 by rw [hfr, hr0, Ring.add_zero]
  -- `r(ζ_p) = 0`
  have hΦ : (evZeta p).toFun (cyclo Int p) = 0 := by
    show eval (zeta p) (mapPoly _ (cyclo Int p)) = 0
    rw [mapPoly_cyclo, eval_cyclo]; exact rsum_zeta_pow h2
  have hrz : (evZeta p).toFun r = 0 := by
    rw [hfr, (evZeta p).map_add, (evZeta p).map_mul, hΦ, Ring.mul_zero, Ring.zero_add] at hf
    exact hf
  -- so `Φ_p ∣ r` over `ℚ`, impossible for degree reasons unless `r = 0`
  rw [evZeta_eq_aeval] at hrz
  obtain ⟨e, he⟩ := (aeval_zeta_eq_zero_iff hp _).1 hrz
  have hD : IsDomain Qc := (Qc.isField C.isField).isDomain
  have hrQ : mapPoly (icastHom Qc) r = 0 := by
    apply Classical.byContradiction; intro hne
    have he0 : e ≠ 0 := by intro h; rw [h, Ring.mul_zero] at he; exact hne he
    have hΦ0 := cyclo_ne_zero (R := Qc) hD.1 (n := p) (by omega)
    have hdeg := natDegree_mul hD hΦ0 he0
    rw [← he, natDegree_cyclo hD.1 (by omega)] at hdeg
    have := natDegree_lt_of_degLT hne (degLT_mapPoly (icastHom Qc) hr)
    omega
  apply ext; intro n
  have h1 := congrArg (fun g => (coeff g n).1) hrQ
  simp only [coeff_mapPoly] at h1
  rw [coeff_zero]
  apply C.charZero
  have : ((icastHom Qc).toFun (coeff r n)).1 = (0 : ℂ) := h1
  rw [← this]; exact (Subfield.coe_intCast Qc _).symm

end IntZeta

/-! ## Reduction modulo `q` -/

section Reduce

variable {p : Nat} (q : Nat) [NeZero q]

/-- Reduction of integer polynomials to `𝔽_q[x]/(Φ_p)`: reduce the coefficients modulo `q` and
take the class modulo `Φ_p`. -/
noncomputable def redHom (p : Nat) : RingHom (Polynomial Int) (ResRing q p) :=
  RingHom.comp (QuotientRing.proj (cycloIdeal q p)) (mapHom (icastHom (Fin q)))

/-- `x` reduces to the class `ζ` of `x`. -/
theorem redHom_X : (redHom q p).toFun X = zetaRes q p := by
  show QuotientRing.mk _ (mapPoly _ X) = _; rw [mapPoly_X]; rfl

/-- `Φ_p` reduces to `0`. -/
theorem redHom_cyclo : (redHom q p).toFun (cyclo Int p) = 0 := by
  show QuotientRing.mk _ (mapPoly _ (cyclo Int p)) = 0
  rw [mapPoly_cyclo]
  exact QuotientRing.mk_eq_zero.2 ⟨1, (Ring.one_mul _).symm⟩

/-- An integer constant reduces through the structure map `𝔽_q → A`. -/
theorem redHom_C (a : Int) :
    (redHom q p).toFun (C a) = (constHom q p).toFun ((a : Int) : Fin q) := by
  show QuotientRing.mk _ (mapPoly _ (C a)) = _; rw [mapPoly_C]; rfl

variable (hp : IsPrime p)

include hp in
/-- **Reduction is well defined on `ℤ[ζ_p]`**: if `f(ζ_p) = g(ζ_p)` then `f` and `g` have the
same image in `𝔽_q[x]/(Φ_p)`. -/
theorem redHom_congr {f g : Polynomial Int} (h : (evZeta p).toFun f = (evZeta p).toFun g) :
    (redHom q p).toFun f = (redHom q p).toFun g := by
  have h0 : (evZeta p).toFun (f + -g) = 0 := by
    rw [(evZeta p).map_add, (evZeta p).map_neg, h, Ring.add_neg_cancel]
  obtain ⟨Q, hQ⟩ := dvd_cyclo_of_evZeta hp h0
  have h1 : (redHom q p).toFun (f + -g) = 0 := by
    rw [hQ, (redHom q p).map_mul, redHom_cyclo, Ring.mul_zero]
  rw [(redHom q p).map_add, (redHom q p).map_neg] at h1
  grind

/-- **Reduction modulo `q`**, the ring homomorphism `ℤ[ζ_p] → 𝔽_q[x]/(Φ_p)`,
`f(ζ_p) ↦ f(x) mod (q, Φ_p)`. -/
noncomputable def reduce : RingHom (intZeta p) (ResRing q p) where
  toFun α := (redHom q p).toFun (Classical.choose α.2)
  map_add α β := by
    rw [← (redHom q p).map_add]
    apply redHom_congr q hp
    rw [(evZeta p).map_add, Classical.choose_spec α.2, Classical.choose_spec β.2,
      Classical.choose_spec (α + β).2]; rfl
  map_mul α β := by
    rw [← (redHom q p).map_mul]
    apply redHom_congr q hp
    rw [(evZeta p).map_mul, Classical.choose_spec α.2, Classical.choose_spec β.2,
      Classical.choose_spec (α * β).2]; rfl
  map_one := by
    rw [← (redHom q p).map_one]
    apply redHom_congr q hp
    rw [(evZeta p).map_one, Classical.choose_spec (1 : intZeta p).2]; rfl

/-- `reduce (f(ζ_p)) = f mod (q, Φ_p)`. -/
theorem reduce_evZeta (f : Polynomial Int) :
    (reduce q hp).toFun ⟨(evZeta p).toFun f, f, rfl⟩ = (redHom q p).toFun f :=
  redHom_congr q hp (Classical.choose_spec (⟨(evZeta p).toFun f, f, rfl⟩ : intZeta p).2)

/-- `ζ_p ∈ ℤ[ζ_p]` reduces to `ζ = x mod Φ_p`. -/
theorem reduce_zeta :
    (reduce q hp).toFun ⟨zeta p, X, evZeta_X⟩ = zetaRes q p := by
  have := reduce_evZeta q hp X
  rw [redHom_X] at this
  exact (congrArg (reduce q hp).toFun (Subtype.ext evZeta_X.symm)).trans this

end Reduce

/-! ## `σ_q` reduces to the `q`-th power map -/

section Frob

variable {p : Nat} (hp : IsPrime p)

/-- The substitution `f(x) ↦ f(x^a)` on integer polynomials. -/
noncomputable def powSubst (a : Nat) : RingHom (Polynomial Int) (Polynomial Int) :=
  RingHom.comp (evalHom ((X : Polynomial Int) ^ a)) (mapHom CHom)

/-- **`σ_a` on `ℤ[ζ_p]`.** `σ_a(f(ζ_p)) = f(ζ_p^a)`. -/
theorem galAut_evZeta {a : Nat} (ha : ¬ p ∣ a) (f : Polynomial Int) :
    ((galAut hp ha).toFun ⟨(evZeta p).toFun f, intZeta_le hp ⟨f, rfl⟩⟩).1 =
      (evZeta p).toFun ((powSubst a).toFun f) := by
  let σ := galAut hp ha
  let φ : RingHom (Polynomial Int) ℂ :=
    { toFun := fun f => (σ.toFun ⟨(evZeta p).toFun f, intZeta_le hp ⟨f, rfl⟩⟩).1
      map_add := fun f g => by
        show _ = (σ.toFun _ + σ.toFun _).1
        rw [← σ.map_add]; congr 2; apply Subtype.ext; exact (evZeta p).map_add f g
      map_mul := fun f g => by
        show _ = (σ.toFun _ * σ.toFun _).1
        rw [← σ.map_mul]; congr 2; apply Subtype.ext; exact (evZeta p).map_mul f g
      map_one := by
        show _ = ((1 : cycloField hp)).1
        rw [← σ.map_one]; congr 2; apply Subtype.ext; exact (evZeta p).map_one }
  have := polyHom_ext φ (RingHom.comp (evZeta p) (powSubst a))
    (fun c => by
      show (σ.toFun _).1 = (evZeta p).toFun (eval _ (mapPoly CHom (C c)))
      rw [mapPoly_C, eval_C]
      have hval : (evZeta p).toFun (C c) = icast c := by
        show eval (zeta p) (mapPoly _ (C c)) = _; rw [mapPoly_C, eval_C]; rfl
      have hmem : ((evZeta p).toFun (C c)) ∈ Qc := by rw [hval]; exact icast_mem Qc c
      rw [σ.fix _ hmem]
      rfl)
    (by
      show (σ.toFun ⟨(evZeta p).toFun X, _⟩).1 = (evZeta p).toFun (eval _ (mapPoly CHom X))
      have e : (⟨(evZeta p).toFun X, intZeta_le hp ⟨X, rfl⟩⟩ : cycloField hp) = zetaK hp :=
        Subtype.ext evZeta_X
      rw [e, mapPoly_X, eval_X, RingHom.map_pow', galAut_zeta, evZeta_X]; rfl) f
  exact this

/-- `σ_a` maps `ℤ[ζ_p]` into itself. -/
theorem galAut_mem_intZeta {a : Nat} (ha : ¬ p ∣ a) (α : intZeta p) :
    ((galAut hp ha).toFun ⟨α.1, intZeta_le hp α.2⟩).1 ∈ intZeta p := by
  obtain ⟨f, hf⟩ := α.2
  have e : (⟨α.1, intZeta_le hp α.2⟩ : cycloField hp) =
      ⟨(evZeta p).toFun f, intZeta_le hp ⟨f, rfl⟩⟩ := Subtype.ext hf.symm
  rw [e, galAut_evZeta hp ha f]
  exact ⟨_, rfl⟩

/-- `σ_a` as a map `ℤ[ζ_p] → ℤ[ζ_p]`. -/
noncomputable def galAutInt {a : Nat} (ha : ¬ p ∣ a) (α : intZeta p) : intZeta p :=
  ⟨((galAut hp ha).toFun ⟨α.1, intZeta_le hp α.2⟩).1, galAut_mem_intZeta hp ha α⟩

/-- **Fermat in `𝔽_q`**: `c^q = c` for every `c ∈ ℤ/qℤ`. -/
theorem fin_pow_self {q : Nat} [NeZero q] (hq : IsPrime q) (c : Fin q) : rpow c q = c := by
  apply Fin.ext
  rw [rpow_val]
  by_cases h0 : c.val = 0
  · rw [h0, Nat.zero_pow (by have := hq.1; omega)]; exact Nat.zero_mod q
  · have hnd : ¬ q ∣ c.val := fun h => h0 (Nat.eq_zero_of_dvd_of_lt h c.isLt)
    have hf := fermat q c.val hq hnd
    have e : c.val ^ q = c.val ^ (q - 1) * c.val := by
      have := Nat.pow_succ c.val (q - 1)
      rw [show (q - 1).succ = q by have := hq.1; omega] at this
      exact this
    rw [e, Nat.mul_mod, hf, Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt c.isLt]

/-- **Frobenius on integer polynomials mod `(q, Φ_p)`**: `f(x^q) ≡ f(x)^q`. -/
theorem redHom_powSubst {q : Nat} [NeZero q] (hq : IsPrime q) (f : Polynomial Int) :
    (redHom q p).toFun ((powSubst q).toFun f) = (redHom q p).toFun f ^ q := by
  let frob : RingHom (ResRing q p) (ResRing q p) :=
    { toFun := fun y => y ^ q
      map_add := add_pow_char hq resRing_char
      map_mul := fun x y => mul_pow' x y q
      map_one := one_pow' q }
  have := polyHom_ext (RingHom.comp (redHom q p) (powSubst q)) (RingHom.comp frob (redHom q p))
    (fun c => by
      show (redHom q p).toFun (eval _ (mapPoly CHom (C c))) = ((redHom q p).toFun (C c)) ^ q
      rw [mapPoly_C, eval_C]
      show (redHom q p).toFun (C c) = _
      rw [redHom_C, ← RingHom.map_pow']
      exact congrArg (constHom q p).toFun (fin_pow_self hq _).symm)
    (by
      show (redHom q p).toFun (eval _ (mapPoly CHom X)) = ((redHom q p).toFun X) ^ q
      rw [mapPoly_X, eval_X, RingHom.map_pow']) f
  exact this

/-- **`σ_q` is the Frobenius at `q`.** For a prime `q ≠ p` and every `α ∈ ℤ[ζ_p]`,
`σ_q(α) ≡ α^q (mod q)`: under reduction `ℤ[ζ_p] → 𝔽_q[x]/(Φ_p)`, the automorphism
`ζ_p ↦ ζ_p^q` becomes the `q`-th power map. -/
theorem reduce_galAut {q : Nat} [NeZero q] (hq : IsPrime q) (hpq : ¬ p ∣ q) (α : intZeta p) :
    (reduce q hp).toFun (galAutInt hp hpq α) = (reduce q hp).toFun α ^ q := by
  obtain ⟨f, hf⟩ := α.2
  have eα : α = ⟨(evZeta p).toFun f, f, rfl⟩ := Subtype.ext hf.symm
  have eσ : galAutInt hp hpq α = ⟨(evZeta p).toFun ((powSubst q).toFun f), _, rfl⟩ := by
    apply Subtype.ext
    show ((galAut hp hpq).toFun ⟨α.1, _⟩).1 = _
    have e : (⟨α.1, intZeta_le hp α.2⟩ : cycloField hp) =
        ⟨(evZeta p).toFun f, intZeta_le hp ⟨f, rfl⟩⟩ := Subtype.ext hf.symm
    rw [e, galAut_evZeta hp hpq f]
  rw [eσ, eα, reduce_evZeta, reduce_evZeta, redHom_powSubst hq]

/-- The Gauss sum as an integer polynomial in `ζ_p`: `Σ_a (a/p) xᵃ`. -/
noncomputable def gaussPoly (p : Nat) : Polynomial Int :=
  rsum (fun a => C (legendre a p) * X ^ a) p

/-- `gaussPoly` evaluates to the Gauss sum at any `ζ` (in particular `g ∈ ℤ[ζ_p]`). -/
theorem eval_gaussPoly {R : Type} [CommRing R] (φ : RingHom (Polynomial Int) R)
    (hC : ∀ a : Int, φ.toFun (C a) = (a : R)) :
    φ.toFun (gaussPoly p) = gaussSum p (φ.toFun X) := by
  unfold gaussPoly gaussSum
  rw [RingHom.map_rsum]
  apply rsum_congr; intro a _
  rw [φ.map_mul, hC, RingHom.map_pow']

/-- **The Gauss sum reduces to the Gauss sum of `𝔽_q[x]/(Φ_p)`.** So the identity
`g^q = (q/p) g` of `Reciprocity.lean` is the reduction of `σ_q(g) = (q/p) g`. -/
theorem reduce_gaussSum {q : Nat} [NeZero q] :
    (reduce q hp).toFun ⟨(evZeta p).toFun (gaussPoly p), _, rfl⟩ = gaussSum p (zetaRes q p) := by
  rw [reduce_evZeta, eval_gaussPoly, redHom_X]
  intro a
  rw [redHom_C, RingHom.map_intCast]

/-- `g = gaussPoly(ζ_p)`: the complex Gauss sum lies in `ℤ[ζ_p]`. -/
theorem evZeta_gaussPoly : (evZeta p).toFun (gaussPoly p) = gaussSum p (zeta p) := by
  rw [eval_gaussPoly, evZeta_X]
  intro a
  show eval (zeta p) (mapPoly _ (C a)) = _; rw [mapPoly_C, eval_C]; rfl

end Frob

end Foundations.Langlands
