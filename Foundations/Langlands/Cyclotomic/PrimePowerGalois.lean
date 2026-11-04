import Foundations.Langlands.Cyclotomic.PrimePowerIrreducible
import Foundations.Langlands.Cyclotomic.Galois

/-!
# `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/n)ˣ` for prime powers `n = p^{k+1}`

This file repeats the Galois theory of `Field.lean` and `Galois.lean` for `n = p^{k+1}`, with
`ζ_n = e^{2πi/n}` and the minimal polynomial `Φ_n = Σ_{j<p} x^{j p^k}`
(`PrimePowerIrreducible.lean`).

* `ζ_n^a = 1` iff `n ∣ a`. So `ζ_n^a` is a root of `Φ_n` exactly when `p ∤ a`: then
  `(ζ_n^a)^{p^k}` is a `p`-th root of unity other than `1`.
* For each unit `a mod n` there is an automorphism `σ_a` of `ℚ(ζ_n)` with `σ_a(ζ_n) = ζ_n^a`
  (extension of embeddings plus irreducibility). It is determined by this value.
* Every automorphism sends `ζ_n` to a root of `Φ_n`. That root is an `n`-th root of unity,
  hence `ζ_n^j` for some `j < n` (root counting), and `p ∤ j` because `Φ_n(ζ_n^j) = p ≠ 0`
  when `p ∣ j`.

**Headline.** `cycloGaloisIsoPP : (ℤ/p^{k+1})ˣ ≃* Aut(ℚ(ζ_{p^{k+1}})/ℚ)`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield Foundations.Algebra.Group

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Roots of unity of order `n` -/

section RootsN

/-- `ζ_n^a = 1` exactly when `n ∣ a`. -/
theorem zeta_rpow_eq_one_iff {n a : Nat} (hn : 1 ≤ n) : rpow (zeta n) a = 1 ↔ n ∣ a := by
  have hζ : rpow (zeta n) n = 1 := zeta_rpow_self hn
  constructor
  · intro h
    apply Classical.byContradiction; intro hd
    have h' : rpow (zeta n) (a % n) = 1 :=
      (pow_mod_of_pow_eq_one (R := ℂ) hζ a).symm.trans h
    apply zeta_pow_ne_one (m := n) (k := a % n)
    · rcases Nat.eq_zero_or_pos (a % n) with h0 | h0
      · exact absurd (Nat.dvd_of_mod_eq_zero h0) hd
      · exact h0
    · exact Nat.mod_lt _ (by omega)
    · rw [C.pow_eq_rpow]; exact h'
  · rintro ⟨c, rfl⟩
    rw [rpow_mul', hζ, one_rpow']

/-- The powers `ζ_n^0, …, ζ_n^{n-1}` are distinct. -/
theorem zeta_rpow_inj {n a b : Nat} (hn : 1 ≤ n) (ha : a < n) (hb : b < n)
    (h : rpow (zeta n) a = rpow (zeta n) b) : a = b := by
  have key : ∀ a b, a < b → b < n → rpow (zeta n) a = rpow (zeta n) b → False := by
    intro a b hab hb e
    have hz : rpow (zeta n) a ≠ 0 := fun h0 => by
      have := eq_zero_of_rpow_eq_zero C.isDomain h0
      have h1 := zeta_rpow_self hn
      rw [this] at h1
      obtain ⟨r, hr⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
      rw [hr, zero_rpow_succ] at h1; exact C.isField.1 h1
    have e2 : rpow (zeta n) b = rpow (zeta n) a * rpow (zeta n) (b - a) := by
      rw [← rpow_add]; congr 1; omega
    rw [e2] at e
    have : rpow (zeta n) (b - a) = 1 :=
      (C.isDomain.mul_left_cancel hz (e.symm.trans (Ring.mul_one _).symm))
    have := (zeta_rpow_eq_one_iff hn).1 this
    have := Nat.le_of_dvd (by omega) this
    omega
  rcases Nat.lt_trichotomy a b with h' | h' | h'
  · exact (key a b h' hb h).elim
  · exact h'
  · exact (key b a h' ha h.symm).elim

/-- **All `n`-th roots of unity are powers of `ζ_n`.** -/
theorem eq_zeta_rpow {n : Nat} (hn : 1 ≤ n) {ω : ℂ} (hω : rpow ω n = 1) :
    ∃ j, j < n ∧ ω = rpow (zeta n) j := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  let Lst : List ℂ := ω :: (List.range (q + 1)).map (rpow (zeta (q + 1)))
  have hnd : Lst.Nodup := by
    rw [List.nodup_cons]
    constructor
    · intro hmem
      obtain ⟨k, hk, hk'⟩ := List.mem_map.1 hmem
      exact hne ⟨k, List.mem_range.1 hk, hk'.symm⟩
    · unfold List.Nodup
      rw [List.pairwise_map]
      exact (List.pairwise_lt_range (n := q + 1)).imp_of_mem fun {a b} ha hb hab e =>
        absurd (zeta_rpow_inj hn (List.mem_range.1 ha) (List.mem_range.1 hb) e) (Nat.ne_of_lt hab)
  have hroots : ∀ a, a ∈ Lst → eval a (binomial 1 q) = 0 := by
    intro a ha
    rw [eval_binomial]
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [hω]; exact Ring.add_neg_cancel _
    · obtain ⟨k, _, rfl⟩ := List.mem_map.1 ha
      rw [← rpow_mul', Nat.mul_comm, rpow_mul', zeta_rpow_self hn, one_rpow']
      exact Ring.add_neg_cancel _
  have := card_roots_le C.isDomain Lst (q + 1) (binomial 1 q) (binomial_ne_zero C.isDomain.1 1 q)
    (degLT_binomial 1 q) hnd hroots
  simp [Lst] at this
  omega

end RootsN

/-! ## The field `ℚ(ζ_{p^{k+1}})` -/

section FieldPP

variable {p : Nat} (hp : IsPrime p) (k : Nat)

/-- `p^{k+1} = p · p^k`. -/
theorem ppow_succ : p ^ (k + 1) = p * p ^ k := by rw [Nat.pow_succ, Nat.mul_comm]

include hp in
/-- `p^{k+1} ∣ a p^k` iff `p ∣ a`. -/
theorem ppow_dvd_iff (a : Nat) : p ^ (k + 1) ∣ a * p ^ k ↔ p ∣ a := by
  have hm : 0 < p ^ k := Nat.pow_pos (by have := hp.1; omega)
  rw [ppow_succ]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, Nat.eq_of_mul_eq_mul_right hm ?_⟩
    rw [hc]; grind
  · rintro ⟨c, rfl⟩; exact ⟨c, by grind⟩

/-- `Φ_{p^{k+1}}(γ) = Σ_{j<p} γ^{j p^k}`. -/
theorem aeval_cycloPP (γ : ℂ) :
    aeval Qc γ (cycloPP Qc p k) = rsum (fun j => rpow γ (j * p ^ k)) p := by
  unfold aeval; rw [mapPoly_cycloPP, eval_cycloPP]; rfl

/-- An `n`-th root of unity `ω` with `ω^{p^k} ≠ 1` is a root of `Φ_{p^{k+1}}`. -/
theorem aeval_cycloPP_root {ω : ℂ} (hω : rpow ω (p ^ (k + 1)) = 1) (hωm : rpow ω (p ^ k) ≠ 1) :
    aeval Qc ω (cycloPP Qc p k) = 0 := by
  rw [aeval_cycloPP]
  have : rsum (fun j => rpow ω (j * p ^ k)) p = rsum (fun j => rpow (rpow ω (p ^ k)) j) p :=
    rsum_congr p fun j _ => by rw [Nat.mul_comm, rpow_mul']
  rw [this]
  apply rsum_root_of_unity _ hωm
  rw [← rpow_mul', Nat.mul_comm, ← ppow_succ]; exact hω

include hp in
/-- `n = p^{k+1} ≥ 1`. -/
theorem ppow_pos : 1 ≤ p ^ (k + 1) := Nat.pow_pos (by have := hp.1; omega)

include hp in
/-- `ζ_n^a` is a root of `Φ_n` for `p ∤ a`. -/
theorem aeval_cycloPP_zeta_pow {a : Nat} (ha : ¬ p ∣ a) :
    aeval Qc (rpow (zeta (p ^ (k + 1))) a) (cycloPP Qc p k) = 0 := by
  apply aeval_cycloPP_root k
  · rw [← rpow_mul', Nat.mul_comm, rpow_mul', zeta_rpow_self (ppow_pos hp k), one_rpow']
  · rw [← rpow_mul']
    intro h
    exact ha ((ppow_dvd_iff hp k a).1 ((zeta_rpow_eq_one_iff (ppow_pos hp k)).1 h))

include hp in
/-- `ζ_n` is algebraic over `ℚ`. -/
theorem zetaPP_isAlgebraic : IsAlgebraic Qc (zeta (p ^ (k + 1))) := by
  refine ⟨cycloPP Qc p k, fun h => ?_, ?_⟩
  · -- `(X^{p^k} - 1) Φ_n = X^n - 1` is not zero (evaluate at `0`)
    have h1 := X_pow_sub_one_mul_cycloPP (R := Qc) p k
    rw [h, Ring.mul_zero] at h1
    have h2 := congrArg (eval (0 : Qc)) h1
    rw [eval_add, eval_neg] at h2
    rw [show eval (0 : Qc) 1 = 1 from (evalHom (0 : Qc)).map_one,
      show eval (0 : Qc) 0 = 0 from (evalHom (0 : Qc)).map_zero] at h2
    have h3 : eval (0 : Qc) ((X : Polynomial Qc) ^ (p ^ (k + 1))) = 0 := by
      show (evalHom (0 : Qc)).toFun _ = 0
      rw [RingHom.map_pow']
      show rpow (eval 0 X) _ = 0
      rw [eval_X]
      obtain ⟨r, hr⟩ : ∃ r, p ^ (k + 1) = r + 1 := ⟨p ^ (k + 1) - 1, by have := ppow_pos hp k; omega⟩
      rw [hr]; exact zero_rpow_succ r
    rw [h3, Ring.zero_add] at h2
    exact (Qc.isField C.isField).1 (by
      have := congrArg (fun x => -x) h2
      simp only [Ring.neg_neg, Ring.neg_zero] at this
      exact this)
  · have := aeval_cycloPP_zeta_pow hp k (a := 1)
      (fun h => by have := Nat.le_of_dvd (by decide) h; have := hp.1; omega)
    rwa [rpow_one'] at this

/-- **The cyclotomic field `ℚ(ζ_{p^{k+1}})`** inside `ℂ`. -/
noncomputable def cycloFieldPP : Subfield ℂ :=
  adjoin C.isField Qc (zeta (p ^ (k + 1))) (zetaPP_isAlgebraic hp k)

/-- `ℚ ⊆ ℚ(ζ_n)`. -/
theorem Qc_le_cycloFieldPP : Qc.le (cycloFieldPP hp k) := le_adjoin _ _ _ _

/-- `ζ_n ∈ ℚ(ζ_n)`. -/
theorem zetaPP_mem : zeta (p ^ (k + 1)) ∈ cycloFieldPP hp k := mem_adjoin_self _ _ _ _

/-- `ℚ(ζ_n)` is finite over `ℚ`. -/
theorem cycloFieldPP_finite : FiniteExt Qc (cycloFieldPP hp k) (Qc_le_cycloFieldPP hp k) :=
  adjoin_finite _ _ _ _

include hp in
/-- **The minimal polynomial of `ζ_{p^{k+1}}` is `Φ_{p^{k+1}}`.** -/
theorem aeval_zetaPP_eq_zero_iff (f : Polynomial Qc) :
    aeval Qc (zeta (p ^ (k + 1))) f = 0 ↔ Divides (cycloPP Qc p k) f := by
  obtain ⟨m, hm0, hm⟩ := exists_minpoly Qc (zeta (p ^ (k + 1))) C.isField (zetaPP_isAlgebraic hp k)
  have hirr : Irreducible (cycloPP Qc p k) := cycloPP_irreducible C.isField C.charZero hp k
  have hΦ : aeval Qc (zeta (p ^ (k + 1))) (cycloPP Qc p k) = 0 := by
    have := aeval_cycloPP_zeta_pow hp k (a := 1)
      (fun h => by have := Nat.le_of_dvd (by decide) h; have := hp.1; omega)
    rwa [rpow_one'] at this
  obtain ⟨c, hc⟩ := (hm _).1 hΦ
  have hmu : ¬ IsUnit m := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (aeval Qc (zeta (p ^ (k + 1)))) hu
    rw [aeval_mul, (hm m).2 ⟨1, (Ring.mul_one m).symm⟩, Ring.zero_mul, aeval_one] at h1
    exact C.isField.1 h1
  obtain ⟨d, hd⟩ : IsUnit c := (hirr.2.2 m c hc).resolve_left hmu
  have hmΦ : m = cycloPP Qc p k * d := by rw [hc, Ring.mul_assoc, hd, Ring.mul_one]
  constructor
  · intro h
    obtain ⟨e, he⟩ := (hm f).1 h
    exact ⟨d * e, by rw [he, hmΦ, Ring.mul_assoc]⟩
  · rintro ⟨e, rfl⟩
    rw [aeval_mul, hΦ, Ring.zero_mul]

/-- `ζ_n` as an element of `ℚ(ζ_n)`. -/
noncomputable def zetaKPP : cycloFieldPP hp k := ⟨zeta (p ^ (k + 1)), zetaPP_mem hp k⟩

include hp in
/-- **The automorphisms `σ_a` of `ℚ(ζ_n)` exist** for `p ∤ a`. -/
theorem exists_galAutPP {a : Nat} (ha : ¬ p ∣ a) :
    ∃ σ : FieldAut Qc (cycloFieldPP hp k),
      (σ.toFun (zetaKPP hp k)).1 = rpow (zeta (p ^ (k + 1))) a := by
  obtain ⟨τ, hτQ, hτζ, hτp⟩ := extend C.isField Qc (zeta (p ^ (k + 1))) (zetaPP_isAlgebraic hp k)
    Qc.incl (rpow (zeta (p ^ (k + 1))) a) (fun f hf => by
      obtain ⟨e, rfl⟩ := (aeval_zetaPP_eq_zero_iff hp k f).1 hf
      show aeval Qc _ _ = 0
      rw [aeval_mul, aeval_cycloPP_zeta_pow hp k ha, Ring.zero_mul])
  have hmem : ∀ y : cycloFieldPP hp k, τ.toFun y ∈ cycloFieldPP hp k := by
    intro y
    obtain ⟨f, hf⟩ := y.2
    have hy : y = ⟨aeval Qc (zeta (p ^ (k + 1))) f, (⟨f, rfl⟩ : aeval Qc (zeta (p ^ (k + 1))) f ∈
        adjoin C.isField Qc (zeta (p ^ (k + 1))) (zetaPP_isAlgebraic hp k))⟩ :=
      Subtype.ext hf.symm
    have e : τ.toFun y = eval (rpow (zeta (p ^ (k + 1))) a) (mapPoly Qc.incl f) :=
      (congrArg τ.toFun hy).trans (hτp f)
    rw [e]
    exact aeval_mem Qc _ (Qc_le_cycloFieldPP hp k) (rpow_mem (zetaPP_mem hp k) a) f
  let τ' : RingHom (cycloFieldPP hp k) (cycloFieldPP hp k) :=
    { toFun := fun y => ⟨τ.toFun y, hmem y⟩
      map_add := fun x y => Subtype.ext (τ.map_add x y)
      map_mul := fun x y => Subtype.ext (τ.map_mul x y)
      map_one := Subtype.ext τ.map_one }
  have hfix : ∀ x : cycloFieldPP hp k, x.1 ∈ Qc → τ'.toFun x = x := by
    intro x hx
    apply Subtype.ext
    show τ.toFun x = x.1
    exact hτQ ⟨x.1, hx⟩
  exact ⟨autOfRingHom C.isField (Qc_le_cycloFieldPP hp k) (cycloFieldPP_finite hp k) τ' hfix, hτζ⟩

/-- **The Galois automorphism `σ_a` of `ℚ(ζ_n)`**: `ζ_n ↦ ζ_n^a` (`p ∤ a`). -/
noncomputable def galAutPP {a : Nat} (ha : ¬ p ∣ a) : FieldAut Qc (cycloFieldPP hp k) :=
  Classical.choose (exists_galAutPP hp k ha)

/-- `σ_a(ζ_n) = ζ_n^a`. -/
theorem galAutPP_zeta {a : Nat} (ha : ¬ p ∣ a) :
    ((galAutPP hp k ha).toFun (zetaKPP hp k)).1 = rpow (zeta (p ^ (k + 1))) a :=
  Classical.choose_spec (exists_galAutPP hp k ha)

/-- **Rigidity**: automorphisms of `ℚ(ζ_n)` agreeing at `ζ_n` are equal. -/
theorem aut_ext_zetaPP {σ τ : FieldAut Qc (cycloFieldPP hp k)}
    (h : σ.toFun (zetaKPP hp k) = τ.toFun (zetaKPP hp k)) : σ = τ := by
  let ρ := τ⁻¹ * σ
  have hfix : ρ.toFun (zetaKPP hp k) = zetaKPP hp k := by
    rw [FieldAut.mul_apply, h]
    show τ.invFun (τ.toFun (zetaKPP hp k)) = zetaKPP hp k
    exact τ.left_inv _
  have hL := adjoin_le C.isField Qc (zeta (p ^ (k + 1))) (zetaPP_isAlgebraic hp k)
    (M := fixedField (cycloFieldPP hp k) (fun φ => φ = ρ)) (le_fixedField (Qc_le_cycloFieldPP hp k) _)
    ⟨zetaPP_mem hp k, fun φ hφ => by rw [hφ]; exact hfix⟩
  have hρ : ρ = 1 := FieldAut.ext fun x => by
    obtain ⟨_, hx⟩ := hL x.1 x.2
    exact hx ρ rfl
  calc σ = τ * (τ⁻¹ * σ) := by rw [← Group.mul_assoc, Group.mul_inv_cancel, Group.one_mul]
    _ = τ := by rw [show τ⁻¹ * σ = 1 from hρ, Group.mul_one]

/-- `σ_a = σ_b` when `a ≡ b (mod n)`. -/
theorem galAutPP_congr {a b : Nat} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    (hab : a % p ^ (k + 1) = b % p ^ (k + 1)) : galAutPP hp k ha = galAutPP hp k hb := by
  apply aut_ext_zetaPP
  apply Subtype.ext
  rw [galAutPP_zeta, galAutPP_zeta]
  have hζ : rpow (zeta (p ^ (k + 1))) (p ^ (k + 1)) = 1 := zeta_rpow_self (ppow_pos hp k)
  exact (pow_mod_of_pow_eq_one (R := ℂ) hζ a).trans
    (by rw [hab]; exact (pow_mod_of_pow_eq_one (R := ℂ) hζ b).symm)

/-- `σ_a σ_b = σ_{ab}`. -/
theorem galAutPP_mul {a b : Nat} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) (hab : ¬ p ∣ a * b) :
    galAutPP hp k hab = galAutPP hp k ha * galAutPP hp k hb := by
  apply aut_ext_zetaPP
  apply Subtype.ext
  rw [galAutPP_zeta, FieldAut.mul_apply]
  have e : (galAutPP hp k hb).toFun (zetaKPP hp k) = rpow (zetaKPP hp k) b :=
    Subtype.ext (by rw [galAutPP_zeta, Subfield.coe_rpow]; rfl)
  rw [e, FieldAut.map_rpow, Subfield.coe_rpow, galAutPP_zeta, rpow_mul']

omit hp in
/-- A unit modulo `p^{k+1}` is prime to `p`. -/
theorem not_dvd_of_unitPP (hp : IsPrime p) (u : ZModUnits (p ^ (k + 1))) : ¬ p ∣ u.1.val := by
  intro h
  have hpn : p ∣ p ^ (k + 1) := ⟨p ^ k, by rw [ppow_succ]⟩
  have h1 : p ∣ Nat.gcd u.1.val (p ^ (k + 1)) := Nat.dvd_gcd h hpn
  have h2 : Nat.gcd u.1.val (p ^ (k + 1)) = 1 := u.2
  rw [h2] at h1
  have := Nat.le_of_dvd (by decide) h1; have := hp.1; omega

/-- Automorphisms send roots of rational polynomials to roots: `σ(f(ζ_n)) = f(σ ζ_n)`. -/
theorem aut_aevalPP (σ : FieldAut Qc (cycloFieldPP hp k)) (f : Polynomial Qc) :
    (σ.toFun ⟨aeval Qc (zeta (p ^ (k + 1))) f,
      aeval_mem Qc _ (Qc_le_cycloFieldPP hp k) (zetaPP_mem hp k) f⟩).1 =
      aeval Qc (σ.toFun (zetaKPP hp k)).1 f := by
  let φ : RingHom (Polynomial Qc) ℂ :=
    { toFun := fun f => (σ.toFun ⟨aeval Qc (zeta (p ^ (k + 1))) f,
        aeval_mem Qc _ (Qc_le_cycloFieldPP hp k) (zetaPP_mem hp k) f⟩).1
      map_add := fun f g => by
        show _ = (σ.toFun _ + σ.toFun _).1
        rw [← σ.map_add]; congr 2; apply Subtype.ext; exact aeval_add Qc _ f g
      map_mul := fun f g => by
        show _ = (σ.toFun _ * σ.toFun _).1
        rw [← σ.map_mul]; congr 2; apply Subtype.ext; exact aeval_mul Qc _ f g
      map_one := by
        show _ = ((1 : cycloFieldPP hp k)).1
        rw [← σ.map_one]; congr 2; apply Subtype.ext; exact aeval_one Qc _ }
  have := polyHom_ext φ (aevalHom Qc (σ.toFun (zetaKPP hp k)).1)
    (fun c => by
      show (σ.toFun _).1 = aeval Qc _ (C c)
      have hmem : aeval Qc (zeta (p ^ (k + 1))) (C c) ∈ Qc := by rw [aeval_C]; exact c.2
      rw [σ.fix _ hmem]; exact (aeval_C Qc _ c).trans (aeval_C Qc _ c).symm)
    (by
      show (σ.toFun _).1 = aeval Qc _ X
      have e : (⟨aeval Qc (zeta (p ^ (k + 1))) X, aeval_mem Qc _ (Qc_le_cycloFieldPP hp k)
          (zetaPP_mem hp k) X⟩ : cycloFieldPP hp k) = zetaKPP hp k := Subtype.ext (aeval_X Qc _)
      rw [e, aeval_X]) f
  exact this

variable [NeZero (p ^ (k + 1))]

/-- **The Galois representation** `(ℤ/p^{k+1})ˣ → Aut(ℚ(ζ_n)/ℚ)`, `a ↦ σ_a`. -/
noncomputable def galHomPP : ZModUnits (p ^ (k + 1)) →* FieldAut Qc (cycloFieldPP hp k) where
  toFun u := galAutPP hp k (not_dvd_of_unitPP k hp u)
  map_mul u v := by
    have hmul : ¬ p ∣ u.1.val * v.1.val := fun h =>
      (hp.dvd_mul h).elim (not_dvd_of_unitPP k hp u) (not_dvd_of_unitPP k hp v)
    show galAutPP hp k (not_dvd_of_unitPP k hp (u * v)) = _
    rw [galAutPP_congr hp k (not_dvd_of_unitPP k hp (u * v)) hmul
      (by rw [ZModUnits.val_mul, Nat.mod_mod]), galAutPP_mul hp k _ _ hmul]

/-- `galHomPP` is injective. -/
theorem galHomPP_injective :
    ∀ u v : ZModUnits (p ^ (k + 1)), galHomPP hp k u = galHomPP hp k v → u = v := by
  intro u v h
  have h1 := congrArg (fun σ : FieldAut Qc (cycloFieldPP hp k) => (σ.toFun (zetaKPP hp k)).1) h
  change ((galAutPP hp k (not_dvd_of_unitPP k hp u)).toFun (zetaKPP hp k)).1 =
    ((galAutPP hp k (not_dvd_of_unitPP k hp v)).toFun (zetaKPP hp k)).1 at h1
  rw [galAutPP_zeta, galAutPP_zeta] at h1
  exact ZModUnits.ext (zeta_rpow_inj (ppow_pos hp k) u.1.isLt v.1.isLt h1)

/-- `galHomPP` is surjective. -/
theorem galHomPP_surjective :
    ∀ σ : FieldAut Qc (cycloFieldPP hp k), ∃ u, galHomPP hp k u = σ := by
  intro σ
  have h2 := hp.1
  have hn := ppow_pos hp k
  let ω := (σ.toFun (zetaKPP hp k)).1
  -- `ω` is a root of `Φ_n`
  have hΦ : aeval Qc ω (cycloPP Qc p k) = 0 := by
    rw [← aut_aevalPP hp k σ]
    have h0 : (⟨aeval Qc (zeta (p ^ (k + 1))) (cycloPP Qc p k), aeval_mem Qc _
        (Qc_le_cycloFieldPP hp k) (zetaPP_mem hp k) _⟩ : cycloFieldPP hp k) = 0 :=
      Subtype.ext ((aeval_zetaPP_eq_zero_iff hp k _).2 ⟨1, (Ring.mul_one _).symm⟩)
    rw [h0, FieldAut.map_zero]; rfl
  -- hence an `n`-th root of unity
  have hωn : rpow ω (p ^ (k + 1)) = 1 := by
    have h := congrArg (aeval Qc ω) (X_pow_sub_one_mul_cycloPP (R := Qc) p k)
    rw [aeval_mul, hΦ, Ring.mul_zero] at h
    have e : aeval Qc ω ((X : Polynomial Qc) ^ (p ^ (k + 1)) + -1) = rpow ω (p ^ (k + 1)) + -1 := by
      rw [aeval_add, aeval_neg, aeval_one]
      show (aevalHom Qc ω).toFun _ + _ = _
      rw [RingHom.map_pow']
      show rpow (aeval Qc ω X) _ + _ = _
      rw [aeval_X]
    rw [e] at h
    have := congrArg (· + 1) h
    rw [Ring.add_assoc, Ring.neg_add_cancel, Ring.add_zero, Ring.zero_add] at this
    exact this.symm
  obtain ⟨j, hj, hjω⟩ := eq_zeta_rpow hn hωn
  -- `p ∤ j`, since otherwise `Φ_n(ω) = p ≠ 0`
  have hpj : ¬ p ∣ j := by
    intro hd
    have hωm : rpow ω (p ^ k) = 1 := by
      rw [hjω, ← rpow_mul', zeta_rpow_eq_one_iff hn]
      exact (ppow_dvd_iff hp k j).2 hd
    rw [aeval_cycloPP] at hΦ
    have : rsum (fun i => rpow ω (i * p ^ k)) p = rsum (fun _ => (1 : ℂ)) p :=
      rsum_congr p fun i _ => by rw [Nat.mul_comm, rpow_mul', hωm, one_rpow']
    rw [this, rsum_const, Ring.mul_one] at hΦ
    exact absurd (C.charZero _ hΦ) (by omega)
  have hcop : Nat.Coprime j (p ^ (k + 1)) := by
    apply Nat.Coprime.pow_right
    show Nat.gcd j p = 1
    rcases hp.2 _ (Nat.gcd_dvd_right j p) with h | h
    · exact h
    · exact absurd (h ▸ Nat.gcd_dvd_left j p) hpj
  refine ⟨⟨⟨j, hj⟩, hcop⟩, aut_ext_zetaPP hp k (Subtype.ext ?_)⟩
  show ((galAutPP hp k (not_dvd_of_unitPP k hp _)).toFun (zetaKPP hp k)).1 = _
  rw [galAutPP_zeta]
  exact hjω.symm

/-- **The Galois group of `ℚ(ζ_{p^{k+1}})` over `ℚ`.** For a prime `p` and `k ≥ 0`,
`Aut(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ` with `n = p^{k+1}`, the unit `a` acting by `ζ_n ↦ ζ_n^a`. -/
noncomputable def cycloGaloisIsoPP : ZModUnits (p ^ (k + 1)) ≃* FieldAut Qc (cycloFieldPP hp k) :=
  Iso.ofBijective (galHomPP hp k) (galHomPP_injective hp k) (galHomPP_surjective hp k)

/-- The isomorphism sends `a` to the automorphism `ζ_n ↦ ζ_n^a`. -/
theorem cycloGaloisIsoPP_zeta (u : ZModUnits (p ^ (k + 1))) :
    (((cycloGaloisIsoPP hp k) u).toFun (zetaKPP hp k)).1 = rpow (zeta (p ^ (k + 1))) u.1.val :=
  galAutPP_zeta hp k (not_dvd_of_unitPP k hp u)

end FieldPP

end Foundations.Langlands
