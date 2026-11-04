import Foundations.Langlands.Cyclotomic.MonicPoly

/-!
# The cyclotomic polynomial `Φ_n` over `ℂ`

For every `n ≥ 1` the **primitive `n`-th roots of unity** are the powers `ζ_n^a` with
`0 ≤ a < n` and `gcd(a, n) = 1`, where `ζ_n = e^{2πi/n}`. The `n`-th cyclotomic polynomial is

  `Φ_n(x) = ∏_{a < n, gcd(a, n) = 1} (x - ζ_n^a)`  (`cycloC`).

This is the definition used here. It is a monic polynomial over `ℂ` of degree `φ(n)`, Euler's
totient (`natDegree_cycloC`), and it is a factor of `xⁿ - 1`. Indeed

  `xⁿ - 1 = ∏_{a < n} (x - ζ_n^a) = Φ_n(x) · ∏_{a < n, gcd(a, n) ≠ 1} (x - ζ_n^a)`
  (`X_pow_sub_one_eq`),

the first equality because the `n` distinct powers `ζ_n^a` are roots of the monic polynomial
`xⁿ - 1` of degree `n`. That `Φ_n` has integer coefficients and is irreducible over `ℚ` is
proved in `IrreducibleN.lean`. There it is identified with the minimal polynomial of `ζ_n`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.Polynomial Foundations.NumberTheory
open Foundations.Algebra.Subfield

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

/-! ## Exponents -/

/-- The exponents `a < n` with `gcd(a, n) = 1`. -/
def unitExps (n : Nat) : List Nat := (List.range n).filter (fun a => decide (Nat.Coprime a n))

/-- The exponents `a < n` with `gcd(a, n) ≠ 1`. -/
def nonUnitExps (n : Nat) : List Nat :=
  (List.range n).filter (fun a => !decide (Nat.Coprime a n))

/-- Membership in `unitExps n`. -/
theorem mem_unitExps {n a : Nat} : a ∈ unitExps n ↔ a < n ∧ Nat.Coprime a n := by
  unfold unitExps; simp

/-- Membership in `nonUnitExps n`. -/
theorem mem_nonUnitExps {n a : Nat} : a ∈ nonUnitExps n ↔ a < n ∧ ¬ Nat.Coprime a n := by
  unfold nonUnitExps; simp

/-- There are `φ(n)` exponents `a < n` prime to `n`. -/
theorem length_unitExps (n : Nat) : (unitExps n).length = totient n := by
  unfold unitExps totient
  rw [← List.countP_eq_length_filter, ← finRange_map_val, List.countP_map]
  rfl

/-! ## Powers of `ζ_n` -/

/-- Distinct exponents below `n` give distinct powers of `ζ_n`. -/
theorem nodup_zeta_pow {n : Nat} (hn : 1 ≤ n) :
    ∀ {l : List Nat}, l.Nodup → (∀ a, a ∈ l → a < n) →
      (l.map (fun a => rpow (zeta n) a)).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hl, hlt => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_zeta_pow hn hl.2 (fun b hb => hlt b (List.mem_cons_of_mem a hb))⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    have := zeta_rpow_inj hn (hlt b (List.mem_cons_of_mem a hb)) (hlt a List.mem_cons_self) e
    exact hl.1 (this ▸ hb)

/-- Every power of `ζ_n` is a root of `xⁿ - 1`. -/
theorem eval_X_pow_sub_one_zeta_pow {n : Nat} (hn : 1 ≤ n) (a : Nat) :
    eval (rpow (zeta n) a) ((X : Polynomial ℂ) ^ n + -1) = 0 := by
  rw [eval_add, eval_neg]
  show (evalHom (rpow (zeta n) a)).toFun _ + -(evalHom (rpow (zeta n) a)).toFun 1 = 0
  rw [RingHom.map_pow', (evalHom _).map_one]
  show rpow (eval _ X) n + -1 = 0
  rw [eval_X, ← rpow_mul', Nat.mul_comm, rpow_mul', zeta_rpow_self hn, one_rpow']
  exact Ring.add_neg_cancel _

/-! ## The polynomial -/

/-- The primitive `n`-th roots of unity `ζ_n^a`, `a < n`, `gcd(a, n) = 1`. -/
noncomputable def primRoots (n : Nat) : List ℂ := (unitExps n).map (fun a => rpow (zeta n) a)

/-- The remaining `n`-th roots of unity `ζ_n^a`, `a < n`, `gcd(a, n) ≠ 1`. -/
noncomputable def nonPrimRoots (n : Nat) : List ℂ :=
  (nonUnitExps n).map (fun a => rpow (zeta n) a)

/-- **The `n`-th cyclotomic polynomial** over `ℂ`: `Φ_n = ∏ (x - ζ)` over the primitive `n`-th
roots of unity `ζ = ζ_n^a`, `a < n`, `gcd(a, n) = 1`. -/
noncomputable def cycloC (n : Nat) : Polynomial ℂ := prodLin (primRoots n)

/-- `Φ_n` is monic of degree `φ(n)`. -/
theorem monic_cycloC (n : Nat) : Monic (cycloC n) (totient n) := by
  have := monic_prodLin (primRoots n)
  unfold primRoots at this
  rwa [List.length_map, length_unitExps] at this

/-- **The degree of `Φ_n` is `φ(n)`.** -/
theorem natDegree_cycloC (n : Nat) : natDegree (cycloC n) = totient n :=
  (monic_cycloC n).natDegree_eq C.isField.1

/-- The primitive `n`-th roots of unity are distinct. -/
theorem nodup_primRoots {n : Nat} (hn : 1 ≤ n) : (primRoots n).Nodup :=
  nodup_zeta_pow hn (List.Nodup.sublist List.filter_sublist List.nodup_range)
    (fun _ ha => (mem_unitExps.1 ha).1)

/-- **`xⁿ - 1 = Φ_n · ∏_{gcd(a,n) ≠ 1} (x - ζ_n^a)`** over `ℂ`. -/
theorem X_pow_sub_one_eq {n : Nat} (hn : 1 ≤ n) :
    (X : Polynomial ℂ) ^ n + -1 = cycloC n * prodLin (nonPrimRoots n) := by
  let all : List ℂ := (List.range n).map (fun a => rpow (zeta n) a)
  have hnd : all.Nodup := nodup_zeta_pow hn List.nodup_range (fun _ ha => List.mem_range.1 ha)
  obtain ⟨c, hc⟩ := prodLin_dvd C.isDomain all _ hnd (fun x hx => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
    exact eval_X_pow_sub_one_zeta_pow hn a)
  have hmall : Monic (prodLin all) n := by
    have := monic_prodLin all; rwa [List.length_map, List.length_range] at this
  obtain ⟨_, hcm⟩ := hmall.of_mul C.isDomain (monic_X_pow_sub_one hn) hc.symm
  rw [Nat.sub_self] at hcm
  rw [hc, hcm.eq_one, Ring.mul_one]
  have hperm := (List.filter_append_perm (fun a => decide (Nat.Coprime a n)) (List.range n)).map
    (fun a => rpow (zeta n) a)
  rw [List.map_append] at hperm
  rw [← prodLin_perm hperm, prodLin_append]
  rfl

/-- A product of linear factors vanishes at each of its roots. -/
theorem eval_prodLin_of_mem {R : Type} [CommRing R] {a : R} :
    ∀ {L : List R}, a ∈ L → eval a (prodLin L) = 0
  | b :: L, h => by
    show eval a (linear b * prodLin L) = 0
    rw [eval_mul]
    rcases List.mem_cons.1 h with rfl | h
    · rw [eval_linear, Ring.zero_mul]
    · rw [eval_prodLin_of_mem h, Ring.mul_zero]

/-- `Φ_n` vanishes at every primitive `n`-th root of unity. -/
theorem eval_cycloC_zeta_pow {n a : Nat} (ha : Nat.Coprime a n) (han : a < n) :
    eval (rpow (zeta n) a) (cycloC n) = 0 :=
  eval_prodLin_of_mem (List.mem_map.2 ⟨a, mem_unitExps.2 ⟨han, ha⟩, rfl⟩)

end Foundations.Langlands
