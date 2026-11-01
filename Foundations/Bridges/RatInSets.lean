import Foundations.Bridges.IntInSets
import Foundations.Numbers.Rat

/-!
# The rationals as a set

With the set ℤ of `IntInSets` in hand, the rationals are built in the set-theoretic
universe by the same recipe one level up:

* a fraction is a Kuratowski pair `⟪x, k⟫` with `x ∈ ℤ` (a ZF integer, itself a set
  of pairs of von Neumann naturals) and `k ∈ ω ∖ {∅}` a nonzero von Neumann natural;
* `⟪x, k⟫ ~ ⟪y, m⟫` iff `x · m = y · k`, computed with the set-theoretic
  multiplication of ℤ (a natural `m` being read as the ZF integer `[⟪m, ∅⟫]`);
* **the set ℚ** is the set of equivalence classes, separated out of
  `𝒫(ℤ × (ω ∖ {∅}))`;
* `⟪x, k⟫ + ⟪y, m⟫ = ⟪x·m + y·k, k ·ω m⟫`, `⟪x, k⟫ · ⟪y, m⟫ = ⟪x·y, k ·ω m⟫`,
  `−⟪x, k⟫ = ⟪−x, k⟫`, and `⟪x, k⟫ ≤ ⟪y, m⟫ ↔ x·m ≤ y·k`, lifted to classes.

Again every object is a pure set. We prove that this ZF-ℚ is isomorphic to Part
II's quotient type `Q`: the comparison map is a bijection onto the members of the
set ℚ preserving `0`, `1`, `+`, `−`, `·` and `≤`. (The reciprocal is not
transported separately: being an isomorphism of ordered rings onto a set, the
comparison map carries Part II's field inverse along with everything else.)

Part II represented a fraction by two Lean integers; the dictionary between the two
representations goes through `intToSet : Int → ℤ_ZF` of the previous file.
-/

namespace Foundations.Bridges

open Foundations.Sets Foundations.Sets.ZFSet Foundations.Numbers

/-! ## Positive naturals and the representatives of fractions -/

/-- The nonzero von Neumann naturals `ω ∖ {∅}`, by separation. -/
noncomputable def omegaPos : ZFSet := sep (fun k => k ≠ ∅) ω

/-- The members of `ω ∖ {∅}` are the numerals `vn m` with `m ≠ 0`. -/
theorem mem_omegaPos {k : ZFSet} : k ∈ omegaPos ↔ ∃ m, m ≠ 0 ∧ k = vn m := by
  simp only [omegaPos, mem_sep]
  constructor
  · rintro ⟨hk, hne⟩
    obtain ⟨m, rfl⟩ := mem_omega.1 hk
    refine ⟨m, fun h => hne (by rw [h]; rfl), rfl⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨vn_mem_omega m, ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact succ_ne_empty _

/-- A von Neumann natural read as a ZF integer: `k ↦ [⟪k, ∅⟫]`. -/
noncomputable def natZ (k : ZFSet) : ZFSet := ZModel.cls ⟪k, ∅⟫

/-- `natZ (vn k)` is the ZF integer of the Lean integer `k`. -/
theorem natZ_vn (k : Nat) : natZ (vn k) = intToSet (k : Int) := (intToSet_natCast k).symm

/-- The set of representatives of fractions: `ℤ × (ω ∖ {∅})`. -/
noncomputable def QReps : ZFSet := prod ZInt omegaPos

/-- The **equivalence of fractions**, set-theoretically: `⟪x, k⟫ ~ ⟪y, m⟫` iff both are
representatives and `x · m = y · k` in the set ℤ. -/
def QRel (p q : ZFSet) : Prop :=
  p ∈ QReps ∧ q ∈ QReps ∧ zmul (pfst p) (natZ (psnd q)) = zmul (pfst q) (natZ (psnd p))

/-- Encoding a Part II fraction `n/d` as the pair `⟪n, d⟫` of a ZF integer and a
nonzero von Neumann natural. -/
noncomputable def fracEnc (f : Frac) : ZFSet := ⟪intToSet f.num, vn f.den.toNat⟫

/-- The denominator of an encoded fraction, as a ZF integer. -/
theorem natZ_den (f : Frac) : natZ (vn f.den.toNat) = intToSet f.den := by
  rw [natZ_vn]
  congr 1
  have := f.den_pos
  omega

/-- Encoded fractions are representatives. -/
theorem fracEnc_mem (f : Frac) : fracEnc f ∈ QReps := by
  refine kpair_mem_prod.2 ⟨intToSet_mem _, mem_omegaPos.2 ⟨f.den.toNat, ?_, rfl⟩⟩
  have := f.den_pos
  omega

/-- The ZF rationals as a set-theoretic model of Part II's quotient type `Q`. -/
noncomputable def QModel : ZFModel Frac where
  S := QReps
  R := QRel
  enc := fracEnc
  enc_mem := fracEnc_mem
  enc_surj p hp := by
    obtain ⟨x, hx, k, hk, rfl⟩ := mem_prod.1 hp
    obtain ⟨i, rfl⟩ := intToSet_surj hx
    obtain ⟨m, hm, rfl⟩ := mem_omegaPos.1 hk
    refine ⟨⟨i, (m : Int), by omega⟩, ?_⟩
    simp only [fracEnc, Int.toNat_natCast]
  rel_iff a b := by
    show QRel (fracEnc a) (fracEnc b) ↔ _
    simp only [QRel, fracEnc_mem, true_and]
    simp only [fracEnc, pfst_kpair, psnd_kpair, natZ_den, ← intToSet_mul, frac_rel_iff]
    exact ⟨fun h => intToSet_injective h, fun h => by rw [h]⟩
  rel_mem _ _ h := ⟨h.1, h.2.1⟩

/-- **The set ℚ** of Zermelo–Fraenkel rationals. -/
noncomputable def QSet : ZFSet := QModel.carrier

/-- Sum of fraction representatives: `⟪x, k⟫ + ⟪y, m⟫ = ⟪x·m + y·k, k ·ω m⟫`. -/
noncomputable def qaddP (p q : ZFSet) : ZFSet :=
  ⟪zadd (zmul (pfst p) (natZ (psnd q))) (zmul (pfst q) (natZ (psnd p))), psnd p *ω psnd q⟫

/-- Product of fraction representatives: `⟪x, k⟫ · ⟪y, m⟫ = ⟪x·y, k ·ω m⟫`. -/
noncomputable def qmulP (p q : ZFSet) : ZFSet := ⟪zmul (pfst p) (pfst q), psnd p *ω psnd q⟫

/-- Negation of a fraction representative: `−⟪x, k⟫ = ⟪−x, k⟫`. -/
noncomputable def qnegP (p : ZFSet) : ZFSet := ⟪zneg (pfst p), psnd p⟫

/-- Order of fraction representatives: `⟪x, k⟫ ≤ ⟪y, m⟫ ↔ x·m ≤ y·k`. -/
def qleP (p q : ZFSet) : Prop := zle (zmul (pfst p) (natZ (psnd q))) (zmul (pfst q) (natZ (psnd p)))

/-- Addition of ZF rationals. -/
noncomputable def qadd : ZFSet → ZFSet → ZFSet := QModel.lift2 qaddP

/-- Multiplication of ZF rationals. -/
noncomputable def qmul : ZFSet → ZFSet → ZFSet := QModel.lift2 qmulP

/-- Negation of ZF rationals. -/
noncomputable def qneg : ZFSet → ZFSet := QModel.lift1 qnegP

/-- The order on ZF rationals. -/
def qle : ZFSet → ZFSet → Prop := liftRel qleP

/-- The strict order on ZF rationals. -/
def qlt (x y : ZFSet) : Prop := qle x y ∧ ¬ qle y x

/-- The ZF rational zero: the class of `⟪0_ℤ, 1⟫`. -/
noncomputable def qzero : ZFSet := QModel.cls ⟪zzero, vn 1⟫

/-- The ZF rational one: the class of `⟪1_ℤ, 1⟫`. -/
noncomputable def qone : ZFSet := QModel.cls ⟪zone, vn 1⟫

/-! ## The comparison with Part II -/

/-- The **comparison map** from Part II's rationals to the ZF rationals. -/
noncomputable def qToSet (x : Q) : ZFSet := QModel.toSet x

/-- The comparison map lands in the set ℚ. -/
theorem qToSet_mem (x : Q) : qToSet x ∈ QSet := QModel.toSet_mem x

/-- The comparison map is injective. -/
theorem qToSet_injective : Function.Injective qToSet := QModel.toSet_injective

/-- Every member of the set ℚ comes from a Part II rational. -/
theorem qToSet_surj {x : ZFSet} (hx : x ∈ QSet) : ∃ y : Q, qToSet y = x := QModel.toSet_surj hx

/-- Product of denominators, read off in `ω`. -/
theorem vn_toNat_mul {b d : Int} (hb : 0 < b) (hd : 0 < d) :
    vn b.toNat *ω vn d.toNat = vn (b * d).toNat := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, b = m := ⟨b.toNat, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n : Nat, d = n := ⟨d.toNat, by omega⟩
  rw [← Int.natCast_mul, Int.toNat_natCast, Int.toNat_natCast, Int.toNat_natCast, vn_mul]

/-- Congruence for a binary operation on `Q`. -/
theorem Q_congr2 (op : Q → Q → Q) {x x' y y' : Q} (h₁ : x = x') (h₂ : y = y') :
    op x y = op x' y' := by rw [h₁, h₂]

/-- The comparison map preserves zero. -/
theorem qToSet_zero : qToSet 0 = qzero := by
  show QModel.cls (fracEnc _) = _
  simp only [fracEnc, qzero]
  rfl

/-- The comparison map preserves one. -/
theorem qToSet_one : qToSet 1 = qone := by
  show QModel.cls (fracEnc _) = _
  simp only [fracEnc, qone]
  rfl

/-- The comparison map preserves addition. -/
theorem qToSet_add (x y : Q) : qToSet (x + y) = qadd (qToSet x) (qToSet y) := by
  induction x using Q.ind with
  | _ a b hb =>
  induction y using Q.ind with
  | _ c d hd =>
  exact QModel.toSet_lift2 qaddP
    (fun p q => ⟨p.num * q.den + q.num * p.den, p.den * q.den, Int.mul_pos p.den_pos q.den_pos⟩)
    (fun p p' q q' h₁ h₂ => Q.mk_eq_mk.1 (Q_congr2 (· + ·)
      ((Q.mk_eq_mk (hb := p.den_pos) (hd := p'.den_pos)).2 h₁)
      ((Q.mk_eq_mk (hb := q.den_pos) (hd := q'.den_pos)).2 h₂)))
    (fun p q => by
      simp only [QModel, qaddP, fracEnc, pfst_kpair, psnd_kpair, natZ_den, ← intToSet_mul,
        ← intToSet_add, vn_toNat_mul p.den_pos q.den_pos])
    ⟨a, b, hb⟩ ⟨c, d, hd⟩

/-- The comparison map preserves multiplication. -/
theorem qToSet_mul (x y : Q) : qToSet (x * y) = qmul (qToSet x) (qToSet y) := by
  induction x using Q.ind with
  | _ a b hb =>
  induction y using Q.ind with
  | _ c d hd =>
  exact QModel.toSet_lift2 qmulP
    (fun p q => ⟨p.num * q.num, p.den * q.den, Int.mul_pos p.den_pos q.den_pos⟩)
    (fun p p' q q' h₁ h₂ => Q.mk_eq_mk.1 (Q_congr2 (· * ·)
      ((Q.mk_eq_mk (hb := p.den_pos) (hd := p'.den_pos)).2 h₁)
      ((Q.mk_eq_mk (hb := q.den_pos) (hd := q'.den_pos)).2 h₂)))
    (fun p q => by
      simp only [QModel, qmulP, fracEnc, pfst_kpair, psnd_kpair, ← intToSet_mul,
        vn_toNat_mul p.den_pos q.den_pos])
    ⟨a, b, hb⟩ ⟨c, d, hd⟩

/-- The comparison map preserves negation. -/
theorem qToSet_neg (x : Q) : qToSet (-x) = qneg (qToSet x) := by
  induction x using Q.ind with
  | _ a b hb =>
  exact (QModel.lift1_enc qnegP (fun p => ⟨-p.num, p.den, p.den_pos⟩)
    (fun p p' h => Q.mk_eq_mk.1 (congrArg (- ·)
      ((Q.mk_eq_mk (hb := p.den_pos) (hd := p'.den_pos)).2 h)))
    (fun p => by simp only [QModel, qnegP, fracEnc, pfst_kpair, psnd_kpair, ← intToSet_neg])
    ⟨a, b, hb⟩).symm

/-- The comparison map preserves and reflects the order. -/
theorem qToSet_le (x y : Q) : x ≤ y ↔ qle (qToSet x) (qToSet y) := by
  induction x using Q.ind with
  | _ a b hb =>
  induction y using Q.ind with
  | _ c d hd =>
  refine (QModel.liftRel_enc qleP (fun p q => p.num * q.den ≤ q.num * p.den) ?_ ?_
    ⟨a, b, hb⟩ ⟨c, d, hd⟩).symm
  · intro p p' q q' h₁ h₂
    have e := (Q.mk_eq_mk (hb := p.den_pos) (hd := p'.den_pos)).2 h₁
    have e' := (Q.mk_eq_mk (hb := q.den_pos) (hd := q'.den_pos)).2 h₂
    have := Q.mk_le p.num p.den q.num q.den p.den_pos q.den_pos
    rw [e, e', Q.mk_le] at this
    exact this.symm
  · intro p q
    simp only [QModel, qleP, fracEnc, pfst_kpair, psnd_kpair, natZ_den, ← intToSet_mul,
      intToSet_le]

/-- The comparison map preserves and reflects the strict order. -/
theorem qToSet_lt (x y : Q) : x < y ↔ qlt (qToSet x) (qToSet y) := by
  show (x ≤ y ∧ ¬ y ≤ x) ↔ _
  rw [qToSet_le, qToSet_le]; rfl

/-- **The rationals live in the set-theoretic universe.** The comparison map from
Part II's rationals `Q` to the ZF set `ℚ` (classes of pairs `⟪x, k⟫` with `x` in the
ZF set `ℤ` and `k ∈ ω ∖ {∅}`) is a bijection onto the members of `ℚ` preserving
`0`, `1`, addition, negation, multiplication and order. -/
theorem rat_in_sets :
    Bijective (fun x : Q => (⟨qToSet x, qToSet_mem x⟩ : {s : ZFSet // s ∈ QSet})) ∧
    qToSet 0 = qzero ∧ qToSet 1 = qone ∧
    (∀ x y, qToSet (x + y) = qadd (qToSet x) (qToSet y)) ∧
    (∀ x, qToSet (-x) = qneg (qToSet x)) ∧
    (∀ x y, qToSet (x * y) = qmul (qToSet x) (qToSet y)) ∧
    (∀ x y, x ≤ y ↔ qle (qToSet x) (qToSet y)) :=
  ⟨QModel.bij.bijective, qToSet_zero, qToSet_one, qToSet_add, qToSet_neg, qToSet_mul, qToSet_le⟩

/-- **The set ℚ is an ordered field**, transported: its addition, multiplication and
order, defined purely set-theoretically, satisfy for instance commutativity of `·`
and the cancellation of a nonzero element by its (transported) inverse — the
argument is that each law holds in `Q` and the comparison map is an isomorphism. -/
theorem qset_field_laws {x y : ZFSet} (hx : x ∈ QSet) (hy : y ∈ QSet) :
    qmul x y = qmul y x ∧
    (x ≠ qzero → ∃ z ∈ QSet, qmul x z = qone) := by
  obtain ⟨a, rfl⟩ := qToSet_surj hx
  obtain ⟨b, rfl⟩ := qToSet_surj hy
  refine ⟨by rw [← qToSet_mul, ← qToSet_mul, Q.mul_comm], fun hne => ?_⟩
  have ha : a ≠ 0 := fun h => hne (by rw [h, qToSet_zero])
  exact ⟨qToSet a⁻¹, qToSet_mem _, by rw [← qToSet_mul, Q.mul_inv_cancel ha, qToSet_one]⟩

end Foundations.Bridges
