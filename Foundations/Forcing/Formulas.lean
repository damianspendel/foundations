import Foundations.Forcing.CheckNames
import Foundations.Forcing.BSetZF

/-!
# Set-theoretic notions as formulas, and their Boolean truth values

To state the Continuum Hypothesis as a sentence of the first-order language `LSet` (whose
only non-logical symbol is `∈`), we build up the usual definitions as formula
combinators: `x ⊆ y`, ordered pairs, "`f` is a function from `X` to `Y`", "`f` is
injective on `X`", "`w` is `ω`" and "`p` is the power set of `w`". Each combinator takes
*terms* as arguments and lifts them past its own quantifiers with `up`, so combinators nest
freely.

For each combinator we compute its truth value in `V^B` as an explicit Boolean expression in
names (`val_subsetF`, `val_pmF`, `val_isFuncF`, …). Ordered pairs are Kuratowski pairs: the
formula "`z = (a, b)`" has value exactly `⟦z = {{a, a}, {a, b}}⟧` (`val_opairF`), and
"`(a, b) ∈ f`" has value `⟦(a, b) ∈ f⟧` for the pair name (`val_pmF`).

Functions are coded as usual by sets of pairs. `isFuncF f X Y` says: every `a ∈ X` has some
`b ∈ Y` with `(a, b) ∈ f`, and for `a ∈ X` such a `b` is unique. Elements of `f` outside `X × Y`
are not forbidden. For statements "there is a function/injection from `X` to `Y`" this is
equivalent to the textbook definition (restrict `f`), an informal remark that is not
formalised.

Finally `CH` is the sentence

> for all `w`, `p`: if `w = ω` and `p = 𝒫(w)`, then every `x ⊆ p` admits an injection into
> `w` or receives an injection from `p`,

that is, every subset of `𝒫(ω)` is countable or has the cardinality of `𝒫(ω)`. Here "`w = ω`"
is expressed as "`w` is inductive and contained in every inductive set".
-/

namespace Foundations.Forcing

open Foundations.Logic.FO CBA BStructure

-- The truth-value computations below use one shared simp set; not every lemma fires in
-- every computation.
set_option linter.unusedSimpArgs false

variable {B : Type} [CompleteBooleanAlgebra B]

/-! ### Semantic notions on names -/

namespace BSet

/-- `⟦x ⊆ y⟧ = ⨅_z (⟦z ∈ x⟧ ⇨ ⟦z ∈ y⟧)`. -/
def subset (x y : BSet B) : B := iInf fun z => mem z x ⇨ mem z y

/-- `⟦(a, b) ∈ f⟧`, membership of the Kuratowski pair name. -/
def pm (a b f : BSet B) : B := mem (opair a b) f

/-- `⟦f is a function from X to Y⟧`: totality on `X` into `Y` and single-valuedness on `X`. -/
def isFunc (f X Y : BSet B) : B :=
  (iInf fun a => mem a X ⇨ iSup fun b => mem b Y ⊓ pm a b f) ⊓
  (iInf fun a => mem a X ⇨ iInf fun b => iInf fun b' => (pm a b f ⊓ pm a b' f) ⇨ eq b b')

/-- `⟦f is injective on X⟧`. -/
def isInj (f X : BSet B) : B :=
  iInf fun a => iInf fun a' => iInf fun b => (mem a X ⊓ mem a' X ⊓ pm a b f ⊓ pm a' b f) ⇨ eq a a'

/-- `⟦e has no members⟧`. -/
def isEmpty (e : BSet B) : B := iInf fun z => mem z e ⇨ ⊥

/-- `⟦s = y ∪ {y}⟧`. -/
def isSucc (s y : BSet B) : B := iInf fun w => mem w s ⇔ (mem w y ⊔ eq w y)

/-- `⟦v is inductive⟧`: contains an empty set and is closed under successor. -/
def isInductive (v : BSet B) : B :=
  (iSup fun e => mem e v ⊓ isEmpty e) ⊓ (iInf fun y => mem y v ⇨ iSup fun s => mem s v ⊓ isSucc s y)

/-- `⟦w = ω⟧`: `w` is inductive and contained in every inductive set. -/
def isOmega (w : BSet B) : B := isInductive w ⊓ iInf fun v => isInductive v ⇨ subset w v

/-- `⟦p = 𝒫(w)⟧`. -/
def isPow (p w : BSet B) : B := iInf fun z => mem z p ⇔ subset z w

/-- Pair membership respects equality in the second coordinate. -/
theorem pm_congr_right (a b b' f : BSet B) : eq b b' ⊓ pm a b f ≤ pm a b' f :=
  le_trans' (inf_le_inf (le_trans' (le_inf _ _ _ (by rw [eq_self]; exact le_top') le_rfl)
    (opair_congr a a b b')) le_rfl) (mem_congr_left _ _ f)

/-- Pair membership respects equality in the first coordinate. -/
theorem pm_congr_left (a a' b f : BSet B) : eq a a' ⊓ pm a b f ≤ pm a' b f :=
  le_trans' (inf_le_inf (le_trans' (le_inf _ _ _ le_rfl (by rw [eq_self]; exact le_top'))
    (opair_congr a a' b b)) le_rfl) (mem_congr_left _ _ f)

end BSet

/-! ### Formula combinators -/

/-- Lift a term past one new binder. -/
def up (t : Term LSet) : Term LSet := t.rename Nat.succ

/-- Evaluating a lifted term after pushing a value. -/
@[simp] theorem evalT_up (x : BSet B) (e : Nat → BSet B) (t : Term LSet) :
    (VB B).evalT (BEnv.cons (α := BSet B) x e) (up t) = (VB B).evalT e t := by
  unfold up; rw [evalT_rename]; rfl

/-- Evaluating a variable. -/
@[simp] theorem evalT_var' (e : Nat → BSet B) (n : Nat) : (VB B).evalT e (Term.var n) = e n := rfl

/-- Pushing a value: index `0`. -/
@[simp] theorem cons_zero' (x : (VB B).Dom) (e : Nat → (VB B).Dom) : BEnv.cons x e 0 = x := rfl

/-- Pushing a value: index `n + 1`. -/
@[simp] theorem cons_succ' (x : BSet B) (e : Nat → BSet B) (n : Nat) :
    BEnv.cons (α := BSet B) x e (n + 1) = e n := rfl

/-- Pushing a value: index `0` (domain-typed form). -/
@[simp] theorem cons_zeroD (x : (VB B).Dom) (e : Nat → (VB B).Dom) :
    BEnv.cons (α := (VB B).Dom) x e 0 = x := rfl

/-- Pushing a value: index `n + 1` (domain-typed form). -/
@[simp] theorem cons_succD (x : (VB B).Dom) (e : Nat → (VB B).Dom) (n : Nat) :
    BEnv.cons (α := (VB B).Dom) x e (n + 1) = e n := rfl

/-- Evaluating a variable (domain-typed form). -/
@[simp] theorem evalT_varD (e : Nat → (VB B).Dom) (n : Nat) : (VB B).evalT e (Term.var n) = e n := rfl

/-- The formula `t ⊆ s`. -/
def subsetF (t s : Term LSet) : Formula LSet := .all (.imp (memF (v 0) (up t)) (memF (v 0) (up s)))

/-- The formula `w = {a}`. -/
def singF (w a : Term LSet) : Formula LSet := .all (iffF (memF (v 0) (up w)) (.eq (v 0) (up a)))

/-- The formula `w = {a, b}`. -/
def doubF (w a b : Term LSet) : Formula LSet :=
  .all (iffF (memF (v 0) (up w)) (.disj (.eq (v 0) (up a)) (.eq (v 0) (up b))))

/-- The formula `z = (a, b)` (Kuratowski: `z = {{a}, {a, b}}`). -/
def opairF (z a b : Term LSet) : Formula LSet :=
  .all (iffF (memF (v 0) (up z)) (.disj (singF (v 0) (up a)) (doubF (v 0) (up a) (up b))))

/-- The formula `(a, b) ∈ f`, i.e. `∃z (z ∈ f ∧ z = (a, b))`. -/
def pmF (a b f : Term LSet) : Formula LSet :=
  .ex (.conj (memF (v 0) (up f)) (opairF (v 0) (up a) (up b)))

/-- The formula "`f` is a function from `X` to `Y`". -/
def isFuncF (f X Y : Term LSet) : Formula LSet :=
  .conj (.all (.imp (memF (v 0) (up X)) (.ex (.conj (memF (v 0) (up (up Y))) (pmF (v 1) (v 0) (up (up f)))))))
    (.all (.imp (memF (v 0) (up X)) (.all (.all (.imp
      (.conj (pmF (v 2) (v 1) (up (up (up f)))) (pmF (v 2) (v 0) (up (up (up f))))) (.eq (v 1) (v 0)))))))

/-- The formula "`f` is injective on `X`". -/
def injF (f X : Term LSet) : Formula LSet :=
  .all (.all (.all (.imp (.conj (.conj (.conj (memF (v 2) (up (up (up X)))) (memF (v 1) (up (up (up X)))))
    (pmF (v 2) (v 0) (up (up (up f))))) (pmF (v 1) (v 0) (up (up (up f))))) (.eq (v 2) (v 1)))))

/-- The formula "`e` is empty". -/
def emptyF (e : Term LSet) : Formula LSet := .all (Formula.neg (memF (v 0) (up e)))

/-- The formula `s = y ∪ {y}`. -/
def succF (s y : Term LSet) : Formula LSet :=
  .all (iffF (memF (v 0) (up s)) (.disj (memF (v 0) (up y)) (.eq (v 0) (up y))))

/-- The formula "`w` is inductive". -/
def inductiveF (w : Term LSet) : Formula LSet :=
  .conj (.ex (.conj (memF (v 0) (up w)) (emptyF (v 0))))
    (.all (.imp (memF (v 0) (up w)) (.ex (.conj (memF (v 0) (up (up w))) (succF (v 0) (v 1))))))

/-- The formula "`w = ω`": `w` is inductive and contained in every inductive set. -/
def omegaF (w : Term LSet) : Formula LSet :=
  .conj (inductiveF w) (.all (.imp (inductiveF (v 0)) (subsetF (up w) (v 0))))

/-- The formula "`p = 𝒫(w)`". -/
def powF (p w : Term LSet) : Formula LSet := .all (iffF (memF (v 0) (up p)) (subsetF (v 0) (up w)))

/-- **The Continuum Hypothesis** as a sentence of `LSet`: for `w = ω` and `p = 𝒫(w)`, every
`x ⊆ p` injects into `w` or receives an injection from `p`. -/
def CH : Formula LSet :=
  .all (.all (.imp (.conj (omegaF (v 1)) (powF (v 0) (v 1)))
    (.all (.imp (subsetF (v 0) (v 1))
      (.disj (.ex (.conj (isFuncF (v 0) (v 1) (v 3)) (injF (v 0) (v 1))))
        (.ex (.conj (isFuncF (v 0) (v 2) (v 1)) (injF (v 0) (v 2)))))))))

/-! ### Truth values of the combinators -/

section Values

variable (e : Nat → BSet B)

/-- Truth value of `t ⊆ s`. -/
theorem val_subsetF (t s : Term LSet) :
    (VB B).val e (subsetF t s) = BSet.subset ((VB B).evalT e t) ((VB B).evalT e s) := by
  simp only [subsetF, val, val_memF, evalT_up, evalT_var', cons_zero', cons_zeroD, cons_succD, evalT_varD]; rfl

/-- Truth value of `w = {a}`. -/
theorem val_singF (w a : Term LSet) : (VB B).val e (singF w a) =
    BSet.eq ((VB B).evalT e w) (BSet.pair ((VB B).evalT e a) ((VB B).evalT e a)) := by
  simp only [singF, val, val_iffF, val_memF, evalT_up, evalT_var', cons_zero', cons_zeroD, cons_succD, evalT_varD]
  rw [BSet.eq_eq_iInf_biimp]
  congr; funext u; rw [BSet.mem_pair, BSet.sup_idem']; rfl

/-- Truth value of `w = {a, b}`. -/
theorem val_doubF (w a b : Term LSet) : (VB B).val e (doubF w a b) =
    BSet.eq ((VB B).evalT e w) (BSet.pair ((VB B).evalT e a) ((VB B).evalT e b)) := by
  simp only [doubF, val, val_iffF, val_memF, evalT_up, evalT_var', cons_zero', cons_zeroD, cons_succD, evalT_varD]
  rw [BSet.eq_eq_iInf_biimp]
  congr; funext u; rw [BSet.mem_pair]; rfl

/-- **Truth value of `z = (a, b)`**: exactly Boolean equality with the pair name. -/
theorem val_opairF (z a b : Term LSet) : (VB B).val e (opairF z a b) =
    BSet.eq ((VB B).evalT e z) (BSet.opair ((VB B).evalT e a) ((VB B).evalT e b)) := by
  simp only [opairF, val, val_iffF, val_memF, val_singF, val_doubF, evalT_up, evalT_var',
    cons_zero', cons_zeroD, cons_succD, evalT_varD]
  rw [BSet.eq_eq_iInf_biimp]
  congr; funext u; unfold BSet.opair; rw [BSet.mem_pair]; rfl

/-- **Truth value of `(a, b) ∈ f`**: membership of the pair name. -/
theorem val_pmF (a b f : Term LSet) : (VB B).val e (pmF a b f) =
    BSet.pm ((VB B).evalT e a) ((VB B).evalT e b) ((VB B).evalT e f) := by
  simp only [pmF, val, val_memF, val_opairF, evalT_up, evalT_var', cons_zero', cons_zeroD, cons_succD, evalT_varD]
  apply le_antisymm'
  · exact iSup_le fun z => by
      rw [inf_comm]; exact BSet.mem_congr_left _ _ _
  · exact le_iSup_of_le (BSet.opair _ _) (le_inf _ _ _ le_rfl
      (le_trans' le_top' (eq_top_iff.1 (BSet.eq_self _))))

/-- Truth value of "`f` is a function from `X` to `Y`". -/
theorem val_isFuncF (f X Y : Term LSet) : (VB B).val e (isFuncF f X Y) =
    BSet.isFunc ((VB B).evalT e f) ((VB B).evalT e X) ((VB B).evalT e Y) := by
  simp only [isFuncF, val, val_memF, val_pmF, evalT_up, evalT_var', cons_zero', cons_succ', cons_zeroD, cons_succD, evalT_varD]; rfl

/-- Truth value of "`f` is injective on `X`". -/
theorem val_injF (f X : Term LSet) : (VB B).val e (injF f X) =
    BSet.isInj ((VB B).evalT e f) ((VB B).evalT e X) := by
  simp only [injF, val, val_memF, val_pmF, evalT_up, evalT_var', cons_zero', cons_succ', cons_zeroD, cons_succD, evalT_varD]; rfl

/-- Truth value of "`w = ω`". -/
theorem val_omegaF (w : Term LSet) : (VB B).val e (omegaF w) = BSet.isOmega ((VB B).evalT e w) := by
  simp only [omegaF, inductiveF, emptyF, succF, Formula.neg, val, val_memF, val_iffF,
    val_subsetF, evalT_up, evalT_var', cons_zero', cons_succ', cons_zeroD, cons_succD, evalT_varD]; rfl

/-- Truth value of "`p = 𝒫(w)`". -/
theorem val_powF (p w : Term LSet) : (VB B).val e (powF p w) =
    BSet.isPow ((VB B).evalT e p) ((VB B).evalT e w) := by
  simp only [powF, val, val_memF, val_iffF, val_subsetF, evalT_up, evalT_var', cons_zero', cons_zeroD, cons_succD, evalT_varD]; rfl

/-- **Truth value of CH.** -/
theorem val_CH : (VB B).val e CH =
    iInf fun w => iInf fun p => (BSet.isOmega w ⊓ BSet.isPow p w) ⇨
      iInf fun x => BSet.subset x p ⇨
        ((iSup fun f => BSet.isFunc f x w ⊓ BSet.isInj f x) ⊔
          (iSup fun f => BSet.isFunc f p x ⊓ BSet.isInj f p)) := by
  simp only [CH, val, val_omegaF, val_powF, val_subsetF, val_isFuncF, val_injF, evalT_var',
    cons_zero', cons_succ', cons_zeroD, cons_succD, evalT_varD]
  rfl

end Values

end Foundations.Forcing
