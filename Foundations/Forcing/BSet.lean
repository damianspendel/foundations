import Foundations.Forcing.BooleanAlgebra

/-!
# The Boolean-valued universe `V^B`

Aczel's pre-sets (`Sets/PSet`) model the cumulative hierarchy: a set is an indexed family
of earlier sets. Scott and Solovay's Boolean-valued universe `V^B` is the same idea with
*fuzzy* membership. A **`B`-valued pre-set** (`BSet B`, following the `bSet` of Han and van
Doorn's *flypitch* project) is an index type `α`, a family `A : α → BSet B` of earlier
names, and for each index a truth value `b i ∈ B`, the degree to which `A i` belongs.
In the forcing literature such objects are called **names**: a name does not yet denote a
definite set; it denotes "the set containing `A i` with probability `b i`".

Membership and equality are then defined by simultaneous recursion, as in `PSet.Equiv`:

* `⟦x = y⟧ = ⨅ᵢ (aᵢ ⇨ ⨆ⱼ (bⱼ ⊓ ⟦Aᵢ = Bⱼ⟧)) ⊓ ⨅ⱼ (bⱼ ⇨ ⨆ᵢ (aᵢ ⊓ ⟦Aᵢ = Bⱼ⟧))`
  ("every member of `x` is in `y`, and vice versa", to the appropriate degree);
* `⟦x ∈ y⟧ = ⨆ⱼ (bⱼ ⊓ ⟦x = Bⱼ⟧)`.

If `B` is the two-element algebra this is Aczel's construction. The main results of this file are
that Boolean equality is reflexive (`eq_self`), symmetric (`eq_symm`) and transitive
(`eq_trans`), and that membership respects it on both sides (`mem_congr_left`,
`mem_congr_right`). Transitivity is the delicate one: it is proved by induction on the
first name with the other two arbitrary, and uses infinite distributivity in both
directions. These are exactly the hypotheses needed to turn `V^B` into a Boolean-valued
structure for the language of set theory, which is done in `BSetModel`.

We require `B : Type`, so that `BSet B` lives in `Type 1`, like `PSet`.
-/

namespace Foundations.Forcing

open CBA

/-- **`B`-valued pre-sets (names).** A name is an index type `α`, a family of earlier names
`A : α → BSet B`, and for each index the Boolean degree `b i` to which `A i` is a member. -/
inductive BSet (B : Type) [CompleteBooleanAlgebra B] : Type 1
  | mk (α : Type) (A : α → BSet B) (b : α → B) : BSet B

namespace BSet

variable {B : Type} [CompleteBooleanAlgebra B]

/-- The index type of a name. -/
def type : BSet B → Type
  | mk α _ _ => α

/-- The member listed under an index. -/
def func : (x : BSet B) → x.type → BSet B
  | mk _ A _ => A

/-- The Boolean degree of membership of the member listed under an index. -/
def bval : (x : BSet B) → x.type → B
  | mk _ _ b => b

/-- **Boolean equality of names**, by recursion: every member of `x` is (to its degree) equal
to some member of `y`, and vice versa. -/
def eq : BSet B → BSet B → B
  | mk _ A a, mk _ A' a' =>
      iInf (fun i => a i ⇨ iSup fun j => a' j ⊓ eq (A i) (A' j)) ⊓
      iInf (fun j => a' j ⇨ iSup fun i => a i ⊓ eq (A i) (A' j))

/-- **Boolean membership of names**: `⟦x ∈ y⟧ = ⨆ⱼ (bⱼ ⊓ ⟦x = Bⱼ⟧)`. -/
def mem (x y : BSet B) : B := iSup fun j => y.bval j ⊓ eq x (y.func j)

/-- Unfolding Boolean equality for arbitrary names. -/
theorem eq_def (x y : BSet B) : eq x y =
    iInf (fun i => x.bval i ⇨ iSup fun j => y.bval j ⊓ eq (x.func i) (y.func j)) ⊓
    iInf (fun j => y.bval j ⇨ iSup fun i => x.bval i ⊓ eq (x.func i) (y.func j)) := by
  cases x; cases y; rfl

/-- A listed member of `x` is, to the degree `⟦x = y⟧`, equal to some member of `y`. -/
theorem eq_inf_bval_left (x y : BSet B) (i : x.type) :
    eq x y ⊓ x.bval i ≤ iSup fun j => y.bval j ⊓ eq (x.func i) (y.func j) := by
  rw [eq_def]
  exact le_trans' (inf_le_inf (inf_le_of_left_le (iInf_le _ i)) le_rfl) himp_inf_le

/-- A listed member of `y` is, to the degree `⟦x = y⟧`, equal to some member of `x`. -/
theorem eq_inf_bval_right (x y : BSet B) (j : y.type) :
    eq x y ⊓ y.bval j ≤ iSup fun i => x.bval i ⊓ eq (x.func i) (y.func j) := by
  rw [eq_def]
  exact le_trans' (inf_le_inf (inf_le_of_right_le (iInf_le _ j)) le_rfl) himp_inf_le

/-- Introduction rule for Boolean equality: to bound `⟦x = y⟧` from below by `c`, check both
halves of the definition under the hypothesis `c`. -/
theorem le_eq_of {x y : BSet B} {c : B}
    (h₁ : ∀ i, c ⊓ x.bval i ≤ iSup fun j => y.bval j ⊓ eq (x.func i) (y.func j))
    (h₂ : ∀ j, c ⊓ y.bval j ≤ iSup fun i => x.bval i ⊓ eq (x.func i) (y.func j)) :
    c ≤ eq x y := by
  rw [eq_def]
  exact le_inf _ _ _ (le_iInf fun i => le_himp_iff.2 (h₁ i))
    (le_iInf fun j => le_himp_iff.2 (h₂ j))

/-- **Reflexivity of Boolean equality.** `⟦x = x⟧ = ⊤`. -/
theorem eq_self (x : BSet B) : eq x x = ⊤ := by
  induction x with
  | mk α A a ih =>
    apply eq_top_iff.2
    apply le_eq_of
    · intro i
      exact le_iSup_of_le i (by show _ ≤ a i ⊓ eq (A i) (A i); rw [ih i]; lattice_le)
    · intro j
      exact le_iSup_of_le j (by show _ ≤ a j ⊓ eq (A j) (A j); rw [ih j]; lattice_le)

/-- **Symmetry of Boolean equality.** `⟦x = y⟧ ≤ ⟦y = x⟧`. -/
theorem eq_symm (x y : BSet B) : eq x y ≤ eq y x := by
  induction x generalizing y with
  | mk α A a ih =>
    apply le_eq_of
    · intro j
      exact le_trans' (eq_inf_bval_right _ y j)
        (iSup_mono fun i => inf_le_inf le_rfl (ih i _))
    · intro i
      exact le_trans' (eq_inf_bval_left _ y i)
        (iSup_mono fun j => inf_le_inf le_rfl (ih i _))

/-- Boolean equality is symmetric, as an equation. -/
theorem eq_comm (x y : BSet B) : eq x y = eq y x :=
  le_antisymm' (eq_symm x y) (eq_symm y x)

/-- **Transitivity of Boolean equality.** `⟦x = y⟧ ⊓ ⟦y = z⟧ ≤ ⟦x = z⟧`. -/
theorem eq_trans (x y z : BSet B) : eq x y ⊓ eq y z ≤ eq x z := by
  induction x generalizing y z with
  | mk α A a ih =>
    apply le_eq_of
    · intro i
      -- push `a i` into `⟦x = y⟧`, then push the resulting `y`-member into `⟦y = z⟧`
      calc eq (mk α A a) y ⊓ eq y z ⊓ a i
          ≤ (eq (mk α A a) y ⊓ a i) ⊓ eq y z := by lattice_le
        _ ≤ (iSup fun j => y.bval j ⊓ eq (A i) (y.func j)) ⊓ eq y z :=
            inf_le_inf (eq_inf_bval_left (mk α A a) y i) le_rfl
        _ ≤ iSup (fun j => y.bval j ⊓ eq (A i) (y.func j) ⊓ eq y z) := iSup_inf_le
        _ ≤ iSup fun k => z.bval k ⊓ eq (A i) (z.func k) := iSup_le fun j => by
            calc y.bval j ⊓ eq (A i) (y.func j) ⊓ eq y z
                ≤ eq (A i) (y.func j) ⊓ (eq y z ⊓ y.bval j) := by lattice_le
              _ ≤ eq (A i) (y.func j) ⊓ iSup (fun k => z.bval k ⊓ eq (y.func j) (z.func k)) :=
                  inf_le_inf le_rfl (eq_inf_bval_left y z j)
              _ ≤ iSup (fun k => eq (A i) (y.func j) ⊓ (z.bval k ⊓ eq (y.func j) (z.func k))) :=
                  inf_iSup_le
              _ ≤ _ := iSup_mono fun k => le_inf _ _ _ (by lattice_le)
                  (le_trans' (by lattice_le) (ih i (y.func j) (z.func k)))
    · intro k
      calc eq (mk α A a) y ⊓ eq y z ⊓ z.bval k
          ≤ eq (mk α A a) y ⊓ (eq y z ⊓ z.bval k) := by lattice_le
        _ ≤ eq (mk α A a) y ⊓ iSup (fun j => y.bval j ⊓ eq (y.func j) (z.func k)) :=
            inf_le_inf le_rfl (eq_inf_bval_right y z k)
        _ ≤ iSup (fun j => eq (mk α A a) y ⊓ (y.bval j ⊓ eq (y.func j) (z.func k))) :=
            inf_iSup_le
        _ ≤ iSup fun i => a i ⊓ eq (A i) (z.func k) := iSup_le fun j => by
            calc eq (mk α A a) y ⊓ (y.bval j ⊓ eq (y.func j) (z.func k))
                ≤ (eq (mk α A a) y ⊓ y.bval j) ⊓ eq (y.func j) (z.func k) := by lattice_le
              _ ≤ iSup (fun i => a i ⊓ eq (A i) (y.func j)) ⊓ eq (y.func j) (z.func k) :=
                  inf_le_inf (eq_inf_bval_right (mk α A a) y j) le_rfl
              _ ≤ iSup (fun i => a i ⊓ eq (A i) (y.func j) ⊓ eq (y.func j) (z.func k)) :=
                  iSup_inf_le
              _ ≤ _ := iSup_mono fun i => le_inf _ _ _ (by lattice_le)
                  (le_trans' (by lattice_le) (ih i (y.func j) (z.func k)))

/-! ### Membership -/

/-- Unfolding membership. -/
theorem mem_def (x y : BSet B) : mem x y = iSup fun j => y.bval j ⊓ eq x (y.func j) := rfl

/-- A listed member belongs to its name at least to its listed degree. -/
theorem bval_le_mem (y : BSet B) (j : y.type) : y.bval j ≤ mem (y.func j) y :=
  le_iSup_of_le j (by rw [eq_self]; lattice_le)

/-- **Membership respects equality on the left.** `⟦x = x'⟧ ⊓ ⟦x ∈ y⟧ ≤ ⟦x' ∈ y⟧`. -/
theorem mem_congr_left (x x' y : BSet B) : eq x x' ⊓ mem x y ≤ mem x' y :=
  le_trans' inf_iSup_le (iSup_mono fun j => le_inf _ _ _ (by lattice_le)
    (le_trans' (le_inf _ _ _ (inf_le_of_left_le (eq_symm x x')) (by lattice_le))
      (eq_trans _ _ _)))

/-- **Membership respects equality on the right.** `⟦y = y'⟧ ⊓ ⟦x ∈ y⟧ ≤ ⟦x ∈ y'⟧`. -/
theorem mem_congr_right (x y y' : BSet B) : eq y y' ⊓ mem x y ≤ mem x y' := by
  refine le_trans' inf_iSup_le (iSup_le fun j => ?_)
  calc eq y y' ⊓ (y.bval j ⊓ eq x (y.func j))
      ≤ (eq y y' ⊓ y.bval j) ⊓ eq x (y.func j) := by lattice_le
    _ ≤ iSup (fun k => y'.bval k ⊓ eq (y.func j) (y'.func k)) ⊓ eq x (y.func j) :=
        inf_le_inf (eq_inf_bval_left y y' j) le_rfl
    _ ≤ iSup (fun k => y'.bval k ⊓ eq (y.func j) (y'.func k) ⊓ eq x (y.func j)) := iSup_inf_le
    _ ≤ mem x y' := iSup_mono fun k => le_inf _ _ _ (by lattice_le)
        (le_trans' (by lattice_le) (eq_trans x (y.func j) (y'.func k)))

/-- `⟦x ∈ y⟧ ⊓ ⟦x = x'⟧ ⊓ ⟦y = y'⟧ ≤ ⟦x' ∈ y'⟧`: membership respects equality on both sides. -/
theorem mem_congr (x x' y y' : BSet B) : eq x x' ⊓ eq y y' ⊓ mem x y ≤ mem x' y' :=
  le_trans' (le_inf _ _ _ (by lattice_le)
      (le_trans' (le_inf _ _ _ (by lattice_le) (by lattice_le)) (mem_congr_left x x' y)))
    (mem_congr_right x' y y')

/-- **Boolean extensionality.** If `x` and `y` have the same members to degree `c`, they are
equal to degree `c`: `⨅_z (⟦z ∈ x⟧ ⇔ ⟦z ∈ y⟧) ≤ ⟦x = y⟧`. -/
theorem iInf_biimp_le_eq (x y : BSet B) :
    iInf (fun z => mem z x ⇔ mem z y) ≤ eq x y := by
  apply le_eq_of
  · intro i
    calc iInf (fun z => mem z x ⇔ mem z y) ⊓ x.bval i
        ≤ (mem (x.func i) x ⇨ mem (x.func i) y) ⊓ mem (x.func i) x :=
          inf_le_inf (le_trans' (iInf_le _ (x.func i)) (inf_le_left _ _)) (bval_le_mem x i)
      _ ≤ mem (x.func i) y := himp_inf_le
  · intro j
    calc iInf (fun z => mem z x ⇔ mem z y) ⊓ y.bval j
        ≤ (mem (y.func j) y ⇨ mem (y.func j) x) ⊓ mem (y.func j) y :=
          inf_le_inf (le_trans' (iInf_le _ (y.func j)) (inf_le_right _ _)) (bval_le_mem y j)
      _ ≤ mem (y.func j) x := himp_inf_le
      _ ≤ _ := iSup_mono fun i => by rw [eq_comm]; exact le_rfl

end BSet

end Foundations.Forcing
