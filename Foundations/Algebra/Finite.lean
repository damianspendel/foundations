import Foundations.Algebra.Group

/-!
# Finite types and counting

Lagrange's theorem, Fermat's little theorem, Sylow's theorems: the classical results of
finite group theory are all theorems about *counting*. Before we can state them we need
a precise notion of a finite collection and of the number of things in it satisfying a
property.

We take the most concrete route available. A type is **finite** when we are handed a
list of its elements that mentions every element exactly once — an explicit census. The
*cardinality* is the length of the census, and the number of elements satisfying a
property `P` is the number of entries of the census satisfying `P`. Every counting
principle we need is then a fact about lists: counts add over a partition, counts are
invariant under bijections (the one principle Frege and Cantor took as the very
definition of "equinumerous"), and a list without repetitions cannot be longer than the
census (the pigeonhole principle).

Properties of elements need not be decidable (membership in an abstract subgroup, for
instance), so the counting function consults classical logic to decide each entry. The
price is that `count` is noncomputable; the gain is that we may count anything.
-/

namespace Foundations.Algebra

universe u v

/-- **Finite type.** A type together with a census: a list of its elements, without
repetitions, that contains every element. -/
class FiniteType (α : Type u) where
  /-- The census of all elements. -/
  elems : List α
  /-- No element is listed twice. -/
  nodup : elems.Nodup
  /-- Every element is listed. -/
  complete : ∀ x : α, x ∈ elems

namespace FiniteType

variable {α : Type u} {β : Type v} [FiniteType α]

/-- The **cardinality** of a finite type: the length of its census. -/
def card (α : Type u) [FiniteType α] : Nat := (elems : List α).length

/-- The **number of elements satisfying `P`**. Membership is decided classically, so `P`
can be any property whatsoever. -/
noncomputable def count (P : α → Prop) : Nat :=
  (elems : List α).countP (fun x => @decide (P x) (Classical.propDecidable _))

/-- For a decidable property, `count` can be computed with any decision procedure. -/
theorem count_eq_countP (P : α → Prop) [DecidablePred P] :
    count P = (elems : List α).countP (fun x => decide (P x)) := by
  unfold count
  apply List.countP_congr
  intro x _
  simp only [decide_eq_true_eq]

/-- Counting depends only on which elements satisfy the property. -/
theorem count_congr {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : count P = count Q := by
  have : P = Q := funext fun x => propext (h x)
  rw [this]

/-- A list fact: counting `p` splits into counting `p ∧ q` and `p ∧ ¬q`. -/
theorem countP_split {γ : Type u} (p q : γ → Bool) (l : List γ) :
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

/-- **Additivity of counting.** The elements satisfying `P` split into those that also
satisfy `Q` and those that do not. -/
theorem count_split (P Q : α → Prop) :
    count P = count (fun x => P x ∧ Q x) + count (fun x => P x ∧ ¬ Q x) := by
  classical
  rw [count_eq_countP, count_eq_countP, count_eq_countP,
    countP_split (fun x => decide (P x)) (fun x => decide (Q x))]
  congr 1 <;> apply List.countP_congr <;> intro x _ <;> simp

/-- Counting the always-true property gives the cardinality. -/
theorem count_true : count (fun _ : α => True) = card α := by
  classical
  rw [count_eq_countP]
  simp [card]

/-- No property is satisfied by more elements than there are. -/
theorem count_le_card (P : α → Prop) : count P ≤ card α := by
  unfold count card; exact List.countP_le_length

/-- A count is zero exactly when nothing satisfies the property. -/
theorem count_eq_zero {P : α → Prop} : count P = 0 ↔ ∀ x, ¬ P x := by
  unfold count
  rw [List.countP_eq_zero]
  constructor
  · intro h x hx; exact h x (complete x) (by simpa using hx)
  · intro h x _ hx; exact h x (by simpa using hx)

/-- A count is positive exactly when something satisfies the property. -/
theorem count_pos {P : α → Prop} : 0 < count P ↔ ∃ x, P x := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    have : count P = 0 := count_eq_zero.2 fun x hx => hne ⟨x, hx⟩
    omega
  · intro ⟨x, hx⟩
    apply Nat.pos_of_ne_zero
    intro h
    exact count_eq_zero.1 h x hx

/-- The count of `P` plus the count of `¬P` is the cardinality. -/
theorem count_add_count_not (P : α → Prop) : count P + count (fun x => ¬ P x) = card α := by
  rw [← count_true, count_split (fun _ => True) P]
  congr 1 <;> apply count_congr <;> intro x <;> simp

/-- A property holds of everything exactly when its count is the cardinality. -/
theorem count_eq_card {P : α → Prop} : count P = card α ↔ ∀ x, P x := by
  have h := count_add_count_not P
  constructor
  · intro hc x
    apply Classical.byContradiction
    intro hx
    have : count (fun x => ¬ P x) = 0 := by omega
    exact count_eq_zero.1 this x hx
  · intro hall
    have : count (fun x => ¬ P x) = 0 := count_eq_zero.2 fun x hx => hx (hall x)
    omega

/-- **Monotonicity.** If `P` implies `Q`, fewer things satisfy `P` than `Q`. -/
theorem count_mono {P Q : α → Prop} (h : ∀ x, P x → Q x) : count P ≤ count Q := by
  rw [count_split Q P]
  have : count (fun x => Q x ∧ P x) = count P :=
    count_congr fun x => ⟨fun hx => hx.2, fun hx => ⟨h x hx, hx⟩⟩
  omega

/-- **Counting by listing.** If the elements satisfying `P` are exactly the entries of a
repetition-free list `L`, then `P` is satisfied by `L.length` elements. -/
theorem count_eq_length {P : α → Prop} {L : List α} (hL : L.Nodup) (h : ∀ x, P x ↔ x ∈ L) :
    count P = L.length := by
  classical
  rw [count_eq_countP, List.countP_eq_length_filter]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (List.Pairwise.filter _ nodup) hL]
  intro x
  simp [List.mem_filter, complete, h]

/-- Exactly one element is equal to a given `a`. -/
theorem count_eq_self (a : α) : count (fun x => x = a) = 1 :=
  count_eq_length (L := [a]) (List.nodup_cons.2 ⟨by simp, List.Pairwise.nil⟩)
    (fun x => by simp)

/-- **The pigeonhole principle.** A list of elements of `α` without repetitions has at most
`card α` entries. -/
theorem length_le_card {L : List α} (hL : L.Nodup) : L.length ≤ card α :=
  List.Nodup.length_le_of_subset hL (fun x _ => complete x)

/-- Mapping a list by an injective function preserves the absence of repetitions. -/
theorem nodup_map_of_injective {γ δ : Type _} {f : γ → δ} (hf : ∀ a b, f a = f b → a = b)
    {L : List γ} (hL : L.Nodup) : (L.map f).Nodup :=
  List.Pairwise.map f (fun a b hab h => hab (hf a b h)) hL

/-- **Bijections preserve counts** — the Cantor–Frege principle that equinumerosity is the
existence of a one-to-one correspondence. If `f : α → β` is a bijection, then exactly as
many elements of `α` satisfy `Q ∘ f` as elements of `β` satisfy `Q`. -/
theorem count_comp_bij [FiniteType β] (f : α → β) (inj : ∀ a b, f a = f b → a = b)
    (surj : ∀ y, ∃ x, f x = y) (Q : β → Prop) :
    count (fun x => Q (f x)) = count Q := by
  classical
  rw [count_eq_countP, count_eq_countP]
  have hperm : ((elems : List α).map f).Perm (elems : List β) := by
    rw [List.perm_ext_iff_of_nodup (nodup_map_of_injective inj nodup) nodup]
    intro y
    simp only [List.mem_map, complete, true_and, iff_true]
    exact surj y
  rw [← hperm.countP_eq, List.countP_map]
  rfl

/-- **In a finite world, injections are surjections.** An injective map from a finite type
to itself hits every element (this fails for infinite sets — Galileo's and Dedekind's
observation that ℕ is equinumerous with a proper part of itself). -/
theorem surjective_of_injective (f : α → α) (inj : ∀ a b, f a = f b → a = b) :
    ∀ y, ∃ x, f x = y := by
  have hL := nodup_map_of_injective inj (nodup (α := α))
  have hc : count (fun y => y ∈ (elems : List α).map f) = card α := by
    rw [count_eq_length hL (fun _ => Iff.rfl), List.length_map]; rfl
  intro y
  have := count_eq_card.1 hc y
  rw [List.mem_map] at this
  obtain ⟨x, _, hx⟩ := this
  exact ⟨x, hx⟩

/-- **Least-number principle.** If some natural number has property `P`, there is a least
one. -/
theorem exists_least (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hmin : ∀ m, m < n → ¬ P m
    · exact ⟨n, hn, hmin⟩
    · apply Classical.byContradiction
      intro hno
      apply hmin
      intro m hm hPm
      exact hno (ih m hm hPm)

/-! ## Instances -/

/-- `Fin n` is finite, with census `0, 1, …, n-1`. -/
instance instFin (n : Nat) : FiniteType (Fin n) where
  elems := List.finRange n
  nodup := List.nodup_finRange n
  complete := List.mem_finRange

/-- `Fin n` has `n` elements. -/
theorem card_fin (n : Nat) : card (Fin n) = n := List.length_finRange

/-- The one-element type is finite. -/
instance : FiniteType Unit where
  elems := [()]
  nodup := List.nodup_cons.2 ⟨by simp, List.Pairwise.nil⟩
  complete := fun _ => by simp

/-- The sub-list of a list consisting of the entries satisfying `P`, each packaged with the
evidence that it satisfies `P`. -/
def listSubtype {γ : Type u} (P : γ → Prop) [DecidablePred P] : List γ → List {x // P x}
  | [] => []
  | x :: l => if h : P x then ⟨x, h⟩ :: listSubtype P l else listSubtype P l

/-- Membership in `listSubtype`. -/
theorem mem_listSubtype {γ : Type u} (P : γ → Prop) [DecidablePred P] (l : List γ) (x : {x // P x}) :
    x ∈ listSubtype P l ↔ x.1 ∈ l := by
  induction l with
  | nil => simp [listSubtype]
  | cons y l ih =>
    unfold listSubtype
    by_cases h : P y
    · simp only [h, ↓reduceDIte, List.mem_cons, ih]
      constructor
      · rintro (h1 | h1)
        · left; rw [h1]
        · right; exact h1
      · rintro (h1 | h1)
        · left; exact Subtype.ext h1
        · right; exact h1
    · simp only [h, ↓reduceDIte, List.mem_cons, ih]
      constructor
      · intro h1; right; exact h1
      · rintro (h1 | h1)
        · exact absurd (h1 ▸ x.2) h
        · exact h1

/-- `listSubtype` of a repetition-free list is repetition-free. -/
theorem nodup_listSubtype {γ : Type u} (P : γ → Prop) [DecidablePred P] (l : List γ) (hl : l.Nodup) :
    (listSubtype P l).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons y l ih =>
    rw [List.nodup_cons] at hl
    unfold listSubtype
    by_cases h : P y
    · simp only [h, ↓reduceDIte]
      refine List.nodup_cons.2 ⟨?_, ih hl.2⟩
      rw [mem_listSubtype]; exact hl.1
    · simp only [h, ↓reduceDIte]; exact ih hl.2

/-- `listSubtype` has as many entries as the list has entries satisfying `P`. -/
theorem length_listSubtype {γ : Type u} (P : γ → Prop) [DecidablePred P] (l : List γ) :
    (listSubtype P l).length = l.countP (fun x => decide (P x)) := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    unfold listSubtype
    by_cases h : P y
    · simp [h, ih]
    · simp [h, ih]

/-- **Subtypes of finite types are finite.** The elements of a finite type satisfying any
property `P` form a finite type. -/
noncomputable instance instSubtype (P : α → Prop) : FiniteType {x // P x} :=
  @FiniteType.mk _ (@listSubtype _ P (fun _ => Classical.propDecidable _) elems)
    (@nodup_listSubtype _ P (fun _ => Classical.propDecidable _) elems nodup)
    (fun x => (@mem_listSubtype _ P (fun _ => Classical.propDecidable _) elems x).2
      (complete x.1))

/-- The number of elements of the subtype `{x // P x}` is the count of `P`. -/
theorem card_subtype (P : α → Prop) : card {x // P x} = count P :=
  @length_listSubtype _ P (fun _ => Classical.propDecidable _) elems

/-! ## Numbering the elements -/

/-- The position of an element in the census, as an element of `Fin (card α)`. Together with
`ofFin`, this is a bijection between `α` and `{0, …, card α - 1}`: counting a finite set
*is* numbering its elements. -/
noncomputable def toFin (x : α) : Fin (card α) := by
  classical exact ⟨(elems : List α).idxOf x, List.idxOf_lt_length_of_mem (complete x)⟩

/-- The element in position `i` of the census. -/
def ofFin (i : Fin (card α)) : α := (elems : List α)[i.1]'i.2

/-- Numbering then looking up gives back the element. -/
theorem ofFin_toFin (x : α) : ofFin (toFin x) = x := by
  classical
  unfold ofFin toFin
  exact List.getElem_idxOf _

/-- Looking up then numbering gives back the position. -/
theorem toFin_ofFin (i : Fin (card α)) : toFin (ofFin i) = i := by
  classical
  unfold ofFin toFin
  apply Fin.ext
  exact List.Nodup.idxOf_getElem nodup i.1 i.2

end FiniteType

end Foundations.Algebra
