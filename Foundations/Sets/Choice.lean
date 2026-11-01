import Foundations.Sets.Paradoxes

/-!
# Zorn's lemma and the well-ordering theorem

The axiom of choice says that from any family of non-empty collections one may
choose one member of each, all at once. It is innocent-looking yet powerful,
and historically contested. Two of its most useful equivalents are:

* **Zorn's lemma**: in a partial order in which every chain (totally ordered
  part) has an upper bound, there is a maximal element.
* **Zermelo's well-ordering theorem** (1904): every collection can be
  well-ordered — arranged in a line in which every non-empty part has a first
  element.

Lean's logic includes choice (`Classical.choice`), so here we *derive* these
principles from it. The proof of Zorn avoids ordinals altogether. We work with
chains themselves: `succChain` enlarges a chain to a strictly bigger chain, when
one exists (a choice). The *tower* (`ChainClosure`) is the smallest family of
chains closed under `succChain` and under unions. A beautiful argument (going
back to Zermelo's second proof, and to Bourbaki, Witt and Kneser) shows that the
tower is itself linearly ordered by inclusion. Its union is then a chain that
`succChain` cannot enlarge — a *maximal* chain — and any upper bound of a
maximal chain is a maximal element.

Zermelo's theorem then follows from Zorn: consider well-orderings of parts of
the given type, ordered by "is an initial segment of". Chains have unions as
upper bounds; a maximal partial well-ordering must cover everything, since
otherwise a missing element could be appended at the end.
-/

namespace Foundations.Sets

namespace Zorn

universe u

variable {α : Type u}

/-- Inclusion of predicates ("subsets") on `α`. -/
def Sub (s t : α → Prop) : Prop := ∀ x, s x → t x

/-- Inclusion is transitive. -/
theorem Sub.trans {s t w : α → Prop} (h₁ : Sub s t) (h₂ : Sub t w) : Sub s w :=
  fun x h => h₂ x (h₁ x h)

/-- Mutual inclusion gives equality of predicates. -/
theorem Sub.antisymm {s t : α → Prop} (h₁ : Sub s t) (h₂ : Sub t s) : s = t :=
  funext fun x => propext ⟨h₁ x, h₂ x⟩

variable (r : α → α → Prop)

/-- A **chain** is a part of `α` any two of whose members are comparable under `r`. -/
def IsChain (c : α → Prop) : Prop := ∀ x y, c x → c y → r x y ∨ r y x

/-- `d` is a **strictly bigger chain** than `c`. -/
def SuperChain (c d : α → Prop) : Prop := IsChain r d ∧ Sub c d ∧ ¬ Sub d c

/-- Enlarge a chain to a strictly bigger chain if possible (chosen); otherwise leave it. -/
noncomputable def succChain (c : α → Prop) : α → Prop :=
  open Classical in
  if h : ∃ d, IsChain r c ∧ SuperChain r c d then Classical.choose h else c

/-- The union of a family of parts of `α`. -/
def sUnionP (S : (α → Prop) → Prop) : α → Prop := fun x => ∃ c, S c ∧ c x

/-- The **tower**: the smallest family of parts closed under `succChain` and unions. -/
inductive ChainClosure : (α → Prop) → Prop
  | succ {c : α → Prop} : ChainClosure c → ChainClosure (succChain r c)
  | union {S : (α → Prop) → Prop} : (∀ c, S c → ChainClosure c) → ChainClosure (sUnionP S)

variable {r}

/-- `succChain` only enlarges: `c ⊆ succChain c`. -/
theorem sub_succChain (c : α → Prop) : Sub c (succChain r c) := by
  unfold succChain
  by_cases h : ∃ d, IsChain r c ∧ SuperChain r c d
  · simp only [h, ↓reduceDIte]
    exact (Classical.choose_spec h).2.2.1
  · simp only [h, ↓reduceDIte]
    exact fun _ hx => hx

/-- `succChain` of a chain is a chain. -/
theorem succChain_isChain {c : α → Prop} (hc : IsChain r c) : IsChain r (succChain r c) := by
  unfold succChain
  by_cases h : ∃ d, IsChain r c ∧ SuperChain r c d
  · simp only [h, ↓reduceDIte]
    exact (Classical.choose_spec h).2.1
  · simp only [h, ↓reduceDIte]
    exact hc

/-- If a chain has a strictly bigger chain, `succChain` produces one. -/
theorem succChain_super {c : α → Prop} (hc : IsChain r c) (h : ∃ d, SuperChain r c d) :
    SuperChain r c (succChain r c) := by
  have h' : ∃ d, IsChain r c ∧ SuperChain r c d := let ⟨d, hd⟩ := h; ⟨d, hc, hd⟩
  unfold succChain
  simp only [h', ↓reduceDIte]
  exact (Classical.choose_spec h').2

/-- Auxiliary comparison lemma for the tower. -/
theorem closure_succ_total_aux {c₁ c₂ : α → Prop} (hc₁ : ChainClosure r c₁)
    (h : ∀ c₃, ChainClosure r c₃ → Sub c₃ c₂ → c₂ = c₃ ∨ Sub (succChain r c₃) c₂) :
    Sub (succChain r c₂) c₁ ∨ Sub c₁ c₂ := by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    rcases ih with ih | ih
    · exact Or.inl (ih.trans (sub_succChain c₃))
    · rcases h c₃ hc₃ ih with h' | h'
      · subst h'; exact Or.inl fun _ hx => hx
      · exact Or.inr h'
  | @union S _ ih =>
    by_cases hex : ∃ c, S c ∧ Sub (succChain r c₂) c
    · obtain ⟨c, hc, hsub⟩ := hex
      exact Or.inl fun x hx => ⟨c, hc, hsub x hx⟩
    · refine Or.inr fun x ⟨c, hc, hx⟩ => ?_
      rcases ih c hc with h' | h'
      · exact absurd ⟨c, hc, h'⟩ hex
      · exact h' x hx

/-- In the tower, if `c₁ ⊆ c₂` then either `c₂ = c₁` or `succChain c₁ ⊆ c₂`. -/
theorem closure_succ_total {c₁ c₂ : α → Prop} (hc₁ : ChainClosure r c₁)
    (hc₂ : ChainClosure r c₂) (h : Sub c₁ c₂) : c₂ = c₁ ∨ Sub (succChain r c₁) c₂ := by
  induction hc₂ generalizing c₁ with
  | @succ c₂ _ ih =>
    rcases closure_succ_total_aux hc₁ (fun c₃ hc₃ hsub => ih hc₃ hsub) with h' | h'
    · exact Or.inl (Sub.antisymm h' h)
    · rcases ih hc₁ h' with h'' | h''
      · subst h''; exact Or.inr fun _ hx => hx
      · exact Or.inr (h''.trans (sub_succChain c₂))
  | @union S hS ih =>
    by_cases hsucc : Sub (succChain r c₁) (sUnionP S)
    · exact Or.inr hsucc
    · refine Or.inl (Sub.antisymm (fun x ⟨c, hc, hx⟩ => ?_) h)
      rcases closure_succ_total_aux hc₁ (fun c₃ hc₃ hsub => ih c hc hc₃ hsub) with h' | h'
      · exact h' x (sub_succChain c x hx)
      · rcases ih c hc hc₁ h' with h'' | h''
        · subst h''; exact hx
        · exact absurd (fun y hy => ⟨c, hc, h'' y hy⟩) hsucc

/-- **The tower is linearly ordered by inclusion.** -/
theorem ChainClosure.total {c₁ c₂ : α → Prop} (hc₁ : ChainClosure r c₁)
    (hc₂ : ChainClosure r c₂) : Sub c₁ c₂ ∨ Sub c₂ c₁ := by
  rcases closure_succ_total_aux hc₂ (fun c₃ hc₃ hsub => closure_succ_total hc₃ hc₁ hsub) with h | h
  · exact Or.inl ((sub_succChain c₁).trans h)
  · exact Or.inr h

/-- Every member of the tower is a chain. -/
theorem ChainClosure.isChain {c : α → Prop} (hc : ChainClosure r c) : IsChain r c := by
  induction hc with
  | succ _ ih => exact succChain_isChain ih
  | @union S hS ih =>
    rintro x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩
    rcases (hS c hc).total (hS d hd) with h | h
    · exact ih d hd x y (h x hx) hy
    · exact ih c hc x y hx (h y hy)

variable (r) in
/-- The **maximal chain**: the union of the whole tower. -/
def maxChain : α → Prop := sUnionP (ChainClosure r)

/-- The maximal chain belongs to the tower. -/
theorem maxChain_mem : ChainClosure r (maxChain r) := ChainClosure.union fun _ h => h

/-- The maximal chain is a chain. -/
theorem maxChain_isChain : IsChain r (maxChain r) := maxChain_mem.isChain

/-- **The maximal chain is maximal**: no chain is strictly bigger. -/
theorem maxChain_maximal : ¬ ∃ d, SuperChain r (maxChain r) d := by
  intro h
  have hsup := succChain_super maxChain_isChain h
  have hsub : Sub (succChain r (maxChain r)) (maxChain r) :=
    fun x hx => ⟨_, ChainClosure.succ maxChain_mem, hx⟩
  exact hsup.2.2 hsub

/-- **Zorn's lemma.** Let `r` be a partial order on `α` (reflexive, transitive,
antisymmetric). If every chain has an upper bound, then there is a maximal
element: some `m` such that `r m x` implies `x = m`. -/
theorem zorn (refl : ∀ x, r x x) (trans : ∀ x y z, r x y → r y z → r x z)
    (antisymm : ∀ x y, r x y → r y x → x = y)
    (h : ∀ c, IsChain r c → ∃ u, ∀ x, c x → r x u) :
    ∃ m, ∀ x, r m x → x = m := by
  obtain ⟨u, hu⟩ := h (maxChain r) maxChain_isChain
  refine ⟨u, fun x hux => ?_⟩
  -- the maximal chain extended by `x` is still a chain
  let d : α → Prop := fun y => maxChain r y ∨ y = x
  have hd : IsChain r d := by
    rintro y z (hy | rfl) (hz | rfl)
    · exact maxChain_isChain y z hy hz
    · exact Or.inl (trans _ _ _ (hu y hy) hux)
    · exact Or.inr (trans _ _ _ (hu z hz) hux)
    · exact Or.inl (refl _)
  have hsub : Sub d (maxChain r) := Classical.byContradiction fun hn =>
    maxChain_maximal ⟨d, hd, fun _ hy => Or.inl hy, hn⟩
  exact antisymm _ _ (hu x (hsub x (Or.inr rfl))) hux

end Zorn

/-! ## Zermelo's well-ordering theorem -/

namespace WellOrdering

universe u

/-- A **partial well-ordering** of `α`: a strict order `lt` on a part `dom` of `α`
that is total there and in which every non-empty part of `dom` has a minimal
element. -/
structure PWO (α : Type u) where
  /-- The part of `α` that is ordered. -/
  dom : α → Prop
  /-- The strict order. -/
  lt : α → α → Prop
  /-- The order only relates elements of the domain. -/
  lt_dom : ∀ x y, lt x y → dom x ∧ dom y
  /-- Irreflexivity. -/
  irrefl : ∀ x, ¬ lt x x
  /-- Transitivity. -/
  trans : ∀ x y z, lt x y → lt y z → lt x z
  /-- Totality on the domain. -/
  total : ∀ x y, dom x → dom y → lt x y ∨ x = y ∨ lt y x
  /-- Well-foundedness: every non-empty part of the domain has a minimal element. -/
  wf : ∀ S : α → Prop, (∃ x, S x ∧ dom x) → ∃ m, S m ∧ dom m ∧ ∀ y, S y → dom y → ¬ lt y m

variable {α : Type u}

/-- Two partial well-orderings with the same domain and order are equal. -/
theorem PWO.ext {W V : PWO α} (h₁ : W.dom = V.dom) (h₂ : W.lt = V.lt) : W = V := by
  cases W; cases V
  cases h₁; cases h₂
  rfl

/-- `W ≤ V`: `V` **extends** `W` as an end-extension — `W` is an initial segment of `V`.
The domain grows, and below any point of `W` the two orders agree (so nothing new
is inserted below old points). -/
def Extends (W V : PWO α) : Prop :=
  (∀ x, W.dom x → V.dom x) ∧ ∀ x y, W.dom y → (V.lt x y ↔ W.lt x y)

/-- `Extends` is reflexive. -/
theorem extends_refl (W : PWO α) : Extends W W := ⟨fun _ h => h, fun _ _ _ => Iff.rfl⟩

/-- `Extends` is transitive. -/
theorem extends_trans {W V U : PWO α} (h₁ : Extends W V) (h₂ : Extends V U) : Extends W U :=
  ⟨fun x h => h₂.1 x (h₁.1 x h), fun x y hy => (h₂.2 x y (h₁.1 y hy)).trans (h₁.2 x y hy)⟩

/-- `Extends` is antisymmetric. -/
theorem extends_antisymm {W V : PWO α} (h₁ : Extends W V) (h₂ : Extends V W) : W = V := by
  have hdom : W.dom = V.dom := funext fun x => propext ⟨h₁.1 x, h₂.1 x⟩
  refine PWO.ext hdom (funext fun x => funext fun y => propext ?_)
  by_cases hy : W.dom y
  · exact (h₁.2 x y hy).symm
  · exact ⟨fun h => absurd (W.lt_dom x y h).2 hy,
      fun h => absurd (hdom ▸ (V.lt_dom x y h).2) hy⟩

section Union

variable (C : PWO α → Prop) (hC : Zorn.IsChain Extends C)

/-- The union of a chain of partial well-orderings. -/
def unionDom : α → Prop := fun x => ∃ W, C W ∧ W.dom x

/-- The order of the union of a chain. -/
def unionLt : α → α → Prop := fun x y => ∃ W, C W ∧ W.lt x y

include hC in
/-- Below a point of a member `W` of the chain, the union order agrees with `W`. -/
theorem unionLt_iff {W : PWO α} (hW : C W) {x y : α} (hy : W.dom y) :
    unionLt C x y ↔ W.lt x y := by
  refine ⟨fun ⟨V, hV, hxy⟩ => ?_, fun h => ⟨W, hW, h⟩⟩
  rcases hC W V hW hV with h | h
  · exact (h.2 x y hy).1 hxy
  · exact (h.2 x y (V.lt_dom x y hxy).2).2 hxy

/-- The union of a chain of partial well-orderings is a partial well-ordering. -/
noncomputable def unionPWO : PWO α where
  dom := unionDom C
  lt := unionLt C
  lt_dom := fun _ _ ⟨W, hW, h⟩ =>
    ⟨⟨W, hW, (W.lt_dom _ _ h).1⟩, ⟨W, hW, (W.lt_dom _ _ h).2⟩⟩
  irrefl := fun x ⟨W, _, h⟩ => W.irrefl x h
  trans := fun x y z ⟨W, hW, hxy⟩ ⟨V, hV, hyz⟩ => by
    have hy : V.dom y := (V.lt_dom y z hyz).1
    have hxy' : V.lt x y := (unionLt_iff C hC hV hy).1 ⟨W, hW, hxy⟩
    exact ⟨V, hV, V.trans x y z hxy' hyz⟩
  total := fun x y ⟨W, hW, hx⟩ ⟨V, hV, hy⟩ => by
    rcases hC W V hW hV with h | h
    · rcases V.total x y (h.1 x hx) hy with h' | h' | h'
      · exact Or.inl ⟨V, hV, h'⟩
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨V, hV, h'⟩)
    · rcases W.total x y hx (h.1 y hy) with h' | h' | h'
      · exact Or.inl ⟨W, hW, h'⟩
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨W, hW, h'⟩)
  wf := fun S ⟨x, hSx, W, hW, hx⟩ => by
    obtain ⟨m, hSm, hm, hmin⟩ := W.wf S ⟨x, hSx, hx⟩
    refine ⟨m, hSm, ⟨W, hW, hm⟩, fun y hSy _ hym => ?_⟩
    have hym' : W.lt y m := (unionLt_iff C hC hW hm).1 hym
    exact hmin y hSy (W.lt_dom y m hym').1 hym'

/-- Every member of a chain is extended by the union. -/
theorem extends_unionPWO {W : PWO α} (hW : C W) : Extends W (unionPWO C hC) :=
  ⟨fun _ hx => ⟨W, hW, hx⟩, fun _ _ hy => unionLt_iff C hC hW hy⟩

end Union

/-- Append a new element `a` on top of a partial well-ordering not containing it. -/
def PWO.append (M : PWO α) (a : α) (ha : ¬ M.dom a) : PWO α where
  dom := fun x => M.dom x ∨ x = a
  lt := fun x y => M.lt x y ∨ (M.dom x ∧ y = a)
  lt_dom := by
    rintro x y (h | ⟨hx, rfl⟩)
    · exact ⟨Or.inl (M.lt_dom x y h).1, Or.inl (M.lt_dom x y h).2⟩
    · exact ⟨Or.inl hx, Or.inr rfl⟩
  irrefl := by
    rintro x (h | ⟨hx, rfl⟩)
    · exact M.irrefl x h
    · exact ha hx
  trans := by
    rintro x y z (hxy | ⟨hx, rfl⟩) (hyz | ⟨hy, rfl⟩)
    · exact Or.inl (M.trans x y z hxy hyz)
    · exact Or.inr ⟨(M.lt_dom x y hxy).1, rfl⟩
    · exact absurd (M.lt_dom _ z hyz).1 ha
    · exact absurd hy ha
  total := by
    rintro x y (hx | rfl) (hy | rfl)
    · rcases M.total x y hx hy with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr ⟨hx, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hy, rfl⟩))
    · exact Or.inr (Or.inl rfl)
  wf := by
    intro S hS
    by_cases hM : ∃ x, S x ∧ M.dom x
    · obtain ⟨m, hSm, hm, hmin⟩ := M.wf S hM
      refine ⟨m, hSm, Or.inl hm, fun y hSy _ hym => ?_⟩
      rcases hym with h | ⟨_, rfl⟩
      · exact hmin y hSy (M.lt_dom y m h).1 h
      · exact ha hm
    · obtain ⟨x, hSx, hx⟩ := hS
      have hxa : x = a := hx.resolve_left fun h => hM ⟨x, hSx, h⟩
      subst hxa
      refine ⟨x, hSx, Or.inr rfl, fun y hSy _ hyx => ?_⟩
      rcases hyx with h | ⟨hy, _⟩
      · exact ha (M.lt_dom y x h).2
      · exact hM ⟨y, hSy, hy⟩

/-- Appending on top is an end-extension. -/
theorem extends_append (M : PWO α) (a : α) (ha : ¬ M.dom a) : Extends M (M.append a ha) := by
  refine ⟨fun x hx => Or.inl hx, fun x y hy => ⟨?_, Or.inl⟩⟩
  rintro (h | ⟨_, rfl⟩)
  · exact h
  · exact absurd hy ha

/-- **Zermelo's well-ordering theorem.** Every type `α` carries a well-ordering:
a strict total order `lt` in which every non-empty part has a least element.
Proved from Zorn's lemma. -/
theorem well_ordering_theorem (α : Type u) :
    ∃ lt : α → α → Prop, (∀ x, ¬ lt x x) ∧ (∀ x y z, lt x y → lt y z → lt x z) ∧
      (∀ x y, lt x y ∨ x = y ∨ lt y x) ∧
      (∀ S : α → Prop, (∃ x, S x) → ∃ m, S m ∧ ∀ y, S y → ¬ lt y m) := by
  obtain ⟨M, hM⟩ := Zorn.zorn (r := @Extends α) extends_refl (fun _ _ _ => extends_trans)
    (fun _ _ => extends_antisymm)
    (fun C hC => ⟨unionPWO C hC, fun _ hW => extends_unionPWO C hC hW⟩)
  have hall : ∀ a, M.dom a := fun a => Classical.byContradiction fun ha => by
    have heq := hM _ (extends_append M a ha)
    have : (M.append a ha).dom a := Or.inr rfl
    rw [heq] at this
    exact ha this
  refine ⟨M.lt, M.irrefl, M.trans, fun x y => M.total x y (hall x) (hall y), fun S ⟨x, hx⟩ => ?_⟩
  obtain ⟨m, hSm, _, hmin⟩ := M.wf S ⟨x, hx, hall x⟩
  exact ⟨m, hSm, fun y hy => hmin y hy (hall y)⟩

/-- A relation in which every non-empty part has a minimal element is
well-founded in Lean's sense (every element is accessible). -/
theorem wellFounded_of_min {α : Sort _} {lt : α → α → Prop}
    (h : ∀ S : α → Prop, (∃ x, S x) → ∃ m, S m ∧ ∀ y, S y → ¬ lt y m) : WellFounded lt := by
  refine ⟨fun a => Classical.byContradiction fun ha => ?_⟩
  obtain ⟨m, hm, hmin⟩ := h (fun x => ¬ Acc lt x) ⟨a, ha⟩
  exact hm ⟨m, fun y hy => Classical.byContradiction fun hy' => hmin y hy' hy⟩

/-- **Well-ordering theorem, `WellFounded` form.** Every type carries a strict total
order that is well-founded. -/
theorem exists_wellOrder (α : Type u) :
    ∃ lt : α → α → Prop, (∀ x y z, lt x y → lt y z → lt x z) ∧
      (∀ x y, lt x y ∨ x = y ∨ lt y x) ∧ WellFounded lt := by
  obtain ⟨lt, _, htrans, htot, hmin⟩ := well_ordering_theorem α
  exact ⟨lt, htrans, htot, wellFounded_of_min hmin⟩

end WellOrdering

end Foundations.Sets
