import Foundations.Sets.Infinite

/-!
# The arithmetic of the infinite: κ · κ = κ

For finite numbers, multiplication makes things bigger: `n · n > n` once `n > 1`.
For infinite sizes Cantor found the opposite. Already `ℕ × ℕ ≃ ℕ`
(`Cardinality.lean`): a grid of numbers, infinite in two directions, can be
listed in a single sequence. The great generalisation, due to Hessenberg (1906)
for well-ordered sets and hence, with the axiom of choice, to all sets, is

* **κ · κ = κ for every infinite κ**: for any infinite type `α`, `α × α ≃ α`.

From it the whole of infinite cardinal arithmetic collapses into a single rule:
the sum and the product of two sizes, at least one of them infinite, is simply
the larger of the two (`α ⊕ β ≃ α × β ≃ max(α, β)`).

**The proof.** We follow Zorn's lemma once more. Fix a copy `e : ℕ ↪ α` of the
natural numbers inside `α`. Consider *partial squarings*: a part `A` of `α`
containing the copy of `ℕ`, together with an injection `A × A → A` (recorded as a
relation). The copy of `ℕ` itself carries one, by Cantor's pairing function, and
the union of a chain of partial squarings is again one; so Zorn gives a maximal
partial squaring with part `A`. Now compare `A` with its complement `C`
(comparability, `CardinalOrder.lean`):

* If `A` fits into `C`, say via `g`, let `B = g(A)`, a copy of `A` outside `A`.
  The new pairs in `(A ∪ B) × (A ∪ B)` — those not already in `A × A` — are at
  most as many as `(A ⊕ A) × (A ⊕ A)`, hence (using the injection `A × A → A`
  twice over) at most as many as `A`, hence as `B`. So we can send the new pairs
  injectively into `B` and enlarge the partial squaring — contradicting
  maximality.
* So `C` fits into `A`; then all of `α = A ∪ C` fits into `A ⊕ A`, hence into
  `A`, and `α × α` fits into `A × A`, hence into `A ⊆ α`. Schröder–Bernstein
  turns the injection `α × α → α` into a bijection.
-/

namespace Foundations.Sets

universe u v

namespace SquareAbsorb

variable {α : Type u}

/-- A **partial squaring** of `α` around the copy `e` of `ℕ`: a part `dom` of `α`
containing every `e n`, and an injection `dom × dom → dom` given by its graph `rel`. -/
structure PSq (e : Nat → α) where
  /-- The part of `α` being squared. -/
  dom : α → Prop
  /-- The graph of the injection `dom × dom → dom`. -/
  rel : α × α → α → Prop
  /-- The graph lives on `dom × dom` and lands in `dom`. -/
  rel_dom : ∀ p c, rel p c → dom p.1 ∧ dom p.2 ∧ dom c
  /-- Each pair has at most one image. -/
  func : ∀ p c c', rel p c → rel p c' → c = c'
  /-- Distinct pairs have distinct images. -/
  inj : ∀ p p' c, rel p c → rel p' c → p = p'
  /-- Every pair from `dom × dom` has an image. -/
  total : ∀ x y, dom x → dom y → ∃ c, rel (x, y) c
  /-- The copy of `ℕ` lies inside `dom`. -/
  base : ∀ n, dom (e n)

variable {e : Nat → α}

/-- Two partial squarings with the same part and graph are equal. -/
theorem PSq.ext {W V : PSq e} (h₁ : W.dom = V.dom) (h₂ : W.rel = V.rel) : W = V := by
  cases W; cases V; cases h₁; cases h₂; rfl

/-- `V` extends `W`: a larger part and a larger graph. -/
def Le (W V : PSq e) : Prop := (∀ x, W.dom x → V.dom x) ∧ ∀ p c, W.rel p c → V.rel p c

/-- The starting partial squaring: the copy of `ℕ`, squared by Cantor's pairing function. -/
def basePSq (he : Function.Injective e) : PSq e where
  dom x := ∃ n, e n = x
  rel p c := ∃ m n, p = (e m, e n) ∧ c = e (cantorPair (m, n))
  rel_dom p c := by
    rintro ⟨m, n, rfl, rfl⟩
    exact ⟨⟨m, rfl⟩, ⟨n, rfl⟩, ⟨_, rfl⟩⟩
  func p c c' := by
    rintro ⟨m, n, rfl, rfl⟩ ⟨m', n', hp, rfl⟩
    simp only [Prod.mk.injEq] at hp
    rw [he hp.1, he hp.2]
  inj p p' c := by
    rintro ⟨m, n, rfl, rfl⟩ ⟨m', n', rfl, hc⟩
    have := cantorPair_injective (he hc)
    simp only [Prod.mk.injEq] at this
    rw [this.1, this.2]
  total x y := by
    rintro ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨_, m, n, rfl, rfl⟩
  base n := ⟨n, rfl⟩

/-- The union of a non-empty chain of partial squarings is a partial squaring. -/
def unionPSq (C : PSq e → Prop) (hC : Zorn.IsChain Le C) (W₀ : PSq e) (hW₀ : C W₀) : PSq e where
  dom x := ∃ W, C W ∧ W.dom x
  rel p c := ∃ W, C W ∧ W.rel p c
  rel_dom p c := by
    rintro ⟨W, hW, h⟩
    have := W.rel_dom p c h
    exact ⟨⟨W, hW, this.1⟩, ⟨W, hW, this.2.1⟩, ⟨W, hW, this.2.2⟩⟩
  func p c c' := by
    rintro ⟨W, hW, h⟩ ⟨V, hV, h'⟩
    rcases hC W V hW hV with hle | hle
    · exact V.func _ _ _ (hle.2 _ _ h) h'
    · exact W.func _ _ _ h (hle.2 _ _ h')
  inj p p' c := by
    rintro ⟨W, hW, h⟩ ⟨V, hV, h'⟩
    rcases hC W V hW hV with hle | hle
    · exact V.inj _ _ _ (hle.2 _ _ h) h'
    · exact W.inj _ _ _ h (hle.2 _ _ h')
  total x y := by
    rintro ⟨W, hW, hx⟩ ⟨V, hV, hy⟩
    rcases hC W V hW hV with hle | hle
    · obtain ⟨c, hc⟩ := V.total x y (hle.1 x hx) hy
      exact ⟨c, V, hV, hc⟩
    · obtain ⟨c, hc⟩ := W.total x y hx (hle.1 y hy)
      exact ⟨c, W, hW, hc⟩
  base n := ⟨W₀, hW₀, W₀.base n⟩

/-- A maximal partial squaring exists (Zorn's lemma). -/
theorem exists_maximal (he : Function.Injective e) : ∃ M : PSq e, ∀ V, Le M V → V = M := by
  refine Zorn.zorn (r := @Le α e) (fun _ => ⟨fun _ h => h, fun _ _ h => h⟩)
    (fun _ _ _ h₁ h₂ => ⟨fun x h => h₂.1 x (h₁.1 x h), fun p c h => h₂.2 p c (h₁.2 p c h)⟩)
    (fun _ _ h₁ h₂ => PSq.ext (funext fun x => propext ⟨h₁.1 x, h₂.1 x⟩)
      (funext fun p => funext fun c => propext ⟨h₁.2 p c, h₂.2 p c⟩)) ?_
  intro C hC
  by_cases hne : ∃ W, C W
  · obtain ⟨W₀, hW₀⟩ := hne
    exact ⟨unionPSq C hC W₀ hW₀, fun W hW => ⟨fun x h => ⟨W, hW, h⟩, fun p c h => ⟨W, hW, h⟩⟩⟩
  · exact ⟨basePSq he, fun W hW => absurd ⟨W, hW⟩ hne⟩

/-! ### Working inside a partial squaring -/

section Inside

variable (M : PSq e)

/-- The squaring map `A × A → A` of a partial squaring, read off from its graph. -/
noncomputable def mu (q : {x // M.dom x} × {x // M.dom x}) : {x // M.dom x} :=
  ⟨Classical.choose (M.total q.1.1 q.2.1 q.1.2 q.2.2),
   (M.rel_dom _ _ (Classical.choose_spec (M.total q.1.1 q.2.1 q.1.2 q.2.2))).2.2⟩

/-- The squaring map follows the graph. -/
theorem mu_rel (q : {x // M.dom x} × {x // M.dom x}) : M.rel (q.1.1, q.2.1) (mu M q).1 :=
  Classical.choose_spec (M.total q.1.1 q.2.1 q.1.2 q.2.2)

/-- The squaring map is injective. -/
theorem mu_injective : Function.Injective (mu M) := by
  intro q q' h
  have h₁ := mu_rel M q
  have h₂ := mu_rel M q'
  rw [h] at h₁
  have := M.inj _ _ _ h₁ h₂
  simp only [Prod.mk.injEq] at this
  exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)

/-- Doubling inside `A`: an injection `A ⊕ A → A`, sending the two copies to the
pairs `(a, e 0)` and `(a, e 1)` and then squaring. -/
noncomputable def sigma : {x // M.dom x} ⊕ {x // M.dom x} → {x // M.dom x}
  | .inl a => mu M (a, ⟨e 0, M.base 0⟩)
  | .inr a => mu M (a, ⟨e 1, M.base 1⟩)

/-- Doubling is injective (as `e 0 ≠ e 1`). -/
theorem sigma_injective (he : Function.Injective e) : Function.Injective (sigma M) := by
  intro s t h
  cases s <;> cases t <;> simp only [sigma] at h <;> have h' := mu_injective M h <;>
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h'
  · rw [h'.1]
  · exact absurd (he h'.2) (by omega)
  · exact absurd (he h'.2) (by omega)
  · rw [h'.1]

end Inside

/-! ### Enlarging a partial squaring -/

section Extend

variable (M : PSq e) (g : {x // M.dom x} → {x // ¬ M.dom x})

/-- The enlarged part `A ∪ g(A)`. -/
def dom' (x : α) : Prop := M.dom x ∨ ∃ a, (g a).1 = x

/-- The new pairs: in `(A ∪ B) × (A ∪ B)` but not in `A × A`. -/
def NewPair (p : α × α) : Prop := dom' M g p.1 ∧ dom' M g p.2 ∧ ¬ (M.dom p.1 ∧ M.dom p.2)

/-- Coding the points of `A ∪ B` by points of `A` (injective on `A ∪ B`): old points
go to the first copy of `A`, new points `g a` go to `a` in the second copy. -/
noncomputable def code (x : α) : {x // M.dom x} :=
  open Classical in
  if hx : M.dom x then sigma M (.inl ⟨x, hx⟩)
  else if hx' : ∃ a, (g a).1 = x then sigma M (.inr (Classical.choose hx'))
  else ⟨e 0, M.base 0⟩

/-- Coding is injective on `A ∪ B`. -/
theorem code_inj (he : Function.Injective e) {x y : α} (hx : dom' M g x) (hy : dom' M g y)
    (h : code M g x = code M g y) : x = y := by
  have hs := sigma_injective M he
  by_cases ax : M.dom x <;> by_cases ay : M.dom y
  · simp only [code, ax, ay, ↓reduceDIte] at h
    have := hs h
    simp only [Sum.inl.injEq, Subtype.mk.injEq] at this
    exact this
  · have hy' := hy.resolve_left ay
    simp only [code, ax, ay, hy', ↓reduceDIte] at h
    exact absurd (hs h) (by intro h; cases h)
  · have hx' := hx.resolve_left ax
    simp only [code, ax, ay, hx', ↓reduceDIte] at h
    exact absurd (hs h) (by intro h; cases h)
  · have hx' := hx.resolve_left ax
    have hy' := hy.resolve_left ay
    simp only [code, ax, ay, hx', hy', ↓reduceDIte] at h
    have := hs h
    simp only [Sum.inr.injEq] at this
    rw [← Classical.choose_spec hx', ← Classical.choose_spec hy', this]

/-- Coding pairs: `(x, y) ↦ μ(code x, code y)`, injective on the new pairs. -/
noncomputable def pairCode (p : α × α) : {x // M.dom x} := mu M (code M g p.1, code M g p.2)

/-- Pair coding is injective on the new pairs. -/
theorem pairCode_inj (he : Function.Injective e) {p p' : α × α} (hp : NewPair M g p)
    (hp' : NewPair M g p') (h : pairCode M g p = pairCode M g p') : p = p' := by
  have := mu_injective M h
  simp only [Prod.mk.injEq] at this
  exact Prod.ext (code_inj M g he hp.1 hp'.1 this.1) (code_inj M g he hp.2.1 hp'.2.1 this.2)

/-- The enlarged partial squaring: old pairs as before, new pairs sent injectively
into the new points `B = g(A)`. -/
noncomputable def extend (he : Function.Injective e) (hg : Function.Injective g) : PSq e where
  dom := dom' M g
  rel p c := M.rel p c ∨ (NewPair M g p ∧ c = (g (pairCode M g p)).1)
  rel_dom p c := by
    rintro (h | ⟨hp, rfl⟩)
    · have := M.rel_dom p c h
      exact ⟨Or.inl this.1, Or.inl this.2.1, Or.inl this.2.2⟩
    · exact ⟨hp.1, hp.2.1, Or.inr ⟨_, rfl⟩⟩
  func p c c' := by
    rintro (h | ⟨hp, rfl⟩) (h' | ⟨hp', rfl⟩)
    · exact M.func _ _ _ h h'
    · exact absurd ⟨(M.rel_dom _ _ h).1, (M.rel_dom _ _ h).2.1⟩ hp'.2.2
    · exact absurd ⟨(M.rel_dom _ _ h').1, (M.rel_dom _ _ h').2.1⟩ hp.2.2
    · rfl
  inj p p' c := by
    rintro (h | ⟨hp, hc⟩) (h' | ⟨hp', hc'⟩)
    · exact M.inj _ _ _ h h'
    · exact absurd ((M.rel_dom _ _ h).2.2) (hc' ▸ (g _).2)
    · exact absurd ((M.rel_dom _ _ h').2.2) (hc ▸ (g _).2)
    · rw [hc] at hc'
      exact pairCode_inj M g he hp hp' (hg (Subtype.ext hc'))
  total x y hx hy := by
    by_cases hold : M.dom x ∧ M.dom y
    · obtain ⟨c, hc⟩ := M.total x y hold.1 hold.2
      exact ⟨c, Or.inl hc⟩
    · exact ⟨_, Or.inr ⟨⟨hx, hy, hold⟩, rfl⟩⟩
  base n := Or.inl (M.base n)

/-- A partial squaring whose part fits into its complement is not maximal. -/
theorem not_maximal (he : Function.Injective e) (hg : Function.Injective g)
    (hM : ∀ V, Le M V → V = M) : False := by
  have heq := hM (extend M g he hg) ⟨fun _ h => Or.inl h, fun _ _ h => Or.inl h⟩
  have hmem : (extend M g he hg).dom (g ⟨e 0, M.base 0⟩).1 := Or.inr ⟨_, rfl⟩
  rw [heq] at hmem
  exact (g ⟨e 0, M.base 0⟩).2 hmem

end Extend

end SquareAbsorb

open SquareAbsorb in
/-- Squaring absorbs, in the form needed: if `ℕ` embeds in `α`, then `α × α ≃ α`. -/
theorem mul_self_equinum_of_nat_le {α : Type u} (h : CardLE Nat α) : Equinum (α × α) α := by
  obtain ⟨e, he⟩ := h
  obtain ⟨M, hM⟩ := exists_maximal he
  rcases card_comparable {x // M.dom x} {x // ¬ M.dom x} with ⟨g, hg⟩ | ⟨k, hk⟩
  · exact (not_maximal M g he hg hM).elim
  · -- all of `α` fits into `A ⊕ A`, hence into `A`
    classical
    let j : α → {x // M.dom x} := fun x =>
      if hx : M.dom x then sigma M (.inl ⟨x, hx⟩) else sigma M (.inr (k ⟨x, hx⟩))
    have hj : Function.Injective j := by
      intro x y hxy
      have hs := sigma_injective M he
      by_cases ax : M.dom x <;> by_cases ay : M.dom y <;>
        simp only [j, ax, ay, ↓reduceDIte] at hxy <;> have := hs hxy
      · simp only [Sum.inl.injEq, Subtype.mk.injEq] at this; exact this
      · cases this
      · cases this
      · simp only [Sum.inr.injEq] at this
        have := hk this
        simp only [Subtype.mk.injEq] at this
        exact this
    let F : α × α → α := fun p => (mu M (j p.1, j p.2)).1
    have hF : Function.Injective F := by
      intro p q hpq
      have := mu_injective M (Subtype.ext hpq)
      simp only [Prod.mk.injEq] at this
      exact Prod.ext (hj this.1) (hj this.2)
    exact schroeder_bernstein (f := F) (g := fun a => (a, a)) hF
      (fun a b h => (Prod.mk.inj h).1)

/-- **κ · κ = κ.** For every infinite type `α`, the type of pairs `α × α` is
equinumerous with `α`. (Hessenberg's theorem; uses Zorn's lemma.) -/
theorem mul_self_equinum {α : Type u} (h : IsInfinite α) : Equinum (α × α) α :=
  mul_self_equinum_of_nat_le (nat_le_of_isInfinite h)

/-! ## Consequences: sums and products of infinite sizes -/

/-- **κ + κ = κ.** For every infinite type `α`, `α ⊕ α ≃ α`. -/
theorem add_self_equinum {α : Type u} (h : IsInfinite α) : Equinum (α ⊕ α) α := by
  obtain ⟨e, he⟩ := nat_le_of_isInfinite h
  obtain ⟨m, hm, _⟩ := mul_self_equinum h
  let F : α ⊕ α → α := fun
    | .inl a => m (a, e 0)
    | .inr a => m (a, e 1)
  have hF : Function.Injective F := by
    intro s t hst
    cases s <;> cases t <;> simp only [F] at hst <;> have := hm hst <;>
      simp only [Prod.mk.injEq] at this
    · rw [this.1]
    · exact absurd (he this.2) (by omega)
    · exact absurd (he this.2) (by omega)
    · rw [this.1]
  exact schroeder_bernstein (f := F) (g := Sum.inl) hF (fun a b h => Sum.inl.inj h)

/-- If `α` is infinite and `β` is no larger, then `α ⊕ β ≃ α`. -/
theorem sum_equinum_of_le {α : Type u} {β : Type v} (h : IsInfinite α) (hβ : CardLE β α) :
    Equinum (α ⊕ β) α := by
  obtain ⟨k, hk⟩ := hβ
  obtain ⟨d, hd, _⟩ := add_self_equinum h
  let F : α ⊕ β → α := fun
    | .inl a => d (.inl a)
    | .inr b => d (.inr (k b))
  have hF : Function.Injective F := by
    intro s t hst
    cases s <;> cases t <;> simp only [F] at hst <;> have := hd hst
    · rw [Sum.inl.inj this]
    · cases this
    · cases this
    · rw [hk (Sum.inr.inj this)]
  exact schroeder_bernstein (f := F) (g := Sum.inl) hF (fun a b h => Sum.inl.inj h)

/-- If `α` is infinite and `β` is non-empty and no larger, then `α × β ≃ α`. -/
theorem prod_equinum_of_le {α : Type u} {β : Type v} (h : IsInfinite α) (hβ : CardLE β α)
    (b₀ : β) : Equinum (α × β) α := by
  obtain ⟨k, hk⟩ := hβ
  obtain ⟨m, hm, _⟩ := mul_self_equinum h
  refine schroeder_bernstein (f := fun p : α × β => m (p.1, k p.2)) (g := fun a => (a, b₀))
    (fun p q hpq => ?_) (fun a b h => (Prod.mk.inj h).1)
  have := hm hpq
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 (hk this.2)

/-- Exchanging the factors of a product is a bijection. -/
theorem prod_comm_equinum (α : Type u) (β : Type v) : Equinum (α × β) (β × α) :=
  ⟨fun p => (p.2, p.1), fun p q h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1, fun q => ⟨(q.2, q.1), rfl⟩⟩

/-- Exchanging the summands of a sum is a bijection. -/
theorem sum_comm_equinum (α : Type u) (β : Type v) : Equinum (α ⊕ β) (β ⊕ α) :=
  ⟨fun | .inl a => .inr a | .inr b => .inl b,
   fun s t h => by cases s <;> cases t <;> simp_all,
   fun | .inl b => ⟨.inr b, rfl⟩ | .inr a => ⟨.inl a, rfl⟩⟩

/-- **Infinite sums are maxima.** If `α` is infinite, then `α ⊕ β` is equinumerous
with the larger of `α` and `β`. -/
theorem sum_equinum_max {α : Type u} {β : Type v} (h : IsInfinite α) :
    (CardLE β α ∧ Equinum (α ⊕ β) α) ∨ (CardLE α β ∧ Equinum (α ⊕ β) β) := by
  rcases card_comparable β α with hle | hle
  · exact Or.inl ⟨hle, sum_equinum_of_le h hle⟩
  · have hβ : IsInfinite β := isInfinite_of_nat_le ((nat_le_of_isInfinite h).trans hle)
    exact Or.inr ⟨hle, (sum_comm_equinum α β).trans (sum_equinum_of_le hβ hle)⟩

/-- **Infinite products are maxima.** If `α` is infinite and `β` non-empty, then
`α × β` is equinumerous with the larger of `α` and `β`. -/
theorem prod_equinum_max {α : Type u} {β : Type v} (h : IsInfinite α) (b₀ : β) :
    (CardLE β α ∧ Equinum (α × β) α) ∨ (CardLE α β ∧ Equinum (α × β) β) := by
  rcases card_comparable β α with hle | hle
  · exact Or.inl ⟨hle, prod_equinum_of_le h hle b₀⟩
  · have hβ : IsInfinite β := isInfinite_of_nat_le ((nat_le_of_isInfinite h).trans hle)
    obtain ⟨e, _⟩ := nat_le_of_isInfinite h
    exact Or.inr ⟨hle, (prod_comm_equinum α β).trans (prod_equinum_of_le hβ hle (e 0))⟩

end Foundations.Sets
