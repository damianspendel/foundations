import Foundations.Sets.Cardinality
import Foundations.Sets.Choice

/-!
# Comparing sizes: the comparability of cardinals

Cantor took it for granted that any two collections can be compared in size:
either the first fits into the second, or the second into the first. Without the
axiom of choice this cannot be proved — in fact Hartogs showed in 1915 that
comparability is *equivalent* to the axiom of choice. With choice (here in the
form of Zorn's lemma, proved in `Choice.lean`) it is a theorem:

* **Comparability.** For any two types `α` and `β`, there is an injection
  `α → β` or an injection `β → α`.

The proof considers *partial injections* from `α` to `β`: one-to-one
correspondences between a part of `α` and a part of `β`, recorded as a relation.
Ordered by inclusion they satisfy the hypothesis of Zorn's lemma (the union of a
chain of partial injections is again one), so there is a maximal one. If it left
out both a point `a` of `α` and a point `b` of `β`, we could add the pair
`(a, b)` and enlarge it; so it either uses up all of `α` — giving an injection
`α → β` — or all of `β` — giving an injection `β → α`.

Together with the Schröder–Bernstein theorem this makes "is at most as large as"
(`CardLE`) a **total preorder** on types whose associated equivalence is
equinumerosity: the sizes of collections form a linear order — the order of the
cardinal numbers.
-/

namespace Foundations.Sets

universe u v w

/-- `CardLE α β`: `α` is **at most as large as** `β`, i.e. `α` injects into `β`. -/
def CardLE (α : Sort u) (β : Sort v) : Prop := ∃ f : α → β, Function.Injective f

/-- `CardLT α β`: `α` is **strictly smaller** than `β`: it injects, but not conversely. -/
def CardLT (α : Sort u) (β : Sort v) : Prop := CardLE α β ∧ ¬ CardLE β α

namespace Comparability

/-- A **partial injection** from `α` to `β`, as a relation `rel a b` ("`a` is sent
to `b`") that is functional and injective. Its domain and range are implicit. -/
structure PInj (α : Type u) (β : Type v) where
  /-- The graph of the partial injection. -/
  rel : α → β → Prop
  /-- Each point is sent to at most one point. -/
  func : ∀ a b b', rel a b → rel a b' → b = b'
  /-- Distinct points are sent to distinct points. -/
  inj : ∀ a a' b, rel a b → rel a' b → a = a'

variable {α : Type u} {β : Type v}

/-- Two partial injections with the same graph are equal. -/
theorem PInj.ext {F G : PInj α β} (h : F.rel = G.rel) : F = G := by
  cases F; cases G; cases h; rfl

/-- Inclusion of graphs: `G` extends `F`. -/
def Le (F G : PInj α β) : Prop := ∀ a b, F.rel a b → G.rel a b

/-- The union of a chain of partial injections is a partial injection. -/
def unionPInj (C : PInj α β → Prop) (hC : Zorn.IsChain Le C) : PInj α β where
  rel a b := ∃ F, C F ∧ F.rel a b
  func a b b' := by
    rintro ⟨F, hF, h⟩ ⟨G, hG, h'⟩
    rcases hC F G hF hG with hle | hle
    · exact G.func a b b' (hle a b h) h'
    · exact F.func a b b' h (hle a b' h')
  inj a a' b := by
    rintro ⟨F, hF, h⟩ ⟨G, hG, h'⟩
    rcases hC F G hF hG with hle | hle
    · exact G.inj a a' b (hle a b h) h'
    · exact F.inj a a' b h (hle a' b h')

/-- Adding a new pair `(a₀, b₀)`, with `a₀` outside the domain and `b₀` outside
the range, to a partial injection. -/
def PInj.add (F : PInj α β) (a₀ : α) (b₀ : β) (ha : ∀ b, ¬ F.rel a₀ b)
    (hb : ∀ a, ¬ F.rel a b₀) : PInj α β where
  rel a b := F.rel a b ∨ (a = a₀ ∧ b = b₀)
  func a b b' := by
    rintro (h | ⟨h₁, h₂⟩) (h' | ⟨h₁', h₂'⟩)
    · exact F.func _ _ _ h h'
    · subst h₁'; exact absurd h (ha _)
    · subst h₁; exact absurd h' (ha _)
    · rw [h₂, h₂']
  inj a a' b := by
    rintro (h | ⟨h₁, h₂⟩) (h' | ⟨h₁', h₂'⟩)
    · exact F.inj _ _ _ h h'
    · subst h₂'; exact absurd h (hb _)
    · subst h₂; exact absurd h' (hb _)
    · rw [h₁, h₁']

/-- A maximal partial injection exists (Zorn's lemma). -/
theorem exists_maximal : ∃ M : PInj α β, ∀ G, Le M G → G = M :=
  Zorn.zorn (r := @Le α β) (fun _ _ _ h => h)
    (fun _ _ _ h₁ h₂ x y h => h₂ x y (h₁ x y h))
    (fun _ _ h₁ h₂ => PInj.ext (funext fun a => funext fun b => propext ⟨h₁ a b, h₂ a b⟩))
    (fun C hC => ⟨unionPInj C hC, fun F hF _ _ h => ⟨F, hF, h⟩⟩)

/-- A maximal partial injection is defined everywhere on `α` or hits everything in `β`. -/
theorem maximal_total {M : PInj α β} (hM : ∀ G, Le M G → G = M) :
    (∀ a, ∃ b, M.rel a b) ∨ (∀ b, ∃ a, M.rel a b) := by
  apply Classical.byContradiction
  intro hn
  have ha : ∃ a, ∀ b, ¬ M.rel a b := Classical.byContradiction fun h =>
    hn (Or.inl fun a => Classical.byContradiction fun h' => h ⟨a, fun b hb => h' ⟨b, hb⟩⟩)
  have hb : ∃ b, ∀ a, ¬ M.rel a b := Classical.byContradiction fun h =>
    hn (Or.inr fun b => Classical.byContradiction fun h' => h ⟨b, fun a ha => h' ⟨a, ha⟩⟩)
  obtain ⟨a₀, ha₀⟩ := ha
  obtain ⟨b₀, hb₀⟩ := hb
  have heq := hM (M.add a₀ b₀ ha₀ hb₀) (fun a b h => Or.inl h)
  have : (M.add a₀ b₀ ha₀ hb₀).rel a₀ b₀ := Or.inr ⟨rfl, rfl⟩
  rw [heq] at this
  exact ha₀ b₀ this

end Comparability

/-- A relation that is functional and total on `α` and injective yields an
injection `α → β` (choosing the value at each point). -/
theorem injective_of_rel {α : Type u} {β : Type v} (r : α → β → Prop)
    (inj : ∀ a a' b, r a b → r a' b → a = a') (tot : ∀ a, ∃ b, r a b) :
    ∃ f : α → β, Function.Injective f :=
  ⟨fun a => Classical.choose (tot a), fun a a' h => by
    have h₁ := Classical.choose_spec (tot a)
    have h₂ := Classical.choose_spec (tot a')
    simp only at h
    rw [h] at h₁
    exact inj a a' _ h₁ h₂⟩

/-- **Comparability of cardinals.** For any two types `α` and `β`, one injects
into the other. Proved from Zorn's lemma via a maximal partial injection. -/
theorem card_comparable (α : Type u) (β : Type v) : CardLE α β ∨ CardLE β α := by
  obtain ⟨M, hM⟩ := Comparability.exists_maximal (α := α) (β := β)
  rcases Comparability.maximal_total hM with h | h
  · exact Or.inl (injective_of_rel M.rel M.inj h)
  · exact Or.inr (injective_of_rel (fun b a => M.rel a b) (fun b b' a h₁ h₂ => M.func a b b' h₁ h₂) h)

/-- `CardLE` is reflexive. -/
theorem CardLE.refl (α : Sort u) : CardLE α α := ⟨id, fun _ _ h => h⟩

/-- `CardLE` is transitive. -/
theorem CardLE.trans {α : Sort u} {β : Sort v} {γ : Sort w} :
    CardLE α β → CardLE β γ → CardLE α γ := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  exact ⟨g ∘ f, fun _ _ h => hf (hg h)⟩

/-- Equinumerous types are each at most as large as the other. -/
theorem CardLE.of_equinum {α : Sort u} {β : Sort v} (h : Equinum α β) : CardLE α β :=
  let ⟨f, hf, _⟩ := h; ⟨f, hf⟩

/-- **Antisymmetry up to equinumerosity** (Schröder–Bernstein). -/
theorem CardLE.antisymm {α : Type u} {β : Type v} (h₁ : CardLE α β) (h₂ : CardLE β α) :
    Equinum α β := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact schroeder_bernstein hf hg

/-- **Cardinality is a total preorder.** "At most as large as" is reflexive,
transitive and total on types, and two types are each at most as large as the
other exactly when they are equinumerous. -/
theorem cardLE_total_preorder :
    (∀ α : Type u, CardLE α α) ∧
    (∀ α β γ : Type u, CardLE α β → CardLE β γ → CardLE α γ) ∧
    (∀ α β : Type u, CardLE α β ∨ CardLE β α) ∧
    (∀ α β : Type u, (CardLE α β ∧ CardLE β α) ↔ Equinum α β) :=
  ⟨CardLE.refl, fun _ _ _ => CardLE.trans, card_comparable,
   fun _ _ => ⟨fun h => CardLE.antisymm h.1 h.2,
     fun h => ⟨CardLE.of_equinum h, CardLE.of_equinum h.symm⟩⟩⟩

/-- **Trichotomy of cardinals.** Any two types are either strictly smaller, of the
same size, or strictly larger than each other. -/
theorem card_trichotomy (α : Type u) (β : Type v) :
    CardLT α β ∨ Equinum α β ∨ CardLT β α := by
  rcases card_comparable α β with h | h
  · by_cases h' : CardLE β α
    · exact Or.inr (Or.inl (CardLE.antisymm h h'))
    · exact Or.inl ⟨h, h'⟩
  · by_cases h' : CardLE α β
    · exact Or.inr (Or.inl (CardLE.antisymm h' h))
    · exact Or.inr (Or.inr ⟨h, h'⟩)

end Foundations.Sets
