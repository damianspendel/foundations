import Foundations.Sets.SchroederBernstein

/-!
# Cardinality: countable and uncountable

Cantor's great discovery was that infinite collections come in different sizes.
Two collections have the *same size* (are **equinumerous**) when there is a
one-to-one correspondence between them; a collection is **countable** when it
can be injected into the natural numbers — when its members can be tagged by
distinct numbers.

In this file we work with Lean types rather than ZF sets, since that is where
these facts are used later in the project. We show:

* **ℕ × ℕ ≃ ℕ**, by Cantor's explicit pairing function, which walks through the
  grid of pairs diagonal by diagonal: `(0,0), (1,0), (0,1), (2,0), (1,1), …`.
  So "infinitely many infinities of numbers" are no more than the numbers.
* The integers and finite lists of naturals are countable.
* A countable union of countable collections is countable (this needs the axiom
  of choice, to pick an enumeration of each piece simultaneously).
* **α < 𝒫(α)**: every type injects into its power type `α → Prop`, but nothing
  injects back — Cantor's theorem in its sharpest form.
* **ℕ → Bool is uncountable**: the infinite binary sequences (equivalently, the
  real numbers in binary) cannot be listed. This is Cantor's diagonal argument.
-/

namespace Foundations.Sets

/-! ## Equinumerosity -/

/-- `α` and `β` are **equinumerous** when there is a bijection `α → β`. -/
def Equinum (α : Sort _) (β : Sort _) : Prop := ∃ f : α → β, Bijective f

/-- A type is **countable** when it injects into the natural numbers. -/
def Countable (α : Sort _) : Prop := ∃ f : α → Nat, Function.Injective f

/-- Every type is equinumerous with itself. -/
theorem Equinum.refl (α : Sort _) : Equinum α α := ⟨id, fun _ _ h => h, fun b => ⟨b, rfl⟩⟩

/-- Equinumerosity is symmetric (the inverse of a bijection is chosen pointwise). -/
theorem Equinum.symm {α β : Sort _} : Equinum α β → Equinum β α := by
  rintro ⟨f, hfi, hfs⟩
  let g : β → α := fun b => Classical.choose (hfs b)
  have hg : ∀ b, f (g b) = b := fun b => Classical.choose_spec (hfs b)
  refine ⟨g, fun b b' h => ?_, fun a => ⟨f a, hfi (hg (f a))⟩⟩
  rw [← hg b, ← hg b', h]

/-- Equinumerosity is transitive. -/
theorem Equinum.trans {α β γ : Sort _} : Equinum α β → Equinum β γ → Equinum α γ := by
  rintro ⟨f, hfi, hfs⟩ ⟨g, hgi, hgs⟩
  refine ⟨g ∘ f, fun a a' h => hfi (hgi h), fun c => ?_⟩
  obtain ⟨b, rfl⟩ := hgs c
  obtain ⟨a, rfl⟩ := hfs b
  exact ⟨a, rfl⟩

/-- An injection into a countable type makes the source countable. -/
theorem Countable.of_injective {α β : Sort _} {f : α → β} (hf : Function.Injective f)
    (hβ : Countable β) : Countable α :=
  let ⟨e, he⟩ := hβ; ⟨e ∘ f, fun _ _ h => hf (he h)⟩

/-- A type in bijection with a countable type is countable. -/
theorem Countable.of_equinum {α β : Sort _} (h : Equinum α β) (hβ : Countable β) : Countable α :=
  let ⟨_, hf, _⟩ := h; hβ.of_injective hf

/-- The natural numbers are countable. -/
theorem countable_nat : Countable Nat := ⟨id, fun _ _ h => h⟩

/-! ## Cantor's pairing function -/

/-- Triangular numbers: `tri s = 0 + 1 + ⋯ + s`, the number of grid points on the
diagonals before diagonal `s`. -/
def tri : Nat → Nat
  | 0 => 0
  | s + 1 => tri s + s + 1

/-- Triangular numbers are monotone. -/
theorem tri_mono {s t : Nat} (h : s ≤ t) : tri s ≤ tri t := by
  induction t with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have := ih (by omega); simp only [tri]; omega
    · rw [Nat.le_antisymm h hge]; exact Nat.le_refl _

/-- Diagonal `s` ends before diagonal `t > s` begins: `tri s + s < tri t`. -/
theorem tri_gap {s t : Nat} (h : s < t) : tri s + s < tri t := by
  have := tri_mono (Nat.succ_le_of_lt h)
  simp only [tri] at this
  omega

/-- **Cantor's pairing function** `(m, n) ↦ tri (m + n) + n`: position `n` on diagonal `m + n`. -/
def cantorPair (p : Nat × Nat) : Nat := tri (p.1 + p.2) + p.2

/-- Cantor's pairing function is injective. -/
theorem cantorPair_injective : Function.Injective cantorPair := by
  rintro ⟨m, n⟩ ⟨m', n'⟩ h
  simp only [cantorPair] at h
  rcases Nat.lt_trichotomy (m + n) (m' + n') with hl | he | hg
  · have := tri_gap hl; omega
  · rw [he] at h
    have hn : n = n' := by omega
    have hm : m = m' := by omega
    rw [hm, hn]
  · have := tri_gap hg; omega

/-- Cantor's pairing function is surjective: every number codes some pair. -/
theorem cantorPair_surjective : Function.Surjective cantorPair := by
  intro k
  induction k with
  | zero => exact ⟨(0, 0), rfl⟩
  | succ k ih =>
    obtain ⟨⟨m, n⟩, hk⟩ := ih
    cases m with
    | zero =>
      -- end of a diagonal: jump to the start of the next one
      refine ⟨(n + 1, 0), ?_⟩
      simp only [cantorPair, Nat.zero_add] at hk
      simp only [cantorPair, Nat.add_zero, tri]
      omega
    | succ m =>
      -- move one step along the diagonal
      refine ⟨(m, n + 1), ?_⟩
      simp only [cantorPair] at hk ⊢
      rw [show m + (n + 1) = m + 1 + n by omega]
      omega

/-- **ℕ × ℕ ≃ ℕ.** Cantor's pairing function is a bijection between pairs of
natural numbers and natural numbers. -/
theorem nat_prod_equinum_nat : Equinum (Nat × Nat) Nat :=
  ⟨cantorPair, cantorPair_injective, cantorPair_surjective⟩

/-! ## Countable types -/

/-- Encoding integers by naturals: `n ↦ 2n`, `-(n+1) ↦ 2n + 1`. -/
def encodeInt : Int → Nat
  | Int.ofNat n => 2 * n
  | Int.negSucc n => 2 * n + 1

/-- **The integers are countable.** -/
theorem countable_int : Countable Int := by
  refine ⟨encodeInt, ?_⟩
  intro a b h
  cases a <;> cases b <;> simp only [encodeInt] at h
  · exact congrArg Int.ofNat (by omega)
  · omega
  · omega
  · exact congrArg Int.negSucc (by omega)

/-- Encoding lists of naturals: `[] ↦ 0`, `x :: l ↦ cantorPair (x, code l) + 1`. -/
def encodeList : List Nat → Nat
  | [] => 0
  | x :: l => cantorPair (x, encodeList l) + 1

/-- **Finite lists of naturals are countable.** -/
theorem countable_list_nat : Countable (List Nat) := by
  refine ⟨encodeList, ?_⟩
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ with
    | nil => rfl
    | cons y l₂ => simp [encodeList] at h
  | cons x l₁ ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp [encodeList] at h
    | cons y l₂ =>
      simp only [encodeList, Nat.add_right_cancel_iff] at h
      have h' := cantorPair_injective h
      simp only [Prod.mk.injEq] at h'
      rw [h'.1, ih h'.2]

/-- **A countable union of countable types is countable.** If the index type `ι`
is countable and every `β i` is countable, then the (disjoint) union
`Σ i, β i` is countable. Uses choice to pick an injection for every `i` at once. -/
theorem countable_sigma {ι : Type _} {β : ι → Type _} (hι : Countable ι)
    (hβ : ∀ i, Countable (β i)) : Countable (Σ i, β i) := by
  obtain ⟨e, he⟩ := hι
  let f : ∀ i, β i → Nat := fun i => Classical.choose (hβ i)
  have hf : ∀ i, Function.Injective (f i) := fun i => Classical.choose_spec (hβ i)
  refine ⟨fun p => cantorPair (e p.1, f p.1 p.2), ?_⟩
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have h' := cantorPair_injective h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hij, hbc⟩ := h'
  have hij' : i = j := he hij
  subst hij'
  rw [hf i hbc]

/-! ## Uncountability -/

/-- From an injection `β → α` with `β` inhabited, choice yields a surjection `α → β`. -/
theorem exists_surjective_of_injective {α β : Sort _} {e : β → α} (he : Function.Injective e)
    (b₀ : β) : ∃ f : α → β, Function.Surjective f := by
  classical
  refine ⟨fun a => if h : ∃ b, e b = a then Classical.choose h else b₀, fun b => ⟨e b, ?_⟩⟩
  have h : ∃ b', e b' = e b := ⟨b, rfl⟩
  simp only [h, ↓reduceDIte]
  exact he (Classical.choose_spec h)

/-- **α < 𝒫(α).** Every type injects into its power type `α → Prop`
(via `a ↦ {a}`), but no function from `α → Prop` back into `α` is injective. -/
theorem lt_powerType (α : Type _) :
    (∃ f : α → (α → Prop), Function.Injective f) ∧ ¬ ∃ g : (α → Prop) → α, Function.Injective g := by
  refine ⟨⟨fun a x => x = a, fun a b h => ?_⟩, ?_⟩
  · have := congrFun h a
    simp only [eq_iff_iff, true_iff] at this
    exact this.symm ▸ rfl
  · rintro ⟨g, hg⟩
    obtain ⟨f, hf⟩ := exists_surjective_of_injective hg (fun _ => False)
    exact cantor_type ⟨f, hf⟩

/-- A type is never equinumerous with its power type. -/
theorem not_equinum_powerType (α : Type _) : ¬ Equinum α (α → Prop) := fun h =>
  let ⟨g, hg, _⟩ := h.symm; (lt_powerType α).2 ⟨g, hg⟩

/-- **Cantor's diagonal argument for binary sequences.** No function from `α` to
`α → Bool` is surjective. -/
theorem cantor_bool {α : Type _} : ¬ ∃ f : α → (α → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨d, hd⟩ := hf (fun x => !(f x x))
  have := congrFun hd d
  cases h : f d d <;> simp [h] at this

/-- **ℕ → Bool is uncountable.** The infinite binary sequences cannot be injected
into the natural numbers. -/
theorem nat_bool_uncountable : ¬ Countable (Nat → Bool) := by
  rintro ⟨e, he⟩
  obtain ⟨f, hf⟩ := exists_surjective_of_injective he (fun _ => false)
  exact cantor_bool ⟨f, hf⟩

end Foundations.Sets
