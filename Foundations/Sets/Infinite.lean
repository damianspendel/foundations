import Foundations.Sets.CardinalOrder

/-!
# What it means to be infinite

There are two classical ways to say that a collection is infinite.

* **Not finite**: it cannot be counted off as `0, 1, …, n - 1` for any `n`; we say
  a type is *finite* when it injects into `Fin n = {0, …, n - 1}` for some `n`.
* **Dedekind-infinite**: it can be mapped one-to-one onto a *proper part* of
  itself. Galileo had noticed, puzzled, that the square numbers are in
  one-to-one correspondence with all numbers; Dedekind (1888) turned the paradox
  into a definition.

A third, more concrete property is that the natural numbers **embed** in the
collection (`ℕ ↪ α`). Here we prove that all three agree:

* `ℕ ↪ α` ⇒ Dedekind-infinite: shift the copy of `ℕ` one step along, `n ↦ n + 1`,
  and leave everything else fixed; the first point of the copy is missed.
* Dedekind-infinite ⇒ `ℕ ↪ α`: take a point `a` that `f` misses and follow its
  orbit `a, f a, f (f a), …`; the orbit never repeats.
* `ℕ ↪ α` ⇒ not finite: this is the **pigeonhole principle** — `n + 1` pigeons
  do not fit injectively into `n` holes — proved by induction on `n`.
* not finite ⇒ `ℕ ↪ α`: here the **axiom of choice** enters (in its weak,
  "dependent" form). Since no finite list exhausts `α`, we can keep choosing new
  points: having chosen `a₀, …, aₙ₋₁`, choose `aₙ` outside the list.

Without some choice, "infinite but Dedekind-finite" sets are consistent with ZF;
so the last step is not a mere technicality.
-/

namespace Foundations.Sets

universe u

/-- A type is **finite** when it injects into `Fin n = {0, …, n - 1}` for some `n`. -/
def IsFinite (α : Sort u) : Prop := ∃ n, ∃ f : α → Fin n, Function.Injective f

/-- A type is **infinite** when it is not finite. -/
def IsInfinite (α : Sort u) : Prop := ¬ IsFinite α

/-- A type is **Dedekind-infinite** when some injection of it into itself is not
surjective: it is in one-to-one correspondence with a proper part of itself. -/
def DedekindInfinite (α : Sort u) : Prop :=
  ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f

/-! ## The pigeonhole principle -/

/-- **Pigeonhole principle (arithmetic form).** If `f` sends each of `0, …, n` to a
number below `n`, two of them collide. -/
theorem pigeonhole_nat : ∀ n (f : Nat → Nat), (∀ i, i < n + 1 → f i < n) →
    ∃ i j, i < j ∧ j < n + 1 ∧ f i = f j := by
  intro n
  induction n with
  | zero => intro f hf; exact absurd (hf 0 (Nat.zero_lt_one)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro f hf
    -- either something collides with the last pigeon `n + 1` ...
    by_cases hc : ∃ i, i < n + 1 ∧ f i = f (n + 1)
    · obtain ⟨i, hi, he⟩ := hc
      exact ⟨i, n + 1, hi, Nat.lt_succ_self _, he⟩
    · -- ... or we move the pigeons in hole `n` to the last pigeon's hole and recurse
      have hne : ∀ i, i < n + 1 → f i ≠ f (n + 1) := fun i hi he => hc ⟨i, hi, he⟩
      let g : Nat → Nat := fun i => if f i = n then f (n + 1) else f i
      have hg : ∀ i, i < n + 1 → g i < n := by
        intro i hi
        have h1 := hf i (by omega)
        have h2 := hf (n + 1) (by omega)
        have h3 := hne i hi
        simp only [g]
        split <;> omega
      obtain ⟨i, j, hij, hj, he⟩ := ih g hg
      simp only [g] at he
      by_cases hi' : f i = n <;> by_cases hj' : f j = n <;> simp only [hi', hj', ↓reduceIte] at he
      · exact ⟨i, j, hij, by omega, by rw [hi', hj']⟩
      · exact absurd he.symm (hne j (by omega))
      · exact absurd he (hne i (by omega))
      · exact ⟨i, j, hij, by omega, he⟩

/-- **Pigeonhole principle.** There is no injection `Fin (n + 1) → Fin n`. -/
theorem no_injection_fin_succ (n : Nat) (f : Fin (n + 1) → Fin n) : ¬ Function.Injective f := by
  intro hf
  let F : Nat → Nat := fun i => if h : i < n + 1 then (f ⟨i, h⟩).val else 0
  obtain ⟨i, j, hij, hj, he⟩ := pigeonhole_nat n F (fun i hi => by
    simp only [F, hi, ↓reduceDIte]; exact (f ⟨i, hi⟩).isLt)
  simp only [F, show i < n + 1 by omega, hj, ↓reduceDIte] at he
  have := hf (Fin.ext he)
  simp only [Fin.mk.injEq] at this
  omega

/-- The natural numbers do not inject into any `Fin n`. -/
theorem no_injection_nat_fin (n : Nat) (f : Nat → Fin n) : ¬ Function.Injective f := fun hf =>
  no_injection_fin_succ n (fun i => f i.val) (fun _ _ h => Fin.ext (hf h))

/-! ## Finite and infinite -/

/-- Each `Fin n` is finite. -/
theorem isFinite_fin (n : Nat) : IsFinite (Fin n) := ⟨n, id, fun _ _ h => h⟩

/-- A type that injects into a finite type is finite. -/
theorem IsFinite.of_injective {α : Sort u} {β : Sort _} {f : α → β}
    (hf : Function.Injective f) (hβ : IsFinite β) : IsFinite α :=
  let ⟨n, g, hg⟩ := hβ; ⟨n, g ∘ f, fun _ _ h => hf (hg h)⟩

/-- A type into which `ℕ` embeds is infinite (pigeonhole). -/
theorem isInfinite_of_nat_le {α : Sort u} (h : CardLE Nat α) : IsInfinite α := by
  rintro ⟨n, f, hf⟩
  obtain ⟨e, he⟩ := h
  exact no_injection_nat_fin n (f ∘ e) (fun _ _ h => he (hf h))

/-- **The natural numbers are infinite.** -/
theorem nat_isInfinite : IsInfinite Nat := isInfinite_of_nat_le (CardLE.refl Nat)

/-- No finite list exhausts an infinite type. -/
theorem IsInfinite.exists_not_mem {α : Type u} (h : IsInfinite α) (l : List α) :
    ∃ a, a ∉ l := by
  apply Classical.byContradiction
  intro hall
  have hmem : ∀ a, a ∈ l := fun a => Classical.byContradiction fun ha => hall ⟨a, ha⟩
  -- every element has a position in the list: an injection into `Fin l.length`
  have hpos : ∀ a, ∃ i : Fin l.length, l[i] = a := fun a => by
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 (hmem a)
    exact ⟨⟨i, hi⟩, he⟩
  refine h ⟨l.length, fun a => Classical.choose (hpos a), fun a b hab => ?_⟩
  have ha := Classical.choose_spec (hpos a)
  have hb := Classical.choose_spec (hpos b)
  simp only at hab
  rw [← ha, ← hb, hab]

section Enumeration

variable {α : Type u} (h : IsInfinite α)

/-- A chosen point outside the list `l` (exists since `α` is infinite). -/
noncomputable def freshPoint (l : List α) : α := Classical.choose (h.exists_not_mem l)

/-- The chosen fresh point is not in the list. -/
theorem freshPoint_not_mem (l : List α) : freshPoint h l ∉ l :=
  Classical.choose_spec (h.exists_not_mem l)

/-- The list `[aₙ₋₁, …, a₀]` of the first `n` points chosen, each fresh for the previous ones. -/
noncomputable def chosenList : Nat → List α
  | 0 => []
  | n + 1 => freshPoint h (chosenList n) :: chosenList n

/-- The `n`-th chosen point. -/
noncomputable def chosenSeq (n : Nat) : α := freshPoint h (chosenList h n)

/-- Earlier points stay in later lists. -/
theorem chosenSeq_mem_chosenList {m n : Nat} (hmn : m < n) : chosenSeq h m ∈ chosenList h n := by
  induction n with
  | zero => exact absurd hmn (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [chosenList, List.mem_cons]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hmn) with hlt | heq
    · exact Or.inr (ih hlt)
    · subst heq; exact Or.inl rfl

/-- The chosen sequence never repeats. -/
theorem chosenSeq_injective : Function.Injective (chosenSeq h) := by
  intro m n hmn
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · have := chosenSeq_mem_chosenList h hlt
    rw [hmn] at this
    exact absurd this (freshPoint_not_mem h _)
  · exact heq
  · have := chosenSeq_mem_chosenList h hgt
    rw [← hmn] at this
    exact absurd this (freshPoint_not_mem h _)

end Enumeration

/-- **Infinite types contain a copy of ℕ** (uses choice). -/
theorem nat_le_of_isInfinite {α : Type u} (h : IsInfinite α) : CardLE Nat α :=
  ⟨chosenSeq h, chosenSeq_injective h⟩

/-- **Infinite ⇔ ℕ ↪ α.** A type is infinite exactly when the natural numbers embed in it. -/
theorem isInfinite_iff_nat_le {α : Type u} : IsInfinite α ↔ CardLE Nat α :=
  ⟨nat_le_of_isInfinite, isInfinite_of_nat_le⟩

/-! ## Dedekind-infinity -/

/-- The orbit `a, f a, f (f a), …` of a point under a map. -/
def orbit {α : Sort u} (f : α → α) (a : α) : Nat → α
  | 0 => a
  | n + 1 => f (orbit f a n)

/-- The orbit of a point missed by an injection never repeats. -/
theorem orbit_injective {α : Sort u} {f : α → α} (hf : Function.Injective f) {a : α}
    (ha : ∀ x, f x ≠ a) : Function.Injective (orbit f a) := by
  intro m
  induction m with
  | zero =>
    intro n h
    cases n with
    | zero => rfl
    | succ n => exact absurd h.symm (ha _)
  | succ m ih =>
    intro n h
    cases n with
    | zero => exact absurd h (ha _)
    | succ n => exact congrArg Nat.succ (ih (hf h))

/-- A Dedekind-infinite type contains a copy of `ℕ` (no choice of sequence needed:
the orbit of a missed point). -/
theorem nat_le_of_dedekindInfinite {α : Sort u} (h : DedekindInfinite α) : CardLE Nat α := by
  obtain ⟨f, hf, hns⟩ := h
  have : ∃ a, ∀ x, f x ≠ a := Classical.byContradiction fun hn =>
    hns fun a => Classical.byContradiction fun ha => hn ⟨a, fun x hx => ha ⟨x, hx⟩⟩
  obtain ⟨a, ha⟩ := this
  exact ⟨orbit f a, orbit_injective hf ha⟩

/-- A type containing a copy of `ℕ` is Dedekind-infinite: shift the copy along. -/
theorem dedekindInfinite_of_nat_le {α : Sort u} (h : CardLE Nat α) : DedekindInfinite α := by
  classical
  obtain ⟨e, he⟩ := h
  let f : α → α := fun x => if hx : ∃ n, e n = x then e (Classical.choose hx + 1) else x
  have hfe : ∀ n, f (e n) = e (n + 1) := by
    intro n
    have hx : ∃ m, e m = e n := ⟨n, rfl⟩
    simp only [f, hx, ↓reduceDIte]
    rw [he (Classical.choose_spec hx)]
  refine ⟨f, fun x y hxy => ?_, fun hs => ?_⟩
  · by_cases hx : ∃ n, e n = x <;> by_cases hy : ∃ n, e n = y
    · obtain ⟨m, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := hy
      rw [hfe, hfe] at hxy
      rw [show m = n by have := he hxy; omega]
    · obtain ⟨m, rfl⟩ := hx
      simp only [f, hy, ↓reduceDIte, hfe] at hxy
      exact absurd ⟨m + 1, hxy⟩ hy
    · obtain ⟨n, rfl⟩ := hy
      simp only [f, hx, ↓reduceDIte, hfe] at hxy
      exact absurd ⟨n + 1, hxy.symm⟩ hx
    · simpa only [f, hx, hy, ↓reduceDIte] using hxy
  · obtain ⟨x, hx⟩ := hs (e 0)
    by_cases hx' : ∃ n, e n = x
    · obtain ⟨n, rfl⟩ := hx'
      rw [hfe] at hx
      exact absurd (he hx) (by omega)
    · simp only [f, hx', ↓reduceDIte] at hx
      exact hx' ⟨0, hx.symm⟩

/-- **Infinite ⇔ Dedekind-infinite ⇔ ℕ ↪ α.** The three notions of infinity agree
(the passage from "not finite" to the others uses the axiom of choice). -/
theorem infinite_tfae (α : Type u) :
    (IsInfinite α ↔ DedekindInfinite α) ∧ (DedekindInfinite α ↔ CardLE Nat α) :=
  ⟨⟨fun h => dedekindInfinite_of_nat_le (nat_le_of_isInfinite h),
    fun h => isInfinite_of_nat_le (nat_le_of_dedekindInfinite h)⟩,
   ⟨nat_le_of_dedekindInfinite, dedekindInfinite_of_nat_le⟩⟩

end Foundations.Sets
