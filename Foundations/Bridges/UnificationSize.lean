import Foundations.Bridges.Unification
import Foundations.Sets.Cardinality
import Foundations.Sets.Infinite
import Foundations.Algebra.Finite
import Foundations.Logic.FOCompleteness

/-!
# Unification II: countable and finite, said two ways

The previous file reconciled duplicate *arithmetic* notions. This one reconciles two
pairs of duplicate notions of *size*.

**Countability.** Part I (`Sets/Cardinality.lean`) calls a type countable when it
*injects* into `ℕ` — its members can be tagged by distinct numbers. The logic of
Part III (`Logic/FOCompleteness.lean`, `Logic/TermModel.lean`,
`Logic/NonstandardArithmetic.lean`) and Part II's uncountability of the reals
(`Numbers/Uncountable.lean`) instead say "there is a *surjection* from `ℕ`" — its
members can be listed, possibly with repetitions. For a nonempty type the two agree:
from a listing, tag each member by (a chosen) position where it occurs; from a tagging,
list the members by sending each tag to the member carrying it and every unused number
to a fixed default member. (The empty type injects into `ℕ` but is not listed by any
function `ℕ → ∅`; this is the only difference.) As consequences, **the reals are
uncountable in Part I's sense**, and the countable models of the Löwenheim–Skolem
theorem are countable in Part I's sense.

**Finiteness.** Part I (`Sets/Infinite.lean`) calls a type finite when it injects into
some `Fin n`; Part IV (`Algebra/Finite.lean`) instead *equips* a type with a census
`FiniteType`, a duplicate-free list of all its elements. A census yields an injection
(the position in the list) and conversely an injection into `Fin n` yields a census
(list the elements of `Fin n` that are hit, and replace each by its preimage). The
census size `card` is then the cardinal in Part I's sense: `card α = n` exactly when `α`
is equinumerous with `Fin n`, and `card α ≤ n` whenever `α` injects into `Fin n`.
-/

namespace Foundations.Bridges

open Foundations.Sets Foundations.Numbers

/-! ## Countability: injections into `ℕ` versus surjections from `ℕ` -/

/-- "Listed by the natural numbers": there is a surjection `ℕ → α`. This is the notion
of countability used in Part III's logic and Part II's `R.uncountable`. -/
def ListedByNat (α : Sort _) : Prop := ∃ f : Nat → α, ∀ x : α, ∃ n, f n = x

/-- A type listed by `ℕ` is countable in Part I's sense (`Sets/Cardinality.lean`):
tag each member by a chosen position at which it is listed. -/
theorem countable_of_listedByNat {α : Sort _} (h : ListedByNat α) : Countable α := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun x => Classical.choose (hf x), fun x y hxy => ?_⟩
  have hx := Classical.choose_spec (hf x)
  have hy := Classical.choose_spec (hf y)
  rw [← hx, ← hy]
  exact congrArg f hxy

/-- A nonempty type that is countable in Part I's sense (`Sets/Cardinality.lean`) is
listed by `ℕ`: send each used tag back to its member and every unused number to a fixed
default member. -/
theorem listedByNat_of_countable {α : Sort _} (hne : Nonempty α) (h : Countable α) :
    ListedByNat α := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨a₀⟩ := hne
  classical
  refine ⟨fun n => if hn : ∃ a, g a = n then Classical.choose hn else a₀, fun x => ⟨g x, ?_⟩⟩
  have hn : ∃ a, g a = g x := ⟨x, rfl⟩
  simp only [hn, ↓reduceDIte]
  exact hg (Classical.choose_spec hn)

/-- **Bridge: the two notions of countability agree on nonempty types.** For a
nonempty type, Part I's `Countable` (an injection into `ℕ`, `Sets/Cardinality.lean`) is
equivalent to the surjection-from-`ℕ` formulation used in `Logic/FOCompleteness.lean`,
`Logic/TermModel.lean`, `Logic/NonstandardArithmetic.lean` and
`Numbers/Uncountable.lean`. (Uses the axiom of choice.) -/
theorem countable_iff_listedByNat {α : Sort _} (hne : Nonempty α) :
    Countable α ↔ ∃ f : Nat → α, ∀ x : α, ∃ n, f n = x :=
  ⟨listedByNat_of_countable hne, countable_of_listedByNat⟩

/-- Without the nonemptiness hypothesis the two notions differ exactly at the empty
type: a type is countable (Part I) iff it is empty or listed by `ℕ`. -/
theorem countable_iff_empty_or_listedByNat {α : Sort _} :
    Countable α ↔ (¬ Nonempty α) ∨ ListedByNat α := by
  constructor
  · intro h
    by_cases hne : Nonempty α
    · exact Or.inr (listedByNat_of_countable hne h)
    · exact Or.inl hne
  · rintro (h | h)
    · exact ⟨fun x => absurd ⟨x⟩ h, fun x => absurd ⟨x⟩ h⟩
    · exact countable_of_listedByNat h

/-- **ℝ is uncountable in Part I's sense.** Part II's Cauchy reals `R` do not inject
into `ℕ`: the uncountability theorem `R.uncountable` of `Numbers/Uncountable.lean`
(no surjection `ℕ → R`) transported along `countable_iff_listedByNat` to Part I's
`Countable` of `Sets/Cardinality.lean`. -/
theorem reals_not_countable : ¬ Countable R := fun h =>
  R.uncountable ((countable_iff_listedByNat ⟨0⟩).1 h)

/-- **Löwenheim–Skolem with Part I's countability.** If a theory in a countable
language has a model, it has one whose domain is `Countable` in the sense of
`Sets/Cardinality.lean` — Part III's `lowenheim_skolem` (`Logic/FOCompleteness.lean`)
read through `countable_of_listedByNat`. -/
theorem lowenheim_skolem_countable {L : Foundations.Logic.FO.Signature}
    [Foundations.Logic.FO.Signature.Countable L] {Γ : Foundations.Logic.FO.Theory L}
    {M : Foundations.Logic.FO.Structure L} {e : Nat → M.Dom}
    (h : ∀ ψ, Γ ψ → Foundations.Logic.FO.Formula.Sat M e ψ) :
    ∃ (N : Foundations.Logic.FO.Structure L) (e' : Nat → N.Dom),
      (∀ ψ, Γ ψ → Foundations.Logic.FO.Formula.Sat N e' ψ) ∧ Countable N.Dom := by
  obtain ⟨N, e', hN, hc⟩ := Foundations.Logic.FO.lowenheim_skolem h
  exact ⟨N, e', hN, countable_of_listedByNat hc⟩

/-! ## Finiteness: injections into `Fin n` versus censuses -/

open Foundations.Algebra in
/-- **Bridge: a census makes a type finite.** A type with a `FiniteType` census
(`Algebra/Finite.lean`) is `IsFinite` in Part I's sense (`Sets/Infinite.lean`): the
position of an element in the census is an injection into `Fin (card α)`. -/
theorem isFinite_of_finiteType (α : Type _) [FiniteType α] : IsFinite α :=
  ⟨FiniteType.card α, FiniteType.toFin, fun x y h => by
    rw [← FiniteType.ofFin_toFin x, ← FiniteType.ofFin_toFin y, h]⟩

open Foundations.Algebra in
/-- The census of a type injecting into `Fin n`: run through `0, …, n − 1` and keep the
(chosen, hence unique) preimage of each number that is hit. Noncomputable, since
"is hit" is not decidable in general. -/
@[instance_reducible] noncomputable def finiteTypeOfInjective {α : Type _} {n : Nat} (f : α → Fin n)
    (hf : Function.Injective f) : FiniteType α := by
  classical
  let P : Fin n → Prop := fun i => ∃ a, f a = i
  let g : {i // P i} → α := fun i => Classical.choose i.2
  have hg : ∀ i, f (g i) = i.1 := fun i => Classical.choose_spec i.2
  exact
  { elems := (FiniteType.listSubtype P (List.finRange n)).map g
    nodup := by
      refine FiniteType.nodup_map_of_injective (fun i j hij => Subtype.ext ?_)
        (FiniteType.nodup_listSubtype P _ (List.nodup_finRange n))
      rw [← hg i, ← hg j, hij]
    complete := by
      intro x
      refine List.mem_map.2 ⟨⟨f x, x, rfl⟩, (FiniteType.mem_listSubtype P _ _).2
        (List.mem_finRange _), hf (hg _)⟩ }

open Foundations.Algebra in
/-- **Bridge: a finite type carries a census.** Conversely, a type that is
`IsFinite` in Part I's sense (`Sets/Infinite.lean`) can be equipped (noncomputably)
with a `FiniteType` census of Part IV (`Algebra/Finite.lean`). -/
theorem nonempty_finiteType_of_isFinite {α : Type _} (h : IsFinite α) :
    Nonempty (FiniteType α) :=
  let ⟨_, f, hf⟩ := h; ⟨finiteTypeOfInjective f hf⟩

open Foundations.Algebra in
/-- **The two notions of finiteness agree.** For `α : Type`, Part I's `IsFinite`
(`Sets/Infinite.lean`) holds iff `α` admits a census `FiniteType` of Part IV
(`Algebra/Finite.lean`). -/
theorem isFinite_iff_nonempty_finiteType (α : Type _) :
    IsFinite α ↔ Nonempty (FiniteType α) :=
  ⟨nonempty_finiteType_of_isFinite, fun ⟨_⟩ => isFinite_of_finiteType α⟩

open Foundations.Algebra in
/-- A census exhibits its type as equinumerous (Part I, `Sets/Cardinality.lean`) with
`Fin (card α)` (Part IV, `Algebra/Finite.lean`). -/
theorem equinum_fin_card (α : Type _) [FiniteType α] : Equinum α (Fin (FiniteType.card α)) :=
  ⟨FiniteType.toFin,
    fun x y h => by rw [← FiniteType.ofFin_toFin x, ← FiniteType.ofFin_toFin y, h],
    fun i => ⟨FiniteType.ofFin i, FiniteType.toFin_ofFin i⟩⟩

open Foundations.Algebra in
/-- An injection `α → β` between census-carrying types bounds the cardinalities. -/
theorem card_le_of_injective {α β : Type _} [FiniteType α] [FiniteType β] (f : α → β)
    (hf : Function.Injective f) : FiniteType.card α ≤ FiniteType.card β := by
  have h := FiniteType.length_le_card (α := β)
    (FiniteType.nodup_map_of_injective (fun a b h => hf h) (FiniteType.nodup (α := α)))
  simpa [FiniteType.card] using h

open Foundations.Algebra in
/-- **`card` is the size of any injective image.** If `α` (with a census,
`Algebra/Finite.lean`) injects into `Fin n` — i.e. witnesses Part I's `IsFinite`
(`Sets/Infinite.lean`) with bound `n` — then `card α ≤ n`; so `card α` is the least such
bound. -/
theorem card_le_of_injective_fin {α : Type _} [FiniteType α] {n : Nat} (f : α → Fin n)
    (hf : Function.Injective f) : FiniteType.card α ≤ n := by
  have := card_le_of_injective f hf
  rwa [FiniteType.card_fin] at this

open Foundations.Algebra in
/-- **Bridge: census size = Part I cardinal.** For a type with a census
(`Algebra/Finite.lean`), `card α = n` iff `α` is equinumerous with `Fin n` in the sense
of `Sets/Cardinality.lean`. -/
theorem card_eq_iff_equinum_fin (α : Type _) [FiniteType α] (n : Nat) :
    FiniteType.card α = n ↔ Equinum α (Fin n) := by
  constructor
  · rintro rfl; exact equinum_fin_card α
  · intro h
    obtain ⟨g, hg, _⟩ := Equinum.symm h
    obtain ⟨f, hf, _⟩ := h
    have h1 := card_le_of_injective_fin f hf
    have h2 := card_le_of_injective g hg
    rw [FiniteType.card_fin] at h2
    omega

end Foundations.Bridges
