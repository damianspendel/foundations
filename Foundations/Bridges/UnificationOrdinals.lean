import Foundations.Bridges.UnificationSize
import Foundations.Logic.Ordinals
import Foundations.Sets.Ordinals

/-!
# Unification III: ordinal notations are von Neumann ordinals

The project has two theories of ordinals that never met.

* Part III (`Logic/Ordinals.lean`) works *without sets*: an ordinal below ε₀ is a finite
  tree `ON` in Cantor normal form, `zero` or `oadd a b` read `ω^a + b`, compared by a
  purely combinatorial lexicographic order `lt`; Gentzen-style, the order is proved
  well-founded on normal notations (`NF`).
* Part I (`Sets/Ordinals.lean`) works *inside the ZF universe*: a von Neumann ordinal is a
  transitive set of transitive sets, ordered by membership `∈`; the naturals are
  `vn 0 = ∅`, `vn (n+1) = vn n ∪ {vn n}`.

We connect them by von Neumann's own recipe, *an ordinal is the set of the smaller
ordinals*: define, by well-founded recursion along Part III's well-ordering,

  `⟦x⟧ = { ⟦y⟧ : y normal, y < x }`.

The recursion is legitimate precisely because Part III proved the order well-founded
(`wellFounded_R`), and the set exists by Part I's family principle (`ofFamily`, indexed
by the type of smaller normal notations). We then prove:

* every `⟦x⟧` is a **von Neumann ordinal**;
* on normal notations the map is an **order-embedding**: `y < x ↔ ⟦y⟧ ∈ ⟦x⟧`, and it is
  **injective**;
* the **finite notations** `1 + 1 + ⋯ + 1` (i.e. `ω^0 + (ω^0 + ⋯)`) go exactly to the
  von Neumann naturals: `⟦n⟧ = vn n`;
* the notation `ω = ω^1 + 0` goes to the ZF set `ω` of `Sets/ZFSet.lean`.

So all of Part III's ordinals below ε₀ — not just those below `ω^ω` — live, with their
order, among Part I's ZF ordinals.
-/

namespace Foundations.Bridges

open Foundations.Sets Foundations.Sets.ZFSet Foundations.Logic.Ordinals

namespace OrdinalBridge

/-! ## The von Neumann interpretation of a notation -/

/-- **The von Neumann ordinal of a notation.** By well-founded recursion on Part III's
order (`Logic/Ordinals.lean`, `ON.wellFounded_R`), `toZF x` is the ZF set
(`Sets/ZFSet.lean`) of all `toZF y` for normal notations `y < x`. -/
noncomputable def toZF : ON → ZFSet :=
  ON.wellFounded_R.fix fun x rec => ofFamily fun y : {y : ON // ON.R y x} => rec y.1 y.2

/-- The defining equation of `toZF`. -/
theorem toZF_eq (x : ON) :
    toZF x = ofFamily fun y : {y : ON // ON.R y x} => toZF y.1 :=
  ON.wellFounded_R.fix_eq _ x

/-- **Members of `⟦x⟧`.** The members of `toZF x` are exactly the `toZF y` with `y` normal
and `y < x`. -/
theorem mem_toZF {x : ON} {z : ZFSet} :
    z ∈ toZF x ↔ ∃ y, ON.NF y ∧ ON.lt y x ∧ z = toZF y := by
  rw [toZF_eq, mem_ofFamily]
  constructor
  · rintro ⟨⟨y, hy, hlt⟩, rfl⟩; exact ⟨y, hy, hlt, rfl⟩
  · rintro ⟨y, hy, hlt, rfl⟩; exact ⟨⟨y, hy, hlt⟩, rfl⟩

/-- A smaller normal notation gives a member. -/
theorem toZF_mem_toZF {x y : ON} (hy : ON.NF y) (h : ON.lt y x) : toZF y ∈ toZF x :=
  mem_toZF.2 ⟨y, hy, h, rfl⟩

/-- `toZF x` is a transitive set. -/
theorem isTransitive_toZF (x : ON) : IsTransitive (toZF x) := by
  intro z hz w hw
  obtain ⟨y, _, hyx, rfl⟩ := mem_toZF.1 hz
  obtain ⟨v, hv, hvy, rfl⟩ := mem_toZF.1 hw
  exact toZF_mem_toZF hv (ON.lt_trans hvy hyx)

/-- **Every notation denotes a von Neumann ordinal.** For every Part III notation `x`
(`Logic/Ordinals.lean`), `toZF x` satisfies Part I's `IsOrdinal` (`Sets/Ordinals.lean`). -/
theorem isOrdinal_toZF (x : ON) : IsOrdinal (toZF x) :=
  ⟨isTransitive_toZF x, fun z hz => by
    obtain ⟨y, _, _, rfl⟩ := mem_toZF.1 hz
    exact isTransitive_toZF y⟩

/-! ## An order-embedding -/

/-- **The interpretation reflects the order.** For normal notations, `⟦y⟧ ∈ ⟦x⟧`
implies `y < x`. -/
theorem lt_of_toZF_mem {x y : ON} (hx : ON.NF x) (h : toZF y ∈ toZF x) :
    ON.lt y x := by
  rcases ON.lt_trichotomy y x with h' | rfl | h'
  · exact h'
  · exact absurd h (mem_irrefl _)
  · exact absurd (toZF_mem_toZF hx h') (mem_asymm h)

/-- **Bridge: ordinal notations embed into the von Neumann ordinals.** On normal
notations of Part III (`Logic/Ordinals.lean`), the combinatorial order coincides with
membership of the corresponding ZF ordinals of Part I (`Sets/Ordinals.lean`):
`y < x ↔ ⟦y⟧ ∈ ⟦x⟧`. -/
theorem lt_iff_toZF_mem {x y : ON} (hx : ON.NF x) (hy : ON.NF y) :
    ON.lt y x ↔ toZF y ∈ toZF x :=
  ⟨toZF_mem_toZF hy, lt_of_toZF_mem hx⟩

/-- **The interpretation is injective on normal notations.** Distinct normal
notations (`Logic/Ordinals.lean`) denote distinct ZF ordinals (`Sets/Ordinals.lean`). -/
theorem toZF_injective {x y : ON} (hx : ON.NF x) (hy : ON.NF y) (h : toZF x = toZF y) :
    x = y := by
  rcases ON.lt_trichotomy x y with h' | h' | h'
  · have := toZF_mem_toZF (x := y) hx h'; rw [h] at this; exact absurd this (mem_irrefl _)
  · exact h'
  · have := toZF_mem_toZF (x := x) hy h'; rw [h] at this; exact absurd this (mem_irrefl _)

/-- **The ordinals below ε₀ as a ZF order-embedding.** Summary bridge between
`Logic/Ordinals.lean` and `Sets/Ordinals.lean`: `toZF` sends every notation to a von
Neumann ordinal, and on normal notations it is injective and turns `lt` into `∈`. -/
theorem notations_embed_in_vonNeumann :
    (∀ x, IsOrdinal (toZF x)) ∧
    (∀ x y, ON.NF x → ON.NF y → toZF x = toZF y → x = y) ∧
    (∀ x y, ON.NF x → ON.NF y → (ON.lt y x ↔ toZF y ∈ toZF x)) :=
  ⟨isOrdinal_toZF, fun _ _ hx hy => toZF_injective hx hy, fun _ _ hx hy => lt_iff_toZF_mem hx hy⟩

/-! ## The finite notations and `ω` -/

/-- The finite notation `n = ω^0 + (ω^0 + ⋯ + 0)` (with `n` summands). -/
def ofNat : Nat → ON
  | 0 => ON.zero
  | n + 1 => ON.oadd ON.zero (ofNat n)

/-- Finite notations are in Cantor normal form. -/
theorem nf_ofNat : ∀ n, ON.NF (ofNat n)
  | 0 => ON.NF.zero
  | n + 1 => ON.NF.oadd ON.NF.zero (nf_ofNat n) (fun a' b' he h => by
      cases n with
      | zero => cases he
      | succ k => injection he with h1; subst h1; exact ON.lt_irrefl _ h)

/-- The notations below `ω^0 + b` are `0` and the `ω^0 + b'` with `b' < b` (no exponent
lies below `0`). -/
theorem lt_oadd_zero {y b : ON} :
    ON.lt y (ON.oadd ON.zero b) ↔ y = ON.zero ∨ ∃ b', y = ON.oadd ON.zero b' ∧ ON.lt b' b := by
  cases y with
  | zero => exact ⟨fun _ => Or.inl rfl, fun _ => ON.zero_lt_oadd _ _⟩
  | oadd a b' =>
    rw [ON.lt_oadd]
    constructor
    · rintro (h | ⟨rfl, h⟩)
      · exact absurd h (ON.not_lt_zero a)
      · exact Or.inr ⟨b', rfl, h⟩
    · rintro (h | ⟨b'', h, hlt⟩)
      · cases h
      · cases h; exact Or.inr ⟨rfl, hlt⟩

/-- The normal notations below the finite notation `n` are the finite notations `m < n`. -/
theorem nf_lt_ofNat {y : ON} : ∀ {n : Nat}, ON.NF y ∧ ON.lt y (ofNat n) ↔ ∃ m, m < n ∧ y = ofNat m
  | 0 => ⟨fun ⟨_, h⟩ => absurd h (ON.not_lt_zero _), fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    show ON.NF y ∧ ON.lt y (ON.oadd ON.zero (ofNat n)) ↔ _
    rw [lt_oadd_zero]
    constructor
    · rintro ⟨hy, rfl | ⟨b', rfl, hlt⟩⟩
      · exact ⟨0, by omega, rfl⟩
      · cases hy with
        | oadd _ hb' _ =>
          obtain ⟨m, hm, rfl⟩ := (nf_lt_ofNat (y := b')).1 ⟨hb', hlt⟩
          exact ⟨m + 1, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨nf_ofNat m, ?_⟩
      cases m with
      | zero => exact Or.inl rfl
      | succ m => exact Or.inr ⟨ofNat m, rfl, ((nf_lt_ofNat (y := ofNat m)).2 ⟨m, by omega, rfl⟩).2⟩

/-- **Bridge: finite notations are the von Neumann naturals.** The finite notation `n`
of `Logic/Ordinals.lean` denotes the von Neumann natural `vn n` of `Sets/ZFSet.lean`. -/
theorem toZF_ofNat : ∀ n, toZF (ofNat n) = vn n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    apply ZFSet.ext
    intro z
    rw [mem_toZF, mem_vn]
    constructor
    · rintro ⟨y, hy, hlt, rfl⟩
      obtain ⟨m, hm, rfl⟩ := nf_lt_ofNat.1 ⟨hy, hlt⟩
      exact ⟨m, hm, ih m hm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨ofNat m, nf_ofNat m, (nf_lt_ofNat.2 ⟨m, hm, rfl⟩).2, (ih m hm).symm⟩

/-- **The finite notations, ordered, are the von Neumann naturals, ordered.** For the
finite notations of `Logic/Ordinals.lean`, `m < n` as notations iff `vn m ∈ vn n`
(`Sets/Omega.lean`) iff `m < n` as natural numbers. -/
theorem ofNat_lt_iff (m n : Nat) :
    ON.lt (ofNat m) (ofNat n) ↔ vn m ∈ vn n ∧ m < n := by
  rw [lt_iff_toZF_mem (nf_ofNat n) (nf_ofNat m), toZF_ofNat, toZF_ofNat]
  exact ⟨fun h => ⟨h, vn_mem_vn_iff.1 h⟩, fun h => h.1⟩

/-- The notation `ω = ω^(ω^0 + 0) + 0`. -/
def omegaON : ON := ON.oadd (ofNat 1) ON.zero

/-- The normal notations below `ω` are the finite ones. -/
theorem nf_lt_omega {y : ON} : ON.NF y ∧ ON.lt y omegaON ↔ ∃ m, y = ofNat m := by
  constructor
  · rintro ⟨hy, hlt⟩
    cases y with
    | zero => exact ⟨0, rfl⟩
    | oadd a b =>
      rcases ON.lt_oadd.1 hlt with h | ⟨_, h⟩
      · -- the head exponent is below `1`, hence it is `0`
        have ha : a = ON.zero := by
          rcases lt_oadd_zero.1 h with rfl | ⟨b', _, hb'⟩
          · rfl
          · exact absurd hb' (ON.not_lt_zero _)
        subst ha
        -- a normal `ω^0 + c` has all exponents `0`, hence is finite (induction on `c`)
        have key : ∀ c, ON.NF (ON.oadd ON.zero c) → ∃ m, ON.oadd ON.zero c = ofNat m := by
          intro c
          induction c with
          | zero => intro _; exact ⟨1, rfl⟩
          | oadd a' c' _ ihc =>
            intro hc
            cases hc with
            | oadd _ hc' hcond =>
              have ha' : a' = ON.zero := by
                rcases ON.le_of_not_lt (hcond a' c' rfl) with h' | h'
                · exact h'
                · exact absurd h' (ON.not_lt_zero _)
              subst ha'
              obtain ⟨m, hm⟩ := ihc hc'
              exact ⟨m + 1, by rw [ofNat, ← hm]⟩
        exact key b hy
      · exact absurd h (ON.not_lt_zero _)
  · rintro ⟨m, rfl⟩
    refine ⟨nf_ofNat m, ?_⟩
    cases m with
    | zero => exact ON.zero_lt_oadd _ _
    | succ m => exact ON.lt_oadd.2 (Or.inl (ON.zero_lt_oadd _ _))

/-- **Bridge: the notation `ω` denotes the ZF set `ω`.** The first infinite ordinal of
`Logic/Ordinals.lean` is sent to the set `ω` of all von Neumann naturals
(`Sets/ZFSet.lean`). -/
theorem toZF_omega : toZF omegaON = ω := by
  apply ZFSet.ext
  intro z
  rw [mem_toZF, mem_omega]
  constructor
  · rintro ⟨y, hy, hlt, rfl⟩
    obtain ⟨m, rfl⟩ := nf_lt_omega.1 ⟨hy, hlt⟩
    exact ⟨m, toZF_ofNat m⟩
  · rintro ⟨m, rfl⟩
    exact ⟨ofNat m, nf_ofNat m, (nf_lt_omega.2 ⟨m, rfl⟩).2, (toZF_ofNat m).symm⟩

end OrdinalBridge

end Foundations.Bridges
