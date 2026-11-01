import Foundations.Forcing.Cohen
import Foundations.Forcing.BSetZF

/-!
# Cohen reals in the Boolean-valued universe

We now combine the two halves: the Boolean-valued universe `V^B` and the Cohen algebra
`B = Cohen I`. For each index `α ∈ I` there is a canonical name `ċ_α` for the `α`-th
**Cohen real**, the subset of `ω` whose characteristic function is the `α`-th row of the
generic function `I × ℕ → 2`:

`ċ_α = {(ň, ⟦the generic function takes value 1 at (α, n)⟧) | n ∈ ℕ}`,

where `ň` is the canonical name of the natural number `n` and the truth value is the
regular open set of conditions `p` with `p(α, n) = 1`.

The theorems of this file are the first genuinely *forcing-theoretic* facts proved here.
Each rests on a **density argument**: any condition can be extended to decide a fresh
coordinate either way.

* `creal_subset_omega`: `⟦ċ_α ⊆ ω̌⟧ = ⊤`, so each `ċ_α` is a set of natural numbers, i.e. a
  real.
* `creal_ne`: `⟦ċ_α = ċ_β⟧ = ⊥` for `α ≠ β`. The Cohen reals are pairwise distinct with
  Boolean value `⊤`. This is an external statement, one for each pair `α ≠ β`; the
  internal statement "`α ↦ ċ_α` is an injection `Ǐ → 𝒫(ω̌)` in `V^B`" is not formalised.
* `creal_ne_ground`: `⟦ċ_α = ǎ⟧ = ⊥` for every ground-model set `a ⊆ ℕ`. The Cohen reals
  are **new**: none of them was already in the ground model.

What these facts do *not* yet give is `V^B ⊨ ¬CH`. For that one must also show that `ℵ₂`
of the ground model is still `ℵ₂` in `V^B`. That is where the countable chain condition
(`cohen_ccc`) enters: ccc forcing preserves cofinalities and hence cardinals. One would then
take `|I| = ℵ₂`. These steps are not formalised here.
-/

namespace Foundations.Forcing

open Foundations.Logic.FO CBA BStructure ForcingNotion

attribute [local instance] Classical.propDecidable

/-! ### Names for natural numbers -/


/-! ### Atoms of the Cohen algebra and extension of conditions -/

namespace Cond

variable {J : Type}

/-- Extend a condition by one new value. -/
noncomputable def extend (p : Cond J) (j : J) (c : Bool) : Cond J where
  f k := if k = j then (match p.f j with | some b => some b | none => some c) else p.f k
  fin := by
    obtain ⟨l, hl⟩ := p.fin
    exact ⟨j :: l, fun k hk => by
      by_cases h : k = j
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hl k (by simpa [h] using hk))⟩

/-- An extension extends. -/
theorem extend_le (p : Cond J) (j : J) (c : Bool) : p.extend j c ≤ p := by
  intro k b hk
  show (if k = j then _ else _) = _
  by_cases h : k = j
  · subst h; simp [hk]
  · simp [h, hk]

/-- At a fresh point, the extension takes the prescribed value. -/
theorem extend_at {p : Cond J} {j : J} (c : Bool) (h : p.f j = none) :
    (p.extend j c).f j = some c := by
  show (if j = j then _ else _) = _
  simp [h]

/-- Away from the new point, the extension agrees with the original condition. -/
theorem extend_off (p : Cond J) {j k : J} (c : Bool) (h : k ≠ j) :
    (p.extend j c).f k = p.f k := by
  show (if k = j then _ else _) = _
  simp [h]

/-- Every element of a list of naturals is at most its sum. -/
theorem le_sum_of_mem {n : Nat} : ∀ {L : List Nat}, n ∈ L → n ≤ L.sum
  | _ :: L, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp
      · have := le_sum_of_mem h; simp; omega

/-- **Fresh coordinates.** For every condition `p` on `I × ℕ` and rows `α`, `β` there is a
coordinate `n` with `p(α, n)` and `p(β, n)` both undefined. -/
theorem exists_fresh {I : Type} (p : Cond (I × Nat)) (α β : I) :
    ∃ n, p.f (α, n) = none ∧ p.f (β, n) = none := by
  obtain ⟨l, hl⟩ := p.fin
  refine ⟨(l.map Prod.snd).sum + 1, ?_, ?_⟩ <;>
  · refine Classical.byContradiction fun h => ?_
    have hm := le_sum_of_mem (List.mem_map_of_mem (f := Prod.snd) (hl _ h))
    simp only at hm; omega

end Cond

/-- The **atom** `⟦the generic function has value c at j⟧`, i.e. the conditions `p` with
`p(j) = c`. It is regular open. -/
def atom {J : Type} (j : J) (c : Bool) : RO (Cond J) where
  carrier p := p.f j = some c
  down _ _ h hp := h _ _ hp
  reg p h := by
    cases hp : p.f j with
    | some b =>
      obtain ⟨r, hr, hrc⟩ := h p (ForcingNotion.refl p)
      have := (hr j b hp).symm.trans hrc
      rw [Option.some.inj this]
    | none =>
      obtain ⟨r, hr, hrc⟩ := h (p.extend j (!c)) (Cond.extend_le p j _)
      have := (hr j _ (Cond.extend_at _ hp)).symm.trans hrc
      cases c <;> simp at this

/-- A condition with value `c'` at `j`, where `c' ≠ c`, lies outside the atom
`⟦value c at j⟧` (and so do all its extensions). -/
theorem not_mem_atom {J : Type} {p : Cond J} {j : J} {c c' : Bool} (hp : p.f j = some c')
    (hc : c' ≠ c) : ¬ (atom j c).carrier p := fun h => by
  have := hp.symm.trans h; exact hc (Option.some.inj this)

/-! ### The Cohen reals -/

variable {I : Type}

/-- **The `α`-th Cohen real** `ċ_α = {(ň, ⟦value 1 at (α, n)⟧) | n ∈ ℕ}`. -/
def creal (α : I) : BSet (Cohen I) := .mk Nat natB (fun n => atom (α, n) true)

/-- `⟦ň ∈ ċ_α⟧` is the atom `⟦value 1 at (α, n)⟧`. -/
theorem mem_creal (α : I) (n : Nat) : BSet.mem (natB n) (creal α) = atom (α, n) true :=
  mem_natB_family _ n

/-- **Each Cohen real is a set of natural numbers.** `⟦ċ_α ⊆ ω̌⟧ = ⊤`. -/
theorem creal_subset_omega (α : I) :
    iInf (fun z => BSet.mem z (creal α) ⇨ BSet.mem z omegaB) = ⊤ :=
  eq_top_iff.2 <| le_iInf fun _ => le_himp_iff.2 <| inf_le_of_right_le <|
    iSup_mono fun _ => inf_le_inf le_top' le_rfl

/-- In the regular-open algebra, `X ≤ ⊥` as soon as `X` contains no condition. -/
theorem RO.le_bot_of_empty {P : Type} [ForcingNotion P] {X : RO P}
    (h : ∀ p, X.carrier p → False) : X ≤ ⊥ := fun p hp => h p hp

/-- **Distinct Cohen reals are distinct.** For `α ≠ β`, `⟦ċ_α = ċ_β⟧ = ⊥`. Density
argument: below any condition `p`, choose a coordinate `n` on which `p` says nothing about
rows `α` and `β`, and extend `p` to put `n` into `ċ_α` but not into `ċ_β`. -/
theorem creal_ne {α β : I} (hαβ : α ≠ β) : BSet.eq (creal α) (creal β) = ⊥ := by
  apply eq_bot_iff.2
  apply RO.le_bot_of_empty
  intro p hp
  obtain ⟨n, hα, hβ⟩ := Cond.exists_fresh p α β
  have hne : (β, n) ≠ (α, n) := fun h => hαβ (congrArg Prod.fst h).symm
  let q := (p.extend (α, n) true).extend (β, n) false
  have hqp : q ≤ p := ForcingNotion.trans _ _ _ (Cond.extend_le _ _ _) (Cond.extend_le _ _ _)
  have hqα : q.f (α, n) = some true := by
    show ((p.extend (α, n) true).extend (β, n) false).f (α, n) = _
    rw [Cond.extend_off _ _ hne.symm, Cond.extend_at _ hα]
  have hqβ : q.f (β, n) = some false :=
    Cond.extend_at _ (by rw [Cond.extend_off _ _ hne]; exact hβ)
  -- `⟦ċ_α = ċ_β⟧ ⊓ ⟦ň ∈ ċ_α⟧ ≤ ⟦ň ∈ ċ_β⟧`
  have hcong := BSet.mem_congr_right (natB n) (creal α) (creal β)
  rw [mem_creal, mem_creal] at hcong
  exact not_mem_atom hqβ (by decide) (hcong q ⟨(BSet.eq (creal α) (creal β)).down p q hqp hp, hqα⟩)

/-- **Cohen reals are new.** For every ground-model set `a ⊆ ℕ`, `⟦ċ_α = ǎ⟧ = ⊥`: the generic
real differs from every real of the ground model. -/
theorem creal_ne_ground (α : I) (a : Nat → Prop) : BSet.eq (creal α) (subsetB a) = ⊥ := by
  apply eq_bot_iff.2
  apply RO.le_bot_of_empty
  intro p hp
  obtain ⟨n, hα, -⟩ := Cond.exists_fresh p α α
  by_cases ha : a n
  · -- extend so that `n ∉ ċ_α`; but `n ∈ ǎ`
    let q := p.extend (α, n) false
    have hq : q.f (α, n) = some false := Cond.extend_at _ hα
    have hcong := BSet.mem_congr_right (natB n) (subsetB a) (creal α)
    rw [mem_creal, mem_subsetB_of_mem ha, inf_top, BSet.eq_comm] at hcong
    exact not_mem_atom hq (by decide)
      (hcong q ((BSet.eq (creal α) (subsetB a)).down p q (Cond.extend_le _ _ _) hp))
  · -- extend so that `n ∈ ċ_α`; but `n ∉ ǎ`
    let q := p.extend (α, n) true
    have hq : q.f (α, n) = some true := Cond.extend_at _ hα
    have hcong := BSet.mem_congr_right (natB n) (creal α) (subsetB a)
    rw [mem_creal, mem_subsetB_of_not_mem ha] at hcong
    exact hcong q ⟨(BSet.eq (creal α) (subsetB a)).down p q (Cond.extend_le _ _ _) hp, hq⟩

/-! ### The same facts as truth values of first-order formulas -/

/-- The formula `x ≠ y` (with `x = var 0`, `y = var 1`). -/
def neqF : Formula LSet := Formula.neg (.eq (v 0) (v 1))

/-- **`V^{Cohen I}` ⊨ ċ_α ≠ ċ_β.** For `α ≠ β`, the first-order formula `x ≠ y`, evaluated at
`x = ċ_α`, `y = ċ_β`, has truth value `⊤` in the Boolean-valued universe over the Cohen
algebra. -/
theorem VB_creal_ne {α β : I} (hαβ : α ≠ β) (e : Nat → BSet (Cohen I)) :
    (VB (Cohen I)).val (BEnv.cons (creal α) (BEnv.cons (creal β) e)) neqF = ⊤ := by
  show BSet.eq (creal α) (creal β) ⇨ ⊥ = ⊤
  rw [creal_ne hαβ, himp_eq_top_iff]; exact le_rfl

/-- **`V^{Cohen I}` ⊨ ċ_α ≠ ǎ** for every ground-model `a ⊆ ℕ`. -/
theorem VB_creal_ne_ground (α : I) (a : Nat → Prop) (e : Nat → BSet (Cohen I)) :
    (VB (Cohen I)).val (BEnv.cons (creal α) (BEnv.cons (subsetB a) e)) neqF = ⊤ := by
  show BSet.eq (creal α) (subsetB a) ⇨ ⊥ = ⊤
  rw [creal_ne_ground α a, himp_eq_top_iff]; exact le_rfl

end Foundations.Forcing
