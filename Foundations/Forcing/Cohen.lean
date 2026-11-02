import Foundations.Forcing.RegularOpen
import Foundations.Sets.Cardinality
import Foundations.Sets.Choice

/-!
# Cohen forcing and the countable chain condition

To violate CH, Cohen adjoined `ℵ₂` new real numbers at once. A real is coded by a function
`ℕ → 2`, so `ℵ₂` reals form one function `I × ℕ → 2` with `|I| = ℵ₂`. A **Cohen condition** is a
*finite* piece of such a function: a finite partial function `p : J ⇀ Bool` (here
`J = I × ℕ`). `p` extends `q` if it agrees with `q` wherever `q` is defined. The **Cohen
algebra** is the regular-open algebra of this poset. Topologically it is the algebra of
regular open subsets of the Cantor space `2^J`, since conditions are exactly the basic
clopen sets. That identification is not formalised here: we *define* the Cohen algebra as
`RO (Cond J)`.

The decisive combinatorial property is the **countable chain condition (ccc)**: every
antichain is countable. In the forcing extension it guarantees that cardinals are not
collapsed, so the `ℵ₂` new reals really are `ℵ₂` many there. The usual proof goes through
the Δ-system lemma. We use a short induction on the size of the conditions instead:

> Let `A` be an antichain of conditions with at most `n + 1` points each, and fix `p₀ ∈ A`.
> Every other `q ∈ A` is incompatible with `p₀`, so `q` contradicts `p₀` at one of the
> finitely many points `j` of `p₀`'s domain. For a fixed `j`, erasing `j` from the
> conditions of `A` that contradict `p₀` at `j` is injective and gives an antichain of
> conditions with at most `n` points. By induction each of these finitely many families is
> countable, and so is `A`.

This works for an **arbitrary** index type `J`, of any size (`cond_ccc`). We then
transfer ccc to the regular-open algebra (`RO.ccc_of_poset`): every family of pairwise
disjoint non-zero elements of the Cohen algebra is countable (`cohen_ccc`).

Finally, using Zorn's lemma from `Sets/Choice`, we derive the form in which ccc is used in
practice: in a ccc algebra every supremum `⨆ᵢ bᵢ` is already the supremum of a countable
subfamily (`ccc_iSup_countable`).
-/

namespace Foundations.Forcing

open Foundations.Sets CBA ForcingNotion

/-! ### Countable unions of finitely many countable families -/

/-- The union of two countable families is countable. -/
theorem countable_or {α : Type} {P Q : α → Prop} (hP : Countable {x // P x})
    (hQ : Countable {x // Q x}) : Countable {x // P x ∨ Q x} := by
  classical
  obtain ⟨f, hf⟩ := hP
  obtain ⟨g, hg⟩ := hQ
  refine ⟨fun x => if h : P x.1 then 2 * f ⟨x.1, h⟩ else 2 * g ⟨x.1, x.2.resolve_left h⟩ + 1,
    fun x y hxy => ?_⟩
  by_cases hx : P x.1 <;> by_cases hy : P y.1 <;> simp only [hx, hy, dite_true, dite_false] at hxy
  · have := congrArg Subtype.val (hf (by omega : f ⟨x.1, hx⟩ = f ⟨y.1, hy⟩))
    exact Subtype.ext this
  · omega
  · omega
  · have := congrArg Subtype.val (hg (by omega : g ⟨x.1, _⟩ = g ⟨y.1, _⟩))
    exact Subtype.ext this

/-- A family is countable if it is covered by a finite list of countable families. -/
theorem countable_of_list_cover {α : Type} (P : α → Prop) (Qs : List (α → Prop))
    (hQ : ∀ Q ∈ Qs, Countable {x // Q x}) (hcov : ∀ x, P x → ∃ Q ∈ Qs, Q x) :
    Countable {x // P x} := by
  induction Qs generalizing P with
  | nil =>
    exact ⟨fun _ => 0, fun x _ _ => by obtain ⟨_, h, _⟩ := hcov x.1 x.2; cases h⟩
  | cons Q Qs ih =>
    have hR : Countable {x // P x ∧ ¬ Q x} :=
      ih _ (fun Q' h => hQ Q' (List.mem_cons_of_mem _ h)) fun x ⟨hx, hnq⟩ => by
        obtain ⟨Q', hQ', hx'⟩ := hcov x hx
        rcases List.mem_cons.1 hQ' with rfl | h
        · exact absurd hx' hnq
        · exact ⟨Q', h, hx'⟩
    obtain ⟨f, hf⟩ := countable_or (hQ Q (List.mem_cons_self ..)) hR
    refine ⟨fun x => f ⟨x.1, (Classical.em (Q x.1)).elim Or.inl fun h => Or.inr ⟨x.2, h⟩⟩,
      fun x y h => Subtype.ext ?_⟩
    exact congrArg (fun z : {x // Q x ∨ (P x ∧ ¬ Q x)} => z.1) (hf h)

/-! ### Cohen conditions -/

/-- **Cohen conditions** on an index type `J`: finite partial functions `J ⇀ Bool`. The
domain is finite in the sense that it is covered by some list. -/
structure Cond (J : Type) where
  /-- The partial function (`none` = undefined). -/
  f : J → Option Bool
  /-- The domain is finite. -/
  fin : ∃ l : List J, ∀ j, f j ≠ none → j ∈ l

namespace Cond

variable {J : Type}

/-- Conditions with the same values are equal. -/
theorem ext {p q : Cond J} (h : ∀ j, p.f j = q.f j) : p = q := by
  cases p; cases q; cases funext h; rfl

/-- `p ≤ q` (`p` extends `q`): `p` agrees with `q` wherever `q` is defined. -/
instance : ForcingNotion (Cond J) where
  le p q := ∀ j b, q.f j = some b → p.f j = some b
  refl _ _ _ h := h
  trans _ _ _ h₁ h₂ j b h := h₁ j b (h₂ j b h)

/-- The extension order, unfolded. -/
theorem le_def {p q : Cond J} : p ≤ q ↔ ∀ j b, q.f j = some b → p.f j = some b := Iff.rfl

/-- The union of two conditions, which is a condition extending both when they do not
conflict (the values of `p` take precedence). -/
def union (p q : Cond J) : Cond J where
  f j := match p.f j with
    | some b => some b
    | none => q.f j
  fin := by
    obtain ⟨l₁, h₁⟩ := p.fin
    obtain ⟨l₂, h₂⟩ := q.fin
    refine ⟨l₁ ++ l₂, fun j hj => List.mem_append.2 ?_⟩
    cases hp : p.f j with
    | some b => exact Or.inl (h₁ j (by rw [hp]; exact Option.some_ne_none b))
    | none => simp only [hp] at hj; exact Or.inr (h₂ j hj)

/-- **Compatibility of Cohen conditions.** Two conditions are compatible iff they never
assign different values to the same point. -/
theorem compatible_iff {p q : Cond J} :
    Compatible p q ↔ ∀ j b c, p.f j = some b → q.f j = some c → b = c := by
  constructor
  · rintro ⟨r, hrp, hrq⟩ j b c hb hc
    have := (hrp j b hb).symm.trans (hrq j c hc)
    exact Option.some.inj this
  · intro h
    refine ⟨union p q, fun j b hb => ?_, fun j c hc => ?_⟩
    · show (match p.f j with | some b => some b | none => q.f j) = some b
      rw [hb]
    · show (match p.f j with | some b => some b | none => q.f j) = some c
      cases hp : p.f j with
      | some b => rw [h j b c hp hc]
      | none => exact hc

/-- Erase a point from the domain of a condition. -/
def erase [DecidableEq J] (q : Cond J) (j : J) : Cond J where
  f k := if k = j then none else q.f k
  fin := by
    obtain ⟨l, hl⟩ := q.fin
    exact ⟨l, fun k hk => hl k (by by_cases h : k = j <;> simp_all)⟩

/-- A condition has **size at most `n`** if its domain is covered by a list of length `n`. -/
def SizeLE (q : Cond J) (n : Nat) : Prop := ∃ l : List J, l.length ≤ n ∧ ∀ j, q.f j ≠ none → j ∈ l

/-- Every condition has some finite size. -/
theorem exists_sizeLE (q : Cond J) : ∃ n, q.SizeLE n :=
  let ⟨l, hl⟩ := q.fin; ⟨l.length, l, Nat.le_refl _, hl⟩

/-- Erasing a point of the domain lowers the size by one. -/
theorem sizeLE_erase [DecidableEq J] {q : Cond J} {n : Nat} {j : J} (hq : q.SizeLE (n + 1))
    (hj : q.f j ≠ none) : (q.erase j).SizeLE n := by
  obtain ⟨l, hlen, hl⟩ := hq
  have hjl := hl j hj
  refine ⟨l.erase j, ?_, fun k hk => ?_⟩
  · have := List.length_erase_of_mem hjl; omega
  · have hkj : k ≠ j := fun h => hk (by simp [erase, h])
    have hk' : q.f k ≠ none := by simpa [erase, hkj] using hk
    exact (List.mem_erase_of_ne hkj).2 (hl k hk')

/-- The key induction: an antichain of conditions of size at most `n` is countable. -/
theorem antichain_countable_of_size (n : Nat) :
    ∀ A : Cond J → Prop, IsAntichain A → (∀ q, A q → q.SizeLE n) → Countable {q // A q} := by
  classical
  induction n with
  | zero =>
    -- all conditions of size `0` are the empty condition, so `A` has at most one element
    intro A _ hsize
    refine ⟨fun _ => 0, fun x y _ => Subtype.ext (ext fun j => ?_)⟩
    obtain ⟨l, hl, hl'⟩ := hsize x.1 x.2
    obtain ⟨l₂, hl₂, hl₂'⟩ := hsize y.1 y.2
    have e1 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    have e2 : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst e1; subst e2
    have h1 : x.1.f j = none := Classical.byContradiction fun h => by simpa using hl' j h
    have h2 : y.1.f j = none := Classical.byContradiction fun h => by simpa using hl₂' j h
    rw [h1, h2]
  | succ n ih =>
    intro A hA hsize
    by_cases hne : ¬ ∃ p₀, A p₀
    · exact ⟨fun _ => 0, fun x _ _ => absurd ⟨x.1, x.2⟩ hne⟩
    obtain ⟨p₀, hp₀⟩ := Classical.byContradiction fun h => hne h
    obtain ⟨l₀, hl₀⟩ := p₀.fin
    -- the members of `A` contradicting `p₀` at the point `j`
    let C : J → Cond J → Prop := fun j q =>
      A q ∧ ∃ b c, p₀.f j = some b ∧ q.f j = some c ∧ b ≠ c
    have hC : ∀ j, Countable {q // C j q} := by
      intro j
      let A' : Cond J → Prop := fun r => ∃ q, C j q ∧ r = q.erase j
      -- two members of `C j` agree at `j`
      have agree : ∀ q₁ q₂, C j q₁ → C j q₂ → q₁.f j = q₂.f j := by
        rintro q₁ q₂ ⟨_, b, c, hb, hc, hbc⟩ ⟨_, b', c', hb', hc', hbc'⟩
        rw [hb] at hb'; cases hb'
        rw [hc, hc']
        cases b <;> cases c <;> cases c' <;> simp_all
      have hinj : ∀ q₁ q₂, C j q₁ → C j q₂ → q₁.erase j = q₂.erase j → q₁ = q₂ := by
        intro q₁ q₂ h₁ h₂ he
        refine ext fun k => ?_
        by_cases hk : k = j
        · subst hk; exact agree _ _ h₁ h₂
        · have := congrArg (fun r : Cond J => r.f k) he
          simpa [erase, hk] using this
      have hA' : IsAntichain A' := by
        rintro _ _ ⟨q₁, h₁, rfl⟩ ⟨q₂, h₂, rfl⟩ hne hcomp
        have hq : q₁ ≠ q₂ := fun h => hne (h ▸ rfl)
        apply hA q₁ q₂ h₁.1 h₂.1 hq
        rw [compatible_iff] at hcomp ⊢
        intro k b c hb hc
        by_cases hk : k = j
        · subst hk; have := agree _ _ h₁ h₂; rw [hb, hc] at this; exact Option.some.inj this
        · exact hcomp k b c (by simp [erase, hk, hb]) (by simp [erase, hk, hc])
      have hsize' : ∀ r, A' r → r.SizeLE n := by
        rintro _ ⟨q, ⟨hq, b, c, _, hc, _⟩, rfl⟩
        exact sizeLE_erase (hsize q hq) (by rw [hc]; exact Option.some_ne_none c)
      obtain ⟨g, hg⟩ := ih A' hA' hsize'
      exact ⟨fun q => g ⟨q.1.erase j, q.1, q.2, rfl⟩, fun q₁ q₂ h =>
        Subtype.ext (hinj _ _ q₁.2 q₂.2 (congrArg Subtype.val (hg h)))⟩
    refine countable_of_list_cover A ((fun q => q = p₀) :: l₀.map C) ?_ ?_
    · intro Q hQ
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact ⟨fun _ => 0, fun x y _ => Subtype.ext (x.2.trans y.2.symm)⟩
      · obtain ⟨j, _, rfl⟩ := List.mem_map.1 hQ
        exact hC j
    · intro q hq
      by_cases hqp : q = p₀
      · exact ⟨_, List.mem_cons_self .., hqp⟩
      · have hinc := hA q p₀ hq hp₀ hqp
        rw [compatible_iff] at hinc
        simp only [Classical.not_forall] at hinc
        obtain ⟨j, c, b, hc, hb, hbc⟩ := hinc
        refine ⟨C j, List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, ?_, rfl⟩),
          hq, b, c, hb, hc, fun h => hbc h.symm⟩
        exact hl₀ j (by rw [hb]; exact Option.some_ne_none b)

/-- **Cohen forcing has the countable chain condition.** For an index type `J` of any
cardinality, every antichain of finite partial functions `J ⇀ Bool` is countable. -/
theorem cond_ccc (A : Cond J → Prop) (hA : IsAntichain A) : Countable {q // A q} := by
  -- split `A` by (a chosen bound on) size; each slice is countable by the induction
  let sz : Cond J → Nat := fun q => Classical.choose (exists_sizeLE q)
  have hsz : ∀ q : Cond J, q.SizeLE (sz q) := fun q => Classical.choose_spec (exists_sizeLE q)
  have hslice : ∀ n, Countable {q // A q ∧ sz q = n} := fun n =>
    antichain_countable_of_size n _ (fun p q hp hq => hA p q hp.1 hq.1)
      (fun (q : Cond J) (hq : A q ∧ sz q = n) => by rw [← hq.2]; exact hsz q)
  obtain ⟨f, hf⟩ := countable_sigma countable_nat hslice
  exact ⟨fun q => f ⟨sz q.1, q.1, q.2, rfl⟩, fun q₁ q₂ h => by
    have := hf h
    exact Subtype.ext (congrArg (fun x : (Σ n, {q // A q ∧ sz q = n}) => x.2.1) this)⟩

end Cond

/-! ### The chain condition for the regular-open algebra -/

namespace RO

variable {P : Type} [ForcingNotion P]

/-- A regular open set is non-zero iff it contains a condition. -/
theorem ne_bot_iff {U : RO P} : U ≠ ⊥ ↔ ∃ p, U.carrier p := by
  constructor
  · intro h
    exact Classical.byContradiction fun hn =>
      h (ext fun p => ⟨fun hp => hn ⟨p, hp⟩, fun hp => hp.elim⟩)
  · rintro ⟨p, hp⟩ rfl
    exact hp

/-- **Non-degeneracy.** If there is at least one condition, the regular-open algebra is
non-trivial: `⊤ ≠ ⊥`. -/
theorem top_ne_bot (p : P) : (⊤ : RO P) ≠ ⊥ := ne_bot_iff.2 ⟨p, trivial⟩

/-- Disjoint regular open sets share no condition. -/
theorem not_mem_of_inf_eq_bot {U V : RO P} (h : U ⊓ V = ⊥) (p : P) :
    ¬ (U.carrier p ∧ V.carrier p) := fun hp => by
  have : (U ⊓ V).carrier p = (⊥ : RO P).carrier p := congrArg (fun W : RO P => W.carrier p) h
  exact (this ▸ hp : (⊥ : RO P).carrier p)

/-- **ccc transfers from a poset to its regular-open algebra.** If every antichain of
conditions is countable, then every family of non-zero, pairwise disjoint regular open sets
is countable. Pick a condition in each set: distinct sets give incompatible conditions. -/
theorem ccc_of_poset (hP : ∀ A : P → Prop, IsAntichain A → Countable {p // A p})
    (S : RO P → Prop) (hne : ∀ U, S U → U ≠ ⊥)
    (hdisj : ∀ U V, S U → S V → U ≠ V → U ⊓ V = ⊥) : Countable {U // S U} := by
  let pick : {U // S U} → P := fun U => Classical.choose (ne_bot_iff.1 (hne U.1 U.2))
  have hpick : ∀ U : {U // S U}, U.1.carrier (pick U) := fun U => Classical.choose_spec (ne_bot_iff.1 (hne U.1 U.2))
  have hinj : ∀ U V : {U // S U}, pick U = pick V → U = V := by
    intro U V h
    exact Classical.byContradiction fun hUV =>
      not_mem_of_inf_eq_bot (hdisj U.1 V.1 U.2 V.2 fun e => hUV (Subtype.ext e)) (pick U)
        ⟨hpick U, h ▸ hpick V⟩
  let A : P → Prop := fun p => ∃ U, pick U = p
  have hA : IsAntichain A := by
    rintro _ _ ⟨U, rfl⟩ ⟨V, rfl⟩ hne' ⟨r, hrU, hrV⟩
    have hUV : U.1 ≠ V.1 := fun e => hne' (congrArg pick (Subtype.ext e))
    exact not_mem_of_inf_eq_bot (hdisj U.1 V.1 U.2 V.2 hUV) r
      ⟨U.1.down _ r hrU (hpick U), V.1.down _ r hrV (hpick V)⟩
  obtain ⟨g, hg⟩ := hP A hA
  exact ⟨fun U => g ⟨pick U, U, rfl⟩, fun U V h => hinj U V (congrArg Subtype.val (hg h))⟩

end RO

/-- **The Cohen algebra** for adding `I`-many Cohen reals: the regular-open algebra of finite
partial functions `I × ℕ ⇀ Bool`. (For the failure of CH one takes `|I| = ℵ₂`.) -/
abbrev Cohen (I : Type) : Type := RO (Cond (I × Nat))

/-- The empty Cohen condition. -/
def Cond.empty (J : Type) : Cond J := ⟨fun _ => none, ⟨[], fun _ h => absurd rfl h⟩⟩

/-- **The Cohen algebra is non-degenerate:** `⊤ ≠ ⊥`, since the empty condition lies in `⊤`.
Without this, statements of the form `⟦φ⟧ = ⊥` about the Cohen algebra would be vacuous. -/
theorem cohen_top_ne_bot (I : Type) : (⊤ : Cohen I) ≠ ⊥ := RO.top_ne_bot (Cond.empty _)

/-- **The Cohen algebra satisfies the countable chain condition.** For every index type `I`,
every family of non-zero, pairwise disjoint elements of the Cohen algebra is countable. -/
theorem cohen_ccc (I : Type) (S : Cohen I → Prop) (hne : ∀ U, S U → U ≠ ⊥)
    (hdisj : ∀ U V, S U → S V → U ≠ V → U ⊓ V = ⊥) : Countable {U // S U} :=
  RO.ccc_of_poset Cond.cond_ccc S hne hdisj

/-! ### Suprema in a ccc algebra are countable suprema -/

/-- A complete Boolean algebra satisfies the **countable chain condition** if every family of
non-zero, pairwise disjoint elements is countable. -/
def IsCCC (B : Type) [CompleteBooleanAlgebra B] : Prop :=
  ∀ S : B → Prop, (∀ a, S a → a ≠ ⊥) → (∀ a a', S a → S a' → a ≠ a' → a ⊓ a' = ⊥) →
    Countable {a // S a}

/-- The Cohen algebra is ccc. -/
theorem cohen_isCCC (I : Type) : IsCCC (Cohen I) := cohen_ccc I

/-- **Every supremum in a ccc algebra is a countable supremum.** If `B` is ccc, then for every
family `(bᵢ)_{i ∈ ι}` there is a countable subfamily with the same supremum.

Proof: by Zorn's lemma take a maximal family `M` of pairwise disjoint non-zero elements, each
below some `bᵢ`; it is countable by ccc. Choosing such an `i` for each member of `M` gives a
countable subfamily. If its supremum `T` were below `⨆ᵢ bᵢ` and different from it, some
`bᵢ ⊓ Tᶜ` would be non-zero and could be added to `M`.

This is the algebraic core of the standard proof that ccc forcing preserves cardinals: a
name for a function from `ω` into a ground-model set has, at each argument, only countably
many possible values. That set-theoretic consequence is **not** formalised here. -/
theorem ccc_iSup_countable {B : Type} [CompleteBooleanAlgebra B] (hB : IsCCC B)
    {ι : Type} (b : ι → B) :
    ∃ (J : Type) (j : J → ι), Countable J ∧ iSup b = iSup fun k => b (j k) := by
  -- good families: pairwise disjoint, non-zero, each member below some `bᵢ`
  let Good : (B → Prop) → Prop := fun A =>
    (∀ a, A a → a ≠ ⊥ ∧ ∃ i, a ≤ b i) ∧ (∀ a a', A a → A a' → a ≠ a' → a ⊓ a' = ⊥)
  let r : {A // Good A} → {A // Good A} → Prop := fun A A' => Zorn.Sub A.1 A'.1
  obtain ⟨M, hM⟩ := Zorn.zorn (r := r) (fun _ _ h => h) (fun _ _ _ h₁ h₂ => Zorn.Sub.trans h₁ h₂)
    (fun _ _ h₁ h₂ => Subtype.ext (Zorn.Sub.antisymm h₁ h₂)) (by
      intro c hc
      refine ⟨⟨fun a => ∃ A : {A // Good A}, c A ∧ A.1 a, ?_, ?_⟩, fun A hA a ha => ⟨A, hA, ha⟩⟩
      · rintro a ⟨A, _, ha⟩; exact A.2.1 a ha
      · rintro a a' ⟨A, hA, ha⟩ ⟨A', hA', ha'⟩ hne
        rcases hc A A' hA hA' with h | h
        · exact A'.2.2 a a' (h a ha) ha' hne
        · exact A.2.2 a a' ha (h a' ha') hne)
  let idx : {a // M.1 a} → ι := fun a => Classical.choose (M.2.1 a.1 a.2).2
  have hidx : ∀ a : {a // M.1 a}, a.1 ≤ b (idx a) := fun a =>
    Classical.choose_spec (M.2.1 a.1 a.2).2
  refine ⟨{a // M.1 a}, idx, hB M.1 (fun a h => (M.2.1 a h).1) M.2.2, ?_⟩
  apply le_antisymm' _ (iSup_le fun k => le_iSup b (idx k))
  let T := iSup fun k => b (idx k)
  apply le_of_inf_compl_le_bot
  -- suppose `d = (⨆ᵢ bᵢ) ⊓ Tᶜ ≠ ⊥`
  refine Classical.byContradiction fun hd => ?_
  have hdne : iSup b ⊓ Tᶜ ≠ ⊥ := fun h => hd (h ▸ le_rfl)
  -- some `bᵢ` meets `Tᶜ`
  have : ∃ i, b i ⊓ Tᶜ ≠ ⊥ := Classical.byContradiction fun hn => by
    apply hdne
    apply eq_bot_iff.2
    refine le_trans' iSup_inf_le (iSup_le fun i => ?_)
    exact eq_bot_iff.1 (Classical.byContradiction fun h => hn ⟨i, h⟩)
  obtain ⟨i, hi⟩ := this
  let c := b i ⊓ Tᶜ
  have hcT : ∀ a, M.1 a → a ⊓ c = ⊥ := fun a ha => eq_bot_iff.2 <|
    le_trans' (inf_le_inf (le_trans' (hidx ⟨a, ha⟩) (le_iSup (fun k => b (idx k)) ⟨a, ha⟩))
      (inf_le_right _ _)) inf_compl_le
  have hcM : ¬ M.1 c := fun h => hi (by have := hcT c h; rwa [inf_idem] at this)
  -- `M ∪ {c}` is good and strictly bigger
  let M' : {A // Good A} := ⟨fun a => M.1 a ∨ a = c, by
    refine ⟨?_, ?_⟩
    · rintro a (h | rfl)
      · exact M.2.1 a h
      · exact ⟨hi, i, inf_le_left _ _⟩
    · rintro a a' (h | rfl) (h' | rfl) hne
      · exact M.2.2 a a' h h' hne
      · exact hcT a h
      · rw [inf_comm]; exact hcT a' h'
      · exact absurd rfl hne⟩
  have := hM M' (fun a h => Or.inl h)
  have hc' : M'.1 c := Or.inr rfl
  rw [this] at hc'
  exact hcM hc'

/-- **Suprema in the Cohen algebra are countable suprema.** -/
theorem cohen_iSup_countable (I : Type) {ι : Type} (b : ι → Cohen I) :
    ∃ (J : Type) (j : J → ι), Countable J ∧ iSup b = iSup fun k => b (j k) :=
  ccc_iSup_countable (cohen_isCCC I) b

end Foundations.Forcing
