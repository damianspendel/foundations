import Foundations.Forcing.NotCH

/-!
# The Lévy collapse of the continuum onto `ω₁`: the forcing poset

`NotCH` showed that ZF does not prove CH. The other half of the independence of CH is that
ZF does not refute it either. **Gödel (1938)** proved this by building, inside any model of
ZF, the constructible universe `L`, in which CH holds. Formalising `L` would need the whole
theory of definability inside set theory. Here we take the forcing route instead. Forcing
can make CH *true* as easily as false: **collapse** the continuum onto `ω₁`.

This idea goes back to **Lévy (1963)**, whose collapsing posets make a given cardinal
countable or of size `ℵ₁`. The poset used here is the version that collapses `2^ℵ₀` onto
`ℵ₁`:

> a condition is a **countable** partial function `p : ω₁ ⇀ 𝒫(ℕ)`, and `p ≤ q` when `p`
> extends `q`.

The generic object is a function from `ω₁` onto the ground-model reals. Its decisive property
is **σ-closure**: every descending sequence `p₀ ≥ p₁ ≥ p₂ ≥ …` has a lower bound, namely the
union (`sigma_closed`). This is the exact opposite of the countable chain condition of Cohen
forcing. ccc forcing preserves cardinals but adds many reals. σ-closed forcing adds **no new
countable sequences**, so no new reals and no new countable sets of ordinals, while it may
collapse cardinals above `ℵ₁`.

This file sets up:

* `Omega1Like I`: the properties of `ω₁` that are used (a well-order, all of whose initial
  segments are countable, which is itself uncountable), with the instance for the ground
  `ω₁ = W₁` of `CardinalPreservation` (`instOmega1LikeW₁`), and the regularity fact that
  countable subsets are bounded (`Omega1Like.exists_bound`);
* the conditions `CCond I` and their extension order, the existence of fresh points
  (`CCond.exists_fresh`), one-point extensions, and **σ-closure** (`CCond.sigma_closed`);
* the collapse algebra `Col I = RO (CCond I)`, its non-degeneracy (`col_top_ne_bot`) and
  small helpers for computing in regular-open algebras;
* the atoms `⟦g(ξ) = a⟧` of the generic function, which are pairwise disjoint in `a`
  (`catom_disj`) and dense in `ξ` (`top_le_iSup_catom`): every ground real is a value of `g`;
* the **deciding lemma** `decide_countable`, the Boolean-valued form of "σ-closed forcing adds
  no new countable sequences": below any condition, countably many questions, each of which
  has an answer with value `⊤`, are all answered by a single condition.
-/

namespace Foundations.Forcing

open Foundations.Sets CBA ForcingNotion

attribute [local instance] Classical.propDecidable

/-! ### `ω₁`-like orders -/

/-- **ω₁-like order.** A strict well-order (well-founded, transitive, trichotomous) all of
whose proper initial segments are countable, while the whole type is uncountable. These are
exactly the properties of `ω₁` used for the collapse. -/
class Omega1Like (I : Type) extends LT I where
  /-- The order is well-founded. -/
  wf : WellFounded (fun a b : I => a < b)
  /-- The order is transitive. -/
  lt_trans : ∀ a b c : I, a < b → b < c → a < c
  /-- The order is total. -/
  tri : ∀ a b : I, a < b ∨ a = b ∨ b < a
  /-- Every proper initial segment is countable. -/
  seg : ∀ γ : I, Countable {ξ // ξ < γ}
  /-- The order itself is uncountable. -/
  uncountable : ¬ Countable I

namespace Omega1Like

variable {I : Type} [Omega1Like I]

/-- The order is irreflexive. -/
theorem lt_irrefl (a : I) : ¬ a < a := fun h =>
  (Omega1Like.wf.apply a).rec (motive := fun x _ => ¬ x < x) (fun x _ ih hx => ih x hx hx) h

/-- Every element is below some element of `I`, or equal: the closed initial segment
`{η | η < ζ ∨ η = ζ}` is countable. -/
theorem seg_le (ζ : I) : Countable {η // η < ζ ∨ η = ζ} := by
  obtain ⟨g, hg⟩ := Omega1Like.seg ζ
  refine ⟨fun η => if h : η.1 < ζ then g ⟨η.1, h⟩ + 1 else 0, fun η η' e => ?_⟩
  by_cases h : η.1 < ζ <;> by_cases h' : η'.1 < ζ <;> simp only [h, h', dite_true, dite_false] at e
  · have e' : g ⟨η.1, h⟩ = g ⟨η'.1, h'⟩ := by omega
    have := congrArg Subtype.val (hg e')
    exact Subtype.ext this
  · omega
  · omega
  · exact Subtype.ext ((η.2.resolve_left h).trans (η'.2.resolve_left h').symm)

/-- **Countable subsets of an ω₁-like order are bounded** (`ω₁` is regular). For every
countable family `ζ : K → I` there is `γ` above all `ζ k`. A countable union of countable
initial segments cannot exhaust the uncountable `I`. -/
theorem exists_bound {K : Type} (hK : Countable K) (ζ : K → I) : ∃ γ, ∀ k, ζ k < γ := by
  have hT : Countable {η : I // ∃ k, η < ζ k ∨ η = ζ k} := by
    obtain ⟨f, hf⟩ := countable_sigma hK fun k => seg_le (ζ k)
    refine ⟨fun η => f ⟨Classical.choose η.2, η.1, Classical.choose_spec η.2⟩, fun η η' e => ?_⟩
    have := hf e
    exact Subtype.ext (congrArg (fun x : (Σ k, {η // η < ζ k ∨ η = ζ k}) => x.2.1) this)
  have : ∃ γ, ¬ ∃ k, γ < ζ k ∨ γ = ζ k := Classical.byContradiction fun h => by
    apply Omega1Like.uncountable (I := I)
    obtain ⟨f, hf⟩ := hT
    refine ⟨fun η => f ⟨η, Classical.byContradiction fun hn => h ⟨η, hn⟩⟩, fun η η' e => ?_⟩
    exact congrArg Subtype.val (hf e)
  obtain ⟨γ, hγ⟩ := this
  refine ⟨γ, fun k => ?_⟩
  rcases Omega1Like.tri (ζ k) γ with h | h | h
  · exact h
  · exact absurd ⟨k, Or.inr h.symm⟩ hγ
  · exact absurd ⟨k, Or.inl h⟩ hγ

end Omega1Like

/-- The order of the ground `ω₁`: `ξ < η` iff `ξ ∈ η` as ordinals. -/
instance : LT W₁ := ⟨fun ξ η => ξ.val ∈ η.val⟩

/-- **The ground `ω₁` is ω₁-like.** The members of the Hartogs ordinal `ℵ(ℕ)`, ordered by
membership, form an uncountable well-order with countable initial segments. -/
instance instOmega1LikeW₁ : Omega1Like W₁ where
  wf := by
    have key : ∀ z : ZFSet, ∀ ξ : W₁, ξ.val = z → Acc (fun a b : W₁ => a < b) ξ := by
      refine ZFSet.mem_induction _ (fun z ih ξ hξ => ⟨_, fun η hη => ?_⟩)
      have : η.val ∈ z := hξ ▸ hη
      exact ih η.val this η rfl
    exact ⟨fun ξ => key ξ.val ξ rfl⟩
  lt_trans a b c hab hbc :=
    ((ZFSet.hartogs_isOrdinal Nat).mem c.val_mem).mem_trans hab hbc
  tri a b := by
    rcases ZFSet.ordinal_trichotomy ((ZFSet.hartogs_isOrdinal Nat).mem a.val_mem)
      ((ZFSet.hartogs_isOrdinal Nat).mem b.val_mem) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Small.val_injective h))
    · exact Or.inr (Or.inr h)
  seg γ := by
    obtain ⟨f, hf⟩ := (ZFSet.mem_hartogs_iff ((ZFSet.hartogs_isOrdinal Nat).mem γ.val_mem)).1
      γ.val_mem
    refine ⟨fun ξ => f ⟨ξ.1.val, ξ.2⟩, fun ξ ξ' e => ?_⟩
    have := congrArg Subtype.val (hf e)
    exact Subtype.ext (Small.val_injective this)
  uncountable := fun ⟨g, hg⟩ =>
    W₁_not_inj ⟨fun ξ => (g ξ, 0), fun ξ ξ' e => hg (congrArg Prod.fst e)⟩

/-! ### Collapse conditions -/

/-- **Collapse conditions.** Countable partial functions from `I` (think `ω₁`) to the
ground-model reals `ℕ → Prop`. -/
structure CCond (I : Type) where
  /-- The partial function (`none` = undefined). -/
  f : I → Option (Nat → Prop)
  /-- The domain is countable. -/
  dom_countable : Countable {ξ // f ξ ≠ none}

namespace CCond

variable {I : Type}

/-- `p ≤ q` (`p` extends `q`): `p` agrees with `q` wherever `q` is defined. -/
instance : ForcingNotion (CCond I) where
  le p q := ∀ ξ a, q.f ξ = some a → p.f ξ = some a
  refl _ _ _ h := h
  trans _ _ _ h₁ h₂ ξ a h := h₁ ξ a (h₂ ξ a h)

/-- The extension order, unfolded. -/
theorem le_def {p q : CCond I} : p ≤ q ↔ ∀ ξ a, q.f ξ = some a → p.f ξ = some a := Iff.rfl

/-- The empty condition. -/
def empty (I : Type) : CCond I := ⟨fun _ => none, ⟨fun _ => 0, fun ξ _ _ => absurd rfl ξ.2⟩⟩

/-- Extend a condition at a point where it is undefined (if it is defined there, nothing
changes). -/
noncomputable def extend (p : CCond I) (ξ : I) (a : Nat → Prop) : CCond I where
  f η := if η = ξ ∧ p.f ξ = none then some a else p.f η
  dom_countable := by
    obtain ⟨g, hg⟩ := p.dom_countable
    refine ⟨fun η => if h : η.1 = ξ then 0 else g ⟨η.1, fun e => η.2 (by simp [h, e])⟩ + 1,
      fun η η' e => ?_⟩
    by_cases h : η.1 = ξ <;> by_cases h' : η'.1 = ξ <;>
      simp only [h, h', dite_true, dite_false] at e
    · exact Subtype.ext (h.trans h'.symm)
    · omega
    · omega
    · have e' : g ⟨η.1, fun e => η.2 (by simp [h, e])⟩ = g ⟨η'.1, fun e => η'.2 (by simp [h', e])⟩ := by
        omega
      have := congrArg Subtype.val (hg e')
      exact Subtype.ext this

/-- An extension extends. -/
theorem extend_le (p : CCond I) (ξ : I) (a : Nat → Prop) : p.extend ξ a ≤ p := by
  intro η b hη
  show (if η = ξ ∧ p.f ξ = none then some a else p.f η) = some b
  have : ¬ (η = ξ ∧ p.f ξ = none) := fun ⟨e, hn⟩ => by subst e; rw [hη] at hn; cases hn
  simp only [this, ite_false, hη]

/-- At a fresh point the extension takes the prescribed value. -/
theorem extend_at {p : CCond I} {ξ : I} (a : Nat → Prop) (h : p.f ξ = none) :
    (p.extend ξ a).f ξ = some a := by
  show (if ξ = ξ ∧ p.f ξ = none then some a else p.f ξ) = some a
  simp [h]

/-- **Fresh points.** Every condition is undefined somewhere: its domain is countable and
`I` is not. -/
theorem exists_fresh [Omega1Like I] (p : CCond I) : ∃ ξ, p.f ξ = none :=
  Classical.byContradiction fun h => Omega1Like.uncountable (I := I) <| by
    obtain ⟨g, hg⟩ := p.dom_countable
    exact ⟨fun ξ => g ⟨ξ, fun e => h ⟨ξ, e⟩⟩, fun ξ ξ' e => congrArg Subtype.val (hg e)⟩

/-- Along a descending sequence, later conditions extend earlier ones. -/
theorem chain_anti (s : Nat → CCond I) (hs : ∀ n, s (n + 1) ≤ s n) (n : Nat) :
    ∀ k, s (n + k) ≤ s n
  | 0 => ForcingNotion.refl _
  | k + 1 => ForcingNotion.trans _ _ _ (hs (n + k)) (chain_anti s hs n k)

/-- **σ-closure.** Every descending sequence of collapse conditions has a lower bound, the
union of the sequence. Its domain is a countable union of countable sets. -/
theorem sigma_closed (s : Nat → CCond I) (hs : ∀ n, s (n + 1) ≤ s n) :
    ∃ r : CCond I, ∀ n, r ≤ s n := by
  -- two members of the chain agree wherever both are defined
  have agree : ∀ n m ξ a b, (s n).f ξ = some a → (s m).f ξ = some b → a = b := by
    intro n m ξ a b ha hb
    have h1 := chain_anti s hs n m ξ a ha
    have h2 := chain_anti s hs m n ξ b hb
    rw [Nat.add_comm] at h2
    exact Option.some.inj (h1.symm.trans h2)
  let F : I → Option (Nat → Prop) := fun ξ =>
    if h : ∃ n, (s n).f ξ ≠ none then (s (Classical.choose h)).f ξ else none
  have hF : ∀ ξ (h : ∃ n, (s n).f ξ ≠ none), F ξ = (s (Classical.choose h)).f ξ :=
    fun ξ h => by simp only [F, h, dite_true]
  have hdom : ∀ ξ, F ξ ≠ none → ∃ n, (s n).f ξ ≠ none := fun ξ hξ =>
    Classical.byContradiction fun h => hξ (by simp only [F, h, dite_false])
  refine ⟨⟨F, ?_⟩, fun n ξ a ha => ?_⟩
  · obtain ⟨g, hg⟩ := countable_sigma countable_nat fun n => (s n).dom_countable
    refine ⟨fun ξ => g ⟨Classical.choose (hdom ξ.1 ξ.2), ξ.1,
      Classical.choose_spec (hdom ξ.1 ξ.2)⟩, fun ξ ξ' e => ?_⟩
    have := hg e
    exact Subtype.ext (congrArg (fun x : (Σ n, {ξ // (s n).f ξ ≠ none}) => x.2.1) this)
  · have h : ∃ n, (s n).f ξ ≠ none := ⟨n, by rw [ha]; exact Option.some_ne_none a⟩
    show F ξ = some a
    rw [hF ξ h]
    have hs' := Classical.choose_spec h
    cases hb : (s (Classical.choose h)).f ξ with
    | none => exact absurd hb hs'
    | some b => rw [agree _ _ ξ b a hb ha]

end CCond

/-! ### Helpers for regular-open algebras -/

namespace RO

variable {P : Type} [ForcingNotion P]

/-- Membership in a join: `p ∈ ⨆ᵢ Uᵢ` iff below every extension of `p` some condition lies in
some `Uᵢ`. -/
theorem mem_iSup_iff {ι : Sort _} (f : ι → RO P) (p : P) :
    (iSup f).carrier p ↔ ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (f i).carrier r := by
  constructor
  · intro h q hq
    obtain ⟨r, hr, U, ⟨i, rfl⟩, hU⟩ := h q hq
    exact ⟨r, hr, i, hU⟩
  · intro h q hq
    obtain ⟨r, hr, i, hi⟩ := h q hq
    exact ⟨r, hr, f i, ⟨i, rfl⟩, hi⟩

/-- Membership in a meet: `p ∈ ⨅ᵢ Uᵢ` iff `p ∈ Uᵢ` for every `i`. -/
theorem mem_iInf_iff {ι : Sort _} (f : ι → RO P) (p : P) :
    (iInf f).carrier p ↔ ∀ i, (f i).carrier p :=
  ⟨fun h i => h (f i) ⟨i, rfl⟩, fun h _ ⟨i, hi⟩ => hi ▸ h i⟩

/-- Membership in a complement: no extension of `p` lies in `U`. -/
theorem mem_compl_iff (U : RO P) (p : P) : (Uᶜ).carrier p ↔ ∀ q, q ≤ p → ¬ U.carrier q :=
  Iff.rfl

/-- The bottom element contains no condition. -/
theorem not_mem_bot (p : P) : ¬ (⊥ : RO P).carrier p := fun h => h

/-- The top element contains every condition. -/
theorem mem_top (p : P) : (⊤ : RO P).carrier p := trivial

/-- **Density criterion.** If every condition of `U` has an extension in `V`, then `U ≤ V`
(by downward closure and regularity of `V`). -/
theorem le_of_dense {U V : RO P} (h : ∀ p, U.carrier p → ∃ r, r ≤ p ∧ V.carrier r) : U ≤ V :=
  fun p hp => V.reg p fun q hq => h q (U.down p q hq hp)

/-- A regular open set into which every condition can be extended is `⊤`. -/
theorem top_le_of_dense {V : RO P} (h : ∀ p, ∃ r, r ≤ p ∧ V.carrier r) : ⊤ ≤ V :=
  le_of_dense fun p _ => h p

/-- The **principal** regular open set `⌈r⌉` generated by a condition `r`. -/
def prin (r : P) : RO P := ofSet fun q => q ≤ r

/-- A condition lies in its principal regular open set. -/
theorem mem_prin (r : P) : (prin r).carrier r :=
  le_regClosure (fun _ _ h h' => ForcingNotion.trans _ _ _ h h') (ForcingNotion.refl r)

/-- `⌈r⌉ ≤ U` iff `r ∈ U`. -/
theorem prin_le_iff {r : P} {U : RO P} : prin r ≤ U ↔ U.carrier r :=
  ⟨fun h => h r (mem_prin r), fun h _ hp => regClosure_le (fun q hq => U.down r q hq h) hp⟩

end RO

/-! ### The collapse algebra and the generic function -/

/-- **The collapse algebra** `Col I`: regular open sets of countable partial functions
`I ⇀ 𝒫(ℕ)`. For `I = W₁` it collapses the continuum onto `ω₁`. -/
abbrev Col (I : Type) : Type := RO (CCond I)

/-- **The collapse algebra is non-degenerate**: `⊤ ≠ ⊥`. -/
theorem col_top_ne_bot (I : Type) : (⊤ : Col I) ≠ ⊥ := RO.top_ne_bot (CCond.empty I)

variable {I : Type}

/-- The **atom** `⟦g(ξ) = a⟧` of the generic function `g : I → 𝒫(ℕ)`: the conditions with
value `a` at `ξ`. -/
noncomputable def catom (ξ : I) (a : Nat → Prop) : Col I where
  carrier p := p.f ξ = some a
  down _ _ h hp := h _ _ hp
  reg p h := by
    cases hp : p.f ξ with
    | some b =>
      obtain ⟨r, hr, hra⟩ := h p (ForcingNotion.refl p)
      exact (hr ξ b hp).symm.trans hra
    | none =>
      obtain ⟨r, hr, hra⟩ := h (p.extend ξ fun n => ¬ a n) (CCond.extend_le p ξ _)
      have e := Option.some.inj ((hr ξ _ (CCond.extend_at _ hp)).symm.trans hra)
      have e0 := congrFun e 0
      exact absurd (propext_iff.1 e0) (fun h => by by_cases h0 : a 0 <;> simp_all)

/-- **The generic function is single-valued.** `⟦g(ξ) = a⟧ ⊓ ⟦g(ξ) = a'⟧ = ⊥` for `a ≠ a'`. -/
theorem catom_disj {ξ : I} {a a' : Nat → Prop} (h : a ≠ a') : catom ξ a ⊓ catom ξ a' ≤ ⊥ :=
  fun _ hp => h (Option.some.inj (hp.1.symm.trans hp.2))

/-- **The generic function hits every ground real.** `⨆_ξ ⟦g(ξ) = a⟧ = ⊤`: any condition can
be extended at a fresh point to take the value `a`. -/
theorem top_le_iSup_catom [Omega1Like I] (a : Nat → Prop) :
    ⊤ ≤ iSup fun ξ : I => catom ξ a :=
  RO.top_le_of_dense fun p => by
    obtain ⟨ξ, hξ⟩ := CCond.exists_fresh p
    refine ⟨p.extend ξ a, CCond.extend_le p ξ a, ?_⟩
    exact (RO.mem_iSup_iff _ _).2 fun q hq => ⟨q, ForcingNotion.refl q, ξ,
      hq ξ a (CCond.extend_at a hξ)⟩

/-- **Deciding lemma (σ-closed forcing adds no new countable sequences).** Let `K` be
countable and, for each `k : K`, let `V k : J → Col I` be a family of possible answers with
`c ≤ ⨆_j V k j`. Then below every condition `p ∈ c` there is a single condition `r` and an
answer `ζ k` for every question `k` with `r ∈ V k (ζ k)` for all `k`. The conditions are found
one question at a time and the resulting descending sequence has a lower bound. -/
theorem decide_countable {K J : Type} (hK : Countable K) (c : Col I) (V : K → J → Col I)
    (hV : ∀ k, c ≤ iSup (V k)) {p : CCond I} (hp : c.carrier p) :
    ∃ r, r ≤ p ∧ ∃ ζ : K → J, ∀ k, (V k (ζ k)).carrier r := by
  rcases Classical.em (Nonempty K) with hne | hne
  rotate_left
  · exact ⟨p, ForcingNotion.refl p, fun k => absurd ⟨k⟩ hne, fun k => absurd ⟨k⟩ hne⟩
  obtain ⟨k₀⟩ := hne
  obtain ⟨g, hg⟩ := hK
  obtain ⟨e, he⟩ := exists_surjective_of_injective hg k₀
  have step : ∀ q, c.carrier q → ∀ k, ∃ r, r ≤ q ∧ ∃ j, (V k j).carrier r := fun q hq k =>
    (RO.mem_iSup_iff _ _).1 (hV k q hq) q (ForcingNotion.refl q)
  let seq : Nat → {q // c.carrier q} := fun n => Nat.rec ⟨p, hp⟩ (fun n q =>
    ⟨Classical.choose (step q.1 q.2 (e n)),
      c.down _ _ (Classical.choose_spec (step q.1 q.2 (e n))).1 q.2⟩) n
  have hseq : ∀ n, (seq (n + 1)).1 ≤ (seq n).1 ∧ ∃ j, (V (e n) j).carrier (seq (n + 1)).1 :=
    fun n => Classical.choose_spec (step (seq n).1 (seq n).2 (e n))
  obtain ⟨r, hr⟩ := CCond.sigma_closed (fun n => (seq n).1) fun n => (hseq n).1
  let nk : K → Nat := fun k => Classical.choose (he k)
  have hnk : ∀ k, e (nk k) = k := fun k => Classical.choose_spec (he k)
  have hk : ∀ k, ∃ j, (V k j).carrier r := by
    intro k
    obtain ⟨j, hj⟩ := (hseq (nk k)).2
    have h2 := (V (e (nk k)) j).down _ r (hr (nk k + 1)) hj
    rw [hnk k] at h2
    exact ⟨j, h2⟩
  exact ⟨r, hr 0, fun k => Classical.choose (hk k), fun k => Classical.choose_spec (hk k)⟩

end Foundations.Forcing
