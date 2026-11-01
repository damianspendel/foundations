import Foundations.Categories.CCC

/-!
# Toposes: the category of types as a universe of sets

In 1969–70 F. William Lawvere and Myles Tierney distilled from Grothendieck's
sheaf-theoretic "toposes" a short list of elementary axioms on a category: finite
limits, exponentials, and a **subobject classifier**. A category satisfying them —
an **elementary topos** — behaves in every essential respect like a universe of sets:
one can form products, subsets, function sets and power sets, and interpret
higher-order logic in it.

The new ingredient is the subobject classifier: an object `Ω` of "truth values" with
a point `true : 1 ⟶ Ω`, such that the subobjects (monomorphisms `m : U ↣ X`) of any
object `X` correspond exactly to arrows `χ : X ⟶ Ω`, via pullback:

```
  U ──────→ 1
  │m        │ true
  ↓         ↓
  X ──χ───→ Ω
```

`χ` is the *characteristic map* of `U`, and `U` is "the set of `x` with `χ(x) = true`".
This is the comprehension principle of set theory, stated structurally: no membership
relation, only arrows and a universal property. In the category of types `Ω` is `Prop`
and `true` is the proposition `True` — the classifying map of an injection `m : U → X`
is the predicate `x ↦ ∃ u, m u = x`. (We work in the universe `Type`; other universes
work the same way after lifting `Prop`.)

**The internal logic.** The subobjects of any object of a topos form a *Heyting
algebra*, so the logic valid in every topos is *intuitionistic* higher-order logic —
excluded middle may fail (it fails in most sheaf toposes, where truth values are
"local"). A topos is **Boolean** when `Ω ≅ 1 + 1` with `true` and `false` as the two
injections; then the internal logic is classical. The topos of Lean types is Boolean,
because Lean's `Prop` is classical: Lean derives excluded middle `Classical.em` from the
axiom of choice by **Diaconescu's theorem** (1975) — itself a topos-theoretic discovery
(choice implies Booleanness in any topos). We prove the coproduct decomposition
`Prop ≅ 1 + 1` and two-valuedness of global truth values using `Classical.choice`.

**Lawvere–Tierney topologies.** An arrow `j : Ω ⟶ Ω` preserving `true`, idempotent,
and preserving conjunction is a *modality* "it is locally the case that"; it carves out a
subtopos of *sheaves*. The paradigm is double negation `¬¬`, whose sheaf subtopos is
always Boolean — Cohen's **forcing** is, in this language, passage to `¬¬`-sheaves on a
poset of conditions. We define topologies in general and show that `¬¬` is one on
`Prop` (an intuitionistically valid proof), collapsing to the identity classically.

**Why structuralists care.** In ZF (Part I) every mathematical object is a set built
from `∅` by membership; sets have "internal" structure (`∅ ∈ 2`), and foundations are
a single global universe. Topos theory offers instead *many* universes of discourse —
each topos a "world" with its own logic — characterised entirely by how their objects
relate. Mathematics done "internally" makes sense in any of them. The next file
singles out the axioms (Lawvere's ETCS) that make a topos look exactly like the
classical universe of sets.
-/

namespace Foundations.Categories

universe v u

open Category CartesianClosed

/-- A **monomorphism**: an arrow that can be cancelled on the left side of composites
(the categorical notion of injectivity). -/
structure Mono {C : Type u} [Category.{v} C] {X Y : C} (m : X ⟶ Y) : Prop where
  /-- Left cancellation. -/
  cancel : ∀ {W : C} (g h : W ⟶ X), g ≫ m = h ≫ m → g = h

/-- A **binary coproduct** `S` of `X` and `Y` with injections `i₁, i₂`: every pair of
arrows out of `X` and `Y` factors uniquely through `S` (the dual of a product). -/
structure IsCoproduct {C : Type u} [Category.{v} C] (X Y S : C) (i₁ : X ⟶ S) (i₂ : Y ⟶ S) where
  /-- The copairing `[f, g] : S ⟶ W`. -/
  desc : {W : C} → (X ⟶ W) → (Y ⟶ W) → (S ⟶ W)
  /-- `i₁ ≫ [f, g] = f`. -/
  fac₁ : ∀ {W : C} (f : X ⟶ W) (g : Y ⟶ W), i₁ ≫ desc f g = f
  /-- `i₂ ≫ [f, g] = g`. -/
  fac₂ : ∀ {W : C} (f : X ⟶ W) (g : Y ⟶ W), i₂ ≫ desc f g = g
  /-- Uniqueness of the copairing. -/
  uniq : ∀ {W : C} (f : X ⟶ W) (g : Y ⟶ W) (h : S ⟶ W), i₁ ≫ h = f → i₂ ≫ h = g →
    h = desc f g

/-- An **elementary topos**: a cartesian closed category with equalisers (hence all finite
limits) and a **subobject classifier** `true : 1 ⟶ Ω`: for every mono `m : U ⟶ X` there
is exactly one `χ : X ⟶ Ω` making `m` the pullback of `true` along `χ`. -/
class Topos (C : Type u) [Category.{v} C] extends CartesianClosed C where
  /-- The equaliser object of `f, g`. -/
  eqObj : {X Y : C} → (X ⟶ Y) → (X ⟶ Y) → C
  /-- The equalising arrow. -/
  eqι : {X Y : C} → (f g : X ⟶ Y) → (eqObj f g ⟶ X)
  /-- It is an equaliser. -/
  isEq : ∀ {X Y : C} (f g : X ⟶ Y), IsEqualizer f g (eqObj f g) (eqι f g)
  /-- The object of truth values. -/
  Ω : C
  /-- The truth value "true". -/
  truth : one ⟶ Ω
  /-- The characteristic map of a subobject. -/
  classify : {U X : C} → (m : U ⟶ X) → Mono m → (X ⟶ Ω)
  /-- The subobject is the pullback of `true` along its characteristic map. -/
  classify_pullback : ∀ {U X : C} (m : U ⟶ X) (hm : Mono m),
    IsPullback (classify m hm) truth U m (terminal.lift U)
  /-- The characteristic map is unique. -/
  classify_uniq : ∀ {U X : C} (m : U ⟶ X) (hm : Mono m) (χ : X ⟶ Ω),
    IsPullback χ truth U m (terminal.lift U) → χ = classify m hm

namespace Topos

variable {C : Type u} [Category.{v} C] [Topos C]

/-- **A topos has all pullbacks** (hence, with the terminal object, all finite limits): the
pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the equaliser of `π₁ ≫ f` and `π₂ ≫ g` on
`X × Y`. -/
def pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback f g (eqObj (fst ≫ f) (snd ≫ g)) (eqι _ _ ≫ fst) (eqι _ _ ≫ snd) where
  w := by rw [assoc, assoc, (isEq _ _).w]
  lift k₁ k₂ hk := (isEq _ _).lift (pair k₁ k₂) (by rw [← assoc, pair_fst, ← assoc, pair_snd, hk])
  fac₁ k₁ k₂ hk := by rw [← assoc, (isEq _ _).fac, pair_fst]
  fac₂ k₁ k₂ hk := by rw [← assoc, (isEq _ _).fac, pair_snd]
  uniq k₁ k₂ hk h h₁ h₂ := (isEq _ _).uniq _ _ h
    (hom_ext (by rw [assoc, h₁, pair_fst]) (by rw [assoc, h₂, pair_snd]))

/-- Every arrow out of the terminal object is a monomorphism. -/
theorem mono_from_one {X : C} (x : one ⟶ X) : Mono x :=
  ⟨fun g h _ => terminal.uniq g h⟩

/-- **Internal conjunction** `∧ : Ω × Ω ⟶ Ω`: the characteristic map of the point
`⟨true, true⟩`. -/
def and : prod (Ω : C) Ω ⟶ Ω := classify (pair truth truth) (mono_from_one _)

end Topos

/-- A **Lawvere–Tierney topology** on a topos: a modality `j : Ω ⟶ Ω` ("it is locally the
case that") which preserves truth, is idempotent and commutes with conjunction. -/
structure LTTopology (C : Type u) [Category.{v} C] [Topos C] where
  /-- The modality. -/
  j : (Topos.Ω : C) ⟶ Topos.Ω
  /-- `j true = true`. -/
  truth_j : Topos.truth ≫ j = Topos.truth
  /-- `j ∘ j = j`. -/
  idem : j ≫ j = j
  /-- `j (p ∧ q) = j p ∧ j q`. -/
  and_j : Topos.and ≫ j = pair (fst ≫ j) (snd ≫ j) ≫ Topos.and

/-! ## The topos of types -/

/-- In the category of types, a monomorphism is an injective function. -/
theorem types_mono_injective {U X : Type} {m : U ⟶ X} (hm : Mono m) (a b : U)
    (h : m a = m b) : a = b :=
  congrFun (hm.cancel (W := PUnit) (fun _ => a) (fun _ => b) (funext fun _ => h)) PUnit.unit

/-- The characteristic predicate of a map `m : U → X`: "`x` is in the image of `m`". -/
def typesClassify {U X : Type} (m : U → X) : X → Prop := fun x => ∃ u, m u = x

/-- The image of an injection is the pullback of `True` along its characteristic
predicate. -/
noncomputable def typesClassifyPullback {U X : Type} (m : U ⟶ X) (hm : Mono m) :
    IsPullback (C := Type) (typesClassify m) (fun _ : PUnit => True) U m (fun _ => PUnit.unit) where
  w := funext fun u => eq_true ⟨u, rfl⟩
  lift k₁ _ hk := fun w =>
    Classical.choose (of_eq_true (congrFun hk w : (∃ u, m u = k₁ w) = True))
  fac₁ k₁ _ hk := funext fun w =>
    Classical.choose_spec (of_eq_true (congrFun hk w : (∃ u, m u = k₁ w) = True))
  fac₂ _ _ _ := rfl
  uniq k₁ _ hk h h₁ _ := funext fun w => types_mono_injective hm _ _ (by
    have e₁ := congrFun h₁ w
    have e₂ := Classical.choose_spec (of_eq_true (congrFun hk w : (∃ u, m u = k₁ w) = True))
    exact e₁.trans e₂.symm)

/-- **The category of types is an elementary topos**: it is cartesian closed, has
equalisers (subtypes), and `Prop` with `True` classifies subobjects — the characteristic
map of an injection `m : U → X` being `x ↦ ∃ u, m u = x`. -/
noncomputable instance typesTopos : Topos Type where
  toCartesianClosed := typesCCC
  eqObj f g := {x // f x = g x}
  eqι _ _ := fun x => x.1
  isEq f g := types_equalizer f g
  Ω := Prop
  truth := fun _ => True
  classify m _ := typesClassify m
  classify_pullback m hm := typesClassifyPullback m hm
  classify_uniq {U X} m hm χ hχ := funext fun x => propext ⟨fun hx => by
      let k : PUnit ⟶ X := fun _ => x
      have hk : k ≫ χ = (fun _ : PUnit => PUnit.unit) ≫ (fun _ : PUnit => True) :=
        funext fun _ => eq_true hx
      exact ⟨hχ.lift k _ hk PUnit.unit, congrFun (hχ.fac₁ k _ hk) PUnit.unit⟩,
    fun ⟨u, hu⟩ => by
      have := congrFun hχ.w u
      change χ (m u) = True at this
      rw [← hu, this]; trivial⟩

/-- In the topos of types, the truth value `true` is the proposition `True`. -/
theorem types_truth : (Topos.truth : PUnit ⟶ (Topos.Ω : Type)) = fun _ => True := rfl

/-- The truth value "false" in the topos of types. -/
def typesFalse : PUnit ⟶ (Topos.Ω : Type) := fun _ => False

/-- **The topos of types is two-valued** (classically): every global truth value
`1 ⟶ Ω` is `true` or `false`. This uses excluded middle, i.e. (by Diaconescu's theorem as
implemented in Lean) the axiom of choice. -/
theorem types_two_valued (p : PUnit ⟶ (Topos.Ω : Type)) :
    p = Topos.truth ∨ p = typesFalse := by
  rcases Classical.em (p PUnit.unit) with h | h
  · exact .inl (funext fun u => by cases u; exact eq_true h)
  · exact .inr (funext fun u => by cases u; exact eq_false h)

/-- **The topos of types is Boolean**: `Ω` is the coproduct `1 + 1`, with `true` and
`false` as the two injections. The copairing `[f, g]` sends a proposition to `f` if it
holds and to `g` otherwise — a definition by cases that needs excluded middle. -/
noncomputable def types_boolean :
    IsCoproduct (C := Type) PUnit PUnit (Topos.Ω : Type) Topos.truth typesFalse where
  desc f g := fun p => @ite _ p (Classical.propDecidable p) (f PUnit.unit) (g PUnit.unit)
  fac₁ f g := funext fun u => by
    cases u; exact @ite_eq_left _ (Classical.propDecidable True) trivial _ _ _
  fac₂ f g := funext fun u => by
    cases u; exact @ite_eq_right _ (Classical.propDecidable False) id _ _ _
  uniq f g h h₁ h₂ := funext fun p => by
    rcases Classical.em p with hp | hp
    · rw [@ite_eq_left _ (Classical.propDecidable p) hp, eq_true hp]
      exact congrFun h₁ PUnit.unit
    · rw [@ite_eq_right _ (Classical.propDecidable p) hp, eq_false hp]
      exact congrFun h₂ PUnit.unit

/-- In the topos of types, internal conjunction is conjunction of propositions. -/
theorem types_and (p q : Prop) : (Topos.and : Prop × Prop ⟶ Prop) (p, q) =
    (p ∧ q) := by
  show (∃ _ : PUnit, (True, True) = (p, q)) = (p ∧ q)
  refine propext ⟨fun ⟨_, h⟩ => ?_, fun ⟨hp, hq⟩ => ⟨PUnit.unit, by rw [eq_true hp, eq_true hq]⟩⟩
  cases h
  exact ⟨trivial, trivial⟩

/-- **Double negation is a Lawvere–Tierney topology** on the topos of types. The logical
content is intuitionistically valid: `¬¬True`, `¬¬¬¬p ↔ ¬¬p` and `¬¬(p ∧ q) ↔ ¬¬p ∧ ¬¬q`
need no excluded middle (the axiom check still lists `Classical.choice`, inherited from
the construction of the topos structure on types). -/
def doubleNegation : LTTopology Type where
  j := fun p => ¬¬p
  truth_j := funext fun _ => propext ⟨fun _ => trivial, fun _ h => h trivial⟩
  idem := funext fun p => propext ⟨fun h hp => h fun hnn => hnn hp, fun h hn => hn h⟩
  and_j := funext fun ⟨p, q⟩ => by
    show (¬¬(Topos.and : Prop × Prop ⟶ Prop) (p, q)) =
      (Topos.and : Prop × Prop ⟶ Prop) (¬¬p, ¬¬q)
    rw [types_and, types_and]
    exact propext ⟨fun h => ⟨fun hp => h fun hpq => hp hpq.1, fun hq => h fun hpq => hq hpq.2⟩,
      fun ⟨hp, hq⟩ hpq => hp fun p' => hq fun q' => hpq ⟨p', q'⟩⟩

/-- **Classically, the double negation topology is trivial**: in a Boolean topos `¬¬p = p`,
so passing to `¬¬`-sheaves changes nothing. (In a non-Boolean topos, such as presheaves
on a poset of forcing conditions, it does — that is Cohen forcing.) -/
theorem doubleNegation_trivial : doubleNegation.j = 𝟙 (Topos.Ω : Type) :=
  funext fun _ => propext ⟨fun h => Classical.byContradiction h, fun hp hn => hn hp⟩

end Foundations.Categories
