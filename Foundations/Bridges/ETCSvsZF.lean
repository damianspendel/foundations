import Foundations.Bridges.ZFQuotient

/-!
# Material sets and structural sets: ZF versus ETCS

Two pictures of what a set is have competed since the 1960s.

* **Material set theory** (Zermelo, Fraenkel, von Neumann; Part I). There is one
  global membership relation; every set has members which are themselves sets, and
  one may sensibly ask whether `∅ ∈ 2` or whether `1 ∈ π`. Functions are particular
  sets: sets of ordered pairs.
* **Structural set theory** (Lawvere's ETCS, 1964; Part VII). Sets are objects of a
  category and functions are primitive arrows. An element of `X` is an arrow
  `1 → X`; a set has no hidden internal nature, and isomorphic sets are
  indistinguishable. Paul Benacerraf's *What numbers could not be* (1965) — that
  arithmetic cannot settle whether `2 = {∅, {∅}}` or `2 = {{∅}}` — is the
  structuralist's favourite argument; John Mayberry (*The Foundations of
  Mathematics in the Theory of Sets*, 2000) and William Lawvere argued, from opposite
  directions, about which picture is foundationally prior.

The two are not rivals in the way they first appear: each can be interpreted in the
other. This file makes one half of that precise inside our project. The ZF sets of
Part I together with their set-theoretic functions (sets of pairs that are
functional) form a **category** `ZFCat`. Sending a set `X` to the *type of its
members* `{z // z ∈ X}` gives a functor

    El : ZFCat ⥤ Type 1

into the category of types, which Part VII showed to be a model of ETCS (in `Type`;
the same proofs work one universe up). We prove:

* `El` is **faithful** — a set-function is determined by what it does to elements
  (extensionality of graphs) — and **full** — every type-theoretic function between
  members comes from a set (by separation inside a cartesian product). So the
  material functions are exactly the structural ones.
* `El` is **not essentially surjective**: no set has as many members as there are
  sets (Russell). The type universe contains "proper classes" such as the type
  `ZFSet` itself; the ZF universe sits inside the structural world as a full
  subcategory, not as the whole.
* `ZFCat` has a terminal object `{∅}`, binary products (the Kuratowski product
  `X × Y`), and a **natural numbers object**: `ω` with `∅` and set-successor — the
  recursion theorem of Part I is precisely the NNO property. `El` **preserves** all
  of these: it sends them to a terminal object, products and an NNO in the category
  of types.
* Hence, by Part VII's categoricity, `El ω` is *uniquely* isomorphic to Lean's `Nat`
  as an NNO — and the unique isomorphism is the concrete bridge `Omega.toNat` of
  `NatBridges`. On the natural numbers, the material and the structural foundation
  provably say the same thing.
-/

namespace Foundations.Bridges

open Foundations.Sets Foundations.Sets.ZFSet Foundations.Categories Category

/-! ## Graphs of operations -/

/-- The **graph** of an operation `f` on the set `X`, as a subset of `X × Y`:
`{⟪a, f a⟫ | a ∈ X}`, obtained by separation. -/
noncomputable def graphOf (X Y : ZFSet) (f : ZFSet → ZFSet) : ZFSet :=
  sep (fun p => ∃ a ∈ X, p = ⟪a, f a⟫) (prod X Y)

/-- The graph of an operation mapping `X` into `Y` is a function from `X` to `Y`. -/
theorem graphOf_isFunction {X Y : ZFSet} {f : ZFSet → ZFSet} (hf : ∀ a ∈ X, f a ∈ Y) :
    IsFunction (graphOf X Y f) X Y := by
  refine ⟨sep_subset _ _, fun a ha => ⟨f a, mem_sep.2 ⟨kpair_mem_prod.2 ⟨ha, hf a ha⟩, a, ha, rfl⟩,
    fun y hy => ?_⟩⟩
  obtain ⟨_, a', _, he⟩ := mem_sep.1 hy
  obtain ⟨rfl, rfl⟩ := kpair_inj.1 he
  rfl

/-- Applying the graph of `f` to `a ∈ X` gives `f a`. -/
theorem app_graphOf {X Y : ZFSet} {f : ZFSet → ZFSet} (hf : ∀ a ∈ X, f a ∈ Y) {a : ZFSet}
    (ha : a ∈ X) : app (graphOf X Y f) a = f a :=
  app_eq (graphOf_isFunction hf) (mem_sep.2 ⟨kpair_mem_prod.2 ⟨ha, hf a ha⟩, a, ha, rfl⟩)

/-! ## The category of ZF sets -/

/-- The objects of the **category of ZF sets**: a wrapper around `ZFSet`, so that the
category structure does not leak onto `ZFSet` itself. -/
structure ZFCat where
  /-- The underlying ZF set. -/
  set : ZFSet

/-- The set-theoretic functions from `X` to `Y`. -/
def ZFHom (X Y : ZFSet) : Type 1 := {F : ZFSet // IsFunction F X Y}

/-- Two set-theoretic functions agreeing on the domain are equal. -/
theorem ZFHom.ext {X Y : ZFSet} {F G : ZFHom X Y} (h : ∀ a ∈ X, app F.1 a = app G.1 a) :
    F = G := Subtype.ext (function_ext F.2 G.2 h)

/-- The identity function of `X`: the diagonal `{⟪a, a⟫ | a ∈ X}`. -/
noncomputable def ZFHom.id (X : ZFSet) : ZFHom X X :=
  ⟨graphOf X X (fun a => a), graphOf_isFunction fun _ h => h⟩

/-- Composition of set-theoretic functions ("first `F`, then `G`"). -/
noncomputable def ZFHom.comp {X Y Z : ZFSet} (F : ZFHom X Y) (G : ZFHom Y Z) : ZFHom X Z :=
  ⟨graphOf X Z (fun a => app G.1 (app F.1 a)),
    graphOf_isFunction fun _ ha => app_mem G.2 (app_mem F.2 ha)⟩

/-- Application of the identity. -/
theorem ZFHom.app_id {X a : ZFSet} (ha : a ∈ X) : app (ZFHom.id X).1 a = a :=
  app_graphOf (fun _ h => h) ha

/-- Application of a composite. -/
theorem ZFHom.app_comp {X Y Z : ZFSet} (F : ZFHom X Y) (G : ZFHom Y Z) {a : ZFSet} (ha : a ∈ X) :
    app (ZFHom.comp F G).1 a = app G.1 (app F.1 a) :=
  app_graphOf (fun _ hb => app_mem G.2 (app_mem F.2 hb)) ha

/-- **The category of ZF sets.** Objects are sets; arrows `X ⟶ Y` are set-theoretic
functions — sets `F ⊆ X × Y` that are functional; composition and identities are
graphs formed by separation. -/
noncomputable instance zfCategory : Category.{1} ZFCat where
  Hom X Y := ZFHom X.set Y.set
  id X := ZFHom.id X.set
  comp F G := ZFHom.comp F G
  id_comp F := ZFHom.ext fun a ha => by rw [ZFHom.app_comp _ _ ha, ZFHom.app_id ha]
  comp_id F := ZFHom.ext fun a ha => by rw [ZFHom.app_comp _ _ ha, ZFHom.app_id (app_mem F.2 ha)]
  assoc F G H := ZFHom.ext fun a ha => by
    rw [ZFHom.app_comp _ _ ha, ZFHom.app_comp _ _ ha, ZFHom.app_comp _ _ ha,
      ZFHom.app_comp _ _ (app_mem F.2 ha)]

/-- Two arrows of `ZFCat` are equal when they agree on every element of the domain. -/
theorem zf_hom_ext {X Y : ZFCat} {F G : X ⟶ Y} (h : ∀ a ∈ X.set, app F.1 a = app G.1 a) :
    F = G := ZFHom.ext h

/-- Application of a composite in `ZFCat`. -/
theorem app_comp {X Y Z : ZFCat} (F : X ⟶ Y) (G : Y ⟶ Z) {a : ZFSet} (ha : a ∈ X.set) :
    app (F ≫ G).1 a = app G.1 (app F.1 a) := ZFHom.app_comp F G ha

/-- Application of an identity in `ZFCat`. -/
theorem app_id {X : ZFCat} {a : ZFSet} (ha : a ∈ X.set) : app (𝟙 X : X ⟶ X).1 a = a :=
  ZFHom.app_id ha

/-! ## The functor "members of" -/

/-- **The functor `El : ZFCat ⥤ Type 1`**, sending a set to the type of its members and a
set-theoretic function to the corresponding type-theoretic function. -/
noncomputable def El : ZFCat ⥤ Type 1 where
  obj X := {z : ZFSet // z ∈ X.set}
  map F z := ⟨app F.1 z.1, app_mem F.2 z.2⟩
  map_id _ := funext fun z => Subtype.ext (app_id z.2)
  map_comp F G := funext fun z => Subtype.ext (app_comp F G z.2)

/-- **`El` is faithful**: set-functions with the same action on members are equal. -/
theorem El_faithful {X Y : ZFCat} {F G : X ⟶ Y} (h : El.map F = El.map G) : F = G :=
  zf_hom_ext fun a ha => congrArg Subtype.val (congrFun h ⟨a, ha⟩)

/-- Extending a function on members to an operation on all sets (by `∅` outside `X`). -/
noncomputable def extend {X Y : ZFSet} (f : {z // z ∈ X} → {z // z ∈ Y}) (a : ZFSet) : ZFSet :=
  open Classical in if h : a ∈ X then (f ⟨a, h⟩).1 else ∅

/-- `extend f` agrees with `f` on members. -/
theorem extend_mem {X Y : ZFSet} (f : {z // z ∈ X} → {z // z ∈ Y}) {a : ZFSet} (ha : a ∈ X) :
    extend f a = (f ⟨a, ha⟩).1 := by
  simp [extend, ha]

/-- **`El` is full**: every function between the members of two sets is induced by a
set-theoretic function — its graph, formed by separation in the product. -/
theorem El_full {X Y : ZFCat} (f : El.obj X ⟶ El.obj Y) : ∃ F : X ⟶ Y, El.map F = f := by
  have hf : ∀ a ∈ X.set, extend f a ∈ Y.set := fun a ha => by
    rw [extend_mem f ha]; exact (f ⟨a, ha⟩).2
  refine ⟨⟨graphOf X.set Y.set (extend f), graphOf_isFunction hf⟩, funext fun z => ?_⟩
  apply Subtype.ext
  show app (graphOf X.set Y.set (extend f)) z.1 = (f z).1
  rw [app_graphOf hf z.2, extend_mem f z.2]
  rfl

/-- **`El` is not essentially surjective.** No ZF set has members in bijection with all
ZF sets: otherwise, by replacement, there would be a universal set, which Russell's
paradox forbids. The type of all sets is a "proper class" of the structural world. -/
theorem El_not_essSurj : ¬ ∃ X : ZFCat, Nonempty (El.obj X ≅ (ZFSet : Type 1)) := by
  rintro ⟨X, ⟨i⟩⟩
  apply russell
  let g : El.obj X → ZFSet := i.hom
  refine ⟨image (fun a => open Classical in if h : a ∈ X.set then g ⟨a, h⟩ else ∅) X.set,
    fun x => mem_image.2 ⟨(i.inv x).1, (i.inv x).2, ?_⟩⟩
  have hx : i.hom (i.inv x) = x := congrFun i.inv_hom_id x
  simp only [(i.inv x).2, dite_true]
  exact hx

/-! ## Terminal object and products -/

/-- The one-point set `{∅}` as an object of `ZFCat`. -/
noncomputable def zfOne : ZFCat := ⟨{∅}⟩

/-- **`{∅}` is terminal** in `ZFCat`: there is exactly one function into it. -/
noncomputable def zfOne_terminal : IsTerminal zfOne where
  lift X := ⟨graphOf X.set {∅} (fun _ => ∅), graphOf_isFunction fun _ _ => mem_singleton.2 rfl⟩
  uniq F G := zf_hom_ext fun _ ha =>
    (mem_singleton.1 (app_mem F.2 ha)).trans (mem_singleton.1 (app_mem G.2 ha)).symm

/-- **`El` preserves the terminal object**: `El {∅}` is terminal in the category of types. -/
noncomputable def El_one_terminal : IsTerminal (C := Type 1) (El.obj zfOne) where
  lift _ := fun _ => ⟨∅, mem_singleton.2 rfl⟩
  uniq f g := funext fun x => Subtype.ext
    ((mem_singleton.1 (f x).2).trans (mem_singleton.1 (g x).2).symm)

/-- The cartesian product `X × Y` as an object of `ZFCat`. -/
noncomputable def zfProd (X Y : ZFCat) : ZFCat := ⟨prod X.set Y.set⟩

/-- First projection maps `X × Y` into `X`. -/
theorem pfst_mem {X Y p : ZFSet} (hp : p ∈ prod X Y) : pfst p ∈ X := by
  obtain ⟨a, ha, b, _, rfl⟩ := mem_prod.1 hp; rw [pfst_kpair]; exact ha

/-- Second projection maps `X × Y` into `Y`. -/
theorem psnd_mem {X Y p : ZFSet} (hp : p ∈ prod X Y) : psnd p ∈ Y := by
  obtain ⟨a, _, b, hb, rfl⟩ := mem_prod.1 hp; rw [psnd_kpair]; exact hb

/-- The first projection arrow `X × Y ⟶ X`. -/
noncomputable def zfFst (X Y : ZFCat) : zfProd X Y ⟶ X :=
  ⟨graphOf _ X.set pfst, graphOf_isFunction fun _ => pfst_mem⟩

/-- The second projection arrow `X × Y ⟶ Y`. -/
noncomputable def zfSnd (X Y : ZFCat) : zfProd X Y ⟶ Y :=
  ⟨graphOf _ Y.set psnd, graphOf_isFunction fun _ => psnd_mem⟩

/-- A member of a product is the pair of its projections. -/
theorem eq_kpair_of_mem_prod {X Y p : ZFSet} (hp : p ∈ prod X Y) : p = ⟪pfst p, psnd p⟫ := by
  obtain ⟨a, _, b, _, rfl⟩ := mem_prod.1 hp; simp

/-- The first projection on members of the product. -/
theorem app_zfFst {X Y : ZFCat} {p : ZFSet} (hp : p ∈ prod X.set Y.set) :
    app (zfFst X Y).1 p = pfst p := app_graphOf (fun _ => pfst_mem) hp

/-- The second projection on members of the product. -/
theorem app_zfSnd {X Y : ZFCat} {p : ZFSet} (hp : p ∈ prod X.set Y.set) :
    app (zfSnd X Y).1 p = psnd p := app_graphOf (fun _ => psnd_mem) hp

/-- The pairing arrow `⟨f, g⟩ : W ⟶ X × Y`, `w ↦ ⟪f w, g w⟫`. -/
noncomputable def zfPair {W X Y : ZFCat} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ zfProd X Y :=
  ⟨graphOf W.set (prod X.set Y.set) (fun w => ⟪app f.1 w, app g.1 w⟫),
    graphOf_isFunction fun _ hw => kpair_mem_prod.2 ⟨app_mem f.2 hw, app_mem g.2 hw⟩⟩

/-- The pairing arrow at `w`. -/
theorem app_zfPair {W X Y : ZFCat} (f : W ⟶ X) (g : W ⟶ Y) {w : ZFSet} (hw : w ∈ W.set) :
    app (zfPair f g).1 w = ⟪app f.1 w, app g.1 w⟫ :=
  app_graphOf (fun _ hw => kpair_mem_prod.2 ⟨app_mem f.2 hw, app_mem g.2 hw⟩) hw

/-- **The Kuratowski product is a categorical product** in `ZFCat`. -/
noncomputable def zfProd_isProduct (X Y : ZFCat) :
    IsProduct X Y (zfProd X Y) (zfFst X Y) (zfSnd X Y) where
  lift f g := zfPair f g
  fac₁ f g := zf_hom_ext fun w hw => by
    rw [app_comp _ _ hw, app_zfPair f g hw,
      app_zfFst (kpair_mem_prod.2 ⟨app_mem f.2 hw, app_mem g.2 hw⟩), pfst_kpair]
  fac₂ f g := zf_hom_ext fun w hw => by
    rw [app_comp _ _ hw, app_zfPair f g hw,
      app_zfSnd (kpair_mem_prod.2 ⟨app_mem f.2 hw, app_mem g.2 hw⟩), psnd_kpair]
  uniq f g h h₁ h₂ := zf_hom_ext fun w hw => by
    rw [app_zfPair f g hw]
    have hm : app h.1 w ∈ prod X.set Y.set := app_mem h.2 hw
    have e₁ : app (h ≫ zfFst X Y).1 w = app f.1 w := by rw [h₁]
    have e₂ : app (h ≫ zfSnd X Y).1 w = app g.1 w := by rw [h₂]
    rw [app_comp _ _ hw, app_zfFst hm] at e₁
    rw [app_comp _ _ hw, app_zfSnd hm] at e₂
    rw [eq_kpair_of_mem_prod hm, e₁, e₂]

/-- **`El` preserves binary products**: the members of `X × Y`, with the projections,
form a product of the member types in the category of types. -/
noncomputable def El_preserves_product (X Y : ZFCat) :
    IsProduct (C := Type 1) (El.obj X) (El.obj Y) (El.obj (zfProd X Y))
      (El.map (zfFst X Y)) (El.map (zfSnd X Y)) where
  lift f g w := ⟨⟪(f w).1, (g w).1⟫, kpair_mem_prod.2 ⟨(f w).2, (g w).2⟩⟩
  fac₁ f g := funext fun w => Subtype.ext
    ((app_zfFst (kpair_mem_prod.2 ⟨(f w).2, (g w).2⟩)).trans (pfst_kpair _ _))
  fac₂ f g := funext fun w => Subtype.ext
    ((app_zfSnd (kpair_mem_prod.2 ⟨(f w).2, (g w).2⟩)).trans (psnd_kpair _ _))
  uniq f g h h₁ h₂ := funext fun w => Subtype.ext (by
    have hm : (h w).1 ∈ prod X.set Y.set := (h w).2
    have e₁ : app (zfFst X Y).1 (h w).1 = (f w).1 := congrArg Subtype.val (congrFun h₁ w)
    have e₂ : app (zfSnd X Y).1 (h w).1 = (g w).1 := congrArg Subtype.val (congrFun h₂ w)
    rw [app_zfFst hm] at e₁
    rw [app_zfSnd hm] at e₂
    exact (eq_kpair_of_mem_prod hm).trans (by rw [e₁, e₂]))

/-! ## ω is a natural numbers object -/

/-- `ω` as an object of `ZFCat`. -/
noncomputable def zfOmega : ZFCat := ⟨ω⟩

/-- The zero arrow `{∅} ⟶ ω`, picking out `∅`. -/
noncomputable def zfZero : zfOne ⟶ zfOmega :=
  ⟨graphOf {∅} ω (fun _ => ∅), graphOf_isFunction fun _ _ => empty_mem_omega⟩

/-- The successor arrow `ω ⟶ ω`, `n ↦ n ∪ {n}`. -/
noncomputable def zfSucc : zfOmega ⟶ zfOmega :=
  ⟨graphOf ω ω ZFSet.succ, graphOf_isFunction fun _ => succ_mem_omega⟩

/-- The natural number named by a set (`0` if it is not a von Neumann numeral). -/
noncomputable def natOf (n : ZFSet) : Nat :=
  open Classical in if h : ∃ k, n = vn k then Classical.choose h else 0

/-- `natOf (vn k) = k`. -/
theorem natOf_vn (k : Nat) : natOf (vn k) = k := by
  have h : ∃ j, vn k = vn j := ⟨k, rfl⟩
  simp only [natOf, h, dite_true]
  exact (vn_injective (Classical.choose_spec h)).symm

/-- Iterating an operation `g` `k` times on `x`. -/
noncomputable def iterZ (x : ZFSet) (g : ZFSet → ZFSet) : Nat → ZFSet
  | 0 => x
  | k + 1 => g (iterZ x g k)

/-- Iterates stay in a set closed under `g`. -/
theorem iterZ_mem {X x : ZFSet} {g : ZFSet → ZFSet} (hx : x ∈ X) (hg : ∀ y ∈ X, g y ∈ X) :
    ∀ k, iterZ x g k ∈ X
  | 0 => hx
  | k + 1 => hg _ (iterZ_mem hx hg k)

/-- The arrow `ω ⟶ X` defined by recursion from `x : {∅} ⟶ X` and `f : X ⟶ X`:
`n ↦ fⁿ(x(∅))`, as a graph. -/
noncomputable def zfRec {X : ZFCat} (x : zfOne ⟶ X) (f : X ⟶ X) : zfOmega ⟶ X :=
  ⟨graphOf ω X.set (fun n => iterZ (app x.1 ∅) (app f.1) (natOf n)),
    graphOf_isFunction fun _ _ =>
      iterZ_mem (app_mem x.2 (mem_singleton.2 rfl)) (fun _ hy => app_mem f.2 hy) _⟩

/-- The recursively defined arrow at the numeral `vn k`. -/
theorem app_zfRec {X : ZFCat} (x : zfOne ⟶ X) (f : X ⟶ X) (k : Nat) :
    app (zfRec x f).1 (vn k) = iterZ (app x.1 ∅) (app f.1) k := by
  have hX := iterZ_mem (app_mem x.2 (mem_singleton.2 rfl)) (fun _ hy => app_mem f.2 hy)
  show app (graphOf ω X.set _) (vn k) = _
  rw [app_graphOf (fun _ _ => hX _) (vn_mem_omega k), natOf_vn]

/-- The zero arrow sends `∅` to `∅`. -/
theorem app_zfZero : app zfZero.1 ∅ = ∅ :=
  app_graphOf (fun _ _ => empty_mem_omega) (mem_singleton.2 rfl)

/-- The successor arrow sends `n ∈ ω` to `succ n`. -/
theorem app_zfSucc {n : ZFSet} (hn : n ∈ ω) : app zfSucc.1 n = ZFSet.succ n :=
  app_graphOf (fun _ => succ_mem_omega) hn

/-- **ω is a natural numbers object in `ZFCat`.** For every `x : {∅} ⟶ X` and `f : X ⟶ X`
there is exactly one `h : ω ⟶ X` with `h(∅) = x` and `h(n+1) = f(h(n))`. This is Part I's
recursion theorem, recast as a universal property. -/
noncomputable def zfOmega_isNNO : IsNNO zfOne zfOmega zfZero zfSucc where
  ind x f := zfRec x f
  ind_zero x f := zf_hom_ext fun a ha => by
    obtain rfl := mem_singleton.1 ha
    rw [app_comp _ _ ha, app_zfZero, show (∅ : ZFSet) = vn 0 from rfl, app_zfRec]
    rfl
  ind_succ x f := zf_hom_ext fun a ha => by
    obtain ⟨k, rfl⟩ := mem_omega.1 ha
    rw [app_comp _ _ ha, app_comp _ _ ha, app_zfSucc ha, ← vn_succ, app_zfRec, app_zfRec]
    rfl
  uniq x f h h₀ h₁ := zf_hom_ext fun a ha => by
    obtain ⟨k, rfl⟩ := mem_omega.1 ha
    rw [app_zfRec]
    induction k with
    | zero =>
      have : app (zfZero ≫ h).1 ∅ = app x.1 ∅ := by rw [h₀]
      exact (congrArg (app h.1) app_zfZero.symm).trans
        ((app_comp zfZero h (mem_singleton.2 rfl)).symm.trans this)
    | succ k ih =>
      have : app (zfSucc ≫ h).1 (vn k) = app (h ≫ f).1 (vn k) := by rw [h₁]
      exact (congrArg (app h.1) (app_zfSucc (vn_mem_omega k)).symm).trans
        ((app_comp zfSucc h (vn_mem_omega k)).symm.trans (this.trans
          ((app_comp h f (vn_mem_omega k)).trans (congrArg (app f.1) (ih (vn_mem_omega k))))))

/-! ## `El` preserves the natural numbers object, and the bridge to `Nat` -/

/-- The unique element of `El {∅}`. -/
noncomputable def oneElt : El.obj zfOne := ⟨∅, mem_singleton.2 rfl⟩

/-- Every element of `El {∅}` is `oneElt`. -/
theorem eq_oneElt (u : El.obj zfOne) : u = oneElt := Subtype.ext (mem_singleton.1 u.2)

/-- Iterating a type-theoretic function along a Lean natural number. -/
def iterT {X : Type 1} (x : X) (f : X → X) : Nat → X
  | 0 => x
  | k + 1 => f (iterT x f k)

/-- `El zfZero` picks out the numeral `0`. -/
theorem toNat_El_zero : Omega.toNat (El.map zfZero oneElt) = 0 :=
  vn_injective ((Omega.val_eq _).symm.trans app_zfZero)

/-- `El zfSucc` is the successor on numerals. -/
theorem toNat_El_succ (n : El.obj zfOmega) :
    Omega.toNat (El.map zfSucc n) = Omega.toNat n + 1 := by
  apply vn_injective
  exact (Omega.val_eq _).symm.trans ((app_zfSucc n.2).trans (congrArg ZFSet.succ (Omega.val_eq n)))

/-- `El zfZero` sends the point to `toOmega 0`. -/
theorem El_zero_eq : (El.map zfZero oneElt : El.obj zfOmega) = toOmega 0 :=
  Subtype.ext app_zfZero

/-- `El zfSucc` sends `toOmega k` to `toOmega (k + 1)`. -/
theorem El_succ_eq (k : Nat) : (El.map zfSucc (toOmega k) : El.obj zfOmega) = toOmega (k + 1) :=
  Subtype.ext (app_zfSucc (vn_mem_omega k))

/-- **`El` preserves the natural numbers object**: the members of `ω`, with `∅` and
successor, form an NNO in the category of types (one universe up from Part VII's). -/
noncomputable def El_omega_isNNO :
    IsNNO (C := Type 1) (El.obj zfOne) (El.obj zfOmega) (El.map zfZero) (El.map zfSucc) where
  ind x f n := iterT (x oneElt) f (Omega.toNat n)
  ind_zero x f := funext fun u => by
    rw [eq_oneElt u]
    show iterT _ f (Omega.toNat (El.map zfZero oneElt)) = _
    rw [toNat_El_zero]; rfl
  ind_succ x f := funext fun n => by
    show iterT _ f (Omega.toNat (El.map zfSucc n)) = f (iterT _ f (Omega.toNat n))
    rw [toNat_El_succ]; rfl
  uniq x f h h₀ h₁ := funext fun n => by
    have key : ∀ k, h (toOmega k) = iterT (x oneElt) f k := by
      intro k
      induction k with
      | zero =>
        have := congrFun h₀ oneElt
        rw [← this]
        exact congrArg h El_zero_eq.symm
      | succ k ih =>
        have := congrFun h₁ (toOmega k)
        have e : h (El.map zfSucc (toOmega k)) = f (h (toOmega k)) := this
        rw [El_succ_eq] at e
        rw [e, ih]; rfl
    exact (congrArg h (Omega.toOmega_toNat n)).symm.trans (key (Omega.toNat n))

/-- Lean's natural numbers, lifted to `Type 1`, form an NNO there (relative to `El {∅}`). -/
noncomputable def ulNatNNO :
    IsNNO (C := Type 1) (El.obj zfOne) (ULift.{1} Nat) (fun _ => ⟨0⟩) (fun n => ⟨n.down + 1⟩) where
  ind x f n := iterT (x oneElt) f n.down
  ind_zero x f := funext fun u => by rw [eq_oneElt u]; rfl
  ind_succ _ _ := rfl
  uniq x f h h₀ h₁ := funext fun ⟨n⟩ => by
    induction n with
    | zero => exact congrFun h₀ oneElt
    | succ k ih =>
      show h ⟨k + 1⟩ = f (iterT _ f k)
      rw [← ih]; exact congrFun h₁ ⟨k⟩

/-- **The structural and the material natural numbers coincide.** The unique isomorphism
of natural numbers objects between the members of ZF's `ω` and Lean's `Nat` (Part VII's
`IsNNO.uniqueIso`, applied to the images under `El`) is, concretely, the bridge
`Omega.toNat` of `NatBridges` — and it is the only map preserving zero and successor. -/
theorem omega_nno_iso_eq_bridge :
    (IsNNO.uniqueIso El_omega_isNNO ulNatNNO).hom = fun n => ULift.up (Omega.toNat n) := by
  refine (IsNNO.uniqueIso_unique (C := Type 1) El_omega_isNNO ulNatNNO
    (fun n => ULift.up (Omega.toNat n)) ?_ ?_).symm
  · funext u
    rw [eq_oneElt u]
    show ULift.up (Omega.toNat (El.map zfZero oneElt)) = ⟨0⟩
    rw [toNat_El_zero]
  · funext n
    show ULift.up (Omega.toNat (El.map zfSucc n)) = ⟨Omega.toNat n + 1⟩
    rw [toNat_El_succ]

/-- **Summary: the members-functor from ZF to types.** `El : ZFCat ⥤ Type 1` is faithful
and full, is not essentially surjective, and sends `{∅}`, `X × Y` and `ω` to a terminal
object, a product and a natural numbers object. -/
theorem El_summary :
    (∀ {X Y : ZFCat} (F G : X ⟶ Y), El.map F = El.map G → F = G) ∧
    (∀ {X Y : ZFCat} (f : El.obj X ⟶ El.obj Y), ∃ F, El.map F = f) ∧
    (¬ ∃ X : ZFCat, Nonempty (El.obj X ≅ (ZFSet : Type 1))) ∧
    Nonempty (IsTerminal (C := Type 1) (El.obj zfOne)) ∧
    (∀ X Y : ZFCat, Nonempty (IsProduct (C := Type 1) (El.obj X) (El.obj Y)
      (El.obj (zfProd X Y)) (El.map (zfFst X Y)) (El.map (zfSnd X Y)))) ∧
    Nonempty (IsNNO (C := Type 1) (El.obj zfOne) (El.obj zfOmega) (El.map zfZero)
      (El.map zfSucc)) :=
  ⟨fun _ _ h => El_faithful h, El_full, El_not_essSurj, ⟨El_one_terminal⟩,
    fun X Y => ⟨El_preserves_product X Y⟩, ⟨El_omega_isNNO⟩⟩

end Foundations.Bridges
