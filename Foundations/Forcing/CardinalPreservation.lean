import Foundations.Forcing.Formulas
import Foundations.Forcing.Cohen
import Foundations.Sets.Hartogs
import Foundations.Sets.CardinalArith

/-!
# The countable chain condition preserves cardinals

Why does adding `ℵ₂` Cohen reals not simply collapse `ℵ₂` to something smaller, making the
new reals too few after all? Because the Cohen algebra is **ccc**. Here is the Boolean form of
the classical argument. Suppose that in `V^B` some `f` is, to degree `d`, an injective
function from a name `X = {xₜ | t ∈ T}` (pairwise Boolean-distinct members) into a name
`Y = {yᵤ | u ∈ U}`.

* For each `t`, `d ≤ ⨆ᵤ ⟦(xₜ, yᵤ) ∈ f⟧`, since `f` is total on `X`.
* For each fixed `u`, the values `d ⊓ ⟦(xₜ, yᵤ) ∈ f⟧` for different `t` are pairwise disjoint,
  since `f` is injective and the `xₜ` are distinct. By ccc only countably many of them are
  non-zero.
* If `d ≠ ⊥`, choosing for every `t` some `u` with non-zero value gives an injection of `T`
  into `U × ℕ`.

So if `T` does **not** inject into `U × ℕ` (in the ground model), then `d = ⊥`: in `V^B` there is
no injection from `X` into `Y` (`isFunc_inf_isInj_eq_bot`). Cardinals that differ in the ground
model by more than a factor `ℵ₀` stay apart in the extension.

The second half of the file sets up the ground-model cardinals used later: `W₁`, the members
of the Hartogs ordinal `ℵ(ℕ) = ω₁`, and `W₂`, the members of `ℵ(W₁) = ω₂`. It proves the two
non-injectivity facts that are needed: `W₁ ↛ ℕ × ℕ` and `W₂ ↛ W₁ × ℕ`, the latter via
`κ · κ = κ` from `Sets/CardinalArith`.
-/

namespace Foundations.Forcing

open Foundations.Sets CBA

attribute [local instance] Classical.propDecidable

/-! ### The combinatorial core -/

/-- **ccc core lemma.** In a ccc algebra, let `d` be such that each `t ∈ T` has
`d ≤ ⨆ᵤ P t u`, and for each `u` the elements `d ⊓ P t u` (`t ∈ T`) are pairwise disjoint.
If `T` does not inject into `U × ℕ`, then `d = ⊥`. -/
theorem ccc_core {B : Type} [CompleteBooleanAlgebra B] (hB : IsCCC B) {T U : Type} (d : B)
    (P : T → U → B) (htot : ∀ t, d ≤ iSup (P t))
    (hdisj : ∀ u t t', t ≠ t' → (d ⊓ P t u) ⊓ (d ⊓ P t' u) ≤ ⊥)
    (hcard : ¬ ∃ g : T → U × Nat, Function.Injective g) : d = ⊥ := by
  -- for each `u`, only countably many `t` give a non-zero value
  have cnt : ∀ u, Countable {t // d ⊓ P t u ≠ ⊥} := by
    intro u
    obtain ⟨g, hg⟩ := hB (fun b => ∃ t, d ⊓ P t u = b ∧ b ≠ ⊥) (fun _ ⟨_, _, hb⟩ => hb)
      (fun b b' ⟨t, ht, _⟩ ⟨t', ht', _⟩ hne => by
        subst ht ht'
        exact eq_bot_iff.2 (hdisj u t t' fun e => hne (e ▸ rfl)))
    refine ⟨fun t => g ⟨d ⊓ P t.1 u, t.1, rfl, t.2⟩, fun t₁ t₂ heq => ?_⟩
    have h1 : d ⊓ P t₁.1 u = d ⊓ P t₂.1 u := congrArg Subtype.val (hg heq)
    refine Classical.byContradiction fun hne => t₁.2 (eq_bot_iff.2 ?_)
    have := hdisj u t₁.1 t₂.1 fun e => hne (Subtype.ext e)
    rwa [← h1, inf_idem] at this
  refine Classical.byContradiction fun hd => hcard ?_
  -- each `t` has some `u` with non-zero value
  have hex : ∀ t, ∃ u, d ⊓ P t u ≠ ⊥ := fun t => Classical.byContradiction fun hn => hd <|
    eq_bot_iff.2 <| le_trans' (le_inf _ _ _ le_rfl (htot t)) <| le_trans' inf_iSup_le <|
      iSup_le fun u => eq_bot_iff.1 (Classical.byContradiction fun h => hn ⟨u, h⟩)
  let ut : T → U := fun t => Classical.choose (hex t)
  have hut : ∀ t, d ⊓ P t (ut t) ≠ ⊥ := fun t => Classical.choose_spec (hex t)
  let g : ∀ u, {t // d ⊓ P t u ≠ ⊥} → Nat := fun u => Classical.choose (cnt u)
  have hg : ∀ u, Function.Injective (g u) := fun u => Classical.choose_spec (cnt u)
  let F : T → (Σ u, {t // d ⊓ P t u ≠ ⊥}) := fun t => ⟨ut t, t, hut t⟩
  have hF : Function.Injective F := fun t t' h =>
    congrArg (fun p : (Σ u, {t // d ⊓ P t u ≠ ⊥}) => p.2.1) h
  let G : (Σ u, {t // d ⊓ P t u ≠ ⊥}) → U × Nat := fun p => (p.1, g p.1 p.2)
  have hG : Function.Injective G := by
    rintro ⟨u, c⟩ ⟨u', c'⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    simp only at h1
    subst h1
    have := hg u h2
    subst this; rfl
  exact ⟨fun t => G (F t), fun t t' h => hF (hG h)⟩

/-! ### No injections between names of different ground cardinality -/

variable {B : Type} [CompleteBooleanAlgebra B]

/-- Shrinking the domain can only increase the degree of being a function. -/
theorem BSet.isFunc_mono_dom {f X X' Y : BSet B} (h : ∀ a, BSet.mem a X' ≤ BSet.mem a X) :
    BSet.isFunc f X Y ≤ BSet.isFunc f X' Y :=
  inf_le_inf (iInf_mono fun a => himp_le_himp (h a) le_rfl)
    (iInf_mono fun a => himp_le_himp (h a) le_rfl)

/-- Shrinking the domain can only increase the degree of injectivity. -/
theorem BSet.isInj_mono_dom {f X X' : BSet B} (h : ∀ a, BSet.mem a X' ≤ BSet.mem a X) :
    BSet.isInj f X ≤ BSet.isInj f X' :=
  iInf_mono fun a => iInf_mono fun a' => iInf_mono fun _ =>
    himp_le_himp (inf_le_inf (inf_le_inf (inf_le_inf (h a) (h a')) le_rfl) le_rfl) le_rfl

/-- **Preservation of cardinals by ccc forcing.** Let `X = {h t | t ∈ T}` and
`Y = {k u | u ∈ U}` be names (all members with degree `⊤`) whose members `h t` are pairwise
Boolean-distinct. If `T` does not inject into `U × ℕ`, then in `V^B` (for ccc `B`) no `f` is an
injective function from `X` into `Y`: `⟦f is a function X → Y⟧ ⊓ ⟦f is injective on X⟧ = ⊥`. -/
theorem isFunc_inf_isInj_eq_bot (hB : IsCCC B) {T U : Type} (h : T → BSet B) (k : U → BSet B)
    (hdist : ∀ t t', t ≠ t' → BSet.eq (h t) (h t') = ⊥)
    (hcard : ¬ ∃ g : T → U × Nat, Function.Injective g) (f : BSet B) :
    BSet.isFunc f (.mk T h fun _ => ⊤) (.mk U k fun _ => ⊤) ⊓
      BSet.isInj f (.mk T h fun _ => ⊤) = ⊥ := by
  let X : BSet B := .mk T h fun _ => ⊤
  let Y : BSet B := .mk U k fun _ => ⊤
  have memX : ∀ t, ⊤ ≤ BSet.mem (h t) X := fun t => BSet.bval_le_mem X t
  refine ccc_core hB _ (fun t u => BSet.pm (h t) (k u) f) (fun t => ?_) (fun u t t' hne => ?_) hcard
  · -- totality
    have h1 : BSet.isFunc f X Y ⊓ BSet.isInj f X ≤
        BSet.mem (h t) X ⇨ iSup fun b => BSet.mem b Y ⊓ BSet.pm (h t) b f :=
      inf_le_of_left_le (inf_le_of_left_le (iInf_le _ (h t)))
    refine le_trans' (le_trans' (le_inf _ _ _ h1 (le_trans' le_top' (memX t))) himp_inf_le) ?_
    refine iSup_le fun b => le_trans' iSup_inf_le (iSup_mono fun u => ?_)
    exact le_trans' (inf_le_inf (inf_le_right _ _) le_rfl) (BSet.pm_congr_right _ _ _ _)
  · -- disjointness, from injectivity and distinctness
    have hi : BSet.isFunc f X Y ⊓ BSet.isInj f X ≤
        (BSet.mem (h t) X ⊓ BSet.mem (h t') X ⊓ BSet.pm (h t) (k u) f ⊓ BSet.pm (h t') (k u) f) ⇨
          BSet.eq (h t) (h t') :=
      inf_le_of_right_le (iInf_le_of_le (h t) (iInf_le_of_le (h t') (iInf_le _ (k u))))
    rw [← hdist t t' hne]
    refine le_trans' (le_inf _ _ _ (inf_le_of_left_le (inf_le_of_left_le hi)) ?_) himp_inf_le
    refine le_inf _ _ _ (le_inf _ _ _ (le_inf _ _ _ ?_ ?_) (by lattice_le)) (by lattice_le)
    · exact le_trans' le_top' (memX t)
    · exact le_trans' le_top' (memX t')

/-! ### The ground cardinals `ω₁` and `ω₂` -/

/-- A small type (in `Type`) of the members of a ZF set: the index type of a presentation,
with indices identified when they name the same member. (The subtype `{z // z ∈ s}` lives in
`Type 1`, which is too big to be fed back into `hartogs`.) -/
def Small (s : ZFSet) : Type := Quot fun i j : s.Idx => s.elt i = s.elt j

namespace Small

variable {s : ZFSet}

/-- The member named by an element of `Small s`. -/
noncomputable def val : Small s → ZFSet := Quot.lift s.elt fun _ _ h => h

/-- Elements of `Small s` name members of `s`. -/
theorem val_mem (q : Small s) : q.val ∈ s :=
  Quot.ind (β := fun q => val q ∈ s) (fun i => ZFSet.elt_mem s i) q

/-- Distinct elements of `Small s` name distinct members. -/
theorem val_injective : Function.Injective (val : Small s → ZFSet) := by
  intro q q'
  induction q using Quot.ind
  induction q' using Quot.ind
  exact fun h => Quot.sound h

/-- The element of `Small s` naming a given member. -/
noncomputable def ofMem (z : ZFSet) (h : z ∈ s) : Small s :=
  Quot.mk _ (Classical.choose (ZFSet.mem_iff_elt.1 h))

/-- `ofMem` names the given member. -/
theorem val_ofMem (z : ZFSet) (h : z ∈ s) : (ofMem z h).val = z :=
  (Classical.choose_spec (ZFSet.mem_iff_elt.1 h)).symm

/-- Every function out of the big subtype factors through `Small s` injectively. -/
theorem ofMem_injective : Function.Injective fun z : {z // z ∈ s} => ofMem z.1 z.2 :=
  fun z z' h => Subtype.ext (by
    have := congrArg val h; simp only at this; rwa [val_ofMem, val_ofMem] at this)

end Small

/-- The countable ordinals: members of `ω₁ = ℵ(ℕ)`, the Hartogs ordinal of `ℕ`, as a small type. -/
def W₁ : Type := Small (ZFSet.hartogs Nat)

/-- The members of `ω₂ = ℵ(W₁)` (ordinals of cardinality at most `ℵ₁`), as a small type. -/
def W₂ : Type := Small (ZFSet.hartogs W₁)

/-- `ℕ` injects into `W₁`, via the finite von Neumann ordinals. -/
theorem nat_le_W₁ : CardLE Nat W₁ := by
  have hmem : ∀ n, ZFSet.vn n ∈ ZFSet.hartogs Nat := fun n => by
    refine (ZFSet.mem_hartogs_iff (ZFSet.isOrdinal_vn n)).2 ⟨fun z => Classical.choose
      (ZFSet.mem_vn.1 z.2), fun z z' h => Subtype.ext ?_⟩
    rw [(Classical.choose_spec (ZFSet.mem_vn.1 z.2)).2,
      (Classical.choose_spec (ZFSet.mem_vn.1 z'.2)).2]
    exact congrArg ZFSet.vn h
  refine ⟨fun n => Small.ofMem (ZFSet.vn n) (hmem n), fun m n h => ZFSet.vn_injective ?_⟩
  have := congrArg Small.val h
  rwa [Small.val_ofMem, Small.val_ofMem] at this

/-- **`ω₁` is uncountable:** `W₁` does not inject into `ℕ × ℕ`. -/
theorem W₁_not_inj : ¬ ∃ g : W₁ → Nat × Nat, Function.Injective g := fun ⟨g, hg⟩ =>
  ZFSet.hartogs_not_injective Nat ⟨fun z => cantorPair (g (Small.ofMem z.1 z.2)),
    fun _ _ h => Small.ofMem_injective (hg (cantorPair_injective h))⟩

/-- **`ω₂` is bigger than `ω₁ · ℵ₀`:** `W₂` does not inject into `W₁ × ℕ`. -/
theorem W₂_not_inj : ¬ ∃ g : W₂ → W₁ × Nat, Function.Injective g := by
  rintro ⟨g, hg⟩
  obtain ⟨m, hm, -⟩ := mul_self_equinum_of_nat_le nat_le_W₁
  obtain ⟨j, hj⟩ := nat_le_W₁
  refine ZFSet.hartogs_not_injective W₁
    ⟨fun z => m ((g (Small.ofMem z.1 z.2)).1, j (g (Small.ofMem z.1 z.2)).2),
      fun z z' h => Small.ofMem_injective (hg ?_)⟩
  obtain ⟨h1, h2⟩ := Prod.mk.inj (hm h)
  exact Prod.ext h1 (hj h2)

/-- `ω₁ ⊆ ω₂`: every countable ordinal is a member of `ω₂`. -/
theorem W₁_sub_W₂ {z : ZFSet} (h : z ∈ ZFSet.hartogs Nat) : z ∈ ZFSet.hartogs W₁ := by
  have h1 : ZFSet.hartogs Nat ∈ ZFSet.hartogs W₁ :=
    (ZFSet.mem_hartogs_iff (ZFSet.hartogs_isOrdinal Nat)).2
      ⟨fun z => Small.ofMem z.1 z.2, Small.ofMem_injective⟩
  exact (ZFSet.hartogs_isOrdinal W₁).1 _ h1 h

/-- The inclusion `W₁ → W₂`. -/
noncomputable def W₁.incl (ξ : W₁) : W₂ := Small.ofMem ξ.val (W₁_sub_W₂ ξ.val_mem)

/-- The inclusion is injective. -/
theorem W₁.incl_injective : Function.Injective W₁.incl := fun ξ ξ' h => by
  have := congrArg Small.val h
  simp only [W₁.incl, Small.val_ofMem] at this
  exact Small.val_injective this

end Foundations.Forcing
