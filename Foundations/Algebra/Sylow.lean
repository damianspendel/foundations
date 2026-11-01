import Foundations.Algebra.Cauchy

/-!
# Sylow's first theorem

Lagrange's theorem restricts the possible sizes of subgroups; Cauchy's theorem guarantees
subgroups of every prime order dividing `|G|`. In 1872 the Norwegian schoolteacher Ludwig
Sylow went much further: **if `p ^ k` divides `|G|`, then `G` has a subgroup of order
exactly `p ^ k`.** The maximal such subgroups, the *Sylow `p`-subgroups*, are the
skeleton on which the classification of finite groups is built.

We prove Sylow's first theorem by climbing a ladder of `p`-subgroups, one rung at a time.
Suppose `H` is a subgroup of order `p ^ j` and `p ^ (j+1)` still divides `|G|`. Let `H`
act on the set `G ⧸ H` of its left cosets. The fixed cosets are exactly the cosets `gH`
with `g` in the **normaliser** `N(H)`, so their number is `[N(H) : H]`; by the fixed-point
congruence of `Action.lean` it is congruent to `[G : H]`, a multiple of `p`. Thus `p`
divides the order of the quotient group `N(H) ⧸ H`, and Cauchy's theorem supplies an
element of order `p` there. Its preimage in `N(H)` is a subgroup of order `p · |H| =
p ^ (j+1)`. Starting from the trivial subgroup and climbing `k` rungs gives the theorem.

The proof thus assembles almost everything built in this part — cosets and Lagrange
counting, quotient groups, group actions and the orbit–stabiliser theorem, the `p`-group
congruence, and Cauchy's theorem — a fitting finale for the structural method.
-/

namespace Foundations.Algebra

open Group FiniteType QuotientGroup

universe u v

/-! ## Finiteness of quotients -/

section Dedup

variable {α : Type u}

/-- Remove repetitions from a list (keeping the last occurrence), deciding equality
classically. -/
noncomputable def dedup : List α → List α
  | [] => []
  | a :: l => by
    classical
    exact if a ∈ dedup l then dedup l else a :: dedup l

/-- `dedup` keeps exactly the same elements. -/
theorem mem_dedup (x : α) : ∀ l : List α, x ∈ dedup l ↔ x ∈ l
  | [] => Iff.rfl
  | a :: l => by
    classical
    unfold dedup
    by_cases h : a ∈ dedup l
    · simp only [h, ↓reduceIte, List.mem_cons, mem_dedup x l]
      constructor
      · intro hx; exact Or.inr hx
      · rintro (rfl | hx)
        · exact (mem_dedup _ l).1 h
        · exact hx
    · simp only [h, ↓reduceIte, List.mem_cons, mem_dedup x l]

/-- `dedup` produces a list without repetitions. -/
theorem nodup_dedup : ∀ l : List α, (dedup l).Nodup
  | [] => List.Pairwise.nil
  | a :: l => by
    classical
    unfold dedup
    by_cases h : a ∈ dedup l
    · simp only [h, ↓reduceIte]; exact nodup_dedup l
    · simp only [h, ↓reduceIte]; exact List.nodup_cons.2 ⟨h, nodup_dedup l⟩

/-- **Quotients of finite types are finite.** -/
noncomputable instance instFiniteQuotient [FiniteType α] (s : Setoid α) :
    FiniteType (Quotient s) where
  elems := dedup ((elems : List α).map (Quotient.mk s))
  nodup := nodup_dedup _
  complete q := by
    rw [mem_dedup, List.mem_map]
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    exact ⟨a, complete a, rfl⟩

end Dedup

/-! ## The action on cosets -/

section Cosets

variable {G : Type u} [Group G]

/-- Every group acts on the left cosets of any subgroup: `g • (xH) = (gx)H`. -/
instance cosetAction (H : Subgroup G) : MulAction G (G ⧸ H) where
  smul g := Quotient.lift (fun x => mk H (g * x)) (fun a b (hab : a⁻¹ * b ∈ H) => by
    apply mk_eq_mk.2
    rw [mul_inv_rev, Group.mul_assoc, inv_mul_cancel_left]; exact hab)
  one_smul q := by
    induction q using QuotientGroup.ind with
    | h a => exact congrArg (mk H) (Group.one_mul a)
  mul_smul g h q := by
    induction q using QuotientGroup.ind with
    | h a => exact congrArg (mk H) (Group.mul_assoc g h a)

/-- The coset space `G ⧸ H` of a finite group is finite. -/
noncomputable instance instFiniteCosets [FiniteType G] (H : Subgroup G) : FiniteType (G ⧸ H) :=
  instFiniteQuotient (cosetSetoid H)

/-- `g • (xH) = (gx)H`. -/
theorem coset_smul (H : Subgroup G) (g x : G) : g • mk H x = mk H (g * x) := rfl

/-- A subgroup acts wherever the ambient group acts. -/
instance Subgroup.action (S : Subgroup G) {X : Type v} [MulAction G X] : MulAction S X where
  smul s x := s.1 • x
  one_smul x := MulAction.one_smul (G := G) x
  mul_smul s t x := MulAction.mul_smul (G := G) s.1 t.1 x

variable [FiniteType G]

/-- **Counting preimages of cosets.** For any set `R` of cosets of `H`, the number of
`g ∈ G` whose coset lies in `R` is `|R| · |H|`: each coset has `|H|` elements. -/
theorem count_preimage_coset (H : Subgroup G) (R : G ⧸ H → Prop) :
    count (fun g => R (mk H g)) = count R * count (· ∈ H) := by
  have hstab : ∀ g, g ∈ MulAction.stabilizer G (mk H 1) ↔ g ∈ H := by
    intro g
    show mk H (g * 1) = mk H 1 ↔ g ∈ H
    rw [mul_one, mk_eq_mk, mul_one, H.inv_mem_iff]
  rw [count_congr (Q := (· ∈ H)) hstab |>.symm]
  rw [← MulAction.count_smul_mem (mk H 1) (count R) R rfl]
  · apply count_congr
    intro g
    show R (mk H g) ↔ R (mk H (g * 1))
    rw [mul_one]
  · intro q _
    obtain ⟨a, rfl⟩ := mk_surjective q
    exact ⟨a, by show mk H (a * 1) = mk H a; rw [mul_one]⟩

/-- **Lagrange's theorem for coset spaces.** `|G ⧸ H| · |H| = |G|`. -/
theorem card_quotient_mul (H : Subgroup G) : card (G ⧸ H) * card H = card G := by
  rw [show card H = count (· ∈ H) from card_subtype _, ← count_true, ← count_true,
    ← count_preimage_coset]

end Cosets

/-! ## Counting inside a subgroup -/

/-- Counting elements of a subtype `{x // R x}` satisfying `P` is the same as counting
elements `x` of the ambient type that satisfy `R` and (then) `P`. -/
theorem count_subtype {α : Type u} [FiniteType α] (R : α → Prop) (P : {x // R x} → Prop) :
    count (fun x => ∃ h : R x, P ⟨x, h⟩) = count P := by
  rw [← card_subtype, ← card_subtype, ← count_true, ← count_true]
  exact count_comp_bij (α := {y : {x // R x} // P y}) (β := {x // ∃ h : R x, P ⟨x, h⟩})
    (fun y => ⟨y.1.1, y.1.2, y.2⟩)
    (fun a b h => by
      have e := congrArg (fun z : {x // ∃ h : R x, P ⟨x, h⟩} => z.1) h
      exact Subtype.ext (Subtype.ext e))
    (fun ⟨x, h, hp⟩ => ⟨⟨⟨x, h⟩, hp⟩, rfl⟩) (fun _ => True) |>.symm

/-- If `P` implies `Q` and both are satisfied equally often, then `Q` implies `P`. -/
theorem imp_of_count_eq {α : Type u} [FiniteType α] {P Q : α → Prop} (hPQ : ∀ x, P x → Q x)
    (hc : count P = count Q) : ∀ x, Q x → P x := by
  have h := count_split Q P
  have h1 : count (fun x => Q x ∧ P x) = count P :=
    count_congr fun x => ⟨fun h => h.2, fun h => ⟨hPQ x h, h⟩⟩
  have h0 : count (fun x => Q x ∧ ¬ P x) = 0 := by omega
  intro x hq
  exact Classical.byContradiction fun hp => count_eq_zero.1 h0 x ⟨hq, hp⟩

/-! ## The normaliser -/

section Normalizer

variable {G : Type u} [Group G]

/-- The **normaliser** `N(H)` of a subgroup: the elements `g` with `g⁻¹ H g = H`. It is the
largest subgroup in which `H` is normal. -/
def normalizer (H : Subgroup G) : Subgroup G where
  carrier g := ∀ h, h ∈ H ↔ g⁻¹ * h * g ∈ H
  one_mem h := by rw [inv_one, one_mul, mul_one]
  mul_mem := by
    intro a b ha hb h
    rw [ha h, hb, mul_inv_rev]
    simp only [Group.mul_assoc]
  inv_mem := by
    intro a ha h
    rw [ha (a⁻¹⁻¹ * h * a⁻¹), inv_inv]
    simp only [Group.mul_assoc, inv_mul_cancel_left, Group.inv_mul_cancel, mul_one]

/-- `H ⊆ N(H)`. -/
theorem le_normalizer (H : Subgroup G) {g : G} (hg : g ∈ H) : g ∈ normalizer H := by
  intro h
  constructor
  · intro hh; exact H.mul_mem (H.mul_mem (H.inv_mem hg) hh) hg
  · intro hh
    have := H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)
    have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by
      simp only [Group.mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    rw [e] at this; exact this

/-- `H`, viewed as a subgroup of its normaliser. -/
def Subgroup.inNormalizer (H : Subgroup G) : Subgroup (normalizer H) :=
  Subgroup.comap (Hom.subtype (normalizer H)) H

/-- `H` is normal in its normaliser. -/
instance Subgroup.inNormalizer_normal (H : Subgroup G) : H.inNormalizer.Normal :=
  ⟨fun n hn g => by
    show g.1 * n.1 * g.1⁻¹ ∈ H
    rw [g.2 (g.1 * n.1 * g.1⁻¹)]
    have : g.1⁻¹ * (g.1 * n.1 * g.1⁻¹) * g.1 = n.1 := by
      simp only [Group.mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [this]; exact hn⟩

variable [FiniteType G]

/-- **Fixed cosets.** The coset `gH` is fixed by the action of `H` exactly when `g` lies in
the normaliser of `H`. (One inclusion `g⁻¹ H g ⊆ H` suffices, by counting.) -/
theorem isFixed_coset_iff (H : Subgroup G) (g : G) :
    MulAction.IsFixed H (mk H g) ↔ g ∈ normalizer H := by
  have key : MulAction.IsFixed H (mk H g) ↔ ∀ h, h ∈ H → g⁻¹ * h * g ∈ H := by
    constructor
    · intro hf h hh
      have : mk H (h⁻¹ * g) = mk H g := hf ⟨h⁻¹, H.inv_mem hh⟩
      have := mk_eq_mk.1 this
      rwa [mul_inv_rev, inv_inv] at this
    · intro hc h
      show mk H (h.1 * g) = mk H g
      apply mk_eq_mk.2
      rw [mul_inv_rev]
      exact hc _ (H.inv_mem h.2)
  rw [key]
  constructor
  · intro hc h
    refine ⟨hc h, ?_⟩
    apply imp_of_count_eq (P := (· ∈ H)) (Q := fun h => g⁻¹ * h * g ∈ H) hc
    · exact count_comp_bij (fun h => g⁻¹ * h * g)
        (fun a b hab => by
          have := congrArg (fun x => g * x * g⁻¹) hab
          simpa only [Group.mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using this)
        (fun y => ⟨g * y * g⁻¹, by
          simp only [Group.mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]⟩)
        (· ∈ H) |>.symm
  · intro hn h hh; exact (hn h).1 hh

end Normalizer

/-! ## Climbing the ladder -/

section Sylow

variable {G : Type u} [Group G] [FiniteType G]

/-- The order of `H` viewed inside its normaliser equals the order of `H`. -/
theorem card_inNormalizer (H : Subgroup G) : card H.inNormalizer = card H := by
  rw [card_subtype, card_subtype, ← count_subtype]
  exact count_congr fun g => ⟨fun ⟨_, h⟩ => h, fun h => ⟨le_normalizer H h, h⟩⟩

/-- **One rung of the ladder.** If `H` has order `p ^ j` and `p ^ (j+1)` divides `|G|`, then
`G` has a subgroup of order `p ^ (j+1)`. -/
theorem exists_subgroup_card_pow_succ {p j : Nat} (hp : IsPrime p) (H : Subgroup G)
    (hH : card H = p ^ j) (hdvd : p ^ (j + 1) ∣ card G) :
    ∃ K : Subgroup G, card K = p ^ (j + 1) := by
  have hp0 : 0 < p := by have := hp.1; omega
  have hpj : 0 < p ^ j := Nat.pow_pos hp0
  -- `p` divides the index `[G : H]`.
  have hindex : p ∣ card (G ⧸ H) := by
    obtain ⟨t, ht⟩ := hdvd
    have h1 := card_quotient_mul H
    rw [hH, ht, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm] at h1
    have : card (G ⧸ H) = p * t := Nat.eq_of_mul_eq_mul_left hpj h1
    rw [this]; exact Nat.dvd_mul_right p t
  -- So `p` divides the number of cosets fixed by `H`.
  have hfix := MulAction.count_fixed_mod (G := H) (X := G ⧸ H) hp hH
  rw [Nat.mod_eq_zero_of_dvd hindex] at hfix
  -- The number of fixed cosets is `|N(H) ⧸ H|`.
  let N := normalizer H
  have hcountN : count (fun g => MulAction.IsFixed H (mk H g)) = card N := by
    rw [card_subtype]; exact count_congr (isFixed_coset_iff H)
  rw [count_preimage_coset H (MulAction.IsFixed H)] at hcountN
  have hQ := card_quotient_mul H.inNormalizer
  rw [card_inNormalizer, ← hcountN, show card H = count (· ∈ H) from card_subtype _] at hQ
  have hHpos : 0 < count (· ∈ H) := count_pos.2 ⟨1, H.one_mem⟩
  have hQeq : card (N ⧸ H.inNormalizer) = count (MulAction.IsFixed H (X := G ⧸ H)) :=
    Nat.eq_of_mul_eq_mul_right hHpos hQ
  -- Cauchy's theorem in `N(H) ⧸ H` gives an element `q` of order `p`.
  obtain ⟨q, hq⟩ := cauchy (G := N ⧸ H.inNormalizer) hp
    (by rw [hQeq]; exact Nat.dvd_of_mod_eq_zero hfix)
  -- Its preimage is the desired subgroup.
  let K : Subgroup G := {
    carrier := fun g => ∃ h : g ∈ N, mk H.inNormalizer ⟨g, h⟩ ∈ powers q
    one_mem := ⟨N.one_mem, (powers q).one_mem⟩
    mul_mem := fun ⟨ha, hqa⟩ ⟨hb, hqb⟩ => ⟨N.mul_mem ha hb, (powers q).mul_mem hqa hqb⟩
    inv_mem := fun ⟨ha, hqa⟩ => ⟨N.inv_mem ha, (powers q).inv_mem hqa⟩ }
  refine ⟨K, ?_⟩
  rw [card_subtype]
  show count (fun g => ∃ h : g ∈ N, mk H.inNormalizer ⟨g, h⟩ ∈ powers q) = _
  rw [count_subtype (fun g => g ∈ N) (fun n => mk H.inNormalizer n ∈ powers q),
    count_preimage_coset H.inNormalizer (· ∈ powers q), count_powers, hq,
    ← card_subtype, card_inNormalizer, hH, Nat.pow_succ, Nat.mul_comm]

/-- **Sylow's first theorem.** If `p` is prime and `p ^ k` divides the order of the finite
group `G`, then `G` has a subgroup of order exactly `p ^ k`. -/
theorem sylow_first {p k : Nat} (hp : IsPrime p) (hdvd : p ^ k ∣ card G) :
    ∃ H : Subgroup G, card H = p ^ k := by
  induction k with
  | zero =>
    refine ⟨Subgroup.bot, ?_⟩
    rw [card_subtype, Nat.pow_zero]
    exact count_eq_self 1
  | succ k ih =>
    obtain ⟨H, hH⟩ := ih (Nat.dvd_trans (Nat.pow_dvd_pow p (Nat.le_succ k)) hdvd)
    exact exists_subgroup_card_pow_succ hp H hH hdvd

end Sylow

end Foundations.Algebra
