import Foundations.Langlands.Rep.Basic

/-!
# Maschke's theorem

Heinrich Maschke proved in 1898–99 that a representation of a finite group over the complex
numbers is **completely reducible**: every subrepresentation has an invariant complement, so
every representation breaks into irreducible pieces. Frobenius had worked with the group
algebra as a whole; Maschke's theorem is what makes it legitimate to study representations one
irreducible at a time, and it is the first place where finiteness of `G` (more precisely, the
invertibility of `|G|` in the field) is essential: over a field of characteristic `p` dividing
`|G|` the theorem fails, which is the starting point of Brauer's modular representation theory.

The proof is the **averaging trick**, which reappears throughout the subject (Schur used it,
and in the form of Haar measure it extends to compact groups, a step towards automorphic
forms). Given an invariant subspace `W`:

1. choose *any* complement `C` of `W` (here: spanned by suitable standard basis vectors) and
   the corresponding projection `P` onto `W` along `C`;
2. average it over the group, `Q = |G|⁻¹ Σ_g ρ(g) P ρ(g⁻¹)`. Then `Q` still maps into `W` and
   fixes `W`, but now commutes with every `ρ(h)`;
3. the kernel of `Q` is an invariant complement of `W`.

We work over any field `K` in which `|G| ≠ 0` (so in particular over `ℂ`).
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u v w

variable {K : Type w} [CommRing K] {ι : Type v} [FiniteType ι]

/-! ## Sums and coordinate subspaces -/

namespace Subspace

/-- The **sum** `W + C = {w + c}` of two subspaces. -/
def sup (W C : Subspace ι K) : Subspace ι K where
  carrier x := ∃ w c, w ∈ W ∧ c ∈ C ∧ x = w + c
  zero_mem := ⟨0, 0, W.zero_mem, C.zero_mem, (AddAbGroup.zero_add 0).symm⟩
  add_mem := by
    rintro _ _ ⟨w, c, hw, hc, rfl⟩ ⟨w', c', hw', hc', rfl⟩
    exact ⟨w + w', c + c', W.add_mem hw hw', C.add_mem hc hc', by ac_rfl⟩
  smul_mem a := by
    rintro _ ⟨w, c, hw, hc, rfl⟩
    exact ⟨a • w, a • c, W.smul_mem a hw, C.smul_mem a hc, VectorSpace.smul_add a w c⟩

/-- The **coordinate subspace** of vectors supported on `S ⊆ ι`. -/
def coord (S : ι → Prop) : Subspace ι K where
  carrier x := ∀ a, ¬ S a → x a = 0
  zero_mem _ _ := rfl
  add_mem hx hy a ha := by
    show _ + _ = (0 : K); rw [hx a ha, hy a ha, Ring.add_zero]
  smul_mem c x hx a ha := by show c * _ = (0 : K); rw [hx a ha, Ring.mul_zero]

end Subspace

/-- One step of the greedy construction of a complement: if `eⱼ ∉ W + C_S`, then adding `j`
to `S` keeps the coordinate subspace independent of `W`. -/
theorem disjoint_step (hF : IsField K) (W : Subspace ι K) (S : ι → Prop) (j : ι)
    (hS : ∀ x, x ∈ W → x ∈ coord S → x = 0) (hj : ¬ Vec.basisVec j ∈ sup W (coord S)) :
    ∀ x, x ∈ W → x ∈ coord (fun a => S a ∨ a = j) → x = 0 := by
  intro x hx hxS
  have hxS' : ∀ a, ¬ (S a ∨ a = j) → x a = 0 := hxS
  let y : Vec ι K := x + -(x j • Vec.basisVec j)
  have hy : y ∈ coord S := by
    intro a ha
    show x a + -(x j * kd a j) = 0
    by_cases haj : a = j
    · subst haj; rw [kd_self]; grind
    · rw [kd_ne haj, hxS' a (by rintro (h | h) <;> contradiction)]; grind
  by_cases hxj : x j = 0
  · apply hS x hx
    have : y = x := Vec.ext fun a => by
      show x a + -(x j * kd a j) = x a; rw [hxj]; grind
    rw [← this]; exact hy
  · obtain ⟨t, ht⟩ := hF.2 _ hxj
    exfalso; apply hj
    refine ⟨t • x, t • -y, W.smul_mem t hx, (coord S).smul_mem t ((coord S).neg_mem hy),
      Vec.ext fun a => ?_⟩
    show kd a j = t * x a + t * -(x a + -(x j * kd a j))
    grind

/-- **Every subspace of `K^ι` has a complement** (not necessarily invariant): a coordinate
subspace spanned by standard basis vectors, chosen greedily. -/
theorem exists_compl (hF : IsField K) (W : Subspace ι K) : ∃ C : Subspace ι K, IsCompl W C := by
  have key : ∀ l : List ι, ∃ S : ι → Prop, (∀ x, x ∈ W → x ∈ coord S → x = 0) ∧
      ∀ j ∈ l, Vec.basisVec j ∈ sup W (coord S) := by
    intro l
    induction l with
    | nil =>
      refine ⟨fun _ => False, fun x _ hx => Vec.ext fun a => hx a id, fun j hj => ?_⟩
      exact absurd hj List.not_mem_nil
    | cons j l ih =>
      obtain ⟨S, hS, hl⟩ := ih
      by_cases hj : Vec.basisVec j ∈ sup W (coord S)
      · refine ⟨S, hS, fun j' hj' => ?_⟩
        rcases List.mem_cons.1 hj' with rfl | h
        · exact hj
        · exact hl j' h
      · refine ⟨fun a => S a ∨ a = j, disjoint_step hF W S j hS hj, fun j' hj' => ?_⟩
        rcases List.mem_cons.1 hj' with rfl | h
        · refine ⟨0, _, W.zero_mem, ?_, (AddAbGroup.zero_add _).symm⟩
          intro a ha
          exact kd_ne (fun h => ha (Or.inr h))
        · obtain ⟨w, c, hw, hc, he⟩ := hl j' h
          exact ⟨w, c, hw, fun a ha => hc a (fun h => ha (Or.inl h)), he⟩
  obtain ⟨S, hS, hall⟩ := key elems
  refine ⟨coord S, hS, fun x => ?_⟩
  have : x ∈ sup W (coord S) := by
    rw [Vec.eq_isum_basisVec x]
    exact (sup W (coord S)).isum_mem fun j =>
      (sup W (coord S)).smul_mem _ (hall j (complete j))
  exact this

/-! ## Projections -/

section Projection

variable {W C : Subspace ι K} (h : IsCompl W C)

/-- The **projection onto `W` along `C`**, for complementary `W` and `C`. -/
noncomputable def proj (x : Vec ι K) : Vec ι K := Classical.choose (h.2 x)

/-- The projection lands in `W`, with remainder in `C`. -/
theorem proj_spec (x : Vec ι K) :
    proj h x ∈ W ∧ ∃ c, c ∈ C ∧ x = proj h x + c := by
  obtain ⟨c, hw, hc, he⟩ := Classical.choose_spec (h.2 x)
  exact ⟨hw, c, hc, he⟩

/-- **Uniqueness of the decomposition** `x = w + c`. -/
theorem proj_unique {x w c : Vec ι K} (hw : w ∈ W) (hc : c ∈ C) (hx : x = w + c) :
    proj h x = w := by
  obtain ⟨hp, c', hc', he⟩ := proj_spec h x
  have hd : proj h x + -w = c + -c' := by
    have e : proj h x + c' = w + c := he.symm.trans hx
    have : proj h x + c' + -w + -c' = w + c + -w + -c' := by rw [e]
    calc proj h x + -w = proj h x + c' + -w + -c' := by
          rw [AddAbGroup.add_assoc (proj h x) c', AddAbGroup.add_comm c' (-w),
            AddAbGroup.add_assoc, AddAbGroup.add_assoc, AddAbGroup.add_neg_cancel,
            AddAbGroup.add_zero]
      _ = w + c + -w + -c' := this
      _ = c + -c' := by
          rw [AddAbGroup.add_comm w c, AddAbGroup.add_assoc c, AddAbGroup.add_neg_cancel,
            AddAbGroup.add_zero]
  have h0 := h.1 _ (W.add_mem hp (W.neg_mem hw)) (hd ▸ C.add_mem hc (C.neg_mem hc'))
  have := congrArg (· + w) h0
  simp only [AddAbGroup.zero_add, AddAbGroup.add_assoc, AddAbGroup.neg_add_cancel,
    AddAbGroup.add_zero] at this
  exact this

/-- The projection fixes `W`. -/
theorem proj_of_mem {w : Vec ι K} (hw : w ∈ W) : proj h w = w :=
  proj_unique h hw C.zero_mem (AddAbGroup.add_zero w).symm

/-- The projection is additive. -/
theorem proj_add (x y : Vec ι K) : proj h (x + y) = proj h x + proj h y := by
  obtain ⟨hx, c, hc, ex⟩ := proj_spec h x
  obtain ⟨hy, d, hd, ey⟩ := proj_spec h y
  refine proj_unique h (W.add_mem hx hy) (C.add_mem hc hd) ?_
  conv => lhs; rw [ex, ey]
  ac_rfl

/-- The projection commutes with scalars. -/
theorem proj_smul (a : K) (x : Vec ι K) : proj h (a • x) = a • proj h x := by
  obtain ⟨hx, c, hc, ex⟩ := proj_spec h x
  refine proj_unique h (W.smul_mem a hx) (C.smul_mem a hc) ?_
  conv => lhs; rw [ex]
  exact VectorSpace.smul_add a _ _

end Projection

/-! ## Averaging over the group -/

variable {G : Type u} [Group G] [FiniteType G]

/-- A sum of a constant vector: `Σₐ v = |α| • v`. -/
theorem isum_const_vec {α : Type u} [FiniteType α] (v : Vec ι K) :
    isum (fun _ : α => v) = (ncast (card α) : K) • v :=
  Vec.ext fun i => by rw [Vec.isum_apply]; exact isum_const (v i)

/-- **Reindexing a sum over a group** by left multiplication: `Σ_g F(g) = Σ_g F(hg)`. -/
theorem isum_mul_left_reindex {A : Type w} [AddAbGroup A] (h : G) (F : G → A) :
    isum (fun g => F (h * g)) = isum F :=
  isum_comp_bij (h * ·) (fun _ _ e => Group.mul_left_cancel e)
    (fun y => ⟨h⁻¹ * y, Group.mul_inv_cancel_left h y⟩) F

section Averaging

variable (ρ : Rep G K ι) (P : Vec ι K → Vec ι K) (t : K)

/-- The **average** `t · Σ_g ρ(g) P(ρ(g⁻¹) x)` of a map `P` over the group (with `t = |G|⁻¹`
in applications). -/
def average (x : Vec ι K) : Vec ι K := t • isum (fun g => ρ g *ᵥ P (ρ g⁻¹ *ᵥ x))

/-- **The average is equivariant**: `Q(ρ(h) x) = ρ(h) Q(x)`. -/
theorem average_equivariant (h : G) (x : Vec ι K) :
    average ρ P t (ρ h *ᵥ x) = ρ h *ᵥ average ρ P t x := by
  unfold average
  rw [mulVec_smul, mulVec_isum, ← isum_mul_left_reindex h]
  congr 1; apply isum_congr; intro g
  rw [ρ.act_mul, Group.mul_inv_rev, ρ.act_mul, ρ.act_inv_act]

/-- The average of an additive map is additive. -/
theorem average_add (hP : ∀ x y, P (x + y) = P x + P y) (x y : Vec ι K) :
    average ρ P t (x + y) = average ρ P t x + average ρ P t y := by
  unfold average
  rw [← VectorSpace.smul_add, ← isum_add]
  congr 1; apply isum_congr; intro g
  rw [mulVec_add, hP, mulVec_add]

/-- The average of a homogeneous map is homogeneous. -/
theorem average_smul (hP : ∀ (a : K) x, P (a • x) = a • P x) (a : K) (x : Vec ι K) :
    average ρ P t (a • x) = a • average ρ P t x := by
  unfold average
  rw [← VectorSpace.mul_smul, CommRing.mul_comm, VectorSpace.mul_smul, VectorSpace.smul_isum a]
  congr 1; congr 1; funext g
  rw [mulVec_smul, hP, mulVec_smul]

end Averaging

/-- **Maschke's theorem.** Let `G` be a finite group and `K` a field in which `|G| ≠ 0`
(e.g. any field of characteristic zero). Then every subrepresentation `W` of a representation
`ρ` of `G` has an invariant complement `W'`: `K^ι = W ⊕ W'` as representations. -/
theorem maschke (hF : IsField K) (hG : (ncast (card G) : K) ≠ 0) (ρ : Rep G K ι)
    (W : Subspace ι K) (hW : Invariant ρ W) :
    ∃ W' : Subspace ι K, Invariant ρ W' ∧ IsCompl W W' := by
  obtain ⟨C, hC⟩ := exists_compl hF W
  obtain ⟨t, ht⟩ := hF.2 _ hG
  have hadd : ∀ x y, average ρ (proj hC) t (x + y) =
      average ρ (proj hC) t x + average ρ (proj hC) t y :=
    average_add ρ (proj hC) t (proj_add hC)
  have hsmul : ∀ (a : K) x, average ρ (proj hC) t (a • x) = a • average ρ (proj hC) t x :=
    average_smul ρ (proj hC) t (proj_smul hC)
  have hmem : ∀ x, average ρ (proj hC) t x ∈ W := fun x =>
    W.smul_mem t (W.isum_mem fun g => hW g _ (proj_spec hC _).1)
  have hfix : ∀ w, w ∈ W → average ρ (proj hC) t w = w := by
    intro w hw
    show t • isum (fun g => ρ g *ᵥ proj hC (ρ g⁻¹ *ᵥ w)) = w
    rw [isum_congr (fun g => show ρ g *ᵥ proj hC (ρ g⁻¹ *ᵥ w) = w by
      rw [proj_of_mem hC (hW _ _ hw), ρ.act_act_inv]), isum_const_vec,
      ← VectorSpace.mul_smul, CommRing.mul_comm, ht, VectorSpace.one_smul]
  have hneg : ∀ x, average ρ (proj hC) t (-x) = -average ρ (proj hC) t x := fun x => by
    rw [← VectorSpace.one_smul (K := K) x, ← VectorSpace.neg_smul, hsmul,
      VectorSpace.neg_smul, VectorSpace.one_smul, VectorSpace.one_smul]
  let W' : Subspace ι K :=
    { carrier := fun x => average ρ (proj hC) t x = 0
      zero_mem := by
        show average ρ (proj hC) t 0 = 0
        have := hsmul 0 0; rwa [VectorSpace.zero_smul, VectorSpace.zero_smul] at this
      add_mem := fun hx hy => by
        show average ρ (proj hC) t _ = 0
        rw [hadd, show average ρ (proj hC) t _ = 0 from hx,
          show average ρ (proj hC) t _ = 0 from hy]
        exact AddAbGroup.zero_add 0
      smul_mem := fun a x hx => by
        show average ρ (proj hC) t _ = 0
        rw [hsmul, show average ρ (proj hC) t x = 0 from hx]; exact VectorSpace.smul_zero a }
  refine ⟨W', fun g x hx => ?_, fun x hx hx' => ?_, fun x => ?_⟩
  · show average ρ (proj hC) t (ρ g *ᵥ x) = 0
    rw [average_equivariant, show average ρ (proj hC) t x = 0 from hx, mulVec_zero]
  · rw [← hfix x hx]; exact hx'
  · refine ⟨average ρ (proj hC) t x, x + -average ρ (proj hC) t x, hmem x, ?_, ?_⟩
    · show average ρ (proj hC) t (x + -average ρ (proj hC) t x) = 0
      rw [hadd, hneg, hfix _ (hmem x), AddAbGroup.add_neg_cancel]
    · rw [AddAbGroup.add_comm x, ← AddAbGroup.add_assoc, AddAbGroup.add_neg_cancel,
        AddAbGroup.zero_add]

/-- A finite group has at least one element, so `|G| = n + 1` for some `n`. -/
theorem card_group_pos : 0 < card G :=
  List.length_pos_of_mem (complete (1 : G))

/-- **Maschke's theorem over `ℂ`.** Every subrepresentation of a complex representation of a
finite group has an invariant complement. -/
theorem maschke_complex (ρ : Rep G C ι) (W : Subspace ι C) (hW : Invariant ρ W) :
    ∃ W' : Subspace ι C, Invariant ρ W' ∧ IsCompl W W' := by
  refine maschke C.isField ?_ ρ W hW
  obtain ⟨n, hn⟩ : ∃ n, card G = n + 1 := ⟨card G - 1, by have := card_group_pos (G := G); omega⟩
  rw [hn]; exact C.ncast_succ_ne_zero n

/-- **Complete reducibility, one step.** Over a field with `|G| ≠ 0`, a representation on a
non-zero space that is not irreducible splits as `W ⊕ W'` with `W`, `W'` non-zero
subrepresentations. -/
theorem split_of_not_irreducible (hF : IsField K) (hG : (ncast (card G) : K) ≠ 0)
    (ρ : Rep G K ι) (hne : Nonempty ι) (hred : ¬ Irreducible ρ) :
    ∃ W W' : Subspace ι K, Invariant ρ W ∧ Invariant ρ W' ∧ IsCompl W W' ∧
      ¬ W.IsZero ∧ ¬ W'.IsZero := by
  have : ∃ W, Invariant ρ W ∧ ¬ W.IsZero ∧ ¬ W.IsTop :=
    Classical.byContradiction fun hno => hred ⟨hne, fun W hW =>
      Classical.byCases (p := W.IsZero) Or.inl fun h0 =>
        Or.inr (Classical.byContradiction fun ht => hno ⟨W, hW, h0, ht⟩)⟩
  obtain ⟨W, hW, h0, htop⟩ := this
  obtain ⟨W', hW', hc⟩ := maschke hF hG ρ W hW
  refine ⟨W, W', hW, hW', hc, h0, fun h0' => htop fun x => ?_⟩
  obtain ⟨w, w', hw, hw', rfl⟩ := hc.2 x
  rw [h0' w' hw', AddAbGroup.add_zero]; exact hw

end Foundations.Langlands
