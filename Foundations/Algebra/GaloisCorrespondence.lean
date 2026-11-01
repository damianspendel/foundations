import Foundations.Algebra.FieldAut

/-!
# Artin's theorem and the Galois correspondence

The **fundamental theorem of Galois theory** matches the intermediate fields of a Galois
extension `L/K` with the subgroups of its Galois group, by `M ↦ Aut(L/M)` and `H ↦ Fix(H)`.
The modern proof, due to Emil Artin (1938, *Galois Theory*), rests on a single theorem:

**Artin's theorem.** If `H` is a finite group of `n` automorphisms of a field `L`, then
`[L : Fix(H)] = n`.

Dedekind's lemma (previous file) gives `n ≤ [L : Fix(H)]`. For the reverse inequality, Artin
shows that any `m > n` elements `a₁, …, aₘ` of `L` are dependent over `Fix(H)`. The linear
system `∑ⱼ σᵢ(aⱼ) yⱼ = 0` (one equation for each `σᵢ ∈ H`) has a non-zero solution. Choose one
with as few non-zero entries as possible, scaled so that some entry equals `1`. Applying any
`τ ∈ H` only permutes the equations, so `τ(y)` is again a solution, and `τ(y) - y` is a solution
with fewer non-zero entries. Hence `τ(y) = y` for every `τ`, so all `yⱼ` lie in `Fix(H)`, and
the equation for `σ = id` reads `∑ aⱼ yⱼ = 0`.

**What is proved here.** For a finite group `H = {σ₁, …, σₙ}` of automorphisms of `L` over
`K` (a family of distinct automorphisms containing the identity and closed under composition):

* `[L : Fix(H)] = n` (`artin`);
* `Aut(L / Fix(H)) = H` (`aut_fixedField`): every automorphism of `L` fixing `Fix(H)` is one of
  the `σᵢ`;
* hence `H ↦ Fix(H)` is **injective** on finite subgroups (`fixedField_injective`) and
  inclusion-reversing (`fixedField_anti`, previous file).

For a **Galois** extension (defined as `|Aut(L/K)| = [L : K]`):

* `Fix(Aut(L/K)) = K` (`galois_fixedField`).

**What remains.** For the full bijection one must also show that every intermediate field `M`
is `Fix(Aut(L/M))`, which needs `L/M` to be Galois again (via splitting fields and
separability). That, and the correspondence between normal subgroups and normal
subextensions, are not formalised here.
-/

namespace Foundations.Algebra

open Ring FiniteType VectorSpace Subfield KSubspace

universe u v w

/-! ## Two lemmas of linear algebra -/

section LinearAlgebra

variable {K : Type u} {V : Type v} [CommRing K] [AddAbGroup V] [VectorSpace K V]

/-- **A bound on independent families gives finite dimension.** If no `n + 1` vectors are
linearly independent, then `V` is finite-dimensional of dimension at most `n`. -/
theorem finDim_of_no_indep (hF : IsField K) (n : Nat) (h : ¬ ∃ u : Fin (n + 1) → V, LinIndep K u) :
    FinDim K V ∧ dim K V ≤ n := by
  have hex : ∃ m, ¬ ∃ u : Fin (m + 1) → V, LinIndep K u := ⟨n, h⟩
  obtain ⟨m, hm, hmin⟩ := FiniteType.exists_least _ hex
  have hfam : ∃ u : Fin m → V, LinIndep K u := by
    rcases m with _ | k
    · exact ⟨fun i => absurd i.isLt (Nat.not_lt_zero _), linIndep_empty _⟩
    · exact Classical.byContradiction fun hno => hmin k (Nat.lt_succ_self k) hno
  obtain ⟨u, hu⟩ := hfam
  have hspan : Spans K u := fun x =>
    Classical.byContradiction fun hx => hm ⟨_, linIndep_tcons hF hu hx⟩
  have hfin := finDim_of_spans hspan
  refine ⟨hfin, ?_⟩
  have h1 := dim_le_card hF hfin hspan
  rw [card_fin] at h1
  have h2 : m ≤ n := Nat.le_of_not_lt fun hlt => hmin n hlt h
  omega

end LinearAlgebra

/-- A sum in which only the term at `a` can be non-zero (any universe of index type). -/
theorem isum_single' {A : Type u} [AddAbGroup A] {ι : Type v} [FiniteType ι] (f : ι → A) (a : ι)
    (hf : ∀ i, i ≠ a → f i = 0) : isum f = f a := by
  classical
  have key : ∀ l : List ι, l.Nodup → lsum (l.map f) = if a ∈ l then f a else 0 := by
    intro l hl
    induction l with
    | nil => simp [lsum]
    | cons b l ih =>
      rw [List.nodup_cons] at hl
      show f b + lsum (l.map f) = _
      rw [ih hl.2]
      by_cases hb : b = a
      · subst hb; simp [hl.1, AddAbGroup.add_zero]
      · rw [hf b hb, AddAbGroup.zero_add]
        by_cases ha : a ∈ l
        · simp [ha]
        · have : a ∉ b :: l := by simp [ha, Ne.symm hb]
          simp [ha, this]
  unfold isum
  rw [key _ nodup]
  simp [complete]

variable {Ω : Type u} [CommRing Ω]

/-! ## Artin's theorem -/

section Artin

variable {K L : Subfield Ω} {n : Nat} (σ : Fin n → FieldAut K L)

/-- The fixed field of the family `σ`, `Fix(H)` for `H = {σ₁, …, σₙ}`. -/
def famFix : Subfield Ω := fixedField L (fun τ => ∃ i, σ i = τ)

/-- `Fix(H) ⊆ L`. -/
theorem famFix_le : (famFix σ).le L := fixedField_le _

/-- **Artin's key lemma.** If `H = {σ₁, …, σₙ}` is a finite group of automorphisms of `L`
(distinct, containing the identity, closed under composition), then any `m > n` elements of `L`
are linearly dependent over `Fix(H)`. -/
theorem artin_dependent (hΩ : IsField Ω) (hdist : ∀ i j, σ i = σ j → i = j)
    (hone : ∃ i, σ i = 1) (hmul : ∀ i j, ∃ k, σ k = σ i * σ j) {m : Nat} (a : Fin m → L)
    (hmn : n < m) :
    ∃ c : Fin m → L, (∃ j, c j ≠ 0) ∧ (∀ j, (c j).1 ∈ famFix σ) ∧
      isum (fun j => c j * a j) = 0 := by
  have hFL := L.isField hΩ
  -- Solutions of the system `∑ⱼ σᵢ(aⱼ) yⱼ = 0`.
  let Sol : (Fin m → L) → Prop := fun y => ∀ i, isum (fun j => (σ i).toFun (a j) * y j) = 0
  obtain ⟨y0, hy0, hsol0⟩ := exists_nontrivial_solution hFL m n (fun i j => (σ i).toFun (a j)) hmn
  -- A non-zero solution with the fewest non-zero entries.
  obtain ⟨s, ⟨y, hy, ⟨j0, hj0⟩, hs⟩, hmin⟩ := FiniteType.exists_least
    (fun s => ∃ y, Sol y ∧ (∃ j, y j ≠ 0) ∧ count (fun j => y j ≠ 0) = s)
    ⟨_, y0, hsol0, hy0, rfl⟩
  -- Normalise so that the entry at `j0` is `1`.
  obtain ⟨w, hw⟩ := hFL.2 _ hj0
  have hw0 : w ≠ 0 := fun h => hFL.1 (by rw [← hw, h, Ring.mul_zero])
  let y' : Fin m → L := fun j => w * y j
  have hy'sol : Sol y' := by
    intro i
    have := hy i
    calc isum (fun j => (σ i).toFun (a j) * y' j)
        = w * isum (fun j => (σ i).toFun (a j) * y j) := by
          rw [isum_mul_left]; congr 1; funext j; show _ * (w * y j) = _; grind
      _ = 0 := by rw [this, Ring.mul_zero]
  have hy'j0 : y' j0 = 1 := by show w * y j0 = 1; rw [CommRing.mul_comm]; exact hw
  have hsupp : ∀ j, y' j ≠ 0 ↔ y j ≠ 0 := by
    intro j
    constructor
    · intro h h0; apply h; show w * y j = 0; rw [h0, Ring.mul_zero]
    · intro h h0
      rcases hFL.isDomain.2 _ _ h0 with h1 | h1
      · exact hw0 h1
      · exact h h1
  have hs' : count (fun j => y' j ≠ 0) = s := by rw [← hs]; exact count_congr hsupp
  -- Every `τ ∈ H` fixes `y'`.
  have hfix : ∀ k j, (σ k).toFun (y' j) = y' j := by
    intro k
    let τ := σ k
    -- Left multiplication by `τ` permutes `H`.
    let π : Fin n → Fin n := fun i => Classical.choose (hmul k i)
    have hπ : ∀ i, σ (π i) = τ * σ i := fun i => Classical.choose_spec (hmul k i)
    have hπinj : ∀ i i', π i = π i' → i = i' := by
      intro i i' h
      apply hdist
      apply Group.mul_left_cancel (a := τ)
      rw [← hπ, ← hπ, h]
    have hπsurj := surjective_of_injective π hπinj
    let z : Fin m → L := fun j => τ.toFun (y' j) + -y' j
    have hzsol : Sol z := by
      intro i
      obtain ⟨i', hi'⟩ := hπsurj i
      have hrow : isum (fun j => (σ i).toFun (a j) * τ.toFun (y' j)) = 0 := by
        calc isum (fun j => (σ i).toFun (a j) * τ.toFun (y' j))
            = τ.toFun (isum (fun j => (σ i').toFun (a j) * y' j)) := by
              rw [FieldAut.map_isum]; congr 1; funext j
              rw [← hi', hπ]; exact (τ.map_mul _ _).symm
          _ = 0 := by rw [hy'sol i', τ.map_zero]
      calc isum (fun j => (σ i).toFun (a j) * z j)
          = isum (fun j => (σ i).toFun (a j) * τ.toFun (y' j)) +
              -isum (fun j => (σ i).toFun (a j) * y' j) := by
            rw [← isum_neg, ← isum_add]; congr 1; funext j; show _ * (_ + -_) = _; grind
        _ = 0 := by rw [hrow, hy'sol i, Ring.zero_add, neg_zero]
    have hzsub : ∀ j, z j ≠ 0 → y' j ≠ 0 := by
      intro j hz hy0'
      apply hz
      show τ.toFun (y' j) + -y' j = 0
      rw [hy0', τ.map_zero, Ring.add_neg_cancel]
    have hzj0 : z j0 = 0 := by
      show τ.toFun (y' j0) + -y' j0 = 0
      rw [hy'j0, τ.map_one, Ring.add_neg_cancel]
    have hzero : ∀ j, z j = 0 := by
      apply Classical.byContradiction
      intro hne
      have hex : ∃ j, z j ≠ 0 := Classical.byContradiction fun h =>
        hne fun j => Classical.byContradiction fun hj => h ⟨j, hj⟩
      have hlt : count (fun j => z j ≠ 0) < s := by
        have h1 := count_split (fun j => y' j ≠ 0) (fun j => z j ≠ 0)
        have h2 : count (fun j => y' j ≠ 0 ∧ z j ≠ 0) = count (fun j => z j ≠ 0) :=
          count_congr fun j => ⟨fun h => h.2, fun h => ⟨hzsub j h, h⟩⟩
        have h3 : 0 < count (fun j => y' j ≠ 0 ∧ ¬ z j ≠ 0) :=
          count_pos.2 ⟨j0, by rw [hy'j0]; exact fun h => hFL.1 h.symm, fun h => h hzj0⟩
        omega
      exact hmin _ hlt ⟨z, hzsol, hex, rfl⟩
    intro j
    have := hzero j
    exact eq_of_sub_eq_zero this
  refine ⟨y', ⟨j0, by rw [hy'j0]; exact fun h => hFL.1 h.symm⟩, fun j => ⟨(y' j).2, ?_⟩, ?_⟩
  · intro τ ⟨k, hk⟩; rw [← hk]; exact hfix k j
  · obtain ⟨i1, hi1⟩ := hone
    have := hy'sol i1
    rw [hi1] at this
    rw [← this]; congr 1; funext j; exact CommRing.mul_comm _ _

/-- The members of `H`, viewed as automorphisms of `L` over `Fix(H)`. -/
def famOver (i : Fin n) : FieldAut (famFix σ) L :=
  (σ i).toOver fun _ ⟨_, hx⟩ => hx (σ i) ⟨i, rfl⟩

/-- **Artin's theorem.** For a finite group `H` of `n` automorphisms of `L`, the extension
`L / Fix(H)` is finite of degree exactly `n`. -/
theorem artin (hΩ : IsField Ω) (hdist : ∀ i j, σ i = σ j → i = j) (hone : ∃ i, σ i = 1)
    (hmul : ∀ i j, ∃ k, σ k = σ i * σ j) :
    FiniteExt (famFix σ) L (famFix_le σ) ∧ deg (famFix σ) L (famFix_le σ) = n := by
  let F := famFix σ
  have hFF := F.isField hΩ
  have hnone : ¬ ∃ u : Fin (n + 1) → L.over F (famFix_le σ), LinIndep F u := by
    intro ⟨u, hu⟩
    obtain ⟨c, ⟨j0, hj0⟩, hcF, hc⟩ :=
      artin_dependent σ hΩ hdist hone hmul (fun j => (⟨(u j).1, (u j).2⟩ : L)) (Nat.lt_succ_self n)
    have := hu (fun j => ⟨(c j).1, hcF j⟩) (by
      apply Subtype.ext
      rw [KSubspace.coe_isum]
      have := congrArg Subtype.val hc
      rw [Subfield.coe_isum] at this
      exact this) j0
    exact hj0 (Subtype.ext (show (c j0).1 = (0 : L).1 from congrArg (fun z : {x // x ∈ famFix σ} => z.1) this))
  obtain ⟨hfin, hle⟩ := finDim_of_no_indep hFF n hnone
  refine ⟨hfin, Nat.le_antisymm hle ?_⟩
  exact card_aut_le hΩ (famFix_le σ) hfin (famOver σ) (fun i j h => hdist i j
    (FieldAut.ext fun x => congrArg (fun τ : FieldAut F L => τ.toFun x) h))

/-- **`Aut(L / Fix(H)) = H`.** Every automorphism of `L` fixing `Fix(H)` pointwise is one of the
`σᵢ`. -/
theorem aut_fixedField (hΩ : IsField Ω) (hdist : ∀ i j, σ i = σ j → i = j) (hone : ∃ i, σ i = 1)
    (hmul : ∀ i j, ∃ k, σ k = σ i * σ j) (τ : FieldAut (famFix σ) L) :
    ∃ i, (σ i).toFun = τ.toFun := by
  apply Classical.byContradiction
  intro hno
  have hτ : ∀ i, (σ i).toFun ≠ τ.toFun := fun i h => hno ⟨i, h⟩
  obtain ⟨hfin, hdeg⟩ := artin σ hΩ hdist hone hmul
  let fam : Fin (n + 1) → FieldAut (famFix σ) L := tcons τ (famOver σ)
  have hfam : ∀ i j, fam i = fam j → i = j := by
    intro i j hij
    have e := congrArg FieldAut.toFun hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact absurd e.symm (hτ j)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd e (hτ i)
      | succ j =>
        exact congrArg Fin.succ (hdist i j (FieldAut.ext fun x => congrFun e x))
  have := card_aut_le hΩ (famFix_le σ) hfin fam hfam
  omega

/-- **The Galois correspondence is injective on finite subgroups.** Two finite groups of
automorphisms with the same fixed field have the same members. -/
theorem fixedField_injective (hΩ : IsField Ω) {m : Nat} (ρ : Fin m → FieldAut K L)
    (hdist : ∀ i j, σ i = σ j → i = j) (hone : ∃ i, σ i = 1)
    (hmul : ∀ i j, ∃ k, σ k = σ i * σ j)
    (hsame : ∀ x, x ∈ famFix σ ↔ x ∈ famFix ρ) : ∀ j, ∃ i, σ i = ρ j := by
  intro j
  let τ : FieldAut (famFix σ) L := (ρ j).toOver fun x hx => by
    obtain ⟨_, h⟩ := (hsame x.1).1 hx
    exact h (ρ j) ⟨j, rfl⟩
  obtain ⟨i, hi⟩ := aut_fixedField σ hΩ hdist hone hmul τ
  exact ⟨i, FieldAut.ext fun x => congrFun hi x⟩

end Artin

/-! ## Galois extensions -/

/-- A finite extension `L/K` is **Galois** if it has exactly `[L : K]` automorphisms: there is
an enumeration of `Aut(L/K)` without repetitions of length `[L : K]`. -/
def IsGalois (K L : Subfield Ω) (hKL : K.le L) : Prop :=
  FiniteExt K L hKL ∧ ∃ (n : Nat) (σ : Fin n → FieldAut K L), (∀ i j, σ i = σ j → i = j) ∧
    (∀ τ, ∃ i, σ i = τ) ∧ n = deg K L hKL

/-- **Equal degrees force equality.** If `K ⊆ F ⊆ L` and `[L : F] = [L : K]` (both finite), then
`F = K`. (Proof: a basis of `L` over `F` is independent over `K` and has the right size, hence
is a basis over `K`; comparing coordinates of `f · b` in the two bases shows `f ∈ K`.) -/
theorem le_of_deg_eq (hΩ : IsField Ω) {K F L : Subfield Ω} (hKF : K.le F) (hFL : F.le L)
    (hKL : K.le L) (hfinK : FiniteExt K L hKL) (hfinF : FiniteExt F L hFL)
    (h : deg F L hFL = deg K L hKL) : F.le K := by
  have hFK := K.isField hΩ
  have hFF := F.isField hΩ
  obtain ⟨b, hb⟩ := exists_basis hFF hfinF
  let bK : Fin (deg F L hFL) → L.over K hKL := fun j => ⟨(b j).1, (b j).2⟩
  have hindK : LinIndep K bK := by
    intro c hc j
    have := hb.1 (fun j => ⟨(c j).1, hKF _ (c j).2⟩) (by
      apply Subtype.ext
      rw [KSubspace.coe_isum]
      have := congrArg Subtype.val hc
      rw [KSubspace.coe_isum] at this
      exact this) j
    exact Subtype.ext (show (c j).1 = (0 : K).1 from congrArg (fun z : {x // x ∈ F} => z.1) this)
  have hspanK := spans_of_card_eq_dim hFK hfinK hindK (by rw [card_fin]; exact h)
  -- `[L : F] ≥ 1`, since `1 ≠ 0` in `L`.
  have hpos : 0 < deg F L hFL := by
    apply Nat.pos_of_ne_zero
    intro h0
    have h0' : dim F (L.over F hFL) = 0 := h0
    obtain ⟨c, hc⟩ := hb.2 ⟨1, (show (L.over F hFL).carrier 1 from L.one_mem)⟩
    have h1 : (1 : Ω) = isum (fun j => (c j • b j).1) := by
      have := congrArg Subtype.val hc; rw [KSubspace.coe_isum] at this; exact this
    rw [isum_eq_zero (fun j => absurd j.isLt (by omega))] at h1
    exact hΩ.1 h1.symm
  let j0 : Fin (deg F L hFL) := ⟨0, hpos⟩
  intro f hf
  obtain ⟨k, hk⟩ := hspanK ⟨f * (b j0).1, L.mul_mem (hFL _ hf) (b j0).2⟩
  have hkv : f * (b j0).1 = isum (fun j => (k j).1 * (b j).1) := by
    have := congrArg Subtype.val hk; rw [KSubspace.coe_isum] at this; exact this
  classical
  let d : Fin (deg F L hFL) → F := fun j =>
    ⟨(if j = j0 then f else 0) + -(k j).1,
      F.add_mem (by split
                    · exact hf
                    · exact F.zero_mem) (F.neg_mem (hKF _ (k j).2))⟩
  have hd := hb.1 d (by
    apply Subtype.ext
    rw [KSubspace.coe_isum]
    show isum (fun j => ((if j = j0 then f else 0) + -(k j).1) * (b j).1) = 0
    have e : (fun j : Fin (deg F L hFL) => ((if j = j0 then f else 0) + -(k j).1) * (b j).1) =
        fun j => (if j = j0 then f else 0) * (b j).1 + -((k j).1 * (b j).1) := by
      funext j; grind
    rw [e, isum_add, isum_neg, ← hkv,
      isum_single' _ j0 (fun j hj => by rw [ite_false_of hj, Ring.zero_mul]),
      ite_true_of rfl, Ring.add_neg_cancel]) j0
  have hd' : (if j0 = j0 then f else 0) + -(k j0).1 = 0 := congrArg Subtype.val hd
  rw [ite_true_of rfl] at hd'
  rw [eq_of_sub_eq_zero hd']
  exact (k j0).2

/-- **The fixed field of the Galois group is the base field.** If `L/K` is Galois, then the
elements of `L` fixed by every automorphism in `Aut(L/K)` are exactly the elements of `K`. -/
theorem galois_fixedField (hΩ : IsField Ω) {K L : Subfield Ω} (hKL : K.le L)
    (hG : IsGalois K L hKL) : ∀ x, x ∈ fixedField L (fun _ : FieldAut K L => True) → x ∈ K := by
  obtain ⟨hfin, n, σ, hdist, hall, hn⟩ := hG
  have hone : ∃ i, σ i = 1 := hall 1
  have hmul : ∀ i j, ∃ k, σ k = σ i * σ j := fun i j => hall _
  obtain ⟨hfinF, hdeg⟩ := artin σ hΩ hdist hone hmul
  have hKF : K.le (famFix σ) := le_fixedField hKL _
  have hle := le_of_deg_eq hΩ hKF (famFix_le σ) hKL hfin hfinF (by rw [hdeg, hn])
  intro x ⟨hx, hfx⟩
  exact hle x ⟨hx, fun τ _ => hfx τ trivial⟩

/-- **Galois correspondence (the part formalised here).** For a Galois extension `L/K` with
Galois group enumerated as `σ₁, …, σₙ`:
* `[L : Fix(G)] = |G| = [L : K]` and `Fix(G) = K`;
* for every finite subgroup `H` (given as a family `ρ`), `[L : Fix(H)] = |H|` and
  `Aut(L/Fix(H)) = H`. -/
theorem galois_correspondence (hΩ : IsField Ω) {K L : Subfield Ω} (hKL : K.le L)
    (hG : IsGalois K L hKL) :
    (∀ x, x ∈ fixedField L (fun _ : FieldAut K L => True) → x ∈ K) ∧
    ∀ {m : Nat} (ρ : Fin m → FieldAut K L), (∀ i j, ρ i = ρ j → i = j) → (∃ i, ρ i = 1) →
      (∀ i j, ∃ k, ρ k = ρ i * ρ j) →
      deg (famFix ρ) L (famFix_le ρ) = m ∧ ∀ τ : FieldAut (famFix ρ) L, ∃ i, (ρ i).toFun = τ.toFun :=
  ⟨galois_fixedField hΩ hKL hG, fun ρ hd ho hm =>
    ⟨(artin ρ hΩ hd ho hm).2, aut_fixedField ρ hΩ hd ho hm⟩⟩

end Foundations.Algebra
