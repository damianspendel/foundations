import Foundations.Langlands.Rep.Permutation

/-!
# Complete reducibility

Maschke's theorem gives, for every subrepresentation `W ⊆ K^ι`, an invariant complement `W'`.
To turn this into the statement that *every representation is isomorphic to a direct sum of
irreducible representations*, the two pieces must become representations in their own right.
Choose bases `b₁, …, b_d` of `W` and `b'₁, …, b'_e` of `W'`. Together they form a basis of
`K^ι`, that is an invertible matrix `T = [b | b']`. Conjugating by it, `σ(g) = T⁻¹ ρ(g) T` is
block diagonal, because `W` and `W'` are invariant, and its two blocks are the
**restrictions** `ρ|_W` and `ρ|_{W'}`. So `ρ ≅ ρ|_W ⊕ ρ|_{W'}`, both of smaller degree, and
induction on the degree finishes the proof. This is the complete reducibility which Maschke
(1899) derived from his theorem, and which Frobenius and Burnside had used for the regular
representation.

Bases of subspaces are built greedily: keep adding a vector of `W` outside the current span,
which keeps the family independent (`linIndep_tcons`). The process stops because an
independent family in `K^ι` has at most `|ι|` members (the Steinitz exchange lemma of
`Algebra/VectorSpace`).

Index types in this file live in `Type`. A *sum of irreducibles* is recorded by the inductive
predicate `SumIrr`: irreducible representations, and direct sums of two such.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace

set_option linter.unusedSectionVars false

universe u w

variable {K : Type w} [CommRing K]

/-! ## Bases of subspaces -/

section Bases

variable {ι : Type} [FiniteType ι]

/-- The standard basis vectors span `K^ι`. -/
theorem spans_basisVec : Spans K (fun j : ι => (Vec.basisVec j : Vec ι K)) :=
  fun x => ⟨fun j => x j, Vec.eq_isum_basisVec x⟩

/-- An independent family in `K^ι` has at most `|ι|` members. -/
theorem card_le_of_linIndep (hF : IsField K) {α : Type} [FiniteType α] {u : α → Vec ι K}
    (hu : LinIndep K u) : card α ≤ card ι :=
  steinitz hF u (fun j : ι => Vec.basisVec j) hu (fun i => spans_basisVec (u i))

/-- **Every subspace of `K^ι` has a basis.** -/
theorem exists_basis_subspace (hF : IsField K) (W : Subspace ι K) :
    ∃ d, ∃ b : Fin d → Vec ι K, (∀ j, b j ∈ W) ∧ LinIndep K b ∧ ∀ w, w ∈ W → InSpan K b w := by
  have key : ∀ m k (b : Fin k → Vec ι K), (∀ j, b j ∈ W) → LinIndep K b → card ι ≤ k + m →
      ∃ d, ∃ b : Fin d → Vec ι K, (∀ j, b j ∈ W) ∧ LinIndep K b ∧
        ∀ w, w ∈ W → InSpan K b w := by
    intro m
    induction m with
    | zero =>
      intro k b hb hi hk
      refine ⟨k, b, hb, hi, fun w _ => Classical.byContradiction fun hn => ?_⟩
      have := card_le_of_linIndep hF (linIndep_tcons hF hi hn)
      rw [card_fin] at this; omega
    | succ m ih =>
      intro k b hb hi hk
      by_cases h : ∀ w, w ∈ W → InSpan K b w
      · exact ⟨k, b, hb, hi, h⟩
      · obtain ⟨w, hw, hn⟩ : ∃ w, w ∈ W ∧ ¬ InSpan K b w :=
          Classical.byContradiction fun hno => h fun w hw =>
            Classical.byContradiction fun hn => hno ⟨w, hw, hn⟩
        refine ih (k + 1) (tcons w b) (fun j => ?_) (linIndep_tcons hF hi hn) (by omega)
        match j with
        | ⟨0, _⟩ => exact hw
        | ⟨_ + 1, _⟩ => exact hb _
  exact key (card ι) 0 (fun i => i.elim0) (fun j => j.elim0) (linIndep_empty _) (by omega)

/-- A basis of a non-zero subspace is non-empty. -/
theorem pos_of_basis {W : Subspace ι K} (hW : ¬ W.IsZero) {d : Nat} {b : Fin d → Vec ι K}
    (hs : ∀ w, w ∈ W → InSpan K b w) : 0 < d := by
  apply Nat.pos_of_ne_zero; rintro rfl
  exact hW fun w hw => by
    obtain ⟨c, rfl⟩ := hs w hw; exact isum_fin_zero _

/-- The matrix whose columns are the vectors of two families. -/
def colMat {d e : Nat} (b : Fin d → Vec ι K) (b' : Fin e → Vec ι K) : Mat ι (Fin d ⊕ Fin e) K :=
  fun i a => Sum.elim b b' a i

/-- The vector of `ι ⊕ κ` with blocks `α` and `β`. -/
def vecSum {α β : Type} (x : α → K) (y : β → K) : Vec (α ⊕ β) K := fun a => Sum.elim x y a

/-- `[b | b'] c = Σⱼ c_j b_j + Σₖ c'_k b'_k`. -/
theorem colMat_mulVec {d e : Nat} (b : Fin d → Vec ι K) (b' : Fin e → Vec ι K)
    (c : Vec (Fin d ⊕ Fin e) K) :
    colMat b b' *ᵥ c = isum (fun j => c (.inl j) • b j) + isum (fun k => c (.inr k) • b' k) := by
  apply Vec.ext; intro i
  rw [mulVec_apply, isum_sum, Vec.add_apply, Vec.isum_apply, Vec.isum_apply]
  congr 1 <;> exact isum_congr fun _ => CommRing.mul_comm _ _

end Bases

/-! ## Rectangular block matrices and isomorphisms -/

section Blocks

variable {ι₁ ι₂ κ₁ κ₂ μ₁ μ₂ : Type}

/-- The block matrix `diag(A, B)` for rectangular blocks `A : κ₁ × ι₁`, `B : κ₂ × ι₂`. -/
def blk (A : Mat κ₁ ι₁ K) (B : Mat κ₂ ι₂ K) : Mat (κ₁ ⊕ κ₂) (ι₁ ⊕ ι₂) K
  | .inl i, .inl j => A i j
  | .inr k, .inr l => B k l
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0

/-- Square block matrices are block-diagonal matrices. -/
theorem blockDiag_eq_blk [FiniteType ι₁] [FiniteType ι₂] (A : Mat ι₁ ι₁ K) (B : Mat ι₂ ι₂ K) :
    blockDiag A B = blk A B := ext fun a b => by cases a <;> cases b <;> rfl

/-- Block matrices multiply blockwise. -/
theorem blk_mul [FiniteType ι₁] [FiniteType ι₂] (A : Mat κ₁ ι₁ K) (B : Mat κ₂ ι₂ K)
    (C : Mat ι₁ μ₁ K) (D : Mat ι₂ μ₂ K) : blk A B * blk C D = blk (A * C) (B * D) := by
  apply ext; intro a b
  rw [mul_apply, isum_sum]
  cases a <;> cases b <;>
    simp only [blk, Ring.zero_mul, Ring.mul_zero, isum_zero, AddAbGroup.add_zero,
      AddAbGroup.zero_add] <;> rfl

end Blocks

variable {G : Type u} [Group G]

/-- Isomorphism is transitive. -/
theorem Iso.trans {ι κ μ : Type} [FiniteType ι] [FiniteType κ] [FiniteType μ]
    {ρ : Rep G K ι} {σ : Rep G K κ} {τ : Rep G K μ} (h₁ : Iso ρ σ) (h₂ : Iso σ τ) : Iso ρ τ := by
  obtain ⟨T, S, hT, hST, hTS⟩ := h₁
  obtain ⟨T', S', hT', hST', hTS'⟩ := h₂
  refine ⟨T' * T, S * S', hT.comp hT', ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc S', hST', one_mul, hST]
  · rw [mul_assoc, ← mul_assoc T, hTS, one_mul, hTS']

/-- **Direct sums respect isomorphism.** -/
theorem Iso.dsum {ι₁ ι₂ κ₁ κ₂ : Type} [FiniteType ι₁] [FiniteType ι₂] [FiniteType κ₁]
    [FiniteType κ₂] {ρ₁ : Rep G K ι₁} {ρ₂ : Rep G K ι₂} {σ₁ : Rep G K κ₁} {σ₂ : Rep G K κ₂}
    (h₁ : Iso ρ₁ σ₁) (h₂ : Iso ρ₂ σ₂) : Iso (ρ₁.dsum ρ₂) (σ₁.dsum σ₂) := by
  obtain ⟨T, S, hT, hST, hTS⟩ := h₁
  obtain ⟨T', S', hT', hST', hTS'⟩ := h₂
  refine ⟨blk T T', blk S S', fun g => ?_, ?_, ?_⟩
  · show blk T T' * blockDiag (ρ₁ g) (ρ₂ g) = blockDiag (σ₁ g) (σ₂ g) * blk T T'
    rw [blockDiag_eq_blk, blockDiag_eq_blk, blk_mul, blk_mul, hT g, hT' g]
  · rw [blk_mul, hST, hST', ← blockDiag_eq_blk, blockDiag_one]
  · rw [blk_mul, hTS, hTS', ← blockDiag_eq_blk, blockDiag_one]

/-! ## Restriction to an invariant subspace -/

section Restrict

variable {ι : Type} [FiniteType ι] (ρ : Rep G K ι) {d e : Nat} {b : Fin d → Vec ι K}
  {b' : Fin e → Vec ι K} {S : Mat (Fin d ⊕ Fin e) ι K}

/-- `S` kills the second (resp. first) coordinates of combinations of `b` (resp. `b'`). -/
theorem inv_mulVec_span (hST : S * colMat b b' = 1) {w : Vec ι K} (hw : InSpan K b w)
    (k : Fin e) : (S *ᵥ w) (.inr k) = 0 := by
  obtain ⟨α, rfl⟩ := hw
  have : isum (fun j => α j • b j) =
      colMat b b' *ᵥ vecSum α (fun _ => (0 : K)) := by
    rw [colMat_mulVec]
    show _ = isum (fun j => α j • b j) + isum (fun k => (0 : K) • b' k)
    rw [isum_eq_zero fun _ => VectorSpace.zero_smul _, AddAbGroup.add_zero]
  rw [this, mulVec_mulVec, hST, one_mulVec]; rfl

/-- See `inv_mulVec_span`. -/
theorem inv_mulVec_span' (hST : S * colMat b b' = 1) {w : Vec ι K} (hw : InSpan K b' w)
    (j : Fin d) : (S *ᵥ w) (.inl j) = 0 := by
  obtain ⟨α, rfl⟩ := hw
  have : isum (fun k => α k • b' k) =
      colMat b b' *ᵥ vecSum (fun _ => (0 : K)) α := by
    rw [colMat_mulVec]
    show _ = isum (fun j => (0 : K) • b j) + isum (fun k => α k • b' k)
    rw [isum_eq_zero fun _ => VectorSpace.zero_smul _, AddAbGroup.zero_add]
  rw [this, mulVec_mulVec, hST, one_mulVec]; rfl

variable (S) (T : Mat ι (Fin d ⊕ Fin e) K)

/-- The conjugate `S ρ(g) T` of `ρ` by `T` (with `S = T⁻¹`). -/
def conjRep (hST : S * T = 1) (hTS : T * S = 1) : Rep G K (Fin d ⊕ Fin e) where
  toFun g := S * ρ g * T
  map_one := by
    show S * ρ.toFun 1 * T = 1; rw [ρ.map_one, mul_one, hST]
  map_mul g h := by
    show S * ρ.toFun (g * h) * T = S * ρ.toFun g * T * (S * ρ.toFun h * T)
    rw [ρ.map_mul]; simp only [mul_assoc]; rw [← mul_assoc T S, hTS, one_mul]

/-- The conjugate representation is isomorphic to `ρ`. -/
theorem iso_conjRep (hST : S * T = 1) (hTS : T * S = 1) : Iso ρ (conjRep ρ S T hST hTS) :=
  ⟨S, T, fun g => by
    show S * ρ g = S * ρ g * T * S
    rw [mul_assoc (S * ρ g), hTS, mul_one], hTS, hST⟩

/-- The top-left block of a representation. -/
def topBlock (σ : Rep G K (Fin d ⊕ Fin e)) (g : G) : Mat (Fin d) (Fin d) K :=
  fun i j => σ g (.inl i) (.inl j)

/-- The bottom-right block of a representation. -/
def botBlock (σ : Rep G K (Fin d ⊕ Fin e)) (g : G) : Mat (Fin e) (Fin e) K :=
  fun i j => σ g (.inr i) (.inr j)

/-- A representation with vanishing off-diagonal blocks is block diagonal. -/
theorem eq_blockDiag {σ : Rep G K (Fin d ⊕ Fin e)}
    (h₁ : ∀ g j k, σ g (.inr k) (.inl j) = 0) (h₂ : ∀ g j k, σ g (.inl j) (.inr k) = 0) (g : G) :
    σ g = blockDiag (topBlock σ g) (botBlock σ g) :=
  ext fun a c => by
    cases a <;> cases c
    · rfl
    · exact h₂ g _ _
    · exact h₁ g _ _
    · rfl

/-- The **restriction** to the top-left block of a block-diagonal representation. -/
noncomputable def restrictTop (σ : Rep G K (Fin d ⊕ Fin e))
    (h₁ : ∀ g j k, σ g (.inr k) (.inl j) = 0) (h₂ : ∀ g j k, σ g (.inl j) (.inr k) = 0) :
    Rep G K (Fin d) where
  toFun := topBlock σ
  map_one := ext fun i j => by
    show σ.toFun 1 (.inl i) (.inl j) = kd i j
    rw [σ.map_one]; exact kd_map Sum.inl (fun _ _ h => Sum.inl.inj h) i j
  map_mul g h := ext fun i j => by
    have := congrFun (congrFun (σ.map_mul g h) (.inl i)) (.inl j)
    show σ.toFun (g * h) (.inl i) (.inl j) = _
    rw [this]
    show (σ g * σ h) (.inl i) (.inl j) = _
    rw [eq_blockDiag h₁ h₂ g, eq_blockDiag h₁ h₂ h, blockDiag_mul]; rfl

/-- The **restriction** to the bottom-right block of a block-diagonal representation. -/
noncomputable def restrictBot (σ : Rep G K (Fin d ⊕ Fin e))
    (h₁ : ∀ g j k, σ g (.inr k) (.inl j) = 0) (h₂ : ∀ g j k, σ g (.inl j) (.inr k) = 0) :
    Rep G K (Fin e) where
  toFun := botBlock σ
  map_one := ext fun i j => by
    show σ.toFun 1 (.inr i) (.inr j) = kd i j
    rw [σ.map_one]; exact kd_map Sum.inr (fun _ _ h => Sum.inr.inj h) i j
  map_mul g h := ext fun i j => by
    have := congrFun (congrFun (σ.map_mul g h) (.inr i)) (.inr j)
    show σ.toFun (g * h) (.inr i) (.inr j) = _
    rw [this]
    show (σ g * σ h) (.inr i) (.inr j) = _
    rw [eq_blockDiag h₁ h₂ g, eq_blockDiag h₁ h₂ h, blockDiag_mul]; rfl

/-- A block-diagonal representation is the direct sum of its blocks. -/
theorem iso_restrict (σ : Rep G K (Fin d ⊕ Fin e))
    (h₁ : ∀ g j k, σ g (.inr k) (.inl j) = 0) (h₂ : ∀ g j k, σ g (.inl j) (.inr k) = 0) :
    Iso σ ((restrictTop σ h₁ h₂).dsum (restrictBot σ h₁ h₂)) := by
  refine ⟨1, 1, fun g => ?_, one_mul 1, one_mul 1⟩
  rw [one_mul, mul_one]
  exact eq_blockDiag h₁ h₂ g

end Restrict

/-- **Splitting along a complement.** If `W ⊕ W' = K^ι` with both summands invariant and
non-zero, then `ρ ≅ ρ₁ ⊕ ρ₂` for representations `ρ₁`, `ρ₂` of degrees `d, e ≥ 1` with
`d + e ≤ |ι|`. -/
theorem iso_dsum_of_compl (hF : IsField K) {ι : Type} [FiniteType ι] (ρ : Rep G K ι)
    {W W' : Subspace ι K} (hW : Invariant ρ W) (hW' : Invariant ρ W') (hc : IsCompl W W')
    (h0 : ¬ W.IsZero) (h0' : ¬ W'.IsZero) :
    ∃ d e : Nat, 0 < d ∧ 0 < e ∧ d + e ≤ card ι ∧ ∃ (ρ₁ : Rep G K (Fin d)) (ρ₂ : Rep G K (Fin e)),
      Iso ρ (ρ₁.dsum ρ₂) := by
  obtain ⟨d, b, hbW, hbi, hbs⟩ := exists_basis_subspace hF W
  obtain ⟨e, b', hbW', hbi', hbs'⟩ := exists_basis_subspace hF W'
  let T := colMat b b'
  have hker : (ker T).IsZero := by
    intro c hc0
    have e0 : isum (fun j => c (.inl j) • b j) + isum (fun k => c (.inr k) • b' k) = 0 := by
      rw [← colMat_mulVec]; exact hc0
    have m1 : isum (fun j => c (.inl j) • b j) ∈ W := W.isum_mem fun j => W.smul_mem _ (hbW j)
    have m2 : isum (fun k => c (.inr k) • b' k) ∈ W' :=
      W'.isum_mem fun k => W'.smul_mem _ (hbW' k)
    have hneg := AddAbGroup.eq_neg_of_add_eq_zero (Eq.trans (AddAbGroup.add_comm _ _) e0)
    have z1 := hc.1 _ m1 (by rw [hneg]; exact W'.neg_mem m2)
    rw [z1, AddAbGroup.zero_add] at e0
    apply Vec.ext; intro a
    cases a with
    | inl j => exact hbi _ z1 j
    | inr k => exact hbi' _ e0 k
  have hrange : (range T).IsTop := by
    intro x
    obtain ⟨w, w', hw, hw', rfl⟩ := hc.2 x
    obtain ⟨α, rfl⟩ := hbs w hw
    obtain ⟨β, rfl⟩ := hbs' w' hw'
    exact ⟨vecSum α β, by rw [colMat_mulVec]; rfl⟩
  obtain ⟨S, hST, hTS⟩ := exists_inverse hker hrange
  have hd := pos_of_basis h0 hbs
  have he := pos_of_basis h0' hbs'
  have hcard : d + e ≤ card ι := by
    have := card_le_of_linIndep (u := fun a => Sum.elim b b' a) hF (fun c hc' a => by
      let c' : Vec (Fin d ⊕ Fin e) K := c
      have hm : c' ∈ ker T := by
        show T *ᵥ c' = 0
        apply Vec.ext; intro i
        rw [mulVec_apply, ← hc', Vec.isum_apply]
        exact isum_congr fun _ => CommRing.mul_comm _ _
      exact congrFun (hker c' hm) a)
    rwa [card_sum, card_fin, card_fin] at this
  let σ := conjRep ρ S T hST hTS
  have h₁ : ∀ g j k, σ g (.inr k) (.inl j) = 0 := fun g j k => by
    have e1 : σ g (.inr k) (.inl j) = (S *ᵥ (ρ g *ᵥ (T *ᵥ Vec.basisVec (.inl j)))) (.inr k) := by
      rw [mulVec_mulVec, mulVec_mulVec, mulVec_basisVec]; rfl
    rw [e1]
    apply inv_mulVec_span hST
    have hcol : T *ᵥ Vec.basisVec (.inl j) = b j := Vec.ext fun i => mulVec_basisVec T _ i
    rw [hcol]; exact hbs _ (hW g _ (hbW j))
  have h₂ : ∀ g j k, σ g (.inl j) (.inr k) = 0 := fun g j k => by
    have e1 : σ g (.inl j) (.inr k) = (S *ᵥ (ρ g *ᵥ (T *ᵥ Vec.basisVec (.inr k)))) (.inl j) := by
      rw [mulVec_mulVec, mulVec_mulVec, mulVec_basisVec]; rfl
    rw [e1]
    apply inv_mulVec_span' hST
    have hcol : T *ᵥ Vec.basisVec (.inr k) = b' k := Vec.ext fun i => mulVec_basisVec T _ i
    rw [hcol]; exact hbs' _ (hW' g _ (hbW' k))
  exact ⟨d, e, hd, he, hcard, _, _, (iso_conjRep ρ S T hST hTS).trans (iso_restrict σ h₁ h₂)⟩

/-! ## Complete reducibility -/

/-- **Sums of irreducibles.** `SumIrr σ` says that `σ` is built from irreducible
representations by direct sums. -/
inductive SumIrr : (κ : Type) → [FiniteType κ] → Rep G K κ → Prop
  /-- An irreducible representation. -/
  | irr {κ : Type} [FiniteType κ] (σ : Rep G K κ) : Irreducible σ → SumIrr κ σ
  /-- A direct sum of two sums of irreducibles. -/
  | sum {κ₁ κ₂ : Type} [FiniteType κ₁] [FiniteType κ₂] (σ₁ : Rep G K κ₁) (σ₂ : Rep G K κ₂) :
      SumIrr κ₁ σ₁ → SumIrr κ₂ σ₂ → SumIrr (κ₁ ⊕ κ₂) (σ₁.dsum σ₂)

/-- **Complete reducibility** (Maschke). Over a field with `|G| ≠ 0`, every representation of a
finite group on a non-zero space `K^ι` is isomorphic to a direct sum of irreducible
representations. -/
theorem complete_reducibility [FiniteType G] (hF : IsField K) (hG : (ncast (card G) : K) ≠ 0) :
    ∀ {ι : Type} [FiniteType ι] (ρ : Rep G K ι), Nonempty ι →
      ∃ (κ : Type) (_ : FiniteType κ) (σ : Rep G K κ), SumIrr κ σ ∧ Iso ρ σ := by
  have key : ∀ n {ι : Type} [FiniteType ι] (ρ : Rep G K ι), card ι = n → Nonempty ι →
      ∃ (κ : Type) (_ : FiniteType κ) (σ : Rep G K κ), SumIrr κ σ ∧ Iso ρ σ := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro ι _ ρ hn hne
      by_cases hirr : Irreducible ρ
      · exact ⟨ι, inferInstance, ρ, .irr ρ hirr, Iso.refl ρ⟩
      · obtain ⟨W, W', hW, hW', hc, h0, h0'⟩ := split_of_not_irreducible hF hG ρ hne hirr
        obtain ⟨d, e, hd, he, hde, ρ₁, ρ₂, hiso⟩ := iso_dsum_of_compl hF ρ hW hW' hc h0 h0'
        obtain ⟨κ₁, _, σ₁, hs₁, hi₁⟩ :=
          ih d (by omega) ρ₁ (card_fin d) ⟨⟨0, hd⟩⟩
        obtain ⟨κ₂, _, σ₂, hs₂, hi₂⟩ :=
          ih e (by omega) ρ₂ (card_fin e) ⟨⟨0, he⟩⟩
        exact ⟨κ₁ ⊕ κ₂, inferInstance, σ₁.dsum σ₂, .sum σ₁ σ₂ hs₁ hs₂,
          hiso.trans (hi₁.dsum hi₂)⟩
  intro ι _ ρ hne
  exact key _ ρ rfl hne

end Foundations.Langlands
