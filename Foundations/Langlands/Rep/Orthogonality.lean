import Foundations.Langlands.Rep.Schur

/-!
# Orthogonality of characters

Frobenius' 1896 paper *Über Gruppencharaktere* contains the relations that make characters
computable: for irreducible characters `χ`, `ψ` of a finite group `G`,

  `Σ_{g ∈ G} χ(g) ψ(g⁻¹) = |G|` if the representations are isomorphic, and `0` otherwise.

Frobenius found them through the group determinant; Schur (1905) gave the proof reproduced here,
which needs nothing but his lemma and averaging. For any matrix `X` the average
`X° = Σ_g σ(g) X ρ(g⁻¹)` is a `G`-map from `ρ` to `σ`. If `ρ ≇ σ`, Schur says `X° = 0`; if
`ρ = σ`, Schur over `ℂ` says `X° = c · 1`, and taking traces gives `c · deg ρ = |G| · tr X`.
Choosing for `X` the elementary matrices `E_{ji}` and adding up the diagonal entries produces
exactly the sums above.

Consequences proved here: the irreducible characters are orthonormal for the bilinear pairing
`⟨χ, ψ⟩ = |G|⁻¹ Σ_g χ(g) ψ(g⁻¹)`, and therefore, when a character is a combination
`Σ_k m_k χ_k` of pairwise non-isomorphic irreducible characters, the **multiplicities** are
recovered as `m_k = ⟨χ, χ_k⟩` — Frobenius' answer to the question *which irreducibles occur, and
how often*. (Over `ℂ` one has `ψ(g⁻¹) = conj ψ(g)`, making the pairing the usual Hermitian
inner product; that identity is not proved in this file.) In the Langlands programme the same
mechanism, now with infinite groups and integrals in place of sums, is the *trace formula*.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u v w

variable {K : Type w} [CommRing K] {ι κ : Type v} [FiniteType ι] [FiniteType κ]

/-! ## Sums of matrices -/

namespace Mat

/-- Matrices form an additive abelian group under entrywise addition. -/
instance instAddAbGroup : AddAbGroup (Mat κ ι K) where
  add_assoc A B D := ext fun _ _ => Ring.add_assoc _ _ _
  add_comm A B := ext fun _ _ => Ring.add_comm _ _
  zero_add A := ext fun _ _ => Ring.zero_add _
  neg_add_cancel A := ext fun _ _ => Ring.neg_add_cancel _

/-- Entries of a finite sum of matrices. -/
theorem isum_apply' {α : Type u} [FiniteType α] (M : α → Mat κ ι K) (k : κ) (i : ι) :
    (isum M) k i = isum (fun a => M a k i) := by
  unfold isum
  induction (elems : List α) with
  | nil => rfl
  | cons a l ih => show M a k i + (lsum (l.map M)) k i = M a k i + lsum _; rw [ih]

/-- A finite sum of matrices acts as the sum of the actions. -/
theorem isum_mulVec {α : Type u} [FiniteType α] (M : α → Mat κ ι K) (x : Vec ι K) :
    isum M *ᵥ x = isum (fun a => M a *ᵥ x) := by
  apply Vec.ext; intro k
  rw [mulVec_apply, Vec.isum_apply]
  simp only [isum_apply', isum_mul_right, mulVec_apply]
  exact isum_comm _

/-- The trace of a finite sum is the sum of the traces. -/
theorem trace_isum {α : Type u} [FiniteType α] (M : α → Mat ι ι K) :
    trace (isum M) = isum (fun a => trace (M a)) := by
  show isum (fun i => isum M i i) = _
  simp only [isum_apply']
  exact isum_comm _

/-- The **elementary matrix** `E_{ji}`, with a single `1` in row `j`, column `i`. -/
noncomputable def elem (j : κ) (i : ι) : Mat κ ι K := fun a b => kd a j * kd b i

/-- `(A E_{ji} B)ₗₖ = A_{lj} B_{ik}`. -/
theorem mul_elem_mul {μ ν : Type v} [FiniteType μ] [FiniteType ν] (A : Mat μ κ K) (j : κ) (i : ι)
    (B : Mat ι ν K) (l : μ) (k : ν) : (A * (elem j i : Mat κ ι K) * B : Mat μ ν K) l k = A l j * B i k := by
  rw [mul_apply]
  have hAE : ∀ b, (A * (elem j i : Mat κ ι K) : Mat μ ι K) l b = A l j * kd b i := fun b =>
    (isum_congr (fun a => show A l a * (kd a j * kd b i) = kd a j * (A l a * kd b i) by
      grind)).trans (isum_kd_mul j (fun a => A l a * kd b i))
  refine (isum_congr (fun b => show (A * (elem j i : Mat κ ι K) : Mat μ ι K) l b * B b k =
    kd b i * (A l j * B b k) by rw [hAE b]; grind)).trans ?_
  exact isum_kd_mul i (fun b => A l j * B b k)

/-- The trace of an elementary matrix: `tr E_{ji} = δ_{ji}`. -/
theorem trace_elem (j i : ι) : trace (elem j i : Mat ι ι K) = kd j i :=
  isum_kd_mul j (fun a => kd a i)

end Mat

/-! ## The averaged map -/

variable {G : Type u} [Group G] [FiniteType G]

/-- The **average** `X° = Σ_g σ(g) X ρ(g⁻¹)` of a matrix `X : K^ι → K^κ`. -/
def avgMap (ρ : Rep G K ι) (σ : Rep G K κ) (X : Mat κ ι K) : Mat κ ι K :=
  isum (fun g => σ g * X * ρ g⁻¹)

/-- **The average is a `G`-map.** -/
theorem avgMap_isGMap (ρ : Rep G K ι) (σ : Rep G K κ) (X : Mat κ ι K) :
    IsGMap ρ σ (avgMap ρ σ X) := by
  apply IsGMap.of_act; intro h x
  unfold avgMap
  rw [isum_mulVec, isum_mulVec, mulVec_isum, ← isum_mul_left_reindex h]
  apply isum_congr; intro g
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    ← ρ.act_mul, Group.mul_inv_rev, Group.mul_assoc, Group.inv_mul_cancel, Group.mul_one,
    σ.act_mul]

/-- **The key identity.** `Σ_g χ_σ(g) χ_ρ(g⁻¹)` is the sum of the diagonal-type entries
`(E_{ji})°_{ji}` of the averaged elementary matrices. -/
theorem pairing_eq_sum_avg (ρ : Rep G K ι) (σ : Rep G K κ) :
    isum (fun g => character σ g * character ρ g⁻¹) =
      isum (fun j : κ => isum (fun i : ι => avgMap ρ σ (Mat.elem j i) j i)) := by
  unfold avgMap
  simp only [Mat.isum_apply', Mat.mul_elem_mul]
  have e : ∀ g, character σ g * character ρ g⁻¹ =
      isum (fun j => isum (fun i => σ g j j * ρ g⁻¹ i i)) := by
    intro g; show isum (fun j => σ g j j) * isum (fun i => ρ g⁻¹ i i) = _
    rw [isum_mul_right]; apply isum_congr; intro j; rw [isum_mul_left]
  rw [isum_congr e]
  conv => lhs; rw [isum_comm]
  apply isum_congr; intro j
  conv => lhs; rw [isum_comm]

/-- The **pairing** `Σ_g χ(g) ψ(g⁻¹)` of two functions on `G` (`|G|` times the usual inner
product). -/
def pairing (χ ψ : G → K) : K := isum (fun g => χ g * ψ g⁻¹)

/-- **First orthogonality relation, non-isomorphic case.** For non-isomorphic irreducible
representations `ρ`, `σ` (over any commutative ring), `Σ_g χ_σ(g) χ_ρ(g⁻¹) = 0`. -/
theorem orthogonality_of_not_iso {ρ : Rep G K ι} {σ : Rep G K κ} (hρ : Irreducible ρ)
    (hσ : Irreducible σ) (hn : ¬ Iso ρ σ) : pairing (character σ) (character ρ) = 0 := by
  unfold pairing
  rw [pairing_eq_sum_avg]
  apply isum_eq_zero; intro j
  apply isum_eq_zero; intro i
  rw [schur_of_not_iso hρ hσ hn (avgMap_isGMap ρ σ _)]; rfl

/-- **First orthogonality relation, diagonal case.** Over an algebraically closed field in which
the degree of `ρ` is non-zero (e.g. `ℂ`), an irreducible character satisfies
`Σ_g χ(g) χ(g⁻¹) = |G|`. -/
theorem orthogonality_self (hF : IsField K) (hK : AlgClosed K) {ρ : Rep G K ι}
    (hρ : Irreducible ρ) (hdeg : (ncast (card ι) : K) ≠ 0) :
    pairing (character ρ) (character ρ) = ncast (card G) := by
  unfold pairing
  rw [pairing_eq_sum_avg]
  have hc : ∀ j i, ∃ c : K, avgMap ρ ρ (Mat.elem j i) = c • (1 : Mat ι ι K) := fun j i =>
    schur_scalar hF hK hρ (avgMap_isGMap ρ ρ _)
  let c : ι → ι → K := fun j i => Classical.choose (hc j i)
  have hcs : ∀ j i, avgMap ρ ρ (Mat.elem j i) = c j i • (1 : Mat ι ι K) := fun j i =>
    Classical.choose_spec (hc j i)
  -- traces: `n · c_{ji} = |G| · δ_{ji}`
  have htr : ∀ j i, ncast (card ι) * c j i = ncast (card G) * kd j i := by
    intro j i
    have e := congrArg trace (hcs j i)
    rw [trace_smul, trace_one, avgMap, Mat.trace_isum,
      isum_congr (fun g => trace_conj (ρ g) (Mat.elem j i) (ρ g⁻¹) (ρ.inv_mul g)),
      isum_const, Mat.trace_elem] at e
    rw [CommRing.mul_comm]; exact e.symm
  have hS : isum (fun j => isum (fun i => avgMap ρ ρ (Mat.elem j i) j i)) =
      isum (fun j => isum (fun i => c j i * kd j i)) := by
    apply isum_congr; intro j; apply isum_congr; intro i
    rw [hcs]; rfl
  rw [hS]
  obtain ⟨t, ht⟩ := hF.2 _ hdeg
  have hnS : ncast (card ι) * isum (fun j => isum (fun i => c j i * kd j i)) =
      ncast (card ι) * (ncast (card G) : K) := by
    rw [isum_mul_left]
    rw [isum_congr (fun j => show ncast (card ι) * isum (fun i => c j i * kd j i) =
      (ncast (card G) : K) by
        rw [isum_mul_left]
        rw [isum_congr (fun i => show ncast (card ι) * (c j i * kd j i) =
          kd j i * (ncast (card G) * kd j i) by rw [← Ring.mul_assoc, htr]; grind)]
        rw [isum_kd_mul', kd_self, Ring.mul_one])]
    rw [isum_const, CommRing.mul_comm]
  have := congrArg (t * ·) hnS
  rw [← Ring.mul_assoc, ← Ring.mul_assoc, CommRing.mul_comm t, ht, Ring.one_mul,
    Ring.one_mul] at this
  exact this

open Classical in
/-- **First orthogonality relation.** For irreducible representations over an algebraically
closed field in which `deg ρ ≠ 0`: `Σ_g χ_σ(g) χ_ρ(g⁻¹)` is `|G|` if `ρ ≅ σ` and `0` otherwise. -/
theorem orthogonality (hF : IsField K) (hK : AlgClosed K) {ρ : Rep G K ι} {σ : Rep G K κ}
    (hρ : Irreducible ρ) (hσ : Irreducible σ) (hdeg : (ncast (card ι) : K) ≠ 0) :
    pairing (character σ) (character ρ) =
      if Iso ρ σ then (ncast (card G) : K) else 0 := by
  by_cases h : Iso ρ σ
  · simp only [h, ↓reduceIte]
    rw [ ← character_eq_of_iso h]; exact orthogonality_self hF hK hρ hdeg
  · simp only [h, ↓reduceIte]; exact orthogonality_of_not_iso hρ hσ h

/-- `ncast` of a positive natural number is non-zero in `ℂ`. -/
theorem ncast_ne_zero_complex {n : Nat} (hn : 0 < n) : (ncast n : C) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact C.ncast_succ_ne_zero m

/-- An irreducible representation has positive degree. -/
theorem card_pos_of_irreducible {ρ : Rep G K ι} (hρ : Irreducible ρ) : 0 < card ι := by
  obtain ⟨i⟩ := hρ.1; exact List.length_pos_of_mem (complete i)

open Classical in
/-- **First orthogonality relation over `ℂ`.** For irreducible complex representations `ρ`, `σ`
of a finite group: `Σ_g χ_σ(g) χ_ρ(g⁻¹) = |G|` if `ρ ≅ σ`, and `0` otherwise. -/
theorem orthogonality_complex {ρ : Rep G C ι} {σ : Rep G C κ} (hρ : Irreducible ρ)
    (hσ : Irreducible σ) :
    pairing (character σ) (character ρ) = if Iso ρ σ then (ncast (card G) : C) else 0 :=
  orthogonality C.isField algClosed_complex hρ hσ
    (ncast_ne_zero_complex (card_pos_of_irreducible hρ))

end Foundations.Langlands
