import Foundations.Langlands.Rep.Maschke

/-!
# Schur's lemma

Issai Schur, a student of Frobenius, re-founded the theory of group characters in 1905
(*Neue Begründung der Theorie der Gruppencharaktere*) on a lemma of striking simplicity:

* a `G`-map between irreducible representations is either zero or an isomorphism, because its
  kernel and image are subrepresentations;
* over an algebraically closed field such as `ℂ`, a `G`-map from an irreducible representation
  to itself is a scalar multiple of the identity, because it has an eigenvalue `λ`, and then
  `T − λ` is a `G`-map with a non-zero kernel.

Everything Frobenius had obtained by laborious determinant calculations (the orthogonality of
characters, in the next file) follows from these two statements by the averaging trick. In the
Langlands programme Schur's lemma reappears in the guise of **central characters**: the centre
of the group acts on an irreducible representation by scalars.

The second statement needs an eigenvalue, hence the fundamental theorem of algebra. There are
no determinants in this library, so we follow the determinant-free route (popularised by Axler):
for `v ≠ 0` the `n + 1` vectors `v, Tv, …, Tⁿv` in `Kⁿ` are dependent (Gaussian elimination,
`exists_nontrivial_solution`), giving a non-zero polynomial `p` with `p(T) v = 0`. Dividing `p`
by `X − λ` at a root `λ` (synthetic division) gives `p(T) v = (T − λ) q(T) v`, so either
`q(T) v` is an eigenvector or `q`, of smaller degree, also kills `v`. The field is assumed
algebraically closed in the form `AlgClosed K`, which `ℂ` satisfies by `fta`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat Subspace
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u v w

variable {G : Type u} [Group G] {K : Type w} [CommRing K] {ι κ : Type v} [FiniteType ι]
  [FiniteType κ]

/-! ## Schur's lemma, first form -/

/-- A matrix with zero kernel is injective. -/
theorem injective_of_ker {T : Mat κ ι K} (h : (ker T).IsZero) {a b : Vec ι K}
    (e : T *ᵥ a = T *ᵥ b) : a = b := by
  have h0 : a + -b = 0 := h _ (show T *ᵥ (a + -b) = 0 by
    rw [mulVec_add, mulVec_neg, e, AddAbGroup.add_neg_cancel])
  have := congrArg (· + b) h0
  simp only [AddAbGroup.add_assoc, AddAbGroup.neg_add_cancel, AddAbGroup.add_zero,
    AddAbGroup.zero_add] at this
  exact this

/-- A matrix that is injective and surjective (as a map `K^ι → K^κ`) has a two-sided inverse
matrix. -/
theorem exists_inverse {T : Mat κ ι K} (hinj : (ker T).IsZero) (hsurj : (range T).IsTop) :
    ∃ S : Mat ι κ K, S * T = 1 ∧ T * S = 1 := by
  have hu : ∀ k : κ, ∃ u : Vec ι K, Vec.basisVec k = T *ᵥ u := fun k => hsurj _
  let u : κ → Vec ι K := fun k => Classical.choose (hu k)
  have hTu : ∀ k, T *ᵥ u k = Vec.basisVec k := fun k => (Classical.choose_spec (hu k)).symm
  let S : Mat ι κ K := fun i k => u k i
  have hTS : T * S = 1 := ext fun k' k => by
    show (T *ᵥ u k) k' = kd k' k
    rw [hTu]; rfl
  refine ⟨S, ext_mulVec fun x => injective_of_ker hinj ?_, hTS⟩
  rw [mulVec_mulVec, ← mul_assoc, hTS, one_mul, one_mulVec]

/-- **Schur's lemma.** A `G`-map between irreducible representations is either zero or an
isomorphism (it has a two-sided inverse). -/
theorem schur {ρ : Rep G K ι} {σ : Rep G K κ} (hρ : Irreducible ρ) (hσ : Irreducible σ)
    {T : Mat κ ι K} (hT : IsGMap ρ σ T) : T = 0 ∨ ∃ S : Mat ι κ K, S * T = 1 ∧ T * S = 1 := by
  rcases hρ.2 _ hT.ker_invariant with hk | hk
  · rcases hσ.2 _ hT.range_invariant with hr | hr
    · exact Or.inl (eq_zero_of_mulVec fun x => hr _ ⟨x, rfl⟩)
    · exact Or.inr (exists_inverse hk hr)
  · exact Or.inl (eq_zero_of_mulVec fun x => hk x)

/-- **Schur's lemma, non-isomorphic case.** Every `G`-map between non-isomorphic irreducible
representations is zero. -/
theorem schur_of_not_iso {ρ : Rep G K ι} {σ : Rep G K κ} (hρ : Irreducible ρ)
    (hσ : Irreducible σ) (hn : ¬ Iso ρ σ) {T : Mat κ ι K} (hT : IsGMap ρ σ T) : T = 0 :=
  (schur hρ hσ hT).resolve_right fun ⟨S, h1, h2⟩ => hn ⟨T, S, hT, h1, h2⟩

/-! ## Polynomials, synthetic division and eigenvalues -/

/-- **Evaluation** of the polynomial with coefficient list `[c₀, c₁, …]` at `z` (Horner). -/
def peval : List K → K → K
  | [], _ => 0
  | c :: cs, z => c + z * peval cs z

/-- **Algebraically closed field** (in the form needed here): every polynomial `c₀ + c₁ z + ⋯`
with a non-zero coefficient beyond `c₀` has a root. -/
def AlgClosed (K : Type w) [CommRing K] : Prop :=
  ∀ (c : K) (t : List K), (∃ a ∈ t, a ≠ 0) → ∃ z, peval (c :: t) z = 0

/-- **`ℂ` is algebraically closed**: this is the fundamental theorem of algebra `fta`. -/
theorem algClosed_complex : AlgClosed C := by
  intro c t ⟨a, ha, ha0⟩
  have e : ∀ (l : List C) (z : C), peval l z = Foundations.Numbers.C.peval l z := by
    intro l z
    induction l with
    | nil => rfl
    | cons b l ih => show b + z * peval l z = b + z * _; rw [ih]
  obtain ⟨z, hz⟩ := Foundations.Numbers.C.fta c t ⟨a, ha, ha0⟩
  exact ⟨z, by rw [e]; exact hz⟩

/-- **Synthetic division** by `X − z`: returns `(q, r)` with `p = (X − z) q + r`. -/
def synDiv (z : K) : List K → List K × K
  | [] => ([], 0)
  | [c] => ([], c)
  | c :: d :: cs => ((synDiv z (d :: cs)).2 :: (synDiv z (d :: cs)).1,
      c + z * (synDiv z (d :: cs)).2)

/-- **Remainder theorem**: the remainder of division by `X − z` is `p(z)`. -/
theorem synDiv_snd (z : K) : ∀ l : List K, (synDiv z l).2 = peval l z
  | [] => rfl
  | [c] => by show c = c + z * 0; rw [Ring.mul_zero, Ring.add_zero]
  | c :: d :: cs => by
    show c + z * (synDiv z (d :: cs)).2 = c + z * peval (d :: cs) z
    rw [synDiv_snd z (d :: cs)]

/-- The quotient has one coefficient fewer. -/
theorem synDiv_length (z : K) : ∀ l : List K, (synDiv z l).1.length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | c :: d :: cs => by
    show (synDiv z (d :: cs)).1.length + 1 = cs.length + 1 + 1 - 1
    rw [synDiv_length z (d :: cs)]; simp

/-- If quotient and remainder vanish, so does the dividend. -/
theorem synDiv_allZero (z : K) : ∀ l : List K, (∀ a ∈ (synDiv z l).1, a = 0) →
    (synDiv z l).2 = 0 → ∀ a ∈ l, a = 0
  | [], _, _ => fun _ h => absurd h List.not_mem_nil
  | [c], _, hr => fun a ha => by rw [List.mem_singleton.1 ha]; exact hr
  | c :: d :: cs, hq, hr => by
    have h2 : (synDiv z (d :: cs)).2 = 0 := hq _ List.mem_cons_self
    have h1 : ∀ a ∈ (synDiv z (d :: cs)).1, a = 0 := fun a ha => hq a (List.mem_cons_of_mem _ ha)
    have hc : c = 0 := by
      have : c + z * (synDiv z (d :: cs)).2 = 0 := hr
      rw [h2, Ring.mul_zero, Ring.add_zero] at this; exact this
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hc
    · exact synDiv_allZero z (d :: cs) h1 h2 a ha

/-- **Evaluating a polynomial at a matrix**, applied to a vector: `p(T) v`, by Horner's rule
`p(T) v = c₀ v + T (c₁ v + T (⋯))`. -/
def opEval (T : Mat ι ι K) : List K → Vec ι K → Vec ι K
  | [], _ => 0
  | c :: cs, v => c • v + T *ᵥ opEval T cs v

/-- The zero polynomial evaluates to `0`. -/
theorem opEval_allZero (T : Mat ι ι K) (v : Vec ι K) :
    ∀ l : List K, (∀ a ∈ l, a = 0) → opEval T l v = 0
  | [], _ => rfl
  | c :: cs, h => by
    show c • v + T *ᵥ opEval T cs v = 0
    rw [h c List.mem_cons_self, opEval_allZero T v cs (fun a ha => h a (List.mem_cons_of_mem _ ha)),
      VectorSpace.zero_smul, mulVec_zero, AddAbGroup.zero_add]

/-- **Division at the level of operators**: `p(T) v = (T − z) q(T) v + r v`. -/
theorem opEval_synDiv (T : Mat ι ι K) (z : K) (v : Vec ι K) : ∀ l : List K,
    opEval T l v = T *ᵥ opEval T (synDiv z l).1 v + -(z • opEval T (synDiv z l).1 v) +
      (synDiv z l).2 • v
  | [] => by
    show (0 : Vec ι K) = T *ᵥ 0 + -(z • 0) + (0 : K) • v
    rw [mulVec_zero, VectorSpace.smul_zero, AddAbGroup.neg_zero, VectorSpace.zero_smul,
      AddAbGroup.add_zero, AddAbGroup.add_zero]
  | [c] => by
    show c • v + T *ᵥ 0 = T *ᵥ 0 + -(z • 0) + c • v
    rw [mulVec_zero, VectorSpace.smul_zero, AddAbGroup.neg_zero, AddAbGroup.add_zero,
      AddAbGroup.add_zero, AddAbGroup.zero_add]
  | c :: d :: cs => by
    have ih := opEval_synDiv T z v (d :: cs)
    show c • v + T *ᵥ opEval T (d :: cs) v =
      T *ᵥ ((synDiv z (d :: cs)).2 • v + T *ᵥ opEval T (synDiv z (d :: cs)).1 v) +
        -(z • ((synDiv z (d :: cs)).2 • v + T *ᵥ opEval T (synDiv z (d :: cs)).1 v)) +
        (c + z * (synDiv z (d :: cs)).2) • v
    rw [ih]
    generalize (synDiv z (d :: cs)).2 = r
    generalize opEval T (synDiv z (d :: cs)).1 v = Q
    simp only [mulVec_add, mulVec_neg, mulVec_smul]
    apply Vec.ext; intro i
    simp only [Vec.add_apply, Vec.neg_apply, Vec.smul_apply]
    grind

/-- Iterates `Tʲ v`. -/
def iter (T : Mat ι ι K) (v : Vec ι K) : Nat → Vec ι K
  | 0 => v
  | j + 1 => T *ᵥ iter T v j

/-- `p(T) v = Σⱼ cⱼ Tʲ v` for the polynomial with coefficients `c₀, …, cₙ₋₁`. -/
theorem opEval_ofFn (T : Mat ι ι K) (v : Vec ι K) :
    ∀ (n : Nat) (c : Fin n → K), opEval T (List.ofFn c) v = isum (fun j => c j • iter T v j.val)
  | 0, c => rfl
  | n + 1, c => by
    rw [List.ofFn_succ, isum_fin_succ]
    show c 0 • v + T *ᵥ opEval T (List.ofFn fun j => c j.succ) v = _
    rw [opEval_ofFn T v n, mulVec_isum]
    congr 1; apply isum_congr; intro j
    rw [mulVec_smul]; rfl

/-- **Every vector is killed by a non-zero polynomial in `T`**: for `n = |ι|`, the vectors
`v, Tv, …, Tⁿv` are linearly dependent. -/
theorem exists_annihilating (hF : IsField K) (T : Mat ι ι K) (v : Vec ι K) :
    ∃ l : List K, (∃ a ∈ l, a ≠ 0) ∧ opEval T l v = 0 := by
  let a : Fin (card ι) → Fin (card ι + 1) → K := fun r j => iter T v j.val (ofFin r)
  obtain ⟨x, ⟨j0, hj0⟩, hx⟩ := exists_nontrivial_solution hF _ _ a (Nat.lt_succ_self _)
  refine ⟨List.ofFn x, ⟨x j0, List.mem_ofFn.2 ⟨j0, rfl⟩, hj0⟩, ?_⟩
  rw [opEval_ofFn]
  apply Vec.ext; intro i
  rw [Vec.isum_apply]
  have := hx (toFin i)
  simp only [a, ofFin_toFin] at this
  exact (isum_congr fun j => CommRing.mul_comm _ _).trans this

/-- A non-zero scalar cannot kill a non-zero vector. -/
theorem smul_ne_zero (hF : IsField K) {c : K} (hc : c ≠ 0) {v : Vec ι K} (hv : v ≠ 0) :
    c • v ≠ 0 := by
  intro h
  obtain ⟨t, ht⟩ := hF.2 c hc
  apply hv
  rw [← VectorSpace.one_smul (K := K) v, ← ht, CommRing.mul_comm, VectorSpace.mul_smul, h,
    VectorSpace.smul_zero]

/-- The descent step: a non-zero polynomial killing `v ≠ 0` produces an eigenvector. -/
theorem eigen_of_annihilating (hF : IsField K) (hK : AlgClosed K) (T : Mat ι ι K)
    {v : Vec ι K} (hv : v ≠ 0) : ∀ (n : Nat) (l : List K), l.length ≤ n →
      (∃ a ∈ l, a ≠ 0) → opEval T l v = 0 → ∃ z : K, ∃ w : Vec ι K, w ≠ 0 ∧ T *ᵥ w = z • w := by
  intro n
  induction n with
  | zero =>
    intro l hl ⟨a, ha, _⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)] at ha
    exact absurd ha List.not_mem_nil
  | succ n ih =>
    intro l hl hnz hl0
    match l, hl, hnz, hl0 with
    | [], _, ⟨a, ha, _⟩, _ => exact absurd ha List.not_mem_nil
    | c :: t, hl, hnz, hl0 =>
      by_cases ht : ∃ a ∈ t, a ≠ 0
      · obtain ⟨z, hz⟩ := hK c t ht
        have hid := opEval_synDiv T z v (c :: t)
        rw [synDiv_snd, hz, VectorSpace.zero_smul, AddAbGroup.add_zero, hl0] at hid
        by_cases hw : opEval T (synDiv z (c :: t)).1 v = 0
        · apply ih (synDiv z (c :: t)).1
          · rw [synDiv_length]; simp at hl ⊢; omega
          · apply Classical.byContradiction; intro hno
            obtain ⟨a, ha, ha0⟩ := hnz
            apply ha0
            refine synDiv_allZero z (c :: t) (fun b hb => ?_) (by rw [synDiv_snd]; exact hz) a ha
            exact Classical.byContradiction fun hb0 => hno ⟨b, hb, hb0⟩
          · exact hw
        · refine ⟨z, _, hw, ?_⟩
          have := congrArg (· + z • opEval T (synDiv z (c :: t)).1 v) hid
          simp only [AddAbGroup.zero_add, AddAbGroup.add_assoc, AddAbGroup.neg_add_cancel,
            AddAbGroup.add_zero] at this
          exact this.symm
      · have hc : c ≠ 0 := by
          obtain ⟨a, ha, ha0⟩ := hnz
          rcases List.mem_cons.1 ha with rfl | ha
          · exact ha0
          · exact absurd ⟨a, ha, ha0⟩ ht
        have h0 : opEval T t v = 0 := opEval_allZero T v t fun a ha =>
          Classical.byContradiction fun h => ht ⟨a, ha, h⟩
        have : c • v + T *ᵥ opEval T t v = 0 := hl0
        rw [h0, mulVec_zero, AddAbGroup.add_zero] at this
        exact absurd this (smul_ne_zero hF hc hv)

/-- **Existence of eigenvectors.** Over an algebraically closed field, every square matrix on a
non-zero space has an eigenvector: `T w = z w` with `w ≠ 0`. -/
theorem exists_eigenvector (hF : IsField K) (hK : AlgClosed K) (T : Mat ι ι K) (i : ι) :
    ∃ z : K, ∃ w : Vec ι K, w ≠ 0 ∧ T *ᵥ w = z • w := by
  have hv : (Vec.basisVec i : Vec ι K) ≠ 0 := fun h => by
    have := congrFun h i
    exact hF.1 (by rw [← kd_self (K := K) i]; exact this.symm)
  obtain ⟨l, hnz, hl⟩ := exists_annihilating hF T (Vec.basisVec i)
  exact eigen_of_annihilating hF hK T hv l.length l (Nat.le_refl _) hnz hl

/-! ## Schur's lemma, second form -/

/-- **Schur's lemma over an algebraically closed field.** A `G`-map from an irreducible
representation to itself is a scalar: `T = z · 1`. -/
theorem schur_scalar (hF : IsField K) (hK : AlgClosed K) {ρ : Rep G K ι} (hρ : Irreducible ρ)
    {T : Mat ι ι K} (hT : IsGMap ρ ρ T) : ∃ z : K, T = z • (1 : Mat ι ι K) := by
  obtain ⟨i⟩ := hρ.1
  obtain ⟨z, w, hw, hTw⟩ := exists_eigenvector hF hK T i
  refine ⟨z, ?_⟩
  let U : Mat ι ι K := T + -(z • (1 : Mat ι ι K))
  have hU : ∀ x, U *ᵥ x = T *ᵥ x + -(z • x) := fun x => by
    rw [add_mulVec, neg_mulVec, smul_mulVec, one_mulVec]
  have hUg : IsGMap ρ ρ U := IsGMap.of_act fun g x => by
    rw [hU, hU, hT.act, mulVec_add, mulVec_neg, mulVec_smul]
  rcases hρ.2 _ hUg.ker_invariant with hk | hk
  · exfalso; apply hw; apply hk
    show U *ᵥ w = 0
    rw [hU, hTw, AddAbGroup.add_neg_cancel]
  · apply ext_mulVec; intro x
    have : U *ᵥ x = 0 := hk x
    rw [hU] at this
    rw [smul_mulVec, one_mulVec]
    have := congrArg (· + z • x) this
    simp only [AddAbGroup.zero_add, AddAbGroup.add_assoc, AddAbGroup.neg_add_cancel,
      AddAbGroup.add_zero] at this
    exact this

/-- **Schur's lemma over `ℂ`.** Every `G`-endomorphism of an irreducible complex representation
is a scalar multiple of the identity. -/
theorem schur_complex {ρ : Rep G C ι} (hρ : Irreducible ρ) {T : Mat ι ι C} (hT : IsGMap ρ ρ T) :
    ∃ z : C, T = z • (1 : Mat ι ι C) :=
  schur_scalar C.isField algClosed_complex hρ hT

end Foundations.Langlands
