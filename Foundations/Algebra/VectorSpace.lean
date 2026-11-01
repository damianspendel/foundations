import Foundations.Algebra.TwoSquares

/-!
# Vector spaces and dimension

The final chapter of this Part is about three problems the Greeks posed and could not solve
with straightedge and compass: *doubling the cube*, *trisecting an angle*, and *squaring the
circle*. For two thousand years they resisted, until in 1837 Pierre Wantzel showed the first
two impossible. The key was to translate geometry into algebra and then to *count
dimensions*: a length constructible by ruler and compass lives in a tower of quadratic field
extensions, hence in a space whose dimension over `ℚ` is a power of `2` — while `∛2` and
`cos 20°` need dimension `3`.

Dimension is the subject of this file. A **vector space** over a field `K` is an additive
group whose elements can be scaled by elements of `K`. A family of vectors is **linearly
independent** if no non-trivial combination vanishes, and **spans** if every vector is a
combination. The central result, going back to Grassmann (1844) and Steinitz (1913), is the
**exchange lemma**: an independent family inside the span of another family is no larger
than it. Consequently all bases of a finite-dimensional space have the same size — the
**dimension** is well defined. The engine of the proof is the oldest algorithm of linear
algebra, Gaussian elimination (already in the Chinese *Nine Chapters*, c. 200 BCE): a
homogeneous linear system with more unknowns than equations has a non-zero solution.

Families are indexed by arbitrary finite types; sums run over the census of the index type.
-/

namespace Foundations.Algebra

open FiniteType

universe u v w

/-! ## Additive abelian groups and finite sums -/

/-- **Additive abelian group**: the additive structure of a vector space. -/
class AddAbGroup (A : Type u) extends Add A, Zero A, Neg A where
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : A, a + b + c = a + (b + c)
  /-- Addition is commutative. -/
  add_comm : ∀ a b : A, a + b = b + a
  /-- `0` is an identity. -/
  zero_add : ∀ a : A, 0 + a = a
  /-- `-a` is an inverse. -/
  neg_add_cancel : ∀ a : A, -a + a = 0

/-- Every ring is an additive abelian group. -/
instance (priority := low) Ring.toAddAbGroup {R : Type u} [Ring R] : AddAbGroup R where
  add_assoc := Ring.add_assoc
  add_comm := Ring.add_comm
  zero_add := Ring.zero_add
  neg_add_cancel := Ring.neg_add_cancel

namespace AddAbGroup

variable {A : Type u} [AddAbGroup A]

/-- Addition is associative (for `ac_rfl`). -/
instance : Std.Associative (α := A) (· + ·) := ⟨add_assoc⟩

/-- Addition is commutative (for `ac_rfl`). -/
instance : Std.Commutative (α := A) (· + ·) := ⟨add_comm⟩

/-- `a + 0 = a`. -/
theorem add_zero (a : A) : a + 0 = a := by rw [add_comm, zero_add]

/-- `a + -a = 0`. -/
theorem add_neg_cancel (a : A) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

/-- Additive cancellation. -/
theorem add_left_cancel {a b c : A} (h : a + b = a + c) : b = c := by
  have := congrArg (-a + ·) h
  simp only [← add_assoc, neg_add_cancel, zero_add] at this
  exact this

/-- If `a + b = 0` then `b = -a`. -/
theorem eq_neg_of_add_eq_zero {a b : A} (h : a + b = 0) : b = -a :=
  add_left_cancel (h.trans (add_neg_cancel a).symm)

/-- `-0 = 0`. -/
theorem neg_zero : -(0 : A) = 0 := (eq_neg_of_add_eq_zero (add_zero 0)).symm

end AddAbGroup

open AddAbGroup

/-- Sum of a list. -/
def lsum {A : Type u} [AddAbGroup A] : List A → A
  | [] => 0
  | a :: l => a + lsum l

/-- **Sum over a finite type**: `∑ᵢ f i`, summing over the census. -/
def isum {A : Type u} [AddAbGroup A] {ι : Type v} [FiniteType ι] (f : ι → A) : A :=
  lsum ((elems : List ι).map f)

section Sums

variable {A : Type u} [AddAbGroup A]

/-- Sum of a concatenation. -/
theorem lsum_append (l m : List A) : lsum (l ++ m) = lsum l + lsum m := by
  induction l with
  | nil => exact (zero_add _).symm
  | cons a l ih => show a + lsum (l ++ m) = a + lsum l + lsum m; rw [ih, add_assoc]

/-- Sums do not depend on the order of the terms. -/
theorem lsum_perm {l m : List A} (h : l.Perm m) : lsum l = lsum m := by
  induction h with
  | nil => rfl
  | cons a _ ih => show a + _ = a + _; rw [ih]
  | swap a b l => show b + (a + lsum l) = a + (b + lsum l); ac_rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

variable {ι : Type v} [FiniteType ι]

/-- Sums are additive. -/
theorem isum_add (f g : ι → A) : isum (fun i => f i + g i) = isum f + isum g := by
  unfold isum
  induction (elems : List ι) with
  | nil => exact (add_zero 0).symm
  | cons a l ih =>
    show f a + g a + lsum (l.map _) = (f a + lsum (l.map f)) + (g a + lsum (l.map g))
    rw [ih]; ac_rfl

/-- A sum of zeros is zero. -/
theorem isum_zero : isum (fun _ : ι => (0 : A)) = 0 := by
  unfold isum
  induction (elems : List ι) with
  | nil => rfl
  | cons a l ih => show 0 + lsum (l.map _) = 0; rw [ih, zero_add]

/-- A sum of terms that are all zero is zero. -/
theorem isum_eq_zero {f : ι → A} (h : ∀ i, f i = 0) : isum f = 0 := by
  have : f = fun _ => 0 := funext h
  rw [this, isum_zero]

/-- Sums respect negation. -/
theorem isum_neg (f : ι → A) : isum (fun i => -f i) = -isum f := by
  apply eq_neg_of_add_eq_zero
  rw [← isum_add]
  exact isum_eq_zero fun i => add_neg_cancel _

/-- **Reindexing** a sum along a bijection. -/
theorem isum_comp_bij {κ : Type w} [FiniteType κ] (e : ι → κ) (inj : ∀ a b, e a = e b → a = b)
    (surj : ∀ y, ∃ x, e x = y) (f : κ → A) : isum (fun i => f (e i)) = isum f := by
  unfold isum
  have hperm : ((elems : List ι).map e).Perm (elems : List κ) := by
    rw [List.perm_ext_iff_of_nodup (nodup_map_of_injective inj nodup) nodup]
    intro y
    simp only [List.mem_map, complete, true_and, iff_true]
    exact surj y
  rw [← lsum_perm (hperm.map f), List.map_map]; rfl

/-- Splitting off the first term of a sum over `Fin (n+1)`. -/
theorem isum_fin_succ {n : Nat} (f : Fin (n + 1) → A) : isum f = f 0 + isum (fun i : Fin n => f i.succ) := by
  show lsum ((List.finRange (n + 1)).map f) = f 0 + lsum ((List.finRange n).map _)
  rw [List.finRange_succ, List.map_cons, List.map_map]; rfl

/-- The empty sum. -/
theorem isum_fin_zero (f : Fin 0 → A) : isum f = 0 := rfl

/-- **Sums over a product** are iterated sums. -/
theorem isum_prod {κ : Type w} [FiniteType κ] (f : ι × κ → A) :
    isum f = isum (fun i => isum (fun k => f (i, k))) := by
  show lsum (((elems : List ι).flatMap (fun a => (elems : List κ).map (fun b => (a, b)))).map f) = _
  unfold isum
  induction (elems : List ι) with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, lsum_append, ih, List.map_map]; rfl

/-- **Fubini for finite sums**: the order of summation can be swapped. -/
theorem isum_comm {κ : Type w} [FiniteType κ] (f : ι → κ → A) :
    isum (fun i => isum (fun k => f i k)) = isum (fun k => isum (fun i => f i k)) := by
  unfold isum
  induction (elems : List ι) with
  | nil => exact (isum_zero (ι := κ)).symm
  | cons a l ih =>
    show lsum ((elems : List κ).map (f a)) + lsum (l.map _) = _
    rw [ih]
    exact (isum_add (fun k => f a k) (fun k => lsum (l.map fun i => f i k))).symm

end Sums

section RingSums

variable {R : Type u} [Ring R] {ι : Type v} [FiniteType ι]

/-- Multiplying a sum on the left. -/
theorem isum_mul_left (c : R) (f : ι → R) : c * isum f = isum (fun i => c * f i) := by
  unfold isum
  induction (elems : List ι) with
  | nil => exact Ring.mul_zero c
  | cons a l ih => show c * (f a + lsum _) = c * f a + lsum _; rw [Ring.left_distrib, ih]

end RingSums

/-! ## Vector spaces -/

/-- **Vector space** over `K` (a field, assumed where needed): an additive abelian group with
a scalar multiplication satisfying the distributive and associative laws. -/
class VectorSpace (K : Type u) (V : Type v) [CommRing K] [AddAbGroup V] extends SMul K V where
  /-- Scalars distribute over vector addition. -/
  smul_add : ∀ (c : K) (x y : V), c • (x + y) = c • x + c • y
  /-- Scalar addition distributes. -/
  add_smul : ∀ (c d : K) (x : V), (c + d) • x = c • x + d • x
  /-- Scaling twice is scaling by the product. -/
  mul_smul : ∀ (c d : K) (x : V), (c * d) • x = c • (d • x)
  /-- Scaling by `1` does nothing. -/
  one_smul : ∀ x : V, (1 : K) • x = x

namespace VectorSpace

variable {K : Type u} {V : Type v} [CommRing K] [AddAbGroup V] [VectorSpace K V]

/-- `0 • x = 0`. -/
theorem zero_smul (x : V) : (0 : K) • x = 0 := by
  apply add_left_cancel (a := (0 : K) • x)
  rw [← add_smul, Ring.add_zero, add_zero]

/-- `c • 0 = 0`. -/
theorem smul_zero (c : K) : c • (0 : V) = 0 := by
  apply add_left_cancel (a := c • (0 : V))
  rw [← smul_add, add_zero, add_zero]

/-- `(-c) • x = -(c • x)`. -/
theorem neg_smul (c : K) (x : V) : (-c) • x = -(c • x) := by
  apply eq_neg_of_add_eq_zero
  rw [← add_smul, Ring.add_neg_cancel, zero_smul]

/-- `c • (-x) = -(c • x)`. -/
theorem smul_neg (c : K) (x : V) : c • (-x) = -(c • x) := by
  apply eq_neg_of_add_eq_zero
  rw [← smul_add, add_neg_cancel, smul_zero]

variable {ι : Type w} [FiniteType ι]

/-- Scaling a sum. -/
theorem smul_isum (c : K) (f : ι → V) : c • isum f = isum (fun i => c • f i) := by
  unfold isum
  induction (elems : List ι) with
  | nil => exact smul_zero c
  | cons a l ih => show c • (f a + lsum _) = c • f a + lsum _; rw [smul_add, ih]

/-- A sum of scalars times a vector. -/
theorem isum_smul (c : ι → K) (x : V) : isum c • x = isum (fun i => c i • x) := by
  unfold isum
  induction (elems : List ι) with
  | nil => exact zero_smul x
  | cons a l ih => show (c a + lsum _) • x = c a • x + lsum _; rw [add_smul, ih]

end VectorSpace

open VectorSpace

section Linear

variable (K : Type u) {V : Type v} [CommRing K] [AddAbGroup V] [VectorSpace K V]

/-- A family `u` is **linearly independent** if the only combination `∑ cᵢ uᵢ` equal to `0`
is the trivial one. -/
def LinIndep {ι : Type w} [FiniteType ι] (u : ι → V) : Prop :=
  ∀ c : ι → K, isum (fun i => c i • u i) = 0 → ∀ i, c i = 0

/-- `x` is in the **span** of `u` if it is a linear combination `∑ cᵢ uᵢ`. -/
def InSpan {ι : Type w} [FiniteType ι] (u : ι → V) (x : V) : Prop :=
  ∃ c : ι → K, x = isum (fun i => c i • u i)

/-- A family **spans** if every vector is in its span. -/
def Spans {ι : Type w} [FiniteType ι] (u : ι → V) : Prop := ∀ x, InSpan K u x

/-- A **basis** is an independent spanning family. -/
def IsBasis {ι : Type w} [FiniteType ι] (u : ι → V) : Prop := LinIndep K u ∧ Spans K u

/-- A space is **finite-dimensional** if some finite family spans it. -/
def FinDim (V : Type v) [AddAbGroup V] [VectorSpace K V] : Prop :=
  ∃ n, ∃ u : Fin n → V, Spans K u

end Linear

/-! ## Gaussian elimination -/

/-- Skipping index `p`: an enumeration of `Fin (m+1) \ {p}` by `Fin m`. -/
def skip {m : Nat} (p : Fin (m + 1)) (i : Fin m) : Fin (m + 1) :=
  if i.val < p.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- Every index other than `p` is skipped to. -/
theorem skip_surj {m : Nat} (p : Fin (m + 1)) (i : Fin (m + 1)) (hi : i ≠ p) :
    ∃ i', skip p i' = i := by
  have hv : i.val ≠ p.val := fun h => hi (Fin.ext h)
  by_cases h : i.val < p.val
  · refine ⟨⟨i.val, by omega⟩, ?_⟩
    unfold skip; rw [ite_true_of (show i.val < p.val from h)]
  · refine ⟨⟨i.val - 1, by omega⟩, Fin.ext ?_⟩
    unfold skip; rw [ite_false_of (show ¬ (i.val - 1 < p.val) by omega)]; simp; omega

/-- **Homogeneous systems with more unknowns than equations have non-zero solutions**
(Gaussian elimination). For an `m × n` system `∑ⱼ aᵢⱼ xⱼ = 0` over a field with `m < n`
there is a solution `x ≠ 0`. -/
theorem exists_nontrivial_solution {K : Type u} [CommRing K] (hF : IsField K) :
    ∀ (n m : Nat) (a : Fin m → Fin n → K), m < n →
      ∃ x : Fin n → K, (∃ j, x j ≠ 0) ∧ ∀ i, isum (fun j => a i j * x j) = 0 := by
  intro n
  induction n with
  | zero => intro m _ h; omega
  | succ k ih =>
    intro m a hmn
    by_cases hcol : ∀ i, a i 0 = 0
    · refine ⟨tcons 1 (fun _ => 0), ⟨0, fun h => hF.1 h.symm⟩, fun i => ?_⟩
      rw [isum_fin_succ]
      show a i 0 * 1 + isum (fun j : Fin k => a i j.succ * 0) = 0
      rw [hcol i, Ring.zero_mul, Ring.zero_add]
      exact isum_eq_zero fun j => Ring.mul_zero _
    · have : ∃ p, a p 0 ≠ 0 := by
        apply Classical.byContradiction; intro hno
        exact hcol fun i => Classical.byContradiction fun h => hno ⟨i, h⟩
      obtain ⟨p, hp⟩ := this
      obtain ⟨t, ht⟩ := hF.2 _ hp
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := p.isLt; omega⟩
      let a' : Fin m' → Fin k → K := fun i j =>
        a (skip p i) j.succ + -(a (skip p i) 0 * t) * a p j.succ
      obtain ⟨y, ⟨j0, hj0⟩, hy⟩ := ih m' a' (by omega)
      let S := isum (fun j : Fin k => a p j.succ * y j)
      refine ⟨tcons (-(t * S)) y, ⟨j0.succ, hj0⟩, fun i => ?_⟩
      rw [isum_fin_succ]
      show a i 0 * -(t * S) + isum (fun j : Fin k => a i j.succ * y j) = 0
      by_cases hip : i = p
      · subst hip
        rw [Ring.mul_neg, ← Ring.mul_assoc, ht, Ring.one_mul, Ring.neg_add_cancel]
      · obtain ⟨i', rfl⟩ := skip_surj p i hip
        have h1 := hy i'
        have e : isum (fun j => a' i' j * y j) =
            isum (fun j : Fin k => a (skip p i') j.succ * y j) + -(a (skip p i') 0 * t) * S := by
          rw [isum_mul_left, ← isum_add]
          congr 1; funext j
          show (a (skip p i') j.succ + -(a (skip p i') 0 * t) * a p j.succ) * y j = _
          rw [Ring.right_distrib, Ring.mul_assoc]
        rw [e] at h1
        rw [Ring.mul_neg, Ring.add_comm, ← h1, Ring.neg_mul, Ring.mul_assoc]

/-! ## The exchange lemma -/

section Steinitz

variable {K : Type u} {V : Type v} [CommRing K] [AddAbGroup V] [VectorSpace K V]

/-- `ofFin` is a bijection `Fin (card ι) → ι`. -/
theorem ofFin_bij {ι : Type w} [FiniteType ι] :
    (∀ a b : Fin (card ι), ofFin a = ofFin b → a = b) ∧ (∀ y : ι, ∃ x, ofFin x = y) :=
  ⟨fun a b h => by rw [← toFin_ofFin a, h, toFin_ofFin], fun y => ⟨toFin y, ofFin_toFin y⟩⟩

/-- **Steinitz exchange lemma.** If an independent family `u` lies in the span of a family
`w`, then `u` has at most as many members as `w`. -/
theorem steinitz (hF : IsField K) {ι : Type w} {κ : Type w} [FiniteType ι] [FiniteType κ]
    (u : ι → V) (w' : κ → V) (hu : LinIndep K u) (hw : ∀ i, InSpan K w' (u i)) :
    card ι ≤ card κ := by
  apply Nat.le_of_not_lt
  intro hlt
  let a : ι → κ → K := fun i => Classical.choose (hw i)
  have ha : ∀ i, u i = isum (fun k => a i k • w' k) := fun i => Classical.choose_spec (hw i)
  let A : Fin (card κ) → Fin (card ι) → K := fun r j => a (ofFin j) (ofFin r)
  obtain ⟨x, ⟨j0, hj0⟩, hx⟩ := exists_nontrivial_solution hF _ _ A hlt
  let c : ι → K := fun i => x (toFin i)
  have hsum : isum (fun i => c i • u i) = 0 := by
    have step : ∀ i, c i • u i = isum (fun k => (c i * a i k) • w' k) := by
      intro i; rw [ha i, smul_isum]; congr 1; funext k; rw [mul_smul]
    rw [show (fun i => c i • u i) = fun i => isum (fun k => (c i * a i k) • w' k) from funext step,
      isum_comm]
    apply isum_eq_zero
    intro k
    rw [← isum_smul]
    have hinner : isum (fun i => c i * a i k) = 0 := by
      rw [← isum_comp_bij ofFin ofFin_bij.1 ofFin_bij.2]
      have := hx (toFin k)
      rw [← this]
      congr 1; funext j
      show x (toFin (ofFin j)) * a (ofFin j) k = a (ofFin j) (ofFin (toFin k)) * x j
      rw [toFin_ofFin, ofFin_toFin, CommRing.mul_comm]
    rw [hinner, zero_smul]
  have := hu c hsum (ofFin j0)
  apply hj0
  rw [← this]; show x j0 = x (toFin (ofFin j0)); rw [toFin_ofFin]

end Steinitz

/-! ## Dimension -/

section Dimension

variable (K : Type u) (V : Type v) [CommRing K] [AddAbGroup V] [VectorSpace K V]

/-- The **dimension**: the largest size of an independent family (`0` if there is no
bound). By `card_eq_dim` every basis has exactly this size. -/
noncomputable def dim : Nat := by
  classical
  exact if h : ∃ n, ¬ ∃ u : Fin (n + 1) → V, LinIndep K u then
    Classical.choose (FiniteType.exists_least _ h) else 0

variable {K V}

/-- Adding a vector outside the span keeps a family independent. -/
theorem linIndep_tcons (hF : IsField K) {n : Nat} {u : Fin n → V} (hu : LinIndep K u) {x : V}
    (hx : ¬ InSpan K u x) : LinIndep K (tcons x u) := by
  intro c hc
  rw [isum_fin_succ] at hc
  have hc' : c 0 • x + isum (fun j : Fin n => c j.succ • u j) = 0 := hc
  have h0 : c 0 = 0 := by
    apply Classical.byContradiction
    intro hne
    obtain ⟨t, ht⟩ := hF.2 _ hne
    apply hx
    refine ⟨fun j => -(t * c j.succ), ?_⟩
    have e := congrArg (fun z => t • z) (eq_neg_of_add_eq_zero (Eq.trans (add_comm _ _) hc'))
    rw [← mul_smul, CommRing.mul_comm, ht, one_smul] at e
    rw [e, smul_neg, smul_isum, ← isum_neg]
    congr 1; funext j
    show -(t • c j.succ • u j) = (-(t * c j.succ)) • u j
    rw [neg_smul, mul_smul]
  have hrest := hu (fun j => c j.succ) (by rw [h0, zero_smul, zero_add] at hc'; exact hc')
  intro j
  cases j using Fin.cases with
  | zero => exact h0
  | succ j => exact hrest j

/-- The empty family is independent. -/
theorem linIndep_empty (u : Fin 0 → V) : LinIndep K u := fun _ _ i => absurd i.isLt (Nat.not_lt_zero _)

/-- Reindexing an independent family along `ofFin` keeps it independent. -/
theorem linIndep_ofFin {ι : Type w} [FiniteType ι] {u : ι → V} (hu : LinIndep K u) :
    LinIndep K (fun j : Fin (card ι) => u (ofFin j)) := by
  intro c hc j
  have := hu (fun i => c (toFin i)) (by
    rw [← isum_comp_bij ofFin ofFin_bij.1 ofFin_bij.2]
    simp only [toFin_ofFin]; exact hc) (ofFin j)
  rwa [toFin_ofFin] at this

/-- Spans are unchanged by reindexing along `ofFin`. -/
theorem inSpan_ofFin {ι : Type w} [FiniteType ι] {u : ι → V} {x : V} :
    InSpan K (fun j : Fin (card ι) => u (ofFin j)) x ↔ InSpan K u x := by
  constructor
  · intro ⟨c, hc⟩
    refine ⟨fun i => c (toFin i), ?_⟩
    rw [hc]; symm
    rw [← isum_comp_bij ofFin ofFin_bij.1 ofFin_bij.2 (fun i => c (toFin i) • u i)]
    simp only [toFin_ofFin]
  · intro ⟨c, hc⟩
    refine ⟨fun j => c (ofFin j), ?_⟩
    rw [hc, ← isum_comp_bij ofFin ofFin_bij.1 ofFin_bij.2]

/-- A space spanned by a finite family is finite-dimensional. -/
theorem finDim_of_spans {ι : Type w} [FiniteType ι] {u : ι → V} (hu : Spans K u) : FinDim K V :=
  ⟨card ι, fun j => u (ofFin j), fun x => inSpan_ofFin.2 (hu x)⟩

/-- The defining properties of the dimension of a finite-dimensional space. -/
theorem dim_spec (hF : IsField K) (hfin : FinDim K V) :
    (∃ u : Fin (dim K V) → V, LinIndep K u) ∧ ¬ ∃ u : Fin (dim K V + 1) → V, LinIndep K u := by
  classical
  obtain ⟨m, w', hw⟩ := hfin
  have h : ∃ n, ¬ ∃ u : Fin (n + 1) → V, LinIndep K u :=
    ⟨m, fun ⟨u, hu⟩ => by
      have := steinitz hF u w' hu (fun i => hw (u i))
      rw [card_fin, card_fin] at this; omega⟩
  have hd : dim K V = Classical.choose (FiniteType.exists_least _ h) := by
    unfold dim; simp only [h, ↓reduceDIte]
  have hspec := Classical.choose_spec (FiniteType.exists_least _ h)
  rw [← hd] at hspec
  refine ⟨?_, hspec.1⟩
  rcases hk : dim K V with _ | k
  · exact ⟨fun i => absurd i.isLt (Nat.not_lt_zero _), linIndep_empty _⟩
  · have := hspec.2 k (by omega)
    exact Classical.byContradiction fun hno => this hno

/-- **Every finite-dimensional space has a basis**, of size `dim K V`. -/
theorem exists_basis (hF : IsField K) (hfin : FinDim K V) :
    ∃ b : Fin (dim K V) → V, IsBasis K b := by
  obtain ⟨⟨u, hu⟩, hmax⟩ := dim_spec hF hfin
  refine ⟨u, hu, fun x => Classical.byContradiction fun hx => hmax ⟨_, linIndep_tcons hF hu hx⟩⟩

/-- An independent family has at most `dim K V` members. -/
theorem card_le_dim (hF : IsField K) (hfin : FinDim K V) {ι : Type w} [FiniteType ι]
    {u : ι → V} (hu : LinIndep K u) : card ι ≤ dim K V := by
  obtain ⟨b, _, hb⟩ := exists_basis hF hfin
  have := steinitz hF (fun j : Fin (card ι) => u (ofFin j)) b (linIndep_ofFin hu) (fun i => hb _)
  rwa [card_fin, card_fin] at this

/-- A spanning family has at least `dim K V` members. -/
theorem dim_le_card (hF : IsField K) (hfin : FinDim K V) {ι : Type w} [FiniteType ι]
    {u : ι → V} (hu : Spans K u) : dim K V ≤ card ι := by
  obtain ⟨b, hb, _⟩ := exists_basis hF hfin
  have := steinitz hF b (fun j : Fin (card ι) => u (ofFin j)) hb
    (fun i => inSpan_ofFin.2 (hu (b i)))
  rwa [card_fin, card_fin] at this

/-- **Dimension is well defined.** Every basis of a finite-dimensional space has exactly
`dim K V` members. -/
theorem card_eq_dim (hF : IsField K) (hfin : FinDim K V) {ι : Type w} [FiniteType ι]
    {b : ι → V} (hb : IsBasis K b) : card ι = dim K V :=
  Nat.le_antisymm (card_le_dim hF hfin hb.1) (dim_le_card hF hfin hb.2)

/-- **Any two bases have the same size.** -/
theorem card_basis_eq (hF : IsField K) {ι κ : Type w} [FiniteType ι] [FiniteType κ]
    {b : ι → V} {b' : κ → V} (hb : IsBasis K b) (hb' : IsBasis K b') : card ι = card κ := by
  have hfin := finDim_of_spans hb.2
  rw [card_eq_dim hF hfin hb, card_eq_dim hF hfin hb']

/-- An independent family with `dim K V` members spans, hence is a basis. -/
theorem spans_of_card_eq_dim (hF : IsField K) (hfin : FinDim K V) {ι : Type w} [FiniteType ι]
    {u : ι → V} (hu : LinIndep K u) (hc : card ι = dim K V) : Spans K u := by
  intro x
  apply Classical.byContradiction
  intro hx
  have h := linIndep_tcons hF (linIndep_ofFin hu) (fun h => hx (inSpan_ofFin.1 h))
  have := card_le_dim hF hfin h
  rw [card_fin] at this; omega

end Dimension

end Foundations.Algebra
