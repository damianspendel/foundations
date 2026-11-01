import Foundations.Topology.Tychonoff

/-!
# Vitali's non-measurable set

Lebesgue (1902) asked for a "measure" of *every* set of reals: a length that is countably
additive, invariant under translation, and gives an interval its length. Giuseppe **Vitali**
showed in 1905 that no such thing exists. We prove the version on the circle `[0, 1)`, where
translation is taken modulo `1`:

  **There is no function `μ` on all subsets of `[0, 1)`, with values `≥ 0`, `μ [0, 1) = 1`,
  invariant under translation mod 1, and countably additive.**

*The construction.* Call `x ~ y` if `x − y` is rational. Using the **axiom of choice**, pick one
representative of each equivalence class inside `[0, 1)`: this is the Vitali set `V`. Its
translates `V + q (mod 1)` by the rationals `q ∈ [0, 1)` are pairwise disjoint and cover `[0, 1)`.
There are countably many of them, all of the same measure `μ V`. If `μ V = 0`, countable
additivity gives `μ [0, 1) = 0`; if `μ V > 0`, then already finitely many translates have total
measure `> 1`. Either way: contradiction.

*Consequences.* Measure theory must give up measuring *all* sets: Lebesgue measure lives on a
σ-algebra of **measurable sets**, and Vitali's set is not among them. The use of choice is
essential: Robert Solovay (1970) built a model of set theory without full choice (but with
dependent choice) in which every set of reals is Lebesgue measurable. In three dimensions even
*finite* additivity fails for all sets: the **Banach–Tarski paradox** (1924) decomposes a ball
into finitely many pieces that can be reassembled by rigid motions into two balls of the same
size — again using choice, and again with non-measurable pieces.

Our proof is fully formal; the choice of representatives is `Classical.epsilon`.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace Vitali

/-- The unit interval `[0, 1)`. -/
def I (x : R) : Prop := 0 ≤ x ∧ x < 1

/-- `x ~ y`: the difference `x − y` is a rational number `a/(n+1)`. -/
def Rel (x y : R) : Prop := ∃ a : Int, ∃ n : Nat, x - y = (a : R) / ((n : R) + 1)

/-- `n + 1 > 0` in `R`. -/
theorem succ_pos (n : Nat) : (0 : R) < (n : R) + 1 := by
  have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg; grind

/-- `~` is reflexive. -/
theorem rel_refl (x : R) : Rel x x := ⟨0, 0, by grind⟩

/-- `~` is symmetric. -/
theorem rel_symm {x y : R} (h : Rel x y) : Rel y x := by
  obtain ⟨a, n, h⟩ := h
  have := succ_pos n
  exact ⟨-a, n, by grind⟩

/-- `~` is transitive. -/
theorem rel_trans {x y z : R} (h₁ : Rel x y) (h₂ : Rel y z) : Rel x z := by
  obtain ⟨a, n, h₁⟩ := h₁
  obtain ⟨b, m, h₂⟩ := h₂
  have := succ_pos n; have := succ_pos m
  refine ⟨a * ((m : Int) + 1) + b * ((n : Int) + 1), n * m + n + m, ?_⟩
  have e1 : (((n * m + n + m : Nat) : R)) + 1 = ((n : R) + 1) * ((m : R) + 1) := by grind
  have e2 : (((a * ((m : Int) + 1) + b * ((n : Int) + 1) : Int)) : R) =
      (a : R) * ((m : R) + 1) + (b : R) * ((n : R) + 1) := by
    have := Ring.intCast_natCast (α := R) m; have := Ring.intCast_natCast (α := R) n; grind
  rw [e1, e2]
  have hx : x - z = (x - y) + (y - z) := by grind
  rw [hx, h₁, h₂]
  generalize (a : R) = A; generalize (b : R) = B
  generalize (n : R) = N at *; generalize (m : R) = M at *
  have i1 := Field.mul_inv_cancel (show N + 1 ≠ 0 by grind)
  have i2 := Field.mul_inv_cancel (show M + 1 ≠ 0 by grind)
  have i3 : ((N + 1) * (M + 1))⁻¹ = (N + 1)⁻¹ * (M + 1)⁻¹ := by
    have := Field.mul_inv_cancel (show (N + 1) * (M + 1) ≠ 0 by grind)
    grind
  rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv, Field.div_eq_mul_inv, i3]
  grind

/-- The fraction `m/(n+1)` is related to `0`. -/
theorem rel_frac_zero (m n : Nat) : Rel ((m : R) / ((n : R) + 1)) 0 :=
  ⟨m, n, by rw [Ring.intCast_natCast]; grind⟩

/-! ## The Vitali set -/

/-- Every real is related to some point of `[0, 1)` (subtract the integer part). -/
theorem exists_rep (x : R) : ∃ y, (I y ∧ Rel y x) := by
  obtain ⟨m, h1, h2⟩ := exists_floor (K := R) archimedean x
  exact ⟨x - m, ⟨by grind, by grind⟩, -m, 0, by grind⟩

/-- `R` is non-empty (needed for the choice operator). -/
instance : Nonempty R := ⟨0⟩

/-- The chosen representative of the class of `x` (axiom of choice). -/
noncomputable def rep (x : R) : R := Classical.epsilon (fun y => I y ∧ Rel y x)

/-- The representative lies in `[0, 1)` and is related to `x`. -/
theorem rep_spec (x : R) : I (rep x) ∧ Rel (rep x) x :=
  Classical.epsilon_spec (exists_rep x)

/-- Related points have the same representative: the choice depends only on the class. -/
theorem rep_eq {x y : R} (h : Rel x y) : rep x = rep y := by
  have : (fun z => I z ∧ Rel z x) = (fun z => I z ∧ Rel z y) := funext fun z => propext
    ⟨fun ⟨h1, h2⟩ => ⟨h1, rel_trans h2 h⟩, fun ⟨h1, h2⟩ => ⟨h1, rel_trans h2 (rel_symm h)⟩⟩
  unfold rep; rw [this]

/-- **The Vitali set**: the points of `[0, 1)` that are the chosen representatives of their
class. -/
def V (x : R) : Prop := I x ∧ rep x = x

/-- Two related points of `V` are equal. -/
theorem V_unique {v w : R} (hv : V v) (hw : V w) (h : Rel v w) : v = w := by
  rw [← hv.2, ← hw.2]; exact rep_eq h

/-- Every point of `[0, 1)` is related to a point of `V`. -/
theorem V_cover (x : R) : V (rep x) ∧ Rel x (rep x) :=
  ⟨⟨(rep_spec x).1, rep_eq (rep_spec x).2⟩, rel_symm (rep_spec x).2⟩

/-- The translate `A + r (mod 1)` of a subset `A ⊆ [0, 1)`. -/
def shift (A : R → Prop) (r : R) (x : R) : Prop := I x ∧ (A (x - r) ∨ A (x - r + 1))

/-- **Translates of `V` by distinct related amounts are disjoint.** -/
theorem shift_disjoint {r s : R} (hr : I r) (hs : I s) (hrs : r ≠ s) (hrel : Rel r s) {x : R}
    (h1 : shift V r x) (h2 : shift V s x) : False := by
  obtain ⟨a, n, hrel⟩ := hrel
  have hn := succ_pos n
  have hlem : ∀ v w : R, V v → V w → ∀ e : Int, v - w = (s - r) + (e : R) → False := by
    intro v w hv hw e he
    have hvw : v = w := V_unique hv hw ⟨-a + e * ((n : Int) + 1), n, by
      have := Ring.intCast_natCast (α := R) n
      have : (((-a + e * ((n : Int) + 1)) : Int) : R) = -(a : R) + (e : R) * ((n : R) + 1) := by
        grind
      rw [this, he]; grind⟩
    have hv := hv.1; have hw := hw.1
    unfold I at hr hs hv hw
    have h1' : (-2 : R) < (e : R) := by grind
    have h2' : (e : R) < (2 : R) := by grind
    have k1 := (intCast_lt (K := R) (a := -2) (b := e)).1 (by grind)
    have k2 := (intCast_lt (K := R) (a := e) (b := 2)).1 (by grind)
    have : e = -1 ∨ e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl | rfl <;> grind
  obtain ⟨_, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hlem _ _ h1 h2 0 (by grind)
  · exact hlem _ _ h1 h2 (-1) (by grind)
  · exact hlem _ _ h1 h2 1 (by grind)
  · exact hlem _ _ h1 h2 0 (by grind)

/-! ## An enumeration of the rationals in `[0, 1)` -/

/-- Walk through the pairs `(n, m)` with `m ≤ n`: `(0,0), (1,0), (1,1), (2,0), …`. -/
def tri : Nat → Nat × Nat
  | 0 => (0, 0)
  | k + 1 => if (tri k).2 < (tri k).1 then ((tri k).1, (tri k).2 + 1) else ((tri k).1 + 1, 0)

/-- Every pair `(n, m)` with `m ≤ n` is reached. -/
theorem tri_surj : ∀ n m, m ≤ n → ∃ k, tri k = (n, m) := by
  intro n
  induction n with
  | zero => intro m hm; exact ⟨0, by rw [show m = 0 by omega]; rfl⟩
  | succ n ih =>
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨k, hk⟩ := ih n (Nat.le_refl n)
      exact ⟨k + 1, by simp [tri, hk]⟩
    | succ m ihm =>
      intro hm
      obtain ⟨k, hk⟩ := ihm (by omega)
      exact ⟨k + 1, by simp [tri, hk]; omega⟩

/-- Along the walk, `m ≤ n`. -/
theorem tri_le (k : Nat) : (tri k).2 ≤ (tri k).1 := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    show (if (tri k).2 < (tri k).1 then ((tri k).1, (tri k).2 + 1) else ((tri k).1 + 1, 0)).2 ≤
      (if (tri k).2 < (tri k).1 then ((tri k).1, (tri k).2 + 1) else ((tri k).1 + 1, 0)).1
    split <;> simp <;> omega

/-- The `k`-th rational `m/(n+1)` of `[0, 1)`. -/
noncomputable def q (k : Nat) : R := ((tri k).2 : R) / (((tri k).1 : R) + 1)

/-- The fractions `m/(n+1)` with `m ≤ n` lie in `[0, 1)`. -/
theorem frac_mem {m n : Nat} (h : m ≤ n) : I ((m : R) / ((n : R) + 1)) := by
  have hn := succ_pos n
  have : (0 : R) ≤ (m : R) := OrderedRing.natCast_nonneg
  have : (m : R) ≤ (n : R) := OrderedRing.natCast_le_natCast_of_le _ _ h
  constructor
  · rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg (by grind) (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hn))
  · have e : (m : R) / ((n : R) + 1) * ((n : R) + 1) = (m : R) := by grind
    apply Classical.byContradiction; intro hc
    have := OrderedRing.mul_le_mul_of_nonneg_right (by grind : (1 : R) ≤ (m : R) / ((n : R) + 1))
      (Std.le_of_lt hn)
    grind

/-- The rationals `q k` lie in `[0, 1)`. -/
theorem q_mem (k : Nat) : I (q k) := frac_mem (tri_le k)

/-- Any two of them are related. -/
theorem q_rel (j k : Nat) : Rel (q j) (q k) :=
  rel_trans (rel_frac_zero _ _) (rel_symm (rel_frac_zero _ _))

/-- **The translates cover `[0, 1)`**: every `x ∈ [0, 1)` lies in `V + q k (mod 1)` for some `k`. -/
theorem shift_cover {x : R} (hx : I x) : ∃ k, shift V (q k) x := by
  obtain ⟨hv, hrel⟩ := V_cover x
  generalize rep x = v at hv hrel
  obtain ⟨a, n, h⟩ := hrel
  have hn := succ_pos n
  have hb : (0 : Int) < (n : Int) + 1 := by omega
  have h1 := Int.emod_nonneg a (b := (n : Int) + 1) (by omega)
  have h2 := Int.emod_lt_of_pos a hb
  have h3 := Int.emod_add_ediv_mul a ((n : Int) + 1)
  generalize a % ((n : Int) + 1) = e at h1 h2 h3
  generalize a / ((n : Int) + 1) = t at h3
  obtain ⟨m, rfl⟩ : ∃ m : Nat, e = (m : Int) := ⟨e.toNat, (Int.toNat_of_nonneg h1).symm⟩
  have hmn : m ≤ n := by omega
  have ha : (a : R) = (m : R) + (t : R) * ((n : R) + 1) := by
    rw [← h3]; have := Ring.intCast_natCast (α := R) m; have := Ring.intCast_natCast (α := R) n
    grind
  -- `x − v = r + t` with `r = m/(n+1) ∈ [0, 1)`.
  have hr := frac_mem (n := n) hmn
  have hxv : x - v = (m : R) / ((n : R) + 1) + (t : R) := by rw [h, ha]; grind
  have hvI := hv.1
  unfold I at hx hr hvI
  have k1 := (intCast_lt (K := R) (a := -2) (b := t)).1 (by grind)
  have k2 := (intCast_lt (K := R) (a := t) (b := 1)).1 (by grind)
  obtain ⟨k, hk⟩ := tri_surj n m hmn
  refine ⟨k, ⟨hx.1, hx.2⟩, ?_⟩
  have hqk : q k = (m : R) / ((n : R) + 1) := by unfold q; rw [hk]
  rw [hqk]
  have : t = -1 ∨ t = 0 := by omega
  rcases this with rfl | rfl
  · right; rw [show x - (m : R) / ((n : R) + 1) + 1 = v by grind]; exact hv
  · left; rw [show x - (m : R) / ((n : R) + 1) = v by grind]; exact hv

/-! ## No invariant measure -/

/-- A **translation-invariant probability measure on all subsets of `[0, 1)`**, countably
additive — the object Vitali shows cannot exist. -/
structure InvariantMeasure where
  /-- The measure of a set. -/
  μ : (R → Prop) → R
  /-- Measures are non-negative. -/
  nonneg : ∀ A, 0 ≤ μ A
  /-- The whole interval has measure `1`. -/
  unit : μ I = 1
  /-- Translation (mod 1) does not change the measure. -/
  invariant : ∀ A : R → Prop, (∀ x, A x → I x) → ∀ r, I r → μ (shift A r) = μ A
  /-- **Countable additivity**: for pairwise disjoint subsets of `[0, 1)`, the measure of the
  union is the sum of the series of measures. -/
  additive : ∀ A : Nat → R → Prop, (∀ n x, A n x → I x) →
    (∀ m n x, m ≠ n → A m x → A n x → False) → HasSum (fun n => μ (A n)) (μ (fun x => ∃ n, A n x))

namespace InvariantMeasure

variable (M : InvariantMeasure)

/-- The empty set has measure `0`. -/
theorem empty : M.μ (fun _ => False) = 0 := by
  have h := M.additive (fun _ _ => False) (fun _ _ h => h.elim) (fun _ _ _ _ h => h.elim)
  have e : (fun x => ∃ _ : Nat, False) = (fun (_ : R) => False) :=
    funext fun _ => propext ⟨fun ⟨_, h⟩ => h, fun h => h.elim⟩
  rw [e] at h
  have h2 := hasSum_succ_iff.2 h
  have := h.unique h2
  grind

/-- A series that vanishes from index `m` on sums to its `m`-th partial sum. -/
theorem hasSum_of_zero {b : Nat → R} {m : Nat} (hb : ∀ k, m ≤ k → b k = 0) :
    HasSum b (fsum b m) :=
  (tendsto_const (fsum b m)).congr_eventually m fun n hn => by
    obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
    show fsum b m = fsum b (m + j)
    induction j with
    | zero => rfl
    | succ j ih => rw [← Nat.add_assoc, fsum_succ, ← ih (by omega), hb (m + j) (by omega)]; grind

/-- **Monotonicity**: a subset of `[0, 1)` has measure at most `1`. -/
theorem le_one {U : R → Prop} (hU : ∀ x, U x → I x) : M.μ U ≤ 1 := by
  let A : Nat → R → Prop := fun n x => (n = 0 ∧ U x) ∨ (n = 1 ∧ I x ∧ ¬ U x)
  have h := M.additive A (fun n x h => by rcases h with ⟨_, h⟩ | ⟨_, h, _⟩; exact hU x h; exact h)
    (fun m n x hmn h1 h2 => by rcases h1 with ⟨rfl, h1⟩ | ⟨rfl, -, h1⟩ <;>
      rcases h2 with ⟨rfl, h2⟩ | ⟨rfl, -, h2⟩ <;> first | exact hmn rfl | exact h1 h2 | exact h2 h1)
  have e : (fun x => ∃ n, A n x) = I := funext fun x => propext
    ⟨fun ⟨n, h⟩ => by rcases h with ⟨_, h⟩ | ⟨_, h, _⟩; exact hU x h; exact h,
     fun hx => by by_cases hu : U x
                  · exact ⟨0, Or.inl ⟨rfl, hu⟩⟩
                  · exact ⟨1, Or.inr ⟨rfl, hx, hu⟩⟩⟩
  rw [e, M.unit] at h
  have hz : ∀ k, 2 ≤ k → M.μ (A k) = 0 := fun k hk => by
    have : A k = fun _ => False := funext fun x => propext
      ⟨fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega, fun h => h.elim⟩
    rw [this, M.empty]
  have h2 := h.unique (hasSum_of_zero hz)
  have e0 : A 0 = U := funext fun x => propext
    ⟨fun h => by rcases h with ⟨_, h⟩ | ⟨h, _⟩; exact h; omega, fun h => Or.inl ⟨rfl, h⟩⟩
  rw [fsum_succ, fsum_succ, fsum_zero, e0] at h2
  have := M.nonneg (A 1)
  grind

end InvariantMeasure

/-- **Vitali's theorem** (1905). There is no countably additive, translation-invariant (mod 1)
measure defined on *all* subsets of `[0, 1)` with `μ [0, 1) = 1`. -/
theorem vitali (M : InvariantMeasure) : False := by
  have hV : ∀ x, V x → I x := fun x h => h.1
  have hsh : ∀ r, I r → M.μ (shift V r) = M.μ V := fun r hr => M.invariant V hV r hr
  rcases (by have := M.nonneg V; grind : M.μ V = 0 ∨ 0 < M.μ V) with h0 | hpos
  · -- Countably many translates of measure `0` cover `[0, 1)`.
    let A : Nat → R → Prop := fun n x => (∀ k, k < n → q k ≠ q n) ∧ shift V (q n) x
    have h := M.additive A (fun n x h => h.2.1) (fun m n x hmn h1 h2 => by
      rcases Nat.lt_or_gt_of_ne hmn with hlt | hlt
      · exact shift_disjoint (q_mem m) (q_mem n) (h2.1 m hlt) (q_rel m n) h1.2 h2.2
      · exact shift_disjoint (q_mem m) (q_mem n) (fun e => h1.1 n hlt e.symm) (q_rel m n)
          h1.2 h2.2)
    have e : (fun x => ∃ n, A n x) = I := funext fun x => propext
      ⟨fun ⟨n, h⟩ => h.2.1, fun hx => by
        obtain ⟨k, hk⟩ := shift_cover hx
        obtain ⟨k₀, hk₀, hmin⟩ := nat_least (fun j => q j = q k) ⟨k, rfl⟩
        exact ⟨k₀, fun j hj e => hmin j hj (e.trans hk₀), hk₀ ▸ hk⟩⟩
    rw [e, M.unit] at h
    have hz : ∀ n, M.μ (A n) = 0 := fun n => by
      by_cases hn : ∀ k, k < n → q k ≠ q n
      · have : A n = shift V (q n) := funext fun x => propext ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩
        rw [this, hsh _ (q_mem n), h0]
      · have : A n = fun _ => False := funext fun x => propext ⟨fun h => hn h.1, fun h => h.elim⟩
        rw [this, M.empty]
    have := h.unique (InvariantMeasure.hasSum_of_zero (m := 0) fun k _ => hz k)
    rw [fsum_zero] at this; grind
  · -- Finitely many disjoint translates already have total measure `> 1`.
    obtain ⟨m, hm⟩ := archimedean (1 / M.μ V)
    have hmV : 1 < (m : R) * M.μ V := by
      have := OrderedRing.mul_lt_mul_of_pos_right hm hpos
      have : 1 / M.μ V * M.μ V = 1 := by grind
      grind
    let r : Nat → R := fun k => (k : R) / ((m : R) + 1)
    have hr : ∀ k, k < m → I (r k) := fun k hk => frac_mem (by omega)
    have hrinj : ∀ j k, r j = r k → j = k := fun j k e => by
      have hm := succ_pos m
      have : (j : R) = (k : R) := by
        have : (j : R) = r j * ((m : R) + 1) := by show _ = _ / _ * _; grind
        rw [this, e]; show _ / _ * _ = _; grind
      exact Nat.le_antisymm (OrderedRing.le_of_natCast_le_natCast (R := R) _ _ (by grind))
        (OrderedRing.le_of_natCast_le_natCast (R := R) _ _ (by grind))
    let A : Nat → R → Prop := fun k x => k < m ∧ shift V (r k) x
    have h := M.additive A (fun n x h => h.2.1) (fun j k x hjk h1 h2 =>
      shift_disjoint (hr j h1.1) (hr k h2.1) (fun e => hjk (hrinj j k e))
        (rel_trans (rel_frac_zero j m) (rel_symm (rel_frac_zero k m))) h1.2 h2.2)
    have hz : ∀ k, m ≤ k → M.μ (A k) = 0 := fun k hk => by
      have : A k = fun _ => False := funext fun x => propext ⟨fun h => by omega, fun h => h.elim⟩
      rw [this, M.empty]
    have hsum := h.unique (InvariantMeasure.hasSum_of_zero hz)
    have hval : ∀ j, j ≤ m → fsum (fun k => M.μ (A k)) j = (j : R) * M.μ V := by
      intro j
      induction j with
      | zero => intro _; rw [fsum_zero]; grind
      | succ j ih =>
        intro hj
        have : A j = shift V (r j) := funext fun x => propext ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
        rw [fsum_succ, ih (by omega), this, hsh _ (hr j (by omega))]; grind
    rw [hval m (Nat.le_refl m)] at hsum
    have := M.le_one (U := fun x => ∃ n, A n x) fun x ⟨n, h⟩ => h.2.1
    grind

end Vitali

end Foundations.Topology
