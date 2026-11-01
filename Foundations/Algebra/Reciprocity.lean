import Foundations.Algebra.GaussLemma

/-!
# The law of quadratic reciprocity

For distinct odd primes `p` and `q`,

  `(p/q) · (q/p) = (-1)^(((p-1)/2) · ((q-1)/2))`:

the questions "is `p` a square mod `q`?" and "is `q` a square mod `p`?" have the same answer,
unless both primes are `≡ 3 (mod 4)`, in which case the answers are opposite. Euler found the
law empirically (1744–1783), and Legendre stated it and gave an incomplete proof (1785, 1798).
Gauss proved it in 1796, at nineteen, and published the proof in the *Disquisitiones
Arithmeticae* (1801). He called it the *theorema aureum*, the golden theorem, and gave eight
different proofs during his lifetime. Hundreds more have been found since. It is the first of
the "reciprocity laws" that run through modern number theory, up to class field theory and the
Langlands programme.

We formalise the proof Eisenstein published in 1844, a geometric reworking of Gauss's third
proof. It has two steps.

1. **From Gauss's lemma to a floor sum.** For odd `a` prime to `p`, the count `μ` in Gauss's
   lemma has the same parity as `Σ_{k=1}^{(p-1)/2} ⌊ka/p⌋`. (Sum the equations
   `ka = p⌊ka/p⌋ + rₖ` and use that the folded residues are a rearrangement of
   `1, …, (p-1)/2`.) So `(q/p) = (-1)^{Σ ⌊kq/p⌋}`.
2. **Counting lattice points.** Count the points `(x, y)` with `1 ≤ x ≤ (p-1)/2` and
   `1 ≤ y ≤ (q-1)/2` in the rectangle. None lies on the diagonal line `qx = py`, because `p ∤ qx`.
   Those below it number `Σₓ ⌊qx/p⌋`, those above number `Σ_y ⌊py/q⌋`. Hence
   `Σ ⌊kq/p⌋ + Σ ⌊kp/q⌋ = ((p-1)/2)((q-1)/2)`, and the law follows.

Sums are taken in `ℤ` over finite index types `Fin h`.
-/

namespace Foundations.Algebra

open FiniteType

/-! ## Sums of integers over `Fin n` -/

/-- A sum over `Fin n` of a function of the index value is a sum over `0, …, n-1`. -/
theorem isum_fin_val (n : Nat) (g : Nat → Int) :
    isum (fun k : Fin n => g k.val) = lsum ((List.range n).map g) := by
  show lsum ((List.finRange n).map (fun k => g k.val)) = _
  rw [← finRange_map_val, List.map_map]; rfl

/-- A sum of indicators counts. -/
theorem lsum_indicator (P : Nat → Prop) [DecidablePred P] : ∀ l : List Nat,
    lsum (l.map (fun k => if P k then (1 : Int) else 0)) = (l.countP (fun k => decide (P k)) : Int)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.countP_cons]
    show (if P a then (1 : Int) else 0) + lsum _ = _
    rw [lsum_indicator P l]
    by_cases h : P a <;> simp [h] <;> omega

/-- A sum of a constant over `Fin n`. -/
theorem isum_const_int (n : Nat) (c : Int) : isum (fun _ : Fin n => c) = n * c := by
  show lsum ((List.finRange n).map _) = _
  have : ∀ l : List (Fin n), lsum (l.map (fun _ => c)) = l.length * c := by
    intro l; induction l with
    | nil => show (0 : Int) = 0 * c; rw [Int.zero_mul]
    | cons _ l ih =>
      show c + lsum (l.map _) = ((l.length + 1 : Nat) : Int) * c
      rw [ih]; push_cast; rw [Int.add_mul, Int.one_mul, Int.add_comm]
  rw [this, List.length_finRange]

/-- Counting the `k < n` with `k < t`. -/
theorem countP_range_lt (t : Nat) : ∀ n, (List.range n).countP (fun k => decide (k < t)) = min n t
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_lt t n]
    by_cases h : n < t
    · simp [h]; omega
    · simp [h]; omega

/-! ## Step 1: Gauss's count and the floor sum -/

/-- The **floor sum** `Σ_{k=1}^{(p-1)/2} ⌊k a / p⌋`. -/
def floorSum (a p : Nat) : Int := isum (fun k : Fin (half p) => (((k.val + 1) * a / p : Nat) : Int))

/-- **Eisenstein's lemma.** For an odd prime `p` and odd `a` with `p ∤ a`, Gauss's count `μ` has
the same parity as the floor sum `Σ ⌊ka/p⌋`. -/
theorem floorSum_parity {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (ha : ¬ p ∣ a)
    (haodd : a % 2 = 1) : (floorSum a p - gaussMu a p) % 2 = 0 := by
  have ⟨_, _, h3⟩ := half_spec hp hodd
  let h := half p
  let R : Fin h → Int := fun k => (res a p k.val : Int)
  let I : Fin h → Int := fun k => if half p < res a p k.val then 1 else 0
  -- `ka = p ⌊ka/p⌋ + rₖ`.
  have hX : isum (fun k : Fin h => (((k.val + 1) * a : Nat) : Int)) =
      (p : Int) * floorSum a p + isum R := by
    unfold floorSum
    rw [isum_mul_left, ← isum_add]
    congr 1; funext k
    have := Nat.div_add_mod ((k.val + 1) * a) p
    show (((k.val + 1) * a : Nat) : Int) = (p : Int) * (((k.val + 1) * a / p : Nat) : Int) +
      (((k.val + 1) * a % p : Nat) : Int)
    omega
  -- `Σ ka = a · Σ k`.
  let S := isum (fun k : Fin h => ((k.val + 1 : Nat) : Int))
  have hXS : isum (fun k : Fin h => (((k.val + 1) * a : Nat) : Int)) = (a : Int) * S := by
    rw [isum_mul_left]; congr 1; funext k; push_cast; rw [Int.mul_comm]
  -- Folding: `fold = r + p·[r > p/2] - 2·[r > p/2]·r`.
  have hfold : isum (fun k : Fin h => (fold a p k.val : Int)) =
      isum R + (p : Int) * isum I + -(2 * isum (fun k => I k * R k)) := by
    rw [isum_mul_left, isum_mul_left, ← isum_neg, ← isum_add, ← isum_add]
    congr 1; funext k
    have hlt : res a p k.val < p := Nat.mod_lt _ (by omega)
    show (fold a p k.val : Int) = R k + p * I k + -(2 * (I k * R k))
    simp only [R, I]
    unfold fold
    by_cases hc : half p < res a p k.val
    · rw [ite_false_of (by omega), ite_true_of hc]
      have : ((p - res a p k.val : Nat) : Int) = p - res a p k.val := by omega
      rw [this]; omega
    · rw [ite_true_of (by omega), ite_false_of hc]; omega
  -- The folded residues are a rearrangement of `1, …, (p-1)/2`.
  have hperm : isum (fun k : Fin h => (fold a p k.val : Int)) = S := by
    show _ = isum (fun k : Fin h => ((k.val + 1 : Nat) : Int))
    rw [← isum_comp_bij (foldFin hp hodd ha) (foldFin_bij hp hodd ha).1 (foldFin_bij hp hodd ha).2
      (fun k : Fin h => ((k.val + 1 : Nat) : Int))]
    congr 1; funext k
    show (fold a p k.val : Int) = ((fold a p k.val - 1 + 1 : Nat) : Int)
    rw [Nat.sub_add_cancel (fold_bounds hp hodd ha k.isLt).1]
  have hI : isum I = gaussMu a p := by
    exact (isum_fin_val (half p) (fun n => if half p < res a p n then (1 : Int) else 0)).trans
      (lsum_indicator (fun n => half p < res a p n) _)
  rw [hI] at hfold
  -- Combine: `p (F - μ) = (a - 1) S - 2 T` is even.
  obtain ⟨b, hb⟩ : ∃ b, a = 2 * b + 1 := ⟨a / 2, by omega⟩
  have key : (p : Int) * (floorSum a p - gaussMu a p) =
      2 * ((b : Int) * S - isum (fun k => I k * R k)) := by
    rw [hXS, hb] at hX
    rw [hperm] at hfold
    push_cast at hX
    grind
  have hev : ((p : Int) * (floorSum a p - gaussMu a p)) % 2 = 0 := by
    rw [key]; exact Int.mul_emod_right 2 _
  rw [Int.mul_emod] at hev
  have hp2 : (p : Int) % 2 = 1 := by omega
  rw [hp2, Int.one_mul, Int.emod_emod] at hev
  exact hev

/-! ## Step 2: counting lattice points -/

section Lattice

variable {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) (hpo : p % 2 = 1) (hqo : q % 2 = 1)
  (hpq : p ≠ q)

include hp hq hpq in
/-- No lattice point of the rectangle lies on the diagonal: `q x ≠ p y`. -/
theorem lattice_off_diag {x : Nat} (hx0 : 0 < x) (hx : x < p) : ¬ p ∣ q * x := by
  intro hd
  rcases hp.dvd_mul hd with h | h
  · rcases hq.2 p h with h1 | h1
    · have := hp.1; omega
    · exact hpq h1
  · have := Nat.le_of_dvd hx0 h; omega

include hp hq hpo hqo hpq in
/-- **One column of lattice points.** For `1 ≤ x ≤ (p-1)/2`, the number of `y ∈ {1, …, (q-1)/2}`
with `p y < q x` is `⌊q x / p⌋`. -/
theorem column_count {x : Nat} (hx : x < half p) :
    (List.range (half q)).countP (fun y => decide (p * (y + 1) < q * (x + 1))) = q * (x + 1) / p := by
  have ⟨_, _, h3p⟩ := half_spec hp hpo
  have ⟨_, _, h3q⟩ := half_spec hq hqo
  have hp0 : 0 < p := by omega
  have hnd := lattice_off_diag hp hq hpq (x := x + 1) (by omega) (by omega)
  -- `⌊qx/p⌋ ≤ (q-1)/2`.
  have hle : q * (x + 1) / p ≤ half q := by
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hp0]
    have e1 : q * (x + 1) ≤ q * half p := Nat.mul_le_mul_left q (by omega)
    have e2 : 2 * (q * half p) + q = q * p := by rw [← h3p]; grind
    have e3 : 2 * ((half q + 1) * p) = q * p + p := by rw [← h3q]; grind
    show q * (x + 1) < (half q + 1) * p
    omega
  rw [← Nat.min_eq_right hle, ← countP_range_lt]
  apply List.countP_congr
  intro y _
  simp only [decide_eq_true_eq]
  rw [show y < q * (x + 1) / p ↔ y + 1 ≤ q * (x + 1) / p by omega, Nat.le_div_iff_mul_le hp0]
  constructor
  · intro h; rw [Nat.mul_comm] at h; omega
  · intro h
    rcases Nat.lt_or_ge ((y + 1) * p) (q * (x + 1)) with hl | hl
    · rw [Nat.mul_comm]; exact hl
    · exfalso; apply hnd; rw [show q * (x + 1) = (y + 1) * p by omega]; exact Nat.dvd_mul_left p _

include hp hq hpo hqo hpq in
/-- **Eisenstein's lattice-point count**: `Σ ⌊kq/p⌋ + Σ ⌊kp/q⌋ = ((p-1)/2)((q-1)/2)`. -/
theorem floorSum_add : floorSum q p + floorSum p q = (half p : Int) * half q := by
  let I1 : Fin (half p) → Fin (half q) → Int := fun x y =>
    if p * (y.val + 1) < q * (x.val + 1) then 1 else 0
  let I2 : Fin (half p) → Fin (half q) → Int := fun x y =>
    if q * (x.val + 1) < p * (y.val + 1) then 1 else 0
  have hcol : ∀ x : Fin (half p), isum (fun y => I1 x y) = ((q * (x.val + 1) / p : Nat) : Int) := by
    intro x
    rw [← column_count hp hq hpo hqo hpq x.isLt]
    exact (isum_fin_val (half q) (fun n => if p * (n + 1) < q * (x.val + 1) then (1 : Int) else 0)).trans
      (lsum_indicator (fun n => p * (n + 1) < q * (x.val + 1)) _)
  have hrow : ∀ y : Fin (half q), isum (fun x => I2 x y) = ((p * (y.val + 1) / q : Nat) : Int) := by
    intro y
    rw [← column_count hq hp hqo hpo (Ne.symm hpq) y.isLt]
    exact (isum_fin_val (half p) (fun n => if q * (n + 1) < p * (y.val + 1) then (1 : Int) else 0)).trans
      (lsum_indicator (fun n => q * (n + 1) < p * (y.val + 1)) _)
  have h1 : floorSum q p = isum (fun x => isum (fun y => I1 x y)) := by
    unfold floorSum; congr 1; funext x; rw [hcol, Nat.mul_comm q]
  have h2 : floorSum p q = isum (fun x => isum (fun y => I2 x y)) := by
    unfold floorSum; rw [isum_comm]; congr 1; funext y; rw [hrow, Nat.mul_comm p]
  have hone : ∀ x y, I1 x y + I2 x y = 1 := by
    intro x y
    have ⟨_, _, h3p⟩ := half_spec hp hpo
    have hne : p * (y.val + 1) ≠ q * (x.val + 1) := fun e =>
      lattice_off_diag hp hq hpq (x := x.val + 1) (by omega) (by have := x.isLt; omega)
        ⟨y.val + 1, e.symm⟩
    simp only [I1, I2]
    by_cases hc : p * (y.val + 1) < q * (x.val + 1)
    · rw [ite_true_of hc, ite_false_of (by omega)]; rfl
    · rw [ite_false_of hc, ite_true_of (by omega)]; rfl
  rw [h1, h2, ← isum_add]
  rw [show (fun x => isum (fun y => I1 x y) + isum (fun y => I2 x y)) =
      fun _ : Fin (half p) => ((half q : Nat) : Int) * 1 from funext fun x => by
        rw [← isum_add, show (fun y => I1 x y + I2 x y) = fun _ => (1 : Int) from funext (hone x),
          isum_const_int]]
  rw [isum_const_int, Int.mul_one]

end Lattice

/-! ## The theorem -/

/-- **The law of quadratic reciprocity** (Gauss's *theorema aureum*). For distinct odd primes `p`
and `q`, `(q/p) · (p/q) = (-1)^(((p-1)/2) · ((q-1)/2))`. -/
theorem quadratic_reciprocity {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) (hpo : p % 2 = 1)
    (hqo : q % 2 = 1) (hpq : p ≠ q) :
    legendre q p * legendre p q = (-1) ^ (half p * half q) := by
  have hpq' : ¬ p ∣ q := fun h => by
    rcases hq.2 p h with h1 | h1
    · have := hp.1; omega
    · exact hpq h1
  have hqp' : ¬ q ∣ p := fun h => by
    rcases hp.2 q h with h1 | h1
    · have := hq.1; omega
    · exact hpq h1.symm
  rw [gauss_lemma hp hpo hpq', gauss_lemma hq hqo hqp', ← Int.pow_add]
  have e1 := floorSum_parity hp hpo hpq' hqo
  have e2 := floorSum_parity hq hqo hqp' hpo
  have e3 : floorSum q p + floorSum p q = ((half p * half q : Nat) : Int) := by
    rw [floorSum_add hp hq hpo hqo hpq]; push_cast; rfl
  rw [neg_one_pow_int, neg_one_pow_int]
  generalize half p * half q = N at e3 ⊢
  have hpar : (gaussMu q p + gaussMu p q) % 2 = N % 2 := by
    have : ((gaussMu q p + gaussMu p q : Nat) : Int) % 2 = (N : Int) % 2 := by
      push_cast; omega
    omega
  rw [hpar]

/-- **Reciprocity, classical form.** For distinct odd primes `p`, `q`: if either is `≡ 1 (mod 4)`
then `(p/q) = (q/p)`; if both are `≡ 3 (mod 4)` then `(p/q) = -(q/p)`. -/
theorem quadratic_reciprocity' {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) (hpo : p % 2 = 1)
    (hqo : q % 2 = 1) (hpq : p ≠ q) :
    ((p % 4 = 1 ∨ q % 4 = 1) → legendre p q = legendre q p) ∧
    ((p % 4 = 3 ∧ q % 4 = 3) → legendre p q = -legendre q p) := by
  have hr := quadratic_reciprocity hp hq hpo hqo hpq
  have hpq' : ¬ p ∣ q := fun h => by
    rcases hq.2 p h with h1 | h1
    · have := hp.1; omega
    · exact hpq h1
  have hcases := legendre_cases hp hpo hpq'
  rw [neg_one_pow_int] at hr
  have hpar : (half p * half q) % 2 = 0 ↔ (p % 4 = 1 ∨ q % 4 = 1) := by
    unfold half
    rw [Nat.mul_mod]
    have : (p - 1) / 2 % 2 = 0 ∨ (p - 1) / 2 % 2 = 1 := by omega
    have : (q - 1) / 2 % 2 = 0 ∨ (q - 1) / 2 % 2 = 1 := by omega
    constructor
    · intro h
      rcases ‹(p - 1) / 2 % 2 = 0 ∨ _› with h1 | h1 <;>
        rcases ‹(q - 1) / 2 % 2 = 0 ∨ _› with h2 | h2 <;> rw [h1, h2] at h <;> first | omega | simp at h
    · intro h
      rcases h with h | h
      · rw [show (p - 1) / 2 % 2 = 0 by omega]; simp
      · rw [show (q - 1) / 2 % 2 = 0 by omega]; simp
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · rw [ite_true_of (hpar.2 h)] at hr
    rcases hcases with ⟨hl, _⟩ | ⟨hl, _⟩ <;> rw [hl] at hr ⊢ <;> omega
  · rw [ite_false_of (fun e => by rcases hpar.1 e with e | e <;> omega)] at hr
    rcases hcases with ⟨hl, _⟩ | ⟨hl, _⟩ <;> rw [hl] at hr ⊢ <;> omega

end Foundations.Algebra
