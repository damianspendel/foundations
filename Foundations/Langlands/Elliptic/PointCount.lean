import Foundations.Langlands.Elliptic.Weierstrass
import Foundations.Langlands.Elliptic.Fp

/-!
# Counting points over `𝔽_p`

Over a finite field an elliptic curve has finitely many points, and their number is the first
arithmetic invariant one meets. For `E` over `𝔽_p` write `#E(𝔽_p)` for the number of points,
including `O`, and

  `a_p = p + 1 − #E(𝔽_p)`.

Heuristically each `x ∈ 𝔽_p` gives on average one point (two square roots half of the time),
so `#E(𝔽_p) ≈ p + 1` and `a_p` measures the error. **Artin** conjectured in his thesis (1924)
the bound `|a_p| ≤ 2√p`, and **Hasse** proved it in 1933 (the Riemann hypothesis for elliptic
curves over finite fields), using the Frobenius endomorphism. The bound is not proved here; we
check it, as `a_p² ≤ 4p`, on finitely many examples (`Examples`).

This file defines, for a curve `E` over `Fp p`:
* `affinePoints E` — the list of all `(x, y) ∈ 𝔽_p²` on `E`, without repetitions
  (`mem_affinePoints`, `nodup_affinePoints`);
* `card E = #affinePoints + 1` (the `+ 1` is `O`), and `ap E = p + 1 − card E`.

Since `Fp p` has computable arithmetic, `card E` for a concrete curve and small `p` is computed
by the kernel with plain `decide`.
-/

namespace Foundations.Langlands.Elliptic

namespace Curve

variable {p : Nat}

/-- The elements `0, 1, …, p − 1` of `𝔽_p`, in order. -/
def elems (p : Nat) : List (Fp p) := List.finRange p

/-- Every element of `𝔽_p` is listed. -/
theorem mem_elems (x : Fp p) : x ∈ elems p := List.mem_finRange (n := p) x

/-- The list of elements has no repetitions. -/
theorem nodup_elems : (elems p).Nodup := List.nodup_finRange p

/-- All pairs `(x, y)` of elements of `𝔽_p`, listed with `x` as the outer index. -/
def allPairs (p : Nat) : List (Fp p × Fp p) :=
  (elems p).flatMap fun x => (elems p).map fun y => (x, y)

/-- Every pair occurs in `allPairs`. -/
theorem mem_allPairs (q : Fp p × Fp p) : q ∈ allPairs p := by
  unfold allPairs
  rw [List.mem_flatMap]
  exact ⟨q.1, mem_elems q.1, List.mem_map.2 ⟨q.2, mem_elems q.2, rfl⟩⟩

/-- `allPairs` has no repetitions. -/
theorem nodup_allPairs : (allPairs p).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  unfold allPairs
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.nodup_iff_pairwise_ne.1 nodup_elems).imp
      (fun h e => h (congrArg Prod.snd e))
  · exact (List.nodup_iff_pairwise_ne.1 nodup_elems).imp (fun h u hu v hv e => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hu
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hv
      exact h (congrArg Prod.fst e))

variable [PrimeNat p] (E : Curve (Fp p))

/-- Membership of the curve is decidable over `𝔽_p`. -/
instance (x y : Fp p) : Decidable (E.OnCurve x y) :=
  inferInstanceAs (Decidable (y ^ 2 = x ^ 3 + E.a * x + E.b))

/-- **Affine points over `𝔽_p`.** The list of all `(x, y) ∈ 𝔽_p²` with
`y² = x³ + a x + b`. -/
def affinePoints : List (Fp p × Fp p) :=
  (allPairs p).filter fun q => decide (E.OnCurve q.1 q.2)

/-- A pair is in `affinePoints E` exactly when it lies on the curve. -/
theorem mem_affinePoints (x y : Fp p) : (x, y) ∈ E.affinePoints ↔ E.OnCurve x y := by
  unfold affinePoints
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_allPairs _, h⟩⟩

/-- `affinePoints E` lists each affine point exactly once. -/
theorem nodup_affinePoints : E.affinePoints.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact (List.nodup_iff_pairwise_ne.1 nodup_allPairs).filter _

/-- **The number of points** `#E(𝔽_p)`: the affine points together with `O`. -/
def card : Nat := E.affinePoints.length + 1

/-- **The trace of Frobenius** `a_p = p + 1 − #E(𝔽_p)`. -/
def ap : Int := (p : Int) + 1 - (E.card : Int)

end Curve

/-! ## Primality of small numbers, by a bounded check -/

/-- A number `p ≥ 2` all of whose divisors `d ≤ p` are `1` or `p` is prime; for a concrete `p`
the hypothesis is a bounded check that `decide` can do. -/
theorem isPrime_of_check (p : Nat) (h2 : 2 ≤ p)
    (h : ∀ d, d < p + 1 → d ∣ p → d = 1 ∨ d = p) : Foundations.Algebra.IsPrime p :=
  ⟨h2, fun d hd => h d (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd)) hd⟩

/-- `5` is prime. -/
instance : PrimeNat 5 := ⟨isPrime_of_check 5 (by decide) (by decide)⟩
/-- `7` is prime. -/
instance : PrimeNat 7 := ⟨isPrime_of_check 7 (by decide) (by decide)⟩
/-- `11` is prime. -/
instance : PrimeNat 11 := ⟨isPrime_of_check 11 (by decide) (by decide)⟩
/-- `13` is prime. -/
instance : PrimeNat 13 := ⟨isPrime_of_check 13 (by decide) (by decide)⟩
/-- `17` is prime. -/
instance : PrimeNat 17 := ⟨isPrime_of_check 17 (by decide) (by decide)⟩
/-- `19` is prime. -/
instance : PrimeNat 19 := ⟨isPrime_of_check 19 (by decide) (by decide)⟩
/-- `23` is prime. -/
instance : PrimeNat 23 := ⟨isPrime_of_check 23 (by decide) (by decide)⟩
/-- `29` is prime. -/
instance : PrimeNat 29 := ⟨isPrime_of_check 29 (by decide) (by decide)⟩

end Foundations.Langlands.Elliptic
