import Foundations.Langlands.Padic.Valuation
import Foundations.Numbers.Cauchy

/-!
# The product formula

Every nonzero rational number `x` has one "size" for each place of ℚ: the ordinary absolute value
`|x|_∞` (the *infinite place*) and the `p`-adic absolute values `|x|ₚ`, one for each prime `p`
(the *finite places*). These sizes are not independent. Writing `x = ± ∏ p^(vₚ(x))` by the
fundamental theorem of arithmetic, `|x|_∞ = ∏ p^(vₚ(x))` while `|x|ₚ = p^(−vₚ(x))`, so

  `∏ₚ |x|ₚ · |x|_∞ = 1`.

Only finitely many factors differ from `1`, so the product is really finite. This
**product formula** is the simplest instance of the *local–global* philosophy: information at all
places together is constrained by a global identity. It is the arithmetic analogue of the fact
that a nonzero rational function on the Riemann sphere has as many zeros as poles, counted with
multiplicity — Hensel's analogy between primes and points again.

Concretely we prove: for every `x ≠ 0` there is `N` such that `|x|ₚ = 1` for all `p ≥ N`, and
the product of `|x|ₚ` over the primes `p < M` times `|x|_∞` equals `1` for every `M ≥ N`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Foundations.NumberTheory Lean.Grind

/-! ## Finite products over primes -/

/-- The product `∏_{p < N, p prime} g(p)` of the values of `g` at the primes below `N`. -/
noncomputable def primeProd (g : Nat → Q) : Nat → Q
  | 0 => 1
  | N + 1 => open Classical in primeProd g N * (if Prime N then g N else 1)

/-- The product over primes of a pointwise product is the product of the products. -/
theorem primeProd_mul (g h : Nat → Q) (N : Nat) :
    primeProd (fun p => g p * h p) N = primeProd g N * primeProd h N := by
  induction N with
  | zero => show (1 : Q) = 1 * 1; grind
  | succ N ih =>
    simp only [primeProd, ih]
    by_cases hN : Prime N <;> simp [hN] <;> grind

/-- The product over primes of inverses is the inverse of the product. -/
theorem primeProd_inv (g : Nat → Q) (N : Nat) :
    primeProd (fun p => (g p)⁻¹) N = (primeProd g N)⁻¹ := by
  induction N with
  | zero => show (1 : Q) = 1⁻¹; rw [Field.inv_one]
  | succ N ih =>
    simp only [primeProd, ih]
    by_cases hN : Prime N <;> simp [hN, Field.inv_mul, Field.inv_one]

/-- The product over primes only depends on the values at primes below `N`. -/
theorem primeProd_congr {g h : Nat → Q} {N : Nat} (H : ∀ p, Prime p → p < N → g p = h p) :
    primeProd g N = primeProd h N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [primeProd, ih (fun p hp hpN => H p hp (by omega))]
    by_cases hN : Prime N
    · simp [hN, H N hN (by omega)]
    · simp [hN]

/-- A product of ones is one. -/
theorem primeProd_one (N : Nat) : primeProd (fun _ => 1) N = 1 := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [primeProd, ih]; split <;> grind

/-- The product of a function that is `1` except at the prime `q`. -/
theorem primeProd_single {q : Nat} (hq : Prime q) (c : Q) {N : Nat} (hN : q < N) :
    primeProd (fun p => open Classical in if p = q then c else 1) N = c := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [primeProd]
    by_cases h : q = N
    · subst h
      rw [primeProd_congr (h := fun _ => 1) (fun p _ hp => by simp; omega), primeProd_one]
      simp [hq]; grind
    · rw [ih (by omega)]
      by_cases hN : Prime N <;> simp [hN, Ne.symm h] <;> grind

/-- Factors at or beyond `N` that equal `1` do not change the product. -/
theorem primeProd_stable {g : Nat → Q} {N : Nat} (H : ∀ p, N ≤ p → g p = 1) :
    ∀ M, N ≤ M → primeProd g M = primeProd g N := by
  intro M hM
  induction M with
  | zero => have : N = 0 := by omega
            rw [this]
  | succ M ih =>
    by_cases h : N = M + 1
    · rw [h]
    · simp only [primeProd, ih (by omega), H M (by omega)]; split <;> grind

/-! ## Unique factorisation, multiplicatively -/

/-- For primes `p, q`: `vₚ(q) = 1` if `p = q` and `0` otherwise. -/
theorem vp_prime {p q : Nat} (hp : Prime p) (hq : Prime q) :
    vp p q = open Classical in if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst h; simp only [↓reduceIte]; exact vZ_self hp
  · simp only [h, ↓reduceIte]
    apply vp_eq (r := q) hp.1 (by simp)
    intro hd
    rcases hq.2 p hd with h1 | h1
    · have := hp.1; omega
    · exact h h1

/-- **Unique factorisation as a product formula.** For `1 ≤ m < N`,
`∏_{p < N prime} p^(vₚ(m)) = m`. -/
theorem primeProd_factor (N : Nat) : ∀ m, 1 ≤ m → m < N →
    primeProd (fun p => (p : Q) ^ (vp p m)) N = (m : Q) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro hm hmN
  by_cases h1 : m = 1
  · subst h1
    rw [primeProd_congr (h := fun _ => 1) (fun p hp _ => by rw [vp_one hp.1]; rfl),
      primeProd_one]
    grind
  · obtain ⟨q, hq, k, rfl⟩ := exists_prime_dvd (show 2 ≤ m by omega)
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    have hq2 := hq.1
    have hkm : k < q * k := by
      have := Nat.mul_le_mul_right k hq2; omega
    have hqN : q < N := by
      have := Nat.mul_le_mul_left q hk; omega
    rw [primeProd_congr (h := fun p => (open Classical in if p = q then (q : Q) else 1) *
        (p : Q) ^ (vp p k)) ?_]
    · rw [primeProd_mul, primeProd_single hq _ hqN, ih k hkm hk (by omega)]
      grind
    · intro p hp _
      rw [vp_mul hp (by omega) (by omega), vp_prime hp hq, Semiring.pow_add]
      by_cases hpq : p = q
      · subst hpq; simp [Semiring.pow_one]
      · simp [hpq, Semiring.pow_zero]

/-! ## The product formula -/

/-- A rational `n/d` equals `n · d⁻¹` in the field `ℚ`. -/
theorem mk_eq_mul_inv (n d : Int) (hd : 0 < d) : Q.mk n d hd = (n : Q) * (d : Q)⁻¹ := by
  have hd' : (d : Q) ≠ 0 := fun h => by have := (mk_eq_zero_iff Int.one_pos).1 h; omega
  have : Q.mk n d hd * (d : Q) = (n : Q) := by
    show Q.mk n d hd * Q.mk d 1 Int.one_pos = Q.mk n 1 Int.one_pos
    rw [Q.mk_mul, Q.mk_eq_mk]; grind
  rw [← this, Semiring.mul_assoc, Field.mul_inv_cancel hd', Semiring.mul_one]

/-- The `p`-adic absolute value of `n/d` (with `n ≠ 0`, `p` prime) is `p^(vₚ(d)) / p^(vₚ(n))`. -/
theorem padicAbs_mk {p : Nat} (hp : Prime p) {n d : Int} (hd : 0 < d) (hn : n ≠ 0) :
    padicAbs p (Q.mk n d hd) = (p : Q) ^ (vp p d.natAbs) * ((p : Q) ^ (vp p n.natAbs))⁻¹ := by
  have hx : Q.mk n d hd ≠ 0 := fun h => hn ((mk_eq_zero_iff hd).1 h)
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hp; grind
  rw [padicAbs_of_ne hx, vQ_mk hp hd hn,
    show -(((vZ p n : Nat) : Int) - (vZ p d : Nat)) = ((vZ p d : Nat) : Int) + -((vZ p n : Nat) : Int)
      by omega,
    Field.zpow_add hp0, Field.zpow_neg, Field.zpow_natCast, Field.zpow_natCast]
  rfl

/-- The ordinary absolute value of `n/d` is `|n| · d⁻¹`. -/
theorem abs_mk {n d : Int} (hd : 0 < d) :
    Q.abs (Q.mk n d hd) = (n.natAbs : Q) * ((d.natAbs : Nat) : Q)⁻¹ := by
  have e1 : ((d.natAbs : Nat) : Q) = (d : Q) := by
    have : (d.natAbs : Int) = d := by omega
    rw [← this]; rfl
  rw [e1]
  have hd' : (0 : Q) < (d : Q) := OrderedRing.pos_intCast_of_pos _ hd
  have hi := inv_pos' hd'
  rcases Int.lt_or_le n 0 with hn | hn
  rotate_left
  · have e2 : ((n.natAbs : Nat) : Q) = (n : Q) := by
      have : (n.natAbs : Int) = n := by omega
      rw [← this]; rfl
    rw [e2, mk_eq_mul_inv]
    have := OrderedRing.nonneg_intCast_of_nonneg (R := Q) _ hn
    exact Q.abs_of_nonneg (OrderedRing.mul_nonneg this (Std.le_of_lt hi))
  · have e2 : ((n.natAbs : Nat) : Q) = -(n : Q) := by
      have : (n.natAbs : Int) = -n := by omega
      have h3 : ((n.natAbs : Nat) : Q) = (((n.natAbs : Nat) : Int) : Q) := rfl
      rw [h3, this]; grind
    rw [e2, mk_eq_mul_inv]
    have := OrderedRing.neg_intCast_of_neg (R := Q) _ hn
    have hneg : (n : Q) * (d : Q)⁻¹ < 0 := OrderedRing.mul_neg_of_neg_of_pos this hi
    rw [Q.abs_of_neg hneg]; grind

/-- If `p > |n| ≥ 1` then `vₚ(n) = 0`. -/
theorem vp_eq_zero_of_lt {p m : Nat} (hp : 1 < p) (hm : 1 ≤ m) (h : m < p) : vp p m = 0 :=
  vp_eq (r := m) hp (by simp) (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)

/-- **The product formula.** For every nonzero rational `x` there is a bound `N` such that
`|x|ₚ = 1` for every `p ≥ N`, and for every `M ≥ N`,
`(∏_{p < M, p prime} |x|ₚ) · |x|_∞ = 1`. In short: `∏ₚ |x|ₚ · |x|_∞ = 1`. -/
theorem product_formula {x : Q} (hx : x ≠ 0) :
    ∃ N, (∀ p, N ≤ p → padicAbs p x = 1) ∧
      ∀ M, N ≤ M → primeProd (fun p => padicAbs p x) M * Q.abs x = 1 := by
  induction x using Q.ind with | h n d hd => ?_
  have hn : n ≠ 0 := fun h => hx ((mk_eq_zero_iff hd).2 h)
  have ha : 1 ≤ n.natAbs := by omega
  have hb : 1 ≤ d.natAbs := by omega
  refine ⟨n.natAbs + d.natAbs + 2, ?_, ?_⟩
  · -- far-away places see `x` as a unit
    intro p hp
    by_cases hpr : Prime p
    · rw [padicAbs_mk hpr hd hn, vp_eq_zero_of_lt (by omega) hb (by omega),
        vp_eq_zero_of_lt (by omega) ha (by omega)]
      simp [Semiring.pow_zero, Field.inv_one]; grind
    · rw [padicAbs_of_ne hx]
      have : vQ p (Q.mk n d hd) = 0 := by
        show fracVal p ⟨n, d, hd⟩ = 0
        unfold fracVal; simp [hpr]
      rw [this]; rfl
  · intro M hM
    have hfac := fun m (h1 : 1 ≤ m) (h2 : m < M) => primeProd_factor M m h1 h2
    rw [primeProd_congr (h := fun p => (p : Q) ^ (vp p d.natAbs) * ((p : Q) ^ (vp p n.natAbs))⁻¹)
        (fun p hp _ => padicAbs_mk hp hd hn),
      primeProd_mul, primeProd_inv (fun p => (p : Q) ^ (vp p n.natAbs)),
      hfac _ hb (by omega), hfac _ ha (by omega), abs_mk]
    have h1 : ((d.natAbs : Nat) : Q) ≠ 0 := by
      have := OrderedRing.pos_natCast_of_pos (R := Q) _ hb; grind
    have h2 : ((n.natAbs : Nat) : Q) ≠ 0 := by
      have := OrderedRing.pos_natCast_of_pos (R := Q) _ ha; grind
    have := Field.mul_inv_cancel h1
    have := Field.mul_inv_cancel h2
    grind

end Foundations.Langlands.Padic
