import Foundations.Langlands.Padic.Hensel

/-!
# Units of ℤₚ, the factorisation `x = pᵛ · u`, and ℤₚ is an integral domain

A `p`-adic integer is a **unit** (has an inverse in ℤₚ) exactly when it is not divisible by `p`,
i.e. when its residue mod `p` is nonzero. Concretely, if `u₁ ≢ 0 (mod p)` then each
approximation `uₙ` is invertible modulo `pⁿ`, and the inverses modulo `p, p², p³, …` are
compatible: they form the `p`-adic sequence of `u⁻¹`. (The inverse modulo `pⁿ⁺¹` is lifted from
the one modulo `pⁿ` by the Newton step `w ↦ w (2 − u w)`, as in Hensel's lemma.)

Every nonzero `x ∈ ℤₚ` is then `pᵛ · u` with `u` a unit: `v` is the number of leading zero digits
of `x`, and `u` is `x` with those digits removed. This is the local counterpart of unique
factorisation — at the place `p`, the only prime is `p` itself — and it shows at once that ℤₚ has
no zero divisors. ℤₚ is a *discrete valuation ring*, the basic local object; its fraction field
ℚₚ is built in `Field`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- Cancelling a nonzero factor in a divisibility of integers. -/
theorem int_dvd_cancel {a m n : Int} (ha : a ≠ 0) (h : a * m ∣ a * n) : m ∣ n := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, Int.eq_of_mul_eq_mul_left ha (by rw [hc]; grind)⟩

/-- **Inverses modulo prime powers.** If `p ∤ c` then for every `n` some `w` has
`pⁿ ∣ w c − 1`. -/
theorem exists_inv_pow {p : Nat} (hp : Prime p) {c : Int} (hc : ¬ (p : Int) ∣ c) :
    ∀ n, ∃ w : Int, (p : Int) ^ n ∣ w * c - 1
  | 0 => ⟨0, by rw [Int.pow_zero]; exact Int.one_dvd _⟩
  | n + 1 => by
    cases n with
    | zero =>
      obtain ⟨u, hu⟩ := exists_inv_mod hp hc
      exact ⟨u, by rw [Int.pow_one]; exact hu⟩
    | succ m =>
      obtain ⟨w, k, hk⟩ := exists_inv_pow hp hc (m + 1)
      refine ⟨w * (1 - (p : Int) ^ (m + 1) * k), -((p : Int) ^ m * k * k), ?_⟩
      have e1 : w * c = 1 + (p : Int) ^ (m + 1) * k := by omega
      have e2 : (p : Int) ^ (m + 1) = (p : Int) ^ m * p := Int.pow_succ _ _
      have e3 : (p : Int) ^ (m + 1 + 1) = (p : Int) ^ m * p * p := by
        rw [Int.pow_succ, e2]
      rw [e3, show w * (1 - (p : Int) ^ (m + 1) * k) * c = (w * c) * (1 - (p : Int) ^ (m + 1) * k)
        by grind, e1, e2]
      grind

/-- Inverses modulo `pⁿ` are unique and depend only on `c` modulo `pⁿ`. -/
theorem inv_unique {P w w' c c' : Int} (h1 : P ∣ w * c - 1) (h2 : P ∣ w' * c' - 1)
    (h3 : P ∣ c - c') : P ∣ w - w' := by
  rw [show w - w' = -w * (w' * c' - 1) + w' * (-(c - c') * w + (w * c - 1)) by grind]
  exact Int.dvd_add (Int.dvd_trans h2 (Int.dvd_mul_left _ _))
    (Int.dvd_trans (Int.dvd_add (Int.dvd_trans (Int.dvd_neg.2 h3) (Int.dvd_mul_right _ _)) h1)
      (Int.dvd_mul_left _ _))

namespace Zp

open PSeq

variable {p : Nat}

/-- A `p`-adic integer is **`p`-adically a unit** if it is not `≡ 0 (mod p)`. -/
def IsPUnit (x : Zp p) : Prop := ¬ ModPow 1 x 0

/-- If `p ∤ x₁` then `p ∤ xₙ` for every `n ≥ 1`. -/
theorem not_dvd_seq {a : PSeq p} (ha : ¬ (p : Int) ∣ a.seq 1) {n : Nat} (hn : 1 ≤ n) :
    ¬ (p : Int) ∣ a.seq n := fun h => ha (by
  have := a.coh_le hn; rw [Int.pow_one] at this
  rw [show a.seq 1 = a.seq n - (a.seq n - a.seq 1) by omega]; exact Int.dvd_sub h this)

/-- Existence of inverses of every approximation of a unit (trivially at `n = 0`). -/
theorem exists_inv_seq (hp : Prime p) {a : PSeq p} (ha : ¬ (p : Int) ∣ a.seq 1) (n : Nat) :
    ∃ w : Int, (p : Int) ^ n ∣ w * a.seq n - 1 := by
  cases n with
  | zero => exact ⟨0, by rw [Int.pow_zero]; exact Int.one_dvd _⟩
  | succ n => exact exists_inv_pow hp (not_dvd_seq ha (by omega)) _

/-- The inverse `p`-adic sequence of a unit. -/
noncomputable def invSeq (hp : Prime p) (a : PSeq p) (ha : ¬ (p : Int) ∣ a.seq 1) : PSeq p :=
  ⟨fun n => Classical.choose (exists_inv_seq hp ha n), fun n => by
    have h1 := Classical.choose_spec (exists_inv_seq hp ha (n + 1))
    have h2 := Classical.choose_spec (exists_inv_seq hp ha n)
    have hd : (p : Int) ^ n ∣ (p : Int) ^ (n + 1) := Int.pow_dvd_pow_of_le' (by omega)
    exact inv_unique (Int.dvd_trans hd h1) h2 (a.coh n)⟩

/-- The `p`-adic representative of `1` at every level. -/
theorem one_seq : ((1 : Zp p)) = mk (const 1) := rfl

/-- **Units of ℤₚ.** For `p` prime, `x` has an inverse in `ℤₚ` iff `x ≢ 0 (mod p)`. -/
theorem isUnit_iff (hp : Prime p) (x : Zp p) : (∃ y, x * y = 1) ↔ IsPUnit x := by
  induction x using ind with | h a => ?_
  constructor
  · rintro ⟨y, hy⟩ h0
    induction y using ind with | h b => ?_
    have h1 := mk_eq_mk.1 hy 1
    have h2 := modPow_mk.1 h0
    simp only [PSeq.mul, const, Int.pow_one] at h1 h2
    rw [show ((0 : Nat) : Int) = 0 from rfl, Int.sub_zero] at h2
    have : (p : Int) ∣ 1 := by
      rw [show (1 : Int) = a.seq 1 * b.seq 1 - (a.seq 1 * b.seq 1 - 1) by omega]
      exact Int.dvd_sub (Int.dvd_trans h2 (Int.dvd_mul_right _ _)) h1
    have := Int.eq_one_of_dvd_one (by omega) this; have := hp.1; omega
  · intro hu
    have ha : ¬ (p : Int) ∣ a.seq 1 := fun h => hu (modPow_mk.2 (by
      show _ ∣ a.seq 1 - 0; rw [Int.pow_one, Int.sub_zero]; exact h))
    refine ⟨mk (invSeq hp a ha), mk_eq_mk.2 fun n => ?_⟩
    have := Classical.choose_spec (exists_inv_seq hp ha n)
    show _ ∣ a.seq n * Classical.choose (exists_inv_seq hp ha n) - 1
    rwa [Int.mul_comm]

/-- The product of two units is a unit. -/
theorem IsPUnit.mul (hp : Prime p) {u w : Zp p} (hu : IsPUnit u) (hw : IsPUnit w) :
    IsPUnit (u * w) := by
  obtain ⟨u', hu'⟩ := (isUnit_iff hp u).2 hu
  obtain ⟨w', hw'⟩ := (isUnit_iff hp w).2 hw
  exact (isUnit_iff hp _).1 ⟨u' * w', by grind⟩

/-- `pᵛ` in `ℤₚ` is represented by the constant sequence `pᵛ`. -/
theorem pow_p_eq (v : Nat) : (p : Zp p) ^ v = mk (const ((p : Int) ^ v)) := by
  induction v with
  | zero => rfl
  | succ v ih =>
    show (p : Zp p) ^ v * (p : Zp p) = _
    rw [ih]; exact mk_eq_of_seq fun n => by simp [PSeq.mul, const, Int.pow_succ]

/-- **`pᵛ · u ≠ 0`** for a unit `u`. -/
theorem pow_mul_unit_ne_zero (hp : Prime p) (v : Nat) {u : Zp p} (hu : IsPUnit u) :
    (p : Zp p) ^ v * u ≠ 0 := by
  induction u using ind with | h a => ?_
  intro h
  have ha : ¬ (p : Int) ∣ a.seq 1 := fun h' => hu (modPow_mk.2 (by
    show _ ∣ a.seq 1 - 0; rw [Int.pow_one, Int.sub_zero]; exact h'))
  rw [pow_p_eq] at h
  have h1 := mk_eq_mk.1 h (v + 1)
  simp only [PSeq.mul, const] at h1
  rw [show ((0 : Nat) : Int) = 0 from rfl, Int.sub_zero] at h1
  rw [Int.pow_succ] at h1
  have hpv : (p : Int) ^ v ≠ 0 := Int.pow_ne_zero (by have := hp.1; omega)
  exact not_dvd_seq ha (n := v + 1) (by omega) (int_dvd_cancel hpv h1)

/-- **Factorisation in ℤₚ.** Every nonzero `x ∈ ℤₚ` is `pᵛ · u` with `u` a unit. -/
theorem eq_pow_mul_unit (hp : Prime p) {x : Zp p} (hx : x ≠ 0) :
    ∃ v : Nat, ∃ u : Zp p, IsPUnit u ∧ x = (p : Zp p) ^ v * u := by
  induction x using ind with | h a => ?_
  have hex : ∃ k, ¬ (p : Int) ^ k ∣ a.seq k := by
    apply Classical.byContradiction; intro h
    apply hx; apply mk_eq_mk.2; intro n
    show _ ∣ a.seq n - 0
    rw [Int.sub_zero]
    exact Classical.byContradiction fun h' => h ⟨n, h'⟩
  obtain ⟨k, hk, hmin⟩ := OF.nat_least _ hex
  have hk0 : k ≠ 0 := by intro h; subst h; exact hk (by rw [Int.pow_zero]; exact Int.one_dvd _)
  obtain ⟨v, rfl⟩ : ∃ v, k = v + 1 := ⟨k - 1, by omega⟩
  have hv : (p : Int) ^ v ∣ a.seq v := Classical.byContradiction (hmin v (by omega))
  -- `pᵛ` divides every later approximation
  have hall : ∀ n, (p : Int) ^ v ∣ a.seq (n + v) := fun n => by
    have := a.coh_le (n := v) (m := n + v) (by omega)
    rw [show a.seq (n + v) = (a.seq (n + v) - a.seq v) + a.seq v by omega]
    exact Int.dvd_add this hv
  let w : Nat → Int := fun n => Classical.choose (hall n)
  have hw : ∀ n, a.seq (n + v) = (p : Int) ^ v * w n := fun n => Classical.choose_spec (hall n)
  have hpv : (p : Int) ^ v ≠ 0 := Int.pow_ne_zero (by have := hp.1; omega)
  let u : PSeq p := ⟨w, fun n => by
    apply int_dvd_cancel hpv
    rw [← Int.pow_add, show (p : Int) ^ v * (w (n + 1) - w n) = a.seq (n + 1 + v) - a.seq (n + v)
      by rw [hw, hw]; grind, Nat.add_comm v n]
    exact a.coh_le (by omega)⟩
  refine ⟨v, mk u, ?_, ?_⟩
  · intro h0
    have h1 := modPow_mk.1 h0
    show False
    change (p : Int) ^ 1 ∣ w 1 - 0 at h1
    rw [Int.pow_one, Int.sub_zero] at h1
    apply hk
    rw [show a.seq (v + 1) = a.seq (1 + v) by rw [Nat.add_comm], hw, Int.pow_succ]
    exact Int.mul_dvd_mul_left _ h1
  · rw [pow_p_eq]
    apply mk_eq_mk.2; intro n
    show _ ∣ a.seq n - (p : Int) ^ v * w n
    rw [← hw]
    have := a.coh_le (n := n) (m := n + v) (by omega)
    rw [show a.seq n - a.seq (n + v) = -(a.seq (n + v) - a.seq n) by omega]
    exact Int.dvd_neg.2 this

/-- **ℤₚ is an integral domain.** For `p` prime, `x y = 0` forces `x = 0` or `y = 0`. -/
theorem eq_zero_or_eq_zero (hp : Prime p) {x y : Zp p} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  apply Classical.byContradiction; intro hne
  have hx : x ≠ 0 := fun h' => hne (Or.inl h')
  have hy : y ≠ 0 := fun h' => hne (Or.inr h')
  obtain ⟨a, u, hu, rfl⟩ := eq_pow_mul_unit hp hx
  obtain ⟨b, w, hw, rfl⟩ := eq_pow_mul_unit hp hy
  apply pow_mul_unit_ne_zero hp (a + b) (hu.mul hp hw)
  rw [Semiring.pow_add]; rw [← h]; grind

/-- `1 ≠ 0` in `ℤₚ` for `p ≥ 2`. -/
theorem one_ne_zero (hp : 2 ≤ p) : (1 : Zp p) ≠ 0 := fun h =>
  absurd (intCast_injective (a := 1) (b := 0) hp h) (by omega)

/-- Cancellation in ℤₚ: `c ≠ 0` and `c a = c b` give `a = b`. -/
theorem mul_left_cancel (hp : Prime p) {a b c : Zp p} (hc : c ≠ 0) (h : c * a = c * b) :
    a = b := by
  have : c * (a - b) = 0 := by grind
  rcases eq_zero_or_eq_zero hp this with h' | h'
  · exact absurd h' hc
  · grind

end Zp

end Foundations.Langlands.Padic
