import Foundations.Langlands.Padic.Field

/-!
# The `p`-adic absolute value on ℚₚ, and ℚ inside ℚₚ

The factorisation `x = pᵛ · u` of `Units` is unique, so every nonzero `x ∈ ℤₚ` has a
well-defined **valuation** `v(x) ∈ ℕ`, the number of factors of `p` in `x`; for `x / pᵏ ∈ ℚₚ` the
valuation is `v(x) − k ∈ ℤ`. As on ℚ (`Valuation`), it is additive and satisfies
`v(x + y) ≥ min(v(x), v(y))`, and the **`p`-adic absolute value** `|q|ₚ = p^(−v(q))` on ℚₚ is
multiplicative and ultrametric.

Finally ℚ embeds in ℚₚ as a subfield: `n/d ↦ n · d⁻¹`, which makes sense because ℚₚ is a field
of characteristic `0`. In the language of the introduction, ℚₚ is the *local field* of ℚ at the
place `p`, just as ℝ is the local field at `∞`.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

namespace Zp

variable {p : Nat}

/-- `pᶜ w` with `c ≥ 1` is not a unit. -/
theorem not_isPUnit_pow_mul {c : Nat} (hc : 1 ≤ c) (w : Zp p) :
    ¬ IsPUnit ((p : Zp p) ^ c * w) := by
  induction w using ind with | h b => ?_
  intro hu; apply hu
  rw [pow_p_eq]
  apply modPow_mk.2
  show (p : Int) ^ 1 ∣ (p : Int) ^ c * b.seq 1 - 0
  rw [Int.pow_one, Int.sub_zero]
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [Int.pow_succ]
  exact Int.dvd_trans (Int.dvd_mul_left _ _) (Int.dvd_mul_right _ _)

/-- **Uniqueness of the factorisation.** `pᵃ u = pᵇ w` with units `u, w` forces `a = b`. -/
theorem pow_unique (hp : Prime p) {a b : Nat} {u w : Zp p} (hu : IsPUnit u) (hw : IsPUnit w)
    (h : (p : Zp p) ^ a * u = (p : Zp p) ^ b * w) : a = b := by
  have key : ∀ {a b : Nat} {u w : Zp p}, IsPUnit u → (p : Zp p) ^ a * u = (p : Zp p) ^ b * w →
      a < b → False := by
    intro a b u w hu h hab
    have hpa : (p : Zp p) ^ a ≠ 0 := by
      have := pow_mul_unit_ne_zero hp a (u := u) hu
      intro h0; apply this; rw [h0]; grind
    have : u = (p : Zp p) ^ (b - a) * w := by
      apply mul_left_cancel hp hpa
      rw [h, show b = a + (b - a) by omega, Semiring.pow_add]
      rw [show a + (b - a) - a = b - a by omega]; grind
    exact not_isPUnit_pow_mul (by omega) w (this ▸ hu)
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact (key hu h hab).elim
  · exact hab
  · exact (key hw h.symm hab).elim

/-- The **valuation** `v(x) ∈ ℕ` of a nonzero `p`-adic integer: `x = p^(v(x)) · u` with `u` a
unit (and `v(0) = 0` by convention). -/
noncomputable def val (hp : Prime p) (x : Zp p) : Nat :=
  open Classical in if h : x = 0 then 0 else Classical.choose (eq_pow_mul_unit hp h)

/-- The defining property of the valuation. -/
theorem val_spec (hp : Prime p) {x : Zp p} (hx : x ≠ 0) :
    ∃ u, IsPUnit u ∧ x = (p : Zp p) ^ (val hp x) * u := by
  unfold val; rw [dite_eq_right_of_eq_false (eq_false hx)]; exact Classical.choose_spec (eq_pow_mul_unit hp hx)

/-- `v(pᵃ u) = a` for a unit `u`. -/
theorem val_pow_mul (hp : Prime p) (a : Nat) {u : Zp p} (hu : IsPUnit u) :
    val hp ((p : Zp p) ^ a * u) = a := by
  obtain ⟨w, hw, he⟩ := val_spec hp (pow_mul_unit_ne_zero hp a hu)
  exact (pow_unique hp hu hw he).symm

/-- **Additivity of the valuation** on ℤₚ. -/
theorem val_mul (hp : Prime p) {x y : Zp p} (hx : x ≠ 0) (hy : y ≠ 0) :
    val hp (x * y) = val hp x + val hp y := by
  obtain ⟨u, hu, hxu⟩ := val_spec hp hx
  obtain ⟨w, hw, hyw⟩ := val_spec hp hy
  conv => lhs; rw [hxu, hyw]
  rw [show (p : Zp p) ^ val hp x * u * ((p : Zp p) ^ val hp y * w) =
    (p : Zp p) ^ (val hp x + val hp y) * (u * w) by rw [Semiring.pow_add]; grind]
  exact val_pow_mul hp _ (hu.mul hp hw)

/-- **Ultrametric property of the valuation** on ℤₚ. -/
theorem min_le_val_add (hp : Prime p) {x y : Zp p} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (val hp x) (val hp y) ≤ val hp (x + y) := by
  have gen : ∀ {x y : Zp p}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → val hp x ≤ val hp y →
      val hp x ≤ val hp (x + y) := by
    intro x y hx hy hxy hle
    obtain ⟨u, hu, hxu⟩ := val_spec hp hx
    obtain ⟨w, hw, hyw⟩ := val_spec hp hy
    have e : x + y = (p : Zp p) ^ val hp x * (u + (p : Zp p) ^ (val hp y - val hp x) * w) := by
      rw [hxu, hyw]
      conv => lhs; rw [show val hp y = val hp x + (val hp y - val hp x) by omega]
      rw [Semiring.pow_add]; grind
    have hs : u + (p : Zp p) ^ (val hp y - val hp x) * w ≠ 0 := by
      intro h0; apply hxy; rw [e, h0]; grind
    obtain ⟨t, ht, hst⟩ := val_spec hp hs
    rw [e, hst, ← Semiring.mul_assoc, ← Semiring.pow_add, val_pow_mul hp _ ht]
    omega
  rcases Nat.le_total (val hp x) (val hp y) with h | h
  · have := gen hx hy hxy h; omega
  · have := gen hy hx (by rwa [show y + x = x + y by grind]) h
    rw [show y + x = x + y by grind] at this; omega

end Zp

namespace Qp

variable {p : Nat} [hP : PrimeP p]

/-- Valuation of a representative `x / pᵏ`: `v(x) − k` (and `0` if `x = 0`). -/
noncomputable def repVal (a : Zp p × Nat) : Int :=
  open Classical in if a.1 = 0 then 0 else (Zp.val hP.prime a.1 : Int) - a.2

/-- `v(pˡ x) = l + v(x)` for nonzero `x`. -/
theorem val_pow_mul' (l : Nat) {x : Zp p} (hx : x ≠ 0) :
    Zp.val hP.prime ((p : Zp p) ^ l * x) = l + Zp.val hP.prime x := by
  rw [Zp.val_mul hP.prime (pow_ne_zero l) hx]
  have := Zp.val_pow_mul hP.prime l (u := 1) (fun h0 => by
    have := Zp.modPow_mk.1 h0
    change (p : Int) ^ 1 ∣ 1 - 0 at this
    rw [Int.pow_one, Int.sub_zero] at this
    have := Int.eq_one_of_dvd_one (by omega) this; have := hP.prime.1; omega)
  rw [Semiring.mul_one] at this; rw [this]

/-- The **valuation** `v : ℚₚ → ℤ`, `v(x / pᵏ) = v(x) − k` (with `v(0) = 0`). -/
noncomputable def val : Qp p → Int :=
  Quotient.lift repVal fun a b (h : (p : Zp p) ^ b.2 * a.1 = (p : Zp p) ^ a.2 * b.1) => by
    unfold repVal
    by_cases ha : a.1 = 0
    · have : b.1 = 0 := by
        rw [ha, Semiring.mul_zero] at h
        rcases Zp.eq_zero_or_eq_zero hP.prime h.symm with h' | h'
        · exact absurd h' (pow_ne_zero _)
        · exact h'
      simp [ha, this]
    · have hb : b.1 ≠ 0 := fun hb => by
        rw [hb, Semiring.mul_zero] at h
        rcases Zp.eq_zero_or_eq_zero hP.prime h with h' | h'
        · exact pow_ne_zero _ h'
        · exact ha h'
      have e := congrArg (Zp.val hP.prime) h
      rw [val_pow_mul' _ ha, val_pow_mul' _ hb] at e
      simp only [ha, hb, ↓reduceIte]; omega

/-- The valuation on a representative. -/
theorem val_mk {x : Zp p} (hx : x ≠ 0) (k : Nat) :
    val (mk x k) = (Zp.val hP.prime x : Int) - k := by
  show repVal (x, k) = _; unfold repVal; simp [hx]

/-- **Additivity of the valuation** on ℚₚ: `v(q r) = v(q) + v(r)` for `q, r ≠ 0`. -/
theorem val_mul {q r : Qp p} (hq : q ≠ 0) (hr : r ≠ 0) : val (q * r) = val q + val r := by
  induction q using ind with | h x k => ?_
  induction r using ind with | h y l => ?_
  have hx : x ≠ 0 := fun h => hq (mk_eq_zero.2 h)
  have hy : y ≠ 0 := fun h => hr (mk_eq_zero.2 h)
  have hxy : x * y ≠ 0 := fun h => by
    rcases Zp.eq_zero_or_eq_zero hP.prime h with h | h <;> contradiction
  rw [mk_mul, val_mk hxy, val_mk hx, val_mk hy, Zp.val_mul hP.prime hx hy]; omega

/-- **Ultrametric property of the valuation** on ℚₚ. -/
theorem min_le_val_add {q r : Qp p} (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) :
    min (val q) (val r) ≤ val (q + r) := by
  induction q using ind with | h x k => ?_
  induction r using ind with | h y l => ?_
  have hx : x ≠ 0 := fun h => hq (mk_eq_zero.2 h)
  have hy : y ≠ 0 := fun h => hr (mk_eq_zero.2 h)
  rw [mk_add] at hqr ⊢
  have hs : (p : Zp p) ^ l * x + (p : Zp p) ^ k * y ≠ 0 := fun h => hqr (mk_eq_zero.2 h)
  have h1 : (p : Zp p) ^ l * x ≠ 0 := fun h => by
    rcases Zp.eq_zero_or_eq_zero hP.prime h with h | h
    · exact pow_ne_zero _ h
    · exact hx h
  have h2 : (p : Zp p) ^ k * y ≠ 0 := fun h => by
    rcases Zp.eq_zero_or_eq_zero hP.prime h with h | h
    · exact pow_ne_zero _ h
    · exact hy h
  have := Zp.min_le_val_add hP.prime h1 h2 hs
  rw [val_pow_mul' _ hx, val_pow_mul' _ hy] at this
  rw [val_mk hs, val_mk hx, val_mk hy]; omega

/-! ## The absolute value -/

/-- **The `p`-adic absolute value on ℚₚ.** `|q|ₚ = p^(−v(q))` for `q ≠ 0`, `|0|ₚ = 0`. -/
noncomputable def abs (q : Qp p) : Q :=
  open Classical in if q = 0 then 0 else (p : Q) ^ (-(val q))

/-- `|q|ₚ = p^(−v(q))` for `q ≠ 0`. -/
theorem abs_of_ne {q : Qp p} (hq : q ≠ 0) : abs q = (p : Q) ^ (-(val q)) := by
  simp [abs, hq]

/-- `|q|ₚ = 0` iff `q = 0`. -/
theorem abs_eq_zero {q : Qp p} : abs q = 0 ↔ q = 0 := by
  constructor
  · intro h; apply Classical.byContradiction; intro hq
    rw [abs_of_ne hq] at h
    have := zpow_pos (by have := one_le_prime hP.prime; grind : (0 : Q) < p) (-(val q))
    grind
  · intro h; simp [abs, h]

/-- `|q|ₚ ≥ 0`. -/
theorem abs_nonneg (q : Qp p) : 0 ≤ abs q := by
  by_cases hq : q = 0
  · simp [abs, hq]
  · rw [abs_of_ne hq]
    exact Std.le_of_lt (zpow_pos (by have := one_le_prime hP.prime; grind) _)

/-- **Multiplicativity** of `|·|ₚ` on ℚₚ. -/
theorem abs_mul (q r : Qp p) : abs (q * r) = abs q * abs r := by
  by_cases hq : q = 0
  · rw [hq, show (0 : Qp p) * r = 0 by grind]; simp [abs]; grind
  by_cases hr : r = 0
  · rw [hr, show q * (0 : Qp p) = 0 by grind]; simp [abs]; grind
  have hqr : q * r ≠ 0 := fun h => by
    rcases Field.of_mul_eq_zero h with h | h <;> contradiction
  have hp0 : (p : Q) ≠ 0 := by have := one_le_prime hP.prime; grind
  rw [abs_of_ne hq, abs_of_ne hr, abs_of_ne hqr, val_mul hq hr, ← Field.zpow_add hp0]
  congr 1; omega

/-- **The ultrametric inequality on ℚₚ.** `|q + r|ₚ ≤ |q|ₚ` or `|q + r|ₚ ≤ |r|ₚ`. -/
theorem abs_ultrametric (q r : Qp p) : abs (q + r) ≤ abs q ∨ abs (q + r) ≤ abs r := by
  by_cases hq : q = 0
  · right; rw [hq, show (0 : Qp p) + r = r by grind]; exact Std.le_refl _
  by_cases hr : r = 0
  · left; rw [hr, show q + (0 : Qp p) = q by grind]; exact Std.le_refl _
  by_cases hqr : q + r = 0
  · left; rw [hqr, abs_eq_zero.2 rfl]; exact abs_nonneg q
  have hm := min_le_val_add hq hr hqr
  have h1 := one_le_prime hP.prime
  rw [abs_of_ne hq, abs_of_ne hr, abs_of_ne hqr]
  rcases Int.le_total (val q) (val r) with h | h
  · left; exact zpow_le_zpow h1 (by omega)
  · right; exact zpow_le_zpow h1 (by omega)

/-- `|ofZp x|ₚ ≤ 1`: `p`-adic integers have absolute value at most `1`. -/
theorem abs_ofZp_le_one (x : Zp p) : abs (ofZp x) ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, show ofZp (0 : Zp p) = 0 from rfl, abs_eq_zero.2 rfl]
    exact OrderedRing.zero_le_one
  · have hne : ofZp x ≠ 0 := fun h => hx (mk_eq_zero.1 h)
    rw [abs_of_ne hne]
    unfold ofZp; rw [val_mk hx]
    have := zpow_le_zpow (one_le_prime hP.prime)
      (show -(((Zp.val hP.prime x : Nat) : Int) - ((0 : Nat) : Int)) ≤ 0 by omega)
    rwa [Field.zpow_zero] at this

/-! ## ℚ inside ℚₚ -/

/-- Nonzero integers stay nonzero in `ℚₚ`. -/
theorem intCast_ne_zero {n : Int} (hn : n ≠ 0) : (n : Qp p) ≠ 0 := fun h =>
  hn (Zp.intCast_injective (p := p) hP.prime.1 (mk_eq_zero.1 h))

/-- The image of a fraction `n/d` in `ℚₚ`: `n · d⁻¹`. -/
noncomputable def ofFrac (f : Frac) : Qp p := (f.num : Qp p) * (f.den : Qp p)⁻¹

/-- The canonical map `ℚ → ℚₚ`, `n/d ↦ n · d⁻¹`. -/
noncomputable def ofQ : Q → Qp p :=
  Quotient.lift ofFrac fun f g (h : f.num * g.den = g.num * f.den) => by
    unfold ofFrac
    have hf := intCast_ne_zero (p := p) (show f.den ≠ 0 by have := f.den_pos; omega)
    have hg := intCast_ne_zero (p := p) (show g.den ≠ 0 by have := g.den_pos; omega)
    have e : (f.num : Qp p) * (g.den : Qp p) = (g.num : Qp p) * (f.den : Qp p) := by
      rw [← Ring.intCast_mul, ← Ring.intCast_mul, h]
    have := Field.mul_inv_cancel hf
    have := Field.mul_inv_cancel hg
    calc (f.num : Qp p) * (f.den : Qp p)⁻¹
        = (f.num : Qp p) * (g.den : Qp p) * ((f.den : Qp p)⁻¹ * (g.den : Qp p)⁻¹) := by grind
      _ = (g.num : Qp p) * (f.den : Qp p) * ((f.den : Qp p)⁻¹ * (g.den : Qp p)⁻¹) := by rw [e]
      _ = (g.num : Qp p) * (g.den : Qp p)⁻¹ := by grind

/-- `ofQ` on a representative. -/
theorem ofQ_mk (n d : Int) (hd : 0 < d) :
    ofQ (p := p) (Q.mk n d hd) = (n : Qp p) * (d : Qp p)⁻¹ := rfl

/-- **ℚ ⊂ ℚₚ is a ring map: addition.** -/
theorem ofQ_add (x y : Q) : ofQ (p := p) (x + y) = ofQ x + ofQ y := by
  induction x using Q.ind with | h a b hb => ?_
  induction y using Q.ind with | h c d hd => ?_
  rw [Q.mk_add, ofQ_mk, ofQ_mk, ofQ_mk]
  have h1 := Field.mul_inv_cancel (intCast_ne_zero (p := p) (show b ≠ 0 by omega))
  have h2 := Field.mul_inv_cancel (intCast_ne_zero (p := p) (show d ≠ 0 by omega))
  rw [Ring.intCast_add, Ring.intCast_mul, Ring.intCast_mul, Ring.intCast_mul, Field.inv_mul]
  grind

/-- **ℚ ⊂ ℚₚ is a ring map: multiplication.** -/
theorem ofQ_mul (x y : Q) : ofQ (p := p) (x * y) = ofQ x * ofQ y := by
  induction x using Q.ind with | h a b hb => ?_
  induction y using Q.ind with | h c d hd => ?_
  rw [Q.mk_mul, ofQ_mk, ofQ_mk, ofQ_mk, Ring.intCast_mul, Ring.intCast_mul, Field.inv_mul]
  grind

/-- `ofQ 1 = 1`. -/
theorem ofQ_one : ofQ (p := p) 1 = 1 := by
  show ofQ (Q.mk 1 1 Int.one_pos) = 1
  rw [ofQ_mk, show ((1 : Int) : Qp p) = 1 from rfl, Field.inv_one]; grind

/-- **ℚ embeds in ℚₚ.** The map `ofQ : ℚ → ℚₚ` is injective. -/
theorem ofQ_injective {x y : Q} (h : ofQ (p := p) x = ofQ y) : x = y := by
  have hz : ∀ z : Q, ofQ (p := p) z = 0 → z = 0 := by
    intro z hz
    induction z using Q.ind with | h n d hd => ?_
    rw [ofQ_mk] at hz
    rcases Field.of_mul_eq_zero hz with h | h
    · by_cases hn : n = 0
      · exact (mk_eq_zero_iff hd).2 hn
      · exact absurd h (intCast_ne_zero hn)
    · have := Field.inv_eq_zero_iff.1 h
      exact absurd this (intCast_ne_zero (show d ≠ 0 by omega))
  have := hz (x - y) (by
    rw [show x - y = x + (-1) * y by grind, ofQ_add, ofQ_mul, h]
    have : ofQ (p := p) (-1) = -1 := by
      have e := ofQ_add (p := p) (-1) 1
      rw [show (-1 : Q) + 1 = 0 by grind, ofQ_one] at e
      have : ofQ (p := p) 0 = 0 := by
        show ofQ (Q.mk 0 1 Int.one_pos) = 0
        rw [ofQ_mk]; show (0 : Qp p) * _ = 0; grind
      grind
    rw [this]; grind)
  grind

/-- `v(1) = 0` in ℤₚ. -/
theorem zp_val_one : Zp.val hP.prime (1 : Zp p) = 0 := by
  have := Zp.val_pow_mul hP.prime 0 (u := (1 : Zp p)) (fun h0 => by
    have := Zp.modPow_mk.1 h0
    change (p : Int) ^ 1 ∣ 1 - 0 at this
    rw [Int.pow_one, Int.sub_zero] at this
    have := Int.eq_one_of_dvd_one (by omega) this; have := hP.prime.1; omega)
  rwa [Semiring.pow_zero, Semiring.one_mul] at this

/-- The valuation of a nonzero integer, computed in ℤₚ, is its `p`-adic valuation `vₚ(n)`. -/
theorem zp_val_intCast {n : Int} (hn : n ≠ 0) : Zp.val hP.prime (n : Zp p) = vZ p n := by
  obtain ⟨r, hr, hpr⟩ := NumberTheory.vp_spec hP.prime.1 (m := n.natAbs) (by omega)
  have hA : (n.natAbs : Int) = (p : Int) ^ (vZ p n) * (r : Int) := by
    unfold vZ; rw [← Int.natCast_pow, ← Int.natCast_mul, ← hr]
  obtain ⟨s, hs, hps⟩ : ∃ s : Int, n = (p : Int) ^ vZ p n * s ∧ ¬ (p : Int) ∣ s := by
    rcases Int.natAbs_eq n with h | h
    · exact ⟨r, by rw [← hA]; exact h, fun hd => hpr (Int.ofNat_dvd.1 hd)⟩
    · exact ⟨-(r : Int), by rw [Int.mul_neg, ← hA]; exact h,
        fun hd => hpr (Int.ofNat_dvd.1 (Int.dvd_neg.1 hd))⟩
  have hu : Zp.IsPUnit (s : Zp p) := fun h0 => by
    have := Zp.modPow_mk.1 h0
    change (p : Int) ^ 1 ∣ s - 0 at this
    rw [Int.pow_one, Int.sub_zero] at this; exact hps this
  have e : (n : Zp p) = (p : Zp p) ^ vZ p n * (s : Zp p) := by
    rw [Zp.pow_p_eq]; conv => lhs; rw [hs]
    rfl
  rw [e, Zp.val_pow_mul hP.prime _ hu]

/-- The valuation of `q⁻¹` is `−v(q)`. -/
theorem val_inv {q : Qp p} (hq : q ≠ 0) : val q⁻¹ = -val q := by
  have h1 := Field.mul_inv_cancel hq
  have hq' : q⁻¹ ≠ 0 := fun h => zero_ne_one (by rw [← h1, h]; grind)
  have := val_mul hq hq'
  rw [h1, show (1 : Qp p) = mk 1 0 from rfl, val_mk (Zp.one_ne_zero hP.prime.1), zp_val_one]
    at this
  omega

/-- **The absolute value on ℚₚ extends the one on ℚ.** `|x|ₚ` computed in ℚₚ equals
`|x|ₚ` computed in ℚ (`padicAbs`). -/
theorem abs_ofQ (x : Q) : abs (ofQ (p := p) x) = padicAbs p x := by
  induction x using Q.ind with | h n d hd => ?_
  by_cases hn : n = 0
  · subst hn
    have h0 : Q.mk 0 d hd = 0 := (mk_eq_zero_iff hd).2 rfl
    rw [h0, padicAbs_zero, abs_eq_zero]
    have : ofQ (p := p) (Q.mk 0 d hd) = 0 := by rw [ofQ_mk]; show (0 : Qp p) * _ = 0; grind
    rw [← h0, this]
  · have hx : Q.mk n d hd ≠ 0 := fun h => hn ((mk_eq_zero_iff hd).1 h)
    have hnq := intCast_ne_zero (p := p) hn
    have hdq := intCast_ne_zero (p := p) (show d ≠ 0 by omega)
    have hdi : (d : Qp p)⁻¹ ≠ 0 := fun h => by
      have := Field.mul_inv_cancel hdq; rw [h] at this; exact zero_ne_one (p := p) (by grind)
    have hne : ofQ (p := p) (Q.mk n d hd) ≠ 0 := by
      rw [ofQ_mk]; intro h
      rcases Field.of_mul_eq_zero h with h | h <;> contradiction
    rw [abs_of_ne hne, padicAbs_of_ne hx, vQ_mk hP.prime hd hn, ofQ_mk, val_mul hnq hdi,
      val_inv hdq]
    show (p : Q) ^ (-(val (mk (n : Zp p) 0) + -val (mk (d : Zp p) 0))) = _
    have hnz : (n : Zp p) ≠ 0 := fun h => hnq (mk_eq_zero.2 h)
    have hdz : (d : Zp p) ≠ 0 := fun h => hdq (mk_eq_zero.2 h)
    rw [val_mk hnz, val_mk hdz, zp_val_intCast hn, zp_val_intCast (show d ≠ 0 by omega)]
    congr 1

end Qp

end Foundations.Langlands.Padic
