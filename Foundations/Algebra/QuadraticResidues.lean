import Foundations.Algebra.Solvable

/-!
# Quadratic residues and Euler's criterion

Which numbers are perfect squares modulo a prime `p`? Fermat knew that `-1` is a square modulo
`p` exactly when `p ≡ 1 (mod 4)`; Euler, in the 1740s and 1750s, found the general test that
bears his name, and Legendre in 1798 introduced the notation `(a/p)` — the **Legendre symbol**:
`+1` if `a` is a non-zero square ("quadratic residue") mod `p`, `-1` if it is not, `0` if `p`
divides `a`.

**Euler's criterion.** For an odd prime `p` and `a` not divisible by `p`,
`a^((p-1)/2) ≡ (a/p) (mod p)`.

One direction is Fermat's little theorem: if `a ≡ x²` then `a^((p-1)/2) ≡ x^(p-1) ≡ 1`. For the
other we use the structure of `ℤ/pℤ` as a *field*: the polynomial `X^((p-1)/2) - 1` has at most
`(p-1)/2` roots, and the `(p-1)/2` distinct squares `1², 2², …, ((p-1)/2)²` already are roots,
so a non-square is not. Since `(a^((p-1)/2))² = a^(p-1) ≡ 1`, and `x² = 1` forces `x = ±1` in a
field, a non-square must give `-1`.

Two corollaries follow at once: the Legendre symbol is **multiplicative**,
`(ab/p) = (a/p)(b/p)`, and the **first supplement** `(-1/p) = (-1)^((p-1)/2)` holds — Fermat's
observation about `-1`.

Residues are natural numbers here; `-1` is represented by `p - 1`.
-/

namespace Foundations.Algebra

open Ring

/-- Half of `p - 1`. -/
def half (p : Nat) : Nat := (p - 1) / 2

/-- `a` is a **quadratic residue** modulo `p`: `a ≡ x² (mod p)` for some `x`. -/
def IsQR (a p : Nat) : Prop := ∃ x : Nat, x * x % p = a % p

/-- The **Legendre symbol** `(a/p)`: `0` if `p ∣ a`, `1` if `a` is a quadratic residue, `-1`
otherwise. -/
noncomputable def legendre (a p : Nat) : Int := by
  classical exact if p ∣ a then 0 else if IsQR a p then 1 else -1

section Euler

variable {p : Nat}

/-- `2 · half p = p - 1` and `half p ≥ 1` for an odd prime. -/
theorem half_spec (hp : IsPrime p) (hodd : p % 2 = 1) : 2 * half p = p - 1 ∧ 1 ≤ half p ∧ 2 * half p + 1 = p := by
  have := hp.1; unfold half; omega

/-- **Fermat, for squares.** If `p ∤ x` then `(x²)^((p-1)/2) ≡ 1`. -/
theorem sq_pow_half (hp : IsPrime p) (hodd : p % 2 = 1) {x : Nat} (hx : ¬ p ∣ x) : (x * x) ^ half p % p = 1 := by
  have ⟨h2, _, _⟩ := half_spec hp hodd
  rw [show x * x = x ^ 2 by rw [Nat.pow_two], ← Nat.pow_mul, h2]
  exact fermat p x hp hx

/-- **The only square roots of `1` are `±1`.** If `y < p` and `y² ≡ 1` then `y = 1` or
`y = p - 1`. -/
theorem sq_eq_one (hp : IsPrime p) {y : Nat} (hy : y < p) (h : y * y % p = 1) : y = 1 ∨ y = p - 1 := by
  have h2 := hp.1
  have hy0 : y ≠ 0 := by rintro rfl; simp at h
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
  have hmod : (z * (z + 2)) % p = 0 := by
    have e : (z + 1) * (z + 1) = z * (z + 2) + 1 := by grind
    have h' : (z * (z + 2) + 1) % p = 1 := by rw [← e]; exact h
    have hlt := Nat.mod_lt (z * (z + 2)) (by omega : 0 < p)
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < p by omega)] at h'
    rcases Nat.lt_or_ge (z * (z + 2) % p + 1) p with hl | hl
    · rw [Nat.mod_eq_of_lt hl] at h'; omega
    · have : z * (z + 2) % p + 1 = p := by omega
      rw [this, Nat.mod_self] at h'; omega
  rcases hp.dvd_mul (Nat.dvd_of_mod_eq_zero hmod) with hd | hd
  · left; have := Nat.eq_zero_of_dvd_of_lt hd (by omega); omega
  · right
    rcases Nat.eq_zero_or_pos (z + 2) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd; omega

/-- **Squares of `1, …, (p-1)/2` are distinct modulo `p`.** -/
theorem sq_inj (hp : IsPrime p) (hodd : p % 2 = 1) {u v : Nat} (hu0 : 0 < u) (hv0 : 0 < v) (hu : u ≤ half p)
    (hv : v ≤ half p) (h : u * u % p = v * v % p) : u = v := by
  have ⟨_, _, h3⟩ := half_spec hp hodd
  have key : ∀ u v, 0 < u → 0 < v → u ≤ half p → v ≤ half p → u < v → u * u % p = v * v % p → False := by
    intro u v hu0 hv0 hu hv huv h
    have hm := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [Nat.mul_self_sub_mul_self_eq] at hm
    rcases hp.dvd_mul (Nat.dvd_of_mod_eq_zero hm) with hd | hd
    · have := Nat.le_of_dvd (by omega) hd; omega
    · have := Nat.le_of_dvd (by omega) hd; omega
  rcases Nat.lt_trichotomy u v with hl | he | hg
  · exact (key u v hu0 hv0 hu hv hl h).elim
  · exact he
  · exact (key v u hv0 hu0 hv hu hg h.symm).elim

/-! ## Counting roots in the field `ℤ/pℤ` -/

/-- Values of powers in `Fin p`: evaluating `X^j` at `x` gives `x^j mod p`. -/
theorem eval_Xpow_val [NeZero p] (x : Fin p) (j : Nat) :
    (Polynomial.eval x (Polynomial.Xpow j)).val = x.val ^ j % p := by
  induction j with
  | zero =>
    show (Polynomial.eval x 1).val = 1 % p
    rw [show Polynomial.eval x 1 = 1 from (Polynomial.evalHom x).map_one]
    exact Fin.val_ofNat p 1
  | succ j ih =>
    show (Polynomial.eval x (Polynomial.X * Polynomial.Xpow j)).val = _
    rw [Polynomial.eval_mul, Polynomial.eval_X, Fin.val_mul, ih, Nat.mul_mod_mod, Nat.pow_succ,
      Nat.mul_comm]

/-- **The key step of Euler's criterion.** A non-residue `a` does not satisfy
`a^((p-1)/2) ≡ 1`: otherwise `X^((p-1)/2) - 1` would have `(p-1)/2 + 1` roots in the field
`ℤ/pℤ`, namely `a` and the squares `1², …, ((p-1)/2)²`. -/
theorem pow_half_ne_one_of_not_qr (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (_ha : ¬ p ∣ a) (hq : ¬ IsQR a p) :
    a ^ half p % p ≠ 1 := by
  intro hpow
  have ⟨_, h1, h3⟩ := half_spec hp hodd
  haveI : NeZero p := ⟨by omega⟩
  have hF : IsField (Fin p) := (fin_isField_iff_prime p).2 hp
  have hD := hF.isDomain
  let h := half p
  let f : Polynomial (Fin p) := Polynomial.Xpow h + -Polynomial.C 1
  have hXpow : ∀ n, Polynomial.coeff (Polynomial.Xpow h : Polynomial (Fin p)) n =
      if h ≤ n then (if n - h = 0 then 1 else 0) else 0 := by
    intro n
    rw [← Ring.mul_one (Polynomial.Xpow h), Polynomial.coeff_Xpow_mul, ← Polynomial.C_one,
      Polynomial.coeff_C]
  have hcoef : ∀ n, Polynomial.coeff f n =
      (if h ≤ n then (if n - h = 0 then 1 else 0) else 0) + -(if n = 0 then 1 else 0) := by
    intro n
    show Polynomial.coeff (Polynomial.Xpow h + -Polynomial.C 1) n = _
    rw [Polynomial.coeff_add, Polynomial.coeff_neg, hXpow, Polynomial.coeff_C]
  have hdeg : Polynomial.DegLT f (h + 1) := by
    intro n hn
    rw [hcoef, ite_true_of (by omega : h ≤ n), ite_false_of (by omega : ¬ n - h = 0),
      ite_false_of (by omega : ¬ n = 0), neg_zero, Ring.add_zero]
  have hf0 : f ≠ 0 := by
    intro hf
    have := hcoef h
    rw [hf, Polynomial.coeff_zero, ite_true_of (Nat.le_refl h), ite_true_of (Nat.sub_self h),
      ite_false_of (by omega : ¬ h = 0), neg_zero, Ring.add_zero] at this
    exact hF.1 this
  have hroot : ∀ x : Fin p, x.val ^ h % p = 1 → Polynomial.eval x f = 0 := by
    intro x hx
    show Polynomial.eval x (Polynomial.Xpow h + -Polynomial.C 1) = 0
    rw [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_C]
    have : Polynomial.eval x (Polynomial.Xpow h) = 1 := by
      apply Fin.ext; rw [eval_Xpow_val, hx]
      show 1 = (Fin.ofNat p 1).val
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [this, add_neg_cancel]
  let sq : Nat → Fin p := fun k => Fin.ofNat p ((k + 1) * (k + 1))
  let L := (List.range h).map sq
  let A : Fin p := Fin.ofNat p a
  have hLnd : L.Nodup := by
    have hpw : (List.range h).Pairwise (fun i j => sq i ≠ sq j) := by
      refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := h))
      intro i j hi hj hij heq
      rw [List.mem_range] at hi hj
      apply hij
      have := congrArg Fin.val heq
      simp only [sq, Fin.val_ofNat] at this
      have := sq_inj hp hodd (by omega) (by omega) (by omega) (by omega) this
      omega
    exact List.Pairwise.map _ (fun _ _ h => h) hpw
  have hAL : A ∉ L := by
    intro hA
    obtain ⟨k, _, hk⟩ := List.mem_map.1 hA
    apply hq
    refine ⟨k + 1, ?_⟩
    have := congrArg Fin.val hk
    simpa only [sq, A, Fin.val_ofNat] using this
  have hnd : (A :: L).Nodup := List.nodup_cons.2 ⟨hAL, hLnd⟩
  have hroots : ∀ x, x ∈ A :: L → Polynomial.eval x f = 0 := by
    intro x hx
    apply hroot
    rcases List.mem_cons.1 hx with rfl | hx
    · show (a % p) ^ h % p = 1; rw [← Nat.pow_mod]; exact hpow
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      rw [List.mem_range] at hk
      show ((k + 1) * (k + 1) % p) ^ h % p = 1
      rw [← Nat.pow_mod]
      exact sq_pow_half hp hodd (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)
  have := Polynomial.card_roots_le hD (A :: L) h f hf0 hdeg hnd hroots
  simp [L] at this
  omega

/-- **Euler's criterion.** For an odd prime `p` and `p ∤ a`, `a^((p-1)/2) ≡ 1 (mod p)` if `a` is
a quadratic residue and `a^((p-1)/2) ≡ -1 (mod p)` otherwise. -/
theorem euler_criterion (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (ha : ¬ p ∣ a) :
    a ^ half p % p = (by classical exact if IsQR a p then 1 else p - 1) := by
  classical
  have ⟨h2, _, _⟩ := half_spec hp hodd
  by_cases hq : IsQR a p
  · simp only [hq, ↓reduceIte]
    obtain ⟨x, hx⟩ := hq
    have hxp : ¬ p ∣ x := by
      intro hd; apply ha
      have : a % p = 0 := by rw [← hx, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd]; simp
      exact Nat.dvd_of_mod_eq_zero this
    rw [Nat.pow_mod, ← hx, ← Nat.pow_mod]
    exact sq_pow_half hp hodd hxp
  · simp only [hq, ↓reduceIte]
    have hsq : (a ^ half p % p) * (a ^ half p % p) % p = 1 := by
      rw [← Nat.mul_mod, ← Nat.pow_two, ← Nat.pow_mul, Nat.mul_comm, h2]
      exact fermat p a hp ha
    rcases sq_eq_one hp (Nat.mod_lt _ (by have := hp.1; omega)) hsq with h | h
    · exact absurd h (pow_half_ne_one_of_not_qr hp hodd ha hq)
    · exact h

/-- **Euler's criterion, Legendre-symbol form.** `(a/p) = 1` exactly when `a^((p-1)/2) ≡ 1`, and
`(a/p) = -1` exactly when `a^((p-1)/2) ≡ -1`. -/
theorem legendre_eq_of_pow (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (ha : ¬ p ∣ a) :
    (a ^ half p % p = 1 → legendre a p = 1) ∧ (a ^ half p % p = p - 1 → legendre a p = -1) := by
  classical
  have h3 := hp.1
  have he := euler_criterion hp hodd ha
  unfold legendre
  simp only [ha, ↓reduceIte]
  by_cases hq : IsQR a p
  · simp only [hq, ↓reduceIte] at he ⊢
    exact ⟨fun _ => trivial, fun h => by omega⟩
  · simp only [hq, ↓reduceIte] at he ⊢
    exact ⟨fun h => by omega, fun _ => trivial⟩

/-- The Legendre symbol of a number prime to `p` is `±1`. -/
theorem legendre_cases (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (ha : ¬ p ∣ a) :
    (legendre a p = 1 ∧ a ^ half p % p = 1) ∨ (legendre a p = -1 ∧ a ^ half p % p = p - 1) := by
  classical
  have he := euler_criterion hp hodd ha
  have hl := legendre_eq_of_pow hp hodd ha
  by_cases hq : IsQR a p
  · simp only [hq, ↓reduceIte] at he; exact Or.inl ⟨hl.1 he, he⟩
  · simp only [hq, ↓reduceIte] at he; exact Or.inr ⟨hl.2 he, he⟩

/-- `(p - 1)² ≡ 1 (mod p)`. -/
theorem pred_mul_pred_mod (h2 : 2 ≤ p) : (p - 1) * (p - 1) % p = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have : (m + 2 - 1) * (m + 2 - 1) = (m + 2) * m + 1 := by
    rw [show m + 2 - 1 = m + 1 by omega]; grind
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- **Multiplicativity of the Legendre symbol**: `(ab/p) = (a/p)(b/p)`. -/
theorem legendre_mul (hp : IsPrime p) (hodd : p % 2 = 1) (a b : Nat) : legendre (a * b) p = legendre a p * legendre b p := by
  classical
  have h3 := hp.1
  by_cases ha : p ∣ a
  · have : p ∣ a * b := Nat.dvd_mul_right_of_dvd ha b
    unfold legendre; simp [ha, this]
  by_cases hb : p ∣ b
  · have : p ∣ a * b := Nat.dvd_mul_left_of_dvd hb a
    unfold legendre; simp [hb, this]
  have hab : ¬ p ∣ a * b := fun h => (hp.dvd_mul h).elim ha hb
  have hpow : (a * b) ^ half p % p = (a ^ half p % p) * (b ^ half p % p) % p := by
    rw [Nat.mul_pow, Nat.mul_mod]
  have hl := legendre_eq_of_pow hp hodd hab
  rcases legendre_cases hp hodd ha with ⟨la, pa⟩ | ⟨la, pa⟩ <;>
    rcases legendre_cases hp hodd hb with ⟨lb, pb⟩ | ⟨lb, pb⟩ <;> rw [la, lb]
  · exact hl.1 (by rw [hpow, pa, pb, Nat.mod_eq_of_lt (by omega)])
  · exact hl.2 (by rw [hpow, pa, pb, Nat.one_mul, Nat.mod_eq_of_lt (by omega)])
  · exact hl.2 (by rw [hpow, pa, pb, Nat.mul_one, Nat.mod_eq_of_lt (by omega)])
  · exact hl.1 (by rw [hpow, pa, pb, pred_mul_pred_mod (by omega)])

/-- Powers of `-1 ≡ p - 1` modulo `p`. -/
theorem pred_pow_mod (h2 : 2 ≤ p) (n : Nat) :
    (p - 1) ^ n % p = if n % 2 = 0 then 1 else p - 1 := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt (by omega : 1 < p)]
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    by_cases hn : n % 2 = 0
    · rw [ite_true_of hn, ite_false_of (by omega), Nat.mod_eq_of_lt (by omega : p - 1 < p),
        Nat.one_mul, Nat.mod_eq_of_lt (by omega)]
    · rw [ite_false_of hn, ite_true_of (by omega), Nat.mod_eq_of_lt (by omega : p - 1 < p),
        pred_mul_pred_mod h2]

/-- **The first supplement**: `(-1/p) = (-1)^((p-1)/2)`, with `-1` represented by `p - 1`. -/
theorem legendre_neg_one (hp : IsPrime p) (hodd : p % 2 = 1) : legendre (p - 1) p = (-1) ^ half p := by
  have h3 := hp.1
  have hnd : ¬ p ∣ p - 1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hl := legendre_eq_of_pow hp hodd hnd
  rw [pred_pow_mod h3] at hl
  have hpow : ∀ n : Nat, (-1 : Int) ^ n = if n % 2 = 0 then 1 else -1 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      rw [Int.pow_succ, ih]
      by_cases hn : n % 2 = 0
      · rw [ite_true_of hn, ite_false_of (by omega)]; rfl
      · rw [ite_false_of hn, ite_true_of (by omega)]; rfl
  rw [hpow]
  by_cases hh : half p % 2 = 0
  · rw [ite_true_of hh]; exact hl.1 (by rw [ite_true_of hh])
  · rw [ite_false_of hh]; exact hl.2 (by rw [ite_false_of hh])

/-- **Fermat's criterion for `-1`.** `-1` is a quadratic residue modulo an odd prime `p` exactly
when `p ≡ 1 (mod 4)`. -/
theorem neg_one_qr_iff (hp : IsPrime p) (hodd : p % 2 = 1) : IsQR (p - 1) p ↔ p % 4 = 1 := by
  classical
  have h3 := hp.1
  have hnd : ¬ p ∣ p - 1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have he := euler_criterion hp hodd hnd
  rw [pred_pow_mod h3] at he
  have hh : half p % 2 = 0 ↔ p % 4 = 1 := by unfold half; omega
  by_cases hq : IsQR (p - 1) p
  · simp only [hq, ↓reduceIte, true_iff] at he ⊢
    apply hh.1
    apply Classical.byContradiction; intro hne; rw [ite_false_of hne] at he; omega
  · simp only [hq, ↓reduceIte, false_iff] at he ⊢
    intro h4; rw [ite_true_of (hh.2 h4)] at he; omega

end Euler

end Foundations.Algebra
