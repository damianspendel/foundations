import Foundations.Algebra.Embedding

/-!
# The five complex roots of `x⁵ - 6x + 3`

This file locates the roots of `f = x⁵ - 6x + 3` in `ℂ`: there are exactly five, three real and
two complex conjugate, and they are distinct.

* **No repeated roots** (`no_double_root`). In any domain of characteristic zero, `f` is not
  divisible by `(x - r)²`. Division by `x - r` leaves the explicit quotient
  `Q = x⁴ + r x³ + r² x² + r³ x + (r⁴ - 6)` (`quinticPoly_factor`), so `(x - r)² ∣ f` forces
  `Q(r) = 5r⁴ - 6 = 0`. Together with `r⁵ - 6r + 3 = 0` this gives `24 r = 15` and then
  `6 · 24⁴ = 5 · 15⁴`, which is false.
* **Two non-real roots.** The three real roots `r₁ < r₂ < r₃` split off three linear factors:
  `f = (x - r₁)(x - r₂)(x - r₃) q` with `q` quadratic. By the fundamental theorem of algebra `q`
  has a root `z`. It is not real: a real root of `f` is one of the `rᵢ`, and `z = rᵢ` would make
  `rᵢ` a double root. Its conjugate `z̄ ≠ z` is a root too.
* **The enumeration** (`exists_quintic_roots`): an injective `β : Fin 5 → ℂ` listing the roots,
  with `β 0, β 1, β 2` real, `β 3` non-real and `β 4 = conj (β 3)`. Every root is some `β i`
  (`quintic_root_enum`), since a polynomial of degree `5` has at most five roots.
-/

namespace Foundations.Algebra

open Polynomial

/-- The complex numbers of Part II. -/
local notation "ℂ" => Foundations.Numbers.C

universe u

/-! ## Division by `x - r` -/

section Generic

variable {A : Type u} [CommRing A]

/-- Coefficients of a list vanish beyond its length. -/
theorem PolyList.coeff_of_length_le : ∀ (l : List A) (n : Nat), l.length ≤ n → PolyList.coeff l n = 0
  | [], n, _ => PolyList.coeff_nil n
  | a :: l, 0, h => absurd h (by simp)
  | a :: l, n + 1, h => by
    rw [PolyList.coeff_cons_succ]; exact PolyList.coeff_of_length_le l n (by simp at h; omega)

/-- The linear polynomial `x - r`. -/
def linC (r : A) : Polynomial A := mk [-r, 1]

/-- The quotient `x⁴ + r x³ + r² x² + r³ x + (r⁴ - 6)` of `x⁵ - 6x + 3` by `x - r`. -/
def quinticQuot (r : A) : Polynomial A := mk [r * r * r * r + Int.cast (-6), r * r * r, r * r, r, 1]

/-- **Division of `x⁵ - 6x + 3` by `x - r`**: `f = (x - r) Q + f(r)`. -/
theorem quinticPoly_factor (r : A) :
    quinticPoly A = linC r * quinticQuot r + Polynomial.C (eval r (quinticPoly A)) := by
  apply ext; intro n
  rw [coeff_add, coeff_mul_sum, eval_quinticPoly, coeff_quinticPoly, coeff_C]
  unfold linC quinticQuot
  match n with
  | 0 => simp only [rsum, coeff_mk, Nat.sub_self, PolyList.coeff, quinticCoeffs]; grind
  | 1 => simp only [rsum, coeff_mk, Nat.sub_self, PolyList.coeff, quinticCoeffs]; grind
  | 2 => simp only [rsum, coeff_mk, Nat.sub_self, PolyList.coeff, quinticCoeffs]; grind
  | 3 => simp only [rsum, coeff_mk, Nat.sub_self, PolyList.coeff, quinticCoeffs]; grind
  | 4 => simp only [rsum, coeff_mk, Nat.sub_self, PolyList.coeff, quinticCoeffs]; grind
  | 5 => simp only [rsum, coeff_mk, Nat.sub_self, PolyList.coeff, quinticCoeffs]; grind
  | n + 6 =>
    rw [rsum_zero, ite_false_of (by omega)]
    · show (Int.cast (0 : Int) : A) = 0 + 0; rw [icast_zero', Ring.add_zero]
    · intro k hk
      rw [coeff_mk, coeff_mk]
      by_cases h2 : 2 ≤ k
      · rw [PolyList.coeff_of_length_le _ k (by simp; omega), Ring.zero_mul]
      · rw [PolyList.coeff_of_length_le _ (n + 6 - k) (by simp; omega), Ring.mul_zero]

/-- Mapping `x⁵ - 6x + 3` along a ring homomorphism gives `x⁵ - 6x + 3`. -/
theorem mapPoly_quinticPoly {B : Type u} [CommRing B] (φ : RingHom A B) :
    mapPoly φ (quinticPoly A) = quinticPoly B :=
  ext fun n => by rw [coeff_mapPoly, coeff_quinticPoly, coeff_quinticPoly, RingHom.map_intCast]

/-- `(x - r)(x₀) = x₀ - r`. -/
theorem eval_linC (r x : A) : eval x (linC r) = x + -r := by
  show evalList x [-r, 1] = _
  simp only [evalList]; grind

/-- `x - r` is the polynomial `linear r` of the factor theorem. -/
theorem linear_eq_linC (r : A) : linear r = linC r := by
  apply ext; intro n
  unfold linear linC
  rw [coeff_add, coeff_neg, coeff_X, coeff_C, coeff_mk]
  match n with
  | 0 => show 0 + -r = -r; grind
  | 1 => show 1 + -0 = 1; grind
  | n + 2 => rw [PolyList.coeff_of_length_le _ (n + 2) (by simp)]; show (0 : A) + -0 = 0; grind

/-- `x - r` has degree `1`. -/
theorem natDegree_linC (h01 : (0 : A) ≠ 1) (r : A) : natDegree (linC r) = 1 := by
  apply natDegree_eq_of
  · intro n hn; exact PolyList.coeff_of_length_le _ n (by simp; omega)
  · show (1 : A) ≠ 0; exact fun h => h01 h.symm

/-- `x - r ≠ 0`. -/
theorem linC_ne_zero (h01 : (0 : A) ≠ 1) (r : A) : linC r ≠ 0 := by
  intro h; have := congrArg (fun p => coeff p 1) h
  exact h01 (this.symm.trans rfl)

/-- **No repeated roots.** In a domain of characteristic zero, `(x - r)²` never divides
`x⁵ - 6x + 3`. -/
theorem no_double_root (hD : IsDomain A) (hc : CharZero A) (r : A) (g : Polynomial A)
    (h : quinticPoly A = linC r * (linC r * g)) : False := by
  have hr : eval r (quinticPoly A) = 0 := by
    rw [h, eval_mul, eval_linC]; grind
  have hfac := quinticPoly_factor r
  rw [hr, C_zero, Ring.add_zero, h] at hfac
  have hQ : quinticQuot r = linC r * g := by
    have e : linC r * (quinticQuot r + -(linC r * g)) = 0 := by grind
    rcases (isDomain hD).2 _ _ e with h1 | h1
    · exact absurd h1 (linC_ne_zero hD.1 r)
    · grind
  have hQr : eval r (quinticQuot r) = 0 := by rw [hQ, eval_mul, eval_linC]; grind
  have h1 : r * r * r * r + Int.cast (-6) + r * (r * r * r + r * (r * r + r * (r + r * (1 + r * 0))))
      = 0 := hQr
  have h2 := hr
  rw [eval_quinticPoly] at h2
  have h3 : (Int.cast (24 : Int) : A) * r = Int.cast 15 := by grind
  have h4 : (Int.cast (1737531 : Int) : A) = 0 := by grind
  exact absurd (hc _ h4) (by decide)

end Generic

/-! ## The roots in `ℂ` -/

/-- Real and imaginary parts determine a complex number. -/
theorem C.eq_ofReal {z : ℂ} (h : z.im = 0) : z = ⟨z.re, 0⟩ := Foundations.Numbers.C.ext rfl h

/-- `ℂ` is an integral domain. -/
theorem C.isDomain : IsDomain ℂ := C.isField.isDomain

/-- If `f = (x - a) q` and `b ≠ a` is a root of `f`, then `b` is a root of `q`. -/
theorem root_of_factor {f q : Polynomial ℂ} {a b : ℂ} (hf : f = linC a * q) (hb : eval b f = 0)
    (hab : b ≠ a) : eval b q = 0 := by
  rw [hf, eval_mul, eval_linC] at hb
  rcases C.isDomain.2 _ _ hb with h | h
  · exact absurd (by grind) hab
  · exact h

/-- **The roots of `x⁵ - 6x + 3` in `ℂ`.** There is an injective `β : Fin 5 → ℂ` of roots with
`β 0, β 1, β 2` real, `β 3` not real and `β 4` the conjugate of `β 3`. -/
theorem exists_quintic_roots : ∃ β : Fin 5 → ℂ, (∀ i j, β i = β j → i = j) ∧
    (∀ i, eval (β i) (quinticPoly ℂ) = 0) ∧ (β 0).im = 0 ∧ (β 1).im = 0 ∧ (β 2).im = 0 ∧
    (β 3).im ≠ 0 ∧ β 4 = Foundations.Numbers.C.conj (β 3) := by
  obtain ⟨r₁, r₂, r₃, h12, h23, e1, e2, e3, hall⟩ := quintic_three_real_roots
  let ρ₁ : ℂ := ⟨r₁, 0⟩
  let ρ₂ : ℂ := ⟨r₂, 0⟩
  let ρ₃ : ℂ := ⟨r₃, 0⟩
  have f1 : eval ρ₁ (quinticPoly ℂ) = 0 := by rw [quinticPoly_eval_ofReal, e1]; rfl
  have f2 : eval ρ₂ (quinticPoly ℂ) = 0 := by rw [quinticPoly_eval_ofReal, e2]; rfl
  have f3 : eval ρ₃ (quinticPoly ℂ) = 0 := by rw [quinticPoly_eval_ofReal, e3]; rfl
  have ne : ∀ {x y : Foundations.Numbers.R}, x < y → (⟨y, 0⟩ : ℂ) ≠ ⟨x, 0⟩ := by
    intro x y hxy h; have := congrArg Foundations.Numbers.C.re h
    change y = x at this; grind
  -- split off the three real roots
  obtain ⟨q₁, hq₁⟩ := (factor_theorem _ ρ₁).1 f1
  rw [linear_eq_linC] at hq₁
  obtain ⟨q₂, hq₂⟩ := (factor_theorem _ ρ₂).1 (root_of_factor hq₁ f2 (ne h12))
  rw [linear_eq_linC] at hq₂
  have f3' : eval ρ₃ q₂ = 0 :=
    root_of_factor hq₂ (root_of_factor hq₁ f3 (ne (Std.lt_trans h12 h23))) (ne h23)
  obtain ⟨q₃, hq₃⟩ := (factor_theorem _ ρ₃).1 f3'
  rw [linear_eq_linC] at hq₃
  have hf : quinticPoly ℂ = linC ρ₁ * (linC ρ₂ * (linC ρ₃ * q₃)) := by rw [hq₁, hq₂, hq₃]
  have h01 := C.isField.1
  have hf0 : quinticPoly ℂ ≠ 0 := fun h => by
    have := natDegree_quinticPoly (R := ℂ) h01; rw [h] at this
    unfold natDegree at this; rw [len_eq_zero.2 rfl] at this; exact absurd this (by decide)
  have hq0 : q₃ ≠ 0 := fun h => hf0 (by rw [hf, h]; grind)
  have hd := natDegree_quinticPoly (R := ℂ) h01
  have hl := fun r => linC_ne_zero h01 r
  rw [hf, natDegree_mul C.isDomain (hl _) (mul_ne_zero_of_domain C.isDomain (hl _)
      (mul_ne_zero_of_domain C.isDomain (hl _) hq0).1).1,
    natDegree_mul C.isDomain (hl _) (mul_ne_zero_of_domain C.isDomain (hl _) hq0).1,
    natDegree_mul C.isDomain (hl _) hq0, natDegree_linC h01, natDegree_linC h01,
    natDegree_linC h01] at hd
  -- the quadratic factor has a complex root `z`
  obtain ⟨z, hz⟩ := C.fta' q₃ (n := natDegree q₃) (by omega) (leadingCoeff_ne_zero hq0)
  have fz : eval z (quinticPoly ℂ) = 0 := by rw [hf, eval_mul, eval_mul, eval_mul, hz]; grind
  -- `z` is not real
  have hzim : z.im ≠ 0 := by
    intro him
    have hzr := C.eq_ofReal him
    have hR : quinticR z.re = 0 := by
      have := fz; rw [hzr, quinticPoly_eval_ofReal] at this
      exact congrArg Foundations.Numbers.C.re this
    obtain ⟨q₄, hq₄⟩ := (factor_theorem _ z).1 hz
    rw [linear_eq_linC] at hq₄
    rcases hall _ hR with h | h | h
    · apply no_double_root C.isDomain C.charZero ρ₁ (linC ρ₂ * linC ρ₃ * q₄)
      rw [hf, hq₄, hzr, h]; grind
    · apply no_double_root C.isDomain C.charZero ρ₂ (linC ρ₁ * linC ρ₃ * q₄)
      rw [hf, hq₄, hzr, h]; grind
    · apply no_double_root C.isDomain C.charZero ρ₃ (linC ρ₁ * linC ρ₂ * q₄)
      rw [hf, hq₄, hzr, h]; grind
  let cz := Foundations.Numbers.C.conj z
  have fcz : eval cz (quinticPoly ℂ) = 0 := by
    have := RingHom.map_eval conjHom z (quinticPoly ℂ)
    rw [fz, conjHom.map_zero, mapPoly_quinticPoly] at this
    exact this.symm
  -- distinctness
  have nr : ∀ {x : Foundations.Numbers.R} {w : ℂ}, w.im ≠ 0 → w ≠ ⟨x, 0⟩ :=
    fun hw h => hw (by rw [h])
  have hczim : cz.im ≠ 0 := fun h => hzim (by change -z.im = 0 at h; grind)
  have hzcz : z ≠ cz := fun h => hzim (by
    have := congrArg Foundations.Numbers.C.im h; change z.im = -z.im at this; grind)
  let β : Fin 5 → ℂ := fun i => match i with
    | ⟨0, _⟩ => ρ₁ | ⟨1, _⟩ => ρ₂ | ⟨2, _⟩ => ρ₃ | ⟨3, _⟩ => z | _ => cz
  refine ⟨β, ?_, ?_, rfl, rfl, rfl, hzim, rfl⟩
  · intro i j h
    have d12 := ne h12; have d23 := ne h23; have d13 := ne (Std.lt_trans h12 h23)
    have z1 := nr (x := r₁) hzim; have z2 := nr (x := r₂) hzim; have z3 := nr (x := r₃) hzim
    have c1 := nr (x := r₁) hczim; have c2 := nr (x := r₂) hczim; have c3 := nr (x := r₃) hczim
    obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
    apply Fin.ext
    revert h
    match i, j, hi, hj with
    | 0, 0, _, _ => intro _; rfl
    | 1, 1, _, _ => intro _; rfl
    | 2, 2, _, _ => intro _; rfl
    | 3, 3, _, _ => intro _; rfl
    | 4, 4, _, _ => intro _; rfl
    | 0, 1, _, _ => intro h; exact absurd h.symm d12
    | 0, 2, _, _ => intro h; exact absurd h.symm d13
    | 0, 3, _, _ => intro h; exact absurd h.symm z1
    | 0, 4, _, _ => intro h; exact absurd h.symm c1
    | 1, 0, _, _ => intro h; exact absurd h d12
    | 1, 2, _, _ => intro h; exact absurd h.symm d23
    | 1, 3, _, _ => intro h; exact absurd h.symm z2
    | 1, 4, _, _ => intro h; exact absurd h.symm c2
    | 2, 0, _, _ => intro h; exact absurd h d13
    | 2, 1, _, _ => intro h; exact absurd h d23
    | 2, 3, _, _ => intro h; exact absurd h.symm z3
    | 2, 4, _, _ => intro h; exact absurd h.symm c3
    | 3, 0, _, _ => intro h; exact absurd h z1
    | 3, 1, _, _ => intro h; exact absurd h z2
    | 3, 2, _, _ => intro h; exact absurd h z3
    | 3, 4, _, _ => intro h; exact absurd h hzcz
    | 4, 0, _, _ => intro h; exact absurd h c1
    | 4, 1, _, _ => intro h; exact absurd h c2
    | 4, 2, _, _ => intro h; exact absurd h c3
    | 4, 3, _, _ => intro h; exact absurd h.symm hzcz
    | i + 5, _, hi, _ => exact absurd hi (by omega)
    | _, j + 5, _, hj => exact absurd hj (by omega)
  · intro i
    obtain ⟨i, hi⟩ := i
    match i, hi with
    | 0, _ => exact f1
    | 1, _ => exact f2
    | 2, _ => exact f3
    | 3, _ => exact fz
    | 4, _ => exact fcz

/-- **Every root is listed.** If `β` lists five distinct roots of `x⁵ - 6x + 3` in `ℂ`, every
complex root is one of them. -/
theorem quintic_root_enum {β : Fin 5 → ℂ} (hinj : ∀ i j, β i = β j → i = j)
    (hroot : ∀ i, eval (β i) (quinticPoly ℂ) = 0) (w : ℂ) (hw : eval w (quinticPoly ℂ) = 0) :
    ∃ i, β i = w := by
  apply Classical.byContradiction; intro hno
  let L := (FiniteType.elems : List (Fin 5)).map β
  have hL : L.Nodup := FiniteType.nodup_map_of_injective hinj FiniteType.nodup
  have hwL : w ∉ L := fun h => by
    obtain ⟨i, _, hi⟩ := List.mem_map.1 h; exact hno ⟨i, hi⟩
  have hf0 : quinticPoly ℂ ≠ 0 := fun h => by
    have := natDegree_quinticPoly (R := ℂ) C.isField.1; rw [h] at this
    unfold natDegree at this; rw [len_eq_zero.2 rfl] at this; exact absurd this (by decide)
  have := card_roots_le_natDegree C.isDomain hf0 (w :: L) (List.nodup_cons.2 ⟨hwL, hL⟩)
    (fun a ha => by
      rcases List.mem_cons.1 ha with h | h
      · rw [h]; exact hw
      · obtain ⟨i, _, rfl⟩ := List.mem_map.1 h; exact hroot i)
  rw [natDegree_quinticPoly C.isField.1, List.length_cons, List.length_map] at this
  have hc : (FiniteType.elems : List (Fin 5)).length = 5 := FiniteType.card_fin 5
  omega

end Foundations.Algebra
