import Foundations.Topology.Circle

/-!
# Path lifting and homotopy lifting for the exponential map

The exponential map `p(θ) = cis θ` wraps the real line around the circle; over a small arc it
looks like a stack of disjoint copies of the arc, so that `p` is a **covering map** (the notion
goes back to Poincaré and to the Riemann surfaces of the nineteenth century). The computation of
`π₁(S¹)` rests on two of its properties:

* **Path lifting.** Every path `γ` in the circle has a continuous lift `L` to the line,
  `cis (L t) = γ t` on `[0, 1]`, starting at any prescribed angle over `γ 0`; two lifts differ by a
  constant (**uniqueness**).
* **Homotopy lifting.** Every jointly continuous family `H(s, t)` of points of the circle lifts to
  a jointly continuous family of angles.

The lifts are written down explicitly. Uniform continuity (`uniform_square`, the Lebesgue-number
argument of the previous file) gives `M` such that points of the path at parameter distance
`≤ 1/M` are less than `1` apart; we say the subdivision into `M` steps is **fine**. Cutting `[0, t]`
into `M` equal steps `t_k = k t / M`, every quotient `γ(t_{k+1}) · conj γ(t_k)` lies in the right
half of the circle, where the local inverse `ang` of `p` is defined, and

  `L(t) = θ₀ + Σ_{k<M} ang (γ(t_{k+1}) · conj γ(t_k))`

is a lift: applying `cis`, the sum becomes a product which **telescopes** to `γ(t) · conj γ(0)`.
Since `ang` is Lipschitz, the formula is continuous in `t` — and, for a family `H(s, ·)`, jointly
continuous in `(s, t)`: homotopy lifting comes for free.

Uniqueness rests on the intermediate value theorem: a continuous function on `[0, 1]` with values
in `2πℤ` cannot jump, so it is constant.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind
open Foundations.Numbers.C (cabs normSq conj cis)

/-! ## Arithmetic of the subdivision -/

/-- Division by a positive number preserves `≤`. -/
theorem div_le_div_of_le {x y M : R} (hM : 0 < M) (h : x ≤ y) : x / M ≤ y / M := by
  rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]
  exact OrderedRing.mul_le_mul_of_nonneg_right h (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.2 hM))

/-- The subdivision points `c t / M` (`0 ≤ c ≤ M`, `t ∈ [0, 1]`) lie in `[0, 1]`. -/
theorem step_mem {M c t : R} (hM : 0 < M) (hc0 : 0 ≤ c) (hc : c ≤ M) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ c * t / M ∧ c * t / M ≤ 1 := by
  have a := OrderedRing.mul_nonneg hc0 h0
  have b := OrderedRing.mul_le_mul_of_nonneg_left h1 hc0
  have k1 := div_le_div_of_le hM a
  have k2 := div_le_div_of_le hM (show c * t ≤ M by grind)
  constructor <;> grind

/-- A positive natural number is positive in `ℝ`. -/
theorem natCast_pos_R {M : Nat} (h : 0 < M) : (0 : R) < (M : R) := by
  have := OrderedRing.natCast_le_natCast_of_le (R := R) 1 M h; grind

/-! ## Fine subdivisions -/

/-- The subdivision of `[0, 1]` into `M` steps is **fine** for `γ`: `γ` takes values on the unit
circle on `[0, 1]`, and points at parameter distance `≤ 1/M` are mapped less than `1` apart. -/
def Fine (γ : R → C) (M : Nat) : Prop :=
  0 < M ∧ (∀ t, 0 ≤ t → t ≤ 1 → normSq (γ t) = 1) ∧
    ∀ u v, 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → abs (u - v) ≤ 1 / (M : R) → cabs (γ u - γ v) < 1

/-- For a jointly continuous family of paths in the circle, some subdivision is fine for all the
paths `H(s, ·)`, `s ∈ [0, 1]`, at once. -/
theorem exists_fine {H : R → R → C} (hH : Cont2 H)
    (hunit : ∀ s t, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → normSq (H s t) = 1) :
    ∃ M, ∀ s, 0 ≤ s → s ≤ 1 → Fine (H s) M := by
  obtain ⟨δ, hδ, h⟩ := uniform_square hH (by grind : (0 : R) < 1)
  obtain ⟨N, hN⟩ := eps_small hδ
  refine ⟨N + 1, fun s s0 s1 => ⟨by omega, fun t t0 t1 => hunit s t s0 s1 t0 t1,
    fun u v u0 u1 v0 v1 huv => h s u v s0 s1 u0 u1 v0 v1 ?_⟩⟩
  have := hN N (Nat.le_refl N)
  have e : ((N + 1 : Nat) : R) = (N : R) + 1 := by grind
  rw [e] at huv; grind

/-- The `k`-th summand of the lifting formula at parameter `t`: the angle from `γ(k t/M)` to
`γ((k+1) t/M)`. -/
noncomputable def angStep (γ : R → C) (M : Nat) (t : R) (k : Nat) : R :=
  ang (γ (((k : R) + 1) * t / (M : R)) * conj (γ ((k : R) * t / (M : R))))

/-- The **lifting sum** `Σ_{k<M} ang (γ(t_{k+1}) · conj γ(t_k))`. -/
noncomputable def angSum (γ : R → C) (M : Nat) (t : R) : R := fsum (angStep γ M t) M

/-- For a fine subdivision, each quotient of consecutive points lies in the right half of the
circle (the domain of `ang`). -/
theorem step_dom {γ : R → C} {M : Nat} (hF : Fine γ M) {t : R} (h0 : 0 ≤ t) (h1 : t ≤ 1) {k : Nat}
    (hk : k < M) :
    normSq (γ (((k : R) + 1) * t / (M : R)) * conj (γ ((k : R) * t / (M : R)))) = 1 ∧
      0 < (γ (((k : R) + 1) * t / (M : R)) * conj (γ ((k : R) * t / (M : R)))).re := by
  obtain ⟨hM, hunit, hclose⟩ := hF
  have hMR := natCast_pos_R hM
  have hk0 : (0 : R) ≤ (k : R) := OrderedRing.natCast_nonneg
  have hk1 : (k : R) + 1 ≤ (M : R) := by
    have := OrderedRing.natCast_le_natCast_of_le (R := R) (k + 1) M hk; grind
  obtain ⟨u0, u1⟩ := step_mem hMR (by grind) hk1 h0 h1
  obtain ⟨v0, v1⟩ := step_mem hMR hk0 (by grind) h0 h1
  apply quotient_right (hunit _ v0 v1) (hunit _ u0 u1)
  apply hclose _ _ u0 u1 v0 v1
  rw [show ((k : R) + 1) * t / (M : R) - (k : R) * t / (M : R) = t / M by grind,
    abs_of_nonneg (by have := div_le_div_of_le hMR h0; grind)]
  exact div_le_div_of_le hMR h1

/-- **Telescoping.** For a fine subdivision and `t ∈ [0, 1]`, `cis (angSum γ M t) · γ 0 = γ t`. -/
theorem cis_angSum {γ : R → C} {M : Nat} (hF : Fine γ M) {t : R} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    cis (angSum γ M t) * γ 0 = γ t := by
  have hMR := natCast_pos_R hF.1
  suffices key : ∀ m, m ≤ M → cis (fsum (angStep γ M t) m) * γ 0 = γ ((m : R) * t / M) by
    have := key M (Nat.le_refl M)
    rw [show (M : R) * t / M = t by grind] at this; exact this
  intro m
  induction m with
  | zero =>
    intro _
    show cis 0 * γ 0 = γ (((0 : Nat) : R) * t / M)
    rw [cis_zero, C.one_mul]; congr 1; grind
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hm0 : (0 : R) ≤ (m : R) := OrderedRing.natCast_nonneg
    have hm1 : (m : R) ≤ (M : R) := OrderedRing.natCast_le_natCast_of_le (R := R) m M (by omega)
    obtain ⟨v0, v1⟩ := step_mem hMR hm0 hm1 h0 h1
    have hs := (ang_spec (step_dom hF h0 h1 (k := m) (by omega)).1
      (step_dom hF h0 h1 (k := m) (by omega)).2).1
    show cis (fsum (angStep γ M t) m + angStep γ M t m) * γ 0 = γ (((m + 1 : Nat) : R) * t / M)
    rw [← C.cis_add, show ((m + 1 : Nat) : R) * t / M = ((m : R) + 1) * t / M by grind]
    unfold angStep; rw [hs]
    calc cis (fsum (angStep γ M t) m) * (γ (((m : R) + 1) * t / M) * conj (γ ((m : R) * t / M)))
          * γ 0
        = γ (((m : R) + 1) * t / M) * conj (γ ((m : R) * t / M)) *
            (cis (fsum (angStep γ M t) m) * γ 0) := by grind
      _ = γ (((m : R) + 1) * t / M) := by rw [ih']; exact mul_conj_mul (hF.2.1 _ v0 v1) _

/-- The lifting sum vanishes at `t = 0`. -/
theorem angSum_zero {γ : R → C} {M : Nat} (hF : Fine γ M) : angSum γ M 0 = 0 := by
  have hMR := natCast_pos_R hF.1
  apply fsum_eq_zero
  intro k _
  unfold angStep
  rw [show ((k : R) + 1) * 0 / (M : R) = 0 by grind, show (k : R) * 0 / (M : R) = 0 by grind,
    mul_conj_eq_one (hF.2.1 0 (Std.le_refl 0) (by grind)), ang_one]

/-- **Joint continuity of the lifting sum.** It holds for a family of paths with a common fine
subdivision (clamped to `[0, 1]²`). -/
theorem cont2_angSum {H : R → R → C} {M : Nat} (hH : Cont2 H)
    (hF : ∀ s, 0 ≤ s → s ≤ 1 → Fine (H s) M) :
    Cont2 (fun s t => angSum (H (clamp01 s)) M (clamp01 t)) := by
  unfold angSum
  apply Cont2.fsum (F := fun k s t => angStep (H (clamp01 s)) M (clamp01 t) k)
  intro k hk
  unfold angStep
  have hs : Cont2 (fun s (_ : R) => clamp01 s) := continuous_clamp01.cont2_left
  have hlin : ∀ c : R, Cont2 (fun (_ : R) t => c * clamp01 t / (M : R)) := fun c =>
    (((continuous_affine (c / M) 0).comp continuous_clamp01).congr fun t => by grind).cont2_right
  apply Cont2.ang ((hH.comp2 hs (hlin _)).cmul ((hH.comp2 hs (hlin _)).comp_left continuous_conj))
  intro s t
  have ms := clamp01_mem s; have mt := clamp01_mem t
  exact step_dom (hF _ ms.1 ms.2) mt.1 mt.2 hk

/-! ## Lifting -/

/-- `L` is a **lift** of the path `γ` through the exponential map: `L` is continuous and
`cis (L t) = γ t` for `t ∈ [0, 1]`. -/
def IsLift (γ : R → C) (L : R → R) : Prop :=
  Continuous L ∧ ∀ t, 0 ≤ t → t ≤ 1 → cis (L t) = γ t

/-- A constant plus a continuous function is continuous. -/
theorem Continuous.const_add {f : R → R} (hf : Continuous f) (c : R) :
    Continuous (fun t => c + f t) := ((cont2_const c).add (hf.cont2_left (B := R))).slice' 0

/-- **Homotopy lifting for the exponential map.** A jointly continuous family `H(s, t)` of points
of the circle (`s, t ∈ [0, 1]`) lifts to a jointly continuous family of angles `L(s, t)`,
`cis L(s, t) = H(s, t)`, starting at any angle `θ₀` over `H(0, 0)`. -/
theorem homotopy_lifting {H : R → R → C} (hH : Cont2 H)
    (hunit : ∀ s t, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → normSq (H s t) = 1) {θ₀ : R}
    (hθ : cis θ₀ = H 0 0) :
    ∃ L : R → R → R, Cont2 L ∧ (∀ s t, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → cis (L s t) = H s t) ∧
      L 0 0 = θ₀ := by
  -- First lift the path `s ↦ H(s, 0)`, then add the lifting sums of the paths `H(s, ·)`.
  obtain ⟨M₀, hM₀⟩ := exists_fine (H := fun (_ : R) s => H s 0) (hH.slice' 0).cont2_right
    (fun _ s _ _ s0 s1 => hunit s 0 s0 s1 (Std.le_refl 0) (by grind))
  have hF₀ := hM₀ 0 (Std.le_refl 0) (by grind)
  obtain ⟨M, hM⟩ := exists_fine hH hunit
  let Θ : R → R := fun s => θ₀ + angSum (fun s => H s 0) M₀ (clamp01 s)
  have hΘ : Continuous Θ :=
    ((cont2_angSum (H := fun (_ : R) s => H s 0) (hH.slice' 0).cont2_right hM₀).slice 0).const_add θ₀
  refine ⟨fun s t => Θ s + angSum (H (clamp01 s)) M (clamp01 t),
    hΘ.cont2_left.add (cont2_angSum hH hM), fun s t s0 s1 t0 t1 => ?_, ?_⟩
  · have e1 := cis_angSum hF₀ s0 s1
    have e2 := cis_angSum (hM s s0 s1) t0 t1
    simp only [Θ]; rw [clamp01_of_mem s0 s1, clamp01_of_mem t0 t1, ← C.cis_add, ← C.cis_add, hθ]
    rw [← e2, ← e1]; grind
  · simp only [Θ]
    rw [clamp01_of_mem (Std.le_refl 0) (by grind), angSum_zero hF₀, angSum_zero (hM 0 (Std.le_refl 0)
      (by grind))]; grind

/-- **Path lifting for the exponential map.** Every path `γ` in the circle has a lift `L`,
`cis (L t) = γ t` on `[0, 1]`, starting at any angle `θ₀` over `γ 0`. -/
theorem path_lifting {γ : R → C} (hγ : Continuous γ)
    (hunit : ∀ t, 0 ≤ t → t ≤ 1 → normSq (γ t) = 1) {θ₀ : R} (hθ : cis θ₀ = γ 0) :
    ∃ L, IsLift γ L ∧ L 0 = θ₀ := by
  obtain ⟨L, hL, h1, h2⟩ := homotopy_lifting (H := fun _ t => γ t) hγ.cont2_right
    (fun _ t _ _ t0 t1 => hunit t t0 t1) hθ
  exact ⟨fun t => L 0 t, ⟨hL.slice 0, fun t t0 t1 => h1 0 t (Std.le_refl 0) (by grind) t0 t1⟩, h2⟩

/-! ## Uniqueness of lifts -/

/-- A continuous function with values in `2πℤ` on `[0, 1]` never exceeds its value at `0`. -/
theorem le_of_int_valued {f : R → R} (hf : Continuous f)
    (h : ∀ t, 0 ≤ t → t ≤ 1 → ∃ k : Int, f t = 2 * pi * (k : R)) :
    ∀ t, 0 ≤ t → t ≤ 1 → f t ≤ f 0 := by
  intro t t0 t1
  apply Classical.byContradiction; intro hlt
  have hp := pi_pos
  obtain ⟨a, ha⟩ := h 0 (Std.le_refl 0) (by grind)
  obtain ⟨b, hb⟩ := h t t0 t1
  have hab : (a : R) < (b : R) := by
    apply Classical.byContradiction; intro hn
    have := OrderedRing.mul_le_mul_of_nonneg_left (show (b : R) ≤ (a : R) by grind)
      (show (0 : R) ≤ 2 * pi by grind)
    grind
  have hab' : a + 1 ≤ b := by have := (intCast_lt (K := R)).1 hab; omega
  have hab'' : (a : R) + 1 ≤ (b : R) := by
    rcases (by omega : a + 1 < b ∨ a + 1 = b) with e | e
    · have := (intCast_lt (K := R)).2 e; grind
    · rw [← e]; grind
  obtain ⟨c, c0, c1, hc⟩ := intermediate_value_connected (f := f) (v := 2 * pi * (a : R) + pi) t0
    (fun x _ _ => (continuousAt_iff_R f x).1 (hf x)) (by grind)
    (by have := OrderedRing.mul_le_mul_of_nonneg_left hab'' (show (0 : R) ≤ 2 * pi by grind); grind)
  obtain ⟨k, hk⟩ := h c c0 (by grind)
  exact two_pi_int_ne_odd k a (by rw [← hk, hc])

/-- **Integer-valued functions are constant.** A continuous function with values in `2πℤ` is
constant on `[0, 1]` — the connectedness of
the interval, in the form of the intermediate value theorem. -/
theorem const_of_int_valued {f : R → R} (hf : Continuous f)
    (h : ∀ t, 0 ≤ t → t ≤ 1 → ∃ k : Int, f t = 2 * pi * (k : R)) :
    ∀ t, 0 ≤ t → t ≤ 1 → f t = f 0 := by
  intro t t0 t1
  have h1 := le_of_int_valued hf h t t0 t1
  have hneg : Continuous (fun t => -f t) :=
    ((cont2_const 0).sub (hf.cont2_left (B := R))).slice' 0 |>.congr fun t => by grind
  have h2 := le_of_int_valued hneg (fun t t0 t1 => by
    obtain ⟨k, hk⟩ := h t t0 t1; exact ⟨-k, by rw [hk]; grind⟩) t t0 t1
  grind

/-- **Uniqueness of lifts.** Two lifts of the same path differ by a constant on `[0, 1]`. -/
theorem lift_unique {γ : R → C} {L₁ L₂ : R → R} (h₁ : IsLift γ L₁) (h₂ : IsLift γ L₂) :
    ∀ t, 0 ≤ t → t ≤ 1 → L₁ t - L₂ t = L₁ 0 - L₂ 0 :=
  const_of_int_valued (f := fun t => L₁ t - L₂ t)
    ((h₁.1.cont2_left (B := R)).sub h₂.1.cont2_left |>.slice' 0)
    (fun t t0 t1 => (cis_eq_one_iff _).1 (cis_sub_eq_one (by rw [h₁.2 t t0 t1, h₂.2 t t0 t1])))

end Foundations.Topology
