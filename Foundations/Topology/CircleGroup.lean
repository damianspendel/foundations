import Foundations.Topology.Covering

/-!
# The fundamental group of the circle

A loop `γ` in the circle, starting and ending at the same point, lifts to a path `L` in the line
whose endpoints lie over the same point: `L(1) − L(0) = 2πn` for an integer `n`, the **degree**
(or **winding number**) of the loop — the number of times it winds around the origin,
counted with orientation. By uniqueness of lifts, `n` does not depend on the lift chosen.

* **Homotopy invariance.** Lifting a homotopy of loops, the degree becomes a continuous function
  of the deformation parameter with values in `ℤ` — hence constant. (We prove this for *free*
  homotopies, where the base point may move; this is what the applications in the next file
  need.)
* **Additivity.** Lifting `γ` and then `δ` from where the first lift stopped gives a lift of
  `γ ⬝ δ`, so `deg (γ ⬝ δ) = deg γ + deg δ`.
* **Surjectivity.** The loop `t ↦ cis (2πnt)` has degree `n`.
* **Injectivity.** Two loops of equal degree have lifts with the same endpoints; the straight-line
  homotopy between the lifts, pushed down to the circle, is a homotopy between the loops.

Together: **`π₁(S¹) ≅ ℤ`**, the first non-trivial fundamental group, already computed in
substance by Poincaré. The circle is the simplest space with a "hole", and the integer counts how
often a loop goes around it. Everything topological about the plane in the next file — no
retraction of the disc onto its boundary, Brouwer's fixed-point theorem, the fundamental theorem
of algebra — is a consequence of this one computation.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind
open Foundations.Numbers.C (cabs normSq conj cis)

/-! ## The degree of a loop -/

/-- `γ : ℝ → ℂ` is a **loop in the circle**: continuous, with values of modulus `1` on `[0, 1]`,
and `γ 1 = γ 0`. -/
def IsCircleLoop (γ : R → C) : Prop :=
  Continuous γ ∧ (∀ t, 0 ≤ t → t ≤ 1 → normSq (γ t) = 1) ∧ γ 1 = γ 0

/-- Every loop in the circle has a lift. -/
theorem IsCircleLoop.exists_lift {γ : R → C} (hγ : IsCircleLoop γ) : ∃ L, IsLift γ L := by
  obtain ⟨θ, hθ⟩ := exists_cis_eq (hγ.2.1 0 (Std.le_refl 0) (by grind))
  obtain ⟨L, hL, -⟩ := path_lifting hγ.1 hγ.2.1 hθ
  exact ⟨L, hL⟩

/-- The endpoints of a lift of a loop differ by a multiple of `2π`. -/
theorem IsCircleLoop.lift_int {γ : R → C} (hγ : IsCircleLoop γ) {L : R → R} (hL : IsLift γ L) :
    ∃ n : Int, L 1 - L 0 = 2 * pi * (n : R) :=
  (cis_eq_one_iff _).1 (cis_sub_eq_one (by
    rw [hL.2 1 (by grind) (Std.le_refl 1), hL.2 0 (Std.le_refl 0) (by grind), hγ.2.2]))

/-- **Degree.** The degree (winding number) of a loop in the circle: the integer `n` with
`L(1) − L(0) = 2πn` for a lift `L` (and `0` for functions that are not loops). -/
noncomputable def degree (γ : R → C) : Int :=
  open Classical in
  if h : ∃ n : Int, ∃ L, IsLift γ L ∧ L 1 - L 0 = 2 * pi * (n : R) then h.choose else 0

/-- `n ↦ 2πn` is injective on the integers. -/
theorem two_pi_mul_inj {m n : Int} (h : 2 * pi * (m : R) = 2 * pi * (n : R)) : m = n := by
  have hp := pi_pos
  have hpi : pi * pi⁻¹ = 1 := R.mul_inv_cancel (by grind)
  apply intCast_inj
  calc (m : R) = (2 * pi)⁻¹ * (2 * pi * (m : R)) := by grind
    _ = (n : R) := by rw [h]; grind

/-- **The degree is well defined.** every lift `L` of a loop satisfies `L(1) − L(0) = 2π deg γ`. -/
theorem degree_spec {γ : R → C} (hγ : IsCircleLoop γ) {L : R → R} (hL : IsLift γ L) :
    L 1 - L 0 = 2 * pi * (degree γ : R) := by
  have hex : ∃ n : Int, ∃ L, IsLift γ L ∧ L 1 - L 0 = 2 * pi * (n : R) := by
    obtain ⟨n, hn⟩ := hγ.lift_int hL; exact ⟨n, L, hL, hn⟩
  unfold degree
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨L', hL', e⟩ := hex.choose_spec
  have := lift_unique hL hL' 1 (by grind) (Std.le_refl 1)
  grind

/-- A loop with a lift `L` such that `L(1) − L(0) = 2πn` has degree `n`. -/
theorem degree_eq {γ : R → C} (hγ : IsCircleLoop γ) {L : R → R} (hL : IsLift γ L) {n : Int}
    (h : L 1 - L 0 = 2 * pi * (n : R)) : degree γ = n :=
  two_pi_mul_inj (by rw [← degree_spec hγ hL, h])

/-- The degree depends only on the values on `[0, 1]`. -/
theorem degree_congr {γ δ : R → C} (hγ : IsCircleLoop γ) (hδ : IsCircleLoop δ)
    (h : ∀ t, 0 ≤ t → t ≤ 1 → γ t = δ t) : degree γ = degree δ := by
  obtain ⟨L, hL⟩ := hγ.exists_lift
  exact (degree_eq hδ ⟨hL.1, fun t t0 t1 => by rw [hL.2 t t0 t1, h t t0 t1]⟩ (degree_spec hγ hL)).symm

/-- **Homotopy invariance of the degree.** If `H(s, ·)` is a loop in the circle for every
`s ∈ [0, 1]` (a *free* homotopy: the base point `H(s, 0)` may move), then `H(0, ·)` and `H(1, ·)`
have the same degree. -/
theorem degree_homotopy {H : R → R → C} (hH : Cont2 H)
    (hunit : ∀ s t, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → normSq (H s t) = 1)
    (hloop : ∀ s, 0 ≤ s → s ≤ 1 → H s 1 = H s 0) : degree (H 0) = degree (H 1) := by
  obtain ⟨θ, hθ⟩ := exists_cis_eq (hunit 0 0 (Std.le_refl 0) (by grind) (Std.le_refl 0) (by grind))
  obtain ⟨L, hL, hcis, -⟩ := homotopy_lifting hH hunit hθ
  have loop : ∀ s, 0 ≤ s → s ≤ 1 → IsCircleLoop (H s) := fun s s0 s1 =>
    ⟨hH.slice s, fun t t0 t1 => hunit s t s0 s1 t0 t1, hloop s s0 s1⟩
  have lift : ∀ s, 0 ≤ s → s ≤ 1 → IsLift (H s) (L s) := fun s s0 s1 =>
    ⟨hL.slice s, fun t t0 t1 => hcis s t s0 s1 t0 t1⟩
  -- The degree times `2π` is the continuous function `s ↦ L(s, 1) − L(s, 0)`.
  have hc := const_of_int_valued (f := fun s => L s 1 - L s 0)
    (((hL.slice' 1).cont2_left (B := R)).sub (hL.slice' 0).cont2_left |>.slice' 0)
    (fun s s0 s1 => ⟨degree (H s), degree_spec (loop s s0 s1) (lift s s0 s1)⟩) 1 (by grind)
    (Std.le_refl 1)
  have e0 := degree_spec (loop 0 (Std.le_refl 0) (by grind)) (lift 0 (Std.le_refl 0) (by grind))
  have e1 := degree_spec (loop 1 (by grind) (Std.le_refl 1)) (lift 1 (by grind) (Std.le_refl 1))
  exact two_pi_mul_inj (by rw [← e0, ← e1]; exact hc.symm)

/-! ## Loops at the base point of `S¹` -/

/-- A loop in the metric space `S¹`, viewed as a function into `ℂ`. -/
def toC {x y : S1} (γ : Path x y) : R → C := fun t => (γ.toFun t).1

/-- A point of `S¹` has `|z|² = 1`. -/
theorem S1.normSq_val (z : S1) : normSq z.1 = 1 := (cabs_eq_one_iff _).1 z.2

/-- A loop at the base point of `S¹` is a loop in the circle in the sense of `IsCircleLoop`. -/
theorem isCircleLoop_toC {x : S1} (γ : Path x x) : IsCircleLoop (toC γ) :=
  ⟨(continuous_val _).comp γ.cont, fun t _ _ => S1.normSq_val _, by
    show (γ.toFun 1).1 = (γ.toFun 0).1; rw [γ.source, γ.target]⟩

/-- A jointly continuous family with values in `ℂ` of modulus one is jointly continuous as a
family in `S¹`. -/
theorem Cont2.subtype_mk {A B X : Type} [MetricSpace A] [MetricSpace B] [MetricSpace X]
    {P : X → Prop} {F : A → B → X} (hF : Cont2 F) (h : ∀ a b, P (F a b)) :
    Cont2 (fun a b => (⟨F a b, h a b⟩ : {x // P x})) := hF

/-- `cis θ` as a point of `S¹`. -/
noncomputable def S1.cis (θ : R) : S1 := ⟨C.cis θ, (cabs_eq_one_iff _).2 (normSq_cis θ)⟩

/-- The degree of a homotopy class of loops at `1 ∈ S¹` (well defined by homotopy invariance). -/
noncomputable def degreeπ : FundamentalGroup S1 S1.one → Int :=
  Quotient.lift (fun γ => degree (toC γ)) (fun γ δ h => by
    obtain ⟨H, hH, h0, h1, hx, hy⟩ := h
    have hH' : Cont2 (fun s t => (H s t).1) := hH.comp_left (continuous_val _)
    have := degree_homotopy hH' (fun s t _ _ _ _ => S1.normSq_val _) (fun s s0 s1 => by
      (try simp only); rw [hx s s0 s1, hy s s0 s1])
    rw [degree_congr (isCircleLoop_toC γ) ⟨hH'.slice 0, fun t _ _ => S1.normSq_val _, by
        (try simp only); rw [hx 0 (Std.le_refl 0) (by grind), hy 0 (Std.le_refl 0) (by grind)]⟩
        (fun t t0 t1 => by simp only [toC]; rw [h0 t t0 t1]), this]
    exact degree_congr ⟨hH'.slice 1, fun t _ _ => S1.normSq_val _, by
        (try simp only); rw [hx 1 (by grind) (Std.le_refl 1), hy 1 (by grind) (Std.le_refl 1)]⟩
      (isCircleLoop_toC δ) (fun t t0 t1 => by simp only [toC]; rw [h1 t t0 t1]))

/-- The degree of the class of `γ` is the degree of `γ`. -/
theorem degreeπ_mk (γ : Path S1.one S1.one) :
    degreeπ (FundamentalGroup.mk γ) = degree (toC γ) := rfl

/-- **Additivity of the degree.** `deg (γ ⬝ δ) = deg γ + deg δ`. -/
theorem degree_trans (γ δ : Path S1.one S1.one) :
    degree (toC (γ.trans δ)) = degree (toC γ) + degree (toC δ) := by
  obtain ⟨Lγ, hLγ⟩ := (isCircleLoop_toC γ).exists_lift
  obtain ⟨Lδ, hLδ, hLδ0⟩ := path_lifting (isCircleLoop_toC δ).1 (isCircleLoop_toC δ).2.1
    (θ₀ := Lγ 1) (by rw [hLγ.2 1 (by grind) (Std.le_refl 1)]; show (γ.toFun 1).1 = (δ.toFun 0).1
                     rw [γ.target, δ.source])
  have eγ := degree_spec (isCircleLoop_toC γ) hLγ
  have eδ := degree_spec (isCircleLoop_toC δ) hLδ
  -- Concatenate the lifts.
  let L : R → R := fun t => open Classical in if t ≤ 1 / 2 then Lγ (2 * t) else Lδ (2 * t - 1)
  have hL : IsLift (toC (γ.trans δ)) L := by
    refine ⟨Continuous.paste (hLγ.1.comp continuous_two_mul) (hLδ.1.comp continuous_two_mul_sub_one)
      (by (try simp only); rw [show 2 * (1 / 2 : R) = 1 by grind, show (1 : R) - 1 = 0 by grind, hLδ0]),
      fun t t0 t1 => ?_⟩
    simp only [L, toC, Path.trans_apply]
    by_cases h : t ≤ 1 / 2
    · rw [ite_eq_left h, ite_eq_left h]; exact hLγ.2 _ (by grind) (by grind)
    · rw [ite_eq_right h, ite_eq_right h]; exact hLδ.2 _ (by grind) (by grind)
  apply degree_eq (isCircleLoop_toC _) hL
  simp only [L]
  rw [ite_eq_right (by grind), ite_eq_left (by grind), show 2 * (1 : R) - 1 = 1 by grind,
    show 2 * (0 : R) = 0 by grind]
  grind

/-- The loop `t ↦ cis (2πnt)`, winding `n` times around the circle. -/
noncomputable def windLoop (n : Int) : Path S1.one S1.one where
  toFun t := S1.cis (2 * pi * (n : R) * t)
  cont := continuous_subtype_mk (f := fun t => C.cis (2 * pi * (n : R) * t))
    (continuous_cis.comp (continuous_affine (2 * pi * (n : R)) 0) |>.congr fun t => by
      simp only [Lean.Grind.Semiring.add_zero])
    (fun t => (cabs_eq_one_iff _).2 (normSq_cis _))
  source := Subtype.ext (by
    show C.cis (2 * pi * (n : R) * 0) = 1
    rw [show 2 * pi * (n : R) * 0 = 0 by grind, cis_zero])
  target := Subtype.ext (by
    show C.cis (2 * pi * (n : R) * 1) = 1
    rw [show 2 * pi * (n : R) * 1 = 2 * pi * (n : R) by grind, cis_two_pi_int])

/-- **The loop `t ↦ cis (2πnt)` has degree `n`.** -/
theorem degree_windLoop (n : Int) : degree (toC (windLoop n)) = n :=
  degree_eq (isCircleLoop_toC _) (L := fun t => 2 * pi * (n : R) * t)
    ⟨(continuous_affine (2 * pi * (n : R)) 0).congr fun t => by grind, fun _ _ _ => rfl⟩
    (by grind)

/-- **Loops of equal degree are homotopic.** Push the straight-line homotopy between lifts with
the same endpoints down to the circle. -/
theorem homotopic_of_degree_eq {γ δ : Path S1.one S1.one} (h : degree (toC γ) = degree (toC δ)) :
    Path.Homotopic γ δ := by
  have h1 : cis 0 = toC γ 0 := by rw [cis_zero]; show (1 : C) = (γ.toFun 0).1; rw [γ.source]; rfl
  have h2 : cis 0 = toC δ 0 := by rw [cis_zero]; show (1 : C) = (δ.toFun 0).1; rw [δ.source]; rfl
  obtain ⟨Lγ, hLγ, hLγ0⟩ := path_lifting (isCircleLoop_toC γ).1 (isCircleLoop_toC γ).2.1 h1
  obtain ⟨Lδ, hLδ, hLδ0⟩ := path_lifting (isCircleLoop_toC δ).1 (isCircleLoop_toC δ).2.1 h2
  have eγ := degree_spec (isCircleLoop_toC γ) hLγ
  have eδ := degree_spec (isCircleLoop_toC δ) hLδ
  rw [h] at eγ
  have hs : Cont2 (fun (s : R) (_ : R) => s) := cont2_fst
  let F : R → R → R := fun s t => (1 - s) * Lγ (clamp01 t) + s * Lδ (clamp01 t)
  have hF : Cont2 F := (((cont2_const 1).sub hs).mul (hLγ.1.comp continuous_clamp01).cont2_right).add
    (hs.mul (hLδ.1.comp continuous_clamp01).cont2_right)
  refine ⟨fun s t => S1.cis (F s t), Cont2.subtype_mk (hF.comp_left continuous_cis) _,
    fun t t0 t1 => Subtype.ext ?_, fun t t0 t1 => Subtype.ext ?_, fun s _ _ => Subtype.ext ?_,
    fun s _ _ => Subtype.ext ?_⟩
  · show cis (F 0 t) = toC γ t
    rw [← hLγ.2 t t0 t1]; simp only [F]; rw [clamp01_of_mem t0 t1]; congr 1; grind
  · show cis (F 1 t) = toC δ t
    rw [← hLδ.2 t t0 t1]; simp only [F]; rw [clamp01_of_mem t0 t1]; congr 1; grind
  · show cis (F s 0) = 1
    simp only [F]; rw [clamp01_of_mem (Std.le_refl 0) (by grind), hLγ0, hLδ0,
      show (1 - s) * 0 + s * 0 = 0 by grind, cis_zero]
  · show cis (F s 1) = 1
    simp only [F]; rw [clamp01_of_mem (by grind) (Std.le_refl 1),
      show (1 - s) * Lγ 1 + s * Lδ 1 = 2 * pi * (degree (toC δ) : R) by grind, cis_two_pi_int]

/-! ## `π₁(S¹) ≅ ℤ` -/

/-- The degree as a group homomorphism `π₁(S¹, 1) → (ℤ, +)`. -/
noncomputable def degreeHom :
    Foundations.Algebra.Hom (FundamentalGroup S1 S1.one) Foundations.Algebra.IntAdd where
  toFun a := Foundations.Algebra.IntAdd.of (degreeπ a)
  map_mul a b := by
    obtain ⟨γ, rfl⟩ := FundamentalGroup.exists_mk a
    obtain ⟨δ, rfl⟩ := FundamentalGroup.exists_mk b
    rw [FundamentalGroup.mk_mul]
    exact degree_trans γ δ

/-- **π₁(S¹) ≅ ℤ.** The fundamental group of the circle is the integers, the isomorphism
being the degree (winding number). -/
noncomputable def fundamentalGroup_circle :
    Foundations.Algebra.Iso (FundamentalGroup S1 S1.one) Foundations.Algebra.IntAdd :=
  Foundations.Algebra.Iso.ofBijective degreeHom
    (fun a b hab => by
      obtain ⟨γ, rfl⟩ := FundamentalGroup.exists_mk a
      obtain ⟨δ, rfl⟩ := FundamentalGroup.exists_mk b
      exact FundamentalGroup.mk_eq_mk.2 (homotopic_of_degree_eq hab))
    (fun n => ⟨FundamentalGroup.mk (windLoop n), degree_windLoop n⟩)

/-- **π₁(S¹) ≅ ℤ, as a statement.** The degree map on homotopy classes of loops at `1 ∈ S¹` is
a bijective homomorphism onto `(ℤ, +)`. -/
theorem pi1_circle_iso_int :
    (∀ a b : FundamentalGroup S1 S1.one, degreeπ (a * b) = degreeπ a + degreeπ b) ∧
    (∀ a b : FundamentalGroup S1 S1.one, degreeπ a = degreeπ b → a = b) ∧
    (∀ n : Int, ∃ a : FundamentalGroup S1 S1.one, degreeπ a = n) :=
  ⟨degreeHom.map_mul, fun _ _ h => fundamentalGroup_circle.injective h,
    fun n => ⟨FundamentalGroup.mk (windLoop n), degree_windLoop n⟩⟩

end Foundations.Topology
