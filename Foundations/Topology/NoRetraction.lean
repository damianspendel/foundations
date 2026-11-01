import Foundations.Topology.CircleGroup

/-!
# No retraction of the disc onto its boundary; Brouwer's fixed-point theorem in the plane

Every continuous map of the closed disc `D² = {z : |z| ≤ 1}` into itself has a **fixed point**.
L. E. J. **Brouwer** proved this, in every dimension, in 1910–12 (the planar case was known in
equivalent forms to Poincaré and to Bohl, 1904). The theorem is the archetype of a *pure
existence* statement: it asserts that a fixed point exists without offering any way to find one,
or even to approximate one in a manner that depends continuously on the map. History has a sense
of irony: a few years later Brouwer became the founder of **intuitionism**, the philosophy of
mathematics according to which an existence claim is meaningful only when accompanied by a
construction — and he came to reject, in that spirit, the very form of his own most famous
theorem. (Constructive substitutes exist: approximate fixed points can be found, but exact ones
cannot in general be computed.) The proof below is classical through and through; `#print
axioms` will duly report `Classical.choice`.

The proof is the topological one, via the degree of the previous file.

* **The boundary of a disc map has degree zero.** If `G : D² → S¹` is continuous, the boundary
  loop `t ↦ G(cis 2πt)` is freely homotopic, through the loops `t ↦ G(s · cis 2πt)`, to the
  constant loop `G(0)`; so its degree is `0`. (The disc is contractible: its inclusion induces
  the zero map on `π₁`.)
* **No retraction.** A continuous `r : D² → S¹` fixing every boundary point would have boundary
  loop `t ↦ cis 2πt`, of degree `1 ≠ 0`. The circle is not a "continuous shadow" of the disc.
* **Brouwer.** If `f : D² → D²` had no fixed point, `G(z) = (z − f z)/|z − f z|` would be a
  continuous map `D² → S¹`; its boundary loop has degree `0`, but the homotopy
  `(e − u·f(e))/|e − u·f(e)|`, `u ∈ [0, 1]`, `e = cis 2πt`, deforms it into `t ↦ cis 2πt`, of
  degree `1` — the vector `e − u·f(e)` never vanishes, since `|u·f(e)| ≤ 1 = |e|` with equality only
  if `f(e) = e`. (Classically one builds a retraction from `f`; the homotopy avoids the explicit
  formula.)
* **Maps of non-zero degree are surjective**: a loop in the circle missing a point can be
  contracted along straight segments away from it.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind
open Foundations.Numbers.C (cabs normSq conj cis)

variable {A B X Y : Type} [MetricSpace A] [MetricSpace B] [MetricSpace X] [MetricSpace Y]

/-! ## Continuity tools -/

/-- Post-composition with a map continuous at every value of the family. -/
theorem Cont2.comp_left' {f : X → Y} {H : A → B → X} (hH : Cont2 H)
    (hf : ∀ a b, ContinuousAt f (H a b)) : Cont2 (fun a b => f (H a b)) :=
  cont2_of_seq fun _ _ _ _ ha hb => (continuousAt_iff_seq f _).1 (hf _ _) _ (hH.seq ha hb)

/-- Composition with a map continuous at every value. -/
theorem Continuous.comp_at {f : X → Y} {g : A → X} (hg : Continuous g)
    (hf : ∀ a, ContinuousAt f (g a)) : Continuous (fun a => f (g a)) :=
  (Cont2.comp_left' (hg.cont2_left (B := R)) fun a _ => hf a).slice' 0

/-- The embedding `ℝ → ℂ` is continuous. -/
theorem continuous_ofReal : Continuous C.ofReal :=
  (Cont2.mkC (cont2_snd (A := R)) (cont2_const 0)).slice 0

/-- The modulus is continuous. -/
theorem continuous_cabs : Continuous cabs :=
  continuous_of_lipschitz (K := 1) (by grind) fun z w => by
    rw [dist_R, dist_C]
    have := C.cabs_sub_le z w; have := C.cabs_sub_le w z; rw [C.cabs_sub_comm w z] at this
    have := abs_le.2 (show -cabs (z - w) ≤ cabs z - cabs w ∧ cabs z - cabs w ≤ cabs (z - w) from
      ⟨by grind, by grind⟩)
    grind

/-- **Limit of reciprocals.** If `aₙ → L > 0` then `1/aₙ → 1/L`. -/
theorem tendsto_one_div {a : Nat → R} {L : R} (h : Tendsto a L) (hL : 0 < L) :
    Tendsto (fun n => 1 / a n) (1 / L) := fun ε hε => by
  obtain ⟨N₁, h₁⟩ := h (L / 2) (by grind)
  have hq : 0 < ε * L * L / 2 := by
    have := OrderedRing.mul_pos (OrderedRing.mul_pos hε hL) hL; grind
  obtain ⟨N₂, h₂⟩ := h (ε * L * L / 2) hq
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have k1 := abs_lt.1 (h₁ n (by omega))
  have k2 := h₂ n (by omega)
  have ha : 0 < a n := by grind
  have hp : 0 < a n * L := OrderedRing.mul_pos ha hL
  have e : 1 / a n - 1 / L = (L - a n) * (1 / (a n * L)) := by grind
  have hpos : 0 < 1 / (a n * L) := div_pos (by grind) hp
  have hle : 1 / (a n * L) ≤ 1 / (L * L / 2) := one_div_le_one_div (by
    have := OrderedRing.mul_pos hL hL; grind) (by
    have := OrderedRing.mul_le_mul_of_nonneg_right (Std.le_of_lt k1.1) (Std.le_of_lt hL); grind)
  rw [e, abs_mul, abs_of_nonneg (Std.le_of_lt hpos), abs_sub_comm]
  have m1 := OrderedRing.mul_lt_mul_of_pos_right k2 hpos
  have m2 := OrderedRing.mul_le_mul_of_nonneg_left hle (Std.le_of_lt hq)
  have e2 : ε * L * L / 2 * (1 / (L * L / 2)) = ε := by
    have := OrderedRing.mul_pos hL hL; grind
  grind

/-! ## Normalisation onto the circle -/

/-- **Normalisation.** `w ↦ w / |w|` projects `ℂ ∖ {0}` radially onto the circle. -/
noncomputable def nrm (w : C) : C := C.ofReal (1 / cabs w) * w

/-- A non-zero number normalises to a point of the circle. -/
theorem normSq_nrm {w : C} (hw : w ≠ 0) : normSq (nrm w) = 1 := by
  have hc := C.cabs_pos hw
  have h2 := C.cabs_mul_self w
  unfold nrm; rw [C.normSq_mul]
  have : normSq (C.ofReal (1 / cabs w)) = 1 / cabs w * (1 / cabs w) := by
    unfold normSq C.ofReal; grind
  rw [this, ← h2]; grind

/-- Points of the circle are fixed by normalisation. -/
theorem nrm_of_unit {w : C} (h : normSq w = 1) : nrm w = w := by
  unfold nrm; rw [(cabs_eq_one_iff w).2 h, show (1 : R) / 1 = 1 by grind]
  apply C.ext <;> simp only [C.mul_re, C.mul_im] <;> show _ = _ <;> unfold C.ofReal <;>
    simp only <;> grind

/-- Normalisation is continuous away from `0`. -/
theorem continuousAt_nrm {w : C} (hw : w ≠ 0) : ContinuousAt nrm w := by
  apply (continuousAt_iff_seq nrm w).2
  intro s hs
  have hc : Converges (fun n => cabs (s n)) (cabs w) :=
    (continuousAt_iff_seq cabs w).1 (continuous_cabs w) s hs
  have hinv := tendsto_one_div hc (C.cabs_pos hw)
  have hof : Converges (fun n => C.ofReal (1 / cabs (s n))) (C.ofReal (1 / cabs w)) :=
    (continuousAt_iff_seq C.ofReal _).1 (continuous_ofReal _) _ hinv
  exact cont2_cmul.seq hof hs

/-! ## The disc -/

/-- **Closed unit disc.** `D² = {z ∈ ℂ : |z| ≤ 1}`. -/
abbrev Disc : Type := {z : C // cabs z ≤ 1}

/-- `|cis θ| = 1`. -/
theorem cabs_cis (θ : R) : cabs (cis θ) = 1 := (cabs_eq_one_iff _).2 (normSq_cis θ)

/-- The boundary point `cis 2πt` of the disc. -/
noncomputable def bd (t : R) : Disc := ⟨C.cis (2 * pi * t), by rw [cabs_cis]; grind⟩

/-- `t ↦ cis 2πt` is continuous. -/
theorem continuous_cis_two_pi : Continuous (fun t => C.cis (2 * pi * t)) :=
  continuous_cis.comp ((continuous_affine (2 * pi) 0).congr fun t => by grind)

/-- The boundary loop is continuous as a map into the disc. -/
theorem continuous_bd : Continuous bd := continuous_subtype_mk continuous_cis_two_pi _

/-- The boundary loop is closed: `bd 1 = bd 0`. -/
theorem bd_one : bd 1 = bd 0 := Subtype.ext (by
  show C.cis (2 * pi * 1) = C.cis (2 * pi * 0)
  rw [show 2 * pi * 1 = 2 * pi * ((1 : Int) : R) by grind, cis_two_pi_int,
    show 2 * pi * (0 : R) = 0 by grind, cis_zero])

/-- **The standard loop `t ↦ cis 2πt` has degree `1`.** -/
theorem degree_cis_two_pi : degree (fun t => C.cis (2 * pi * t)) = 1 :=
  degree_eq ⟨continuous_cis_two_pi, fun t _ _ => normSq_cis _, congrArg Subtype.val bd_one⟩
    (L := fun t => 2 * pi * t) ⟨(continuous_affine (2 * pi) 0).congr fun t => by grind,
      fun _ _ _ => rfl⟩ (by grind)

/-- A constant loop has degree `0`. -/
theorem degree_const {c : C} (hc : normSq c = 1) : degree (fun _ => c) = 0 := by
  obtain ⟨θ, hθ⟩ := exists_cis_eq hc
  exact degree_eq ⟨continuous_constant c, fun _ _ _ => hc, rfl⟩ (L := fun _ => θ)
    ⟨continuous_constant θ, fun _ _ _ => hθ⟩ (by grind)

/-- The circles `t ↦ s · cis 2πt` (`s` clamped to `[0, 1]`) sweep out the disc. -/
noncomputable def radial (s t : R) : Disc :=
  ⟨C.ofReal (clamp01 s) * C.cis (2 * pi * t), by
    rw [C.cabs_mul, C.cabs_ofReal (clamp01_mem s).1, cabs_cis]; have := clamp01_mem s; grind⟩

/-- The radial family is jointly continuous. -/
theorem cont2_radial : Cont2 radial :=
  Cont2.subtype_mk ((continuous_ofReal.comp continuous_clamp01).cont2_left.cmul
    continuous_cis_two_pi.cont2_right) _

/-- **Disc maps have boundary degree zero.** The boundary loop of a map of the disc into the
circle has degree `0`: it contracts
through the images of the concentric circles. -/
theorem degree_boundary_eq_zero {G : Disc → C} (hG : Continuous G)
    (hunit : ∀ z, normSq (G z) = 1) : degree (fun t => G (bd t)) = 0 := by
  have hH : Cont2 (fun s t => G (radial s t)) := cont2_radial.comp_left hG
  have hloop : ∀ s, G (radial s 1) = G (radial s 0) := fun s => by
    congr 1; apply Subtype.ext
    show C.ofReal (clamp01 s) * C.cis (2 * pi * 1) = C.ofReal (clamp01 s) * C.cis (2 * pi * 0)
    have e : C.cis (2 * pi * 1) = C.cis (2 * pi * 0) := congrArg Subtype.val bd_one
    rw [e]
  have key := degree_homotopy hH (fun _ _ _ _ _ _ => hunit _) (fun s _ _ => hloop s)
  have h0 : (fun t => G (radial 0 t)) = fun _ => G (radial 0 0) := funext fun t => by
    congr 1; apply Subtype.ext
    show C.ofReal (clamp01 0) * _ = C.ofReal (clamp01 0) * _
    rw [clamp01_of_mem (Std.le_refl 0) (by grind)]
    apply C.ext <;> simp only [C.mul_re, C.mul_im] <;> unfold C.ofReal <;> simp only <;> grind
  have h1 : (fun t => G (radial 1 t)) = fun t => G (bd t) := funext fun t => by
    congr 1; apply Subtype.ext
    show C.ofReal (clamp01 1) * C.cis (2 * pi * t) = C.cis (2 * pi * t)
    rw [clamp01_of_mem (by grind) (Std.le_refl 1)]
    apply C.ext <;> simp only [C.mul_re, C.mul_im] <;> unfold C.ofReal <;> simp only <;> grind
  (try simp only at key)
  rw [← h1, ← key, h0, degree_const (hunit _)]

/-! ## No retraction, and Brouwer's theorem -/

/-- **No-retraction theorem.** There is no continuous map `r : D² → S¹` restricting to the
identity on the boundary circle. -/
theorem no_retraction :
    ¬ ∃ r : Disc → S1, Continuous r ∧ ∀ z : Disc, cabs z.1 = 1 → (r z).1 = z.1 := by
  intro ⟨r, hr, hfix⟩
  have h0 := degree_boundary_eq_zero (G := fun z => (r z).1) ((continuous_val _).comp hr)
    (fun z => S1.normSq_val _)
  have e : (fun t => (r (bd t)).1) = fun t => C.cis (2 * pi * t) :=
    funext fun t => hfix (bd t) (cabs_cis _)
  (try simp only at h0)
  rw [e, degree_cis_two_pi] at h0
  exact absurd h0 (by decide)

/-- If a boundary point `e` equals `u · w` with `u ∈ [0, 1]` and `|w| ≤ 1`, then `u = 1` and
`w = e`. -/
theorem eq_of_boundary_eq_mul {e w : C} {u : R} (he : cabs e = 1) (hw : cabs w ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (h : e - C.ofReal u * w = 0) : u = 1 ∧ w = e := by
  have e1 : e = C.ofReal u * w := by grind
  have e2 := congrArg cabs e1
  rw [he, C.cabs_mul, C.cabs_ofReal hu0] at e2
  have := OrderedRing.mul_le_mul_of_nonneg_left hw hu0
  have hu : u = 1 := by grind
  refine ⟨hu, ?_⟩
  rw [e1, hu]; apply C.ext <;> simp only [C.mul_re, C.mul_im] <;> unfold C.ofReal <;> simp only <;>
    grind

/-- **Brouwer's fixed-point theorem in dimension 2.** Every continuous map of the closed disc
into itself has a fixed point. -/
theorem brouwer_disc (f : Disc → Disc) (hf : Continuous f) : ∃ z, f z = z := by
  apply Classical.byContradiction; intro hno
  have hne : ∀ z : Disc, z.1 - (f z).1 ≠ 0 := fun z h =>
    hno ⟨z, Subtype.ext (by grind)⟩
  have hfv : Continuous (fun z : Disc => (f z).1) := (continuous_val _).comp hf
  have hd : Continuous (fun z : Disc => z.1 - (f z).1) :=
    (((continuous_val _).cont2_left (B := R)).csub hfv.cont2_left).slice' 0
  -- The boundary loop of `z ↦ (z − f z)/|z − f z|` has degree `0` …
  have h0 := degree_boundary_eq_zero (G := fun z => nrm (z.1 - (f z).1))
    (hd.comp_at fun z => continuousAt_nrm (hne z)) (fun z => normSq_nrm (hne z))
  -- … but it is homotopic to `t ↦ cis 2πt`, of degree `1`.
  have knz : ∀ u t, (bd t).1 - C.ofReal (clamp01 u) * (f (bd t)).1 ≠ 0 := fun u t h => by
    have := clamp01_mem u
    obtain ⟨-, hw⟩ := eq_of_boundary_eq_mul (cabs_cis _) (f (bd t)).2 this.1 this.2 h
    exact hno ⟨bd t, Subtype.ext hw⟩
  have hin : Cont2 (fun u t => (bd t).1 - C.ofReal (clamp01 u) * (f (bd t)).1) :=
    continuous_cis_two_pi.cont2_right.csub ((continuous_ofReal.comp continuous_clamp01).cont2_left.cmul
      (hfv.comp continuous_bd).cont2_right)
  have hK := hin.comp_left' fun u t => continuousAt_nrm (knz u t)
  have key := degree_homotopy hK (fun u t _ _ _ _ => normSq_nrm (knz u t))
    (fun u _ _ => by (try simp only); rw [bd_one])
  have k0 : (fun t => nrm ((bd t).1 - C.ofReal (clamp01 0) * (f (bd t)).1)) =
      fun t => C.cis (2 * pi * t) := funext fun t => by
    rw [clamp01_of_mem (Std.le_refl 0) (by grind)]
    rw [show (bd t).1 - C.ofReal 0 * (f (bd t)).1 = (bd t).1 by
      apply C.ext <;> simp only [sub_re', sub_im', C.mul_re, C.mul_im] <;> unfold C.ofReal <;>
        simp only <;> grind]
    exact nrm_of_unit (normSq_cis _)
  have k1 : (fun t => nrm ((bd t).1 - C.ofReal (clamp01 1) * (f (bd t)).1)) =
      fun t => nrm ((bd t).1 - (f (bd t)).1) := funext fun t => by
    rw [clamp01_of_mem (by grind) (Std.le_refl 1)]
    congr 2; apply C.ext <;> simp only [C.mul_re, C.mul_im] <;> unfold C.ofReal <;> simp only <;>
      grind
  (try simp only at key h0)
  rw [k0, k1, degree_cis_two_pi, h0] at key
  exact absurd key (by decide)

/-- **Maps of non-zero degree are surjective.** A loop in the circle of non-zero degree passes
through every point of the circle. -/
theorem surjective_of_degree_ne_zero {γ : R → C} (hγ : IsCircleLoop γ) (hd : degree γ ≠ 0)
    {z : C} (hz : normSq z = 1) : ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ γ t = z := by
  apply Classical.byContradiction; intro hno
  have hcz := (cabs_eq_one_iff z).2 hz
  -- The segment from `γ t` to `−z` avoids `0`.
  have knz : ∀ s t, C.ofReal (1 - clamp01 s) * γ (clamp01 t) - C.ofReal (clamp01 s) * z ≠ 0 := by
    intro s t h
    have ms := clamp01_mem s; have mt := clamp01_mem t
    have hg := (cabs_eq_one_iff _).2 (hγ.2.1 _ mt.1 mt.2)
    have e1 : C.ofReal (1 - clamp01 s) * γ (clamp01 t) = C.ofReal (clamp01 s) * z := by grind
    have e2 := congrArg cabs e1
    rw [C.cabs_mul, C.cabs_mul, C.cabs_ofReal (by grind), C.cabs_ofReal ms.1, hg, hcz] at e2
    have hs : clamp01 s = 1 / 2 := by grind
    rw [hs, show (1 : R) - 1 / 2 = 1 / 2 by grind] at e1
    have : γ (clamp01 t) = z := by
      have e3 := congrArg (fun w => C.ofReal 2 * w) e1
      (try simp only at e3)
      have l : ∀ w : C, C.ofReal 2 * (C.ofReal (1 / 2) * w) = w := fun w => by
        apply C.ext <;> simp only [C.mul_re, C.mul_im] <;> unfold C.ofReal <;> simp only <;> grind
      rwa [l, l] at e3
    exact hno ⟨clamp01 t, mt.1, mt.2, this⟩
  have hin : Cont2 (fun s t => C.ofReal (1 - clamp01 s) * γ (clamp01 t) - C.ofReal (clamp01 s) * z) :=
    ((continuous_ofReal.comp (continuous_one_sub.comp continuous_clamp01)).cont2_left.cmul
      (hγ.1.comp continuous_clamp01).cont2_right).csub
      ((continuous_ofReal.comp continuous_clamp01).cont2_left.cmul (cont2_const z))
  have hK := hin.comp_left' fun s t => continuousAt_nrm (knz s t)
  have key := degree_homotopy hK (fun s t _ _ _ _ => normSq_nrm (knz s t)) (fun s _ _ => by
    (try simp only); rw [clamp01_of_mem (by grind) (Std.le_refl 1), clamp01_of_mem (Std.le_refl 0)
      (by grind), hγ.2.2])
  have k0 : degree (fun t => nrm (C.ofReal (1 - clamp01 0) * γ (clamp01 t) -
      C.ofReal (clamp01 0) * z)) = degree γ := by
    apply degree_congr ⟨hK.slice 0, fun t _ _ => normSq_nrm (knz 0 t), by
      (try simp only); rw [clamp01_of_mem (by grind) (Std.le_refl 1), clamp01_of_mem (Std.le_refl 0)
        (by grind), hγ.2.2]⟩ hγ
    intro t t0 t1
    rw [clamp01_of_mem (Std.le_refl 0) (by grind), clamp01_of_mem t0 t1]
    rw [show C.ofReal (1 - 0) * γ t - C.ofReal 0 * z = γ t by
      apply C.ext <;> simp only [sub_re', sub_im', C.mul_re, C.mul_im] <;> unfold C.ofReal <;>
        simp only <;> grind]
    exact nrm_of_unit (hγ.2.1 t t0 t1)
  have k1 : (fun t => nrm (C.ofReal (1 - clamp01 1) * γ (clamp01 t) - C.ofReal (clamp01 1) * z)) =
      fun _ => nrm (C.ofReal (1 - clamp01 1) * γ (clamp01 0) - C.ofReal (clamp01 1) * z) :=
    funext fun t => by
      rw [clamp01_of_mem (by grind) (Std.le_refl 1)]
      congr 1; apply C.ext <;> simp only [sub_re', sub_im', C.mul_re, C.mul_im] <;>
        unfold C.ofReal <;> simp only <;> grind
  (try simp only at key)
  rw [k0, k1, degree_const (normSq_nrm (knz 1 0))] at key
  exact hd key

end Foundations.Topology
