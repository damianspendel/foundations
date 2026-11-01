import Foundations.Topology.FundamentalGroup
import Foundations.Topology.Basel

/-!
# The circle and the local inverse of the exponential map

The circle `S¹ = {z ∈ ℂ : |z| = 1}` is wrapped around by the real line through the **exponential
map** `p(θ) = cis θ = cos θ + i sin θ`. This file collects what the lifting theory of the next file
needs about `p`, about continuity in the plane, and about uniform continuity.

* **Continuity in `ℂ`**: a sequence converges iff its real and imaginary parts do; hence complex
  multiplication, subtraction, conjugation and `cis` are continuous (jointly, where there are two
  variables).
* **The kernel of `p`**: `cis x = 1` exactly when `x ∈ 2πℤ`, so `p(a) = p(b)` iff `a − b ∈ 2πℤ`.
  Every point of the circle is `p(θ)` for some `θ`.
* **The local inverse of `p`.** On the right half of the circle the angle
  `ang w = π/2 − arccos (Im w)` is the unique angle in `[−π/2, π/2]` with `cis (ang w) = w`. It is
  **Lipschitz**: by **Jordan's inequality** (from `Basel`), a chord of the circle is at least `2/π`
  times the arc it subtends, so `|ang w − ang w'| ≤ (π/2) |w − w'|`. Two points of the circle less
  than `1` apart have their quotient `z' z̄` in the right half — the domain of `ang`.
* **Uniform continuity on the square** `[0, 1]²` for jointly continuous families — the
  Lebesgue-number lemma in the form needed for lifting, proved with Bolzano–Weierstrass.

Geometrically: over every arc shorter than a half-circle, `p` is a stack of disjoint copies of the
arc, each mapped homeomorphically — `p` is a **covering map**, and `ang` (shifted by multiples of
`2π`) gives the sheets.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind
open Foundations.Numbers.C (cabs normSq conj cis)
open Wallis (hpi hpi_pos)

variable {A B X : Type} [MetricSpace A] [MetricSpace B] [MetricSpace X]

/-! ## Continuity in the complex plane -/

/-- The distance of `ℂ` is the modulus of the difference. -/
theorem dist_C (z w : C) : dist z w = cabs (z - w) := rfl

/-- Real part of a difference. -/
theorem sub_re' (z w : C) : (z - w).re = z.re - w.re := by show z.re + -w.re = _; grind

/-- Imaginary part of a difference. -/
theorem sub_im' (z w : C) : (z - w).im = z.im - w.im := by show z.im + -w.im = _; grind

/-- A sequence of complex numbers converges exactly when its real and imaginary parts do. -/
theorem converges_C_iff (s : Nat → C) (z : C) :
    Converges s z ↔ Tendsto (fun n => (s n).re) z.re ∧ Tendsto (fun n => (s n).im) z.im := by
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      have := C.abs_re_le_cabs (s n - z); rw [sub_re'] at this
      have := hN n hn; rw [dist_C] at this; grind
    · obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      have := C.abs_im_le_cabs (s n - z); rw [sub_im'] at this
      have := hN n hn; rw [dist_C] at this; grind
  · intro ⟨h1, h2⟩ ε hε
    obtain ⟨N₁, k1⟩ := h1 (ε / 2) (by grind)
    obtain ⟨N₂, k2⟩ := h2 (ε / 2) (by grind)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have := C.cabs_le_nrm (s n - z)
    have a := k1 n (by omega); have b := k2 n (by omega)
    rw [dist_C]; unfold C.nrm at this; rw [sub_re', sub_im'] at this; grind

/-- Jointly continuous real and imaginary parts assemble to a jointly continuous complex
function. -/
theorem Cont2.mkC {F G : A → B → R} (hF : Cont2 F) (hG : Cont2 G) :
    Cont2 (fun a b => (⟨F a b, G a b⟩ : C)) :=
  cont2_of_seq fun _ _ _ _ ha hb => (converges_C_iff _ _).2 ⟨hF.seq ha hb, hG.seq ha hb⟩

/-- Joint continuity is a property of the function, not of its expression. -/
theorem Cont2.congr {H H' : A → B → X} (hH : Cont2 H) (h : ∀ a b, H a b = H' a b) :
    Cont2 H' := by
  have : H = H' := funext fun a => funext fun b => h a b
  exact this ▸ hH

/-- Complex multiplication is jointly continuous. -/
theorem cont2_cmul : Cont2 (fun z w : C => z * w) :=
  cont2_of_seq fun _ _ _ _ ha hb => (converges_C_iff _ _).2
    (C.CTendsto.mul ((converges_C_iff _ _).1 ha) ((converges_C_iff _ _).1 hb))

/-- The real part is continuous. -/
theorem continuous_re : Continuous (fun z : C => z.re) :=
  continuous_of_lipschitz (K := 1) (by grind) fun z w => by
    rw [dist_R, dist_C]; have := C.abs_re_le_cabs (z - w); rw [sub_re'] at this; grind

/-- The imaginary part is continuous. -/
theorem continuous_im : Continuous (fun z : C => z.im) :=
  continuous_of_lipschitz (K := 1) (by grind) fun z w => by
    rw [dist_R, dist_C]; have := C.abs_im_le_cabs (z - w); rw [sub_im'] at this; grind

/-- Complex subtraction is jointly continuous. -/
theorem cont2_csub : Cont2 (fun z w : C => z - w) :=
  (Cont2.mkC (continuous_re.cont2_left.sub continuous_re.cont2_right)
    (continuous_im.cont2_left.sub continuous_im.cont2_right)).congr fun z w =>
    C.ext (sub_re' z w).symm (sub_im' z w).symm

/-- Products of jointly continuous complex functions. -/
theorem Cont2.cmul {F G : A → B → C} (hF : Cont2 F) (hG : Cont2 G) :
    Cont2 (fun a b => F a b * G a b) := cont2_cmul.comp2 hF hG

/-- Differences of jointly continuous complex functions. -/
theorem Cont2.csub {F G : A → B → C} (hF : Cont2 F) (hG : Cont2 G) :
    Cont2 (fun a b => F a b - G a b) := cont2_csub.comp2 hF hG

/-- Complex conjugation is continuous (an isometry). -/
theorem continuous_conj : Continuous (fun z : C => conj z) :=
  continuous_of_lipschitz (K := 1) (by grind) fun z w => by
    rw [dist_C, dist_C]
    have : cabs (conj z - conj w) = cabs (z - w) := by
      unfold C.cabs normSq; congr 1; rw [sub_re', sub_im', sub_re', sub_im']
      simp only [C.conj_re, C.conj_im]; grind
    grind

/-- The real part of `cis θ` is `cos θ`. -/
theorem cis_re (θ : R) : (cis θ).re = cos θ := rfl

/-- The imaginary part of `cis θ` is `sin θ`. -/
theorem cis_im (θ : R) : (cis θ).im = sin θ := rfl

/-- The exponential map `θ ↦ cis θ` is continuous. -/
theorem continuous_cis : Continuous cis := fun x => by
  refine (continuousAt_iff_seq cis x).2 fun s hs => (converges_C_iff _ _).2 ⟨?_, ?_⟩
  · simp only [cis_re]; exact tendsto_comp (continuousAt_cos x) hs
  · simp only [cis_im]; exact tendsto_comp (hasDerivAt_sin x).continuousAt hs

/-- Sums of continuous real functions are continuous. -/
theorem Continuous.add' {f g : R → R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => f t + g t) :=
  ((hf.cont2_left (B := R)).add hg.cont2_left).slice' 0

/-- A finite sum of jointly continuous functions is jointly continuous. -/
theorem Cont2.fsum {F : Nat → A → B → R} {n : Nat} (h : ∀ k, k < n → Cont2 (F k)) :
    Cont2 (fun a b => fsum (fun k => F k a b) n) := by
  induction n with
  | zero => exact cont2_const 0
  | succ n ih => exact (ih fun k hk => h k (by omega)).add (h n (by omega))

/-- A sum of zeros is zero. -/
theorem fsum_eq_zero {f : Nat → R} {n : Nat} (h : ∀ k, k < n → f k = 0) : fsum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => show fsum f n + f n = 0; rw [ih fun k hk => h k (by omega), h n (by omega)]; grind

/-! ## The circle and the exponential map -/

/-- **Unit circle.** `S¹ = {z ∈ ℂ : |z| = 1}`, a metric space with the distance of `ℂ`. -/
abbrev S1 : Type := {z : C // cabs z = 1}

/-- `|z| = 1` exactly when `|z|² = 1`. -/
theorem cabs_eq_one_iff (z : C) : cabs z = 1 ↔ normSq z = 1 := by
  constructor
  · intro h; rw [← C.cabs_mul_self, h]; grind
  · intro h; unfold C.cabs; rw [h]; exact sqrt_eq (by grind) (by grind)

/-- The base point `1` of the circle. -/
def S1.one : S1 := ⟨1, (cabs_eq_one_iff 1).2 (by unfold normSq; simp only [C.one_re, C.one_im]; grind)⟩

/-- `cis θ` lies on the unit circle. -/
theorem normSq_cis (θ : R) : normSq (cis θ) = 1 := by
  unfold normSq; show cos θ * cos θ + sin θ * sin θ = 1; have := sin_sq_add_cos_sq θ; grind

/-- `cis 0 = 1`. -/
theorem cis_zero : cis 0 = 1 :=
  C.ext (by show cos 0 = 1; exact cos_zero) (by show sin 0 = 0; exact sin_zero)

/-- `z · z̄ = 1` on the unit circle. -/
theorem mul_conj_eq_one {z : C} (h : normSq z = 1) : z * conj z = 1 := by
  rw [C.mul_conj, h]; rfl

/-- Dividing by a point of the circle is multiplying by its conjugate: `z' z̄ z = z'`. -/
theorem mul_conj_mul {z : C} (h : normSq z = 1) (z' : C) : z' * conj z * z = z' := by
  unfold normSq at h
  apply C.ext <;> simp only [C.mul_re, C.mul_im, C.conj_re, C.conj_im] <;> grind

/-- If `cis a = cis b` then `cis (a − b) = 1`. -/
theorem cis_sub_eq_one {a b : R} (h : cis a = cis b) : cis (a - b) = 1 := by
  have e := C.cis_add (a - b) b
  rw [show a - b + b = a by grind, h] at e
  calc cis (a - b) = cis (a - b) * (cis b * conj (cis b)) := by
        rw [mul_conj_eq_one (normSq_cis b), C.mul_one]
    _ = cis (a - b) * cis b * conj (cis b) := by rw [C.mul_assoc]
    _ = 1 := by rw [e, mul_conj_eq_one (normSq_cis b)]

/-- The half-angle formula `cos x = 1 − 2 sin²(x/2)`. -/
theorem cos_eq_one_sub_sin_half (x : R) : cos x = 1 - 2 * (sin (x / 2) * sin (x / 2)) := by
  have h := cos_add (x / 2) (x / 2)
  rw [show x / 2 + x / 2 = x by grind] at h
  have := sin_sq_add_cos_sq (x / 2); grind

/-- **Kernel of the exponential map.** `cis x = 1` exactly when `x ∈ 2πℤ`. -/
theorem cis_eq_one_iff (x : R) : cis x = 1 ↔ ∃ k : Int, x = 2 * pi * (k : R) := by
  constructor
  · intro h
    have hc : cos x = 1 := congrArg C.re h
    have hs : sin (x / 2) = 0 := by
      have := cos_eq_one_sub_sin_half x
      exact (eq_zero_of_sq_add_sq (b := 0) (by grind)).1
    obtain ⟨k, hk⟩ := (sin_eq_zero_iff _).1 hs
    exact ⟨k, by grind⟩
  · intro ⟨k, hk⟩
    have hs : sin (x / 2) = 0 := (sin_eq_zero_iff _).2 ⟨k, by rw [hk]; grind⟩
    apply C.ext
    · show cos x = 1; rw [cos_eq_one_sub_sin_half, hs]; grind
    · show sin x = 0
      have := sin_add (x / 2) (x / 2); rw [show x / 2 + x / 2 = x by grind, hs] at this; grind

/-- `cis (2πk) = 1` for integers `k`. -/
theorem cis_two_pi_int (k : Int) : cis (2 * pi * (k : R)) = 1 := (cis_eq_one_iff _).2 ⟨k, rfl⟩

/-- Every point of the circle is `cis θ` for some angle `θ`. -/
theorem exists_cis_eq {z : C} (h : normSq z = 1) : ∃ θ, cis θ = z := by
  obtain ⟨θ, hc, hs⟩ := exists_angle (x := z.re) (y := z.im) h
  exact ⟨θ, C.ext hc hs⟩

/-- The integer cast into `ℝ` is injective. -/
theorem intCast_inj {m n : Int} (h : (m : R) = (n : R)) : m = n := by
  rcases Int.lt_trichotomy m n with e | e | e
  · have := (intCast_lt (K := R)).2 e; grind
  · exact e
  · have := (intCast_lt (K := R)).2 e; grind

/-- `2πk = 2πa + π` has no integer solutions: `π` is not a multiple of `2π`. -/
theorem two_pi_int_ne_odd (k a : Int) : 2 * pi * (k : R) ≠ 2 * pi * (a : R) + pi := by
  intro h
  have hp := pi_pos
  have hpi : pi * pi⁻¹ = 1 := R.mul_inv_cancel (by grind)
  have e : (2 : R) * (k : R) - 2 * (a : R) - 1 = 0 := by
    have : pi * (2 * (k : R) - 2 * (a : R) - 1) = 0 := by grind
    calc (2 : R) * (k : R) - 2 * (a : R) - 1
        = pi⁻¹ * (pi * (2 * (k : R) - 2 * (a : R) - 1)) := by grind
      _ = 0 := by rw [this]; grind
  have : ((2 * k - 2 * a - 1 : Int) : R) = ((0 : Int) : R) := by grind
  have := intCast_inj this; omega

/-! ## The local inverse of the exponential map -/

/-- **Angle function.** On the right half-plane, `ang w = π/2 − arccos (Im w)`, the angle in
`[−π/2, π/2]` whose sine is `Im w`. -/
noncomputable def ang (w : C) : R := pi / 2 - arccos w.im

/-- On the right half of the unit circle, `ang` inverts the exponential map:
`cis (ang w) = w`, with `ang w ∈ [−π/2, π/2]`. -/
theorem ang_spec {w : C} (hw : normSq w = 1) (hre : 0 < w.re) :
    cis (ang w) = w ∧ -(pi / 2) ≤ ang w ∧ ang w ≤ pi / 2 := by
  have him : -1 ≤ w.im ∧ w.im ≤ 1 :=
    abs_le_one_of_sq (by unfold normSq at hw; have := C.mul_self_nonneg w.re; grind)
  obtain ⟨a0, a1, a2⟩ := arccos_spec him.1 him.2
  have e : ang w = -arccos w.im + pi / 2 := by unfold ang; grind
  have hs : sin (ang w) = w.im := by rw [e, sin_add_pi_div_two, cos_neg, a2]
  have hc0 : cos (ang w) = sin (arccos w.im) := by rw [e, cos_add_pi_div_two, sin_neg]; grind
  have hsa : 0 ≤ sin (arccos w.im) := sin_nonneg_of_mem a0 a1
  have hc : cos (ang w) = w.re := by
    apply eq_of_mul_self_eq (hc0 ▸ hsa) (Std.le_of_lt hre)
    have := sin_sq_add_cos_sq (ang w); rw [hs] at this; unfold normSq at hw; grind
  exact ⟨C.ext hc hs, by rw [e]; grind, by rw [e]; grind⟩

/-- `ang 1 = 0`. -/
theorem ang_one : ang 1 = 0 := by
  have hp := pi_pos
  have := arccos_cos (θ := pi / 2) (by grind) (by grind)
  rw [cos_pi_div_two] at this
  unfold ang; rw [C.one_im, this]; grind

/-- **Chords and arcs.** For `|a − b| ≤ π`, `|a − b| ≤ (π/2) |cis a − cis b|`: by Jordan's
inequality the chord is at least `2/π` times the arc. -/
theorem chord_bound {a b : R} (h : abs (a - b) ≤ pi) :
    abs (a - b) ≤ hpi * cabs (cis a - cis b) := by
  have hp := pi_pos
  have hn : normSq (cis a - cis b) = 4 * (sin ((a - b) / 2) * sin ((a - b) / 2)) := by
    unfold normSq; rw [sub_re', sub_im']
    show (cos a - cos b) * (cos a - cos b) + (sin a - sin b) * (sin a - sin b) = _
    have h1 := cos_add a (-b); rw [cos_neg, sin_neg, show a + -b = a - b by grind] at h1
    have h2 := cos_eq_one_sub_sin_half (a - b)
    have := sin_sq_add_cos_sq a; have := sin_sq_add_cos_sq b
    grind
  have hc : cabs (cis a - cis b) = 2 * abs (sin ((a - b) / 2)) := by
    unfold C.cabs; rw [hn]
    exact sqrt_eq (by have := abs_nonneg (sin ((a - b) / 2)); grind)
      (by rcases abs_cases (sin ((a - b) / 2)) with e | e <;> grind)
  rw [hc]
  have hh : hpi = pi / 2 := rfl
  have hj : abs ((a - b) / 2) ≤ hpi * abs (sin ((a - b) / 2)) := by
    have la := le_abs (sin ((a - b) / 2))
    have hpos := hpi_pos
    rcases abs_cases ((a - b) / 2) with e | e
    · have k := Wallis.jordan e.1 (by have := abs_le.1 h; grind)
      have := OrderedRing.mul_le_mul_of_nonneg_left la.1 (Std.le_of_lt hpos); grind
    · have k := Wallis.jordan (x := -((a - b) / 2)) (by grind) (by have := abs_le.1 h; grind)
      rw [sin_neg] at k
      have := OrderedRing.mul_le_mul_of_nonneg_left la.2 (Std.le_of_lt hpos); grind
  have : abs (a - b) = 2 * abs ((a - b) / 2) := by
    rcases abs_cases (a - b) with e | e <;> rcases abs_cases ((a - b) / 2) with e' | e' <;> grind
  grind

/-- **Lipschitz bound for `ang`.** On the right half of the circle, with constant `π/2`. -/
theorem ang_lipschitz {w w' : C} (hw : normSq w = 1) (hre : 0 < w.re) (hw' : normSq w' = 1)
    (hre' : 0 < w'.re) : abs (ang w - ang w') ≤ hpi * cabs (w - w') := by
  obtain ⟨c1, l1, u1⟩ := ang_spec hw hre
  obtain ⟨c2, l2, u2⟩ := ang_spec hw' hre'
  have := chord_bound (a := ang w) (b := ang w') (abs_le.2 ⟨by grind, by grind⟩)
  rwa [c1, c2] at this

/-- Two points of the circle at distance `< 1` have quotient `z' z̄` in the right half-plane. -/
theorem quotient_right {z z' : C} (hz : normSq z = 1) (hz' : normSq z' = 1)
    (h : cabs (z' - z) < 1) : normSq (z' * conj z) = 1 ∧ 0 < (z' * conj z).re := by
  have hlt : normSq (z' - z) < 1 := by
    rw [← C.cabs_mul_self]; have := mul_self_lt_mul_self (C.cabs_nonneg _) h; grind
  have hnc : normSq (conj z) = 1 := by unfold normSq at *; simp only [C.conj_re, C.conj_im]; grind
  refine ⟨by rw [C.normSq_mul, hz', hnc]; grind, ?_⟩
  unfold normSq at hlt hz hz'; rw [sub_re', sub_im'] at hlt
  simp only [C.mul_re, C.conj_re, C.conj_im]; grind

/-- **Continuity of `ang`.** `ang` preserves joint continuity for functions with values in the right half of the
circle. -/
theorem Cont2.ang {w : A → B → C} (hw : Cont2 w)
    (hdom : ∀ a b, normSq (w a b) = 1 ∧ 0 < (w a b).re) : Cont2 (fun a b => ang (w a b)) := by
  intro a b ε hε
  have hp := hpi_pos
  have hq : 0 < ε / (hpi + 1) := div_pos hε (by grind)
  obtain ⟨δ, hδ, h⟩ := hw a b (ε / (hpi + 1)) hq
  refine ⟨δ, hδ, fun a' b' ha hb => ?_⟩
  have k := h a' b' ha hb
  rw [dist_C] at k; rw [dist_R]
  have l := ang_lipschitz (hdom a' b').1 (hdom a' b').2 (hdom a b).1 (hdom a b).2
  have e : (hpi + 1) * (ε / (hpi + 1)) = ε := by grind
  have := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt k) (Std.le_of_lt hp)
  grind

/-! ## Uniform continuity on the square -/

/-- **Uniform continuity on the square.** (A Lebesgue-number lemma for `[0, 1]²`.) For jointly
continuous `H` and `ε > 0` there is `δ > 0` such that `H(s, u)` and `H(s, v)` are `ε`-close
whenever `s, u, v ∈ [0, 1]` and `|u − v| < δ`. -/
theorem uniform_square {H : R → R → X} (hH : Cont2 H) {ε : R} (hε : 0 < ε) :
    ∃ δ : R, 0 < δ ∧ ∀ s u v, 0 ≤ s → s ≤ 1 → 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
      abs (u - v) < δ → dist (H s u) (H s v) < ε := by
  apply Classical.byContradiction; intro hno
  have hx : ∀ n : Nat, ∃ p : R × R × R, (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2.1 ∧ p.2.1 ≤ 1) ∧
      abs (p.2.1 - p.2.2) < 1 / ((n : R) + 1) ∧ ε ≤ dist (H p.1 p.2.1) (H p.1 p.2.2) := by
    intro n
    apply Classical.byContradiction; intro h'
    exact hno ⟨1 / ((n : R) + 1), eps_pos n, fun s u v h1 h2 h3 h4 _ _ h7 => by
      apply Classical.byContradiction; intro h8
      exact h' ⟨(s, u, v), ⟨h1, h2⟩, ⟨h3, h4⟩, h7, by grind⟩⟩
  let p : Nat → R × R × R := fun n => (hx n).choose
  have hp : ∀ n, _ := fun n => (hx n).choose_spec
  obtain ⟨φ, hφ, s0, hs⟩ := bolzano_weierstrass (a := fun n => (p n).1)
    ⟨1, fun n => abs_le.2 ⟨by have := (hp n).1; grind, (hp n).1.2⟩⟩
  obtain ⟨ψ, hψ, u0, hu⟩ := bolzano_weierstrass (a := fun k => (p (φ k)).2.1)
    ⟨1, fun k => abs_le.2 ⟨by have := (hp (φ k)).2.1; grind, (hp (φ k)).2.1.2⟩⟩
  let χ : Nat → Nat := fun k => φ (ψ k)
  have hχ : ∀ k, χ k < χ (k + 1) := fun k => C.strictMono_lt hφ (hψ k)
  have hs' : Converges (fun k => (p (χ k)).1) s0 := C.tendsto_subseq hs hψ
  have hu' : Converges (fun k => (p (χ k)).2.1) u0 := hu
  have hv' : Converges (fun k => (p (χ k)).2.2) u0 := by
    intro e he
    obtain ⟨N₁, k1⟩ := hu (e / 2) (by grind)
    obtain ⟨N₂, k2⟩ := eps_small (by grind : (0 : R) < e / 2)
    refine ⟨max N₁ N₂, fun k hk => ?_⟩
    have a1 := k1 k (by omega)
    have a2 := k2 (χ k) (by have := le_of_strictMono hχ k; omega)
    have a3 := (hp (χ k)).2.2.1
    rw [dist_R]
    have := abs_add ((p (χ k)).2.2 - (p (χ k)).2.1) ((p (χ k)).2.1 - u0)
    rw [abs_sub_comm ((p (χ k)).2.2)] at this
    simp only at a1; grind
  obtain ⟨N₁, k1⟩ := hH.seq hs' hu' (ε / 2) (by grind)
  obtain ⟨N₂, k2⟩ := hH.seq hs' hv' (ε / 2) (by grind)
  have a1 := k1 (max N₁ N₂) (by omega)
  have a2 := k2 (max N₁ N₂) (by omega)
  have a3 := (hp (χ (max N₁ N₂))).2.2.2
  have := dist_triangle (H (p (χ (max N₁ N₂))).1 (p (χ (max N₁ N₂))).2.1) (H s0 u0)
    (H (p (χ (max N₁ N₂))).1 (p (χ (max N₁ N₂))).2.2)
  have := dist_comm (H s0 u0) (H (p (χ (max N₁ N₂))).1 (p (χ (max N₁ N₂))).2.2)
  simp only at a1 a2; grind

end Foundations.Topology
