import Foundations.Topology.DominatedConvergence

/-!
# The Lebesgue integral extends the Riemann integral

Lebesgue's integral was meant to *extend* Riemann's, not to replace it: on the functions that
Riemann could already integrate, the two must agree. We prove this for the functions that matter
most in Part II, the continuous ones:

  **If `f` is continuous on `[a, b]`, then `f` (extended by `0` outside `[a, b]`) is Lebesgue
  integrable for `λ_{a,b}` and its Lebesgue integral equals its Riemann integral.**

The proof compares both integrals with a **step function**. By uniform continuity (Heine–Cantor),
on a fine uniform partition `a = x₀ < x₁ < ⋯ < x_N = b` the function `f` differs from its value
at the left end point by less than `ε` on each piece `[xᵢ, xᵢ₊₁)`. The step function
`s = Σ f(xᵢ) · 1_{[xᵢ, xᵢ₊₁)}` has Lebesgue integral `Σ f(xᵢ)(xᵢ₊₁ − xᵢ)` — because Lebesgue
measure gives intervals their length — which is exactly a Riemann sum. So both integrals lie
within `ε (b − a + 1)` of the same number.

Along the way: integrals of indicator functions and of step functions, half-open intervals, and
the measurability of continuous functions (the set `{c < f}` is a countable union of intervals
with rational end points).
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind Outer

namespace MeasureTheory

/-! ## Indicator and step functions -/

section steps

variable {α : Type} {S : SigmaAlgebra α} (m : Measure S)

/-- The **indicator function** `1_A`. -/
noncomputable def ind (A : α → Prop) (x : α) : R := open Classical in if A x then 1 else 0

/-- `1_A = 1` on `A`. -/
theorem ind_pos {A : α → Prop} {x : α} (h : A x) : ind A x = 1 := by unfold ind; simp [h]

/-- `1_A = 0` off `A`. -/
theorem ind_neg {A : α → Prop} {x : α} (h : ¬ A x) : ind A x = 0 := by unfold ind; simp [h]

/-- **Integral of an indicator.** `∫ 1_A dμ = μ(A)`. -/
theorem lintegral_ind {A : α → Prop} (hA : S.M A) :
    LIntegrable m (ind A) ∧ lintegral m (ind A) = m.μ A := by
  have h0 : ∀ x, 0 ≤ ind A x := fun x => by unfold ind; split <;> grind
  have hmeas : Measurable S (ind A) := fun c => by
    by_cases hc : c < 0
    · exact S.congr S.univ fun x => ⟨fun _ => by have := h0 x; grind, fun _ => trivial⟩
    · by_cases hc1 : c < 1
      · exact S.congr hA fun x => by unfold ind; split <;> grind
      · exact S.congr S.empty fun x => by unfold ind; split <;> grind
  have key : ∀ l, IsSimple S l → Below l (ind A) → sint m l ≤ m.μ A := fun l hl hb => by
    have h1 : sint m l ≤ lsum (fun p => m.μ (fun x => A x ∧ p.2 x)) l := lsum_le fun p hp => by
      have hμ := m.nonneg _ (hl.1 p hp).2
      by_cases hsub : ∀ x, p.2 x → A x
      · have e : m.μ (fun x => A x ∧ p.2 x) = m.μ p.2 :=
          m.congr fun x => ⟨fun h => h.2, fun h => ⟨hsub x h, h⟩⟩
        rw [e]
        by_cases hne : ∃ x, p.2 x
        · obtain ⟨x, hx⟩ := hne
          have := hb p hp x hx; rw [ind_pos (hsub x hx)] at this
          have := OrderedRing.mul_le_mul_of_nonneg_right this hμ; grind
        · have : m.μ p.2 = 0 := by
            rw [← m.empty]; exact m.congr fun x => ⟨fun h => hne ⟨x, h⟩, False.elim⟩
          rw [this]; grind
      · have : ∃ x, p.2 x ∧ ¬ A x := Classical.byContradiction fun h =>
          hsub fun x hx => Classical.byContradiction fun ha => h ⟨x, hx, ha⟩
        obtain ⟨x, hx, ha⟩ := this
        have := hb p hp x hx; rw [ind_neg ha] at this
        have e : p.1 = 0 := by have := (hl.1 p hp).1; grind
        rw [e]; have := m.nonneg _ (S.inter hA (hl.1 p hp).2); grind
    rw [lsum_measure_inter m hA (set := Prod.snd) (fun p hp => (hl.1 p hp).2) hl.2] at h1
    have := m.mono (S.inter hA (measurable_unionOf fun p hp => (hl.1 p hp).2)) hA fun x h => h.1
    grind
  refine ⟨⟨hmeas, h0, _, key⟩, Std.le_antisymm (lintegral_le m key) ?_⟩
  have := le_lintegral m ⟨_, key⟩ (l := [(1, A)])
    ⟨fun p hp => by rw [List.mem_singleton.1 hp]; exact ⟨by grind, hA⟩, List.pairwise_singleton _ _⟩
    fun p hp x hx => by rw [List.mem_singleton.1 hp] at hx ⊢; rw [ind_pos hx]; exact Std.le_refl _
  unfold sint at this; simp only [lsum] at this; grind

/-- `∫ c · 1_A = c μ(A)` for every real `c`. -/
theorem integral_ind {A : α → Prop} (hA : S.M A) (c : R) :
    Integrable m (fun x => c * ind A x) ∧ integral m (fun x => c * ind A x) = c * m.μ A := by
  have h0 : ∀ x, 0 ≤ ind A x := fun x => by unfold ind; split <;> grind
  obtain ⟨h1, e1⟩ := lintegral_ind m hA
  have hi := (integrable_iff_of_nonneg m h0).1.2 h1
  have := hi.const_mul m c
  rw [(integrable_iff_of_nonneg m h0).2, e1] at this; exact this

/-- The **step function** `Σ cᵢ · 1_{Aᵢ}` given by a list of pairs `(cᵢ, Aᵢ)`. -/
noncomputable def step (l : List (R × (α → Prop))) (x : α) : R := lsum (fun p => p.1 * ind p.2 x) l

/-- **Integral of a step function.** `∫ Σ cᵢ 1_{Aᵢ} = Σ cᵢ μ(Aᵢ)`. -/
theorem integral_step {l : List (R × (α → Prop))} (hl : ∀ p ∈ l, S.M p.2) :
    Integrable m (step l) ∧ integral m (step l) = lsum (fun p => p.1 * m.μ p.2) l := by
  induction l with
  | nil =>
    have e : step ([] : List (R × (α → Prop))) = fun _ => 0 := rfl
    rw [e]
    have h0 : ∀ _ : α, (0 : R) ≤ 0 := fun _ => Std.le_refl 0
    exact ⟨(integrable_iff_of_nonneg m h0).1.2 (lintegral_zero m).1,
      by rw [(integrable_iff_of_nonneg m h0).2, (lintegral_zero m).2]; rfl⟩
  | cons p l ih =>
    obtain ⟨h1, e1⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨h2, e2⟩ := integral_ind m (hl p List.mem_cons_self) p.1
    obtain ⟨h3, e3⟩ := h2.add m h1
    exact ⟨h3, by rw [show step (p :: l) = fun x => p.1 * ind p.2 x + step l x from rfl, e3, e2, e1]; rfl⟩

/-- On a piece of a disjoint step function, its value is the coefficient of that piece. -/
theorem step_eval {l : List (R × (α → Prop))} (hd : DisjOn Prod.snd l) {p : R × (α → Prop)}
    (hp : p ∈ l) {x : α} (hx : p.2 x) : step l x = p.1 := by
  induction l with
  | nil => exact absurd hp List.not_mem_nil
  | cons q l ih =>
    have hd' := List.pairwise_cons.1 hd
    show q.1 * ind q.2 x + step l x = p.1
    rcases List.mem_cons.1 hp with rfl | hp
    · have : step l x = 0 := step_eval_zero fun r hr hr' => hd'.1 r hr x hx hr'
      rw [ind_pos hx, this]; grind
    · have : ¬ q.2 x := fun hq => hd'.1 p hp x hq hx
      rw [ind_neg this, ih hd'.2 hp]; grind
where
  /-- Off all pieces, a step function vanishes. -/
  step_eval_zero {l : List (R × (α → Prop))} {x : α} (h : ∀ p ∈ l, ¬ p.2 x) : step l x = 0 := by
    induction l with
    | nil => rfl
    | cons q l ih =>
      show q.1 * ind q.2 x + step l x = 0
      rw [ind_neg (h q List.mem_cons_self), ih fun r hr => h r (List.mem_cons_of_mem _ hr)]; grind

end steps

/-! ## Lebesgue measure of half-open intervals and points -/

/-- `m*([t, u)) = u − t`. -/
theorem outer_Ico {t u : R} (htu : t ≤ u) : outer (fun z => t ≤ z ∧ z < u) = u - t := by
  have h := outer_interval htu
  apply Std.le_antisymm
  · have := outer_mono (coverable_of_bdd (A := fun z => t ≤ z ∧ z ≤ u) (a := t) (b := u)
      fun _ h => h) (A := fun z => t ≤ z ∧ z < u) fun z h => ⟨h.1, Std.le_of_lt h.2⟩
    grind
  · have hu := outer_union_le' (coverable_of_bdd (A := fun z => t ≤ z ∧ z < u) (a := t) (b := u)
      fun z h => ⟨h.1, Std.le_of_lt h.2⟩)
      (coverable_of_bdd (A := fun z => z = u) (a := u) (b := u) fun z h => by grind)
    have := outer_mono hu.1 (A := fun z => t ≤ z ∧ z ≤ u) fun z ⟨h1, h2⟩ => by
      rcases (by grind : z < u ∨ z = u) with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr h
    rw [outer_point] at hu
    grind

/-- Half-open intervals are measurable. -/
theorem measurable_Ico (t u : R) : LebesgueMeasurable (fun z => t ≤ z ∧ z < u) :=
  lebesgueSigma.congr (lebesgueSigma.diff (measurable_Iio u) (measurable_Iio t)) fun z => by grind

/-! ## Measurability of continuous functions -/

/-- `f` on `[a, b]`, extended by `0`. -/
noncomputable def restr (f : R → R) (a b : R) (x : R) : R :=
  open Classical in if Icc a b x then f x else 0

/-- **Continuous functions are measurable.** `{c < f} ∩ [a, b]` is a countable union of
relatively open intervals with rational end points. -/
theorem measurable_restr {f : R → R} {a b : R} (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) :
    Measurable lebesgueSigma (restr f a b) := fun c => by
  let p : Nat → R := fun k => ratEnum (pairEnum k).1
  let q : Nat → R := fun k => ratEnum (pairEnum k).2
  let G : Nat → Prop := fun k => ∀ y, Icc a b y → p k < y → y < q k → c < f y
  have hA : ∀ k, LebesgueMeasurable (fun y => G k ∧ Icc a b y ∧ p k < y ∧ y < q k) := fun k => by
    by_cases hk : G k
    · exact lebesgueSigma.congr (lebesgueSigma.inter (measurable_Icc a b) (lebesgueSigma.inter
        (lebesgueSigma.compl _ (measurable_Iic (p k))) (measurable_Iio (q k)))) fun y => by grind
    · exact lebesgueSigma.congr lebesgueSigma.empty fun y => ⟨False.elim, fun h => hk h.1⟩
  have hU : LebesgueMeasurable (fun y => Icc a b y ∧ c < f y) :=
    lebesgueSigma.congr (lebesgueSigma.iUnion _ hA) fun x => by
      constructor
      · rintro ⟨k, hk, hx, h1, h2⟩; exact ⟨hx, hk x hx h1 h2⟩
      · rintro ⟨hx, hc⟩
        obtain ⟨δ, hδ, hδf⟩ := hf x hx.1 hx.2 (f x - c) (by grind)
        obtain ⟨i, hi1, hi2⟩ := ratEnum_dense (by grind : x - δ < x)
        obtain ⟨j, hj1, hj2⟩ := ratEnum_dense (by grind : x < x + δ)
        refine ⟨pairIndex (i, j), ?_, hx, ?_, ?_⟩
        · intro y _ h1 h2
          simp only [p, q, pairEnum_surj] at h1 h2
          have := abs_lt.1 (hδf y (abs_lt.2 ⟨by grind, by grind⟩)); grind
        · simp only [p, pairEnum_surj]; exact hi2
        · simp only [q, pairEnum_surj]; exact hj1
  have hV : LebesgueMeasurable (fun y => ¬ Icc a b y ∧ c < 0) := by
    by_cases hc : c < 0
    · exact lebesgueSigma.congr (lebesgueSigma.compl _ (measurable_Icc a b)) fun y => by simp [hc]
    · exact lebesgueSigma.congr lebesgueSigma.empty fun y => by simp [hc]
  exact lebesgueSigma.congr (lebesgueSigma.union hU hV) fun y => by
    unfold restr; split
    · rename_i h; simp [h]
    · rename_i h; simp [h]

/-! ## Uniform step functions -/

/-- The pieces `[y + i h, y + (i+1) h)`, `i < N`, with coefficients `f(y + i h)`. -/
noncomputable def upieces (f : R → R) (h : R) : R → Nat → List (R × (R → Prop))
  | _, 0 => []
  | y, n + 1 => (f y, fun z => y ≤ z ∧ z < y + h) :: upieces f h (y + h) n

/-- The properties of the uniform pieces. -/
theorem upieces_spec (f : R → R) {h : R} (hh : 0 ≤ h) (N : Nat) : ∀ y : R,
    (∀ p ∈ upieces f h y N, ∃ t, p.1 = f t ∧ y ≤ t ∧ t + h ≤ y + (N : R) * h ∧
      ∀ z, p.2 z ↔ (t ≤ z ∧ z < t + h)) ∧
    DisjOn Prod.snd (upieces f h y N) ∧
    (∀ z, y ≤ z → z < y + (N : R) * h → ∃ p ∈ upieces f h y N, p.2 z) := by
  induction N with
  | zero => intro y; refine ⟨fun p hp => absurd hp List.not_mem_nil, List.Pairwise.nil, ?_⟩
            intro z h1 h2; have : ((0 : Nat) : R) * h = 0 := by grind
            grind
  | succ N ih =>
    intro y
    obtain ⟨i1, i2, i3⟩ := ih (y + h)
    have hN : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg
    have e : y + h + (N : R) * h = y + ((N + 1 : Nat) : R) * h := by grind
    refine ⟨fun p hp => ?_, List.pairwise_cons.2 ⟨fun p hp z h1 h2 => ?_, i2⟩, fun z h1 h2 => ?_⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨y, rfl, Std.le_refl y, ?_, fun z => Iff.rfl⟩
        have := OrderedRing.mul_nonneg hN hh; grind
      · obtain ⟨t, a1, a2, a3, a4⟩ := i1 p hp
        exact ⟨t, a1, by grind, by grind, a4⟩
    · obtain ⟨t, _, a2, _, a4⟩ := i1 p hp
      have := (a4 z).1 h2; grind
    · by_cases hz : z < y + h
      · exact ⟨_, List.mem_cons_self, h1, hz⟩
      · obtain ⟨p, hp, hpz⟩ := i3 z (by grind) (by grind)
        exact ⟨p, List.mem_cons_of_mem _ hp, hpz⟩

/-- The Lebesgue integral of the uniform step function is a **Riemann sum**. -/
theorem lsum_upieces (f : R → R) {a b h : R} (hh : 0 ≤ h) (N : Nat) : ∀ y : R, a ≤ y →
    y + (N : R) * h ≤ b →
    lsum (fun p => p.1 * (lebesgue a b).μ p.2) (upieces f h y N) = rsum f y (unif y h N) := by
  induction N with
  | zero => intro y _ _; rfl
  | succ N ih =>
    intro y hy hb
    have hN : (0 : R) ≤ (N : R) := OrderedRing.natCast_nonneg
    have := OrderedRing.mul_nonneg hN hh
    show f y * (lebesgue a b).μ _ + lsum _ (upieces f h (y + h) N) = f y * (y + h - y) + _
    rw [ih (y + h) (by grind) (by grind), lebesgue_apply,
      outer_congr (B := fun z => y ≤ z ∧ z < y + h) fun z => by unfold Icc; grind,
      outer_Ico (by grind)]

/-! ## Lebesgue = Riemann -/

/-- **The Lebesgue integral of a continuous function equals its Riemann integral.** If `f` is
continuous on `[a, b]` with Riemann integral `I`, then `f` (extended by `0`) is integrable for
Lebesgue measure `λ_{a,b}` and `∫ f dλ = I`. -/
theorem lebesgue_eq_riemann {f : R → R} {a b I : R}
    (hf : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x) (hI : HasIntegral f a b I) :
    Integrable (lebesgue a b) (restr f a b) ∧ integral (lebesgue a b) (restr f a b) = I := by
  have hab := hI.le
  let L := lebesgue a b
  have hFm := measurable_restr hf
  -- Boundedness and integrability.
  obtain ⟨M1, hM1⟩ := bounded_above hf
  obtain ⟨M2, hM2⟩ := bounded_above (f := fun x => -f x) fun x h1 h2 ε hε => by
    obtain ⟨δ, hδ, h⟩ := hf x h1 h2 ε hε
    exact ⟨δ, hδ, fun y hy => by rw [show -f y - -f x = -(f y - f x) by grind, abs_neg]; exact h y hy⟩
  have hM : ∀ x, abs (restr f a b x) ≤ pp M1 + pp M2 := fun x => by
    have := le_pp M1; have := le_pp M2; have := pp_nonneg M1; have := pp_nonneg M2
    unfold restr; split
    · rename_i h; have := hM1 x h.1 h.2; have := hM2 x h.1 h.2; exact abs_le.2 ⟨by grind, by grind⟩
    · exact abs_le.2 ⟨by grind, by grind⟩
  have hFi : Integrable L (restr f a b) := Integrable.of_dominated L hFm
    (lintegral_const L (show 0 ≤ pp M1 + pp M2 by have := pp_nonneg M1; have := pp_nonneg M2; grind)).1 hM
  refine ⟨hFi, ?_⟩
  have hLab : L.μ (Icc a b) = b - a := lebesgue_Icc (Std.le_refl a) hab (Std.le_refl b)
  -- For every `ε`, the two integrals are within `ε (b − a + 1)` of each other.
  have key : ∀ ε : R, 0 < ε → abs (integral L (restr f a b) - I) ≤ ε * (b - a + 1) := by
    intro ε hε
    obtain ⟨δ, hδ, hδf⟩ := uniform_continuous hf hε
    obtain ⟨δ', hδ', hδ'I⟩ := hI.2 ε hε
    obtain ⟨η, hη, hη1, hη2⟩ := exists_pos_le_both hδ hδ'
    obtain ⟨n, hn⟩ := exists_div_lt (by grind : (0 : R) ≤ b - a) hη
    let h := (b - a) / ((n : R) + 1)
    have hlt := hn n (Nat.le_refl n)
    have hh : 0 ≤ h := by
      have : (0 : R) ≤ (n : R) := OrderedRing.natCast_nonneg
      rcases (by grind : a = b ∨ a < b) with e | e
      · show 0 ≤ (b - a) / ((n : R) + 1); rw [e, show b - b = 0 by grind]; grind
      · exact Std.le_of_lt (lt_div_of_mul_lt (by grind) (by grind))
    have hend := unif_end a b n
    -- The Riemann sum over the uniform partition.
    have hR : abs (rsum f a (unif a h (n + 1)) - I) < ε := by
      have ht := unif_isTagged hh (n + 1) a; rw [hend] at ht
      exact hδ'I _ ht (unif_meshLt (by grind) (n + 1) a)
    -- The step function: uniform pieces, plus the point `b`.
    let l := upieces f h a (n + 1) ++ [(f b, fun z => z = b)]
    obtain ⟨u1, u2, u3⟩ := upieces_spec f hh (n + 1) a
    have hlm : ∀ p ∈ l, LebesgueMeasurable p.2 := fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨t, _, _, _, a4⟩ := u1 p hp
        exact lebesgueSigma.congr (measurable_Ico t (t + h)) fun z => (a4 z).symm
      · rw [List.mem_singleton.1 hp]
        exact lebesgueSigma.congr (measurable_Icc b b) fun z => by unfold Icc; grind
    have hld : DisjOn Prod.snd l := List.pairwise_append.2 ⟨u2, List.pairwise_singleton _ _,
      fun p hp q hq z h1 h2 => by
        rw [List.mem_singleton.1 hq] at h2
        obtain ⟨t, _, _, a3, a4⟩ := u1 p hp
        have := (a4 z).1 h1; grind⟩
    obtain ⟨hsi, hsv⟩ := integral_step L hlm
    have hsv' : integral L (step l) = rsum f a (unif a h (n + 1)) := by
      rw [hsv, lsum_append, lsum_upieces f hh (n + 1) a (Std.le_refl a) (by grind)]
      have : L.μ (fun z => z = b) = 0 := by
        show outer _ = 0
        rw [outer_congr (B := fun z => z = b) fun z => by unfold Icc; grind, outer_point]
      show _ + (f b * L.μ (fun z => z = b) + 0) = _
      rw [this]; grind
    -- Pointwise, `|f − s| ≤ ε · 1_{[a,b]}`.
    have hpt : ∀ z, abs (restr f a b z - step l z) ≤ ε * ind (Icc a b) z := fun z => by
      by_cases hz : Icc a b z
      · rw [ind_pos hz]
        have e1 : restr f a b z = f z := by unfold restr; simp [hz]
        rcases (by have := hz.2; grind : z < b ∨ z = b) with hzb | hzb
        · obtain ⟨p, hp, hpz⟩ := u3 z hz.1 (by grind)
          obtain ⟨t, a1, a2, a3, a4⟩ := u1 p hp
          rw [e1, step_eval hld (List.mem_append_left _ hp) hpz, a1]
          have := (a4 z).1 hpz
          have : h < δ := by grind
          rw [show ε * 1 = ε by grind]
          exact Std.le_of_lt (hδf z t hz.1 hz.2 (by grind) (by grind)
            (abs_lt.2 ⟨by grind, by grind⟩))
        · rw [e1, step_eval hld (List.mem_append_right _ (List.mem_singleton_self _)) hzb, hzb]
          rw [show f b - f b = 0 by grind, abs_of_nonneg (Std.le_refl 0)]; grind
      · rw [ind_neg hz]
        have e1 : restr f a b z = 0 := by unfold restr; simp [hz]
        have e2 : step l z = 0 := step_eval.step_eval_zero fun p hp hpz => by
          rcases List.mem_append.1 hp with hp | hp
          · obtain ⟨t, _, a2, a3, a4⟩ := u1 p hp
            have := (a4 z).1 hpz; apply hz; unfold Icc; grind
          · rw [List.mem_singleton.1 hp] at hpz; apply hz; unfold Icc; grind
        rw [e1, e2, show (0 : R) - 0 = 0 by grind, abs_of_nonneg (Std.le_refl 0)]; grind
    obtain ⟨hεi, hεv⟩ := integral_ind L (measurable_Icc a b) ε
    obtain ⟨hd1, ed1⟩ := hFi.sub L hsi
    obtain ⟨hd2, ed2⟩ := hsi.sub L hFi
    have i1 := integral_mono L hd1 hεi fun z => (abs_le.1 (hpt z)).2
    have i2 := integral_mono L hd2 hεi fun z => by have := abs_le.1 (hpt z); grind
    rw [ed1, hεv, hLab, hsv'] at i1; rw [ed2, hεv, hLab, hsv'] at i2
    have := abs_lt.1 hR
    exact abs_le.2 ⟨by grind, by grind⟩
  -- Hence the two integrals agree.
  apply eq_of_abs_lt_all; intro ε hε
  have hpos : 0 < b - a + 1 := by grind
  have := key (ε / (2 * (b - a + 1))) (div_pos hε (by grind))
  have e : ε / (2 * (b - a + 1)) * (b - a + 1) = ε / 2 := by grind
  grind

end MeasureTheory

end Foundations.Topology
