import Foundations.Topology.LebesgueIntegral

/-!
# Integrable functions, Fatou's lemma and dominated convergence

**Signed functions.** A real function `f` is split into its positive and negative parts,
`f = f⁺ − f⁻` with `f⁺ = max(f, 0)` and `f⁻ = max(−f, 0)`; it is **integrable** when both parts
are, and `∫ f = ∫ f⁺ − ∫ f⁻`. Additivity of the integral of non-negative functions makes the
integral **linear** on integrable functions, and **monotone**.

**Fatou's lemma** (Pierre Fatou, 1906). If `fₙ ≥ 0` are integrable and converge pointwise to `f`,
and `∫ fₙ ≤ B` from some index on, then `f` is integrable and `∫ f ≤ B`. Mass can escape in the
limit — `∫ f` may be strictly smaller than `lim ∫ fₙ` — but it cannot appear from nowhere. The
proof applies monotone convergence to the increasing sequence `gₙ = inf_{k ≥ n} fₖ`.

**The dominated convergence theorem** (Lebesgue, 1908/1910). If `fₙ → f` pointwise and
`|fₙ| ≤ g` for one integrable `g`, then `f` is integrable and `∫ fₙ → ∫ f`. This is the theorem
that made Lebesgue's integral indispensable: the exchange of limit and integral, which for the
Riemann integral needs uniform convergence (`UniformConvergence.lean`), here needs only a
dominating function. The proof is Fatou's lemma applied to `g − fₙ` and `g + fₙ` along a
subsequence that would witness a failure of convergence.
-/

namespace Foundations.Topology

open Foundations.Numbers Foundations.Numbers.R OF Lean.Grind

namespace MeasureTheory

variable {α : Type} {S : SigmaAlgebra α} (m : Measure S)

/-! ## Positive and negative parts -/

/-- `x = pp x − pp (−x)`. -/
theorem pp_sub_pp (x : R) : pp x - pp (-x) = x := by
  unfold pp; split <;> split <;> grind

/-- Positive parts of measurable functions are measurable. -/
theorem Measurable.pp {f : α → R} (hf : Measurable S f) : Measurable S (fun x => pp (f x)) :=
  fun c => by
    by_cases hc : c < 0
    · exact S.congr S.univ fun x => ⟨fun _ => by have := pp_nonneg (f x); grind, fun _ => trivial⟩
    · exact S.congr (hf c) fun x => by
        show c < f x ↔ c < MeasureTheory.pp (f x); unfold MeasureTheory.pp; split <;> grind

/-- **Integrable function.** Both `f⁺` and `f⁻` have finite integral. -/
structure Integrable (f : α → R) : Prop where
  /-- The positive part is integrable. -/
  pos : LIntegrable m (fun x => pp (f x))
  /-- The negative part is integrable. -/
  neg : LIntegrable m (fun x => pp (-f x))

/-- **The integral.** For an integrable function, `∫ f = ∫ f⁺ − ∫ f⁻`. -/
noncomputable def integral (f : α → R) : R :=
  lintegral m (fun x => pp (f x)) - lintegral m (fun x => pp (-f x))

/-- Integrable functions are measurable. -/
theorem Integrable.measurable {f : α → R} (hf : Integrable m f) : Measurable S f := by
  have := hf.pos.measurable.sub hf.neg.measurable
  exact fun c => S.congr (this c) fun x => by
    show c < pp (f x) - pp (-f x) ↔ c < f x; rw [pp_sub_pp]

/-- **Non-negative integrable functions.** For `f ≥ 0`, integrability in the two senses agree and
`∫ f = ∫ f dμ` (the integral of a non-negative function). -/
theorem integrable_iff_of_nonneg {f : α → R} (h0 : ∀ x, 0 ≤ f x) :
    (Integrable m f ↔ LIntegrable m f) ∧ integral m f = lintegral m f := by
  have e1 : (fun x => pp (f x)) = f := funext fun x => pp_of_nonneg (h0 x)
  have e2 : (fun x => pp (-f x)) = fun _ => 0 := funext fun x => pp_of_nonpos (by have := h0 x; grind)
  refine ⟨⟨fun h => by have := h.pos; rwa [e1] at this,
    fun h => ⟨by rw [e1]; exact h, by rw [e2]; exact (lintegral_zero m).1⟩⟩, ?_⟩
  unfold integral; rw [e1, e2, (lintegral_zero m).2]; grind

/-- An integrable non-negative function is integrable in the sense of `LIntegrable`. -/
theorem Integrable.lintegrable {f : α → R} (hf : Integrable m f) (h0 : ∀ x, 0 ≤ f x) :
    LIntegrable m f := ((integrable_iff_of_nonneg m h0).1.1 hf)

/-- **Domination.** A measurable `f` with `|f| ≤ g`, `g` integrable, is integrable. -/
theorem Integrable.of_dominated {f g : α → R} (hf : Measurable S f) (hg : LIntegrable m g)
    (h : ∀ x, abs (f x) ≤ g x) : Integrable m f :=
  ⟨(lintegral_mono m hg hf.pp (fun x => pp_nonneg _) fun x => by
      have := abs_le.1 (h x); unfold pp; split <;> grind).1,
    (lintegral_mono m hg hf.neg.pp (fun x => pp_nonneg _) fun x => by
      have := abs_le.1 (h x); unfold pp; split <;> grind).1⟩

/-! ## Linearity -/

/-- **Additivity.** `f + g` is integrable and `∫ (f + g) = ∫ f + ∫ g`. -/
theorem Integrable.add {f g : α → R} (hf : Integrable m f) (hg : Integrable m g) :
    Integrable m (fun x => f x + g x) ∧
      integral m (fun x => f x + g x) = integral m f + integral m g := by
  obtain ⟨hP, eP⟩ := lintegral_add m hf.pos hg.pos
  obtain ⟨hN, eN⟩ := lintegral_add m hf.neg hg.neg
  have hi : Integrable m (fun x => f x + g x) :=
    ⟨(lintegral_mono m hP (hf.measurable.add hg.measurable).pp (fun x => pp_nonneg _) fun x => by
        have := le_pp (f x); have := le_pp (g x); have := pp_nonneg (f x)
        have := pp_nonneg (g x); unfold pp; split <;> grind).1,
      (lintegral_mono m hN (hf.measurable.add hg.measurable).neg.pp (fun x => pp_nonneg _)
        fun x => by
          have := le_pp (-f x); have := le_pp (-g x); have := pp_nonneg (-f x)
          have := pp_nonneg (-g x); unfold pp; split <;> grind).1⟩
  refine ⟨hi, ?_⟩
  -- `(f+g)⁺ + f⁻ + g⁻ = (f+g)⁻ + f⁺ + g⁺`.
  obtain ⟨h1, e1⟩ := lintegral_add m hi.pos hN
  obtain ⟨h2, e2⟩ := lintegral_add m hi.neg hP
  have e : (fun x => pp (f x + g x) + (pp (-f x) + pp (-g x))) =
      (fun x => pp (-(f x + g x)) + (pp (f x) + pp (g x))) := funext fun x => by
    have := pp_sub_pp (f x); have := pp_sub_pp (g x); have := pp_sub_pp (f x + g x); grind
  rw [e] at e1
  unfold integral
  rw [eP, eN] at *
  grind

/-- **Negation.** `∫ (−f) = −∫ f`. -/
theorem Integrable.negate {f : α → R} (hf : Integrable m f) :
    Integrable m (fun x => -f x) ∧ integral m (fun x => -f x) = -integral m f := by
  have e : (fun x => pp (- -f x)) = fun x => pp (f x) := funext fun x => by rw [show - -f x = f x by grind]
  refine ⟨⟨hf.neg, e ▸ hf.pos⟩, ?_⟩
  unfold integral; rw [e]; grind

/-- **Subtraction.** `∫ (f − g) = ∫ f − ∫ g`. -/
theorem Integrable.sub {f g : α → R} (hf : Integrable m f) (hg : Integrable m g) :
    Integrable m (fun x => f x - g x) ∧
      integral m (fun x => f x - g x) = integral m f - integral m g := by
  obtain ⟨h1, e1⟩ := hg.negate m
  obtain ⟨h2, e2⟩ := hf.add m h1
  have e : (fun x => f x + -g x) = fun x => f x - g x := funext fun x => by grind
  rw [e] at h2 e2; rw [e2, e1]; exact ⟨h2, by grind⟩

/-- **Homogeneity.** `∫ c f = c ∫ f` for every real `c`. -/
theorem Integrable.const_mul {f : α → R} (hf : Integrable m f) (c : R) :
    Integrable m (fun x => c * f x) ∧ integral m (fun x => c * f x) = c * integral m f := by
  have pos : ∀ {c : R}, 0 ≤ c → Integrable m (fun x => c * f x) ∧
      integral m (fun x => c * f x) = c * integral m f := fun {c} hc => by
    have e1 : (fun x => pp (c * f x)) = fun x => c * pp (f x) := funext fun x => by
      unfold pp; split <;> split <;> (try grind) <;>
        (rename_i h1 h2; first
          | (have := OrderedRing.mul_nonneg hc (show 0 ≤ f x by grind); grind)
          | (have := OrderedRing.mul_le_mul_of_nonneg_left (show f x ≤ 0 by grind) hc; grind))
    have e2 : (fun x => pp (-(c * f x))) = fun x => c * pp (-f x) := funext fun x => by
      rw [show -(c * f x) = c * -f x by grind]
      unfold pp; split <;> split <;> (try grind) <;>
        (rename_i h1 h2; first
          | (have := OrderedRing.mul_nonneg hc (show 0 ≤ -f x by grind); grind)
          | (have := OrderedRing.mul_le_mul_of_nonneg_left (show -f x ≤ 0 by grind) hc; grind))
    obtain ⟨a1, b1⟩ := lintegral_const_mul m hf.pos hc
    obtain ⟨a2, b2⟩ := lintegral_const_mul m hf.neg hc
    refine ⟨⟨e1 ▸ a1, e2 ▸ a2⟩, ?_⟩
    unfold integral; rw [e1, e2, b1, b2]; grind
  rcases (by grind : 0 ≤ c ∨ c < 0) with hc | hc
  · exact pos hc
  · obtain ⟨h1, e1⟩ := pos (c := -c) (by grind)
    obtain ⟨h2, e2⟩ := h1.negate m
    have e : (fun x => -(-c * f x)) = fun x => c * f x := funext fun x => by grind
    rw [e] at h2 e2; rw [e2, e1]; exact ⟨h2, by grind⟩

/-- **Monotonicity.** `f ≤ g` implies `∫ f ≤ ∫ g`. -/
theorem integral_mono {f g : α → R} (hf : Integrable m f) (hg : Integrable m g)
    (h : ∀ x, f x ≤ g x) : integral m f ≤ integral m g := by
  obtain ⟨h1, e1⟩ := hg.sub m hf
  have h0 : ∀ x, 0 ≤ g x - f x := fun x => by have := h x; grind
  have := lintegral_nonneg m (h1.lintegrable m h0).bdd
  rw [← (integrable_iff_of_nonneg m h0).2, e1] at this; grind

/-! ## Fatou's lemma -/

/-- The infimum `inf_{k ≥ n} aₖ` of a tail of a sequence (for `a ≥ 0`). -/
noncomputable def tailInf (a : Nat → R) (n : Nat) : R :=
  open Classical in
  if h : ∃ M, ∀ y, (∃ k, n ≤ k ∧ y = -a k) → y ≤ M then
    -Classical.choose (exists_lub _ ⟨-a n, n, Nat.le_refl n, rfl⟩ h)
  else 0

/-- The basic properties of `tailInf` for a non-negative sequence: it is a lower bound of the
tail, and the greatest one. -/
theorem tailInf_spec {a : Nat → R} (ha : ∀ k, 0 ≤ a k) (n : Nat) :
    (∀ k, n ≤ k → tailInf a n ≤ a k) ∧ ∀ c, (∀ k, n ≤ k → c ≤ a k) → c ≤ tailInf a n := by
  have h : ∃ M, ∀ y, (∃ k, n ≤ k ∧ y = -a k) → y ≤ M :=
    ⟨0, fun y ⟨k, _, e⟩ => by have := ha k; grind⟩
  unfold tailInf; rw [dite_eq_left_of_eq_true (eq_true h)]
  have hs := Classical.choose_spec (exists_lub _ ⟨-a n, n, Nat.le_refl n, rfl⟩ h)
  refine ⟨fun k hk => ?_, fun c hc => ?_⟩
  · have := hs.1 (-a k) ⟨k, hk, rfl⟩; grind
  · have := hs.2 (-c) fun y ⟨k, hk, e⟩ => by have := hc k hk; grind
    grind

/-- **Fatou's lemma (1906).** For pointwise convergent sequences: if `fₙ ≥ 0` are integrable,
`fₙ → f` pointwise, and `∫ fₙ ≤ B` for all `n ≥ N`, then `f` is integrable and `∫ f ≤ B`. -/
theorem fatou {F : Nat → α → R} {f : α → R} (hF : ∀ n, LIntegrable m (F n))
    (hlim : ∀ x, Tendsto (fun n => F n x) (f x)) {B : R} {N : Nat}
    (hB : ∀ n, N ≤ n → lintegral m (F n) ≤ B) : LIntegrable m f ∧ lintegral m f ≤ B := by
  let G : Nat → α → R := fun n x => tailInf (fun k => F k x) n
  have hs : ∀ n x, _ := fun n x => tailInf_spec (a := fun k => F k x) (fun k => (hF k).nonneg x) n
  have hGF : ∀ n x, G n x ≤ F n x := fun n x => (hs n x).1 n (Nat.le_refl n)
  have hG0 : ∀ n x, 0 ≤ G n x := fun n x => (hs n x).2 0 fun k _ => (hF k).nonneg x
  have hGmono : ∀ n x, G n x ≤ G (n + 1) x := fun n x =>
    (hs (n + 1) x).2 _ fun k hk => (hs n x).1 k (by omega)
  have hGm : ∀ n, Measurable S (G n) := fun n c =>
    S.congr (S.iUnion _ fun j => S.iInter _ fun i => (hF (n + i)).measurable.ge
      (c + 1 / ((j : R) + 1))) fun x => by
      constructor
      · rintro ⟨j, hj⟩
        have := (hs n x).2 (c + 1 / ((j : R) + 1)) fun k hk => by
          have := hj (k - n); rwa [show n + (k - n) = k by omega] at this
        have := eps_pos j; grind
      · intro h
        obtain ⟨j, hj⟩ := eps_small (by grind : (0 : R) < G n x - c)
        exact ⟨j, fun i => by
          have := hj j (Nat.le_refl j); have := (hs n x).1 (n + i) (by omega); grind⟩
  have hGlim : ∀ x, Tendsto (fun n => G n x) (f x) := fun x ε hε => by
    obtain ⟨K, hK⟩ := hlim x (ε / 2) (by grind)
    refine ⟨K, fun n hn => abs_lt.2 ⟨?_, ?_⟩⟩
    · have := (hs n x).2 (f x - ε / 2) fun k hk => by
        have := abs_lt.1 (hK k (by omega)); grind
      grind
    · have := hGF n x; have := abs_lt.1 (hK n hn); grind
  have hGi : ∀ n, LIntegrable m (G n) := fun n =>
    (lintegral_mono m (hF n) (hGm n) (hG0 n) (hGF n)).1
  have hGB : ∀ n, lintegral m (G n) ≤ B := fun n => by
    have h1 := (lintegral_mono m (hF (n + N)) (hGm n) (hG0 n)
      fun x => (hs n x).1 (n + N) (by omega)).2
    have := hB (n + N) (by omega); grind
  obtain ⟨hfi, hlimI⟩ := monotone_convergence m hGi hGmono hGlim hGB
  exact ⟨hfi, tendsto_le hlimI hGB⟩

/-! ## Dominated convergence -/

/-- A subsequence along which a property holds, given that it holds arbitrarily late. -/
noncomputable def subseqOf {P : Nat → Prop} (h : ∀ N, ∃ n, N ≤ n ∧ P n) : Nat → Nat
  | 0 => Classical.choose (h 0)
  | k + 1 => Classical.choose (h (subseqOf h k + 1))

/-- The subsequence satisfies `P` and its indices grow at least like `k`. -/
theorem subseqOf_spec {P : Nat → Prop} (h : ∀ N, ∃ n, N ≤ n ∧ P n) (k : Nat) :
    P (subseqOf h k) ∧ k ≤ subseqOf h k := by
  induction k with
  | zero => exact ⟨(Classical.choose_spec (h 0)).2, Nat.zero_le _⟩
  | succ k ih =>
    have := Classical.choose_spec (h (subseqOf h k + 1))
    exact ⟨this.2, by show k + 1 ≤ Classical.choose _; omega⟩

/-- A subsequence (with indices `φ k ≥ k`) of a convergent sequence converges to the same limit. -/
theorem Tendsto.comp_ge {a : Nat → R} {L : R} (h : Tendsto a L) {φ : Nat → Nat}
    (hφ : ∀ k, k ≤ φ k) : Tendsto (fun k => a (φ k)) L := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun k hk => hN (φ k) (Nat.le_trans hk (hφ k))⟩

/-- **Dominated convergence theorem (Lebesgue).** Let `fₙ` be measurable, `fₙ → f` pointwise, and
`|fₙ| ≤ g` with `g ≥ 0` integrable. Then `f` and all `fₙ` are integrable and
`∫ fₙ dμ → ∫ f dμ`. -/
theorem dominated_convergence {F : Nat → α → R} {f g : α → R} (hF : ∀ n, Measurable S (F n))
    (hg : LIntegrable m g) (hdom : ∀ n x, abs (F n x) ≤ g x)
    (hlim : ∀ x, Tendsto (fun n => F n x) (f x)) :
    Integrable m f ∧ (∀ n, Integrable m (F n)) ∧
      Tendsto (fun n => integral m (F n)) (integral m f) := by
  have hFi : ∀ n, Integrable m (F n) := fun n => Integrable.of_dominated m (hF n) hg (hdom n)
  have hfdom : ∀ x, abs (f x) ≤ g x := fun x => by
    have h1 := le_of_tendsto (hlim x) fun n => (abs_le.1 (hdom n x)).1
    have h2 := tendsto_le (hlim x) fun n => (abs_le.1 (hdom n x)).2
    exact abs_le.2 ⟨h1, h2⟩
  have hfi : Integrable m f :=
    Integrable.of_dominated m (Measurable.of_tendsto hF hlim) hg hfdom
  have hgi : Integrable m g := (integrable_iff_of_nonneg m hg.nonneg).1.2 hg
  have hgI := (integrable_iff_of_nonneg m hg.nonneg).2
  refine ⟨hfi, hFi, fun ε hε => ?_⟩
  -- Fatou applied along a subsequence on which `∫ fₙ` stays `ε` away from `∫ f`.
  apply Classical.byContradiction; intro hno
  have hoften : ∀ N, ∃ n, N ≤ n ∧ ε ≤ abs (integral m (F n) - integral m f) := fun N => by
    apply Classical.byContradiction; intro h; apply hno
    exact ⟨N, fun n hn => by
      apply Classical.byContradiction; intro h'; exact h ⟨n, hn, by grind⟩⟩
  -- Case analysis: too large infinitely often, or too small infinitely often.
  by_cases hup : ∀ N, ∃ n, N ≤ n ∧ integral m f + ε ≤ integral m (F n)
  · let φ := subseqOf hup
    have hφ := subseqOf_spec hup
    let H : Nat → α → R := fun k x => g x - F (φ k) x
    have hH0 : ∀ k x, 0 ≤ H k x := fun k x => by have := abs_le.1 (hdom (φ k) x); grind
    have hHi : ∀ k, LIntegrable m (H k) := fun k => ((hgi.sub m (hFi (φ k))).1.lintegrable m (hH0 k))
    have hHval : ∀ k, lintegral m (H k) = integral m g - integral m (F (φ k)) := fun k => by
      rw [← (integrable_iff_of_nonneg m (hH0 k)).2]; exact (hgi.sub m (hFi (φ k))).2
    have h0 : ∀ x, 0 ≤ g x - f x := fun x => by have := abs_le.1 (hfdom x); grind
    obtain ⟨_, hle⟩ := fatou m hHi (f := fun x => g x - f x)
      (fun x => (tendsto_const (g x)).sub (Tendsto.comp_ge (hlim x) fun k => (hφ k).2)) (N := 0)
      (B := integral m g - integral m f - ε) fun k _ => by
        rw [hHval]; have := (hφ k).1; grind
    rw [← (integrable_iff_of_nonneg m h0).2, (hgi.sub m hfi).2] at hle
    grind
  · have hdown : ∀ N, ∃ n, N ≤ n ∧ integral m (F n) ≤ integral m f - ε := by
      have : ∃ N₀, ∀ n, N₀ ≤ n → integral m (F n) < integral m f + ε := by
        apply Classical.byContradiction; intro h; apply hup; intro N
        apply Classical.byContradiction; intro h'; apply h
        exact ⟨N, fun n hn => by
          apply Classical.byContradiction; intro h''; exact h' ⟨n, hn, by grind⟩⟩
      obtain ⟨N₀, hN₀⟩ := this
      intro N
      obtain ⟨n, hn, h⟩ := hoften (N + N₀)
      refine ⟨n, by omega, ?_⟩
      have := hN₀ n (by omega)
      rcases abs_cases (integral m (F n) - integral m f) with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h <;> grind
    let φ := subseqOf hdown
    have hφ := subseqOf_spec hdown
    let H : Nat → α → R := fun k x => g x + F (φ k) x
    have hH0 : ∀ k x, 0 ≤ H k x := fun k x => by have := abs_le.1 (hdom (φ k) x); grind
    have hHi : ∀ k, LIntegrable m (H k) := fun k => ((hgi.add m (hFi (φ k))).1.lintegrable m (hH0 k))
    have hHval : ∀ k, lintegral m (H k) = integral m g + integral m (F (φ k)) := fun k => by
      rw [← (integrable_iff_of_nonneg m (hH0 k)).2]; exact (hgi.add m (hFi (φ k))).2
    have h0 : ∀ x, 0 ≤ g x + f x := fun x => by have := abs_le.1 (hfdom x); grind
    obtain ⟨_, hle⟩ := fatou m hHi (f := fun x => g x + f x)
      (fun x => (tendsto_const (g x)).add (Tendsto.comp_ge (hlim x) fun k => (hφ k).2)) (N := 0)
      (B := integral m g + integral m f - ε) fun k _ => by
        rw [hHval]; have := (hφ k).1; grind
    rw [← (integrable_iff_of_nonneg m h0).2, (hgi.add m hfi).2] at hle
    grind

end MeasureTheory

end Foundations.Topology
