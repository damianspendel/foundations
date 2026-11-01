import Foundations.Numbers.ComplexModulus

/-!
# A two-dimensional extreme value theorem

The extreme value theorem of the `Continuity` file says that a continuous function on a closed
interval attains its minimum. For the fundamental theorem of algebra we need the same for a
function of a *complex* variable on a closed square `|re z| ≤ ρ`, `|im z| ≤ ρ`.

The proof is the classical one: take points `zₙ` of the square with `g(zₙ)` tending to the
infimum `m`; by **Bolzano–Weierstrass** the real parts have a convergent subsequence, and along it
the imaginary parts have a further convergent subsequence. The limit point `z*` lies in the square
(the square is closed), and by continuity `g(z*) = m`. This is compactness of the square, used
in its sequential form.
-/

namespace Foundations.Numbers

open Lean.Grind OF

namespace C

open R

/-- `z` lies in the closed square `|re z| ≤ ρ`, `|im z| ≤ ρ`. -/
def InSq (ρ : R) (z : C) : Prop := abs z.re ≤ ρ ∧ abs z.im ≤ ρ

/-- Strictly increasing index sequences preserve `<`. -/
theorem strictMono_lt {φ : Nat → Nat} (hφ : ∀ k, φ k < φ (k + 1)) {a b : Nat} (h : a < b) :
    φ a < φ b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hab : a = b
    · rw [hab]; exact hφ b
    · have := ih (by omega); have := hφ b; omega

/-- A subsequence of a convergent sequence converges to the same limit. -/
theorem tendsto_subseq {a : Nat → R} {L : R} (h : Tendsto a L) {ψ : Nat → Nat}
    (hψ : ∀ k, ψ k < ψ (k + 1)) : Tendsto (fun k => a (ψ k)) L := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun k hk => hN (ψ k) (by have := le_of_strictMono hψ k; omega)⟩

/-- **Two-dimensional extreme value theorem.** A non-negative function `g : ℂ → ℝ`, continuous
everywhere, attains its minimum on every closed square `|re z|, |im z| ≤ ρ`. -/
theorem exists_min_on_square {g : C → R} {ρ : R} (hρ : 0 ≤ ρ) (hg0 : ∀ z, 0 ≤ g z)
    (hg : ∀ z₀, ∀ ε : R, 0 < ε → ∃ δ : R, 0 < δ ∧ ∀ z, cabs (z - z₀) < δ → abs (g z - g z₀) < ε) :
    ∃ zs, InSq ρ zs ∧ ∀ z, InSq ρ z → g zs ≤ g z := by
  have h0 : InSq ρ 0 := ⟨by rw [zero_re, R.abs_zero]; exact hρ, by rw [zero_im, R.abs_zero]; exact hρ⟩
  -- The infimum `m` of `g` over the square.
  obtain ⟨L, hL1, hL2⟩ := exists_lub (fun x => ∃ z, InSq ρ z ∧ x = -g z) ⟨_, 0, h0, rfl⟩
    ⟨0, fun x ⟨z, _, hx⟩ => by have := hg0 z; grind⟩
  have hm : ∀ z, InSq ρ z → -L ≤ g z := fun z hz => by have := hL1 _ ⟨z, hz, rfl⟩; grind
  have hx : ∀ n : Nat, ∃ z, InSq ρ z ∧ g z < -L + 1 / ((n : R) + 1) := fun n => by
    apply Classical.byContradiction; intro hno
    have := hL2 (L - 1 / ((n : R) + 1)) fun x ⟨z, hz, hxz⟩ => by
      apply Classical.byContradiction; intro h; exact hno ⟨z, hz, by grind⟩
    have := eps_pos n; grind
  let zs : Nat → C := fun n => (hx n).choose
  have hzs : ∀ n, InSq ρ (zs n) ∧ g (zs n) < -L + 1 / ((n : R) + 1) := fun n => (hx n).choose_spec
  have bnd : ∀ n, abs (zs n).re ≤ ρ ∧ abs (zs n).im ≤ ρ := fun n => (hzs n).1
  -- Bolzano–Weierstrass twice.
  obtain ⟨φ, hφ, x, hxlim⟩ := bolzano_weierstrass (a := fun n => (zs n).re) ⟨ρ, fun n => (bnd n).1⟩
  obtain ⟨ψ, hψ, y, hylim⟩ := bolzano_weierstrass (a := fun k => (zs (φ k)).im)
    ⟨ρ, fun k => (bnd (φ k)).2⟩
  let χ : Nat → Nat := fun k => φ (ψ k)
  have hχ : ∀ k, χ k < χ (k + 1) := fun k => strictMono_lt hφ (hψ k)
  have hxlim' : Tendsto (fun k => (zs (χ k)).re) x := tendsto_subseq hxlim hψ
  let zstar : C := ⟨x, y⟩
  have hin : InSq ρ zstar := by
    constructor
    · show abs x ≤ ρ
      exact abs_le.2 ⟨le_of_tendsto hxlim fun k => (abs_le.1 (bnd (φ k)).1).1,
        tendsto_le hxlim fun k => (abs_le.1 (bnd (φ k)).1).2⟩
    · show abs y ≤ ρ
      exact abs_le.2 ⟨le_of_tendsto hylim fun k => (abs_le.1 (bnd (φ (ψ k))).2).1,
        tendsto_le hylim fun k => (abs_le.1 (bnd (φ (ψ k))).2).2⟩
  -- By continuity, `g (zs (χ k)) → g z*`; by construction, `g (zs (χ k)) → m`.
  have h1 : Tendsto (fun k => g (zs (χ k))) (g zstar) := fun ε hε => by
    obtain ⟨δ, hδ, hδ'⟩ := hg zstar ε hε
    obtain ⟨N₁, hN₁⟩ := hxlim' (δ / 2) (by grind)
    obtain ⟨N₂, hN₂⟩ := hylim (δ / 2) (by grind)
    refine ⟨max N₁ N₂, fun k hk => hδ' _ ?_⟩
    have k1 := hN₁ k (by omega)
    have k2 : abs ((zs (φ (ψ k))).im - y) < δ / 2 := hN₂ k (by omega)
    have := cabs_le_nrm (zs (χ k) - zstar)
    unfold nrm at this
    have e1 : (zs (χ k) - zstar).re = (zs (χ k)).re - x := by
      show (zs (χ k) + -zstar).re = _; simp only [add_re, neg_re]; grind
    have e2 : (zs (χ k) - zstar).im = (zs (χ k)).im - y := by
      show (zs (χ k) + -zstar).im = _; simp only [add_im, neg_im]; grind
    rw [e1, e2] at this
    have k1' : abs ((zs (χ k)).re - x) < δ / 2 := k1
    have k2' : abs ((zs (χ k)).im - y) < δ / 2 := k2
    grind
  have h2 : Tendsto (fun k => g (zs (χ k))) (-L) := fun ε hε => by
    obtain ⟨N, hN⟩ := eps_small hε
    refine ⟨N, fun k hk => abs_lt.2 ⟨?_, ?_⟩⟩
    · have := hm _ (hzs (χ k)).1; grind
    · have := (hzs (χ k)).2
      have := hN (χ k) (by have := le_of_strictMono hχ k; omega)
      grind
  have heq := tendsto_unique h1 h2
  exact ⟨zstar, hin, fun z hz => by rw [heq]; exact hm z hz⟩

end C

end Foundations.Numbers
