import Foundations.NumberTheory.PNTTauberianC

/-!
# The prime number theorem

  **`π(N) ∼ N / log N`**: the number of primes up to `N`, multiplied by `log N / N`, tends to `1`.

Gauss guessed it from tables at fifteen (1792); Legendre proposed a version in 1798. Chebyshev
(1852) showed that `π(N) log N / N` stays between two constants, and Riemann (1859) tied the
question to the zeros of the zeta function. Hadamard and de la Vallée Poussin proved it in 1896
by complex analysis. Selberg and Erdős gave the first *elementary* proof in 1948/49, and that
is the proof formalised in the files `PNT*` of this part, ending here.

The last step only iterates the improvement lemma. Chebyshev's bound gives `|V(n)| ≤ C₀`
everywhere, where `V(n) = ψ(n)/n − 1`. As long as the current bound `α` is still at least `ε`,
the improvement lemma lowers it by the fixed amount `δ(ε)`. So after finitely many steps,
`|V(n)| < ε` for all large `n`. Since `ε` is arbitrary, `ψ(N)/N → 1`, and the equivalences of
`PNTEquivalence` turn this into `θ(N)/N → 1` and `π(N) log N / N → 1`.
-/

namespace Foundations.NumberTheory.PNT

open Foundations.Numbers Foundations.Numbers.Arith Foundations.Numbers.R Lean.Grind OF

/-- A property true at `0` and false at `n` has a last point `j` with `P j ∧ ¬ P (j + 1)`. -/
theorem exists_last (P : Nat → Prop) (h0 : P 0) : ∀ n, ¬ P n → ∃ j, P j ∧ ¬ P (j + 1)
  | 0, hn => absurd h0 hn
  | n + 1, hn => by
    by_cases h : P n
    · exact ⟨n, h, hn⟩
    · exact exists_last P h0 n h

/-- **The remainder is `o(N)`.** For every `ε > 0`, eventually `|ψ(N)/N − 1| ≤ ε`. -/
theorem vrem_eventually_small {ε : R} (hε : 0 < ε) :
    ∃ N₁ : Nat, ∀ N, N₁ ≤ N → abs (vrem N) ≤ ε := by
  by_cases hεC : C0 < ε
  · exact ⟨0, fun N _ => by have := abs_vrem_le N; grind⟩
  obtain ⟨δ, hδ, himp⟩ := improve hε
  -- Repeated improvement: the bound `C₀ − j δ` holds eventually while it is at least `ε`.
  have step : ∀ j : Nat, ε ≤ C0 - (j : R) * δ →
      ∃ N₁ : Nat, ∀ N, N₁ ≤ N → abs (vrem N) ≤ C0 - (j : R) * δ := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, fun N _ => by have := abs_vrem_le N; grind⟩
    | succ j ih =>
      intro hj
      have e : ((j + 1 : Nat) : R) * δ = (j : R) * δ + δ := by grind
      rw [e] at hj ⊢
      obtain ⟨N₀, hN₀⟩ := ih (by grind)
      have hjd : 0 ≤ (j : R) * δ := OrderedRing.mul_nonneg (natCast_nonneg' j) (Std.le_of_lt hδ)
      obtain ⟨N₁, hN₁⟩ := himp (C0 - (j : R) * δ) (by grind) (by grind) N₀ hN₀
      exact ⟨N₁, fun N hN => by have := hN₁ N hN; grind⟩
  -- Find the last `j` with `C₀ − j δ ≥ ε`.
  obtain ⟨n, -, hn⟩ := exists_nat_mul_ge C0 hδ
  obtain ⟨j, hj, hj1⟩ := exists_last (fun j => ε ≤ C0 - (j : R) * δ)
    (by show ε ≤ C0 - ((0 : Nat) : R) * δ; grind) n (by
      show ¬ ε ≤ C0 - (n : R) * δ
      have : (n : R) * δ = δ * (n : R) := by grind
      grind)
  obtain ⟨N₀, hN₀⟩ := step j hj
  have hjd : 0 ≤ (j : R) * δ := OrderedRing.mul_nonneg (natCast_nonneg' j) (Std.le_of_lt hδ)
  obtain ⟨N₁, hN₁⟩ := himp (C0 - (j : R) * δ) hj (by grind) N₀ hN₀
  refine ⟨N₁, fun N hN => ?_⟩
  have := hN₁ N hN
  have e : ((j + 1 : Nat) : R) * δ = (j : R) * δ + δ := by grind
  change ¬ ε ≤ C0 - ((j + 1 : Nat) : R) * δ at hj1
  rw [e] at hj1
  grind

/-- **The prime number theorem, Chebyshev's form: `ψ(N) ∼ N`.** `ψ(N)/N → 1`. -/
theorem psi_div_tendsto_one : Tendsto (fun N => psi N / (N : R)) 1 := by
  apply tendsto_of_le_eps; intro ε hε
  obtain ⟨N₁, hN₁⟩ := vrem_eventually_small hε
  refine ⟨N₁ + 1, fun N hN => ?_⟩
  have h := hN₁ N (by omega)
  have hN0 : (0 : R) < (N : R) := natCast_pos' (by omega)
  have e : psi N / (N : R) - 1 = vrem N := by
    unfold vrem rem; have : (N : R) ≠ 0 := by grind
    grind
  rw [e]; exact h

/-- **`θ(N) ∼ N`.** `θ(N)/N → 1`. -/
theorem theta_div_tendsto_one : Tendsto (fun N => theta N / (N : R)) 1 :=
  psi_iff_theta.1 psi_div_tendsto_one

/-- **The prime number theorem** (Hadamard, de la Vallée Poussin 1896; elementary proof by
Selberg and Erdős 1949). `π(N) · log N / N → 1`, i.e. `π(N) ∼ N / log N`. -/
theorem prime_number_theorem : PrimeNumberTheorem :=
  pnt_iff_psi.2 psi_div_tendsto_one

end Foundations.NumberTheory.PNT
