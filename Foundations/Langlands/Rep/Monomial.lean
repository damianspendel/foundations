import Foundations.Langlands.Rep.Completeness

/-!
# Monomial representations and a cube root of unity

To write down character tables we need representations given by explicit matrices. The ones
used for `S₃` and `A₄` are all **monomial**: each `ρ(g)` has exactly one non-zero entry in every
column, a root of unity, so `ρ(g) e_j = ζ^{E_g(j)} e_{P_g(j)}` for a permutation `P_g` of the
basis and exponents `E_g(j)` modulo `m`, where `ζ^m = 1`. Products of monomial matrices are
monomial (`monoMat_mul`), so `ρ` is a representation as soon as the finite data `(P, E)`
satisfy the cocycle rules `P_{gh} = P_g ∘ P_h` and `E_{gh}(j) = E_g(P_h(j)) + E_h(j)`
(`monoRep`). For explicit finite groups these rules can be checked by `decide`.

Its character is `χ(g) = Σ_{j : P_g(j) = j} ζ^{E_g(j)}` (`character_monoRep`).

The last section fixes a primitive cube root of unity `ω ∈ ℂ` (`omega3`): a root of
`1 + z + z²`, which exists by the fundamental theorem of algebra; so `ω³ = 1` and `ω ≠ 1`.
-/

namespace Foundations.Langlands

open Foundations.Algebra Foundations.Algebra.FiniteType Mat
open Foundations.Numbers (C)

set_option linter.unusedSectionVars false

universe u w

variable {K : Type w} [CommRing K]

/-! ## Powers -/

/-- Natural powers `z^n` in a commutative ring. -/
def cpow (z : K) : Nat → K
  | 0 => 1
  | n + 1 => cpow z n * z

/-- `z⁰ = 1`. -/
theorem cpow_zero (z : K) : cpow z 0 = 1 := rfl

/-- `z^(n+1) = z^n z`. -/
theorem cpow_succ (z : K) (n : Nat) : cpow z (n + 1) = cpow z n * z := rfl

/-- `z^(a+b) = z^a z^b`. -/
theorem cpow_add (z : K) (a : Nat) : ∀ b, cpow z (a + b) = cpow z a * cpow z b
  | 0 => (Ring.mul_one _).symm
  | b + 1 => by
    rw [← Nat.add_assoc, cpow_succ, cpow_succ, cpow_add z a b, Ring.mul_assoc]

/-- If `z^m = 1` then `z^(m k) = 1`. -/
theorem cpow_mul_eq_one {z : K} {m : Nat} (h : cpow z m = 1) : ∀ k, cpow z (m * k) = 1
  | 0 => rfl
  | k + 1 => by rw [Nat.mul_succ, cpow_add, cpow_mul_eq_one h k, h, Ring.one_mul]

/-- If `z^m = 1`, exponents may be reduced modulo `m`. -/
theorem cpow_mod {z : K} {m : Nat} (h : cpow z m = 1) (n : Nat) : cpow z (n % m) = cpow z n := by
  conv => rhs; rw [← Nat.mod_add_div n m]
  rw [cpow_add, cpow_mul_eq_one h, Ring.mul_one]

/-- With `z^m = 1`, powers with exponents in `Fin m` multiply by adding exponents mod `m`. -/
theorem cpow_fin_add {z : K} {m : Nat} (h : cpow z m = 1) (a b : Fin m) :
    cpow z (a + b).val = cpow z a.val * cpow z b.val := by
  rw [Fin.val_add, cpow_mod h, cpow_add]

/-! ## Monomial matrices -/

variable {n : Nat}

/-- The **monomial matrix** with `e_j ↦ c_j e_{π(j)}`: its `(i, j)` entry is `c_j` if
`i = π(j)` and `0` otherwise. -/
noncomputable def monoMat (π : Fin n → Fin n) (c : Fin n → K) : Mat (Fin n) (Fin n) K :=
  fun i j => kd i (π j) * c j

/-- **Products of monomial matrices are monomial**:
`M(π, c) M(π', c') = M(π ∘ π', j ↦ c_{π'(j)} c'_j)`. -/
theorem monoMat_mul (π π' : Fin n → Fin n) (c c' : Fin n → K) :
    monoMat π c * monoMat π' c' = monoMat (fun j => π (π' j)) (fun j => c (π' j) * c' j) := by
  apply ext; intro i l
  rw [mul_apply]
  have e : ∀ j, monoMat π c i j * monoMat π' c' j l = (kd i (π j) * c j * c' l) * kd j (π' l) :=
    fun j => by
      show kd i (π j) * c j * (kd j (π' l) * c' l) = _
      rw [CommRing.mul_comm (kd j (π' l)) (c' l), ← Ring.mul_assoc]
  rw [isum_congr e, isum_mul_kd]
  show kd i (π (π' l)) * c (π' l) * c' l = kd i (π (π' l)) * (c (π' l) * c' l)
  rw [Ring.mul_assoc]

/-- The identity matrix is monomial. -/
theorem monoMat_one : monoMat (fun j : Fin n => j) (fun _ => (1 : K)) = 1 :=
  ext fun i j => by show kd i j * 1 = kd i j; rw [Ring.mul_one]

/-- The trace of a monomial matrix. -/
theorem trace_monoMat (π : Fin n → Fin n) (c : Fin n → K) :
    trace (monoMat π c) = isum (fun j => kd j (π j) * c j) := rfl

/-! ## Monomial representations -/

/-- **Monomial representation.** Given `ζ` with `ζ^m = 1`, permutations `P_g` of `Fin n` and
exponents `E_g : Fin n → Fin m` with `P_1 = id`, `E_1 = 0` and the cocycle rules
`P_{gh} = P_g ∘ P_h`, `E_{gh}(j) = E_g(P_h(j)) + E_h(j)`, the matrices
`ρ(g) : e_j ↦ ζ^{E_g(j)} e_{P_g(j)}` form a representation of `G` on `K^n`. -/
noncomputable def monoRep {G : Type u} [Group G] {m : Nat} (ζ : K) (hζ : cpow ζ m = 1)
    (P : G → Fin n → Fin n) (E : G → Fin n → Fin m) (h1 : ∀ j, P 1 j = j ∧ (E 1 j).val = 0)
    (hmul : ∀ g h j, P (g * h) j = P g (P h j) ∧ E (g * h) j = E g (P h j) + E h j) :
    Rep G K (Fin n) where
  toFun g := monoMat (P g) (fun j => cpow ζ (E g j).val)
  map_one := by
    rw [← monoMat_one]
    have e1 : P 1 = fun j => j := funext fun j => (h1 j).1
    have e2 : (fun j => cpow ζ (E 1 j).val) = fun _ => 1 :=
      funext fun j => by rw [(h1 j).2]; rfl
    rw [e1, e2]
  map_mul g h := by
    rw [monoMat_mul]
    have e1 : P (g * h) = fun j => P g (P h j) := funext fun j => (hmul g h j).1
    have e2 : (fun j => cpow ζ (E (g * h) j).val) =
        fun j => cpow ζ (E g (P h j)).val * cpow ζ (E h j).val :=
      funext fun j => by rw [(hmul g h j).2, cpow_fin_add hζ]
    rw [e1, e2]

/-- **The character of a monomial representation**: `χ(g) = Σ_j [P_g(j) = j] ζ^{E_g(j)}`. -/
theorem character_monoRep {G : Type u} [Group G] {m : Nat} (ζ : K) (hζ : cpow ζ m = 1)
    (P : G → Fin n → Fin n) (E : G → Fin n → Fin m) (h1) (hmul) (g : G) :
    character (monoRep ζ hζ P E h1 hmul) g = isum (fun j => kd j (P g j) * cpow ζ (E g j).val) :=
  rfl

/-! ## A primitive cube root of unity in `ℂ` -/

/-- `1 + z + z²` has a root in `ℂ` (fundamental theorem of algebra). -/
theorem exists_omega3 : ∃ ω : C, ω * ω + ω + 1 = 0 := by
  obtain ⟨z, hz⟩ := algClosed_complex 1 [1, 1] ⟨1, List.mem_cons_self, C.zero_ne_one.symm⟩
  refine ⟨z, ?_⟩
  have e : peval [(1 : C), 1, 1] z = 1 + z * (1 + z * (1 + z * 0)) := rfl
  rw [e] at hz
  grind

/-- **A primitive cube root of unity** `ω ∈ ℂ`, a chosen root of `1 + ω + ω² = 0`. -/
noncomputable def omega3 : C := Classical.choose exists_omega3

/-- `ω² + ω + 1 = 0`. -/
theorem omega3_spec : omega3 * omega3 + omega3 + 1 = 0 := Classical.choose_spec exists_omega3

/-- `ω³ = 1`. -/
theorem omega3_cube : cpow omega3 3 = 1 := by
  have h := omega3_spec
  show 1 * omega3 * omega3 * omega3 = 1
  grind

/-- `3 ≠ 0` in `ℂ`. -/
theorem three_ne_zero_C : (1 + 1 + 1 : C) ≠ 0 := by
  have := C.ncast_succ_ne_zero 2
  have e : (ncast 3 : C) = 1 + 1 + 1 := rfl
  rwa [e] at this

/-- `ω ≠ 1`. -/
theorem omega3_ne_one : omega3 ≠ 1 := by
  intro h
  have h' := omega3_spec
  rw [h] at h'
  exact three_ne_zero_C (by grind)

/-- `ω² ≠ 1`. -/
theorem omega3_sq_ne_one : omega3 * omega3 ≠ 1 := by
  intro h
  apply omega3_ne_one
  have h' := omega3_spec
  grind

/-- `ω ≠ ω²`. -/
theorem omega3_ne_sq : omega3 ≠ omega3 * omega3 := by
  intro h
  apply omega3_ne_one
  have h' := omega3_spec
  have hc := omega3_cube
  have hc' : 1 * omega3 * omega3 * omega3 = 1 := hc
  grind

/-- `-1` squares to `1`. -/
theorem neg_one_sq_C : cpow (-1 : C) 2 = 1 := by
  show 1 * (-1 : C) * (-1) = 1
  grind

end Foundations.Langlands
