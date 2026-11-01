import Foundations.Algebra.Lagrange
import Foundations.Numbers.ComplexModulus

/-!
# Characters of finite abelian groups

To isolate the primes `p ≡ a (mod q)` among all primes, Dirichlet (1837) needed a way to pick
out one residue class by *averaging*. His device, which became one of the great organising ideas
of modern mathematics, is the **character**: a homomorphism `χ : G → ℂ` from a finite abelian
group (for him, the units modulo `q`) into the non-zero complex numbers. Characters behave like
the exponentials `e^{2πikx/n}` of Fourier analysis, and the identity Dirichlet exploited is the
**orthogonality relation**

  `Σ_χ χ(a) · χ(b)⁻¹ = |G|` if `a = b`, and `0` otherwise,

which turns the indicator of a single element into a linear combination of characters. The set
`Ĝ` of characters is itself a group, the *dual group*; this is the first instance of the duality
between a group and its characters that Pontryagin, Weyl and Tate later made central to harmonic
analysis and number theory.

The orthogonality relation rests on the fact that there are **enough** characters to tell the
elements apart. We prove this without the structure theorem for finite abelian groups, by
*extending characters one generator at a time*: if `H` is a subgroup, `g ∉ H`, and `m ≥ 1` is the
least exponent with `gᵐ ∈ H`, then every character `χ` of `H` extends to `⟨H, g⟩` in
`m` ways — choose an `m`-th root `w` of `χ(gᵐ)` and send `g` to `w·ζʲ`, `ζ` a primitive `m`-th
root of unity. Running through all these choices and using `Σ_{j<m} ζ^{jk} = m·[m ∣ k]`,
orthogonality propagates from `H` to `⟨H, g⟩`. Starting from the trivial subgroup we reach all
of `G` and obtain a list of characters satisfying orthogonality; it then follows that this list
contains *every* character, so `Ĝ` is finite, `|Ĝ| = |G|`, and both orthogonality relations hold.

The roots of unity come from the polar form of Part II: `ζ = cos (2π/m) + i sin (2π/m)`.
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Algebra.FiniteType Foundations.Numbers Foundations.Numbers.C
open Foundations.Numbers.R Lean.Grind OF

universe u v

/-! ## Finite sums of complex numbers over lists -/

/-- The sum `Σ_{a ∈ l} f a` of complex numbers indexed by the entries of a list. -/
noncomputable def lsum {α : Type u} (l : List α) (f : α → C) : C := l.foldr (fun a s => f a + s) 0

section LSum

variable {α : Type u}

/-- The empty sum is zero. -/
@[simp] theorem lsum_nil (f : α → C) : lsum [] f = 0 := rfl

/-- Sum over a list with a first entry. -/
@[simp] theorem lsum_cons (a : α) (l : List α) (f : α → C) : lsum (a :: l) f = f a + lsum l f :=
  rfl

/-- Sums over a concatenation add. -/
theorem lsum_append (l₁ l₂ : List α) (f : α → C) : lsum (l₁ ++ l₂) f = lsum l₁ f + lsum l₂ f := by
  induction l₁ with
  | nil => show lsum l₂ f = 0 + lsum l₂ f; grind
  | cons a l ih => rw [List.cons_append, lsum_cons, lsum_cons, ih]; grind

/-- Sums only depend on the values at the listed entries. -/
theorem lsum_congr {l : List α} {f g : α → C} (h : ∀ a ∈ l, f a = g a) : lsum l f = lsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [lsum_cons, lsum_cons, h a (List.mem_cons_self), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- Sums are additive in the summand. -/
theorem lsum_add (l : List α) (f g : α → C) : lsum l (fun a => f a + g a) = lsum l f + lsum l g := by
  induction l with
  | nil => show (0 : C) = 0 + 0; grind
  | cons a l ih => rw [lsum_cons, lsum_cons, lsum_cons, ih]; grind

/-- Constants factor out of sums. -/
theorem lsum_mul_left (c : C) (l : List α) (f : α → C) : lsum l (fun a => c * f a) = c * lsum l f := by
  induction l with
  | nil => show (0 : C) = c * 0; grind
  | cons a l ih => rw [lsum_cons, lsum_cons, ih]; grind

/-- The sum of zeros is zero. -/
theorem lsum_zero (l : List α) : lsum l (fun _ => (0 : C)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [lsum_cons, ih]; grind

/-- The sum of a constant is the length times the constant. -/
theorem lsum_const (l : List α) (c : C) : lsum l (fun _ => c) = (l.length : C) * c := by
  induction l with
  | nil => show (0 : C) = ((0 : Nat) : C) * c; grind
  | cons a l ih =>
    rw [lsum_cons, ih, List.length_cons]
    have : ((l.length + 1 : Nat) : C) = (l.length : C) + 1 := by grind
    rw [this]; grind

/-- Summing over a mapped list. -/
theorem lsum_map {β : Type v} (l : List α) (e : α → β) (f : β → C) :
    lsum (l.map e) f = lsum l (fun a => f (e a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, lsum_cons, lsum_cons, ih]

/-- Summing over a flattened list of lists. -/
theorem lsum_flatMap {β : Type v} (l : List α) (e : α → List β) (f : β → C) :
    lsum (l.flatMap e) f = lsum l (fun a => lsum (e a) f) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, lsum_append, lsum_cons, ih]

/-- **Sums are invariant under permutation** of the list. -/
theorem lsum_perm {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → C) : lsum l₁ f = lsum l₂ f :=
  List.Perm.foldr_eq' h (fun _ _ _ _ _ => by grind) 0

/-- **Interchanging a double sum.** -/
theorem lsum_comm {β : Type v} (l₁ : List α) (l₂ : List β) (F : α → β → C) :
    lsum l₁ (fun a => lsum l₂ (fun b => F a b)) = lsum l₂ (fun b => lsum l₁ (fun a => F a b)) := by
  induction l₁ with
  | nil => rw [lsum_nil]; exact (lsum_zero l₂).symm
  | cons a l ih =>
    rw [lsum_cons, ih]
    show _ = lsum l₂ (fun b => F a b + lsum l (fun a => F a b))
    rw [lsum_add]

/-- The real part of a sum is the sum of the real parts. -/
theorem lsum_re (l : List α) (f : α → C) : (lsum l f).re = l.foldr (fun a s => (f a).re + s) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [lsum_cons, add_re, ih]; rfl

/-- Conjugation commutes with sums. -/
theorem conj_lsum (l : List α) (f : α → C) : conj (lsum l f) = lsum l (fun a => conj (f a)) := by
  induction l with
  | nil => apply ext <;> simp [lsum_nil]; grind
  | cons a l ih => rw [lsum_cons, lsum_cons, conj_add, ih]

end LSum

/-! ## Sums over a finite type -/

section SumOver

variable {α : Type u} [FiniteType α]

/-- The sum `Σ_{x : α} f x` over all elements of a finite type. -/
noncomputable def sumOver (f : α → C) : C := lsum (FiniteType.elems : List α) f

/-- **Reindexing.** Summing `f ∘ e` over a finite type, for an injective `e`, gives the same as
summing `f`: an injective self-map of a finite type is a permutation. -/
theorem sumOver_comp_injective (e : α → α) (he : ∀ a b, e a = e b → a = b) (f : α → C) :
    sumOver (fun a => f (e a)) = sumOver f := by
  unfold sumOver
  rw [← lsum_map]
  apply lsum_perm
  rw [List.perm_ext_iff_of_nodup (nodup_map_of_injective he FiniteType.nodup) FiniteType.nodup]
  intro x
  constructor
  · intro _; exact FiniteType.complete x
  · intro _
    obtain ⟨y, hy⟩ := surjective_of_injective e he x
    rw [List.mem_map]; exact ⟨y, FiniteType.complete y, hy⟩

/-- A sum over a finite type in which only the term at `a` can be non-zero. -/
theorem sumOver_single (a : α) (f : α → C) (h : ∀ x, x ≠ a → f x = 0) : sumOver f = f a := by
  unfold sumOver
  have hmem := FiniteType.complete a
  have hnd := (FiniteType.nodup : (FiniteType.elems : List α).Nodup)
  generalize (FiniteType.elems : List α) = l at hmem hnd
  induction l with
  | nil => cases hmem
  | cons b l ih =>
    rw [lsum_cons]
    rw [List.nodup_cons] at hnd
    by_cases hb : b = a
    · subst hb
      have : lsum l f = 0 := by
        rw [lsum_congr (g := fun _ => 0) (fun x hx => h x (fun e => hnd.1 (e ▸ hx)))]
        exact lsum_zero l
      rw [this]; grind
    · rw [h b hb, ih (by cases hmem with | head => exact absurd rfl hb | tail _ h => exact h) hnd.2]
      grind

end SumOver

/-! ## Powers and roots of unity -/

/-- Exponent law `z^(a+b) = z^a z^b` in `C`. -/
theorem cpow_add (z : C) (a b : Nat) : z ^ (a + b) = z ^ a * z ^ b := by
  induction b with
  | zero => show z ^ a = z ^ a * 1; grind
  | succ b ih => show z ^ (a + b) * z = z ^ a * (z ^ b * z); rw [ih]; grind

/-- Exponent law `z^(a b) = (z^a)^b` in `C`. -/
theorem cpow_mul (z : C) (a b : Nat) : z ^ (a * b) = (z ^ a) ^ b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.mul_succ, cpow_add, ih]; rfl

/-- `1^k = 1` in `C`. -/
theorem cone_pow (k : Nat) : (1 : C) ^ k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => show (1 : C) ^ k * 1 = 1; rw [ih]; grind

/-- The primitive `m`-th root of unity `ζₘ = cos (2π/m) + i sin (2π/m)`. -/
noncomputable def zeta (m : Nat) : C := cis (2 * pi / (m : R))

/-- `ζₘ^k = cos (2πk/m) + i sin (2πk/m)`. -/
theorem zeta_pow (m k : Nat) : zeta m ^ k = cis ((k : R) * (2 * pi / (m : R))) := cis_pow _ _

/-- `ζₘ^m = 1`. -/
theorem zeta_pow_self {m : Nat} (hm : 1 ≤ m) : zeta m ^ m = 1 := by
  rw [zeta_pow]
  have hm' : (0 : R) < (m : R) := OrderedRing.pos_natCast_of_pos _ (by omega)
  rw [show (m : R) * (2 * pi / (m : R)) = 2 * pi by grind]
  apply ext
  · show cos (2 * pi) = 1; exact cos_two_pi
  · show sin (2 * pi) = 0; exact sin_two_pi

/-- `ζₘ^k ≠ 1` for `0 < k < m`: `ζₘ` is a *primitive* `m`-th root of unity. -/
theorem zeta_pow_ne_one {m k : Nat} (hk0 : 0 < k) (hkm : k < m) : zeta m ^ k ≠ 1 := by
  intro h
  rw [zeta_pow] at h
  have hc : cos ((k : R) * (2 * pi / (m : R))) = 1 := congrArg C.re h
  have hs : sin ((k : R) * (2 * pi / (m : R))) = 0 := congrArg C.im h
  have hm' : (0 : R) < (m : R) := OrderedRing.pos_natCast_of_pos _ (by omega)
  have hk' : (0 : R) < (k : R) := OrderedRing.pos_natCast_of_pos _ hk0
  have hkm' : (k : R) < (m : R) := by
    have := OrderedRing.pos_natCast_of_pos (R := R) (m - k) (by omega)
    have e : ((m - k : Nat) : R) = (m : R) - (k : R) := by
      rw [show m = (m - k) + k from by omega]; rw [Nat.add_sub_cancel]; grind
    grind
  have hpi := pi_pos
  have ht : 0 < 2 * pi / (m : R) := div_pos (show (0 : R) < 2 * pi by grind) hm'
  have hmt : (m : R) * (2 * pi / (m : R)) = 2 * pi := by
    have : (m : R) ≠ 0 := by grind
    grind
  generalize ht' : 2 * pi / (m : R) = t at hc hs ht hmt
  have hθ0 : 0 < (k : R) * t := OrderedRing.mul_pos hk' ht
  have hθ2 : (k : R) * t < 2 * pi := by
    have := OrderedRing.mul_lt_mul_of_pos_left hkm' ht
    grind
  generalize (k : R) * t = θ at hc hs hθ0 hθ2
  rcases (by grind : θ < pi ∨ θ = pi ∨ pi < θ) with h1 | h1 | h1
  · have := sin_pos_of_pos_of_lt_pi hθ0 h1; grind
  · rw [h1, cos_pi] at hc; grind
  · have := sin_pos_of_pos_of_lt_pi (x := θ - pi) (by grind) (by grind)
    have e := sin_add_pi (θ - pi)
    rw [show θ - pi + pi = θ by grind] at e
    grind

/-- **Geometric sums of roots of unity.** If `uᵐ = 1` and `u ≠ 1` then `1 + u + ⋯ + u^{m−1} = 0`. -/
theorem lsum_pow_eq_zero {u : C} {m : Nat} (hm : u ^ m = 1) (hu : u ≠ 1) :
    lsum (List.range m) (fun j => u ^ j) = 0 := by
  -- `u · S = S`, because multiplying by `u` shifts the terms cyclically.
  have shift : ∀ n, u * lsum (List.range n) (fun j => u ^ j) + 1 =
      lsum (List.range n) (fun j => u ^ j) + u ^ n := by
    intro n
    induction n with
    | zero => show u * 0 + 1 = 0 + 1; grind
    | succ n ih =>
      rw [List.range_succ, lsum_append, lsum_cons, lsum_nil]
      show u * (lsum (List.range n) (fun j => u ^ j) + (u ^ n + 0)) + 1 =
        lsum (List.range n) (fun j => u ^ j) + (u ^ n + 0) + u ^ n * u
      grind
  have h := shift m
  rw [hm] at h
  have h2 : (u - 1) * lsum (List.range m) (fun j => u ^ j) = 0 := by grind
  have hu' : u - 1 ≠ 0 := fun e => hu (by grind)
  calc lsum (List.range m) (fun j => u ^ j)
      = (u - 1)⁻¹ * ((u - 1) * lsum (List.range m) (fun j => u ^ j)) := by
        rw [← Semiring.mul_assoc, Field.inv_mul_cancel hu', Semiring.one_mul]
    _ = 0 := by rw [h2]; grind

/-- `Σ_{j<m} (ζₘ^j)^k = m` if `m ∣ k` and `0` otherwise. -/
theorem lsum_zeta_pow {m : Nat} (hm : 1 ≤ m) (k : Nat) :
    lsum (List.range m) (fun j => (zeta m ^ j) ^ k) = if m ∣ k then (m : C) else 0 := by
  have e : ∀ j : Nat, (zeta m ^ j) ^ k = (zeta m ^ k) ^ j := by
    intro j; rw [← cpow_mul, ← cpow_mul, Nat.mul_comm]
  rw [lsum_congr (g := fun j : Nat => (zeta m ^ k) ^ j) (fun j _ => e j)]
  have hum : (zeta m ^ k) ^ m = 1 := by
    rw [← cpow_mul, Nat.mul_comm, cpow_mul, zeta_pow_self hm, cone_pow]
  split
  · next hd =>
    obtain ⟨s, rfl⟩ := hd
    rw [cpow_mul, zeta_pow_self hm, cone_pow]
    rw [lsum_congr (g := fun _ : Nat => (1 : C)) (fun j _ => cone_pow j), lsum_const, List.length_range]
    grind
  · next hd =>
    apply lsum_pow_eq_zero hum
    intro h1
    have hk : zeta m ^ k = zeta m ^ (k % m) := by
      conv => lhs; rw [← Nat.div_add_mod k m]
      rw [cpow_add, cpow_mul, zeta_pow_self hm, cone_pow]; grind
    have hpos : 0 < k % m := by
      rcases Nat.eq_zero_or_pos (k % m) with h0 | h0
      · exact absurd (Nat.dvd_of_mod_eq_zero h0) hd
      · exact h0
    exact zeta_pow_ne_one hpos (Nat.mod_lt _ (by omega)) (hk ▸ h1)

end Foundations.NumberTheory
