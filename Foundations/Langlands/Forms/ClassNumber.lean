import Foundations.Langlands.Forms.Uniqueness

/-!
# Finiteness and class numbers

Reduction bounds the coefficients. If `f = (a, b, c)` is reduced with `D = b² − 4ac < 0`, then
`b² ≤ a² ≤ ac`, so

  `|D| = 4ac − b² ≥ 4a² − a² = 3a²`,  i.e. `a ≤ √(|D|/3)`  (`three_mul_sq_le`).

Given `D`, there are therefore only finitely many choices for `a`, then for `b` (`|b| ≤ a`),
and `c = (b² − D)/(4a)` is determined. Lagrange used exactly this to see that the number of
classes of each discriminant is finite; Gauss (*Disquisitiones*, art. 175 ff.) tabulated these
numbers. Following him we count **primitive** forms (`gcd(a, b, c) = 1`), since a
non-primitive form is an integer multiple of a form of smaller discriminant.

## What is defined and proved

* `candidates D` lists all triples `(a, b, (b² − D)/(4a))` with `0 ≤ 3a ≤ |D|`, `|b| ≤ a` — a
  crude but sufficient search space; `reducedForms D` keeps the reduced ones of discriminant
  `D`. For `D < 0` it contains **exactly** the reduced forms of discriminant `D`
  (`mem_reducedForms`) and has no repetitions (`reducedForms_nodup`).
* **Class number.** `classNumber D` is the number of primitive entries of `reducedForms D`.
  By `exists_reduced`, primitivity invariance (`content_act`) and `reduced_unique`, for
  `D < 0` the list `primReducedForms D` is a complete, irredundant system of representatives
  for proper equivalence classes of primitive positive definite forms of discriminant `D`
  (`primReducedForms_complete`, `primReducedForms_inequiv`), so `classNumber D` is the number of
  such classes.
* **Examples.** `h(−3) = 1`, `h(−4) = 1`, `h(−20) = 2`, `h(−23) = 3`, each with the explicit
  representatives and the class statements `classes_neg3`, `classes_neg4`, `classes_neg20`,
  `classes_neg23` (every positive definite form of that discriminant is equivalent to exactly
  one representative) (`reducedForms_neg20`: the classes of `x² + 5y²` and `2x² + 2xy + 3y²`;
  `reducedForms_neg23`: `x² + xy + 6y²` and `2x² ± xy + 3y²`). These are computed by `decide`
  in the kernel.

## Outlook (prose only)

Gauss composed classes of the same discriminant into a finite abelian group, the **class
group**, of order `h(D)`. Dirichlet's class number formula (1839) expresses `h(D)` through the
value at `s = 1` of an `L`-function; in the language of algebraic number theory, for
fundamental `D < 0` the class group of forms is the ideal class group of `ℚ(√D)`. Class field
theory (Hilbert, Takagi, Artin) identifies it with the Galois group of the **Hilbert class
field**, the maximal unramified abelian extension, and the primes represented by the principal
form are (apart from primes dividing `D`) those splitting completely there — e.g. for
`p ∤ 20`, `p = x² + 5y²` iff `p` splits completely in `ℚ(√−5, i)`. On the automorphic side,
reduced forms of discriminant `D` correspond to the CM points `τ_f ∈ F` of discriminant `D`,
and `j(τ_f)` generates the Hilbert class field (Kronecker's *Jugendtraum* for imaginary
quadratic fields). None of this is formalised here.
-/

namespace Foundations.Langlands.Forms

open Foundations.Algebra Foundations.Langlands.Modular

namespace Form

/-- **Gauss's bound.** A reduced form satisfies `3a² ≤ |D|`, i.e. `a ≤ √(|D|/3)`. -/
theorem three_mul_sq_le {f : Form} (hf : f.IsReduced) : 3 * (f.a * f.a) ≤ -f.disc := by
  have h1 : (f.b.natAbs : Int) ≤ f.a := hf.1
  have h2 := hf.2.1
  have hb : f.b * f.b ≤ f.a * f.a := by
    rw [← Int.natAbs_mul_self' f.b]
    exact Int.mul_le_mul h1 h1 (by omega) (by omega)
  have hc : f.a * f.a ≤ f.a * f.c := Int.mul_le_mul_of_nonneg_left h2 (by omega)
  have e : 4 * f.a * f.c = 4 * (f.a * f.c) := by grind
  unfold disc; omega

/-- The search space: triples `(a, b, (b² − D)/(4a))` with `0 ≤ 3a ≤ |D|` and `−a ≤ b ≤ a`. -/
def candidates (D : Int) : List Form :=
  (List.range (D.natAbs / 3 + 1)).flatMap fun (i : Nat) =>
    (List.range (2 * i + 1)).map fun (j : Nat) =>
      (⟨(i : Int), (j : Int) - i, (((j : Int) - i) * ((j : Int) - i) - D) / (4 * (i : Int))⟩ : Form)

/-- **The reduced forms of discriminant `D`**, as an explicit list. -/
def reducedForms (D : Int) : List Form :=
  (candidates D).filter fun f => decide (f.IsReduced ∧ f.disc = D)

/-- The primitive reduced forms of discriminant `D`. -/
def primReducedForms (D : Int) : List Form :=
  (reducedForms D).filter fun f => decide f.Primitive

/-- **Class number.** `h(D)` is the number of reduced primitive forms of discriminant `D`. -/
def classNumber (D : Int) : Nat := (primReducedForms D).length

/-- `a ≤ a²` for `a ≥ 1`. -/
theorem le_mul_self {a : Int} (ha : 1 ≤ a) : a ≤ a * a := by
  have := Int.mul_le_mul_of_nonneg_left ha (by omega : 0 ≤ a); omega

/-- **The list is complete.** For `D < 0`, `f ∈ reducedForms D` iff `f` is reduced of
discriminant `D`. -/
theorem mem_reducedForms {D : Int} (hD : D < 0) (f : Form) :
    f ∈ reducedForms D ↔ f.IsReduced ∧ f.disc = D := by
  unfold reducedForms
  rw [List.mem_filter, decide_eq_true_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨hf, hd⟩ := h
  have hpos : 0 < f.a := (hf.posDef (by omega)).2
  have h3 := three_mul_sq_le hf
  have hsq := le_mul_self (by omega : 1 ≤ f.a)
  have h1 : (f.b.natAbs : Int) ≤ f.a := hf.1
  unfold candidates
  rw [List.mem_flatMap]
  refine ⟨f.a.toNat, List.mem_range.2 (by omega), ?_⟩
  rw [List.mem_map]
  refine ⟨(f.b + f.a).toNat, List.mem_range.2 (by omega), ?_⟩
  have ea : ((f.a.toNat : Nat) : Int) = f.a := by omega
  have eb : (((f.b + f.a).toNat : Nat) : Int) - f.a = f.b := by omega
  rw [ea, eb]
  apply ext
  · rfl
  · rfl
  · show (f.b * f.b - D) / (4 * f.a) = f.c
    have e : f.b * f.b - D = 4 * f.a * f.c := by rw [← hd]; unfold disc; omega
    rw [e]; exact Int.mul_ediv_cancel_left _ (by omega)

/-- The search space has no repetitions. -/
theorem candidates_nodup (D : Int) : (candidates D).Nodup := by
  unfold candidates List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (List.nodup_range).imp fun hij heq => hij ?_
    have := congrArg Form.b heq; simp only at this; omega
  · refine (List.nodup_range).imp fun hij x hx y hy heq => hij ?_
    simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    have := congrArg Form.a heq; simp only at this; omega

/-- **No repetitions.** `reducedForms D` lists each reduced form at most once. -/
theorem reducedForms_nodup (D : Int) : (reducedForms D).Nodup :=
  (candidates_nodup D).filter _

/-- `primReducedForms D` has no repetitions. -/
theorem primReducedForms_nodup (D : Int) : (primReducedForms D).Nodup :=
  (reducedForms_nodup D).filter _

/-- Membership in `primReducedForms D` for `D < 0`: reduced, discriminant `D`, primitive. -/
theorem mem_primReducedForms {D : Int} (hD : D < 0) (f : Form) :
    f ∈ primReducedForms D ↔ f.IsReduced ∧ f.disc = D ∧ f.Primitive := by
  unfold primReducedForms
  rw [List.mem_filter, mem_reducedForms hD, decide_eq_true_iff, and_assoc]

/-- **Completeness of the representatives.** For `D < 0`, every primitive positive definite
form of discriminant `D` is properly equivalent to a form in `primReducedForms D`. -/
theorem primReducedForms_complete {D : Int} (hD : D < 0) (f : Form) (hf : f.PosDef)
    (hd : f.disc = D) (hp : f.Primitive) : ∃ g ∈ primReducedForms D, Equiv f g := by
  obtain ⟨g, eg, hg⟩ := exists_reduced f hf
  refine ⟨g, (mem_primReducedForms hD g).2 ⟨hg, ?_, eg.primitive_iff.1 hp⟩, eg⟩
  rw [← eg.disc_eq, hd]

/-- **Irredundancy of the representatives.** Two properly equivalent entries of
`primReducedForms D` (for `D < 0`) are equal. -/
theorem primReducedForms_inequiv {D : Int} (hD : D < 0) {g g' : Form}
    (hg : g ∈ primReducedForms D) (hg' : g' ∈ primReducedForms D) (h : Equiv g g') : g = g' := by
  obtain ⟨r, d, _⟩ := (mem_primReducedForms hD g).1 hg
  obtain ⟨r', _, _⟩ := (mem_primReducedForms hD g').1 hg'
  exact reduced_unique r r' (by omega) h

/-- **The class number counts classes.** For `D < 0`, `h(D)` is the length of a duplicate-free
list of primitive positive definite forms of discriminant `D` such that every primitive
positive definite form of discriminant `D` is properly equivalent to exactly one entry. -/
theorem classNumber_spec {D : Int} (hD : D < 0) :
    classNumber D = (primReducedForms D).length ∧ (primReducedForms D).Nodup ∧
      (∀ g ∈ primReducedForms D, g.PosDef ∧ g.disc = D ∧ g.Primitive) ∧
      (∀ f : Form, f.PosDef → f.disc = D → f.Primitive →
        ∃ g ∈ primReducedForms D, Equiv f g ∧
          ∀ g' ∈ primReducedForms D, Equiv f g' → g' = g) := by
  refine ⟨rfl, primReducedForms_nodup D, fun g hg => ?_, fun f hf hd hp => ?_⟩
  · obtain ⟨r, d, p⟩ := (mem_primReducedForms hD g).1 hg
    exact ⟨r.posDef (by omega), d, p⟩
  · obtain ⟨g, hg, eg⟩ := primReducedForms_complete hD f hf hd hp
    exact ⟨g, hg, eg, fun g' hg' eg' =>
      primReducedForms_inequiv hD hg' hg (eg'.symm.trans eg)⟩

/-! ## Computed examples -/

/-- The reduced forms of discriminant `−3`: only `x² + xy + y²`. -/
theorem reducedForms_neg3 : reducedForms (-3) = [⟨1, 1, 1⟩] := by decide

/-- The reduced forms of discriminant `−4`: only `x² + y²`. -/
theorem reducedForms_neg4 : reducedForms (-4) = [⟨1, 0, 1⟩] := by decide

/-- The reduced forms of discriminant `−20`: `x² + 5y²` and `2x² + 2xy + 3y²`. -/
theorem reducedForms_neg20 : reducedForms (-20) = [⟨1, 0, 5⟩, ⟨2, 2, 3⟩] := by decide

/-- The reduced forms of discriminant `−23`: `x² + xy + 6y²`, `2x² − xy + 3y²`,
`2x² + xy + 3y²`. -/
theorem reducedForms_neg23 : reducedForms (-23) = [⟨1, 1, 6⟩, ⟨2, -1, 3⟩, ⟨2, 1, 3⟩] := by
  decide

/-- **h(−3) = 1.** -/
theorem classNumber_neg3 : classNumber (-3) = 1 := by decide

/-- **h(−4) = 1.** -/
theorem classNumber_neg4 : classNumber (-4) = 1 := by decide

/-- **h(−20) = 2.** -/
theorem classNumber_neg20 : classNumber (-20) = 2 := by decide

/-- **h(−23) = 3.** -/
theorem classNumber_neg23 : classNumber (-23) = 3 := by decide

/-- **Two classes of discriminant −20.** Every positive definite form of discriminant `−20` is
properly equivalent to exactly one of `x² + 5y²` and `2x² + 2xy + 3y²`. (No primitivity
hypothesis is needed: these are the only reduced forms of discriminant `−20`.) -/
theorem classes_neg20 (f : Form) (hf : f.PosDef) (hd : f.disc = -20) :
    (Equiv f ⟨1, 0, 5⟩ ∨ Equiv f ⟨2, 2, 3⟩) ∧ ¬ (Equiv f ⟨1, 0, 5⟩ ∧ Equiv f ⟨2, 2, 3⟩) := by
  obtain ⟨g, eg, hg⟩ := exists_reduced f hf
  have hgd : g.disc = -20 := by rw [← eg.disc_eq, hd]
  have hm : g ∈ reducedForms (-20) := (mem_reducedForms (by decide) g).2 ⟨hg, hgd⟩
  rw [reducedForms_neg20] at hm
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Or.inl eg
    · exact Or.inr eg
  · have := reduced_unique (f := ⟨1, 0, 5⟩) (g := ⟨2, 2, 3⟩) (by decide) (by decide) (by decide)
      (h1.symm.trans h2)
    simp at this

/-- Every positive definite form of discriminant `D < 0` is properly equivalent to an entry of
`reducedForms D`. -/
theorem exists_mem_reducedForms {D : Int} (hD : D < 0) (f : Form) (hf : f.PosDef)
    (hd : f.disc = D) : ∃ g ∈ reducedForms D, Equiv f g := by
  obtain ⟨g, eg, hg⟩ := exists_reduced f hf
  exact ⟨g, (mem_reducedForms hD g).2 ⟨hg, by rw [← eg.disc_eq, hd]⟩, eg⟩

/-- **One class of discriminant −3.** Every positive definite form of discriminant `−3` is
properly equivalent to `x² + xy + y²`. -/
theorem classes_neg3 (f : Form) (hf : f.PosDef) (hd : f.disc = -3) : Equiv f ⟨1, 1, 1⟩ := by
  obtain ⟨g, hg, eg⟩ := exists_mem_reducedForms (by decide) f hf hd
  rw [reducedForms_neg3] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rw [hg] at eg; exact eg

/-- **One class of discriminant −4.** Every positive definite form of discriminant `−4` is
properly equivalent to `x² + y²`. -/
theorem classes_neg4 (f : Form) (hf : f.PosDef) (hd : f.disc = -4) : Equiv f ⟨1, 0, 1⟩ := by
  obtain ⟨g, hg, eg⟩ := exists_mem_reducedForms (by decide) f hf hd
  rw [reducedForms_neg4] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rw [hg] at eg; exact eg

/-- **Three classes of discriminant −23.** Every positive definite form of discriminant `−23`
is properly equivalent to one of `x² + xy + 6y²`, `2x² − xy + 3y²`, `2x² + xy + 3y²`, and these
three are pairwise properly inequivalent. (The last two are exchanged by `y ↦ −y`, which has
determinant `−1`: this is Gauss's distinction between proper and improper equivalence.) -/
theorem classes_neg23 (f : Form) (hf : f.PosDef) (hd : f.disc = -23) :
    (Equiv f ⟨1, 1, 6⟩ ∨ Equiv f ⟨2, -1, 3⟩ ∨ Equiv f ⟨2, 1, 3⟩) ∧
      ¬ Equiv ⟨1, 1, 6⟩ ⟨2, -1, 3⟩ ∧ ¬ Equiv ⟨1, 1, 6⟩ ⟨2, 1, 3⟩ ∧
      ¬ Equiv ⟨2, -1, 3⟩ ⟨2, 1, 3⟩ := by
  obtain ⟨g, hg, eg⟩ := exists_mem_reducedForms (by decide) f hf hd
  rw [reducedForms_neg23] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases hg with rfl | rfl | rfl
    · exact Or.inl eg
    · exact Or.inr (Or.inl eg)
    · exact Or.inr (Or.inr eg)
  · have := reduced_unique (by decide) (by decide) (by decide) h; simp at this
  · have := reduced_unique (by decide) (by decide) (by decide) h; simp at this
  · have := reduced_unique (by decide) (by decide) (by decide) h; simp at this

end Form

end Foundations.Langlands.Forms
