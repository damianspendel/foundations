# Exercises

A graded problem set on top of the Foundations library: 62 exercises in nine sets, one per
part of the library, for a reader who already knows some Lean 4. Every exercise is a single
theorem about the library's own definitions (its ZF sets, its real numbers, its Hilbert system,
its λ-calculus, its categories, …), so working through it is also a guided tour of the library.

The exercises live outside the library, in `Exercises/`. They are not part of the default
build, the dependency graph or the website.

## Layout

| Path | Contents |
|------|----------|
| `Exercises/Problems/<Part>.lean` | Student files: statements, hints and `sorry`. **Work here.** |
| `Exercises/Solutions/<Part>.lean` | The same files with full proofs. |
| `Exercises/Solutions.lean` | Imports all solution files. |
| `scripts/make_exercises.py` | Generates `Problems/` from `Solutions/`. |

Each exercise's docstring gives:

- the statement in plain words,
- a **hint**,
- **Uses:** the library results it relies on. Type these names into the search box on the
  site, or `#check` them, to see their exact statements.

### Grades

- ★: a one-liner that applies a library lemma. The work is finding the right lemma and
  instantiating it.
- ★★: a short proof of a few lines: an induction, an ε-argument, a typing derivation, a
  calculation.
- ★★★: a small project, for example re-proving a library fact by a different route, proving a
  corollary that the library does not state, or proving an auxiliary lemma by induction first.

## How to work through the set

1. Build the library once (`lake build`). Every `.olean` the exercises need comes from this
   build.
2. Open `Exercises/Problems/<Part>.lean` in your editor and replace each `sorry` with a proof.
   You can also check a file from the command line:

   ```
   lake env lean Exercises/Problems/Sets.lean
   ```

   You get one "declaration uses sorry" warning for each exercise you have not done yet.
   When your file elaborates with no errors and no warnings, you have solved the whole set.
3. To make sure that a proof does not rely on `sorry` or on extra axioms, add a line such as
   `#print axioms Exercises.Sets.diagonal_nat` at the end of the file. The answer should list
   only some of `propext`, `Classical.choice` and `Quot.sound`. If it lists `sorryAx`, part of
   the proof is still missing.
4. Compare with `Exercises/Solutions/<Part>.lean` when you are done or stuck. The solutions are
   one possible proof each; many others work.

The parts are independent, but within a part the exercises are roughly in order of
difficulty, and a later exercise sometimes reuses the idea of an earlier one.

### Rules of the game

Use only core Lean and the library: no Mathlib. Avoid `native_decide`, since it adds an axiom.
`decide`, `omega`, `simp` and `grind` are all fine. `grind` is particularly strong on the
library's real numbers, which are registered as an ordered field.

## Table of exercises

The numbering follows the library's parts: I Sets, II Numbers, III Logic, IV Algebra,
V Types, VI Geometry, VII Categories, VIII Topology. Set 9 covers number theory, which draws on
Parts II, IV and XII.

| # | ★ | Exercise | Lean name |
|---|---|----------|-----------|
| **1** | | **Sets** (`Exercises.Sets`) | |
| 1.1 | ★ | The grid ℕ × ℕ is countable | `countable_nat_prod` |
| 1.2 | ★★ | The diagonal argument for number sequences | `diagonal_nat` |
| 1.3 | ★★ | Two copies of ℕ are no bigger than one (Schröder–Bernstein) | `sum_nat_equinum_nat` |
| 1.4 | ★★ | No ZF set is its own successor | `succ_ne_self` |
| 1.5 | ★★ | No membership triangles x ∈ y ∈ z ∈ x (∈-induction) | `no_mem_cycle3` |
| 1.6 | ★★ | Lists of bits are infinite | `list_bool_infinite` |
| 1.7 | ★★★ | Binary sequences cannot be numbered: every map to ℕ has a collision | `collision_of_nat_bool` |
| **2** | | **Numbers** (`Exercises.Numbers`) | |
| 2.1 | ★★ | No Peano number is its own successor (induction) | `succ_ne_self` |
| 2.2 | ★★ | One is a left unit for Peano multiplication | `one_mul'` |
| 2.3 | ★★ | An ε-δ proof: y ↦ 3y + 1 is continuous | `continuousAt_affine` |
| 2.4 | ★★ | 1/(n+1) → 0 | `tendsto_one_div_succ` |
| 2.5 | ★★★ | The squeeze theorem | `squeeze` |
| 2.6 | ★ | A cube root of 5 | `exists_cube_root_five` |
| 2.7 | ★★★ | Every continuous self-map of [0, 1] has a fixed point | `fixed_point_unit_interval` |
| **3** | | **Logic** (`Exercises.Logic`) | |
| 3.1 | ★★ | Hypothetical syllogism in the Hilbert system, from K and S | `hilbert_imp_trans` |
| 3.2 | ★★ | Double-negation introduction in the Hilbert system | `hilbert_dni` |
| 3.3 | ★★★ | The converse of the deduction theorem (with Hilbert weakening) | `hilbert_undeduction` |
| 3.4 | ★★ | The Hilbert system is consistent | `hilbert_consistent` |
| 3.5 | ★★ | p₀ → p₁ is not derivable | `hilbert_not_imp` |
| 3.6 | ★ | Peirce's law, by completeness and truth tables | `peirce` |
| 3.7 | ★★ | Hilbert proofs use finitely many premises | `finite_hilbert_proof` |
| **4** | | **Algebra** (`Exercises.Algebra`) | |
| 4.1 | ★ | (abc)⁻¹ = c⁻¹b⁻¹a⁻¹ | `mul_inv_rev3` |
| 4.2 | ★★ | If x² = 1 for all x, the group is commutative | `comm_of_sq_eq_one` |
| 4.3 | ★★ | (gag⁻¹)ⁿ = gaⁿg⁻¹ | `conj_pow` |
| 4.4 | ★★★ | (ab)ⁿ = 1 implies (ba)ⁿ = 1 | `pow_mul_comm_eq_one` |
| 4.5 | ★ | Equal images under a homomorphism differ by the kernel | `inv_mul_mem_ker` |
| 4.6 | ★★ | A transposition is an involution | `swap_mul_self` |
| 4.7 | ★ | genⁿ = 1 in ℤ/nℤ | `gen_pow_n` |
| **5** | | **Types** (`Exercises.Types`) | |
| 5.1 | ★★ | Typing derivation: λg f x. g (f x) : (B→C)→(A→B)→A→C | `typing_compose` |
| 5.2 | ★★ | Typing derivation: swapping a pair | `typing_swap` |
| 5.3 | ★★ | Typing derivation: swapping a sum | `typing_sum_swap` |
| 5.4 | ★ | β-reduction preserves types | `typing_beta` |
| 5.5 | ★★★ | No closed normal term of type ⊥ | `no_normal_bot` |
| 5.6 | ★★ | csucc (csucc n̄) reduces to the numeral for n + 2 | `csucc_csucc_church` |
| 5.7 | ★★ | Ω never reduces to a Church numeral | `omega_not_church` |
| **6** | | **Geometry** (`Exercises.Geometry`) | |
| 6.1 | ★ | ab ≡ cd implies ba ≡ dc (Tarski) | `cong_comm_both` |
| 6.2 | ★★ | A Tarski plane has three distinct points | `exists_three_distinct` |
| 6.3 | ★★ | Apollonius' median formula | `apollonius` |
| 6.4 | ★★ | The median to the hypotenuse is half the hypotenuse | `median_hypotenuse` |
| 6.5 | ★★★ | The reverse triangle inequality in ℝ² | `reverse_triangle` |
| 6.6 | ★★ | No rational point on the x-axis at squared distance 12 from 0 | `no_rat_point_sq_dist_12` |
| **7** | | **Categories** (`Exercises.Categories`) | |
| 7.1 | ★★ | Inverses are unique | `inverse_unique` |
| 7.2 | ★★ | Isomorphisms can be cancelled | `iso_cancel_left` |
| 7.3 | ★ | Endo-transformations of Hom(A, −) are pre-compositions (Yoneda) | `homFunctor_endo` |
| 7.4 | ★ | A transformation out of Hom(A, −) is determined by its value at 𝟙 | `nat_trans_ext_id` |
| 7.5 | ★★ | The Yoneda principle: f ≫ h = g ≫ h for all h gives f = g | `eq_of_comp_eq` |
| 7.6 | ★★★ | Isomorphic objects have isomorphic hom-functors | `homFunctor_iso_of_iso` |
| 7.7 | ★★ | No surjection A → (A → ℕ), by Lawvere | `no_surjection_nat` |
| **8** | | **Topology** (`Exercises.Topology`) | |
| 8.1 | ★★ | Finite sets are compact | `isCompact_list` |
| 8.2 | ★★ | The union of two compact sets is compact | `IsCompact.union'` |
| 8.3 | ★★★ | A closed subset of a compact set is compact | `IsCompact.inter_closed` |
| 8.4 | ★★ | In the indiscrete topology every set is compact | `isCompact_indiscrete` |
| 8.5 | ★★ | The image of [0, 1] under x ↦ x² is compact | `isCompact_square_image` |
| 8.6 | ★ | Convergent sequences in a discrete space are eventually constant | `converges_discrete` |
| 8.7 | ★★ | x ↦ 2x + 1 is continuous on ℝ, via Lipschitz | `continuous_two_mul_add_one` |
| **9** | | **Number theory** (`Exercises.NumberTheory`) | |
| 9.1 | ★★ | Squares are 0 or 1 mod 4 | `sq_mod_four` |
| 9.2 | ★★ | x² + y² is never 3 mod 4 | `sum_two_sq_mod_four` |
| 9.3 | ★★★ | Fermat: aᵖ ≡ a (mod p) for all a | `pow_prime_mod` |
| 9.4 | ★★★ | p ∣ C(p, k) for 0 < k < p | `prime_dvd_choose` |
| 9.5 | ★ | Primes ≡ 3 (mod 4) are unbounded | `primes_mod_four_unbounded` |
| 9.6 | ★ | There is a prime between 100 and 200 | `prime_between_100_200` |
| 9.7 | ★ | gcd(a, b) divides a + b | `gcd_dvd_add` |

Totals: 62 exercises (14 ★, 37 ★★, 11 ★★★).

## For maintainers

### Building and checking

```
lake build Exercises                       # all solution files (the lean_lib `Exercises`)
lake build Exercises.Solutions.Topology    # one part
python3 scripts/make_exercises.py --lean   # regenerate Problems/ and elaborate each file
python3 scripts/make_exercises.py --check  # fail if Problems/ is out of date
```

The `Exercises` library in `lakefile.toml` only covers `Exercises.Solutions.*`, and it is not a
default target. As a result, plain `lake build`, the extractor (`lake exe extract Foundations
Foundations`) and `scripts/check_axioms.py`, which only scans `Foundations/`, never see the
exercises. Because the problem files contain `sorry` by design, they are checked with
`lake env lean`, not built.

The solution files contain no `sorry`, `axiom` or `native_decide`, and every theorem in them
depends only on `propext`, `Classical.choice` and `Quot.sound`.

### Marker scheme

In a solution file, each proof is wrapped like this:

```lean
theorem diagonal_nat (f : Nat → (Nat → Nat)) : ∃ g : Nat → Nat, ∀ n, f n ≠ g := by
  -- SOLUTION
  refine ⟨fun n => f n n + 1, fun n h => ?_⟩
  ...
  -- END
```

`scripts/make_exercises.py` replaces each block, markers included, with a single `sorry`
indented like the `-- SOLUTION` line. Everything else is copied verbatim, with a "generated"
banner added at the top. The script rejects a file if:

- a block is nested or left unclosed,
- the line before a block does not end in `:= by`,
- the number of `-- SOLUTION` blocks differs from the number of `theorem`s. This guarantees that
  no worked proof leaks into a problem file.

To add an exercise:

1. Write the theorem with its docstring and marked proof in the solution file.
2. Run `python3 scripts/make_exercises.py --lean`.
3. Add a row to the table above.

Do not edit the files in `Problems/` by hand.
