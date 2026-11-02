# Exercises

A graded problem set on top of the Foundations library: 94 exercises in fourteen sets, covering
most parts of the library, for a reader who already knows some Lean 4. Every exercise is a single
theorem about the library's own definitions (its ZF sets, its real numbers, its Hilbert system,
its λ-calculus, its categories, its Boolean-valued models, …), so working through it is also a
guided tour of the library.

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
V Types, VI Geometry, VII Categories, VIII Topology. Set 9 covers elementary number theory, which
draws on Parts II, IV and XII. Sets 10–14 were added later for the parts that grew most:
analytic number theory (characters, Mertens, Dirichlet, Euler, the prime number theorem,
Möbius), forcing, the Gödel II and Löb material of Part III, combinatorics and probability.

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
| **10** | | **Analytic number theory** (`Exercises.NumberTheory2`) | |
| 10.1 | ★ | A non-trivial character sums to zero (orthogonality) | `sum_nontrivial_character` |
| 10.2 | ★★ | Infinitely many primes ≡ 3 (mod 8) and ≡ 1 (mod 3) (Dirichlet) | `primes_three_mod_eight_one_mod_three` |
| 10.3 | ★★ | Σ_{p ≤ M} 1/p is eventually above every bound (Euler) | `eventually_sum_reciprocal_primes_ge` |
| 10.4 | ★★★ | Σ_{n ≤ N} Λ(n)/n ∼ log N (Mertens) | `mertens_ratio_tendsto` |
| 10.5 | ★ | θ(N) ≤ N log 1024, via θ ≤ ψ | `theta_le_mul_log_1024` |
| 10.6 | ★ | π(N) → ∞ | `primeCount_tendsto_top` |
| 10.7 | ★★ | Eventually π(N) log N ≥ N/2 (from the PNT) | `primeCount_mul_log_ge_half` |
| 10.8 | ★★ | μ(30) = −1 and Σ_{d ∣ 30} μ(d) = 0 | `mobius_thirty` |
| **11** | | **Forcing** (`Exercises.Forcing`) | |
| 11.1 | ★ | a ⊓ aᶜ = ⊥ in a complete Boolean algebra | `inf_compl_eq_bot'` |
| 11.2 | ★★ | (a ⇨ b) ⊓ (b ⇨ c) ≤ a ⇨ c | `himp_trans` |
| 11.3 | ★★ | De Morgan: (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ | `compl_sup'` |
| 11.4 | ★★ | ⟦∃ x, x = x⟧ = ⊤ in every V^B | `val_exists_eq_self` |
| 11.5 | ★★ | ⟦x̌ ∈ x̌⟧ = ⊥ for check names | `mem_zcheck_self` |
| 11.6 | ★★ | ZF does not prove ∀ x ∀ y, x = y (via `not_proves_of_val`) | `ZF_not_proves_subsingleton` |
| 11.7 | ★★ | ZFC is consistent and does not prove ¬¬CH (from CH's independence) | `ZFC_consistent_and_not_proves_notnotCH` |
| 11.8 | ★★★ | ZF does not prove ¬(∃ x, x = x) | `ZF_not_proves_not_exists` |
| **12** | | **Gödel II and Löb** (`Exercises.Logic2`) | |
| 12.1 | ★ | A (D1) instance: PA ⊢ □_DP (x = x) | `PA_proves_box_refl` |
| 12.2 | ★★ | PA ⊢ φ → ψ gives PA ⊢ □φ → □ψ | `box_mono_provDP` |
| 12.3 | ★★ | Henkin: PA ⊢ ψ ↔ □ψ implies PA ⊢ ψ (Löb) | `henkin_provDP` |
| 12.4 | ★★★ | PA proves no formula unprovable: PA ⊬ ¬□φ | `not_proves_unprovable` |
| 12.5 | ★★ | Gödel II for provH ∨ provDP (transfer) | `godel_second_disj` |
| 12.6 | ★★ | Feferman's provF is not provably above provH | `not_boxH_imp_boxF` |
| **13** | | **Combinatorics** (`Exercises.Combinatorics`) | |
| 13.1 | ★ | Among five numbers, two agree mod 4 (pigeonhole) | `two_same_mod_four` |
| 13.2 | ★★ | Every Boolean sequence has a constant infinite subsequence | `bool_constant_subsequence` |
| 13.3 | ★★ | N → (3, 3) iff N ≥ 6 | `isRamsey_three_three_iff` |
| 13.4 | ★★ | A monochromatic triangle in every colouring of ℕ (infinite Ramsey) | `mono_triangle` |
| 13.5 | ★★★ | Three sets inside {0, 1} have no distinct representatives (Hall) | `no_sdr_three_in_two` |
| **14** | | **Probability** (`Exercises.Probability`) | |
| 14.1 | ★ | The union bound | `prob_or_le` |
| 14.2 | ★★ | Complements of independent events are independent | `Indep.compl_compl` |
| 14.3 | ★★ | A Bernoulli trial has variance ≤ 1/4 | `Var_success_le` |
| 14.4 | ★★ | Zero variance: deviations have probability 0 (Chebyshev) | `prob_dev_eq_zero_of_Var_eq_zero` |
| 14.5 | ★★★ | Bernoulli's theorem with the bound 1/(4nε²), uniform in p | `bernoulli_uniform` |

Totals: 94 exercises (21 ★, 57 ★★, 16 ★★★). Sets 1–9: 62 (14 ★, 37 ★★, 11 ★★★);
sets 10–14: 32 (7 ★, 20 ★★, 5 ★★★).

## For maintainers

### Building and checking

```
lake build Exercises                       # all solution files (the lean_lib `Exercises`)
lake build Exercises.Solutions.Topology    # one part
python3 scripts/make_exercises.py --lean   # regenerate Problems/ and elaborate each file
python3 scripts/make_exercises.py --check  # fail if Problems/ is out of date
```

The script picks up every `Exercises/Solutions/*.lean`, so a new set needs no change to it: add
the solution file, import it in `Exercises/Solutions.lean`, and regenerate. All three commands
must succeed before a change is committed; `--lean` must report one `sorry` warning per
exercise and no errors.

The new sets import large parts of the library (set 10 imports the prime number theorem, set 12
the whole Gödel II development), so `lake build` must have been run first; with a warm cache,
elaborating a problem file takes a few seconds.

To check axioms for a whole set at once, append `#print axioms` lines for its theorems to a
scratch copy of the solution file, or run, for example,

```
echo 'import Exercises.Solutions.Forcing
#print axioms Exercises.Forcing.ZF_not_proves_not_exists' > /tmp/Ax.lean
lake env lean /tmp/Ax.lean
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
