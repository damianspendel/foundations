import Foundations.Langlands.Rep.Matrix
import Foundations.Langlands.Rep.Basic
import Foundations.Langlands.Rep.Maschke
import Foundations.Langlands.Rep.Schur
import Foundations.Langlands.Rep.Orthogonality
import Foundations.Langlands.Rep.Multiplicity
import Foundations.Langlands.Rep.Abelian
import Foundations.Langlands.Rep.Permutation
import Foundations.Langlands.Rep.Decompose
import Foundations.Langlands.Rep.Regular
import Foundations.Langlands.Rep.Completeness
import Foundations.Langlands.Rep.Existence
import Foundations.Langlands.Rep.ClassFunctions
import Foundations.Langlands.Rep.Classes
import Foundations.Langlands.Rep.SecondOrthogonality
import Foundations.Langlands.Rep.Monomial
import Foundations.Langlands.Rep.S3
import Foundations.Langlands.Rep.A4
import Foundations.Langlands.Rep.CharacterIso
import Foundations.Langlands.Rep.Induction
import Foundations.Langlands.Rep.Induced
import Foundations.Langlands.Rep.InducedS3

/-!
# Part XV, chapter 2: representations of finite groups

The Langlands programme relates Galois representations to automorphic representations. This
chapter builds its most basic layer, the representation theory of finite groups created by
Frobenius (1896), developed by Burnside and refounded by Schur (1905). Representations are
matrix-valued: `Rep G K ι` is a homomorphism `G → GL(K^ι)`, the degree being `card ι`.

## What is proved

* `Matrix`: vectors `K^ι`, matrices, products, the trace, and `trace_mul_comm`
  (`tr (A B) = tr (B A)`, also for rectangular matrices).
* `Basic`: subspaces, invariant subspaces (subrepresentations), irreducibility, `G`-maps,
  isomorphism, direct sums `ρ ⊕ σ` (whose two summands are complementary subrepresentations),
  characters `χ_ρ(g) = tr ρ(g)`; characters are class functions (`character_isClassFunction`),
  additive on direct sums (`character_dsum`), equal for isomorphic representations
  (`character_eq_of_iso`), with `χ_ρ(1) = deg ρ` (`character_one`).
* `Maschke`: **Maschke's theorem** (`maschke`): over a field with `|G| ≠ 0`, every
  subrepresentation has an invariant complement; `maschke_complex` over `ℂ`; and
  `split_of_not_irreducible`: a non-zero, non-irreducible representation splits as `W ⊕ W'`
  with `W`, `W'` non-zero subrepresentations.
* `Schur`: **Schur's lemma** (`schur`): a `G`-map between irreducibles is `0` or invertible;
  `schur_of_not_iso`; existence of eigenvectors over an algebraically closed field
  (`exists_eigenvector`, determinant-free); `schur_scalar`: an endomorphism of an irreducible
  representation over an algebraically closed field is a scalar; `algClosed_complex` (from
  `fta`) and `schur_complex`.
* `Orthogonality`: **first orthogonality** (`orthogonality`, `orthogonality_complex`): for
  irreducible `ρ`, `σ` over `ℂ`, `Σ_g χ_σ(g) χ_ρ(g⁻¹) = |G|` if `ρ ≅ σ` and `0` otherwise
  (the non-isomorphic case `orthogonality_of_not_iso` holds over any commutative ring).
* `Multiplicity`: if `χ = Σ_k m_k χ_k` for pairwise non-isomorphic irreducibles, then
  `Σ_g χ(g) χ_j(g⁻¹) = m_j |G|` (`multiplicity_eq`, `multiplicity_eq_complex`), so
  `m_j = ⟨χ, χ_j⟩` (`multiplicity_eq_inner`) and the multiplicities are unique as elements of
  the field (`multiplicity_unique`).
* `Abelian`: for finite abelian `G`, irreducible complex representations have degree `1`
  (`card_eq_one_of_irreducible`), and `ψ : G → ℂ` is the character of an irreducible
  representation iff `IsChar ψ`, i.e. `ψ` is an element of `Character G` from
  `NumberTheory/DualGroup` (`irreducible_character_iff_isChar`).
* `Permutation`: permutation representations of a `MulAction`; their characters count fixed
  points (`character_permRep`); they contain the trivial representation, which splits off
  (`trivial_sub_permRep`, `permRep_splits`).

* `Decompose`: bases of subspaces (`exists_basis_subspace`); restriction of a representation
  to complementary invariant subspaces (`iso_dsum_of_compl`: `ρ ≅ ρ₁ ⊕ ρ₂` with degrees
  `d, e ≥ 1`, `d + e ≤ deg ρ`); `Iso.trans`, `Iso.dsum`; and **complete reducibility**
  (`complete_reducibility`): over a field with `|G| ≠ 0`, every representation on a non-zero
  `K^ι` (`ι : Type`) is isomorphic to some `σ` with `SumIrr σ`, i.e. built from irreducibles by
  direct sums.
* `Regular`: the **irreducibility criterion** over `ℂ` (`irreducible_iff_pairing`):
  `ρ` irreducible ⇔ `Σ_g χ(g) χ(g⁻¹) = |G|`; the regular representation `regularRep`, with
  character `|G|·[g = 1]` (`character_regularRep`); `pairing_regular`
  (`Σ_g χ_reg(g) χ_ρ(g⁻¹) = dim ρ · |G|`), and `regular_multiplicity`: if
  `χ_reg = Σ_k m_k χ_k` for pairwise non-isomorphic irreducibles, then `m_k = dim ρ_k`;
  **Burnside's formula** (`sum_sq_degrees`, for `G : Type`): if `ρ₀, …, ρ_{r−1}` are pairwise
  non-isomorphic irreducible complex representations and every irreducible representation
  (on an index type in `Type`) is isomorphic to one of them, then `Σ_k (dim ρ_k)² = |G|`.
* `Completeness`: isomorphic representations have equal degree (`Iso.card_eq`);
  **Burnside's inequality** (`sum_sq_le`, for `G : Type`): for any list of pairwise
  non-isomorphic irreducible complex representations, `Σ_k (dim ρ_k)² ≤ |G|`; the
  **completeness criterion** (`complete_of_sum_sq`): if equality holds, every irreducible
  representation (on an index type in `Type`) is isomorphic to a member of the list; and
  `complete_iff_sum_sq`, combining this with `sum_sq_degrees`.
* `Existence`: every finite group (`G : Type`) has a finite complete list of pairwise
  non-isomorphic irreducible complex representations (`exists_complete_irrList`), so
  Burnside's formula holds for it without hypotheses (`exists_sum_sq_degrees`).
* `ClassFunctions`: for a class function `f`, `Σ_g f(g) ρ(g)` is a `G`-map (`classOp_isGMap`);
  **characters detect class functions** (`classFunction_eq_zero`, for `G : Type`): a class
  function `f` with `Σ_g f(g) χ(g) = 0` for every irreducible character `χ` is zero.
* `Classes`: conjugacy classes `ConjClasses G` (the quotient by conjugacy); **the number of
  irreducibles is the number of conjugacy classes** (`card_irr_eq_card_conjClasses`): every
  complete list of pairwise non-isomorphic irreducible complex representations has
  `|ConjClasses G|` members; with `exists_card_irr_eq_card_conjClasses` for existence.
* `SecondOrthogonality`: **characters span the class functions** (`classFunction_expansion`):
  for a complete list, `|G| f(g) = Σ_k (Σ_x f(x) χ_k(x)) χ_k(g⁻¹)` for every class function `f`;
  **second orthogonality** (`second_orthogonality`): `|cl(h)| · Σ_k χ_k(h) χ_k(g⁻¹)` is `|G|`
  if `g` is conjugate to `h` and `0` otherwise, with `|cl(h)|` the number of conjugates of `h`;
  `second_orthogonality_of_not_conj`.
* `Monomial`: monomial matrices and their products (`monoMat_mul`); monomial representations
  `monoRep` built from a permutation-and-exponent cocycle, with their characters
  (`character_monoRep`); a primitive cube root of unity `omega3` in `ℂ` (`ω² + ω + 1 = 0`,
  from the fundamental theorem of algebra).
* `S3`: `S₃`, built as `C₃ ⋊ C₂`, with its trivial, sign and 2-dimensional standard
  representations (the latter as explicit matrices `r ↦ diag(ω, ω²)`, `s ↦ (0 1; 1 0)`),
  each irreducible, pairwise non-isomorphic, and complete (`S3.irreducibles_complete`, from
  `1 + 1 + 4 = 6`); the character table on `1, r, s` (`S3.character_table`); every element is conjugate to one of
  `1, r, s` (`S3.conj_rep`).
* `A4`: `A₄`, built as `V ⋊ C₃` (Klein four-group by a cyclic group of order 3), with three
  1-dimensional representations through `A₄ → C₃` and a 3-dimensional representation by signed
  permutation matrices, each irreducible, pairwise non-isomorphic, and complete
  (`A4.irreducibles_complete`, from `1 + 1 + 1 + 9 = 12`); the character table on `1, t, c, c²`
  (`A4.character_table`); every element is conjugate to one of `1, t, c, c²`
  (`A4.conj_rep`).
* `CharacterIso`: reindexing isomorphisms (`iso_of_reindex`), associativity and commutativity
  of direct sums up to isomorphism (`Iso.dsum_assoc`, `Iso.dsum_comm`); splitting an
  irreducible `τ` with `⟨χ_S, χ_τ⟩ ≠ 0` off a sum of irreducibles (`sumIrr_split`); and
  **characters determine representations** (`iso_of_character_eq`, `iso_iff_character_eq`): for
  `G : Type u` and index types in `Type`, complex representations with equal characters are
  isomorphic (complete reducibility plus multiplicities, by induction on the degree).
* `Induction`: the restriction `Rep.res H ρ` to a subgroup `H : Subgroup G` (the subgroups of
  `Algebra/Group`, as used for Lagrange and Sylow), with `χ_{Res ρ} = (χ_ρ)|_H`
  (`character_res`); the **induced class function** `indFun H f`,
  `Ind f(g) = (1/|H|) Σ_{x ∈ G} f°(x g x⁻¹)` with `f°` the extension by zero, a class function
  (`indFun_isClassFunction`); and **Frobenius reciprocity** (Frobenius 1898,
  `frobenius_reciprocity`): `(1/|G|) Σ_g Ind f(g) ψ(g⁻¹) = (1/|H|) Σ_h f(h) ψ(h⁻¹)` for every
  `f : H → ℂ` and every class function `ψ` on `G`.
* `Induced`: coset representatives `cosetRep H g` chosen classically (Hilbert's `ε`), depending
  only on the coset; the finite type `CosetReps H`; the **induced representation**
  `indRep H σ` on `K^(CosetReps H × ι)`, over any commutative ring, by the block matrices
  `σ°(t⁻¹ g s)`; its **character** `χ_{Ind σ} = Ind χ_σ` over `ℂ` (`character_indRep`); and
  Frobenius reciprocity for induced representations (`frobenius_reciprocity_indRep`).
* `InducedS3`: the rotation subgroup `C₃ ≤ S₃` (`S3.rot`) and its non-trivial character
  `λ(r^a) = ω^a`; `Ind^{S₃}_{C₃} λ` has the character of `std` (`S3.indFun_lam`), hence
  **`Ind^{S₃}_{C₃} λ ≅ std`** (`S3.std_iso_induced`) and it is irreducible
  (`S3.induced_irreducible`).

## What is not proved

The pairing used is `Σ_g χ(g) ψ(g⁻¹)`; its agreement with the Hermitian product
`Σ_g χ(g) conj ψ(g)` over `ℂ` is not proved. Second orthogonality is stated with the class size
`|cl(h)|`; its relation `|G| = |cl(h)| · |C_G(h)|` with the centraliser is not used or proved
here. Induction is formalised for class functions and for representations, with Frobenius reciprocity
at the level of the pairing; the categorical form (`Hom_G(Ind σ, ρ) ≅ Hom_H(σ, Res ρ)`),
transitivity of induction, Mackey's formula and the degree formula
`deg Ind σ = [G : H] · deg σ` are not proved. Only one choice of coset representatives is
constructed (its character `Ind χ_σ` does not refer to the choice). `iso_of_character_eq` is stated for
index types in `Type`. The groups `S3` and
`A4` are constructed directly as semidirect products; their isomorphisms with the permutation
group of three letters and the even permutations of four letters are not proved. Every element
is shown to be conjugate to one of the chosen class representatives (`S3.conj_rep`,
`A4.conj_rep`); that the representatives are pairwise non-conjugate is not stated as a theorem.
The characters at every element are given by `S3.character_sign`, `S3.character_std`,
`A4.character_lin`, `A4.character_three_V` and `A4.character_three_off`.
-/
