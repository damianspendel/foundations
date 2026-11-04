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

## What is not proved

The pairing used is `Σ_g χ(g) ψ(g⁻¹)`; its agreement with the Hermitian product
`Σ_g χ(g) conj ψ(g)` over `ℂ` is not proved. `sum_sq_degrees` takes the complete list of
irreducibles as a hypothesis; that such a finite list exists is not proved separately. Also not
formalised: second orthogonality, the count of irreducibles by conjugacy classes, induced
representations, and worked character tables of `S₃` and `A₄`.
-/
