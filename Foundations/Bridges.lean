import Foundations.Bridges.NatBridges
import Foundations.Bridges.ZFQuotient
import Foundations.Bridges.IntInSets
import Foundations.Bridges.RatInSets
import Foundations.Bridges.RealsInSets
import Foundations.Bridges.CurryHowardBridge
import Foundations.Bridges.ETCSvsZF
import Foundations.Bridges.Unification
import Foundations.Bridges.UnificationSize
import Foundations.Bridges.UnificationOrdinals

/-!
# Part XI: Bridges

The first ten parts of this project mostly stand side by side, each using Lean's
built-in natural numbers, licensed by a separate "bridge" theorem. This part makes
the claim that they form *one building* literal, by proving the connections:

* **NatBridges** — the von Neumann ω of Part I, the Peano numbers of Part II and
  Lean's `Nat` are isomorphic by explicit bijections preserving zero, successor,
  `+`, `×` and `≤`; the bridges commute, coincide with the categorical comparison map
  of Part VII, and are unique (Dedekind categoricity).
* **ZFQuotient**, **IntInSets**, **RatInSets** — the integers and the rationals are
  built *inside the ZF universe* as sets of equivalence classes (of pairs in `ω × ω`,
  resp. of pairs of ZF integers and nonzero naturals) and proved isomorphic, as
  ordered rings, to Part II's quotient types `Z` and `Q`.
* **RealsInSets** — the set of Dedekind cuts of the ZF rationals is in
  order-preserving (and addition-preserving) bijection with Part II's cuts and
  Cauchy reals; suprema are unions.
* **CurryHowardBridge** — Part V's intuitionistic natural deduction embeds in Part
  III's classical one (strictly), and Glivenko's theorem gives the converse up to
  double negation; hence classical consistency follows from cut elimination.
* **ETCSvsZF** — the ZF sets and their functions form a category; the functor
  "type of members" into the category of types is full and faithful, not
  essentially surjective, and preserves the terminal object, products and the
  natural numbers object — material and structural set theory agree on ℕ.
* **Unification**, **UnificationSize**, **UnificationOrdinals** — the coherence layer:
  notions defined more than once across parts are proved to agree. The two prime
  predicates and the three factorials coincide; the absolute value of `Q` is the
  ordered-field one and is carried into `R`; Part I's countability (injection into ℕ)
  matches the logic's "surjection from ℕ" on nonempty types, so ℝ is uncountable in
  Part I's sense; Part I's `IsFinite` matches Part IV's `FiniteType` censuses, with
  `card` the Part I cardinal; and Part III's ordinal notations below ε₀ embed, order-
  preservingly, into Part I's von Neumann ordinals, sending `n` to `vn n` and `ω` to `ω`.
-/
