import Foundations.Categories.Category
import Foundations.Categories.Yoneda
import Foundations.Categories.Limits
import Foundations.Categories.Adjunctions
import Foundations.Categories.Lawvere
import Foundations.Categories.GeneralLimits
import Foundations.Categories.Equivalence
import Foundations.Categories.Monads
import Foundations.Categories.CCC
import Foundations.Categories.Topos
import Foundations.Categories.ETCS

/-!
# Part VII: Categories — structure itself

Categories, functors and natural transformations (Eilenberg–Mac Lane), with the
categories of types, preorders, monoids and groups (one-object categories), groups
with homomorphisms, and opposites; the functor category and the Yoneda lemma with the
fully faithful Yoneda embedding (objects are determined by their relations); products,
terminal objects, equalisers and pullbacks, unique up to unique isomorphism, in types
and in groups; adjunctions with unit, counit and triangle identities, the free monoid
adjunction, right adjoints preserving products, and the cartesian closedness of types
(currying); and Lawvere's fixed-point theorem, which unifies the diagonal arguments of
Cantor, Russell, Gödel and Turing.

The second phase generalises and turns foundational: limits and colimits of arbitrary
diagrams (all small ones exist in types; right adjoints preserve limits); equivalences
of categories (fully faithful + essentially surjective, with finite sets equivalent to
their skeleton); monads, Kleisli and Eilenberg–Moore categories (algebras of the list
monad are exactly monoids); cartesian closed categories and Lambek's interpretation of
the simply typed λ-calculus of Part V, sound for β and η; elementary toposes, with the
category of types as a Boolean topos (`Ω = Prop`) and double negation as a
Lawvere–Tierney topology; and Lawvere's ETCS, the structuralist rival to ZF, with types
as a model and natural numbers objects unique up to unique isomorphism (Benacerraf's
problem dissolved).
-/
