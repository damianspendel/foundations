import Foundations.Types.Lambda
import Foundations.Types.STLC
import Foundations.Types.Normalization
import Foundations.Types.CurryHoward
import Foundations.Types.SystemF
import Foundations.Types.SystemFSubst
import Foundations.Types.SystemFNormalization
import Foundations.Types.SystemFEncodings

/-!
# Part V: Types — examining the ground floor

The whole project is written in Lean, whose logic is a dependent type theory.
This part turns around and studies small type theories as mathematical objects:
the untyped λ-calculus of Church with the Church–Rosser theorem; the simply
typed λ-calculus with subject reduction and progress; Tait's strong
normalization proof by reducibility, and the consistency it implies; the
Curry–Howard correspondence between simply typed terms and intuitionistic
natural deduction proofs, with cut elimination and the unprovability of
excluded middle, Peirce's law and double-negation elimination; and Girard and
Reynolds' polymorphic System F, with an account of why `Type : Type` is
inconsistent, Girard's strong normalization theorem for System F by
reducibility candidates (hence its consistency), and the impredicative Church
encodings of booleans, numbers and pairs. All metatheory here is constructive:
normality is decidable, and no use is made of `Classical.choice`.
-/
