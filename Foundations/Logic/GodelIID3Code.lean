import Foundations.Logic.GodelIID3Syntax

/-!
# Codes of formulas with internal numerals substituted

Formalised Σ-completeness (the heart of (D3)) asserts, inside a model `N` of PA: if a
Σ-formula `χ` holds of elements `a₀, a₁, …` of `N`, then the *sentence* `χ(ā₀, ā₁, …)`
— with the numerals of the `aᵢ` substituted for the free variables — is provable. When the
`aᵢ` are non-standard, this sentence is not a formula in the metatheory at all; it exists
only as a number of `N`. This file defines that number:

  `codeM χ d vals` = the code, computed inside `N`, of `χ` with the variable `d + m`
  replaced by the numeral `NumN (vals m)` (variables `< d` are bound and stay put),

built from the internal pairing function `pairN` exactly as the Gödel numbering `fcode`
is built from `pair`. Two properties are proved:

* `codeM_cast`: on standard values `codeM` *is* the Gödel number of the substituted
  formula;
* `codeM_subst`: a substitution lemma — substituting terms into `χ` and then numerals is
  the same as substituting numerals of the values of those terms. This is what lets
  derivations obtained for one formula be reused inside another.

*Place in the argument.* Gödel (1931) only sketched the second incompleteness theorem;
Hilbert and Bernays (1939) carried out the arithmetisation it needs; Löb (1955) reduced it to
three derivability conditions, of which (D3) — formalised Σ₁-completeness — is the hard one.
Feferman (1960) showed that the theorem depends on how provability is expressed, which is why
it matters that `provDP` is a derivation predicate rather than one engineered to satisfy (D3).
This file is one step of the proof of (D3) for `provDP` assembled in `GodelIID3Main`.
-/

namespace Foundations.Logic.FO

open Arith Formula Theory Computability

namespace GodelII

/-- Iterated lifting of a substitution under `d` binders. -/
def liftN : Nat → (Nat → Term Arith) → Nat → Term Arith
  | 0, σ => σ
  | d + 1, σ => Subst.lift (liftN d σ)

/-- Renaming twice. -/
theorem rename_rename (ρ τ : Nat → Nat) : ∀ t : Term Arith, (t.rename ρ).rename τ = t.rename (τ ∘ ρ)
  | .var _ => rfl
  | .func f ts => by simp only [Term.rename]; congr; funext i; exact rename_rename ρ τ (ts i)

/-- Renaming by `· + 0` is the identity. -/
theorem rename_add_zero : ∀ t : Term Arith, t.rename (· + 0) = t
  | .var _ => rfl
  | .func f ts => by simp only [Term.rename]; congr; funext i; exact rename_add_zero (ts i)

/-- **Lifting explicitly.** Under `d` binders, variables `< d` are untouched and the
variable `d + j` becomes `σ j` shifted by `d`. -/
theorem liftN_apply (σ : Nat → Term Arith) : ∀ d m, liftN d σ m =
    if m < d then Term.var m else (σ (m - d)).rename (· + d)
  | 0, m => by
    simp only [liftN, Nat.not_lt_zero, ite_false, Nat.sub_zero]
    exact (rename_add_zero (σ m)).symm
  | d + 1, 0 => by simp [liftN, Subst.lift]
  | d + 1, m + 1 => by
    simp only [liftN, Subst.lift]
    rw [liftN_apply σ d m]
    by_cases h : m < d
    · simp [h, Term.rename]
    · simp only [h, ite_false, show ¬ m + 1 < d + 1 by omega, rename_rename]
      rw [show m + 1 - (d + 1) = m - d by omega]
      congr 1

/-- Renaming fixes numerals. -/
theorem numeral_rename (ρ : Nat → Nat) : ∀ n, (numeral n).rename ρ = numeral n
  | 0 => by simp only [numeral, zero, Term.rename]; congr 1; funext i; exact i.elim0
  | n + 1 => by
    simp only [numeral, succ, Term.rename]; congr; funext _; exact numeral_rename ρ n

end GodelII

open GodelII

namespace PAModel

variable {N : PAModel}

/-- Internal code of a function application, mirroring `funcCode`. -/
noncomputable def funcCodeM : {n : Nat} → ArithFunc n → (Fin n → N.Dom) → N.Dom
  | _, .zero, _ => 2
  | _, .succ, c => pairN 2 (c 0)
  | _, .add, c => pairN 3 (pairN (c 0) (c 1))
  | _, .mul, c => pairN 4 (pairN (c 0) (c 1))

/-- **Internal code of a term with numerals substituted.** -/
noncomputable def tcM : Term Arith → Nat → (Nat → N.Dom) → N.Dom
  | .var m, d, vals => if m < d then ((pair 0 m : Nat) : N.Dom) else NumN (vals (m - d))
  | .func f ts, d, vals => funcCodeM f fun i => tcM (ts i) d vals

/-- **Internal code of a formula with numerals substituted** for its free variables. -/
noncomputable def codeM : Formula Arith → Nat → (Nat → N.Dom) → N.Dom
  | .bot, _, _ => 0
  | .eq t s, d, v => pairN 1 (pairN (tcM t d v) (tcM s d v))
  | .rel R _, _, _ => (R : Empty).elim
  | .imp φ ψ, d, v => pairN 2 (pairN (codeM φ d v) (codeM ψ d v))
  | .conj φ ψ, d, v => pairN 3 (pairN (codeM φ d v) (codeM ψ d v))
  | .disj φ ψ, d, v => pairN 4 (pairN (codeM φ d v) (codeM ψ d v))
  | .all φ, d, v => pairN 5 (codeM φ (d + 1) v)
  | .ex φ, d, v => pairN 6 (codeM φ (d + 1) v)

/-- The code of `0`. -/
@[simp] theorem tcM_zero (d : Nat) (v : Nat → N.Dom) : tcM zero d v = 2 := rfl
/-- The code of `S t`. -/
@[simp] theorem tcM_succ (t : Term Arith) (d : Nat) (v : Nat → N.Dom) :
    tcM (succ t) d v = pairN 2 (tcM t d v) := rfl
/-- The code of `t + s`. -/
@[simp] theorem tcM_add (t s : Term Arith) (d : Nat) (v : Nat → N.Dom) :
    tcM (add t s) d v = pairN 3 (pairN (tcM t d v) (tcM s d v)) := rfl
/-- The code of `t · s`. -/
@[simp] theorem tcM_mul (t s : Term Arith) (d : Nat) (v : Nat → N.Dom) :
    tcM (mul t s) d v = pairN 4 (pairN (tcM t d v) (tcM s d v)) := rfl

/-- At depth `0`, a variable is replaced by its numeral. -/
@[simp] theorem tcM_var0 (m : Nat) (v : Nat → N.Dom) : tcM (Term.var m) 0 v = NumN (v m) := by
  simp [tcM]

/-- `2 = ⌜0⌝` as an element of the model. -/
theorem two_eq_cast : (2 : N.Dom) = ((pair 1 0 : Nat) : N.Dom) := by rw [pair_one_zero]; rfl

/-- A shifted term at depth `d` has the code of the original term at depth `0`. -/
theorem tcM_rename_add (d : Nat) (v : Nat → N.Dom) :
    ∀ t : Term Arith, tcM (t.rename (· + d)) d v = tcM t 0 v
  | .var m => by
    have h : ¬ m + d < d := by omega
    simp only [Term.rename, tcM, h, Nat.add_sub_cancel,
      Nat.not_lt_zero, ite_false, Nat.sub_zero]
  | .func f ts => by
    simp only [Term.rename, tcM]; congr; funext i; exact tcM_rename_add d v (ts i)

/-- **Substitution lemma for terms.** -/
theorem tcM_subst {σ : Nat → Term Arith} {v v' : Nat → N.Dom}
    (hσ : ∀ m, tcM (σ m) 0 v = NumN (v' m)) (d : Nat) :
    ∀ t : Term Arith, tcM (t.subst (liftN d σ)) d v = tcM t d v'
  | .var m => by
    simp only [Term.subst, liftN_apply]
    by_cases h : m < d
    · simp [h, tcM]
    · simp only [h, ite_false, tcM_rename_add, hσ, tcM]
  | .func f ts => by
    simp only [Term.subst, tcM]; congr; funext i; exact tcM_subst hσ d (ts i)

/-- **Substitution lemma for formulas.** If every `σ m` has (at depth `0`, under `v`) the
code of the numeral of `v' m`, then substituting `σ` and then the numerals of `v` gives the
same code as substituting the numerals of `v'`. -/
theorem codeM_subst {σ : Nat → Term Arith} {v v' : Nat → N.Dom}
    (hσ : ∀ m, tcM (σ m) 0 v = NumN (v' m)) :
    ∀ (φ : Formula Arith) (d : Nat), codeM (φ.subst (liftN d σ)) d v = codeM φ d v'
  | .bot, _ => rfl
  | .eq t s, d => by simp only [Formula.subst, codeM, tcM_subst hσ d]
  | .rel R _, _ => (R : Empty).elim
  | .imp φ ψ, d => by simp only [Formula.subst, codeM, codeM_subst hσ φ d, codeM_subst hσ ψ d]
  | .conj φ ψ, d => by simp only [Formula.subst, codeM, codeM_subst hσ φ d, codeM_subst hσ ψ d]
  | .disj φ ψ, d => by simp only [Formula.subst, codeM, codeM_subst hσ φ d, codeM_subst hσ ψ d]
  | .all φ, d => by
    simp only [Formula.subst, codeM]
    exact congrArg _ (codeM_subst hσ φ (d + 1))
  | .ex φ, d => by
    simp only [Formula.subst, codeM]
    exact congrArg _ (codeM_subst hσ φ (d + 1))

/-- The depth-`0` form of the substitution lemma. -/
theorem codeM_subst0 {σ : Nat → Term Arith} {v v' : Nat → N.Dom}
    (hσ : ∀ m, tcM (σ m) 0 v = NumN (v' m)) (φ : Formula Arith) :
    codeM (φ.subst σ) 0 v = codeM φ 0 v' :=
  codeM_subst hσ φ 0

/-- Function codes on standard values. -/
theorem funcCodeM_cast : ∀ {n : Nat} (f : ArithFunc n) (c : Fin n → Nat),
    funcCodeM f (fun i => ((c i : Nat) : N.Dom)) = ((funcCode f c : Nat) : N.Dom)
  | _, .zero, _ => two_eq_cast
  | _, .succ, c => by
    simp only [funcCodeM, funcCode]
    rw [show (2 : N.Dom) = ((2 : Nat) : N.Dom) from rfl, pairN_cast]
  | _, .add, c => by
    simp only [funcCodeM, funcCode]
    rw [pairN_cast, show (3 : N.Dom) = ((3 : Nat) : N.Dom) from rfl, pairN_cast]
  | _, .mul, c => by
    simp only [funcCodeM, funcCode]
    rw [pairN_cast, show (4 : N.Dom) = ((4 : Nat) : N.Dom) from rfl, pairN_cast]

/-- **Standard values (terms).** -/
theorem tcM_cast (e : Nat → Nat) (d : Nat) : ∀ t : Term Arith,
    tcM t d (fun m => (e m : N.Dom)) =
      ((tcode (t.subst (liftN d fun m => numeral (e m))) : Nat) : N.Dom)
  | .var m => by
    simp only [Term.subst, liftN_apply, tcM]
    by_cases h : m < d
    · simp [h]
    · simp only [h, ite_false, numeral_rename]
      exact numN_cast _
  | .func f ts => by
    simp only [Term.subst, tcM, tcode]
    rw [show (fun i => tcM (ts i) d (fun m => (e m : N.Dom))) = fun i =>
      ((tcode ((ts i).subst (liftN d fun m => numeral (e m))) : Nat) : N.Dom) from
      funext fun i => tcM_cast e d (ts i)]
    exact funcCodeM_cast f _

/-- Pairing a numeral tag with a cast. -/
theorem pairN_tag (k : Nat) (a b : Nat) :
    pairN (OfNat.ofNat k : N.Dom) (pairN (a : N.Dom) (b : N.Dom)) =
      ((pair k (pair a b) : Nat) : N.Dom) := by
  rw [pairN_cast, show (OfNat.ofNat k : N.Dom) = ((k : Nat) : N.Dom) from rfl, pairN_cast]

/-- **Standard values (formulas).** On standard values, `codeM` is the Gödel number of the
formula with numerals substituted. -/
theorem codeM_cast (e : Nat → Nat) : ∀ (φ : Formula Arith) (d : Nat),
    codeM φ d (fun m => (e m : N.Dom)) =
      ((fcode (φ.subst (liftN d fun m => numeral (e m))) : Nat) : N.Dom)
  | .bot, _ => rfl
  | .eq t s, d => by simp only [Formula.subst, codeM, fcode, tcM_cast e d]; exact pairN_tag 1 _ _
  | .rel R _, _ => (R : Empty).elim
  | .imp φ ψ, d => by
    simp only [Formula.subst, codeM, fcode, codeM_cast e φ d, codeM_cast e ψ d]
    exact pairN_tag 2 _ _
  | .conj φ ψ, d => by
    simp only [Formula.subst, codeM, fcode, codeM_cast e φ d, codeM_cast e ψ d]
    exact pairN_tag 3 _ _
  | .disj φ ψ, d => by
    simp only [Formula.subst, codeM, fcode, codeM_cast e φ d, codeM_cast e ψ d]
    exact pairN_tag 4 _ _
  | .all φ, d => by
    simp only [Formula.subst, codeM, fcode]
    rw [codeM_cast e φ (d + 1), show (5 : N.Dom) = ((5 : Nat) : N.Dom) from rfl, pairN_cast]; rfl
  | .ex φ, d => by
    simp only [Formula.subst, codeM, fcode]
    rw [codeM_cast e φ (d + 1), show (6 : N.Dom) = ((6 : Nat) : N.Dom) from rfl, pairN_cast]; rfl

/-- The depth-`0` form: `codeM φ 0 ⌜e⌝ = ⌜φ(ē)⌝`. -/
theorem codeM_cast0 (e : Nat → Nat) (φ : Formula Arith) :
    codeM φ 0 (fun m => (e m : N.Dom)) = ((fcode (φ.subst fun m => numeral (e m)) : Nat) : N.Dom) :=
  codeM_cast e φ 0

end PAModel

end Foundations.Logic.FO
