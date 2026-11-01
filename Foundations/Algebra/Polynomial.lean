import Foundations.Algebra.RingHom

/-!
# Polynomials

A polynomial `a₀ + a₁x + ⋯ + aₙxⁿ` is, to the algebraist, not a function but a *formal*
object: a finite list of coefficients, manipulated by the familiar rules. The shift from
"polynomial functions" to "formal polynomials" was one of the quiet conceptual revolutions
of nineteenth-century algebra — it is what allows Galois theory to speak of the roots of
a polynomial before knowing where (or whether) they live, and it is essential over finite
coefficient rings, where different polynomials may define the same function (`x^p` and `x`
over `ℤ/pℤ`, by Fermat).

**Representation.** We represent a polynomial by its list of coefficients `[a₀, a₁, …]`
and identify two lists with the same coefficients (so trailing zeros do not matter):
formally, the polynomial ring `R[x]` is the *quotient* of lists by "equal coefficient
functions" — another definition by abstraction. Multiplication is defined by recursion on
the first factor,

  `(a₀ + x·p') · q = a₀·q + x·(p'·q)`,

which turns every ring law into a straightforward induction on lists; no reindexing of
double sums is ever needed.

**Results.** `R[x]` is a commutative ring; the constants `C a` and the indeterminate `X`
behave as expected on coefficients; and for every `x ∈ R` evaluation `p ↦ p(x)` is a ring
homomorphism `R[x] → R`. Degrees, division and roots follow in `PolyDivision.lean`.
-/

namespace Foundations.Algebra

open Ring

universe u

/-! ## Coefficient lists -/

namespace PolyList

variable {R : Type u} [CommRing R]

/-- The `n`-th coefficient of a coefficient list (zero beyond its end). -/
def coeff : List R → Nat → R
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: p, n + 1 => coeff p n

/-- Coefficients of the empty list vanish. -/
@[simp] theorem coeff_nil (n : Nat) : coeff ([] : List R) n = 0 := by cases n <;> rfl

/-- The constant coefficient of `a :: p` is `a`. -/
@[simp] theorem coeff_cons_zero (a : R) (p : List R) : coeff (a :: p) 0 = a := rfl

/-- The higher coefficients of `a :: p` are those of `p`, shifted. -/
@[simp] theorem coeff_cons_succ (a : R) (p : List R) (n : Nat) :
    coeff (a :: p) (n + 1) = coeff p n := rfl

/-- Two lists are **equivalent** if they have the same coefficients. -/
def Eqv (p q : List R) : Prop := ∀ n, coeff p n = coeff q n

/-- Sum of coefficient lists. -/
def add : List R → List R → List R
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

/-- Negation of a coefficient list. -/
def neg (p : List R) : List R := p.map (fun a => -a)

/-- Scalar multiple `c · p`. -/
def smul (c : R) (p : List R) : List R := p.map (fun a => c * a)

/-- **Product** of coefficient lists, by recursion on the first factor:
`(a :: p) · q = a·q + x·(p·q)`. -/
def mul : List R → List R → List R
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

/-- Coefficients add. -/
@[simp] theorem coeff_add (p q : List R) (n : Nat) : coeff (add p q) n = coeff p n + coeff q n := by
  induction p generalizing q n with
  | nil => simp [add, zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp [add, add_zero]
    | cons b q => cases n <;> simp [add, ih]

/-- Coefficients negate. -/
@[simp] theorem coeff_neg (p : List R) (n : Nat) : coeff (neg p) n = -coeff p n := by
  induction p generalizing n with
  | nil => simp [neg, neg_zero]
  | cons a p ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

/-- Coefficients scale. -/
@[simp] theorem coeff_smul (c : R) (p : List R) (n : Nat) : coeff (smul c p) n = c * coeff p n := by
  induction p generalizing n with
  | nil => simp [smul, mul_zero]
  | cons a p ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

/-- Coefficients of a product with a cons on the left. -/
theorem coeff_mul_cons (a : R) (p q : List R) (n : Nat) :
    coeff (mul (a :: p) q) n = a * coeff q n + coeff (0 :: mul p q) n := by
  simp [mul]

/-- `p · [] ≡ 0`. -/
theorem coeff_mul_nil (p : List R) (n : Nat) : coeff (mul p []) n = 0 := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih =>
    rw [coeff_mul_cons, coeff_nil, mul_zero, zero_add]
    cases n with
    | zero => rfl
    | succ k => exact ih k

/-- If `p ≡ 0` then `p · q ≡ 0`. -/
theorem coeff_mul_of_eqv_nil {p : List R} (hp : Eqv p []) (q : List R) (n : Nat) :
    coeff (mul p q) n = 0 := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih =>
    have ha : a = 0 := hp 0
    have hp' : Eqv p [] := fun k => hp (k + 1)
    rw [coeff_mul_cons, ha, zero_mul, zero_add]
    cases n with
    | zero => rfl
    | succ k => exact ih hp' k

/-- Multiplication respects equivalence in the left factor. -/
theorem mul_congr_left {p p' : List R} (h : Eqv p p') (q : List R) : Eqv (mul p q) (mul p' q) := by
  induction p generalizing p' with
  | nil =>
    intro n
    rw [coeff_mul_of_eqv_nil (fun k => (h k).symm)]; rfl
  | cons a p ih =>
    cases p' with
    | nil => intro n; rw [coeff_mul_of_eqv_nil h]; rfl
    | cons b p' =>
      have hab : a = b := h 0
      have hp : Eqv p p' := fun k => h (k + 1)
      intro n
      rw [coeff_mul_cons, coeff_mul_cons, hab]
      cases n with
      | zero => rfl
      | succ k => simp only [coeff_cons_succ]; rw [ih hp k]

/-- Multiplication respects equivalence in the right factor. -/
theorem mul_congr_right (p : List R) {q q' : List R} (h : Eqv q q') : Eqv (mul p q) (mul p q') := by
  induction p with
  | nil => intro n; rfl
  | cons a p ih =>
    intro n
    rw [coeff_mul_cons, coeff_mul_cons, h n]
    cases n with
    | zero => rfl
    | succ k => simp only [coeff_cons_succ]; rw [ih k]

/-- Left distributivity. -/
theorem mul_add_right (p q r : List R) : Eqv (mul p (add q r)) (add (mul p q) (mul p r)) := by
  induction p with
  | nil => intro n; simp [mul, add_zero]
  | cons a p ih =>
    intro n
    rw [coeff_add, coeff_mul_cons, coeff_mul_cons, coeff_mul_cons, coeff_add, left_distrib]
    cases n with
    | zero => simp only [coeff_cons_zero, add_zero] <;> ac_rfl
    | succ k => simp only [coeff_cons_succ]; rw [ih k, coeff_add]; ac_rfl

/-- Right distributivity. -/
theorem mul_add_left (p q r : List R) : Eqv (mul (add p q) r) (add (mul p r) (mul q r)) := by
  induction p generalizing q with
  | nil => intro n; simp [mul, add]
  | cons a p ih =>
    cases q with
    | nil => intro n; simp [mul, add, add_zero]
    | cons b q =>
      intro n
      show coeff (mul ((a + b) :: add p q) r) n = _
      rw [coeff_add, coeff_mul_cons, coeff_mul_cons, coeff_mul_cons, right_distrib]
      cases n with
      | zero => simp only [coeff_cons_zero, add_zero]
      | succ k => simp only [coeff_cons_succ]; rw [ih q k, coeff_add]; ac_rfl

/-- Scalars pull out of the left factor. -/
theorem smul_mul (c : R) (p q : List R) : Eqv (mul (smul c p) q) (smul c (mul p q)) := by
  induction p with
  | nil => intro n; simp [mul, smul]
  | cons a p ih =>
    intro n
    show coeff (mul ((c * a) :: smul c p) q) n = _
    rw [coeff_smul, coeff_mul_cons, coeff_mul_cons, left_distrib, Ring.mul_assoc]
    cases n with
    | zero => simp only [coeff_cons_zero, mul_zero]
    | succ k => simp only [coeff_cons_succ]; rw [ih k, coeff_smul]

/-- Scalars pull out of the right factor. -/
theorem mul_smul (c : R) (p q : List R) : Eqv (mul p (smul c q)) (smul c (mul p q)) := by
  induction p with
  | nil => intro n; simp [mul, mul_zero]
  | cons a p ih =>
    intro n
    rw [coeff_smul, coeff_mul_cons, coeff_mul_cons, coeff_smul, left_distrib]
    have e : a * (c * coeff q n) = c * (a * coeff q n) := by ac_rfl
    rw [e]
    cases n with
    | zero => simp only [coeff_cons_zero, mul_zero]
    | succ k => simp only [coeff_cons_succ]; rw [ih k, coeff_smul]

/-- **Associativity** of multiplication. -/
theorem mul_assoc (p q r : List R) : Eqv (mul (mul p q) r) (mul p (mul q r)) := by
  induction p with
  | nil => intro n; rfl
  | cons a p ih =>
    intro n
    show coeff (mul (add (smul a q) (0 :: mul p q)) r) n = _
    rw [mul_add_left, coeff_add, smul_mul, coeff_smul, coeff_mul_cons, coeff_mul_cons,
      zero_mul, zero_add]
    cases n with
    | zero => rfl
    | succ k => simp only [coeff_cons_succ]; rw [ih k]

/-- Multiplying by a cons on the right. -/
theorem mul_cons_right (a : R) (p q : List R) :
    Eqv (mul q (a :: p)) (add (smul a q) (0 :: mul q p)) := by
  induction q with
  | nil => intro n; cases n <;> simp [mul, add, smul]
  | cons b q ih =>
    intro n
    rw [coeff_mul_cons, coeff_add, coeff_smul]
    cases n with
    | zero => simp only [coeff_cons_zero, add_zero]; exact CommRing.mul_comm b a
    | succ k =>
      simp only [coeff_cons_succ]
      rw [ih k, coeff_add, coeff_smul, coeff_mul_cons]
      cases k <;> simp only [coeff_cons_zero, coeff_cons_succ] <;> ac_rfl

/-- **Commutativity** of multiplication. -/
theorem mul_comm (p q : List R) : Eqv (mul p q) (mul q p) := by
  induction p with
  | nil => intro n; rw [coeff_mul_nil]; rfl
  | cons a p ih =>
    intro n
    rw [coeff_mul_cons, mul_cons_right, coeff_add, coeff_smul]
    cases n with
    | zero => rfl
    | succ k => simp only [coeff_cons_succ]; rw [ih k]

/-- `[1]` is a multiplicative identity. -/
theorem one_mul (q : List R) : Eqv (mul [1] q) q := by
  intro n
  rw [coeff_mul_cons, Ring.one_mul]
  cases n <;> simp [mul, add_zero]

/-- The coefficient-equivalence relation, as a setoid. -/
def setoid (R : Type u) [CommRing R] : Setoid (List R) where
  r := Eqv
  iseqv := ⟨fun _ _ => rfl, fun h n => (h n).symm, fun h1 h2 n => (h1 n).trans (h2 n)⟩

end PolyList

/-! ## The polynomial ring -/

/-- **The polynomial ring** `R[x]`: coefficient lists modulo equality of coefficients. -/
def Polynomial (R : Type u) [CommRing R] : Type u := Quotient (PolyList.setoid R)

namespace Polynomial

open PolyList

variable {R : Type u} [CommRing R]

/-- The polynomial with coefficient list `l`. -/
def mk (l : List R) : Polynomial R := Quotient.mk (PolyList.setoid R) l

/-- Lists with the same coefficients give the same polynomial. -/
theorem mk_eq {p q : List R} (h : Eqv p q) : mk p = mk q := Quotient.sound h

/-- **The ring `R[x]`.** -/
instance : CommRing (Polynomial R) where
  add := Quotient.lift₂ (fun p q => mk (PolyList.add p q))
    (fun _ _ _ _ (h1 : Eqv _ _) (h2 : Eqv _ _) => mk_eq fun n => by
      rw [coeff_add, coeff_add, h1 n, h2 n])
  mul := Quotient.lift₂ (fun p q => mk (PolyList.mul p q))
    (fun _ _ _ _ (h1 : Eqv _ _) (h2 : Eqv _ _) => mk_eq fun n =>
      (mul_congr_left h1 _ n).trans (mul_congr_right _ h2 n))
  neg := Quotient.lift (fun p => mk (PolyList.neg p))
    (fun _ _ (h : Eqv _ _) => mk_eq fun n => by rw [coeff_neg, coeff_neg, h n])
  zero := mk []
  one := mk [1]
  add_assoc a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact mk_eq fun n => by simp only [coeff_add, Ring.add_assoc]
  add_comm a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact mk_eq fun n => by simp only [coeff_add, Ring.add_comm]
  zero_add a := by
    induction a using Quotient.ind
    exact mk_eq fun n => by simp only [coeff_add, coeff_nil, Ring.zero_add]
  neg_add_cancel a := by
    induction a using Quotient.ind
    exact mk_eq fun n => by simp only [coeff_add, coeff_neg, coeff_nil, Ring.neg_add_cancel]
  mul_assoc a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact mk_eq (PolyList.mul_assoc _ _ _)
  one_mul a := by
    induction a using Quotient.ind
    exact mk_eq (PolyList.one_mul _)
  mul_one a := by
    induction a using Quotient.ind
    exact mk_eq fun n => (PolyList.mul_comm _ _ n).trans (PolyList.one_mul _ n)
  left_distrib a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact mk_eq (mul_add_right _ _ _)
  right_distrib a b c := by
    induction a using Quotient.ind; induction b using Quotient.ind
    induction c using Quotient.ind
    exact mk_eq (mul_add_left _ _ _)
  mul_comm a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact mk_eq (PolyList.mul_comm _ _)

/-- The `n`-th coefficient of a polynomial. -/
def coeff (p : Polynomial R) (n : Nat) : R :=
  Quotient.lift (s := PolyList.setoid R) (fun l => PolyList.coeff l n) (fun a b h => (show Eqv a b from h) n) p

/-- Coefficients of `mk l`. -/
@[simp] theorem coeff_mk (l : List R) (n : Nat) : coeff (mk l) n = PolyList.coeff l n := rfl

/-- **Polynomials are determined by their coefficients.** -/
theorem ext {p q : Polynomial R} (h : ∀ n, coeff p n = coeff q n) : p = q := by
  induction p using Quotient.ind; induction q using Quotient.ind
  exact mk_eq h

/-- Coefficients of a sum. -/
@[simp] theorem coeff_add (p q : Polynomial R) (n : Nat) :
    coeff (p + q) n = coeff p n + coeff q n := by
  induction p using Quotient.ind; induction q using Quotient.ind
  exact PolyList.coeff_add _ _ n

/-- Coefficients of a negation. -/
@[simp] theorem coeff_neg (p : Polynomial R) (n : Nat) : coeff (-p) n = -coeff p n := by
  induction p using Quotient.ind
  exact PolyList.coeff_neg _ n

/-- The zero polynomial has zero coefficients. -/
@[simp] theorem coeff_zero (n : Nat) : coeff (0 : Polynomial R) n = 0 := coeff_nil n

/-- The **constant polynomial** `C a`. -/
def C (a : R) : Polynomial R := mk [a]

/-- The **indeterminate** `X`. -/
def X : Polynomial R := mk [0, 1]

/-- Coefficients of a constant. -/
theorem coeff_C (a : R) (n : Nat) : coeff (C a) n = if n = 0 then a else 0 := by
  cases n <;> simp [C]

/-- The constant coefficient of `C a`. -/
@[simp] theorem coeff_C_zero (a : R) : coeff (C a) 0 = a := rfl

/-- Higher coefficients of `C a` vanish. -/
@[simp] theorem coeff_C_succ (a : R) (n : Nat) : coeff (C a) (n + 1) = 0 := by simp [C]

/-- `C 1 = 1`. -/
theorem C_one : C (1 : R) = 1 := rfl

/-- `C 0 = 0`. -/
theorem C_zero : C (0 : R) = 0 := ext fun n => by cases n <;> simp [C]

/-- **Multiplying by a constant scales the coefficients.** -/
@[simp] theorem coeff_C_mul (a : R) (p : Polynomial R) (n : Nat) :
    coeff (C a * p) n = a * coeff p n := by
  induction p using Quotient.ind
  show PolyList.coeff (PolyList.mul [a] _) n = _
  rw [coeff_mul_cons]
  cases n <;> simp [PolyList.mul, add_zero] <;> rfl

/-- **Multiplying by `X` shifts the coefficients.** -/
@[simp] theorem coeff_X_mul_zero (p : Polynomial R) : coeff (X * p) 0 = 0 := by
  induction p using Quotient.ind
  show PolyList.coeff (PolyList.mul [0, 1] _) 0 = _
  rw [coeff_mul_cons, zero_mul, zero_add]; rfl

/-- **Multiplying by `X` shifts the coefficients.** -/
@[simp] theorem coeff_X_mul_succ (p : Polynomial R) (n : Nat) :
    coeff (X * p) (n + 1) = coeff p n := by
  induction p using Quotient.ind with
  | _ l =>
    show PolyList.coeff (PolyList.mul [0, 1] l) (n + 1) = _
    rw [coeff_mul_cons, zero_mul, zero_add, coeff_cons_succ]
    exact PolyList.one_mul l n

/-- `C` preserves addition. -/
theorem C_add (a b : R) : C (a + b) = C a + C b :=
  ext fun n => by cases n <;> simp [add_zero]

/-- `C` preserves negation. -/
theorem C_neg (a : R) : C (-a) = -C a :=
  ext fun n => by cases n <;> simp [neg_zero]

/-- `C` preserves multiplication. -/
theorem C_mul (a b : R) : C (a * b) = C a * C b :=
  ext fun n => by cases n <;> simp [mul_zero]

/-- The constant-polynomial embedding `R → R[x]` is a ring homomorphism. -/
def CHom : RingHom R (Polynomial R) where
  toFun := C
  map_add := C_add
  map_mul := C_mul
  map_one := C_one

/-- Every polynomial has only finitely many non-zero coefficients. -/
theorem exists_bound (p : Polynomial R) : ∃ d, ∀ n, d ≤ n → coeff p n = 0 := by
  induction p using Quotient.ind with
  | _ l =>
    refine ⟨l.length, fun n hn => ?_⟩
    show PolyList.coeff l n = 0
    induction l generalizing n with
    | nil => rfl
    | cons a l ih =>
      cases n with
      | zero => simp at hn
      | succ k => exact ih k (by simp at hn; omega)

/-! ## Evaluation -/

/-- Evaluating a coefficient list at `x` (Horner's scheme): `a₀ + x · (a₁ + x · (⋯))`. -/
def evalList (x : R) : List R → R
  | [] => 0
  | a :: p => a + x * evalList x p

/-- A list with zero coefficients evaluates to `0`. -/
theorem evalList_of_eqv_nil (x : R) {p : List R} (h : Eqv p []) : evalList x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show a + x * evalList x p = 0
    rw [show a = 0 from h 0, ih (fun k => h (k + 1)), mul_zero, add_zero]

/-- Evaluation respects equivalence of lists. -/
theorem evalList_congr (x : R) {p q : List R} (h : Eqv p q) : evalList x p = evalList x q := by
  induction p generalizing q with
  | nil => rw [evalList_of_eqv_nil x (fun k => (h k).symm)]; rfl
  | cons a p ih =>
    cases q with
    | nil => exact evalList_of_eqv_nil x h
    | cons b q =>
      show a + x * evalList x p = b + x * evalList x q
      rw [show a = b from h 0, ih (fun k => h (k + 1))]

/-- Evaluation of a sum. -/
theorem evalList_add (x : R) (p q : List R) :
    evalList x (PolyList.add p q) = evalList x p + evalList x q := by
  induction p generalizing q with
  | nil => show evalList x q = 0 + _; rw [Ring.zero_add]
  | cons a p ih =>
    cases q with
    | nil => show _ = _ + 0; rw [add_zero]; rfl
    | cons b q =>
      show (a + b) + x * evalList x (PolyList.add p q) = (a + x * evalList x p) + (b + x * evalList x q)
      rw [ih, left_distrib]; ac_rfl

/-- Evaluation of a scalar multiple. -/
theorem evalList_smul (x c : R) (p : List R) :
    evalList x (PolyList.smul c p) = c * evalList x p := by
  induction p with
  | nil => show (0 : R) = c * 0; rw [mul_zero]
  | cons a p ih =>
    show c * a + x * evalList x (PolyList.smul c p) = c * (a + x * evalList x p)
    rw [ih, left_distrib]
    congr 1; ac_rfl

/-- Evaluation of a product. -/
theorem evalList_mul (x : R) (p q : List R) :
    evalList x (PolyList.mul p q) = evalList x p * evalList x q := by
  induction p with
  | nil => show (0 : R) = 0 * _; rw [zero_mul]
  | cons a p ih =>
    show evalList x (PolyList.add (PolyList.smul a q) (0 :: PolyList.mul p q)) = _
    rw [evalList_add, evalList_smul]
    show a * evalList x q + (0 + x * evalList x (PolyList.mul p q)) = (a + x * evalList x p) * _
    rw [ih, Ring.zero_add, right_distrib, Ring.mul_assoc]

/-- Evaluation of a negation. -/
theorem evalList_neg (x : R) (p : List R) : evalList x (PolyList.neg p) = -evalList x p := by
  induction p with
  | nil => exact neg_zero.symm
  | cons a p ih =>
    show -a + x * evalList x (PolyList.neg p) = -(a + x * evalList x p)
    rw [ih, mul_neg, neg_add]

/-- **Evaluation** of a polynomial at `x`. -/
def eval (x : R) (p : Polynomial R) : R :=
  Quotient.lift (s := PolyList.setoid R) (evalList x) (fun a b h => evalList_congr x (show Eqv a b from h)) p

/-- **Evaluation is a ring homomorphism** `R[x] → R`, for every `x ∈ R`. -/
def evalHom (x : R) : RingHom (Polynomial R) R where
  toFun := eval x
  map_add a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact evalList_add x _ _
  map_mul a b := by
    induction a using Quotient.ind; induction b using Quotient.ind
    exact evalList_mul x _ _
  map_one := by
    show 1 + x * 0 = 1
    rw [mul_zero, add_zero]

/-- `(p + q)(x) = p(x) + q(x)`. -/
theorem eval_add (x : R) (p q : Polynomial R) : eval x (p + q) = eval x p + eval x q :=
  (evalHom x).map_add p q

/-- `(p * q)(x) = p(x) * q(x)`. -/
theorem eval_mul (x : R) (p q : Polynomial R) : eval x (p * q) = eval x p * eval x q :=
  (evalHom x).map_mul p q

/-- `(-p)(x) = -p(x)`. -/
theorem eval_neg (x : R) (p : Polynomial R) : eval x (-p) = -eval x p := by
  induction p using Quotient.ind
  exact evalList_neg x _

/-- `(C a)(x) = a`. -/
@[simp] theorem eval_C (x a : R) : eval x (C a) = a := by
  show a + x * 0 = a; rw [mul_zero, add_zero]

/-- `X(x) = x`. -/
@[simp] theorem eval_X (x : R) : eval x X = x := by
  show 0 + x * (1 + x * 0) = x
  rw [mul_zero, add_zero, Ring.mul_one, Ring.zero_add]

end Polynomial

end Foundations.Algebra
