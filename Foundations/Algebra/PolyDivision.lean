import Foundations.Algebra.Polynomial

/-!
# Degree, division with remainder, and roots

Schoolchildren learn to divide polynomials by long division; Euclid (Elements VII) divided
numbers. Both are instances of a single structural fact, the **division algorithm**: given
`g` with invertible leading coefficient, every `p` can be written `p = q·g + r` with `r` of
smaller degree than `g`. It is the engine behind the next file, where rings with such an
algorithm (Euclidean domains) are shown to have principal ideals.

Two classical corollaries close this file.

* **The factor theorem** (Descartes, *La Géométrie*, 1637): `a` is a root of `p` exactly when
  `x - a` divides `p`. Division by `x - a` leaves the constant remainder `p(a)`.
* **A polynomial of degree `n` has at most `n` roots** in an integral domain — a fact
  Lagrange used in 1768 to prove that `x^(p-1) - 1` factors completely mod `p`. Each root
  splits off a linear factor and lowers the degree by one; the absence of zero divisors
  ensures that no new roots appear along the way.

Instead of a degree *function* with a special value for the zero polynomial, the basic notion
here is the predicate `DegLT p d` — "all coefficients from index `d` on vanish" — from which
the length `len p` (one more than the degree, and `0` for the zero polynomial), the degree
`natDegree p` and the leading coefficient are derived.
-/

namespace Foundations.Algebra

open Ring

universe u

/-- **Integral domain.** A commutative ring in which `0 ≠ 1` and a product vanishes only if
one factor does. -/
def IsDomain (R : Type u) [CommRing R] : Prop :=
  (0 : R) ≠ 1 ∧ ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

/-- **Every field is an integral domain.** -/
theorem IsField.isDomain {R : Type u} [CommRing R] (hF : IsField R) : IsDomain R := by
  refine ⟨hF.1, fun a b hab => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    obtain ⟨c, hc⟩ := hF.2 a ha
    calc b = (a * c) * b := by rw [hc, Ring.one_mul]
      _ = c * (a * b) := by rw [CommRing.mul_comm a c, Ring.mul_assoc]
      _ = 0 := by rw [hab, mul_zero]

/-- In a commutative ring, `b + -a = 0` forces `b = a`. -/
theorem eq_of_sub_eq_zero {R : Type u} [Ring R] {a b : R} (h : b + -a = 0) : b = a := by
  calc b = b + (-a + a) := by rw [neg_add_cancel, add_zero]
    _ = (b + -a) + a := (Ring.add_assoc _ _ _).symm
    _ = a := by rw [h, Ring.zero_add]

/-- Rewriting an `if` whose condition holds. -/
theorem ite_true_of {α : Sort u} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

/-- Rewriting an `if` whose condition fails. -/
theorem ite_false_of {α : Sort u} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

namespace PolyList

variable {R : Type u} [CommRing R]

/-- **Top coefficients multiply** (list version). If `p` vanishes from index `s + 1` on and
`q` from index `t + 1` on, then the coefficient of `p·q` at `s + t` is `pₛ·qₜ`, and `p·q`
vanishes from index `s + t + 1` on. -/
theorem mul_top (q : List R) (t : Nat) (hq : ∀ n, t + 1 ≤ n → coeff q n = 0) :
    ∀ (p : List R) (s : Nat), (∀ n, s + 1 ≤ n → coeff p n = 0) →
      coeff (mul p q) (s + t) = coeff p s * coeff q t ∧
      ∀ n, s + t + 1 ≤ n → coeff (mul p q) n = 0 := by
  intro p
  induction p with
  | nil =>
    intro s _
    exact ⟨by rw [show mul [] q = [] from rfl, coeff_nil, coeff_nil, zero_mul], fun n _ => rfl⟩
  | cons a p ih =>
    intro s hp
    cases s with
    | zero =>
      have hp0 : Eqv p [] := fun n => hp (n + 1) (by omega)
      have key : ∀ n, coeff (mul (a :: p) q) n = a * coeff q n := by
        intro n
        rw [coeff_mul_cons]
        cases n with
        | zero => rw [coeff_cons_zero, add_zero]
        | succ k => rw [coeff_cons_succ, coeff_mul_of_eqv_nil hp0, add_zero]
      refine ⟨by rw [Nat.zero_add, key]; rfl, fun n hn => ?_⟩
      rw [key, hq n (by omega), mul_zero]
    | succ s =>
      have hp' : ∀ n, s + 1 ≤ n → coeff p n = 0 := fun n hn => hp (n + 1) (by omega)
      obtain ⟨ih1, ih2⟩ := ih s hp'
      refine ⟨?_, fun n hn => ?_⟩
      · rw [show s + 1 + t = (s + t) + 1 by omega, coeff_mul_cons, coeff_cons_succ, ih1,
          hq _ (by omega), mul_zero, Ring.zero_add]
        rfl
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [coeff_mul_cons, coeff_cons_succ, ih2 k (by omega), hq _ (by omega), mul_zero,
          add_zero]

end PolyList

namespace Polynomial

variable {R : Type u} [CommRing R]

/-! ## The predicate `DegLT` -/

/-- `DegLT p d`: every coefficient of `p` at index `≥ d` vanishes, i.e. `deg p < d`. -/
def DegLT (p : Polynomial R) (d : Nat) : Prop := ∀ n, d ≤ n → coeff p n = 0

/-- `DegLT` is monotone in the bound. -/
theorem DegLT.mono {p : Polynomial R} {d e : Nat} (h : DegLT p d) (hde : d ≤ e) : DegLT p e :=
  fun n hn => h n (by omega)

/-- Only the zero polynomial satisfies `DegLT p 0`. -/
theorem degLT_zero_iff {p : Polynomial R} : DegLT p 0 ↔ p = 0 :=
  ⟨fun h => ext fun n => by rw [h n (Nat.zero_le n), coeff_zero],
   fun h n _ => by rw [h, coeff_zero]⟩

/-- **Top coefficients multiply.** If `deg p ≤ s` and `deg q ≤ t`, then the coefficient of
`p * q` at `s + t` is `pₛ · qₜ`, and `deg (p * q) ≤ s + t`. -/
theorem mul_top {p q : Polynomial R} {s t : Nat} (hp : DegLT p (s + 1)) (hq : DegLT q (t + 1)) :
    coeff (p * q) (s + t) = coeff p s * coeff q t ∧ DegLT (p * q) (s + t + 1) := by
  induction p using Quotient.ind with
  | _ lp =>
  induction q using Quotient.ind with
  | _ lq =>
  exact PolyList.mul_top lq t hq lp s hp

/-! ## Length, degree and leading coefficient -/

/-- Existence of a least bound. -/
theorem exists_len (p : Polynomial R) :
    ∃ d, DegLT p d ∧ ∀ m, m < d → ¬ DegLT p m :=
  FiniteType.exists_least _ (exists_bound p)

/-- The **length** of `p`: the least `d` with `DegLT p d`. It is `deg p + 1` for `p ≠ 0` and
`0` for `p = 0`. -/
noncomputable def len (p : Polynomial R) : Nat := Classical.choose (exists_len p)

/-- `p` vanishes from index `len p` on. -/
theorem degLT_len (p : Polynomial R) : DegLT p (len p) := (Classical.choose_spec (exists_len p)).1

/-- `len p` is the least bound. -/
theorem len_le {p : Polynomial R} {d : Nat} (h : DegLT p d) : len p ≤ d :=
  Nat.le_of_not_lt fun hlt => (Classical.choose_spec (exists_len p)).2 d hlt h

/-- `len p = 0` iff `p = 0`. -/
theorem len_eq_zero {p : Polynomial R} : len p = 0 ↔ p = 0 := by
  constructor
  · intro h; have := degLT_len p; rw [h] at this; exact degLT_zero_iff.1 this
  · intro h; apply Nat.eq_zero_of_le_zero; apply len_le; rw [h]; exact degLT_zero_iff.2 rfl

/-- The **degree** of a polynomial (with the convention `natDegree 0 = 0`). -/
noncomputable def natDegree (p : Polynomial R) : Nat := len p - 1

/-- The **leading coefficient**: the coefficient at the degree. -/
noncomputable def leadingCoeff (p : Polynomial R) : R := coeff p (natDegree p)

/-- For `p ≠ 0`, `len p = natDegree p + 1`. -/
theorem len_eq_natDegree_succ {p : Polynomial R} (hp : p ≠ 0) : len p = natDegree p + 1 := by
  have : len p ≠ 0 := fun h => hp (len_eq_zero.1 h)
  unfold natDegree; omega

/-- A non-zero polynomial vanishes above its degree. -/
theorem degLT_natDegree {p : Polynomial R} (hp : p ≠ 0) : DegLT p (natDegree p + 1) := by
  rw [← len_eq_natDegree_succ hp]; exact degLT_len p

/-- **The leading coefficient of a non-zero polynomial is non-zero.** -/
theorem leadingCoeff_ne_zero {p : Polynomial R} (hp : p ≠ 0) : leadingCoeff p ≠ 0 := by
  intro h
  have h1 : DegLT p (natDegree p) := by
    intro n hn
    rcases Nat.eq_or_lt_of_le hn with e | lt
    · rw [← e]; exact h
    · exact degLT_natDegree hp n lt
  have := len_le h1
  rw [len_eq_natDegree_succ hp] at this
  omega

/-! ## Polynomials over a domain -/

/-- **`R[x]` is an integral domain when `R` is**, and degrees add:
`deg (p q) = deg p + deg q` with leading coefficient `lc p · lc q`. -/
theorem mul_ne_zero_of_domain (hD : IsDomain R) {p q : Polynomial R} (hp : p ≠ 0) (hq : q ≠ 0) :
    p * q ≠ 0 ∧ coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q := by
  obtain ⟨h1, _⟩ := mul_top (degLT_natDegree hp) (degLT_natDegree hq)
  refine ⟨fun h => ?_, h1⟩
  rw [h, coeff_zero] at h1
  rcases hD.2 _ _ h1.symm with h | h
  · exact leadingCoeff_ne_zero hp h
  · exact leadingCoeff_ne_zero hq h

/-- `R[x]` is an integral domain whenever `R` is. -/
theorem isDomain (hD : IsDomain R) : IsDomain (Polynomial R) := by
  refine ⟨fun h => hD.1 ?_, fun p q hpq => ?_⟩
  · have := congrArg (fun p => coeff p 0) h
    exact this
  · apply Classical.byContradiction
    intro hne
    have hp : p ≠ 0 := fun h => hne (Or.inl h)
    have hq : q ≠ 0 := fun h => hne (Or.inr h)
    exact (mul_ne_zero_of_domain hD hp hq).1 hpq

/-! ## Powers of `X` -/

/-- The monomial `X ^ j`. -/
def Xpow : Nat → Polynomial R
  | 0 => 1
  | j + 1 => X * Xpow j

/-- Multiplying by `X ^ j` shifts coefficients up by `j`. -/
theorem coeff_Xpow_mul (j : Nat) (p : Polynomial R) (n : Nat) :
    coeff (Xpow j * p) n = if j ≤ n then coeff p (n - j) else 0 := by
  induction j generalizing n with
  | zero => show coeff (1 * p) n = _; rw [Ring.one_mul]; simp
  | succ j ih =>
    show coeff (X * Xpow j * p) n = _
    rw [Ring.mul_assoc]
    cases n with
    | zero => rw [coeff_X_mul_zero]; simp
    | succ k =>
      rw [coeff_X_mul_succ, ih]
      by_cases hjk : j ≤ k
      · rw [ite_true_of hjk, ite_true_of (by omega : j + 1 ≤ k + 1)]; congr 1; omega
      · rw [ite_false_of hjk, ite_false_of (by omega : ¬ j + 1 ≤ k + 1)]

/-! ## The division algorithm -/

/-- **Division with remainder by a polynomial with invertible leading coefficient.** If `g`
has degree `≤ m` and its coefficient at `m` is a unit (with inverse `u`), then every `p` can
be written `p = q * g + r` with `deg r < m`. Proved by long division: cancel the top
coefficient of `p` with a multiple `c u X^(k-m) g`, and recurse. -/
theorem div_mod_aux (g : Polynomial R) (m : Nat) (u : R) (hg : DegLT g (m + 1))
    (hu : coeff g m * u = 1) :
    ∀ (d : Nat) (p : Polynomial R), DegLT p d → ∃ q r, p = q * g + r ∧ DegLT r m := by
  intro d
  induction d with
  | zero => intro p hp; exact ⟨0, p, by rw [zero_mul, Ring.zero_add], hp.mono (Nat.zero_le m)⟩
  | succ k ih =>
    intro p hp
    by_cases hkm : k + 1 ≤ m
    · exact ⟨0, p, by rw [zero_mul, Ring.zero_add], hp.mono hkm⟩
    · have hmk : m ≤ k := by omega
      let c := coeff p k
      let t : Polynomial R := C (c * u) * (Xpow (k - m) * g)
      have hcoef : ∀ n, k ≤ n → coeff t n = if n = k then c else 0 := by
        intro n hn
        show coeff (C (c * u) * (Xpow (k - m) * g)) n = _
        rw [coeff_C_mul, coeff_Xpow_mul, ite_true_of (by omega)]
        by_cases hnk : n = k
        · rw [ite_true_of hnk, hnk, show k - (k - m) = m by omega, Ring.mul_assoc,
            CommRing.mul_comm u, hu, Ring.mul_one]
        · rw [ite_false_of hnk, hg _ (by omega), mul_zero]
      have hp' : DegLT (p + -t) k := by
        intro n hn
        rw [coeff_add, coeff_neg, hcoef n hn]
        by_cases hnk : n = k
        · rw [ite_true_of hnk, hnk, add_neg_cancel]
        · rw [ite_false_of hnk, hp n (by omega), neg_zero, add_zero]
      obtain ⟨q, r, hqr, hr⟩ := ih _ hp'
      refine ⟨q + C (c * u) * Xpow (k - m), r, ?_, hr⟩
      calc p = (p + -t) + t := by rw [Ring.add_assoc, neg_add_cancel, add_zero]
        _ = q * g + r + C (c * u) * (Xpow (k - m) * g) := by rw [hqr]
        _ = (q + C (c * u) * Xpow (k - m)) * g + r := by
          rw [right_distrib, Ring.mul_assoc]; ac_rfl

/-- **The division algorithm over a field.** If `g ≠ 0`, then every polynomial `p` can be
written `p = q * g + r` where `r = 0` or `deg r < deg g`. -/
theorem div_mod (hF : IsField R) (p g : Polynomial R) (hg : g ≠ 0) :
    ∃ q r, p = q * g + r ∧ (r = 0 ∨ natDegree r < natDegree g) := by
  obtain ⟨u, hu⟩ := hF.2 _ (leadingCoeff_ne_zero hg)
  obtain ⟨q, r, hqr, hr⟩ :=
    div_mod_aux g (natDegree g) u (degLT_natDegree hg) hu (len p) p (degLT_len p)
  refine ⟨q, r, hqr, ?_⟩
  by_cases hr0 : r = 0
  · exact Or.inl hr0
  · right
    have := len_le hr
    rw [len_eq_natDegree_succ hr0] at this
    omega

/-! ## The factor theorem -/

/-- Coefficients of `X`. -/
theorem coeff_X (n : Nat) : coeff (X : Polynomial R) n = if n = 1 then 1 else 0 := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp [X]

/-- The linear polynomial `X - a`. -/
def linear (a : R) : Polynomial R := X + -C a

/-- `X - a` has degree `≤ 1`. -/
theorem degLT_linear (a : R) : DegLT (linear a) 2 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp [linear, coeff_X, neg_zero, add_zero]

/-- The coefficient of `X` in `X - a` is `1`. -/
theorem coeff_linear_one (a : R) : coeff (linear a) 1 = 1 := by
  simp [linear, coeff_X, neg_zero, add_zero]

/-- `X - a` vanishes at `a`. -/
theorem eval_linear (a : R) : eval a (linear a) = 0 := by
  rw [linear, eval_add, eval_neg, eval_X, eval_C, add_neg_cancel]

/-- **The remainder theorem.** Dividing `p` by `X - a` leaves remainder `p(a)`:
`p = q * (X - a) + p(a)` for some `q`. -/
theorem remainder_theorem (p : Polynomial R) (a : R) :
    ∃ q, p = q * linear a + C (eval a p) := by
  obtain ⟨q, r, hqr, hr⟩ := div_mod_aux (linear a) 1 1 (degLT_linear a)
    (by rw [coeff_linear_one, Ring.mul_one]) (len p) p (degLT_len p)
  have hrC : r = C (coeff r 0) := ext fun n => by
    cases n with
    | zero => rfl
    | succ k => rw [hr _ (by omega), coeff_C_succ]
  refine ⟨q, ?_⟩
  have hev : eval a p = coeff r 0 := by
    rw [hqr, eval_add, eval_mul, eval_linear, mul_zero, Ring.zero_add, hrC, eval_C]
    exact (coeff_C_zero _).symm
  rw [hev, ← hrC]; exact hqr

/-- **The factor theorem** (Descartes). `a` is a root of `p` if and only if `X - a` divides
`p`. -/
theorem factor_theorem (p : Polynomial R) (a : R) :
    eval a p = 0 ↔ ∃ q, p = linear a * q := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := remainder_theorem p a
    refine ⟨q, ?_⟩
    rw [hq, h, C_zero, add_zero, CommRing.mul_comm]
  · intro ⟨q, hq⟩
    rw [hq, eval_mul, eval_linear, zero_mul]

/-! ## Counting roots -/

/-- **A non-zero polynomial of degree `≤ n` over an integral domain has at most `n` roots.**
Any list of distinct roots has length at most `n`. -/
theorem card_roots_le (hD : IsDomain R) :
    ∀ (L : List R) (n : Nat) (p : Polynomial R), p ≠ 0 → DegLT p (n + 1) → L.Nodup →
      (∀ a, a ∈ L → eval a p = 0) → L.length ≤ n := by
  intro L
  induction L with
  | nil => intro n _ _ _ _ _; exact Nat.zero_le n
  | cons a L ih =>
    intro n p hp hdeg hnd hroots
    rw [List.nodup_cons] at hnd
    obtain ⟨q, hq⟩ := (factor_theorem p a).1 (hroots a (List.mem_cons_self))
    have hq0 : q ≠ 0 := by intro h; apply hp; rw [hq, h, mul_zero]
    -- The degree drops by one.
    obtain ⟨htop, _⟩ := mul_top (s := 1) (degLT_linear a) (degLT_natDegree hq0)
    rw [coeff_linear_one, Ring.one_mul] at htop
    have hlt : 1 + natDegree q < n + 1 := by
      apply Classical.byContradiction
      intro hge
      apply leadingCoeff_ne_zero hq0
      rw [leadingCoeff, ← htop, ← hq]
      exact hdeg _ (by omega)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hdeg' : DegLT q (n' + 1) := (degLT_natDegree hq0).mono (by omega)
    -- The remaining roots are roots of `q`.
    have hroots' : ∀ b, b ∈ L → eval b q = 0 := by
      intro b hb
      have h1 := hroots b (List.mem_cons_of_mem a hb)
      rw [hq, eval_mul] at h1
      rcases hD.2 _ _ h1 with h | h
      · exfalso
        rw [linear, eval_add, eval_neg, eval_X, eval_C] at h
        exact hnd.1 (eq_of_sub_eq_zero h ▸ hb)
      · exact h
    have := ih n' q hq0 hdeg' hnd.2 hroots'
    simp only [List.length_cons]
    omega

/-- **Root bound, degree form.** A non-zero polynomial over an integral domain has at most
`deg p` distinct roots. -/
theorem card_roots_le_natDegree (hD : IsDomain R) {p : Polynomial R} (hp : p ≠ 0)
    (L : List R) (hL : L.Nodup) (hroots : ∀ a, a ∈ L → eval a p = 0) :
    L.length ≤ natDegree p :=
  card_roots_le hD L _ p hp (degLT_natDegree hp) hL hroots

end Polynomial

end Foundations.Algebra
