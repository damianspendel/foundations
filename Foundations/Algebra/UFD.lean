import Foundations.Algebra.PID

/-!
# Unique factorisation

The **fundamental theorem of arithmetic** — every integer `n ≥ 2` is a product of primes,
uniquely up to order — is implicit in Euclid and was first stated and proved with full
clarity by Gauss in the *Disquisitiones Arithmeticae* (1801). Its failure in rings such as
`ℤ[√-5]`, where `6 = 2 · 3 = (1 + √-5)(1 - √-5)`, was the crisis that led Kummer to "ideal
numbers" and Dedekind to ideals.

A factorisation theorem has two halves, and they rest on different foundations.

* **Uniqueness** follows from Euclid's lemma alone: in any integral domain in which every
  irreducible element is prime (in particular in every PID, by the previous file), two
  factorisations of the same element into irreducibles agree up to order and unit factors.
  The proof is Euclid's: a prime factor on one side divides the product on the other, hence
  divides — and is associated to — one of its factors, which can then be cancelled.
* **Existence** is a finiteness property: factoring cannot go on forever. We prove it for
  `ℤ` (by induction on absolute value) and for `F[x]` over a field (by induction on degree).

Since factorisations are unique only "up to order and units", we compare them by counting,
for each `x`, how many factors are **associated** to `x` (equal to it up to a unit factor):
a factorisation is in effect a multiset of associate classes.
-/

namespace Foundations.Algebra

open Ring

universe u

section General

variable {R : Type u} [CommRing R]

/-- The **product** of a list of ring elements. -/
def lprod : List R → R
  | [] => 1
  | a :: l => a * lprod l

/-- The product of a concatenation. -/
theorem lprod_append (L M : List R) : lprod (L ++ M) = lprod L * lprod M := by
  induction L with
  | nil => exact (Ring.one_mul _).symm
  | cons a L ih => show a * lprod (L ++ M) = a * lprod L * lprod M; rw [ih, Ring.mul_assoc]

/-- The product does not depend on the order of the factors. -/
theorem lprod_perm {L M : List R} (h : L.Perm M) : lprod L = lprod M := by
  induction h with
  | nil => rfl
  | cons a _ ih => show a * _ = a * _; rw [ih]
  | swap a b l => show b * (a * lprod l) = a * (b * lprod l); ac_rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two elements are **associated** if they differ by a unit factor. -/
def Associated (a b : R) : Prop := ∃ u, IsUnit u ∧ b = a * u

/-- Associatedness is reflexive. -/
theorem Associated.refl (a : R) : Associated a a := ⟨1, ⟨1, Ring.mul_one 1⟩, (Ring.mul_one a).symm⟩

/-- Associatedness is symmetric. -/
theorem Associated.symm {a b : R} (h : Associated a b) : Associated b a := by
  obtain ⟨u, ⟨v, huv⟩, rfl⟩ := h
  refine ⟨v, ⟨u, by rw [CommRing.mul_comm, huv]⟩, ?_⟩
  rw [Ring.mul_assoc, huv, Ring.mul_one]

/-- Associatedness is transitive. -/
theorem Associated.trans {a b c : R} (h1 : Associated a b) (h2 : Associated b c) :
    Associated a c := by
  obtain ⟨u, ⟨u', hu⟩, rfl⟩ := h1
  obtain ⟨v, ⟨v', hv⟩, rfl⟩ := h2
  refine ⟨u * v, ⟨u' * v', ?_⟩, Ring.mul_assoc _ _ _⟩
  calc u * v * (u' * v') = (u * u') * (v * v') := by ac_rfl
    _ = 1 := by rw [hu, hv, Ring.mul_one]

/-- A product of units is a unit. -/
theorem IsUnit.mul {a b : R} (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a * b) := by
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  exact ⟨a' * b', by
    calc a * b * (a' * b') = (a * a') * (b * b') := by ac_rfl
      _ = 1 := by rw [ha', hb', Ring.mul_one]⟩

/-- A divisor of a unit is a unit. -/
theorem IsUnit.of_dvd {a u : R} (hu : IsUnit u) (h : Divides a u) : IsUnit a := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨v, hv⟩ := hu
  exact ⟨c * v, by rw [← Ring.mul_assoc]; exact hv⟩

/-- **Euclid's lemma for products of many factors.** A prime dividing a product of a list
divides one of its entries. -/
theorem IsPrimeElt.dvd_lprod {p : R} (hp : IsPrimeElt p) :
    ∀ M : List R, Divides p (lprod M) → ∃ q, q ∈ M ∧ Divides p q := by
  intro M
  induction M with
  | nil => intro h; exact absurd (IsUnit.of_dvd ⟨1, Ring.mul_one 1⟩ h) hp.2.1
  | cons q M ih =>
    intro h
    rcases hp.2.2 q (lprod M) h with h1 | h1
    · exact ⟨q, List.mem_cons_self, h1⟩
    · obtain ⟨q', hq', hd⟩ := ih h1
      exact ⟨q', List.mem_cons_of_mem q hq', hd⟩

/-- A non-unit dividing an irreducible element is associated to it. -/
theorem Irreducible.associated_of_dvd {p q : R} (hq : Irreducible q) (hp : ¬ IsUnit p)
    (h : Divides p q) : Associated p q := by
  obtain ⟨c, hc⟩ := h
  rcases hq.2.2 p c hc with h1 | h1
  · exact absurd h1 hp
  · exact ⟨c, h1, hc⟩

/-- The number of entries of `L` associated to `x`. -/
noncomputable def countAssoc (x : R) (L : List R) : Nat := by
  classical exact L.countP (fun y => decide (Associated x y))

/-- Counting associates in a cons. -/
theorem countAssoc_cons (x a : R) (L : List R) :
    countAssoc x (a :: L) = countAssoc x L + (by classical exact if Associated x a then 1 else 0) := by
  classical
  unfold countAssoc
  rw [List.countP_cons]
  simp

/-- Counting associates does not depend on order. -/
theorem countAssoc_perm (x : R) {L M : List R} (h : L.Perm M) : countAssoc x L = countAssoc x M := by
  classical
  unfold countAssoc
  exact h.countP_eq _

/-- **Uniqueness of factorisation.** In an integral domain in which every irreducible element
is prime — for instance any principal ideal domain — two factorisations into irreducibles of
associated elements agree up to order and units: if `∏ L = u · ∏ M` with `u` a unit, then for
every `x`, `L` and `M` contain equally many factors associated to `x`. -/
theorem factorization_unique (hD : IsDomain R) (hprime : ∀ p : R, Irreducible p → IsPrimeElt p) :
    ∀ (L M : List R) (u : R), (∀ p, p ∈ L → Irreducible p) → (∀ q, q ∈ M → Irreducible q) →
      IsUnit u → lprod L = u * lprod M → ∀ x, countAssoc x L = countAssoc x M := by
  intro L
  induction L with
  | nil =>
    intro M u _ hM hu h x
    cases M with
    | nil => rfl
    | cons q M =>
      exfalso
      apply (hM q List.mem_cons_self).2.1
      apply IsUnit.of_dvd ⟨1, Ring.mul_one 1⟩
      exact ⟨u * lprod M, by
        show (1 : R) = q * (u * lprod M)
        rw [show (1 : R) = lprod [] from rfl, h]
        show u * (q * lprod M) = _
        ac_rfl⟩
  | cons p L ih =>
    intro M u hL hM hu h x
    have hp := hprime p (hL p List.mem_cons_self)
    -- `p` divides `∏ M`, hence some `q ∈ M`, to which it is associated.
    have hdvd : Divides p (lprod M) := by
      obtain ⟨v, hv⟩ := hu
      exact ⟨v * lprod L, by
        calc lprod M = (u * v) * lprod M := by rw [hv, Ring.one_mul]
          _ = v * (u * lprod M) := by ac_rfl
          _ = v * (p * lprod L) := by rw [← h]; rfl
          _ = p * (v * lprod L) := by ac_rfl⟩
    obtain ⟨q, hqM, hpq⟩ := hp.dvd_lprod M hdvd
    have hassoc := (hM q hqM).associated_of_dvd hp.2.1 hpq
    obtain ⟨c, hc, hcq⟩ := hassoc
    obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem hqM
    have hperm : (M₁ ++ q :: M₂).Perm (q :: (M₁ ++ M₂)) := List.perm_middle
    -- Cancel `p`.
    have h' : lprod L = (u * c) * lprod (M₁ ++ M₂) := by
      apply hD.mul_left_cancel hp.1
      calc p * lprod L = lprod (p :: L) := rfl
        _ = u * lprod (q :: (M₁ ++ M₂)) := by rw [h, lprod_perm hperm]
        _ = p * (u * c * lprod (M₁ ++ M₂)) := by
            show u * (q * _) = _; rw [hcq]; ac_rfl
    have hM' : ∀ r, r ∈ M₁ ++ M₂ → Irreducible r := by
      intro r hr
      apply hM r
      rw [List.mem_append] at hr ⊢
      rcases hr with hr | hr
      · exact Or.inl hr
      · exact Or.inr (List.mem_cons_of_mem q hr)
    have ihx := ih (M₁ ++ M₂) (u * c) (fun r hr => hL r (List.mem_cons_of_mem p hr)) hM'
      (hu.mul hc) h' x
    rw [countAssoc_perm x hperm, countAssoc_cons, countAssoc_cons, ihx]
    congr 1
    classical
    have : Associated x p ↔ Associated x q :=
      ⟨fun h1 => h1.trans ⟨c, hc, hcq⟩, fun h1 => h1.trans (Associated.symm ⟨c, hc, hcq⟩)⟩
    simp only [this]

/-- **Uniqueness of factorisation in a PID.** -/
theorem IsPID.factorization_unique (hP : IsPID R) (L M : List R) (u : R)
    (hL : ∀ p, p ∈ L → Irreducible p) (hM : ∀ q, q ∈ M → Irreducible q) (hu : IsUnit u)
    (h : lprod L = u * lprod M) (x : R) : countAssoc x L = countAssoc x M :=
  Foundations.Algebra.factorization_unique hP.1 (fun _ hp => hP.irreducible_isPrime hp)
    L M u hL hM hu h x

end General

/-! ## Existence: the integers -/

/-- The units of `ℤ` are the elements of absolute value `1`. -/
theorem int_isUnit_iff (a : Int) : IsUnit a ↔ a.natAbs = 1 := by
  constructor
  · intro ⟨b, hb⟩
    have := congrArg Int.natAbs hb
    rw [Int.natAbs_mul] at this
    exact Nat.eq_one_of_mul_eq_one_right this
  · intro h
    rcases Int.natAbs_eq a with e | e <;> rw [h] at e <;> subst e
    · exact ⟨1, rfl⟩
    · exact ⟨-1, rfl⟩

/-- **Existence of factorisations in `ℤ`** (fundamental theorem of arithmetic, existence
half). Every non-zero non-unit integer is a product of irreducibles. -/
theorem int_exists_factorization :
    ∀ (n : Nat) (a : Int), a.natAbs = n → a ≠ 0 → ¬ IsUnit a →
      ∃ L : List Int, (∀ p, p ∈ L → Irreducible p) ∧ lprod L = a := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a han ha0 hau
    by_cases hirr : Irreducible a
    · exact ⟨[a], fun p hp => by rw [List.mem_singleton.1 hp]; exact hirr,
        show a * 1 = a from Int.mul_one a⟩
    · have : ∃ b c, a = b * c ∧ ¬ IsUnit b ∧ ¬ IsUnit c := by
        apply Classical.byContradiction
        intro hno
        apply hirr
        refine ⟨ha0, hau, fun b c hbc => ?_⟩
        apply Classical.byContradiction
        intro hbc'
        exact hno ⟨b, c, hbc, fun h => hbc' (Or.inl h), fun h => hbc' (Or.inr h)⟩
      obtain ⟨b, c, rfl, hb, hc⟩ := this
      have hb0 : b ≠ 0 := by intro h; apply ha0; rw [h]; exact Int.zero_mul c
      have hc0 : c ≠ 0 := by intro h; apply ha0; rw [h]; exact Int.mul_zero b
      have hb2 : 2 ≤ b.natAbs := by
        have h1 : b.natAbs ≠ 1 := fun e => hb ((int_isUnit_iff b).2 e)
        have h2 : b.natAbs ≠ 0 := fun e => hb0 (Int.natAbs_eq_zero.1 e)
        omega
      have hc2 : 2 ≤ c.natAbs := by
        have h1 : c.natAbs ≠ 1 := fun e => hc ((int_isUnit_iff c).2 e)
        have h2 : c.natAbs ≠ 0 := fun e => hc0 (Int.natAbs_eq_zero.1 e)
        omega
      have hmul : (b * c).natAbs = b.natAbs * c.natAbs := Int.natAbs_mul b c
      have hbl : b.natAbs < n := by
        have := Nat.mul_le_mul_left b.natAbs hc2; omega
      have hcl : c.natAbs < n := by
        have := Nat.mul_le_mul_right c.natAbs hb2; omega
      obtain ⟨L1, hL1, hp1⟩ := ih _ hbl b rfl hb0 hb
      obtain ⟨L2, hL2, hp2⟩ := ih _ hcl c rfl hc0 hc
      refine ⟨L1 ++ L2, fun p hp => ?_, by rw [lprod_append, hp1, hp2]⟩
      rcases List.mem_append.1 hp with h | h
      · exact hL1 p h
      · exact hL2 p h

/-- **The fundamental theorem of arithmetic.** Every non-zero non-unit integer is a product
of irreducible integers, and any two such factorisations agree up to order and signs. -/
theorem fundamental_theorem_of_arithmetic (a : Int) (ha0 : a ≠ 0) (hau : ¬ IsUnit a) :
    (∃ L : List Int, (∀ p, p ∈ L → Irreducible p) ∧ lprod L = a) ∧
    ∀ L M : List Int, (∀ p, p ∈ L → Irreducible p) → (∀ q, q ∈ M → Irreducible q) →
      lprod L = a → lprod M = a → ∀ x, countAssoc x L = countAssoc x M :=
  ⟨int_exists_factorization _ a rfl ha0 hau, fun L M hL hM h1 h2 x =>
    int_isPID.factorization_unique L M 1 hL hM ⟨1, rfl⟩ (by rw [h1, h2]; exact (Int.one_mul a).symm) x⟩

/-! ## Existence: polynomials over a field -/

namespace Polynomial

variable {F : Type u} [CommRing F]

/-- **Degrees add** in a polynomial ring over a domain. -/
theorem natDegree_mul (hD : IsDomain F) {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q := by
  obtain ⟨hpq, hcoef⟩ := mul_ne_zero_of_domain hD hp hq
  have hlt := len_le (mul_top (degLT_natDegree hp) (degLT_natDegree hq)).2
  have hge : natDegree p + natDegree q + 1 ≤ len (p * q) := by
    apply Classical.byContradiction
    intro hlt'
    have := (degLT_len (p * q)) (natDegree p + natDegree q) (by omega)
    rw [hcoef] at this
    rcases hD.2 _ _ this with h | h
    · exact leadingCoeff_ne_zero hp h
    · exact leadingCoeff_ne_zero hq h
  rw [len_eq_natDegree_succ hpq] at hlt hge
  omega

/-- A non-zero polynomial of degree `0` over a field is a unit. -/
theorem isUnit_of_natDegree_zero (hF : IsField F) {p : Polynomial F} (hp : p ≠ 0)
    (h0 : natDegree p = 0) : IsUnit p := by
  have hpC : p = C (coeff p 0) := ext fun n => by
    cases n with
    | zero => rfl
    | succ k => rw [degLT_natDegree hp _ (by omega), coeff_C_succ]
  have hc : coeff p 0 ≠ 0 := by
    intro h; apply hp; rw [hpC, h, C_zero]
  obtain ⟨d, hd⟩ := hF.2 _ hc
  exact ⟨C d, by rw [hpC, ← C_mul, hd, C_one]⟩

/-- **Existence of factorisations in `F[x]`.** Over a field, every non-zero non-unit
polynomial is a product of irreducible polynomials. -/
theorem exists_factorization (hF : IsField F) :
    ∀ (n : Nat) (p : Polynomial F), natDegree p = n → p ≠ 0 → ¬ IsUnit p →
      ∃ L : List (Polynomial F), (∀ q, q ∈ L → Irreducible q) ∧ lprod L = p := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro p hpn hp0 hpu
    by_cases hirr : Irreducible p
    · exact ⟨[p], fun q hq => by rw [List.mem_singleton.1 hq]; exact hirr, Ring.mul_one p⟩
    · have : ∃ b c, p = b * c ∧ ¬ IsUnit b ∧ ¬ IsUnit c := by
        apply Classical.byContradiction
        intro hno
        apply hirr
        refine ⟨hp0, hpu, fun b c hbc => ?_⟩
        apply Classical.byContradiction
        intro hbc'
        exact hno ⟨b, c, hbc, fun h => hbc' (Or.inl h), fun h => hbc' (Or.inr h)⟩
      obtain ⟨b, c, rfl, hb, hc⟩ := this
      have hb0 : b ≠ 0 := by intro h; apply hp0; rw [h, zero_mul]
      have hc0 : c ≠ 0 := by intro h; apply hp0; rw [h, mul_zero]
      have hdeg := natDegree_mul hF.isDomain hb0 hc0
      have hb1 : natDegree b ≠ 0 := fun h => hb (isUnit_of_natDegree_zero hF hb0 h)
      have hc1 : natDegree c ≠ 0 := fun h => hc (isUnit_of_natDegree_zero hF hc0 h)
      obtain ⟨L1, hL1, hp1⟩ := ih _ (by omega) b rfl hb0 hb
      obtain ⟨L2, hL2, hp2⟩ := ih _ (by omega) c rfl hc0 hc
      refine ⟨L1 ++ L2, fun q hq => ?_, by rw [lprod_append, hp1, hp2]⟩
      rcases List.mem_append.1 hq with h | h
      · exact hL1 q h
      · exact hL2 q h

/-- **Unique factorisation in `F[x]`.** Over a field, every non-zero non-unit polynomial is a
product of irreducible polynomials, uniquely up to order and constant factors. -/
theorem unique_factorization (hF : IsField F) (p : Polynomial F) (hp0 : p ≠ 0)
    (hpu : ¬ IsUnit p) :
    (∃ L : List (Polynomial F), (∀ q, q ∈ L → Irreducible q) ∧ lprod L = p) ∧
    ∀ L M : List (Polynomial F), (∀ q, q ∈ L → Irreducible q) → (∀ q, q ∈ M → Irreducible q) →
      lprod L = p → lprod M = p → ∀ x, countAssoc x L = countAssoc x M :=
  ⟨exists_factorization hF _ p rfl hp0 hpu, fun L M hL hM h1 h2 x =>
    (polynomial_isPID hF).factorization_unique L M 1 hL hM ⟨1, Ring.mul_one 1⟩
      (by rw [h1, h2, Ring.one_mul]) x⟩

end Polynomial

end Foundations.Algebra
