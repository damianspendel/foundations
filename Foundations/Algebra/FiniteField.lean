import Foundations.Algebra.Constructible

/-!
# Finite fields have prime-power order

Galois, in a paper of 1830 written at the age of eighteen, introduced the "imaginary"
solutions of congruences modulo a prime and thereby created the finite fields now named after
him. Their first structural property is a striking restriction on size: **a finite field has
`pⁿ` elements for some prime `p`** — there are fields with 2, 3, 4, 5, 7, 8, 9 elements, but
none with 6 or 10.

The proof is a beautiful application of the linear algebra of this chapter.

* Adding `1` to itself repeatedly must eventually give `0` (the field is finite); the least
  number of steps, the **characteristic** `p`, is prime, because the field has no zero
  divisors.
* The multiples `0, 1, 2·1, …, (p-1)·1` form a subfield with exactly `p` elements, the
  **prime field** — a copy of `ℤ/pℤ`.
* The whole field is a finite-dimensional vector space over its prime field; choosing a basis
  of size `n` identifies it with the set of `n`-tuples of elements of the prime field, of
  which there are `pⁿ`.
-/

namespace Foundations.Algebra

open Ring FiniteType VectorSpace Subfield KSubspace

universe u

section Casts

variable {R : Type u} [CommRing R]

/-- `ncast` is additive. -/
theorem ncast_add (a b : Nat) : (ncast (a + b) : R) = ncast a + ncast b :=
  Lean.Grind.Semiring.natCast_add (α := R) a b

/-- `ncast` is multiplicative. -/
theorem ncast_mul (a b : Nat) : (ncast (a * b) : R) = ncast a * ncast b :=
  Lean.Grind.Semiring.natCast_mul (α := R) a b

/-- Powers add: `x^(m+n) = x^m x^n`. -/
theorem rpow_add (x : R) (m n : Nat) : rpow x (m + n) = rpow x m * rpow x n := by
  induction n with
  | zero => exact (Ring.mul_one _).symm
  | succ n ih => show rpow x (m + n) * x = rpow x m * (rpow x n * x); rw [ih, Ring.mul_assoc]

end Casts

/-- A sum over a finite type in which only the term at `a` can be non-zero equals that term. -/
theorem isum_single {A : Type u} [AddAbGroup A] {ι : Type u} [FiniteType ι] (f : ι → A) (a : ι)
    (hf : ∀ i, i ≠ a → f i = 0) : isum f = f a := by
  have key : ∀ l : List ι, l.Nodup → lsum (l.map f) = (by classical exact if a ∈ l then f a else 0) := by
    intro l hl
    classical
    induction l with
    | nil => simp [lsum]
    | cons b l ih =>
      rw [List.nodup_cons] at hl
      show f b + lsum (l.map f) = _
      rw [ih hl.2]
      by_cases hb : b = a
      · subst hb; simp [hl.1, AddAbGroup.add_zero]
      · rw [hf b hb, AddAbGroup.zero_add]
        by_cases ha : a ∈ l
        · simp [ha]
        · have : a ∉ b :: l := by simp [ha, Ne.symm hb]
          simp [ha, this]
  classical
  unfold isum
  rw [key _ nodup]
  simp [complete]

section FiniteField

variable {F : Type u} [CommRing F] [FiniteType F] (hF : IsField F)

/-- In a finite field, some positive multiple of `1` is `0`. -/
theorem exists_ncast_eq_zero : ∃ p, 0 < p ∧ (ncast p : F) = 0 := by
  apply Classical.byContradiction
  intro hno
  have hinj : ∀ i j : Nat, (ncast i : F) = ncast j → i = j := by
    intro i j h
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exfalso; apply hno; refine ⟨j - i, by omega, ?_⟩
      have e := ncast_add (R := F) i (j - i)
      rw [show i + (j - i) = j by omega, ← h] at e
      grind
    · exact heq
    · exfalso; apply hno; refine ⟨i - j, by omega, ?_⟩
      have e := ncast_add (R := F) j (i - j)
      rw [show j + (i - j) = i by omega, h] at e
      grind
  have hnd := nodup_map_of_injective hinj (List.nodup_range (n := card F + 1))
  have := length_le_card hnd
  rw [List.length_map, List.length_range] at this
  omega

/-- The **characteristic** of a finite field: the least `p > 0` with `p · 1 = 0`. -/
theorem exists_char : ∃ p, (0 < p ∧ (ncast p : F) = 0) ∧ ∀ m, m < p → ¬ (0 < m ∧ (ncast m : F) = 0) :=
  FiniteType.exists_least _ exists_ncast_eq_zero

omit [FiniteType F] in
include hF in
/-- **The characteristic of a finite field is prime.** -/
theorem char_prime {p : Nat} (hp : 0 < p ∧ (ncast p : F) = 0)
    (hmin : ∀ m, m < p → ¬ (0 < m ∧ (ncast m : F) = 0)) : IsPrime p := by
  have h1 : p ≠ 1 := by intro h; rw [h] at hp; exact hF.1 hp.2.symm
  refine ⟨by omega, fun d hd => ?_⟩
  obtain ⟨e, he⟩ := hd
  have hd0 : 0 < d := by apply Nat.pos_of_ne_zero; intro h; rw [h] at he; omega
  have he0 : 0 < e := by apply Nat.pos_of_ne_zero; intro h; rw [h] at he; omega
  have hprod : (ncast d : F) * ncast e = 0 := by rw [← ncast_mul, ← he]; exact hp.2
  rcases hF.isDomain.2 _ _ hprod with h | h
  · have : ¬ d < p := fun hlt => hmin d hlt ⟨hd0, h⟩
    right; have := Nat.le_of_dvd hp.1 ⟨e, he⟩; omega
  · have : ¬ e < p := fun hlt => hmin e hlt ⟨he0, h⟩
    left
    have : d * e ≥ d * p := Nat.mul_le_mul_left d (by omega)
    have : d * p ≥ 1 * p := Nat.mul_le_mul_right p hd0
    have : e ≤ p := Nat.le_of_dvd hp.1 ⟨d, by rw [he, Nat.mul_comm]⟩
    have : d * e = p := he.symm
    rcases Nat.lt_or_ge 1 d with hd1 | hd1
    · have : d * e ≥ 2 * e := Nat.mul_le_mul_right e hd1
      omega
    · omega

variable {p : Nat} (hp : 0 < p ∧ (ncast p : F) = 0)
  (hmin : ∀ m, m < p → ¬ (0 < m ∧ (ncast m : F) = 0))

omit [FiniteType F] in
include hp in
/-- `-1 = (p - 1) · 1` in characteristic `p`. -/
theorem ncast_pred : (ncast (p - 1) : F) = -1 := by
  have e := ncast_add (R := F) (p - 1) 1
  rw [show p - 1 + 1 = p by omega, hp.2] at e
  have : (ncast 1 : F) = 1 := rfl
  grind

include hF in
/-- Non-zero elements of a finite field have a power equal to `1`. -/
theorem exists_rpow_eq_one {x : F} (hx : x ≠ 0) : ∃ m, 0 < m ∧ rpow x m = 1 := by
  have hnz : ∀ n, rpow x n ≠ 0 := by
    intro n
    induction n with
    | zero => exact fun h => hF.1 h.symm
    | succ n ih =>
      intro h
      rcases hF.isDomain.2 _ _ h with h1 | h1
      · exact ih h1
      · exact hx h1
  apply Classical.byContradiction
  intro hno
  have hinj : ∀ i j : Nat, rpow x i = rpow x j → i = j := by
    intro i j h
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exfalso; apply hno; refine ⟨j - i, by omega, ?_⟩
      have e := rpow_add x i (j - i)
      rw [show i + (j - i) = j by omega, ← h] at e
      have h0 : rpow x i * (rpow x (j - i) + -1) = 0 := by grind
      rcases hF.isDomain.2 _ _ h0 with h1 | h1
      · exact absurd h1 (hnz i)
      · grind
    · exact heq
    · exfalso; apply hno; refine ⟨i - j, by omega, ?_⟩
      have e := rpow_add x j (i - j)
      rw [show j + (i - j) = i by omega, h] at e
      have h0 : rpow x j * (rpow x (i - j) + -1) = 0 := by grind
      rcases hF.isDomain.2 _ _ h0 with h1 | h1
      · exact absurd h1 (hnz j)
      · grind
  have hnd := nodup_map_of_injective hinj (List.nodup_range (n := card F + 1))
  have := length_le_card hnd
  rw [List.length_map, List.length_range] at this
  omega

/-- **The prime field** `{0, 1, 2·1, …}` of a finite field of characteristic `p`. -/
def primeSubfield : Subfield F where
  carrier x := ∃ k, x = ncast k
  zero_mem := ⟨0, rfl⟩
  one_mem := ⟨1, rfl⟩
  add_mem := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [ha, hb, ncast_add]⟩
  neg_mem := by
    intro x ⟨k, hk⟩
    refine ⟨(p - 1) * k, ?_⟩
    rw [ncast_mul, ncast_pred hp, hk]; grind
  mul_mem := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [ha, hb, ncast_mul]⟩
  inv_mem := by
    intro x hxP hx0
    obtain ⟨m, hm, hxm⟩ := exists_rpow_eq_one hF hx0
    have hpow : ∀ n, ∃ k, rpow x n = ncast k := by
      intro n
      induction n with
      | zero => exact ⟨1, rfl⟩
      | succ n ih =>
        obtain ⟨k, hk⟩ := ih
        obtain ⟨j, hj⟩ := hxP
        exact ⟨k * j, by show rpow x n * x = _; rw [hk, hj, ncast_mul]⟩
    refine ⟨rpow x (m - 1), hpow (m - 1), ?_⟩
    have := rpow_add x (m - 1) 1
    rw [show m - 1 + 1 = m by omega, hxm] at this
    have e : rpow x 1 = x := by show 1 * x = x; exact Ring.one_mul x
    rw [e] at this
    rw [CommRing.mul_comm]; exact this.symm

include hmin in
/-- **The prime field has exactly `p` elements**: the residues `0, 1, …, p-1` give distinct
elements, and every multiple of `1` is one of them. -/
theorem card_primeSubfield : card {x // x ∈ primeSubfield hF hp} = p := by
  let e : Fin p → {x // x ∈ primeSubfield hF hp} := fun k => ⟨ncast k.val, k.val, rfl⟩
  have hmod : ∀ k, (ncast k : F) = ncast (k % p) := by
    intro k
    have := ncast_add (R := F) (k % p) (p * (k / p))
    rw [Nat.mod_add_div, ncast_mul, hp.2, Ring.zero_mul, Ring.add_zero] at this
    exact this
  have hinj : ∀ a b, e a = e b → a = b := by
    intro a b hab
    have h : (ncast a.val : F) = ncast b.val := congrArg Subtype.val hab
    apply Fin.ext
    apply Classical.byContradiction
    intro hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have e1 := ncast_add (R := F) a.val (b.val - a.val)
      rw [show a.val + (b.val - a.val) = b.val by omega, ← h] at e1
      exact hmin (b.val - a.val) (by omega) ⟨by omega, by grind⟩
    · have e1 := ncast_add (R := F) b.val (a.val - b.val)
      rw [show b.val + (a.val - b.val) = a.val by omega, h] at e1
      exact hmin (a.val - b.val) (by omega) ⟨by omega, by grind⟩
  have hsurj : ∀ y, ∃ k, e k = y := by
    intro ⟨y, k, hk⟩
    refine ⟨⟨k % p, Nat.mod_lt _ hp.1⟩, Subtype.ext ?_⟩
    show (ncast (k % p) : F) = y
    rw [hk]; exact (hmod k).symm
  have := count_comp_bij e hinj hsurj (fun _ => True)
  rw [count_true, count_true, card_fin] at this
  exact this.symm

/-- The whole field, as a subfield of itself. -/
def topSubfield : Subfield F where
  carrier _ := True
  zero_mem := trivial
  one_mem := trivial
  add_mem _ _ := trivial
  neg_mem _ := trivial
  mul_mem _ _ := trivial
  inv_mem := by intro a _ ha; obtain ⟨b, hb⟩ := hF.2 a ha; exact ⟨b, trivial, hb⟩

include hF in
/-- **Finite fields have prime-power order.** Every finite field has `pⁿ` elements, where the
prime `p` is its characteristic and `n` is its dimension over the prime field. -/
theorem finite_field_card : ∃ p n, IsPrime p ∧ card F = p ^ n := by
  obtain ⟨p, hp, hmin⟩ := exists_char (F := F)
  have hpr := char_prime hF hp hmin
  let P := primeSubfield hF hp
  let T := topSubfield hF
  have hPT : P.le T := fun _ _ => trivial
  let V := T.over P hPT
  have hFP := P.isField hF
  -- `F` is finite-dimensional over `P`: the family of all elements spans.
  have hspan : Spans P (fun y : F => (⟨y, trivial⟩ : V)) := by
    intro x
    classical
    refine ⟨fun i => if i = x.1 then 1 else 0, Subtype.ext ?_⟩
    rw [coe_isum]
    rw [isum_single _ x.1 (fun i hi => by
      show (if i = x.1 then (1 : P) else 0).1 * i = 0
      rw [ite_false_of hi]; exact Ring.zero_mul i)]
    show x.1 = (if x.1 = x.1 then (1 : P) else 0).1 * x.1
    rw [ite_true_of rfl]; exact (Ring.one_mul x.1).symm
  have hfin : FinDim P V := finDim_of_spans hspan
  obtain ⟨b, hb⟩ := exists_basis hFP hfin
  -- Coordinates with respect to the basis identify `F` with `Pⁿ`.
  let Φ : (Fin (dim P V) → P) → V := fun c => isum (fun i => c i • b i)
  have hinj : ∀ c d, Φ c = Φ d → c = d := by
    intro c d h
    have h' := congrArg Subtype.val h
    simp only [Φ, coe_isum] at h'
    have hz := hb.1 (fun i => c i + -d i) (by
      apply Subtype.ext
      rw [coe_isum]
      show isum (fun i => (c i + -d i).1 * (b i).1) = 0
      have e : (fun i => (c i + -d i).1 * (b i).1) =
          fun i => (c i • b i).1 + -(d i • b i).1 := by
        funext i; show ((c i).1 + -(d i).1) * (b i).1 = (c i).1 * (b i).1 + -((d i).1 * (b i).1)
        grind
      rw [e, isum_add, isum_neg, h']
      exact Ring.add_neg_cancel _)
    funext i
    apply Subtype.ext
    have := congrArg Subtype.val (hz i)
    show (c i).1 = (d i).1
    have e : (c i).1 + -(d i).1 = 0 := this
    grind
  have hsurj : ∀ v, ∃ c, Φ c = v := fun v => by
    obtain ⟨c, hc⟩ := hb.2 v; exact ⟨c, hc.symm⟩
  have h1 := count_comp_bij Φ hinj hsurj (fun _ => True)
  rw [count_true, count_true, card_tuple, card_primeSubfield hF hp hmin] at h1
  have h2 := count_comp_bij (fun v : V => v.1) (fun a b h => Subtype.ext h)
    (fun y => ⟨⟨y, trivial⟩, rfl⟩) (fun _ => True)
  rw [count_true, count_true] at h2
  exact ⟨p, dim P V, hpr, by rw [← h2, ← h1]⟩

end FiniteField

end Foundations.Algebra
