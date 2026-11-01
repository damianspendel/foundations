import Foundations.NumberTheory.DualGroup

/-!
# Orthogonality, and Dirichlet characters modulo `q`

With the dual group `Ĝ` of a finite commutative group `G` in hand (file `DualGroup`), we prove
the two **orthogonality relations** and `|Ĝ| = |G|`:

* `Σ_{x ∈ G} χ(x) = |G|` if `χ` is the trivial character, `0` otherwise;
* `Σ_{χ ∈ Ĝ} χ(a) · conj χ(b) = |G|` if `a = b`, `0` otherwise.

Then we specialise to `G = (ℤ/qℤ)ˣ`. A **Dirichlet character modulo `q`** is a character `χ` of
the units, extended to all natural numbers by `χ(n) = χ(n mod q)` when `gcd(n, q) = 1` and
`χ(n) = 0` otherwise. It is *completely multiplicative* (`χ(mn) = χ(m)χ(n)`), *periodic* with
period `q`, and bounded by `1`. For a non-trivial character the values over one period sum to
zero, and the second orthogonality relation becomes Dirichlet's **sieve for a residue class**:

  `Σ_χ conj χ(a) · χ(n) = φ(q)` if `n ≡ a (mod q)`, and `0` otherwise   (`gcd(a, q) = 1`).

This identity is what lets one count primes in the class `a` by counting primes weighted by
the characters — and the analytic behaviour of these weighted counts is governed by the
`L`-functions `L(s, χ) = Σ χ(n) n⁻ˢ`.
-/

namespace Foundations.NumberTheory

open Foundations.Algebra Foundations.Algebra.FiniteType Foundations.Algebra.Group
open Foundations.Numbers Lean.Grind

universe u

attribute [local instance] Classical.propDecidable

section Dual

variable {G : Type u} [CommGroup G] [FiniteType G]

namespace Character

omit [FiniteType G] in
/-- Two characters are equal when their values agree. -/
theorem ext {χ ψ : Character G} (h : ∀ a, χ.1 a = ψ.1 a) : χ = ψ := Subtype.ext (funext h)

/-- The **trivial character** `χ₀ = 1`. -/
def one : Character G := ⟨fun _ => 1, ⟨rfl, fun _ _ => by grind⟩⟩

/-- The product of two characters. -/
noncomputable def mul (χ ψ : Character G) : Character G := ⟨fun a => χ.1 a * ψ.1 a, χ.2.mul ψ.2⟩

/-- The **conjugate character** `χ̄(a) = conj χ(a) = χ(a)⁻¹`. -/
noncomputable def conj (χ : Character G) : Character G := ⟨fun a => C.conj (χ.1 a), χ.2.conj⟩

omit [FiniteType G] in
/-- A character other than `1` takes a value other than `1` somewhere. -/
theorem exists_ne_one {χ : Character G} (h : χ ≠ one) : ∃ y, χ.1 y ≠ 1 :=
  Classical.byContradiction fun hc => h (ext fun y =>
    Classical.byContradiction fun hy => hc ⟨y, hy⟩)

/-- **Characters separate points**: for `x ≠ 1` some character has `χ(x) ≠ 1`. -/
theorem exists_apply_ne_one {x : G} (hx : x ≠ 1) : ∃ χ : Character G, χ.1 x ≠ 1 := by
  obtain ⟨hne, hch, hs⟩ := orthoFamily_spec (G := G)
  apply Classical.byContradiction
  intro hall
  have h1 : ∀ ψ ∈ (orthoFamily : List (G → C)), ψ x = 1 := fun ψ hψ =>
    Classical.byContradiction fun h => hall ⟨⟨ψ, hch ψ hψ⟩, h⟩
  have := hs x
  rw [lsum_congr h1, lsum_const, ite_eq_right hx] at this
  have hlen : 0 < (orthoFamily : List (G → C)).length := by
    cases h : (orthoFamily : List (G → C)) with
    | nil => exact absurd h hne
    | cons a l => simp
  exact natCast_ne_zero_C hlen (by rw [← this]; grind)

end Character

/-- The sum over a finite type of a constant. -/
theorem sumOver_const {α : Type u} [FiniteType α] (c : C) :
    sumOver (fun _ : α => c) = (card α : C) * c := lsum_const _ c

/-- **First orthogonality relation.** `Σ_{x ∈ G} χ(x) = |G|` for `χ = 1`, and `0` otherwise. -/
theorem sum_character (χ : Character G) :
    sumOver χ.1 = if χ = Character.one then (card G : C) else 0 := by
  split
  · next h => subst h; rw [show (Character.one : Character G).1 = fun _ => 1 from rfl,
      sumOver_const]; grind
  · next h =>
    obtain ⟨y, hy⟩ := Character.exists_ne_one h
    exact χ.2.sum_eq_zero hy

/-- Summing the values at one point over all characters: `Σ_χ χ(x) = |Ĝ| · [x = 1]`. -/
theorem sum_over_characters (x : G) :
    sumOver (fun χ : Character G => χ.1 x) = if x = 1 then (card (Character G) : C) else 0 := by
  split
  · next h =>
    subst h
    rw [show (fun χ : Character G => χ.1 1) = fun _ => (1 : C) from funext fun χ => χ.2.map_one,
      sumOver_const]; grind
  · next h =>
    obtain ⟨ψ, hψ⟩ := Character.exists_apply_ne_one h
    apply eq_zero_of_mul_eq_self _ hψ
    have hinj : ∀ a b : Character G, Character.mul ψ a = Character.mul ψ b → a = b := by
      intro a b hab
      apply Character.ext; intro y
      have := congrArg (fun χ : Character G => χ.1 y) hab
      simp only [Character.mul] at this
      calc a.1 y = ψ.1 y⁻¹ * (ψ.1 y * a.1 y) := by
              rw [← Semiring.mul_assoc, C.mul_comm (ψ.1 y⁻¹), ψ.2.mul_inv]; grind
        _ = b.1 y := by rw [this, ← Semiring.mul_assoc, C.mul_comm (ψ.1 y⁻¹), ψ.2.mul_inv]; grind
    have e := sumOver_comp_injective (Character.mul ψ) hinj (fun χ : Character G => χ.1 x)
    calc ψ.1 x * sumOver (fun χ : Character G => χ.1 x)
        = sumOver (fun a => (Character.mul ψ a).1 x) := by
          unfold sumOver; rw [← lsum_mul_left]; rfl
      _ = _ := e

/-- **The dual group has as many elements as the group**: `|Ĝ| = |G|`. Count the pairs
`(x, χ)` weighted by `χ(x)` in both orders, using both orthogonality relations. -/
theorem card_character : card (Character G) = card G := by
  have h1 : sumOver (fun x : G => sumOver (fun χ : Character G => χ.1 x)) =
      (card (Character G) : C) := by
    rw [show (fun x : G => sumOver (fun χ : Character G => χ.1 x)) =
      fun x => if x = 1 then (card (Character G) : C) else 0 from funext sum_over_characters]
    rw [sumOver_single 1 _ (fun x hx => ite_eq_right hx), ite_eq_left rfl]
  have h2 : sumOver (fun x : G => sumOver (fun χ : Character G => χ.1 x)) = (card G : C) := by
    unfold sumOver; rw [lsum_comm]
    have := sumOver_single (Character.one : Character G) (fun χ => sumOver χ.1) (fun χ hχ => by
      show sumOver χ.1 = 0; rw [sum_character, ite_eq_right hχ])
    unfold sumOver at this; rw [this]
    have := sum_character (Character.one : Character G)
    unfold sumOver at this; rw [this, ite_eq_left rfl]
  have h3 : ((card (Character G) : C)).re = ((card G : C)).re := by rw [← h1, ← h2]
  have h4 : ((card (Character G) : Nat) : R) = ((card G : Nat) : R) := h3
  have a1 := OrderedRing.le_of_natCast_le_natCast (R := R) (card (Character G)) (card G)
    (by rw [h4]; grind)
  have a2 := OrderedRing.le_of_natCast_le_natCast (R := R) (card G) (card (Character G))
    (by rw [h4]; grind)
  omega

/-- **Second orthogonality relation.** `Σ_χ χ(a) · conj χ(b) = |G| · [a = b]`. -/
theorem sum_characters_mul_conj (a b : G) :
    sumOver (fun χ : Character G => χ.1 a * C.conj (χ.1 b)) =
      if a = b then (card G : C) else 0 := by
  have e : ∀ χ : Character G, χ.1 a * C.conj (χ.1 b) = χ.1 (a * b⁻¹) := fun χ => by
    rw [χ.2.conj_eq, χ.2.map_mul]
  rw [show (fun χ : Character G => χ.1 a * C.conj (χ.1 b)) = fun χ => χ.1 (a * b⁻¹) from funext e,
    sum_over_characters, card_character]
  by_cases h : a = b
  · rw [ite_eq_left (mul_inv_eq_one.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (mul_inv_eq_one.1 h')), ite_eq_right h]

end Dual

/-! ## Dirichlet characters modulo `q` -/

section Dirichlet

variable {q : Nat} [NeZero q]

/-- The unit of `ℤ/qℤ` represented by a natural number `n` coprime to `q`. -/
def toUnit (q : Nat) [NeZero q] (n : Nat) (h : Nat.Coprime n q) : ZModUnits q :=
  ⟨Fin.ofNat q n, by rw [Fin.val_ofNat, coprime_mod_iff]; exact h⟩

/-- The **Dirichlet character** modulo `q` attached to a character `χ` of `(ℤ/qℤ)ˣ`:
`χ(n) = χ(n mod q)` if `gcd(n, q) = 1`, and `0` otherwise. -/
noncomputable def dchar (χ : Character (ZModUnits q)) (n : Nat) : C :=
  if h : Nat.Coprime n q then χ.1 (toUnit q n h) else 0

/-- The value of a Dirichlet character at an integer coprime to `q`. -/
theorem dchar_of_coprime (χ : Character (ZModUnits q)) {n : Nat} (h : Nat.Coprime n q) :
    dchar χ n = χ.1 (toUnit q n h) := dite_eq_left h

/-- A Dirichlet character vanishes at integers sharing a factor with `q`. -/
theorem dchar_of_not_coprime (χ : Character (ZModUnits q)) {n : Nat} (h : ¬ Nat.Coprime n q) :
    dchar χ n = 0 := by unfold dchar; rw [dite_eq_right h]

/-- `χ(1) = 1`. -/
theorem dchar_one (χ : Character (ZModUnits q)) : dchar χ 1 = 1 := by
  rw [dchar_of_coprime χ (Nat.coprime_one_left q)]
  have : toUnit q 1 (Nat.coprime_one_left q) = 1 := ZModUnits.ext (by
    show (Fin.ofNat q 1).val = (1 : ZModUnits q).1.val
    rw [ZModUnits.val_one, Fin.val_ofNat])
  rw [this, χ.2.map_one]

/-- **Dirichlet characters are completely multiplicative.** `χ(mn) = χ(m)χ(n)`. -/
theorem dchar_mul (χ : Character (ZModUnits q)) (m n : Nat) :
    dchar χ (m * n) = dchar χ m * dchar χ n := by
  by_cases hm : Nat.Coprime m q
  · by_cases hn : Nat.Coprime n q
    · have hmn : Nat.Coprime (m * n) q := Nat.coprime_mul_iff_left.2 ⟨hm, hn⟩
      rw [dchar_of_coprime χ hm, dchar_of_coprime χ hn, dchar_of_coprime χ hmn, ← χ.2.map_mul]
      have hu : toUnit q (m * n) hmn = toUnit q m hm * toUnit q n hn := by
        apply ZModUnits.ext
        show (Fin.ofNat q (m * n)).val = (toUnit q m hm * toUnit q n hn).1.val
        rw [ZModUnits.val_mul]
        show (Fin.ofNat q (m * n)).val = (Fin.ofNat q m).val * (Fin.ofNat q n).val % q
        rw [Fin.val_ofNat, Fin.val_ofNat, Fin.val_ofNat, Nat.mul_mod]
      rw [hu]
    · rw [dchar_of_not_coprime χ hn, dchar_of_not_coprime χ
        (fun h => hn (Nat.coprime_mul_iff_left.1 h).2)]; grind
  · rw [dchar_of_not_coprime χ hm, dchar_of_not_coprime χ
      (fun h => hm (Nat.coprime_mul_iff_left.1 h).1)]; grind

/-- **Dirichlet characters are periodic** with period `q`. -/
theorem dchar_add_period (χ : Character (ZModUnits q)) (n : Nat) : dchar χ (n + q) = dchar χ n := by
  have hmod : (n + q) % q = n % q := Nat.add_mod_right n q
  have hiff : Nat.Coprime (n + q) q ↔ Nat.Coprime n q := by
    rw [← coprime_mod_iff, hmod, coprime_mod_iff]
  by_cases h : Nat.Coprime n q
  · rw [dchar_of_coprime χ h, dchar_of_coprime χ (hiff.2 h)]
    have hu : toUnit q (n + q) (hiff.2 h) = toUnit q n h := by
      apply ZModUnits.ext
      show (Fin.ofNat q (n + q)).val = (Fin.ofNat q n).val
      rw [Fin.val_ofNat, Fin.val_ofNat, hmod]
    rw [hu]
  · rw [dchar_of_not_coprime χ h, dchar_of_not_coprime χ (fun h' => h (hiff.1 h'))]

/-- Dirichlet characters are bounded by `1`: `|χ(n)| ≤ 1`. -/
theorem cabs_dchar_le (χ : Character (ZModUnits q)) (n : Nat) : C.cabs (dchar χ n) ≤ 1 := by
  by_cases h : Nat.Coprime n q
  · rw [dchar_of_coprime χ h, χ.2.cabs_eq_one]; grind
  · rw [dchar_of_not_coprime χ h, C.cabs_zero]; grind

/-- The Dirichlet character of `χ̄` is the complex conjugate of that of `χ`. -/
theorem dchar_conj (χ : Character (ZModUnits q)) (n : Nat) :
    dchar (Character.conj χ) n = C.conj (dchar χ n) := by
  by_cases h : Nat.Coprime n q
  · rw [dchar_of_coprime _ h, dchar_of_coprime _ h]; rfl
  · rw [dchar_of_not_coprime _ h, dchar_of_not_coprime _ h]; apply C.ext <;> simp; grind

/-- The **principal character** `χ₀`: `χ₀(n) = 1` if `gcd(n, q) = 1`, else `0`. -/
theorem dchar_one_char (n : Nat) :
    dchar (Character.one : Character (ZModUnits q)) n = if Nat.Coprime n q then 1 else 0 := by
  by_cases h : Nat.Coprime n q
  · rw [dchar_of_coprime _ h, ite_eq_left h]; rfl
  · rw [dchar_of_not_coprime _ h, ite_eq_right h]

/-! ## Sums over a period, and the sieve for a residue class -/

/-- Finite sums `gsum` (Part II) as list sums over `0, …, n − 1`. -/
theorem gsum_eq_lsum_finRange (f : Nat → C) : ∀ n, gsum f n = lsum (List.finRange n) (fun a => f a.val)
  | 0 => rfl
  | n + 1 => by
    rw [gsum_succ, List.finRange_succ_last, lsum_append, lsum_map, gsum_eq_lsum_finRange f n]
    simp only [lsum_cons, lsum_nil, Fin.val_castSucc, Fin.val_last]
    grind

/-- A sum over `listSubtype`. -/
theorem lsum_listSubtype {γ : Type u} (P : γ → Prop) [DecidablePred P] (l : List γ)
    (F : {x // P x} → C) :
    lsum (listSubtype P l) F = lsum l (fun a => if h : P a then F ⟨a, h⟩ else 0) := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    unfold listSubtype
    by_cases h : P y
    · simp only [h, ↓reduceDIte, lsum_cons, ih]
    · simp only [h, ↓reduceDIte, lsum_cons, ih]; grind

/-- Summing a Dirichlet character over one period is summing the group character over
`(ℤ/qℤ)ˣ`. -/
theorem gsum_dchar_eq_sumOver (χ : Character (ZModUnits q)) : gsum (dchar χ) q = sumOver χ.1 := by
  have e := @lsum_listSubtype (Fin q) (fun a : Fin q => Nat.Coprime a.val q)
    (fun _ => Classical.propDecidable _) (List.finRange q) χ.1
  unfold sumOver; rw [gsum_eq_lsum_finRange]; refine Eq.trans ?_ e.symm
  apply lsum_congr
  intro a _
  by_cases h : Nat.Coprime a.val q
  · rw [dchar_of_coprime χ h, dite_eq_left h]
    have hu : toUnit q a.val h = (⟨a, h⟩ : ZModUnits q) := by
      apply ZModUnits.ext
      show (Fin.ofNat q a.val).val = a.val
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt a.isLt]
    rw [hu]
  · rw [dchar_of_not_coprime χ h, dite_eq_right h]

/-- **A non-principal character sums to zero over a period**: `Σ_{n<q} χ(n) = 0` for `χ ≠ χ₀`. -/
theorem gsum_dchar_period (χ : Character (ZModUnits q)) (h : χ ≠ Character.one) :
    gsum (dchar χ) q = 0 := by
  rw [gsum_dchar_eq_sumOver, sum_character, ite_eq_right h]

/-- **Dirichlet's sieve for a residue class.** For `a` coprime to `q`,
`Σ_χ conj χ(a) · χ(n) = φ(q)` if `n ≡ a (mod q)`, and `0` otherwise. -/
theorem sum_conj_dchar_mul (a : Nat) (ha : Nat.Coprime a q) (n : Nat) :
    sumOver (fun χ : Character (ZModUnits q) => C.conj (dchar χ a) * dchar χ n) =
      if n % q = a % q then (totient q : C) else 0 := by
  by_cases hn : Nat.Coprime n q
  · have e : ∀ χ : Character (ZModUnits q), C.conj (dchar χ a) * dchar χ n =
        χ.1 (toUnit q n hn) * C.conj (χ.1 (toUnit q a ha)) := fun χ => by
      rw [dchar_of_coprime χ ha, dchar_of_coprime χ hn, C.mul_comm]
    rw [show (fun χ : Character (ZModUnits q) => C.conj (dchar χ a) * dchar χ n) =
      fun χ => χ.1 (toUnit q n hn) * C.conj (χ.1 (toUnit q a ha)) from funext e,
      sum_characters_mul_conj, card_zmodUnits]
    have hiff : toUnit q n hn = toUnit q a ha ↔ n % q = a % q := by
      constructor
      · intro h; have := congrArg (fun u : ZModUnits q => u.1.val) h
        simpa [toUnit, Fin.val_ofNat] using this
      · intro h; apply ZModUnits.ext; show (Fin.ofNat q n).val = (Fin.ofNat q a).val
        rw [Fin.val_ofNat, Fin.val_ofNat, h]
    by_cases h : n % q = a % q
    · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]
  · have hne : ¬ n % q = a % q := by
      intro h; apply hn; rw [← coprime_mod_iff, h, coprime_mod_iff]; exact ha
    rw [ite_eq_right hne]
    unfold sumOver
    rw [lsum_congr (g := fun _ => (0 : C)) (fun χ _ => by rw [dchar_of_not_coprime χ hn]; grind),
      lsum_zero]

/-- Interchanging a list sum with a finite sum `gsum`. -/
theorem lsum_gsum {α : Type u} (l : List α) (F : α → Nat → C) (N : Nat) :
    lsum l (fun a => gsum (F a) N) = gsum (fun n => lsum l (fun a => F a n)) N := by
  induction N with
  | zero => exact lsum_zero l
  | succ N ih =>
    rw [gsum_succ, ← ih, ← lsum_add]; rfl

end Dirichlet

end Foundations.NumberTheory
