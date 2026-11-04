import Foundations.Langlands.Padic.Ostrowski

/-!
# The `p`-adic integers ℤₚ

Hensel's `p`-adic integers are "integers written in base `p` with infinitely many digits to the
left", such as `… 2 2 2 3` in base `7`. A cleaner description: a `p`-adic integer is a
*compatible system of residues* — a residue class mod `p`, one mod `p²`, one mod `p³`, … — each
reducing to the previous one. That is, ℤₚ is the inverse limit `lim ℤ/pⁿ`.

We realise this with a quotient, the same device that built ℤ, ℚ and ℝ. A **`p`-adic sequence**
is a sequence of integers `x₀, x₁, x₂, …` with `pⁿ ∣ xₙ₊₁ − xₙ` (so `xₙ` is meaningful mod `pⁿ`),
and two such sequences are identified when `pⁿ ∣ xₙ − yₙ` for every `n`. Addition and
multiplication are done term by term — no reductions needed — so every ring law of ℤ passes
straight to ℤₚ. In the language of `Valuation`, a `p`-adic sequence is a Cauchy sequence of
integers for `|·|ₚ` with a prescribed rate (`|xₙ₊₁ − xₙ|ₚ ≤ p^(−n)`), and identified sequences
are those whose difference tends to `0` at that rate: informally, ℤₚ is the completion of ℤ
(this identification is explained here, not formalised).

We prove that ℤₚ is a commutative ring (registered with `grind`), that ℤ embeds in it, define
congruence modulo `pᵏ` on ℤₚ, and prove the *completeness* of ℤₚ in its natural form: every
sequence of `p`-adic integers that is Cauchy modulo powers of `p` converges. The next file uses
this ring for Hensel's lemma.
-/

namespace Foundations.Langlands.Padic

open Foundations.Numbers Foundations.Numbers.Arith Lean.Grind

/-- A **`p`-adic sequence**: integers `xₙ` with `pⁿ ∣ xₙ₊₁ − xₙ`. -/
structure PSeq (p : Nat) where
  /-- The approximations `xₙ` (meaningful modulo `pⁿ`). -/
  seq : Nat → Int
  /-- Compatibility: `xₙ₊₁ ≡ xₙ (mod pⁿ)`. -/
  coh : ∀ n, (p : Int) ^ n ∣ seq (n + 1) - seq n

/-- Powers of a fixed integer divide higher powers. -/
theorem Int.pow_dvd_pow_of_le' {a : Int} {m n : Nat} (h : m ≤ n) : a ^ m ∣ a ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [Int.pow_add]; exact Int.dvd_mul_right _ _

namespace PSeq

variable {p : Nat}

/-- Compatibility over longer ranges: `pⁿ ∣ xₘ − xₙ` for `n ≤ m`. -/
theorem coh_le (x : PSeq p) {n m : Nat} (h : n ≤ m) : (p : Int) ^ n ∣ x.seq m - x.seq n := by
  induction m with
  | zero => have : n = 0 := by omega
            subst this; rw [Int.sub_self]; exact Int.dvd_zero _
  | succ m ih =>
    by_cases hnm : n = m + 1
    · subst hnm; rw [Int.sub_self]; exact Int.dvd_zero _
    · have h1 := ih (by omega)
      have h2 : (p : Int) ^ n ∣ (p : Int) ^ m :=
        Int.pow_dvd_pow_of_le' (by omega)
      have h3 := Int.dvd_trans h2 (x.coh m)
      rw [show x.seq (m + 1) - x.seq n = (x.seq (m + 1) - x.seq m) + (x.seq m - x.seq n) by omega]
      exact Int.dvd_add h3 h1

/-- The constant sequence at an integer. -/
def const (a : Int) : PSeq p := ⟨fun _ => a, fun _ => by rw [Int.sub_self]; exact Int.dvd_zero _⟩

/-- Termwise sum. -/
def add (x y : PSeq p) : PSeq p :=
  ⟨fun n => x.seq n + y.seq n, fun n => by
    rw [show x.seq (n + 1) + y.seq (n + 1) - (x.seq n + y.seq n) =
      (x.seq (n + 1) - x.seq n) + (y.seq (n + 1) - y.seq n) by omega]
    exact Int.dvd_add (x.coh n) (y.coh n)⟩

/-- Termwise negation. -/
def neg (x : PSeq p) : PSeq p :=
  ⟨fun n => -x.seq n, fun n => by
    rw [show -x.seq (n + 1) - -x.seq n = -(x.seq (n + 1) - x.seq n) by omega]
    exact Int.dvd_neg.2 (x.coh n)⟩

/-- `a ∣ u` and `a ∣ v` give `a ∣ x' y' − x y` when `u = x' − x`, `v = y' − y`. -/
theorem dvd_mul_sub {a x x' y y' : Int} (h1 : a ∣ x' - x) (h2 : a ∣ y' - y) :
    a ∣ x' * y' - x * y := by
  rw [show x' * y' - x * y = x' * (y' - y) + (x' - x) * y by grind]
  exact Int.dvd_add (Int.dvd_trans h2 (Int.dvd_mul_left _ _))
    (Int.dvd_trans h1 (Int.dvd_mul_right _ _))

/-- Termwise product. -/
def mul (x y : PSeq p) : PSeq p :=
  ⟨fun n => x.seq n * y.seq n, fun n => dvd_mul_sub (x.coh n) (y.coh n)⟩

/-- Two `p`-adic sequences are **equivalent** when `pⁿ ∣ xₙ − yₙ` for all `n`. -/
instance setoid (p : Nat) : Setoid (PSeq p) where
  r x y := ∀ n, (p : Int) ^ n ∣ x.seq n - y.seq n
  iseqv := {
    refl := fun x n => by rw [Int.sub_self]; exact Int.dvd_zero _
    symm := fun {x y} h n => by
      rw [show y.seq n - x.seq n = -(x.seq n - y.seq n) by omega]; exact Int.dvd_neg.2 (h n)
    trans := fun {x y z} h₁ h₂ n => by
      rw [show x.seq n - z.seq n = (x.seq n - y.seq n) + (y.seq n - z.seq n) by omega]
      exact Int.dvd_add (h₁ n) (h₂ n) }

end PSeq

/-- **The `p`-adic integers** `ℤₚ`: `p`-adic sequences up to equivalence, i.e. compatible
systems of residues modulo `p, p², p³, …`. -/
def Zp (p : Nat) : Type := Quotient (PSeq.setoid p)

namespace Zp

open PSeq

variable {p : Nat}

/-- The `p`-adic integer represented by a `p`-adic sequence. -/
def mk (x : PSeq p) : Zp p := Quotient.mk _ x

/-- Every `p`-adic integer has a representative. -/
@[elab_as_elim]
theorem ind {P : Zp p → Prop} (h : ∀ x, P (mk x)) (z : Zp p) : P z := Quotient.ind h z

/-- Sequences that agree termwise represent the same `p`-adic integer. -/
theorem mk_eq_of_seq {x y : PSeq p} (h : ∀ n, x.seq n = y.seq n) : mk x = mk y :=
  Quotient.sound fun n => by rw [h n, Int.sub_self]; exact Int.dvd_zero _

/-- Equality in `ℤₚ` unfolded. -/
theorem mk_eq_mk {x y : PSeq p} : mk x = mk y ↔ ∀ n, (p : Int) ^ n ∣ x.seq n - y.seq n :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

instance : Zero (Zp p) := ⟨mk (const 0)⟩
instance : One (Zp p) := ⟨mk (const 1)⟩
instance : NatCast (Zp p) := ⟨fun n => mk (const n)⟩
instance : IntCast (Zp p) := ⟨fun i => mk (const i)⟩
instance (n : Nat) : OfNat (Zp p) n := ⟨mk (const n)⟩

/-- Addition on `ℤₚ`. -/
instance : Add (Zp p) := ⟨Quotient.lift₂ (fun a b => mk (a.add b)) fun a₁ a₂ b₁ b₂ h₁ h₂ =>
  Quotient.sound fun n => by
    show _ ∣ (_ + _) - (_ + _)
    rw [show ∀ a b c d : Int, a + b - (c + d) = (a - c) + (b - d) from fun _ _ _ _ => by omega]
    exact Int.dvd_add (h₁ n) (h₂ n)⟩

/-- Negation on `ℤₚ`. -/
instance : Neg (Zp p) := ⟨Quotient.lift (fun a => mk a.neg) fun _ _ h =>
  Quotient.sound fun n => by
    show _ ∣ -_ - -_
    rw [show ∀ a b : Int, -a - -b = -(a - b) from fun _ _ => by omega]
    exact Int.dvd_neg.2 (h n)⟩

/-- Subtraction on `ℤₚ`. -/
instance : Sub (Zp p) := ⟨fun x y => x + -y⟩

/-- Multiplication on `ℤₚ`. -/
instance : Mul (Zp p) := ⟨Quotient.lift₂ (fun a b => mk (a.mul b)) fun _ _ _ _ h₁ h₂ =>
  Quotient.sound fun n => dvd_mul_sub (h₁ n) (h₂ n)⟩

/-- Natural powers on `ℤₚ`. -/
def npow (x : Zp p) : Nat → Zp p
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow (Zp p) Nat (Zp p) := ⟨npow⟩

/-- Computation rule for addition. -/
theorem mk_add (x y : PSeq p) : mk x + mk y = mk (x.add y) := rfl
/-- Computation rule for negation. -/
theorem mk_neg (x : PSeq p) : -mk x = mk x.neg := rfl
/-- Computation rule for multiplication. -/
theorem mk_mul (x y : PSeq p) : mk x * mk y = mk (x.mul y) := rfl

/-- **ℤₚ is a commutative ring.** Registered with Lean's automation as a `Lean.Grind.CommRing`;
every law is inherited termwise from ℤ. -/
instance instCommRing : Lean.Grind.CommRing (Zp p) where
  nsmul := ⟨fun n x => (n : Zp p) * x⟩
  zsmul := ⟨fun i x => (i : Zp p) * x⟩
  add_zero x := by induction x using ind; exact mk_eq_of_seq fun n => by simp [PSeq.add, const]
  add_comm x y := by
    induction x using ind; induction y using ind
    exact mk_eq_of_seq fun n => by simp only [PSeq.add]; omega
  add_assoc x y z := by
    induction x using ind; induction y using ind; induction z using ind
    exact mk_eq_of_seq fun n => by simp only [PSeq.add]; omega
  mul_assoc x y z := by
    induction x using ind; induction y using ind; induction z using ind
    exact mk_eq_of_seq fun n => by simp only [PSeq.mul]; grind
  mul_one x := by
    induction x using ind; exact mk_eq_of_seq fun n => by simp [PSeq.mul, const]
  one_mul x := by
    induction x using ind; exact mk_eq_of_seq fun n => by simp [PSeq.mul, const]
  left_distrib x y z := by
    induction x using ind; induction y using ind; induction z using ind
    exact mk_eq_of_seq fun n => by simp only [PSeq.mul, PSeq.add]; grind
  right_distrib x y z := by
    induction x using ind; induction y using ind; induction z using ind
    exact mk_eq_of_seq fun n => by simp only [PSeq.mul, PSeq.add]; grind
  zero_mul x := by
    induction x using ind; exact mk_eq_of_seq fun n => by simp [PSeq.mul, const]
  mul_zero x := by
    induction x using ind; exact mk_eq_of_seq fun n => by simp [PSeq.mul, const]
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := mk_eq_of_seq fun k => by simp [PSeq.add, const]
  neg_add_cancel x := by
    induction x using ind
    exact mk_eq_of_seq fun n => by simp only [PSeq.add, PSeq.neg, const]; omega
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i x := by
    induction x using ind
    exact mk_eq_of_seq fun n => by simp only [PSeq.mul, PSeq.neg, const]; grind
  intCast_neg i := mk_eq_of_seq fun n => by simp [PSeq.neg, const]
  mul_comm x y := by
    induction x using ind; induction y using ind
    exact mk_eq_of_seq fun n => by simp only [PSeq.mul]; grind

/-! ## The integers inside ℤₚ -/

/-- The image of an integer in `ℤₚ` is its constant sequence. -/
theorem intCast_def (a : Int) : (a : Zp p) = mk (const a) := rfl

/-- `pⁿ` grows without bound: `n < pⁿ` for `p ≥ 2`. -/
theorem lt_pow {p : Nat} (hp : 2 ≤ p) : ∀ n : Nat, n < p ^ n
  | 0 => by simp
  | n + 1 => by
    have := lt_pow hp n
    rw [Nat.pow_succ]
    have := Nat.mul_le_mul_left (p ^ n) hp
    omega

/-- An integer divisible by every power of `p ≥ 2` is zero. -/
theorem eq_zero_of_forall_dvd {p : Nat} (hp : 2 ≤ p) {a : Int}
    (h : ∀ n, (p : Int) ^ n ∣ a) : a = 0 := by
  have h1 := h a.natAbs
  have h2 := lt_pow hp a.natAbs
  rw [show (p : Int) ^ a.natAbs = ((p ^ a.natAbs : Nat) : Int) by simp] at h1
  apply Classical.byContradiction; intro ha
  have := Nat.le_of_dvd (by omega) (Int.natAbs_dvd_natAbs.2 h1)
  simp at this; omega

/-- **ℤ embeds in ℤₚ.** For `p ≥ 2`, distinct integers have distinct images in `ℤₚ`. -/
theorem intCast_injective {p : Nat} (hp : 2 ≤ p) {a b : Int} (h : (a : Zp p) = (b : Zp p)) :
    a = b := by
  have := mk_eq_mk.1 h
  have := eq_zero_of_forall_dvd hp (a := a - b) (fun n => this n)
  omega

/-! ## Congruences and completeness -/

/-- **Congruence modulo `pᵏ`** in `ℤₚ`: `x ≡ y (mod pᵏ)` iff the `k`-th approximations agree
modulo `pᵏ` (independent of representatives). -/
def ModPow (k : Nat) (x y : Zp p) : Prop :=
  Quotient.lift₂ (fun a b : PSeq p => (p : Int) ^ k ∣ a.seq k - b.seq k)
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => propext ⟨fun h => by
        rw [show a₂.seq k - b₂.seq k =
          -(a₁.seq k - a₂.seq k) + (a₁.seq k - b₁.seq k) + (b₁.seq k - b₂.seq k) by omega]
        exact Int.dvd_add (Int.dvd_add (Int.dvd_neg.2 (h₁ k)) h) (h₂ k),
      fun h => by
        rw [show a₁.seq k - b₁.seq k =
          (a₁.seq k - a₂.seq k) + (a₂.seq k - b₂.seq k) - (b₁.seq k - b₂.seq k) by omega]
        exact Int.dvd_sub (Int.dvd_add (h₁ k) h) (h₂ k)⟩) x y

/-- Congruence on representatives. -/
theorem modPow_mk {k : Nat} {a b : PSeq p} :
    ModPow k (mk a) (mk b) ↔ (p : Int) ^ k ∣ a.seq k - b.seq k := Iff.rfl

/-- Two `p`-adic integers are equal iff they are congruent modulo every `pᵏ`. -/
theorem eq_iff_modPow {x y : Zp p} : x = y ↔ ∀ k, ModPow k x y := by
  induction x using ind; induction y using ind
  exact mk_eq_mk

/-- A congruence modulo `pᵏ` implies the congruence modulo every `pʲ` with `j ≤ k`. -/
theorem ModPow.mono {j k : Nat} (hjk : j ≤ k) {x y : Zp p} (h : ModPow k x y) : ModPow j x y := by
  induction x using ind with | h a => ?_
  induction y using ind with | h b => ?_
  have h' := modPow_mk.1 h
  apply modPow_mk.2
  rw [show a.seq j - b.seq j = -(a.seq k - a.seq j) + (a.seq k - b.seq k) + (b.seq k - b.seq j)
    by omega]
  have hd : (p : Int) ^ j ∣ (p : Int) ^ k := Int.pow_dvd_pow_of_le' hjk
  exact Int.dvd_add (Int.dvd_add (Int.dvd_neg.2 (a.coh_le hjk)) (Int.dvd_trans hd h'))
    (b.coh_le hjk)

/-- A sequence `(zₘ)` in `ℤₚ` is **Cauchy** if for every `k` its terms are eventually all
congruent modulo `pᵏ`. -/
def IsCauchy (z : Nat → Zp p) : Prop :=
  ∀ k, ∃ N, ∀ m, N ≤ m → ModPow k (z m) (z N)

/-- A sequence `(zₘ)` in `ℤₚ` **converges** to `L` if for every `k`, eventually `zₘ ≡ L
(mod pᵏ)`. -/
def Converges (z : Nat → Zp p) (L : Zp p) : Prop :=
  ∀ k, ∃ N, ∀ m, N ≤ m → ModPow k (z m) L

/-- A representative of each `p`-adic integer (by choice). -/
noncomputable def rep (x : Zp p) : PSeq p := Classical.choose (Quotient.exists_rep x)

/-- The chosen representative represents `x`. -/
theorem mk_rep (x : Zp p) : mk (rep x) = x := Classical.choose_spec (Quotient.exists_rep x)

/-- **Completeness of ℤₚ.** Every Cauchy sequence of `p`-adic integers converges in `ℤₚ`. -/
theorem complete (z : Nat → Zp p) (hz : IsCauchy z) : ∃ L, Converges z L := by
  -- `N k`: a threshold for precision `k`, made increasing.
  have hN : ∀ k, ∃ N, ∀ m, N ≤ m → ModPow k (z m) (z N) := hz
  let N0 : Nat → Nat := fun k => Classical.choose (hN k)
  have hN0 : ∀ k m, N0 k ≤ m → ModPow k (z m) (z (N0 k)) := fun k => Classical.choose_spec (hN k)
  let N : Nat → Nat := fun k => Nat.rec (N0 0) (fun j acc => max acc (N0 (j + 1))) k
  have hNsucc : ∀ j, N (j + 1) = max (N j) (N0 (j + 1)) := fun _ => rfl
  have hNmono : ∀ j k, j ≤ k → N j ≤ N k := by
    intro j k hjk
    induction k with
    | zero => have : j = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ k ih =>
      by_cases h : j = k + 1
      · subst h; exact Nat.le_refl _
      · rw [hNsucc]; have := ih (by omega); omega
  have hN0le : ∀ k, N0 k ≤ N k := by
    intro k; cases k with
    | zero => exact Nat.le_refl _
    | succ k => rw [hNsucc]; omega
  -- `zₘ ≡ z_{N k} (mod pᵏ)` for every `m ≥ N k`.
  have hcong : ∀ k m, N k ≤ m → ModPow k (z m) (z (N k)) := by
    intro k m hm
    have h1 := hN0 k m (Nat.le_trans (hN0le k) hm)
    have h2 := hN0 k (N k) (hN0le k)
    rw [← mk_rep (z m), ← mk_rep (z (N k))]
    rw [← mk_rep (z m), ← mk_rep (z (N0 k))] at h1
    rw [← mk_rep (z (N k)), ← mk_rep (z (N0 k))] at h2
    apply modPow_mk.2
    have h1 := modPow_mk.1 h1
    have h2 := modPow_mk.1 h2
    rw [show (rep (z m)).seq k - (rep (z (N k))).seq k = ((rep (z m)).seq k -
      (rep (z (N0 k))).seq k) - ((rep (z (N k))).seq k - (rep (z (N0 k))).seq k) by omega]
    exact Int.dvd_sub h1 h2
  -- the limit: take the `k`-th digit of `z_{N k}`
  let L : PSeq p := ⟨fun k => (rep (z (N k))).seq k, fun k => by
    have h1 := hcong k (N (k + 1)) (hNmono k (k + 1) (Nat.le_succ k))
    rw [← mk_rep (z (N (k + 1))), ← mk_rep (z (N k))] at h1
    have h1 := modPow_mk.1 h1
    have h2 := (rep (z (N (k + 1)))).coh k
    show _ ∣ (rep (z (N (k + 1)))).seq (k + 1) - (rep (z (N k))).seq k
    rw [show (rep (z (N (k + 1)))).seq (k + 1) - (rep (z (N k))).seq k =
      ((rep (z (N (k + 1)))).seq (k + 1) - (rep (z (N (k + 1)))).seq k) +
      ((rep (z (N (k + 1)))).seq k - (rep (z (N k))).seq k) by omega]
    exact Int.dvd_add h2 h1⟩
  refine ⟨mk L, fun k => ⟨N k, fun m hm => ?_⟩⟩
  have h1 := hcong k m hm
  rw [← mk_rep (z m), ← mk_rep (z (N k))] at h1
  rw [← mk_rep (z m)]
  exact h1

end Zp

end Foundations.Langlands.Padic
