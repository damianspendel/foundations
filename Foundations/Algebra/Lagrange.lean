import Foundations.Algebra.Finite

/-!
# Lagrange's theorem and its arithmetic harvest

In 1770 Joseph-Louis Lagrange, studying how the value of an expression in the roots of a
polynomial changes when the roots are permuted, noticed that the number of distinct values
always divides the number of permutations. Stripped of its original setting, the
observation becomes the first great theorem of finite group theory: **the size of a
subgroup divides the size of the group.**

The proof is a counting argument of great simplicity. A subgroup `H` cuts the group into
*cosets* `gH = {g * h | h ∈ H}`; distinct cosets do not overlap, every element lies in
one, and each coset is a bijective copy of `H`. So the group is tiled by blocks of equal
size `|H|`. We formalise the tiling by peeling off one coset at a time.

From Lagrange's theorem pour consequences. The *order* of an element `g` — the least
`n > 0` with `g ^ n = 1` — is the size of the cyclic subgroup it generates, hence divides
`|G|`; so `g ^ |G| = 1` in every finite group. A group of prime size has no room for
proper non-trivial subgroups and must be cyclic. Applied to the multiplicative group of
residues coprime to `n`, the statement `g ^ |G| = 1` becomes **Euler's theorem**
(1763) `a ^ φ(n) ≡ 1 (mod n)`, and for a prime modulus **Fermat's little theorem** (1640)
`a ^ (p-1) ≡ 1 (mod p)`. Fermat stated his theorem without proof and Euler's proof was
by direct computation; seen through Lagrange, both become a single line of structure.
-/

namespace Foundations.Algebra

open Group FiniteType

universe u

section Cosets

variable {G : Type u} [Group G]

/-- The **left coset** `gH = {g * h | h ∈ H}`, described by its membership condition:
`x ∈ gH` iff `g⁻¹ * x ∈ H`. -/
def leftCoset (g : G) (H : Subgroup G) : G → Prop := fun x => g⁻¹ * x ∈ H

/-- `x ∈ gH` iff `x = g * h` for some `h ∈ H`. -/
theorem leftCoset_iff (g : G) (H : Subgroup G) (x : G) :
    leftCoset g H x ↔ ∃ h, h ∈ H ∧ g * h = x := by
  constructor
  · intro hx; exact ⟨g⁻¹ * x, hx, mul_inv_cancel_left g x⟩
  · intro ⟨h, hh, hx⟩
    show g⁻¹ * x ∈ H
    rw [← hx, inv_mul_cancel_left]; exact hh

/-- Every element lies in its own coset: `g ∈ gH`. -/
theorem mem_leftCoset_self (g : G) (H : Subgroup G) : leftCoset g H g := by
  show g⁻¹ * g ∈ H
  rw [inv_mul_cancel]; exact H.one_mem

/-- **Cosets partition the group.** Two left cosets either coincide or are disjoint. -/
theorem leftCoset_eq_or_disjoint (H : Subgroup G) (a b : G) :
    (∀ x, leftCoset a H x ↔ leftCoset b H x) ∨
    (∀ x, ¬ (leftCoset a H x ∧ leftCoset b H x)) := by
  by_cases hab : a⁻¹ * b ∈ H
  · left
    intro x
    constructor
    · intro hx
      show b⁻¹ * x ∈ H
      have : b⁻¹ * x = (a⁻¹ * b)⁻¹ * (a⁻¹ * x) := by
        rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      rw [this]; exact H.mul_mem (H.inv_mem hab) hx
    · intro hx
      show a⁻¹ * x ∈ H
      have : a⁻¹ * x = (a⁻¹ * b) * (b⁻¹ * x) := by
        rw [mul_assoc, mul_inv_cancel_left]
      rw [this]; exact H.mul_mem hab hx
  · right
    intro x ⟨ha, hb⟩
    apply hab
    have : a⁻¹ * b = (a⁻¹ * x) * (b⁻¹ * x)⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [this]; exact H.mul_mem ha (H.inv_mem hb)

variable [FiniteType G]

/-- **All cosets have the same size.** Left multiplication by `g` is a bijection from `H`
onto `gH`, so `|gH| = |H|`. -/
theorem count_leftCoset (g : G) (H : Subgroup G) :
    count (leftCoset g H) = count (· ∈ H) :=
  count_comp_bij (fun x => g⁻¹ * x)
    (fun _ _ h => mul_left_cancel h)
    (fun y => ⟨g * y, inv_mul_cancel_left g y⟩)
    (· ∈ H)

/-- **The tiling argument.** If a set `P` is a union of left cosets of `H` (i.e. closed under
right multiplication by elements of `H`), then `|H|` divides `|P|`. We peel off one coset
at a time: removing a coset from such a set leaves such a set, with `|H|` fewer elements. -/
theorem dvd_count_of_saturated (H : Subgroup G) :
    ∀ (n : Nat) (P : G → Prop), count P = n →
      (∀ a h, P a → h ∈ H → P (a * h)) → count (· ∈ H) ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro P hn hsat
    by_cases h0 : n = 0
    · rw [h0]; exact Nat.dvd_zero _
    · have hpos : 0 < count P := by omega
      obtain ⟨g, hg⟩ := count_pos.1 hpos
      -- The coset `gH` lies inside `P`.
      have hsub : ∀ x, leftCoset g H x → P x := by
        intro x hx
        have := hsat g _ hg hx
        rwa [mul_inv_cancel_left] at this
      -- Split `P` into the coset `gH` and the rest.
      have hsplit := count_split P (leftCoset g H)
      have hC : count (fun x => P x ∧ leftCoset g H x) = count (· ∈ H) := by
        rw [← count_leftCoset g H]
        exact count_congr fun x => ⟨fun h => h.2, fun h => ⟨hsub x h, h⟩⟩
      have hHpos : 0 < count (· ∈ H) := count_pos.2 ⟨1, H.one_mem⟩
      -- The rest is again a union of cosets.
      have hsat' : ∀ a h, (P a ∧ ¬ leftCoset g H a) → h ∈ H →
          (P (a * h) ∧ ¬ leftCoset g H (a * h)) := by
        intro a h ⟨hPa, hna⟩ hh
        refine ⟨hsat a h hPa hh, fun hc => hna ?_⟩
        show g⁻¹ * a ∈ H
        have : g⁻¹ * a = (g⁻¹ * (a * h)) * h⁻¹ := by
          rw [← mul_assoc, mul_inv_cancel_right]
        rw [this]; exact H.mul_mem hc (H.inv_mem hh)
      have hrest := ih (count fun x => P x ∧ ¬ leftCoset g H x) (by omega) _ rfl hsat'
      rw [← hn, hsplit, hC]
      exact Nat.dvd_add (Nat.dvd_refl _) hrest

/-- **Lagrange's theorem (counting form).** The number of elements of a subgroup `H`
divides the number of elements of the finite group `G`. -/
theorem lagrange_count (H : Subgroup G) : count (· ∈ H) ∣ card G := by
  apply dvd_count_of_saturated H (card G) (fun _ => True) count_true
  intro _ _ _ _; trivial

/-- **Lagrange's theorem.** In a finite group `G`, the order (number of elements) of any
subgroup `H` divides the order of `G`. -/
theorem lagrange (H : Subgroup G) : card H ∣ card G := by
  rw [show card H = count (· ∈ H) from card_subtype _]
  exact lagrange_count H

/-- The **index** `[G : H]` of a subgroup: the number of cosets, `|G| / |H|`. -/
noncomputable def Subgroup.index (H : Subgroup G) : Nat := card G / card H

/-- **Lagrange's theorem, multiplicative form.** `|G| = |H| · [G : H]`. -/
theorem card_eq_card_mul_index (H : Subgroup G) : card G = card H * H.index :=
  (Nat.mul_div_cancel' (lagrange H)).symm

end Cosets

/-! ## The order of an element -/

section Order

variable {G : Type u} [Group G]

/-- If `g ^ i = g ^ j` with `i < j`, then `g ^ (j - i) = 1`. -/
theorem pow_sub_eq_one {g : G} {i j : Nat} (hij : i < j) (h : g ^ i = g ^ j) :
    g ^ (j - i) = 1 := by
  have : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add]; congr 1; omega
  rw [this] at h
  exact (mul_left_cancel (a := g ^ i) (by rw [mul_one]; exact h)).symm

variable [FiniteType G]

/-- **Some power of every element is the identity** in a finite group. The powers
`g⁰, g¹, …, g^|G|` are `|G| + 1` elements of a set of size `|G|`, so by the pigeonhole
principle two coincide, and then `g ^ (j - i) = 1`. -/
theorem exists_pow_eq_one (g : G) : ∃ n, 0 < n ∧ g ^ n = 1 := by
  apply Classical.byContradiction
  intro hno
  have hinj : ∀ i j : Nat, g ^ i = g ^ j → i = j := by
    intro i j h
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exact absurd ⟨j - i, by omega, pow_sub_eq_one hlt h⟩ hno
    · exact heq
    · exact absurd ⟨i - j, by omega, pow_sub_eq_one hgt h.symm⟩ hno
  have hnd := nodup_map_of_injective hinj (List.nodup_range (n := card G + 1))
  have := length_le_card hnd
  rw [List.length_map, List.length_range] at this
  omega

/-- Existence of a least positive exponent killing `g`. -/
theorem exists_orderOf (g : G) :
    ∃ n, (0 < n ∧ g ^ n = 1) ∧ ∀ m, m < n → ¬ (0 < m ∧ g ^ m = 1) :=
  exists_least _ (exists_pow_eq_one g)

/-- The **order** of an element `g` of a finite group: the least `n > 0` with `g ^ n = 1`. -/
noncomputable def orderOf (g : G) : Nat := Classical.choose (exists_orderOf g)

/-- The order of an element is positive. -/
theorem orderOf_pos (g : G) : 0 < orderOf g := (Classical.choose_spec (exists_orderOf g)).1.1

/-- `g ^ orderOf g = 1`. -/
theorem pow_orderOf (g : G) : g ^ orderOf g = 1 := (Classical.choose_spec (exists_orderOf g)).1.2

/-- No smaller positive power of `g` is the identity. -/
theorem pow_ne_one_of_lt_orderOf (g : G) {m : Nat} (hm0 : 0 < m) (hm : m < orderOf g) :
    g ^ m ≠ 1 :=
  fun h => (Classical.choose_spec (exists_orderOf g)).2 m hm ⟨hm0, h⟩

/-- Exponents only matter modulo the order: `g ^ k = g ^ (k % orderOf g)`. -/
theorem pow_mod_orderOf (g : G) (k : Nat) : g ^ k = g ^ (k % orderOf g) := by
  conv => lhs; rw [← Nat.mod_add_div k (orderOf g)]
  rw [pow_add, pow_mul, pow_orderOf, one_pow, mul_one]

/-- `g ^ k = 1` exactly when the order of `g` divides `k`. -/
theorem pow_eq_one_iff_dvd (g : G) (k : Nat) : g ^ k = 1 ↔ orderOf g ∣ k := by
  constructor
  · intro h
    rw [pow_mod_orderOf] at h
    apply Nat.dvd_of_mod_eq_zero
    apply Classical.byContradiction
    intro hne
    exact pow_ne_one_of_lt_orderOf g (Nat.pos_of_ne_zero hne)
      (Nat.mod_lt _ (orderOf_pos g)) h
  · intro ⟨c, hc⟩
    rw [hc, pow_mul, pow_orderOf, one_pow]

/-- The **cyclic subgroup** `⟨g⟩` generated by `g`: all powers of `g`. (In a finite group the
inverse of a power is again a power, so no negative exponents are needed.) -/
noncomputable def powers (g : G) : Subgroup G where
  carrier x := ∃ k : Nat, g ^ k = x
  one_mem := ⟨0, rfl⟩
  mul_mem := by
    intro a b ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨i + j, by rw [pow_add, hi, hj]⟩
  inv_mem := by
    intro a ⟨k, hk⟩
    refine ⟨(orderOf g - 1) * k, ?_⟩
    rw [← hk]
    symm
    apply inv_eq_of_mul_eq_one
    have hpos := orderOf_pos g
    have : k + (orderOf g - 1) * k = orderOf g * k := by
      rw [Nat.add_comm, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
    rw [← pow_add, this, pow_mul, pow_orderOf, one_pow]

/-- Membership in `⟨g⟩`. -/
theorem mem_powers (g x : G) : x ∈ powers g ↔ ∃ k : Nat, g ^ k = x := Iff.rfl

/-- **The order of `g` is the size of `⟨g⟩`.** The powers `g⁰, …, g^(n-1)` (with `n` the
order) are distinct and exhaust `⟨g⟩`. -/
theorem count_powers (g : G) : count (· ∈ powers g) = orderOf g := by
  have hL : ((List.range (orderOf g)).map (fun k => g ^ k)).Nodup := by
    have hpw : (List.range (orderOf g)).Pairwise (fun i j => g ^ i ≠ g ^ j) := by
      refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := orderOf g))
      intro i j hi hj hij heq
      rw [List.mem_range] at hi hj
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · exact pow_ne_one_of_lt_orderOf g (by omega) (by omega) (pow_sub_eq_one hlt heq)
      · exact pow_ne_one_of_lt_orderOf g (by omega) (by omega) (pow_sub_eq_one hgt heq.symm)
    exact List.Pairwise.map _ (fun _ _ h => h) hpw
  rw [count_eq_length hL, List.length_map, List.length_range]
  intro x
  rw [mem_powers, List.mem_map]
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k % orderOf g, List.mem_range.2 (Nat.mod_lt _ (orderOf_pos g)),
      by rw [← pow_mod_orderOf, hk]⟩
  · intro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

/-- **The order of an element divides the order of the group.** -/
theorem orderOf_dvd_card (g : G) : orderOf g ∣ card G := by
  rw [← count_powers]; exact lagrange_count (powers g)

/-- **`g ^ |G| = 1`** for every element `g` of a finite group `G`. -/
theorem pow_card_eq_one (g : G) : g ^ card G = 1 :=
  (pow_eq_one_iff_dvd g _).2 (orderOf_dvd_card g)

end Order

/-! ## Groups of prime order -/

/-- A natural number is **prime** if it is at least `2` and its only divisors are `1` and
itself. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- A group is **cyclic** if some element `g` generates it: every element is a power of
`g`. -/
def IsCyclic (G : Type u) [Group G] : Prop := ∃ g : G, ∀ x : G, ∃ k : Nat, g ^ k = x

section PrimeOrder

variable {G : Type u} [Group G] [FiniteType G]

/-- If `⟨g⟩` has as many elements as `G`, then `g` generates `G`. -/
theorem generates_of_orderOf_eq_card {g : G} (h : orderOf g = card G) :
    ∀ x : G, ∃ k : Nat, g ^ k = x := by
  rw [← count_powers] at h
  exact count_eq_card.1 h

/-- **Groups of prime order are cyclic.** If `|G|` is prime, then `G` is generated by any
element other than the identity; in particular `G` is cyclic. -/
theorem isCyclic_of_prime_card (hp : IsPrime (card G)) : IsCyclic G := by
  -- There is an element other than the identity.
  have h1 := count_add_count_not (fun x : G => x = 1)
  rw [count_eq_self] at h1
  have hpos : 0 < count (fun x : G => ¬ x = 1) := by have := hp.1; omega
  obtain ⟨g, hg⟩ := count_pos.1 hpos
  refine ⟨g, generates_of_orderOf_eq_card ?_⟩
  rcases hp.2 _ (orderOf_dvd_card g) with h | h
  · exfalso; apply hg
    have := pow_orderOf g
    rwa [h, pow_one] at this
  · exact h

end PrimeOrder

/-! ## The units of `ℤ/nℤ`: Euler and Fermat -/

/-- `x mod n` is coprime to `n` exactly when `x` is. -/
theorem coprime_mod_iff (x n : Nat) : Nat.Coprime (x % n) n ↔ Nat.Coprime x n := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec n x, Nat.gcd_comm]

/-- Cancellation modulo `n` by a factor coprime to `n`: if `a * b ≡ a * c (mod n)` with
`b, c < n`, then `b = c`. -/
theorem cancel_mod {n a b c : Nat} (ha : Nat.Coprime a n) (hb : b < n) (hc : c < n)
    (h : a * b % n = a * c % n) : b = c := by
  have h1 : n ∣ a * (c - b) := by
    rw [Nat.mul_sub]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  have h2 : n ∣ a * (b - c) := by
    rw [Nat.mul_sub]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
  have e1 := Nat.eq_zero_of_dvd_of_lt (ha.symm.dvd_of_dvd_mul_left h1) (by omega)
  have e2 := Nat.eq_zero_of_dvd_of_lt (ha.symm.dvd_of_dvd_mul_left h2) (by omega)
  omega

/-- The **units of `ℤ/nℤ`**: residues modulo `n` that are coprime to `n`. Under
multiplication modulo `n` they form a group, written `(ℤ/nℤ)ˣ`. -/
def ZModUnits (n : Nat) : Type := {a : Fin n // Nat.Coprime a.val n}

namespace ZModUnits

variable {n : Nat} [NeZero n]

/-- The finitely many units of `ℤ/nℤ`. -/
noncomputable instance : FiniteType (ZModUnits n) :=
  FiniteType.instSubtype (fun a : Fin n => Nat.Coprime a.val n)

/-- Multiplication of units modulo `n`: a product of residues coprime to `n` is coprime
to `n`. -/
instance : Mul (ZModUnits n) :=
  ⟨fun a b => ⟨a.1 * b.1, by
    rw [Fin.val_mul, coprime_mod_iff]
    exact Nat.coprime_mul_iff_left.2 ⟨a.2, b.2⟩⟩⟩

/-- The unit `1`. -/
instance : One (ZModUnits n) :=
  ⟨⟨Fin.ofNat n 1, by rw [Fin.val_ofNat, coprime_mod_iff]; exact Nat.coprime_one_left n⟩⟩

omit [NeZero n] in
/-- The residue of a product of units. -/
theorem val_mul (a b : ZModUnits n) : (a * b).1.val = a.1.val * b.1.val % n := Fin.val_mul _ _

/-- The residue of the unit `1`. -/
theorem val_one : (1 : ZModUnits n).1.val = 1 % n := Fin.val_ofNat _ _

omit [NeZero n] in
/-- Two units with the same residue are equal. -/
theorem ext {a b : ZModUnits n} (h : a.1.val = b.1.val) : a = b := Subtype.ext (Fin.ext h)

/-- Multiplication of units is associative. -/
theorem mul_assoc' (a b c : ZModUnits n) : a * b * c = a * (b * c) := by
  apply Subtype.ext
  show a.1 * b.1 * c.1 = a.1 * (b.1 * c.1)
  grind

/-- Multiplication of units is commutative. -/
theorem mul_comm' (a b : ZModUnits n) : a * b = b * a := by
  apply Subtype.ext
  show a.1 * b.1 = b.1 * a.1
  grind

/-- `1` is a left identity. -/
theorem one_mul' (a : ZModUnits n) : 1 * a = a := by
  apply ext
  rw [val_mul, val_one, Nat.mod_mul_mod, Nat.one_mul, Nat.mod_eq_of_lt a.1.isLt]

omit [NeZero n] in
/-- **Multiplication by a unit is injective** — cancellation modulo `n`. -/
theorem mul_left_injective (a : ZModUnits n) : ∀ b c : ZModUnits n, a * b = a * c → b = c := by
  intro b c h
  apply ext
  have h' := congrArg (fun u : ZModUnits n => u.1.val) h
  simp only [val_mul] at h'
  exact cancel_mod a.2 b.1.isLt c.1.isLt h'

/-- **Every unit has an inverse.** Multiplication by `a` is an injective map of the finite set
of units to itself, hence surjective, so it hits `1`. -/
theorem exists_inv (a : ZModUnits n) : ∃ b : ZModUnits n, a * b = 1 :=
  surjective_of_injective (fun b => a * b) (mul_left_injective a) 1

/-- **The group `(ℤ/nℤ)ˣ`** of units modulo `n`. (The inverse is obtained from the
existence proof above by choice, so this instance is noncomputable.) -/
noncomputable instance : CommGroup (ZModUnits n) where
  mul a b := a * b
  one := 1
  inv a := Classical.choose (exists_inv a)
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  inv_mul_cancel a := by
    show Classical.choose (exists_inv a) * a = 1
    rw [mul_comm']; exact Classical.choose_spec (exists_inv a)
  mul_comm := mul_comm'

/-- The residue of a power of a unit is the power of the residue, reduced mod `n`. -/
theorem val_pow (a : ZModUnits n) (k : Nat) : (a ^ k).1.val = a.1.val ^ k % n := by
  induction k with
  | zero => exact val_one
  | succ k ih =>
    rw [pow_succ]
    show (a ^ k * a).1.val = _
    rw [val_mul, ih, Nat.mod_mul_mod, Nat.pow_succ]

end ZModUnits

/-- **Euler's totient function** `φ(n)`: the number of residues `0 ≤ a < n` coprime to `n`. -/
def totient (n : Nat) : Nat := (List.finRange n).countP (fun a => decide (Nat.Coprime a.val n))

/-- `φ(12) = 4`: the residues coprime to 12 are 1, 5, 7, 11. -/
example : totient 12 = 4 := by decide

/-- The group `(ℤ/nℤ)ˣ` has `φ(n)` elements. -/
theorem card_zmodUnits (n : Nat) [NeZero n] : card (ZModUnits n) = totient n := by
  show card {a : Fin n // Nat.Coprime a.val n} = _
  rw [card_subtype, count_eq_countP]; rfl

/-- **Euler's theorem.** If `a` is coprime to `n > 0`, then `a ^ φ(n) ≡ 1 (mod n)`. -/
theorem euler (n a : Nat) (hn : 0 < n) (ha : Nat.Coprime a n) : a ^ totient n % n = 1 % n := by
  haveI : NeZero n := ⟨by omega⟩
  let u : ZModUnits n := ⟨Fin.ofNat n a, by rw [Fin.val_ofNat, coprime_mod_iff]; exact ha⟩
  have h := pow_card_eq_one u
  rw [card_zmodUnits] at h
  have h' := congrArg (fun v : ZModUnits n => v.1.val) h
  simp only [ZModUnits.val_pow, ZModUnits.val_one] at h'
  rw [Nat.pow_mod, ← h']
  rfl

/-- For a prime `p`, a number is coprime to `p` exactly when `p` does not divide it. -/
theorem coprime_prime_iff {p a : Nat} (hp : IsPrime p) : Nat.Coprime a p ↔ ¬ p ∣ a := by
  constructor
  · intro h hdvd
    have : p ∣ Nat.gcd a p := Nat.dvd_gcd hdvd (Nat.dvd_refl p)
    rw [h] at this
    have := Nat.le_of_dvd (by omega) this
    have := hp.1
    omega
  · intro h
    rcases hp.2 _ (Nat.gcd_dvd_right a p) with h1 | h1
    · exact h1
    · exfalso; apply h; rw [← h1]; exact Nat.gcd_dvd_left a p

/-- For a prime `p`, `φ(p) = p - 1`: every non-zero residue is coprime to `p`. -/
theorem totient_prime {p : Nat} (hp : IsPrime p) : totient p = p - 1 := by
  haveI : NeZero p := ⟨by have := hp.1; omega⟩
  rw [← card_zmodUnits]
  show card {a : Fin p // Nat.Coprime a.val p} = _
  rw [card_subtype]
  have hc : count (fun a : Fin p => Nat.Coprime a.val p) = count (fun a : Fin p => ¬ a = 0) := by
    apply count_congr
    intro a
    rw [coprime_prime_iff hp]
    constructor
    · intro h h0; apply h; rw [h0]; exact Nat.dvd_zero p
    · intro h hdvd
      apply h
      apply Fin.ext
      exact Nat.eq_zero_of_dvd_of_lt hdvd a.isLt
  rw [hc]
  have := count_add_count_not (fun a : Fin p => a = 0)
  rw [count_eq_self, card_fin] at this
  omega

/-- **Fermat's little theorem.** If `p` is prime and does not divide `a`, then
`a ^ (p - 1) ≡ 1 (mod p)`. -/
theorem fermat (p a : Nat) (hp : IsPrime p) (ha : ¬ p ∣ a) : a ^ (p - 1) % p = 1 := by
  have h2 := hp.1
  have := euler p a (by omega) ((coprime_prime_iff hp).2 ha)
  rw [totient_prime hp, Nat.mod_eq_of_lt (by omega : 1 < p)] at this
  exact this

end Foundations.Algebra
