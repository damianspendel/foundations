import Foundations.Algebra.Action

/-!
# Cauchy's theorem

Lagrange's theorem says that the order of every element divides `|G|`. Its converse is
false in general — a group of order `12` need have no subgroup of order `6` — but it is
true for *primes*: **Cauchy's theorem** (Augustin-Louis Cauchy, 1845) says that if a prime
`p` divides `|G|`, then `G` has an element of order exactly `p`.

Cauchy's own proof ran to many pages. The proof formalised here is due to James McKay
(1959) and is a small masterpiece of the "count it two ways" style. Consider the set `X`
of `p`-tuples `(x₀, x₁, …, x_{p-1})` of elements of `G` whose product `x₀ x₁ ⋯ x_{p-1}`
is `1`.

* Counting directly: the first `p - 1` entries can be chosen freely and then the last is
  determined, so `|X| = |G|^(p-1)`, a multiple of `p`.
* Counting by symmetry: the cyclic group `ℤ/pℤ` acts on `X` by rotating tuples (a rotation
  of a tuple with product `1` still has product `1`). By the fixed-point congruence of the
  previous file, the number of fixed points — the constant tuples `(g, g, …, g)` with
  `g ^ p = 1` — is congruent to `|X| ≡ 0` modulo `p`.

Since the constant tuple `(1, …, 1)` is one such fixed point, there are at least `p ≥ 2`
of them, so some `g ≠ 1` satisfies `g ^ p = 1`, and that `g` has order `p`.

Along the way we show that the tuples `Fin n → α` over a finite type form a finite type
with `|α| ^ n` elements.
-/

namespace Foundations.Algebra

open Group FiniteType

universe u

/-! ## Tuples -/

section Tuples

variable {α : Type u}

/-- Prepend an entry to a tuple: `tcons a (x₀, …, x_{n-1}) = (a, x₀, …, x_{n-1})`. -/
def tcons {n : Nat} (a : α) (f : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩ => a
  | ⟨k + 1, h⟩ => f ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Drop the first entry of a tuple. -/
def ttail {n : Nat} (f : Fin (n + 1) → α) : Fin n → α := fun i => f i.succ

/-- The first entry of `tcons a f` is `a`. -/
@[simp] theorem tcons_zero {n : Nat} (a : α) (f : Fin n → α) : tcons a f 0 = a := rfl

/-- The tail of `tcons a f` is `f`. -/
@[simp] theorem ttail_tcons {n : Nat} (a : α) (f : Fin n → α) : ttail (tcons a f) = f := rfl

/-- A tuple is its first entry followed by its tail. -/
theorem tcons_self_ttail {n : Nat} (f : Fin (n + 1) → α) : tcons (f 0) (ttail f) = f := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨k + 1, h⟩ => rfl

/-- The census of all `n`-tuples with entries from the list `L`. -/
def tuples (L : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [fun i => absurd i.isLt (Nat.not_lt_zero _)]
  | n + 1 => L.flatMap (fun a => (tuples L n).map (tcons a))

/-- Every tuple with entries in `L` appears in the census. -/
theorem mem_tuples (L : List α) : ∀ (n : Nat) (f : Fin n → α), (∀ i, f i ∈ L) → f ∈ tuples L n
  | 0, f, _ => by
    simp only [tuples, List.mem_singleton]
    funext i; exact absurd i.isLt (Nat.not_lt_zero _)
  | n + 1, f, h => by
    simp only [tuples, List.mem_flatMap, List.mem_map]
    exact ⟨f 0, h 0, ttail f, mem_tuples L n _ (fun i => h i.succ), tcons_self_ttail f⟩

/-- A `flatMap` of repetition-free, pairwise disjoint blocks indexed by a repetition-free
list is repetition-free. -/
theorem nodup_flatMap {β : Type _} {l : List α} {f : α → List β} (h1 : l.Nodup)
    (h2 : ∀ a, (f a).Nodup) (h3 : ∀ a b, a ≠ b → ∀ x, x ∈ f a → x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    rw [List.nodup_cons] at h1
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h2 a, ih h1.2, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_flatMap] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    have hab : a ≠ b := fun e => h1.1 (e ▸ hb)
    exact h3 a b hab x hx (hxy ▸ hyb)

/-- The census of tuples has no repetitions. -/
theorem nodup_tuples (L : List α) (hL : L.Nodup) : ∀ n, (tuples L n).Nodup
  | 0 => List.nodup_cons.2 ⟨by simp, List.Pairwise.nil⟩
  | n + 1 => by
    apply nodup_flatMap hL
    · intro a
      apply nodup_map_of_injective _ (nodup_tuples L hL n)
      intro f g h
      have := congrArg ttail h
      simpa using this
    · intro a b hab x hx hx'
      rw [List.mem_map] at hx hx'
      obtain ⟨f, _, rfl⟩ := hx
      obtain ⟨g, _, hg⟩ := hx'
      exact hab (congrFun hg 0).symm

/-- A sum of a constant over a list. -/
theorem sum_map_const {β : Type u} (l : List β) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- There are `(length L) ^ n` tuples with entries in `L`. -/
theorem length_tuples (L : List α) : ∀ n, (tuples L n).length = L.length ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [tuples, List.length_flatMap, List.length_map, length_tuples L n]
    rw [sum_map_const, Nat.pow_succ, Nat.mul_comm]

/-- **Tuples over a finite type form a finite type.** -/
instance instFiniteTuple [FiniteType α] (n : Nat) : FiniteType (Fin n → α) where
  elems := tuples elems n
  nodup := nodup_tuples _ nodup n
  complete f := mem_tuples _ n f (fun i => complete (f i))

/-- There are `|α| ^ n` tuples of length `n` over `α`. -/
theorem card_tuple [FiniteType α] (n : Nat) : card (Fin n → α) = card α ^ n :=
  length_tuples _ n

end Tuples

/-! ## Products of tuples -/

section Products

variable {G : Type u} [Group G]

/-- The **product** `x₀ * x₁ * ⋯ * x_{n-1}` of a tuple of group elements. -/
def tprod : {n : Nat} → (Fin n → G) → G
  | 0, _ => 1
  | _ + 1, x => x 0 * tprod (ttail x)

/-- The product of a tuple splits off the last entry. -/
theorem tprod_last : ∀ {m : Nat} (x : Fin (m + 1) → G),
    tprod x = tprod (fun i : Fin m => x i.castSucc) * x (Fin.last m)
  | 0, x => by
    show x 0 * 1 = 1 * x (Fin.last 0)
    rw [mul_one, one_mul]; rfl
  | m + 1, x => by
    show x 0 * tprod (ttail x) = x 0 * tprod (ttail (fun i : Fin (m + 1) => x i.castSucc)) * _
    rw [tprod_last (ttail x), mul_assoc]
    rfl

/-- The product of a constant tuple is a power. -/
theorem tprod_const (g : G) : ∀ n, tprod (fun _ : Fin n => g) = g ^ n
  | 0 => rfl
  | n + 1 => by
    show g * tprod (fun _ : Fin n => g) = _
    rw [tprod_const g n, pow_succ']

/-- **Rotating a tuple conjugates its product.** If `x` has `m + 1` entries and
`x'ᵢ = x_{i+1}` (indices modulo `m + 1`), then `∏ x' = x₀⁻¹ (∏ x) x₀`. -/
theorem tprod_rotate {m : Nat} (x : Fin (m + 1) → G) :
    tprod (fun i => x (i + Fin.ofNat (m + 1) 1)) = (x 0)⁻¹ * tprod x * x 0 := by
  rw [tprod_last]
  have h1 : (fun i : Fin m => x (i.castSucc + Fin.ofNat (m + 1) 1)) = ttail x := by
    funext i
    show x _ = x i.succ
    congr 1
    apply Fin.ext
    have hi := i.isLt
    rw [Fin.val_add, Fin.val_castSucc, Fin.val_ofNat, Fin.val_succ,
      Nat.mod_eq_of_lt (by omega : 1 < m + 1), Nat.mod_eq_of_lt (by omega)]
  have h2 : Fin.last m + Fin.ofNat (m + 1) 1 = 0 := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_last, Fin.val_ofNat]
    show _ = 0
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; rfl
    · rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1), Nat.mod_self]
  rw [h1, h2]
  show tprod (ttail x) * x 0 = (x 0)⁻¹ * (x 0 * tprod (ttail x)) * x 0
  rw [inv_mul_cancel_left]

end Products

/-! ## McKay's proof -/

section McKay

variable (G : Type u) [Group G]

/-- The **necklaces** of length `p`: `p`-tuples of group elements, which the cyclic group
`ℤ/pℤ` rotates. -/
def Necklace (p : Nat) : Type u := Fin p → G

variable {G}

/-- `ℤ/nℤ` (as an additive group on `Fin n`) is finite. -/
instance ZMod.instFinite (n : Nat) : FiniteType (ZMod n) := inferInstanceAs (FiniteType (Fin n))

/-- `ℤ/nℤ` has `n` elements. -/
theorem ZMod.card (n : Nat) : card (ZMod n) = n := card_fin n

variable {p : Nat} [NeZero p]

/-- **Rotation action.** `k ∈ ℤ/pℤ` rotates a necklace by `k` places:
`(k • x)ᵢ = x_{i+k}`. -/
instance Necklace.action : MulAction (ZMod p) (Necklace G p) where
  smul k x := fun i => x (i + ZMod.val k)
  one_smul x := by
    funext i
    show x (i + 0) = x i
    congr 1; grind
  mul_smul j k x := by
    funext i
    show x (i + (ZMod.val j + ZMod.val k)) = x (i + ZMod.val j + ZMod.val k)
    congr 1; grind

omit [Group G] in
/-- How rotation acts on entries. -/
theorem Necklace.smul_apply (k : ZMod p) (x : Necklace G p) (i : Fin p) :
    (k • x) i = x (i + ZMod.val k) := rfl

/-- Rotation preserves the property "the product is `1`". -/
theorem Necklace.tprod_smul (k : ZMod p) (x : Necklace G p) (h : tprod (n := p) x = 1) :
    tprod (n := p) (k • x) = 1 := by
  obtain ⟨j, rfl⟩ := ZMod.cyclic k
  induction j with
  | zero => rw [pow_zero, MulAction.one_smul]; exact h
  | succ j ih =>
    rw [pow_succ', MulAction.mul_smul]
    generalize hy : (ZMod.gen ^ j : ZMod p) • x = y at ih
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := NeZero.ne p; omega⟩
    have hr := tprod_rotate (G := G) (m := m) y
    rw [ih, mul_one, inv_mul_cancel] at hr
    exact hr

/-- McKay's set `X`: the necklaces of length `p` whose product is `1`. -/
def McKaySet (G : Type u) [Group G] (p : Nat) : Type u :=
  {x : Necklace G p // tprod (n := p) x = 1}

/-- `ℤ/pℤ` acts on McKay's set by rotation. -/
instance McKaySet.action : MulAction (ZMod p) (McKaySet G p) where
  smul k x := ⟨k • x.1, Necklace.tprod_smul k x.1 x.2⟩
  one_smul x := Subtype.ext (MulAction.one_smul x.1)
  mul_smul j k x := Subtype.ext (MulAction.mul_smul j k x.1)

variable [FiniteType G]

/-- McKay's set is finite. -/
noncomputable instance McKaySet.instFinite : FiniteType (McKaySet G p) :=
  FiniteType.instSubtype (fun x : Fin p → G => tprod (n := p) x = 1)

/-- **Counting McKay's set directly.** `|X| = |G| ^ (p - 1)`: the first entry of a necklace
with product `1` is determined by the remaining `p - 1` free entries. -/
theorem card_mcKaySet (m : Nat) : card (McKaySet G (m + 1)) = card G ^ m := by
  rw [← card_tuple (α := G) m, ← count_true, ← count_true]
  let e : (Fin m → G) → McKaySet G (m + 1) := fun y =>
    ⟨tcons (tprod y)⁻¹ y, by show (tprod y)⁻¹ * tprod (ttail (tcons _ y)) = 1;
                             rw [ttail_tcons, inv_mul_cancel]⟩
  refine (count_comp_bij e ?_ ?_ (fun _ => True)).symm
  · intro y y' h
    have := congrArg (fun x : McKaySet G (m + 1) => ttail x.1) h
    simpa [e] using this
  · intro ⟨x, hx⟩
    refine ⟨ttail x, Subtype.ext ?_⟩
    show tcons (tprod (ttail x))⁻¹ (ttail x) = x
    have h0 : (tprod (ttail x))⁻¹ = x 0 := by
      have : x 0 * tprod (ttail x) = 1 := hx
      rw [← inv_eq_of_mul_eq_one this, inv_inv]
    rw [h0]; exact tcons_self_ttail x

omit [Group G] [FiniteType G] in
/-- A necklace fixed by rotation is constant. -/
theorem Necklace.const_of_fixed {m : Nat} (x : Necklace G (m + 1))
    (hx : (ZMod.gen : ZMod (m + 1)) • x = x) : ∀ i, x i = x 0 := by
  have step : ∀ i : Fin (m + 1), x (i + Fin.ofNat (m + 1) 1) = x i :=
    fun i => congrFun hx i
  intro ⟨k, hk⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih (by omega), ← step ⟨k, by omega⟩]
    congr 1
    apply Fin.ext
    rw [Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 1 < m + 1),
      Nat.mod_eq_of_lt hk]

/-- **Cauchy's theorem.** If a prime `p` divides the order of a finite group `G`, then `G`
has an element of order exactly `p`. -/
theorem cauchy {p : Nat} (hp : IsPrime p) (hdvd : p ∣ card G) : ∃ g : G, orderOf g = p := by
  have hp2 := hp.1
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  -- The fixed-point congruence for the rotation action.
  have hcong := MulAction.count_fixed_mod (G := ZMod (m + 1)) (X := McKaySet G (m + 1)) hp
    (k := 1) (by rw [ZMod.card, Nat.pow_one])
  rw [card_mcKaySet] at hcong
  have h0 : card G ^ m % (m + 1) = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.pow_succ]; exact Nat.dvd_mul_left_of_dvd hdvd _
  rw [h0] at hcong
  -- The constant necklace `(1, …, 1)` is a fixed point.
  let one : McKaySet G (m + 1) := ⟨fun _ => 1, by rw [tprod_const, one_pow]⟩
  have hone : MulAction.IsFixed (ZMod (m + 1)) one := fun k => Subtype.ext rfl
  -- Hence there are at least `p` fixed points, and one of them is not `(1, …, 1)`.
  have hpos : 0 < count (MulAction.IsFixed (ZMod (m + 1)) (X := McKaySet G (m + 1))) :=
    count_pos.2 ⟨one, hone⟩
  have hge : m + 1 ≤ count (MulAction.IsFixed (ZMod (m + 1)) (X := McKaySet G (m + 1))) :=
    Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero hcong)
  have hsplit := count_split (MulAction.IsFixed (ZMod (m + 1)) (X := McKaySet G (m + 1)))
    (· = one)
  have hle : count (fun x : McKaySet G (m + 1) =>
      MulAction.IsFixed (ZMod (m + 1)) x ∧ x = one) ≤ 1 := by
    exact Nat.le_trans (count_mono fun _ h => h.2) (Nat.le_of_eq (count_eq_self one))
  obtain ⟨x, hxfix, hxne⟩ := count_pos.1 (by omega :
    0 < count (fun x : McKaySet G (m + 1) => MulAction.IsFixed (ZMod (m + 1)) x ∧ ¬ x = one))
  -- That fixed point is a constant necklace `(g, …, g)` with `g ≠ 1` and `g ^ p = 1`.
  have hconst := Necklace.const_of_fixed x.1 (congrArg Subtype.val (hxfix ZMod.gen))
  refine ⟨x.1 0, ?_⟩
  have hx1 : x.1 = fun _ => x.1 0 := funext hconst
  have hpow : x.1 0 ^ (m + 1) = 1 := by
    have := x.2
    rw [hx1, tprod_const] at this
    exact this
  have hne1 : x.1 0 ≠ 1 := by
    intro h
    apply hxne
    apply Subtype.ext
    rw [hx1, h]
  rcases hp.2 _ ((pow_eq_one_iff_dvd _ _).1 hpow) with h | h
  · exfalso; apply hne1
    have := pow_orderOf (x.1 0)
    rwa [h, pow_one] at this
  · exact h

end McKay

end Foundations.Algebra
