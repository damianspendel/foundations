import Foundations.Algebra.Ring

/-!
# Group actions, the orbit–stabiliser theorem and `p`-groups

Groups matter because they *act*. Galois's groups act on the roots of an equation,
symmetry groups act on figures, and Felix Klein's Erlangen programme (1872) went so far
as to define a geometry as the study of the invariants of a group acting on a space.
Cayley's theorem (earlier in this part) is the observation that every group acts on
itself; in this file we make the notion of action explicit.

A **group action** of `G` on a set `X` assigns to each `g` a transformation `x ↦ g • x`
compatibly with multiplication. Each point `x` then has an **orbit** (where it can be
moved to) and a **stabiliser** (the elements that fix it). The **orbit–stabiliser
theorem** says these are complementary: `|orbit x| · |Stab x| = |G|`. It is Lagrange's
theorem in disguise, since the points of the orbit correspond to the cosets of the
stabiliser.

The orbits partition `X`, and when `|G| = p^k` is a prime power every orbit has size
`1` or a multiple of `p`. Counting modulo `p` we obtain the *class equation* in the
form we need: **the number of fixed points is congruent to `|X|` modulo `p`**. Applied
to the action of a `p`-group on itself by conjugation it shows that a non-trivial
`p`-group has a non-trivial centre — the first step in the structure theory initiated by
Ludwig Sylow (1872). The same congruence powers McKay's proof of Cauchy's theorem in the
next file.
-/

namespace Foundations.Algebra

open Group FiniteType

universe u v

/-- **Group action.** An action of the group `G` on a type `X` is an operation
`g • x` such that `1 • x = x` and `(g * h) • x = g • (h • x)`. -/
class MulAction (G : Type u) [Group G] (X : Type v) extends SMul G X where
  /-- The identity acts trivially. -/
  one_smul : ∀ x : X, (1 : G) • x = x
  /-- Acting by a product is acting successively. -/
  mul_smul : ∀ (g h : G) (x : X), (g * h) • x = g • (h • x)

namespace MulAction

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

/-- Acting by `g` and then by `g⁻¹` does nothing. -/
theorem inv_smul_smul (g : G) (x : X) : g⁻¹ • g • x = x := by
  rw [← mul_smul, inv_mul_cancel, one_smul]

/-- Acting by `g⁻¹` and then by `g` does nothing. -/
theorem smul_inv_smul (g : G) (x : X) : g • g⁻¹ • x = x := by
  rw [← mul_smul, mul_inv_cancel, one_smul]

/-- Each `g` acts injectively. -/
theorem smul_left_cancel (g : G) {x y : X} (h : g • x = g • y) : x = y := by
  rw [← inv_smul_smul g x, h, inv_smul_smul]

variable (G)

/-- The **orbit** of `x`: all points `g • x` reachable from `x`. -/
def orbit (x : X) : X → Prop := fun y => ∃ g : G, g • x = y

/-- The **stabiliser** of `x`: the elements of `G` fixing `x`. It is a subgroup. -/
def stabilizer (x : X) : Subgroup G where
  carrier g := g • x = x
  one_mem := one_smul x
  mul_mem := by intro a b ha hb; show (a * b) • x = x; rw [mul_smul, hb, ha]
  inv_mem := by intro a ha; show a⁻¹ • x = x; rw [← ha, inv_smul_smul, ha]

/-- A point is **fixed** by the action if every element of `G` fixes it. -/
def IsFixed (x : X) : Prop := ∀ g : G, g • x = x

variable {G}

/-- Every point lies in its own orbit. -/
theorem mem_orbit_self (x : X) : orbit G x x := ⟨1, one_smul x⟩

/-- Orbits are closed under the action. -/
theorem orbit_smul {x y : X} (h : orbit G x y) (g : G) : orbit G x (g • y) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨g * a, mul_smul g a x⟩

/-- Being in the same orbit is symmetric. -/
theorem orbit_symm {x y : X} (h : orbit G x y) : orbit G y x := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a⁻¹, inv_smul_smul a x⟩

/-- Being in the same orbit is transitive. -/
theorem orbit_trans {x y z : X} (h1 : orbit G x y) (h2 : orbit G y z) : orbit G x z := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨b * a, mul_smul b a x⟩

/-- `g • x = h • x` exactly when `h⁻¹ * g` stabilises `x`: the elements sending `x` to a given
point form a left coset of the stabiliser. -/
theorem smul_eq_smul_iff (g h : G) (x : X) :
    g • x = h • x ↔ leftCoset h (stabilizer G x) g := by
  show g • x = h • x ↔ (h⁻¹ * g) • x = x
  rw [mul_smul]
  constructor
  · intro e; rw [e, inv_smul_smul]
  · intro e; rw [← smul_inv_smul h (g • x), e]

/-- A fixed point is alone in its orbit. -/
theorem orbit_of_fixed {x y : X} (hx : IsFixed G x) (h : orbit G x y) : y = x := by
  obtain ⟨g, rfl⟩ := h; exact hx g

/-- If some point of the orbit of `x` is fixed, then `x` itself is fixed. -/
theorem fixed_of_orbit_fixed {x y : X} (h : orbit G x y) (hy : IsFixed G y) : IsFixed G x := by
  have := orbit_of_fixed hy (orbit_symm h)
  rw [this]; exact hy

/-! ## The orbit–stabiliser theorem -/

variable [FiniteType G] [FiniteType X]

omit [FiniteType X] in
/-- Each fibre of the orbit map `g ↦ g • x` over a point of the orbit has `|Stab x|`
elements. -/
theorem count_fibre (x : X) (h : G) :
    count (fun g : G => g • x = h • x) = count (· ∈ stabilizer G x) := by
  rw [← count_leftCoset h (stabilizer G x)]
  exact count_congr fun g => smul_eq_smul_iff g h x

/-- Counting by fibres: for any part `Q` of the orbit of `x`, the number of `g` with
`g • x ∈ Q` is `|Q| · |Stab x|`. Proved by removing one point of `Q` at a time. -/
theorem count_smul_mem (x : X) :
    ∀ (n : Nat) (Q : X → Prop), count Q = n → (∀ y, Q y → orbit G x y) →
      count (fun g : G => Q (g • x)) = n * count (· ∈ stabilizer G x) := by
  intro n
  induction n with
  | zero =>
    intro Q hQ _
    rw [Nat.zero_mul, count_eq_zero]
    intro g hg
    exact count_eq_zero.1 hQ _ hg
  | succ n ih =>
    intro Q hQ hsub
    obtain ⟨y, hy⟩ := count_pos.1 (by omega : 0 < count Q)
    obtain ⟨h, rfl⟩ := hsub y hy
    have hsplit := count_split Q (· = h • x)
    rw [count_congr (P := fun z => Q z ∧ z = h • x) (Q := fun z => z = h • x)
      (fun z => ⟨fun hz => hz.2, fun hz => ⟨hz ▸ hy, hz⟩⟩), count_eq_self] at hsplit
    have hrest := ih (fun z => Q z ∧ ¬ z = h • x) (by omega) (fun z hz => hsub z hz.1)
    have hsplit' := count_split (fun g : G => Q (g • x)) (fun g => g • x = h • x)
    rw [count_congr (P := fun g : G => Q (g • x) ∧ g • x = h • x)
      (Q := fun g : G => g • x = h • x)
      (fun g => ⟨fun hg => hg.2, fun hg => ⟨hg ▸ hy, hg⟩⟩), count_fibre] at hsplit'
    rw [hsplit', hrest, Nat.succ_mul, Nat.add_comm]

/-- **Orbit–stabiliser theorem.** For a finite group `G` acting on a finite set `X`,
`|orbit x| · |Stab x| = |G|` for every point `x`. -/
theorem orbit_stabilizer (x : X) : count (orbit G x) * card (stabilizer G x) = card G := by
  rw [show card (stabilizer G x) = count (· ∈ stabilizer G x) from card_subtype _,
    ← count_smul_mem x _ (orbit G x) rfl (fun _ h => h), ← count_true]
  exact count_congr fun g => ⟨fun _ => trivial, fun _ => ⟨g, rfl⟩⟩

/-- The size of an orbit divides the order of the group. -/
theorem count_orbit_dvd (x : X) : count (orbit G x) ∣ card G :=
  ⟨_, (orbit_stabilizer x).symm⟩

end MulAction

/-! ## Prime powers -/

/-- **Euclid's lemma.** A prime dividing a product divides one of the factors. -/
theorem IsPrime.dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · right
    have hc : Nat.Coprime p a := ((coprime_prime_iff hp).2 ha).symm
    exact hc.dvd_of_dvd_mul_left h

/-- A divisor of `p ^ k` other than `1` is divisible by `p`. -/
theorem IsPrime.dvd_of_dvd_pow {p k d : Nat} (hp : IsPrime p) (hd : d ∣ p ^ k) (h1 : d ≠ 1) :
    p ∣ d := by
  apply Classical.byContradiction
  intro hnd
  have hc : Nat.Coprime d p := (coprime_prime_iff hp).2 hnd
  have hck : Nat.Coprime d (p ^ k) := Nat.Coprime.pow_right k hc
  have : Nat.gcd d (p ^ k) = d := Nat.gcd_eq_left hd
  exact h1 (this ▸ hck)

/-! ## Fixed points of `p`-group actions -/

namespace MulAction

variable {G : Type u} [Group G] {X : Type v} [MulAction G X] [FiniteType G] [FiniteType X]

omit [FiniteType G] in
/-- A point that is not fixed has at least two points in its orbit. -/
theorem one_lt_count_orbit {x : X} (hx : ¬ IsFixed G x) : 1 < count (orbit G x) := by
  have : ∃ g : G, g • x ≠ x := by
    apply Classical.byContradiction
    intro hno
    exact hx fun g => Classical.byContradiction fun hg => hno ⟨g, hg⟩
  obtain ⟨g, hg⟩ := this
  have h1 := count_split (orbit G x) (· = x)
  have h2 : count (fun y => orbit G x y ∧ y = x) = 1 := by
    rw [← count_eq_self x]
    exact count_congr fun y => ⟨fun h => h.2, fun h => ⟨h ▸ mem_orbit_self (G := G) x, h⟩⟩
  have h3 : 0 < count (fun y => orbit G x y ∧ ¬ y = x) := count_pos.2 ⟨g • x, ⟨g, rfl⟩, hg⟩
  omega

/-- **The fixed-point congruence (class equation modulo `p`).** If a group of order `p ^ k`
(with `p` prime) acts on a finite set `X`, then the number of fixed points is congruent to
`|X|` modulo `p`. More generally this holds for every invariant subset `P` of `X`. Proof:
peel off one non-trivial orbit at a time; each has size a multiple of `p`. -/
theorem count_fixed_mod_of_invariant {p k : Nat} (hp : IsPrime p) (hG : card G = p ^ k) :
    ∀ (n : Nat) (P : X → Prop), count P = n → (∀ (g : G) y, P y → P (g • y)) →
      count (fun y => P y ∧ IsFixed G y) % p = n % p := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro P hn hinv
    by_cases hall : ∀ y, P y → IsFixed G y
    · rw [← hn]
      congr 1
      exact count_congr fun y => ⟨fun h => h.1, fun h => ⟨h, hall y h⟩⟩
    · have : ∃ y, P y ∧ ¬ IsFixed G y := by
        apply Classical.byContradiction
        intro hno
        exact hall fun y hy => Classical.byContradiction fun hf => hno ⟨y, hy, hf⟩
      obtain ⟨y, hy, hny⟩ := this
      -- The orbit of `y` lies in `P`, has size divisible by `p`, and contains no fixed point.
      have hOP : ∀ z, orbit G y z → P z := by
        intro z ⟨g, hg⟩; rw [← hg]; exact hinv g y hy
      have hOdvd : p ∣ count (orbit G y) := by
        apply hp.dvd_of_dvd_pow (k := k)
        · rw [← hG]; exact count_orbit_dvd y
        · have := one_lt_count_orbit hny; omega
      have hsplit := count_split P (orbit G y)
      rw [count_congr (P := fun z => P z ∧ orbit G y z) (Q := orbit G y)
        (fun z => ⟨fun h => h.2, fun h => ⟨hOP z h, h⟩⟩)] at hsplit
      have hpos : 0 < count (orbit G y) := count_pos.2 ⟨y, mem_orbit_self (G := G) y⟩
      have hinv' : ∀ (g : G) z, (P z ∧ ¬ orbit G y z) → (P (g • z) ∧ ¬ orbit G y (g • z)) := by
        intro g z ⟨hz, hno⟩
        refine ⟨hinv g z hz, fun ho => hno ?_⟩
        have := orbit_smul ho g⁻¹
        rwa [inv_smul_smul] at this
      have hrest := ih _ (by omega) _ rfl hinv'
      have hfix : count (fun z => P z ∧ IsFixed G z) =
          count (fun z => (P z ∧ ¬ orbit G y z) ∧ IsFixed G z) := by
        apply count_congr
        intro z
        constructor
        · intro ⟨hz, hf⟩
          exact ⟨⟨hz, fun ho => hny (fixed_of_orbit_fixed ho hf)⟩, hf⟩
        · intro ⟨⟨hz, _⟩, hf⟩; exact ⟨hz, hf⟩
      rw [hfix, hrest, ← hn, hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd hOdvd, Nat.zero_add,
        Nat.mod_mod]

/-- **Fixed points of `p`-group actions.** If a group of order `p ^ k` acts on a finite set
`X`, then `#(fixed points) ≡ |X| (mod p)`. -/
theorem count_fixed_mod {p k : Nat} (hp : IsPrime p) (hG : card G = p ^ k) :
    count (IsFixed G (X := X)) % p = card X % p := by
  rw [← count_true]
  rw [← count_fixed_mod_of_invariant hp hG _ (fun _ : X => True) rfl (fun _ _ _ => trivial)]
  congr 1
  exact count_congr fun y => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

end MulAction

/-! ## Examples of actions -/

/-- **Every group acts on itself** by left multiplication, `g • x = g * x` (the action behind
Cayley's theorem). -/
instance Group.selfAction (G : Type u) [Group G] : MulAction G G where
  smul g x := g * x
  one_smul := Group.one_mul
  mul_smul := Group.mul_assoc

/-- **Permutations act on what they permute**: `σ • x = σ x`. -/
instance Perm.action (α : Type u) : MulAction (Perm α) α where
  smul σ x := σ x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- A type synonym for `G` on which `G` acts by conjugation. -/
def ConjAct (G : Type u) : Type u := G

/-- View an element of `G` as a point of `ConjAct G`. -/
def ConjAct.of {G : Type u} (z : G) : ConjAct G := z

/-- `ConjAct G` is finite when `G` is. -/
instance ConjAct.instFinite (G : Type u) [FiniteType G] : FiniteType (ConjAct G) :=
  inferInstanceAs (FiniteType G)

/-- **Conjugation action.** `G` acts on (a copy of) itself by `g • x = g * x * g⁻¹`. Its orbits
are the *conjugacy classes*. -/
instance ConjAct.action (G : Type u) [Group G] : MulAction G (ConjAct G) where
  smul := fun g (x : G) => (g * x * g⁻¹ : G)
  one_smul := fun (x : G) => by show 1 * x * 1⁻¹ = x; rw [inv_one, mul_one, one_mul]
  mul_smul := fun g h (x : G) => by
    show g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹
    rw [mul_inv_rev]; simp only [Group.mul_assoc]

/-- The **centre** of a group: the elements commuting with everything. -/
def center (G : Type u) [Group G] : Subgroup G where
  carrier z := ∀ g : G, g * z = z * g
  one_mem g := by rw [mul_one, one_mul]
  mul_mem := by
    intro a b ha hb g
    rw [← Group.mul_assoc, ha, Group.mul_assoc, hb, Group.mul_assoc]
  inv_mem := by
    intro a ha g
    apply mul_left_cancel (a := a)
    rw [mul_inv_cancel_left, ← Group.mul_assoc, ← ha, Group.mul_assoc, mul_inv_cancel, mul_one]

/-- The fixed points of the conjugation action are exactly the central elements. -/
theorem ConjAct.isFixed_iff {G : Type u} [Group G] (z : G) :
    MulAction.IsFixed G (ConjAct.of z) ↔ z ∈ center G := by
  constructor
  · intro h g
    have : g * z * g⁻¹ = z := h g
    calc g * z = g * z * g⁻¹ * g := (inv_mul_cancel_right _ _).symm
      _ = z * g := by rw [this]
  · intro h g
    show g * z * g⁻¹ = z
    rw [h g, mul_inv_cancel_right]

/-- **Non-trivial `p`-groups have non-trivial centre.** If `|G| = p ^ k` with `p` prime and
`k ≥ 1`, then `p` divides the order of the centre; in particular the centre contains an
element other than `1`. (This is the class equation `|G| = |Z(G)| + Σ [G : C(xᵢ)]`, read
modulo `p`.) -/
theorem pGroup_center {G : Type u} [Group G] [FiniteType G] {p k : Nat} (hp : IsPrime p)
    (hk : 1 ≤ k) (hG : card G = p ^ k) : p ∣ card (center G) := by
  have h := MulAction.count_fixed_mod (X := ConjAct G) hp hG
  have hc : card (ConjAct G) = card G := rfl
  rw [hc, hG] at h
  have hz : count (MulAction.IsFixed G (X := ConjAct G)) = card (center G) := by
    rw [show card (center G) = count (· ∈ center G) from card_subtype _]
    exact count_comp_bij (α := G) (β := ConjAct G) ConjAct.of (fun _ _ h => h)
      (fun y => ⟨y, rfl⟩) _ |>.symm.trans (count_congr fun z => ConjAct.isFixed_iff z)
  rw [hz] at h
  apply Nat.dvd_of_mod_eq_zero
  rw [h]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_mod_left]

end Foundations.Algebra
