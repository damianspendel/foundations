import Foundations.Algebra.Alternating

/-!
# The simplicity of `A₅`

A group is **simple** if it has no normal subgroups besides the trivial group and itself: it
cannot be broken into smaller pieces by passing to a quotient. **The alternating group `A₅`, of
order 60, is simple** — the smallest non-abelian simple group.

This is the group-theoretic heart of the **insolvability of the quintic**. Ruffini (1799) and
Abel (1824) showed that the general equation of degree five cannot be solved by radicals;
Galois (1830–32) explained why. Solving by radicals means building a tower of extensions, each
obtained by adjoining an `m`-th root, and Galois saw that such a tower corresponds to breaking
the *Galois group* of the equation into a chain of normal subgroups with abelian quotients — a
*solvable* group. The general quintic has Galois group `S₅`, whose only non-trivial proper
normal subgroup is `A₅`; and `A₅`, being simple and non-abelian, cannot be broken down
further. So no chain with abelian steps exists, and no formula in radicals can exist. (This
file is pure group theory; the next file proves "`Sₙ` is not solvable for `n ≥ 5`". Artin's
half of the Galois correspondence is in `GaloisCorrespondence.lean`, and the insolvability of
`x⁵ − 6x + 3` by radicals in `QuinticNotRadical.lean`.)

**The proof.** Let `N ≠ 1` be normal in `A₅` and pick `σ ∈ N` with `σ ≠ 1`.

1. Conjugating by a suitable even permutation (which keeps us in `N`), we may assume
   `σ(0) = 1`. There are only 24 permutations with `σ(0) = 1`, 12 of them even.
2. For each of these 12 we exhibit a 3-cycle `g` such that the commutator `σ g σ⁻¹ g⁻¹` is again
   a 3-cycle. The commutator lies in `N`, because `N` is normal.
3. All 3-cycles are conjugate in `A₅`, so `N` contains every 3-cycle; and the 3-cycles generate
   `A₅` (previous file). Hence `N = A₅`.

Step 2 is a finite verification, carried out by the Lean kernel (`decide`) on the explicit
table below: it is a proof by exhaustion over the 24 cases, in the same spirit as the
classical proof's case distinction by cycle type, but with every case checked mechanically.
-/

namespace Foundations.Algebra

open FiniteType Group Perm

/-! ## Even permutations moving three given points to `0, 1, 2` -/

/-- **`A₅` acts transitively on ordered triples.** For distinct `a, b, c ∈ Fin 5` there is an
even permutation `π` with `π a = 0`, `π b = 1`, `π c = 2`. -/
theorem exists_even_move3 {a b c : Fin 5} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ π : Perm (Fin 5), π ∈ alternating 5 ∧ π a = 0 ∧ π b = 1 ∧ π c = 2 := by
  let ρ1 := swap (0 : Fin 5) a
  let ρ2 := swap (1 : Fin 5) (ρ1 b)
  let ρ3 := swap (2 : Fin 5) (ρ2 (ρ1 c))
  have hρ1a : ρ1 a = 0 := swap_apply_right _ _
  have hb1 : ρ1 b ≠ 0 := fun h => hab (ρ1.injective (hρ1a.trans h.symm))
  have hρ2b : ρ2 (ρ1 b) = 1 := swap_apply_right _ _
  have hρ20 : ρ2 0 = 0 := swap_apply_of_ne (by decide) (Ne.symm hb1)
  have hc0 : ρ2 (ρ1 c) ≠ 0 := fun h => hac (ρ1.injective (ρ2.injective (by rw [h, hρ1a, hρ20])))
  have hc1 : ρ2 (ρ1 c) ≠ 1 := fun h => hbc (ρ1.injective (ρ2.injective (by rw [h, hρ2b])))
  let ρ := ρ3 * ρ2 * ρ1
  have hρa : ρ a = 0 := by
    show ρ3 (ρ2 (ρ1 a)) = 0
    rw [hρ1a, hρ20]; exact swap_apply_of_ne (by decide) (Ne.symm hc0)
  have hρb : ρ b = 1 := by
    show ρ3 (ρ2 (ρ1 b)) = 1
    rw [hρ2b]; exact swap_apply_of_ne (by decide) (Ne.symm hc1)
  have hρc : ρ c = 2 := by show ρ3 (ρ2 (ρ1 c)) = 2; exact swap_apply_right _ _
  cases hp : parity ρ
  · exact ⟨ρ, mem_alternating.2 hp, hρa, hρb, hρc⟩
  · refine ⟨swap 3 4 * ρ, mem_alternating.2 ?_, ?_, ?_, ?_⟩
    · rw [parity_mul, parity_swap (by decide), hp]; rfl
    · show swap (3 : Fin 5) 4 (ρ a) = 0; rw [hρa]; decide
    · show swap (3 : Fin 5) 4 (ρ b) = 1; rw [hρb]; decide
    · show swap (3 : Fin 5) 4 (ρ c) = 2; rw [hρc]; decide

/-- **All 3-cycles are conjugate in `A₅`.** A subset of `S₅` closed under conjugation by even
permutations that contains one 3-cycle contains them all. -/
theorem all_c3_of_one (N : Subgroup (Perm (Fin 5)))
    (hnorm : ∀ g, g ∈ alternating 5 → ∀ x, x ∈ N → g * x * g⁻¹ ∈ N)
    {u v w : Fin 5} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) (h : c3 u v w ∈ N) :
    ∀ σ, IsC3 σ → σ ∈ N := by
  obtain ⟨π, hπ, h1, h2, h3⟩ := exists_even_move3 huv hvw huw
  have h012 : c3 0 1 2 ∈ N := by
    have := hnorm π hπ _ h
    rwa [conj_c3, h1, h2, h3] at this
  intro σ ⟨a, b, c, hab, hbc, hac, hσ⟩
  obtain ⟨π', hπ', h1', h2', h3'⟩ := exists_even_move3 hab hbc hac
  have := hnorm π'⁻¹ ((alternating 5).inv_mem hπ') _ h012
  rw [conj_c3] at this
  have e1 : π'⁻¹ 0 = a := by rw [← h1']; exact π'.left_inv a
  have e2 : π'⁻¹ 1 = b := by rw [← h2']; exact π'.left_inv b
  have e3 : π'⁻¹ 2 = c := by rw [← h3']; exact π'.left_inv c
  rw [e1, e2, e3] at this
  rw [hσ]; exact this

/-! ## The case table -/

/-- The 24 permutations of `Fin 5` sending `0 ↦ 1`, as value tables. -/
def tblF : List (List Nat) :=
  [[1, 0, 2, 3, 4], [1, 0, 2, 4, 3], [1, 0, 3, 2, 4], [1, 0, 3, 4, 2], [1, 0, 4, 2, 3], [1, 0, 4, 3, 2], [1, 2, 0, 3, 4], [1, 2, 0, 4, 3], [1, 2, 3, 0, 4], [1, 2, 3, 4, 0], [1, 2, 4, 0, 3], [1, 2, 4, 3, 0], [1, 3, 0, 2, 4], [1, 3, 0, 4, 2], [1, 3, 2, 0, 4], [1, 3, 2, 4, 0], [1, 3, 4, 0, 2], [1, 3, 4, 2, 0], [1, 4, 0, 2, 3], [1, 4, 0, 3, 2], [1, 4, 2, 0, 3], [1, 4, 2, 3, 0], [1, 4, 3, 0, 2], [1, 4, 3, 2, 0]]

/-- Their inverses. -/
def tblFi : List (List Nat) :=
  [[1, 0, 2, 3, 4], [1, 0, 2, 4, 3], [1, 0, 3, 2, 4], [1, 0, 4, 2, 3], [1, 0, 3, 4, 2], [1, 0, 4, 3, 2], [2, 0, 1, 3, 4], [2, 0, 1, 4, 3], [3, 0, 1, 2, 4], [4, 0, 1, 2, 3], [3, 0, 1, 4, 2], [4, 0, 1, 3, 2], [2, 0, 3, 1, 4], [2, 0, 4, 1, 3], [3, 0, 2, 1, 4], [4, 0, 2, 1, 3], [3, 0, 4, 1, 2], [4, 0, 3, 1, 2], [2, 0, 3, 4, 1], [2, 0, 4, 3, 1], [3, 0, 2, 4, 1], [4, 0, 2, 3, 1], [3, 0, 4, 2, 1], [4, 0, 3, 2, 1]]

/-- For each even one, a 3-cycle `g` whose commutator with it is again a 3-cycle. -/
def tblG : List (List Nat) :=
  [[0, 1, 2], [0, 1, 2], [0, 1, 4], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 3, 4], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 2, 4], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 2, 3], [0, 1, 3], [0, 1, 2]]

/-- The resulting 3-cycle `[σ, g]`. -/
def tblT : List (List Nat) :=
  [[0, 1, 2], [0, 1, 2], [0, 1, 4], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 2], [0, 1, 2], [0, 3, 1], [0, 4, 1], [0, 1, 2], [0, 1, 2], [0, 2, 3], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 2, 1], [0, 2, 4], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 3, 4], [0, 1, 2]]

/-- Reading a table entry as an element of `Fin 5`. -/
def look (T : List (List Nat)) (k j : Nat) : Fin 5 := ⟨((T.getD k []).getD j 0) % 5, Nat.mod_lt _ (by decide)⟩

/-- The tables `tblF` and `tblFi` are mutually inverse. -/
theorem tbl_inv1 : ∀ (k : Fin 24) (x : Fin 5), look tblFi k (look tblF k x) = x := by decide

/-- The tables `tblF` and `tblFi` are mutually inverse. -/
theorem tbl_inv2 : ∀ (k : Fin 24) (x : Fin 5), look tblF k (look tblFi k x) = x := by decide

/-- The `k`-th permutation with `0 ↦ 1`. -/
def Q (k : Fin 24) : Perm (Fin 5) :=
  ⟨fun x => look tblF k x, fun x => look tblFi k x, tbl_inv1 k, tbl_inv2 k⟩

/-- **The finite verification.** Each of the 24 permutations with `0 ↦ 1` is odd, or its
commutator with the tabulated 3-cycle `g` is the tabulated 3-cycle. -/
theorem table_check : ∀ k : Fin 24, parity (Q k) = true ∨
    ((look tblG k 0 ≠ look tblG k 1 ∧ look tblG k 1 ≠ look tblG k 2 ∧ look tblG k 0 ≠ look tblG k 2) ∧
     (look tblT k 0 ≠ look tblT k 1 ∧ look tblT k 1 ≠ look tblT k 2 ∧ look tblT k 0 ≠ look tblT k 2) ∧
     ∀ i : Fin 5, (Q k * c3 (look tblG k 0) (look tblG k 1) (look tblG k 2) * (Q k)⁻¹ *
        (c3 (look tblG k 0) (look tblG k 1) (look tblG k 2))⁻¹ : Perm (Fin 5)) i =
        c3 (look tblT k 0) (look tblT k 1) (look tblT k 2) i) := by decide

/-- The table lists every permutation of `Fin 5` with `0 ↦ 1`. -/
theorem table_complete_vals : ∀ v1 v2 v3 v4 : Fin 5, v1 ≠ 1 → v2 ≠ 1 → v3 ≠ 1 → v4 ≠ 1 →
    v1 ≠ v2 → v1 ≠ v3 → v1 ≠ v4 → v2 ≠ v3 → v2 ≠ v4 → v3 ≠ v4 →
    ∃ k : Fin 24, look tblF k 1 = v1 ∧ look tblF k 2 = v2 ∧ look tblF k 3 = v3 ∧
      look tblF k 4 = v4 := by decide

/-- Every element of `Fin 5` is one of `0, …, 4`. -/
theorem fin5_cases : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide

/-- Every permutation of `Fin 5` with `0 ↦ 1` occurs in the table. -/
theorem table_complete (σ : Perm (Fin 5)) (h0 : σ 0 = 1) : ∃ k, σ = Q k := by
  have inj : ∀ {x y : Fin 5}, x ≠ y → σ x ≠ σ y := fun hxy h => hxy (σ.injective h)
  have n1 : ∀ {x : Fin 5}, x ≠ 0 → σ x ≠ 1 := fun hx h => inj hx (h.trans h0.symm)
  obtain ⟨k, h1, h2, h3, h4⟩ := table_complete_vals (σ 1) (σ 2) (σ 3) (σ 4)
    (n1 (by decide)) (n1 (by decide)) (n1 (by decide)) (n1 (by decide))
    (inj (by decide)) (inj (by decide)) (inj (by decide)) (inj (by decide)) (inj (by decide))
    (inj (by decide))
  have h0' : ∀ k : Fin 24, look tblF k 0 = 1 := by decide
  refine ⟨k, ext fun i => ?_⟩
  show σ i = look tblF k i
  rcases fin5_cases i with rfl | rfl | rfl | rfl | rfl
  · exact h0.trans (h0' k).symm
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm

/-! ## The theorem -/

/-- **`A₅` is simple (concrete form).** Let `N` be a subgroup of `S₅` contained in `A₅` and
closed under conjugation by even permutations. Then `N` is trivial or `N = A₅`. -/
theorem A5_normal_trivial_or_top (N : Subgroup (Perm (Fin 5)))
    (hNA : ∀ x, x ∈ N → x ∈ alternating 5)
    (hnorm : ∀ g, g ∈ alternating 5 → ∀ x, x ∈ N → g * x * g⁻¹ ∈ N) :
    (∀ x, x ∈ N → x = 1) ∨ (∀ x, x ∈ alternating 5 → x ∈ N) := by
  by_cases htriv : ∀ x, x ∈ N → x = 1
  · exact Or.inl htriv
  right
  have : ∃ σ, σ ∈ N ∧ σ ≠ 1 := Classical.byContradiction fun h =>
    htriv fun x hx => Classical.byContradiction fun hx1 => h ⟨x, hx, hx1⟩
  obtain ⟨σ, hσN, hσ1⟩ := this
  have : ∃ a, σ a ≠ a := Classical.byContradiction fun h =>
    hσ1 (ext fun x => Classical.byContradiction fun hx => h ⟨x, hx⟩)
  obtain ⟨a, ha⟩ := this
  -- Normalise: conjugate so that `0 ↦ 1`.
  have hthird : ∀ x y : Fin 5, ∃ z, z ≠ x ∧ z ≠ y := by decide
  obtain ⟨c, hca, hcb⟩ := hthird a (σ a)
  obtain ⟨π, hπ, hπa, hπb, _⟩ := exists_even_move3 (Ne.symm ha) (Ne.symm hcb) (Ne.symm hca)
  let σ' := π * σ * π⁻¹
  have hσ'N : σ' ∈ N := hnorm π hπ σ hσN
  have hσ'0 : σ' 0 = 1 := by
    show π (σ (π.invFun 0)) = 1
    rw [← hπa, π.left_inv, hπb]
  obtain ⟨k, hk⟩ := table_complete σ' hσ'0
  have hpar : parity (Q k) = false := by rw [← hk]; exact mem_alternating.1 (hNA _ hσ'N)
  rcases table_check k with hodd | ⟨⟨g1, g2, g3⟩, ⟨t1, t2, t3⟩, hcomm⟩
  · rw [hpar] at hodd; exact absurd hodd (by decide)
  · -- The commutator of `σ'` with a 3-cycle `g` lies in `N` and is a 3-cycle.
    let g := c3 (look tblG k 0) (look tblG k 1) (look tblG k 2)
    have hg : g ∈ alternating 5 := mem_alternating.2 (parity_c3 g1 g2)
    have hmem : Q k * g * (Q k)⁻¹ * g⁻¹ ∈ N := by
      have h1 : g * (Q k)⁻¹ * g⁻¹ ∈ N := hnorm g hg _ (N.inv_mem (hk ▸ hσ'N))
      have := N.mul_mem (hk ▸ hσ'N) h1
      rw [show Q k * g * (Q k)⁻¹ * g⁻¹ = Q k * (g * (Q k)⁻¹ * g⁻¹) by simp only [mul_assoc]]
      exact this
    have heq : Q k * g * (Q k)⁻¹ * g⁻¹ = c3 (look tblT k 0) (look tblT k 1) (look tblT k 2) :=
      ext hcomm
    rw [heq] at hmem
    exact alternating_le_of_c3 N (all_c3_of_one N hnorm t1 t2 t3 hmem)

/-- A group is **simple** if it is non-trivial and its only normal subgroups are the trivial
subgroup and the whole group. -/
def IsSimpleGroup (G : Type) [Group G] : Prop :=
  (∃ x : G, x ≠ 1) ∧ ∀ N : Subgroup G, N.Normal → (∀ x, x ∈ N → x = 1) ∨ (∀ x, x ∈ N)

/-- **`A₅` is simple** (Galois, 1832): the alternating group on five letters has no normal
subgroups other than `1` and itself. -/
theorem A5_simple : IsSimpleGroup (alternating 5) := by
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  have h12 : (1 : Fin 5) ≠ 2 := by decide
  have h02 : (0 : Fin 5) ≠ 2 := by decide
  refine ⟨⟨⟨c3 0 1 2, mem_alternating.2 (parity_c3 h01 h12)⟩, fun h =>
    c3_ne_one h01 h12 h02 (congrArg Subtype.val h)⟩, fun N hN => ?_⟩
  let N' := Subgroup.map (Hom.subtype (alternating 5)) N
  have hNA : ∀ x, x ∈ N' → x ∈ alternating 5 := by
    intro x ⟨x', _, hx'⟩; rw [← hx']; exact x'.2
  have hnorm : ∀ g, g ∈ alternating 5 → ∀ x, x ∈ N' → g * x * g⁻¹ ∈ N' := by
    intro g hg x ⟨x', hx'N, hx'⟩
    exact ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹, hN.conj_mem x' hx'N _, by rw [← hx']; rfl⟩
  rcases A5_normal_trivial_or_top N' hNA hnorm with h | h
  · left; intro x hx; exact Subtype.ext (h x.1 ⟨x, hx, rfl⟩)
  · right; intro x
    obtain ⟨x', hx'N, hx'⟩ := h x.1 x.2
    have : x' = x := Subtype.ext hx'
    rw [← this]; exact hx'N

end Foundations.Algebra
