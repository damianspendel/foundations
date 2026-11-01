import Foundations.Combinatorics.Pigeonhole

/-!
# Ramsey's theorem

*Complete disorder is impossible.* Frank Ramsey (1930), in a paper on the decision
problem for logic, proved that in every 2-colouring of the pairs of a sufficiently
large set there is a large **monochromatic** subset — all of whose pairs have the same
colour. In the language of parties: among any six people there are three mutual
acquaintances or three mutual strangers, and six is the least number with this
property (`R(3,3) = 6`).

We prove:

* the **finite Ramsey theorem** for graphs: for all `s, t` there is `R(s, t)` such
  that every red/blue colouring of the edges of a complete graph on `R(s, t)` vertices
  contains a red `s`-clique or a blue `t`-clique, via the Erdős–Szekeres recursion
  `R(s, t) ≤ R(s − 1, t) + R(s, t − 1)`: pick a vertex `v`; among the others, either at
  least `R(s − 1, t)` are joined to `v` in red, or at least `R(s, t − 1)` in blue;
* **`R(3, 3) = 6`**: the upper bound by the recursion, the lower bound by the
  pentagon colouring of `K₅` (edges of the 5-cycle red, diagonals blue), which has no
  monochromatic triangle — checked by `decide`;
* the **infinite Ramsey theorem**: every 2-colouring of the pairs of natural numbers
  has an infinite monochromatic set. The proof chooses a vertex `x₀`, keeps the
  infinitely many vertices joined to `x₀` in the "majority" colour `b₀`, chooses `x₁`
  among them, and so on; then the colours `bₖ` repeat infinitely often (infinite
  pigeonhole), and the corresponding `xₖ` form the monochromatic set.

*Paris–Harrington.* A seemingly innocent strengthening of the finite Ramsey theorem —
requiring the homogeneous set `H` to be *relatively large*, `|H| ≥ min H` — is still
true (it follows from the infinite Ramsey theorem by compactness), but Paris and
Harrington (1977) showed that it is **not provable in Peano arithmetic**: like
Goodstein's theorem (Part III), it was among the first natural mathematical
statements shown independent of PA. This is stated informally only.

Vertices are natural numbers; a finite vertex set is a duplicate-free list; a
colouring is a symmetric function `c : ℕ → ℕ → Bool` (`true` = red).
-/

namespace Foundations.Combinatorics

/-! ## List lemmas -/

/-- A list splits into the elements satisfying a test and those failing it. -/
theorem length_filter_add_not {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter fun x => !p x).length = l.length
  | [] => rfl
  | x :: l => by
      have := length_filter_add_not p l
      cases h : p x <;> simp [h] <;> omega

/-- Filtering preserves the absence of duplicates. -/
theorem nodup_filter {α : Type} (p : α → Bool) : ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.filter_cons]
      split
      · exact List.nodup_cons.2 ⟨fun hx => h.1 ((List.mem_filter.1 hx).1), nodup_filter p h.2⟩
      · exact nodup_filter p h.2

/-! ## The finite Ramsey theorem -/

/-- A set `S` (a list) is a **clique of colour `b`** for the colouring `c`: all pairs of
distinct elements have colour `b`. -/
def Clique (c : Nat → Nat → Bool) (b : Bool) (S : List Nat) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y = b

/-- `V` contains a clique of colour `b` with `k` vertices. -/
def HasClique (c : Nat → Nat → Bool) (b : Bool) (k : Nat) (V : List Nat) : Prop :=
  ∃ S : List Nat, S ⊆ V ∧ S.Nodup ∧ S.length = k ∧ Clique c b S

/-- **The Ramsey property** `N → (s, t)`: every symmetric 2-colouring of the pairs of
any set of at least `N` vertices has a red `s`-clique or a blue `t`-clique. -/
def IsRamsey (s t N : Nat) : Prop :=
  ∀ c : Nat → Nat → Bool, (∀ x y, c x y = c y x) → ∀ V : List Nat, V.Nodup → N ≤ V.length →
    HasClique c true s V ∨ HasClique c false t V

/-- The Ramsey property is upward closed in `N`. -/
theorem IsRamsey.mono {s t N N' : Nat} (h : IsRamsey s t N) (hN : N ≤ N') : IsRamsey s t N' :=
  fun c hc V hV hl => h c hc V hV (by omega)

/-- The empty clique. -/
theorem hasClique_zero (c : Nat → Nat → Bool) (b : Bool) (V : List Nat) : HasClique c b 0 V :=
  ⟨[], List.nil_subset _, List.nodup_nil, rfl, fun x hx => by simp at hx⟩

/-- A single vertex is a clique of either colour. -/
theorem hasClique_one (c : Nat → Nat → Bool) (b : Bool) {V : List Nat} (h : 1 ≤ V.length) :
    HasClique c b 1 V := by
  obtain ⟨v, W, rfl⟩ : ∃ v W, V = v :: W := by
    cases V with
    | nil => simp at h
    | cons v W => exact ⟨v, W, rfl⟩
  refine ⟨[v], by simp, by simp, rfl, fun x hx y hy hxy => ?_⟩
  simp at hx hy; subst hx hy; exact absurd rfl hxy

/-- `R(0, t) = 0`. -/
theorem isRamsey_zero_left (t : Nat) : IsRamsey 0 t 0 :=
  fun c _ V _ _ => Or.inl (hasClique_zero c true V)

/-- `R(s, 0) = 0`. -/
theorem isRamsey_zero_right (s : Nat) : IsRamsey s 0 0 :=
  fun c _ V _ _ => Or.inr (hasClique_zero c false V)

/-- `R(1, t) ≤ 1`. -/
theorem isRamsey_one_left (t : Nat) : IsRamsey 1 t 1 :=
  fun c _ _ _ h => Or.inl (hasClique_one c true h)

/-- `R(s, 1) ≤ 1`. -/
theorem isRamsey_one_right (s : Nat) : IsRamsey s 1 1 :=
  fun c _ _ _ h => Or.inr (hasClique_one c false h)

/-- Adding a vertex `v` joined in colour `b` to all of a clique of colour `b`. -/
theorem clique_cons {c : Nat → Nat → Bool} (hc : ∀ x y, c x y = c y x) {b : Bool} {v : Nat}
    {S : List Nat} (hS : Clique c b S) (hv : ∀ y ∈ S, c v y = b) : Clique c b (v :: S) := by
  intro x hx y hy hxy
  simp only [List.mem_cons] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact absurd rfl hxy
  · exact hv y hy
  · rw [hc]; exact hv x hx
  · exact hS x hx y hy hxy

/-- **The Erdős–Szekeres recursion** `R(s+1, t+1) ≤ R(s, t+1) + R(s+1, t)`. -/
theorem ramsey_step {s t N₁ N₂ : Nat} (h₁ : IsRamsey s (t + 1) N₁) (h₂ : IsRamsey (s + 1) t N₂)
    (hpos : 1 ≤ N₁ + N₂) : IsRamsey (s + 1) (t + 1) (N₁ + N₂) := by
  intro c hc V hV hl
  obtain ⟨v, W, rfl⟩ : ∃ v W, V = v :: W := by
    cases V with
    | nil => simp at hl; omega
    | cons v W => exact ⟨v, W, rfl⟩
  rw [List.nodup_cons] at hV
  obtain ⟨hvW, hW⟩ := hV
  let Red := W.filter fun w => c v w
  let Blue := W.filter fun w => !c v w
  have hsplit : Red.length + Blue.length = W.length := length_filter_add_not _ W
  have hl' : N₁ + N₂ ≤ W.length + 1 := by simpa using hl
  have hRedV : Red ⊆ v :: W := fun x hx => List.mem_cons_of_mem _ ((List.mem_filter.1 hx).1)
  have hBlueV : Blue ⊆ v :: W := fun x hx => List.mem_cons_of_mem _ ((List.mem_filter.1 hx).1)
  by_cases hR : N₁ ≤ Red.length
  · rcases h₁ c hc Red (nodup_filter _ hW) hR with ⟨S, hSR, hSn, hSl, hScl⟩ | ⟨S, hSR, hSn, hSl, hScl⟩
    · refine Or.inl ⟨v :: S, ?_, ?_, by simp [hSl], clique_cons hc hScl fun y hy => ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact hRedV (hSR hx)
      · exact List.nodup_cons.2 ⟨fun hv => hvW ((List.mem_filter.1 (hSR hv)).1), hSn⟩
      · have := hSR hy
        simp only [Red, List.mem_filter] at this
        exact this.2
    · exact Or.inr ⟨S, fun x hx => hRedV (hSR hx), hSn, hSl, hScl⟩
  · have hB : N₂ ≤ Blue.length := by omega
    rcases h₂ c hc Blue (nodup_filter _ hW) hB with ⟨S, hSB, hSn, hSl, hScl⟩ | ⟨S, hSB, hSn, hSl, hScl⟩
    · exact Or.inl ⟨S, fun x hx => hBlueV (hSB hx), hSn, hSl, hScl⟩
    · refine Or.inr ⟨v :: S, ?_, ?_, by simp [hSl], clique_cons hc hScl fun y hy => ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact hBlueV (hSB hx)
      · exact List.nodup_cons.2 ⟨fun hv => hvW ((List.mem_filter.1 (hSB hv)).1), hSn⟩
      · have := hSB hy
        simp only [Blue, List.mem_filter, Bool.not_eq_true'] at this
        exact this.2

/-- The Ramsey bounds given by the recursion: `ramsey s t` with `ramsey 1 t = ramsey s 1 = 1`
and `ramsey (s+1) (t+1) = ramsey s (t+1) + ramsey (s+1) t` (for `s, t ≥ 1`). -/
def ramsey : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | 1, _ + 1 => 1
  | _ + 2, 1 => 1
  | s + 2, t + 2 => ramsey (s + 1) (t + 2) + ramsey (s + 2) (t + 1)

/-- The recursion bounds are positive for positive clique sizes. -/
theorem ramsey_pos : ∀ s t, 1 ≤ ramsey (s + 1) (t + 1)
  | 0, _ => by simp [ramsey]
  | _ + 1, 0 => by simp [ramsey]
  | s + 1, t + 1 => by
      have : 1 ≤ ramsey (s + 1) (t + 2) := ramsey_pos s (t + 1); rw [ramsey]; omega

/-- **The finite Ramsey theorem.** For all `s, t`, every symmetric 2-colouring of the
pairs of a set of `ramsey s t` vertices contains a red `s`-clique or a blue
`t`-clique. -/
theorem ramsey_theorem : ∀ s t, IsRamsey s t (ramsey s t)
  | 0, t => by rw [ramsey]; exact isRamsey_zero_left t
  | _ + 1, 0 => by rw [ramsey]; exact isRamsey_zero_right _
  | 1, t + 1 => by rw [ramsey]; exact isRamsey_one_left (t + 1)
  | s + 2, 1 => by rw [ramsey]; exact isRamsey_one_right (s + 2)
  | s + 2, t + 2 => by
      rw [ramsey]
      exact ramsey_step (ramsey_theorem (s + 1) (t + 2)) (ramsey_theorem (s + 2) (t + 1))
        (by have : 1 ≤ ramsey (s + 1) (t + 2) := ramsey_pos s (t + 1); omega)

/-! ## `R(3, 3) = 6` -/

/-- Upper bound: `6 → (3, 3)`. -/
theorem isRamsey_three_three : IsRamsey 3 3 6 := by
  have h : ramsey 3 3 = 6 := by simp [ramsey]
  exact h ▸ ramsey_theorem 3 3

/-- The pentagon colouring: `x, y` are red iff they are neighbours on the 5-cycle
(`x − y ≡ ±1 mod 5`). -/
def pentagon (x y : Nat) : Bool :=
  ((x % 5 + 5 - y % 5) % 5 == 1) || ((y % 5 + 5 - x % 5) % 5 == 1)

/-- The pentagon colouring is symmetric. -/
theorem pentagon_symm (x y : Nat) : pentagon x y = pentagon y x := by
  simp only [pentagon, Bool.or_comm]

/-- The pentagon colouring of `K₅` has no monochromatic triangle (exhaustive check by
`decide`). -/
theorem pentagon_no_triangle' : ∀ x y z : Fin 5, x.val ≠ y.val → x.val ≠ z.val → y.val ≠ z.val →
    ¬ (pentagon x y = true ∧ pentagon x z = true ∧ pentagon y z = true) ∧
      ¬ (pentagon x y = false ∧ pentagon x z = false ∧ pentagon y z = false) := by decide

/-- The pentagon colouring of `K₅` has no monochromatic triangle. -/
theorem pentagon_no_triangle : ∀ x, x < 5 → ∀ y, y < 5 → ∀ z, z < 5 → x ≠ y → x ≠ z → y ≠ z →
    ¬ (pentagon x y = true ∧ pentagon x z = true ∧ pentagon y z = true) ∧
      ¬ (pentagon x y = false ∧ pentagon x z = false ∧ pentagon y z = false) :=
  fun x hx y hy z hz => pentagon_no_triangle' ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩

/-- Lower bound: `5 ↛ (3, 3)`. -/
theorem not_isRamsey_three_three_five : ¬ IsRamsey 3 3 5 := by
  intro h
  have key : ∀ b, ¬ HasClique pentagon b 3 [0, 1, 2, 3, 4] := by
    rintro b ⟨S, hSV, hSn, hSl, hScl⟩
    match S, hSl with
    | [x, y, z], _ =>
      have hx : x < 5 := by have := hSV (by simp : x ∈ [x, y, z]); simp at this; omega
      have hy : y < 5 := by have := hSV (by simp : y ∈ [x, y, z]); simp at this; omega
      have hz : z < 5 := by have := hSV (by simp : z ∈ [x, y, z]); simp at this; omega
      simp only [List.nodup_cons, List.mem_cons, not_or] at hSn
      obtain ⟨⟨hxy, hxz, -⟩, ⟨hyz, -⟩, -⟩ := hSn
      have hp := pentagon_no_triangle x hx y hy z hz hxy hxz hyz
      cases b
      · exact hp.2 ⟨hScl x (by simp) y (by simp) hxy, hScl x (by simp) z (by simp) hxz,
          hScl y (by simp) z (by simp) hyz⟩
      · exact hp.1 ⟨hScl x (by simp) y (by simp) hxy, hScl x (by simp) z (by simp) hxz,
          hScl y (by simp) z (by simp) hyz⟩
  rcases h pentagon pentagon_symm [0, 1, 2, 3, 4] (by decide) (by decide) with h | h
  · exact key true h
  · exact key false h

/-- **`R(3, 3) = 6`**: six vertices force a monochromatic triangle, five do not; hence
`6` is the least `N` with `N → (3, 3)`. -/
theorem ramsey_three_three : IsRamsey 3 3 6 ∧ ∀ N, N ≤ 5 → ¬ IsRamsey 3 3 N :=
  ⟨isRamsey_three_three, fun _ hN h => not_isRamsey_three_three_five (h.mono hN)⟩

/-! ## The infinite Ramsey theorem -/

/-- If `A` is infinite, then for any vertex `x` and colouring of the vertices, the
elements of `A` above `x` of one of the two colours form an infinite set. -/
theorem infOften_split {A : Nat → Prop} (hA : InfOften A) (x : Nat) (col : Nat → Bool) :
    InfOften (fun y => A y ∧ x < y ∧ col y = true) ∨
      InfOften (fun y => A y ∧ x < y ∧ col y = false) := by
  refine Classical.byContradiction fun hno => ?_
  have bound : ∀ b : Bool, ¬ InfOften (fun y => A y ∧ x < y ∧ col y = b) →
      ∃ N, ∀ y, N ≤ y → ¬ (A y ∧ x < y ∧ col y = b) := fun b hb =>
    Classical.byContradiction fun hc => hb fun N =>
      Classical.byContradiction fun hc' => hc ⟨N, fun y hy he => hc' ⟨y, hy, he⟩⟩
  obtain ⟨N₁, h₁⟩ := bound true fun h => hno (Or.inl h)
  obtain ⟨N₂, h₂⟩ := bound false fun h => hno (Or.inr h)
  obtain ⟨y, hy, hAy⟩ := hA (max (max N₁ N₂) (x + 1))
  cases hc : col y
  · exact h₂ y (by omega) ⟨hAy, by omega, hc⟩
  · exact h₁ y (by omega) ⟨hAy, by omega, hc⟩

section InfiniteRamsey

variable (c : Nat → Nat → Bool)

/-- An infinite set of vertices. -/
abbrev InfSet : Type := {A : Nat → Prop // InfOften A}

/-- An element chosen from an infinite set. -/
noncomputable def pick (A : InfSet) : Nat := Classical.choose (A.2 0)

/-- The chosen element belongs to the set. -/
theorem pick_mem (A : InfSet) : A.1 (pick A) := (Classical.choose_spec (A.2 0)).2

/-- The colour in which the chosen element is joined to infinitely many later elements. -/
noncomputable def majority (A : InfSet) : Bool :=
  open Classical in
  if InfOften (fun y => A.1 y ∧ pick A < y ∧ c (pick A) y = true) then true else false

/-- The elements of `A` above `pick A` joined to it in the majority colour. -/
def nextSet (A : InfSet) : Nat → Prop := fun y => A.1 y ∧ pick A < y ∧ c (pick A) y = majority c A

/-- The next set is infinite. -/
theorem nextSet_inf (A : InfSet) : InfOften (nextSet c A) := by
  unfold nextSet majority
  split
  · assumption
  · next h =>
      rcases infOften_split A.2 (pick A) (c (pick A)) with h' | h'
      · exact absurd h' h
      · exact h'

/-- The sequence of nested infinite sets. -/
noncomputable def chain : Nat → InfSet
  | 0 => ⟨fun _ => True, fun N => ⟨N, Nat.le_refl _, trivial⟩⟩
  | k + 1 => ⟨nextSet c (chain k), nextSet_inf c (chain k)⟩

/-- The sets are nested. -/
theorem chain_mono {k l : Nat} (h : k ≤ l) {y : Nat} (hy : (chain c l).1 y) : (chain c k).1 y := by
  induction h with
  | refl => exact hy
  | step _ ih => exact ih hy.1

/-- The chosen vertices: each later vertex is above and joined in colour `majority`
to each earlier one. -/
theorem chain_prop {k l : Nat} (h : k < l) :
    pick (chain c k) < pick (chain c l) ∧
      c (pick (chain c k)) (pick (chain c l)) = majority c (chain c k) := by
  have := chain_mono c h (pick_mem (chain c l))
  exact ⟨this.2.1, this.2.2⟩

/-- **The infinite Ramsey theorem** (Ramsey 1930). For every 2-colouring `c` of the
pairs of natural numbers there is an infinite monochromatic set: a strictly increasing
sequence `f` and a colour `b` with `c (f i) (f j) = b` for all `i < j`. -/
theorem infinite_ramsey : ∃ (b : Bool) (f : Nat → Nat), (∀ i j, i < j → f i < f j) ∧
    ∀ i j, i < j → c (f i) (f j) = b := by
  obtain ⟨b, hb⟩ := infinite_pigeonhole_bool fun k => majority c (chain c k)
  obtain ⟨g, hg, hmono⟩ := hb.enum
  refine ⟨b, fun i => pick (chain c (g i)), fun i j hij => (chain_prop c (hmono i j hij)).1,
    fun i j hij => ?_⟩
  rw [(chain_prop c (hmono i j hij)).2]; exact hg i

end InfiniteRamsey

end Foundations.Combinatorics
