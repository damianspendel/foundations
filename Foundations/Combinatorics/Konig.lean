/-!
# Kőnig's lemma

**Kőnig's lemma** (Dénes Kőnig, 1927): *every infinite, finitely branching tree has an
infinite branch.* If a tree has nodes at every depth but each node has only finitely
many children, then one can walk from the root forever. The proof: call a node
*good* if the subtree above it is still infinite. The root is good; and a good node
has finitely many children, so not all of them can be bad (a finite union of finite
subtrees is finite) — some child is good. Walking from good node to good child gives
the branch.

*A combinatorial compactness theorem.* Kőnig's lemma is the combinatorial core of the
compactness phenomena of Part III. Applied to the tree of partial truth assignments
satisfying more and more of a countable set of propositional formulas, it gives the
**compactness theorem of propositional logic** for countable languages; conversely
compactness implies Kőnig's lemma. In reverse mathematics, Kőnig's lemma for binary
trees is the system WKL₀ and for finitely branching trees it is equivalent to
arithmetical comprehension (ACA₀).

*Non-constructive and choice.* The proof is not constructive: deciding whether a node
is good requires knowing a property of infinitely many nodes, so even for a
computable tree there may be no computable branch (Kleene). For trees whose labels
are natural numbers, as here, one can always choose the *least* good child, so no
choice beyond excluded middle is needed. For trees whose nodes have arbitrary finite
sets of children, however, Kőnig's lemma requires a weak form of the axiom of
choice — over ZF it is equivalent to countable choice for families of finite sets,
and is not a theorem of ZF alone. Our proof uses `Classical.choose`.

*Representation.* A tree is a set `T` of finite sequences of natural numbers (the
nodes; `l` is the node reached by the path `l`) closed under initial segments.
**Finitely branching**: the children `l ++ [a]` of each node have bounded labels `a`.
**Infinite**: there are nodes at every depth (for finitely branching trees this is
equivalent to having infinitely many nodes).
-/

namespace Foundations.Combinatorics

/-- A **tree**: a set of finite sequences closed under initial segments. -/
def IsTree (T : List Nat → Prop) : Prop := ∀ l m, T (l ++ m) → T l

/-- A tree is **finitely branching** if every node has only finitely many children. -/
def FinBranching (T : List Nat → Prop) : Prop := ∀ l, ∃ B, ∀ a, T (l ++ [a]) → a < B

/-- A tree is **infinite**: it has nodes at every depth. -/
def InfTree (T : List Nat → Prop) : Prop := ∀ n, ∃ l, T l ∧ l.length = n

/-- An **infinite branch**: a sequence `f` all of whose initial segments are nodes. -/
def IsBranch (T : List Nat → Prop) (f : Nat → Nat) : Prop := ∀ n, T ((List.range n).map f)

section
variable {T : List Nat → Prop}

/-- A node is **good** if it has extensions of every length. -/
def Good (T : List Nat → Prop) (l : List Nat) : Prop := ∀ n, ∃ m, T (l ++ m) ∧ m.length = n

/-- Good nodes are nodes. -/
theorem Good.mem {l : List Nat} (h : Good T l) : T l := by
  obtain ⟨m, hm, hl⟩ := h 0
  rw [List.length_eq_zero_iff] at hl
  subst hl; simpa using hm

/-- In a tree, an extension of length `n` gives extensions of every smaller length. -/
theorem ext_shorter (hT : IsTree T) {l m : List Nat} (hm : T (l ++ m)) {k : Nat} (hk : k ≤ m.length) :
    ∃ m', T (l ++ m') ∧ m'.length = k := by
  refine ⟨m.take k, ?_, by simp; omega⟩
  have : l ++ m = (l ++ m.take k) ++ m.drop k := by simp
  rw [this] at hm
  exact hT _ _ hm

/-- **The key step**: a good node of a finitely branching tree has a good child. -/
theorem good_child (hT : IsTree T) (hfb : FinBranching T) {l : List Nat} (hl : Good T l) :
    ∃ a, Good T (l ++ [a]) := by
  refine Classical.byContradiction fun hno => ?_
  obtain ⟨B, hB⟩ := hfb l
  -- every child `a < B` has a depth beyond which it has no extensions
  have hbad : ∀ a, ∃ n, ¬ ∃ m, T (l ++ [a] ++ m) ∧ m.length = n := by
    intro a
    refine Classical.byContradiction fun h => hno ⟨a, fun n => ?_⟩
    exact Classical.byContradiction fun h' => h ⟨n, h'⟩
  -- a common depth for all children `a < B`
  have hcommon : ∀ k, ∃ N, ∀ a, a < k → ∀ m, T (l ++ [a] ++ m) → m.length < N := by
    intro k
    induction k with
    | zero => exact ⟨0, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨N₁, hN₁⟩ := ih
      obtain ⟨n, hn⟩ := hbad k
      refine ⟨max N₁ n, fun a ha m hm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · have := hN₁ a ha m hm; omega
      · refine Classical.byContradiction fun hlt => hn ?_
        exact ext_shorter hT hm (by omega)
  obtain ⟨N, hN⟩ := hcommon B
  obtain ⟨m, hm, hml⟩ := hl (N + 1)
  match m, hml with
  | a :: m', hml =>
    have hchild : T (l ++ [a]) := hT _ m' (by simpa using hm)
    have := hN a (hB a hchild) m' (by simpa using hm)
    simp at hml; omega

/-- **Kőnig's lemma.** Every infinite, finitely branching tree has an infinite branch. -/
theorem konig (hT : IsTree T) (hfb : FinBranching T) (hinf : InfTree T) :
    ∃ f : Nat → Nat, IsBranch T f := by
  -- the root is good
  have hroot : Good T [] := fun n => by
    obtain ⟨l, hl, hlen⟩ := hinf n; exact ⟨l, by simpa using hl, hlen⟩
  -- walk from good node to good child
  let G := {l : List Nat // Good T l}
  let step : G → G := fun g =>
    ⟨g.1 ++ [Classical.choose (good_child hT hfb g.2)],
      Classical.choose_spec (good_child hT hfb g.2)⟩
  let walk : Nat → G := fun n => Nat.rec ⟨[], hroot⟩ (fun _ g => step g) n
  let f : Nat → Nat := fun n => Classical.choose (good_child hT hfb (walk n).2)
  have hwalk : ∀ n, (walk n).1 = (List.range n).map f := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        show (walk n).1 ++ [f n] = _
        rw [ih, List.range_succ, List.map_append]; rfl
  exact ⟨f, fun n => hwalk n ▸ (walk n).2.mem⟩

end

end Foundations.Combinatorics
