import Foundations.Combinatorics.Ramsey
import Foundations.Combinatorics.Konig

/-!
# Finite Ramsey from infinite Ramsey, by compactness

The finite Ramsey theorem can be obtained from the infinite one without any
counting, by a **compactness argument** — the same phenomenon as the compactness
theorem of first-order logic (Part III), here in its combinatorial guise, Kőnig's
lemma. Suppose the finite theorem failed for some `s`: for every `N` there would be a
colouring of the pairs of `{0, …, N−1}` without a monochromatic `s`-set. Arrange the
*partial* colourings without monochromatic `s`-sets into a tree (a node of depth `n`
colours the first `n` pairs, in a fixed enumeration of pairs); it is finitely
branching (two colours) and infinite (by the assumption). By Kőnig's lemma it has an
infinite branch: a colouring of *all* pairs of natural numbers without a
monochromatic `s`-set — contradicting the infinite Ramsey theorem.

This proof gives no bound at all on `N` — it is purely existential. The constructive
proof of `Ramsey` gives the bound `R(s, t) ≤ binom(s+t−2, s−1)`. The difference is
significant: for the Paris–Harrington variant (see `Ramsey`), the compactness proof
still works, but no proof in Peano arithmetic exists.

Pairs `x < y` are enumerated by the code `y² + x`.
-/

open Classical

namespace Foundations.Combinatorics

/-- A **monochromatic set** of colour `b`: all pairs `x < y` from `S` have colour `b`. -/
def MonoSet (c : Nat → Nat → Bool) (b : Bool) (S : List Nat) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → c x y = b

/-! ## Coding pairs -/

/-- Codes of pairs below `V` are below `V²`. -/
theorem code_lt {x y V : Nat} (hxy : x < y) (hy : y < V) : y * y + x < V * V := by
  have h := Nat.mul_le_mul (show y + 1 ≤ V by omega) (show y + 1 ≤ V by omega)
  have : (y + 1) * (y + 1) = y * y + y + y + 1 := by rw [Nat.succ_mul, Nat.mul_succ]; omega
  omega

/-- The code `y² + x` (with `x < y`) determines the pair. -/
theorem code_inj {x y x' y' : Nat} (h : x < y) (h' : x' < y') (he : y * y + x = y' * y' + x') :
    y = y' ∧ x = x' := by
  rcases Nat.lt_trichotomy y y' with hy | rfl | hy
  · have := code_lt h hy; omega
  · omega
  · have := code_lt h' hy; omega

/-- The colouring read off a finite list of bits. -/
def colOf (l : List Nat) (x y : Nat) : Bool := l.getD (y * y + x) 0 == 1

/-- Reading a list of the form `[f 0, …, f (n−1)]`. -/
theorem getD_map_range (f : Nat → Nat) {n k : Nat} (h : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Mapping an injective function preserves the absence of duplicates. -/
theorem nodup_map_of_inj {f : Nat → Nat} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List Nat}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_map_of_inj hf h.2⟩
      obtain ⟨b, hb, he⟩ := List.mem_map.1 hm
      exact h.1 (hf _ _ he ▸ hb)

/-! ## The tree of good partial colourings -/

/-- The nodes of the tree for clique size `s`: lists of bits all of whose "complete"
vertex ranges `{0, …, V−1}` (those with `V² ≤ length`) carry no monochromatic
`s`-set. -/
def goodTree (s : Nat) (l : List Nat) : Prop :=
  (∀ a ∈ l, a < 2) ∧ ∀ V, V * V ≤ l.length → ∀ (b : Bool) (S : List Nat), S.Nodup →
    S.length = s → (∀ x ∈ S, x < V) → ¬ MonoSet (colOf l) b S

/-- Colours of pairs inside a complete range are unchanged by extending the list. -/
theorem colOf_append {l m : List Nat} {V x y : Nat} (hV : V * V ≤ l.length) (hxy : x < y)
    (hy : y < V) : colOf (l ++ m) x y = colOf l x y := by
  simp only [colOf, List.getD_eq_getElem?_getD, List.getElem?_append_left
    (show y * y + x < l.length from Nat.lt_of_lt_of_le (code_lt hxy hy) hV)]

/-- The good partial colourings form a tree. -/
theorem goodTree_isTree (s : Nat) : IsTree (goodTree s) := by
  intro l m ⟨hbits, hgood⟩
  refine ⟨fun a ha => hbits a (List.mem_append_left _ ha), fun V hV b S hS hSl hSV hmono => ?_⟩
  refine hgood V (by simp; omega) b S hS hSl hSV fun x hx y hy hxy => ?_
  rw [colOf_append hV hxy (hSV y hy)]; exact hmono x hx y hy hxy

/-- The tree is finitely branching (two colours). -/
theorem goodTree_finBranching (s : Nat) : FinBranching (goodTree s) :=
  fun _ => ⟨2, fun a ha => ha.1 a (by simp)⟩

/-- **Finite Ramsey theorem, by compactness.** For every `s` there is `N` such that every
2-colouring of the pairs of `{0, …, N−1}` has a monochromatic set of size `s`. (Proved
from the infinite Ramsey theorem and Kőnig's lemma.) -/
theorem finite_ramsey_compactness (s : Nat) :
    ∃ N, ∀ c : Nat → Nat → Bool, ∃ (b : Bool) (S : List Nat),
      S.Nodup ∧ S.length = s ∧ (∀ x ∈ S, x < N) ∧ MonoSet c b S := by
  refine Classical.byContradiction fun hno => ?_
  have hbad : ∀ N, ∃ c : Nat → Nat → Bool, ∀ (b : Bool) (S : List Nat), S.Nodup →
      S.length = s → (∀ x ∈ S, x < N) → ¬ MonoSet c b S := by
    intro N
    refine Classical.byContradiction fun h => hno ⟨N, fun c => ?_⟩
    refine Classical.byContradiction fun h' => h ⟨c, fun b S hS hSl hSN hm => h' ⟨b, S, hS, hSl, hSN, hm⟩⟩
  -- the tree is infinite
  have hinf : InfTree (goodTree s) := by
    intro n
    obtain ⟨c, hc⟩ := hbad n
    let bit : Nat → Nat := fun k => if ∃ x y, x < y ∧ y * y + x = k ∧ c x y = true then 1 else 0
    refine ⟨(List.range n).map bit, ⟨fun a ha => ?_, fun V hV b S hS hSl hSV hm => ?_⟩, by simp⟩
    · simp only [List.mem_map] at ha
      obtain ⟨k, -, rfl⟩ := ha
      simp only [bit]; split <;> omega
    · simp only [List.length_map, List.length_range] at hV
      refine hc b S hS hSl (fun x hx => ?_) fun x hx y hy hxy => ?_
      · have := hSV x hx
        have : V ≤ V * V := Nat.le_mul_self V
        omega
      · have hcode := code_lt hxy (hSV y hy)
        have := hm x hx y hy hxy
        simp only [colOf, getD_map_range _ (Nat.lt_of_lt_of_le hcode hV), bit] at this
        split at this
        · next hex =>
            obtain ⟨x', y', hxy', he, hc'⟩ := hex
            obtain ⟨rfl, rfl⟩ := code_inj hxy' hxy he
            rw [hc']; simpa using this
        · next hex =>
            have hcf : c x y = false := by
              cases h : c x y
              · rfl
              · exact absurd ⟨x, y, hxy, rfl, h⟩ hex
            rw [hcf]; simpa using this
  -- an infinite branch is a colouring of all pairs without monochromatic `s`-sets
  obtain ⟨f, hf⟩ := konig (goodTree_isTree s) (goodTree_finBranching s) hinf
  obtain ⟨b, g, hgmono, hgcol⟩ := infinite_ramsey fun x y => f (y * y + x) == 1
  have hT := (hf (g s * g s)).2 (g s) (by simp) b ((List.range s).map g)
  have ginj : ∀ i j, g i = g j → i = j := fun i j h => by
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · have := hgmono i j hij; omega
    · rfl
    · have := hgmono j i hij; omega
  have hmem : ∀ x, x ∈ (List.range s).map g → ∃ i, i < s ∧ g i = x := by
    intro x hx; simp only [List.mem_map, List.mem_range] at hx; exact hx
  refine hT (nodup_map_of_inj ginj List.nodup_range) (by simp)
    (fun x hx => ?_) fun x hx y hy hxy => ?_
  · obtain ⟨i, hi, rfl⟩ := hmem x hx; exact hgmono i s hi
  · obtain ⟨i, hi, rfl⟩ := hmem x hx
    obtain ⟨j, hj, rfl⟩ := hmem y hy
    have hij : i < j := Classical.byContradiction fun h => by
      rcases Nat.lt_or_ge j i with h' | h'
      · have := hgmono j i h'; omega
      · have : i = j := by omega
        subst this; omega
    have hcode := code_lt hxy (hgmono j s hj)
    simp only [colOf, getD_map_range _ hcode]
    exact hgcol i j hij

end Foundations.Combinatorics
