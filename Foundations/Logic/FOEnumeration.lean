import Foundations.Logic.FOProofTheory

/-!
# Enumerating terms and formulas of a countable language

Henkin's proof of completeness goes through the formulas *one by one*, deciding
each in turn. This requires the formulas to be listable in a sequence — i.e. the
language must be **countable**. (Gödel's original 1929 proof, and Henkin's 1949
proof, both assume this; for uncountable languages one needs the axiom of choice in
the form of Zorn's lemma, as shown by Maltsev in 1936.)

A signature is *countable* if its function symbols and its relation symbols can each
be listed by natural-number codes. From such listings we build, exactly as in the
propositional case, cumulative finite lists `termsUpTo k` and `formsUpTo k` that
eventually contain every term and every formula. We also construct a surjection
`ℕ → ℕ × ℕ` (Cantor's diagonal enumeration of pairs), used later to show that the
term model is countable.
-/

namespace Foundations.Logic.FO

/-- **Countable signature.** Codes `0, 1, 2, …` enumerate (possibly with gaps and
repetitions) all function symbols and all relation symbols, together with their
arities. -/
class Signature.Countable (L : Signature) where
  /-- The function symbol with a given code, if any. -/
  funcCode : Nat → Option (Σ n, L.Func n)
  /-- Every function symbol has a code. -/
  funcCode_surj : ∀ n (f : L.Func n), ∃ k, funcCode k = some ⟨n, f⟩
  /-- The relation symbol with a given code, if any. -/
  relCode : Nat → Option (Σ n, L.Rel n)
  /-- Every relation symbol has a code. -/
  relCode_surj : ∀ n (R : L.Rel n), ∃ k, relCode k = some ⟨n, R⟩

/-! ## Tuples -/

/-- All `n`-tuples with entries from the list `l`. -/
def tuples {α : Type} (l : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [fun i => i.elim0]
  | n + 1 => l.flatMap fun a => (tuples l n).map fun f i => Fin.cases a f i

/-- A tuple belongs to `tuples l n` iff all its entries belong to `l`. -/
theorem mem_tuples {α : Type} {l : List α} : ∀ {n : Nat} {f : Fin n → α},
    f ∈ tuples l n ↔ ∀ i, f i ∈ l
  | 0, f => by
      simp only [tuples, List.mem_singleton]
      exact ⟨fun _ i => i.elim0, fun _ => funext fun i => i.elim0⟩
  | n + 1, f => by
      simp only [tuples, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨a, ha, g, hg, rfl⟩ i
        cases i using Fin.cases with
        | zero => simpa using ha
        | succ i => simpa using (mem_tuples.1 hg) i
      · intro h
        refine ⟨f 0, h 0, fun i => f i.succ, mem_tuples.2 fun i => h _, ?_⟩
        funext i; cases i using Fin.cases <;> simp

variable {L : Signature} [Signature.Countable L]

open Signature.Countable

/-! ## Terms -/

/-- The terms obtained by applying the function symbol with a given code to argument
tuples from `prev`. -/
def symbolTerms (prev : List (Term L)) : Option (Σ n, L.Func n) → List (Term L)
  | none => []
  | some p => (tuples prev p.1).map (Term.func p.2)

omit [Signature.Countable L] in
/-- Membership in `symbolTerms` is monotone in the list of available arguments. -/
theorem symbolTerms_mono {l l' : List (Term L)} (h : ∀ t ∈ l, t ∈ l')
    {c : Option (Σ n, L.Func n)} {t : Term L} (ht : t ∈ symbolTerms l c) :
    t ∈ symbolTerms l' c := by
  cases c with
  | none => simp [symbolTerms] at ht
  | some p =>
      simp only [symbolTerms, List.mem_map] at ht ⊢
      obtain ⟨ts, hts, rfl⟩ := ht
      exact ⟨ts, mem_tuples.2 fun i => h _ (mem_tuples.1 hts i), rfl⟩

variable (L) in
/-- The `k`-th finite list of terms: variables `< k - 1`, and function symbols with
codes `< k - 1` applied to terms of the previous list. -/
def termsUpTo : Nat → List (Term L)
  | 0 => []
  | k + 1 => (List.range k).map Term.var ++
      (List.range k).flatMap fun j => symbolTerms (termsUpTo k) (funcCode j)

/-- Membership in the next list of terms, unfolded one level. -/
theorem mem_termsUpTo_succ {t : Term L} {k : Nat} : t ∈ termsUpTo L (k + 1) ↔
    (∃ i, i < k ∧ Term.var i = t) ∨ ∃ j, j < k ∧ t ∈ symbolTerms (termsUpTo L k) (funcCode j) := by
  rw [termsUpTo]
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap]

/-- The lists of terms are cumulative. -/
theorem termsUpTo_succ {t : Term L} : ∀ {k}, t ∈ termsUpTo L k → t ∈ termsUpTo L (k + 1)
  | 0, h => by simp [termsUpTo] at h
  | k + 1, h => by
      rw [mem_termsUpTo_succ] at h ⊢
      rcases h with ⟨i, hi, rfl⟩ | ⟨j, hj, h⟩
      · exact Or.inl ⟨i, by omega, rfl⟩
      · exact Or.inr ⟨j, by omega, symbolTerms_mono (fun _ h => termsUpTo_succ h) h⟩

/-- The lists of terms are cumulative (general form). -/
theorem termsUpTo_mono {t : Term L} {k k' : Nat} (hk : k ≤ k') (h : t ∈ termsUpTo L k) :
    t ∈ termsUpTo L k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact termsUpTo_succ ih

/-- **Every term is eventually listed.** -/
theorem exists_mem_termsUpTo : ∀ t : Term L, ∃ k, t ∈ termsUpTo L k
  | .var i => ⟨i + 2, mem_termsUpTo_succ.2 (Or.inl ⟨i, by omega, rfl⟩)⟩
  | .func (n := n) f ts => by
      obtain ⟨K, hK⟩ := fin_eventually (fun i k => ts i ∈ termsUpTo L k) (fun i => by
        obtain ⟨k, hk⟩ := exists_mem_termsUpTo (ts i)
        exact ⟨k, fun x hx => termsUpTo_mono hx hk⟩)
      obtain ⟨j, hj⟩ := funcCode_surj n f
      refine ⟨max K (j + 1) + 1, mem_termsUpTo_succ.2 (Or.inr ⟨j, by omega, ?_⟩)⟩
      rw [hj]
      simp only [symbolTerms, List.mem_map]
      exact ⟨ts, mem_tuples.2 fun i => hK _ (by omega) i, rfl⟩

/-! ## Formulas -/

/-- The atomic formulas obtained from the relation symbol with a given code and
argument tuples from `prev`. -/
def symbolAtoms (prev : List (Term L)) : Option (Σ n, L.Rel n) → List (Formula L)
  | none => []
  | some p => (tuples prev p.1).map (Formula.rel p.2)

omit [Signature.Countable L] in
/-- Membership in `symbolAtoms` is monotone in the list of available arguments. -/
theorem symbolAtoms_mono {l l' : List (Term L)} (h : ∀ t ∈ l, t ∈ l')
    {c : Option (Σ n, L.Rel n)} {φ : Formula L} (hφ : φ ∈ symbolAtoms l c) :
    φ ∈ symbolAtoms l' c := by
  cases c with
  | none => simp [symbolAtoms] at hφ
  | some p =>
      simp only [symbolAtoms, List.mem_map] at hφ ⊢
      obtain ⟨ts, hts, rfl⟩ := hφ
      exact ⟨ts, mem_tuples.2 fun i => h _ (mem_tuples.1 hts i), rfl⟩

variable (L) in
/-- The `k`-th finite list of formulas: falsum, equations and atomic formulas over
the `k`-th terms, and one more layer of connectives and quantifiers over the
previous list. -/
def formsUpTo : Nat → List (Formula L)
  | 0 => []
  | k + 1 => Formula.bot ::
      (((termsUpTo L k).flatMap fun s => (termsUpTo L k).map (Formula.eq s)) ++
      ((List.range k).flatMap fun j => symbolAtoms (termsUpTo L k) (relCode j)) ++
      ((formsUpTo k).flatMap fun a => (formsUpTo k).flatMap fun b =>
        [Formula.imp a b, Formula.conj a b, Formula.disj a b]) ++
      ((formsUpTo k).flatMap fun a => [Formula.all a, Formula.ex a]))

/-- Membership in the next list of formulas, unfolded one level. -/
theorem mem_formsUpTo_succ {φ : Formula L} {k : Nat} : φ ∈ formsUpTo L (k + 1) ↔
    φ = .bot ∨
    (∃ s ∈ termsUpTo L k, ∃ t ∈ termsUpTo L k, Formula.eq s t = φ) ∨
    (∃ j, j < k ∧ φ ∈ symbolAtoms (termsUpTo L k) (relCode j)) ∨
    (∃ a ∈ formsUpTo L k, ∃ b ∈ formsUpTo L k,
      φ ∈ [Formula.imp a b, Formula.conj a b, Formula.disj a b]) ∨
    (∃ a ∈ formsUpTo L k, φ ∈ [Formula.all a, Formula.ex a]) := by
  rw [formsUpTo]
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    or_assoc]

/-- The lists of formulas are cumulative. -/
theorem formsUpTo_succ {φ : Formula L} : ∀ {k}, φ ∈ formsUpTo L k → φ ∈ formsUpTo L (k + 1)
  | 0, h => by simp [formsUpTo] at h
  | k + 1, h => by
      rw [mem_formsUpTo_succ] at h ⊢
      rcases h with h | ⟨s, hs, t, ht, h⟩ | ⟨j, hj, h⟩ | ⟨a, ha, b, hb, h⟩ | ⟨a, ha, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨s, termsUpTo_succ hs, t, termsUpTo_succ ht, h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨j, by omega,
          symbolAtoms_mono (fun _ h => termsUpTo_succ h) h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, formsUpTo_succ ha, b, formsUpTo_succ hb, h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, formsUpTo_succ ha, h⟩)))

/-- The lists of formulas are cumulative (general form). -/
theorem formsUpTo_mono {φ : Formula L} {k k' : Nat} (hk : k ≤ k') (h : φ ∈ formsUpTo L k) :
    φ ∈ formsUpTo L k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact formsUpTo_succ ih

/-- **Every formula is eventually listed.** -/
theorem exists_mem_formsUpTo : ∀ φ : Formula L, ∃ k, φ ∈ formsUpTo L k
  | .bot => ⟨1, mem_formsUpTo_succ.2 (Or.inl rfl)⟩
  | .eq s t => by
      obtain ⟨k₁, h₁⟩ := exists_mem_termsUpTo s
      obtain ⟨k₂, h₂⟩ := exists_mem_termsUpTo t
      exact ⟨max k₁ k₂ + 1, mem_formsUpTo_succ.2 (Or.inr (Or.inl
        ⟨s, termsUpTo_mono (by omega) h₁, t, termsUpTo_mono (by omega) h₂, rfl⟩))⟩
  | .rel (n := n) R ts => by
      obtain ⟨K, hK⟩ := fin_eventually (fun i k => ts i ∈ termsUpTo L k) (fun i => by
        obtain ⟨k, hk⟩ := exists_mem_termsUpTo (ts i)
        exact ⟨k, fun x hx => termsUpTo_mono hx hk⟩)
      obtain ⟨j, hj⟩ := relCode_surj n R
      refine ⟨max K (j + 1) + 1, mem_formsUpTo_succ.2 (Or.inr (Or.inr (Or.inl
        ⟨j, by omega, ?_⟩)))⟩
      rw [hj]
      simp only [symbolAtoms, List.mem_map]
      exact ⟨ts, mem_tuples.2 fun i => hK _ (by omega) i, rfl⟩
  | .imp a b | .conj a b | .disj a b => by
      obtain ⟨k₁, h₁⟩ := exists_mem_formsUpTo a
      obtain ⟨k₂, h₂⟩ := exists_mem_formsUpTo b
      exact ⟨max k₁ k₂ + 1, mem_formsUpTo_succ.2 (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a, formsUpTo_mono (by omega) h₁, b, formsUpTo_mono (by omega) h₂, by simp⟩))))⟩
  | .all a | .ex a => by
      obtain ⟨k, h⟩ := exists_mem_formsUpTo a
      exact ⟨k + 1, mem_formsUpTo_succ.2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, h, by simp⟩))))⟩

/-! ## Enumerating pairs -/

/-- Triangular numbers: `tri s = 0 + 1 + ⋯ + s`. -/
def tri : Nat → Nat
  | 0 => 0
  | s + 1 => tri s + s + 1

/-- Cantor's enumeration of pairs of natural numbers, diagonal by diagonal:
`(0,0), (0,1), (1,0), (0,2), (1,1), (2,0), …`. -/
def pairAt : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
      let p := pairAt n
      if p.2 = 0 then (0, p.1 + 1) else (p.1 + 1, p.2 - 1)

/-- Position `tri s + a` of the enumeration is the pair `(a, s - a)`. -/
theorem pairAt_tri : ∀ s a, a ≤ s → pairAt (tri s + a) = (a, s - a) := by
  intro s
  induction s with
  | zero => intro a ha; have : a = 0 := by omega
            subst this; rfl
  | succ s ih =>
      intro a ha
      induction a with
      | zero =>
          show pairAt (tri s + s + 1) = (0, s + 1)
          simp only [pairAt, ih s (Nat.le_refl s)]; simp
      | succ a iha =>
          rw [show tri (s + 1) + (a + 1) = (tri (s + 1) + a) + 1 by omega]
          simp only [pairAt, iha (by omega)]
          have hne : ¬ (s + 1 - a = 0) := by omega
          simp only [hne, ite_false]
          rw [Nat.sub_sub]

/-- **Cantor's pairing.** Every pair of natural numbers occurs in the enumeration. -/
theorem pairAt_surj (a b : Nat) : ∃ n, pairAt n = (a, b) :=
  ⟨tri (a + b) + a, by rw [pairAt_tri _ _ (by omega)]; congr 1; omega⟩

end Foundations.Logic.FO
