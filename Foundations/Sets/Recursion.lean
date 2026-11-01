import Foundations.Sets.Omega
import Foundations.Sets.Pairs

/-!
# Dedekind's recursion theorem

In *Was sind und was sollen die Zahlen?* (1888) Dedekind faced a question that
looks almost too innocent to ask: what entitles us to *define* a function on the
natural numbers by recursion — "`F(0) = a`, and `F(n + 1) = g(F(n))`"? Such a
clause only says how to get from one value to the next; that it determines a
single, completed function is a theorem, not a triviality. Dedekind proved it,
and this file reproduces his proof inside our model of ZF.

First we say what a *function* is, set-theoretically: a set `F` of Kuratowski
pairs inside a cartesian product `X × A` containing, for every `x ∈ X`, exactly
one pair `⟪x, y⟫`. We write `app F x` for that unique `y`.

The proof of the recursion theorem is Dedekind's own. Call a set `R` *closed*
if it contains `⟪∅, a⟫` and, together with any `⟪n, y⟫` with `n ∈ ω`, also
contains `⟪succ n, g y⟫`. Let `F` be the set of pairs in `ω × A` lying in *every*
closed set — the least closed relation. Then `F` is closed, and induction on `ω`
shows that it is a function: if `F` contained a second, "rogue" pair above some
`n`, removing it would leave a smaller closed set, contradicting minimality.
Uniqueness is another induction. Note that the proof uses only set-theoretic
means — no appeal to Lean's built-in natural numbers.
-/

namespace Foundations.Sets

namespace ZFSet

/-! ## Functions as sets of pairs -/

/-- `IsFunction F X A`: the set `F` is a **function from `X` to `A`**, i.e. a set of
pairs `F ⊆ X × A` such that every `x ∈ X` is paired with exactly one `y`. -/
def IsFunction (F X A : ZFSet) : Prop :=
  F ⊆ prod X A ∧ ∀ x ∈ X, ∃ y, ⟪x, y⟫ ∈ F ∧ ∀ y', ⟪x, y'⟫ ∈ F → y' = y

/-- Function application `app F x`: the `y` with `⟪x, y⟫ ∈ F` (chosen; `∅` if there is none). -/
noncomputable def app (F x : ZFSet) : ZFSet :=
  open Classical in
  if h : ∃ y, ⟪x, y⟫ ∈ F then Classical.choose h else ∅

variable {F G X A B x y : ZFSet}

/-- `⟪x, app F x⟫ ∈ F` for `x` in the domain of a function `F`. -/
theorem app_spec (hF : IsFunction F X A) (hx : x ∈ X) : ⟪x, app F x⟫ ∈ F := by
  have h : ∃ y, ⟪x, y⟫ ∈ F := let ⟨y, hy, _⟩ := hF.2 x hx; ⟨y, hy⟩
  unfold app
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

/-- If `⟪x, y⟫ ∈ F` for a function `F`, then `app F x = y`. -/
theorem app_eq (hF : IsFunction F X A) (h : ⟪x, y⟫ ∈ F) : app F x = y := by
  have hx : x ∈ X := (kpair_mem_prod.1 (hF.1 h)).1
  obtain ⟨y₀, _, huniq⟩ := hF.2 x hx
  rw [huniq _ (app_spec hF hx), huniq _ h]

/-- A function from `X` to `A` takes values in `A`. -/
theorem app_mem (hF : IsFunction F X A) (hx : x ∈ X) : app F x ∈ A :=
  (kpair_mem_prod.1 (hF.1 (app_spec hF hx))).2

/-- The graph of a function: `⟪x, y⟫ ∈ F ↔ x ∈ X ∧ app F x = y`. -/
theorem kpair_mem_iff (hF : IsFunction F X A) : ⟪x, y⟫ ∈ F ↔ x ∈ X ∧ app F x = y :=
  ⟨fun h => ⟨(kpair_mem_prod.1 (hF.1 h)).1, app_eq hF h⟩,
   fun ⟨hx, he⟩ => he ▸ app_spec hF hx⟩

/-- **Extensionality for functions.** Two functions on `X` with the same values are equal. -/
theorem function_ext (hF : IsFunction F X A) (hG : IsFunction G X B)
    (h : ∀ x ∈ X, app F x = app G x) : F = G := by
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := mem_prod.1 (hF.1 hz)
    rw [kpair_mem_iff hF] at hz
    rw [kpair_mem_iff hG, ← h x hx]
    exact hz
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := mem_prod.1 (hG.1 hz)
    rw [kpair_mem_iff hG] at hz
    rw [kpair_mem_iff hF, h x hx]
    exact hz

/-! ## The least closed relation -/

/-- A set `R` is **closed** (for `a` and `g`) if `⟪∅, a⟫ ∈ R` and `⟪n, y⟫ ∈ R` with
`n ∈ ω` implies `⟪succ n, g y⟫ ∈ R`. -/
def RecClosed (a : ZFSet) (g : ZFSet → ZFSet) (R : ZFSet) : Prop :=
  ⟪∅, a⟫ ∈ R ∧ ∀ n y, n ∈ ω → ⟪n, y⟫ ∈ R → ⟪succ n, g y⟫ ∈ R

/-- Dedekind's function: the pairs in `ω × A` belonging to every closed set. -/
noncomputable def recFun (A a : ZFSet) (g : ZFSet → ZFSet) : ZFSet :=
  sep (fun z => ∀ R, RecClosed a g R → z ∈ R) (prod ω A)

section
variable {A a : ZFSet} {g : ZFSet → ZFSet}

/-- `recFun` lies inside `ω × A`. -/
theorem recFun_subset : recFun A a g ⊆ prod ω A := sep_subset _ _

/-- `recFun` is contained in every closed set. -/
theorem recFun_minimal {R : ZFSet} (hR : RecClosed a g R) : recFun A a g ⊆ R :=
  fun _ hz => (mem_sep.1 hz).2 R hR

/-- `recFun` is itself closed (given `a ∈ A` and `g` mapping `A` into `A`). -/
theorem recFun_closed (ha : a ∈ A) (hg : ∀ x ∈ A, g x ∈ A) : RecClosed a g (recFun A a g) := by
  refine ⟨mem_sep.2 ⟨kpair_mem_prod.2 ⟨empty_mem_omega, ha⟩, fun R hR => hR.1⟩, ?_⟩
  intro n y hn hny
  have hy : y ∈ A := (kpair_mem_prod.1 (recFun_subset hny)).2
  exact mem_sep.2 ⟨kpair_mem_prod.2 ⟨succ_mem_omega hn, hg y hy⟩,
    fun R hR => hR.2 n y hn ((mem_sep.1 hny).2 R hR)⟩

/-- **Removing a rogue pair.** If deleting the pair `p` from `recFun` leaves a closed
set, then `p ∉ recFun`. -/
theorem not_mem_recFun_of_closed {p : ZFSet}
    (h : RecClosed a g (recFun A a g \ {p})) : p ∉ recFun A a g := fun hp =>
  (mem_sdiff.1 (recFun_minimal h hp)).2 (mem_singleton.2 rfl)

/-- `recFun` is a function from `ω` to `A`. -/
theorem recFun_isFunction (ha : a ∈ A) (hg : ∀ x ∈ A, g x ∈ A) :
    IsFunction (recFun A a g) ω A := by
  have hcl := recFun_closed ha hg
  refine ⟨recFun_subset, omega_induction _ ?_ ?_⟩
  · -- base case: the only value at `∅` is `a`
    refine ⟨a, hcl.1, fun b hb => Classical.byContradiction fun hba => ?_⟩
    refine not_mem_recFun_of_closed ⟨?_, ?_⟩ hb
    · refine mem_sdiff.2 ⟨hcl.1, fun h => hba ?_⟩
      exact (kpair_inj.1 (mem_singleton.1 h)).2.symm
    · intro n y hn hny
      refine mem_sdiff.2 ⟨hcl.2 n y hn (mem_sdiff.1 hny).1, fun h => ?_⟩
      exact succ_ne_empty n (kpair_inj.1 (mem_singleton.1 h)).1
  · -- successor case: the only value at `succ n` is `g y`, where `y` is the value at `n`
    rintro n hn ⟨y, hy, huniq⟩
    refine ⟨g y, hcl.2 n y hn hy, fun c hc => Classical.byContradiction fun hcy => ?_⟩
    refine not_mem_recFun_of_closed ⟨?_, ?_⟩ hc
    · refine mem_sdiff.2 ⟨hcl.1, fun h => ?_⟩
      exact succ_ne_empty n (kpair_inj.1 (mem_singleton.1 h)).1.symm
    · intro m z hm hmz
      have hmzF := (mem_sdiff.1 hmz).1
      refine mem_sdiff.2 ⟨hcl.2 m z hm hmzF, fun h => ?_⟩
      obtain ⟨hmn, hzc⟩ := kpair_inj.1 (mem_singleton.1 h)
      have hmn' : m = n := succ_injective hmn
      subst hmn'
      rw [huniq z hmzF] at hzc
      exact hcy hzc.symm

end

/-! ## The recursion theorem -/

/-- **Dedekind's recursion theorem.** Let `a ∈ A` and let `g` map `A` into `A`.
Then there is exactly one function `F` from `ω` to `A` (a set of pairs) with
`F(∅) = a` and `F(succ n) = g(F(n))` for all `n ∈ ω`. -/
theorem recursion_theorem {A a : ZFSet} (ha : a ∈ A) (g : ZFSet → ZFSet)
    (hg : ∀ x ∈ A, g x ∈ A) :
    ∃ F, IsFunction F ω A ∧ app F ∅ = a ∧ (∀ n ∈ ω, app F (succ n) = g (app F n)) ∧
      ∀ G, IsFunction G ω A → app G ∅ = a → (∀ n ∈ ω, app G (succ n) = g (app G n)) →
        G = F := by
  have hF := recFun_isFunction ha hg
  have hcl := recFun_closed ha hg
  have h0 : app (recFun A a g) ∅ = a := app_eq hF hcl.1
  have hs : ∀ n ∈ ω, app (recFun A a g) (succ n) = g (app (recFun A a g) n) := fun n hn =>
    app_eq hF (hcl.2 n _ hn (app_spec hF hn))
  refine ⟨recFun A a g, hF, h0, hs, fun G hG hG0 hGs => function_ext hG hF ?_⟩
  refine omega_induction _ (hG0.trans h0.symm) fun n hn ih => ?_
  rw [hGs n hn, hs n hn, ih]

/-- The function produced by the recursion theorem satisfies the base equation. -/
theorem recFun_zero {A a : ZFSet} (ha : a ∈ A) {g : ZFSet → ZFSet} (hg : ∀ x ∈ A, g x ∈ A) :
    app (recFun A a g) ∅ = a :=
  app_eq (recFun_isFunction ha hg) (recFun_closed ha hg).1

/-- The function produced by the recursion theorem satisfies the step equation. -/
theorem recFun_succ {A a : ZFSet} (ha : a ∈ A) {g : ZFSet → ZFSet} (hg : ∀ x ∈ A, g x ∈ A)
    {n : ZFSet} (hn : n ∈ ω) :
    app (recFun A a g) (succ n) = g (app (recFun A a g) n) :=
  app_eq (recFun_isFunction ha hg)
    ((recFun_closed ha hg).2 n _ hn (app_spec (recFun_isFunction ha hg) hn))

/-- **Recursion theorem, set-function form.** If `G` is a function from `A` to `A`
(a set of pairs) and `a ∈ A`, there is exactly one function `F` from `ω` to `A`
with `F(∅) = a` and `F(succ n) = G(F(n))`. -/
theorem recursion_theorem_set {A a G : ZFSet} (ha : a ∈ A) (hG : IsFunction G A A) :
    ∃ F, IsFunction F ω A ∧ app F ∅ = a ∧ (∀ n ∈ ω, app F (succ n) = app G (app F n)) ∧
      ∀ F', IsFunction F' ω A → app F' ∅ = a →
        (∀ n ∈ ω, app F' (succ n) = app G (app F' n)) → F' = F :=
  recursion_theorem ha (app G) fun _ hx => app_mem hG hx

end ZFSet

end Foundations.Sets
