/-!
# Hall's marriage theorem

Given finitely many finite sets `A₀, …, A_{N−1}`, when can one choose **distinct
representatives** `f(i) ∈ Aᵢ` (a "system of distinct representatives", or, in the
classical story, marry each of `N` women to a man she likes, no man marrying twice)?
An obvious necessary condition is **Hall's condition**: any `k` of the sets together
contain at least `k` elements. Philip Hall (1935) proved that it is also sufficient.

We follow the inductive proof of Halmos and Vaughan (1950), by induction on the number
of sets.

* If every proper, non-empty subfamily `I` has *strictly* more than `|I|` elements in
  its union, match one set `A_{i₀}` to any of its elements `x`, delete `x` from all
  other sets; Hall's condition survives (each union lost at most one element but had
  one to spare).
* Otherwise some proper non-empty subfamily `I` is *critical*: its union has exactly
  `|I|` elements. Match `I` by induction (it uses up exactly its union), and match the
  rest after deleting that union from their sets; Hall's condition for the rest
  follows from Hall's condition for the rest *together with* `I`.

*Representation.* The sets live in the universe `{0, …, M−1}` and are indexed by
`{0, …, N−1}`; a family is a relation `A i x` ("`x ∈ Aᵢ`"), a subfamily is a predicate on
indices, and sizes are computed by counting (`cnt`). This "bounded universe" approach
makes all the cardinality bookkeeping a matter of simple inductions.
-/

open Classical

namespace Foundations.Combinatorics

/-! ## Counting -/

/-- The number of `x < n` satisfying `P`. -/
noncomputable def cnt (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt P n + if P n then 1 else 0

/-- Counting is monotone. -/
theorem cnt_mono {P Q : Nat → Prop} : ∀ n, (∀ x, x < n → P x → Q x) → cnt P n ≤ cnt Q n
  | 0, _ => Nat.le_refl _
  | n + 1, h => by
      have := cnt_mono n fun x hx => h x (by omega)
      simp only [cnt]
      by_cases hp : P n
      · simp [hp, h n (by omega) hp]; omega
      · simp only [hp, ite_false]; split <;> omega

/-- Counting respects equivalence. -/
theorem cnt_congr {P Q : Nat → Prop} (n : Nat) (h : ∀ x, x < n → (P x ↔ Q x)) :
    cnt P n = cnt Q n :=
  Nat.le_antisymm (cnt_mono n fun x hx => (h x hx).1) (cnt_mono n fun x hx => (h x hx).2)

/-- **Inclusion–exclusion**: `|P ∪ Q| + |P ∩ Q| = |P| + |Q|`. -/
theorem cnt_or_and (P Q : Nat → Prop) : ∀ n,
    cnt (fun x => P x ∨ Q x) n + cnt (fun x => P x ∧ Q x) n = cnt P n + cnt Q n
  | 0 => rfl
  | n + 1 => by
      have := cnt_or_and P Q n
      simp only [cnt]
      by_cases hp : P n <;> by_cases hq : Q n <;> simp [hp, hq] <;> omega

/-- The count of an empty predicate is `0`. -/
theorem cnt_eq_zero {P : Nat → Prop} : ∀ n, (∀ x, x < n → ¬ P x) → cnt P n = 0
  | 0, _ => rfl
  | n + 1, h => by
      simp only [cnt, h n (by omega), ite_false, cnt_eq_zero n fun x hx => h x (by omega)]

/-- Disjoint union: `|P ∪ Q| = |P| + |Q|` when `P ∩ Q = ∅`. -/
theorem cnt_or_disjoint {P Q : Nat → Prop} (n : Nat) (h : ∀ x, x < n → ¬ (P x ∧ Q x)) :
    cnt (fun x => P x ∨ Q x) n = cnt P n + cnt Q n := by
  have := cnt_or_and P Q n
  rw [cnt_eq_zero n h] at this; omega

/-- A non-empty predicate has positive count. -/
theorem cnt_pos {P : Nat → Prop} : ∀ n, (∃ x, x < n ∧ P x) → 0 < cnt P n
  | 0, ⟨_, hx, _⟩ => absurd hx (Nat.not_lt_zero _)
  | n + 1, ⟨x, hx, hpx⟩ => by
      simp only [cnt]
      by_cases hn : x = n
      · subst hn; simp [hpx]
      · have := cnt_pos n ⟨x, by omega, hpx⟩; omega

/-- Positive count gives a witness. -/
theorem exists_of_cnt_pos {P : Nat → Prop} (n : Nat) (h : 0 < cnt P n) : ∃ x, x < n ∧ P x :=
  Classical.byContradiction fun hno => by
    rw [cnt_eq_zero n fun x hx hp => hno ⟨x, hx, hp⟩] at h; exact Nat.lt_irrefl _ h

/-- A proper sub-predicate has strictly smaller count. -/
theorem cnt_lt {P Q : Nat → Prop} (n : Nat) (hsub : ∀ x, x < n → P x → Q x)
    (hproper : ∃ x, x < n ∧ Q x ∧ ¬ P x) : cnt P n < cnt Q n := by
  have h₁ := cnt_or_disjoint (P := P) (Q := fun x => Q x ∧ ¬ P x) n fun x _ h => h.2.2 h.1
  have h₂ := cnt_congr (P := fun x => P x ∨ (Q x ∧ ¬ P x)) (Q := Q) n fun x hx =>
    ⟨fun h => h.elim (hsub x hx) And.left, fun h => (Classical.em (P x)).elim Or.inl
      fun hp => Or.inr ⟨h, hp⟩⟩
  have h₃ := cnt_pos n (let ⟨x, hx, h⟩ := hproper; ⟨x, hx, h⟩)
  omega

/-- A single point has count at most `1`. -/
theorem cnt_eq_le_one (a : Nat) : ∀ n, cnt (fun x => x = a) n ≤ 1
  | 0 => Nat.zero_le _
  | n + 1 => by
      simp only [cnt]
      by_cases h : n = a
      · subst h
        rw [cnt_eq_zero n fun x hx he => by omega]; simp
      · simp only [h, ite_false]; exact cnt_eq_le_one a n

/-- Removing one point lowers the count by at most `1`. -/
theorem cnt_remove (P : Nat → Prop) (a n : Nat) : cnt P n ≤ cnt (fun x => P x ∧ x ≠ a) n + 1 := by
  have h₁ := cnt_mono (P := P) (Q := fun x => (P x ∧ x ≠ a) ∨ x = a) n fun x _ hp =>
    (Classical.em (x = a)).elim Or.inr fun h => Or.inl ⟨hp, h⟩
  have h₂ := cnt_or_and (fun x => P x ∧ x ≠ a) (fun x => x = a) n
  have h₃ := cnt_eq_le_one a n
  omega

/-- A single point below `n` has count `1`. -/
theorem cnt_point {a : Nat} : ∀ n, a < n → cnt (fun x => x = a) n = 1
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
      simp only [cnt]
      by_cases hn : n = a
      · subst hn; rw [cnt_eq_zero n fun x hx he => by omega]; simp
      · simp only [hn, ite_false]; exact cnt_point n (by omega)

/-- Removing a point of `Q` lowers the count by exactly `1`. -/
theorem cnt_remove_eq {Q : Nat → Prop} {a m : Nat} (hQa : Q a) (ha : a < m) :
    cnt Q m = cnt (fun x => Q x ∧ x ≠ a) m + 1 := by
  rw [← cnt_point m ha, ← cnt_or_disjoint m fun x _ h => h.1.2 h.2]
  exact cnt_congr m fun x _ => ⟨fun hq => (Classical.em (x = a)).elim Or.inr
    fun h => Or.inl ⟨hq, h⟩, fun h => h.elim And.left fun h => h ▸ hQa⟩

/-- **Counting through an injection**: an injective map from the `P`-points below `n`
into the `Q`-points below `m` shows `|P| ≤ |Q|`. -/
theorem cnt_le_of_inj {m : Nat} (g : Nat → Nat) : ∀ n (P Q : Nat → Prop),
    (∀ x, x < n → P x → g x < m ∧ Q (g x)) →
    (∀ x y, x < n → y < n → P x → P y → x ≠ y → g x ≠ g y) → cnt P n ≤ cnt Q m
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, P, Q, hmap, hinj => by
      simp only [cnt]
      by_cases hP : P n
      · simp only [hP, ite_true]
        obtain ⟨hgm, hgQ⟩ := hmap n (by omega) hP
        have := cnt_le_of_inj g n P (fun y => Q y ∧ y ≠ g n)
          (fun x hx hPx => ⟨(hmap x (by omega) hPx).1, (hmap x (by omega) hPx).2,
            hinj x n (by omega) (by omega) hPx hP (by omega)⟩)
          (fun x y hx hy => hinj x y (by omega) (by omega))
        rw [cnt_remove_eq hgQ hgm]; omega
      · simp only [hP, ite_false, Nat.add_zero]
        exact cnt_le_of_inj g n P Q (fun x hx => hmap x (by omega))
          (fun x y hx hy => hinj x y (by omega) (by omega))

/-! ## Hall's theorem -/

section Hall

variable (N M : Nat)

/-- The union of the subfamily `I`: the elements of some `Aᵢ` with `i ∈ I`. -/
def union (A : Nat → Nat → Prop) (I : Nat → Prop) (x : Nat) : Prop := ∃ i, i < N ∧ I i ∧ A i x

/-- **Hall's condition** for the subfamily `J`: every subfamily `I ⊆ J` has at least
`|I|` elements in its union. -/
def HallCond (J : Nat → Prop) (A : Nat → Nat → Prop) : Prop :=
  ∀ I : Nat → Prop, (∀ i, i < N → I i → J i) → cnt I N ≤ cnt (union N A I) M

/-- A **system of distinct representatives** for the subfamily `J`. -/
def SDR (J : Nat → Prop) (A : Nat → Nat → Prop) (f : Nat → Nat) : Prop :=
  (∀ i, i < N → J i → f i < M ∧ A i (f i)) ∧
    ∀ i j, i < N → j < N → J i → J j → i ≠ j → f i ≠ f j

/-- **Hall's theorem for subfamilies**, by strong induction on `|J|`. -/
theorem hall_aux : ∀ k (J : Nat → Prop) (A : Nat → Nat → Prop), cnt J N = k →
    HallCond N M J A → ∃ f, SDR N M J A f := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro J A hk hHall
  by_cases hcrit : ∃ I : Nat → Prop, (∀ i, i < N → I i → J i) ∧ (∃ i, i < N ∧ I i) ∧
      (∃ i, i < N ∧ J i ∧ ¬ I i) ∧ cnt (union N A I) M ≤ cnt I N
  · -- a critical subfamily `I`
    obtain ⟨I, hIJ, hIne, hIprop, hIcrit⟩ := hcrit
    obtain ⟨f₁, hf₁⟩ := ih (cnt I N) (hk ▸ cnt_lt N hIJ hIprop) I A rfl
      fun I' hI' => hHall I' fun i hi h => hIJ i hi (hI' i hi h)
    let K : Nat → Prop := fun i => J i ∧ ¬ I i
    let A' : Nat → Nat → Prop := fun i x => A i x ∧ ¬ union N A I x
    have hKlt : cnt K N < k := by
      rw [← hk]
      refine cnt_lt N (fun i _ h => h.1) ?_
      obtain ⟨i, hi, hIi⟩ := hIne
      exact ⟨i, hi, hIJ i hi hIi, fun h => h.2 hIi⟩
    have hHallK : HallCond N M K A' := by
      intro L hLK
      have hLI := hHall (fun i => L i ∨ I i) fun i hi h => h.elim (fun h => (hLK i hi h).1) (hIJ i hi)
      rw [cnt_or_disjoint N fun i hi h => (hLK i hi h.1).2 h.2] at hLI
      -- `⋃(L ∪ I) = (⋃'L) ⊔ ⋃I`
      have hU : cnt (union N A fun i => L i ∨ I i) M =
          cnt (union N A' L) M + cnt (union N A I) M := by
        rw [← cnt_or_disjoint M fun x _ h => by
          obtain ⟨i, _, _, _, hx⟩ := h.1; exact hx h.2]
        refine cnt_congr M fun x _ => ⟨?_, ?_⟩
        · rintro ⟨i, hi, hLIi, hAx⟩
          by_cases hx : union N A I x
          · exact Or.inr hx
          · rcases hLIi with hL | hI
            · exact Or.inl ⟨i, hi, hL, hAx, hx⟩
            · exact Or.inr ⟨i, hi, hI, hAx⟩
        · rintro (⟨i, hi, hL, hAx, _⟩ | ⟨i, hi, hI, hAx⟩)
          · exact ⟨i, hi, Or.inl hL, hAx⟩
          · exact ⟨i, hi, Or.inr hI, hAx⟩
      omega
    obtain ⟨f₂, hf₂⟩ := ih (cnt K N) hKlt K A' rfl hHallK
    refine ⟨fun i => if I i then f₁ i else f₂ i, fun i hi hJ => ?_, fun i j hi hj hJi hJj hij => ?_⟩
    · by_cases hI : I i
      · simp only [hI, ite_true]; exact hf₁.1 i hi hI
      · simp only [hI, ite_false]
        obtain ⟨h₁, h₂, -⟩ := hf₂.1 i hi ⟨hJ, hI⟩
        exact ⟨h₁, h₂⟩
    · by_cases hIi : I i <;> by_cases hIj : I j <;> simp only [hIi, hIj, ite_true, ite_false]
      · exact hf₁.2 i j hi hj hIi hIj hij
      · intro he
        exact (hf₂.1 j hj ⟨hJj, hIj⟩).2.2 (he ▸ ⟨i, hi, hIi, (hf₁.1 i hi hIi).2⟩)
      · intro he
        exact (hf₂.1 i hi ⟨hJi, hIi⟩).2.2 (he ▸ ⟨j, hj, hIj, (hf₁.1 j hj hIj).2⟩)
      · exact hf₂.2 i j hi hj ⟨hJi, hIi⟩ ⟨hJj, hIj⟩ hij
  · -- every proper non-empty subfamily has a surplus
    by_cases hJne : ∃ i₀, i₀ < N ∧ J i₀
    · obtain ⟨i₀, hi₀, hJi₀⟩ := hJne
      -- an element of `A i₀`
      obtain ⟨x, hxM, hx⟩ : ∃ x, x < M ∧ A i₀ x := by
        have h := hHall (fun i => i = i₀) fun i _ h => h ▸ hJi₀
        have h1 := cnt_pos (P := fun i => i = i₀) N ⟨i₀, hi₀, rfl⟩
        obtain ⟨x, hx, i, _, rfl, hAx⟩ := exists_of_cnt_pos M (Nat.lt_of_lt_of_le h1 h)
        exact ⟨x, hx, hAx⟩
      let J' : Nat → Prop := fun i => J i ∧ i ≠ i₀
      let A' : Nat → Nat → Prop := fun i y => A i y ∧ y ≠ x
      have hJ'lt : cnt J' N < k := by
        rw [← hk]; exact cnt_lt N (fun i _ h => h.1) ⟨i₀, hi₀, hJi₀, fun h => h.2 rfl⟩
      have hHall' : HallCond N M J' A' := by
        intro L hLJ
        by_cases hLne : ∃ i, i < N ∧ L i
        · have hsurplus : cnt L N < cnt (union N A L) M := by
            refine Nat.lt_of_not_le fun hle => hcrit ⟨L, fun i hi h => (hLJ i hi h).1, hLne,
              ⟨i₀, hi₀, hJi₀, fun h => (hLJ i₀ hi₀ h).2 rfl⟩, hle⟩
          have hrem := cnt_remove (union N A L) x M
          have heq : cnt (fun y => union N A L y ∧ y ≠ x) M = cnt (union N A' L) M :=
            cnt_congr M fun y _ => ⟨fun ⟨⟨i, hi, hL, hA⟩, hne⟩ => ⟨i, hi, hL, hA, hne⟩,
              fun ⟨i, hi, hL, hA, hne⟩ => ⟨⟨i, hi, hL, hA⟩, hne⟩⟩
          omega
        · rw [cnt_eq_zero N fun i hi h => hLne ⟨i, hi, h⟩]; exact Nat.zero_le _
      obtain ⟨f', hf'⟩ := ih (cnt J' N) hJ'lt J' A' rfl hHall'
      refine ⟨fun i => if i = i₀ then x else f' i, fun i hi hJ => ?_,
        fun i j hi hj hJi hJj hij => ?_⟩
      · by_cases h : i = i₀
        · subst h; simp [hxM, hx]
        · simp only [h, ite_false]
          obtain ⟨h₁, h₂, -⟩ := hf'.1 i hi ⟨hJ, h⟩
          exact ⟨h₁, h₂⟩
      · by_cases hi₀' : i = i₀ <;> by_cases hj₀' : j = i₀ <;>
          simp only [hi₀', hj₀', ite_true, ite_false]
        · exact absurd (hi₀'.trans hj₀'.symm) hij
        · exact fun he => (hf'.1 j hj ⟨hJj, hj₀'⟩).2.2 he.symm
        · exact fun he => (hf'.1 i hi ⟨hJi, hi₀'⟩).2.2 he
        · exact hf'.2 i j hi hj ⟨hJi, hi₀'⟩ ⟨hJj, hj₀'⟩ hij
    · exact ⟨fun _ => 0, fun i hi hJ => absurd ⟨i, hi, hJ⟩ hJne,
        fun i _ hi _ hJ => absurd ⟨i, hi, hJ⟩ hJne⟩

/-- **Hall's marriage theorem.** Let `A₀, …, A_{N−1}` be subsets of `{0, …, M−1}` such
that every subfamily `I` has at least `|I|` elements in its union. Then there is a
system of distinct representatives: an injective choice `f(i) ∈ Aᵢ`. -/
theorem hall (A : Nat → Nat → Prop)
    (hHall : ∀ I : Nat → Prop, cnt I N ≤ cnt (union N A I) M) :
    ∃ f : Nat → Nat, (∀ i, i < N → f i < M ∧ A i (f i)) ∧
      ∀ i j, i < N → j < N → i ≠ j → f i ≠ f j := by
  obtain ⟨f, h₁, h₂⟩ := hall_aux N M _ (fun _ => True) A rfl fun I _ => hHall I
  exact ⟨f, fun i hi => h₁ i hi trivial, fun i j hi hj hij => h₂ i j hi hj trivial trivial hij⟩

/-- Hall's condition is **necessary**: a system of distinct representatives maps every
subfamily injectively into its union. -/
theorem hall_necessary (A : Nat → Nat → Prop) (f : Nat → Nat)
    (hf : ∀ i, i < N → f i < M ∧ A i (f i)) (hinj : ∀ i j, i < N → j < N → i ≠ j → f i ≠ f j)
    (I : Nat → Prop) : cnt I N ≤ cnt (union N A I) M :=
  cnt_le_of_inj f N I _ (fun i hi hI => ⟨(hf i hi).1, i, hi, hI, (hf i hi).2⟩)
    fun i j hi hj _ _ hij => hinj i j hi hj hij

/-- **Hall's marriage theorem, both directions**: a finite family has a system of
distinct representatives iff it satisfies Hall's condition. -/
theorem hall_iff (A : Nat → Nat → Prop) :
    (∃ f : Nat → Nat, (∀ i, i < N → f i < M ∧ A i (f i)) ∧
      ∀ i j, i < N → j < N → i ≠ j → f i ≠ f j) ↔
    ∀ I : Nat → Prop, cnt I N ≤ cnt (union N A I) M :=
  ⟨fun ⟨f, hf, hinj⟩ => hall_necessary N M A f hf hinj, hall N M A⟩

end Hall

end Foundations.Combinatorics
