import Foundations.Types.SystemFSubst

/-!
# Girard's theorem: strong normalization of System F

Tait's method (`Normalization.lean`) defines, for each type, the set of
*reducible* terms by recursion on the type. For System F this breaks down at the
quantifier: a term of type `∀α. A` can be instantiated at *any* type `B`,
including types far larger than `∀α. A` itself (for instance `∀α. A` again), so
"reducible at `∀α. A`" cannot be defined from "reducible at `A[B]`" by recursion
on types. This is impredicativity, and it is exactly what makes the system
strong.

**Girard's solution** (1972): do not try to say *which* set of terms `α`
denotes. Instead quantify over *all* sets of terms that could serve: the
**reducibility candidates** — predicates on terms satisfying Tait's three
conditions (CR1) members are strongly normalizing, (CR2) closure under
reduction, (CR3) a neutral term all of whose reducts are members is a member.
A type with free type variables is interpreted relative to an *environment*
`ρ` assigning a candidate to each type variable:

* `⟦α⟧ρ = ρ(α)`;
* `⟦A → B⟧ρ = { t | ∀ u ∈ ⟦A⟧ρ, t u ∈ ⟦B⟧ρ }`;
* `⟦∀α. A⟧ρ = { t | for every type B and every candidate C, t [B] ∈ ⟦A⟧(ρ, α ↦ C) }`.

The last clause quantifies over *all candidates* — a quantification over sets of
terms that includes the very set being defined. In Lean this is possible
because `Prop` is impredicative: `∀ C : Cand, …` is again a proposition. (By
Gödel's second incompleteness theorem the proof cannot be formalized in
second-order arithmetic, whose consistency it implies: Girard's theorem shows
that the functions provably total there are exactly those definable in
System F.)

The key lemmas are that each `⟦A⟧ρ` is a candidate, and the **substitution
lemma** `⟦A[B]⟧ρ = ⟦A⟧(ρ, α ↦ ⟦B⟧ρ)`, which is where the impredicative
quantification pays off in the case of type application. The **fundamental
lemma** then states that a well-typed term, with reducible terms substituted for
its free variables (and any types for its type variables), lies in the
interpretation of its type.

**Corollary: consistency.** The type `∀α. α` — under Curry–Howard the
second-order proposition "everything is true", i.e. falsity — has no closed
inhabitant. Its normal form would have to be `Λ. s` with `s` a closed normal term
of the bare type variable `α`, and there is none. The proofs in this file use
no choice; excluded middle is not needed either, since normality is decidable
(`step?`).
-/

namespace Foundations.Types

namespace SystemF

open Term

/-! ## Strong normalization and neutral terms -/

/-- A term is **strongly normalizing** when all its reduction sequences are finite. -/
def SN (t : Term) : Prop := Acc (fun t' t => Step t t') t

/-- A term all of whose reducts are strongly normalizing is strongly normalizing. -/
theorem SN.intro {t : Term} (h : ∀ t', Step t t' → SN t') : SN t := Acc.intro t h

/-- Reducts of strongly normalizing terms are strongly normalizing. -/
theorem SN.step {t t' : Term} (h : SN t) (hs : Step t t') : SN t' := Acc.inv h hs

/-- If a step-preserving context `f` makes `f t` strongly normalizing, so is `t`. -/
theorem SN.of_map (f : Term → Term) (hf : ∀ t t', Step t t' → Step (f t) (f t')) {t : Term}
    (h : SN (f t)) : SN t := by
  suffices ∀ s, SN s → ∀ t, f t = s → SN t from this _ h t rfl
  intro s hs
  induction hs with
  | intro s _ ih =>
    intro t ht
    subst ht
    exact SN.intro fun t' h => ih (f t') (hf _ _ h) t' rfl

/-- A term is **neutral** when it is not an abstraction of either kind. -/
def Neutral : Term → Prop
  | lam _ => False
  | tlam _ => False
  | _ => True

/-! ## Reducibility candidates -/

/-- A **reducibility candidate** (Girard): a predicate on terms satisfying
CR1–CR3. -/
structure Cand where
  /-- The terms belonging to the candidate. -/
  pred : Term → Prop
  /-- (CR1) Members are strongly normalizing. -/
  cr1 : ∀ t, pred t → SN t
  /-- (CR2) Membership is preserved by reduction. -/
  cr2 : ∀ t t', pred t → Step t t' → pred t'
  /-- (CR3) A neutral term whose reducts are all members is a member. -/
  cr3 : ∀ t, Neutral t → (∀ t', Step t t' → pred t') → pred t

/-- Candidates with the same members are equal. -/
theorem Cand.ext {C D : Cand} (h : ∀ t, C.pred t ↔ D.pred t) : C = D := by
  cases C with
  | mk p _ _ _ =>
    cases D with
    | mk q _ _ _ =>
      have : p = q := funext fun t => propext (h t)
      subst this
      rfl

/-- The strongly normalizing terms form a candidate (so candidates exist). -/
def snCand : Cand where
  pred := SN
  cr1 _ h := h
  cr2 _ _ h hs := h.step hs
  cr3 _ _ h := SN.intro h

/-- Every candidate contains all variables (by CR3: they are neutral and normal). -/
theorem Cand.var (C : Cand) (n : Nat) : C.pred (var n) :=
  C.cr3 _ trivial (fun _ h => by cases h)

/-- Extending an environment of candidates by a new type variable `0`. -/
def extend (C : Cand) (ρ : Nat → Cand) : Nat → Cand
  | 0 => C
  | n + 1 => ρ n

/-- The **interpretation** `⟦A⟧ρ` of a type as a set of terms, relative to an
environment `ρ` of candidates for its type variables. -/
def RED : (Nat → Cand) → Ty → Term → Prop
  | ρ, .tvar n, t => (ρ n).pred t
  | ρ, .arr A B, t => ∀ u, RED ρ A u → RED ρ B (app t u)
  | ρ, .all A, t => ∀ (B : Ty) (C : Cand), RED (extend C ρ) A (tapp t B)

/-- **Every interpretation is a candidate**: `⟦A⟧ρ` satisfies CR1–CR3. -/
theorem red_cand (A : Ty) : ∀ ρ,
    (∀ t, RED ρ A t → SN t) ∧ (∀ t t', RED ρ A t → Step t t' → RED ρ A t') ∧
    (∀ t, Neutral t → (∀ t', Step t t' → RED ρ A t') → RED ρ A t) := by
  induction A with
  | tvar n => intro ρ; exact ⟨(ρ n).cr1, (ρ n).cr2, (ρ n).cr3⟩
  | arr A B ihA ihB =>
    intro ρ
    obtain ⟨a₁, a₂, a₃⟩ := ihA ρ
    obtain ⟨b₁, b₂, b₃⟩ := ihB ρ
    have hv : RED ρ A (var 0) := a₃ (var 0) trivial (fun _ h => by cases h)
    refine ⟨fun t h => ?_, fun t t' h hs u hu => b₂ _ _ (h u hu) (Step.appL hs),
      fun t hn h u hu => ?_⟩
    · exact SN.of_map (fun t => app t (var 0)) (fun _ _ => Step.appL) (b₁ _ (h _ hv))
    · have hsn := a₁ u hu
      revert hu
      induction hsn with
      | intro u _ ih =>
        intro hu
        refine b₃ _ (by exact trivial) ?_
        intro x hx
        cases hx with
        | beta => exact hn.elim
        | appL hx => exact h _ hx u hu
        | appR hx => exact ih _ hx (a₂ _ _ hu hx)
  | all A ih =>
    intro ρ
    refine ⟨fun t h => ?_, fun t t' h hs B C => (ih _).2.1 _ _ (h B C) (Step.tapp hs),
      fun t hn h B C => ?_⟩
    · exact SN.of_map (fun t => tapp t (.tvar 0)) (fun _ _ => Step.tapp)
        ((ih (extend snCand ρ)).1 _ (h (.tvar 0) snCand))
    · refine (ih (extend C ρ)).2.2 _ (by exact trivial) ?_
      intro x hx
      cases hx with
      | tbeta => exact hn.elim
      | tapp hx => exact h _ hx B C

/-- The interpretation `⟦A⟧ρ`, packaged as a candidate. -/
def interp (ρ : Nat → Cand) (A : Ty) : Cand where
  pred := RED ρ A
  cr1 := (red_cand A ρ).1
  cr2 := (red_cand A ρ).2.1
  cr3 := (red_cand A ρ).2.2

/-- Extending after a lifted renaming. -/
theorem extend_upRen (C : Cand) (ρ : Nat → Cand) (ξ : Nat → Nat) :
    extend C ρ ∘ Ty.upRen ξ = extend C (ρ ∘ ξ) := by
  funext n; cases n <;> rfl

/-- **Renaming lemma**: `⟦A ξ⟧ρ = ⟦A⟧(ρ ∘ ξ)`. -/
theorem RED_rename (A : Ty) : ∀ ρ ξ t, RED ρ (A.rename ξ) t ↔ RED (ρ ∘ ξ) A t := by
  induction A with
  | tvar n => intros; exact Iff.rfl
  | arr A B ihA ihB => intros; simp only [RED, Ty.rename, ihA, ihB]
  | all A ih => intros; simp only [RED, Ty.rename, ih, extend_upRen]

/-- **Substitution lemma**: `⟦A σ⟧ρ = ⟦A⟧(n ↦ ⟦σ n⟧ρ)`. -/
theorem RED_subst (A : Ty) : ∀ ρ σ t, RED ρ (A.subst σ) t ↔ RED (fun n => interp ρ (σ n)) A t := by
  induction A with
  | tvar n => intros; exact Iff.rfl
  | arr A B ihA ihB => intros; simp only [RED, Ty.subst, ihA, ihB]
  | all A ih =>
    intro ρ σ t
    have henv : ∀ C, (fun n => interp (extend C ρ) (Ty.up σ n)) = extend C (fun n => interp ρ (σ n)) := by
      intro C
      funext n
      cases n with
      | zero => exact Cand.ext fun _ => Iff.rfl
      | succ n => exact Cand.ext fun t => RED_rename (σ n) (extend C ρ) Nat.succ t
    simp only [RED, Ty.subst, ih, henv]

/-- **Instantiation lemma**: `⟦A[B]⟧ρ = ⟦A⟧(ρ, 0 ↦ ⟦B⟧ρ)`. -/
theorem RED_inst (A B : Ty) (ρ : Nat → Cand) (t : Term) :
    RED ρ (A.inst B) t ↔ RED (extend (interp ρ B) ρ) A t := by
  have henv : (fun n => interp ρ (Ty.cons B Ty.tvar n)) = extend (interp ρ B) ρ := by
    funext n
    cases n with
    | zero => rfl
    | succ n => exact Cand.ext fun _ => Iff.rfl
  unfold Ty.inst
  rw [RED_subst, henv]

/-! ## Introduction rules preserve reducibility -/

/-- If `s[u]` is strongly normalizing, so is `s`. -/
theorem SN.of_inst {s u : Term} (h : SN (inst s u)) : SN s :=
  SN.of_map (fun s => inst s u) (fun _ _ hs => hs.subst _) h

/-- If `s[B]` is strongly normalizing, so is `s`. -/
theorem SN.of_tyInst {s : Term} {B : Ty} (h : SN (tyInst s B)) : SN s :=
  SN.of_map (fun s => tyInst s B) (fun _ _ hs => hs.tySubst _) h

/-- The core of `lam_red`, by induction on strong normalization. -/
theorem lam_red_aux {ρ : Nat → Cand} {A B : Ty} : ∀ s, SN s → ∀ u, SN u → RED ρ A u →
    (∀ v, RED ρ A v → RED ρ B (inst s v)) → RED ρ B (app (lam s) u) := by
  intro s hs
  induction hs with
  | intro s _ ihs =>
    intro u hu₀
    induction hu₀ with
    | intro u huacc ihu =>
      intro hu h
      refine (interp ρ B).cr3 _ (by exact trivial) ?_
      intro x hx
      cases hx with
      | beta => exact h u hu
      | appL hx =>
        cases hx with
        | lam hx =>
          exact ihs _ hx u (SN.intro huacc) hu
            (fun v hv => (interp ρ B).cr2 _ _ (h v hv) (hx.subst _))
      | appR hx => exact ihu _ hx ((interp ρ A).cr2 _ _ hu hx) h

/-- **Abstraction is reducible** when its body is, under every reducible argument. -/
theorem lam_red {ρ : Nat → Cand} {A B : Ty} {s : Term}
    (h : ∀ u, RED ρ A u → RED ρ B (inst s u)) : RED ρ (.arr A B) (lam s) := fun u hu =>
  lam_red_aux s (SN.of_inst ((interp ρ B).cr1 _ (h _ ((interp ρ A).var 0)))) u
    ((interp ρ A).cr1 _ hu) hu h

/-- The core of `tlam_red`, by induction on strong normalization. -/
theorem tlam_red_aux {ρ : Nat → Cand} {A : Ty} : ∀ s, SN s →
    (∀ (B : Ty) (C : Cand), RED (extend C ρ) A (tyInst s B)) →
    ∀ (B : Ty) (C : Cand), RED (extend C ρ) A (tapp (tlam s) B) := by
  intro s hs
  induction hs with
  | intro s _ ih =>
    intro h B C
    refine (interp (extend C ρ) A).cr3 _ (by exact trivial) ?_
    intro x hx
    cases hx with
    | tbeta => exact h B C
    | tapp hx =>
      cases hx with
      | tlam hx =>
        exact ih _ hx (fun B' C' => (interp (extend C' ρ) A).cr2 _ _ (h B' C') (hx.tySubst _)) B C

/-- **Type abstraction is reducible** when every instance of its body is
reducible, for every candidate. -/
theorem tlam_red {ρ : Nat → Cand} {A : Ty} {s : Term}
    (h : ∀ (B : Ty) (C : Cand), RED (extend C ρ) A (tyInst s B)) : RED ρ (.all A) (tlam s) :=
  tlam_red_aux s (SN.of_tyInst ((interp (extend snCand ρ) A).cr1 _ (h (.tvar 0) snCand))) h

/-! ## The fundamental lemma -/

/-- **The fundamental lemma.** If `Γ ⊢ t : A`, then for every environment `ρ` of
candidates, every substitution `σ` of reducible terms for the term variables, and
every substitution `τ` of types for the type variables, `t` (substituted) belongs
to `⟦A⟧ρ`. -/
theorem fundamental {Γ : List Ty} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ (ρ : Nat → Cand) (σ : Nat → Term) (τ : Nat → Ty),
      (∀ n B, Γ[n]? = some B → RED ρ B (σ n)) → RED ρ A (subst σ (tySubst τ t)) := by
  induction h with
  | var hn => intro ρ σ τ hσ; exact hσ _ _ hn
  | lam _ ih =>
    intro ρ σ τ hσ
    refine lam_red fun u hu => ?_
    rw [inst_up]
    refine ih ρ (cons u σ) τ fun n B hn => ?_
    cases n with
    | zero => simp at hn; subst hn; exact hu
    | succ n => exact hσ n B (by simpa using hn)
  | app _ _ ih₁ ih₂ => intro ρ σ τ hσ; exact ih₁ ρ σ τ hσ _ (ih₂ ρ σ τ hσ)
  | tlam _ ih =>
    intro ρ σ τ hσ
    refine tlam_red fun B C => ?_
    rw [tyInst_subst_tySubst]
    refine ih (extend C ρ) σ _ fun n B' hn => ?_
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
    obtain ⟨B₀, hB₀, rfl⟩ := hn
    exact (RED_rename B₀ (extend C ρ) Nat.succ _).2 (hσ n B₀ hB₀)
  | @tapp Γ t A B _ ih =>
    intro ρ σ τ hσ
    exact (RED_inst A B ρ _).2 (ih ρ σ τ hσ (B.subst τ) (interp ρ B))

/-- **Girard's theorem: strong normalization of System F.** Every well-typed term
of System F is strongly normalizing. -/
theorem strong_normalization {Γ : List Ty} {t : Term} {A : Ty} (h : HasType Γ t A) : SN t := by
  have := fundamental h (fun _ => snCand) var Ty.tvar (fun n B _ => (interp _ B).var n)
  rw [tySubst_tvar, subst_var] at this
  exact (interp _ A).cr1 _ this

/-- A strongly normalizing term has a normal form (constructively, via `step?`). -/
theorem SN.normalizes {t : Term} (h : SN t) : ∃ n, Star Step t n ∧ Normal n := by
  induction h with
  | intro t _ ih =>
    cases hs : step? t with
    | some t' =>
      have ht' := step?_sound _ _ hs
      obtain ⟨n, hn, hn'⟩ := ih t' ht'
      exact ⟨n, Star.head ht' hn, hn'⟩
    | none => exact ⟨t, Star.refl t, (normal_iff_step?_none t).2 hs⟩

/-- **Weak normalization of System F**, with the normal form typed. -/
theorem weak_normalization {Γ : List Ty} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∃ n, Star Step t n ∧ Normal n ∧ HasType Γ n A := by
  obtain ⟨n, hn, hn'⟩ := (strong_normalization h).normalizes
  refine ⟨n, hn, hn', ?_⟩
  clear hn'
  induction hn with
  | refl => exact h
  | tail _ hs ih => exact subject_reduction hs ih

/-- A closed normal term of a bare type variable does not exist. -/
theorem no_closed_normal_tvar {s : Term} {k : Nat} (hs : HasType [] s (.tvar k))
    (hn : Normal s) : False := by
  rcases progress hs with hv | ⟨s', hs'⟩
  · cases s with
    | lam => cases hs
    | tlam => cases hs
    | _ => exact hv
  · exact hn _ hs'

/-- **Consistency of System F.** The type `∀α. α` has no closed inhabitant: under
Curry–Howard, second-order intuitionistic logic does not prove falsity. -/
theorem no_closed_all_tvar : ¬ ∃ t, HasType [] t (.all (.tvar 0)) := by
  rintro ⟨t, ht⟩
  obtain ⟨n, _, hn, hnt⟩ := weak_normalization ht
  rcases progress hnt with hv | ⟨n', hn'⟩
  · cases n with
    | lam => cases hnt
    | tlam s =>
      cases hnt with
      | tlam hs => exact no_closed_normal_tvar hs (fun s' h => hn _ (Step.tlam h))
    | _ => exact hv
  · exact hn _ hn'

end SystemF

end Foundations.Types
