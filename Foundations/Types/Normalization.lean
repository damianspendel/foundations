import Foundations.Types.STLC

/-!
# Strong normalization: Tait's method of reducibility

The simply typed λ-calculus has a property the untyped calculus lacks
spectacularly: **every reduction sequence of a well-typed term is finite**.
There is no `Ω`; every typed program terminates, whatever order of evaluation is
chosen (*strong* normalization). This was proved by W. W. Tait (1967), whose
method — later extended by Girard (1972) to System F with his "candidats de
réductibilité", and by Martin-Löf to his type theory — has become the
standard tool for such results.

**Why a naive proof fails.** One would like to prove "every typed term is
strongly normalizing" by induction on the term. The case of an application
`t u` breaks down: `t` and `u` may each terminate, yet `t u` can create a new
redex whose contraction substitutes `u` deep inside `t`, producing a larger
term. The induction hypothesis is too weak.

**Tait's idea.** Strengthen the claim, by recursion on the type, to a property
`RED A` ("reducible at type `A`") that is *closed under the elimination rule* of
`A` by definition:

* at an atom or `⊥`: `t` is strongly normalizing;
* at `A → B`: for every reducible `u` of type `A`, the application `t u` is
  reducible at `B`;
* at `A × B`: both projections are reducible;
* at `A + B`: `t` is strongly normalizing, and whatever injection it reduces to
  carries a reducible term.

One then checks Girard's three conditions — reducible terms are strongly
normalizing (CR1), reducibility is preserved by reduction (CR2), and a
*neutral* term (one that is not an introduction form) all of whose one-step
reducts are reducible is reducible (CR3) — and proves the **fundamental lemma**:
every well-typed term, with reducible terms substituted for its free variables,
is reducible. Substituting the variables themselves (which are reducible by
CR3) gives strong normalization.

Philosophically, `RED A` is a *semantics* of the type `A`: a meaning-explanation
in the style of the Brouwer–Heyting–Kolmogorov interpretation, where a proof of
`A → B` is a method transforming proofs of `A` into proofs of `B`. Normalization
is then soundness of the calculus for that semantics. Note that the definition
of `RED (A → B)` quantifies over `RED A`: the strength of the proof lies in this
quantification, which is why (by Gödel's second incompleteness theorem) such a
proof cannot be carried out in a much weaker system than the one in which `RED`
is defined.

**Consistency.** A closed term of type `⊥` would normalize to a closed normal
term of type `⊥`; but closed normal terms are values (`progress`), and no value
has type `⊥`. Read as logic (`CurryHoward.lean`), this says the calculus cannot
prove a contradiction.
**Constructive metatheory.** None of these proofs uses `Classical.choice` (and
hence none uses excluded middle): strong normalization is an accessibility
proof, and the passage to a normal form decides at each stage, with the
function `step?` of `STLC.lean`, whether another step is possible. So the
consistency of intuitionistic logic, and the unprovability of excluded middle
in `CurryHoward.lean`, are established by intuitionistically acceptable means —
as Brouwer and Heyting would have wished.
-/

namespace Foundations.Types

namespace STLC

open Term

/-! ## Strong normalization -/

/-- A term is **strongly normalizing** when every reduction sequence from it is
finite (it is accessible for the converse of `Step`). -/
def SN (t : Term) : Prop := Acc (fun t' t => Step t t') t

/-- A term all of whose one-step reducts are strongly normalizing is strongly normalizing. -/
theorem SN.intro {t : Term} (h : ∀ t', Step t t' → SN t') : SN t := Acc.intro t h

/-- Reducts of strongly normalizing terms are strongly normalizing. -/
theorem SN.step {t t' : Term} (h : SN t) (hs : Step t t') : SN t' := Acc.inv h hs

/-- If a step-preserving context `f` makes `f t` strongly normalizing, `t` is
strongly normalizing. -/
theorem SN.of_map (f : Term → Term) (hf : ∀ t t', Step t t' → Step (f t) (f t')) {t : Term}
    (h : SN (f t)) : SN t := by
  suffices ∀ s, SN s → ∀ t, f t = s → SN t from this _ h t rfl
  intro s hs
  induction hs with
  | intro s _ ih =>
    intro t ht
    subst ht
    exact SN.intro fun t' h => ih (f t') (hf _ _ h) t' rfl

/-- If every reduct of `f a` is `f a'` for a reduct `a'` of `a`, then `f` preserves
strong normalization. -/
theorem SN.map_of_inv (f : Term → Term) (hf : ∀ a x, Step (f a) x → ∃ a', x = f a' ∧ Step a a')
    {a : Term} (h : SN a) : SN (f a) := by
  induction h with
  | intro a _ ih =>
    exact SN.intro fun x hx => by
      obtain ⟨a', rfl, ha'⟩ := hf a x hx
      exact ih a' ha'

/-- The reduction-sequence version of the inversion hypothesis above. -/
theorem red_inv (f : Term → Term) (hf : ∀ a x, Step (f a) x → ∃ a', x = f a' ∧ Step a a')
    {a x : Term} (h : Red (f a) x) : ∃ a', x = f a' ∧ Red a a' := by
  induction h with
  | refl => exact ⟨a, rfl, Star.refl a⟩
  | tail _ hs ih =>
    obtain ⟨a', rfl, ha'⟩ := ih
    obtain ⟨a'', rfl, ha''⟩ := hf a' _ hs
    exact ⟨a'', rfl, ha'.tail ha''⟩

/-- Every reduct of `inl a` is `inl a'` for a reduct `a'` of `a`. -/
theorem inl_inv (a x : Term) (h : Step (inl a) x) : ∃ a', x = inl a' ∧ Step a a' := by
  cases h with
  | inl h => exact ⟨_, rfl, h⟩

/-- Every reduct of `inr a` is `inr a'` for a reduct `a'` of `a`. -/
theorem inr_inv (a x : Term) (h : Step (inr a) x) : ∃ a', x = inr a' ∧ Step a a' := by
  cases h with
  | inr h => exact ⟨_, rfl, h⟩

/-! ## Reducibility -/

/-- A term is **neutral** when it is not an introduction form: placing it in an
elimination context cannot create a new redex at the top. -/
def Neutral : Term → Prop
  | lam _ => False
  | pair _ _ => False
  | inl _ => False
  | inr _ => False
  | _ => True

/-- **Reducibility** (Tait's computability predicate), by recursion on the type. -/
def RED : Ty → Term → Prop
  | .atom _, t => SN t
  | .bot, t => SN t
  | .arr A B, t => ∀ u, RED A u → RED B (app t u)
  | .prod A B, t => RED A (fst t) ∧ RED B (snd t)
  | .sum A B, t => SN t ∧ (∀ a, Red t (inl a) → RED A a) ∧ (∀ b, Red t (inr b) → RED B b)

/-- **Girard's conditions CR1–CR3**, proved simultaneously by induction on the type:
(CR1) reducible terms are strongly normalizing; (CR2) reducibility is closed under
reduction; (CR3) a neutral term whose one-step reducts are all reducible is reducible. -/
theorem cr (A : Ty) :
    (∀ t, RED A t → SN t) ∧ (∀ t t', RED A t → Step t t' → RED A t') ∧
    (∀ t, Neutral t → (∀ t', Step t t' → RED A t') → RED A t) := by
  induction A with
  | atom n => exact ⟨fun _ h => h, fun _ _ h hs => SN.step h hs, fun _ _ h => SN.intro h⟩
  | bot => exact ⟨fun _ h => h, fun _ _ h hs => SN.step h hs, fun _ _ h => SN.intro h⟩
  | arr A B ihA ihB =>
    have hv : RED A (var 0) := ihA.2.2 (var 0) trivial (fun _ h => by cases h)
    refine ⟨fun t h => ?_, fun t t' h hs u hu => ihB.2.1 _ _ (h u hu) (Step.appL hs),
      fun t hn h u hu => ?_⟩
    · exact SN.of_map (fun t => app t (var 0)) (fun _ _ => Step.appL) (ihB.1 _ (h _ hv))
    · have hsn := ihA.1 u hu
      revert hu
      induction hsn with
      | intro u _ ih =>
        intro hu
        refine ihB.2.2 _ (by exact trivial) ?_
        intro x hx
        cases hx with
        | beta => simp [Neutral] at hn
        | appL hx => exact h _ hx u hu
        | appR hx => exact ih _ hx (ihA.2.1 _ _ hu hx)
  | prod A B ihA ihB =>
    refine ⟨fun t h => SN.of_map fst (fun _ _ => Step.fst) (ihA.1 _ h.1),
      fun t t' h hs => ⟨ihA.2.1 _ _ h.1 (Step.fst hs), ihB.2.1 _ _ h.2 (Step.snd hs)⟩,
      fun t hn h => ⟨?_, ?_⟩⟩
    · refine ihA.2.2 _ (by exact trivial) ?_
      intro x hx
      cases hx with
      | fstPair => simp [Neutral] at hn
      | fst hx => exact (h _ hx).1
    · refine ihB.2.2 _ (by exact trivial) ?_
      intro x hx
      cases hx with
      | sndPair => simp [Neutral] at hn
      | snd hx => exact (h _ hx).2
  | sum A B ihA ihB =>
    refine ⟨fun t h => h.1,
      fun t t' h hs => ⟨h.1.step hs, fun a ha => h.2.1 a (Star.head hs ha),
        fun b hb => h.2.2 b (Star.head hs hb)⟩,
      fun t hn h => ⟨SN.intro fun t' hs => (h t' hs).1, fun a ha => ?_, fun b hb => ?_⟩⟩
    · rcases ha.cases_head with rfl | ⟨x, hx, hxa⟩
      · simp [Neutral] at hn
      · exact (h x hx).2.1 a hxa
    · rcases hb.cases_head with rfl | ⟨x, hx, hxb⟩
      · simp [Neutral] at hn
      · exact (h x hx).2.2 b hxb

/-- Variables are reducible at every type (CR3: they are neutral and do not reduce). -/
theorem var_red (A : Ty) (n : Nat) : RED A (var n) :=
  (cr A).2.2 _ trivial (fun _ h => by cases h)

/-- Reducibility is closed under many-step reduction. -/
theorem red_red {A : Ty} {t t' : Term} (h : RED A t) (hs : Red t t') : RED A t' := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact (cr A).2.1 _ _ ih hs

/-- If `s[u]` is strongly normalizing for some `u`, so is `s`. -/
theorem SN.of_inst {s u : Term} (h : SN (inst s u)) : SN s :=
  SN.of_map (fun s => inst s u) (fun _ _ hs => hs.subst _) h

/-- The core of `lam_red`, by induction on the strong normalization of body and argument. -/
theorem lam_red_aux {A B : Ty} : ∀ s, SN s → ∀ u, SN u → RED A u →
    (∀ v, RED A v → RED B (inst s v)) → RED B (app (lam s) u) := by
  intro s hs
  induction hs with
  | intro s _ ihs =>
    intro u hu₀
    induction hu₀ with
    | intro u huacc ihu =>
      intro hu h
      refine (cr B).2.2 _ (by exact trivial) ?_
      intro x hx
      cases hx with
      | beta => exact h u hu
      | appL hx =>
        cases hx with
        | lam hx =>
          exact ihs _ hx u (SN.intro huacc) hu
            (fun v hv => (cr B).2.1 _ _ (h v hv) (hx.subst _))
      | appR hx => exact ihu _ hx ((cr A).2.1 _ _ hu hx) h

/-- **Abstraction is reducible** when its body is reducible under every reducible
substitution for the bound variable. -/
theorem lam_red {A B : Ty} {s : Term} (h : ∀ u, RED A u → RED B (inst s u)) :
    RED (.arr A B) (lam s) := fun u hu =>
  lam_red_aux s (SN.of_inst ((cr B).1 _ (h _ (var_red A 0)))) u ((cr A).1 _ hu) hu h

/-- The core of `pair_red`, by induction on the strong normalization of the components. -/
theorem pair_red_aux {A B : Ty} : ∀ a, SN a → ∀ b, SN b → RED A a → RED B b →
    RED (.prod A B) (pair a b) := by
  intro a hsa
  induction hsa with
  | intro a _ iha =>
    intro b hsb
    induction hsb with
    | intro b hbacc ihb =>
      intro ha hb
      constructor
      · refine (cr A).2.2 _ (by exact trivial) ?_
        intro x hx
        cases hx with
        | fstPair => exact ha
        | fst hx => cases hx with
          | pairL hx => exact (iha _ hx b (SN.intro hbacc) ((cr A).2.1 _ _ ha hx) hb).1
          | pairR hx => exact (ihb _ hx ha ((cr B).2.1 _ _ hb hx)).1
      · refine (cr B).2.2 _ (by exact trivial) ?_
        intro x hx
        cases hx with
        | sndPair => exact hb
        | snd hx => cases hx with
          | pairL hx => exact (iha _ hx b (SN.intro hbacc) ((cr A).2.1 _ _ ha hx) hb).2
          | pairR hx => exact (ihb _ hx ha ((cr B).2.1 _ _ hb hx)).2

/-- **Pairs of reducible terms are reducible.** -/
theorem pair_red {A B : Ty} {a b : Term} (ha : RED A a) (hb : RED B b) :
    RED (.prod A B) (pair a b) :=
  pair_red_aux a ((cr A).1 _ ha) b ((cr B).1 _ hb) ha hb

/-- **Left injections of reducible terms are reducible.** -/
theorem inl_red {A B : Ty} {a : Term} (ha : RED A a) : RED (.sum A B) (inl a) := by
  refine ⟨SN.map_of_inv inl inl_inv ((cr A).1 _ ha), fun a' h => ?_, fun b h => ?_⟩
  · obtain ⟨a'', he, hr⟩ := red_inv inl inl_inv h
    cases he
    exact red_red ha hr
  · obtain ⟨a'', he, _⟩ := red_inv inl inl_inv h
    cases he

/-- **Right injections of reducible terms are reducible.** -/
theorem inr_red {A B : Ty} {b : Term} (hb : RED B b) : RED (.sum A B) (inr b) := by
  refine ⟨SN.map_of_inv inr inr_inv ((cr B).1 _ hb), fun a h => ?_, fun b' h => ?_⟩
  · obtain ⟨b'', he, _⟩ := red_inv inr inr_inv h
    cases he
  · obtain ⟨b'', he, hr⟩ := red_inv inr inr_inv h
    cases he
    exact red_red hb hr

/-- The core of `case_red`, by induction on the strong normalization of the
scrutinee and of both branches. -/
theorem case_red_aux {A B C : Ty} : ∀ t, SN t → ∀ u₁, SN u₁ → ∀ u₂, SN u₂ →
    RED (.sum A B) t → (∀ a, RED A a → RED C (inst u₁ a)) →
    (∀ b, RED B b → RED C (inst u₂ b)) → RED C (case t u₁ u₂) := by
  intro t hst
  induction hst with
  | intro t _ iht =>
    intro u₁ hs₁
    induction hs₁ with
    | intro u₁ hacc₁ ih₁ =>
      intro u₂ hs₂
      induction hs₂ with
      | intro u₂ hacc₂ ih₂ =>
        intro ht h₁ h₂
        refine (cr C).2.2 _ (by exact trivial) ?_
        intro x hx
        cases hx with
        | caseInl a => exact h₁ a (ht.2.1 a (Star.refl _))
        | caseInr b => exact h₂ b (ht.2.2 b (Star.refl _))
        | case₀ hx =>
          exact iht _ hx u₁ (SN.intro hacc₁) u₂ (SN.intro hacc₂) ((cr _).2.1 _ _ ht hx) h₁ h₂
        | case₁ hx =>
          exact ih₁ _ hx u₂ (SN.intro hacc₂) ht
            (fun a ha => (cr C).2.1 _ _ (h₁ a ha) (hx.subst _)) h₂
        | case₂ hx =>
          exact ih₂ _ hx ht h₁ (fun b hb => (cr C).2.1 _ _ (h₂ b hb) (hx.subst _))

/-- **Case analysis is reducible** when the scrutinee is reducible and both branches
are reducible under every reducible substitution. -/
theorem case_red {A B C : Ty} {t u₁ u₂ : Term} (ht : RED (.sum A B) t)
    (h₁ : ∀ a, RED A a → RED C (inst u₁ a)) (h₂ : ∀ b, RED B b → RED C (inst u₂ b)) :
    RED C (case t u₁ u₂) :=
  case_red_aux t ht.1 u₁ (SN.of_inst ((cr C).1 _ (h₁ _ (var_red A 0))))
    u₂ (SN.of_inst ((cr C).1 _ (h₂ _ (var_red B 0)))) ht h₁ h₂

/-- **Ex falso is reducible** on a reducible term of the empty type. -/
theorem absurd_red {C : Ty} {t : Term} (ht : RED .bot t) : RED C (.absurd t) := by
  have hst : SN t := ht
  clear ht
  induction hst with
  | intro t _ ih =>
    refine (cr C).2.2 _ (by exact trivial) ?_
    intro x hx
    cases hx with
    | absurd hx => exact ih _ hx

/-- **The fundamental lemma of logical relations.** A well-typed term with
reducible terms substituted for its free variables is reducible. -/
theorem fundamental {Γ : Ctx} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ σ, (∀ n B, Γ[n]? = some B → RED B (σ n)) → RED A (subst σ t) := by
  have hcons : ∀ {Γ : Ctx} {A : Ty} {σ : Nat → Term} {u : Term},
      (∀ n B, Γ[n]? = some B → RED B (σ n)) → RED A u →
      ∀ n B, (A :: Γ)[n]? = some B → RED B (cons u σ n) := by
    intro Γ A σ u hσ hu n B hn
    cases n with
    | zero => simp at hn; subst hn; exact hu
    | succ n => exact hσ n B (by simpa using hn)
  induction h with
  | var hn => intro σ hσ; exact hσ _ _ hn
  | lam _ ih =>
    intro σ hσ
    exact lam_red fun u hu => by rw [inst_up]; exact ih _ (hcons hσ hu)
  | app _ _ ih₁ ih₂ => intro σ hσ; exact ih₁ σ hσ _ (ih₂ σ hσ)
  | pair _ _ ih₁ ih₂ => intro σ hσ; exact pair_red (ih₁ σ hσ) (ih₂ σ hσ)
  | fst _ ih => intro σ hσ; exact (ih σ hσ).1
  | snd _ ih => intro σ hσ; exact (ih σ hσ).2
  | inl _ ih => intro σ hσ; exact inl_red (ih σ hσ)
  | inr _ ih => intro σ hσ; exact inr_red (ih σ hσ)
  | case _ _ _ ih ih₁ ih₂ =>
    intro σ hσ
    exact case_red (ih σ hσ)
      (fun a ha => by rw [inst_up]; exact ih₁ _ (hcons hσ ha))
      (fun b hb => by rw [inst_up]; exact ih₂ _ (hcons hσ hb))
  | absurd _ ih => intro σ hσ; exact absurd_red (ih σ hσ)

/-- **Strong normalization** (Tait 1967). Every well-typed term of the simply
typed λ-calculus is strongly normalizing: all its reduction sequences are finite. -/
theorem strong_normalization {Γ : Ctx} {t : Term} {A : Ty} (h : HasType Γ t A) : SN t := by
  have := fundamental h var (fun n B _ => var_red B n)
  rw [subst_var] at this
  exact (cr A).1 _ this

/-- A strongly normalizing term has a normal form. The proof is constructive: at
each stage `step?` decides whether a further step is possible. -/
theorem SN.normalizes {t : Term} (h : SN t) : ∃ n, Red t n ∧ Normal n := by
  induction h with
  | intro t _ ih =>
    cases hs : step? t with
    | some t' =>
      have ht' := step?_sound _ _ hs
      obtain ⟨n, hn, hn'⟩ := ih t' ht'
      exact ⟨n, Star.head ht' hn, hn'⟩
    | none => exact ⟨t, Star.refl t, (normal_iff_step?_none t).2 hs⟩

/-- **Weak normalization.** Every well-typed term reduces to a well-typed normal form
of the same type. -/
theorem weak_normalization {Γ : Ctx} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∃ n, Red t n ∧ Normal n ∧ HasType Γ n A := by
  obtain ⟨n, hn, hn'⟩ := (strong_normalization h).normalizes
  exact ⟨n, hn, hn', subject_reduction_red hn h⟩

/-- **Consistency of the simply typed λ-calculus.** The empty type has no closed
inhabitant. -/
theorem no_closed_bot : ¬ ∃ t, HasType [] t .bot := by
  rintro ⟨t, ht⟩
  obtain ⟨n, _, hn, hnt⟩ := weak_normalization ht
  have hv := normal_closed_isValue hnt hn
  cases hnt <;> simp [IsValue] at hv

/-- No atomic type has a closed inhabitant either. -/
theorem no_closed_atom (k : Nat) : ¬ ∃ t, HasType [] t (.atom k) := by
  rintro ⟨t, ht⟩
  obtain ⟨n, _, hn, hnt⟩ := weak_normalization ht
  have hv := normal_closed_isValue hnt hn
  cases hnt <;> simp [IsValue] at hv

end STLC

end Foundations.Types
