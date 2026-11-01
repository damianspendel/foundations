/-!
# Complete Boolean algebras

## Why truth values other than "true" and "false"?

In 1938 Kurt Gödel showed that the Continuum Hypothesis (CH: every infinite set of reals
is either countable or of the size of ℝ) cannot be *refuted* from the axioms of ZF set
theory with choice: inside any model of ZF he carved out the *constructible universe* `L`,
in which both choice and CH hold. In 1963 Paul Cohen proved the converse, that CH cannot be
*proved* either. His method, **forcing**, enlarges a model by adjoining a "generic" object
whose properties are decided only piecemeal, by finite pieces of information called
*conditions*.

Shortly afterwards Dana Scott and Robert Solovay, and independently Petr Vopěnka,
recast forcing as a semantics with many truth values. Instead of asking whether a sentence
is true in a model, one computes its **Boolean truth value** `⟦φ⟧`, an element of a complete
Boolean algebra `B`. The sentence "holds" in the Boolean-valued model when `⟦φ⟧ = ⊤`. If
`B` is the two-element algebra this is ordinary Tarskian semantics. For richer `B`, the
quantifiers become infinite meets and joins, which is why *completeness* (every family has a
supremum and an infimum) is required.

This file sets up complete Boolean algebras from scratch (there is no Mathlib here) and
proves the small lemma library the rest of the `Forcing` part needs: lattice laws,
complements, the Heyting implication `a ⇨ b = aᶜ ⊔ b` with its adjunction
`c ≤ a ⇨ b ↔ c ⊓ a ≤ b`, and **infinite distributivity** `a ⊓ ⨆ᵢ bᵢ = ⨆ᵢ (a ⊓ bᵢ)`, which is
what makes the existential quantifier behave.

The notation `⊓ ⊔ ᶜ ⊤ ⊥ ⇨ ⇔` is *scoped* to the namespace `Foundations.Forcing`, so it does
not clash with anything elsewhere in the library.
-/

namespace Foundations.Forcing

universe u v

/-- **Complete Boolean algebra.** A partial order with binary meets `inf` and joins `sup`,
a complement `compl`, top and bottom, and meets `sInf` and joins `sSup` of *arbitrary*
families (given as predicates `B → Prop`). The lattice is required to be distributive and
complements are required to be genuine complements (`a ⊓ aᶜ = ⊥`, `a ⊔ aᶜ = ⊤`). -/
class CompleteBooleanAlgebra (B : Type u) extends LE B where
  /-- Binary meet ("and"). -/
  inf : B → B → B
  /-- Binary join ("or"). -/
  sup : B → B → B
  /-- Complement ("not"). -/
  compl : B → B
  /-- The top element ("true"). -/
  top : B
  /-- The bottom element ("false"). -/
  bot : B
  /-- The join of an arbitrary family. -/
  sSup : (B → Prop) → B
  /-- The meet of an arbitrary family. -/
  sInf : (B → Prop) → B
  /-- Reflexivity of the order. -/
  le_refl : ∀ a : B, a ≤ a
  /-- Transitivity of the order. -/
  le_trans : ∀ a b c : B, a ≤ b → b ≤ c → a ≤ c
  /-- Antisymmetry of the order. -/
  le_antisymm : ∀ a b : B, a ≤ b → b ≤ a → a = b
  /-- A meet lies below its left argument. -/
  inf_le_left : ∀ a b : B, inf a b ≤ a
  /-- A meet lies below its right argument. -/
  inf_le_right : ∀ a b : B, inf a b ≤ b
  /-- A meet is the greatest lower bound. -/
  le_inf : ∀ a b c : B, a ≤ b → a ≤ c → a ≤ inf b c
  /-- A join lies above its left argument. -/
  le_sup_left : ∀ a b : B, a ≤ sup a b
  /-- A join lies above its right argument. -/
  le_sup_right : ∀ a b : B, b ≤ sup a b
  /-- A join is the least upper bound. -/
  sup_le : ∀ a b c : B, a ≤ c → b ≤ c → sup a b ≤ c
  /-- `top` is the greatest element. -/
  le_top : ∀ a : B, a ≤ top
  /-- `bot` is the least element. -/
  bot_le : ∀ a : B, bot ≤ a
  /-- `sSup S` is an upper bound of `S`. -/
  le_sSup : ∀ (S : B → Prop) (a : B), S a → a ≤ sSup S
  /-- `sSup S` is the least upper bound of `S`. -/
  sSup_le : ∀ (S : B → Prop) (a : B), (∀ b, S b → b ≤ a) → sSup S ≤ a
  /-- `sInf S` is a lower bound of `S`. -/
  sInf_le : ∀ (S : B → Prop) (a : B), S a → sInf S ≤ a
  /-- `sInf S` is the greatest lower bound of `S`. -/
  le_sInf : ∀ (S : B → Prop) (a : B), (∀ b, S b → a ≤ b) → a ≤ sInf S
  /-- Distributivity of meet over join. -/
  inf_sup_le : ∀ a b c : B, inf a (sup b c) ≤ sup (inf a b) (inf a c)
  /-- A element and its complement are disjoint. -/
  inf_compl_le_bot : ∀ a : B, inf a (compl a) ≤ bot
  /-- An element and its complement cover everything. -/
  top_le_sup_compl : ∀ a : B, top ≤ sup a (compl a)

namespace CBA

open CompleteBooleanAlgebra

@[inherit_doc] scoped infixl:69 " ⊓ " => CompleteBooleanAlgebra.inf
@[inherit_doc] scoped infixl:68 " ⊔ " => CompleteBooleanAlgebra.sup
@[inherit_doc] scoped postfix:max "ᶜ" => CompleteBooleanAlgebra.compl
@[inherit_doc] scoped notation "⊤" => CompleteBooleanAlgebra.top
@[inherit_doc] scoped notation "⊥" => CompleteBooleanAlgebra.bot

variable {B : Type u} [CompleteBooleanAlgebra B] {a b c d : B}

/-- Reflexivity of `≤`. -/
@[simp] theorem le_rfl : a ≤ a := le_refl a
/-- Transitivity of `≤`. -/
theorem le_trans' (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := le_trans a b c h₁ h₂
/-- Antisymmetry of `≤`. -/
theorem le_antisymm' (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := le_antisymm a b h₁ h₂
/-- `≤` chains in `calc` blocks. -/
instance : @Trans B B B LE.le LE.le LE.le := ⟨fun h₁ h₂ => le_trans _ _ _ h₁ h₂⟩
/-- `⊤` is the greatest element. -/
@[simp] theorem le_top' : a ≤ ⊤ := le_top a
/-- `⊥` is the least element. -/
@[simp] theorem bot_le' : ⊥ ≤ a := bot_le a

/-- An element equals `⊤` iff it lies above `⊤`. -/
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
  ⟨fun h => h ▸ le_rfl, fun h => le_antisymm' le_top' h⟩

/-- An element equals `⊥` iff it lies below `⊥`. -/
theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
  ⟨fun h => h ▸ le_rfl, fun h => le_antisymm' h bot_le'⟩

/-- The universal property of the meet. -/
theorem le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
  ⟨fun h => ⟨le_trans' h (inf_le_left _ _), le_trans' h (inf_le_right _ _)⟩,
   fun h => le_inf _ _ _ h.1 h.2⟩

/-- The universal property of the join. -/
theorem sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h => ⟨le_trans' (le_sup_left _ _) h, le_trans' (le_sup_right _ _) h⟩,
   fun h => sup_le _ _ _ h.1 h.2⟩

/-- Weakening on the left of a meet. -/
theorem inf_le_of_left_le (h : a ≤ c) : a ⊓ b ≤ c := le_trans' (inf_le_left _ _) h
/-- Weakening on the right of a meet. -/
theorem inf_le_of_right_le (h : b ≤ c) : a ⊓ b ≤ c := le_trans' (inf_le_right _ _) h
/-- Landing in the left of a join. -/
theorem le_sup_of_le_left (h : a ≤ b) : a ≤ b ⊔ c := le_trans' h (le_sup_left _ _)
/-- Landing in the right of a join. -/
theorem le_sup_of_le_right (h : a ≤ c) : a ≤ b ⊔ c := le_trans' h (le_sup_right _ _)

/-- Meet is monotone in both arguments. -/
theorem inf_le_inf (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
  le_inf _ _ _ (inf_le_of_left_le h₁) (inf_le_of_right_le h₂)

/-- Join is monotone in both arguments. -/
theorem sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
  sup_le _ _ _ (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)

/-- Meet is commutative. -/
theorem inf_comm : a ⊓ b = b ⊓ a :=
  le_antisymm' (le_inf _ _ _ (inf_le_right _ _) (inf_le_left _ _))
    (le_inf _ _ _ (inf_le_right _ _) (inf_le_left _ _))

/-- Join is commutative. -/
theorem sup_comm : a ⊔ b = b ⊔ a :=
  le_antisymm' (sup_le _ _ _ (le_sup_right _ _) (le_sup_left _ _))
    (sup_le _ _ _ (le_sup_right _ _) (le_sup_left _ _))

/-- Meet is associative. -/
theorem inf_assoc : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
  le_antisymm'
    (le_inf _ _ _ (inf_le_of_left_le (inf_le_left _ _))
      (inf_le_inf (inf_le_right _ _) le_rfl))
    (le_inf _ _ _ (inf_le_inf le_rfl (inf_le_left _ _))
      (inf_le_of_right_le (inf_le_right _ _)))

/-- Meet with `⊤` does nothing. -/
@[simp] theorem inf_top : a ⊓ ⊤ = a := le_antisymm' (inf_le_left _ _) (le_inf _ _ _ le_rfl le_top')
/-- Meet with `⊤` on the left does nothing. -/
@[simp] theorem top_inf : ⊤ ⊓ a = a := by rw [inf_comm]; exact inf_top
/-- Meet is idempotent. -/
@[simp] theorem inf_idem : a ⊓ a = a := le_antisymm' (inf_le_left _ _) (le_inf _ _ _ le_rfl le_rfl)

/-- Distributivity, with the meet on the right. -/
theorem sup_inf_le : (b ⊔ c) ⊓ a ≤ (b ⊓ a) ⊔ (c ⊓ a) := by
  rw [inf_comm, @inf_comm _ _ b, @inf_comm _ _ c]; exact inf_sup_le _ _ _

/-- `a ⊓ aᶜ ≤ ⊥`. -/
theorem inf_compl_le : a ⊓ aᶜ ≤ ⊥ := inf_compl_le_bot a
/-- `⊤ ≤ a ⊔ aᶜ`. -/
theorem top_le_sup_compl' : ⊤ ≤ a ⊔ aᶜ := top_le_sup_compl a

/-! ### Heyting implication -/

/-- **Implication** in a Boolean algebra: `a ⇨ b = aᶜ ⊔ b`. -/
def himp (a b : B) : B := aᶜ ⊔ b

@[inherit_doc] scoped infixr:60 " ⇨ " => himp

/-- **Residuation (the deduction theorem for truth values).** `c ≤ a ⇨ b` iff
`c ⊓ a ≤ b`. -/
theorem le_himp_iff : c ≤ a ⇨ b ↔ c ⊓ a ≤ b := by
  constructor
  · intro h
    calc c ⊓ a ≤ (aᶜ ⊔ b) ⊓ a := inf_le_inf h le_rfl
      _ ≤ (aᶜ ⊓ a) ⊔ (b ⊓ a) := sup_inf_le
      _ ≤ b := sup_le _ _ _
          (le_trans' (by rw [inf_comm]; exact inf_compl_le) bot_le') (inf_le_left _ _)
  · intro h
    calc c ≤ c ⊓ (a ⊔ aᶜ) := le_inf _ _ _ le_rfl (le_trans' le_top' top_le_sup_compl')
      _ ≤ (c ⊓ a) ⊔ (c ⊓ aᶜ) := inf_sup_le _ _ _
      _ ≤ aᶜ ⊔ b := sup_le _ _ _ (le_sup_of_le_right h) (le_sup_of_le_left (inf_le_right _ _))

/-- Modus ponens for truth values: `(a ⇨ b) ⊓ a ≤ b`. -/
theorem himp_inf_le : (a ⇨ b) ⊓ a ≤ b := le_himp_iff.1 le_rfl

/-- Modus ponens, other order: `a ⊓ (a ⇨ b) ≤ b`. -/
theorem inf_himp_le : a ⊓ (a ⇨ b) ≤ b := by rw [inf_comm]; exact himp_inf_le

/-- `a ⇨ b = ⊤` iff `a ≤ b`. -/
theorem himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b := by
  rw [eq_top_iff, le_himp_iff, top_inf]

/-- `b ≤ a ⇨ b`. -/
theorem le_himp : b ≤ a ⇨ b := le_sup_right _ _

/-- Implication is antitone in its first argument and monotone in its second. -/
theorem himp_le_himp (h₁ : c ≤ a) (h₂ : b ≤ d) : a ⇨ b ≤ c ⇨ d :=
  le_himp_iff.2 (le_trans' (inf_le_inf le_rfl h₁) (le_trans' himp_inf_le h₂))

/-! ### Complements -/

/-- Complements are unique: if `a ⊓ b ≤ ⊥` and `⊤ ≤ a ⊔ b` then `b = aᶜ`. -/
theorem le_compl_of_inf_le_bot (h : b ⊓ a ≤ ⊥) : b ≤ aᶜ := by
  have : b ≤ a ⇨ ⊥ := le_himp_iff.2 h
  exact le_trans' this (sup_le _ _ _ le_rfl bot_le')

/-- `aᶜ ⊓ a ≤ ⊥`. -/
theorem compl_inf_le : aᶜ ⊓ a ≤ ⊥ := by rw [inf_comm]; exact inf_compl_le

/-- The complement equals `a ⇨ ⊥`. -/
theorem compl_eq_himp_bot : aᶜ = a ⇨ ⊥ :=
  le_antisymm' (le_sup_left _ _) (sup_le _ _ _ le_rfl bot_le')

/-- `b ≤ aᶜ ↔ b ⊓ a ≤ ⊥`. -/
theorem le_compl_iff : b ≤ aᶜ ↔ b ⊓ a ≤ ⊥ := by rw [compl_eq_himp_bot]; exact le_himp_iff

/-- Double complement. -/
@[simp] theorem compl_compl : aᶜᶜ = a := by
  apply le_antisymm'
  · calc aᶜᶜ ≤ aᶜᶜ ⊓ (a ⊔ aᶜ) := le_inf _ _ _ le_rfl (le_trans' le_top' top_le_sup_compl')
      _ ≤ (aᶜᶜ ⊓ a) ⊔ (aᶜᶜ ⊓ aᶜ) := inf_sup_le _ _ _
      _ ≤ a := sup_le _ _ _ (inf_le_right _ _) (le_trans' compl_inf_le bot_le')
  · exact le_compl_iff.2 inf_compl_le

/-- Complement is antitone. -/
theorem compl_le_compl (h : a ≤ b) : bᶜ ≤ aᶜ :=
  le_compl_iff.2 (le_trans' (inf_le_inf le_rfl h) compl_inf_le)

/-- Contraposition: `aᶜ ≤ b ↔ bᶜ ≤ a`. -/
theorem compl_le_iff : aᶜ ≤ b ↔ bᶜ ≤ a :=
  ⟨fun h => by have := compl_le_compl h; rwa [compl_compl] at this,
   fun h => by have := compl_le_compl h; rwa [compl_compl] at this⟩

/-- Classical reasoning for truth values: if `c ⊓ aᶜ ≤ ⊥` then `c ≤ a`. -/
theorem le_of_inf_compl_le_bot (h : c ⊓ aᶜ ≤ ⊥) : c ≤ a := by
  have := le_compl_iff.2 h; rwa [compl_compl] at this

/-- `a ≤ b` iff `a ⊓ bᶜ ≤ ⊥`. -/
theorem le_iff_inf_compl_le_bot : a ≤ b ↔ a ⊓ bᶜ ≤ ⊥ :=
  ⟨fun h => le_trans' (inf_le_inf h le_rfl) inf_compl_le, le_of_inf_compl_le_bot⟩

/-! ### Biimplication -/

/-- **Biimplication** `a ⇔ b = (a ⇨ b) ⊓ (b ⇨ a)`. -/
def biimp (a b : B) : B := (a ⇨ b) ⊓ (b ⇨ a)

@[inherit_doc] scoped infix:59 " ⇔ " => biimp

/-- Biimplication is symmetric. -/
theorem biimp_comm : a ⇔ b = b ⇔ a := inf_comm

/-! ### Arbitrary meets and joins of indexed families -/

/-- The join `⨆ᵢ f i` of an indexed family. -/
def iSup {ι : Sort v} (f : ι → B) : B := sSup fun b => ∃ i, f i = b

/-- The meet `⨅ᵢ f i` of an indexed family. -/
def iInf {ι : Sort v} (f : ι → B) : B := sInf fun b => ∃ i, f i = b

variable {ι : Sort v} {f g : ι → B}

/-- Each member lies below the join. -/
theorem le_iSup (f : ι → B) (i : ι) : f i ≤ iSup f := le_sSup _ _ ⟨i, rfl⟩

/-- The join is the least upper bound. -/
theorem iSup_le (h : ∀ i, f i ≤ a) : iSup f ≤ a := sSup_le _ _ fun _ ⟨i, hi⟩ => hi ▸ h i

/-- The meet lies below each member. -/
theorem iInf_le (f : ι → B) (i : ι) : iInf f ≤ f i := sInf_le _ _ ⟨i, rfl⟩

/-- The meet is the greatest lower bound. -/
theorem le_iInf (h : ∀ i, a ≤ f i) : a ≤ iInf f := le_sInf _ _ fun _ ⟨i, hi⟩ => hi ▸ h i

/-- Universal property of `iSup`. -/
theorem iSup_le_iff : iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  ⟨fun h i => le_trans' (le_iSup f i) h, iSup_le⟩

/-- Universal property of `iInf`. -/
theorem le_iInf_iff : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  ⟨fun h i => le_trans' h (iInf_le f i), le_iInf⟩

/-- Landing below a member suffices to land below the join. -/
theorem le_iSup_of_le (i : ι) (h : a ≤ f i) : a ≤ iSup f := le_trans' h (le_iSup f i)

/-- Lying above a member suffices for the meet. -/
theorem iInf_le_of_le (i : ι) (h : f i ≤ a) : iInf f ≤ a := le_trans' (iInf_le f i) h

/-- `iSup` is monotone. -/
theorem iSup_mono (h : ∀ i, f i ≤ g i) : iSup f ≤ iSup g :=
  iSup_le fun i => le_iSup_of_le i (h i)

/-- `iInf` is monotone. -/
theorem iInf_mono (h : ∀ i, f i ≤ g i) : iInf f ≤ iInf g :=
  le_iInf fun i => iInf_le_of_le i (h i)

/-- **Infinite distributivity.** `a ⊓ ⨆ᵢ f i ≤ ⨆ᵢ (a ⊓ f i)`; the reverse inequality is
automatic. This is the law behind the soundness of `∃`-elimination. -/
theorem inf_iSup_le : a ⊓ iSup f ≤ iSup (fun i => a ⊓ f i) := by
  have : iSup f ≤ a ⇨ iSup (fun i => a ⊓ f i) :=
    iSup_le fun i => le_himp_iff.2 (by rw [inf_comm]; exact le_iSup (fun i => a ⊓ f i) i)
  rw [inf_comm]; exact le_himp_iff.1 this

/-- Infinite distributivity, with the meet on the right. -/
theorem iSup_inf_le : iSup f ⊓ a ≤ iSup (fun i => f i ⊓ a) := by
  rw [inf_comm]
  exact le_trans' inf_iSup_le (iSup_mono fun i => by rw [inf_comm]; exact le_rfl)

/-- Join of a constant family over an inhabited index is that constant (one inequality). -/
theorem le_iSup_const (i : ι) : a ≤ iSup (fun _ : ι => a) := le_iSup_of_le i le_rfl

/-- **The complement of a join is the meet of the complements** (de Morgan, one
inequality, which is the one needed below). -/
theorem compl_iSup_le : (iSup f)ᶜ ≤ iInf (fun i => (f i)ᶜ) :=
  le_iInf fun i => compl_le_compl (le_iSup f i)

/-- The complement of a meet lies below the join of the complements (de Morgan). -/
theorem compl_iInf_le : (iInf f)ᶜ ≤ iSup (fun i => (f i)ᶜ) := by
  rw [compl_le_iff]
  exact le_iInf fun i => by
    have := compl_le_compl (le_iSup (fun i => (f i)ᶜ) i)
    rwa [compl_compl] at this

/- Make the basic lattice axioms available to every file that opens `CBA`. -/
export CompleteBooleanAlgebra (inf_le_left inf_le_right le_inf le_sup_left le_sup_right sup_le
  inf_sup_le le_sSup sSup_le sInf_le le_sInf)

end CBA

end Foundations.Forcing

namespace Foundations.Forcing.CBA

/-- `lattice_le` closes goals `a₁ ⊓ … ⊓ aₙ ≤ b₁ ⊓ … ⊓ bₘ` in which every `bⱼ` occurs among the
`aᵢ` (up to the associativity and commutativity of `⊓`), by splitting the right-hand side
and projecting from the left-hand side. -/
scoped syntax "lattice_le" : tactic

macro_rules
  | `(tactic| lattice_le) => `(tactic| first
      | exact le_rfl
      | exact le_top'
      | (apply le_inf <;> lattice_le)
      | (apply inf_le_of_left_le; lattice_le)
      | (apply inf_le_of_right_le; lattice_le))

end Foundations.Forcing.CBA
