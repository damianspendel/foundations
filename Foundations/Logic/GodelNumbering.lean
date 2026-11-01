import Foundations.Logic.Computability

/-!
# Gödel numbering of codes

Gödel's decisive technical idea (1931) was to **represent syntax by numbers**:
formulas, proofs — and, for us, algorithms — are finite objects and can be coded
as natural numbers in such a way that the code determines the object. Programs can
then take (the numbers of) programs as input, which makes self-reference possible.

We encode each code by a number using Cantor's pairing function (a tag for the
constructor, paired with the numbers of the components), prove that this
**Gödel numbering is injective** and admits a decoding, and then show that the
encoding is itself *computable* in the sense that matters: there are codes which,
given numbers of codes as input, output the numbers of new codes built from them.
In particular

* `constEncCode` computes, from `x`, the number of the constant-`x` code;
* `rhoCode a` computes, from `⌜c⌝` and `x`, the number of a code that first runs `c`
  on `x` and then behaves like `a`.

This "programs computing programs" machinery is a special case of Kleene's
s-m-n theorem, and is what Rice's theorem needs.
-/

namespace Foundations.Logic.Computability

open Code

/-- Encoding a list of numbers as a single number. -/
def encList : List Nat → Nat
  | [] => 0
  | x :: l => pair x (encList l) + 1

/-- List encoding is injective. -/
theorem encList_inj : ∀ {l l' : List Nat}, encList l = encList l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encList] at h
  | _ :: _, [], h => by simp [encList] at h
  | x :: l, x' :: l', h => by
      simp only [encList, Nat.add_right_cancel_iff] at h
      obtain ⟨h₁, h₂⟩ := pair_inj h
      rw [h₁, encList_inj h₂]

/-- **Gödel numbering of codes.** Each constructor gets a tag `0–5`, paired with the
numbers of its components. -/
def encode : Code → Nat
  | .zero => pair 0 0
  | .succ => pair 1 0
  | .proj i => pair 2 i
  | .comp f gs => pair 3 (pair (encode f) (encList (List.ofFn fun i => encode (gs i))))
  | .prec f g => pair 4 (pair (encode f) (encode g))
  | .mu f => pair 5 (encode f)

/-- **The Gödel numbering is injective**: distinct codes have distinct numbers. -/
theorem encode_inj : ∀ {c c' : Code}, encode c = encode c' → c = c' := by
  intro c
  induction c with
  | zero => intro c' h; cases c' <;> simp only [encode] at h <;>
      first | rfl | (have := (pair_inj h).1; omega)
  | succ => intro c' h; cases c' <;> simp only [encode] at h <;>
      first | rfl | (have := (pair_inj h).1; omega)
  | proj i => intro c' h; cases c' <;> simp only [encode] at h <;>
      first | (have := (pair_inj h).1; omega) | (rw [(pair_inj h).2])
  | @comp k f gs ihf ihg =>
      intro c' h
      cases c' with
      | @comp k' f' gs' =>
          simp only [encode] at h
          obtain ⟨h₁, h₂⟩ := pair_inj (pair_inj h).2
          have hf := ihf h₁
          have hl := encList_inj h₂
          have hk : k = k' := by simpa using congrArg List.length hl
          subst hk hf
          have : gs = gs' := funext fun i => ihg i (by
            have := congrArg (fun l => l[i.val]?) hl
            simpa using this)
          rw [this]
      | _ => simp only [encode] at h; have := (pair_inj h).1; omega
  | prec f g ihf ihg =>
      intro c' h
      cases c' with
      | prec f' g' =>
          simp only [encode] at h
          obtain ⟨h₁, h₂⟩ := pair_inj (pair_inj h).2
          rw [ihf h₁, ihg h₂]
      | _ => simp only [encode] at h; have := (pair_inj h).1; omega
  | mu f ih =>
      intro c' h
      cases c' with
      | mu f' => simp only [encode] at h; rw [ih (pair_inj h).2]
      | _ => simp only [encode] at h; have := (pair_inj h).1; omega

/-- Decoding: the code with a given number (an arbitrary default if there is none). -/
noncomputable def decode (n : Nat) : Code :=
  open Classical in if h : ∃ c, encode c = n then Classical.choose h else .zero

/-- **Decoding inverts the Gödel numbering.** -/
theorem decode_encode (c : Code) : decode (encode c) = c := by
  have h : ∃ c', encode c' = encode c := ⟨c, rfl⟩
  simp only [decode, h, dite_true]
  exact encode_inj (Classical.choose_spec h)

/-- The number of a composition with one inner function. -/
theorem encode_comp1 (f g : Code) :
    encode (.comp f (vec1 g)) = pair 3 (pair (encode f) (pair (encode g) 0 + 1)) := rfl

/-- The number of a composition with two inner functions. -/
theorem encode_comp2 (f g h : Code) : encode (.comp f (vec2 g h)) =
    pair 3 (pair (encode f) (pair (encode g) (pair (encode h) 0 + 1) + 1)) := rfl

/-! ## Codes computing code numbers -/

/-- `pairOf g h` computes `⟨g(x⃗), h(x⃗)⟩`. -/
abbrev pairOf (g h : Code) : Code := .comp pairCode (vec2 g h)

/-- `succOf g` computes `g(x⃗) + 1`. -/
abbrev succOf (g : Code) : Code := .comp .succ (vec1 g)

/-- Evaluating `pairOf`. -/
theorem eval_pairOf {g h : Code} {xs : List Nat} {a b : Nat} (hg : Eval g xs a)
    (hh : Eval h xs b) : Eval (pairOf g h) xs (pair a b) :=
  eval_comp2 hg hh (eval_pair a b [])

/-- Evaluating `succOf`. -/
theorem eval_succOf {g : Code} {xs : List Nat} {a : Nat} (hg : Eval g xs a) :
    Eval (succOf g) xs (a + 1) :=
  eval_comp1 hg .succ

/-- A code computing, from `x`, the Gödel number of `constCode x`. -/
def constEncCode : Code :=
  .prec (constCode (encode .zero))
    (pairOf (constCode 3) (pairOf (constCode (encode .succ))
      (succOf (pairOf (.proj 1) (constCode 0)))))

/-- `constEncCode` computes the numbers of the constant codes. -/
theorem eval_constEnc (xs : List Nat) : ∀ x, Eval constEncCode (x :: xs) (encode (constCode x))
  | 0 => Eval.prec_zero (eval_const xs _)
  | x + 1 => by
      refine Eval.prec_succ (eval_constEnc xs x) ?_
      show Eval _ _ (encode (.comp .succ (vec1 (constCode x))))
      rw [encode_comp1]
      exact eval_pairOf (eval_const _ 3) (eval_pairOf (eval_const _ _)
        (eval_succOf (eval_pairOf .proj (eval_const _ 0))))

/-- **Run `c` on `x`, then behave like `a`.** On input `y`, this code first computes
`c(x)` (diverging if that diverges), discards the result, and returns `a(y)`. -/
def rho (a c : Code) (x : Nat) : Code :=
  .comp (.proj 1) (vec2 (.comp c (vec1 (constCode x))) (.comp a (vec1 (.proj 0))))

/-- A code computing `⌜rho a c x⌝` from `⌜c⌝` and `x` (an instance of the s-m-n
theorem: the code of `c` appears as *data*, it is never run). -/
def rhoCode (a : Code) : Code :=
  pairOf (constCode 3) (pairOf (constCode (encode (.proj 1)))
    (succOf (pairOf
      (pairOf (constCode 3) (pairOf (.proj 0)
        (succOf (pairOf (.comp constEncCode (vec1 (.proj 1))) (constCode 0)))))
      (succOf (pairOf (constCode (encode (.comp a (vec1 (.proj 0))))) (constCode 0))))))

/-- `rhoCode a` computes the Gödel number of `rho a c x`. -/
theorem eval_rhoCode (a c : Code) (x : Nat) :
    Eval (rhoCode a) [encode c, x] (encode (rho a c x)) := by
  simp only [rho, encode_comp2, encode_comp1]
  exact eval_pairOf (eval_const _ 3) (eval_pairOf (eval_const _ _) (eval_succOf (eval_pairOf
    (eval_pairOf (eval_const _ 3) (eval_pairOf .proj (eval_succOf (eval_pairOf
      (eval_comp1 .proj (eval_constEnc [] x)) (eval_const _ 0)))))
    (eval_succOf (eval_pairOf (eval_const _ _) (eval_const _ 0))))))

end Foundations.Logic.Computability
