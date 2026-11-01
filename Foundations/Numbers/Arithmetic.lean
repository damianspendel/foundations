import Foundations.Numbers.Int

/-!
# Elementary number theory: Euclid's legacy

Before moving on from the whole numbers to fractions, we pause to prove the classical results of
*arithmetic* in Euclid's *Elements* (Books VII and IX), now on a fully formal footing. Thanks to
the bridge theorems `N.bridge_nat` and `Z.bridge_int` we work with Lean's `Nat` and `Int`.

* **Euclid's algorithm** computes the greatest common divisor by repeated division with
  remainder: `gcd a 0 = a` and `gcd a b = gcd b (a mod b)`. We prove that it really is the
  greatest common divisor.
* **Bézout's identity**: the gcd of `a` and `b` is an integer combination `a·x + b·y`. This is
  where negative numbers earn their keep.
* **Euclid's lemma**: a prime dividing a product divides one of the factors. This is what makes
  primes the "atoms" of multiplication.
* **Infinitude of primes** (Euclid IX.20): for every `n` there is a prime `p ≥ n`, found among the
  prime factors of `n! + 1`.
* **The fundamental theorem of arithmetic**: every positive integer is a product of primes, in
  exactly one way up to the order of the factors. Factorisations are represented as lists of
  primes, and "up to order" means "up to permutation of the list".
-/

namespace Foundations.Numbers

namespace Arith

/-! ## Euclid's algorithm -/

/-- **Euclid's algorithm** for the greatest common divisor: `gcd a 0 = a`, and otherwise
`gcd a b = gcd b (a mod b)`. It terminates because the second argument strictly decreases. -/
def gcd : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => gcd (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

/-- Defining equation of Euclid's algorithm: `gcd a 0 = a`. -/
theorem gcd_zero (a : Nat) : gcd a 0 = a := by simp [gcd]

/-- Defining equation of Euclid's algorithm: `gcd a b = gcd b (a mod b)` for `b > 0`. -/
theorem gcd_succ (a b : Nat) : gcd a (b + 1) = gcd (b + 1) (a % (b + 1)) := by
  rw [gcd]

/-- The gcd divides both arguments. -/
theorem gcd_dvd (a b : Nat) : gcd a b ∣ a ∧ gcd a b ∣ b := by
  induction a, b using gcd.induct with
  | case1 a => rw [gcd_zero]; exact ⟨Nat.dvd_refl a, Nat.dvd_zero a⟩
  | case2 a b ih =>
    rw [gcd_succ]
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, h1⟩
    have := Nat.mod_add_div a (b + 1)
    have h3 := Nat.dvd_add h2 (Nat.dvd_mul_right_of_dvd h1 (a / (b + 1)))
    rwa [this] at h3

/-- Every common divisor divides the gcd: so the gcd is the *greatest* common divisor. -/
theorem dvd_gcd {d a b : Nat} (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b := by
  induction a, b using gcd.induct with
  | case1 a => rw [gcd_zero]; exact ha
  | case2 a b ih =>
    rw [gcd_succ]
    apply ih hb
    have := Nat.mod_add_div a (b + 1)
    have h2 : d ∣ (b + 1) * (a / (b + 1)) := Nat.dvd_mul_right_of_dvd hb _
    have : a % (b + 1) = a - (b + 1) * (a / (b + 1)) := by omega
    rw [this]
    exact Nat.dvd_sub ha h2

/-- **Bézout's identity.** The greatest common divisor of `a` and `b` is an integer linear
combination of them: `gcd a b = a·x + b·y` for some integers `x, y`. -/
theorem bezout (a b : Nat) : ∃ x y : Int, (gcd a b : Int) = a * x + b * y := by
  induction a, b using gcd.induct with
  | case1 a => exact ⟨1, 0, by rw [gcd_zero]; omega⟩
  | case2 a b ih =>
    obtain ⟨x, y, h⟩ := ih
    rw [gcd_succ]
    refine ⟨y, x - (a / (b + 1) : Nat) * y, ?_⟩
    have hm : ((a % (b + 1) : Nat) : Int) + ((b + 1 : Nat) : Int) * ((a / (b + 1) : Nat) : Int)
        = (a : Int) := by
      have := Nat.mod_add_div a (b + 1)
      exact_mod_cast this
    rw [h]
    grind

/-! ## Primes and Euclid's lemma -/

/-- A natural number is **prime** if it is at least `2` and its only divisors are `1` and
itself. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- **Euclid's lemma.** If a prime `p` divides a product `a·b`, it divides `a` or `b`. -/
theorem euclid_lemma {p a b : Nat} (hp : Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · right
    -- `gcd p a` divides `p`, and is not `p` (else `p ∣ a`), so it is `1`.
    have hg : gcd p a = 1 := by
      rcases hp.2 _ (gcd_dvd p a).1 with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ (gcd_dvd p a).2) ha
    obtain ⟨x, y, hxy⟩ := bezout p a
    rw [hg] at hxy
    -- Then `b = p·b·x + (a·b)·y` is divisible by `p`.
    have hb : (b : Int) = p * (b * x) + (a * b : Nat) * y := by
      push_cast
      have hxy' : (1 : Int) = p * x + a * y := by exact_mod_cast hxy
      grind
    have hpab : (p : Int) ∣ ((a * b : Nat) : Int) := Int.natCast_dvd_natCast.2 h
    have : (p : Int) ∣ (b : Int) := by
      rw [hb]
      exact Int.dvd_add (Int.dvd_mul_right _ _) (Int.dvd_mul_of_dvd_left hpab)
    exact Int.natCast_dvd_natCast.1 this

/-- Every number `n ≥ 2` has a prime divisor. -/
theorem exists_prime_dvd {n : Nat} (hn : 2 ≤ n) : ∃ p, Prime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hp : Prime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · -- `n` has a divisor `d` other than `1` and `n`; recurse on it.
      have : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
        apply Classical.byContradiction
        intro hno
        apply hp
        refine ⟨hn, fun d hd => ?_⟩
        apply Classical.byContradiction
        intro h
        exact hno ⟨d, hd, fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩
      obtain ⟨d, hd, hd1, hdn⟩ := this
      have hd0 : d ≠ 0 := by
        rintro rfl; rw [Nat.zero_dvd] at hd; omega
      have hle := Nat.le_of_dvd (by omega) hd
      obtain ⟨p, hp, hpd⟩ := ih d (by omega) (by omega)
      exact ⟨p, hp, Nat.dvd_trans hpd hd⟩

/-- The factorial `n! = 1 · 2 ⋯ n`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Factorials are positive. -/
theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => simp [fact]
  | succ n ih => simp only [fact]; exact Nat.mul_pos (by omega) ih

/-- Every `k` with `1 ≤ k ≤ n` divides `n!`. -/
theorem dvd_fact {k n : Nat} (h1 : 1 ≤ k) (h2 : k ≤ n) : k ∣ fact n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [fact]
    by_cases hk : k = n + 1
    · rw [hk]; exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih (by omega)) _

/-- **Infinitude of primes** (Euclid). For every `n` there is a prime `p ≥ n`. -/
theorem exists_prime_ge (n : Nat) : ∃ p, n ≤ p ∧ Prime p := by
  have h2 : 2 ≤ fact n + 1 := by have := fact_pos n; omega
  obtain ⟨p, hp, hpd⟩ := exists_prime_dvd h2
  refine ⟨p, ?_, hp⟩
  apply Classical.byContradiction
  intro hlt
  have h1 : p ∣ fact n := dvd_fact (by have := hp.1; omega) (by omega)
  have : p ∣ 1 := by
    have := Nat.dvd_sub hpd h1
    rwa [Nat.add_sub_cancel_left] at this
  have := Nat.le_of_dvd (by omega) this
  have := hp.1
  omega

/-! ## The fundamental theorem of arithmetic -/

/-- The product of a list of natural numbers. -/
def prod : List Nat → Nat
  | [] => 1
  | x :: xs => x * prod xs

/-- **Fundamental theorem of arithmetic, existence.** Every positive integer is a product of a
(possibly empty) list of primes. -/
theorem factorization_exists {n : Nat} (hn : 1 ≤ n) :
    ∃ l : List Nat, (∀ p ∈ l, Prime p) ∧ prod l = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact ⟨[], by simp, by simp [prod, h1]⟩
    · obtain ⟨p, hp, ⟨m, rfl⟩⟩ := exists_prime_dvd (n := n) (by omega)
      have hp2 := hp.1
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at hn
        · exact h
      have hlt : m < p * m := by
        have : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp2
        omega
      obtain ⟨l, hl, hprod⟩ := ih m hlt hm
      refine ⟨p :: l, ?_, by simp [prod, hprod]⟩
      intro q hq
      rcases List.mem_cons.1 hq with h | h
      · rw [h]; exact hp
      · exact hl q h

/-- A prime dividing a product of primes is one of them. -/
theorem mem_of_dvd_prod {p : Nat} (hp : Prime p) :
    ∀ {l : List Nat}, (∀ q ∈ l, Prime q) → p ∣ prod l → p ∈ l
  | [], _, h => by
    simp only [prod] at h
    have := Nat.le_of_dvd (by omega) h; have := hp.1; omega
  | q :: l, hl, h => by
    simp only [prod] at h
    rcases euclid_lemma hp h with h' | h'
    · rcases (hl q (List.mem_cons_self ..)).2 p h' with h'' | h''
      · have := hp.1; omega
      · rw [h'']; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _
        (mem_of_dvd_prod hp (fun r hr => hl r (List.mem_cons_of_mem _ hr)) h')

/-- Products are invariant under permutation. -/
theorem prod_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : prod l₁ = prod l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [prod, ih]
  | swap x y l => simp only [prod]; exact Nat.mul_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- **Fundamental theorem of arithmetic, uniqueness.** Two lists of primes with the same product
are permutations of each other: the prime factorisation is unique up to order. -/
theorem factorization_unique :
    ∀ {l₁ l₂ : List Nat}, (∀ p ∈ l₁, Prime p) → (∀ p ∈ l₂, Prime p) →
      prod l₁ = prod l₂ → l₁.Perm l₂
  | [], l₂, _, h₂, h => by
    cases l₂ with
    | nil => exact List.Perm.refl _
    | cons q l₂ =>
      exfalso
      have hq := (h₂ q (List.mem_cons_self ..)).1
      simp only [prod] at h
      have : q ∣ 1 := ⟨prod l₂, h⟩
      have := Nat.le_of_dvd (by omega) this
      omega
  | p :: l₁, l₂, h₁, h₂, h => by
    have hp := h₁ p (List.mem_cons_self ..)
    have hmem : p ∈ l₂ := mem_of_dvd_prod hp h₂ ⟨prod l₁, by rw [← h]; rfl⟩
    have hperm := List.perm_cons_erase hmem
    have h' : prod l₁ = prod (l₂.erase p) := by
      have := prod_perm hperm
      simp only [prod] at h this
      exact Nat.eq_of_mul_eq_mul_left (by have := hp.1; omega) (h.trans this)
    have ih := factorization_unique (fun q hq => h₁ q (List.mem_cons_of_mem _ hq))
      (fun q hq => h₂ q (List.mem_of_mem_erase hq)) h'
    exact (ih.cons p).trans hperm.symm

end Arith

end Foundations.Numbers
