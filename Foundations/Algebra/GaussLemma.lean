import Foundations.Algebra.QuadraticResidues

/-!
# Gauss's lemma and the second supplement

In his third proof of quadratic reciprocity (1808) Gauss found a way to read off the Legendre
symbol by counting. Take the multiples `a, 2a, …, ((p-1)/2)·a` and reduce them modulo `p` to
their least positive residues. Let `μ` be the number of these residues that exceed `p/2`.
**Gauss's lemma** says

  `(a/p) = (-1)^μ`.

The proof is a small piece of bookkeeping. "Folding" each residue `r > p/2` to `p - r` produces
numbers `s₁, …, s_h` (with `h = (p-1)/2`) that turn out to be a rearrangement of `1, 2, …, h`.
Multiplying everything together gives `a^h · h! ≡ (-1)^μ · h! (mod p)`. Cancelling `h!` (which
is invertible mod `p`) and applying Euler's criterion gives the lemma.

For `a = 2` the residues are just `2, 4, …, p - 1`, and counting those above `p/2` gives the
**second supplement**: `(2/p) = (-1)^((p²-1)/8)`, i.e. `2` is a square mod `p` exactly when
`p ≡ ±1 (mod 8)`. Fermat and Euler knew this empirically; Lagrange gave the first proof.

We carry out the multiplications in the field `ℤ/pℤ` (on `Fin p`), using products over finite
index types.
-/

namespace Foundations.Algebra

open Ring FiniteType

universe u

/-! ## Finite products in a commutative ring -/

section Products

variable {R : Type u} [CommRing R]

/-- The product `∏ᵢ f i` over a finite type, taken over the census. -/
def iprod {ι : Type} [FiniteType ι] (f : ι → R) : R := lprod ((elems : List ι).map f)

/-- Products are multiplicative. -/
theorem iprod_mul {ι : Type} [FiniteType ι] (f g : ι → R) :
    iprod (fun i => f i * g i) = iprod f * iprod g := by
  unfold iprod
  induction (elems : List ι) with
  | nil => exact (Ring.mul_one 1).symm
  | cons a l ih =>
    show f a * g a * lprod (l.map _) = (f a * lprod (l.map f)) * (g a * lprod (l.map g))
    rw [ih]; grind

/-- The product of a constant is a power. -/
theorem lprod_const (c : R) : ∀ l : List Nat, lprod (l.map (fun _ => c)) = rpow c l.length
  | [] => rfl
  | _ :: l => by
    show c * lprod (l.map _) = rpow c l.length * c
    rw [lprod_const c l]; exact CommRing.mul_comm _ _

/-- The product of a constant over `Fin n` is its `n`-th power. -/
theorem iprod_const_fin (n : Nat) (c : R) : iprod (fun _ : Fin n => c) = rpow c n := by
  unfold iprod
  have : ∀ l : List (Fin n), lprod (l.map (fun _ => c)) = rpow c l.length := by
    intro l; induction l with
    | nil => rfl
    | cons _ l ih =>
      show c * lprod (l.map _) = rpow c l.length * c
      rw [ih]; exact CommRing.mul_comm _ _
  rw [this]; show rpow c (List.finRange n).length = _; rw [List.length_finRange]

/-- **Reindexing** a product along a bijection. -/
theorem iprod_comp_bij {ι : Type} [FiniteType ι] (e : ι → ι) (inj : ∀ a b, e a = e b → a = b)
    (surj : ∀ y, ∃ x, e x = y) (f : ι → R) : iprod (fun i => f (e i)) = iprod f := by
  unfold iprod
  have hperm : ((elems : List ι).map e).Perm (elems : List ι) := by
    rw [List.perm_ext_iff_of_nodup (nodup_map_of_injective inj nodup) nodup]
    intro y
    simp only [List.mem_map, complete, true_and, iff_true]
    exact surj y
  rw [← lprod_perm (hperm.map f), List.map_map]; rfl

/-- In an integral domain a product of non-zero factors is non-zero. -/
theorem lprod_ne_zero (hD : IsDomain R) : ∀ l : List R, (∀ x, x ∈ l → x ≠ 0) → lprod l ≠ 0
  | [], _ => fun h => hD.1 h.symm
  | a :: l, h => by
    intro h0
    rcases hD.2 _ _ h0 with h1 | h1
    · exact h a List.mem_cons_self h1
    · exact lprod_ne_zero hD l (fun x hx => h x (List.mem_cons_of_mem a hx)) h1

/-- A product of signs is `-1` raised to the number of minus signs. -/
theorem lprod_sign (P : Nat → Prop) [DecidablePred P] : ∀ l : List Nat,
    lprod (l.map (fun k => if P k then (-1 : R) else 1)) = rpow (-1) (l.countP (fun k => decide (P k)))
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.countP_cons]
    show (if P a then (-1 : R) else 1) * lprod _ = _
    rw [lprod_sign P l]
    by_cases h : P a
    · simp only [h, ↓reduceIte, decide_true]; show _ = rpow (-1) _ * -1; exact CommRing.mul_comm _ _
    · simp only [h, ↓reduceIte, decide_false]; exact Ring.one_mul _

/-- The census of `Fin n` lists `0, …, n - 1`. -/
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

/-- A product over `Fin n` of a function of the index value is a product over `0, …, n-1`. -/
theorem iprod_fin_val (n : Nat) (g : Nat → R) :
    iprod (fun k : Fin n => g k.val) = lprod ((List.range n).map g) := by
  show lprod ((List.finRange n).map (fun k => g k.val)) = _
  rw [← finRange_map_val, List.map_map]; rfl

end Products

/-! ## Values in `Fin p` -/

section Values

variable {p : Nat} [NeZero p]

/-- Values of powers in `Fin p`. -/
theorem rpow_val (x : Fin p) (n : Nat) : (rpow x n).val = x.val ^ n % p := by
  induction n with
  | zero => exact Fin.val_ofNat p 1
  | succ n ih =>
    show (rpow x n * x).val = _
    rw [Fin.val_mul, ih, Nat.mod_mul_mod, Nat.pow_succ]

/-- `(-1 : Fin p)` has value `p - 1` (for `p ≥ 2`). -/
theorem neg_one_val (h2 : 2 ≤ p) : ((-1 : Fin p)).val = p - 1 := by
  have h1 : ((1 : Fin p)).val = 1 := by
    show (Fin.ofNat p 1).val = 1; rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : (1 : Fin p) ≠ 0 := fun h => by
    have := congrArg Fin.val h; rw [h1] at this; exact absurd this (by
      show 1 ≠ (Fin.ofNat p 0).val; rw [Fin.val_ofNat]; simp)
  rw [Fin.val_neg, ite_false_of hne, h1]

end Values

/-- Powers of `-1` in `ℤ` depend only on the parity of the exponent. -/
theorem neg_one_pow_int (n : Nat) : (-1 : Int) ^ n = if n % 2 = 0 then 1 else -1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, ih]
    by_cases hn : n % 2 = 0
    · rw [ite_true_of hn, ite_false_of (by omega)]; rfl
    · rw [ite_false_of hn, ite_true_of (by omega)]; rfl

/-! ## Folding the residues -/

section Folding

variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (ha : ¬ p ∣ a)

/-- The least residue of `(k+1)·a` modulo `p`. -/
def res (a p k : Nat) : Nat := (k + 1) * a % p

/-- The residue **folded** into `1, …, (p-1)/2`: `r` if `r ≤ p/2`, else `p - r`. -/
def fold (a p k : Nat) : Nat := if res a p k ≤ half p then res a p k else p - res a p k

/-- **Gauss's count** `μ`: the number of `k ∈ {1, …, (p-1)/2}` whose multiple `k·a` has least
residue exceeding `p/2`. -/
def gaussMu (a p : Nat) : Nat := (List.range (half p)).countP (fun k => decide (half p < res a p k))

include hp hodd ha in
/-- For `k < (p-1)/2` the residue of `(k+1)·a` is non-zero. -/
theorem res_pos {k : Nat} (hk : k < half p) : 0 < res a p k := by
  have ⟨_, _, h3⟩ := half_spec hp hodd
  apply Nat.pos_of_ne_zero
  intro h
  rcases hp.dvd_mul (Nat.dvd_of_mod_eq_zero h) with hd | hd
  · have := Nat.le_of_dvd (by omega) hd; omega
  · exact ha hd

include hp hodd ha in
/-- Equal residues come from equal multiples. -/
theorem res_inj {j k : Nat} (hj : j < half p) (hk : k < half p) (h : res a p j = res a p k) :
    j = k := by
  have ⟨_, _, h3⟩ := half_spec hp hodd
  have hc : Nat.Coprime a p := ((coprime_prime_iff hp).2 ha)
  have := cancel_mod hc (show j + 1 < p by omega) (show k + 1 < p by omega)
    (by unfold res at h; rw [Nat.mul_comm a, Nat.mul_comm a]; exact h)
  omega

include hp hodd ha in
/-- Two residues never add up to `p`. -/
theorem res_add_ne {j k : Nat} (hj : j < half p) (hk : k < half p) :
    res a p j + res a p k ≠ p := by
  have ⟨_, _, h3⟩ := half_spec hp hodd
  intro h
  have hm : ((j + 1) * a + (k + 1) * a) % p = 0 := by
    rw [Nat.add_mod]; unfold res at h; rw [h, Nat.mod_self]
  rw [← Nat.add_mul] at hm
  rcases hp.dvd_mul (Nat.dvd_of_mod_eq_zero hm) with hd | hd
  · have := Nat.le_of_dvd (by omega) hd; omega
  · exact ha hd

include hp hodd ha in
/-- Folded residues lie in `1, …, (p-1)/2`. -/
theorem fold_bounds {k : Nat} (hk : k < half p) : 1 ≤ fold a p k ∧ fold a p k ≤ half p := by
  have ⟨_, _, h3⟩ := half_spec hp hodd
  have h0 := res_pos hp hodd ha hk
  have hlt : res a p k < p := Nat.mod_lt _ (by omega)
  unfold fold
  by_cases h : res a p k ≤ half p
  · rw [ite_true_of h]; omega
  · rw [ite_false_of h]; omega

include hp hodd ha in
/-- **Folding is injective** on `0, …, (p-1)/2 - 1`. -/
theorem fold_inj {j k : Nat} (hj : j < half p) (hk : k < half p) (h : fold a p j = fold a p k) :
    j = k := by
  have ⟨_, _, h3⟩ := half_spec hp hodd
  have hlj : res a p j < p := Nat.mod_lt _ (by omega)
  have hlk : res a p k < p := Nat.mod_lt _ (by omega)
  unfold fold at h
  by_cases h1 : res a p j ≤ half p <;> by_cases h2 : res a p k ≤ half p
  · rw [ite_true_of h1, ite_true_of h2] at h; exact res_inj hp hodd ha hj hk h
  · rw [ite_true_of h1, ite_false_of h2] at h
    exact absurd (by omega) (res_add_ne hp hodd ha hj hk)
  · rw [ite_false_of h1, ite_true_of h2] at h
    exact absurd (by omega) (res_add_ne hp hodd ha hj hk)
  · rw [ite_false_of h1, ite_false_of h2] at h; exact res_inj hp hodd ha hj hk (by omega)

/-- The folding map as a map `Fin h → Fin h`. -/
def foldFin (hp : IsPrime p) (hodd : p % 2 = 1) (ha : ¬ p ∣ a) (k : Fin (half p)) : Fin (half p) :=
  ⟨fold a p k.val - 1, by have := fold_bounds hp hodd ha k.isLt; omega⟩

include hp hodd ha in
/-- **The folded residues are a rearrangement of `1, …, (p-1)/2`**: `foldFin` is a bijection. -/
theorem foldFin_bij :
    (∀ j k, foldFin hp hodd ha j = foldFin hp hodd ha k → j = k) ∧
    (∀ y, ∃ x, foldFin hp hodd ha x = y) := by
  have inj : ∀ j k, foldFin hp hodd ha j = foldFin hp hodd ha k → j = k := by
    intro j k h
    have e := congrArg Fin.val h
    simp only [foldFin] at e
    have := fold_bounds hp hodd ha j.isLt
    have := fold_bounds hp hodd ha k.isLt
    exact Fin.ext (fold_inj hp hodd ha j.isLt k.isLt (by omega))
  exact ⟨inj, surjective_of_injective _ inj⟩

end Folding

/-! ## Gauss's lemma -/

/-- **Gauss's lemma.** For an odd prime `p` and `p ∤ a`, `(a/p) = (-1)^μ`, where `μ` is the number
of `k ∈ {1, …, (p-1)/2}` such that the least residue of `k·a` mod `p` exceeds `p/2`. -/
theorem gauss_lemma {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (ha : ¬ p ∣ a) :
    legendre a p = (-1) ^ gaussMu a p := by
  have h2 := hp.1
  have ⟨_, _, h3⟩ := half_spec hp hodd
  haveI : NeZero p := ⟨by omega⟩
  have hF : IsField (Fin p) := (fin_isField_iff_prime p).2 hp
  let h := half p
  let A : Fin p := Fin.ofNat p a
  let K : Fin h → Fin p := fun k => Fin.ofNat p (k.val + 1)
  let S : Fin h → Fin p := fun k => Fin.ofNat p (fold a p k.val)
  let E : Fin h → Fin p := fun k => if half p < res a p k.val then -1 else 1
  -- Each multiple is a sign times a folded residue.
  have hKA : ∀ k, K k * A = E k * S k := by
    intro k
    have hlt : res a p k.val < p := Nat.mod_lt _ (by omega)
    have hpos := res_pos hp hodd ha k.isLt
    apply Fin.ext
    rw [Fin.val_mul]
    show (k.val + 1) % p * (a % p) % p = (E k * S k).val
    rw [← Nat.mul_mod]
    show res a p k.val = _
    by_cases hc : half p < res a p k.val
    · have hE : E k = -1 := ite_true_of hc
      rw [hE, Ring.neg_mul, Ring.one_mul]
      have hS : (S k).val = p - res a p k.val := by
        show (fold a p k.val) % p = _
        unfold fold; rw [ite_false_of (by omega), Nat.mod_eq_of_lt (by omega)]
      have hS0 : S k ≠ 0 := fun e => by
        have := congrArg Fin.val e; rw [hS] at this
        have : (0 : Fin p).val = 0 := rfl
        omega
      rw [Fin.val_neg, ite_false_of hS0, hS]; omega
    · have hE : E k = 1 := ite_false_of hc
      rw [hE, Ring.one_mul]
      show _ = (fold a p k.val) % p
      unfold fold; rw [ite_true_of (by omega), Nat.mod_eq_of_lt hlt]
  -- Multiply over all `k`.
  have hprod := congrArg iprod (funext hKA)
  rw [iprod_mul, iprod_mul, iprod_const_fin] at hprod
  have hS : iprod S = iprod K := by
    rw [← iprod_comp_bij (foldFin hp hodd ha) (foldFin_bij hp hodd ha).1 (foldFin_bij hp hodd ha).2 K]
    congr 1; funext k
    show Fin.ofNat p (fold a p k.val) = Fin.ofNat p (fold a p k.val - 1 + 1)
    have := fold_bounds hp hodd ha k.isLt
    rw [Nat.sub_add_cancel this.1]
  have hE : iprod E = rpow (-1) (gaussMu a p) := by
    exact (iprod_fin_val (half p) (fun n => if half p < res a p n then (-1 : Fin p) else 1)).trans
      (lprod_sign (fun n => half p < res a p n) _)
  have hK0 : iprod K ≠ 0 := by
    apply lprod_ne_zero hF.isDomain
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hx
    intro e
    have := congrArg Fin.val e
    have hk := k.isLt
    simp only [K, Fin.val_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    have : (0 : Fin p).val = 0 := rfl
    omega
  rw [hS, hE, CommRing.mul_comm (rpow (-1) _)] at hprod
  have hcancel : rpow A h = rpow (-1) (gaussMu a p) :=
    hF.isDomain.mul_left_cancel hK0 hprod
  have hval := congrArg Fin.val hcancel
  rw [rpow_val, rpow_val, neg_one_val h2, pred_pow_mod h2] at hval
  have hA : A.val ^ h % p = a ^ half p % p := by
    show (a % p) ^ half p % p = _; rw [← Nat.pow_mod]
  rw [hA] at hval
  have hl := legendre_eq_of_pow hp hodd ha
  rw [neg_one_pow_int]
  by_cases hμ : gaussMu a p % 2 = 0
  · rw [ite_true_of hμ] at hval ⊢; exact hl.1 hval
  · rw [ite_false_of hμ] at hval ⊢; exact hl.2 hval

/-! ## The second supplement -/

/-- Counting the `k < n` with `t ≤ k`. -/
theorem countP_range_ge (t : Nat) : ∀ n, (List.range n).countP (fun k => decide (t ≤ k)) = n - t
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_ge t n]
    by_cases h : t ≤ n
    · simp [h]; omega
    · simp [h]; omega

/-- For `a = 2`, Gauss's count is `h - ⌊h/2⌋` with `h = (p-1)/2`. -/
theorem gaussMu_two {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) :
    gaussMu 2 p = half p - half p / 2 := by
  have ⟨_, _, h3⟩ := half_spec hp hodd
  unfold gaussMu
  rw [← countP_range_ge (half p / 2) (half p)]
  apply List.countP_congr
  intro k hk
  rw [List.mem_range] at hk
  unfold res
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [decide_eq_true_eq]
  omega

/-- **The second supplement** to quadratic reciprocity: `(2/p) = (-1)^((p²-1)/8)` for an odd
prime `p`. -/
theorem legendre_two {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) :
    legendre 2 p = (-1) ^ ((p * p - 1) / 8) := by
  have h2 := hp.1
  have hnd : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by decide) h
    omega
  rw [gauss_lemma hp hodd hnd, gaussMu_two hp hodd, neg_one_pow_int, neg_one_pow_int]
  -- Compare parities by the residue of `p` mod 8.
  have key : (half p - half p / 2) % 2 = (p * p - 1) / 8 % 2 := by
    obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 8 ∧ p = 8 * m + r := ⟨p / 8, p % 8, Nat.mod_lt _ (by decide), by omega⟩
    unfold half
    have hsq : (8 * m + r) * (8 * m + r) = 64 * (m * m) + 16 * (m * r) + r * r := by grind
    rw [hsq]
    have : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> omega
  rw [key]

/-- **When is `2` a square?** `2` is a quadratic residue modulo an odd prime `p` exactly when
`p ≡ ±1 (mod 8)`. -/
theorem two_qr_iff {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) :
    legendre 2 p = 1 ↔ (p % 8 = 1 ∨ p % 8 = 7) := by
  rw [legendre_two hp hodd, neg_one_pow_int]
  have key : (p * p - 1) / 8 % 2 = 0 ↔ (p % 8 = 1 ∨ p % 8 = 7) := by
    obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 8 ∧ p = 8 * m + r := ⟨p / 8, p % 8, Nat.mod_lt _ (by decide), by omega⟩
    have hsq : (8 * m + r) * (8 * m + r) = 64 * (m * m) + 16 * (m * r) + r * r := by grind
    rw [hsq]
    have : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> omega
  by_cases h : (p * p - 1) / 8 % 2 = 0
  · rw [ite_true_of h]; exact ⟨fun _ => key.1 h, fun _ => rfl⟩
  · rw [ite_false_of h]
    exact ⟨fun e => absurd e (by decide), fun e => absurd (key.2 e) h⟩

end Foundations.Algebra
