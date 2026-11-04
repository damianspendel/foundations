import Foundations.Langlands.Padic.LegendreNec

/-!
# Legendre's theorem, the hard half: a point by pigeonhole

Here we prove **sufficiency** in the normalised case `a, b > 0`, `c = −k < 0`: if
`bk`, `ak` and `−ab` are squares modulo `a`, `b` and `k`, then `a x² + b y² − k z² = 0` has a
non-trivial integer point (`legendre_core`). Legendre's own proof (1785) was a descent; we use
the later lattice-point argument (pigeonhole in the spirit of Thue's lemma and of Minkowski's
geometry of numbers; cf. Ireland–Rosen, ch. 17):

1. **Linear factors.** Choose `r₁² ≡ bk (mod a)`, `r₂² ≡ ak (mod b)`, `r₃² ≡ −ab (mod k)`. If
   `b y ≡ r₁ z (mod a)`, `a x ≡ r₂ z (mod b)` and `a x ≡ r₃ y (mod k)`, then
   `a x² + b y² − k z² ≡ 0` modulo `a`, `b`, `k`, hence modulo `abk` (`dvd_quad`).
2. **Pigeonhole** (`box_pigeonhole`, from `Combinatorics.pigeonhole`). The box
   `0 ≤ x ≤ √(bk)`, `0 ≤ y ≤ √(ak)`, `0 ≤ z ≤ √(ab)` has more than `abk` points, so two of them
   have the same three residues; their difference `(x, y, z) ≠ 0` satisfies the three linear
   congruences and `x² ≤ bk`, `y² ≤ ak`, `z² ≤ ab`.
3. **Size.** Then `−abk < a x² + b y² − k z² < 2abk` (equality is excluded because a squarefree
   positive square is `1`), and the value is divisible by `abk`, so it is `0` or `abk`.
4. **Repair.** If the value is `abk = −abc`, Legendre's identity
   `a(xz + by)² + b(yz − ax)² + c(z² + ab)² = (z² + ab)(ax² + by² + cz² + abc)` gives a new
   solution with `z² + ab > 0`.

The general sign pattern is reduced to this one in `Legendre`.
-/

namespace Foundations.Langlands.Padic

namespace Legendre

open Foundations.Numbers Foundations.Numbers.Arith

/-! ## Arithmetic lemmas -/

/-- If `r² ≡ m (mod n)` and `u ≡ r w (mod n)` then `u² ≡ m w² (mod n)`. -/
theorem dvd_quad {n r m u w : Int} (hr : n ∣ r * r - m) (hu : n ∣ u - r * w) :
    n ∣ u * u - m * (w * w) := by
  rw [show u * u - m * (w * w) = (u - r * w) * (u + r * w) + (r * r - m) * (w * w) by grind]
  exact Int.dvd_add (Int.dvd_trans hu (Int.dvd_mul_right _ _))
    (Int.dvd_trans hr (Int.dvd_mul_right _ _))

/-- Coprimality with a product. -/
theorem Coprime.mul_left {a b k : Int} (ha : Coprime a k) (hb : Coprime b k) :
    Coprime (a * b) k := by
  unfold Coprime; rw [Int.natAbs_mul]
  exact Nat.Coprime.symm (Nat.Coprime.mul_right (Nat.Coprime.symm ha) (Nat.Coprime.symm hb))

/-- `−X ≤ d ≤ X` implies `d² ≤ X²`. -/
theorem sq_le_of_abs_le {d : Int} {X : Nat} (h1 : -(X : Int) ≤ d) (h2 : d ≤ X) :
    d * d ≤ (X : Int) * X := by
  rw [← Int.natAbs_mul_self', ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.2 (Nat.mul_self_le_mul_self (by omega))

/-- Equal residues modulo `n` mean divisibility of the difference. -/
theorem dvd_sub_of_emod_eq {n u v : Int} (h : u % n = v % n) : n ∣ u - v :=
  Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h)

/-- A residue modulo a positive `n`, as a natural number below `n`. -/
theorem res_lt {n : Nat} (hn : 0 < n) (u : Int) : (u % (n : Int)).toNat < n := by
  have h1 := Int.emod_nonneg u (show (n : Int) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos u (show (0 : Int) < n by omega)
  omega

/-- Residues modulo `n > 0` that agree as natural numbers agree as integers. -/
theorem res_eq {n : Nat} (hn : 0 < n) {u v : Int} (h : (u % (n : Int)).toNat = (v % (n : Int)).toNat) :
    u % (n : Int) = v % (n : Int) := by
  have h1 := Int.emod_nonneg u (show (n : Int) ≠ 0 by omega)
  have h2 := Int.emod_nonneg v (show (n : Int) ≠ 0 by omega)
  omega

/-! ## Mixed-radix encoding and the pigeonhole principle on a box -/

/-- Mixed-radix codes `r + A (s + B t)` with `r < A`, `s < B` determine their digits. -/
theorem code_inj {A B r s t r' s' t' : Nat} (hA : 0 < A) (hB : 0 < B) (hr : r < A) (hs : s < B)
    (hr' : r' < A) (hs' : s' < B) (h : r + A * (s + B * t) = r' + A * (s' + B * t')) :
    r = r' ∧ s = s' ∧ t = t' := by
  have e1 := congrArg (· % A) h
  have e2 := congrArg (· / A) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at e1
  simp only [Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hr',
    Nat.zero_add] at e2
  have e3 := congrArg (· % B) e2
  have e4 := congrArg (· / B) e2
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs'] at e3
  simp only [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hs, Nat.div_eq_of_lt hs',
    Nat.zero_add] at e4
  exact ⟨e1, e3, e4⟩

/-- A mixed-radix code with `r < A`, `s < B`, `t < K` is below `A B K`. -/
theorem code_lt {A B K r s t : Nat} (hr : r < A) (hs : s < B) (ht : t < K) :
    r + A * (s + B * t) < A * B * K := by
  have h1 : s + B * t + 1 ≤ B * K := by
    have : B * (t + 1) ≤ B * K := Nat.mul_le_mul_left _ ht
    rw [Nat.mul_succ] at this; omega
  have h2 : A * (s + B * t + 1) ≤ A * (B * K) := Nat.mul_le_mul_left _ h1
  rw [Nat.mul_succ, ← Nat.mul_assoc] at h2
  omega

/-- **Pigeonhole on a box.** If `f` takes fewer than `(X+1)(Y+1)(Z+1)` values on the box
`[0, X] × [0, Y] × [0, Z]`, two distinct points of the box have the same image. -/
theorem box_pigeonhole (X Y Z M : Nat) (hM : M < (X + 1) * (Y + 1) * (Z + 1))
    (f : Int → Int → Int → Nat) (hf : ∀ x y z, f x y z < M) :
    ∃ x y z x' y' z' : Int, (0 ≤ x ∧ x ≤ X) ∧ (0 ≤ y ∧ y ≤ Y) ∧ (0 ≤ z ∧ z ≤ Z) ∧
      (0 ≤ x' ∧ x' ≤ X) ∧ (0 ≤ y' ∧ y' ≤ Y) ∧ (0 ≤ z' ∧ z' ≤ Z) ∧
      (x ≠ x' ∨ y ≠ y' ∨ z ≠ z') ∧ f x y z = f x' y' z' := by
  let px : Nat → Nat := fun N => N % (X + 1)
  let py : Nat → Nat := fun N => N / (X + 1) % (Y + 1)
  let pz : Nat → Nat := fun N => N / (X + 1) / (Y + 1)
  obtain ⟨i, j, hij, hj, hfij⟩ := Foundations.Combinatorics.pigeonhole M ((X + 1) * (Y + 1) * (Z + 1))
    (fun N => f (px N) (py N) (pz N)) (fun i _ => hf _ _ _) hM
  have hpz : ∀ N, N < (X + 1) * (Y + 1) * (Z + 1) → pz N ≤ Z := fun N hN => by
    have h1 : N / (X + 1) < (Y + 1) * (Z + 1) :=
      (Nat.div_lt_iff_lt_mul (by omega)).2
        (by rw [show (Y + 1) * (Z + 1) * (X + 1) = (X + 1) * (Y + 1) * (Z + 1) by grind]; exact hN)
    have h2 : N / (X + 1) / (Y + 1) < Z + 1 :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by rwa [Nat.mul_comm] at h1)
    show N / (X + 1) / (Y + 1) ≤ Z; omega
  have hpx : ∀ N, px N ≤ X := fun N => by
    have := Nat.mod_lt N (show 0 < X + 1 by omega); show N % (X + 1) ≤ X; omega
  have hpy : ∀ N, py N ≤ Y := fun N => by
    have := Nat.mod_lt (N / (X + 1)) (show 0 < Y + 1 by omega)
    show N / (X + 1) % (Y + 1) ≤ Y; omega
  refine ⟨px i, py i, pz i, px j, py j, pz j, ⟨by omega, by have := hpx i; omega⟩,
    ⟨by omega, by have := hpy i; omega⟩, ⟨by omega, by have := hpz i (by omega); omega⟩,
    ⟨by omega, by have := hpx j; omega⟩, ⟨by omega, by have := hpy j; omega⟩,
    ⟨by omega, by have := hpz j hj; omega⟩, ?_, hfij⟩
  apply Classical.byContradiction; intro hne
  have e1 : px i = px j := by
    apply Classical.byContradiction; intro h; exact hne (Or.inl (by omega))
  have e2 : py i = py j := by
    apply Classical.byContradiction; intro h; exact hne (Or.inr (Or.inl (by omega)))
  have e3 : pz i = pz j := by
    apply Classical.byContradiction; intro h; exact hne (Or.inr (Or.inr (by omega)))
  have hq : i / (X + 1) = j / (X + 1) := by
    have e2' : i / (X + 1) % (Y + 1) = j / (X + 1) % (Y + 1) := e2
    have e3' : i / (X + 1) / (Y + 1) = j / (X + 1) / (Y + 1) := e3
    rw [← Nat.mod_add_div (i / (X + 1)) (Y + 1), ← Nat.mod_add_div (j / (X + 1)) (Y + 1), e2', e3']
  have : i = j := by
    have e1' : i % (X + 1) = j % (X + 1) := e1
    rw [← Nat.mod_add_div i (X + 1), ← Nat.mod_add_div j (X + 1), e1', hq]
  omega

/-! ## The box is big enough -/

/-- If `X² ≤ n < (X+1)²` etc., then the box with sides `X+1, Y+1, Z+1` has more than `abk`
points when `X² ≤ bk`, `Y² ≤ ak`, `Z² ≤ ab` are the integer square roots. -/
theorem box_big {A B K X Y Z : Nat} (hX : B * K < (X + 1) * (X + 1))
    (hY : A * K < (Y + 1) * (Y + 1)) (hZ : A * B < (Z + 1) * (Z + 1)) :
    A * B * K < (X + 1) * (Y + 1) * (Z + 1) := by
  have h1 := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hX hY) hZ
  apply Classical.byContradiction; intro h
  have h2 := Nat.mul_self_le_mul_self (show (X + 1) * (Y + 1) * (Z + 1) ≤ A * B * K by omega)
  have e1 : (X + 1) * (Y + 1) * (Z + 1) * ((X + 1) * (Y + 1) * (Z + 1)) =
      (X + 1) * (X + 1) * ((Y + 1) * (Y + 1)) * ((Z + 1) * (Z + 1)) := by grind
  have e2 : A * B * K * (A * B * K) = B * K * (A * K) * (A * B) := by grind
  omega

/-! ## The core case -/

/-- An integer multiple `M q` of `M > 0` strictly between `−M` and `2M` is `0` or `M`. -/
theorem mul_cases {M q : Int} (hM : 0 < M) (h1 : -M < M * q) (h2 : M * q < 2 * M) :
    q = 0 ∨ q = 1 := by
  by_cases h : q < 0
  · have := Int.mul_le_mul_of_nonneg_left (show q ≤ -1 by omega) (Int.le_of_lt hM); omega
  by_cases h' : q < 2
  · omega
  · have := Int.mul_le_mul_of_nonneg_left (show 2 ≤ q by omega) (Int.le_of_lt hM); omega

/-- **Legendre's identity.** `a(xz + by)² + b(yz − ax)² + c(z² + ab)²
= (z² + ab)(ax² + by² + cz² + abc)`. -/
theorem legendre_identity (a b c x y z : Int) :
    a * ((x * z + b * y) * (x * z + b * y)) + b * ((y * z - a * x) * (y * z - a * x)) +
      c * ((z * z + a * b) * (z * z + a * b)) =
    (z * z + a * b) * (a * (x * x) + b * (y * y) + c * (z * z) + a * b * c) := by grind

/-- **Legendre's theorem, core case.** Let `A, B, K` be positive, squarefree and pairwise
coprime, and suppose `BK` is a square mod `A`, `AK` mod `B`, and `−AB` mod `K`. Then
`A x² + B y² − K z² = 0` has a non-trivial integer solution. -/
theorem legendre_core {A B K : Nat} (hA : 0 < A) (hB : 0 < B) (hK : 0 < K)
    (sA : Squarefree A) (sB : Squarefree B) (sK : Squarefree K)
    (cAB : Coprime A B) (cBK : Coprime B K) (cKA : Coprime K A)
    (h₁ : IsSqMod ((B : Int) * K) A) (h₂ : IsSqMod ((A : Int) * K) B)
    (h₃ : IsSqMod (-((A : Int) * B)) K) :
    ConicSolvableZ A B (-(K : Int)) := by
  -- the degenerate case `x² + y² = z²`
  by_cases h111 : A = 1 ∧ B = 1 ∧ K = 1
  · obtain ⟨rfl, rfl, rfl⟩ := h111
    exact ⟨1, 0, 1, Or.inl (by decide), by decide⟩
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  obtain ⟨r₃, hr₃⟩ := h₃
  -- the box
  obtain ⟨X, hXd⟩ : ∃ X, X = isqrt (B * K) := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = isqrt (A * K) := ⟨_, rfl⟩
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = if A * B = 1 then 0 else isqrt (A * B) := ⟨_, rfl⟩
  have hXs := isqrt_spec (B * K)
  have hYs := isqrt_spec (A * K)
  rw [← hXd] at hXs
  rw [← hYd] at hYs
  have hbig : A * B * K < (X + 1) * (Y + 1) * (Z + 1) := by
    by_cases hab : A * B = 1
    · have hA1 : A = 1 := Nat.eq_one_of_mul_eq_one_right hab
      have hB1 : B = 1 := Nat.eq_one_of_mul_eq_one_left hab
      subst hA1 hB1
      rw [hZd, hXd, hYd]
      simp only [Nat.one_mul, ite_true, Nat.zero_add, Nat.mul_one]
      exact (isqrt_spec K).2
    · have hZs := isqrt_spec (A * B)
      have : Z = isqrt (A * B) := by rw [hZd]; simp [hab]
      rw [this]
      exact box_big hXs.2 hYs.2 hZs.2
  -- the residue map
  let f : Int → Int → Int → Nat := fun x y z =>
    (((B : Int) * y - r₁ * z) % (A : Int)).toNat + A * ((((A : Int) * x - r₂ * z) % (B : Int)).toNat
      + B * ((((A : Int) * x - r₃ * y) % (K : Int)).toNat))
  have hf : ∀ x y z, f x y z < A * B * K := fun x y z =>
    code_lt (res_lt hA _) (res_lt hB _) (res_lt hK _)
  obtain ⟨x, y, z, x', y', z', bx, byy, bz, bx', by', bz', hne, hfe⟩ :=
    box_pigeonhole X Y Z _ hbig f hf
  obtain ⟨e₁, e₂, e₃⟩ := code_inj hA hB (res_lt hA _) (res_lt hB _) (res_lt hA _) (res_lt hB _) hfe
  have d₁ := dvd_sub_of_emod_eq (res_eq hA e₁)
  have d₂ := dvd_sub_of_emod_eq (res_eq hB e₂)
  have d₃ := dvd_sub_of_emod_eq (res_eq hK e₃)
  -- the difference vector
  obtain ⟨u, hu⟩ : ∃ u, u = x - x' := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = y - y' := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = z - z' := ⟨_, rfl⟩
  have hnt : Nontriv u v w := by
    rcases hne with h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))
  have l₁ : (A : Int) ∣ B * v - r₁ * w := by
    rw [show (B : Int) * v - r₁ * w = (B * y - r₁ * z) - (B * y' - r₁ * z') by subst hv hw; grind]
    exact d₁
  have l₂ : (B : Int) ∣ A * u - r₂ * w := by
    rw [show (A : Int) * u - r₂ * w = (A * x - r₂ * z) - (A * x' - r₂ * z') by subst hu hw; grind]
    exact d₂
  have l₃ : (K : Int) ∣ A * u - r₃ * v := by
    rw [show (A : Int) * u - r₃ * v = (A * x - r₃ * y) - (A * x' - r₃ * y') by subst hu hv; grind]
    exact d₃
  -- divisibility of the value by `A`, `B`, `K`
  have vA : (A : Int) ∣ A * (u * u) + B * (v * v) - K * (w * w) := by
    have q := dvd_quad hr₁ l₁
    rw [show (B : Int) * v * (B * v) - B * K * (w * w) = B * (B * (v * v) - K * (w * w)) by grind]
      at q
    have := cAB.dvd_of_dvd_mul q
    rw [show (A : Int) * (u * u) + B * (v * v) - K * (w * w) =
      A * (u * u) + (B * (v * v) - K * (w * w)) by grind]
    exact Int.dvd_add (Int.dvd_mul_right _ _) this
  have vB : (B : Int) ∣ A * (u * u) + B * (v * v) - K * (w * w) := by
    have q := dvd_quad hr₂ l₂
    rw [show (A : Int) * u * (A * u) - A * K * (w * w) = A * (A * (u * u) - K * (w * w)) by grind]
      at q
    have := cAB.symm.dvd_of_dvd_mul q
    rw [show (A : Int) * (u * u) + B * (v * v) - K * (w * w) =
      B * (v * v) + (A * (u * u) - K * (w * w)) by grind]
    exact Int.dvd_add (Int.dvd_mul_right _ _) this
  have vK : (K : Int) ∣ A * (u * u) + B * (v * v) - K * (w * w) := by
    have q := dvd_quad hr₃ l₃
    rw [show (A : Int) * u * (A * u) - -(A * B) * (v * v) = A * (A * (u * u) + B * (v * v)) by grind]
      at q
    have := cKA.dvd_of_dvd_mul q
    exact Int.dvd_sub this (Int.dvd_mul_right _ _)
  have vM : (A : Int) * B * K ∣ A * (u * u) + B * (v * v) - K * (w * w) :=
    (Coprime.mul_left cKA.symm cBK).mul_dvd (cAB.mul_dvd vA vB) vK
  obtain ⟨q, hq⟩ := vM
  -- size estimates
  have su : u * u ≤ (B : Int) * K := by
    have := sq_le_of_abs_le (d := u) (X := X) (by omega) (by omega)
    have := Int.ofNat_le.2 hXs.1; simp only [Int.natCast_mul] at this; omega
  have sv : v * v ≤ (A : Int) * K := by
    have := sq_le_of_abs_le (d := v) (X := Y) (by omega) (by omega)
    have := Int.ofNat_le.2 hYs.1; simp only [Int.natCast_mul] at this; omega
  have hA' : (0 : Int) < A := by omega
  have hB' : (0 : Int) < B := by omega
  have hK' : (0 : Int) < K := by omega
  have hAB' : (0 : Int) < A * B := Int.mul_pos hA' hB'
  have sw : w * w < (A : Int) * B := by
    by_cases hab : A * B = 1
    · have hZ : Z = 0 := by rw [hZd]; simp [hab]
      have hw0 : w = 0 := by omega
      rw [hw0]; simpa using hAB'
    · have hZ : Z = isqrt (A * B) := by rw [hZd]; simp [hab]
      have h1 := sq_le_of_abs_le (d := w) (X := Z) (by omega) (by omega)
      have h2 := Int.ofNat_le.2 (isqrt_spec (A * B)).1
      rw [← hZ] at h2; simp only [Int.natCast_mul] at h2
      have hne : w * w ≠ (A : Int) * B := fun he => hab (by
        have := (sA.mul cAB sB).eq_one_of_sq hAB' he.symm
        exact Int.ofNat_inj.1 (by simpa using this))
      omega
  have hu0 : 0 ≤ u * u := by rw [← Int.natAbs_mul_self']; exact Int.mul_nonneg (by omega) (by omega)
  have hv0 : 0 ≤ v * v := by rw [← Int.natAbs_mul_self']; exact Int.mul_nonneg (by omega) (by omega)
  have hw0 : 0 ≤ w * w := by rw [← Int.natAbs_mul_self']; exact Int.mul_nonneg (by omega) (by omega)
  have hM : (0 : Int) < A * B * K := Int.mul_pos hAB' hK'
  -- `a u² ≤ abk`, `b v² ≤ abk`, `k w² < abk`, and not both of the first two are equalities
  have t₁ : (A : Int) * (u * u) ≤ A * B * K := by
    have := Int.mul_le_mul_of_nonneg_left su (Int.le_of_lt hA'); rw [Int.mul_assoc]; exact this
  have t₂ : (B : Int) * (v * v) ≤ A * B * K := by
    have := Int.mul_le_mul_of_nonneg_left sv (Int.le_of_lt hB')
    rw [show (A : Int) * B * K = B * (A * K) by grind]; exact this
  have t₃ : (K : Int) * (w * w) < A * B * K := by
    have := Int.mul_lt_mul_of_pos_left sw hK'
    rw [show (A : Int) * B * K = K * (A * B) by grind]; exact this
  have t₄ : (A : Int) * (u * u) < A * B * K ∨ (B : Int) * (v * v) < A * B * K := by
    by_cases hbk : B * K = 1
    · have hB1 : B = 1 := Nat.eq_one_of_mul_eq_one_right hbk
      have hK1 : K = 1 := Nat.eq_one_of_mul_eq_one_left hbk
      have hA1 : A ≠ 1 := fun h => h111 ⟨h, hB1, hK1⟩
      have hak : A * K ≠ 1 := by rw [hK1, Nat.mul_one]; exact hA1
      have hne : v * v ≠ (A : Int) * K := fun he => hak (by
        have := (sA.mul cKA.symm sK).eq_one_of_sq (Int.mul_pos hA' hK') he.symm
        exact Int.ofNat_inj.1 (by simpa using this))
      have := Int.mul_lt_mul_of_pos_left (show v * v < (A : Int) * K by omega) hB'
      exact Or.inr (by rw [show (A : Int) * B * K = B * (A * K) by grind]; exact this)
    · have hne : u * u ≠ (B : Int) * K := fun he => hbk (by
        have := (sB.mul cBK sK).eq_one_of_sq (Int.mul_pos hB' hK') he.symm
        exact Int.ofNat_inj.1 (by simpa using this))
      have := Int.mul_lt_mul_of_pos_left (show u * u < (B : Int) * K by omega) hA'
      exact Or.inl (by rw [Int.mul_assoc]; exact this)
  have hKw : 0 ≤ (K : Int) * (w * w) := Int.mul_nonneg (Int.le_of_lt hK') hw0
  have hAu : 0 ≤ (A : Int) * (u * u) := Int.mul_nonneg (Int.le_of_lt hA') hu0
  have hBv : 0 ≤ (B : Int) * (v * v) := Int.mul_nonneg (Int.le_of_lt hB') hv0
  have hsol : ∀ s t r : Int, (A : Int) * (s * s) + B * (t * t) + (-(K : Int)) * (r * r) =
      A * (s * s) + B * (t * t) - K * (r * r) := fun s t r => by grind
  rcases mul_cases (q := q) hM (by omega) (by omega) with h0 | h1
  · -- the value is `0`: `(u, v, w)` is a solution
    refine ⟨u, v, w, hnt, ?_⟩
    rw [hsol, hq, h0, Int.mul_zero]
  · -- the value is `abk = −abc`: Legendre's identity repairs it
    refine ⟨u * w + B * v, v * w - A * u, w * w + A * B, Or.inr (Or.inr (by omega)), ?_⟩
    rw [legendre_identity, hsol, hq, h1]
    grind

end Legendre

end Foundations.Langlands.Padic
