import Foundations.Algebra.Algebraic

/-!
# Ruler and compass: the impossibility of doubling the cube and trisecting the angle

Greek geometry built figures with two instruments: the straightedge, which draws the line
through two points, and the compass, which draws the circle with a given centre through a
given point. Three problems resisted all attempts:

* **doubling the cube** (the Delian problem): construct the side of a cube with twice the
  volume of a given cube — a length `∛2`;
* **trisecting the angle**: divide any given angle into three equal parts — in particular the
  angle of `60°`, which would require the length `cos 20°`;
* **squaring the circle** — a length `√π`.

Descartes' *La Géométrie* (1637) turned the instruments into algebra. Choose a unit length;
intersecting lines and circles leads only to linear and quadratic equations, so the
coordinates of constructible points are exactly the numbers obtainable from the rationals by
`+, -, ×, ÷` and **square roots**. (The Geometry part of this project shows the converse
phenomenon in miniature: already Euclid's first proposition needs `√3`.) We take this
algebraic description as our definition of a **constructible number**.

Pierre Wantzel (1837) then observed that every constructible number lies in a *tower of
quadratic extensions* `ℚ = F₀ ⊆ F₁ ⊆ ⋯ ⊆ Fₙ`, each `Fᵢ₊₁ = Fᵢ(√dᵢ)` of degree `1` or `2`; by
the tower law `[Fₙ : ℚ]` is a power of `2`. If `α` is constructible, `ℚ(α) ⊆ Fₙ`, so
`[ℚ(α) : ℚ]` divides a power of `2`. But `∛2` is a root of `x³ - 2`, and `cos 20°` a root of
`8x³ - 6x - 1` (from `cos 3θ = 4 cos³ θ - 3 cos θ` with `θ = 20°`); both cubics have no
rational root, so `[ℚ(α) : ℚ] = 3`, which divides no power of `2`. Both constructions are
therefore impossible. (Squaring the circle needs the transcendence of `π`, proved by
Lindemann in 1882, and is beyond this Part.)

As in the previous file we work inside an arbitrary field `Ω` of characteristic zero (such
as `ℝ` or `ℂ`), with `ℚ` its prime field. The theorems say: *no element of `Ω` whose cube
is `2` (resp. which is a root of `8x³ - 6x - 1`) can be obtained from the rationals by field
operations and square roots.*
-/

namespace Foundations.Algebra

open Ring FiniteType VectorSpace Subfield KSubspace

universe u

variable {Ω : Type u} [CommRing Ω] (hΩ : IsField Ω) (hc : CharZero Ω)

/-! ## Towers of quadratic extensions -/

/-- **Quadratic towers** over `ℚ`: `ℚ` itself, and `F(s)` for any quadratic tower `F` and any
`s` with `s² ∈ F`. -/
inductive IsQuadTower : Subfield Ω → Prop
  | base : IsQuadTower (ratField hΩ hc)
  | step {F : Subfield Ω} (s : Ω) (hs : s * s ∈ F) : IsQuadTower F →
      IsQuadTower (adjoinSqrt hΩ F s hs)

/-- `[ℚ : ℚ] = 1`. -/
theorem deg_self (hΩ' : IsField Ω) (K : Subfield Ω) : FiniteExt K K (le_refl K) ∧ deg K K (le_refl K) = 1 := by
  have hF := K.isField hΩ'
  let one : Fin 1 → K.over K (le_refl K) := fun _ => ⟨1, K.one_mem⟩
  have hspan : Spans K one := by
    intro x
    refine ⟨fun _ => ⟨x.1, x.2⟩, Subtype.ext ?_⟩
    rw [coe_isum, isum_fin_succ, isum_fin_zero]
    show x.1 = x.1 * 1 + 0
    grind
  have hind : LinIndep K one := by
    intro c h i
    have := congrArg Subtype.val h
    rw [coe_isum, isum_fin_succ, isum_fin_zero] at this
    have e : (c 0).1 * 1 + 0 = 0 := this
    have : c i = c 0 := congrArg c (Fin.ext (by have := i.isLt; omega))
    rw [this]; exact Subtype.ext (show (c 0).1 = 0 by grind)
  have hfin := finDim_of_spans hspan
  refine ⟨hfin, ?_⟩
  have := card_eq_dim hF hfin ⟨hind, hspan⟩
  rw [card_fin] at this
  exact this.symm

/-- **Quadratic towers have degree a power of `2`** over `ℚ`. -/
theorem IsQuadTower.deg_pow_two {F : Subfield Ω} (hT : IsQuadTower hΩ hc F) :
    ∃ h : (ratField hΩ hc).le F, FiniteExt _ F h ∧ ∃ k, deg _ F h = 2 ^ k := by
  induction hT with
  | base => exact ⟨le_refl _, (deg_self hΩ _).1, 0, (deg_self hΩ _).2⟩
  | step s hs _ ih =>
    obtain ⟨h, hfin, k, hk⟩ := ih
    obtain ⟨hfin2, hdeg2⟩ := deg_adjoinSqrt hΩ _ s hs
    obtain ⟨hfin3, hdeg3⟩ := tower_law hΩ h (le_adjoinSqrt hΩ _ s hs) hfin hfin2
    refine ⟨_, hfin3, ?_⟩
    rw [hdeg3, hk]
    rcases hdeg2 with h1 | h2
    · exact ⟨k, by rw [h1, Nat.one_mul]⟩
    · exact ⟨k + 1, by rw [h2, Nat.pow_succ, Nat.mul_comm]⟩

/-- `ℚ` lies in every quadratic tower. -/
theorem IsQuadTower.rat_le {F : Subfield Ω} (hT : IsQuadTower hΩ hc F) : (ratField hΩ hc).le F :=
  (hT.deg_pow_two).1

/-- **Any two quadratic towers lie in a common one**: adjoin the square roots of the second
on top of the first. -/
theorem IsQuadTower.common {F₁ F₂ : Subfield Ω} (h₁ : IsQuadTower hΩ hc F₁)
    (h₂ : IsQuadTower hΩ hc F₂) : ∃ F₃, IsQuadTower hΩ hc F₃ ∧ F₁.le F₃ ∧ F₂.le F₃ := by
  induction h₂ with
  | base => exact ⟨F₁, h₁, le_refl _, h₁.rat_le⟩
  | step s hs _ ih =>
    obtain ⟨F₃, h₃, h13, hG3⟩ := ih
    have hs' : s * s ∈ F₃ := hG3 _ hs
    exact ⟨adjoinSqrt hΩ F₃ s hs', IsQuadTower.step s hs' h₃,
      le_trans h13 (le_adjoinSqrt hΩ F₃ s hs'), adjoinSqrt_mono hΩ hG3 s hs hs'⟩

/-! ## Constructible numbers -/

/-- **Constructible numbers**: the smallest subset of `Ω` containing the rationals and closed
under addition, negation, multiplication, inverses and square roots — the numbers whose
lengths can be drawn with straightedge and compass from a unit length. -/
inductive Constructible : Ω → Prop
  | rat {x : Ω} : x ∈ ratField hΩ hc → Constructible x
  | add {x y : Ω} : Constructible x → Constructible y → Constructible (x + y)
  | neg {x : Ω} : Constructible x → Constructible (-x)
  | mul {x y : Ω} : Constructible x → Constructible y → Constructible (x * y)
  | inv {x y : Ω} : Constructible x → x * y = 1 → Constructible y
  | sqrt {x y : Ω} : Constructible x → y * y = x → Constructible y

/-- **Wantzel's lemma.** Every constructible number lies in a tower of quadratic extensions
of `ℚ`. -/
theorem Constructible.mem_tower {x : Ω} (h : Constructible hΩ hc x) :
    ∃ F, IsQuadTower hΩ hc F ∧ x ∈ F := by
  induction h with
  | rat hx => exact ⟨_, IsQuadTower.base, hx⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨F₁, h₁, hx⟩ := ih1
    obtain ⟨F₂, h₂, hy⟩ := ih2
    obtain ⟨F₃, h₃, h13, h23⟩ := h₁.common hΩ hc h₂
    exact ⟨F₃, h₃, F₃.add_mem (h13 _ hx) (h23 _ hy)⟩
  | neg _ ih =>
    obtain ⟨F, hF, hx⟩ := ih
    exact ⟨F, hF, F.neg_mem hx⟩
  | mul _ _ ih1 ih2 =>
    obtain ⟨F₁, h₁, hx⟩ := ih1
    obtain ⟨F₂, h₂, hy⟩ := ih2
    obtain ⟨F₃, h₃, h13, h23⟩ := h₁.common hΩ hc h₂
    exact ⟨F₃, h₃, F₃.mul_mem (h13 _ hx) (h23 _ hy)⟩
  | @inv x y _ hxy ih =>
    obtain ⟨F, hF, hx⟩ := ih
    have hx0 : x ≠ 0 := by intro h; apply hΩ.1; rw [← hxy, h, Ring.zero_mul]
    obtain ⟨y', hy', hxy'⟩ := F.inv_mem hx hx0
    have : y = y' := by
      calc y = y * (x * y') := by rw [hxy', Ring.mul_one]
        _ = (x * y) * y' := by grind
        _ = y' := by rw [hxy, Ring.one_mul]
    exact ⟨F, hF, this ▸ hy'⟩
  | @sqrt x y _ hyx ih =>
    obtain ⟨F, hF, hx⟩ := ih
    have hs : y * y ∈ F := hyx ▸ hx
    exact ⟨_, IsQuadTower.step y hs hF, mem_adjoinSqrt_self hΩ F y hs⟩

/-- `3` divides no power of `2`. -/
theorem three_not_dvd_pow_two (k : Nat) : ¬ 3 ∣ 2 ^ k := by
  have h : ∀ k, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih => rw [Nat.pow_succ]; omega
  intro hd
  have := Nat.mod_eq_zero_of_dvd hd
  rcases h k with h1 | h1 <;> omega

/-- **Roots of rational cubics without rational roots are not constructible.** If `α` is a
root of a cubic over `ℚ` with no rational root, then `[ℚ(α) : ℚ] = 3`, which cannot divide the
degree `2^k` of a quadratic tower containing `α`. -/
theorem not_constructible_of_cubic {α : Ω} (C : CubicRoot (ratField hΩ hc) α) :
    ¬ Constructible hΩ hc α := by
  intro hα
  obtain ⟨F, hT, hαF⟩ := hα.mem_tower
  obtain ⟨h, hfin, k, hk⟩ := hT.deg_pow_two
  let L := C.field hΩ
  have hLF : L.le F := C.field_le hΩ h hαF
  obtain ⟨hfinL, hdegL⟩ := C.deg_field hΩ
  have hfin2 := finiteExt_of_tower (C.le_field hΩ) hLF hfin
  obtain ⟨_, htower⟩ := tower_law hΩ (C.le_field hΩ) hLF hfinL hfin2
  have : deg _ F h = deg L F hLF * 3 := by rw [← hdegL]; exact htower
  apply three_not_dvd_pow_two k
  rw [← hk, this]
  exact Nat.dvd_mul_left 3 _

/-- **Doubling the cube is impossible** (Wantzel, 1837). No number whose cube is `2` is
constructible: the side of a cube of twice the volume of the unit cube cannot be drawn with
straightedge and compass. -/
theorem doubling_the_cube_impossible {α : Ω} (h : α * α * α = 1 + 1) :
    ¬ Constructible hΩ hc α := by
  apply not_constructible_of_cubic hΩ hc
  exact {
    d := 1, a := 0, b := 0, c := -((2 : Int) : Ω)
    hd := (ratField hΩ hc).one_mem
    ha := (ratField hΩ hc).zero_mem
    hb := (ratField hΩ hc).zero_mem
    hc := (ratField hΩ hc).neg_mem (intCast_mem_ratField hΩ hc 2)
    d_ne := fun h => hΩ.1 h.symm
    root := by grind
    no_root := cube_two_no_rat_root hΩ hc }

/-- **Trisecting the angle is impossible** (Wantzel, 1837). The number `cos 20°` satisfies
`8x³ = 6x + 1` (from `cos 60° = 1/2` and `cos 3θ = 4cos³θ - 3cos θ`), and no root of this
equation is constructible. Hence the angle of `60°` cannot be trisected with straightedge and
compass. -/
theorem trisecting_the_angle_impossible {γ : Ω}
    (h : ((8 : Int) : Ω) * (γ * γ * γ) = ((6 : Int) : Ω) * γ + 1) :
    ¬ Constructible hΩ hc γ := by
  apply not_constructible_of_cubic hΩ hc
  exact {
    d := ((8 : Int) : Ω), a := 0, b := ((-6 : Int) : Ω), c := ((-1 : Int) : Ω)
    hd := intCast_mem_ratField hΩ hc 8
    ha := (ratField hΩ hc).zero_mem
    hb := intCast_mem_ratField hΩ hc (-6)
    hc := intCast_mem_ratField hΩ hc (-1)
    d_ne := fun h => absurd (hc 8 h) (by decide)
    root := by grind
    no_root := trisect_no_rat_root hΩ hc }

end Foundations.Algebra
