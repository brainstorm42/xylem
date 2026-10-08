import Percolation.Literature.KozmaNitzanHGluing
import Percolation.Literature.KozmaNitzanHittable
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 — Lemma 11: elongated boxes are hittable geometries

Fifth proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4), proving Lemma 11 (p. 22):
under Conjecture 3, for `0 < p < 1` with `θ(p) > 0` and every integer `K ≥ 2`, the couple (`{K} ×
[-1,1]^{d-1}`, `[-1,K] × [-1,1]^{d-1}`) — and its images under the lattice symmetries, here: every
coordinate direction `a` and sign `σ` — is a hittable geometry: from a cube `Λ_m` one reaches the
far face of the elongated box `{-r ≤ σ x_a ≤ Kr, |x_j| ≤ r}` inside the box with probability `→ 1`.

## Proof (KN p. 22–23, with the bookkeeping made explicit)

Work in the weighting `Ω` of `ℤ^d` obtained from the lattice weighting `P_p` by keeping only the
pairs inside the elongated box and WIRING the cube `Λ_k` (KN: "identifying the cube `[-n,n]^d` to a
point (which will be `o`)"; here `restrW`/`wireW` of `KozmaNitzanHittable.lean` /
`KozmaNitzanPinning.lean`, and `o = 0`). Here `s = ⌊r/8⌋`; the side conditions (`2R ≤ s ≤ w`, `w + s
+ 2R ≤ r`, the cube below the first subbox) are KN's "`m = max{10n, 16KR}`".

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4, Lemma 11 and its proof, pp. 22–23; Lemma 9
  p. 16, Lemma 10 pp. 17–22.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Percolation.Literature

open LatticeModels SimpleGraph

namespace KozmaNitzan

variable {d : ℕ}

/-! ## Signed boxes: `{α ≤ σ (x_a - c_a) ≤ β, |x_j - c_j| ≤ w (j ≠ a)}` as order intervals -/

/-- Lower corner of the signed box. [folklore] -/
def sLo (a : Fin d) (σ : ℤ) (c : Site d) (α β w : ℤ) : Site d :=
  fun j => if j = a then (if σ = 1 then c a + α else c a - β) else c j - w

/-- Upper corner of the signed box. [folklore] -/
def sHi (a : Fin d) (σ : ℤ) (c : Site d) (α β w : ℤ) : Site d :=
  fun j => if j = a then (if σ = 1 then c a + β else c a - α) else c j + w

/-- **The signed box** `{α ≤ σ (x_a - c_a) ≤ β} ∩ {|x_j - c_j| ≤ w, j ≠ a}` of direction `a`, sign
`σ = ±1`, centre `c`: a box `v + ∏ [-s_i, s_i]` of `ℤ^d` in KN's sense (p. 15), written as the
order interval `Icc (sLo …) (sHi …)` so that the target lemma applies verbatim; all the boxes of
Lemmas 11–12 and of the proof of Theorem 6 (`[-r, Kr] × [-r, r]^{d-1}`, `{Kr} × [-r, r]^{d-1}`,
`[5r, 25r] × [-5r, 5r]^{d-1}`, …, and their images under lattice symmetries) are of this form.
[cite: KozmaNitzan2024, §4 p. 15 (boxes), Lemma 8 (p. 16)] -/
def sBox (a : Fin d) (σ : ℤ) (c : Site d) (α β w : ℤ) : Finset (Site d) :=
  Finset.Icc (sLo a σ c α β w) (sHi a σ c α β w)

/-- Membership in a signed box, in terms of the level `σ (x_a - c_a)`. [folklore] -/
theorem mem_sBox_iff {a : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {c : Site d} {α β w : ℤ} {x : Site d} :
    x ∈ sBox a σ c α β w ↔
      (α ≤ σ * (x a - c a) ∧ σ * (x a - c a) ≤ β) ∧ ∀ j, j ≠ a → c j - w ≤ x j ∧ x j ≤ c j + w := by
  rw [sBox, mem_Icc_iff]
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have := h a
      simp only [sLo, sHi, if_true] at this
      rcases hσ with rfl | rfl
      · simp only [if_true] at this; omega
      · simp only [show (-1 : ℤ) ≠ 1 by norm_num, if_false] at this; omega
    · have := h j
      simp only [sLo, sHi, if_neg hj] at this
      exact this
  · rintro ⟨ha, hj⟩ i
    by_cases hi : i = a
    · subst hi
      simp only [sLo, sHi, if_true]
      rcases hσ with rfl | rfl
      · simp only [if_true]; omega
      · simp only [show (-1 : ℤ) ≠ 1 by norm_num, if_false]; omega
    · simp only [sLo, sHi, if_neg hi]
      exact hj i hi

/-- **Enlarging a signed box** by `R` in every coordinate is the signed box with
`α - R, β + R, w + R` (KN's `B⟨R⟩`). [cite: KozmaNitzan2024, §4 p. 15 (B⟨R⟩)] -/
theorem sLo_sub (a : Fin d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (c : Site d) (α β w : ℤ) (R : ℕ) :
    sLo a σ c α β w - (R : Site d) = sLo a σ c (α - R) (β + R) (w + R) := by
  funext j
  simp only [sLo, Pi.sub_apply, Pi.natCast_apply]
  by_cases hj : j = a
  · subst hj; simp only [if_true]
    rcases hσ with rfl | rfl
    · simp only [if_true]; ring
    · simp only [show (-1 : ℤ) ≠ 1 by norm_num, if_false]; ring
  · simp only [if_neg hj]; ring

/-- Upper corner of the enlarged signed box. [cite: KozmaNitzan2024, §4 p. 15 (B⟨R⟩)] -/
theorem sHi_add (a : Fin d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (c : Site d) (α β w : ℤ) (R : ℕ) :
    sHi a σ c α β w + (R : Site d) = sHi a σ c (α - R) (β + R) (w + R) := by
  funext j
  simp only [sHi, Pi.add_apply, Pi.natCast_apply]
  by_cases hj : j = a
  · subst hj; simp only [if_true]
    rcases hσ with rfl | rfl
    · simp only [if_true]; ring
    · simp only [show (-1 : ℤ) ≠ 1 by norm_num, if_false]; ring
  · simp only [if_neg hj]; ring

/-- The enlarged signed box. [cite: KozmaNitzan2024, §4 p. 15 (B⟨R⟩)] -/
theorem sBox_enlarge (a : Fin d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (c : Site d) (α β w : ℤ) (R : ℕ) :
    Finset.Icc (sLo a σ c α β w - (R : Site d)) (sHi a σ c α β w + (R : Site d)) =
      sBox a σ c (α - R) (β + R) (w + R) := by
  rw [sLo_sub a σ hσ, sHi_add a σ hσ]; rfl

/-- Monotonicity of signed boxes in their parameters. [folklore] -/
theorem sBox_mono {a : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (c : Site d) {α β w α' β' w' : ℤ}
    (hα : α' ≤ α) (hβ : β ≤ β') (hw : w ≤ w') : sBox a σ c α β w ⊆ sBox a σ c α' β' w' := by
  intro x hx
  rw [mem_sBox_iff hσ] at hx ⊢
  refine ⟨⟨hα.trans hx.1.1, hx.1.2.trans hβ⟩, fun j hj => ?_⟩
  have := hx.2 j hj
  constructor <;> linarith [this.1, this.2]

/-- The point of the signed box at level `β` above the centre. [folklore] -/
theorem sBox_nonempty {a : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (c : Site d) {α β w : ℤ}
    (hαβ : α ≤ β) (hw : 0 ≤ w) : (sBox a σ c α β w).Nonempty := by
  refine ⟨fun j => if j = a then c a + σ * β else c j, ?_⟩
  rw [mem_sBox_iff hσ]
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [if_true, add_sub_cancel_left]
    rcases hσ with rfl | rfl
    · simp; exact hαβ
    · simp; exact hαβ
  · simp only [if_neg hj]; constructor <;> linarith

/-- The level `σ(y_a - c_a)` changes by at most `1` along an edge of `ℤ^d`, and if it changes the
other coordinates do not. [folklore] -/
theorem level_adj {a : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (c : Site d) {x y : Site d}
    (h : (zdGraph d).Adj x y) :
    (σ * (y a - c a) = σ * (x a - c a) ∧ ∃ i, i ≠ a ∧ (y i = x i + 1 ∨ y i = x i - 1) ∧ ∀ j, j ≠ i → y j = x j) ∨
      ((σ * (y a - c a) = σ * (x a - c a) + 1 ∨ σ * (y a - c a) = σ * (x a - c a) - 1) ∧
        ∀ j, j ≠ a → y j = x j) := by
  obtain ⟨i, τ, hτ, rfl⟩ := adj_iff_exists_sign.1 h
  by_cases hi : i = a
  · subst hi
    right
    refine ⟨?_, fun j hj => ?_⟩
    · rw [add_smul_unitVec_apply, if_pos rfl]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp <;> ring_nf <;> simp
    · rw [add_smul_unitVec_apply, if_neg hj]; simp
  · left
    refine ⟨?_, i, hi, ?_, fun j hj => ?_⟩
    · rw [add_smul_unitVec_apply, if_neg (Ne.symm hi)]; simp
    · rw [add_smul_unitVec_apply, if_pos rfl]
      rcases hτ with rfl | rfl
      · left; rfl
      · right; ring
    · rw [add_smul_unitVec_apply, if_neg hj]; simp

/-! ## Sign bookkeeping -/

/-- `σ² = 1`. [folklore] -/
theorem sign_mul_self {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

/-- `|x - y| ≤ ℓ` bounds the signed difference. [folklore] -/
theorem level_bounds_of_abs_le {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {x y ℓ : ℤ} (h1 : x - ℓ ≤ y) (h2 : y ≤ x + ℓ) :
    σ * x - ℓ ≤ σ * y ∧ σ * y ≤ σ * x + ℓ := by
  rcases hσ with rfl | rfl <;> constructor <;> linarith

/-- A symmetric bound passes to the signed coordinate. [folklore] -/
theorem level_bounds_of_symm {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {x n : ℤ} (h1 : -n ≤ x) (h2 : x ≤ n) :
    -n ≤ σ * x ∧ σ * x ≤ n := by
  rcases hσ with rfl | rfl <;> constructor <;> linarith

/-- `y = x + ℓσ` raises the level by `ℓ`. [folklore] -/
theorem level_of_eq_add {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {x y ℓ : ℤ} (h : y = x + ℓ * σ) :
    σ * y = σ * x + ℓ := by
  rw [h, mul_add, ← mul_assoc, mul_comm σ ℓ, mul_assoc, sign_mul_self hσ, mul_one]

/-- The value of the unit `if σ = 1 then 1 else -1` is `σ`. [folklore] -/
theorem units_of_sign_val {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ((if σ = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) = σ := by
  rcases hσ with rfl | rfl
  · simp
  · simp

/-! ## The list of all quarter-face geometries -/

/-- All quarter-face geometries of `ℤ^d` (KN: "the hittable geometry of all quarter faces (recall
lemma 9), which we will denote by `H`", p. 22). [cite: KozmaNitzan2024, §4 p. 22 (H)] -/
def qfList (d : ℕ) : List (Geom d) :=
  (Finset.univ : Finset (Fin d × (Fin d → ℤˣ))).toList.map fun x => qfGeom x.1 x.2

/-- Every quarter-face geometry is in the list. [folklore] -/
theorem qfGeom_mem_qfList (a : Fin d) (τ : Fin d → ℤˣ) : qfGeom a τ ∈ qfList d :=
  List.mem_map.2 ⟨(a, τ), Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩

/-- Every geometry of the list is hittable (Lemma 9). [cite: KozmaNitzan2024, §4 Lemma 9 (p. 16)] -/
theorem isHittable_of_mem_qfList [NeZero d] (p : unitInterval) (hθ : 0 < theta (zdGraph d) (0 : Site d) p)
    (hp1 : (p : ℝ) < 1) : ∀ g ∈ qfList d, IsHittable p g := by
  intro g hg
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hg
  exact isHittable_qfGeom p hθ hp1 x.1 x.2

/-! ## The weighting `Ω` of Lemma 11: an elongated box with a wired cube -/

/-- The data of the construction of Lemma 11: direction `a`, sign `σ`, aspect ratio `K`, scale
`r`, and the radius `k` of the wired cube. [cite: KozmaNitzan2024, §4 Lemma 11 (p. 22)] -/
structure EData (d : ℕ) where
  /-- the long direction -/
  a : Fin d
  /-- its sign -/
  σ : ℤ
  /-- `σ = ±1` -/
  hσ : σ = 1 ∨ σ = -1
  /-- the aspect ratio -/
  K : ℕ
  /-- the scale -/
  r : ℕ
  /-- the radius of the wired cube -/
  k : ℕ

namespace EData

variable (E : EData d)

/-- The elongated box `{-r ≤ σ x_a ≤ Kr, |x_j| ≤ r}` (KN: `[-r, Kr] × [-r, r]^{d-1}`).
[cite: KozmaNitzan2024, §4 Lemma 11 (p. 22)] -/
def bigBox : Finset (Site d) := sBox E.a E.σ 0 (-(E.r : ℤ)) (E.K * E.r) E.r

/-- The wired cube `Λ_k` (KN: `[-n, n]^d` identified to a point). [cite: KozmaNitzan2024, §4 p. 22] -/
def cube : Finset (Site d) := box d E.k

/-- **The weighting `Ω`**: lattice weights on the pairs inside the elongated box, the cube wired.
[cite: KozmaNitzan2024, §4 p. 22 (the graph Ω)] -/
def W (p : unitInterval) : Sym2 (Site d) → unitInterval :=
  Percolation.Literature.wireW (↑E.cube : Set (Site d)) (Percolation.Literature.restrW (↑E.bigBox : Set (Site d)) (lattW d p))

/-- The face `{σ x_a = L, |x_j| ≤ w}` (KN's intermediate stages `B` and targets `T`).
[cite: KozmaNitzan2024, §4 p. 22 (B, T)] -/
def face (L w : ℤ) : Finset (Site d) := sBox E.a E.σ 0 L L w

/-- The region `{L - 2s ≤ σ x_a ≤ L + s, |x_j| ≤ r}` (KN's subbox `D = [r/8, 3r/4] × [-r, r]^{d-1}`).
[cite: KozmaNitzan2024, §4 p. 22 (D)] -/
def region (L s : ℤ) : Finset (Site d) := sBox E.a E.σ 0 (L - 2 * s) (L + s) E.r

/-- Membership in the elongated box. [folklore] -/
theorem mem_bigBox_iff {x : Site d} :
    x ∈ E.bigBox ↔ (-(E.r : ℤ) ≤ E.σ * x E.a ∧ E.σ * x E.a ≤ E.K * E.r) ∧
      ∀ j, j ≠ E.a → -(E.r : ℤ) ≤ x j ∧ x j ≤ E.r := by
  rw [bigBox, mem_sBox_iff E.hσ]; simp

/-- Membership in a face. [folklore] -/
theorem mem_face_iff {L w : ℤ} {x : Site d} :
    x ∈ E.face L w ↔ E.σ * x E.a = L ∧ ∀ j, j ≠ E.a → -w ≤ x j ∧ x j ≤ w := by
  rw [face, mem_sBox_iff E.hσ]
  simp only [Pi.zero_apply, sub_zero, zero_sub, zero_add]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨le_antisymm h1.2 h1.1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1.ge, h1.le⟩, h2⟩

/-- Membership in a region. [folklore] -/
theorem mem_region_iff {L s : ℤ} {x : Site d} :
    x ∈ E.region L s ↔ (L - 2 * s ≤ E.σ * x E.a ∧ E.σ * x E.a ≤ L + s) ∧
      ∀ j, j ≠ E.a → -(E.r : ℤ) ≤ x j ∧ x j ≤ E.r := by
  rw [region, mem_sBox_iff E.hσ]; simp

/-- Membership in the cube, in level form. [folklore] -/
theorem level_of_mem_cube {x : Site d} (hx : x ∈ E.cube) :
    (-(E.k : ℤ) ≤ E.σ * x E.a ∧ E.σ * x E.a ≤ E.k) ∧ ∀ j, -(E.k : ℤ) ≤ x j ∧ x j ≤ E.k := by
  rw [cube, mem_box] at hx
  exact ⟨level_bounds_of_symm E.hσ (hx E.a).1 (hx E.a).2, hx⟩

/-- The origin lies in the elongated box. [folklore] -/
theorem zero_mem_bigBox : (0 : Site d) ∈ E.bigBox := by
  rw [E.mem_bigBox_iff]
  simp only [Pi.zero_apply, mul_zero]
  refine ⟨⟨by omega, by positivity⟩, fun j _ => ⟨by omega, by omega⟩⟩

/-- The cube lies in the elongated box once `k ≤ r` and `K ≥ 1`. [folklore] -/
theorem cube_subset_bigBox (hkr : E.k ≤ E.r) (hK : 1 ≤ E.K) : E.cube ⊆ E.bigBox := by
  intro x hx
  obtain ⟨h1, h2⟩ := E.level_of_mem_cube hx
  rw [E.mem_bigBox_iff]
  have hkr' : (E.k : ℤ) ≤ E.r := by exact_mod_cast hkr
  have hKr : (E.r : ℤ) ≤ E.K * E.r := by
    have : (1 : ℤ) * E.r ≤ E.K * E.r := mul_le_mul_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    linarith
  refine ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, fun j _ => ⟨by linarith [(h2 j).1], by linarith [(h2 j).2]⟩⟩

/-- `Ω` is finitely supported on the elongated box. [cite: KozmaNitzan2024, §4 p. 22] -/
theorem finSupp_W (p : unitInterval) (hkr : E.k ≤ E.r) (hK : 1 ≤ E.K) : FinSupp (E.W p) E.bigBox :=
  finSupp_wireW_restrW E.bigBox (Finset.coe_subset.2 (E.cube_subset_bigBox hkr hK)) _

/-! ## One step of the proof of Lemma 11 -/

/-- **The side conditions of one step** (KN: `m = max{10n, 16KR}`, `r ≥ m`): the inflation `R` is
at least the `R` of the target lemma and at most `s/2`, the face is at least `s` wide and, after the
step, still `s + 2R` inside the box; the wired cube lies below the region, which lies in the box.
[cite: KozmaNitzan2024, §4 pp. 22–23] -/
structure StepOK (E : EData d) (R₀ R : ℕ) (L s w : ℤ) : Prop where
  hR : R₀ ≤ R
  hs : 2 * (R : ℤ) ≤ s
  hw : s ≤ w
  hr : w + s + 2 * R ≤ E.r
  hk : (E.k : ℤ) < L - 2 * s
  hK : L + s ≤ E.K * E.r
  hkr : E.k ≤ E.r
  hK1 : 1 ≤ E.K

variable {E}

section Step

variable {R₀ R : ℕ} {L s w : ℤ} (h : StepOK E R₀ R L s w)
include h

/-- The region lies in the elongated box. [folklore] -/
theorem region_subset_bigBox : E.region L s ⊆ E.bigBox := by
  intro x hx
  rw [E.mem_region_iff] at hx
  rw [E.mem_bigBox_iff]
  have := h.hk; have := h.hK; have := h.hs
  refine ⟨⟨by omega, by omega⟩, hx.2⟩

/-- The origin is not in the region. [folklore] -/
theorem zero_not_mem_region : (0 : Site d) ∉ E.region L s := by
  rw [E.mem_region_iff]
  simp only [Pi.zero_apply, mul_zero]
  have := h.hk
  omega

/-- The wired cube misses the region. [folklore] -/
theorem cube_disjoint_region : ∀ x ∈ (↑E.cube : Set (Site d)), x ∉ E.region L s := by
  intro x hx hx'
  obtain ⟨h1, -⟩ := E.level_of_mem_cube hx
  rw [E.mem_region_iff] at hx'
  have := h.hk
  omega

/-- **The region is a subbox of `Ω`.** [cite: KozmaNitzan2024, §4 p. 22 (D is a subbox)] -/
theorem isSubbox_region (p : unitInterval) : IsSubbox (E.W p) p (E.region L s) :=
  (((isSubbox_lattW p (E.region L s)).restrW (Finset.coe_subset.2 (region_subset_bigBox h))).wireW
    (cube_disjoint_region h))

/-- The next face lies in the region. [folklore] -/
theorem face_subset_region : E.face (L + s) (w + R) ⊆ E.region L s := by
  intro x hx
  rw [E.mem_face_iff] at hx
  rw [E.mem_region_iff]
  have := h.hs; have := h.hr
  refine ⟨⟨by omega, by omega⟩, fun j hj => ?_⟩
  have := hx.2 j hj
  constructor <;> omega

/-- The next face is nonempty. [folklore] -/
theorem face_nonempty : (E.face (L + s) (w + R)).Nonempty := by
  have := h.hs; have := h.hw
  exact sBox_nonempty E.hσ 0 le_rfl (by omega)

/-- The enlarged current face lies in the region. [folklore] -/
theorem enlarge_face_subset_region :
    Finset.Icc (sLo E.a E.σ 0 L L w - (R₀ : Site d)) (sHi E.a E.σ 0 L L w + (R₀ : Site d)) ⊆ E.region L s := by
  rw [sBox_enlarge E.a E.σ E.hσ]
  intro x hx
  rw [mem_sBox_iff E.hσ] at hx
  simp only [Pi.zero_apply, sub_zero, zero_sub, zero_add] at hx
  rw [E.mem_region_iff]
  have := h.hR; have := h.hs; have := h.hr; have := h.hw
  refine ⟨⟨by omega, by omega⟩, fun j hj => ?_⟩
  have := hx.2 j hj
  constructor <;> omega

/-- **The next face is a target** with respect to (current face, region, `R₀`, quarter faces): from
`v` near the current face, the quarter face of direction `(a, σ)` at scale `ℓ(v) = L + s - σ v_a`,
with transverse signs pointing back to the axis, lands on the next face inside the region (KN p. 22:
"choose `ℓ(v) = ¾r - v₁` … `F(v) = {1} × ∏ [0,1] or [-1,0]`"). [cite: KozmaNitzan2024, §4 pp. 22–23] -/
theorem isTarget_step :
    IsTarget (E.face (L + s) (w + R)) (sLo E.a E.σ 0 L L w) (sHi E.a E.σ 0 L L w) (E.region L s) R₀ (qfList d) := by
  refine ⟨fun v hv => ?_⟩
  rw [sBox_enlarge E.a E.σ E.hσ, mem_sBox_iff E.hσ] at hv
  simp only [Pi.zero_apply, sub_zero, zero_sub, zero_add] at hv
  obtain ⟨⟨hv1, hv2⟩, hvj⟩ := hv
  have hR := h.hR; have hs := h.hs; have hw := h.hw; have hr := h.hr
  have hR' : (R₀ : ℤ) ≤ R := by exact_mod_cast hR
  -- the scale
  have hℓ0 : 0 ≤ L + s - E.σ * v E.a := by omega
  set ℓ : ℕ := (L + s - E.σ * v E.a).toNat with hℓdef
  have hℓ : (ℓ : ℤ) = L + s - E.σ * v E.a := Int.toNat_of_nonneg hℓ0
  -- the signs
  set σu : ℤˣ := if E.σ = 1 then 1 else -1 with hσu
  have hσuval : (σu : ℤ) = E.σ := units_of_sign_val E.hσ
  set τ : Fin d → ℤˣ := fun j => if j = E.a then σu else if 0 < v j then -1 else 1 with hτ
  refine ⟨ℓ, ?_, qfGeom E.a τ, qfGeom_mem_qfList _ _, ?_, ?_⟩
  · have : (R₀ : ℤ) ≤ ℓ := by rw [hℓ]; omega
    exact_mod_cast this
  · -- `v + ℓQ ⊆ D`
    intro y hy
    rw [Geom.Qset, mem_Icc_iff] at hy
    rw [E.mem_region_iff]
    refine ⟨?_, fun j hj => ?_⟩
    · have hya := hy E.a
      simp only [qfGeom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_neg, mul_one] at hya
      have hb := level_bounds_of_abs_le E.hσ (x := v E.a) (y := y E.a) (ℓ := ℓ) (by linarith [hya.1]) hya.2
      constructor <;> omega
    · have hyj := hy j
      simp only [qfGeom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_neg, mul_one] at hyj
      have := hvj j hj
      constructor <;> omega
  · -- `v + ℓF ⊆ T`
    intro y hy
    rw [Geom.Fset, mem_Icc_iff] at hy
    rw [E.mem_face_iff]
    refine ⟨?_, fun j hj => ?_⟩
    · have hya := hy E.a
      simp only [qfGeom, hτ, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hσuval] at hya
      have hyeq : y E.a = v E.a + ℓ * E.σ := le_antisymm hya.2 hya.1
      have := level_of_eq_add E.hσ hyeq
      omega
    · have hyj := hy j
      simp only [qfGeom, hτ, if_neg hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hyj
      have hvj' := hvj j hj
      by_cases hpos : 0 < v j
      · simp only [hpos, if_true, Units.val_neg, Units.val_one] at hyj
        norm_num at hyj
        constructor <;> omega
      · simp only [hpos, if_false, Units.val_one] at hyj
        norm_num at hyj
        constructor <;> omega

end Step

/-- [cite: KozmaNitzan2024, §4 pp. 22–23] -/
theorem levelStep_of_target [NeZero d] (p : unitInterval) (hT : TargetProperty d p)
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℕ, ∀ (E : EData d) (R : ℕ) (L s w : ℤ), StepOK E R₀ R L s w →
      1 - δ < (prodBernoulli (E.W p)).real (⋃ b ∈ E.face L w, openConn (0 : Site d) b) →
        1 - ε < (prodBernoulli (E.W p)).real (⋃ b ∈ E.face (L + s) (w + R), openConn (0 : Site d) b) := by
  obtain ⟨δ, hδ, hH⟩ := hT hε
  obtain ⟨R₀, hR₀⟩ := hH (qfList d) (isHittable_of_mem_qfList p hθ hp1)
  refine ⟨δ, hδ, R₀, fun E R L s w hok hB => ?_⟩
  exact hR₀ (E.W p) E.bigBox (E.region L s) (sLo E.a E.σ 0 L L w) (sHi E.a E.σ 0 L L w)
    (E.face (L + s) (w + R)) 0 (E.finSupp_W p hok.hkr hok.hK1) (isSubbox_region hok p)
    (region_subset_bigBox hok) E.zero_mem_bigBox (zero_not_mem_region hok)
    (enlarge_face_subset_region hok) (isTarget_step hok) (face_subset_region hok) (face_nonempty hok) hB

/-! ## The chain of steps -/

/-- **The side conditions of a chain of `N` steps** from the face `(L, w)` with level increment `s`
and inflation `R`. [cite: KozmaNitzan2024, §4 pp. 22–23] -/
structure ChainOK (E : EData d) (R₀ R N : ℕ) (L s w : ℤ) : Prop where
  hR : R₀ ≤ R
  hs : 2 * (R : ℤ) ≤ s
  hw : s ≤ w
  hr : w + N * R + s + 2 * R ≤ E.r
  hk : (E.k : ℤ) < L - 2 * s
  hK : L + N * s ≤ E.K * E.r
  hkr : E.k ≤ E.r
  hK1 : 1 ≤ E.K

/-- The first step of an admissible chain is admissible. [folklore] -/
theorem ChainOK.stepOK {R₀ R N : ℕ} {L s w : ℤ} (h : ChainOK E R₀ R (N + 1) L s w) {R₁ : ℕ} (hR₁ : R₁ ≤ R) :
    StepOK E R₁ R L s w where
  hR := hR₁
  hs := h.hs
  hw := h.hw
  hr := by
    have h1 := h.hr; have h2 := h.hs
    have h0 : (0 : ℤ) ≤ (N : ℤ) * R := by positivity
    push_cast at h1
    nlinarith
  hk := h.hk
  hK := by
    have h1 := h.hK; have h2 := h.hs
    have h0 : (0 : ℤ) ≤ (N : ℤ) * s := by nlinarith
    push_cast at h1
    nlinarith
  hkr := h.hkr
  hK1 := h.hK1

/-- The remaining chain after the first step is admissible. [folklore] -/
theorem ChainOK.shift {R₀ R N : ℕ} {L s w : ℤ} (h : ChainOK E R₀ R (N + 1) L s w) :
    ChainOK E R₀ R N (L + s) s (w + R) where
  hR := h.hR
  hs := h.hs
  hw := by have := h.hw; have := h.hs; omega
  hr := by have := h.hr; push_cast at this; linarith
  hk := by have := h.hk; have := h.hs; omega
  hK := by have := h.hK; push_cast at this; linarith
  hkr := h.hkr
  hK1 := h.hK1

/-- [cite: KozmaNitzan2024, §4 p. 23] -/
theorem levelChain_of_target [NeZero d] (p : unitInterval) (hT : TargetProperty d p)
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℕ, ∀ (E : EData d) (R : ℕ) (L s w : ℤ), ChainOK E R₀ R N L s w →
      1 - δ < (prodBernoulli (E.W p)).real (⋃ b ∈ E.face L w, openConn (0 : Site d) b) →
        1 - ε < (prodBernoulli (E.W p)).real
          (⋃ b ∈ E.face (L + N * s) (w + N * R), openConn (0 : Site d) b) := by
  induction N generalizing ε with
  | zero =>
    refine ⟨ε, hε, 0, fun E R L s w _ hB => ?_⟩
    simpa using hB
  | succ N ih =>
    obtain ⟨δ', hδ', R₁, h1⟩ := ih hε
    obtain ⟨δ, hδ, R₂, h2⟩ := levelStep_of_target p hT hp1 hθ hδ'
    refine ⟨δ, hδ, max R₁ R₂, fun E R L s w hok hB => ?_⟩
    have hR : max R₁ R₂ ≤ R := hok.hR
    have step := h2 E R L s w (hok.stepOK (le_of_max_le_right hR)) hB
    have hok' : ChainOK E R₁ R N (L + s) s (w + R) :=
      { hok.shift with hR := le_of_max_le_left hR }
    have rest := h1 E R (L + s) s (w + R) hok' step
    have e1 : L + s + (N : ℤ) * s = L + ((N + 1 : ℕ) : ℤ) * s := by push_cast; ring
    have e2 : w + (R : ℤ) + (N : ℤ) * R = w + ((N + 1 : ℕ) : ℤ) * R := by push_cast; ring
    rw [e1, e2] at rest
    exact rest

/-! ## From `Ω` back to `P_p` -/

/-- The origin lies in the cube. [folklore] -/
theorem zero_mem_cube : (0 : Site d) ∈ E.cube := zero_mem_box d E.k

/-- **Connection probabilities in `Ω` are connection probabilities from the cube inside the box**:
`P_Ω(0 ↔ T) = P_p(Λ_k ↔ T in the elongated box)`. [cite: KozmaNitzan2024, §4 pp. 22–23 ("Going back to ℤ^d")] -/
theorem real_W_biUnion_openConn (p : unitInterval) (hkr : E.k ≤ E.r) (hK : 1 ≤ E.K) (T : Finset (Site d)) :
    (prodBernoulli (E.W p)).real (⋃ b ∈ T, openConn (0 : Site d) b) =
      (bondPercolation (zdGraph d) p).real
        (⋃ t ∈ (↑T : Set (Site d)), ⋃ s ∈ (↑E.cube : Set (Site d)), openConnIn (↑E.bigBox : Set (Site d)) s t) := by
  have h1 := prodBernoulli_wireW_real_biUnion_openConn
    (Percolation.Literature.restrW (↑E.bigBox : Set (Site d)) (lattW d p)) (↑E.cube : Set (Site d))
    (Finset.mem_coe.2 E.zero_mem_cube) (↑T : Set (Site d))
  have h2 := prodBernoulli_restrW_real_biUnion₂_openConn (lattW d p) (↑E.bigBox : Set (Site d))
    (Finset.coe_subset.2 (E.cube_subset_bigBox hkr hK)) (↑T : Set (Site d))
  rw [prodBernoulli_lattW] at h2
  rw [W, ← Finset.set_biUnion_coe, h1, h2]

/-! ## The elongated-box geometry and Lemma 11 -/

/-- Scaling the corners of a signed box centred at the origin. [folklore] -/
theorem smul_sLo (a : Fin d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (α β w : ℤ) (ℓ : ℕ) :
    (ℓ : ℤ) • sLo a σ 0 α β w = sLo a σ 0 (ℓ * α) (ℓ * β) (ℓ * w) := by
  funext j
  simp only [sLo, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add, zero_sub]
  by_cases hj : j = a
  · subst hj; simp only [if_true]
    rcases hσ with rfl | rfl
    · simp
    · simp
  · simp only [if_neg hj, mul_neg]

/-- Scaling the corners of a signed box centred at the origin. [folklore] -/
theorem smul_sHi (a : Fin d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (α β w : ℤ) (ℓ : ℕ) :
    (ℓ : ℤ) • sHi a σ 0 α β w = sHi a σ 0 (ℓ * α) (ℓ * β) (ℓ * w) := by
  funext j
  simp only [sHi, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add, zero_sub]
  by_cases hj : j = a
  · subst hj; simp only [if_true]
    rcases hσ with rfl | rfl
    · simp
    · simp
  · simp only [if_neg hj]

end EData

/-- **The elongated-box geometry** (`{K} × [-1,1]^{d-1}`, `[-1,K] × [-1,1]^{d-1}`) of direction `a`
and sign `σ` (KN Lemma 11; `K ≥ 1` so that `F` avoids the unit cube). [cite: KozmaNitzan2024, §4 Lemma 11 (p. 22)] -/
def elongGeom (a : Fin d) (σ : ℤˣ) (K : ℕ) (hK : 1 ≤ K) : Geom d where
  loQ := sLo a σ 0 (-1) K 1
  hiQ := sHi a σ 0 (-1) K 1
  loF := sLo a σ 0 K K 1
  hiF := sHi a σ 0 K K 1
  far := ⟨a, by
    have hK' : (1 : ℤ) ≤ K := by exact_mod_cast hK
    rcases Int.units_eq_one_or σ with h | h
    · left; simp only [sLo, h, if_true, Units.val_one, Pi.zero_apply, zero_add]; exact hK'
    · right
      simp only [sHi, h, if_true, Units.val_neg, Units.val_one, Pi.zero_apply, zero_sub,
        show (-1 : ℤ) ≠ 1 by norm_num, if_false]
      linarith⟩

/-- The sign of a unit of `ℤ` is `±1`. [folklore] -/
theorem units_sign (σ : ℤˣ) : (σ : ℤ) = 1 ∨ (σ : ℤ) = -1 := by
  rcases Int.units_eq_one_or σ with h | h
  · left; simp [h]
  · right; simp [h]

/-- The data of Lemma 11 at scale `r` with cube radius `k`. [folklore] -/
def elongData (a : Fin d) (σ : ℤˣ) (K r k : ℕ) : EData d := ⟨a, σ, units_sign σ, K, r, k⟩

/-- `ℓQ` of the elongated-box geometry is the elongated box at scale `ℓ`. [folklore] -/
theorem elongGeom_Qset (a : Fin d) (σ : ℤˣ) (K : ℕ) (hK : 1 ≤ K) (k ℓ : ℕ) :
    (elongGeom a σ K hK).Qset ℓ 0 = (elongData a σ K ℓ k).bigBox := by
  rw [Geom.Qset, zero_add, zero_add]
  change Finset.Icc ((ℓ : ℤ) • sLo a σ 0 (-1) K 1) ((ℓ : ℤ) • sHi a σ 0 (-1) K 1) =
    sBox a σ 0 (-((ℓ : ℕ) : ℤ)) ((K : ℕ) * (ℓ : ℕ)) (ℓ : ℕ)
  rw [EData.smul_sLo a σ (units_sign σ), EData.smul_sHi a σ (units_sign σ)]
  have e1 : (ℓ : ℤ) * (-1) = -(ℓ : ℤ) := by ring
  have e2 : (ℓ : ℤ) * K = K * ℓ := by ring
  have e3 : (ℓ : ℤ) * 1 = ℓ := by ring
  rw [e1, e2, e3]
  rfl

/-- `ℓF` of the elongated-box geometry is the far face at scale `ℓ`. [folklore] -/
theorem elongGeom_Fset (a : Fin d) (σ : ℤˣ) (K : ℕ) (hK : 1 ≤ K) (k ℓ : ℕ) :
    (elongGeom a σ K hK).Fset ℓ 0 = (elongData a σ K ℓ k).face (ℓ * K) ℓ := by
  rw [Geom.Fset, zero_add, zero_add]
  change Finset.Icc ((ℓ : ℤ) • sLo a σ 0 K K 1) ((ℓ : ℤ) • sHi a σ 0 K K 1) =
    sBox a σ 0 ((ℓ : ℤ) * K) ((ℓ : ℤ) * K) (ℓ : ℕ)
  rw [EData.smul_sLo a σ (units_sign σ), EData.smul_sHi a σ (units_sign σ)]
  have e3 : (ℓ : ℤ) * 1 = ℓ := by ring
  rw [e3]
  rfl

/-- [cite: KozmaNitzan2024, §4 Lemma 11 (pp. 22–23)] -/
theorem isHittable_elongGeom_of_target [NeZero d] (p : unitInterval) (hT : TargetProperty d p)
     (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p)
    (a : Fin d) (σ : ℤˣ) (K : ℕ) (hK : 2 ≤ K) :
    IsHittable p (elongGeom a σ K (by omega)) := by
  have hK1 : 1 ≤ K := by omega
  refine ⟨fun ε hε => ?_⟩
  set N : ℕ := 8 * K - 4 with hNdef
  have hN : (N : ℤ) = 8 * K - 4 := by rw [hNdef]; omega
  obtain ⟨δ, hδ, R₀, hchain⟩ := EData.levelChain_of_target p hT hp1 hθ N hε
  obtain ⟨k, -, n₁, -, hlink⟩ := exists_forall_lt_real_linked_orthantFace p hθ hp1 hδ 0
  set A : ℕ := 3 * K + 3 * K * R₀ + k + n₁ + 8 with hAdef
  refine ⟨k, 8 * A, fun m hm r hr => ?_⟩
  rw [elongGeom_Qset a σ K hK1 k r, elongGeom_Fset a σ K hK1 k r]
  -- the parameters of the chain
  set s : ℕ := r / 8 with hsdef
  have hs1 : 8 * s ≤ r := Nat.mul_div_le r 8
  have hs2 : r < 8 * s + 8 := by
    have := Nat.div_add_mod r 8; have := Nat.mod_lt r (show 0 < 8 by norm_num); omega
  have hAs : A ≤ s := by
    rw [hsdef]; exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by linarith)
  set E : EData d := elongData a σ K r k with hE
  set L₀ : ℤ := K * r - N * s with hL₀
  -- casts
  have hK' : (2 : ℤ) ≤ K := by exact_mod_cast hK
  have hs1' : 8 * (s : ℤ) ≤ r := by exact_mod_cast hs1
  have hs2' : (r : ℤ) < 8 * s + 8 := by exact_mod_cast hs2
  have hAs' : (A : ℤ) ≤ s := by exact_mod_cast hAs
  have hA' : (A : ℤ) = 3 * K + 3 * K * R₀ + k + n₁ + 8 := by rw [hAdef]; push_cast; ring
  have hKr1 : (K : ℤ) * (8 * s) ≤ K * r := mul_le_mul_of_nonneg_left hs1' (by positivity)
  have hKr2 : (K : ℤ) * r ≤ K * (8 * s + 8) := mul_le_mul_of_nonneg_left hs2'.le (by positivity)
  have hKR0 : (0 : ℤ) ≤ K * R₀ := by positivity
  have hNs : (N : ℤ) * s = 8 * (K * s) - 4 * s := by rw [hN]; ring
  have hNR : (N : ℤ) * R₀ = 8 * (K * R₀) - 4 * R₀ := by rw [hN]; ring
  have hKR : (R₀ : ℤ) ≤ K * R₀ := by
    have : (1 : ℤ) * R₀ ≤ K * R₀ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hrK : (r : ℤ) ≤ K * r := by
    have : (1 : ℤ) * r ≤ K * r := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hL₀lo : 4 * (s : ℤ) ≤ L₀ := by rw [hL₀]; linarith
  have hL₀hi : L₀ ≤ 4 * (s : ℤ) + 8 * K := by rw [hL₀]; linarith
  have hL₀r : L₀ ≤ r := by linarith
  -- the chain conditions
  have hok : EData.ChainOK E R₀ R₀ N L₀ s L₀ :=
    { hR := le_rfl
      hs := by linarith
      hw := by linarith
      hr := by
        show L₀ + (N : ℤ) * R₀ + s + 2 * R₀ ≤ (r : ℤ)
        linarith
      hk := by
        show ((k : ℕ) : ℤ) < L₀ - 2 * s
        linarith
      hK := by
        show L₀ + (N : ℤ) * s ≤ (K : ℤ) * r
        rw [hL₀]; linarith
      hkr := by
        show k ≤ r
        have : (k : ℤ) ≤ r := by linarith
        exact_mod_cast this
      hK1 := by show 1 ≤ K; omega }
  -- the initial face: a full face of the cube `Λ_{L₀}` is reached from `Λ_k` (Lemma 9)
  have hL₀0 : 0 ≤ L₀ := by linarith
  set L₀' : ℕ := L₀.toNat with hL₀'
  have hL₀cast : (L₀' : ℤ) = L₀ := Int.toNat_of_nonneg hL₀0
  have hn₁ : n₁ ≤ L₀' := by
    have : (n₁ : ℤ) ≤ L₀' := by rw [hL₀cast]; linarith
    exact_mod_cast this
  set τ₀ : Fin d → ℤˣ := fun _ => σ with hτ₀
  have hinit : 1 - δ < (prodBernoulli (E.W p)).real (⋃ b ∈ E.face L₀ L₀, openConn (0 : Site d) b) := by
    rw [E.real_W_biUnion_openConn p hok.hkr hok.hK1]
    refine (hlink L₀' hn₁ a τ₀).trans_le (measureReal_mono ?_ (measure_ne_top _ _))
    rintro ω ⟨y, hy, x, hx, hω⟩
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_coe]
    refine ⟨x, ?_, y, hy, ?_⟩
    · -- the face orthant lies on the full face
      rw [mem_orthantFace, mem_box] at hx
      obtain ⟨hxb, hxa, -⟩ := hx
      rw [EData.mem_face_iff]
      refine ⟨?_, fun j _ => ?_⟩
      · change (σ : ℤ) * x a = L₀
        rw [← hL₀cast, ← hxa]
      · have := hxb j; rw [hL₀cast] at this; exact this
    · -- `Λ_{L₀} ⊆` the elongated box
      rw [DCT16.mem_openConnIn_iff_pathIn] at hω ⊢
      refine hω.mono fun z hz => ?_
      rw [Finset.mem_coe, mem_box] at hz
      rw [Finset.mem_coe, EData.mem_bigBox_iff]
      have hza := level_bounds_of_symm E.hσ (hz a).1 (hz a).2
      change (-(r : ℤ) ≤ E.σ * z a ∧ E.σ * z a ≤ K * r) ∧ ∀ j, j ≠ a → -(r : ℤ) ≤ z j ∧ z j ≤ r
      rw [hL₀cast] at hza
      refine ⟨⟨by linarith [hza.1], by linarith [hza.2]⟩, fun j _ => ?_⟩
      have := hz j; rw [hL₀cast] at this
      constructor <;> linarith [this.1, this.2]
  -- the chain
  have hend := hchain E R₀ L₀ s L₀ hok hinit
  have hlev : L₀ + (N : ℤ) * s = r * K := by rw [hL₀]; ring
  rw [hlev, E.real_W_biUnion_openConn p hok.hkr hok.hK1] at hend
  -- back to the geometry
  have hwid : L₀ + (N : ℤ) * R₀ ≤ r := by
    have h1 : L₀ + (N : ℤ) * R₀ + s + 2 * R₀ ≤ (r : ℤ) := hok.hr
    have h2 : (0 : ℤ) ≤ s := by positivity
    have h3 : (0 : ℤ) ≤ R₀ := by positivity
    linarith
  refine hend.trans_le (measureReal_mono ?_ (measure_ne_top _ _))
  intro ω hω
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_coe] at hω
  obtain ⟨t, ht, y, hy, hω⟩ := hω
  refine ⟨y, box_mono d hm hy, t, ?_, hω⟩
  rw [EData.mem_face_iff] at ht ⊢
  refine ⟨ht.1, fun j hj => ?_⟩
  have h2 := ht.2 j hj
  change -(r : ℤ) ≤ t j ∧ t j ≤ r
  constructor <;> linarith [h2.1, h2.2]

end KozmaNitzan

end Percolation.Literature

end

/-!
# Kozma–Nitzan, Theorem 6 — Lemma 12: from the centre of a cell into the next cell through a corridor

Sixth proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4), proving Lemma 12
(p. 23–25, Figure 1): under Conjecture 3 and for `0 < p < 1` with `θ(p) > 0`, for every `ε > 0`
there are `δ > 0` and `m` such that for every `r > m`, every direction `(a, σ)` and centre `c`,
and every finitely supported weighting `W` of `ℤ^d` with a lattice subbox
`D = c + {-5r ≤ σ x_a ≤ 25r, |x_j| ≤ 5r}` (`[-5r, 25r] × [-5r, 5r]^{d-1}` up to a lattice
symmetry) and `o ∉ D`:

  `P_W(o ↔ c + [-3r,3r]^d in A) > 1 - δ ⟹ P_W(o ↔ c + 20rσe_a + [-3r,3r]^d in U) > 1 - ε`,

`A` = (support) minus the far part `c + {5r < σ x_a ≤ 25r, |x_j| ≤ 5r}` of `D`, and `U = A ∪ (c +
{5r ≤ σ x_a ≤ 22r, |x_j| ≤ 2r})` the corridor added.

## Proof (KN pp. 24–25)

Here "`3r/2`" is `r + ⌈r/2⌉`.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4, Lemma 12 and its proof, pp. 23–25, Figure 1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Percolation.Literature

open LatticeModels SimpleGraph

namespace KozmaNitzan

variable {d : ℕ}

/-! ## Subboxes inside subboxes; cubes -/

/-- **A box inside a subbox whose interior lies in the interior of the subbox is a subbox** (KN
p. 24: `D = [-5r, 5r]^d` inside the subbox of Lemma 12; p. 24: `[-2r, 22r] × [-2r, 2r]^{d-1}`).
[cite: KozmaNitzan2024, §4 p. 17 (subbox), p. 24] -/
theorem IsSubbox.anti {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D D' : Finset (Site d)}
    (h : IsSubbox W p D) (hsub : D' ⊆ D)
    (hint : ∀ y ∈ D', y ∉ innerBoundary (zdGraph d) D' → y ∉ innerBoundary (zdGraph d) D) :
    IsSubbox W p D' := by
  refine ⟨fun u hu v hv huv => h.inside u (hsub hu) v (hsub hv) huv, fun v hvD' hv x hx => ?_⟩
  by_cases hxD : x ∈ D
  · have hne : x ≠ v := fun heq => hx (heq ▸ hvD')
    rw [h.inside x hxD v (hsub hvD') hne, if_neg]
    intro hadj
    exact hv (mem_innerBoundary_iff.2 ⟨hvD', x, hx, hadj.symm⟩)
  · exact h.outside v (hsub hvD') (hint v hvD' hv) x hxD

/-- Interior points of a smaller box are interior points of a larger box. [folklore] -/
theorem not_mem_innerBoundary_Icc_of_subset {lo hi lo' hi' : Site d} (hlo : lo ≤ lo') (hhi : hi' ≤ hi)
    {y : Site d} (hy : y ∈ Finset.Icc lo' hi') (hint : y ∉ innerBoundary (zdGraph d) (Finset.Icc lo' hi')) :
    y ∉ innerBoundary (zdGraph d) (Finset.Icc lo hi) := by
  rw [mem_innerBoundary_Icc]
  rintro ⟨-, i, hcase⟩
  apply hint
  rw [mem_innerBoundary_Icc]
  refine ⟨hy, i, ?_⟩
  rw [mem_Icc_iff] at hy
  have h1 : lo' i ≤ y i ∧ y i ≤ hi' i := hy i
  have h2 : lo i ≤ lo' i := hlo i
  have h3 : hi' i ≤ hi i := hhi i
  rcases hcase with hc | hc
  · left; omega
  · right; omega

/-- Membership in the cube `c + Λ_u`, coordinatewise. [folklore] -/
theorem mem_cIcc_iff {c : Site d} {u : ℕ} {x : Site d} :
    x ∈ Finset.Icc (c - (u : Site d)) (c + (u : Site d)) ↔ ∀ i, c i - u ≤ x i ∧ x i ≤ c i + u := by
  rw [mem_Icc_iff]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]

/-- The centre lies in the cube. [folklore] -/
theorem center_mem_cIcc (c : Site d) (u : ℕ) : c ∈ Finset.Icc (c - (u : Site d)) (c + (u : Site d)) := by
  rw [mem_cIcc_iff]; intro i; constructor <;> omega

/-! ## The setup of Lemma 12 -/

/-- The data of Lemma 12: direction `(a, σ)`, centre `c`, scale `r`, the weighting `W` with its
support `Sfin`, and the source vertex `o`. [cite: KozmaNitzan2024, §4 Lemma 12 (p. 23)] -/
structure CData (d : ℕ) where
  /-- the direction of the corridor -/
  a : Fin d
  /-- its sign -/
  σ : ℤ
  /-- `σ = ±1` -/
  hσ : σ = 1 ∨ σ = -1
  /-- the centre of the cell -/
  c : Site d
  /-- the scale -/
  r : ℕ
  /-- the weighting -/
  W : Sym2 (Site d) → unitInterval
  /-- its finite support -/
  Sfin : Finset (Site d)
  /-- the source vertex -/
  o : Site d

namespace CData

variable (S : CData d)

/-- The subbox `c + {-5r ≤ σ x_a ≤ 25r, |x_j| ≤ 5r}` (KN: `D = [-5r, 25r] × [-5r, 5r]^{d-1}`).
[cite: KozmaNitzan2024, §4 Lemma 12 (p. 23)] -/
def bigD : Finset (Site d) := sBox S.a S.σ S.c (-(5 * S.r : ℤ)) (25 * S.r) (5 * S.r)

/-- The far part `c + {5r < σ x_a ≤ 25r, |x_j| ≤ 5r}` (KN: `[5r, 25r] × [-5r, 5r]^{d-1}`, here without
its first layer, which belongs to the near cube). [cite: KozmaNitzan2024, §4 Lemma 12 (p. 23, A)] -/
def farE : Finset (Site d) := sBox S.a S.σ S.c (5 * S.r + 1) (25 * S.r) (5 * S.r)

/-- The near cube `c + [-5r, 5r]^d` (KN: `D = [-5r, 5r]^d` of the first `d` steps). [cite: KozmaNitzan2024, §4 p. 24] -/
def nearQ : Finset (Site d) := Finset.Icc (S.c - ((5 * S.r : ℕ) : Site d)) (S.c + ((5 * S.r : ℕ) : Site d))

/-- The subgraph `A` = support minus the far part. [cite: KozmaNitzan2024, §4 Lemma 12 (p. 23, A)] -/
def Aset : Finset (Site d) := S.Sfin \ S.farE

/-- The corridor `c + {5r ≤ σ x_a ≤ 22r, |x_j| ≤ 2r}` (KN: `[5r, 22r] × [-2r, 2r]^{d-1}`).
[cite: KozmaNitzan2024, §4 Lemma 12 (p. 23, U)] -/
def corridor : Finset (Site d) := sBox S.a S.σ S.c (5 * S.r) (22 * S.r) (2 * S.r)

/-- The subgraph `U = A ∪` corridor. [cite: KozmaNitzan2024, §4 Lemma 12 (p. 23, U)] -/
def Uset : Finset (Site d) := S.Aset ∪ S.corridor

/-- The subbox `c + {-2r ≤ σ x_a ≤ 22r, |x_j| ≤ 2r}` of the last step (KN: `D = [-2r, 22r] × [-2r, 2r]^{d-1}`).
[cite: KozmaNitzan2024, §4 p. 24] -/
def Dcorr : Finset (Site d) := sBox S.a S.σ S.c (-(2 * S.r : ℤ)) (22 * S.r) (2 * S.r)

/-- The centre `c + 20rσ e_a` of the next cell. [cite: KozmaNitzan2024, §4 Lemma 12 (p. 23)] -/
def cnext : Site d := fun j => if j = S.a then S.c S.a + 20 * S.r * S.σ else S.c j

/-- Half of `3r`, rounded up in its fractional part: `ℓ_h = r + ⌈r/2⌉` (KN's `3r/2`). [folklore] -/
def lh : ℕ := S.r + (S.r + 1) / 2

/-- The half-widths after `k` halvings with inflation `R`: `ℓ_h + kR` in the first `k` coordinates,
`3r + kR` in the others (KN p. 24). [cite: KozmaNitzan2024, §4 p. 24] -/
def hwid (k R : ℕ) : Site d := fun i => if (i : ℕ) < k then (S.lh + k * R : ℤ) else (3 * S.r + k * R : ℤ)

/-- The cube after `k` halvings. [cite: KozmaNitzan2024, §4 p. 24 (B, T of the first d steps)] -/
def Bk (k R : ℕ) : Finset (Site d) := Finset.Icc (S.c - S.hwid k R) (S.c + S.hwid k R)

/-- **The hypotheses of Lemma 12**: `W` finitely supported on `Sfin ⊇ D`, `D` a lattice subbox at
`p`, and `o ∈ Sfin \ D`. [cite: KozmaNitzan2024, §4 Lemma 12 (p. 23)] -/
structure Hyp (S : CData d) (p : unitInterval) : Prop where
  fin : FinSupp S.W S.Sfin
  sub : IsSubbox S.W p S.bigD
  DS : S.bigD ⊆ S.Sfin
  o_mem : S.o ∈ S.Sfin
  o_not : S.o ∉ S.bigD

/-! ## Memberships -/

/-- Membership in `D`. [folklore] -/
theorem mem_bigD_iff {x : Site d} : x ∈ S.bigD ↔
    (-(5 * S.r : ℤ) ≤ S.σ * (x S.a - S.c S.a) ∧ S.σ * (x S.a - S.c S.a) ≤ 25 * S.r) ∧
      ∀ j, j ≠ S.a → S.c j - 5 * S.r ≤ x j ∧ x j ≤ S.c j + 5 * S.r := by
  rw [bigD, mem_sBox_iff S.hσ]

/-- Membership in the far part. [folklore] -/
theorem mem_farE_iff {x : Site d} : x ∈ S.farE ↔
    (5 * (S.r : ℤ) + 1 ≤ S.σ * (x S.a - S.c S.a) ∧ S.σ * (x S.a - S.c S.a) ≤ 25 * S.r) ∧
      ∀ j, j ≠ S.a → S.c j - 5 * S.r ≤ x j ∧ x j ≤ S.c j + 5 * S.r := by
  rw [farE, mem_sBox_iff S.hσ]

/-- Membership in the corridor. [folklore] -/
theorem mem_corridor_iff {x : Site d} : x ∈ S.corridor ↔
    (5 * (S.r : ℤ) ≤ S.σ * (x S.a - S.c S.a) ∧ S.σ * (x S.a - S.c S.a) ≤ 22 * S.r) ∧
      ∀ j, j ≠ S.a → S.c j - 2 * S.r ≤ x j ∧ x j ≤ S.c j + 2 * S.r := by
  rw [corridor, mem_sBox_iff S.hσ]

/-- Membership in the subbox of the last step. [folklore] -/
theorem mem_Dcorr_iff {x : Site d} : x ∈ S.Dcorr ↔
    (-(2 * S.r : ℤ) ≤ S.σ * (x S.a - S.c S.a) ∧ S.σ * (x S.a - S.c S.a) ≤ 22 * S.r) ∧
      ∀ j, j ≠ S.a → S.c j - 2 * S.r ≤ x j ∧ x j ≤ S.c j + 2 * S.r := by
  rw [Dcorr, mem_sBox_iff S.hσ]

/-- Membership in the near cube. [folklore] -/
theorem mem_nearQ_iff {x : Site d} : x ∈ S.nearQ ↔ ∀ i, S.c i - 5 * S.r ≤ x i ∧ x i ≤ S.c i + 5 * S.r := by
  rw [nearQ, mem_cIcc_iff]; push_cast; rfl

/-- Membership in `B_k`. [folklore] -/
theorem mem_Bk_iff {k R : ℕ} {x : Site d} : x ∈ S.Bk k R ↔ ∀ i, S.c i - S.hwid k R i ≤ x i ∧ x i ≤ S.c i + S.hwid k R i := by
  rw [Bk, mem_Icc_iff]
  simp only [Pi.sub_apply, Pi.add_apply]

/-- The value of `hwid`. [folklore] -/
theorem hwid_apply (k R : ℕ) (i : Fin d) :
    S.hwid k R i = if (i : ℕ) < k then (S.lh + k * R : ℤ) else (3 * S.r + k * R : ℤ) := rfl

/-- Bounds on `hwid`: `ℓ_h + kR ≤ hwid ≤ 3r + kR`. [folklore] -/
theorem hwid_bounds (k R : ℕ) (i : Fin d) :
    (S.lh : ℤ) + k * R ≤ S.hwid k R i ∧ S.hwid k R i ≤ 3 * S.r + k * R := by
  have hlh : (S.lh : ℤ) ≤ 3 * S.r := by
    have : S.lh ≤ 3 * S.r := by unfold lh; omega
    exact_mod_cast this
  rw [hwid_apply]
  split_ifs
  · exact ⟨le_rfl, by linarith⟩
  · exact ⟨by linarith, le_rfl⟩

/-- `2 ℓ_h` is `3r` or `3r + 1`. [folklore] -/
theorem two_lh : 3 * (S.r : ℤ) ≤ 2 * S.lh ∧ 2 * (S.lh : ℤ) ≤ 3 * S.r + 1 := by
  have : 3 * S.r ≤ 2 * S.lh ∧ 2 * S.lh ≤ 3 * S.r + 1 := by unfold lh; omega
  exact_mod_cast this

/-- The near cube lies in `D`. [folklore] -/
theorem nearQ_subset_bigD : S.nearQ ⊆ S.bigD := by
  intro x hx
  rw [S.mem_nearQ_iff] at hx
  rw [S.mem_bigD_iff]
  have ha := hx S.a
  have hb := level_bounds_of_abs_le S.hσ (x := S.c S.a) (y := x S.a) (ℓ := 5 * S.r) (by linarith) (by linarith)
  refine ⟨⟨?_, ?_⟩, fun j _ => hx j⟩
  · have : S.σ * (x S.a - S.c S.a) = S.σ * x S.a - S.σ * S.c S.a := by ring
    rw [this]; linarith
  · have : S.σ * (x S.a - S.c S.a) = S.σ * x S.a - S.σ * S.c S.a := by ring
    rw [this]; linarith

/-- The near cube misses the far part. [folklore] -/
theorem nearQ_disjoint_farE {x : Site d} (hx : x ∈ S.nearQ) : x ∉ S.farE := by
  intro hx'
  rw [S.mem_nearQ_iff] at hx
  rw [S.mem_farE_iff] at hx'
  have ha := hx S.a
  have hb := level_bounds_of_abs_le S.hσ (x := S.c S.a) (y := x S.a) (ℓ := 5 * S.r) (by linarith) (by linarith)
  have : S.σ * (x S.a - S.c S.a) = S.σ * x S.a - S.σ * S.c S.a := by ring
  rw [this] at hx'
  linarith [hx'.1.1]

variable {S}

/-- The near cube lies in `A`. [folklore] -/
theorem nearQ_subset_Aset {p : unitInterval} (h : S.Hyp p) : S.nearQ ⊆ S.Aset := by
  intro x hx
  exact Finset.mem_sdiff.2 ⟨h.DS (S.nearQ_subset_bigD hx), S.nearQ_disjoint_farE hx⟩

/-- `o ∈ A`. [folklore] -/
theorem o_mem_Aset {p : unitInterval} (h : S.Hyp p) : S.o ∈ S.Aset := by
  refine Finset.mem_sdiff.2 ⟨h.o_mem, fun ho => h.o_not ?_⟩
  rw [S.mem_farE_iff] at ho
  rw [S.mem_bigD_iff]
  exact ⟨⟨by linarith [ho.1.1], ho.1.2⟩, ho.2⟩

/-- `o` is not in the near cube. [folklore] -/
theorem o_not_mem_nearQ {p : unitInterval} (h : S.Hyp p) : S.o ∉ S.nearQ := fun ho => h.o_not (S.nearQ_subset_bigD ho)

/-- **The near cube is a subbox of `W`** (its interior lies in the interior of `D`). [cite: KozmaNitzan2024, §4 p. 24] -/
theorem isSubbox_nearQ {p : unitInterval} (h : S.Hyp p) : IsSubbox S.W p S.nearQ := by
  refine h.sub.anti S.nearQ_subset_bigD fun y hy hint => ?_
  rw [bigD, sBox]
  refine not_mem_innerBoundary_Icc_of_subset (fun i => ?_) (fun i => ?_) hy hint
  · simp only [sLo, Pi.sub_apply, Pi.natCast_apply]
    by_cases hi : i = S.a
    · subst hi; simp only [if_true]
      rcases S.hσ with h1 | h1
      · rw [if_pos h1]; omega
      · rw [if_neg (by rw [h1]; norm_num)]; omega
    · rw [if_neg hi]; omega
  · simp only [sHi, Pi.add_apply, Pi.natCast_apply]
    by_cases hi : i = S.a
    · subst hi; simp only [if_true]
      rcases S.hσ with h1 | h1
      · rw [if_pos h1]; omega
      · rw [if_neg (by rw [h1]; norm_num)]; omega
    · rw [if_neg hi]; omega

/-- **The last subbox is a subbox of `W`** (its interior lies in the interior of `D`). [cite: KozmaNitzan2024, §4 p. 24] -/
theorem isSubbox_Dcorr {p : unitInterval} (h : S.Hyp p) : IsSubbox S.W p S.Dcorr := by
  have hsub : S.Dcorr ⊆ S.bigD := by
    intro x hx
    rw [S.mem_Dcorr_iff] at hx
    rw [S.mem_bigD_iff]
    refine ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, fun j hj => ?_⟩
    have := hx.2 j hj
    constructor <;> linarith [this.1, this.2]
  refine h.sub.anti hsub fun y hy hint => ?_
  rw [bigD, sBox]
  rw [Dcorr, sBox] at hy hint
  refine not_mem_innerBoundary_Icc_of_subset (fun i => ?_) (fun i => ?_) hy hint
  · simp only [sLo]
    by_cases hi : i = S.a
    · subst hi; simp only [if_true]
      rcases S.hσ with h1 | h1
      · rw [if_pos h1, if_pos h1]; omega
      · rw [if_neg (by rw [h1]; norm_num), if_neg (by rw [h1]; norm_num)]; omega
    · rw [if_neg hi, if_neg hi]; omega
  · simp only [sHi]
    by_cases hi : i = S.a
    · subst hi; simp only [if_true]
      rcases S.hσ with h1 | h1
      · rw [if_pos h1, if_pos h1]; omega
      · rw [if_neg (by rw [h1]; norm_num), if_neg (by rw [h1]; norm_num)]; omega
    · rw [if_neg hi, if_neg hi]; omega

/-! ## The halving steps (KN p. 24) -/

/-- `B_k` lies in the near cube as long as `3r + kR ≤ 5r`. [folklore] -/
theorem Bk_subset_nearQ {k R : ℕ} (hkR : (k : ℤ) * R ≤ 2 * S.r) : S.Bk k R ⊆ S.nearQ := by
  intro x hx
  rw [S.mem_Bk_iff] at hx
  rw [S.mem_nearQ_iff]
  intro i
  have := hx i
  have hb := S.hwid_bounds k R i
  constructor <;> linarith [this.1, this.2, hb.2]

/-- The enlarged `B_k` lies in the near cube as long as `3r + kR + R₀ ≤ 5r`. [folklore] -/
theorem enlarge_Bk_subset_nearQ {k R R₀ : ℕ} (hkR : (k : ℤ) * R + R₀ ≤ 2 * S.r) :
    Finset.Icc (S.c - S.hwid k R - (R₀ : Site d)) (S.c + S.hwid k R + (R₀ : Site d)) ⊆ S.nearQ := by
  intro x hx
  rw [mem_Icc_iff] at hx
  rw [S.mem_nearQ_iff]
  intro i
  have := hx i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at this
  have hb := S.hwid_bounds k R i
  constructor <;> linarith [this.1, this.2, hb.2]

/-- `B_k` is nonempty. [folklore] -/
theorem Bk_nonempty (k R : ℕ) : (S.Bk k R).Nonempty := by
  refine ⟨S.c, ?_⟩
  rw [S.mem_Bk_iff]
  intro i
  have hb := S.hwid_bounds k R i
  have : (0 : ℤ) ≤ S.lh + k * R := by positivity
  constructor <;> linarith [hb.1]

/-- **The next cube is a target of the current one** in the near cube, via the quarter face of the
halved coordinate `k` pointing back to the centre at scale `ℓ_h` (KN p. 24: "`ℓ(v) = 3r/2`,
`Q(v) = [-1,1]^d`, `F(v) = {-sign v_k} × ∏ [0,1] or [-1,0]`"). [cite: KozmaNitzan2024, §4 p. 24] -/
theorem isTarget_halving {k R R₀ : ℕ} (hk : k < d) (hR : R₀ ≤ R) (hR₀ : R₀ ≤ S.lh)
    (hfit : ((S.r + 1) / 2 : ℕ) + (k : ℤ) * R + R₀ ≤ S.r) :
    IsTarget (S.Bk (k + 1) R) (S.c - S.hwid k R) (S.c + S.hwid k R) S.nearQ R₀ (qfList d) := by
  refine ⟨fun v hv => ?_⟩
  rw [mem_Icc_iff] at hv
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv
  set i₀ : Fin d := ⟨k, hk⟩ with hi₀
  have hR' : (R₀ : ℤ) ≤ R := by exact_mod_cast hR
  have hlh := S.two_lh
  have hlhr : (S.r : ℤ) ≤ S.lh := by
    have : S.r ≤ S.lh := by unfold lh; omega
    exact_mod_cast this
  have hfit' : (S.lh : ℤ) + k * R + R₀ ≤ 2 * S.r := by
    have : ((S.r + 1) / 2 : ℕ) + (S.r : ℤ) = S.lh := by unfold lh; push_cast; ring
    linarith
  -- the signs, pointing back to the centre
  set τ : Fin d → ℤˣ := fun j => if S.c j < v j then -1 else 1 with hτ
  refine ⟨S.lh, hR₀, qfGeom i₀ τ, qfGeom_mem_qfList _ _, ?_, ?_⟩
  · -- `v + ℓQ ⊆ nearQ`
    intro y hy
    rw [Geom.Qset, mem_Icc_iff] at hy
    rw [S.mem_nearQ_iff]
    intro i
    have hyi := hy i
    simp only [qfGeom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_neg, mul_one] at hyi
    have hvi := hv i
    have hb := S.hwid_bounds k R i
    constructor <;> linarith [hyi.1, hyi.2, hvi.1, hvi.2, hb.2]
  · -- `v + ℓF ⊆ B_{k+1}`
    intro y hy
    rw [Geom.Fset, mem_Icc_iff] at hy
    rw [S.mem_Bk_iff]
    intro i
    have hyi := hy i
    have hvi := hv i
    rw [S.hwid_apply] at hvi
    simp only [qfGeom, hτ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hyi
    have hkR0 : (0 : ℤ) ≤ ((k : ℤ) + 1) * R := by positivity
    by_cases hi : i = i₀
    · -- the halved coordinate
      subst hi
      have hlt : ¬((i₀ : ℕ) < k) := by simp [hi₀]
      have hlt' : ((i₀ : ℕ) < k + 1) := by simp [hi₀]
      simp only [if_true] at hyi
      rw [if_neg hlt] at hvi
      rw [S.hwid_apply, if_pos hlt']
      push_cast
      by_cases hpos : S.c i₀ < v i₀
      · simp only [hpos, if_true, Units.val_neg, Units.val_one] at hyi
        norm_num at hyi
        constructor <;> linarith [hyi.1, hyi.2]
      · simp only [hpos, if_false, Units.val_one] at hyi
        norm_num at hyi
        push Not at hpos
        constructor <;> linarith [hyi.1, hyi.2]
    · -- the other coordinates
      have hne : ¬(i = i₀) := hi
      simp only [hne, if_false] at hyi
      have hmono : (if (i : ℕ) < k then (S.lh : ℤ) + k * R else 3 * S.r + k * R) + R ≤ S.hwid (k + 1) R i := by
        rw [S.hwid_apply]
        have hik : (i : ℕ) ≠ k := fun h' => hi (by rw [hi₀]; exact Fin.ext h')
        by_cases hlt : (i : ℕ) < k
        · rw [if_pos hlt, if_pos (by omega)]; push_cast; linarith
        · rw [if_neg hlt, if_neg (by omega)]; push_cast; linarith
      have hlow : (S.lh : ℤ) ≤ S.hwid (k + 1) R i := by
        have := (S.hwid_bounds (k + 1) R i).1
        have h0 : (0 : ℤ) ≤ (k + 1 : ℕ) * R := by positivity
        push_cast at this h0
        linarith
      by_cases hpos : S.c i < v i
      · simp only [hpos, if_true, Units.val_neg, Units.val_one] at hyi
        norm_num at hyi
        constructor <;> linarith [hyi.1, hyi.2]
      · simp only [hpos, if_false, Units.val_one] at hyi
        norm_num at hyi
        push Not at hpos
        constructor <;> linarith [hyi.1, hyi.2]

/-- [cite: KozmaNitzan2024, §4 p. 24] -/
theorem halvingStep_of_target [NeZero d] (p : unitInterval) (hT : TargetProperty d p)
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℕ, ∀ (S : CData d), S.Hyp p → ∀ (k R : ℕ), k < d → R₀ ≤ R → R₀ ≤ S.lh →
      ((S.r + 1) / 2 : ℕ) + (k : ℤ) * R + R ≤ S.r →
      1 - δ < (prodBernoulli (restrW (↑S.Aset : Set (Site d)) S.W)).real (⋃ b ∈ S.Bk k R, openConn S.o b) →
        1 - ε < (prodBernoulli (restrW (↑S.Aset : Set (Site d)) S.W)).real (⋃ b ∈ S.Bk (k + 1) R, openConn S.o b) := by
  obtain ⟨δ, hδ, hH⟩ := hT hε
  obtain ⟨R₀, hR₀⟩ := hH (qfList d) (isHittable_of_mem_qfList p hθ hp1)
  refine ⟨δ, hδ, R₀, fun S hS k R hk hR hRlh hfit hB => ?_⟩
  have hR' : (R₀ : ℤ) ≤ R := by exact_mod_cast hR
  have hfit0 : ((S.r + 1) / 2 : ℕ) + (k : ℤ) * R + R₀ ≤ S.r := by linarith
  have hkR : (k : ℤ) * R + R₀ ≤ 2 * S.r := by
    have : (0 : ℤ) ≤ ((S.r + 1) / 2 : ℕ) := by positivity
    linarith
  have hkR1 : ((k + 1 : ℕ) : ℤ) * R ≤ 2 * S.r := by push_cast; linarith
  exact hR₀ (restrW (↑S.Aset : Set (Site d)) S.W) S.Aset S.nearQ (S.c - S.hwid k R) (S.c + S.hwid k R)
    (S.Bk (k + 1) R) S.o (finSupp_restrW S.Aset S.W)
    ((isSubbox_nearQ hS).restrW (Finset.coe_subset.2 (nearQ_subset_Aset hS)))
    (nearQ_subset_Aset hS) (o_mem_Aset hS) (o_not_mem_nearQ hS) (S.enlarge_Bk_subset_nearQ hkR)
    (S.isTarget_halving hk hR hRlh hfit0) (S.Bk_subset_nearQ hkR1) (S.Bk_nonempty _ _) hB

/-- [cite: KozmaNitzan2024, §4 p. 24 ("We continue this way, each time halving one dimension")] -/
theorem halvingChain_of_target [NeZero d] (p : unitInterval) (hT : TargetProperty d p)
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℕ, ∀ (S : CData d), S.Hyp p → ∀ (k R : ℕ), k + n ≤ d → R₀ ≤ R → R₀ ≤ S.lh →
      ((S.r + 1) / 2 : ℕ) + (d : ℤ) * R + R ≤ S.r →
      1 - δ < (prodBernoulli (restrW (↑S.Aset : Set (Site d)) S.W)).real (⋃ b ∈ S.Bk k R, openConn S.o b) →
        1 - ε < (prodBernoulli (restrW (↑S.Aset : Set (Site d)) S.W)).real (⋃ b ∈ S.Bk (k + n) R, openConn S.o b) := by
  induction n generalizing ε with
  | zero =>
    refine ⟨ε, hε, 0, fun S _ k R _ _ _ _ hB => ?_⟩
    simpa using hB
  | succ n ih =>
    obtain ⟨δ', hδ', R₁, h1⟩ := ih hε
    obtain ⟨δ, hδ, R₂, h2⟩ := halvingStep_of_target p hT hp1 hθ hδ'
    refine ⟨δ, hδ, max R₁ R₂, fun S hS k R hkn hR hRlh hfit hB => ?_⟩
    have hfitk : ((S.r + 1) / 2 : ℕ) + (k : ℤ) * R + R ≤ S.r := by
      have : (k : ℤ) * R ≤ (d : ℤ) * R :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k ≤ d)) (by positivity)
      linarith
    have step := h2 S hS k R (by omega) (le_of_max_le_right hR) ((le_max_right _ _).trans hRlh) hfitk hB
    have rest := h1 S hS (k + 1) R (by omega) (le_of_max_le_left hR) ((le_max_left _ _).trans hRlh) hfit step
    have e : k + 1 + n = k + (n + 1) := by ring
    rw [e] at rest
    exact rest

end CData

/-! ## Elongated geometries around an arbitrary vertex -/

/-- Translating the corners of a signed box centred at the origin. [folklore] -/
theorem add_sLo (a : Fin d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (u : Site d) (α β w : ℤ) :
    u + sLo a σ 0 α β w = sLo a σ u α β w := by
  funext j
  simp only [sLo, Pi.add_apply, Pi.zero_apply, zero_add, zero_sub]
  by_cases hj : j = a
  · subst hj; simp only [if_true]
    rcases hσ with rfl | rfl
    · simp
    · simp; ring
  · simp only [if_neg hj]; ring

/-- Translating the corners of a signed box centred at the origin. [folklore] -/
theorem add_sHi (a : Fin d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (u : Site d) (α β w : ℤ) :
    u + sHi a σ 0 α β w = sHi a σ u α β w := by
  funext j
  simp only [sHi, Pi.add_apply, Pi.zero_apply, zero_add, zero_sub]
  by_cases hj : j = a
  · subst hj; simp only [if_true]
    rcases hσ with rfl | rfl
    · simp
    · simp; ring
  · simp only [if_neg hj]

/-- `v + ℓQ` of the elongated geometry is a signed box around `v`. [folklore] -/
theorem elongGeom_Qset_eq (a : Fin d) (σ : ℤˣ) (K : ℕ) (hK : 1 ≤ K) (ℓ : ℕ) (v : Site d) :
    (elongGeom a σ K hK).Qset ℓ v = sBox a σ v (-(ℓ : ℤ)) (ℓ * K) ℓ := by
  rw [Geom.Qset]
  change Finset.Icc (v + (ℓ : ℤ) • sLo a σ 0 (-1) K 1) (v + (ℓ : ℤ) • sHi a σ 0 (-1) K 1) = _
  rw [EData.smul_sLo a σ (units_sign σ), EData.smul_sHi a σ (units_sign σ),
    add_sLo a σ (units_sign σ), add_sHi a σ (units_sign σ)]
  have e1 : (ℓ : ℤ) * (-1) = -(ℓ : ℤ) := by ring
  have e3 : (ℓ : ℤ) * 1 = ℓ := by ring
  rw [e1, e3]
  rfl

/-- `v + ℓF` of the elongated geometry is the far face of that signed box. [folklore] -/
theorem elongGeom_Fset_eq (a : Fin d) (σ : ℤˣ) (K : ℕ) (hK : 1 ≤ K) (ℓ : ℕ) (v : Site d) :
    (elongGeom a σ K hK).Fset ℓ v = sBox a σ v (ℓ * K) (ℓ * K) ℓ := by
  rw [Geom.Fset]
  change Finset.Icc (v + (ℓ : ℤ) • sLo a σ 0 K K 1) (v + (ℓ : ℤ) • sHi a σ 0 K K 1) = _
  rw [EData.smul_sLo a σ (units_sign σ), EData.smul_sHi a σ (units_sign σ),
    add_sLo a σ (units_sign σ), add_sHi a σ (units_sign σ)]
  have e3 : (ℓ : ℤ) * 1 = ℓ := by ring
  rw [e3]
  rfl

/-- All elongated geometries of aspect `K` (all directions and signs: KN's "and its image by
lattice symmetries", p. 30). [cite: KozmaNitzan2024, §4 p. 23, p. 30] -/
def elongList (d K : ℕ) (hK : 1 ≤ K) : List (Geom d) :=
  (Finset.univ : Finset (Fin d × ℤˣ)).toList.map fun x => elongGeom x.1 x.2 K hK

/-- Every elongated geometry of aspect `K` is in the list. [folklore] -/
theorem elongGeom_mem_elongList (a : Fin d) (σ : ℤˣ) (K : ℕ) (hK : 1 ≤ K) :
    elongGeom a σ K hK ∈ elongList d K hK :=
  List.mem_map.2 ⟨(a, σ), Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩

/-- [cite: KozmaNitzan2024, §4 Lemma 11 (p. 22)] -/
theorem isHittable_of_mem_elongList_of_target [NeZero d] (p : unitInterval) (hT : TargetProperty d p)
     (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p)
    (K : ℕ) (hK : 2 ≤ K) : ∀ g ∈ elongList d K (by omega), IsHittable p g := by
  intro g hg
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hg
  exact isHittable_elongGeom_of_target p hT hp1 hθ x.1 x.2 K hK

/-! ## The corridor step (KN pp. 24–25) -/

namespace CData

variable {S : CData d}

variable (S) in
/-- The cube of radius `u` around the next centre. [cite: KozmaNitzan2024, §4 Lemma 12 (p. 23)] -/
def Tn (u : ℕ) : Finset (Site d) := Finset.Icc (S.cnext - (u : Site d)) (S.cnext + (u : Site d))

variable (S) in
/-- Membership in `Tn u`, with the level measured from `c`: `|σ(x_a - c_a) - 20r| ≤ u` and
`|x_j - c_j| ≤ u`. [folklore] -/
theorem mem_Tn_iff {u : ℕ} {x : Site d} : x ∈ S.Tn u ↔
    (20 * (S.r : ℤ) - u ≤ S.σ * (x S.a - S.c S.a) ∧ S.σ * (x S.a - S.c S.a) ≤ 20 * S.r + u) ∧
      ∀ j, j ≠ S.a → S.c j - u ≤ x j ∧ x j ≤ S.c j + u := by
  rw [Tn, mem_cIcc_iff]
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have := h S.a
      simp only [cnext, if_true] at this
      have hsq := sign_mul_self S.hσ
      rcases S.hσ with h1 | h1
      · rw [h1] at this ⊢; constructor <;> nlinarith [this.1, this.2]
      · rw [h1] at this ⊢; constructor <;> nlinarith [this.1, this.2]
    · have := h j
      simp only [cnext, if_neg hj] at this
      exact this
  · rintro ⟨ha, hj⟩ i
    by_cases hi : i = S.a
    · subst hi
      simp only [cnext, if_true]
      rcases S.hσ with h1 | h1
      · rw [h1] at ha ⊢; constructor <;> nlinarith [ha.1, ha.2]
      · rw [h1] at ha ⊢; constructor <;> nlinarith [ha.1, ha.2]
    · simp only [cnext, if_neg hi]
      exact hj i hi

variable (S) in
/-- `Tn u` is nonempty. [folklore] -/
theorem Tn_nonempty (u : ℕ) : (S.Tn u).Nonempty := ⟨S.cnext, center_mem_cIcc _ _⟩

/-- The last subbox lies in `U` (its near part in the near cube, the rest in the corridor).
[cite: KozmaNitzan2024, §4 p. 24] -/
theorem Dcorr_subset_Uset {p : unitInterval} (h : S.Hyp p) : S.Dcorr ⊆ S.Uset := by
  intro x hx
  rw [S.mem_Dcorr_iff] at hx
  rw [Uset, Finset.mem_union]
  by_cases hlev : S.σ * (x S.a - S.c S.a) ≤ 5 * S.r
  · left
    refine nearQ_subset_Aset h ?_
    rw [S.mem_nearQ_iff]
    intro i
    by_cases hi : i = S.a
    · subst hi
      rcases S.hσ with h1 | h1
      · rw [h1] at hx hlev; constructor <;> nlinarith [hx.1.1, hx.1.2]
      · rw [h1] at hx hlev; constructor <;> nlinarith [hx.1.1, hx.1.2]
    · have := hx.2 i hi; constructor <;> linarith [this.1, this.2]
  · right
    rw [S.mem_corridor_iff]
    push Not at hlev
    exact ⟨⟨hlev.le, hx.1.2⟩, hx.2⟩

/-- `o` is not in the last subbox. [folklore] -/
theorem o_not_mem_Dcorr {p : unitInterval} (h : S.Hyp p) : S.o ∉ S.Dcorr := by
  intro ho
  apply h.o_not
  rw [S.mem_Dcorr_iff] at ho
  rw [S.mem_bigD_iff]
  refine ⟨⟨by linarith [ho.1.1], by linarith [ho.1.2]⟩, fun j hj => ?_⟩
  have := ho.2 j hj
  constructor <;> linarith [this.1, this.2]

/-- **The cube around the next centre is a target** of the small cube `B_d` in the last subbox, via
the elongated geometry of aspect `88` in direction `(a, σ)` at scale `ℓ(u) = ⌊(20r - σ(u_a - c_a))/88⌋`
(KN p. 25). Requires `5R₀ + 5 ≤ r`, `r ≥ 44` and `4(ℓ_h + dR + R₀) + 4 ≤ 7r`.
[cite: KozmaNitzan2024, §4 p. 25] -/
theorem isTarget_corridor {R R₀ : ℕ} (h44 : 44 ≤ S.r) (hRc : 5 * R₀ + 5 ≤ S.r)
    (hΔ : 4 * ((S.lh : ℤ) + d * R + R₀) + 4 ≤ 7 * S.r) :
    IsTarget (S.Tn (2 * S.r)) (S.c - S.hwid d R) (S.c + S.hwid d R) S.Dcorr R₀ (elongList d 88 (by norm_num)) := by
  refine ⟨fun u hu => ?_⟩
  rw [mem_Icc_iff] at hu
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hu
  have hw : ∀ i, S.hwid d R i = S.lh + d * R := fun i => by rw [S.hwid_apply, if_pos i.2]
  set Δ : ℤ := S.lh + d * R + R₀ with hΔdef
  have hu' : ∀ i, S.c i - Δ ≤ u i ∧ u i ≤ S.c i + Δ := fun i => by
    have := hu i; rw [hw i] at this; constructor <;> linarith [this.1, this.2]
  have hRc' : 5 * (R₀ : ℤ) + 5 ≤ S.r := by exact_mod_cast hRc
  have h44' : (44 : ℤ) ≤ S.r := by exact_mod_cast h44
  have hΔ0 : 0 ≤ Δ := by positivity
  -- the level of `u`
  set lev : ℤ := S.σ * (u S.a - S.c S.a) with hlev
  have hlevb : -Δ ≤ lev ∧ lev ≤ Δ := by
    have := hu' S.a
    have hb := level_bounds_of_abs_le S.hσ (x := S.c S.a) (y := u S.a) (ℓ := Δ) (by linarith) (by linarith)
    have : lev = S.σ * u S.a - S.σ * S.c S.a := by rw [hlev]; ring
    rw [this]; constructor <;> linarith [hb.1, hb.2]
  -- the scale
  have hx0 : 0 ≤ (20 * S.r - lev) / 88 := Int.ediv_nonneg (by linarith) (by norm_num)
  set ℓ : ℕ := ((20 * S.r - lev) / 88).toNat with hℓdef
  have hℓ : (ℓ : ℤ) = (20 * S.r - lev) / 88 := Int.toNat_of_nonneg hx0
  have hℓ1 : 88 * (ℓ : ℤ) ≤ 20 * S.r - lev := by rw [hℓ]; exact Int.mul_ediv_self_le (by norm_num)
  have hℓ2 : 20 * (S.r : ℤ) - lev < 88 * ℓ + 88 := by
    rw [hℓ]; exact Int.lt_mul_ediv_self_add (show (0 : ℤ) < 88 by norm_num)
  -- the sign as a unit
  set σu : ℤˣ := if S.σ = 1 then 1 else -1 with hσu
  have hσuval : (σu : ℤ) = S.σ := units_of_sign_val S.hσ
  refine ⟨ℓ, ?_, elongGeom S.a σu 88 (by norm_num), elongGeom_mem_elongList _ _ _ _, ?_, ?_⟩
  · have : (R₀ : ℤ) ≤ ℓ := by linarith
    exact_mod_cast this
  · -- `u + ℓQ ⊆ Dcorr`
    intro y hy
    rw [elongGeom_Qset_eq, hσuval, mem_sBox_iff S.hσ] at hy
    rw [S.mem_Dcorr_iff]
    obtain ⟨⟨hy1, hy2⟩, hyj⟩ := hy
    have hsplit : S.σ * (y S.a - S.c S.a) = S.σ * (y S.a - u S.a) + lev := by rw [hlev]; ring
    refine ⟨⟨?_, ?_⟩, fun j hj => ?_⟩
    · rw [hsplit]; linarith
    · rw [hsplit]; push_cast at hy2; linarith
    · have := hyj j hj; have := hu' j
      constructor <;> linarith
  · -- `u + ℓF ⊆ Tn (2r)`
    intro y hy
    rw [elongGeom_Fset_eq, hσuval, mem_sBox_iff S.hσ] at hy
    rw [S.mem_Tn_iff]
    obtain ⟨⟨hy1, hy2⟩, hyj⟩ := hy
    push_cast at hy1 hy2
    have hsplit : S.σ * (y S.a - S.c S.a) = S.σ * (y S.a - u S.a) + lev := by rw [hlev]; ring
    refine ⟨⟨?_, ?_⟩, fun j hj => ?_⟩
    · rw [hsplit]; push_cast; linarith
    · rw [hsplit]; push_cast; linarith
    · have := hyj j hj; have := hu' j
      push_cast
      constructor <;> linarith

/-- [cite: KozmaNitzan2024, §4 pp. 24–25] -/
theorem corridorStep_of_target [NeZero d] (p : unitInterval) (hT : TargetProperty d p)
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℕ, ∀ (S : CData d), S.Hyp p → ∀ R : ℕ, 44 ≤ S.r → 5 * R₀ + 5 ≤ S.r →
      4 * ((S.lh : ℤ) + d * R + R₀) + 4 ≤ 7 * S.r →
      1 - δ < (prodBernoulli (restrW (↑S.Uset : Set (Site d)) S.W)).real (⋃ b ∈ S.Bk d R, openConn S.o b) →
        1 - ε < (prodBernoulli (restrW (↑S.Uset : Set (Site d)) S.W)).real (⋃ b ∈ S.Tn (2 * S.r), openConn S.o b) := by
  obtain ⟨δ, hδ, hH⟩ := hT hε
  obtain ⟨R₀, hR₀⟩ := hH (elongList d 88 (by norm_num)) (isHittable_of_mem_elongList_of_target p hT hp1 hθ 88 (by norm_num))
  refine ⟨δ, hδ, R₀, fun S hS R h44 hRc hΔ hB => ?_⟩
  -- `B_d⟨R₀⟩ ⊆ Dcorr` and `Tn (2r) ⊆ Dcorr`
  have hw : ∀ i, S.hwid d R i = S.lh + d * R := fun i => by rw [S.hwid_apply, if_pos i.2]
  have hRc' : 5 * (R₀ : ℤ) + 5 ≤ S.r := by exact_mod_cast hRc
  have hencl : Finset.Icc (S.c - S.hwid d R - (R₀ : Site d)) (S.c + S.hwid d R + (R₀ : Site d)) ⊆ S.Dcorr := by
    intro x hx
    rw [mem_Icc_iff] at hx
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hx
    rw [S.mem_Dcorr_iff]
    have hlh : (0 : ℤ) ≤ S.lh := by positivity
    refine ⟨?_, fun j hj => ?_⟩
    · have := hx S.a; rw [hw] at this
      have hb := level_bounds_of_abs_le S.hσ (x := S.c S.a) (y := x S.a) (ℓ := S.lh + d * R + R₀)
        (by linarith) (by linarith)
      have e : S.σ * (x S.a - S.c S.a) = S.σ * x S.a - S.σ * S.c S.a := by ring
      rw [e]; constructor <;> linarith [hb.1, hb.2]
    · have := hx j; rw [hw] at this
      constructor <;> linarith [this.1, this.2]
  have hTD : S.Tn (2 * S.r) ⊆ S.Dcorr := by
    intro x hx
    rw [S.mem_Tn_iff] at hx
    rw [S.mem_Dcorr_iff]
    push_cast at hx
    refine ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, fun j hj => ?_⟩
    have := hx.2 j hj
    constructor <;> linarith [this.1, this.2]
  exact hR₀ (restrW (↑S.Uset : Set (Site d)) S.W) S.Uset S.Dcorr (S.c - S.hwid d R) (S.c + S.hwid d R)
    (S.Tn (2 * S.r)) S.o (finSupp_restrW S.Uset S.W)
    ((isSubbox_Dcorr hS).restrW (Finset.coe_subset.2 (Dcorr_subset_Uset hS)))
    (Dcorr_subset_Uset hS) (Finset.mem_union_left _ (o_mem_Aset hS)) (o_not_mem_Dcorr hS) hencl
    (S.isTarget_corridor h44 hRc hΔ) hTD (S.Tn_nonempty _) hB

/-! ## Lemma 12 -/

/-- `B_0` is the cube `c + [-3r, 3r]^d`. [folklore] -/
theorem Bk_zero (R : ℕ) : S.Bk 0 R = Finset.Icc (S.c - ((3 * S.r : ℕ) : Site d)) (S.c + ((3 * S.r : ℕ) : Site d)) := by
  have : S.hwid 0 R = ((3 * S.r : ℕ) : Site d) := by
    funext i; rw [S.hwid_apply, if_neg (Nat.not_lt_zero _), Pi.natCast_apply]; push_cast; ring
  rw [Bk, this]

/-- `A ⊆ U`. [folklore] -/
theorem Aset_subset_Uset : S.Aset ⊆ S.Uset := Finset.subset_union_left

/-- [cite: KozmaNitzan2024, §4 Lemma 12 (pp. 23–25)] -/
theorem corridorLemma_of_target [NeZero d] (p : unitInterval) (hT : TargetProperty d p)
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ m : ℕ, ∀ S : CData d, S.Hyp p → m ≤ S.r →
      1 - δ < (prodBernoulli S.W).real
          (⋃ b ∈ Finset.Icc (S.c - ((3 * S.r : ℕ) : Site d)) (S.c + ((3 * S.r : ℕ) : Site d)),
            openConnIn (↑S.Aset : Set (Site d)) S.o b) →
        1 - ε < (prodBernoulli S.W).real (⋃ b ∈ S.Tn (3 * S.r), openConnIn (↑S.Uset : Set (Site d)) S.o b) := by
  obtain ⟨δc, hδc, Rc, hcorr⟩ := corridorStep_of_target p hT hp1 hθ hε
  obtain ⟨δh, hδh, Rh, hhalf⟩ := halvingChain_of_target p hT hp1 hθ d hδc
  set R : ℕ := max Rc Rh with hRdef
  refine ⟨δh, hδh, 100 * (d + 1) * (R + 1), fun S hS hm hA => ?_⟩
  -- arithmetic
  have hR1 : Rc ≤ R := le_max_left _ _
  have hR2 : Rh ≤ R := le_max_right _ _
  have hm' : 100 * ((d : ℤ) + 1) * (R + 1) ≤ S.r := by exact_mod_cast hm
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hR0 : (0 : ℤ) ≤ R := by positivity
  have hdR : (0 : ℤ) ≤ d * R := by positivity
  have hexp : 100 * ((d : ℤ) + 1) * (R + 1) = 100 * (d * R) + 100 * d + 100 * R + 100 := by ring
  have hlh := S.two_lh
  have hhalf' : (((S.r + 1) / 2 : ℕ) : ℤ) + (S.r : ℤ) = S.lh := by unfold CData.lh; push_cast; ring
  have hRc' : (Rc : ℤ) ≤ R := by exact_mod_cast hR1
  have hRh' : (Rh : ℤ) ≤ R := by exact_mod_cast hR2
  -- into the restricted weighting on `A`
  have ho : S.o ∈ (↑S.Aset : Set (Site d)) := Finset.mem_coe.2 (o_mem_Aset hS)
  have h0 : 1 - δh < (prodBernoulli (restrW (↑S.Aset : Set (Site d)) S.W)).real (⋃ b ∈ S.Bk 0 R, openConn S.o b) := by
    rw [S.Bk_zero, ← Finset.set_biUnion_coe, prodBernoulli_restrW_real_biUnion_openConn S.W _ ho,
      Finset.set_biUnion_coe]
    exact hA
  -- the halving chain
  have h1 := hhalf S hS 0 R (by omega) hR2 ?_ ?_ h0
  rotate_left
  · have : (R : ℤ) ≤ S.lh := by linarith
    have : (Rh : ℤ) ≤ S.lh := by linarith
    exact_mod_cast this
  · have hdRh : (d : ℤ) * R ≤ d * R := le_rfl
    linarith
  rw [zero_add] at h1
  -- from `A` to `U`
  have hoU : S.o ∈ (↑S.Uset : Set (Site d)) := Finset.mem_coe.2 (S.Aset_subset_Uset (o_mem_Aset hS))
  have h2 : 1 - δc < (prodBernoulli (restrW (↑S.Uset : Set (Site d)) S.W)).real (⋃ b ∈ S.Bk d R, openConn S.o b) := by
    rw [← Finset.set_biUnion_coe, prodBernoulli_restrW_real_biUnion_openConn S.W _ hoU]
    rw [← Finset.set_biUnion_coe, prodBernoulli_restrW_real_biUnion_openConn S.W _ ho] at h1
    exact h1.trans_le (measureReal_mono (biUnion_openConnIn_mono (Finset.coe_subset.2 S.Aset_subset_Uset) S.o subset_rfl)
      (measure_ne_top _ _))
  -- the corridor step
  have h3 := hcorr S hS R ?_ ?_ ?_ h2
  rotate_left
  · have : (44 : ℤ) ≤ S.r := by linarith
    exact_mod_cast this
  · have : 5 * (Rc : ℤ) + 5 ≤ S.r := by linarith
    exact_mod_cast this
  · have : (d : ℤ) * Rc ≤ d * R := mul_le_mul_of_nonneg_left hRc' hd0
    nlinarith
  -- back to `W`, and the larger target cube
  rw [← Finset.set_biUnion_coe, prodBernoulli_restrW_real_biUnion_openConn S.W _ hoU] at h3
  rw [← Finset.set_biUnion_coe]
  refine h3.trans_le (measureReal_mono (biUnion_openConnIn_mono subset_rfl S.o (Finset.coe_subset.2 ?_))
    (measure_ne_top _ _))
  intro x hx
  rw [S.mem_Tn_iff] at hx ⊢
  push_cast at hx ⊢
  refine ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, fun j hj => ?_⟩
  have := hx.2 j hj
  constructor <;> linarith [this.1, this.2]

end CData

end KozmaNitzan

end Percolation.Literature

end
