import Percolation.Literature.HistorySiteRenormalization
import Percolation.Literature.KozmaNitzanCorridor
import Percolation.Literature.MacroRenormalization
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 — the cells of the exploration process (static geometry)

Seventh proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4), the lattice geometry of the
proof of Theorem 6 (pp. 25–26, Figures 2–3): the macro-lattice `ℤ²` is embedded in the coordinate
plane `(x₁, x₂)` of `ℤ^d` (`d ≥ 3`) at spacing `20r`, `v ↦ cen v = 20r (0, v₀, v₁, 0, …, 0)`, and to
`v ∈ ℤ²` and a macro-direction `δ` are attached

* the cubes `Q_v = cen v + [-5r, 5r]^d`, `M_v = cen v + [-3r, 3r]^d` (KN p. 26);
* the between-box `Btw v δ` = the part `cen v + {5r < σ x_a < 15r} × [-5r,5r]^{d-1}` of KN's
  "edge" `E_{v,x}` strictly between `Q_v` and `Q_x`, `x = v + δ` (here HALF-OPEN in the long
  direction, so that boxes of distinct macro-edges are disjoint: KN's closed boxes
  `20vr + [5r, 25r] × [-5r, 5r]^{d-1}` of a vertex and of a turning neighbour share an edge);
  `Ewv v δ = Btw v δ ∪ Q_x` is KN's `E_{v,x}` and `Efar v δ` the same set as one signed box;
* the stubs `Stub v δ j = cen v + {5r ≤ σ x_a ≤ 5r + 10sj} × [-2r, 2r]^{d-1}` (KN's `H^j_{v,x}`,
  `10s = 10r/K`, `r = Ks`), the corridor `Hfull` (`H_{v,x} = [5r, 22r] × [-2r,2r]^{d-1}`), its
  faces `Face v δ j` (`F^j_{v,x}`), and the subbox `bigD v δ` (`[-5r, 25r] × [-5r,5r]^{d-1}`);
* the CELL `Cell v = cen v + [-10r, 10r]² × [-5r, 5r]^{d-2}` and the stub ZONES
  `Zone v δ = cen v + {10r ≤ σ x_a ≤ 15r - 10s} × [-2r, 2r]^{d-1}` (the part of a maximal stub
  inside the neighbouring cell), and `Cover det = ⋃_{u ∈ det} (Cell u ∪ ⋃_δ Zone u δ)`: the
  explored region of the process always lies in the cover of the determined macro-vertices, and
  the cover is SEPARATED (no common or adjacent vertices, `Sep`) from the cube `Q_x` of an
  undetermined `x` and from `Efar v δ'` when `v` and `v + δ'` are undetermined
  (`cover_sep_Q`, `cover_sep_Efar`) — the geometric content of KN's (29), (31) and of the
  "straightforward" equivalences of pp. 28–29.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 pp. 25–29, Figures 2–3.
-/

noncomputable section

open MeasureTheory

namespace Percolation.Literature

open LatticeModels SimpleGraph GadgetSystem

namespace KozmaNitzan

variable {d : ℕ}

/-! ## Separation -/

/-- Two sets of vertices are **separated**: no common vertex and no edge of `ℤ^d` between them.
[folklore] -/
def Sep (A B : Set (Site d)) : Prop := ∀ y ∈ A, ∀ z ∈ B, y ≠ z ∧ ¬(zdGraph d).Adj y z

/-- A gap of `2` in one coordinate separates two vertices. [folklore] -/
theorem sep_of_gap {y z : Site d} (i : Fin d) (h : y i + 2 ≤ z i ∨ z i + 2 ≤ y i) :
    y ≠ z ∧ ¬(zdGraph d).Adj y z := by
  refine ⟨fun hyz => ?_, fun hadj => ?_⟩
  · rw [hyz] at h; omega
  · have := abs_sub_le_one_of_adj hadj i
    rw [abs_le] at this
    omega

/-- Separation is inherited by subsets. [folklore] -/
theorem Sep.mono {A A' B B' : Set (Site d)} (h : Sep A B) (hA : A' ⊆ A) (hB : B' ⊆ B) : Sep A' B' :=
  fun y hy z hz => h y (hA hy) z (hB hz)

/-- Separated sets are disjoint. [folklore] -/
theorem Sep.not_mem {A B : Set (Site d)} (h : Sep A B) {y : Site d} (hy : y ∈ A) : y ∉ B :=
  fun hy' => (h y hy y hy').1 rfl

/-! ## The parameters and the planar embedding -/

/-- **The parameters of the cells**: dimension `d ≥ 3`, the number of stub levels `K ≥ 20` and the
stub increment `s ≥ 1`; the scale is `r = Ks` (KN p. 26: "`r` … divisible by `K`").
[cite: KozmaNitzan2024, §4 pp. 25–26] -/
structure Cells (d : ℕ) where
  /-- `d ≥ 3` -/
  hd : 3 ≤ d
  /-- the number of stub levels -/
  K : ℕ
  /-- the stub increment `r / K` -/
  s : ℕ
  /-- `K ≥ 20` -/
  hK : 20 ≤ K
  /-- `s ≥ 1` -/
  hs : 1 ≤ s

namespace Cells

variable (C : Cells d)

/-- The scale `r = Ks`. [cite: KozmaNitzan2024, §4 p. 26] -/
def r : ℕ := C.K * C.s

/-- The first in-plane axis `x₁`. [cite: KozmaNitzan2024, §4 p. 26 ((v₁, v₂, 0, …, 0))] -/
def ax0 : Fin d := ⟨1, by have := C.hd; omega⟩

/-- The second in-plane axis `x₂`. [cite: KozmaNitzan2024, §4 p. 26] -/
def ax1 : Fin d := ⟨2, by have := C.hd; omega⟩

/-- The two in-plane axes differ. [folklore] -/
theorem ax0_ne_ax1 : C.ax0 ≠ C.ax1 := by simp [ax0, ax1, Fin.ext_iff]

/-- The in-plane axis of a planar index. [folklore] -/
def pax (i : Fin 2) : Fin d := if i = 0 then C.ax0 else C.ax1

/-- `pax` is injective. [folklore] -/
theorem pax_injective : Function.Injective C.pax := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h (by simp [pax, C.ax0_ne_ax1])
  · exact absurd h (by simp [pax, C.ax0_ne_ax1.symm])
  · rfl

/-- The lattice axis of a macro-direction. [folklore] -/
def axOf (δ : MDir) : Fin d := C.pax δ.1

/-- The other planar index. [folklore] -/
def oth (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- `oth i ≠ i`. [folklore] -/
theorem oth_ne (i : Fin 2) : oth i ≠ i := by fin_cases i <;> simp [oth]

/-- The sign of a macro-direction. [folklore] -/
def sgOf (δ : MDir) : ℤ := if δ.2 then 1 else -1

/-- The sign is `±1`. [folklore] -/
theorem sgOf_sign (δ : MDir) : sgOf δ = 1 ∨ sgOf δ = -1 := by
  unfold sgOf; split_ifs <;> simp

/-- The step of a macro-direction in its own planar coordinate is its sign. [folklore] -/
theorem stepVec_apply_fst (δ : MDir) : stepVec δ δ.1 = sgOf δ := by
  unfold stepVec sgOf; split_ifs <;> simp

/-- The step of a macro-direction vanishes in the other planar coordinate. [folklore] -/
theorem stepVec_apply_oth (δ : MDir) : stepVec δ (oth δ.1) = 0 := by
  have h := oth_ne δ.1
  unfold stepVec; split_ifs <;> simp [h]

/-- Two macro-vertices with the same two planar coordinates are equal. [folklore] -/
theorem eq_of_coords {u v : Site 2} (a : Fin 2) (ha : u a = v a) (ht : u (oth a) = v (oth a)) : u = v := by
  funext i
  fin_cases a <;> fin_cases i <;> simp_all [oth]

/-- Distinct planar indices: each is the `oth` of the other. [folklore] -/
theorem eq_oth_of_ne {i i' : Fin 2} (h : i ≠ i') : i = oth i' := by
  revert h; revert i i'; decide

/-- `oth` is an involution. [folklore] -/
theorem oth_oth (i : Fin 2) : oth (oth i) = i := by fin_cases i <;> rfl

/-- The scale as a nonnegative integer, positive. [folklore] -/
theorem r_pos : 1 ≤ C.r := by
  have := C.hK; have := C.hs
  unfold r; exact one_le_mul (by omega) this

/-- `10s ≤ r/2` (as `20s ≤ r`). [folklore] -/
theorem twenty_s_le_r : 20 * C.s ≤ C.r := by
  unfold r; exact Nat.mul_le_mul_right _ C.hK

/-- **The centre of the cell of `v ∈ ℤ²`**: `cen v = 20r (0, v₀, v₁, 0, …, 0)` (KN p. 26:
"the `v` on the right hand sides are in fact `(v₁, v₂, 0, …, 0) ∈ ℤ^d`").
[cite: KozmaNitzan2024, §4 p. 26 (M_v, Q_v)] -/
def cen (v : Site 2) : Site d := fun j => if j = C.ax0 then 20 * C.r * v 0 else if j = C.ax1 then 20 * C.r * v 1 else 0

/-- The planar coordinates of the centre. [folklore] -/
theorem cen_pax (v : Site 2) (i : Fin 2) : C.cen v (C.pax i) = 20 * C.r * v i := by
  fin_cases i
  · simp [cen, pax]
  · simp [cen, pax, C.ax0_ne_ax1.symm]

/-- The non-planar coordinates of the centre vanish. [folklore] -/
theorem cen_of_ne (v : Site 2) {j : Fin d} (h0 : j ≠ C.ax0) (h1 : j ≠ C.ax1) : C.cen v j = 0 := by
  simp [cen, h0, h1]

/-- A non-planar axis is not a `pax`. [folklore] -/
theorem ne_pax_iff {j : Fin d} : (∀ i, j ≠ C.pax i) ↔ j ≠ C.ax0 ∧ j ≠ C.ax1 := by
  constructor
  · intro h; exact ⟨h 0, by simpa [pax] using h 1⟩
  · rintro ⟨h0, h1⟩ i; fin_cases i <;> simp [pax, h0, h1]

/-- The centre of the target of a directed macro-edge: `cen (v + δ) = cen v + 20rσ e_a`.
[cite: KozmaNitzan2024, §4 p. 26] -/
theorem cen_add_stepVec (v : Site 2) (δ : MDir) (j : Fin d) :
    C.cen (v + stepVec δ) j = if j = C.axOf δ then C.cen v j + 20 * C.r * sgOf δ else C.cen v j := by
  by_cases hj : ∃ i, j = C.pax i
  · obtain ⟨i, rfl⟩ := hj
    rw [C.cen_pax, C.cen_pax]
    by_cases hi : i = δ.1
    · subst hi
      rw [Pi.add_apply, stepVec_apply_fst]
      split_ifs with h
      · ring
      · exact absurd rfl h
    · have hne : C.pax i ≠ C.axOf δ := fun h => hi (C.pax_injective h)
      rw [if_neg hne, Pi.add_apply]
      have : stepVec δ i = 0 := by
        unfold stepVec; split_ifs <;> simp [Ne.symm hi]
      rw [this]; ring
  · push Not at hj
    obtain ⟨h0, h1⟩ := C.ne_pax_iff.1 hj
    have hne : j ≠ C.axOf δ := hj δ.1
    rw [if_neg hne, C.cen_of_ne _ h0 h1, C.cen_of_ne _ h0 h1]

/-! ## The boxes -/

/-- `Q_v = cen v + [-5r, 5r]^d`. [cite: KozmaNitzan2024, §4 p. 26 (Q_v)] -/
def Q (v : Site 2) : Finset (Site d) :=
  Finset.Icc (C.cen v - ((5 * C.r : ℕ) : Site d)) (C.cen v + ((5 * C.r : ℕ) : Site d))

/-- `M_v = cen v + [-3r, 3r]^d`. [cite: KozmaNitzan2024, §4 p. 26 (M_v)] -/
def M (v : Site 2) : Finset (Site d) :=
  Finset.Icc (C.cen v - ((3 * C.r : ℕ) : Site d)) (C.cen v + ((3 * C.r : ℕ) : Site d))

/-- The between-box of the directed macro-edge `(v, δ)`: `cen v + {5r < σ x_a < 15r} × [-5r,5r]^{d-1}`
(the part of KN's `E_{v,x}` strictly between the two cubes). [cite: KozmaNitzan2024, §4 p. 26 (E_{v,x})] -/
def Btw (v : Site 2) (δ : MDir) : Finset (Site d) :=
  sBox (C.axOf δ) (sgOf δ) (C.cen v) (5 * C.r + 1) (15 * C.r - 1) (5 * C.r)

/-- `E_{v,x}` as one signed box: `cen v + {5r < σ x_a ≤ 25r} × [-5r,5r]^{d-1}`. [cite: KozmaNitzan2024, §4 p. 26 (E_{v,x})] -/
def Efar (v : Site 2) (δ : MDir) : Finset (Site d) :=
  sBox (C.axOf δ) (sgOf δ) (C.cen v) (5 * C.r + 1) (25 * C.r) (5 * C.r)

/-- `E_{v,x} = Btw ∪ Q_x`. [cite: KozmaNitzan2024, §4 p. 26 (E_{v,x})] -/
def Ewv (v : Site 2) (δ : MDir) : Finset (Site d) := C.Btw v δ ∪ C.Q (v + stepVec δ)

/-- The stub `H^j_{v,x} = cen v + {5r ≤ σ x_a ≤ 5r + 10sj} × [-2r,2r]^{d-1}`. [cite: KozmaNitzan2024, §4 p. 26 (H^j_{v,x})] -/
def Stub (v : Site 2) (δ : MDir) (j : ℕ) : Finset (Site d) :=
  sBox (C.axOf δ) (sgOf δ) (C.cen v) (5 * C.r) (5 * C.r + 10 * C.s * j) (2 * C.r)

/-- The corridor `H_{v,x} = cen v + {5r ≤ σ x_a ≤ 22r} × [-2r,2r]^{d-1}`. [cite: KozmaNitzan2024, §4 p. 26 (H_{v,x})] -/
def Hfull (v : Site 2) (δ : MDir) : Finset (Site d) :=
  sBox (C.axOf δ) (sgOf δ) (C.cen v) (5 * C.r) (22 * C.r) (2 * C.r)

/-- The face `F^j_{v,x} = cen v + {σ x_a = 5r + 10sj} × [-2r,2r]^{d-1}`. [cite: KozmaNitzan2024, §4 p. 30 (F^j_{v,x})] -/
def Face (v : Site 2) (δ : MDir) (j : ℕ) : Finset (Site d) :=
  sBox (C.axOf δ) (sgOf δ) (C.cen v) (5 * C.r + 10 * C.s * j) (5 * C.r + 10 * C.s * j) (2 * C.r)

/-- The subbox `Q_v ∪ E_{v,x} = cen v + {-5r ≤ σ x_a ≤ 25r} × [-5r,5r]^{d-1}`. [cite: KozmaNitzan2024, §4 p. 31 (D = E_{v,x} ∪ Q_v)] -/
def bigD (v : Site 2) (δ : MDir) : Finset (Site d) :=
  sBox (C.axOf δ) (sgOf δ) (C.cen v) (-(5 * C.r : ℤ)) (25 * C.r) (5 * C.r)

/-- The half-widths of a cell: `10r` in the plane, `5r` across. [folklore] -/
def wC : Site d := fun j => if j = C.ax0 ∨ j = C.ax1 then 10 * C.r else 5 * C.r

/-- **The cell** `cen v + [-10r, 10r]² × [-5r, 5r]^{d-2}`. [folklore] -/
def Cell (v : Site 2) : Finset (Site d) := Finset.Icc (C.cen v - C.wC) (C.cen v + C.wC)

/-- **The stub zone** `cen v + {10r ≤ σ x_a ≤ 15r - 10s} × [-2r,2r]^{d-1}`: the part of the longest
stub `H^{K-1}_{v,x}` inside the cell of `x`. [cite: KozmaNitzan2024, §4 p. 26 (H^j for j ≤ K-1)] -/
def Zone (v : Site 2) (δ : MDir) : Finset (Site d) :=
  sBox (C.axOf δ) (sgOf δ) (C.cen v) (10 * C.r) (15 * C.r - 10 * C.s) (2 * C.r)

/-- **The cover of a set of macro-vertices**: their cells and stub zones. [folklore] -/
def Cover (det : Set (Site 2)) : Set (Site d) :=
  ⋃ u ∈ det, ((↑(C.Cell u) : Set (Site d)) ∪ ⋃ δ : MDir, ↑(C.Zone u δ))

/-- Cells and zones of a member lie in the cover. [folklore] -/
theorem subset_cover {det : Set (Site 2)} {u : Site 2} (hu : u ∈ det) :
    (↑(C.Cell u) : Set (Site d)) ∪ (⋃ δ : MDir, ↑(C.Zone u δ)) ⊆ C.Cover det := by
  intro y hy
  simp only [Cover, Set.mem_iUnion, exists_prop]
  exact ⟨u, hu, hy⟩

/-! ## Planar coordinates of the boxes -/

/-- Different macro-coordinates give a gap of `20r` between the centres. [folklore] -/
theorem cen_gap {u v : Site 2} {i : Fin 2} (h : u i ≠ v i) :
    20 * (C.r : ℤ) * u i + 20 * C.r ≤ 20 * C.r * v i ∨ 20 * (C.r : ℤ) * v i + 20 * C.r ≤ 20 * C.r * u i := by
  have hr : (0 : ℤ) ≤ 20 * C.r := by positivity
  rcases lt_or_gt_of_ne h with hlt | hlt
  · left
    have : u i + 1 ≤ v i := hlt
    nlinarith
  · right
    have : v i + 1 ≤ u i := hlt
    nlinarith

/-- A difference of at least `2` in a macro-coordinate gives a gap of `40r`. [folklore] -/
theorem cen_gap_two {u v : Site 2} {i : Fin 2} (h : v i + 2 ≤ u i) :
    20 * (C.r : ℤ) * v i + 40 * C.r ≤ 20 * C.r * u i := by
  have hr : (0 : ℤ) ≤ 20 * C.r := by positivity
  nlinarith

/-- Distinct macro-vertices differ in a planar coordinate. [folklore] -/
theorem exists_ne_of_ne {u v : Site 2} (h : u ≠ v) : ∃ i, u i ≠ v i := by
  by_contra hcon
  push Not at hcon
  exact h (funext hcon)

/-- **Planar coordinates of a signed box along `axOf δ`**: the level in the coordinate `δ.1` and the
width in the other planar coordinate. [folklore] -/
theorem planar_of_mem_sBox {v : Site 2} {δ : MDir} {α β w : ℤ} {y : Site d}
    (hy : y ∈ sBox (C.axOf δ) (sgOf δ) (C.cen v) α β w) :
    (α ≤ sgOf δ * (y (C.pax δ.1) - 20 * C.r * v δ.1) ∧ sgOf δ * (y (C.pax δ.1) - 20 * C.r * v δ.1) ≤ β) ∧
      (20 * (C.r : ℤ) * v (oth δ.1) - w ≤ y (C.pax (oth δ.1)) ∧ y (C.pax (oth δ.1)) ≤ 20 * C.r * v (oth δ.1) + w) := by
  rw [mem_sBox_iff (sgOf_sign δ)] at hy
  obtain ⟨hlev, htr⟩ := hy
  have hc := C.cen_pax v δ.1
  change C.cen v (C.axOf δ) = _ at hc
  rw [hc] at hlev
  refine ⟨hlev, ?_⟩
  have hne : C.pax (oth δ.1) ≠ C.axOf δ := fun h => oth_ne δ.1 (C.pax_injective h)
  have := htr _ hne
  rw [C.cen_pax] at this
  exact this

/-- Planar coordinates of a symmetric cube around `cen v`. [folklore] -/
theorem planar_of_mem_cIcc {v : Site 2} {u : ℕ} {y : Site d}
    (hy : y ∈ Finset.Icc (C.cen v - (u : Site d)) (C.cen v + (u : Site d))) (i : Fin 2) :
    20 * (C.r : ℤ) * v i - u ≤ y (C.pax i) ∧ y (C.pax i) ≤ 20 * C.r * v i + u := by
  rw [mem_cIcc_iff] at hy
  have := hy (C.pax i)
  rw [C.cen_pax] at this
  exact this

/-- Planar coordinates of a cell. [folklore] -/
theorem planar_of_mem_Cell {v : Site 2} {y : Site d} (hy : y ∈ C.Cell v) (i : Fin 2) :
    20 * (C.r : ℤ) * v i - 10 * C.r ≤ y (C.pax i) ∧ y (C.pax i) ≤ 20 * C.r * v i + 10 * C.r := by
  rw [Cell, mem_Icc_iff] at hy
  have := hy (C.pax i)
  have hw : C.wC (C.pax i) = 10 * C.r := by
    unfold wC; rw [if_pos]; fin_cases i <;> simp [pax]
  simp only [Pi.sub_apply, Pi.add_apply, hw, C.cen_pax] at this
  exact this

/-! ## Separation of cells and zones from the targets -/

/-- **A cell is separated from the cube of another macro-vertex.** [folklore] -/
theorem cell_sep_Q {u x : Site 2} (hux : u ≠ x) : Sep (↑(C.Cell u) : Set (Site d)) ↑(C.Q x) := by
  intro y hy z hz
  obtain ⟨i, hi⟩ := exists_ne_of_ne hux
  have h1 := C.planar_of_mem_Cell (Finset.mem_coe.1 hy) i
  have h2 := C.planar_of_mem_cIcc (Finset.mem_coe.1 hz) i
  have hr : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  push_cast at h2
  refine sep_of_gap (C.pax i) ?_
  rcases C.cen_gap hi with h | h
  · left; linarith
  · right; linarith

/-- **A cell is separated from `Efar v δ'`** when `u ∉ {v, v + δ'}`. [folklore] -/
theorem cell_sep_Efar {u v : Site 2} {δ' : MDir} (huv : u ≠ v) (hux : u ≠ v + stepVec δ') :
    Sep (↑(C.Cell u) : Set (Site d)) ↑(C.Efar v δ') := by
  intro y hy z hz
  have hr : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  obtain ⟨⟨hz1, hz2⟩, hzt⟩ := C.planar_of_mem_sBox (Finset.mem_coe.1 hz)
  by_cases hut : u (oth δ'.1) = v (oth δ'.1)
  · -- same transverse line: compare along `δ'.1`
    have hya := C.planar_of_mem_Cell (Finset.mem_coe.1 hy) δ'.1
    have hua : u δ'.1 ≠ v δ'.1 := fun h => huv (eq_of_coords δ'.1 h hut)
    have hua' : u δ'.1 ≠ v δ'.1 + sgOf δ' := by
      intro h
      apply hux
      refine eq_of_coords δ'.1 ?_ ?_
      · rw [Pi.add_apply, stepVec_apply_fst]; exact h
      · rw [Pi.add_apply, stepVec_apply_oth, add_zero]; exact hut
    refine sep_of_gap (C.pax δ'.1) ?_
    rcases sgOf_sign δ' with hs | hs <;> rw [hs] at hz1 hz2 hua' <;> rcases C.cen_gap hua with h | h
    · left; linarith
    · right
      have h2 : v δ'.1 + 2 ≤ u δ'.1 := by
        rcases lt_or_gt_of_ne hua with h3 | h3
        · exfalso; have : u δ'.1 + 1 ≤ v δ'.1 := h3; nlinarith
        · have h4 : v δ'.1 + 1 ≤ u δ'.1 := h3
          rcases eq_or_lt_of_le h4 with h5 | h5
          · exact absurd h5.symm hua'
          · omega
      have := C.cen_gap_two h2
      linarith
    · left
      have h2 : u δ'.1 + 2 ≤ v δ'.1 := by
        rcases lt_or_gt_of_ne hua with h3 | h3
        · have h4 : u δ'.1 + 1 ≤ v δ'.1 := h3
          rcases eq_or_lt_of_le h4 with h5 | h5
          · exfalso; apply hua'; linarith
          · omega
        · exfalso; have : v δ'.1 + 1 ≤ u δ'.1 := h3; nlinarith
      have := C.cen_gap_two h2
      linarith
    · right; linarith
  · -- different transverse coordinate: compare along `oth δ'.1`
    have hyt := C.planar_of_mem_Cell (Finset.mem_coe.1 hy) (oth δ'.1)
    refine sep_of_gap (C.pax (oth δ'.1)) ?_
    rcases C.cen_gap hut with h | h
    · left; linarith
    · right; linarith

/-- **A stub zone is separated from the cube of another macro-vertex** (if `u + δ = x` the zone
stops `10s ≥ 10` short of `Q_x`). [folklore] -/
theorem zone_sep_Q {u x : Site 2} {δ : MDir} (hux : u ≠ x) : Sep (↑(C.Zone u δ) : Set (Site d)) ↑(C.Q x) := by
  intro y hy z hz
  have hr : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  have hs : (1 : ℤ) ≤ C.s := by exact_mod_cast C.hs
  have h20 : 20 * (C.s : ℤ) ≤ C.r := by exact_mod_cast C.twenty_s_le_r
  obtain ⟨⟨hy1, hy2⟩, hyt⟩ := C.planar_of_mem_sBox (Finset.mem_coe.1 hy)
  by_cases hut : u (oth δ.1) = x (oth δ.1)
  · have hua : u δ.1 ≠ x δ.1 := fun h => hux (eq_of_coords δ.1 h hut)
    have hza := C.planar_of_mem_cIcc (Finset.mem_coe.1 hz) δ.1
    push_cast at hza
    refine sep_of_gap (C.pax δ.1) ?_
    rcases sgOf_sign δ with hsg | hsg <;> rw [hsg] at hy1 hy2 <;> rcases C.cen_gap hua with h | h
    · left; linarith
    · right; linarith
    · left; linarith
    · right; linarith
  · have hzt := C.planar_of_mem_cIcc (Finset.mem_coe.1 hz) (oth δ.1)
    push_cast at hzt
    refine sep_of_gap (C.pax (oth δ.1)) ?_
    rcases C.cen_gap hut with h | h
    · left; linarith
    · right; linarith

/-- **A stub zone is separated from `Efar v δ'`** when `u ∉ {v, v + δ'}`. [folklore] -/
theorem zone_sep_Efar {u v : Site 2} {δ δ' : MDir} (huv : u ≠ v) (hux : u ≠ v + stepVec δ') :
    Sep (↑(C.Zone u δ) : Set (Site d)) ↑(C.Efar v δ') := by
  intro y hy z hz
  have hr : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  have hs : (1 : ℤ) ≤ C.s := by exact_mod_cast C.hs
  have h20 : 20 * (C.s : ℤ) ≤ C.r := by exact_mod_cast C.twenty_s_le_r
  obtain ⟨⟨hy1, hy2⟩, hyt⟩ := C.planar_of_mem_sBox (Finset.mem_coe.1 hy)
  obtain ⟨⟨hz1, hz2⟩, hzt⟩ := C.planar_of_mem_sBox (Finset.mem_coe.1 hz)
  -- the coordinates of `v + δ'`
  have hxa : (v + stepVec δ') δ'.1 = v δ'.1 + sgOf δ' := by rw [Pi.add_apply, stepVec_apply_fst]
  have hxt : (v + stepVec δ') (oth δ'.1) = v (oth δ'.1) := by rw [Pi.add_apply, stepVec_apply_oth, add_zero]
  by_cases hax : δ.1 = δ'.1
  · -- the zone is parallel to the corridor
    have hδ1 : δ.1 = δ'.1 := hax
    rw [hδ1] at hy1 hy2 hyt
    by_cases hut : u (oth δ'.1) = v (oth δ'.1)
    · have hua : u δ'.1 ≠ v δ'.1 := fun h => huv (eq_of_coords δ'.1 h hut)
      have hua' : u δ'.1 ≠ v δ'.1 + sgOf δ' := by
        intro h; apply hux; exact eq_of_coords δ'.1 (by rw [hxa]; exact h) (by rw [hxt]; exact hut)
      refine sep_of_gap (C.pax δ'.1) ?_
      rcases sgOf_sign δ' with hs' | hs' <;> rw [hs'] at hz1 hz2 hua' <;> rcases C.cen_gap hua with h | h
      · -- `σ' = 1`, `u` below `v`
        left; rcases sgOf_sign δ with hsg | hsg <;> rw [hsg] at hy1 hy2 <;> linarith
      · -- `σ' = 1`, `u` above `v`, hence `u a ≥ v a + 2`
        right
        have h2 : v δ'.1 + 2 ≤ u δ'.1 := by
          rcases lt_or_gt_of_ne hua with h3 | h3
          · exfalso; have : u δ'.1 + 1 ≤ v δ'.1 := h3; nlinarith
          · have h4 : v δ'.1 + 1 ≤ u δ'.1 := h3
            rcases eq_or_lt_of_le h4 with h5 | h5
            · exact absurd h5.symm hua'
            · omega
        have := C.cen_gap_two h2
        rcases sgOf_sign δ with hsg | hsg <;> rw [hsg] at hy1 hy2 <;> linarith
      · -- `σ' = -1`, `u` below `v`, hence `u a ≤ v a - 2`
        left
        have h2 : u δ'.1 + 2 ≤ v δ'.1 := by
          rcases lt_or_gt_of_ne hua with h3 | h3
          · have h4 : u δ'.1 + 1 ≤ v δ'.1 := h3
            rcases eq_or_lt_of_le h4 with h5 | h5
            · exfalso; apply hua'; linarith
            · omega
          · exfalso; have : v δ'.1 + 1 ≤ u δ'.1 := h3; nlinarith
        have := C.cen_gap_two h2
        rcases sgOf_sign δ with hsg | hsg <;> rw [hsg] at hy1 hy2 <;> linarith
      · -- `σ' = -1`, `u` above `v`
        right; rcases sgOf_sign δ with hsg | hsg <;> rw [hsg] at hy1 hy2 <;> linarith
    · refine sep_of_gap (C.pax (oth δ'.1)) ?_
      rcases C.cen_gap hut with h | h
      · left; linarith
      · right; linarith
  · -- the zone is perpendicular to the corridor: `δ.1 = oth δ'.1`
    have hδ1 : δ.1 = oth δ'.1 := eq_oth_of_ne hax
    have hoδ : oth δ.1 = δ'.1 := by rw [hδ1, oth_oth]
    rw [hδ1] at hy1 hy2
    rw [hoδ] at hyt
    by_cases hut : u (oth δ'.1) = v (oth δ'.1)
    · -- compare along `δ'.1`, where the zone is `±2r` around `cen u`
      have hua : u δ'.1 ≠ v δ'.1 := fun h => huv (eq_of_coords δ'.1 h hut)
      have hua' : u δ'.1 ≠ v δ'.1 + sgOf δ' := by
        intro h; apply hux; exact eq_of_coords δ'.1 (by rw [hxa]; exact h) (by rw [hxt]; exact hut)
      refine sep_of_gap (C.pax δ'.1) ?_
      rcases sgOf_sign δ' with hs' | hs' <;> rw [hs'] at hz1 hz2 hua' <;> rcases C.cen_gap hua with h | h
      · left; linarith
      · right
        have h2 : v δ'.1 + 2 ≤ u δ'.1 := by
          rcases lt_or_gt_of_ne hua with h3 | h3
          · exfalso; have : u δ'.1 + 1 ≤ v δ'.1 := h3; nlinarith
          · have h4 : v δ'.1 + 1 ≤ u δ'.1 := h3
            rcases eq_or_lt_of_le h4 with h5 | h5
            · exact absurd h5.symm hua'
            · omega
        have := C.cen_gap_two h2
        linarith
      · left
        have h2 : u δ'.1 + 2 ≤ v δ'.1 := by
          rcases lt_or_gt_of_ne hua with h3 | h3
          · have h4 : u δ'.1 + 1 ≤ v δ'.1 := h3
            rcases eq_or_lt_of_le h4 with h5 | h5
            · exfalso; apply hua'; linarith
            · omega
          · exfalso; have : v δ'.1 + 1 ≤ u δ'.1 := h3; nlinarith
        have := C.cen_gap_two h2
        linarith
      · right; linarith
    · -- compare along `oth δ'.1`, the axis of the zone
      refine sep_of_gap (C.pax (oth δ'.1)) ?_
      rcases sgOf_sign δ with hsg | hsg <;> rw [hsg] at hy1 hy2 <;> rcases C.cen_gap hut with h | h
      · left; linarith
      · right; linarith
      · left; linarith
      · right; linarith

/-- **The cover of the determined vertices is separated from the cube of an undetermined one.**
[cite: KozmaNitzan2024, §4 p. 26 ((29): v ∈ X_i ⟺ Q_v ∩ E_i ≠ ∅)] -/
theorem cover_sep_Q {det : Set (Site 2)} {x : Site 2} (hx : x ∉ det) : Sep (C.Cover det) ↑(C.Q x) := by
  intro y hy z hz
  simp only [Cover, Set.mem_iUnion, Set.mem_union, exists_prop] at hy
  obtain ⟨u, hu, hy⟩ := hy
  have hux : u ≠ x := fun h => hx (h ▸ hu)
  rcases hy with hy | ⟨δ, hy⟩
  · exact C.cell_sep_Q hux y hy z hz
  · exact C.zone_sep_Q hux y hy z hz

/-- **The cover of the determined vertices is separated from `E_{v,x}`** for undetermined `v` and
`x = v + δ'`. [cite: KozmaNitzan2024, §4 pp. 27–29 ((31) and Step II)] -/
theorem cover_sep_Efar {det : Set (Site 2)} {v : Site 2} {δ' : MDir} (hv : v ∉ det)
    (hx : v + stepVec δ' ∉ det) : Sep (C.Cover det) ↑(C.Efar v δ') := by
  intro y hy z hz
  simp only [Cover, Set.mem_iUnion, Set.mem_union, exists_prop] at hy
  obtain ⟨u, hu, hy⟩ := hy
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  have hux : u ≠ v + stepVec δ' := fun h => hx (h ▸ hu)
  rcases hy with hy | ⟨δ, hy⟩
  · exact C.cell_sep_Efar huv hux y hy z hz
  · exact C.zone_sep_Efar huv hux y hy z hz

end Cells

end KozmaNitzan

end Percolation.Literature

end

/-!
# Kozma–Nitzan, Theorem 6 — the exploration process as a history-driven site scheme

Eighth proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4), the DEFINITION of the
process `(E_i, G_i, X_i)` of the proof of Theorem 6 (pp. 26–27, Figure 3) as an `HSiteScheme`
(`HistorySiteRenormalization.lean`) on bond configurations of `ℤ^d`:

* the explored EDGE set after a history `h` is `F h = U₀ ∪ supp h` (`U₀` = the lattice edges inside
  `Q_0`), its pattern `ξ h = U₀ ∪ opens h`, and KN's explored region `E_i` is the vertex span
  `V h` of `F h`; a neighbour `x = v + du` of the examined `v` is "onward" (`x ∉ X_i`) iff its
  centre is unexplored (`onward`), which along the run is KN's (29);
* the success criterion (30): the connection `v–x` is good at stub level `j` iff
  `P(0 ↔ M_x in D ∪ E_{v,x} | ω|_D) > 1 - δ`, `D = E_i ∪ E_{w,v} ∪ H^j_{v,x}` — here the
  probability under the weighting pinned on the lattice edges inside `D` (pattern: the recorded
  one on `F h`, the observed one on the new edges) and restricted to `D ∪ E_{v,x}` (`Wt`, `cond`);
  `jOf` is "the first `j` … if such a `j` may be found … and if not let `j_x = K - 1`" (p. 27), and
  `succ` = "all connections to all `x ∈ X` are good";
* the adaptive probe of the examination of `v` from `w` (`probe`): envelope = the fresh lattice
  edges inside `E_i ∪ E_{w,v} ∪ ⋃_x H^{K-1}_{v,x}`, revealed = those inside
  `E_i ∪ E_{w,v} ∪ ⋃_x H^{j_x}_{v,x}` ("declare `E_{i+1} = E_i ∪ E_{w,v} ∪ ⋃ H^{j_x}_x`", p. 27),
  with locality from the least-witness structure of `j_x` (`jIdx_congr`, `revealOf_congr`);
* the scheme (`scheme`) probes only VALID histories (`Valid`: the structural facts of §4 Step I
  and the estimate (32), `P(0 ↔ M_v in E_i ∪ E_{w,v} | ω|_{E_i}) > 1 - δ`), so that the failure
  bound ((33), `KozmaNitzanSteps.lean`) can be proved for every probed history, and the run lemmas
  (`KozmaNitzanTheorem6.lean`) show that actual histories are valid.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 pp. 26–29 ((29)–(32)), Figure 3.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Percolation.Literature

open LatticeModels SimpleGraph GadgetSystem ProbeHistory

namespace KozmaNitzan

variable {d : ℕ}

/-! ## More static geometry of the cells -/

namespace Cells

variable (C : Cells d)

/-- Stubs grow with the level. [folklore] -/
theorem stub_mono (v : Site 2) (δ : MDir) {j j' : ℕ} (h : j ≤ j') : C.Stub v δ j ⊆ C.Stub v δ j' := by
  refine sBox_mono (sgOf_sign δ) _ le_rfl ?_ le_rfl
  have : (j : ℤ) ≤ j' := by exact_mod_cast h
  nlinarith

end Cells

/-! ## Spans, observed open edges -/

/-- The vertices spanned by a finite set of pairs. [folklore] -/
def span (F : Finset (Sym2 (Site d))) : Finset (Site d) := F.biUnion Sym2.toFinset

/-- Membership in the span. [folklore] -/
theorem mem_span_iff {F : Finset (Sym2 (Site d))} {y : Site d} : y ∈ span F ↔ ∃ e ∈ F, y ∈ e := by
  simp [span, Sym2.mem_toFinset]

/-- The span is monotone. [folklore] -/
theorem span_mono {F F' : Finset (Sym2 (Site d))} (h : F ⊆ F') : span F ⊆ span F' := by
  intro y hy
  rw [mem_span_iff] at hy ⊢
  obtain ⟨e, he, hye⟩ := hy
  exact ⟨e, h he, hye⟩

/-- The union of the observations recorded in a history. [folklore] -/
def opens {V : Type*} (h : ProbeHistory V) : Finset (Sym2 V) := (h.filterMap id).toFinset.biUnion Prod.snd

/-- Membership in `opens`. [folklore] -/
theorem mem_opens_iff {V : Type*} {h : ProbeHistory V} {e : Sym2 V} :
    e ∈ opens h ↔ ∃ r : ProbeRecord V, some r ∈ h ∧ e ∈ r.2 := by
  simp only [opens, Finset.mem_biUnion, List.mem_toFinset, List.mem_filterMap, id]
  constructor
  · rintro ⟨r, ⟨a, ha, rfl⟩, he⟩; exact ⟨r, ha, he⟩
  · rintro ⟨r, hr, he⟩; exact ⟨r, ⟨some r, hr, rfl⟩, he⟩

/-- The empty history has no observations. [folklore] -/
@[simp] theorem opens_nil {V : Type*} : opens ([] : ProbeHistory V) = ∅ := by
  ext e; simp [mem_opens_iff]

/-- A `none` step adds no observation. [folklore] -/
@[simp] theorem opens_cons_none {V : Type*} (h : ProbeHistory V) : opens (none :: h) = opens h := by
  ext e; simp [mem_opens_iff]

/-- A probe adds its observation. [folklore] -/
@[simp] theorem opens_cons_some {V : Type*} (r : ProbeRecord V) (h : ProbeHistory V) :
    opens (some r :: h) = r.2 ∪ opens h := by
  ext e
  simp only [mem_opens_iff, List.mem_cons, Option.some.injEq, Finset.mem_union]
  constructor
  · rintro ⟨r', hr' | hr', he⟩
    · subst hr'; exact Or.inl he
    · exact Or.inr ⟨r', hr', he⟩
  · rintro (he | ⟨r', hr', he⟩)
    · exact ⟨r, Or.inl rfl, he⟩
    · exact ⟨r', Or.inr hr', he⟩

/-! ## The least witness below `K` -/

/-- **The first good level**: the least `j < K` with `P j`, and `K - 1` if there is none (KN p. 27:
"If such a `j` may be found let `j_x` be the first one, and if not let `j_x = K - 1`").
[cite: KozmaNitzan2024, §4 p. 27 (j_x)] -/
def jIdx (K : ℕ) (P : ℕ → Prop) : ℕ := if h : ∃ j, j < K ∧ P j then Nat.find h else K - 1

/-- `jIdx < K` (for `K ≥ 1`). [folklore] -/
theorem jIdx_lt {K : ℕ} (hK : 1 ≤ K) (P : ℕ → Prop) : jIdx K P < K := by
  unfold jIdx
  split_ifs with h
  · exact (Nat.find_spec h).1
  · omega

/-- If the first good level is good then it is at most every good level below `K`; if it is not
good then no level below `K` is. [folklore] -/
theorem jIdx_spec {K : ℕ} (hK : 1 ≤ K) (P : ℕ → Prop) :
    (P (jIdx K P) ∧ ∀ j < jIdx K P, ¬P j) ∨ (¬P (jIdx K P) ∧ ∀ j < K, ¬P j) := by
  unfold jIdx
  split_ifs with h
  · left
    refine ⟨(Nat.find_spec h).2, fun j hj hPj => ?_⟩
    exact Nat.find_min h hj ⟨hj.trans (Nat.find_spec h).1, hPj⟩
  · right
    push Not at h
    exact ⟨fun hP => h (K - 1) (by omega) hP, fun j hj hPj => h j hj hPj⟩

/-- If the first good level is not good, no level below `K` is good. [folklore] -/
theorem forall_not_of_not_jIdx {K : ℕ} (hK : 1 ≤ K) {P : ℕ → Prop} (h : ¬P (jIdx K P)) : ∀ j < K, ¬P j := by
  rcases jIdx_spec hK P with h' | h'
  · exact absurd h'.1 h
  · exact h'.2

/-- **Locality of the first good level**: two predicates agreeing up to the first good level of one
of them have the same first good level. [folklore] -/
theorem jIdx_congr {K : ℕ} {P P' : ℕ → Prop} (h : ∀ j ≤ jIdx K P, (P j ↔ P' j)) : jIdx K P' = jIdx K P := by
  unfold jIdx at h ⊢
  by_cases hex : ∃ j, j < K ∧ P j
  · rw [dif_pos hex] at h ⊢
    have hm := Nat.find_spec hex
    have hex' : ∃ j, j < K ∧ P' j := ⟨Nat.find hex, hm.1, (h _ le_rfl).1 hm.2⟩
    rw [dif_pos hex']
    apply le_antisymm
    · exact Nat.find_min' hex' ⟨hm.1, (h _ le_rfl).1 hm.2⟩
    · by_contra hlt
      push Not at hlt
      have hm' := Nat.find_spec hex'
      have := Nat.find_min hex hlt
      exact this ⟨hm'.1, (h _ hlt.le).2 hm'.2⟩
  · rw [dif_neg hex] at h ⊢
    have hex' : ¬∃ j, j < K ∧ P' j := by
      rintro ⟨j, hj, hPj⟩
      exact hex ⟨j, hj, (h j (by omega)).2 hPj⟩
    rw [dif_neg hex']

/-! ## The scheme -/

/-- **The parameters of the exploration process**: the cells, the percolation parameter `p`, and the
threshold `δ` of (30) and (32). [cite: KozmaNitzan2024, §4 pp. 25–27] -/
structure KSch (d : ℕ) where
  /-- the cells -/
  C : Cells d
  /-- the percolation parameter -/
  p : unitInterval
  /-- the threshold `δ` of (30), (32) -/
  δc : ℝ

namespace KSch

variable (S : KSch d)

/-- The initial edges: the lattice edges inside `Q_0` (KN p. 27: "`G₀ = {(0,0)}` if all edges of
`Q_{(0,0)}` are open (and declare `E₁ = Q_{(0,0)}`)"). [cite: KozmaNitzan2024, §4 p. 27] -/
def U₀ : Finset (Sym2 (Site d)) := edgesIn (zdGraph d) (S.C.Q 0)

/-- The explored edges after a history: `U₀` and everything revealed. [cite: KozmaNitzan2024, §4 p. 26 (ω|_{E_i})] -/
def F (h : ProbeHistory (Site d)) : Finset (Sym2 (Site d)) := S.U₀ ∪ supp h

/-- **The explored region `E_i`**: the vertex span of the explored edges. [cite: KozmaNitzan2024, §4 p. 26 (E_i)] -/
def V (h : ProbeHistory (Site d)) : Finset (Site d) := span (S.F h)

/-- The recorded pattern on the explored edges (`U₀` all open). [cite: KozmaNitzan2024, §4 p. 26 (ω|_{E_i})] -/
def ξ (h : ProbeHistory (Site d)) : Finset (Sym2 (Site d)) := S.U₀ ∪ opens h

/-- **The onward directions** out of `v`: those neighbours `x` whose cell is unexplored (KN's
"`X` = the neighbours of `v` which are not in `X_i`", via (29): `x ∈ X_i ⟺ Q_x ∩ E_i ≠ ∅`).
[cite: KozmaNitzan2024, §4 p. 27 (X = X_v), p. 26 (29)] -/
def onward (h : ProbeHistory (Site d)) (v : Site 2) : Finset MDir :=
  Finset.univ.filter fun du => S.C.cen (v + stepVec du) ∉ S.V h

/-- The support of the examination of the connection `v–x` (`E_i ∪ E_{w,v} ∪ E_{v,x}`).
[cite: KozmaNitzan2024, §4 p. 27 ((30): D ∪ E_{v,x})] -/
def Sx (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) : Finset (Site d) :=
  S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Efar (tgt e) du

/-- The conditioned lattice edges at stub level `j` (`ω|_D`, `D = E_i ∪ E_{w,v} ∪ H^j_{v,x}`).
[cite: KozmaNitzan2024, §4 p. 27 ((30): D)] -/
def Fj (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) : Finset (Sym2 (Site d)) :=
  edgesIn (zdGraph d) (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j)

/-- The pattern pinned at level `j`: the recorded one on the explored edges, the observed one `o` on
the new edges. [cite: KozmaNitzan2024, §4 p. 27 ((30): ω|_D)] -/
def pat (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) (o : Finset (Sym2 (Site d))) :
    Finset (Sym2 (Site d)) :=
  S.ξ h ∪ (o ∩ (S.Fj h e du j \ S.F h))

/-- **The weighting of (30)**: the lattice weighting pinned on `ω|_D` and restricted to
`D ∪ E_{v,x}`. [cite: KozmaNitzan2024, §4 p. 27 ((30))] -/
def Wt (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) (o : Finset (Sym2 (Site d))) :
    Sym2 (Site d) → unitInterval :=
  restrW (↑(S.Sx h e du) : Set (Site d)) (pinW (lattW d S.p) ↑(S.Fj h e du j) ↑(S.pat h e du j o))

/-- The target event `{0 ↔ M_x}`. [cite: KozmaNitzan2024, §4 p. 27 ((30): 0 ↔ M_x)] -/
def Conn (e : Site 2 × MDir) (du : MDir) : Set (BondConfig (Site d)) :=
  ⋃ t ∈ S.C.M (tgt e + stepVec du), openConn (0 : Site d) t

/-- **(30)**: the connection `v–x` is good at level `j` given the observation `o`.
[cite: KozmaNitzan2024, §4 p. 27 ((30))] -/
def cond (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) (o : Finset (Sym2 (Site d))) : Prop :=
  1 - S.δc < (prodBernoulli (S.Wt h e du j o)).real (S.Conn e du)

/-- `j_x`: the first good level, or `K - 1`. [cite: KozmaNitzan2024, §4 p. 27 (j_x)] -/
def jOf (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (o : Finset (Sym2 (Site d))) : ℕ :=
  jIdx S.C.K fun j => S.cond h e du j o

/-- The region revealed by the examination, given the observation (`E_{w,v} ∪ ⋃_x H^{j_x}_{v,x}`).
[cite: KozmaNitzan2024, §4 p. 27 (E_{i+1})] -/
def newRegion (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (o : Finset (Sym2 (Site d))) : Finset (Site d) :=
  S.C.Ewv e.1 e.2 ∪ (S.onward h (tgt e)).biUnion fun du => S.C.Stub (tgt e) du (S.jOf h e du o)

/-- The envelope region (`E_{w,v} ∪ ⋃_x H^{K-1}_{v,x}`). [cite: KozmaNitzan2024, §4 p. 27] -/
def envRegion (h : ProbeHistory (Site d)) (e : Site 2 × MDir) : Finset (Site d) :=
  S.C.Ewv e.1 e.2 ∪ (S.onward h (tgt e)).biUnion fun du => S.C.Stub (tgt e) du (S.C.K - 1)

/-- The envelope of the examination: the fresh lattice edges inside `E_i ∪` envelope region.
[cite: KozmaNitzan2024, §4 p. 27] -/
def env (h : ProbeHistory (Site d)) (e : Site 2 × MDir) : Finset (Sym2 (Site d)) :=
  edgesIn (zdGraph d) (S.V h ∪ S.envRegion h e) \ S.F h

/-- The revealed edges given the observation: the fresh lattice edges inside `E_i ∪` new region.
[cite: KozmaNitzan2024, §4 p. 27 (E_{i+1})] -/
def revealOf (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (o : Finset (Sym2 (Site d))) :
    Finset (Sym2 (Site d)) :=
  edgesIn (zdGraph d) (S.V h ∪ S.newRegion h e o) \ S.F h

/-- **Success** ("declare `v` good … if all connections to all `x ∈ X` are good", p. 27).
[cite: KozmaNitzan2024, §4 p. 27] -/
def succ (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (o : Finset (Sym2 (Site d))) : Prop :=
  ∀ du ∈ S.onward h (tgt e), S.cond h e du (S.jOf h e du o) o

/-! ### Locality -/

/-- `j_x < K`. [folklore] -/
theorem jOf_lt (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (o : Finset (Sym2 (Site d))) :
    S.jOf h e du o < S.C.K :=
  jIdx_lt (by have := S.C.hK; omega) _

/-- The new region lies in the envelope region. [folklore] -/
theorem newRegion_subset_envRegion (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (o : Finset (Sym2 (Site d))) :
    S.newRegion h e o ⊆ S.envRegion h e := by
  intro y hy
  rcases Finset.mem_union.1 hy with hy | hy
  · exact Finset.mem_union_left _ hy
  · refine Finset.mem_union_right _ ?_
    rw [Finset.mem_biUnion] at hy ⊢
    obtain ⟨du, hdu, hy⟩ := hy
    exact ⟨du, hdu, S.C.stub_mono _ _ (by have := S.jOf_lt h e du o; omega) hy⟩

/-- The revealed edges lie in the envelope. [folklore] -/
theorem revealOf_subset_env (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (o : Finset (Sym2 (Site d))) :
    S.revealOf h e o ⊆ S.env h e := by
  refine Finset.sdiff_subset_sdiff ?_ le_rfl
  intro x hx
  rw [mem_edgesIn_iff] at hx ⊢
  refine ⟨hx.1, fun y hy => ?_⟩
  rcases Finset.mem_union.1 (hx.2 y hy) with h' | h'
  · exact Finset.mem_union_left _ h'
  · exact Finset.mem_union_right _ (S.newRegion_subset_envRegion h e o h')

/-- The conditioned edges at level `j ≤ j'` lie among those at level `j'`. [folklore] -/
theorem Fj_mono (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) {j j' : ℕ} (hjj' : j ≤ j') :
    S.Fj h e du j ⊆ S.Fj h e du j' := by
  intro x hx
  rw [Fj, mem_edgesIn_iff] at hx ⊢
  refine ⟨hx.1, fun y hy => ?_⟩
  rcases Finset.mem_union.1 (hx.2 y hy) with h' | h'
  · exact Finset.mem_union_left _ h'
  · exact Finset.mem_union_right _ (S.C.stub_mono _ _ hjj' h')

/-- The explored edges lie among the conditioned edges. [folklore] -/
theorem F_subset_Fj {h : ProbeHistory (Site d)} (hF : S.F h = edgesIn (zdGraph d) (S.V h))
    (e : Site 2 × MDir) (du : MDir) (j : ℕ) : S.F h ⊆ S.Fj h e du j := by
  rw [hF]
  intro x hx
  rw [mem_edgesIn_iff] at hx
  rw [Fj, mem_edgesIn_iff]
  exact ⟨hx.1, fun y hy => Finset.mem_union_left _ (Finset.mem_union_left _ (hx.2 y hy))⟩

/-- The new conditioned edges at level `j ≤ j_x` of an onward direction are revealed. [folklore] -/
theorem Fj_sdiff_subset_revealOf {h : ProbeHistory (Site d)} {e : Site 2 × MDir} {du : MDir}
    (hdu : du ∈ S.onward h (tgt e)) {o : Finset (Sym2 (Site d))} {j : ℕ} (hj : j ≤ S.jOf h e du o) :
    S.Fj h e du j \ S.F h ⊆ S.revealOf h e o := by
  refine Finset.sdiff_subset_sdiff ?_ le_rfl
  intro x hx
  rw [Fj, mem_edgesIn_iff] at hx
  rw [mem_edgesIn_iff]
  refine ⟨hx.1, fun y hy => ?_⟩
  rcases Finset.mem_union.1 (hx.2 y hy) with h' | h'
  · rcases Finset.mem_union.1 h' with h'' | h''
    · exact Finset.mem_union_left _ h''
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h'')
  · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
    exact Finset.mem_biUnion.2 ⟨du, hdu, S.C.stub_mono _ _ hj h'⟩

/-- The new conditioned edges of an onward direction lie in the envelope. [folklore] -/
theorem Fj_sdiff_subset_env (h : ProbeHistory (Site d)) (e : Site 2 × MDir) {du : MDir}
    (hdu : du ∈ S.onward h (tgt e)) {j : ℕ} (hj : j < S.C.K) : S.Fj h e du j \ S.F h ⊆ S.env h e := by
  refine Finset.sdiff_subset_sdiff ?_ le_rfl
  intro x hx
  rw [Fj, mem_edgesIn_iff] at hx
  rw [mem_edgesIn_iff]
  refine ⟨hx.1, fun y hy => ?_⟩
  rcases Finset.mem_union.1 (hx.2 y hy) with h' | h'
  · rcases Finset.mem_union.1 h' with h'' | h''
    · exact Finset.mem_union_left _ h''
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h'')
  · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
    exact Finset.mem_biUnion.2 ⟨du, hdu, S.C.stub_mono _ _ (by omega) h'⟩

/-- The pattern only depends on the observation on the new conditioned edges. [folklore] -/
theorem pat_congr (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) {o o' : Finset (Sym2 (Site d))}
    (hoo' : ∀ x ∈ S.Fj h e du j \ S.F h, x ∈ o ↔ x ∈ o') : S.pat h e du j o = S.pat h e du j o' := by
  unfold pat
  congr 1
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hx, hx'⟩; exact ⟨(hoo' x hx').1 hx, hx'⟩
  · rintro ⟨hx, hx'⟩; exact ⟨(hoo' x hx').2 hx, hx'⟩

/-- Hence so does the good-connection predicate. [folklore] -/
theorem cond_congr (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) {o o' : Finset (Sym2 (Site d))}
    (hoo' : ∀ x ∈ S.Fj h e du j \ S.F h, x ∈ o ↔ x ∈ o') : S.cond h e du j o ↔ S.cond h e du j o' := by
  unfold cond Wt
  rw [S.pat_congr h e du j hoo']

/-- **Locality of `j_x`**: observations agreeing on the revealed edges give the same `j_x` and the
same goodness at `j_x`, for every onward direction. [folklore] -/
theorem jOf_congr {h : ProbeHistory (Site d)} {e : Site 2 × MDir} {du : MDir} (hdu : du ∈ S.onward h (tgt e))
    {o o' : Finset (Sym2 (Site d))} (hoo' : ∀ x ∈ S.revealOf h e o, x ∈ o ↔ x ∈ o') :
    S.jOf h e du o' = S.jOf h e du o ∧
      (S.cond h e du (S.jOf h e du o) o' ↔ S.cond h e du (S.jOf h e du o) o) := by
  have key : ∀ j ≤ S.jOf h e du o, (S.cond h e du j o ↔ S.cond h e du j o') := fun j hj =>
    S.cond_congr h e du j fun x hx => hoo' x (S.Fj_sdiff_subset_revealOf hdu hj hx)
  exact ⟨jIdx_congr key, (key _ le_rfl).symm⟩

/-- **Locality of the revealed set.** [folklore] -/
theorem revealOf_congr {h : ProbeHistory (Site d)} {e : Site 2 × MDir} {o o' : Finset (Sym2 (Site d))}
    (hoo' : ∀ x ∈ S.revealOf h e o, x ∈ o ↔ x ∈ o') : S.revealOf h e o' = S.revealOf h e o := by
  unfold revealOf newRegion
  have : ∀ du ∈ S.onward h (tgt e), S.jOf h e du o' = S.jOf h e du o := fun du hdu => (S.jOf_congr hdu hoo').1
  rw [Finset.biUnion_congr rfl fun du hdu => by rw [this du hdu]]

/-- **Locality of success.** [folklore] -/
theorem succ_congr {h : ProbeHistory (Site d)} {e : Site 2 × MDir} {o o' : Finset (Sym2 (Site d))}
    (hoo' : ∀ x ∈ S.revealOf h e o, x ∈ o ↔ x ∈ o') : S.succ h e o' ↔ S.succ h e o := by
  unfold succ
  refine forall₂_congr fun du hdu => ?_
  obtain ⟨h1, h2⟩ := S.jOf_congr hdu hoo'
  rw [h1, h2]

/-! ### The probe -/

/-- **The adaptive probe of the examination of `v = tgt e` from `e.1`** (reveals `E_{w,v}` and the
stubs `H^{j_x}_{v,x}`, computing the `j_x` from what it sees). [cite: KozmaNitzan2024, §4 p. 27] -/
def probe (h : ProbeHistory (Site d)) (e : Site 2 × MDir) : AProbe (Site d) where
  env := S.env h e
  reveal := fun ω => S.revealOf h e (obs ω (S.env h e))
  reveal_subset := fun ω => S.revealOf_subset_env h e _
  reveal_local := by
    intro ω ω' hag
    refine S.revealOf_congr fun x hx => ?_
    have hxe : x ∈ S.env h e := S.revealOf_subset_env h e _ hx
    simp only [mem_obs_iff, hxe, true_and]
    exact hag x hx

/-- The observation of the probe agrees with the observation of the envelope on the revealed edges,
so success read off either is the same. [folklore] -/
theorem succ_read_iff (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (ω : BondConfig (Site d)) :
    S.succ h e ((S.probe h e).read ω) ↔ S.succ h e (obs ω (S.env h e)) := by
  refine S.succ_congr fun x hx => ?_
  have hxe : x ∈ S.env h e := S.revealOf_subset_env h e _ hx
  simp only [AProbe.read, probe, mem_obs_iff, hxe, hx, true_and]

/-! ### Validity and the scheme -/

/-- The weighting of (32): pinned on `ω|_{E_i}`, restricted to `E_i ∪ E_{w,v}`.
[cite: KozmaNitzan2024, §4 p. 28 ((32))] -/
def W₀ (h : ProbeHistory (Site d)) (e : Site 2 × MDir) : Sym2 (Site d) → unitInterval :=
  restrW (↑(S.V h ∪ S.C.Ewv e.1 e.2) : Set (Site d)) (pinW (lattW d S.p) ↑(S.F h) ↑(S.ξ h))

/-- **Valid histories** for the examination along `e`: the explored edges are the lattice edges
inside the explored region and carry the pattern, the origin and the source's centre are explored,
the explored region is separated from `Q_v` and from the `E_{v,x}` of the onward directions
((29), (31)), and the estimate (32) holds: `P(0 ↔ M_v in E_i ∪ E_{w,v} | ω|_{E_i}) > 1 - δ`.
[cite: KozmaNitzan2024, §4 pp. 26–28 ((29), (31), (32))] -/
structure Valid (h : ProbeHistory (Site d)) (e : Site 2 × MDir) : Prop where
  F_eq : S.F h = edgesIn (zdGraph d) (S.V h)
  ξ_sub : S.ξ h ⊆ S.F h
  zero_mem : (0 : Site d) ∈ S.V h
  src_mem : S.C.cen e.1 ∈ S.V h
  cover : ∃ det : Set (Site 2), tgt e ∉ det ∧ (∀ du ∈ S.onward h (tgt e), tgt e + stepVec du ∉ det) ∧
    (↑(S.V h) : Set (Site d)) ⊆ S.C.Cover det
  reach : 1 - S.δc < (prodBernoulli (S.W₀ h e)).real (⋃ t ∈ S.C.M (tgt e), openConn (0 : Site d) t)

/-- The next probe: examine the chosen candidate, but only after a valid history.
[cite: KozmaNitzan2024, §4 p. 27] -/
def nextProbe (h : ProbeHistory (Site d)) : Option (AProbe (Site d)) :=
  match (HSiteScheme.mstOf S.succ h).choice with
  | none => none
  | some e => if S.Valid h e then some (S.probe h e) else none

/-- **Kozma–Nitzan's exploration process** as a history-driven site scheme.
[cite: KozmaNitzan2024, §4 pp. 26–27] -/
def scheme : HSiteScheme (Site d) := ⟨⟨S.nextProbe⟩, S.U₀, S.succ⟩

/-- If a probe is made, the history is valid for the chosen edge and the probe is the examination.
[folklore] -/
theorem nextProbe_eq_some {h : ProbeHistory (Site d)} {P : AProbe (Site d)} (hP : S.nextProbe h = some P) :
    ∃ e, (HSiteScheme.mstOf S.succ h).choice = some e ∧ S.Valid h e ∧ P = S.probe h e := by
  unfold nextProbe at hP
  cases hc : (HSiteScheme.mstOf S.succ h).choice with
  | none => rw [hc] at hP; simp at hP
  | some e =>
    rw [hc] at hP
    simp only at hP
    split_ifs at hP with hV
    rw [Option.some.injEq] at hP
    exact ⟨e, rfl, hV, hP.symm⟩

/-- Conversely a valid history with a candidate is probed. [folklore] -/
theorem nextProbe_of_valid {h : ProbeHistory (Site d)} {e : Site 2 × MDir}
    (hc : (HSiteScheme.mstOf S.succ h).choice = some e) (hV : S.Valid h e) : S.nextProbe h = some (S.probe h e) := by
  unfold nextProbe; rw [hc]; simp only; rw [if_pos hV]

end KSch

end KozmaNitzan

end Percolation.Literature

end
