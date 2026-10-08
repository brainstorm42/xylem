import Percolation.Literature.FlatKitDef
import Percolation.Literature.FlatRun5
import Percolation.Util.Linter

/-!
# The flat gait, XXXIII–XXXVI

This module gathers 4 consecutive parts of the flat-gait development, in order:
XXXIII: static disjointness, I — frames, shapes, cells ·
XXXIV: static disjointness, II — same target, target-source, assembly ·
XXXV: static disjointness, III — the regions avoid the initial open set ·
XXXVI: the flat kit is good; percolation in `ℤ^d`, flat regime.
Part 1 follows; the later parts keep their own headers below.

# Part 1 (The flat gait, XXXIII): static disjointness, I — frames, shapes, cells

The first half of Grimmett's (C) for the flat block
construction (*Percolation*, 2nd ed. (1999), §7.3 p. 173, case `H < L`): the reserved region of an
attempt `(a, e)` from an admissible token, read in absolute coordinates. The frame of an admissible
token in signed form (`FTAdm.frameS`: the face between `a` and the target cell `c`, the token's
lateral offset on the `+Λ` side, the trunk lane and the take-off lines); the region as seven pieces
with numeric windows (`fzone_cases`); its classification into a **core** strictly inside the target
cell and an **entry** straddling the face between `a` and `c` near the token (`InCell`, `NearFace`,
`fzone_classify`); and the cell arithmetic showing that cores of different cells, a core and the
entry of an attempt from another cell, and the entries of two different attempts never meet
(`incell_incell`, `incell_nearface`, `nearface_nearface`), together with the separation of the
layers (`layers_apartF`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## Cells and directions -/

section Cells

variable (Y : FlatLayout)

omit [NeZero d] in
/-- The centre of the target cell: `2D` on along `e`, unchanged laterally. [folklore] -/
theorem ctr_ftgt (a : Site 2) (e : MDir) :
    Y.ctr (ftgt a e) e.1 = Y.ctr a e.1 + (sgOf e : ℤ) * (2 * Y.Df) ∧ Y.ctr (ftgt a e) (latDir e true).1 = Y.ctr a (latDir e true).1 := by
  unfold FlatLayout.ctr ftgt
  rw [Pi.add_apply, Pi.add_apply, stepVec_apply, stepVec_apply, if_pos rfl, if_neg (latDir_fst_ne e true)]
  constructor <;> ring

omit [NeZero d] in
/-- The centre of a cell along an axis is its index times `2D`. [folklore] -/
theorem ctr_eq (c : Site 2) (i : Fin 2) : Y.ctr c i = c i * (2 * Y.Df) := rfl

omit [NeZero d] in
/-- **The signed lane of any cell**: `s · lane(c, e) = s · ctr_lat(c) + Λ + s · cpar(c) · Λ_J`, with `cpar ∈ {0, 1}`. [folklore] -/
theorem sLane_cell (c : Site 2) (e : MDir) :
    (sgOf e : ℤ) * Y.lane c e = (sgOf e : ℤ) * Y.ctr c (latDir e true).1 + Y.lam + (sgOf e : ℤ) * (TallLayout.cpar c * Y.lamJ) ∧
      0 ≤ TallLayout.cpar c ∧ TallLayout.cpar c ≤ 1 := by
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  refine ⟨?_, by unfold TallLayout.cpar; omega, by unfold TallLayout.cpar; omega⟩
  unfold FlatLayout.lane FlatLayout.nu
  linear_combination Y.lam * hss

omit [NeZero d] in
/-- Along an axis, two cell indices are equal or twice their centres differ by at least `4D`. [folklore] -/
theorem ctr_eq_or_far (c c' : Site 2) (i : Fin 2) : c i = c' i ∨ 4 * Y.Df ≤ |2 * Y.ctr c i - 2 * Y.ctr c' i| := by
  have hD : 0 ≤ Y.Df := by unfold FlatLayout.Df FlatLayout.U; positivity
  by_cases h : c i = c' i
  · exact Or.inl h
  · right
    have e1 : 2 * Y.ctr c i - 2 * Y.ctr c' i = (c i - c' i) * (4 * Y.Df) := by rw [ctr_eq, ctr_eq]; ring
    rw [e1, abs_mul, abs_of_nonneg (by linarith : (0 : ℤ) ≤ 4 * Y.Df)]
    have : 1 ≤ |c i - c' i| := Int.one_le_abs (sub_ne_zero.2 h)
    nlinarith

omit [NeZero d] in
/-- Twice the centres of different cells differ by at least `4D` along some axis. [folklore] -/
theorem ctr_far_of_ne {c c' : Site 2} (h : c ≠ c') : ∃ i, 4 * Y.Df ≤ |2 * Y.ctr c i - 2 * Y.ctr c' i| := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ c' i := by
    by_contra h'; push Not at h'; exact h (funext h')
  exact ⟨i, (ctr_eq_or_far Y c c' i).resolve_left hi⟩

end Cells

/-! ## The signed frame of an admissible token -/

section Frame

variable (Y : FlatLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d)

omit [NeZero d] in
/-- **The signed frame of an admissible token**: twice the token's forward coordinate is between
`4U` and `2` before the face between `a` and the target cell; its lateral coordinate read along
`e` is on the `+Λ` side of the target centre within `Λ_J + ρ_p`; the trunk lane likewise within
`Λ_J`; the take-off lines at `∓Λ` within `Λ_J` along `e`; the token's height within `ρ_v` of the
layer of its source. [folklore] -/
theorem FTAdm.frameS (hτ : FTAdm hd Y a e τ) :
    2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df - 4 * Y.U ≤ 2 * upar hd (dsg e) τ.pos ∧
      2 * upar hd (dsg e) τ.pos ≤ 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df - 2 ∧
      (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.lam - Y.lamJ - Y.ρp ≤ (sgOf e : ℤ) * Uc hd (latDir e true).1 τ.pos ∧
      (sgOf e : ℤ) * Uc hd (latDir e true).1 τ.pos ≤ (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.lam + Y.lamJ + Y.ρp ∧
      (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.lam - Y.lamJ ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) e ∧
      (sgOf e : ℤ) * Y.lane (ftgt a e) e ≤ (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.lam + Y.lamJ ∧
      |(sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 - Y.lam)| ≤ Y.lamJ ∧
      |(sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 + Y.lam)| ≤ Y.lamJ ∧
      ∃ d', τ.src = some d' ∧ |τ.pos (ax0 hd) - Y.zOf d'| ≤ Y.ρv := by
  obtain ⟨f1, f2, -⟩ := FTAdm.frame Y hd a e τ hτ
  have hlat := abs_le.1 hτ.lateral
  obtain ⟨hla, hca0, hca1⟩ := sLane_cell Y a e
  obtain ⟨hlc, hcc0, hcc1⟩ := sLane_cell Y (ftgt a e) e
  obtain ⟨hL1, hL2, hc0, hc1⟩ := sLane_eB Y a e
  rw [(ctr_ftgt Y a e).2] at hlc ⊢
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ FlatLayout.U; positivity
  have pa : 0 ≤ TallLayout.cpar a * Y.lamJ ∧ TallLayout.cpar a * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hca0 hJ, mul_le_of_le_one_left hJ hca1⟩
  have pc : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
  obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 hτ.src_some
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, d', hd', hτ.height d' hd'⟩
  · rcases hs with h | h <;> rw [h] at hla ⊢ <;> linarith [pa.1, pa.2]
  · rcases hs with h | h <;> rw [h] at hla ⊢ <;> linarith [pa.1, pa.2]
  · rcases hs with h | h <;> rw [h] at hlc ⊢ <;> linarith [pc.1, pc.2]
  · rcases hs with h | h <;> rw [h] at hlc ⊢ <;> linarith [pc.1, pc.2]
  · rw [abs_le]; rcases hs with h | h <;> rw [h] at hL1 ⊢ <;> constructor <;> linarith [pc.1, pc.2]
  · rw [abs_le]; rcases hs with h | h <;> rw [h] at hL2 ⊢ <;> constructor <;> linarith [pc.1, pc.2]

end Frame

/-! ## The pieces of the region with numeric windows -/

section Cases

variable (Y : FlatLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d)

omit [NeZero d] in
/-- **The region in seven pieces**: near the token (the lead-in: within `8U + 8H + 4` in both
diagonal coordinates, height between `2U` below and `2U + 4L'` above the token's along the riser);
the riser column, low and high; the entry side; the trunk tube; the two branch tubes — all with the
constraints of `fzone`. [folklore] -/
theorem fzone_cases (hY : Y.OK) {w : Site d} (hw : w ∈ fzone Y hd a e τ) :
    let s : ℤ := (sgOf e : ℤ)
    let u : ℤ := (friseDir hd Y e τ : ℤ)
    let P := s * Uc hd e.1 w
    let L := Uc hd (latDir e true).1 w
    let S2 := 2 * upar hd (dsg e) τ.pos
    let Lt := 2 * Uc hd (latDir e true).1 τ.pos
    let z0 := 2 * τ.pos (ax0 hd)
    let zN2 := 2 * Y.zOf e
    let C := 2 * (s * Y.ctr (ftgt a e) e.1)
    let Cl := 2 * Y.ctr (ftgt a e) (latDir e true).1
    let ln := 2 * Y.lane (ftgt a e) e
    let t1 := 2 * (s * Y.lane (ftgt a e) (eB1 e) - s * Y.U)
    let t2 := 2 * (s * Y.lane (ftgt a e) (eB2 e) - s * Y.U)
    (|P - S2| ≤ 8 * Y.U + 8 * Y.H + 4 ∧ |L - Lt| ≤ 8 * Y.U + 8 * Y.H + 4 ∧ -(2 * Y.U) ≤ u * (w (ax0 hd) - z0) ∧ u * (w (ax0 hd) - z0) ≤ 2 * Y.U + 4 * Y.Lp) ∨
    (2 * Y.m + 1 ≤ u * (w (ax0 hd) - z0) ∧ u * (w (ax0 hd) - z0) ≤ 14 * Y.U + 10 * Y.H ∧
      S2 - 4 * Y.U ≤ P ∧ P ≤ C - 2 * Y.Df + 8 * Y.U ∧ |L - Lt| ≤ 222 * Y.U) ∨
    (2 * Y.m + 1 ≤ u * (w (ax0 hd) - z0) ∧ u * (w (ax0 hd) - zN2) ≤ 8 * Y.U + 2 * Y.H ∧
      C - 2 * Y.Df + 3 * Y.U ≤ P ∧ P ≤ S2 + 440 * Y.U ∧ |L - Lt| ≤ 222 * Y.U) ∨
    (S2 + 2 * cE Y e τ ≤ P ∧ P ≤ S2 + 950 * Y.U ∧
      2 * min (Uc hd (latDir e true).1 τ.pos - 126 * Y.U) (Y.lane (ftgt a e) e - 22 * Y.U) - 4 * Y.U ≤ L ∧
      L ≤ 2 * max (Uc hd (latDir e true).1 τ.pos + 126 * Y.U) (Y.lane (ftgt a e) e + 22 * Y.U) + 4 * Y.U ∧ |w (ax0 hd) - zN2| ≤ 8 * Y.U + 2 * Y.H) ∨
    (S2 + 188 * Y.U ≤ P ∧ P ≤ C + 2 * Y.Df - 2 * Y.U + 4 * Y.H + 2 ∧ |L - ln| ≤ 1076 * Y.U ∧ |w (ax0 hd) - zN2| ≤ 8 * Y.U + 2 * Y.H) ∨
    (|P - t1| ≤ 790 * Y.U ∧ s * Cl - 2 * Y.Df + 2 ≤ s * L ∧ s * L ≤ s * ln + 1076 * Y.U ∧ |w (ax0 hd) - zN2| ≤ 8 * Y.U + 2 * Y.H) ∨
    (|P - t2| ≤ 474 * Y.U ∧ s * ln - 1076 * Y.U ≤ s * L ∧ s * L ≤ s * Cl + 2 * Y.Df - 2 ∧ |w (ax0 hd) - zN2| ≤ 8 * Y.U + 2 * Y.H) := by
  intro s u P L S2 Lt z0 zN2 C Cl ln t1 t2
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hσ : ∀ i : Fin 2, ((dsg e i : ℤ)) = 1 ∨ ((dsg e i : ℤ)) = -1 := fun i => by rcases Int.units_eq_one_or (dsg e i) with h' | h' <;> simp [h']
  have hu : u = 1 ∨ u = -1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [u, h']
  -- the lead-in boxes: plane bounds at both indices, then the diagonal coordinates
  have signed : ∀ {q : Fin 2} {A B : ℤ}, A ≤ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)) →
      (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)) ≤ B → -(4 * Y.U + 4 * Y.H + 2) ≤ A → B ≤ 4 * Y.U + 4 * Y.H + 2 →
      |w (pl hd q) - 2 * τ.pos (pl hd q)| ≤ 4 * Y.U + 4 * Y.H + 2 := by
    intro q A B h1 h2 hA hB
    rw [abs_le]; rcases hσ q with h | h <;> rw [h] at h1 h2 <;> constructor <;> linarith
  have near : ∀ {q : Fin 2}, |w (pl hd q) - 2 * τ.pos (pl hd q)| ≤ 4 * Y.U + 4 * Y.H + 2 →
      |w (pl hd (oth q)) - 2 * τ.pos (pl hd (oth q))| ≤ 4 * Y.U + 4 * Y.H + 2 →
      |P - S2| ≤ 8 * Y.U + 8 * Y.H + 4 ∧ |L - Lt| ≤ 8 * Y.U + 8 * Y.H + 4 := by
    intro q h1 h2
    have hb : ∀ i : Fin 2, |w (pl hd i) - 2 * τ.pos (pl hd i)| ≤ 4 * Y.U + 4 * Y.H + 2 := by
      intro i; rcases eq_or_eq_oth i q with hi | hi <;> rw [hi]
      · exact h1
      · exact h2
    have := near_diag (hd := hd) (e := e) (τ := τ) hb
    exact ⟨this.1.trans (by linarith), this.2.trans (by linarith)⟩
  obtain ⟨-, hcases⟩ := hw
  rcases hcases with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4, a5, a6⟩ | ⟨a1, a2, a3, a4, a5, a6⟩ | ⟨a1, a2, a3, a4, a5, -⟩ | ⟨a1, a2, a3, a4, a5, -⟩ |
    ⟨a1, a2, a3, a4, a5, -⟩ | h | h | h
  · -- the first plate's box
    left
    have t4 := abs_le.1 a4
    obtain ⟨hP, hL⟩ := near (q := plIdx hd τ.ax) (signed a1 a2 (by linarith) (by linarith)) (a3.trans (by linarith))
    refine ⟨hP, hL, ?_, ?_⟩ <;> rcases hu with h | h <;> rw [h] <;> linarith
  · left
    obtain ⟨hP, hL⟩ := near (q := plIdx hd τ.ax) (signed a3 a4 (by linarith) (by linarith)) (signed a1 a2 (by linarith) (by linarith))
    exact ⟨hP, hL, a5, by linarith⟩
  · left
    obtain ⟨hP, hL⟩ := near (q := plIdx hd τ.ax) (signed a1 a2 (by linarith) (by linarith)) (signed a3 a4 (by linarith) (by linarith))
    exact ⟨hP, hL, a5, a6⟩
  · right; left; exact ⟨a1, a2, a3, a4, a5⟩
  · right; right; left; exact ⟨a1, a2, a3, a4, a5⟩
  · right; right; right; left; exact ⟨a1, a2, a3, a4, a5⟩
  · right; right; right; right; left; exact h
  · right; right; right; right; right; left; exact h
  · right; right; right; right; right; right; exact h

end Cases

/-! ## Core and entry -/

section Classify

variable (Y : FlatLayout) (hd : 3 ≤ d)

/-- **Strictly inside a cell**: both diagonal coordinates within `2D - 2` of twice the centre. [folklore] -/
def InCell (c : Site 2) (w : Site d) : Prop := ∀ i : Fin 2, |Uc hd i w - 2 * Y.ctr c i| ≤ 2 * Y.Df - 2

/-- **Near the entry face** of the attempt `(a, e)`: the forward coordinate between `22 U` before
and `1` beyond the face between `a` and the target cell, the lateral one within `5120 U` of the
centre. [folklore] -/
def NearFace (a : Site 2) (e : MDir) (w : Site d) : Prop :=
  2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df - 22 * Y.U ≤ (sgOf e : ℤ) * Uc hd e.1 w ∧
    (sgOf e : ℤ) * Uc hd e.1 w ≤ 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df + 1 ∧
    |Uc hd (latDir e true).1 w - 2 * Y.ctr (ftgt a e) (latDir e true).1| ≤ 5120 * Y.U

variable (a : Site 2) (e : MDir) (τ : TTok d)

omit [NeZero d] in
/-- **Core or entry**: a point of the region of an admissible token is strictly inside the target
cell, or near the entry face with, moreover, either its height near the token's (within `6U`, or
between `2m + 1` and `14U + 10H` beyond it along the riser) or — only when the token came straight —
within the band of the layer of `e`. [folklore] -/
theorem fzone_classify (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {w : Site d} (hw : w ∈ fzone Y hd a e τ) :
    InCell Y hd (ftgt a e) w ∨
      (NearFace Y hd a e w ∧
        ((|w (ax0 hd) - 2 * τ.pos (ax0 hd)| ≤ 14 * Y.U + 10 * Y.H) ∨ (τ.src = some e ∧ |w (ax0 hd) - 2 * Y.zOf e| ≤ 8 * Y.U + 2 * Y.H))) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hρ : Y.ρp = 640 * Y.U := rfl
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := hτ.frameS Y hd a e
  have t7 := abs_le.1 f7; have t8 := abs_le.1 f8
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs with h' | h' <;> rw [h'] <;> norm_num
  have hu : (friseDir hd Y e τ : ℤ) = 1 ∨ (friseDir hd Y e τ : ℤ) = -1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [h']
  have hsU : -(Y.U) ≤ (sgOf e : ℤ) * Y.U ∧ (sgOf e : ℤ) * Y.U ≤ Y.U := by rcases hs with h' | h' <;> simp [h'] <;> linarith
  have hcE : cE Y e τ = 0 ∧ τ.src = some e ∨ cE Y e τ = 8 * Y.U := by
    unfold cE; split_ifs with h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr rfl
  have hcases := fzone_cases Y hd a e τ hY hw
  simp only at hcases
  -- the two coordinates of the core, from the forward one being at least `2` beyond the face
  have key : ∀ {P L : ℤ}, P = (sgOf e : ℤ) * Uc hd e.1 w → L = Uc hd (latDir e true).1 w →
      2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df + 2 ≤ P → P ≤ 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) + 2 * Y.Df - 2 →
      |L - 2 * Y.ctr (ftgt a e) (latDir e true).1| ≤ 2 * Y.Df - 2 → InCell Y hd (ftgt a e) w := by
    intro P L hP hL h1 h2 h3 i
    rcases eq_or_ne i e.1 with hi | hi
    · rw [hi]
      have e1 : Uc hd e.1 w - 2 * Y.ctr (ftgt a e) e.1 = (sgOf e : ℤ) * (P - 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1)) := by
        rw [hP]; linear_combination (2 * Y.ctr (ftgt a e) e.1 - Uc hd e.1 w) * hss
      rw [e1, abs_mul, show |(sgOf e : ℤ)| = 1 by rcases hs with h | h <;> simp [h], one_mul, abs_le]
      constructor <;> linarith
    · have hi' : i = (latDir e true).1 := by
        rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h1 | h1 <;>
          simp_all [latDir]
      rw [hi', ← hL]; exact h3
  by_cases hfwd : 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df + 2 ≤ (sgOf e : ℤ) * Uc hd e.1 w
  · -- core
    left
    refine key rfl rfl hfwd ?_ ?_
    · rcases hcases with ⟨a1, -⟩ | ⟨-, -, -, a4, -⟩ | ⟨-, -, -, a4, -⟩ | ⟨-, a2, -⟩ | ⟨-, a2, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩
      · have := abs_le.1 a1; linarith
      · linarith
      · linarith
      · linarith
      · linarith
      · have := abs_le.1 a1; linarith [hsU.1, hsU.2]
      · have := abs_le.1 a1; linarith [hsU.1, hsU.2]
    · rcases hcases with ⟨-, a2, -⟩ | ⟨-, -, -, -, a5⟩ | ⟨-, -, -, -, a5⟩ | ⟨-, -, a3, a4, -⟩ | ⟨-, -, a3, -⟩ | ⟨-, a2, a3, -⟩ | ⟨-, a2, a3, -⟩
      · have := abs_le.1 a2; rw [abs_le]; rcases hs with h | h <;> rw [h] at f3 f4 <;> constructor <;> linarith
      · have := abs_le.1 a5; rw [abs_le]; rcases hs with h | h <;> rw [h] at f3 f4 <;> constructor <;> linarith
      · have := abs_le.1 a5; rw [abs_le]; rcases hs with h | h <;> rw [h] at f3 f4 <;> constructor <;> linarith
      · have hmn : Y.ctr (ftgt a e) (latDir e true).1 - 2302 * Y.U ≤
            min (Uc hd (latDir e true).1 τ.pos - 126 * Y.U) (Y.lane (ftgt a e) e - 22 * Y.U) := by
          rw [le_min_iff]; rcases hs with h | h <;> rw [h] at f3 f4 f5 f6 <;> constructor <;> linarith
        have hmx : max (Uc hd (latDir e true).1 τ.pos + 126 * Y.U) (Y.lane (ftgt a e) e + 22 * Y.U) ≤
            Y.ctr (ftgt a e) (latDir e true).1 + 2302 * Y.U := by
          rw [max_le_iff]; rcases hs with h | h <;> rw [h] at f3 f4 f5 f6 <;> constructor <;> linarith
        rw [abs_le]; constructor <;> linarith
      · have := abs_le.1 a3; rw [abs_le]; rcases hs with h | h <;> rw [h] at f5 f6 <;> constructor <;> linarith
      · rw [abs_le]; rcases hs with h | h <;> rw [h] at f5 f6 a2 a3 <;> constructor <;> linarith
      · rw [abs_le]; rcases hs with h | h <;> rw [h] at f5 f6 a2 a3 <;> constructor <;> linarith
  · -- entry
    right
    push Not at hfwd
    rcases hcases with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, -, a5⟩ | ⟨-, -, a3, -⟩ | ⟨a1, -, a3, a4, a5⟩ | ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩
    · have t1 := abs_le.1 a1; have t2 := abs_le.1 a2
      refine ⟨⟨by linarith, by linarith, ?_⟩, Or.inl ?_⟩
      · rw [abs_le]; rcases hs with h | h <;> rw [h] at f3 f4 <;> constructor <;> linarith
      · rw [abs_le]; rcases hu with h | h <;> rw [h] at a3 a4 <;> constructor <;> linarith
    · have t5 := abs_le.1 a5
      refine ⟨⟨by linarith, by linarith, ?_⟩, Or.inl ?_⟩
      · rw [abs_le]; rcases hs with h | h <;> rw [h] at f3 f4 <;> constructor <;> linarith
      · rw [abs_le]; rcases hu with h | h <;> rw [h] at a1 a2 <;> constructor <;> linarith
    · exfalso; linarith
    · -- the entry side reaches behind the face only when the token came straight
      rcases hcE with ⟨hc0, hsrc⟩ | hc8
      · refine ⟨⟨by linarith, by linarith, ?_⟩, Or.inr ⟨hsrc, a5⟩⟩
        have hmn : Y.ctr (ftgt a e) (latDir e true).1 - 2558 * Y.U ≤
            min (Uc hd (latDir e true).1 τ.pos - 126 * Y.U) (Y.lane (ftgt a e) e - 22 * Y.U) := by
          rw [le_min_iff]; rcases hs with h | h <;> rw [h] at f3 f4 f5 f6 <;> constructor <;> linarith
        have hmx : max (Uc hd (latDir e true).1 τ.pos + 126 * Y.U) (Y.lane (ftgt a e) e + 22 * Y.U) ≤
            Y.ctr (ftgt a e) (latDir e true).1 + 2558 * Y.U := by
          rw [max_le_iff]; rcases hs with h | h <;> rw [h] at f3 f4 f5 f6 <;> constructor <;> linarith
        rw [abs_le]; constructor <;> linarith
      · exfalso; rw [hc8] at a1; linarith
    · exfalso; linarith
    · exfalso; have := abs_le.1 a1; linarith [hsU.1, hsU.2]
    · exfalso; have := abs_le.1 a1; linarith [hsU.1, hsU.2]

end Classify

/-! ## Cells: cores and entries of different attempts -/

section Generic

variable (Y : FlatLayout) (hd : 3 ≤ d)

omit [NeZero d] in
/-- **Cores of different cells are disjoint.** [folklore] -/
theorem incell_incell {c c' : Site 2} (h : c ≠ c') {w : Site d} (h1 : InCell Y hd c w) (h2 : InCell Y hd c' w) : False := by
  obtain ⟨i, hi⟩ := ctr_far_of_ne Y h
  have a1 := abs_le.1 (h1 i); have a2 := abs_le.1 (h2 i)
  have : |2 * Y.ctr c i - 2 * Y.ctr c' i| ≤ 4 * Y.Df - 4 := by rw [abs_le]; constructor <;> linarith
  linarith

omit [NeZero d] in
/-- **A core does not meet the entry of an attempt from another cell.** [folklore] -/
theorem incell_nearface (hY : Y.OK) {c a : Site 2} {e : MDir} (h : c ≠ a) {w : Site d} (h1 : InCell Y hd c w) (h2 : NearFace Y hd a e w) :
    False := by
  obtain ⟨hU, -⟩ := hY.facts
  have hD : Y.Df = 4096 * Y.U := rfl
  have hD0 : 0 < Y.Df := by rw [hD]; positivity
  obtain ⟨n1, n2, n3⟩ := h2
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  obtain ⟨hce, hcl⟩ := ctr_ftgt Y a e
  rw [hce] at n1 n2; rw [hcl] at n3
  have ha := abs_le.1 (h1 e.1)
  have hl := abs_le.1 (h1 (latDir e true).1)
  have t3 := abs_le.1 n3
  have hcc : ∀ i, Y.ctr c i = c i * (2 * Y.Df) := fun i => rfl
  have hca : ∀ i, Y.ctr a i = a i * (2 * Y.Df) := fun i => rfl
  -- laterally `c` agrees with `a`
  have hlat : c (latDir e true).1 = a (latDir e true).1 := by
    rcases ctr_eq_or_far Y c a (latDir e true).1 with heq | hfar
    · exact heq
    · exfalso
      have : |2 * Y.ctr c (latDir e true).1 - 2 * Y.ctr a (latDir e true).1| ≤ 2 * Y.Df - 2 + 5120 * Y.U := by
        rw [abs_le]; constructor <;> linarith
      linarith
  -- along `e`: `s · Uc ∈ 2 s ctr a + 2D + [-22U, 1]` and `|Uc - 2 ctr c| ≤ 2D - 2`; write `c = a + k` there
  set k : ℤ := c e.1 - a e.1 with hk
  have hck : Y.ctr c e.1 = Y.ctr a e.1 + k * (2 * Y.Df) := by rw [hcc, hca, hk]; ring
  rw [hck] at ha
  -- `k ≠ s` (else `c = a + e`… no: `c ≠ a` only; `k = s` is the target cell, allowed!) — the core along `e`
  -- keeps `2` inside the cell `a + k e₁`; the entry is within `[2D - 22U, 2D + 1]` beyond `2 ctr a` along `s`
  have hk0 : k ≠ 0 := by
    intro h0; apply h; funext i
    rcases eq_or_ne i e.1 with hi | hi
    · rw [hi]; omega
    · have hi' : i = (latDir e true).1 := by
        rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h0' | h0' <;> rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h1' | h1' <;> simp_all [latDir]
      rw [hi']; exact hlat
  -- case on the sign and compare `s k` with `1`
  rcases hs with h' | h' <;> rw [h'] at n1 n2
  · -- `s = 1`: `Uc ∈ 2 ctr a + 2D + [-22U, 1]`, `Uc ∈ 2 ctr a + 4 k D ± (2D - 2)`
    rcases lt_trichotomy k 1 with hk1 | hk1 | hk1
    · have : k ≤ -1 := by omega
      nlinarith [ha.1, ha.2, n1, n2]
    · rw [hk1] at ha; linarith [ha.1, ha.2]
    · have : 2 ≤ k := by omega
      nlinarith [ha.1, ha.2, n1, n2]
  · rcases lt_trichotomy k (-1) with hk1 | hk1 | hk1
    · have : k ≤ -2 := by omega
      nlinarith [ha.1, ha.2, n1, n2]
    · rw [hk1] at ha; linarith [ha.1, ha.2]
    · have : 0 ≤ k := by omega
      have : 1 ≤ k := by omega
      nlinarith [ha.1, ha.2, n1, n2]

omit [NeZero d] in
/-- **Entries of different attempts are disjoint**, unless one attempt starts in the other's
target cell. [folklore] -/
theorem nearface_nearface (hY : Y.OK) {a a' : Site 2} {e e' : MDir} (hne : (a, e) ≠ (a', e')) (hac : a' ≠ ftgt a e)
    {w : Site d} (h1 : NearFace Y hd a e w) (h2 : NearFace Y hd a' e' w) : False := by
  obtain ⟨hU, -⟩ := hY.facts
  have hD : Y.Df = 4096 * Y.U := rfl
  obtain ⟨n1, n2, n3⟩ := h1
  obtain ⟨m1, m2, m3⟩ := h2
  have t3 := abs_le.1 n3; have u3 := abs_le.1 m3
  obtain ⟨hce, hcl⟩ := ctr_ftgt Y a e
  obtain ⟨hce', hcl'⟩ := ctr_ftgt Y a' e'
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hs' : (sgOf e' : ℤ) = 1 ∨ (sgOf e' : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e') with h' | h' <;> simp [h']
  rw [hce] at n1 n2; rw [hcl] at t3; rw [hce'] at m1 m2; rw [hcl'] at u3
  have hca : ∀ i, Y.ctr a i = a i * (2 * Y.Df) := fun i => rfl
  have hca' : ∀ i, Y.ctr a' i = a' i * (2 * Y.Df) := fun i => rfl
  by_cases hax : e'.1 = e.1
  · -- parallel: same lateral axis
    have hlat : (latDir e' true).1 = (latDir e true).1 := by
      rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e'.1, rfl⟩ with h1 | h1 <;> simp_all [latDir]
    rw [hax] at m1 m2; rw [hlat] at u3
    -- laterally the centres agree
    rcases ctr_eq_or_far Y a a' (latDir e true).1 with hl | hl
    · -- along `e`: `2 ctr a + s 2D ≈ 2 ctr a' + s' 2D` within `44 U`
      have key : |(2 * Y.ctr a e.1 + (sgOf e : ℤ) * (2 * Y.Df)) - (2 * Y.ctr a' e.1 + (sgOf e' : ℤ) * (2 * Y.Df))| ≤ 44 * Y.U + 1 := by
        rw [abs_le]; rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h] at n1 n2 ⊢ <;> rw [h'] at m1 m2 ⊢ <;> constructor <;> linarith
      rw [hca, hca'] at key
      have e1 : 2 * (a e.1 * (2 * Y.Df)) + (sgOf e : ℤ) * (2 * Y.Df) - (2 * (a' e.1 * (2 * Y.Df)) + (sgOf e' : ℤ) * (2 * Y.Df)) =
          (2 * (a e.1 - a' e.1) + ((sgOf e : ℤ) - sgOf e')) * (2 * Y.Df) := by ring
      have hD2 : (0 : ℤ) ≤ 2 * Y.Df := by rw [hD]; positivity
      rw [e1, abs_mul, abs_of_nonneg hD2] at key
      have hz : 2 * (a e.1 - a' e.1) + ((sgOf e : ℤ) - sgOf e') = 0 := by
        by_contra h0
        have h1' : 1 ≤ |2 * (a e.1 - a' e.1) + ((sgOf e : ℤ) - sgOf e')| := Int.one_le_abs h0
        have := mul_le_mul_of_nonneg_right h1' hD2
        linarith
      rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h, h'] at hz
      · -- same sign: same cell and direction
        apply hne
        have hae : a = a' := by
          funext i; rcases eq_or_ne i e.1 with hi | hi
          · rw [hi]; omega
          · have hi' : i = (latDir e true).1 := by
              rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h1 | h1 <;> simp_all [latDir]
            rw [hi']; exact hl
        have hee : e = e' := by
          refine Prod.ext_iff.2 ⟨(hax : e'.1 = e.1).symm, ?_⟩
          have h2 : (sgOf e : ℤ) = sgOf e' := by rw [h, h']
          unfold sgOf at h2; cases h3 : e.2 <;> cases h4 : e'.2 <;> simp_all
        rw [hae, hee]
      · -- opposite signs: `a' = a + e`, the target cell
        apply hac; funext i
        unfold ftgt; rw [Pi.add_apply, stepVec_apply]
        rcases eq_or_ne i e.1 with hi | hi
        · rw [hi, if_pos rfl, h]; omega
        · have hi' : i = (latDir e true).1 := by
            rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h1 | h1 <;> simp_all [latDir]
          rw [hi', if_neg (latDir_fst_ne e true)]; linarith
      · apply hac; funext i
        unfold ftgt; rw [Pi.add_apply, stepVec_apply]
        rcases eq_or_ne i e.1 with hi | hi
        · rw [hi, if_pos rfl, h]; omega
        · have hi' : i = (latDir e true).1 := by
            rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h1 | h1 <;> simp_all [latDir]
          rw [hi', if_neg (latDir_fst_ne e true)]; linarith
      · apply hne
        have hae : a = a' := by
          funext i; rcases eq_or_ne i e.1 with hi | hi
          · rw [hi]; omega
          · have hi' : i = (latDir e true).1 := by
              rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h1 | h1 <;> simp_all [latDir]
            rw [hi']; exact hl
        have hee : e = e' := by
          refine Prod.ext_iff.2 ⟨(hax : e'.1 = e.1).symm, ?_⟩
          have h2 : (sgOf e : ℤ) = sgOf e' := by rw [h, h']
          unfold sgOf at h2; cases h3 : e.2 <;> cases h4 : e'.2 <;> simp_all
        rw [hae, hee]
    · have : |2 * Y.ctr a (latDir e true).1 - 2 * Y.ctr a' (latDir e true).1| ≤ 10240 * Y.U := by rw [abs_le]; constructor <;> linarith
      linarith
  · -- perpendicular: their lateral axis is our forward axis; a face value is `2D` off any centre
    have hlat' : (latDir e' true).1 = e.1 := by
      rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e'.1, rfl⟩ with h1 | h1 <;> simp_all [latDir]
    rw [hlat'] at u3
    -- `|Uc_{e.1} w - 2 ctr a' e.1| ≤ 5120 U` and `s Uc_{e.1} w ∈ 2 s ctr a e.1 + 2D + [-22U, 1]`
    have key : |(2 * Y.ctr a e.1 + (sgOf e : ℤ) * (2 * Y.Df)) - 2 * Y.ctr a' e.1| ≤ 5120 * Y.U + 22 * Y.U + 1 := by
      rw [abs_le]; rcases hs with h | h <;> rw [h] at n1 n2 ⊢ <;> constructor <;> linarith
    rw [hca, hca'] at key
    have e1 : 2 * (a e.1 * (2 * Y.Df)) + (sgOf e : ℤ) * (2 * Y.Df) - 2 * (a' e.1 * (2 * Y.Df)) = (2 * (a e.1 - a' e.1) + (sgOf e : ℤ)) * (2 * Y.Df) := by ring
    have hD2 : (0 : ℤ) ≤ 2 * Y.Df := by rw [hD]; positivity
    rw [e1, abs_mul, abs_of_nonneg hD2] at key
    have h1' : 1 ≤ |2 * (a e.1 - a' e.1) + (sgOf e : ℤ)| := by
      apply Int.one_le_abs; rcases hs with h | h <;> rw [h] <;> omega
    have := mul_le_mul_of_nonneg_right h1' hD2
    linarith

end Generic

/-! ## Layers -/

section Layers

variable (Y : FlatLayout)

omit [NeZero d] in
/-- **Two layer bands do not meet**: a height within `8U + 2H` of twice one layer and within
`22U + 10H` of twice another, distinct, layer is impossible (`2W = 32U`, `12H < 2U`). [folklore] -/
theorem layers_apartF (hY : Y.OK) {e e' : MDir} (h : e ≠ e') {Z : ℤ} (h1 : |Z - 2 * Y.zOf e| ≤ 8 * Y.U + 2 * Y.H)
    (h2 : |Z - 2 * Y.zOf e'| ≤ 22 * Y.U + 10 * Y.H) : False := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hW := Wl_le_abs_zOf_sub Y h
  unfold FlatLayout.Wl at hW
  have t1 := abs_le.1 h1; have t2 := abs_le.1 h2
  have : |Y.zOf e - Y.zOf e'| ≤ 15 * Y.U + 6 * Y.H := by rw [abs_le]; constructor <;> linarith
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  linarith

end Layers

end BGNd

end Percolation.Literature

end

/-!
# Part 2 (The flat gait, XXXIV): static disjointness, II — same target, target-source, assembly

The second half of Grimmett's (C) for the flat block
construction (*Percolation*, 2nd ed. (1999), §7.3 p. 173, case `H < L`). Every point of a region
lies in its riser column near the entry face or in the band of the layer of its direction
(`fzone_col_or_planar`). Two attempts aimed at the same cell from different faces keep apart
inside it: their planar parts lie in the bands of different layers, and the riser column of one —
near its entry face on the `+Λ` side — is away from every piece of the other, whose trunk and
branches run on the `-Λ` sides of the faces they cross (`col_vs_sameTarget`,
`fsameTarget_disjoint`). An attempt aimed at the source cell of another, other than from its target
and other than its parent, reaches the latter's entry neither with its planar parts, in the band of
its own layer while the entry stands on the layer of the true parent, nor with its column, at its
own entry face (`ftargetSource_disjoint`). With the cell arithmetic of `FlatStatic` this gives the
static disjointness of the regions (`fzone_disjoint`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : FlatLayout) (hd : 3 ≤ d)

/-! ## Two attempts with the same target -/

section SameTarget

omit [NeZero d] in
/-- Directions with the same macro-axis are equal or reverse to each other. [folklore] -/
theorem eq_or_eq_rev_of_fst_eq {e e' : MDir} (h : e'.1 = e.1) : e' = e ∨ e' = rev e := by
  obtain ⟨i, b⟩ := e; obtain ⟨i', b'⟩ := e'
  simp only at h; subst h
  cases b <;> cases b' <;> simp [rev]

omit [NeZero d] in
/-- The other macro-axis. [folklore] -/
theorem fst_eq_lat_of_ne {e e' : MDir} (h : e'.1 ≠ e.1) : e'.1 = (latDir e true).1 ∧ (latDir e' true).1 = e.1 := by
  rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e'.1, rfl⟩ with h1 | h1 <;>
    simp_all [latDir]

omit [NeZero d] in
/-- **The riser column of an attempt avoids the region of another attempt with the same target.**
The column: at most `440 U` beyond the entry face, within `222 U` of the token laterally
(doubled coordinates); the other attempt enters through another face: the opposite one
(its column and entry side are across the cell, its trunk and second branch run on lanes at least
`972 U` off ours, its first branch turns before reaching our face) or a perpendicular one (its
column, entry side and trunk keep within `4608 U` of the centre line while our column is within
`440 U` of a face; a branch reaching our face does so on the far side of our column, or is too
short to reach our lane). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem col_vs_sameTarget (hY : Y.OK) {a a' : Site 2} {e e' : MDir} {τ τ' : TTok d} (hτ : FTAdm hd Y a e τ) (hτ' : FTAdm hd Y a' e' τ')
    (hcc : ftgt a' e' = ftgt a e) (hee : e' ≠ e) {w : Site d}
    (hP2 : (sgOf e : ℤ) * Uc hd e.1 w ≤ 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df + 440 * Y.U)
    (hL : |Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 τ.pos| ≤ 222 * Y.U) (hw' : w ∈ fzone Y hd a' e' τ') : False := by
  obtain ⟨hU, -, -, -, -, hHU, -⟩ := hY.facts
  have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hρ : Y.ρp = 640 * Y.U := rfl
  obtain ⟨-, -, f3, f4, -⟩ := hτ.frameS Y hd a e
  obtain ⟨-, g2, g3, g4, g5, g6, g7, g8, -⟩ := hτ'.frameS Y hd a' e'
  rw [hcc] at g2 g3 g4 g5 g6 g7 g8
  have tL := abs_le.1 hL
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hs' : (sgOf e' : ℤ) = 1 ∨ (sgOf e' : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e') with h' | h' <;> simp [h']
  -- our lateral coordinate, signed: on the `+Λ` side of the centre, between `546 U` and `4574 U`
  have oursL : 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1) + 546 * Y.U ≤ (sgOf e : ℤ) * Uc hd (latDir e true).1 w ∧
      (sgOf e : ℤ) * Uc hd (latDir e true).1 w ≤ 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1) + 4574 * Y.U := by
    rcases hs with h | h <;> rw [h] at f3 f4 ⊢ <;> constructor <;> linarith
  have hcases := fzone_cases Y hd a' e' τ' hY hw'
  simp only [hcc] at hcases
  by_cases hax : e'.1 = e.1
  · -- the reverse direction: `s' = -s`, same axes
    have hrev : e' = rev e := (eq_or_eq_rev_of_fst_eq hax).resolve_left hee
    have hss : (sgOf e' : ℤ) = -(sgOf e : ℤ) := by rw [hrev, sgOf_rev]
    have hlat : (latDir e' true).1 = (latDir e true).1 := by
      rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e'.1, rfl⟩ with h1 | h1 <;> simp_all [latDir]
    rw [hax, hss] at g2 g7 g8
    rw [hlat, hss] at g5 g6
    have t7 := abs_le.1 g7
    simp only [hax, hlat, hss] at hcases
    rcases hcases with ⟨a1, -⟩ | ⟨-, -, -, a4, -⟩ | ⟨-, -, -, a4, -⟩ | ⟨-, a2, -⟩ | ⟨-, -, a3, -⟩ | ⟨a1, -⟩ | ⟨-, a2, -⟩
    · -- their lead-in is at the opposite face
      have t1 := abs_le.1 a1
      rcases hs with h | h <;> rw [h] at t1 g2 hP2 <;> linarith
    · rcases hs with h | h <;> rw [h] at a4 hP2 <;> linarith
    · rcases hs with h | h <;> rw [h] at a4 g2 hP2 <;> linarith
    · rcases hs with h | h <;> rw [h] at a2 g2 hP2 <;> linarith
    · -- their trunk runs on the lane of the opposite sign
      have t3 := abs_le.1 a3
      rcases hs with h | h <;> rw [h] at g5 g6 oursL <;> linarith
    · -- their first branch turns off `Λ ± Λ_J` before our face
      have t1 := abs_le.1 a1
      rcases hs with h | h <;> rw [h] at t1 t7 hP2 <;> linarith
    · -- their second branch stays on the far side of their lane
      rcases hs with h | h <;> rw [h] at a2 g5 g6 oursL <;> linarith
  · -- the perpendicular directions: their forward axis is our lateral one
    obtain ⟨hax', hlat'⟩ := fst_eq_lat_of_ne hax
    rw [hax'] at g2 g7 g8
    rw [hlat'] at g3 g4 g5 g6
    have t7 := abs_le.1 g7; have t8 := abs_le.1 g8
    simp only [hax', hlat'] at hcases
    rcases hcases with ⟨-, a2, -⟩ | ⟨-, -, -, -, a5⟩ | ⟨-, -, -, -, a5⟩ | ⟨-, -, a3, a4, -⟩ | ⟨-, -, a3, -⟩ | ⟨a1, -, a3, -⟩ | ⟨a1, a2, -⟩
    · -- their lead-in, column and entry side keep within `4608 U` of the centre line across our face
      have t2 := abs_le.1 a2
      rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h] at hP2 <;> rw [h'] at g3 g4 <;> linarith
    · have t5 := abs_le.1 a5
      rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h] at hP2 <;> rw [h'] at g3 g4 <;> linarith
    · have t5 := abs_le.1 a5
      rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h] at hP2 <;> rw [h'] at g3 g4 <;> linarith
    · have hmn : Y.ctr (ftgt a e) e.1 - 2302 * Y.U ≤ min (Uc hd e.1 τ'.pos - 126 * Y.U) (Y.lane (ftgt a e) e' - 22 * Y.U) := by
        rw [le_min_iff]; rcases hs' with h' | h' <;> rw [h'] at g3 g4 g5 g6 <;> constructor <;> linarith
      have hmx : max (Uc hd e.1 τ'.pos + 126 * Y.U) (Y.lane (ftgt a e) e' + 22 * Y.U) ≤ Y.ctr (ftgt a e) e.1 + 2302 * Y.U := by
        rw [max_le_iff]; rcases hs' with h' | h' <;> rw [h'] at g3 g4 g5 g6 <;> constructor <;> linarith
      rcases hs with h | h <;> rw [h] at hP2 <;> linarith
    · -- their trunk: within `Λ + Λ_J + 1076 U` of the centre line
      have t3 := abs_le.1 a3
      rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h] at hP2 <;> rw [h'] at g5 g6 <;> linarith
    · -- their first branch: towards our face only on the other sign, else short of our lane
      have t1 := abs_le.1 a1
      rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h] at hP2 oursL <;> rw [h'] at t1 t7 a3 g5 g6 <;> linarith
    · -- their second branch: towards our face only on our sign, then beyond our lane
      have t1 := abs_le.1 a1
      rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h] at hP2 oursL <;> rw [h'] at t1 t8 a2 g5 g6 <;> linarith

end SameTarget

/-! ## Columns and planar parts; inside a cell -/

section Split

omit [NeZero d] in
/-- **Column or planar**: a point of the region of an admissible token lies either in the riser
column near the entry face (at most `440 U` beyond it, within `222 U` of the token laterally) or
in the band of the layer of `e`. [folklore] -/
theorem fzone_col_or_planar (hY : Y.OK) {a : Site 2} {e : MDir} {τ : TTok d} (hτ : FTAdm hd Y a e τ) {w : Site d}
    (hw : w ∈ fzone Y hd a e τ) :
    ((sgOf e : ℤ) * Uc hd e.1 w ≤ 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df + 440 * Y.U ∧
        |Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 τ.pos| ≤ 222 * Y.U) ∨
      |w (ax0 hd) - 2 * Y.zOf e| ≤ 8 * Y.U + 2 * Y.H := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨f1, f2, -⟩ := hτ.frameS Y hd a e
  have hcases := fzone_cases Y hd a e τ hY hw
  simp only at hcases
  rcases hcases with ⟨a1, a2, -⟩ | ⟨-, -, -, a4, a5⟩ | ⟨-, -, -, a4, a5⟩ | ⟨-, -, -, -, a5⟩ | ⟨-, -, -, a4⟩ |
    ⟨-, -, -, a4⟩ | ⟨-, -, -, a4⟩
  · left; have t1 := abs_le.1 a1; exact ⟨by linarith, a2.trans (by linarith)⟩
  · left; exact ⟨by linarith, a5⟩
  · left; exact ⟨by linarith, a5⟩
  · right; exact a5
  · right; exact a4
  · right; exact a4
  · right; exact a4

end Split

/-! ## Same target; target equal to source -/

section Pairs

omit [NeZero d] in
/-- **Two attempts with the same target have disjoint regions**: columns by `col_vs_sameTarget`,
planar parts by the layers. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem fsameTarget_disjoint (hY : Y.OK) {a a' : Site 2} {e e' : MDir} {τ τ' : TTok d} (hτ : FTAdm hd Y a e τ) (hτ' : FTAdm hd Y a' e' τ')
    (hcc : ftgt a e = ftgt a' e') (hne : (a, e) ≠ (a', e')) {w : Site d} (hw : w ∈ fzone Y hd a e τ) (hw' : w ∈ fzone Y hd a' e' τ') :
    False := by
  obtain ⟨hU, -⟩ := hY.facts
  have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  -- the directions differ
  have hee : e ≠ e' := by
    intro h; subst h; apply hne
    have h1 : a + stepVec e = a' + stepVec e := hcc
    rw [add_right_cancel h1]
  rcases fzone_col_or_planar Y hd hY hτ hw with ⟨hP, hL⟩ | hZ
  · exact col_vs_sameTarget Y hd hY hτ hτ' hcc.symm (Ne.symm hee) hP hL hw'
  rcases fzone_col_or_planar Y hd hY hτ' hw' with ⟨hP', hL'⟩ | hZ'
  · exact col_vs_sameTarget Y hd hY hτ' hτ hcc hee hP' hL' hw
  exact layers_apartF Y hY hee hZ (hZ'.trans (by linarith))

omit [NeZero d] in
/-- **An attempt aimed at the source cell of another, other than from its target and other than
its parent, avoids its entry**: the entry stands on the layer of the true parent (or of `e`, when
the token came straight), the other's planar parts on its own layer, and its column is at its own
entry face, far across or beside the cell. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem ftargetSource_disjoint (hY : Y.OK) {a a' : Site 2} {e e' : MDir} {τ τ' : TTok d} (hτ : FTAdm hd Y a e τ) (hτ' : FTAdm hd Y a' e' τ')
    (hca : ftgt a' e' = a) (h2 : a' ≠ ftgt a e) (h3 : ∀ d', τ.src = some d' → d' ≠ e') {w : Site d} (hn : NearFace Y hd a e w)
    (hz : |w (ax0 hd) - 2 * τ.pos (ax0 hd)| ≤ 14 * Y.U + 10 * Y.H ∨ (τ.src = some e ∧ |w (ax0 hd) - 2 * Y.zOf e| ≤ 8 * Y.U + 2 * Y.H))
    (hw' : w ∈ fzone Y hd a' e' τ') : False := by
  obtain ⟨hU, -⟩ := hY.facts
  have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hρ : Y.ρp = 640 * Y.U := rfl
  have hρv : Y.ρv = 4 * Y.U := rfl
  -- a layer band containing the height of `w`, other than that of `e'`
  obtain ⟨g, hg, hZ⟩ : ∃ g, g ≠ e' ∧ |w (ax0 hd) - 2 * Y.zOf g| ≤ 22 * Y.U + 10 * Y.H := by
    obtain ⟨-, -, -, -, -, -, -, -, d', hd', hh⟩ := hτ.frameS Y hd a e
    rcases hz with hz | ⟨hsrc, hz⟩
    · refine ⟨d', h3 d' hd', ?_⟩
      have t1 := abs_le.1 hz; have t2 := abs_le.1 hh
      rw [abs_le]; constructor <;> linarith
    · exact ⟨e, h3 e hsrc, hz.trans (by linarith)⟩
  rcases fzone_col_or_planar Y hd hY hτ' hw' with ⟨hP', hL'⟩ | hZ'
  · obtain ⟨n1, n2, -⟩ := hn
    obtain ⟨-, -, g3, g4, -⟩ := hτ'.frameS Y hd a' e'
    rw [hca] at hP' g3 g4
    obtain ⟨hce, -⟩ := ctr_ftgt Y a e
    rw [hce] at n1 n2
    have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
    have hs' : (sgOf e' : ℤ) = 1 ∨ (sgOf e' : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e') with h' | h' <;> simp [h']
    have tL := abs_le.1 hL'
    by_cases hax : e'.1 = e.1
    · -- parallel: `e' = e`, the reverse would make `a'` the target cell
      have hee : e' = e := by
        rcases eq_or_eq_rev_of_fst_eq hax with h | h
        · exact h
        · exact absurd (eq_tgtCell_of_rev hca h) h2
      subst hee
      rcases hs with h | h <;> rw [h] at n1 n2 hP' <;> linarith
    · -- perpendicular: their column is near the centre line of `a` across our face
      obtain ⟨-, hlat'⟩ := fst_eq_lat_of_ne hax
      rw [hlat'] at tL g3 g4
      rcases hs with h | h <;> rcases hs' with h' | h' <;> rw [h] at n1 n2 <;> rw [h'] at g3 g4 <;> linarith
  · exact layers_apartF Y hY (Ne.symm hg) hZ' hZ

end Pairs

/-! ## Conclusion -/

section Conclusion

omit [NeZero d] in
/-- **Static disjointness of the regions** (`Kit.Good.disjoint_zone` at the level of regions): the
regions of two admissible attempts are disjoint unless the attempts coincide, or the second starts
in the target cell of the first, or the second is the parent of the first's token.
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem fzone_disjoint (hY : Y.OK) {a a' : Site 2} {e e' : MDir} {τ τ' : TTok d} (hτ : FTAdm hd Y a e τ) (hτ' : FTAdm hd Y a' e' τ')
    (h1 : (a, e) ≠ (a', e')) (h2 : a' ≠ ftgt a e) (h3 : ∀ d', ftgt a' e' = a → τ.src = some d' → d' ≠ e') {w : Site d}
    (hw : w ∈ fzone Y hd a e τ) (hw' : w ∈ fzone Y hd a' e' τ') : False := by
  by_cases hcc : ftgt a e = ftgt a' e'
  · exact fsameTarget_disjoint Y hd hY hτ hτ' hcc h1 hw hw'
  rcases fzone_classify Y hd a e τ hY hτ hw with hc | ⟨hn, hz⟩ <;>
    rcases fzone_classify Y hd a' e' τ' hY hτ' hw' with hc' | ⟨hn', -⟩
  · exact incell_incell Y hd hcc hc hc'
  · exact incell_nearface Y hd hY (Ne.symm h2) hc hn'
  · by_cases hca : ftgt a' e' = a
    · exact ftargetSource_disjoint Y hd hY hτ hτ' hca h2 (fun d' => h3 d' hca) hn hz hw'
    · exact incell_nearface Y hd hY hca hc' hn
  · exact nearface_nearface Y hd hY h1 h2 hn hn'

end Conclusion

end BGNd

end Percolation.Literature

end

/-!
# Part 3 (The flat gait, XXXV): static disjointness, III — the regions avoid the initial open set

The last static obligation of the flat block
construction (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 p. 171 and (C) p. 173, case `H < L`):
the region of an admissible attempt not aimed at the origin cell contains no doubled midpoint of an
edge of `U₀` (`fzone_avoids_U0F`). The midpoints of `U₀` lie in the closed core of the origin cell,
on the first plane axis within `5376 U` and on the second within `2814 U + 2m` of the origin, and
those near a face of the origin cell belong to the initial path or seed of the token of that face
and stand on the layer of its nominal provenance (`dmid_U0F`); a region aimed elsewhere meets them
neither with its core (another cell), nor with its entry from a cell other than the origin, nor —
from the origin — with the entry of a handed-on token (another layer) or of the initial token
itself, whose plates stand beyond the seed and whose entry side starts `16 U` beyond it
(`init_notMem_fzone`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : FlatLayout) (hd : 3 ≤ d)

/-! ## The doubled midpoints of `U₀` -/

section U0

omit [NeZero d] in
/-- **Near a face of the origin cell only at the token of that face**: a point with first plane
coordinate `5376 s'' U` and second within `2814 U + 2m` of `2814 ι'' s'' U` whose diagonal
coordinate along `e` read outwards is at least `2D - 22U` has `e = e''`. [folklore] -/
theorem eq_of_near_face (hY : Y.OK) {e e'' : MDir} {w : Site d} (h0 : w (pl hd 0) = (sgOf e'' : ℤ) * (5376 * Y.U))
    (h1 : |w (pl hd 1) - iotaOf e'' * ((sgOf e'' : ℤ) * (2814 * Y.U))| ≤ 2814 * Y.U + 2 * Y.m)
    (hfar : 2 * Y.Df - 22 * Y.U ≤ (sgOf e : ℤ) * Uc hd e.1 w) : e = e'' := by
  obtain ⟨hU, -, -, hLp0, hULp, -⟩ := hY.facts
  have hD : Y.Df = 4096 * Y.U := rfl
  have hUc : Uc hd e.1 w = w (pl hd 0) + (if e.1 = 0 then 1 else -1) * w (pl hd 1) := rfl
  rw [hUc, h0] at hfar
  have t1 := abs_le.1 h1
  obtain ⟨i, b⟩ := e
  obtain ⟨i'', b''⟩ := e''
  simp only [sgOf_val, iotaOf] at hfar t1
  fin_cases i <;> fin_cases i'' <;> cases b <;> cases b'' <;> simp at hfar t1 ⊢ <;> linarith

variable {Y hd}

omit [NeZero d] in
/-- **The doubled midpoints of `U₀`**: both diagonal coordinates at most `2D - 4` in absolute
value; the first plane coordinate at most `5376 U`, the second at most `2814 U + 2m`; and a
midpoint whose diagonal coordinate along `e`, read outwards, is at least `2D - 22U` stands within
`2m` of twice the layer of `rev e` (it belongs to the path or seed of the initial token towards
`e`). [cite: GrimmettPercolation1999, §7.3 p. 171] -/
theorem dmid_U0F (hY : Y.OK) {z : Sym2 (Site d)} (hz : z ∈ U0F Y hd) :
    (∀ i, |Uc hd i (dmid z)| ≤ 2 * Y.Df - 4) ∧ |dmid z (pl hd 0)| ≤ 5376 * Y.U ∧ |dmid z (pl hd 1)| ≤ 2814 * Y.U + 2 * Y.m ∧
      ∀ e : MDir, 2 * Y.Df - 22 * Y.U ≤ (sgOf e : ℤ) * Uc hd e.1 (dmid z) → |dmid z (ax0 hd) - 2 * Y.zOf (rev e)| ≤ 2 * Y.m := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hD : Y.Df = 4096 * Y.U := rfl
  have h01 : pl hd (0 : Fin 2) ≠ pl hd 1 := pl_ne_pl hd (by decide)
  have hUc : ∀ (i : Fin 2) (x : Site d), Uc hd i x = x (pl hd 0) + (if i = 0 then 1 else -1) * x (pl hd 1) := fun i x => rfl
  have hκ : ∀ i : Fin 2, (if i = 0 then (1 : ℤ) else -1) = 1 ∨ (if i = 0 then (1 : ℤ) else -1) = -1 := fun i => by
    split_ifs <;> simp
  have hs : ∀ e : MDir, (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := fun e => by
    rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hι : ∀ e : MDir, iotaOf e = 1 ∨ iotaOf e = -1 := fun e => by unfold iotaOf; split_ifs <;> simp
  rw [U0F, Finset.mem_biUnion] at hz
  obtain ⟨e'', -, hz⟩ := hz
  have hιs : iotaOf e'' * (sgOf e'' : ℤ) = 1 ∨ iotaOf e'' * (sgOf e'' : ℤ) = -1 := by
    rcases hs e'' with h | h <;> rcases hι e'' with h' | h' <;> rw [h, h'] <;> norm_num
  -- values of the initial points
  have hP0 : initPosF Y hd e'' (pl hd 0) = (sgOf e'' : ℤ) * (2688 * Y.U) := by simp [initPosF]
  have hP1 : initPosF Y hd e'' (pl hd 1) = iotaOf e'' * ((sgOf e'' : ℤ) * (1407 * Y.U)) := by simp [initPosF, h01.symm]
  have hPz : initPosF Y hd e'' (ax0 hd) = Y.zOf (rev e'') := by simp [initPosF, (pl_ne_ax0 hd 0).symm, (pl_ne_ax0 hd 1).symm]
  have hQ1a : initQ1 Y hd e'' (pl hd 0) = 0 := by unfold initQ1; rw [shift_apply_of_ne _ (pl_ne_ax0 hd 0)]; rfl
  have hQ1b : initQ1 Y hd e'' (pl hd 1) = 0 := by unfold initQ1; rw [shift_apply_of_ne _ (pl_ne_ax0 hd 1)]; rfl
  have hQ1z : initQ1 Y hd e'' (ax0 hd) = Y.zOf (rev e'') := by unfold initQ1; rw [shift_apply_self]; simp
  have hQ2a : initQ2 Y hd e'' (pl hd 0) = (sgOf e'' : ℤ) * (2688 * Y.U) := by unfold initQ2; rw [shift_apply_self, hQ1a, zero_add]
  have hQ2b : initQ2 Y hd e'' (pl hd 1) = 0 := by unfold initQ2; rw [shift_apply_of_ne _ h01.symm, hQ1b]
  have hQ2z : initQ2 Y hd e'' (ax0 hd) = Y.zOf (rev e'') := by unfold initQ2; rw [shift_apply_of_ne _ (pl_ne_ax0 hd 0).symm, hQ1z]
  -- the common conclusion from the two plane coordinates
  have conclude : ∀ {w0 w1 wz : ℤ}, dmid z (pl hd 0) = w0 → dmid z (pl hd 1) = w1 → dmid z (ax0 hd) = wz →
      |w0| ≤ 5376 * Y.U → |w1| ≤ 2814 * Y.U + 2 * Y.m →
      (∀ e : MDir, 2 * Y.Df - 22 * Y.U ≤ (sgOf e : ℤ) * Uc hd e.1 (dmid z) → |wz - 2 * Y.zOf (rev e)| ≤ 2 * Y.m) →
      (∀ i, |Uc hd i (dmid z)| ≤ 2 * Y.Df - 4) ∧ |dmid z (pl hd 0)| ≤ 5376 * Y.U ∧ |dmid z (pl hd 1)| ≤ 2814 * Y.U + 2 * Y.m ∧
        ∀ e : MDir, 2 * Y.Df - 22 * Y.U ≤ (sgOf e : ℤ) * Uc hd e.1 (dmid z) → |dmid z (ax0 hd) - 2 * Y.zOf (rev e)| ≤ 2 * Y.m := by
    intro w0 w1 wz e0 e1 ez b0 b1 bz
    refine ⟨fun i => ?_, by rw [e0]; exact b0, by rw [e1]; exact b1, by rw [ez]; exact bz⟩
    rw [hUc, e0, e1]
    have a0 := le_abs_self w0; have a0' := neg_abs_le w0
    have a1 := le_abs_self w1; have a1' := neg_abs_le w1
    rw [abs_le]; rcases hκ i with h | h <;> rw [h] <;> constructor <;> linarith
  rw [Finset.mem_union] at hz
  rcases hz with hz | hz
  · -- the seed square of the initial token towards `e''`
    obtain ⟨h0, hj⟩ := dmid_of_mem_sqEdgesAt hz
    rw [hP0] at h0
    have h1 := hj (pl hd 1) h01.symm
    have hzz := hj (ax0 hd) (pl_ne_ax0 hd 0).symm
    rw [hP1] at h1; rw [hPz] at hzz
    have t1 := abs_le.1 h1
    have h1' : |dmid z (pl hd 1) - iotaOf e'' * ((sgOf e'' : ℤ) * (2814 * Y.U))| ≤ 2814 * Y.U + 2 * Y.m := by
      rw [show iotaOf e'' * ((sgOf e'' : ℤ) * (2814 * Y.U)) = (iotaOf e'' * (sgOf e'' : ℤ)) * (2814 * Y.U) by ring, abs_le]
      rw [show iotaOf e'' * ((sgOf e'' : ℤ) * (1407 * Y.U)) = (iotaOf e'' * (sgOf e'' : ℤ)) * (1407 * Y.U) by ring] at t1
      rcases hιs with h | h <;> rw [h] at t1 ⊢ <;> constructor <;> linarith
    refine conclude h0 rfl rfl ?_ ?_ fun e he => ?_
    · rw [abs_le]; rcases hs e'' with h | h <;> rw [h] <;> constructor <;> linarith
    · rw [show iotaOf e'' * ((sgOf e'' : ℤ) * (1407 * Y.U)) = (iotaOf e'' * (sgOf e'' : ℤ)) * (1407 * Y.U) by ring] at t1
      rw [abs_le]; rcases hιs with h | h <;> rw [h] at t1 <;> constructor <;> linarith
    · rw [eq_of_near_face Y hd hY (by rw [h0]; ring) h1' he]; exact hzz
  · rw [initPathF, Finset.mem_union, Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · -- the vertical leg above the origin
      obtain ⟨hj, -, -⟩ := dmid_of_mem_segEdges hz
      have h0 := hj (pl hd 0) (pl_ne_ax0 hd 0); have h1 := hj (pl hd 1) (pl_ne_ax0 hd 1)
      simp only [Pi.zero_apply, mul_zero] at h0 h1
      refine conclude h0 h1 rfl (by rw [abs_zero]; linarith) (by rw [abs_zero]; linarith) fun e he => ?_
      exfalso; rw [hUc, h0, h1] at he
      rcases hs e with h | h <;> rw [h] at he <;> simp at he <;> linarith
    · -- the leg along the first plane axis
      obtain ⟨hj, hlo, hhi⟩ := dmid_of_mem_segEdges hz
      have h1 := hj (pl hd 1) h01.symm
      rw [hQ1b, mul_zero] at h1
      rw [hQ1a, mul_zero, sub_zero] at hlo hhi
      rw [Int.toNat_of_nonneg (by linarith)] at hhi
      have b0 : |dmid z (pl hd 0)| ≤ 5376 * Y.U := by
        rw [abs_le]; split_ifs at hlo hhi <;> constructor <;> linarith
      refine conclude rfl h1 rfl b0 (by rw [abs_zero]; linarith) fun e he => ?_
      exfalso; rw [hUc, h1] at he
      have := abs_le.1 b0
      rcases hs e with h | h <;> rw [h] at he <;> simp at he <;> linarith
    · -- the leg along the second plane axis, ending at the initial position
      obtain ⟨hj, hlo, hhi⟩ := dmid_of_mem_segEdges hz
      have h0 := hj (pl hd 0) h01; have hzz := hj (ax0 hd) (pl_ne_ax0 hd 1).symm
      rw [hQ2a] at h0; rw [hQ2z] at hzz
      rw [hQ2b, mul_zero, sub_zero] at hlo hhi
      rw [Int.toNat_of_nonneg (by linarith)] at hhi
      -- the leg runs in the direction `ι'' s''`
      have key : 1 ≤ iotaOf e'' * (sgOf e'' : ℤ) * dmid z (pl hd 1) ∧ iotaOf e'' * (sgOf e'' : ℤ) * dmid z (pl hd 1) ≤ 2 * (1407 * Y.U) - 1 := by
        split_ifs at hlo hhi with hb
        · have hb' : 0 ≤ iotaOf e'' * (sgOf e'' : ℤ) := of_decide_eq_true hb
          rcases hιs with h | h
          · rw [h]; constructor <;> linarith
          · exfalso; rw [h] at hb'; norm_num at hb'
        · have hb' : ¬(0 ≤ iotaOf e'' * (sgOf e'' : ℤ)) := fun h => hb (decide_eq_true h)
          rcases hιs with h | h
          · exfalso; rw [h] at hb'; norm_num at hb'
          · rw [h]; constructor <;> linarith
      obtain ⟨k1, k2⟩ := key
      have b1 : |dmid z (pl hd 1)| ≤ 2814 * Y.U - 1 := by
        rw [abs_le]; rcases hιs with h | h <;> rw [h] at k1 k2 <;> constructor <;> linarith
      have h1' : |dmid z (pl hd 1) - iotaOf e'' * ((sgOf e'' : ℤ) * (2814 * Y.U))| ≤ 2814 * Y.U + 2 * Y.m := by
        rw [show iotaOf e'' * ((sgOf e'' : ℤ) * (2814 * Y.U)) = (iotaOf e'' * (sgOf e'' : ℤ)) * (2814 * Y.U) by ring, abs_le]
        rcases hιs with h | h <;> rw [h] at k1 k2 ⊢ <;> constructor <;> linarith
      refine conclude h0 rfl hzz ?_ (b1.trans (by linarith)) fun e he => ?_
      · rw [abs_le]; rcases hs e'' with h | h <;> rw [h] <;> constructor <;> linarith
      · have hee := eq_of_near_face Y hd hY (by rw [h0]; ring) h1' he
        subst hee
        rw [sub_self, abs_zero]; linarith

end U0

/-! ## The initial token's own region -/

section InitTok

omit [NeZero d] in
/-- **The region of the initial token towards `e` avoids `U₀`**: its plates stand beyond the seed
(first plane coordinate beyond `5376 U` outwards, or second beyond `2816 U`), its column likewise,
and its entry side, trunk and branches lie at least `16 U` beyond the token along `e`, outside the
closed core of the origin cell. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
theorem init_notMem_fzone (hY : Y.OK) (e : MDir) {w : Site d} (U1 : ∀ i, |Uc hd i w| ≤ 2 * Y.Df - 4)
    (U2 : |w (pl hd 0)| ≤ 5376 * Y.U) (U3 : |w (pl hd 1)| ≤ 2814 * Y.U + 2 * Y.m) (hw : w ∈ fzone Y hd 0 e (initTokF Y hd e)) :
    False := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have h01 : pl hd (0 : Fin 2) ≠ pl hd 1 := pl_ne_pl hd (by decide)
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hι : iotaOf e = 1 ∨ iotaOf e = -1 := by unfold iotaOf; split_ifs <;> simp
  have hp0 : (initTokF Y hd e).pos (pl hd 0) = (sgOf e : ℤ) * (2688 * Y.U) := by simp [initTokF, initPosF]
  have hp1 : (initTokF Y hd e).pos (pl hd 1) = iotaOf e * ((sgOf e : ℤ) * (1407 * Y.U)) := by simp [initTokF, initPosF, h01.symm]
  have hq : plIdx hd (initTokF Y hd e).ax = 0 := plIdx_pl hd 0
  have hoth : oth (0 : Fin 2) = 1 := by decide
  have hd0 : ((dsg e 0 : ℤˣ) : ℤ) = sgOf e := by unfold dsg; by_cases h : e.1 = 0 <;> simp [h]
  have hd1 : ((dsg e 1 : ℤˣ) : ℤ) = iotaOf e * sgOf e := by
    unfold dsg iotaOf; by_cases h : e.1 = 0 <;> simp [h]
  have hUpar : Uc hd e.1 (initTokF Y hd e).pos = (sgOf e : ℤ) * (4095 * Y.U) := by
    unfold Uc; rw [hp0, hp1]; unfold iotaOf
    rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h | h <;> simp [h] <;> ring
  have hS : upar hd (dsg e) (initTokF Y hd e).pos = 4095 * Y.U := by
    rw [← upar_dsg, hUpar]; linear_combination (4095 * Y.U) * hss
  have hcE : cE Y e (initTokF Y hd e) = 8 * Y.U := by
    have hsrc : (initTokF Y hd e).src = some (rev e) := rfl
    unfold cE; rw [hsrc, if_neg]
    intro h; exact rev_ne_self e (Option.some.inj h)
  obtain ⟨hce, -⟩ := ctr_ftgt Y 0 e
  rw [ctr_eq Y 0] at hce; simp only [Pi.zero_apply, zero_mul, zero_add] at hce
  have hctr2 : (sgOf e : ℤ) * Y.ctr (ftgt 0 e) e.1 = 2 * Y.Df := by rw [hce]; linear_combination (2 * Y.Df) * hss
  obtain ⟨-, -, -, -, -, -, f7, f8, -⟩ := (ftAdm_init Y hd hY e).frameS Y hd 0 e
  rw [hctr2] at f7 f8
  have t7 := abs_le.1 f7; have t8 := abs_le.1 f8
  have u1 := abs_le.1 (U1 e.1); have u2 := abs_le.1 U2; have u3 := abs_le.1 U3
  -- the seed bound along the two plane axes, signed
  have b0 : (sgOf e : ℤ) * (w (pl hd 0) - 2 * ((sgOf e : ℤ) * (2688 * Y.U))) ≤ 0 := by
    rcases hs with h | h <;> rw [h] <;> linarith
  have b1 : iotaOf e * (sgOf e : ℤ) * (w (pl hd 1) - 2 * (iotaOf e * ((sgOf e : ℤ) * (1407 * Y.U)))) ≤ 2 * Y.m := by
    rcases hs with h | h <;> rcases hι with h' | h' <;> rw [h, h'] <;> linarith
  obtain ⟨-, hcases⟩ := hw
  simp only [hq, hoth, hd0, hd1, hp0, hp1, hS, hcE] at hcases
  rcases hcases with ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨-, -, -, -, -, a6⟩ | ⟨-, -, -, -, -, a6⟩ | ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · rcases hs with h | h <;> rw [h] at a1 <;> linarith
  · rcases hs with h | h <;> rw [h] at a1 <;> linarith
  · have t1 := abs_le.1 a1
    rcases hs with h | h <;> rw [h] at t1 t7 <;> linarith
  · have t1 := abs_le.1 a1
    rcases hs with h | h <;> rw [h] at t1 t8 <;> linarith

end InitTok

/-! ## The regions avoid `U₀` -/

section Avoid

omit [NeZero d] in
/-- **The region of an admissible attempt not aimed at the origin cell avoids `U₀`**
(`Kit.Good.disjoint_U₀` at the level of regions). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem fzone_avoids_U0F (hY : Y.OK) {a : Site 2} {e : MDir} {τ : TTok d} (hτ : FTAdm hd Y a e τ)
    (hinit : τ.src = some (rev e) → a = 0 ∧ τ = initTokF Y hd e) (h0 : ftgt a e ≠ 0) {z : Sym2 (Site d)} (hz : z ∈ U0F Y hd)
    (hw : dmid z ∈ fzone Y hd a e τ) : False := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hD : Y.Df = 4096 * Y.U := rfl
  have hD0 : 0 < Y.Df := by rw [hD]; positivity
  have hρv : Y.ρv = 4 * Y.U := rfl
  obtain ⟨U1, U2, U3, U4⟩ := dmid_U0F hY hz
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  rcases fzone_classify Y hd a e τ hY hτ hw with hc | ⟨⟨n1, n2, n3⟩, hzt⟩
  · -- the core of a cell other than the origin's
    obtain ⟨i, hi⟩ := exists_ne_of_ne h0
    have h1 := abs_le.1 (hc i); have h2 := abs_le.1 (U1 i)
    rw [ctr_eq] at h1
    have hk : ftgt a e i ≤ -1 ∨ 1 ≤ ftgt a e i := by have : ftgt a e i ≠ 0 := hi; omega
    rcases hk with hk | hk
    · have : ftgt a e i * (2 * Y.Df) ≤ -(2 * Y.Df) := by nlinarith
      linarith
    · have : 2 * Y.Df ≤ ftgt a e i * (2 * Y.Df) := by nlinarith
      linarith
  · obtain ⟨hce, hcl⟩ := ctr_ftgt Y a e
    rw [hce] at n1 n2; rw [hcl] at n3
    by_cases ha : a = 0
    · subst ha
      rw [ctr_eq] at n1 n2; simp only [Pi.zero_apply, zero_mul, zero_add] at n1 n2
      have e2 : (sgOf e : ℤ) * ((sgOf e : ℤ) * (2 * Y.Df)) = 2 * Y.Df := by linear_combination (2 * Y.Df) * hss
      rw [e2] at n1 n2
      have hZ := U4 e (by linarith)
      obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 hτ.src_some
      by_cases hrev : d' = rev e
      · subst hrev
        obtain ⟨-, rfl⟩ := hinit hd'
        exact init_notMem_fzone Y hd hY e U1 U2 U3 hw
      · have hW := Wl_le_abs_zOf_sub Y hrev
        unfold FlatLayout.Wl at hW
        have tZ := abs_le.1 hZ
        rcases hzt with hzt | ⟨hsrc, hzt⟩
        · have hh := abs_le.1 (hτ.height d' hd')
          have t1 := abs_le.1 hzt
          have : |Y.zOf d' - Y.zOf (rev e)| ≤ 15 * Y.U := by rw [abs_le]; constructor <;> linarith
          linarith
        · have hde : d' = e := Option.some.inj (hd'.symm.trans hsrc)
          rw [hde] at hW
          have t1 := abs_le.1 hzt
          have : |Y.zOf e - Y.zOf (rev e)| ≤ 15 * Y.U := by rw [abs_le]; constructor <;> linarith
          linarith
    · -- the entry of an attempt from a cell other than the origin's is outside the origin cell
      obtain ⟨i, hi⟩ := exists_ne_of_ne ha
      rcases fin2_cases e i with hi' | hi'
      · rw [hi'] at hi
        have u := abs_le.1 (U1 e.1)
        rw [ctr_eq] at n1 n2
        have hk : a e.1 ≤ -1 ∨ 1 ≤ a e.1 := by have : a e.1 ≠ 0 := hi; omega
        rcases hk with hk | hk
        · have : a e.1 * (2 * Y.Df) ≤ -(2 * Y.Df) := by nlinarith
          rcases hs with h | h <;> rw [h] at n1 n2 <;> linarith
        · have : 2 * Y.Df ≤ a e.1 * (2 * Y.Df) := by nlinarith
          rcases hs with h | h <;> rw [h] at n1 n2 <;> linarith
      · rw [hi'] at hi
        have u := abs_le.1 (U1 (latDir e true).1)
        have t3 := abs_le.1 n3
        rw [ctr_eq] at t3
        have hk : a (latDir e true).1 ≤ -1 ∨ 1 ≤ a (latDir e true).1 := by have : a (latDir e true).1 ≠ 0 := hi; omega
        rcases hk with hk | hk
        · have : a (latDir e true).1 * (2 * Y.Df) ≤ -(2 * Y.Df) := by nlinarith
          linarith
        · have : 2 * Y.Df ≤ a (latDir e true).1 * (2 * Y.Df) := by nlinarith
          linarith

end Avoid

end BGNd

end Percolation.Literature

end

/-!
# Part 4 (The flat gait, XXXVI): the flat kit is good; percolation in `ℤ^d`, flat regime

We prove the obligations `Kit.Good` of the block kit
`flatKit` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.52), regime
`8 (H + 1) ≤ L + 1`): the initial tokens are admissible and report no provenance (`FlatKitDef`),
zones are statically disjoint and avoid `U₀` (`flat_disjoint_zone`, `flat_disjoint_U₀`, from
`fzone_disjoint` and `fzone_avoids_U0F`, the reported provenance of an admissible token being its
source unless that is the reverse of its direction, `srcDirF_cases`), `U₀` consists of lattice edges
and joins the origin to the open initial seeds, and the dynamic obligations hold
(`flat_complete`, `flat_connect`). Hence `flatKit_good`, and by `Kit.theta_pos`: if bricks are good
with probability at least `1 - 1/(64 R)`, `R = 2¹⁵`, the origin percolates in `ℤ^d` with positive
probability (`theta_pos_flat`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 169–176, Lemma (7.52).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : FlatLayout) (hd : 3 ≤ d) (hY : Y.OK)

/-! ## Static disjointness for the kit -/

omit [NeZero d] in
include hY in
/-- **The reported provenance of an admissible token** with source `d'`, for an attempt along `e`:
`some d'`, unless `d'` is the reverse of `e` (the nominal provenance of the initial tokens). [folklore] -/
theorem srcDirF_cases {a : Site 2} {e d' : MDir} {τ : TTok d} (hτ : FTAdm hd Y a e τ) (hs : τ.src = some d') :
    srcDirF Y hd τ = some d' ∨ d' = rev e := by
  by_cases h : d' = rev e
  · exact Or.inr h
  · left
    exact hτ.srcDirF_eq Y hd hY hs fun h' => h (by rw [h', rev_rev])

/-- **Static disjointness of zones** (`Kit.Good.disjoint_zone`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem flat_disjoint_zone {a a' : Site 2} {e e' : MDir} {τ τ' : TTok d} (hτ : (flatKit Y hd hY).Adm a e τ) (hτ' : (flatKit Y hd hY).Adm a' e' τ')
    (h1 : (a, e) ≠ (a', e')) (h2 : a' ≠ a + stepVec e) (h3 : ¬(a' + stepVec e' = a ∧ (flatKit Y hd hY).srcDir τ = some e')) :
    Disjoint ((flatKit Y hd hY).zone a e τ) ((flatKit Y hd hY).zone a' e' τ') := by
  rw [flatKit_Adm] at hτ hτ'
  rw [flatKit_srcDir] at h3
  rw [flatKit_zone, flatKit_zone, Finset.disjoint_left]
  intro z hz hz'
  have hr := ((mem_fzoneF Y hd a e τ).1 hz).2.2
  have hr' := ((mem_fzoneF Y hd a' e' τ').1 hz').2.2
  refine fzone_disjoint Y hd hY hτ.1 hτ'.1 h1 h2 (fun d' hca hs heq => ?_) hr hr'
  subst heq
  rcases srcDirF_cases Y hd hY hτ.1 hs with h | h
  · exact h3 ⟨hca, h⟩
  · exact h2 (eq_tgtCell_of_rev hca h)

/-- **Zones not aimed at the origin cell avoid `U₀`** (`Kit.Good.disjoint_U₀`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem flat_disjoint_U₀ {a : Site 2} {e : MDir} {τ : TTok d} (hτ : (flatKit Y hd hY).Adm a e τ) (h0 : a + stepVec e ≠ 0) :
    Disjoint ((flatKit Y hd hY).zone a e τ) (flatKit Y hd hY).U₀ := by
  rw [flatKit_Adm] at hτ
  rw [flatKit_zone, flatKit_U0, Finset.disjoint_left]
  intro z hz hz'
  have hr := ((mem_fzoneF Y hd a e τ).1 hz).2.2
  exact fzone_avoids_U0F Y hd hY hτ.1 hτ.2 h0 hz' hr

/-! ## The flat kit is good -/

/-- **The flat kit satisfies the obligations of a good kit.** [cite: GrimmettPercolation1999, §7.3 pp. 169–176] -/
theorem flatKit_good : (flatKit Y hd hY).Good Y.m Y.L Y.H 0 where
  adm_init e := ⟨ftAdm_init Y hd hY e, fun _ => ⟨rfl, rfl⟩⟩
  src_init e := by
    rw [flatKit_srcDir, flatKit_init]
    exact srcDirF_init Y hd hY e
  disjoint_zone hτ hτ' h1 h2 h3 := flat_disjoint_zone Y hd hY hτ hτ' h1 h2 h3
  disjoint_U₀ hτ h0 := flat_disjoint_U₀ Y hd hY hτ h0
  U₀_subset := by rw [flatKit_U0]; exact U0F_subset_edgeSet Y hd
  conn_init ω hω e := by
    rw [flatKit_U0] at hω
    obtain ⟨hseed, hreach⟩ := init_connF Y hd hω e
    exact ⟨hseed, hreach⟩
  complete ω hτ hgood := by
    rw [flatKit_Adm] at hτ
    obtain ⟨f, hf, -⟩ := flat_complete Y hd _ _ _ hY hτ.1 ω hgood
    change (flatKit Y hd hY).gfinish Y.m Y.L Y.H _ _ _ ((flatKit Y hd hY).run Y.m Y.L Y.H _ _ _ FlatLayout.Rmax ω) ≠ none
    rw [hf]; simp
  connect ω f hτ hpre hf e' he' := by
    rw [flatKit_Adm] at hτ
    exact flat_connect Y hd _ _ _ hY hτ.1 ω hpre hf he'

include hd hY in
/-- **Percolation in `ℤ^d`, flat regime.** If the layout is admissible (`m + 1 ≤ L`, `2m + 2 ≤ H`,
`8 (H + 1) ≤ L + 1`) and bricks `B(L, H)` are good (clean rule, seeds `b_k(m)`) with
`P_p`-probability at least `1 - 1/(64 R)`, `R = 2¹⁵`, then `θ(p) > 0` on `ℤ^d`, `d ≥ 3`.
[cite: GrimmettPercolation1999, Lemma (7.52) p. 169, proof pp. 169–176] -/
theorem theta_pos_flat (p : unitInterval) (hp : 0 < (p : ℝ))
    (hν : (FlatLayout.Rmax : ℝ) * (1 - (bondPercolation (zdGraph d) p).real (goodC d Y.m Y.L Y.H)) ≤ 1 / 64) :
    0 < theta (zdGraph d) 0 p := by
  have hH : 1 ≤ Y.H := by have := hY.hH; omega
  have hmL : Y.m < Y.L := by have := hY.hL; omega
  exact (flatKit Y hd hY).theta_pos Y.m Y.L Y.H (flatKit_good Y hd hY) hH hmL p hp (by rw [flatKit_R]; exact hν)

end BGNd

end Percolation.Literature

end
