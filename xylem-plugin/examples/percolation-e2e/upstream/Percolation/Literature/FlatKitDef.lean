import Percolation.Literature.FlatBoundsG
import Percolation.Literature.TallInit
import Percolation.Literature.TallRun3
import Percolation.Literature.TallStatic
import Percolation.Literature.TallZone
import Percolation.Util.Linter

/-!
# The flat gait, XXIII–XXVII

This module gathers 5 consecutive parts of the flat-gait development, in order:
XXIII: the zone, I — the reserved region and the boxes of the plates ·
XXIV: the zone, II — containment of all boxes ·
XXV: the zone, III — the zone as a finite set of lattice edges ·
XXVI: the initial tokens and the initial open set · XXVII: the block kit.
Part 1 follows; the later parts keep their own headers below.

# Part 1 (The flat gait, XXIII): the zone, I — the reserved region and the boxes of the plates

The reserved region of an attempt of the flat gait
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`), in doubled coordinates
and in the diagonal coordinates of the macro-lattice: the boxes of the lead-in, the riser column
(a low part near the token's height, a high part beyond the entry face), the entry side at the layer
of `e`, the trunk tube, the two branch tubes (`fzone`); and the first half of the containment of the
boxes of all plates of an invariant state: the box inequalities in diagonal coordinates
(`box_P`, `box_L`, `box_P_fwd`, `box_sL_B1`, `box_sL_B2`, `box_Z_plane`, `box_Z_vert`) and the boxes of
the lead-in and of the riser (`boxOf_subset_fzone_A`, `boxOf_subset_fzone_R`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174, p. 173 (C).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## The region -/

section Region

variable (Y : FlatLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d)

/-- The entry-side forward margin: none if the token came straight (the riser may be short), `8 U`
otherwise (the riser then climbs at least a layer pitch less the windows). [folklore] -/
def cE : ℤ := if τ.src = some e then 0 else 8 * Y.U

/-- **The reserved region** of the attempt along `(a, e)` from `τ`, in doubled coordinates `w` and the
diagonal coordinates `P = s · Uc_e(w)`, `L = Uc_lat(w)`, `Z = w_z`: idle coordinates within
`2L' + 2U` of `0`, and one of: the boxes of the three plates of the lead-in; the riser column, low
part (near the token's height, up to `8 U` beyond the entry face) or high part (beyond `3 U` past
the entry face, any height between the token's and the nominal one); the entry side at the layer of
`e`; the trunk tube; the two branch tubes. Near the token (forward coordinate below `S + 180 U`)
the column and the entry side keep beyond the token along the token's axis. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def fzone : Set (Site d) :=
  let s : ℤ := (sgOf e : ℤ)
  let q := plIdx hd τ.ax
  let u : ℤ := (friseDir hd Y e τ : ℤ)
  let S2 := 2 * upar hd (dsg e) τ.pos
  let Lt := 2 * Uc hd (latDir e true).1 τ.pos
  let z0 := 2 * τ.pos (ax0 hd)
  let zN2 := 2 * Y.zOf e
  let C := 2 * (s * Y.ctr (ftgt a e) e.1)
  let F := C - 2 * Y.Df
  let Cl := 2 * Y.ctr (ftgt a e) (latDir e true).1
  let ln := 2 * Y.lane (ftgt a e) e
  let t1 := 2 * (s * Y.lane (ftgt a e) (eB1 e) - s * Y.U)
  let t2 := 2 * (s * Y.lane (ftgt a e) (eB2 e) - s * Y.U)
  {w | (∀ j, Idle hd j → |w j| ≤ 2 * Y.Lp + 2 * Y.U) ∧
    ( -- the first plate's box
      (1 ≤ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)) ∧ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)) ≤ 2 * Y.H + 2 ∧
        |w (pl hd (oth q)) - 2 * τ.pos (pl hd (oth q))| ≤ 2 * Y.U ∧ |w (ax0 hd) - z0| ≤ 2 * Y.U) ∨
      -- the second plate's box: `U` on along the other plane axis
      (2 * Y.U + 1 ≤ (dsg e (oth q) : ℤ) * (w (pl hd (oth q)) - 2 * τ.pos (pl hd (oth q))) ∧
        (dsg e (oth q) : ℤ) * (w (pl hd (oth q)) - 2 * τ.pos (pl hd (oth q))) ≤ 2 * Y.U + 2 * Y.H + 2 ∧
        2 * Y.m + 2 - 2 * Y.U ≤ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)) ∧ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)) ≤ 2 * Y.U + 2 * Y.H ∧
        -(2 * Y.U) ≤ u * (w (ax0 hd) - z0) ∧ u * (w (ax0 hd) - z0) ≤ 2 * Y.U + 2 * Y.Lp) ∨
      -- the third plate's box: `U + t` on along the token's axis
      (2 * Y.U + 2 * Y.m + 3 ≤ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)) ∧ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)) ≤ 2 * Y.U + 4 * Y.H + 2 ∧
        2 * Y.m + 2 ≤ (dsg e (oth q) : ℤ) * (w (pl hd (oth q)) - 2 * τ.pos (pl hd (oth q))) ∧
        (dsg e (oth q) : ℤ) * (w (pl hd (oth q)) - 2 * τ.pos (pl hd (oth q))) ≤ 4 * Y.U + 2 * Y.H ∧
        -(2 * Y.U) ≤ u * (w (ax0 hd) - z0) ∧ u * (w (ax0 hd) - z0) ≤ 2 * Y.U + 4 * Y.Lp) ∨
      -- the riser column, low part
      (2 * Y.m + 1 ≤ u * (w (ax0 hd) - z0) ∧ u * (w (ax0 hd) - z0) ≤ 14 * Y.U + 10 * Y.H ∧
        S2 - 4 * Y.U ≤ s * Uc hd e.1 w ∧ s * Uc hd e.1 w ≤ F + 8 * Y.U ∧ |Uc hd (latDir e true).1 w - Lt| ≤ 222 * Y.U ∧
        1 ≤ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q))) ∨
      -- the riser column, high part
      (2 * Y.m + 1 ≤ u * (w (ax0 hd) - z0) ∧ u * (w (ax0 hd) - zN2) ≤ 8 * Y.U + 2 * Y.H ∧
        F + 3 * Y.U ≤ s * Uc hd e.1 w ∧ s * Uc hd e.1 w ≤ S2 + 440 * Y.U ∧ |Uc hd (latDir e true).1 w - Lt| ≤ 222 * Y.U ∧
        1 ≤ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q))) ∨
      -- the entry side
      (S2 + 2 * cE Y e τ ≤ s * Uc hd e.1 w ∧ s * Uc hd e.1 w ≤ S2 + 950 * Y.U ∧
        2 * min (Uc hd (latDir e true).1 τ.pos - 126 * Y.U) (Y.lane (ftgt a e) e - 22 * Y.U) - 4 * Y.U ≤ Uc hd (latDir e true).1 w ∧
        Uc hd (latDir e true).1 w ≤ 2 * max (Uc hd (latDir e true).1 τ.pos + 126 * Y.U) (Y.lane (ftgt a e) e + 22 * Y.U) + 4 * Y.U ∧
        |w (ax0 hd) - zN2| ≤ 8 * Y.U + 2 * Y.H ∧
        (s * Uc hd e.1 w ≤ S2 + 180 * Y.U → 1 ≤ (dsg e q : ℤ) * (w (pl hd q) - 2 * τ.pos (pl hd q)))) ∨
      -- the trunk tube
      (S2 + 188 * Y.U ≤ s * Uc hd e.1 w ∧ s * Uc hd e.1 w ≤ C + 2 * Y.Df - 2 * Y.U + 4 * Y.H + 2 ∧
        |Uc hd (latDir e true).1 w - ln| ≤ 1076 * Y.U ∧ |w (ax0 hd) - zN2| ≤ 8 * Y.U + 2 * Y.H) ∨
      -- the first branch tube
      (|s * Uc hd e.1 w - t1| ≤ 790 * Y.U ∧ s * Cl - 2 * Y.Df + 2 ≤ s * Uc hd (latDir e true).1 w ∧
        s * Uc hd (latDir e true).1 w ≤ s * ln + 1076 * Y.U ∧ |w (ax0 hd) - zN2| ≤ 8 * Y.U + 2 * Y.H) ∨
      -- the second branch tube
      (|s * Uc hd e.1 w - t2| ≤ 474 * Y.U ∧ s * ln - 1076 * Y.U ≤ s * Uc hd (latDir e true).1 w ∧
        s * Uc hd (latDir e true).1 w ≤ s * Cl + 2 * Y.Df - 2 ∧ |w (ax0 hd) - zN2| ≤ 8 * Y.U + 2 * Y.H))}

end Region

/-! ## Boxes in diagonal coordinates -/

section Box

variable {hd : 3 ≤ d} {Y : FlatLayout} {e : MDir} {β : BrickPos d} {w : Site d}

omit [NeZero d] in
/-- **A plane coordinate of a point of a box** is within `2U` of twice the base's (the axis side being
within `2H + 2 ≤ 2U`). [folklore] -/
theorem box_plane (hY : Y.OK) (hw : w ∈ boxOf Y.L Y.H β) (i : Fin 2) : |w (pl hd i) - 2 * β.b (pl hd i)| ≤ 2 * Y.U := by
  obtain ⟨hU, hUe, -, -, -, hHU, -⟩ := hY.facts
  by_cases hi : pl hd i = β.a
  · obtain ⟨h1, h2⟩ := box_axis hw
    rw [← hi] at h1 h2
    rw [abs_le]
    rcases Int.units_eq_one_or β.s with h | h <;> rw [h] at h1 h2 <;> simp only [Units.val_one, Units.val_neg, one_mul, neg_mul] at h1 h2 <;>
      constructor <;> linarith
  · have := box_trans hw hi; rw [abs_le]; constructor <;> linarith [this.1, this.2]

omit [NeZero d] in
/-- The diagonal coordinates are linear. [folklore] -/
theorem Uc_sub_two (hd : 3 ≤ d) (i : Fin 2) (w b : Site d) :
    Uc hd i w - 2 * Uc hd i b = (w (pl hd 0) - 2 * b (pl hd 0)) + (if i = 0 then 1 else -1 : ℤ) * (w (pl hd 1) - 2 * b (pl hd 1)) := by
  unfold Uc; split_ifs <;> ring

omit [NeZero d] in
/-- **The forward diagonal coordinate of a point of a box** is within `4U` of twice the base's. [folklore] -/
theorem box_P (hY : Y.OK) (hw : w ∈ boxOf Y.L Y.H β) :
    |(sgOf e : ℤ) * Uc hd e.1 w - 2 * upar hd (dsg e) β.b| ≤ 4 * Y.U := by
  have h0 := abs_le.1 (box_plane (hd := hd) hY hw 0)
  have h1 := abs_le.1 (box_plane (hd := hd) hY hw 1)
  rw [← upar_dsg, ← mul_assoc, mul_comm (2 : ℤ), mul_assoc, ← mul_sub, Uc_sub_two]
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  rw [abs_le]
  rcases hs with h | h <;> rw [h] <;> split_ifs <;> constructor <;> linarith

omit [NeZero d] in
/-- **The lateral diagonal coordinate of a point of a box** is within `4U` of twice the base's. [folklore] -/
theorem box_L (hY : Y.OK) (hw : w ∈ boxOf Y.L Y.H β) :
    |Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 β.b| ≤ 4 * Y.U := by
  have h0 := abs_le.1 (box_plane (hd := hd) hY hw 0)
  have h1 := abs_le.1 (box_plane (hd := hd) hY hw 1)
  rw [Uc_sub_two, abs_le]
  split_ifs <;> constructor <;> linarith

omit [NeZero d] in
/-- **A plate read forwards along its axis** (sign `dsg e q` on axis `pl q`) reaches at most
`2U + 2H + 2` beyond twice its base in the forward diagonal coordinate; read backwards, at most `2U`. [folklore] -/
theorem box_P_fwd (hY : Y.OK) (hw : w ∈ boxOf Y.L Y.H β) {q : Fin 2} (ha : β.a = pl hd q) :
    (β.s = dsg e q → (sgOf e : ℤ) * Uc hd e.1 w ≤ 2 * upar hd (dsg e) β.b + 2 * Y.U + 2 * Y.H + 2) ∧
      (β.s = -dsg e q → (sgOf e : ℤ) * Uc hd e.1 w ≤ 2 * upar hd (dsg e) β.b + 2 * Y.U) := by
  obtain ⟨h1, h2⟩ := box_axis hw
  rw [ha] at h1 h2
  have ht := abs_le.1 (box_plane (hd := hd) hY hw (oth q))
  -- `s · Uc_e(w) - 2 upar = σ_q (w_q - 2b_q) + σ_{q'} (w_{q'} - 2b_{q'})`
  have key : (sgOf e : ℤ) * Uc hd e.1 w - 2 * upar hd (dsg e) β.b =
      (dsg e q : ℤ) * (w (pl hd q) - 2 * β.b (pl hd q)) + (dsg e (oth q) : ℤ) * (w (pl hd (oth q)) - 2 * β.b (pl hd (oth q))) := by
    rw [← upar_dsg, ← mul_assoc, mul_comm (2 : ℤ), mul_assoc, ← mul_sub, Uc_sub_two]
    unfold dsg
    rcases Fin.exists_fin_two.1 ⟨q, rfl⟩ with hq | hq <;> rw [hq] <;>
      simp only [show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] <;>
      rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with he | he <;> simp [he] <;> ring
  have hσ : ((dsg e (oth q) : ℤ)) = 1 ∨ ((dsg e (oth q) : ℤ)) = -1 := by
    rcases Int.units_eq_one_or (dsg e (oth q)) with h' | h' <;> simp [h']
  have htr : (dsg e (oth q) : ℤ) * (w (pl hd (oth q)) - 2 * β.b (pl hd (oth q))) ≤ 2 * Y.U := by
    rcases hσ with h | h <;> rw [h] <;> linarith [ht.1, ht.2]
  constructor
  · intro hs; rw [hs] at h1 h2; linarith [key]
  · intro hs; rw [hs] at h1 h2; simp only [Units.val_neg, neg_mul] at h1 h2; linarith [key]

omit [NeZero d] in
/-- **A plate of the first branch** (axis `0` with sign `-dsg e 0`, or axis `1` with sign `dsg e 1`)
reaches at most `2U + 2H + 2` below twice its base in the lateral diagonal coordinate read along `e`. [folklore] -/
theorem box_sL_B1 (hY : Y.OK) (hw : w ∈ boxOf Y.L Y.H β) (ha : (β.a = pl hd 0 ∧ β.s = -dsg e 0) ∨ (β.a = pl hd 1 ∧ β.s = dsg e 1)) :
    2 * vperp hd (dsg e) β.b - 2 * Y.U - 2 * Y.H - 2 ≤ (sgOf e : ℤ) * Uc hd (latDir e true).1 w := by
  have key : (sgOf e : ℤ) * Uc hd (latDir e true).1 w - 2 * vperp hd (dsg e) β.b =
      (dsg e 0 : ℤ) * (w (pl hd 0) - 2 * β.b (pl hd 0)) - (dsg e 1 : ℤ) * (w (pl hd 1) - 2 * β.b (pl hd 1)) := by
    have hlin : (sgOf e : ℤ) * Uc hd (latDir e true).1 w = vperp hd (dsg e) w := by
      rw [Uc_lat_eq_vperp, ← mul_assoc]
      have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
      rw [hss, one_mul]
    rw [hlin]; unfold vperp ox; ring
  have h0 := abs_le.1 (box_plane (hd := hd) hY hw 0)
  have h1 := abs_le.1 (box_plane (hd := hd) hY hw 1)
  obtain ⟨ha1, ha2⟩ := box_axis hw
  have hσ0 : ((dsg e 0 : ℤ)) = 1 ∨ ((dsg e 0 : ℤ)) = -1 := by rcases Int.units_eq_one_or (dsg e 0) with h' | h' <;> simp [h']
  have hσ1 : ((dsg e 1 : ℤ)) = 1 ∨ ((dsg e 1 : ℤ)) = -1 := by rcases Int.units_eq_one_or (dsg e 1) with h' | h' <;> simp [h']
  rcases ha with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha, hs] at ha1 ha2
  · simp only [Units.val_neg, neg_mul] at ha1 ha2
    rcases hσ1 with h | h <;> rw [h] at key <;> linarith
  · rcases hσ0 with h | h <;> rw [h] at key <;> linarith

omit [NeZero d] in
/-- **A plate of the second branch** (axis `1` with sign `-dsg e 1`, or axis `0` with sign `dsg e 0`)
reaches at most `2U + 2H + 2` above twice its base in the lateral diagonal coordinate read along `e`. [folklore] -/
theorem box_sL_B2 (hY : Y.OK) (hw : w ∈ boxOf Y.L Y.H β) (ha : (β.a = pl hd 1 ∧ β.s = -dsg e 1) ∨ (β.a = pl hd 0 ∧ β.s = dsg e 0)) :
    (sgOf e : ℤ) * Uc hd (latDir e true).1 w ≤ 2 * vperp hd (dsg e) β.b + 2 * Y.U + 2 * Y.H + 2 := by
  have key : (sgOf e : ℤ) * Uc hd (latDir e true).1 w - 2 * vperp hd (dsg e) β.b =
      (dsg e 0 : ℤ) * (w (pl hd 0) - 2 * β.b (pl hd 0)) - (dsg e 1 : ℤ) * (w (pl hd 1) - 2 * β.b (pl hd 1)) := by
    have hlin : (sgOf e : ℤ) * Uc hd (latDir e true).1 w = vperp hd (dsg e) w := by
      rw [Uc_lat_eq_vperp, ← mul_assoc]
      have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
      rw [hss, one_mul]
    rw [hlin]; unfold vperp ox; ring
  have h0 := abs_le.1 (box_plane (hd := hd) hY hw 0)
  have h1 := abs_le.1 (box_plane (hd := hd) hY hw 1)
  obtain ⟨ha1, ha2⟩ := box_axis hw
  have hσ0 : ((dsg e 0 : ℤ)) = 1 ∨ ((dsg e 0 : ℤ)) = -1 := by rcases Int.units_eq_one_or (dsg e 0) with h' | h' <;> simp [h']
  have hσ1 : ((dsg e 1 : ℤ)) = 1 ∨ ((dsg e 1 : ℤ)) = -1 := by rcases Int.units_eq_one_or (dsg e 1) with h' | h' <;> simp [h']
  rcases ha with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha, hs] at ha1 ha2
  · simp only [Units.val_neg, neg_mul] at ha1 ha2
    rcases hσ0 with h | h <;> rw [h] at key <;> linarith
  · rcases hσ1 with h | h <;> rw [h] at key <;> linarith

omit [NeZero d] in
/-- The height of a point of the box of a plane plate. [folklore] -/
theorem box_Z_plane (hY : Y.OK) (hw : w ∈ boxOf Y.L Y.H β) (ha : β.a ≠ ax0 hd) : |w (ax0 hd) - 2 * β.b (ax0 hd)| ≤ 2 * Y.U := by
  obtain ⟨hU, hUe, -⟩ := hY.facts
  have := box_trans hw (Ne.symm ha); rw [abs_le]; constructor <;> linarith [this.1, this.2]

omit [NeZero d] in
/-- The height of a point of the box of a horizontal plate. [folklore] -/
theorem box_Z_vert (hw : w ∈ boxOf Y.L Y.H β) (ha : β.a = ax0 hd) :
    1 ≤ (β.s : ℤ) * (w (ax0 hd) - 2 * β.b (ax0 hd)) ∧ (β.s : ℤ) * (w (ax0 hd) - 2 * β.b (ax0 hd)) ≤ 2 * Y.H + 2 := by
  have := box_axis hw; rw [ha] at this; exact this

omit [NeZero d] in
/-- The idle coordinates of a point of a box, from the invariant's `|b_j| ≤ L'`. [folklore] -/
theorem box_idle (hY : Y.OK) (hw : w ∈ boxOf Y.L Y.H β) (hb : ∀ j, Idle hd j → |β.b j| ≤ Y.Lp) (hβ : β.a = ax0 hd ∨ ∃ q, β.a = pl hd q) :
    ∀ j, Idle hd j → |w j| ≤ 2 * Y.Lp + 2 * Y.U := by
  obtain ⟨hU, hUe, -⟩ := hY.facts
  intro j hj
  have hja : j ≠ β.a := by
    rcases hβ with h | ⟨q, h⟩
    · rw [h]; exact hj.2.2
    · rw [h]; rcases Fin.exists_fin_two.1 ⟨q, rfl⟩ with hq | hq <;> rw [hq]
      · exact hj.1
      · exact hj.2.1
  have h1 := abs_le.1 (hb j hj)
  have h2 := box_trans hw hja
  rw [abs_le]; constructor <;> linarith [h2.1, h2.2]

end Box

/-! ## The riser's forward advance by landings -/

section RiserExtra

variable {hd : 3 ≤ d} {Y : FlatLayout} {σ : Fin 2 → ℤˣ} {u : ℤˣ} {q₀ : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- **Each landing advances the forward coordinate by at least `U`**: plate `k` of a riser is at
least `⌊(k+1)/2⌋ U` beyond the start. [folklore] -/
theorem Riser.upar_lb (h : Riser hd Y σ u q₀ s l) {k : ℕ} (hk : k < l.length) :
    upar hd σ s.b + (((k + 1) / 2 : ℕ) : ℤ) * Y.U ≤ upar hd σ (legOf l k).b := by
  induction k with
  | zero =>
    have l0 := (h.plane hk 0).1; have l1 := (h.plane hk 1).1
    unfold upar; simp; linarith
  | succ k ih =>
    have ih' := ih (by omega)
    have m0 := (h.plane hk 0).2 (by omega); have m1 := (h.plane hk 1).2 (by omega)
    simp only [Nat.add_sub_cancel] at m0 m1
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · -- `k + 1 = 2j + 1`: a landing, `+U` along its axis
      have hf := h.land_face (j := j) (by omega)
      rw [show 2 * j = j + j by ring] at hf
      have : ((j + j + 1 + 1) / 2 : ℕ) = (j + j + 1) / 2 + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      unfold upar at ih' ⊢
      rcases Fin.exists_fin_two.1 ⟨qAt q₀ (j + 1), rfl⟩ with hq | hq <;> rw [hq] at hf <;> linarith
    · have : ((2 * j + 1 + 1 + 1) / 2 : ℕ) = (2 * j + 1 + 1) / 2 := by omega
      rw [this]
      unfold upar at ih' ⊢; linarith

end RiserExtra

/-! ## Containment: the first plate and the riser -/

section ContainAR

variable {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

omit [NeZero d] in
/-- The token's axis is the plane axis of its index. [folklore] -/
theorem FTAdm.ax_eq (hτ : FTAdm hd Y a e τ) : τ.ax = pl hd (plIdx hd τ.ax) := by
  rcases hτ.ax_plane with h | h <;> rw [h, plIdx_pl]

/-- **The boxes of the plates of the lead-in lie in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_fzone_A (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {r : BrickRec d} (hr : r ∈ st.segs 0) :
    boxOf Y.L Y.H r.1 ⊆ fzone Y hd a e τ := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hS : SegOK hd Y e τ (eJOf hd Y a e τ st) 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hS
  obtain ⟨hD, hfirst, hlen3⟩ := hS (List.ne_nil_of_mem hr)
  have hfp : (firstPlate hd e τ).b = τ.pos := rfl
  have hfa : (firstPlate hd e τ).a = pl hd (plIdx hd τ.ax) := by change τ.ax = _; exact hτ.ax_eq
  have hfs : (firstPlate hd e τ).s = dsg e (plIdx hd τ.ax) := rfl
  have hq1 : qAt (plIdx hd τ.ax) 1 = oth (plIdx hd τ.ax) := by rw [show qAt (plIdx hd τ.ax) 1 = qAt (plIdx hd τ.ax) (0 + 1) from rfl, qAt_succ, qAt_zero]
  have hq2 : qAt (plIdx hd τ.ax) 2 = plIdx hd τ.ax := by rw [show qAt (plIdx hd τ.ax) 2 = qAt (plIdx hd τ.ax) (0 + 2) from rfl, qAt_add_two, qAt_zero]
  have hidle : ∀ k, (hk : k < (st.segs 0).length) → ∀ j, Idle hd j → |(legOf (st.segs 0) k).b j| ≤ Y.Lp :=
    fun k hk => hD.idle_le (by rw [hfirst]; exact fun i hi => hτ.idle i hi) hk
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  intro w hw
  rw [← hkr] at hw
  obtain ⟨hax, hsg⟩ := hD.axis_sign hk
  have hid := box_idle hY hw (hidle k hk) (Or.inr ⟨_, hax⟩)
  refine ⟨hid, ?_⟩
  obtain ⟨h1, h2⟩ := box_axis hw
  rw [hax, hsg] at h1 h2
  have hk3 : k < 3 := by omega
  interval_cases k
  · -- the first plate
    left
    rw [qAt_zero] at h1 h2 hax
    have ht := box_trans hw (i := pl hd (oth (plIdx hd τ.ax))) (by rw [hax]; exact pl_ne_pl hd (oth_ne _))
    have hz := box_trans hw (i := ax0 hd) (by rw [hax]; exact (pl_ne_ax0 hd _).symm)
    rw [hfirst, hfp] at h1 h2 ht hz
    exact ⟨h1, h2, abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩, abs_le.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
  · -- the second plate: the hop through the other plane face
    right; left
    rw [hq1] at h1 h2 hax
    obtain ⟨f1, d1, d1'⟩ := hD.step (k := 0) (by omega)
    simp only [show (0 : ℕ) + 1 = 1 from rfl, hq1, qAt_zero, hfirst, hfp] at f1 d1 d1'
    have ht := box_trans hw (i := pl hd (plIdx hd τ.ax)) (by rw [hax]; exact pl_ne_pl hd (oth_ne _).symm)
    have hzb := box_trans hw (i := ax0 hd) (by rw [hax]; exact (pl_ne_ax0 hd _).symm)
    have hz := hD.height_dir (u := friseDir hd Y e τ) rfl (k := 0) (k' := 1) (by omega) (by omega)
    rw [hfirst, hfp] at hz
    have hσ : ((dsg e (plIdx hd τ.ax) : ℤ)) = 1 ∨ ((dsg e (plIdx hd τ.ax) : ℤ)) = -1 := by
      rcases Int.units_eq_one_or (dsg e (plIdx hd τ.ax)) with h' | h' <;> simp [h']
    have hu : (friseDir hd Y e τ : ℤ) = 1 ∨ (friseDir hd Y e τ : ℤ) = -1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [h']
    unfold ox at f1 d1 d1'
    refine ⟨by linarith [f1], by linarith [f1], ?_, ?_, ?_, ?_⟩
    · rcases hσ with h | h <;> rw [h] at d1 d1' ⊢ <;> linarith [ht.1, ht.2]
    · rcases hσ with h | h <;> rw [h] at d1 d1' ⊢ <;> linarith [ht.1, ht.2]
    · push_cast at hz; rcases hu with h | h <;> rw [h] at hz ⊢ <;> linarith [hzb.1, hzb.2, hz.1, hz.2]
    · push_cast at hz; rcases hu with h | h <;> rw [h] at hz ⊢ <;> linarith [hzb.1, hzb.2, hz.1, hz.2]
  · -- the third plate: the hop back through the token's axis face
    right; right; left
    rw [hq2] at h1 h2 hax
    obtain ⟨f1, d1, d1'⟩ := hD.step (k := 0) (by omega)
    obtain ⟨f2, d2, d2'⟩ := hD.step (k := 1) (by omega)
    simp only [show (0 : ℕ) + 1 = 1 from rfl, hq1, qAt_zero, hfirst, hfp] at f1 d1 d1'
    simp only [show (1 : ℕ) + 1 = 2 from rfl, hq2, hq1] at f2 d2 d2'
    have ht := box_trans hw (i := pl hd (oth (plIdx hd τ.ax))) (by rw [hax]; exact pl_ne_pl hd (oth_ne _))
    have hzb := box_trans hw (i := ax0 hd) (by rw [hax]; exact (pl_ne_ax0 hd _).symm)
    have hz := hD.height_dir (u := friseDir hd Y e τ) rfl (k := 0) (k' := 2) (by omega) (by omega)
    rw [hfirst, hfp] at hz
    have hσ : ((dsg e (oth (plIdx hd τ.ax)) : ℤ)) = 1 ∨ ((dsg e (oth (plIdx hd τ.ax)) : ℤ)) = -1 := by
      rcases Int.units_eq_one_or (dsg e (oth (plIdx hd τ.ax))) with h' | h' <;> simp [h']
    have hu : (friseDir hd Y e τ : ℤ) = 1 ∨ (friseDir hd Y e τ : ℤ) = -1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [h']
    unfold ox at f1 d1 d1' f2 d2 d2'
    refine ⟨by nlinarith [f2, d1, h1], by nlinarith [f2, d1', h2], ?_, ?_, ?_, ?_⟩
    · rcases hσ with h | h <;> rw [h] at f1 d2 d2' ⊢ <;> linarith [ht.1, ht.2]
    · rcases hσ with h | h <;> rw [h] at f1 d2 d2' ⊢ <;> linarith [ht.1, ht.2]
    · push_cast at hz; rcases hu with h | h <;> rw [h] at hz ⊢ <;> linarith [hzb.1, hzb.2, hz.1, hz.2]
    · push_cast at hz; rcases hu with h | h <;> rw [h] at hz ⊢ <;> linarith [hzb.1, hzb.2, hz.1, hz.2]

/-- **The box of a plate of the riser lies in the region** (low or high part of the column). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_fzone_R (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {r : BrickRec d} (hr : r ∈ st.segs 1) :
    boxOf Y.L Y.H r.1 ⊆ fzone Y hd a e τ := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨hSlo, hShi, -⟩ := hτ.windows
  have h1 : st.segs 1 ≠ [] := List.ne_nil_of_mem hr
  have hR := hI.riser h1
  obtain ⟨hsa, hss, hs0, hs1, hsox, hsup, -, hsidle⟩ := hI.rstart_facts hY hτ h1
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  have hlen := hI.riser_len_le hY hτ
  obtain ⟨hwlo, hwhi, hwlat, hwox⟩ := hI.win_riser hY hτ hk
  obtain ⟨hz1, hz2⟩ := hI.riser_z hY hτ hk
  have habs := friseDir_mul_eq_abs hd Y e τ
  have hub := hR.upar_lb hk
  have hidle : ∀ j, Idle hd j → |(legOf (st.segs 1) k).b j| ≤ Y.Lp := hR.idle_le hsidle hk
  set u : ℤ := (friseDir hd Y e τ : ℤ) with hu
  have huu : u * u = 1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [hu, h']
  intro w hw
  rw [← hkr] at hw
  have hP := abs_le.1 (box_P (hd := hd) (e := e) hY hw)
  have hL := abs_le.1 (box_L (hd := hd) (e := e) hY hw)
  have hlat := abs_le.1 hwlat
  have hkc : (k : ℤ) + 1 ≤ 106 := by have := Nat.cast_le (α := ℤ).2 (show k + 1 ≤ 106 by omega); push_cast at this; exact this
  have hs1' : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  -- the lateral window
  have hLat : |Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 τ.pos| ≤ 222 * Y.U := by
    have : |Uc hd (latDir e true).1 (legOf (st.segs 1) k).b - Uc hd (latDir e true).1 τ.pos| ≤ 106 * Y.U + Y.H := by
      rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1', one_mul]
      calc _ ≤ ((k : ℤ) + 1) * Y.U + Y.H := hwlat
        _ ≤ 106 * Y.U + Y.H := by linarith [mul_le_mul_of_nonneg_right hkc hU.le]
    have h' := abs_le.1 this
    rw [abs_le]; constructor <;> linarith
  -- beyond the token along the token's axis
  have hq : 1 ≤ (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) := by
    have hb := abs_le.1 (box_plane (hd := hd) hY hw (plIdx hd τ.ax))
    have hx := hwox (plIdx hd τ.ax)
    unfold ox at hx
    have hσ : ((dsg e (plIdx hd τ.ax) : ℤ)) = 1 ∨ ((dsg e (plIdx hd τ.ax) : ℤ)) = -1 := by
      rcases Int.units_eq_one_or (dsg e (plIdx hd τ.ax)) with h' | h' <;> simp [h']
    rcases hσ with h | h <;> rw [h] at hx ⊢ <;> linarith [hb.1, hb.2]
  -- heights: parity of `k`
  have hax : ∀ j, Idle hd j → |w j| ≤ 2 * Y.Lp + 2 * Y.U := by
    refine box_idle hY hw hidle ?_
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ((hR.axis_sign hk).1 (by omega)).1
    · exact Or.inr ⟨_, ((hR.axis_sign hk).2 (by omega)).1⟩
  refine ⟨hax, ?_⟩
  -- the height of the box read along `u`, relative to the token and to the plate
  have hZlo : 2 * Y.m + 1 ≤ u * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ∧
      u * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ≤ 2 * (u * ((legOf (st.segs 1) k).b (ax0 hd) - τ.pos (ax0 hd))) + 2 * Y.U ∧
      u * (w (ax0 hd) - 2 * (legOf (st.segs 1) k).b (ax0 hd)) ≤ 2 * Y.U := by
    have e0 : u * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) = u * (w (ax0 hd) - 2 * (legOf (st.segs 1) k).b (ax0 hd)) +
        2 * (u * ((legOf (st.segs 1) k).b (ax0 hd) - τ.pos (ax0 hd))) := by ring
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- vertical plate: axis `z`, sign `u`
      obtain ⟨ha, hs⟩ := (hR.axis_sign hk).1 (by omega)
      obtain ⟨b1, b2⟩ := box_Z_vert hw ha
      rw [hs, ← hu] at b1 b2
      refine ⟨by linarith, by linarith, by linarith⟩
    · -- landing: `z` transverse; the landing is `m + 1` above the vertical plate
      obtain ⟨ha, -⟩ := (hR.axis_sign hk).2 (by omega)
      have bz := abs_le.1 (box_Z_plane hY hw (by rw [ha]; exact pl_ne_ax0 hd _))
      have hv := (hR.uz.2 j (by omega)).1
      obtain ⟨hz1', -⟩ := hI.riser_z hY hτ (k := 2 * j) (by omega)
      rw [← hu] at hv hz1'
      rw [show 2 * j + 1 = k by omega] at hv
      have hu1 : u = 1 ∨ u = -1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [hu, h']
      rcases hu1 with h | h <;> rw [h] at hv hz1' hz1 e0 ⊢ <;> refine ⟨by linarith, by linarith, by linarith⟩
  -- split low / high by the forward coordinate
  by_cases hhi : 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) - 2 * Y.Df + 3 * Y.U ≤ (sgOf e : ℤ) * Uc hd e.1 w
  · -- high part
    right; right; right; right; left
    have hkU := mul_le_mul_of_nonneg_right hkc hU.le
    refine ⟨hZlo.1, ?_, hhi, by linarith [hP.2, hwhi], hLat, hq⟩
    -- `u (z_k - zN) ≤ U + H + 2L' - 1`
    have hzN : u * ((legOf (st.segs 1) k).b (ax0 hd) - zN Y e) ≤ Y.U + Y.H + 2 * Y.Lp - 1 := by
      have := hz2
      have e1 : u * ((legOf (st.segs 1) k).b (ax0 hd) - zN Y e) = u * ((legOf (st.segs 1) k).b (ax0 hd) - τ.pos (ax0 hd)) - u * (zN Y e - τ.pos (ax0 hd)) := by ring
      rw [e1, habs]; linarith
    have e2 : u * (w (ax0 hd) - 2 * Y.zOf e) = u * (w (ax0 hd) - 2 * (legOf (st.segs 1) k).b (ax0 hd)) + 2 * (u * ((legOf (st.segs 1) k).b (ax0 hd) - zN Y e)) := by
      unfold zN; ring
    rw [e2]; linarith [hZlo.2.2]
  · -- low part: few landings, so the height is near the token's
    push Not at hhi
    right; right; right; left
    refine ⟨hZlo.1, ?_, by linarith [hP.1, hwlo], by linarith, hLat, hq⟩
    -- `upar(b) < S + 5.5 U`, the start is `≥ S + 2U + 2m + 2`, so `⌊(k+1)/2⌋ ≤ 3`, `k ≤ 6`
    have hsup' : upar hd (dsg e) τ.pos + 2 * Y.U + 2 * Y.m + 2 ≤ upar hd (dsg e) (rstart hd e τ (st.segs 0)).b := by
      have := hsox 0; have := hsox 1; unfold upar; linarith
    have hk6 : k ≤ 6 := by
      by_contra h'
      have h4 : (4 : ℤ) ≤ (((k + 1) / 2 : ℕ) : ℤ) := by exact_mod_cast (show 4 ≤ (k + 1) / 2 by omega)
      have h4U : 4 * Y.U ≤ (((k + 1) / 2 : ℕ) : ℤ) * Y.U := mul_le_mul_of_nonneg_right h4 hU.le
      linarith [hub, hP.1, hSlo, hhi]
    -- `u (z_k - z(start)) ≤ 4 (U + H - m - 1)`
    have hzk : u * ((legOf (st.segs 1) k).b (ax0 hd) - (rstart hd e τ (st.segs 0)).b (ax0 hd)) ≤ 4 * (Y.U + Y.H - Y.m - 1) := by
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hv := hR.uz.1 j (by omega)
        rw [← hu] at hv
        rw [show j + j = 2 * j by ring] at hj
        rw [hj]
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simp only [Riser.prev, if_true] at hv; linarith [hv, hHU, hmH, hm0]
        · have hprev : Riser.prev (rstart hd e τ (st.segs 0)) (st.segs 1) j = legOf (st.segs 1) (2 * (j - 1) + 1) := by
            unfold Riser.prev; rw [if_neg (by omega)]; congr 1; omega
          rw [hprev] at hv
          have hl := (hR.level.1 (j - 1) (by omega)).2
          rw [← hu] at hl
          have hj5 : ((j - 1 : ℕ) : ℤ) + 1 ≤ 3 := by
            have := Nat.cast_le (α := ℤ).2 (show j - 1 + 1 ≤ 3 by omega); push_cast [Nat.cast_sub (show 1 ≤ j by omega)] at this ⊢; linarith
          have hδ : 0 ≤ Y.U + Y.H - Y.m - 1 := by linarith
          have hprod := mul_le_mul_of_nonneg_right hj5 hδ
          linarith [hv, hl]
      · have hl := (hR.level.1 j (by omega)).2
        rw [← hu, show 2 * j + 1 = k by omega] at hl
        have hj5 : (j : ℤ) + 1 ≤ 4 := by have := Nat.cast_le (α := ℤ).2 (show j + 1 ≤ 4 by omega); push_cast at this; exact this
        have hδ : 0 ≤ Y.U + Y.H - Y.m - 1 := by linarith
        have hprod := mul_le_mul_of_nonneg_right hj5 hδ
        linarith [hl]
    linarith [hZlo.2.1]

end ContainAR

end BGNd

end Percolation.Literature

end

/-!
# Part 2 (The flat gait, XXIV): the zone, II — containment of all boxes

The second half of the containment of the boxes of the
plates of an invariant state of the flat gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp.
171–174, case `H < L`) in the reserved region: plates after the riser have plane axes
(`FlatInv.plane_axis`); when the token did not come straight the riser is long, so the entry side is
at least `12 U` beyond the token (`FlatInv.entry_far`); the entry side, the trunk with the forks,
and the branches (`boxOf_subset_fzone_E`, `boxOf_subset_fzone_T`, `boxOf_subset_fzone_B`); all
plates (`boxOf_subset_fzone`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174, p. 173 (C).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## Plates after the riser are plane plates; a long riser when the token did not come straight -/

/-- **Every plate after the riser has a plane axis.** [folklore] -/
theorem FlatInv.plane_axis (hI : FlatInv hd Y a e τ st) (k : Fin 13) (hk2 : 2 ≤ k.val) : ∀ r ∈ st.segs k, ∃ q, r.1.a = pl hd q := by
  refine hI.propagate (P := fun β => ∃ q, β.a = pl hd q) (fun hT _ k hk => ?_) (fun hD _ _ k hk => ⟨_, (hD.axis_sign hk).1⟩) ?_ k hk2
  · have hlen := hT.len
    have hk' : k < 2 := by omega
    interval_cases k
    · exact ⟨_, (hT.h0 hk).axis⟩
    · exact ⟨_, (hT.h1 hk).axis⟩
  · intro hc s₀ hs₀
    obtain ⟨tl, hl⟩ : ∃ tl, st.segs 1 = s₀ :: tl := by
      rcases hh : st.segs 1 with _ | ⟨r0, tl⟩
      · rw [hh] at hs₀; simp at hs₀
      · rw [hh] at hs₀; simp only [List.head?_cons, Option.some.injEq] at hs₀; subst hs₀; exact ⟨tl, rfl⟩
    simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hl] at hc
    have hR := hI.riser (by rw [hl]; simp)
    have hlast : legOf (st.segs 1) ((st.segs 1).length - 1) = s₀.1 := by rw [hl]; exact legOf_cons_length s₀ tl
    have hodd : ((st.segs 1).length - 1) % 2 = 1 := by
      by_contra h0
      have := ((hR.axis_sign (k := (st.segs 1).length - 1) (by rw [hl]; simp)).1 (by omega)).1
      rw [hlast] at this; exact hc.1 this
    have := ((hR.axis_sign (k := (st.segs 1).length - 1) (by rw [hl]; simp)).2 hodd).1
    rw [hlast] at this; exact ⟨_, this⟩

omit [NeZero d] in
/-- Distinct layers are at least a pitch apart. [folklore] -/
theorem Wl_le_abs_zOf_sub (Y : FlatLayout) {e e' : MDir} (h : e ≠ e') : Y.Wl ≤ |Y.zOf e - Y.zOf e'| := by
  have hW0 : 0 ≤ Y.Wl := by unfold FlatLayout.Wl FlatLayout.U; positivity
  have hne : (TallLayout.layerIdx e : ℤ) ≠ TallLayout.layerIdx e' := by
    intro h'; exact h (layerIdx_injective (by exact_mod_cast h'))
  have : Y.zOf e - Y.zOf e' = ((TallLayout.layerIdx e : ℤ) - TallLayout.layerIdx e') * Y.Wl := by unfold FlatLayout.zOf; ring
  rw [this, abs_mul, abs_of_nonneg hW0]
  have h1 : 1 ≤ |(TallLayout.layerIdx e : ℤ) - TallLayout.layerIdx e'| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  nlinarith

/-- **When the token did not come straight, the riser is long**: its head is at least `11 U`
beyond the token along `e`. [folklore] -/
theorem FlatInv.riser_far (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hsrc : τ.src ≠ some e)
    (hc : complete' hd Y a e τ (eJOf hd Y a e τ st) 1 (st.segs 1)) :
    upar hd (dsg e) τ.pos + 11 * Y.U ≤ upar hd (dsg e) (legOf (st.segs 1) ((st.segs 1).length - 1)).b := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  -- the token's layer is another one: `|zN - z₀| ≥ W - ρ_v = 12 U`
  obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 hτ.src_some
  have hne : e ≠ d' := fun h => hsrc (by rw [hd', h])
  have hfar : 12 * Y.U ≤ |zN Y e - τ.pos (ax0 hd)| := by
    have h1 := Wl_le_abs_zOf_sub Y hne
    have h2 := hτ.height d' hd'
    unfold FlatLayout.Wl at h1; unfold FlatLayout.ρv at h2; unfold zN
    have := abs_sub_abs_le_abs_sub (Y.zOf e - Y.zOf d') (τ.pos (ax0 hd) - Y.zOf d')
    rw [show Y.zOf e - Y.zOf d' - (τ.pos (ax0 hd) - Y.zOf d') = Y.zOf e - τ.pos (ax0 hd) by ring] at this
    linarith
  -- the riser ends beyond `zN`: from a start at most `2L'` beyond the token it climbed at least
  -- `12 U - 2L'`, less than `U + H` a pair
  obtain ⟨r, tl, hrt⟩ : ∃ r tl, st.segs 1 = r :: tl := by
    rcases hh : st.segs 1 with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · exact ⟨r, tl, rfl⟩
  have h1 : st.segs 1 ≠ [] := by rw [hrt]; simp
  have hend := (hI.riser_end hY hτ hc).1
  have habs := friseDir_mul_eq_abs hd Y e τ
  obtain ⟨-, -, hs0, hs1, hsox, -⟩ := hI.rstart_facts hY hτ h1
  have hR := hI.riser h1
  have hlast : legOf (st.segs 1) ((st.segs 1).length - 1) = r.1 := by rw [hrt]; exact legOf_cons_length r tl
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hrt, ffitsR] at hc
  have hodd : ((st.segs 1).length - 1) % 2 = 1 := by
    by_contra h0
    have := ((hR.axis_sign (k := (st.segs 1).length - 1) (by rw [hrt]; simp)).1 (by omega)).1
    rw [hlast] at this; exact hc.1 this
  have hlpos : 0 < (st.segs 1).length := by rw [hrt]; simp
  obtain ⟨j, hj⟩ : ∃ j, (st.segs 1).length = 2 * j + 2 := ⟨((st.segs 1).length - 1) / 2, by omega⟩
  have hlev := (hR.level.1 j (by omega)).2
  rw [show 2 * j + 1 = (st.segs 1).length - 1 by omega] at hlev
  -- so `j + 1 ≥ 9`
  have hj9 : 9 ≤ (j : ℤ) + 1 := by
    by_contra h'
    push Not at h'
    have h8 : (j : ℤ) + 1 ≤ 8 := by linarith
    have hδ : 0 ≤ Y.U + Y.H - Y.m - 1 := by linarith
    have := mul_le_mul_of_nonneg_right h8 hδ
    have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
    have e1 : (friseDir hd Y e τ : ℤ) * ((legOf (st.segs 1) ((st.segs 1).length - 1)).b (ax0 hd) - (rstart hd e τ (st.segs 0)).b (ax0 hd)) =
        (friseDir hd Y e τ : ℤ) * ((legOf (st.segs 1) ((st.segs 1).length - 1)).b (ax0 hd) - zN Y e) + (friseDir hd Y e τ : ℤ) * (zN Y e - τ.pos (ax0 hd)) -
        (friseDir hd Y e τ : ℤ) * ((rstart hd e τ (st.segs 0)).b (ax0 hd) - τ.pos (ax0 hd)) := by ring
    nlinarith [hlev, hend, habs, hfar, e1, hs1]
  -- the forward advance by landings
  have hub := hR.upar_lb (k := (st.segs 1).length - 1) (by omega)
  have hn : (((st.segs 1).length - 1 + 1) / 2 : ℕ) = j + 1 := by omega
  rw [hn] at hub; push_cast at hub
  have := mul_le_mul_of_nonneg_right hj9 hU.le
  have hsup : upar hd (dsg e) τ.pos + 2 * Y.U ≤ upar hd (dsg e) (rstart hd e τ (st.segs 0)).b := by
    have := hsox 0; have := hsox 1; unfold upar; linarith
  linarith

/-- **The entry side is far when the token did not come straight**: every plate of the preamble, the
jog turn, the jog and the turn back is at least `12 U` beyond the token along `e`. [folklore] -/
theorem FlatInv.entry_far (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hsrc : τ.src ≠ some e) {r : BrickRec d}
    (hr : ((r ∈ st.segs 2 ∨ r ∈ st.segs 3) ∨ r ∈ st.segs 4) ∨ r ∈ st.segs 5) : upar hd (dsg e) τ.pos + 12 * Y.U ≤ upar hd (dsg e) r.1.b := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  rcases hr with ((hr | hr) | hr) | hr
  · have h2 : st.segs 2 ≠ [] := List.ne_nil_of_mem hr
    obtain ⟨hc1, R, hR⟩ := hI.head_of_later (i := 2) (j := 1) (by decide) h2
    have hfar := hI.riser_far hY hτ hsrc hc1
    rw [legOf_last_of_head hR] at hfar
    obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
    obtain ⟨hlo, -, -⟩ := hI.win_pre hY hR hk
    rw [hkr] at hlo
    have hk0 : (0 : ℤ) ≤ k := by positivity
    nlinarith [hlo, hfar, hm0, hU]
  · linarith [(hI.abs_GJ hY hτ r hr).1]
  · linarith [((hI.abs_J hY hτ).1 r hr).1]
  · linarith [(hI.abs_GT hY hτ r hr).1]

/-! ## Containment: the entry side, the trunk and the forks, the branches -/

/-- **The box of a plate of the entry side lies in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_fzone_E (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {r : BrickRec d}
    (hr : ((r ∈ st.segs 2 ∨ r ∈ st.segs 3) ∨ r ∈ st.segs 4) ∨ r ∈ st.segs 5) : boxOf Y.L Y.H r.1 ⊆ fzone Y hd a e τ := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  -- the segment index
  obtain ⟨k, hk2, hk5, hrk⟩ : ∃ k : Fin 13, 2 ≤ k.val ∧ k.val ≤ 5 ∧ r ∈ st.segs k := by
    rcases hr with ((hr | hr) | hr) | hr
    · exact ⟨2, by decide, by decide, hr⟩
    · exact ⟨3, by decide, by decide, hr⟩
    · exact ⟨4, by decide, by decide, hr⟩
    · exact ⟨5, by decide, by decide, hr⟩
  obtain ⟨q, hq⟩ := hI.plane_axis k hk2 r hrk
  have hz := hI.z_after hY hτ k hk2 r hrk
  have hidle := hI.idle_all hτ (mem_all_of_mem hrk)
  -- forward and lateral windows of the base
  have hwin : upar hd (dsg e) τ.pos + 2 * Y.U ≤ upar hd (dsg e) r.1.b ∧ upar hd (dsg e) r.1.b ≤ upar hd (dsg e) τ.pos + 469 * Y.U ∧
      min (Uc hd (latDir e true).1 τ.pos - 123 * Y.U) (Y.lane (ftgt a e) e - 19 * Y.U) - 3 * Y.U ≤ Uc hd (latDir e true).1 r.1.b ∧
      Uc hd (latDir e true).1 r.1.b ≤ max (Uc hd (latDir e true).1 τ.pos + 123 * Y.U) (Y.lane (ftgt a e) e + 19 * Y.U) + 3 * Y.U := by
    have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
    have lat_of_v : ∀ {b : Site d} {c : ℤ}, |vperp hd (dsg e) b - vperp hd (dsg e) τ.pos| ≤ c →
        |Uc hd (latDir e true).1 b - Uc hd (latDir e true).1 τ.pos| ≤ c := fun h => by
      rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact h
    rcases hr with ((hr | hr) | hr) | hr
    · obtain ⟨h1, h2, h3⟩ := (hI.abs_P hY hτ).1 r hr
      have hl := abs_le.1 (lat_of_v h3)
      refine ⟨h1, by linarith, ?_, ?_⟩
      · have := min_le_left (Uc hd (latDir e true).1 τ.pos - 123 * Y.U) (Y.lane (ftgt a e) e - 19 * Y.U); linarith
      · have := le_max_left (Uc hd (latDir e true).1 τ.pos + 123 * Y.U) (Y.lane (ftgt a e) e + 19 * Y.U); linarith
    · obtain ⟨h1, h2, h3⟩ := hI.abs_GJ hY hτ r hr
      have hl := abs_le.1 (lat_of_v h3)
      refine ⟨by linarith, by linarith, ?_, ?_⟩
      · have := min_le_left (Uc hd (latDir e true).1 τ.pos - 123 * Y.U) (Y.lane (ftgt a e) e - 19 * Y.U); linarith
      · have := le_max_left (Uc hd (latDir e true).1 τ.pos + 123 * Y.U) (Y.lane (ftgt a e) e + 19 * Y.U); linarith
    · obtain ⟨h1, h2, h3, h4⟩ := (hI.abs_J hY hτ).1 r hr
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · obtain ⟨h1, h2, h3⟩ := hI.abs_GT hY hτ r hr
      have hl := abs_le.1 h3
      refine ⟨by linarith, h2, ?_, ?_⟩
      · have := min_le_right (Uc hd (latDir e true).1 τ.pos - 123 * Y.U) (Y.lane (ftgt a e) e - 19 * Y.U); linarith
      · have := le_max_right (Uc hd (latDir e true).1 τ.pos + 123 * Y.U) (Y.lane (ftgt a e) e + 19 * Y.U); linarith
  obtain ⟨w1, w2, w3, w4⟩ := hwin
  intro w hw
  have hP := abs_le.1 (box_P (hd := hd) (e := e) hY hw)
  have hL := abs_le.1 (box_L (hd := hd) (e := e) hY hw)
  have hZ := abs_le.1 (box_Z_plane hY hw (by rw [hq]; exact pl_ne_ax0 hd _))
  have hz' := abs_le.1 hz
  refine ⟨box_idle hY hw hidle (Or.inr ⟨q, hq⟩), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, by linarith, ?_, ?_, ?_, fun hnear => ?_⟩)))))⟩
  · -- the forward margin
    unfold cE
    split_ifs with hsrc
    · linarith
    · have := hI.entry_far hY hτ hsrc hr; linarith
  · have := min_le_min (show Uc hd (latDir e true).1 τ.pos - 126 * Y.U ≤ Uc hd (latDir e true).1 τ.pos - 123 * Y.U - 3 * Y.U by linarith)
      (show Y.lane (ftgt a e) e - 22 * Y.U ≤ Y.lane (ftgt a e) e - 19 * Y.U - 3 * Y.U by linarith)
    rw [min_sub_sub_right] at this
    linarith
  · have := max_le_max (show Uc hd (latDir e true).1 τ.pos + 123 * Y.U + 3 * Y.U ≤ Uc hd (latDir e true).1 τ.pos + 126 * Y.U by linarith)
      (show Y.lane (ftgt a e) e + 19 * Y.U + 3 * Y.U ≤ Y.lane (ftgt a e) e + 22 * Y.U by linarith)
    rw [max_add_add_right] at this
    linarith
  · unfold zN at hz'; rw [abs_le]; constructor <;> linarith
  · -- near the token only the preamble occurs, beyond the riser's start along the token's axis
    rcases hr with ((hr | hr) | hr) | hr
    · have h2 : st.segs 2 ≠ [] := List.ne_nil_of_mem hr
      obtain ⟨hc1, R, hR⟩ := hI.head_of_later (i := 2) (j := 1) (by decide) h2
      have h1 : st.segs 1 ≠ [] := by intro h; rw [h] at hR; simp at hR
      obtain ⟨-, -, -, hwox⟩ := hI.win_riser hY hτ (k := (st.segs 1).length - 1) (by have := List.length_pos_of_ne_nil h1; omega)
      rw [legOf_last_of_head hR] at hwox
      obtain ⟨R', hR', q₂, hPE⟩ := hI.frame_pre h2
      have hRR : R' = R := by rw [hR] at hR'; simpa using hR'.symm
      subst hRR
      obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
      have hm := (hPE.mono (k := 0) (k' := k + 1) (by omega) (by simp; omega) (plIdx hd τ.ax)).1
      rw [legOf_snoc_zero, legOf_append_singleton_succ, hkr] at hm
      have hx := hwox (plIdx hd τ.ax)
      have hb := abs_le.1 (box_plane (hd := hd) hY hw (plIdx hd τ.ax))
      unfold ox at hx hm
      have hσ : ((dsg e (plIdx hd τ.ax) : ℤ)) = 1 ∨ ((dsg e (plIdx hd τ.ax) : ℤ)) = -1 := by
        rcases Int.units_eq_one_or (dsg e (plIdx hd τ.ax)) with h' | h' <;> simp [h']
      rcases hσ with h | h <;> rw [h] at hx hm ⊢ <;> linarith [hb.1, hb.2]
    · exfalso; have := (hI.abs_GJ hY hτ r hr).1; linarith
    · exfalso; have := ((hI.abs_J hY hτ).1 r hr).1; linarith
    · exfalso; have := (hI.abs_GT hY hτ r hr).1; linarith

/-- **The box of a plate of the trunk or of a fork lies in the region** (the trunk tube). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_fzone_T (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {r : BrickRec d}
    (hr : (r ∈ st.segs 6 ∨ r ∈ st.segs 8 ∨ r ∈ st.segs 10) ∨ (r ∈ st.segs 7 ∨ r ∈ st.segs 9)) : boxOf Y.L Y.H r.1 ⊆ fzone Y hd a e τ := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨hSlo, hShi, -⟩ := hτ.windows
  obtain ⟨hL1, hL2, hc0, hc1⟩ := sLane_eB Y a e
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ; positivity
  have hprod : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  -- the segment index and the plane axis
  obtain ⟨k, hk2, hrk⟩ : ∃ k : Fin 13, 2 ≤ k.val ∧ r ∈ st.segs k := by
    rcases hr with (hr | hr | hr) | (hr | hr)
    · exact ⟨6, by decide, hr⟩
    · exact ⟨8, by decide, hr⟩
    · exact ⟨10, by decide, hr⟩
    · exact ⟨7, by decide, hr⟩
    · exact ⟨9, by decide, hr⟩
  obtain ⟨q, hq⟩ := hI.plane_axis k hk2 r hrk
  have hz := abs_le.1 (hI.z_after hY hτ k hk2 r hrk)
  have hidle := hI.idle_all hτ (mem_all_of_mem hrk)
  -- the base's windows: forward in `[S + 96U, …]`, and either a trunk plate (forward sign) below
  -- `s·ctr + D - 2U + H`, or a fork plate below `thr + 4U`; laterally within `534 U` of the lane
  have hwin : upar hd (dsg e) τ.pos + 96 * Y.U ≤ upar hd (dsg e) r.1.b ∧ |Uc hd (latDir e true).1 r.1.b - Y.lane (ftgt a e) e| ≤ 534 * Y.U ∧
      ((r.1.s = dsg e q ∧ upar hd (dsg e) r.1.b < (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 + Y.Df - 2 * Y.U + Y.H) ∨
        upar hd (dsg e) r.1.b ≤ (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 + Y.Df - 4 * Y.U) := by
    rcases hr with hr | (hr | hr)
    · have hmem : r ∈ st.segs 10 ++ st.segs 8 ++ st.segs 6 := by
        simp only [List.mem_append]; rcases hr with hr | hr | hr
        · exact Or.inr hr
        · exact Or.inl (Or.inr hr)
        · exact Or.inl (Or.inl hr)
      obtain ⟨h1, h2, h3⟩ := hI.abs_T hY hτ r hmem
      refine ⟨h1, h3.trans (by linarith), Or.inl ⟨?_, h2⟩⟩
      -- the sign of a trunk plate: forwards
      rcases hr with hr | hr | hr <;>
        [ (have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 6 (st.segs 6) (st.segs (startOf 6)) := hI.segOK 6);
          (have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 8 (st.segs 8) (st.segs (startOf 8)) := hI.segOK 8);
          (have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10) ] <;>
        simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
      · obtain ⟨_, _, hDg, -⟩ := hK (List.ne_nil_of_mem hr)
        obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
        obtain ⟨ha, hsg⟩ := hDg.axis_sign hj
        rw [hjr] at ha hsg; rw [hq] at ha; rw [hsg, ← pl_injective hd ha]
      · obtain ⟨_, _, _, hDg, -⟩ := hK (List.ne_nil_of_mem hr)
        obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
        obtain ⟨ha, hsg⟩ := hDg.axis_sign hj
        rw [hjr] at ha hsg; rw [hq] at ha; rw [hsg, ← pl_injective hd ha]
      · obtain ⟨_, _, _, hDg, -⟩ := hK (List.ne_nil_of_mem hr)
        obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
        obtain ⟨ha, hsg⟩ := hDg.axis_sign hj
        rw [hjr] at ha hsg; rw [hq] at ha; rw [hsg, ← pl_injective hd ha]
    · obtain ⟨h1, h2, h3⟩ := hI.abs_G1 hY hτ r hr
      refine ⟨?_, h3, Or.inr ?_⟩ <;> rcases hs with h | h <;> rw [h] at hL1 h1 h2 hShi <;> try rw [h]
      all_goals linarith [hprod.1, hprod.2]
    · obtain ⟨h1, h2, h3⟩ := hI.abs_G2 hY hτ r hr
      refine ⟨?_, h3, Or.inr ?_⟩ <;> rcases hs with h | h <;> rw [h] at hL2 h1 h2 hShi <;> try rw [h]
      all_goals linarith [hprod.1, hprod.2]
  obtain ⟨w1, w3, w2⟩ := hwin
  have hlat := abs_le.1 w3
  intro w hw
  have hP := abs_le.1 (box_P (hd := hd) (e := e) hY hw)
  have hL := abs_le.1 (box_L (hd := hd) (e := e) hY hw)
  have hZ := abs_le.1 (box_Z_plane hY hw (by rw [hq]; exact pl_ne_ax0 hd _))
  refine ⟨box_idle hY hw hidle (Or.inr ⟨q, hq⟩), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, ?_, ?_, ?_⟩))))))⟩
  · rcases w2 with ⟨hsg, hhi⟩ | hle
    · have := (box_P_fwd (hd := hd) (e := e) hY hw hq).1 hsg; linarith
    · linarith
  · rw [abs_le]; constructor <;> linarith
  · unfold zN at hz; rw [abs_le]; constructor <;> linarith

/-- **The box of a plate of a branch lies in the region** (its branch tube). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_fzone_B (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {r : BrickRec d}
    (hr : r ∈ st.segs 11 ∨ r ∈ st.segs 12) : boxOf Y.L Y.H r.1 ⊆ fzone Y hd a e τ := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs with h' | h' <;> rw [h'] <;> norm_num
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases hs with h' | h' <;> simp [h']
  obtain ⟨⟨hflip1, hkeep1⟩, hflip2, hkeep2⟩ := flip_keep_B e
  change dsg (eB1 e) 0 = -dsg e 0 at hflip1
  change dsg (eB2 e) 1 = -dsg e 1 at hflip2
  -- `s · (2 · Uc_lat b) = 2 vperp b`
  have hsv : ∀ b : Site d, (sgOf e : ℤ) * (2 * Uc hd (latDir e true).1 b) = 2 * vperp hd (dsg e) b := fun b => by
    rw [Uc_lat_eq_vperp]; linear_combination (2 * vperp hd (dsg e) b) * hss
  rcases hr with hr | hr
  · -- the first branch
    obtain ⟨q, hq⟩ := hI.plane_axis 11 (by decide) r hr
    have hz := abs_le.1 (hI.z_after hY hτ 11 (by decide) r hr)
    have hidle := hI.idle_all hτ (mem_all_of_mem hr)
    obtain ⟨-, hB⟩ := hI.abs_B1 hY hτ
    obtain ⟨hroom, hlat, hlo, hhi⟩ := hB r hr
    -- axis and sign
    have has : (r.1.a = pl hd 0 ∧ r.1.s = -dsg e 0) ∨ (r.1.a = pl hd 1 ∧ r.1.s = dsg e 1) := by
      obtain ⟨γ, -, -, hBE⟩ := hI.frame_branch.1 (List.ne_nil_of_mem hr)
      have hp1 : oth (p1 e) = 0 := (oth_p1_p2 e).1.trans (flipIdx_eB e).1
      rw [hp1] at hBE
      obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
      obtain ⟨ha, hsg⟩ := hBE.axis_sign (k := j + 1) (by simp; omega)
      rw [legOf_append_singleton_succ, hjr] at ha hsg
      rcases Fin.exists_fin_two.1 ⟨qAt 0 (j + 1), rfl⟩ with h0 | h0 <;> rw [h0] at ha hsg
      · exact Or.inl ⟨ha, by rw [hsg, hflip1]⟩
      · exact Or.inr ⟨ha, by rw [hsg, hkeep1]⟩
    intro w hw
    have hP := abs_le.1 (box_P (hd := hd) (e := e) hY hw)
    have hL := abs_le.1 (box_L (hd := hd) (e := e) hY hw)
    have hZ := abs_le.1 (box_Z_plane hY hw (by rw [hq]; exact pl_ne_ax0 hd _))
    have hlow := box_sL_B1 (hd := hd) (e := e) hY hw has
    refine ⟨box_idle hY hw hidle (Or.inr ⟨q, hq⟩), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩)))))))⟩
    · rw [abs_le]; constructor <;> linarith
    · linarith
    · have e1 : (sgOf e : ℤ) * Uc hd (latDir e true).1 w = (sgOf e : ℤ) * (Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 r.1.b) + 2 * vperp hd (dsg e) r.1.b := by
        rw [← hsv]; ring
      have hb : (sgOf e : ℤ) * (Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 r.1.b) ≤ 4 * Y.U := by
        rcases hs with h | h <;> rw [h] <;> linarith
      have e2 : (sgOf e : ℤ) * (2 * Y.lane (ftgt a e) e) = 2 * ((sgOf e : ℤ) * Y.lane (ftgt a e) e) := by ring
      rw [e1, e2]; linarith
    · unfold zN at hz; rw [abs_le]; constructor <;> linarith
  · -- the second branch
    obtain ⟨q, hq⟩ := hI.plane_axis 12 (by decide) r hr
    have hz := abs_le.1 (hI.z_after hY hτ 12 (by decide) r hr)
    have hidle := hI.idle_all hτ (mem_all_of_mem hr)
    obtain ⟨-, hB⟩ := hI.abs_B2 hY hτ
    obtain ⟨hroom, hlat, hlo, hhi⟩ := hB r hr
    have has : (r.1.a = pl hd 1 ∧ r.1.s = -dsg e 1) ∨ (r.1.a = pl hd 0 ∧ r.1.s = dsg e 0) := by
      obtain ⟨γ, -, -, hBE⟩ := hI.frame_branch.2 (List.ne_nil_of_mem hr)
      have hp2 : oth (p2 e) = 1 := (oth_p1_p2 e).2.trans (flipIdx_eB e).2
      rw [hp2] at hBE
      obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
      obtain ⟨ha, hsg⟩ := hBE.axis_sign (k := j + 1) (by simp; omega)
      rw [legOf_append_singleton_succ, hjr] at ha hsg
      rcases Fin.exists_fin_two.1 ⟨qAt 1 (j + 1), rfl⟩ with h0 | h0 <;> rw [h0] at ha hsg
      · exact Or.inr ⟨ha, by rw [hsg, hkeep2]⟩
      · exact Or.inl ⟨ha, by rw [hsg, hflip2]⟩
    intro w hw
    have hP := abs_le.1 (box_P (hd := hd) (e := e) hY hw)
    have hL := abs_le.1 (box_L (hd := hd) (e := e) hY hw)
    have hZ := abs_le.1 (box_Z_plane hY hw (by rw [hq]; exact pl_ne_ax0 hd _))
    have hup := box_sL_B2 (hd := hd) (e := e) hY hw has
    refine ⟨box_idle hY hw hidle (Or.inr ⟨q, hq⟩), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))))⟩
    · rw [abs_le]; constructor <;> linarith
    · have e1 : (sgOf e : ℤ) * Uc hd (latDir e true).1 w = (sgOf e : ℤ) * (Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 r.1.b) + 2 * vperp hd (dsg e) r.1.b := by
        rw [← hsv]; ring
      have hb : -(4 * Y.U) ≤ (sgOf e : ℤ) * (Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 r.1.b) := by
        rcases hs with h | h <;> rw [h] <;> linarith
      have e2 : (sgOf e : ℤ) * (2 * Y.lane (ftgt a e) e) = 2 * ((sgOf e : ℤ) * Y.lane (ftgt a e) e) := by ring
      rw [e1, e2]; linarith
    · linarith
    · unfold zN at hz; rw [abs_le]; constructor <;> linarith

/-- **The box of every plate of an invariant state lies in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_fzone (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {r : BrickRec d} (hr : r ∈ st.all) :
    boxOf Y.L Y.H r.1 ⊆ fzone Y hd a e τ := by
  unfold FS.all at hr
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hr
  obtain ⟨k, hk⟩ := hr
  have hk13 := k.isLt
  rcases k with ⟨kv, _⟩
  interval_cases kv
  · exact boxOf_subset_fzone_A hI hY hτ hk
  · exact boxOf_subset_fzone_R hI hY hτ hk
  · exact boxOf_subset_fzone_E hI hY hτ (Or.inl (Or.inl (Or.inl hk)))
  · exact boxOf_subset_fzone_E hI hY hτ (Or.inl (Or.inl (Or.inr hk)))
  · exact boxOf_subset_fzone_E hI hY hτ (Or.inl (Or.inr hk))
  · exact boxOf_subset_fzone_E hI hY hτ (Or.inr hk)
  · exact boxOf_subset_fzone_T hI hY hτ (Or.inl (Or.inl hk))
  · exact boxOf_subset_fzone_T hI hY hτ (Or.inr (Or.inl hk))
  · exact boxOf_subset_fzone_T hI hY hτ (Or.inl (Or.inr (Or.inl hk)))
  · exact boxOf_subset_fzone_T hI hY hτ (Or.inr (Or.inr hk))
  · exact boxOf_subset_fzone_T hI hY hτ (Or.inl (Or.inr (Or.inr hk)))
  · exact boxOf_subset_fzone_B hI hY hτ (Or.inl hk)
  · exact boxOf_subset_fzone_B hI hY hτ (Or.inr hk)

end BGNd

end Percolation.Literature

end

/-!
# Part 3 (The flat gait, XXV): the zone, III — the zone as a finite set of lattice edges

The reserved zone of an attempt of the flat gait
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`) as a finite set of
lattice edges: those with both endpoints in a vertex box around the target cell and doubled
midpoint in the region (`fzoneF`). The region is bounded in every coordinate (`fzone_bound`), so a
placed plate whose box lies in the region has its support in the zone (`suppP_subset_fzoneF`);
hence every plate of an invariant state does (`FlatInv.suppP_subset_fzoneF`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174, p. 173 (C).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

section Finite

variable (Y : FlatLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d)

/-- The reference point of the zone: the centre of the target cell in the plane, `0` elsewhere
(the diagonal centres `ctr(c, 0) = x₀ + x₁`, `ctr(c, 1) = x₀ - x₁`). [folklore] -/
def fzoneCentre : Site d := fun i =>
  if i = pl hd 0 then (ftgt a e 0 + ftgt a e 1) * Y.Df else if i = pl hd 1 then (ftgt a e 0 - ftgt a e 1) * Y.Df else 0

/-- The radius of the vertex box of the zone, `4 D = 2¹⁴ U`. [folklore] -/
def fzoneRad (Y : FlatLayout) : ℕ := 2 ^ 14 * (Y.L + 1)

omit [NeZero d] in
/-- The radius in `ℤ`. [folklore] -/
theorem fzoneRad_eq (Y : FlatLayout) : ((fzoneRad Y : ℕ) : ℤ) = 4 * Y.Df := by
  unfold fzoneRad FlatLayout.Df FlatLayout.U; push_cast; ring

/-- The vertex box of the zone. [folklore] -/
def fvbox : Finset (Site d) := (box d (fzoneRad Y)).image fun x => x + fzoneCentre Y hd a e

/-- **The zone**: the lattice edges with both endpoints in the vertex box and doubled midpoint in the
region. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def fzoneF : Finset (Sym2 (Site d)) := (edgesIn (zdGraph d) (fvbox Y hd a e)).filter fun z => dmid z ∈ fzone Y hd a e τ

omit [NeZero d] in
/-- Membership in the zone. [folklore] -/
theorem mem_fzoneF {z : Sym2 (Site d)} :
    z ∈ fzoneF Y hd a e τ ↔ z ∈ (zdGraph d).edgeSet ∧ (∀ x ∈ z, x ∈ fvbox Y hd a e) ∧ dmid z ∈ fzone Y hd a e τ := by
  unfold fzoneF; rw [Finset.mem_filter, mem_edgesIn_iff, and_assoc]

omit [NeZero d] in
/-- **The constants of the frame of an admissible token**: the token's forward window, the lateral
offsets of the token, the target lane and the take-off lines from the target centre, the heights. [folklore] -/
theorem FTAdm.frame (hτ : FTAdm hd Y a e τ) :
    -(Y.Df + 2 * Y.U) ≤ upar hd (dsg e) τ.pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 ∧
      upar hd (dsg e) τ.pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 ≤ -(Y.Df + 1) ∧
      |Uc hd (latDir e true).1 τ.pos - Y.ctr (ftgt a e) (latDir e true).1| ≤ Y.lam + 2 * Y.lamJ + Y.ρp ∧
      |Y.lane (ftgt a e) e - Y.ctr (ftgt a e) (latDir e true).1| ≤ Y.lam + Y.lamJ ∧
      |(sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1| ≤ Y.lam + Y.lamJ ∧
      |(sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1| ≤ Y.lam + Y.lamJ ∧
      |Y.zOf e| ≤ 3 * Y.Wl ∧ |τ.pos (ax0 hd)| ≤ 3 * Y.Wl + Y.ρv := by
  obtain ⟨h1, h2, h3⟩ := hτ.windows
  obtain ⟨hL1, hL2, hc0, hc1⟩ := sLane_eB Y a e
  have hsL := sLane_e Y a e
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs with h' | h' <;> rw [h'] <;> norm_num
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ FlatLayout.U; positivity
  have hΛ0 : 0 ≤ Y.lam := by unfold FlatLayout.lam FlatLayout.U; positivity
  have hρ0 : 0 ≤ Y.ρp := by unfold FlatLayout.ρp FlatLayout.U; positivity
  have hprod : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
  have hlane_c : |Y.lane (ftgt a e) e - Y.ctr (ftgt a e) (latDir e true).1| ≤ Y.lam + Y.lamJ := by
    rw [abs_le]
    rcases hs with h | h <;> rw [h] at hsL <;> constructor <;> linarith [hprod.1, hprod.2]
  have hla := lane_ftgt_abs Y a e
  refine ⟨h1, h2, ?_, hlane_c, ?_, ?_, ?_, ?_⟩
  · have t1 := abs_le.1 h3; have t2 := abs_le.1 hla; have t3 := abs_le.1 hlane_c
    rw [Uc_lat_eq_vperp, abs_le]; constructor <;> linarith
  · rw [abs_le]; rcases hs with h | h <;> rw [h] at hL1 ⊢ <;> constructor <;> linarith [hprod.1, hprod.2]
  · rw [abs_le]; rcases hs with h | h <;> rw [h] at hL2 ⊢ <;> constructor <;> linarith [hprod.1, hprod.2]
  · have := zOf_sub_zOf_abs Y e (0, true)
    have h0 : Y.zOf (0, true) = 0 := by unfold FlatLayout.zOf TallLayout.layerIdx; simp
    rw [h0, sub_zero] at this; exact this
  · obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 hτ.src_some
    have hh := abs_le.1 (hτ.height d' hd')
    have := zOf_sub_zOf_abs Y d' (0, true)
    have h0 : Y.zOf (0, true) = 0 := by unfold FlatLayout.zOf TallLayout.layerIdx; simp
    rw [h0, sub_zero] at this
    have t := abs_le.1 this
    rw [abs_le]; constructor <;> linarith

omit [NeZero d] in
/-- Near the token (a point of one of the lead-in boxes) both plane coordinates are within `4U + 4H + 2`
of twice the token's; otherwise the point is in one of the other pieces. [folklore] -/
theorem fzone_leadin_or (hY : Y.OK) {w : Site d} (hw : w ∈ fzone Y hd a e τ) :
    (∀ i : Fin 2, |w (pl hd i) - 2 * τ.pos (pl hd i)| ≤ 4 * Y.U + 4 * Y.H + 2) ∨
    ¬((1 ≤ (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ∧
        (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ≤ 2 * Y.H + 2 ∧
        |w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))| ≤ 2 * Y.U ∧ |w (ax0 hd) - 2 * τ.pos (ax0 hd)| ≤ 2 * Y.U) ∨
      (2 * Y.U + 1 ≤ (dsg e (oth (plIdx hd τ.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))) ∧
        (dsg e (oth (plIdx hd τ.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))) ≤ 2 * Y.U + 2 * Y.H + 2 ∧
        2 * Y.m + 2 - 2 * Y.U ≤ (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ∧
        (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ≤ 2 * Y.U + 2 * Y.H ∧
        -(2 * Y.U) ≤ (friseDir hd Y e τ : ℤ) * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ∧ (friseDir hd Y e τ : ℤ) * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ≤ 2 * Y.U + 2 * Y.Lp) ∨
      (2 * Y.U + 2 * Y.m + 3 ≤ (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ∧
        (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ≤ 2 * Y.U + 4 * Y.H + 2 ∧
        2 * Y.m + 2 ≤ (dsg e (oth (plIdx hd τ.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))) ∧
        (dsg e (oth (plIdx hd τ.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))) ≤ 4 * Y.U + 2 * Y.H ∧
        -(2 * Y.U) ≤ (friseDir hd Y e τ : ℤ) * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ∧ (friseDir hd Y e τ : ℤ) * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ≤ 2 * Y.U + 4 * Y.Lp)) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨hidle, hcases⟩ := hw
  have hσ : ∀ i : Fin 2, ((dsg e i : ℤ)) = 1 ∨ ((dsg e i : ℤ)) = -1 := fun i => by rcases Int.units_eq_one_or (dsg e i) with h' | h' <;> simp [h']
  have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  by_cases hA : (1 ≤ (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ∧
        (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ≤ 2 * Y.H + 2 ∧
        |w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))| ≤ 2 * Y.U ∧ |w (ax0 hd) - 2 * τ.pos (ax0 hd)| ≤ 2 * Y.U) ∨
      (2 * Y.U + 1 ≤ (dsg e (oth (plIdx hd τ.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))) ∧
        (dsg e (oth (plIdx hd τ.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))) ≤ 2 * Y.U + 2 * Y.H + 2 ∧
        2 * Y.m + 2 - 2 * Y.U ≤ (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ∧
        (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ≤ 2 * Y.U + 2 * Y.H ∧
        -(2 * Y.U) ≤ (friseDir hd Y e τ : ℤ) * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ∧ (friseDir hd Y e τ : ℤ) * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ≤ 2 * Y.U + 2 * Y.Lp) ∨
      (2 * Y.U + 2 * Y.m + 3 ≤ (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ∧
        (dsg e (plIdx hd τ.ax) : ℤ) * (w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))) ≤ 2 * Y.U + 4 * Y.H + 2 ∧
        2 * Y.m + 2 ≤ (dsg e (oth (plIdx hd τ.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))) ∧
        (dsg e (oth (plIdx hd τ.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))) ≤ 4 * Y.U + 2 * Y.H ∧
        -(2 * Y.U) ≤ (friseDir hd Y e τ : ℤ) * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ∧ (friseDir hd Y e τ : ℤ) * (w (ax0 hd) - 2 * τ.pos (ax0 hd)) ≤ 2 * Y.U + 4 * Y.Lp)
  · left
    -- bounds on the two plane coordinates at the token's axis index and the other one
    have both : |w (pl hd (plIdx hd τ.ax)) - 2 * τ.pos (pl hd (plIdx hd τ.ax))| ≤ 4 * Y.U + 4 * Y.H + 2 ∧
        |w (pl hd (oth (plIdx hd τ.ax))) - 2 * τ.pos (pl hd (oth (plIdx hd τ.ax)))| ≤ 4 * Y.U + 4 * Y.H + 2 := by
      rcases hA with ⟨a1, a2, a3, -⟩ | ⟨a1, a2, a3, a4, -, -⟩ | ⟨a1, a2, a3, a4, -, -⟩
      · have t := abs_le.1 a3
        refine ⟨?_, abs_le.2 ⟨by linarith, by linarith⟩⟩
        rw [abs_le]; rcases hσ (plIdx hd τ.ax) with h | h <;> rw [h] at a1 a2 <;> constructor <;> linarith
      · constructor
        · rw [abs_le]; rcases hσ (plIdx hd τ.ax) with h | h <;> rw [h] at a3 a4 <;> constructor <;> linarith
        · rw [abs_le]; rcases hσ (oth (plIdx hd τ.ax)) with h | h <;> rw [h] at a1 a2 <;> constructor <;> linarith
      · constructor
        · rw [abs_le]; rcases hσ (plIdx hd τ.ax) with h | h <;> rw [h] at a1 a2 <;> constructor <;> linarith
        · rw [abs_le]; rcases hσ (oth (plIdx hd τ.ax)) with h | h <;> rw [h] at a3 a4 <;> constructor <;> linarith
    intro i
    rcases eq_or_eq_oth i (plIdx hd τ.ax) with hi | hi <;> rw [hi]
    · exact both.1
    · exact both.2
  · right; exact hA

omit [NeZero d] in
/-- Plane bounds near the token translate to the diagonal coordinates. [folklore] -/
theorem near_diag {B : ℤ} {w : Site d} (hB : ∀ i : Fin 2, |w (pl hd i) - 2 * τ.pos (pl hd i)| ≤ B) :
    |(sgOf e : ℤ) * Uc hd e.1 w - 2 * upar hd (dsg e) τ.pos| ≤ 2 * B ∧ |Uc hd (latDir e true).1 w - 2 * Uc hd (latDir e true).1 τ.pos| ≤ 2 * B := by
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have h0 := abs_le.1 (hB 0); have h1 := abs_le.1 (hB 1)
  constructor
  · rw [← upar_dsg, ← mul_assoc, mul_comm (2 : ℤ), mul_assoc, ← mul_sub, Uc_sub_two]
    rw [abs_le]; rcases hs with h | h <;> rw [h] <;> split_ifs <;> constructor <;> linarith
  · rw [Uc_sub_two, abs_le]; split_ifs <;> constructor <;> linarith

omit [NeZero d] in
/-- A bound of the region. [folklore] -/
theorem fzone_bound_P (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {w : Site d} (hw : w ∈ fzone Y hd a e τ) :
    |(sgOf e : ℤ) * Uc hd e.1 w - 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1)| ≤ 6 * Y.Df := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := FTAdm.frame Y hd a e τ hτ
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hρ : Y.ρp = 640 * Y.U := rfl
  have hW : Y.Wl = 16 * Y.U := rfl
  have hρv : Y.ρv = 4 * Y.U := rfl
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have t3 := abs_le.1 f3; have t4 := abs_le.1 f4; have t5 := abs_le.1 f5; have t6 := abs_le.1 f6; have t7 := abs_le.1 f7; have t8 := abs_le.1 f8
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hu : (friseDir hd Y e τ : ℤ) = 1 ∨ (friseDir hd Y e τ : ℤ) = -1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [h']
  have hcE : 0 ≤ cE Y e τ ∧ cE Y e τ ≤ 8 * Y.U := by unfold cE; split_ifs <;> constructor <;> linarith
  obtain ⟨hidle, hcases⟩ := id hw
  have leadin := fzone_leadin_or Y hd a e τ hY hw
  have near := fun {B : ℤ} (hB : ∀ i : Fin 2, |w (pl hd i) - 2 * τ.pos (pl hd i)| ≤ B) => near_diag hd e τ hB
  rcases leadin with hB | hnot
  · have := (near hB).1; have t := abs_le.1 this; rw [abs_le]; constructor <;> linarith
  · rcases hcases with hA0 | hA1 | hA2 | ⟨-, -, a3, a4, -⟩ | ⟨-, -, a3, a4, -⟩ | ⟨a1, a2, -⟩ | ⟨a1, a2, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩
    · exact absurd (Or.inl hA0) hnot
    · exact absurd (Or.inr (Or.inl hA1)) hnot
    · exact absurd (Or.inr (Or.inr hA2)) hnot
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
    · have := abs_le.1 a1; rw [abs_le]; rcases hs with h | h <;> rw [h] at this t5 ⊢ <;> constructor <;> linarith
    · have := abs_le.1 a1; rw [abs_le]; rcases hs with h | h <;> rw [h] at this t6 ⊢ <;> constructor <;> linarith

omit [NeZero d] in
/-- A bound of the region. [folklore] -/
theorem fzone_bound_L (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {w : Site d} (hw : w ∈ fzone Y hd a e τ) :
    |Uc hd (latDir e true).1 w - 2 * Y.ctr (ftgt a e) (latDir e true).1| ≤ 6 * Y.Df := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := FTAdm.frame Y hd a e τ hτ
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hρ : Y.ρp = 640 * Y.U := rfl
  have hW : Y.Wl = 16 * Y.U := rfl
  have hρv : Y.ρv = 4 * Y.U := rfl
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have t3 := abs_le.1 f3; have t4 := abs_le.1 f4; have t5 := abs_le.1 f5; have t6 := abs_le.1 f6; have t7 := abs_le.1 f7; have t8 := abs_le.1 f8
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hu : (friseDir hd Y e τ : ℤ) = 1 ∨ (friseDir hd Y e τ : ℤ) = -1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [h']
  have hcE : 0 ≤ cE Y e τ ∧ cE Y e τ ≤ 8 * Y.U := by unfold cE; split_ifs <;> constructor <;> linarith
  obtain ⟨hidle, hcases⟩ := id hw
  have leadin := fzone_leadin_or Y hd a e τ hY hw
  have near := fun {B : ℤ} (hB : ∀ i : Fin 2, |w (pl hd i) - 2 * τ.pos (pl hd i)| ≤ B) => near_diag hd e τ hB
  rcases leadin with hB | hnot
  · have := (near hB).2; have t := abs_le.1 this; rw [abs_le]; constructor <;> linarith
  · rcases hcases with hA0 | hA1 | hA2 | ⟨-, -, -, -, a5, -⟩ | ⟨-, -, -, -, a5, -⟩ | ⟨-, -, a3, a4, -⟩ | ⟨-, -, a3, -⟩ | ⟨-, a2, a3, -⟩ | ⟨-, a2, a3, -⟩
    · exact absurd (Or.inl hA0) hnot
    · exact absurd (Or.inr (Or.inl hA1)) hnot
    · exact absurd (Or.inr (Or.inr hA2)) hnot
    · have := abs_le.1 a5; rw [abs_le]; constructor <;> linarith
    · have := abs_le.1 a5; rw [abs_le]; constructor <;> linarith
    · have hmin : Uc hd (latDir e true).1 τ.pos - 126 * Y.U - (Y.lam + Y.lamJ + Y.lam + 2 * Y.lamJ + Y.ρp) ≤
          min (Uc hd (latDir e true).1 τ.pos - 126 * Y.U) (Y.lane (ftgt a e) e - 22 * Y.U) := by
        rw [le_min_iff]; constructor <;> linarith
      have hmax : max (Uc hd (latDir e true).1 τ.pos + 126 * Y.U) (Y.lane (ftgt a e) e + 22 * Y.U) ≤
          Uc hd (latDir e true).1 τ.pos + 126 * Y.U + (Y.lam + Y.lamJ + Y.lam + 2 * Y.lamJ + Y.ρp) := by
        rw [max_le_iff]; constructor <;> linarith
      rw [abs_le]; constructor <;> linarith
    · have := abs_le.1 a3; rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; rcases hs with h | h <;> rw [h] at a2 a3 <;> constructor <;> linarith
    · rw [abs_le]; rcases hs with h | h <;> rw [h] at a2 a3 <;> constructor <;> linarith

omit [NeZero d] in
/-- A bound of the region. [folklore] -/
theorem fzone_bound_Z (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {w : Site d} (hw : w ∈ fzone Y hd a e τ) :
    |w (ax0 hd)| ≤ 6 * Y.Df := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨-, -, -, -, -, -, f7, f8⟩ := FTAdm.frame Y hd a e τ hτ
  have hD : Y.Df = 4096 * Y.U := rfl
  have hW : Y.Wl = 16 * Y.U := rfl
  have hρv : Y.ρv = 4 * Y.U := rfl
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hH10 : 10 * (Y.H : ℤ) ≤ 2 * Y.U := by linarith
  have t7 := abs_le.1 f7; have t8 := abs_le.1 f8
  have hu : (friseDir hd Y e τ : ℤ) = 1 ∨ (friseDir hd Y e τ : ℤ) = -1 := by rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [h']
  obtain ⟨-, hcases⟩ := hw
  rw [abs_le]
  rcases hcases with ⟨-, -, -, a4⟩ | ⟨-, -, -, -, a5, a6⟩ | ⟨-, -, -, -, a5, a6⟩ | ⟨a1, a2, -⟩ | ⟨a1, a2, -⟩ | ⟨-, -, -, -, a5, -⟩ | ⟨-, -, -, a4⟩ | ⟨-, -, -, a4⟩ | ⟨-, -, -, a4⟩
  · have := abs_le.1 a4; constructor <;> linarith
  · rcases hu with h | h <;> rw [h] at a5 a6 <;> constructor <;> linarith
  · rcases hu with h | h <;> rw [h] at a5 a6 <;> constructor <;> linarith
  · rcases hu with h | h <;> rw [h] at a1 a2 <;> constructor <;> linarith
  · rcases hu with h | h <;> rw [h] at a1 a2 <;> constructor <;> linarith
  · have := abs_le.1 a5; constructor <;> linarith
  · have := abs_le.1 a4; constructor <;> linarith
  · have := abs_le.1 a4; constructor <;> linarith
  · have := abs_le.1 a4; constructor <;> linarith

omit [NeZero d] in
/-- **The region is bounded**: the diagonal coordinates within `6 D` of the target centre's, the height
and the idle coordinates within `6 D` of `0`. [folklore] -/
theorem fzone_bounds (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {w : Site d} (hw : w ∈ fzone Y hd a e τ) :
    |(sgOf e : ℤ) * Uc hd e.1 w - 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1)| ≤ 6 * Y.Df ∧
      |Uc hd (latDir e true).1 w - 2 * Y.ctr (ftgt a e) (latDir e true).1| ≤ 6 * Y.Df ∧
      |w (ax0 hd)| ≤ 6 * Y.Df ∧ ∀ j, Idle hd j → |w j| ≤ 6 * Y.Df := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hD : Y.Df = 4096 * Y.U := rfl
  refine ⟨fzone_bound_P Y hd a e τ hY hτ hw, fzone_bound_L Y hd a e τ hY hτ hw, fzone_bound_Z Y hd a e τ hY hτ hw, fun j hj => (hw.1 j hj).trans (by linarith)⟩

omit [NeZero d] in
/-- **Every coordinate of a point of the region is within `6 D` of twice the reference point's.** [folklore] -/
theorem fzone_bound (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {w : Site d} (hw : w ∈ fzone Y hd a e τ) (i : Fin d) :
    |w i - 2 * fzoneCentre Y hd a e i| ≤ 6 * Y.Df := by
  obtain ⟨b1, b2, b3, b4⟩ := fzone_bounds Y hd a e τ hY hτ hw
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have b1' : |Uc hd e.1 w - 2 * Y.ctr (ftgt a e) e.1| ≤ 6 * Y.Df := by
    rw [show (sgOf e : ℤ) * Uc hd e.1 w - 2 * ((sgOf e : ℤ) * Y.ctr (ftgt a e) e.1) = (sgOf e : ℤ) * (Uc hd e.1 w - 2 * Y.ctr (ftgt a e) e.1) by ring,
      abs_mul, hs1, one_mul] at b1
    exact b1
  -- the two diagonal coordinates, whichever is `e`'s axis
  have hboth : |Uc hd 0 w - 2 * Y.ctr (ftgt a e) 0| ≤ 6 * Y.Df ∧ |Uc hd 1 w - 2 * Y.ctr (ftgt a e) 1| ≤ 6 * Y.Df := by
    have hlat : (latDir e true).1 = ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ := rfl
    rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with he | he
    · have hl : (latDir e true).1 = 1 := by rw [hlat]; apply Fin.ext; simp [he]
      rw [he] at b1'; rw [hl] at b2; exact ⟨b1', b2⟩
    · have hl : (latDir e true).1 = 0 := by rw [hlat]; apply Fin.ext; simp [he]
      rw [he] at b1'; rw [hl] at b2; exact ⟨b2, b1'⟩
  obtain ⟨c0, c1⟩ := hboth
  have d0 := abs_le.1 c0; have d1 := abs_le.1 c1
  unfold fzoneCentre
  have hU0 : Uc hd 0 w = w (pl hd 0) + w (pl hd 1) := by unfold Uc; simp
  have hU1 : Uc hd 1 w = w (pl hd 0) - w (pl hd 1) := by unfold Uc; simp; ring
  have hc0 : Y.ctr (ftgt a e) 0 = ftgt a e 0 * (2 * Y.Df) := rfl
  have hc1 : Y.ctr (ftgt a e) 1 = ftgt a e 1 * (2 * Y.Df) := rfl
  rw [hU0, hc0] at d0; rw [hU1, hc1] at d1
  by_cases h0 : i = pl hd 0
  · subst h0; rw [if_pos rfl, abs_le]; constructor <;> linarith
  by_cases h1 : i = pl hd 1
  · subst h1; rw [if_neg h0, if_pos rfl, abs_le]; constructor <;> linarith
  by_cases hz : i = ax0 hd
  · subst hz; rw [if_neg h0, if_neg h1, mul_zero, sub_zero]; exact b3
  · rw [if_neg h0, if_neg h1, mul_zero, sub_zero]; exact b4 i ⟨h0, h1, hz⟩

/-- **A placed plate whose box lies in the region has its support in the zone.**
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem suppP_subset_fzoneF (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {β : BrickPos d} (hβ : boxOf Y.L Y.H β ⊆ fzone Y hd a e τ) :
    suppP Y.m Y.L Y.H β ⊆ fzoneF Y hd a e τ := by
  intro z hz
  have hL1 : 1 ≤ Y.L := by have := hY.hL; omega
  have hzE : z ∈ (zdGraph d).edgeSet := suppP_subset_edgeSet hL1 β hz
  have hdm : dmid z ∈ fzone Y hd a e τ := hβ (dmid_mem_boxOf_of_mem_suppP hY.hL hY.hH β hz)
  rw [mem_fzoneF]
  refine ⟨hzE, fun x hx => ?_, hdm⟩
  unfold fvbox
  rw [Finset.mem_image]
  refine ⟨x - fzoneCentre Y hd a e, ?_, sub_add_cancel _ _⟩
  rw [mem_box]
  intro i
  have h1 := abs_le.1 (abs_two_mul_sub_dmid_le hzE hx i)
  have h2 := abs_le.1 (fzone_bound Y hd a e τ hY hτ hdm i)
  have hD0 : 0 ≤ Y.Df := by unfold FlatLayout.Df FlatLayout.U; positivity
  rw [Pi.sub_apply, fzoneRad_eq]
  constructor <;> linarith

end Finite

/-- **The support of every plate of an invariant state of an admissible attempt lies in the zone.**
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem FlatInv.suppP_subset_fzoneF {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}
    (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {r : BrickRec d} (hr : r ∈ st.all) :
    suppP Y.m Y.L Y.H r.1 ⊆ fzoneF Y hd a e τ :=
  BGNd.suppP_subset_fzoneF Y hd a e τ hY hτ (boxOf_subset_fzone hI hY hτ hr)

end BGNd

end Percolation.Literature

end

/-!
# Part 4 (The flat gait, XXVI): the initial tokens and the initial open set

The start of the block construction with the flat gait
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3 p. 171, case `H < L`): the initial token of the
origin cell towards each macro-direction `e` (`initPosF`, `initTokF`) — `U` before the face of the
origin cell along the diagonal of `e`, `U` off the lane, at the height of the layer of `rev e`, on
the plane axis `u₂` — and the initial open set `U₀` (`U0F`): the four seed squares and, for each, a
lattice path from the origin (up, along `u₂`, along `u₃`; `initPathF`). We prove that the initial
tokens are admissible (`ftAdm_init`), that `U₀` consists of lattice edges (`U0F_subset_edgeSet`), and
that when `U₀` is open the initial seeds are open and joined to the origin (`init_connF`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 p. 171.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

section Init

variable (Y : FlatLayout) (hd : 3 ≤ d)

/-- The sign relating the second plane coordinate to the diagonal of macro-axis `i`: `u_c(i) = x₂ + ι x₃`. [folklore] -/
def iotaOf (e : MDir) : ℤ := if e.1 = 0 then 1 else -1

/-- **The initial token position** towards `e`: plane coordinates `s (D + Λ)/2 = 2688 s U` and
`ι s ((D - Λ)/2 - U) = 1407 ι s U` (so forward `s (D - U)`, lateral `s Λ + s U`), height the layer
of `rev e`, idle coordinates `0`. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def initPosF (e : MDir) : Site d := fun i =>
  if i = pl hd 0 then (sgOf e : ℤ) * (2688 * Y.U) else if i = pl hd 1 then iotaOf e * ((sgOf e : ℤ) * (1407 * Y.U))
    else if i = ax0 hd then Y.zOf (rev e) else 0

/-- The initial token towards `e`: at the initial position, on the plane axis `u₂`, with the nominal
provenance `rev e`. [folklore] -/
def initTokF (e : MDir) : TTok d := ⟨initPosF Y hd e, pl hd 0, some (rev e)⟩

/-- The corners of the initial path towards `e`: above the origin, and at the end of the `u₂` leg. [folklore] -/
def initQ1 (e : MDir) : Site d := shift 0 (ax0 hd) (Y.zOf (rev e))
/-- The second corner. [folklore] -/
def initQ2 (e : MDir) : Site d := shift (initQ1 Y hd e) (pl hd 0) ((sgOf e : ℤ) * (2688 * Y.U))

/-- The edges of the initial path towards `e`: up, along `u₂`, along `u₃`. [folklore] -/
def initPathF (e : MDir) : Finset (Sym2 (Site d)) :=
  segEdges 0 (ax0 hd) (Y.zOf (rev e)).toNat true ∪
    segEdges (initQ1 Y hd e) (pl hd 0) (2688 * Y.U).toNat e.2 ∪
    segEdges (initQ2 Y hd e) (pl hd 1) (1407 * Y.U).toNat (decide (0 ≤ iotaOf e * (sgOf e : ℤ)))

/-- **The initial open set `U₀`**: the four initial seed squares and the four paths. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def U0F : Finset (Sym2 (Site d)) :=
  Finset.univ.biUnion fun e : MDir => sqEdgesAt (pl hd 0) Y.m (initPosF Y hd e) ∪ initPathF Y hd e

omit [NeZero d] in
/-- `U₀` consists of lattice edges. [folklore] -/
theorem U0F_subset_edgeSet : (↑(U0F Y hd) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro z hz
  rw [Finset.mem_coe, U0F, Finset.mem_biUnion] at hz
  obtain ⟨e, -, hz⟩ := hz
  rw [Finset.mem_union] at hz
  rcases hz with hz | hz
  · exact sqEdgesAt_subset_edgeSet _ _ _ hz
  · rw [initPathF, Finset.mem_union, Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz <;> exact segEdges_subset_edgeSet _ _ _ _ hz

omit [NeZero d] in
/-- The layers are nonnegative. [folklore] -/
theorem zOf_nonneg (e : MDir) : 0 ≤ Y.zOf e := by
  have hU : 0 ≤ Y.U := by unfold FlatLayout.U; positivity
  unfold FlatLayout.zOf FlatLayout.Wl
  have : (0 : ℤ) ≤ (TallLayout.layerIdx e : ℤ) := by positivity
  positivity

omit [NeZero d] in
/-- The end of the initial path is the initial position. [folklore] -/
theorem initPathF_end (e : MDir) :
    shift (initQ2 Y hd e) (pl hd 1) (if decide (0 ≤ iotaOf e * (sgOf e : ℤ)) then (((1407 * Y.U).toNat : ℕ) : ℤ) else -(((1407 * Y.U).toNat : ℕ) : ℤ)) =
      initPosF Y hd e := by
  have hU : 0 ≤ Y.U := by unfold FlatLayout.U; positivity
  rw [Int.toNat_of_nonneg (by positivity)]
  have hιs : iotaOf e * (sgOf e : ℤ) = 1 ∨ iotaOf e * (sgOf e : ℤ) = -1 := by
    unfold iotaOf; rcases Int.units_eq_one_or (sgOf e) with h | h <;> by_cases h0 : e.1 = 0 <;> simp [h, h0]
  ext j
  unfold initPosF initQ2 initQ1
  have h01 : pl hd (0 : Fin 2) ≠ pl hd 1 := pl_ne_pl hd (by decide)
  by_cases h1 : j = pl hd 1
  · subst h1
    rw [shift_apply_self, shift_apply_of_ne _ h01.symm, shift_apply_of_ne _ (pl_ne_ax0 hd 1), if_neg h01.symm, if_pos rfl]
    simp only [Pi.zero_apply, zero_add]
    rcases hιs with h | h
    · rw [if_pos (by rw [h]; decide), show iotaOf e * ((sgOf e : ℤ) * (1407 * Y.U)) = (iotaOf e * (sgOf e : ℤ)) * (1407 * Y.U) by ring, h, one_mul]
    · rw [if_neg (by rw [h]; decide), show iotaOf e * ((sgOf e : ℤ) * (1407 * Y.U)) = (iotaOf e * (sgOf e : ℤ)) * (1407 * Y.U) by ring, h]; ring
  by_cases h0 : j = pl hd 0
  · subst h0
    rw [shift_apply_of_ne _ h01, shift_apply_self, shift_apply_of_ne _ (pl_ne_ax0 hd 0), if_pos rfl]
    simp
  by_cases h3 : j = ax0 hd
  · subst h3
    rw [shift_apply_of_ne _ (pl_ne_ax0 hd 1).symm, shift_apply_of_ne _ (pl_ne_ax0 hd 0).symm, shift_apply_self, if_neg h0, if_neg h1, if_pos rfl]
    simp
  · rw [shift_apply_of_ne _ h1, shift_apply_of_ne _ h0, shift_apply_of_ne _ h3, if_neg h0, if_neg h1, if_neg h3]; simp

omit [NeZero d] in
/-- The end of the `u₂` leg is the second corner. [folklore] -/
theorem initQ2_eq (e : MDir) :
    shift (initQ1 Y hd e) (pl hd 0) (if e.2 then (((2688 * Y.U).toNat : ℕ) : ℤ) else -(((2688 * Y.U).toNat : ℕ) : ℤ)) = initQ2 Y hd e := by
  have hU : 0 ≤ Y.U := by unfold FlatLayout.U; positivity
  rw [Int.toNat_of_nonneg (by positivity)]
  unfold initQ2 sgOf
  cases e.2 <;> simp

omit [NeZero d] in
/-- **When `U₀` is open, the initial seeds are open and joined to the origin.** [cite: GrimmettPercolation1999, §7.3 p. 171] -/
theorem init_connF {ω : BondConfig (Site d)} (hω : (↑(U0F Y hd) : Set (Sym2 (Site d))) ⊆ ω) (e : MDir) :
    IsSeed ω (square (pl hd 0) Y.m (initPosF Y hd e)) ∧ (openGraph ω).Reachable 0 (initPosF Y hd e) := by
  have hsub : ∀ z, z ∈ sqEdgesAt (pl hd 0) Y.m (initPosF Y hd e) ∪ initPathF Y hd e → z ∈ ω := fun z hz =>
    hω (by rw [Finset.mem_coe, U0F, Finset.mem_biUnion]; exact ⟨e, Finset.mem_univ _, hz⟩)
  refine ⟨isSeed_of_sqEdgesAt_subset fun z hz => hsub z (Finset.mem_union_left _ hz), ?_⟩
  have h1 : (openGraph ω).Reachable 0 (initQ1 Y hd e) := by
    have := reachable_of_segEdges_subset (ω := ω) (x := (0 : Site d)) (i := ax0 hd) (n := (Y.zOf (rev e)).toNat) (pos := true)
      fun z hz => hsub z (by rw [initPathF]; exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hz)))
    simp only [↓reduceIte] at this
    rwa [Int.toNat_of_nonneg (zOf_nonneg Y (rev e))] at this
  have h2 : (openGraph ω).Reachable (initQ1 Y hd e) (initQ2 Y hd e) := by
    have := reachable_of_segEdges_subset (ω := ω) (x := initQ1 Y hd e) (i := pl hd 0) (n := (2688 * Y.U).toNat) (pos := e.2)
      fun z hz => hsub z (by rw [initPathF]; exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz)))
    rwa [initQ2_eq Y hd e] at this
  have h3 : (openGraph ω).Reachable (initQ2 Y hd e) (initPosF Y hd e) := by
    have := reachable_of_segEdges_subset (ω := ω) (x := initQ2 Y hd e) (i := pl hd 1) (n := (1407 * Y.U).toNat)
      (pos := decide (0 ≤ iotaOf e * (sgOf e : ℤ)))
      fun z hz => hsub z (by rw [initPathF]; exact Finset.mem_union_right _ (Finset.mem_union_right _ hz))
    rwa [initPathF_end Y hd e] at this
  exact h1.trans (h2.trans h3)

omit [NeZero d] in
/-- **The initial tokens are admissible** for the attempts of the origin cell. [folklore] -/
theorem ftAdm_init (hY : Y.OK) (e : MDir) : FTAdm hd Y 0 e (initTokF Y hd e) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have h01 : pl hd (0 : Fin 2) ≠ pl hd 1 := pl_ne_pl hd (by decide)
  have hp0 : (initTokF Y hd e).pos (pl hd 0) = (sgOf e : ℤ) * (2688 * Y.U) := by simp [initTokF, initPosF]
  have hp1 : (initTokF Y hd e).pos (pl hd 1) = iotaOf e * ((sgOf e : ℤ) * (1407 * Y.U)) := by
    simp [initTokF, initPosF, h01.symm]
  have hpz : (initTokF Y hd e).pos (ax0 hd) = Y.zOf (rev e) := by
    simp [initTokF, initPosF, (pl_ne_ax0 hd 0).symm, (pl_ne_ax0 hd 1).symm]
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hctr : ∀ i, Y.ctr 0 i = 0 := fun i => by simp [FlatLayout.ctr]
  have hlane : Y.lane 0 e = (sgOf e : ℤ) * Y.lam := by
    simp [FlatLayout.lane, FlatLayout.ctr, FlatLayout.nu, TallLayout.cpar]
  have hUpar : Uc hd e.1 (initTokF Y hd e).pos = (sgOf e : ℤ) * (4095 * Y.U) := by
    unfold Uc; rw [hp0, hp1]; unfold iotaOf
    rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h | h <;> simp [h] <;> ring
  have hUlat : Uc hd (latDir e true).1 (initTokF Y hd e).pos = (sgOf e : ℤ) * (1281 * Y.U) := by
    unfold Uc; rw [hp0, hp1]; unfold iotaOf latDir
    rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h | h <;> simp [h] <;> ring
  refine ⟨Or.inl rfl, ?_, ?_, fun d' hd' => ?_, fun i hi => ?_, by simp [initTokF]⟩
  · rw [hUpar, hctr, sub_zero, ← mul_assoc, hss, one_mul]
    unfold FlatLayout.Df; constructor <;> linarith
  · rw [hUlat, hlane, ← mul_sub, abs_mul]
    have : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    rw [this, one_mul]; unfold FlatLayout.lam FlatLayout.ρp
    rw [show 1281 * Y.U - 1280 * Y.U = Y.U by ring, abs_of_pos hU]; linarith
  · simp only [initTokF, Option.some.injEq] at hd'
    subst hd'; rw [hpz, sub_self, abs_zero]; unfold FlatLayout.ρv; positivity
  · obtain ⟨hi0, hi1, hiz⟩ := hi
    simp [initTokF, initPosF, hi0, hi1, hiz, hLp0]

end Init

end BGNd

end Percolation.Literature

end

/-!
# Part 5 (The flat gait, XXVII): the block kit

The block kit (`BlockKit.Kit`) assembled from the flat
gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): tokens `TTok`,
the plan `flatNext'` with outcome `flatFinish'`, admissibility `FTAdm`, the macro-cell map
`FlatLayout.cellOf`, the finite zone `fzoneF`, the initial tokens and `U₀`, budget
`R = 2¹⁵` (`flatKit`; the cell of an admissible token by the window lemma `ediv_window` of the tall
kit); admissible tokens are the geometrically admissible ones, the nominal
provenance `rev e` being reserved to the initial tokens. The direction of an admissible token is
read off its position (`fdirTok`); the provenance reported to the renormalisation (`srcDirF`) is
the token's source except that the nominal provenance of the initial tokens is reported as none.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-- **The direction of a token**, read off its position: the macro-axis along which it is within
`2U` of a face of its cell, and the side of the centre it lies on (meaningful for admissible
tokens: `fdirTok τ = e` when `FTAdm a e τ`). [folklore] -/
def fdirTok (Y : FlatLayout) (hd : 3 ≤ d) (τ : TTok d) : MDir :=
  let c := Y.cellOf hd τ.pos
  let i : Fin 2 := if Y.Df - 2 * Y.U ≤ |Uc hd 0 τ.pos - Y.ctr c 0| then 0 else 1
  (i, decide (Y.ctr c i < Uc hd i τ.pos))

/-- **The provenance reported to the renormalisation**: the token's source direction, except that
the nominal provenance `rev e` of the initial tokens (never the provenance of a token handed on by a
run, whose onward directions exclude the reverse) is reported as none. [folklore] -/
def srcDirF (Y : FlatLayout) (hd : 3 ≤ d) (τ : TTok d) : Option MDir :=
  match τ.src with
  | none => none
  | some d' => if d' = rev (fdirTok Y hd τ) then none else some d'

/-- **The block kit of the flat gait.** [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
def flatKit (Y : FlatLayout) (hd : 3 ≤ d) (hY : Y.OK) : Kit d where
  Tok := TTok d
  anchor := TTok.pos
  ax := TTok.ax
  srcDir := srcDirF Y hd
  init := initTokF Y hd
  U₀ := U0F Y hd
  Adm := fun a e τ => FTAdm hd Y a e τ ∧ (τ.src = some (rev e) → a = 0 ∧ τ = initTokF Y hd e)
  cell := Y.cellOf hd
  zone := fun a e τ => fzoneF Y hd a e τ
  next := fun a e τ => flatNext' hd Y hY.hL hY.hH a e τ
  finish := fun a e τ => flatFinish' hd Y hY.hL hY.hH a e τ
  R := FlatLayout.Rmax

section Simp

variable (Y : FlatLayout) (hd : 3 ≤ d) (hY : Y.OK)

/-- Unfolding the kit. [folklore] -/
@[simp] theorem flatKit_Tok : (flatKit Y hd hY).Tok = TTok d := rfl
/-- Unfolding the kit. [folklore] -/
@[simp] theorem flatKit_R : (flatKit Y hd hY).R = FlatLayout.Rmax := rfl
/-- Unfolding the kit. [folklore] -/
theorem flatKit_next (a : Site 2) (e : MDir) (τ : TTok d) (h : BrickHist d) :
    (flatKit Y hd hY).next a e τ h = flatNext' hd Y hY.hL hY.hH a e τ h := rfl
/-- Unfolding the kit. [folklore] -/
theorem flatKit_finish (a : Site 2) (e : MDir) (τ : TTok d) (h : BrickHist d) :
    (flatKit Y hd hY).finish a e τ h = flatFinish' hd Y hY.hL hY.hH a e τ h := rfl
/-- Unfolding the kit. [folklore] -/
theorem flatKit_zone (a : Site 2) (e : MDir) (τ : TTok d) : (flatKit Y hd hY).zone a e τ = fzoneF Y hd a e τ := rfl
/-- Unfolding the kit. [folklore] -/
theorem flatKit_Adm (a : Site 2) (e : MDir) (τ : TTok d) :
    (flatKit Y hd hY).Adm a e τ ↔ FTAdm hd Y a e τ ∧ (τ.src = some (rev e) → a = 0 ∧ τ = initTokF Y hd e) := Iff.rfl
/-- Unfolding the kit. [folklore] -/
theorem flatKit_srcDir (τ : TTok d) : (flatKit Y hd hY).srcDir τ = srcDirF Y hd τ := rfl
/-- Unfolding the kit. [folklore] -/
theorem flatKit_init (e : MDir) : (flatKit Y hd hY).init e = initTokF Y hd e := rfl
/-- Unfolding the kit. [folklore] -/
theorem flatKit_U0 : (flatKit Y hd hY).U₀ = U0F Y hd := rfl

end Simp

/-! ## The direction and the cell of an admissible token -/

section Dir

variable (Y : FlatLayout) (hd : 3 ≤ d)

omit [NeZero d] in
/-- **An admissible token lies in its cell.** [folklore] -/
theorem FTAdm.cellOf_eq (hY : Y.OK) {c : Site 2} {e' : MDir} {tok : TTok d} (h : FTAdm hd Y c e' tok) : Y.cellOf hd tok.pos = c := by
  obtain ⟨hU, -⟩ := hY.facts
  have hD0 : 0 < Y.Df := by unfold FlatLayout.Df; positivity
  obtain ⟨hlo, hhi⟩ := h.longit
  have hlat := abs_le.1 h.lateral
  have hs : (sgOf e' : ℤ) = 1 ∨ (sgOf e' : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e') with h' | h' <;> simp [h']
  have hcp : TallLayout.cpar c = 0 ∨ TallLayout.cpar c = 1 := by unfold TallLayout.cpar; omega
  funext i
  unfold FlatLayout.cellOf
  by_cases hi : i = e'.1
  · subst hi
    unfold FlatLayout.ctr at hlo hhi
    have : Uc hd e'.1 tok.pos + Y.Df = (Uc hd e'.1 tok.pos - c e'.1 * (2 * Y.Df) + Y.Df) + 2 * Y.Df * c e'.1 := by ring
    rw [this]
    apply ediv_window hD0
    · rcases hs with h' | h' <;> rw [h'] at hlo hhi <;> unfold FlatLayout.Df at * <;> linarith
    · rcases hs with h' | h' <;> rw [h'] at hlo hhi <;> unfold FlatLayout.Df at * <;> linarith
  · have hi' : i = (latDir e' true).1 := by
      rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h0 | h0 <;> rcases Fin.exists_fin_two.1 ⟨e'.1, rfl⟩ with h1 | h1 <;>
        simp_all [latDir]
    rw [hi'] at hi ⊢
    unfold FlatLayout.lane FlatLayout.ctr FlatLayout.nu at hlat
    have : Uc hd (latDir e' true).1 tok.pos + Y.Df =
        (Uc hd (latDir e' true).1 tok.pos - c (latDir e' true).1 * (2 * Y.Df) + Y.Df) + 2 * Y.Df * c (latDir e' true).1 := by ring
    rw [this]
    apply ediv_window hD0
    · rcases hs with h' | h' <;> rw [h'] at hlat <;> rcases hcp with hc | hc <;> rw [hc] at hlat <;>
        unfold FlatLayout.Df FlatLayout.lam FlatLayout.lamJ FlatLayout.ρp at * <;> linarith
    · rcases hs with h' | h' <;> rw [h'] at hlat <;> rcases hcp with hc | hc <;> rw [hc] at hlat <;>
        unfold FlatLayout.Df FlatLayout.lam FlatLayout.lamJ FlatLayout.ρp at * <;> linarith

omit [NeZero d] in
/-- **The direction of an admissible token is the direction of its attempt.** [folklore] -/
theorem FTAdm.fdirTok_eq (hY : Y.OK) {c : Site 2} {e' : MDir} {tok : TTok d} (h : FTAdm hd Y c e' tok) : fdirTok Y hd tok = e' := by
  obtain ⟨hU, -⟩ := hY.facts
  obtain ⟨hlo, hhi⟩ := h.longit
  have hlat := abs_le.1 h.lateral
  have hs : (sgOf e' : ℤ) = 1 ∨ (sgOf e' : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e') with h' | h' <;> simp [h']
  have hcp : TallLayout.cpar c = 0 ∨ TallLayout.cpar c = 1 := by unfold TallLayout.cpar; omega
  have hDf : Y.Df = 4096 * Y.U := rfl
  unfold fdirTok
  rw [h.cellOf_eq Y hd hY]
  -- the macro-axis
  have hax : (if Y.Df - 2 * Y.U ≤ |Uc hd 0 tok.pos - Y.ctr c 0| then (0 : Fin 2) else 1) = e'.1 := by
    rcases Fin.exists_fin_two.1 ⟨e'.1, rfl⟩ with h1 | h1
    · rw [h1] at hlo hhi
      rw [if_pos, h1]
      rcases hs with h' | h' <;> rw [h'] at hlo hhi
      · simp only [one_mul] at hlo hhi; rw [abs_of_nonneg (by linarith)]; linarith
      · simp only [neg_mul, one_mul] at hlo hhi; rw [abs_of_nonpos (by linarith)]; linarith
    · have hl : (latDir e' true).1 = 0 := by
        apply Fin.ext; simp only [latDir]; rw [h1]; rfl
      unfold FlatLayout.lane FlatLayout.nu at hlat
      rw [hl] at hlat
      rw [if_neg, h1]
      rw [not_le, abs_lt]
      rcases hs with h' | h' <;> rw [h'] at hlat <;> rcases hcp with hc | hc <;> rw [hc] at hlat <;>
        unfold FlatLayout.Df FlatLayout.lam FlatLayout.lamJ FlatLayout.ρp at * <;> constructor <;> linarith
  simp only [hax]
  -- the sign
  have hsg : decide (Y.ctr c e'.1 < Uc hd e'.1 tok.pos) = e'.2 := by
    unfold sgOf at hlo hhi
    cases h2 : e'.2 <;> simp only [h2] at hlo hhi <;> simp only [decide_eq_false_iff_not, decide_eq_true_eq, not_lt] <;>
      push_cast at hlo hhi <;> unfold FlatLayout.Df at * <;> linarith
  rw [hsg]

omit [NeZero d] in
/-- **The provenance of an admissible handed-on token**: a token of an attempt along `e'` with
source `e ≠ rev e'` reports `some e`. [folklore] -/
theorem FTAdm.srcDirF_eq (hY : Y.OK) {c : Site 2} {e e' : MDir} {tok : TTok d} (h : FTAdm hd Y c e' tok) (hsrc : tok.src = some e)
    (hne : e' ≠ rev e) : srcDirF Y hd tok = some e := by
  unfold srcDirF
  rw [hsrc]
  simp only
  rw [h.fdirTok_eq Y hd hY, if_neg]
  intro h'; apply hne; rw [h', rev_rev]

omit [NeZero d] in
/-- The initial tokens report no provenance. [folklore] -/
theorem srcDirF_init (hY : Y.OK) (e : MDir) : srcDirF Y hd (initTokF Y hd e) = none := by
  unfold srcDirF
  have : (initTokF Y hd e).src = some (rev e) := rfl
  rw [this]
  simp only
  rw [(ftAdm_init Y hd hY e).fdirTok_eq Y hd hY, if_pos rfl]

end Dir

end BGNd

end Percolation.Literature

end
