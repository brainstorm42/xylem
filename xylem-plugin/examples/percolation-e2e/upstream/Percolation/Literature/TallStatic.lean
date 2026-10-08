import Percolation.Literature.TallRun5
import Percolation.Util.Linter

/-!
# The tall gait, XXII: static disjointness of the zones

The static obligations of the tall kit (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 p. 173 (C), "the new bricks use no edge examined previously"):
the zone of an admissible token lies in the core of its target cell together with a small *poke*
back into the source cell (the start of the entry leg, on the token's layer); cores of distinct
cells, pokes at distinct faces, and pokes versus foreign cores are disjoint in plan; two zones with
the same target are separated by the lane design (entry parts) and by the layers (tubes); a zone
aimed at the source cell of another avoids its poke by the layers.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 170–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## Frames: the two plane axes seen from a direction -/

section Frame

variable (hd : 3 ≤ d)

omit [NeZero d] in
/-- Directions along the same macro-axis have the same fine axes. [folklore] -/
theorem axes_of_fst_eq {e e' : MDir} (h : e'.1 = e.1) :
    axOf hd e' = axOf hd e ∧ latOf hd e' = latOf hd e ∧ (latDir e' true).1 = (latDir e true).1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold axOf; apply Fin.ext; simp only [h]
  · unfold latOf; apply Fin.ext; simp only [h]
  · simp only [latDir, h]

omit [NeZero d] in
/-- Directions along different macro-axes exchange the fine axes. [folklore] -/
theorem axes_of_fst_ne {e e' : MDir} (h : e'.1 ≠ e.1) :
    axOf hd e' = latOf hd e ∧ latOf hd e' = axOf hd e ∧ (latDir e' true).1 = e.1 ∧ e'.1 = (latDir e true).1 := by
  have h1 := e.1.isLt; have h2 := e'.1.isLt
  have h3 : e'.1.val ≠ e.1.val := fun h' => h (Fin.ext h')
  have hv : e'.1.val = 1 - e.1.val := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold axOf latOf; apply Fin.ext; simp only; omega
  · unfold axOf latOf; apply Fin.ext; simp only; omega
  · simp only [latDir]; apply Fin.ext; simp only; omega
  · simp only [latDir]; apply Fin.ext; simp only; omega

omit [NeZero d] in
/-- A direction is determined by its macro-axis and its sign. [folklore] -/
theorem MDir.ext_of {e e' : MDir} (h1 : e'.1 = e.1) (h2 : (sgOf e' : ℤ) = sgOf e) : e' = e := by
  obtain ⟨i, b⟩ := e; obtain ⟨i', b'⟩ := e'
  simp only at h1; subst h1
  cases b <;> cases b' <;> first | rfl | (exfalso; simp [sgOf] at h2)

omit [NeZero d] in
/-- The reverse: same macro-axis, opposite sign. [folklore] -/
theorem eq_rev_of {e e' : MDir} (h1 : e'.1 = e.1) (h2 : (sgOf e' : ℤ) = -sgOf e) : e' = rev e := by
  obtain ⟨i, b⟩ := e; obtain ⟨i', b'⟩ := e'
  simp only at h1; subst h1
  cases b <;> cases b' <;> first | rfl | (exfalso; simp [sgOf] at h2)

omit [NeZero d] in
/-- The sign of the reverse. [folklore] -/
theorem sgOf_rev (e : MDir) : (sgOf (rev e) : ℤ) = -sgOf e := by
  obtain ⟨i, b⟩ := e; cases b <;> rfl

omit [NeZero d] in
/-- The lane offset is the sign times `Λ`. [folklore] -/
theorem nu_eq (Y : TallLayout) (e : MDir) : Y.nu e = (sgOf e : ℤ) * Y.lam := by
  unfold TallLayout.nu sgOf; obtain ⟨i, b⟩ := e; cases b <;> simp

end Frame

/-! ## Cells, targets and centres -/

section Cells

variable (Y : TallLayout)

omit [NeZero d] in
/-- Centres of cells differ by multiples of `2 · D/2`. [folklore] -/
theorem ctr_sub_ctr (c c' : Site 2) (i : Fin 2) : Y.ctr c i - Y.ctr c' i = (c i - c' i) * (2 * Y.Dh) := by
  unfold TallLayout.ctr; ring

omit [NeZero d] in
/-- Distinct cells have a coordinate where they differ. [folklore] -/
theorem exists_ne_of_ne {c c' : Site 2} (h : c ≠ c') : ∃ i, c i ≠ c' i := by
  by_contra h'; push Not at h'; exact h (funext h')

omit [NeZero d] in
/-- The coordinates of the target cell. [folklore] -/
theorem tgtCell_apply (a : Site 2) (e : MDir) (i : Fin 2) : tgtCell a e i = a i + (if i = e.1 then (sgOf e : ℤ) else 0) := by
  unfold tgtCell; rw [Pi.add_apply, stepVec_apply]

omit [NeZero d] in
/-- A source cell is not its own target. [folklore] -/
theorem tgtCell_ne_self (a : Site 2) (e : MDir) : tgtCell a e ≠ a := by
  intro h
  have := congrFun h e.1
  rw [tgtCell_apply, if_pos rfl] at this
  rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> rw [h'] at this <;> simp at this

omit [NeZero d] in
/-- If `tgtCell a' e' = a` with `e' = rev e` then `a' = tgtCell a e`. [folklore] -/
theorem eq_tgtCell_of_rev {a a' : Site 2} {e e' : MDir} (h : tgtCell a' e' = a) (he : e' = rev e) : a' = tgtCell a e := by
  subst he
  funext i
  have := congrFun h i
  rw [tgtCell_apply] at this
  rw [tgtCell_apply]
  have hr : (rev e).1 = e.1 := rfl
  rw [hr, sgOf_rev] at this
  split_ifs at this ⊢ <;> linarith

end Cells

/-! ## Layers are well separated -/

section Layers

variable (Y : TallLayout)

omit [NeZero d] in
/-- The layer index is injective. [folklore] -/
theorem layerIdx_injective : Function.Injective TallLayout.layerIdx := by
  intro e e' h
  obtain ⟨i, b⟩ := e; obtain ⟨i', b'⟩ := e'
  unfold TallLayout.layerIdx at h
  simp only at h
  have hi := i.isLt; have hi' := i'.isLt
  have : i = i' := by apply Fin.ext; cases b <;> cases b' <;> simp at h <;> omega
  subst this
  cases b <;> cases b' <;> simp at h ⊢

omit [NeZero d] in
/-- **Distinct directions have layers at least `W` apart.** [folklore] -/
theorem W_le_abs_zOf_sub (hY : Y.OK) {e e' : MDir} (h : e ≠ e') : Y.Wl ≤ |Y.zOf e - Y.zOf e'| := by
  obtain ⟨-, -, -, hell, hmH, -, -, -, -, -, -, -, -, hWl, -, -, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  have hW0 : 0 ≤ Y.Wl := by rw [hWl]; positivity
  have hne : (TallLayout.layerIdx e : ℤ) ≠ TallLayout.layerIdx e' := by
    intro h'; exact h (layerIdx_injective (by exact_mod_cast h'))
  have : Y.zOf e - Y.zOf e' = ((TallLayout.layerIdx e : ℤ) - TallLayout.layerIdx e') * Y.Wl := by unfold TallLayout.zOf; ring
  rw [this, abs_mul, abs_of_nonneg hW0]
  have h1 : 1 ≤ |(TallLayout.layerIdx e : ℤ) - TallLayout.layerIdx e'| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  nlinarith

omit [NeZero d] in
/-- **Boxes on distinct layers are disjoint in height**: the tube heights (`2ρ_v + K₀`) and the poke
heights (`2ρ_v + 2Δ_w + K₀`) of two distinct layers never meet. [folklore] -/
theorem layers_apart (hY : Y.OK) {e e' : MDir} (h : e ≠ e') {t : ℤ} (h1 : |t - 2 * Y.zOf e| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0)
    (h2 : |t - 2 * Y.zOf e'| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0) : False := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hW := W_le_abs_zOf_sub Y hY h
  have ha := abs_le.1 h1; have hb := abs_le.1 h2
  have hsmall : 2 * (2 * Y.ρv + 2 * Y.Δw + Y.K0) < 2 * Y.Wl := by
    rw [hK0]; linarith only [hWl, hρv, hΔw, hLeq, hLpP, hP2, hPe, hP64, hell, hmH, hLp0]
  rcases le_or_gt 0 (Y.zOf e - Y.zOf e') with hs | hs
  · rw [abs_of_nonneg hs] at hW; linarith only [hW, ha.1, ha.2, hb.1, hb.2, hsmall]
  · rw [abs_of_neg hs] at hW; linarith only [hW, ha.1, ha.2, hb.1, hb.2, hsmall]

end Layers

/-! ## The constants of the shapes -/

namespace TallLayout

variable {Y : TallLayout}

/-- Depth of the entry parts (`A`, `R`, `J`) beyond the token's plane, doubled. [folklore] -/
def DE (Y : TallLayout) : ℤ := 2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0
/-- Lateral half-width of the entry parts around their lane, doubled. [folklore] -/
def ΓE (Y : TallLayout) : ℤ := 2 * Y.ρp + 2 * Y.Lp + 2 * Y.Δw + 4 * Y.lamJ + 2 * Y.m + 2 * Y.H + 6 + Y.K0
/-- Lateral half-width of the trunk tube around the lane, doubled. [folklore] -/
def ΓT (Y : TallLayout) : ℤ := 4 * Y.lamJ + 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw + Y.K0
/-- Longitudinal half-width of a branch tube around its port lane, doubled. [folklore] -/
def ΓB (Y : TallLayout) : ℤ := 2 * Y.lamJ + 2 * Y.ell + 2 * Y.H + 2 * Y.Lp + Y.K0
/-- Lateral half-width of the poke around the cell's centre line, doubled. [folklore] -/
def ΓP (Y : TallLayout) : ℤ := 2 * Y.lam + 2 * Y.lamJ + 2 * Y.ρp + 2 * Y.Lp + 2 * Y.Δw + Y.K0

/-- **The shape constants are small against the cell and the lane separations.** [folklore] -/
theorem OK.shapes (h : Y.OK) :
    0 ≤ Y.DE ∧ 0 ≤ Y.ΓE ∧ 0 ≤ Y.ΓT ∧ 0 ≤ Y.ΓB ∧ 0 ≤ Y.ΓP ∧ 0 ≤ Y.lam ∧ 0 ≤ Y.lamJ ∧ 1 ≤ Y.ell ∧
      Y.DE + 2 * Y.lam + 2 * Y.lamJ + Y.ΓE + Y.ΓT + Y.ΓB + Y.ΓP + 4 * Y.ell + 8 ≤ 2 * Y.Dh ∧
      Y.ΓE + Y.ΓT + 2 ≤ 4 * Y.lam ∧ Y.ΓE + Y.ΓB + 2 ≤ 4 * Y.lam ∧
      2 * Y.Pw * Y.ell + 2 * Y.m + 2 - Y.K0 ≥ 2 * Y.ell + 2 ∧ 2 * Y.Pw * Y.ell - Y.K0 ≥ 2 * Y.ell + 2 := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := h.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hN0 : (0 : ℤ) ≤ Y.N₁ * Y.Lp := by positivity
  unfold DE ΓE ΓT ΓB ΓP
  rw [hK0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hPwe, hPe, hell, hmH, hN0, hLp0, hLeq, hm0]
  · linarith only [hρp, hΔ0, hlamJ, hP64, hP2, hPe, hell, hmH, hLp0, hLeq, hm0]
  · linarith only [hΔ0, hlamJ, hP64, hP2, hPe, hell, hmH, hLp0, hLeq, hm0]
  · linarith only [hlamJ, hP64, hP2, hPe, hell, hmH, hLp0, hLeq, hm0]
  · linarith only [hlam, hlamJ, hρp, hΔ0, hP64, hP2, hPe, hell, hmH, hLp0, hLeq, hm0]
  · rw [hlam]; positivity
  · rw [hlamJ]; positivity
  · linarith only [hell, hmH]
  · linarith only [hDh, hPwe, hNL, hlam, hlamJ, hρp, hΔw, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  · linarith only [hlam, hlamJ, hρp, hΔw, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  · linarith only [hlam, hlamJ, hρp, hΔw, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  · linarith only [hPwe, hLeq, hLpP, hPe, hell, hmH, hm0, hLp0]
  · linarith only [hPwe, hLeq, hLpP, hPe, hell, hmH, hm0, hLp0]

end TallLayout

/-! ## The shapes of a zone -/

section Shapes

variable (Y : TallLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d)

/-- The doubled face coordinate of the source cell towards `e`, in the oriented coordinate `u = s w_e`. [folklore] -/
def Fc : ℤ := 2 * ((sgOf e : ℤ) * Y.ctr a e.1) + 2 * Y.Dh

/-- **The core of a cell**: doubled plane coordinates within `2 · D/2 - 2` of twice the centre. [folklore] -/
def Core (c : Site 2) : Set (Site d) := {w | ∀ e' : MDir, |w (axOf hd e') - 2 * Y.ctr c e'.1| ≤ 2 * Y.Dh - 2}

/-- **The poke** of a zone back into its source cell: just behind the face, near the centre line,
on the token's layer. [folklore] -/
def Poke : Set (Site d) :=
  {w | Fc Y a e - 2 * Y.ell + 1 ≤ (sgOf e : ℤ) * w (axOf hd e) ∧ (sgOf e : ℤ) * w (axOf hd e) ≤ Fc Y a e + 1 ∧
    |w (latOf hd e) - 2 * Y.ctr a (latDir e true).1| ≤ Y.ΓP ∧ |w (ax0 hd) - 2 * Y.zOf (τ.src.getD e)| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0}

/-- The entry shape (plane bounds of the `A`, `R`, `J` parts). [folklore] -/
def EntryP (w : Site d) : Prop :=
  (sgOf e : ℤ) * w (axOf hd e) ≤ Fc Y a e + Y.DE ∧ |w (latOf hd e) - (2 * Y.ctr a (latDir e true).1 + 2 * Y.nu e)| ≤ Y.ΓE

/-- The trunk-tube shape. [folklore] -/
def TubeTP (w : Site d) : Prop :=
  Fc Y a e + 2 ≤ (sgOf e : ℤ) * w (axOf hd e) ∧ (sgOf e : ℤ) * w (axOf hd e) ≤ Fc Y a e + 4 * Y.Dh - 2 ∧
    |w (latOf hd e) - (2 * Y.ctr a (latDir e true).1 + 2 * Y.nu e)| ≤ Y.ΓT ∧ |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0

/-- The branch-tube shape of sign `w'`. [folklore] -/
def TubeBP (w' : ℤˣ) (w : Site d) : Prop :=
  |(sgOf e : ℤ) * w (axOf hd e) - (Fc Y a e + 2 * Y.Dh) - 2 * ((sgOf e : ℤ) * (w' : ℤ)) * Y.lam| ≤ Y.ΓB ∧
    -(4 * Y.lamJ + 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw) ≤ (w' : ℤ) * (w (latOf hd e) - (2 * Y.ctr a (latDir e true).1 + 2 * Y.nu e)) ∧
    (w' : ℤ) * (w (latOf hd e) - 2 * Y.ctr a (latDir e true).1) ≤ 2 * Y.Dh - 2 ∧ |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0

omit [NeZero d] in
/-- Membership in a core from the two plane bounds seen from `e`. [folklore] -/
theorem mem_core {c : Site 2} {w : Site d} (hu : |w (axOf hd e) - 2 * Y.ctr c e.1| ≤ 2 * Y.Dh - 2)
    (hv : |w (latOf hd e) - 2 * Y.ctr c (latDir e true).1| ≤ 2 * Y.Dh - 2) : w ∈ Core Y hd c := by
  intro e'
  by_cases h : e'.1 = e.1
  · obtain ⟨h1, -, -⟩ := axes_of_fst_eq hd h; rw [h1, h]; exact hu
  · obtain ⟨h1, -, -, h4⟩ := axes_of_fst_ne hd h; rw [h1, h4]; exact hv

omit [NeZero d] in
/-- Along the axis: a `u`-window inside the core. [folklore] -/
theorem abs_u_core {s : ℤ} (hs : s = 1 ∨ s = -1) {x X F D : ℤ} (hX : 2 * (s * X) = F + 2 * D) (h1 : F + 2 ≤ s * x)
    (h2 : s * x ≤ F + 4 * D - 2) : |x - 2 * X| ≤ 2 * D - 2 := by
  rcases hs with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith

omit [NeZero d] in
/-- **The frame of an admissible token**: its plane relative to the face, the target centre, the
lanes relative to the centre line. [folklore] -/
theorem frame_facts (hY : Y.OK) (hτ : TAdm hd Y a e τ) :
    Fc Y a e - 2 * Y.ell ≤ 2 * ((sgOf e : ℤ) * τ.pos (axOf hd e)) ∧ 2 * ((sgOf e : ℤ) * τ.pos (axOf hd e)) ≤ Fc Y a e - 2 ∧
      2 * ((sgOf e : ℤ) * Y.ctr (tgtCell a e) e.1) = Fc Y a e + 2 * Y.Dh ∧
      Y.ctr (tgtCell a e) (latDir e true).1 = Y.ctr a (latDir e true).1 ∧
      |2 * τ.pos (latOf hd e) - (2 * Y.ctr a (latDir e true).1 + 2 * Y.nu e)| ≤ 2 * Y.ρp + 2 * Y.lamJ ∧
      |2 * Y.lane (tgtCell a e) e - (2 * Y.ctr a (latDir e true).1 + 2 * Y.nu e)| ≤ 4 * Y.lamJ ∧
      |Y.nu e| ≤ Y.lam ∧
      |2 * brLane Y a e 1 - (Fc Y a e + 2 * Y.Dh) * (sgOf e : ℤ) - 2 * Y.lam| ≤ 2 * Y.lamJ ∧
      |2 * brLane Y a e (-1) - (Fc Y a e + 2 * Y.Dh) * (sgOf e : ℤ) + 2 * Y.lam| ≤ 2 * Y.lamJ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlam, hlamJ, -⟩ := hY.facts
  have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
  have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hF : Fc Y a e = 2 * ((sgOf e : ℤ) * Y.ctr a e.1) + 2 * Y.Dh := rfl
  obtain ⟨hlo, hhi⟩ := hτ.longit
  have hXc : 2 * ((sgOf e : ℤ) * Y.ctr (tgtCell a e) e.1) = Fc Y a e + 2 * Y.Dh := by
    rw [ctr_tgtCell_fst, hF]
    have : (sgOf e : ℤ) * (Y.ctr a e.1 + (sgOf e : ℤ) * (2 * Y.Dh)) = (sgOf e : ℤ) * Y.ctr a e.1 + ((sgOf e : ℤ) * (sgOf e : ℤ)) * (2 * Y.Dh) := by
      ring
    rw [this, hss]; ring
  have hla : Y.lane a e = Y.ctr a (latDir e true).1 + Y.nu e + TallLayout.cpar a * Y.lamJ := rfl
  have hy : Y.lane (tgtCell a e) e = Y.lane a e + (jogDir a e : ℤ) * Y.lamJ := lane_tgtCell Y a e
  have hpar : TallLayout.cpar a = 0 ∨ TallLayout.cpar a = 1 := by unfold TallLayout.cpar; omega
  have hparc : TallLayout.cpar (tgtCell a e) = 0 ∨ TallLayout.cpar (tgtCell a e) = 1 := by unfold TallLayout.cpar; omega
  have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  have hτl := abs_le.1 hτ.lateral
  rw [hla] at hτl
  -- the port lanes
  have hctr : Y.ctr (tgtCell a e) e.1 * 2 = (Fc Y a e + 2 * Y.Dh) * (sgOf e : ℤ) := by
    have : (Fc Y a e + 2 * Y.Dh) * (sgOf e : ℤ) = 2 * Y.ctr (tgtCell a e) e.1 * ((sgOf e : ℤ) * (sgOf e : ℤ)) := by rw [← hXc]; ring
    rw [this, hss]; ring
  refine ⟨by rw [hF]; linarith only [hlo], by rw [hF]; linarith only [hhi], hXc, ctr_tgtCell_snd Y a e, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; rcases hpar with hq | hq <;> rw [hq] at hτl <;> constructor <;> linarith only [hτl.1, hτl.2, hlamJ0]
  · rw [hy, hla, abs_le]
    rcases hpar with hq | hq <;> rw [hq] <;> rcases hv1 with hv | hv <;> rw [hv] <;> constructor <;> linarith only [hlamJ0]
  · rw [nu_eq]; rcases hs1 with hs | hs <;> rw [hs] <;> simp [abs_of_nonneg hlam0]
  · rw [brLane_eq, abs_le]; simp only [Units.val_one, if_true]
    rcases hparc with hq | hq <;> rw [hq] <;> constructor <;> linarith only [hctr, hlamJ0]
  · rw [brLane_eq, abs_le]; simp only [Units.val_neg, Units.val_one, show ¬((-1 : ℤ) = 1) by decide, if_false]
    rcases hparc with hq | hq <;> rw [hq] <;> constructor <;> linarith only [hctr, hlamJ0]

omit [NeZero d] in
/-- **The `A` part: entry-shaped, in the core or in the poke.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem shapes_A (hY : Y.OK) (hτ : TAdm hd Y a e τ) {w : Site d}
    (h1 : 1 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 2)
    (h3 : |w (latOf hd e) - 2 * τ.pos (latOf hd e)| ≤ 2 * Y.Lp + 2 * Y.Δw + Y.K0)
    (h4 : |w (ax0 hd) - 2 * Y.zOf (τ.src.getD e)| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0) :
    EntryP Y hd a e w ∧ (w ∈ Core Y hd (tgtCell a e) ∨ w ∈ Poke Y hd a e τ) := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, hsepT, hsepB, hR2, hJ2⟩ := hY.shapes
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hN0 : (0 : ℤ) ≤ Y.N₁ * Y.Lp := by have := hY.Lp_nonneg; positivity
  obtain ⟨hp1, hp2, hXc, hXf, hpf, -, hnu, -⟩ := frame_facts Y hd a e τ hY hτ
  have h3' := abs_le.1 h3; have hpf' := abs_le.1 hpf; have hnu' := abs_le.1 hnu
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have e1 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) = (sgOf e : ℤ) * w (axOf hd e) - 2 * ((sgOf e : ℤ) * τ.pos (axOf hd e)) := by
    ring
  rw [e1] at h1 h2
  have hE : EntryP Y hd a e w := by
    constructor
    · unfold TallLayout.DE; linarith only [h2, hp2, hN0, hl1, hLp0, hK0, hLeq, hm0]
    · unfold TallLayout.ΓE; rw [abs_le]; constructor <;> linarith only [h3'.1, h3'.2, hpf'.1, hpf'.2, hlamJ0, hm0, hell, hl1]
  refine ⟨hE, ?_⟩
  have hDEd : Y.DE = 2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0 := rfl
  have hΓPd : Y.ΓP = 2 * Y.lam + 2 * Y.lamJ + 2 * Y.ρp + 2 * Y.Lp + 2 * Y.Δw + Y.K0 := rfl
  have hK00 : 0 ≤ Y.K0 := by rw [hK0]; linarith only [hLeq, hLp0, hm0, hell, hl1]
  by_cases hfar : Fc Y a e + 2 ≤ (sgOf e : ℤ) * w (axOf hd e)
  · left
    apply mem_core Y hd e
    · have hhi : (sgOf e : ℤ) * w (axOf hd e) ≤ Fc Y a e + 4 * Y.Dh - 2 := by
        linarith only [h2, hp2, hbig, hDEd, hDE0, hN0, hl1, hLp0, hK00, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hell]
      exact abs_u_core hs1 hXc hfar hhi
    · rw [hXf, abs_le]
      constructor <;> linarith only [h3'.1, h3'.2, hpf'.1, hpf'.2, hnu'.1, hnu'.2, hbig, hΓPd, hDE0, hΓE0, hΓT0, hΓB0, hlam0, hlamJ0, hl1]
  · right
    push Not at hfar
    refine ⟨by linarith only [h1, hp1], by linarith only [hfar], ?_, h4⟩
    unfold TallLayout.ΓP; rw [abs_le]
    constructor <;> linarith only [h3'.1, h3'.2, hpf'.1, hpf'.2, hnu'.1, hnu'.2]

omit [NeZero d] in
/-- **The riser and the jog: entry-shaped, in the core.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem shapes_RJ (hY : Y.OK) (hτ : TAdm hd Y a e τ) {w : Site d}
    (h1 : 2 * Y.Pw * Y.ell - Y.K0 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0)
    (h3 : |w (latOf hd e) - 2 * τ.pos (latOf hd e)| ≤ 2 * Y.Lp + 2 * Y.Δw + Y.K0 ∨
      (-(2 * Y.Lp + 2 * Y.Δw) ≤ (jogDir a e : ℤ) * (w (latOf hd e) - 2 * τ.pos (latOf hd e)) ∧
        (jogDir a e : ℤ) * (w (latOf hd e) - 2 * Y.lane (tgtCell a e) e) ≤ 2 * Y.m + 2 * Y.H + 6)) :
    EntryP Y hd a e w ∧ w ∈ Core Y hd (tgtCell a e) := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -, -, -, hΔ0, -, hρp, -⟩ := hY.facts
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, hsepT, hsepB, hR2, hJ2⟩ := hY.shapes
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  obtain ⟨hp1, hp2, hXc, hXf, hpf, hyf, hnu, -⟩ := frame_facts Y hd a e τ hY hτ
  have hpf' := abs_le.1 hpf; have hnu' := abs_le.1 hnu; have hyf' := abs_le.1 hyf
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  have e1 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) = (sgOf e : ℤ) * w (axOf hd e) - 2 * ((sgOf e : ℤ) * τ.pos (axOf hd e)) := by
    ring
  rw [e1] at h1 h2
  -- lateral: within `Γ_E` of the centre line offset
  have hlat : |w (latOf hd e) - (2 * Y.ctr a (latDir e true).1 + 2 * Y.nu e)| ≤ Y.ΓE := by
    unfold TallLayout.ΓE; rw [abs_le]
    rcases h3 with h3 | ⟨h3, h4⟩
    · have h3' := abs_le.1 h3
      constructor <;> linarith only [h3'.1, h3'.2, hpf'.1, hpf'.2, hlamJ0, hm0, hell, hl1, hρp, hLp0, hΔ0]
    · rcases hv1 with hv | hv <;> rw [hv] at h3 h4 <;> constructor <;>
        linarith only [h3, h4, hpf'.1, hpf'.2, hyf'.1, hyf'.2, hlamJ0, hm0, hell, hl1, hLp0, hΔ0, hK0, hLeq, hρp]
  have hlat' := abs_le.1 hlat
  have hDEd : Y.DE = 2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0 := rfl
  refine ⟨⟨by linarith only [h2, hp2, hDEd], hlat⟩, ?_⟩
  apply mem_core Y hd e
  · have hlo' : Fc Y a e + 2 ≤ (sgOf e : ℤ) * w (axOf hd e) := by linarith only [h1, hp1, hJ2]
    have hhi' : (sgOf e : ℤ) * w (axOf hd e) ≤ Fc Y a e + 4 * Y.Dh - 2 := by
      linarith only [h2, hp2, hDEd, hDE0, hbig, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
    exact abs_u_core hs1 hXc hlo' hhi'
  · rw [hXf, abs_le]
    constructor <;> linarith only [hlat'.1, hlat'.2, hnu'.1, hnu'.2, hbig, hDE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]

omit [NeZero d] in
/-- **The trunk tube: in the core.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem shapes_T (hY : Y.OK) (hτ : TAdm hd Y a e τ) {w : Site d}
    (h1 : 2 * Y.Pw * Y.ell + 2 * Y.L + 3 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * Y.ctr (tgtCell a e) e.1) ≤ 2 * Y.Dh - 2)
    (h3 : |w (latOf hd e) - 2 * Y.lane (tgtCell a e) e| ≤ 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw + Y.K0)
    (h4 : |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0) : TubeTP Y hd a e w ∧ w ∈ Core Y hd (tgtCell a e) := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -, -, -, hΔ0, -⟩ := hY.facts
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, hsepT, hsepB, hR2, hJ2⟩ := hY.shapes
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  obtain ⟨hp1, -, hXc, hXf, -, hyf, hnu, -⟩ := frame_facts Y hd a e τ hY hτ
  have hnu' := abs_le.1 hnu; have hyf' := abs_le.1 hyf; have h3' := abs_le.1 h3
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have e1 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) = (sgOf e : ℤ) * w (axOf hd e) - 2 * ((sgOf e : ℤ) * τ.pos (axOf hd e)) := by
    ring
  have e2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * Y.ctr (tgtCell a e) e.1) = (sgOf e : ℤ) * w (axOf hd e) - 2 * ((sgOf e : ℤ) * Y.ctr (tgtCell a e) e.1) := by
    ring
  rw [e1] at h1; rw [e2, hXc] at h2
  have hlat : |w (latOf hd e) - (2 * Y.ctr a (latDir e true).1 + 2 * Y.nu e)| ≤ Y.ΓT := by
    unfold TallLayout.ΓT; rw [abs_le]; constructor <;> linarith only [h3'.1, h3'.2, hyf'.1, hyf'.2]
  have hlat' := abs_le.1 hlat
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hlo' : Fc Y a e + 2 ≤ (sgOf e : ℤ) * w (axOf hd e) := by linarith only [h1, hp1, hJ2, hK0, hm0, hLp0, hLeq, hell, hl1]
  have hhi' : (sgOf e : ℤ) * w (axOf hd e) ≤ Fc Y a e + 4 * Y.Dh - 2 := by linarith only [h2]
  refine ⟨⟨hlo', hhi', hlat, h4⟩, ?_⟩
  apply mem_core Y hd e
  · exact abs_u_core hs1 hXc hlo' hhi'
  · rw [hXf, abs_le]
    constructor <;> linarith only [hlat'.1, hlat'.2, hnu'.1, hnu'.2, hbig, hDE0, hΓE0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]

omit [NeZero d] in
/-- **A branch tube: in the core.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem shapes_B (hY : Y.OK) (hτ : TAdm hd Y a e τ) {w : Site d} (w' : ℤˣ)
    (h1 : -(2 * Y.Lp) - Y.K0 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * brLane Y a e w'))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * brLane Y a e w') ≤ 2 * Y.ell + 2 * Y.H + 2 * Y.Lp + Y.K0)
    (h3 : -(2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw) ≤ (w' : ℤ) * (w (latOf hd e) - 2 * Y.lane (tgtCell a e) e))
    (h4 : (w' : ℤ) * (w (latOf hd e) - 2 * Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) ≤ 2 * Y.Dh - 2)
    (h5 : |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0) : TubeBP Y hd a e w' w ∧ w ∈ Core Y hd (tgtCell a e) := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -, -, -, hΔ0, -⟩ := hY.facts
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, hsepT, hsepB, hR2, hJ2⟩ := hY.shapes
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  obtain ⟨-, -, hXc, hXf, -, hyf, hnu, hb1, hb2⟩ := frame_facts Y hd a e τ hY hτ
  have hnu' := abs_le.1 hnu; have hyf' := abs_le.1 hyf; have hb1' := abs_le.1 hb1; have hb2' := abs_le.1 hb2
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hXf' : Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ = Y.ctr a (latDir e true).1 := hXf
  rw [hXf'] at h4
  have e1 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * brLane Y a e w') = (sgOf e : ℤ) * w (axOf hd e) - (sgOf e : ℤ) * (2 * brLane Y a e w') := by ring
  rw [e1] at h1 h2
  have hBB : TubeBP Y hd a e w' w := by
    refine ⟨?_, ?_, h4, h5⟩
    · unfold TallLayout.ΓB; rw [abs_le]
      rcases Int.units_eq_one_or w' with hw | hw <;> subst hw <;> rcases hs1 with hs | hs <;> rw [hs] at h1 h2 hb1' hb2' ⊢ <;> push_cast at h1 h2 hb1' hb2' ⊢ <;>
        constructor <;> linarith only [h1, h2, hb1'.1, hb1'.2, hb2'.1, hb2'.2, hlamJ0]
    · rcases Int.units_eq_one_or w' with hw | hw <;> subst hw <;> push_cast at h3 ⊢ <;> linarith only [h3, hyf'.1, hyf'.2]
  obtain ⟨hB1, hB2, -, -⟩ := hBB
  have hB1' := abs_le.1 hB1
  have hΓTd : Y.ΓT = 4 * Y.lamJ + 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw + Y.K0 := rfl
  have hK00 : 0 ≤ Y.K0 := by rw [hK0]; linarith only [hLeq, hLp0, hm0, hell, hl1]
  have hwl : -Y.lam ≤ (sgOf e : ℤ) * (w' : ℤ) * Y.lam ∧ (sgOf e : ℤ) * (w' : ℤ) * Y.lam ≤ Y.lam := by
    rcases Int.units_eq_one_or w' with hw | hw <;> subst hw <;> rcases hs1 with hs | hs <;> rw [hs] <;> push_cast <;> constructor <;>
      linarith only [hlam0]
  refine ⟨⟨hB1, hB2, h4, h5⟩, ?_⟩
  apply mem_core Y hd e
  · have hlo' : Fc Y a e + 2 ≤ (sgOf e : ℤ) * w (axOf hd e) := by
      linarith only [hB1'.1, hwl.1, hbig, hDE0, hΓE0, hΓT0, hΓP0, hlam0, hlamJ0, hl1]
    have hhi' : (sgOf e : ℤ) * w (axOf hd e) ≤ Fc Y a e + 4 * Y.Dh - 2 := by
      linarith only [hB1'.2, hwl.2, hbig, hDE0, hΓE0, hΓT0, hΓP0, hlam0, hlamJ0, hl1]
    exact abs_u_core hs1 hXc hlo' hhi'
  · rw [hXf, abs_le]
    rcases Int.units_eq_one_or w' with hw | hw <;> subst hw <;> push_cast at hB2 h4 ⊢ <;> constructor <;>
      linarith only [hB2, h4, hnu'.1, hnu'.2, hbig, hΓTd, hK00, hDE0, hΓE0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]

omit [NeZero d] in
/-- **The shapes of the region**: every point of the region of an admissible token is entry-shaped,
in the trunk tube or in a branch tube; and it lies in the core of the target cell or in the poke.
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem shapes_of_mem (hY : Y.OK) (hτ : TAdm hd Y a e τ) {w : Site d} (hw : w ∈ zoneRegion Y hd a e τ) :
    (EntryP Y hd a e w ∨ TubeTP Y hd a e w ∨ ∃ w' : ℤˣ, TubeBP Y hd a e w' w) ∧ (w ∈ Core Y hd (tgtCell a e) ∨ w ∈ Poke Y hd a e τ) := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hN0 : (0 : ℤ) ≤ Y.N₁ * Y.Lp := by positivity
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  have hPw0 : (0 : ℤ) ≤ Y.Pw * Y.ell := by positivity
  obtain ⟨-, hA | hR | hJ | hT | ⟨w', hB⟩⟩ := hw
  · obtain ⟨h1, h2, h3, h4⟩ := hA
    obtain ⟨hE, hCP⟩ := shapes_A Y hd a e τ hY hτ h1 h2 h3 h4
    exact ⟨Or.inl hE, hCP⟩
  · obtain ⟨h1, h2, h3, -, -⟩ := hR
    obtain ⟨hE, hC⟩ := shapes_RJ Y hd a e τ hY hτ (by linarith only [h1, hm0]) (by linarith only [h2, hN0, hl0, hLp0]) (Or.inl h3)
    exact ⟨Or.inl hE, Or.inl hC⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := hJ
    obtain ⟨hE, hC⟩ := shapes_RJ Y hd a e τ hY hτ h1 h2 (Or.inr ⟨h3, h4⟩)
    exact ⟨Or.inl hE, Or.inl hC⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hT
    obtain ⟨hTT, hC⟩ := shapes_T Y hd a e τ hY hτ h1 h2 h3 h4
    exact ⟨Or.inr (Or.inl hTT), Or.inl hC⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hB
    obtain ⟨hBB, hC⟩ := shapes_B Y hd a e τ hY hτ w' h1 h2 h3 h4 h5
    exact ⟨Or.inr (Or.inr ⟨w', hBB⟩), Or.inl hC⟩

end Shapes

/-! ## Cores and pokes are disjoint in plan -/

section Plan

variable (Y : TallLayout) (hd : 3 ≤ d)

omit [NeZero d] in
/-- A nonzero integer multiple of `D ≥ 0` has absolute value at least `D`. [folklore] -/
theorem le_abs_mul_of_ne_zero {D k : ℤ} (hD : 0 ≤ D) (hk : k ≠ 0) : D ≤ |k * D| := by
  rw [abs_mul, abs_of_nonneg hD]
  have : 1 ≤ |k| := Int.one_le_abs hk
  nlinarith

omit [NeZero d] in
/-- The two plane indices seen from `e`. [folklore] -/
theorem fin2_cases (e : MDir) (i : Fin 2) : i = e.1 ∨ i = (latDir e true).1 := by
  by_cases h : i = e.1
  · exact Or.inl h
  · right; simp only [latDir]; apply Fin.ext; have h1 := i.isLt; have h2 := e.1.isLt
    have h3 : i.val ≠ e.1.val := fun h' => h (Fin.ext h')
    simp only; omega

omit [NeZero d] in
/-- **Cores of distinct cells are disjoint.** [folklore] -/
theorem core_core (hY : Y.OK) {c c' : Site 2} (h : c ≠ c') {w : Site d} (h1 : w ∈ Core Y hd c) (h2 : w ∈ Core Y hd c') : False := by
  obtain ⟨-, -, -, hell, hmH, -, -, -, -, -, -, -, -, -, hDh, -, hPe, hP2, hP3, -, -, hP64, -⟩ := hY.facts
  have hDh0 : 0 ≤ Y.Dh := by rw [hDh]; have : (0:ℤ) ≤ Y.ell := by linarith only [hell, hmH]
                             positivity
  obtain ⟨i, hi⟩ := exists_ne_of_ne h
  have ha := abs_le.1 (h1 (i, true)); have hb := abs_le.1 (h2 (i, true))
  simp only at ha hb
  have hsub := ctr_sub_ctr Y c c' i
  have hk : c i - c' i ≠ 0 := sub_ne_zero.2 hi
  have hbig := le_abs_mul_of_ne_zero (D := 2 * Y.Dh) (by linarith) hk
  rw [← hsub] at hbig
  rcases le_or_gt 0 (Y.ctr c i - Y.ctr c' i) with hs | hs
  · rw [abs_of_nonneg hs] at hbig; linarith only [ha.1, ha.2, hb.1, hb.2, hbig, hDh0]
  · rw [abs_of_neg hs] at hbig; linarith only [ha.1, ha.2, hb.1, hb.2, hbig, hDh0]

omit [NeZero d] in
/-- **A poke avoids the cores of all cells but its source and its target.** [folklore] -/
theorem poke_core (hY : Y.OK) {a : Site 2} {e : MDir} {τ : TTok d} {c' : Site 2} (h1 : c' ≠ a) (h2 : c' ≠ tgtCell a e) {w : Site d}
    (hp : w ∈ Poke Y hd a e τ) (hc : w ∈ Core Y hd c') : False := by
  obtain ⟨-, -, -, hell, hmH, -, -, -, -, -, -, -, -, -, hDh, -, hPe, hP2, hP3, -, -, hP64, -⟩ := hY.facts
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, -⟩ := hY.shapes
  have hDh0 : 0 ≤ Y.Dh := by linarith only [hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
  obtain ⟨hu1, hu2, hv, -⟩ := hp
  have hF : Fc Y a e = 2 * ((sgOf e : ℤ) * Y.ctr a e.1) + 2 * Y.Dh := rfl
  have hce := abs_le.1 (hc e)
  have hcf := abs_le.1 (hc (latDir e true))
  rw [axOf_latDir] at hcf
  have hv' := abs_le.1 hv
  set f : Fin 2 := (latDir e true).1 with hf
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  by_cases hΔf : c' f = a f
  · -- same lateral coordinate: compare along `e`
    have hΔe : c' e.1 - a e.1 ≠ 0 := by
      intro h0; apply h1; funext i
      rcases fin2_cases e i with rfl | rfl
      · linarith only [h0]
      · exact hΔf
    have hΔs : c' e.1 - a e.1 ≠ (sgOf e : ℤ) := by
      intro h0; apply h2; funext i
      rw [tgtCell_apply]
      rcases fin2_cases e i with rfl | rfl
      · rw [if_pos rfl]; linarith only [h0]
      · have : (latDir e true).1 ≠ e.1 := by
          simp only [latDir]; intro h'; have := congrArg Fin.val h'; simp at this; have := e.1.isLt; omega
        rw [← hf, if_neg this, add_zero]; exact hΔf
    have hsub := ctr_sub_ctr Y c' a e.1
    -- `σ = s Δ_e ∉ {0, 1}`
    set σ := (sgOf e : ℤ) * (c' e.1 - a e.1) with hσ
    have hσ0 : σ ≠ 0 := by
      rw [hσ]; rcases hs1 with hs | hs <;> rw [hs] <;> omega
    have hσ1 : σ ≠ 1 := by
      rw [hσ]; intro h0; apply hΔs; rcases hs1 with hs | hs <;> rw [hs] at h0 ⊢ <;> linarith only [h0]
    have hsu : (sgOf e : ℤ) * (2 * Y.ctr c' e.1) = 2 * ((sgOf e : ℤ) * Y.ctr a e.1) + 4 * Y.Dh * σ := by
      rw [hσ]; linear_combination 2 * (sgOf e : ℤ) * hsub
    rcases lt_or_gt_of_ne hσ0 with hneg | hpos
    · have hle : σ ≤ -1 := by omega
      have : 4 * Y.Dh * σ ≤ 4 * Y.Dh * (-1) := by nlinarith
      rcases hs1 with hs | hs <;> rw [hs] at hu1 hsu hF <;> linarith only [hu1, hce.1, hce.2, hsu, this, hF, hDh0, hl1, hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0]
    · have hle : 2 ≤ σ := by omega
      have : 4 * Y.Dh * 2 ≤ 4 * Y.Dh * σ := by nlinarith
      rcases hs1 with hs | hs <;> rw [hs] at hu2 hsu hF <;> linarith only [hu2, hce.1, hce.2, hsu, this, hF, hDh0]
  · -- different lateral coordinate: the lateral distance is at least a full cell
    have hk : c' f - a f ≠ 0 := sub_ne_zero.2 hΔf
    have hsub := ctr_sub_ctr Y c' a f
    have hb := le_abs_mul_of_ne_zero (D := 2 * Y.Dh) (by linarith) hk
    rw [← hsub] at hb
    rcases le_or_gt 0 (Y.ctr c' f - Y.ctr a f) with hs | hs
    · rw [abs_of_nonneg hs] at hb
      linarith only [hcf.1, hcf.2, hv'.1, hv'.2, hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hlam0, hlamJ0, hl1]
    · rw [abs_of_neg hs] at hb
      linarith only [hcf.1, hcf.2, hv'.1, hv'.2, hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hlam0, hlamJ0, hl1]

omit [NeZero d] in
/-- **Pokes at different faces are disjoint**: two pokes meet only if they are at the same face, i.e.
the same source and direction, or each the target of the other with reversed directions. [folklore] -/
theorem poke_poke (hY : Y.OK) {a a' : Site 2} {e e' : MDir} {τ τ' : TTok d} (hne : (a, e) ≠ (a', e'))
    (h2 : ¬(a' = tgtCell a e ∧ e' = rev e)) {w : Site d} (hp : w ∈ Poke Y hd a e τ) (hp' : w ∈ Poke Y hd a' e' τ') : False := by
  obtain ⟨-, -, -, hell, hmH, -, -, -, -, -, -, -, -, -, hDh, -, hPe, hP2, hP3, -, -, hP64, -⟩ := hY.facts
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, -⟩ := hY.shapes
  have hDh0 : 0 ≤ Y.Dh := by linarith only [hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
  obtain ⟨hu1, hu2, hv, -⟩ := hp
  obtain ⟨hu1', hu2', hv', -⟩ := hp'
  have hF : Fc Y a e = 2 * ((sgOf e : ℤ) * Y.ctr a e.1) + 2 * Y.Dh := rfl
  have hF' : Fc Y a' e' = 2 * ((sgOf e' : ℤ) * Y.ctr a' e'.1) + 2 * Y.Dh := rfl
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hs1' : (sgOf e' : ℤ) = 1 ∨ (sgOf e' : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e') with h | h <;> simp [h]
  have hva := abs_le.1 hv; have hva' := abs_le.1 hv'
  set f : Fin 2 := (latDir e true).1 with hf
  by_cases hax : e'.1 = e.1
  · -- same macro-axis
    obtain ⟨hA, hL, hT⟩ := axes_of_fst_eq hd hax
    rw [hA] at hu1' hu2'; rw [hL, hT] at hva'; rw [hax] at hF'
    -- lateral: the same cell column
    have hΔf : a' f = a f := by
      by_contra hne'
      have hk : a' f - a f ≠ 0 := sub_ne_zero.2 hne'
      have hsub := ctr_sub_ctr Y a' a f
      have hb := le_abs_mul_of_ne_zero (D := 2 * Y.Dh) (by linarith) hk
      rw [← hsub] at hb
      rcases le_or_gt 0 (Y.ctr a' f - Y.ctr a f) with hs | hs
      · rw [abs_of_nonneg hs] at hb; linarith only [hva.1, hva.2, hva'.1, hva'.2, hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hlam0, hlamJ0, hl1]
      · rw [abs_of_neg hs] at hb; linarith only [hva.1, hva.2, hva'.1, hva'.2, hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hlam0, hlamJ0, hl1]
    have hsub := ctr_sub_ctr Y a' a e.1
    set Δ := a' e.1 - a e.1 with hΔ
    by_cases hss : (sgOf e' : ℤ) = sgOf e
    · -- same sign: the same face only if the same source
      rw [hss] at hF' hu1' hu2'
      have hΔ0 : Δ = 0 := by
        by_contra hk
        have hb := le_abs_mul_of_ne_zero (D := 2 * Y.Dh) (by linarith) hk
        rw [← hsub] at hb
        rcases le_or_gt 0 (Y.ctr a' e.1 - Y.ctr a e.1) with hs | hs
        · rw [abs_of_nonneg hs] at hb
          rcases hs1 with h | h <;> rw [h] at hu1 hu2 hu1' hu2' hF hF' <;>
            linarith only [hu1, hu2, hu1', hu2', hF, hF', hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
        · rw [abs_of_neg hs] at hb
          rcases hs1 with h | h <;> rw [h] at hu1 hu2 hu1' hu2' hF hF' <;>
            linarith only [hu1, hu2, hu1', hu2', hF, hF', hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
      apply hne
      have ha : a' = a := by
        funext i; rcases fin2_cases e i with rfl | rfl
        · linarith only [hΔ0, hΔ]
        · exact hΔf
      rw [ha, MDir.ext_of hax hss]
    · -- opposite sign: the same face only if target and reverse
      have hss' : (sgOf e' : ℤ) = -sgOf e := by
        rcases hs1 with h | h <;> rcases hs1' with h' | h' <;> rw [h, h'] at hss ⊢ <;> simp_all
      rw [hss'] at hF' hu1' hu2'
      have hΔs : Δ = (sgOf e : ℤ) := by
        by_contra hk
        -- `F + F' = 4 Dh (1 - s Δ)` is then a nonzero multiple of `4 Dh`
        have hk' : 1 - (sgOf e : ℤ) * Δ ≠ 0 := by
          intro h0; apply hk; rcases hs1 with h | h <;> rw [h] at h0 ⊢ <;> linarith only [h0]
        have hb := le_abs_mul_of_ne_zero (D := 4 * Y.Dh) (by linarith) hk'
        have hsum : (1 - (sgOf e : ℤ) * Δ) * (4 * Y.Dh) = 4 * Y.Dh - 2 * ((sgOf e : ℤ) * (Y.ctr a' e.1 - Y.ctr a e.1)) := by rw [hsub]; ring
        rw [hsum] at hb
        rcases le_or_gt 0 (4 * Y.Dh - 2 * ((sgOf e : ℤ) * (Y.ctr a' e.1 - Y.ctr a e.1))) with hs | hs
        · rw [abs_of_nonneg hs] at hb
          rcases hs1 with h | h <;> rw [h] at hu1 hu2 hu1' hu2' hF hF' hb <;>
            linarith only [hu1, hu2, hu1', hu2', hF, hF', hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
        · rw [abs_of_neg hs] at hb
          rcases hs1 with h | h <;> rw [h] at hu1 hu2 hu1' hu2' hF hF' hb <;>
            linarith only [hu1, hu2, hu1', hu2', hF, hF', hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
      apply h2
      constructor
      · funext i; rw [tgtCell_apply]
        rcases fin2_cases e i with rfl | rfl
        · rw [if_pos rfl]; linarith only [hΔs, hΔ]
        · have : (latDir e true).1 ≠ e.1 := by
            simp only [latDir]; intro h'; have := congrArg Fin.val h'; simp at this; have := e.1.isLt; omega
          rw [← hf, if_neg this, add_zero]; exact hΔf
      · exact eq_rev_of hax hss'
  · -- different macro-axes: the poke centres differ by an odd multiple of `2 Dh` along `e`
    obtain ⟨hA, hL, hT, h1'⟩ := axes_of_fst_ne hd hax
    rw [hL, hT] at hva'
    have hsub := ctr_sub_ctr Y a a' e.1
    set Δ := a e.1 - a' e.1 with hΔ
    have hk : 2 * Δ + (sgOf e : ℤ) ≠ 0 := by rcases hs1 with h | h <;> rw [h] <;> omega
    have hb := le_abs_mul_of_ne_zero (D := 2 * Y.Dh) (by linarith) hk
    have hsum : (2 * Δ + (sgOf e : ℤ)) * (2 * Y.Dh) = 2 * (Y.ctr a e.1 - Y.ctr a' e.1) + (sgOf e : ℤ) * (2 * Y.Dh) := by rw [hsub]; ring
    rw [hsum] at hb
    rcases le_or_gt 0 (2 * (Y.ctr a e.1 - Y.ctr a' e.1) + (sgOf e : ℤ) * (2 * Y.Dh)) with hs | hs
    · rw [abs_of_nonneg hs] at hb
      rcases hs1 with h | h <;> rw [h] at hu1 hu2 hF hb <;>
        linarith only [hu1, hu2, hF, hva'.1, hva'.2, hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hlam0, hlamJ0, hl1]
    · rw [abs_of_neg hs] at hb
      rcases hs1 with h | h <;> rw [h] at hu1 hu2 hF hb <;>
        linarith only [hu1, hu2, hF, hva'.1, hva'.2, hb, hbig, hDE0, hΓE0, hΓT0, hΓB0, hlam0, hlamJ0, hl1]

end Plan

/-! ## Two zones with the same target -/

section SameTarget

variable (Y : TallLayout) (hd : 3 ≤ d)

omit [NeZero d] in
/-- Equal targets from different directions: same macro-axis means reversed directions. [folklore] -/
theorem sign_of_sameTarget {e₁ e₂ : MDir} (hne : e₁ ≠ e₂) (hax : e₂.1 = e₁.1) :
    (sgOf e₂ : ℤ) = -sgOf e₁ := by
  have hs1 : (sgOf e₁ : ℤ) = 1 ∨ (sgOf e₁ : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e₁) with h | h <;> simp [h]
  have hs2 : (sgOf e₂ : ℤ) = 1 ∨ (sgOf e₂ : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e₂) with h | h <;> simp [h]
  by_contra hss
  have hss' : (sgOf e₂ : ℤ) = sgOf e₁ := by
    rcases hs1 with h | h <;> rcases hs2 with h' | h' <;> rw [h, h'] at hss ⊢ <;> simp_all
  exact hne (MDir.ext_of hax hss').symm

omit [NeZero d] in
/-- Equal targets in the same direction means the same source. [folklore] -/
theorem ne_dir_of_sameTarget {a₁ a₂ : Site 2} {e₁ e₂ : MDir} (hc : tgtCell a₁ e₁ = tgtCell a₂ e₂) (hne : (a₁, e₁) ≠ (a₂, e₂)) : e₁ ≠ e₂ := by
  rintro rfl
  apply hne
  have : a₁ = a₂ := by
    funext i; have := congrFun hc i; rw [tgtCell_apply, tgtCell_apply] at this; linarith
  rw [this]

omit [NeZero d] in
/-- **The entry parts of a zone avoid every zone with the same target from another direction**: by
the opposite faces (reversed directions) or, across, by the lane design. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem entry_vs_sameTarget (hY : Y.OK) {a₁ a₂ : Site 2} {e₁ e₂ : MDir} {τ₁ τ₂ : TTok d} (hτ₁ : TAdm hd Y a₁ e₁ τ₁) (hτ₂ : TAdm hd Y a₂ e₂ τ₂)
    (hc : tgtCell a₁ e₁ = tgtCell a₂ e₂) (hne : e₁ ≠ e₂) {w : Site d} (hE : EntryP Y hd a₁ e₁ w) (hw₂ : w ∈ zoneRegion Y hd a₂ e₂ τ₂) :
    False := by
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, hsepT, hsepB, -⟩ := hY.shapes
  have hΓTd : Y.ΓT = 4 * Y.lamJ + 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw + Y.K0 := rfl
  have hK00 : 0 ≤ Y.K0 := by
    obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
    have : (0:ℤ) ≤ Y.m := by positivity
    unfold TallLayout.K0; linarith
  obtain ⟨-, -, hXc₁, hXf₁, -, -, hnu₁, -⟩ := frame_facts Y hd a₁ e₁ τ₁ hY hτ₁
  obtain ⟨-, -, hXc₂, hXf₂, -, -, hnu₂, -⟩ := frame_facts Y hd a₂ e₂ τ₂ hY hτ₂
  rw [← hc] at hXc₂ hXf₂
  obtain ⟨hE1, hE2⟩ := hE
  have hE2' := abs_le.1 hE2
  have hnu₂' := abs_le.1 hnu₂
  have hs1 : (sgOf e₁ : ℤ) = 1 ∨ (sgOf e₁ : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e₁) with h | h <;> simp [h]
  obtain ⟨hsh, -⟩ := shapes_of_mem Y hd a₂ e₂ τ₂ hY hτ₂ hw₂
  by_cases hax : e₂.1 = e₁.1
  · -- reversed directions
    have hss := sign_of_sameTarget hne hax
    obtain ⟨hA, hL, hT⟩ := axes_of_fst_eq hd hax
    rw [hax, hss] at hXc₂
    -- `F₂ = -F₁ - 4 Dh`
    have hF : Fc Y a₂ e₂ = -Fc Y a₁ e₁ - 4 * Y.Dh := by linarith only [hXc₁, hXc₂]
    have hν : Y.nu e₂ = -Y.nu e₁ := by rw [nu_eq, nu_eq, hss]; ring
    rcases hsh with ⟨h1, -⟩ | ⟨-, -, h3, -⟩ | ⟨w', h1, -, -, -⟩
    · rw [hA, hss] at h1; linarith only [h1, hE1, hF, hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
    · rw [hT] at hXf₂
      rw [hL, hT, ← hXf₂, hXf₁, hν] at h3
      have h3' := abs_le.1 h3
      have hνv : Y.nu e₁ = Y.lam ∨ Y.nu e₁ = -Y.lam := by rw [nu_eq]; rcases hs1 with h | h <;> rw [h] <;> simp
      rcases hνv with hv | hv <;> rw [hv] at h3' hE2' <;> linarith only [h3'.1, h3'.2, hE2'.1, hE2'.2, hsepT]
    · rw [hA, hss, hF] at h1
      have h1' := abs_le.1 h1
      have hwl : -Y.lam ≤ -(sgOf e₁ : ℤ) * (w' : ℤ) * Y.lam ∧ -(sgOf e₁ : ℤ) * (w' : ℤ) * Y.lam ≤ Y.lam := by
        rcases Int.units_eq_one_or w' with hw | hw <;> subst hw <;> rcases hs1 with h | h <;> rw [h] <;> push_cast <;> constructor <;>
          linarith only [hlam0]
      linarith only [h1'.1, h1'.2, hwl.1, hwl.2, hE1, hbig, hDE0, hΓE0, hΓT0, hΓP0, hlam0, hlamJ0, hl1]
  · -- across: Z₂'s entry and trunk are near the centre along `e₁`, its branch lanes are the other side or start near the centre
    obtain ⟨hA, hL, hT, h1'⟩ := axes_of_fst_ne hd hax
    -- `ctr c e₂.1 = ctr a₁ f₁` and `2 s₁ ctr a₂ e₁.1 = F₁ + 2 Dh`
    rw [hT] at hXf₂
    have hXa₂ : 2 * ((sgOf e₁ : ℤ) * Y.ctr a₂ e₁.1) = Fc Y a₁ e₁ + 2 * Y.Dh := by rw [← hXf₂]; exact hXc₁
    rcases hsh with ⟨-, h2⟩ | ⟨-, -, h3, -⟩ | ⟨w', h1, h2, -, -⟩
    · rw [hL, hT] at h2
      have h2' := abs_le.1 h2
      rcases hs1 with h | h <;> rw [h] at hE1 hXa₂ <;>
        linarith only [h2'.1, h2'.2, hnu₂'.1, hnu₂'.2, hE1, hXa₂, hbig, hDE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
    · rw [hL, hT] at h3
      have h3' := abs_le.1 h3
      rcases hs1 with h | h <;> rw [h] at hE1 hXa₂ <;>
        linarith only [h3'.1, h3'.2, hnu₂'.1, hnu₂'.2, hE1, hXa₂, hbig, hDE0, hΓE0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
    · -- the branch tube of sign `w'`: along `e₁` it is `Z₁`'s lateral... compare lanes or the start
      rw [hL, hT] at h2
      rw [hA] at h1
      -- `h1`: `|s₂ v - 2 s₂ ctr a₁ f₁ - 2 (s₂ w') Λ| ≤ Γ_B` with `v = w (latOf e₁)`
      have hs2 : (sgOf e₂ : ℤ) = 1 ∨ (sgOf e₂ : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e₂) with h | h <;> simp [h]
      have hXc₂' : 2 * ((sgOf e₂ : ℤ) * Y.ctr a₁ (latDir e₁ true).1) = Fc Y a₂ e₂ + 2 * Y.Dh := by rw [← hXf₁, ← h1']; exact hXc₂
      by_cases hw : (w' : ℤ) = -(sgOf e₁ : ℤ)
      · -- opposite lane sides: `4Λ` apart laterally
        have h1' := abs_le.1 h1
        rw [hw] at h1'
        have hνv : Y.nu e₁ = (sgOf e₁ : ℤ) * Y.lam := nu_eq Y e₁
        rcases hs1 with h | h <;> rw [h] at h1' hνv <;> rcases hs2 with h' | h' <;> rw [h'] at h1' hXc₂' <;> rw [hνv] at hE2' <;>
          linarith only [h1'.1, h1'.2, hE2'.1, hE2'.2, hXc₂', hsepB]
      · -- same side: the tube starts near the trunk lane, near the centre along `e₁`
        have hw' : (w' : ℤ) = (sgOf e₁ : ℤ) := by
          rcases Int.units_eq_one_or w' with h | h <;> subst h <;> rcases hs1 with h' | h' <;> rw [h'] at hw ⊢ <;> simp_all
        rw [hw'] at h2
        rcases hs1 with h | h <;> rw [h] at hE1 hXa₂ h2 <;>
          linarith only [h2, hnu₂'.1, hnu₂'.2, hE1, hXa₂, hbig, hΓTd, hK00, hDE0, hΓE0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]

omit [NeZero d] in
/-- **Tubes of different directions are on different layers.** [folklore] -/
theorem tube_vs_tube (hY : Y.OK) {a₁ a₂ : Site 2} {e₁ e₂ : MDir} (hne : e₁ ≠ e₂) {w : Site d}
    (h1 : TubeTP Y hd a₁ e₁ w ∨ ∃ w', TubeBP Y hd a₁ e₁ w' w) (h2 : TubeTP Y hd a₂ e₂ w ∨ ∃ w', TubeBP Y hd a₂ e₂ w' w) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, hΔ0, -⟩ := hY.facts
  have ht1 : |w (ax0 hd) - 2 * Y.zOf e₁| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0 := by
    rcases h1 with ⟨-, -, -, h⟩ | ⟨w', -, -, -, h⟩ <;> exact h.trans (by linarith only [hΔ0])
  have ht2 : |w (ax0 hd) - 2 * Y.zOf e₂| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0 := by
    rcases h2 with ⟨-, -, -, h⟩ | ⟨w', -, -, -, h⟩ <;> exact h.trans (by linarith only [hΔ0])
  exact layers_apart Y hY hne ht1 ht2

omit [NeZero d] in
/-- **Two zones with the same target (from different cells) are disjoint.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem sameTarget_disjoint (hY : Y.OK) {a₁ a₂ : Site 2} {e₁ e₂ : MDir} {τ₁ τ₂ : TTok d} (hτ₁ : TAdm hd Y a₁ e₁ τ₁) (hτ₂ : TAdm hd Y a₂ e₂ τ₂)
    (hc : tgtCell a₁ e₁ = tgtCell a₂ e₂) (hne : (a₁, e₁) ≠ (a₂, e₂)) {w : Site d} (hw₁ : w ∈ zoneRegion Y hd a₁ e₁ τ₁)
    (hw₂ : w ∈ zoneRegion Y hd a₂ e₂ τ₂) : False := by
  have hne' := ne_dir_of_sameTarget hc hne
  obtain ⟨hsh₁, -⟩ := shapes_of_mem Y hd a₁ e₁ τ₁ hY hτ₁ hw₁
  obtain ⟨hsh₂, -⟩ := shapes_of_mem Y hd a₂ e₂ τ₂ hY hτ₂ hw₂
  rcases hsh₁ with hE₁ | hrest₁
  · exact entry_vs_sameTarget Y hd hY hτ₁ hτ₂ hc hne' hE₁ hw₂
  · rcases hsh₂ with hE₂ | hrest₂
    · exact entry_vs_sameTarget Y hd hY hτ₂ hτ₁ hc.symm hne'.symm hE₂ hw₁
    · exact tube_vs_tube Y hd hY hne' hrest₁ hrest₂

end SameTarget

/-! ## A zone aimed at the source of another -/

section TargetSource

variable (Y : TallLayout) (hd : 3 ≤ d)

omit [NeZero d] in
/-- **The poke of a zone avoids every zone aimed at its source cell from a direction other than its
provenance** (and other than head-on, which is excluded). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem poke_vs_targetSource (hY : Y.OK) {a₁ a₂ : Site 2} {e₁ e₂ : MDir} {τ₁ τ₂ : TTok d} (hτ₁ : TAdm hd Y a₁ e₁ τ₁)
    (hτ₂ : TAdm hd Y a₂ e₂ τ₂) (hc2 : tgtCell a₂ e₂ = a₁) (ha2 : a₂ ≠ tgtCell a₁ e₁) {d₁ : MDir} (hsrc : τ₁.src = some d₁)
    (hd₁ : d₁ ≠ e₂) {w : Site d} (hp : w ∈ Poke Y hd a₁ e₁ τ₁) (hw₂ : w ∈ zoneRegion Y hd a₂ e₂ τ₂) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, hΔ0, -⟩ := hY.facts
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, hsepT, hsepB, -⟩ := hY.shapes
  have hΓTd : Y.ΓT = 4 * Y.lamJ + 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw + Y.K0 := rfl
  have hK00 : 0 ≤ Y.K0 := by
    obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
    have : (0:ℤ) ≤ Y.m := by positivity
    unfold TallLayout.K0; linarith
  have he2 : e₂ ≠ rev e₁ := fun h => ha2 (eq_tgtCell_of_rev hc2 h)
  obtain ⟨hu1, hu2, -, hht⟩ := hp
  rw [hsrc, Option.getD_some] at hht
  have hF₁ : Fc Y a₁ e₁ = 2 * ((sgOf e₁ : ℤ) * Y.ctr a₁ e₁.1) + 2 * Y.Dh := rfl
  obtain ⟨-, -, hXc₂, hXf₂, -, -, hnu₂, -⟩ := frame_facts Y hd a₂ e₂ τ₂ hY hτ₂
  rw [hc2] at hXc₂ hXf₂
  have hnu₂' := abs_le.1 hnu₂
  have hs1 : (sgOf e₁ : ℤ) = 1 ∨ (sgOf e₁ : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e₁) with h | h <;> simp [h]
  obtain ⟨hsh, -⟩ := shapes_of_mem Y hd a₂ e₂ τ₂ hY hτ₂ hw₂
  have htube : |w (ax0 hd) - 2 * Y.zOf e₂| ≤ 2 * Y.ρv + Y.K0 → False := fun h =>
    layers_apart Y hY hd₁ hht (h.trans (by linarith only [hΔ0]))
  by_cases hax : e₂.1 = e₁.1
  · -- the same direction (head-on being excluded)
    have hee : e₂ = e₁ := by
      by_contra hne
      have hs2 : (sgOf e₂ : ℤ) = 1 ∨ (sgOf e₂ : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e₂) with h | h <;> simp [h]
      have hss : (sgOf e₂ : ℤ) = -sgOf e₁ := by
        by_contra h'
        have : (sgOf e₂ : ℤ) = sgOf e₁ := by rcases hs1 with h | h <;> rcases hs2 with h₂ | h₂ <;> rw [h, h₂] at h' ⊢ <;> simp_all
        exact hne (MDir.ext_of hax this)
      exact he2 (eq_rev_of hax hss)
    subst hee
    -- `F₂ = F₁ - 4 Dh`
    have hF : Fc Y a₂ e₂ = Fc Y a₁ e₂ - 4 * Y.Dh := by rw [hF₁]; linarith only [hXc₂]
    rcases hsh with ⟨h1, -⟩ | ⟨-, -, -, h4⟩ | ⟨w', h1, -, -, h4⟩
    · linarith only [h1, hu1, hF, hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
    · exact htube h4
    · rw [hF] at h1
      have h1' := abs_le.1 h1
      have hwl : -Y.lam ≤ (sgOf e₂ : ℤ) * (w' : ℤ) * Y.lam ∧ (sgOf e₂ : ℤ) * (w' : ℤ) * Y.lam ≤ Y.lam := by
        rcases Int.units_eq_one_or w' with hw | hw <;> subst hw <;> rcases hs1 with h | h <;> rw [h] <;> push_cast <;> constructor <;>
          linarith only [hlam0]
      linarith only [h1'.1, h1'.2, hwl.1, hwl.2, hu1, hbig, hDE0, hΓE0, hΓT0, hΓP0, hlam0, hlamJ0, hl1]
  · -- across
    obtain ⟨hA, hL, hT, h1'⟩ := axes_of_fst_ne hd hax
    rw [hT] at hXf₂
    -- `2 s₁ ctr a₂ e₁.1 = F₁ - 2 Dh`
    have hXa₂ : 2 * ((sgOf e₁ : ℤ) * Y.ctr a₂ e₁.1) = Fc Y a₁ e₁ - 2 * Y.Dh := by rw [← hXf₂, hF₁]; ring
    rcases hsh with ⟨-, h2⟩ | ⟨-, -, h3, -⟩ | ⟨w', -, h2, h3, h4⟩
    · rw [hL, hT] at h2
      have h2' := abs_le.1 h2
      rcases hs1 with h | h <;> rw [h] at hu1 hXa₂ <;>
        linarith only [h2'.1, h2'.2, hnu₂'.1, hnu₂'.2, hu1, hXa₂, hbig, hDE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
    · rw [hL, hT] at h3
      have h3' := abs_le.1 h3
      rcases hs1 with h | h <;> rw [h] at hu1 hXa₂ <;>
        linarith only [h3'.1, h3'.2, hnu₂'.1, hnu₂'.2, hu1, hXa₂, hbig, hDE0, hΓE0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
    · rw [hL, hT] at h2 h3
      by_cases hw : (w' : ℤ) = (sgOf e₁ : ℤ)
      · exact htube h4
      · have hw' : (w' : ℤ) = -(sgOf e₁ : ℤ) := by
          rcases Int.units_eq_one_or w' with h | h <;> subst h <;> rcases hs1 with h' | h' <;> rw [h'] at hw ⊢ <;> simp_all
        rw [hw'] at h2
        rcases hs1 with h | h <;> rw [h] at hu1 hXa₂ h2 <;>
          linarith only [h2, hnu₂'.1, hnu₂'.2, hu1, hXa₂, hbig, hΓTd, hK00, hDE0, hΓE0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]

end TargetSource

/-! ## Conclusion: static disjointness of the regions -/

section Conclusion

variable (Y : TallLayout) (hd : 3 ≤ d)

omit [NeZero d] in
/-- **Static disjointness of the regions** (the hypotheses of `AGadgetSystem.Lawful.disjoint_zone`,
with the provenance condition at the level of the token's source). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem zoneRegion_disjoint (hY : Y.OK) {a a' : Site 2} {e e' : MDir} {τ τ' : TTok d} (hτ : TAdm hd Y a e τ) (hτ' : TAdm hd Y a' e' τ')
    (hsrc : τ.src ≠ none) (h1 : (a, e) ≠ (a', e')) (h2 : a' ≠ tgtCell a e)
    (h3 : ∀ d', tgtCell a' e' = a → τ.src = some d' → d' ≠ e') {w : Site d} (hw : w ∈ zoneRegion Y hd a e τ)
    (hw' : w ∈ zoneRegion Y hd a' e' τ') : False := by
  by_cases hcc : tgtCell a e = tgtCell a' e'
  · exact sameTarget_disjoint Y hd hY hτ hτ' hcc h1 hw hw'
  obtain ⟨-, hcp⟩ := shapes_of_mem Y hd a e τ hY hτ hw
  obtain ⟨-, hcp'⟩ := shapes_of_mem Y hd a' e' τ' hY hτ' hw'
  by_cases hca : tgtCell a' e' = a
  · obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 hsrc
    rw [hca] at hcp'
    rcases hcp with hc | hp
    · rcases hcp' with hc' | hp'
      · exact core_core Y hd hY (tgtCell_ne_self a e) hc hc'
      · exact poke_core Y hd hY (Ne.symm h2) (by rw [hca]; exact tgtCell_ne_self a e) hp' hc
    · exact poke_vs_targetSource Y hd hY hτ hτ' hca h2 hd' (h3 d' hca hd') hp hw'
  · rcases hcp with hc | hp <;> rcases hcp' with hc' | hp'
    · exact core_core Y hd hY hcc hc hc'
    · exact poke_core Y hd hY (Ne.symm h2) hcc hp' hc
    · exact poke_core Y hd hY hca (fun h => hcc h.symm) hp hc'
    · exact poke_poke Y hd hY h1 (fun h => h2 h.1) hp hp'

omit [NeZero d] in
/-- **The region of a zone not aimed at the origin cell avoids the core box of the origin cell**
(`|w_i| ≤ 2 · D/2 - 2ℓ` on both plane axes). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem zoneRegion_avoids_origin (hY : Y.OK) {a : Site 2} {e : MDir} {τ : TTok d} (hτ : TAdm hd Y a e τ) (h0 : tgtCell a e ≠ 0)
    {w : Site d} (hw : w ∈ zoneRegion Y hd a e τ) (hbox : ∀ e' : MDir, |w (axOf hd e')| ≤ 2 * Y.Dh - 2 * Y.ell) : False := by
  obtain ⟨hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1, hbig, -⟩ := hY.shapes
  have hDh0 : 0 ≤ Y.Dh := by linarith only [hbig, hDE0, hΓE0, hΓT0, hΓB0, hΓP0, hlam0, hlamJ0, hl1]
  obtain ⟨-, hcp⟩ := shapes_of_mem Y hd a e τ hY hτ hw
  rcases hcp with hc | hp
  · obtain ⟨i, hi⟩ := exists_ne_of_ne h0
    have ha := abs_le.1 (hc (i, true))
    have hb := abs_le.1 (hbox (i, true))
    simp only at ha
    have hctr : Y.ctr (tgtCell a e) i = tgtCell a e i * (2 * Y.Dh) := rfl
    have hk : tgtCell a e i ≠ 0 := hi
    have hbig' := le_abs_mul_of_ne_zero (D := 2 * Y.Dh) (by linarith) hk
    rw [← hctr] at hbig'
    rcases le_or_gt 0 (Y.ctr (tgtCell a e) i) with hs | hs
    · rw [abs_of_nonneg hs] at hbig'; linarith only [ha.1, ha.2, hb.1, hb.2, hbig', hl1]
    · rw [abs_of_neg hs] at hbig'; linarith only [ha.1, ha.2, hb.1, hb.2, hbig', hl1]
  · obtain ⟨hu1, hu2, -, -⟩ := hp
    have hb := abs_le.1 (hbox e)
    have hF : Fc Y a e = 2 * ((sgOf e : ℤ) * Y.ctr a e.1) + 2 * Y.Dh := rfl
    have hctr : Y.ctr a e.1 = a e.1 * (2 * Y.Dh) := rfl
    have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    set σ := (sgOf e : ℤ) * a e.1 with hσ
    have hFσ : Fc Y a e = 4 * Y.Dh * σ + 2 * Y.Dh := by rw [hF, hctr, hσ]; ring
    rcases le_or_gt 0 σ with hσ0 | hσ0
    · have : 0 ≤ 4 * Y.Dh * σ := by positivity
      rcases hs1 with h | h <;> rw [h] at hu1 <;> linarith only [hu1, hb.1, hb.2, hFσ, this]
    · have hle : σ ≤ -1 := by omega
      have : 4 * Y.Dh * σ ≤ 4 * Y.Dh * (-1) := by nlinarith
      rcases hs1 with h | h <;> rw [h] at hu2 <;> linarith only [hu2, hb.1, hb.2, hFσ, this, hl1]

end Conclusion

end BGNd

end Percolation.Literature

end
