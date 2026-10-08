import Percolation.Literature.TallDisjoint
import Percolation.Util.Linter

/-!
# The tall gait, XIII (cont.): separations among the entry segments and with the trunk

Continuation of `TallDisjoint.lean` (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 p. 173 (C)): the riser lies beyond the top face of the entry
leg `A`; the jog lies beyond the lateral face of `A` (no riser) or in another layer (riser), and
beyond the lateral face of the near part of the riser and above its far part; the trunk lies beside
`A`, and beyond the forward faces of the riser and the jog.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- **Once the jog has started, the riser ended at a brick whose window fits the band.** [folklore] -/
theorem fits_riser_end (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hJ : st.sJ ≠ [])
    (hu : riseDir Y e τ ≠ 0) :
    st.sR ≠ [] ∧ riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) = st.sR.length - 1 ∧
      fits Y ((legOf st.sR (st.sR.length - 1)).b (ax0 hd)) (riseDir Y e τ) (Y.zOf e) := by
  obtain ⟨hRne, hdone⟩ := hI.invJ.prevR hJ hu
  have hk : st.sR.length - 1 < st.sR.length := by have := List.length_pos_of_ne_nil hRne; omega
  have hle := le_riserLen Y hd hL hH a e τ hI hk
  have heq : riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) = st.sR.length - 1 := le_antisymm hdone hle
  have hN := riser_feasible Y hd hL hH a e τ hY hτ hI hRne
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hRpos⟩ := hY.facts
  have hlt : riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) < Y.Rmax := by
    have : Y.N₁ < Y.Rmax := by
      unfold TallLayout.N₁ TallLayout.Rmax; have := hY.hP; have : 0 < Y.P ^ 3 := by positivity
      nlinarith
    omega
  have hfit0 := of_firstIdx_lt (p := fun k => fits Y ((legOf st.sR 0).b (ax0 hd) + riseDir Y e τ * (k * Y.ell)) (riseDir Y e τ) (Y.zOf e))
    (N := Y.Rmax) hlt
  obtain ⟨hb, -, -, -, -, -⟩ := boundsR Y hd hL hH a e τ hY hI hk
  refine ⟨hRne, heq, ?_⟩
  rw [hb]
  have : (legOf st.sR 0).b (ax0 hd) + riseDir Y e τ * Y.ell * ((st.sR.length - 1 : ℕ) : ℤ) =
      (legOf st.sR 0).b (ax0 hd) + riseDir Y e τ * ((riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) : ℕ) * Y.ell) := by
    rw [heq]; ring
  rw [this]; exact hfit0

/-! ## Within a segment -/

/-- **Two bricks of the same grown list are disjoint.** [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem disjoint_of_grown {m L H : ℕ} {hL : m + 1 ≤ L} {hH : 2 * m + 2 ≤ H} {l : List (BrickRec d)} (hg : Grown hL hH l)
    {j k : ℕ} (hjk : j ≠ k) (hj : j < l.length) (hk : k < l.length) :
    Disjoint (boxOf L H (legOf l j)) (boxOf L H (legOf l k)) := by
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · exact hg.isLeg.disjoint_boxOf h (by omega)
  · exact (hg.isLeg.disjoint_boxOf h (by omega)).symm

/-! ## The entry segments among themselves -/

/-- **`A` and the riser are disjoint**: the riser is beyond the top face of the pre-steered `A`.
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem disjoint_A_R (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {j : ℕ} (hj : j < st.sA.length) {k : ℕ}
    (hk : k < st.sR.length) : Disjoint (boxOf Y.L Y.H (legOf st.sA j)) (boxOf Y.L Y.H (legOf st.sR k)) := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
  have hRne : st.sR ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hu : riseDir Y e τ ≠ 0 := fun h => hRne (hI.invR.nil h)
  have hlenA := hI.invR.prev hRne
  obtain ⟨hR0k, hR00, -, -, -, -⟩ := boundsR Y hd hL hH a e τ hY hI hk
  have hsteer := (hI.invA.steer hu).mono (Nat.zero_le j) (show j ≤ Y.Pw by omega) (by omega)
  obtain ⟨hRax, hRs⟩ := hI.invR.axis_sign Y hd hL hH a e τ hRne hk
  have hAne : st.sA ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hAax : (legOf st.sA j).a = axOf hd e := by
    have := (hI.invA.grown hAne).axis_sign (k := j) hj; rw [hI.invA.zero hAne] at this; exact this.1
  have huval := riseUnit_val Y e τ hu
  have hu1 : riseDir Y e τ = 1 ∨ riseDir Y e τ = -1 := (riseDir_cases Y e τ).resolve_left hu
  rw [Set.disjoint_left]
  intro w hwA hwR
  -- `R_k`: along its axis `0`
  obtain ⟨h1, -⟩ := box_axis hwR
  rw [hRax, hRs, huval] at h1
  -- `A_j`: coordinate `0` is transverse
  obtain ⟨-, h2⟩ := box_trans hwA (i := ax0 hd) (by rw [hAax]; exact (axOf_ne_ax0 hd e).symm)
  obtain ⟨h3, -⟩ := box_trans hwA (i := ax0 hd) (by rw [hAax]; exact (axOf_ne_ax0 hd e).symm)
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  have hk0 : (0 : ℤ) ≤ Y.ell * k := by positivity
  rcases hu1 with h | h <;> rw [h] at h1 hR0k hR00 hsteer <;> linarith only [h1, h2, h3, hR0k, hR00, hsteer, hk0, hLeq, hLp0]

/-- **`A` and the jog are disjoint**: without a riser the jog is beyond the lateral face of the
pre-steered `A`; with a riser it is in another layer. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem disjoint_A_J (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {j : ℕ}
    (hj : j < st.sA.length) {k : ℕ} (hk : k < st.sJ.length) :
    Disjoint (boxOf Y.L Y.H (legOf st.sA j)) (boxOf Y.L Y.H (legOf st.sJ k)) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, hΔw, -, hρv, -, -, -, hWl, -, -, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hJne : st.sJ ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlenA := hI.invJ.prevA hJne
  have hAne : st.sA ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hAax : (legOf st.sA j).a = axOf hd e := by
    have := (hI.invA.grown hAne).axis_sign (k := j) hj; rw [hI.invA.zero hAne] at this; exact this.1
  obtain ⟨hJax, hJs⟩ := hI.invJ.axis_sign Y hd hL hH a e τ hJne hk
  obtain ⟨hJf, hJ0, -, -, -, -, hJht, -⟩ := boundsJ Y hd hL hH a e τ hY hI hNR hk
  rw [Set.disjoint_left]
  intro w hwA hwJ
  by_cases hu : riseDir Y e τ = 0
  · -- lateral face
    have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
    have hsteer := (hI.invA.latst hu).mono (Nat.zero_le j) (show j ≤ st.sA.length - 1 by omega) le_rfl
    have hEL : entryLast Y e τ st.sA st.sR = legOf st.sA (st.sA.length - 1) := by unfold entryLast; rw [if_pos hu]
    rw [hEL] at hJ0
    obtain ⟨h1, -⟩ := box_axis hwJ
    rw [hJax, hJs] at h1
    obtain ⟨h3, h2⟩ := box_trans hwA (i := latOf hd e) (by rw [hAax]; exact latOf_ne_axOf hd e)
    have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
    have hk0 : (0 : ℤ) ≤ Y.ell * k := by positivity
    rcases hv1 with h | h <;> rw [h] at h1 hJf hJ0 hsteer <;> linarith only [h1, h2, h3, hJf, hJ0, hsteer, hk0, hLeq, hLp0]
  · -- another layer
    obtain ⟨d', hsrc, hW1, -⟩ := riseDir_layers' Y e τ hY hu
    obtain ⟨-, -, -, hAht, -⟩ := boundsA Y hd hL hH a e τ hY hI hj
    obtain ⟨hA1, hA2⟩ := hAht hu
    have hτh := hτ.height
    rw [hsrc, Option.getD_some] at hτh
    have hτh' := abs_le.1 hτh
    have hJh := abs_le.1 hJht
    obtain ⟨h3, h2⟩ := box_trans hwA (i := ax0 hd) (by rw [hAax]; exact (axOf_ne_ax0 hd e).symm)
    obtain ⟨h5, h4⟩ := box_trans hwJ (i := ax0 hd) (by rw [hJax]; exact (latOf_ne_ax0 hd e).symm)
    have hu1 : riseDir Y e τ = 1 ∨ riseDir Y e τ = -1 := (riseDir_cases Y e τ).resolve_left hu
    rcases hu1 with h | h <;> rw [h] at hA1 hA2 hW1 <;>
      linarith only [h2, h3, h4, h5, hA1, hA2, hW1, hτh'.1, hτh'.2, hJh.1, hJh.2, hWl, hρv, hΔw, hLeq, hLpP, hP2, hPe, hP64, hell, hmH, hLp0]

/-- **The riser and the jog are disjoint**: the jog is beyond the lateral face of the last `P'` riser
bricks (pre-steered), and above the earlier ones. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem disjoint_R_J (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {k : ℕ}
    (hk : k < st.sR.length) {j : ℕ} (hj : j < st.sJ.length) :
    Disjoint (boxOf Y.L Y.H (legOf st.sR k)) (boxOf Y.L Y.H (legOf st.sJ j)) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, -, -, hρv, -, -, -, -, -, -, hPe, -, -, -, -, -, hPwe, -⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hJne : st.sJ ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hRne : st.sR ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hu : riseDir Y e τ ≠ 0 := fun h => hRne (hI.invR.nil h)
  obtain ⟨-, hneq, hfit⟩ := fits_riser_end Y hd hL hH a e τ hY hτ hI hJne hu
  set n := st.sR.length - 1 with hn
  obtain ⟨hRax, hRs⟩ := hI.invR.axis_sign Y hd hL hH a e τ hRne hk
  obtain ⟨hJax, hJs⟩ := hI.invJ.axis_sign Y hd hL hH a e τ hJne hj
  obtain ⟨hJf, hJ0, -, -, -, -, hJht, -⟩ := boundsJ Y hd hL hH a e τ hY hI hNR hj
  have hEL : entryLast Y e τ st.sA st.sR = legOf st.sR n := by unfold entryLast; rw [if_neg hu]
  rw [hEL] at hJ0
  have huval := riseUnit_val Y e τ hu
  have hu1 : riseDir Y e τ = 1 ∨ riseDir Y e τ = -1 := (riseDir_cases Y e τ).resolve_left hu
  have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  rw [Set.disjoint_left]
  intro w hwR hwJ
  by_cases hnear : n ≤ k + Y.Pw
  · -- near the turn: beyond the lateral face
    have hsteer := hI.invR.latst.mono (show riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) - Y.Pw ≤ k by rw [hneq]; omega)
      (show k ≤ n by omega) le_rfl
    obtain ⟨h1, -⟩ := box_axis hwJ
    rw [hJax, hJs] at h1
    obtain ⟨h3, h2⟩ := box_trans hwR (i := latOf hd e) (by rw [hRax]; exact latOf_ne_ax0 hd e)
    have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
    have hj0 : (0 : ℤ) ≤ Y.ell * j := by positivity
    rcases hv1 with h | h <;> rw [h] at h1 hJf hJ0 hsteer <;> linarith only [h1, h2, h3, hJf, hJ0, hsteer, hj0, hLeq, hLp0]
  · -- far below along the riser axis
    push Not at hnear
    obtain ⟨hbk, -, -, -, -, -⟩ := boundsR Y hd hL hH a e τ hY hI hk
    obtain ⟨hbn, -, -, -, -, -⟩ := boundsR Y hd hL hH a e τ hY hI (show n < st.sR.length by omega)
    obtain ⟨-, h1⟩ := box_axis hwR
    obtain ⟨h1', -⟩ := box_axis hwR
    rw [hRax, hRs, huval] at h1 h1'
    obtain ⟨h3, h2⟩ := box_trans hwJ (i := ax0 hd) (by rw [hJax]; exact (latOf_ne_ax0 hd e).symm)
    have hJh := abs_le.1 hJht
    obtain ⟨f1, f2, f3, f4⟩ := hfit
    have hkn : (k : ℤ) + Y.Pw + 1 ≤ n := by exact_mod_cast hnear
    have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
    have hkl : Y.ell * k + Y.ell * Y.Pw + Y.ell ≤ Y.ell * n := by
      have := mul_le_mul_of_nonneg_left hkn hl0
      linarith only [this]
    rcases hu1 with h | h <;> rw [h] at h1 h1' hbk hbn f1 f2 f3 f4 <;>
      linarith only [h1, h1', h2, h3, hbk, hbn, f1, f2, f3, f4, hJh.1, hJh.2, hkl, hPwe, hρv, hLeq, hLpP, hPe, hell, hmH, hLp0]

/-! ## The entry segments and the trunk -/

/-- **`A` and the trunk are disjoint**: beside each other (lanes `Λ_J` apart). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem disjoint_A_T (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {j : ℕ}
    (hj : j < st.sA.length) {k : ℕ} (hk : k < st.sT.length) :
    Disjoint (boxOf Y.L Y.H (legOf st.sA j)) (boxOf Y.L Y.H (legOf st.sT k)) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, hΔw, -, -, hρp, -, hlamJ, -, -, -, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hTne : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hAne : st.sA ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hAax : (legOf st.sA j).a = axOf hd e := by
    have := (hI.invA.grown hAne).axis_sign (k := j) hj; rw [hI.invA.zero hAne] at this; exact this.1
  obtain ⟨hTax, -⟩ := hI.invT.axis_sign Y hd hL hH a e hTne hk
  obtain ⟨-, hAlat, -, -, -⟩ := boundsA Y hd hL hH a e τ hY hI hj
  obtain ⟨-, -, -, -, hTlat, -, -⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ hk
  have hy := lane_tgtCell Y a e
  have hτl := abs_le.1 hτ.lateral
  have hAl := abs_le.1 hAlat
  have hTl := abs_le.1 hTlat
  have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  rw [Set.disjoint_left]
  intro w hwA hwT
  obtain ⟨h3, h2⟩ := box_trans hwA (i := latOf hd e) (by rw [hAax]; exact latOf_ne_axOf hd e)
  obtain ⟨h5, h4⟩ := box_trans hwT (i := latOf hd e) (by rw [hTax]; exact latOf_ne_axOf hd e)
  rw [hy] at hTl
  rcases hv1 with h | h <;> rw [h] at hTl <;>
    linarith only [h2, h3, h4, h5, hAl.1, hAl.2, hTl.1, hTl.2, hτl.1, hτl.2, hlamJ, hρp, hΔw, hLeq, hLpP, hP2, hPe, hP64, hell, hmH, hLp0]

/-- **The forward start of the trunk** dominates the riser and the jog along `e`:
`s w_e ≤ 2 s J_last.b_e + 2L + 2 < 2 s T₀.b_e + 1` for points of riser and jog boxes. [folklore] -/
theorem e_le_of_R_J (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hT : st.sT ≠ [])
    {r : BrickRec d} (hr : r ∈ st.sR ∨ r ∈ st.sJ) {w : Site d} (hw : w ∈ boxOf Y.L Y.H r.1) :
    (sgOf e : ℤ) * w (axOf hd e) ≤ 2 * ((sgOf e : ℤ) * (legOf st.sT 0).b (axOf hd e)) := by
  obtain ⟨hLp0, -, hLeq, -⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  obtain ⟨hJne, -⟩ := hI.invT.prev hT
  have hkJ : st.sJ.length - 1 < st.sJ.length := by have := List.length_pos_of_ne_nil hJne; omega
  have hface := (hI.invT.turn hT).face
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  -- `s b_e ≤ s J_last.b_e` for the brick
  suffices hb : (sgOf e : ℤ) * r.1.b (axOf hd e) ≤ (sgOf e : ℤ) * (legOf st.sJ (st.sJ.length - 1)).b (axOf hd e) ∧ r.1.a ≠ axOf hd e by
    obtain ⟨hb, hax⟩ := hb
    obtain ⟨h3, h2⟩ := box_trans hw (i := axOf hd e) (Ne.symm hax)
    rw [hface]
    rcases hs1 with h | h <;> rw [h] at hb ⊢ <;> linarith only [h2, h3, hb, hLeq, hLp0]
  have hJmono : ∀ j < st.sJ.length, (sgOf e : ℤ) * (legOf st.sJ j).b (axOf hd e) ≤ (sgOf e : ℤ) * (legOf st.sJ (st.sJ.length - 1)).b (axOf hd e) := by
    intro j hj
    have := hI.invJ.fwd.mono (Nat.zero_le j) (show j ≤ st.sJ.length - 1 by omega) le_rfl
    linarith
  rcases hr with hr | hr
  · obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr
    have hRne : st.sR ≠ [] := List.ne_nil_of_mem hr
    have hu : riseDir Y e τ ≠ 0 := fun h => hRne (hI.invR.nil h)
    obtain ⟨hRax, -⟩ := hI.invR.axis_sign Y hd hL hH a e τ hRne hk
    refine ⟨?_, by rw [show (recOf st.sR k).1 = legOf st.sR k from rfl, hRax]; exact (axOf_ne_ax0 hd e).symm⟩
    show (sgOf e : ℤ) * (legOf st.sR k).b (axOf hd e) ≤ _
    have h1 := hI.invR.fwd.mono (Nat.zero_le k) (show k ≤ st.sR.length - 1 by omega) le_rfl
    have h2 := hI.invJ.fwd0 hJne
    have hEL : entryLast Y e τ st.sA st.sR = legOf st.sR (st.sR.length - 1) := by unfold entryLast; rw [if_neg hu]
    rw [hEL] at h2
    have h3 := hJmono 0 (List.length_pos_of_ne_nil hJne)
    linarith
  · obtain ⟨j, hj, rfl⟩ := exists_recOf_of_mem hr
    obtain ⟨hJax, -⟩ := hI.invJ.axis_sign Y hd hL hH a e τ hJne hj
    refine ⟨hJmono j hj, by rw [show (recOf st.sJ j).1 = legOf st.sJ j from rfl, hJax]; exact latOf_ne_axOf hd e⟩

/-- **The riser, the jog and the trunk are disjoint**: the trunk is beyond the forward face.
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem disjoint_RJ_T (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {r : BrickRec d} (hr : r ∈ st.sR ∨ r ∈ st.sJ) {k : ℕ} (hk : k < st.sT.length) :
    Disjoint (boxOf Y.L Y.H r.1) (boxOf Y.L Y.H (legOf st.sT k)) := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hTne : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨hTax, hTs⟩ := hI.invT.axis_sign Y hd hL hH a e hTne hk
  obtain ⟨hTe, -, -, -, -, -, -⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ hk
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  rw [Set.disjoint_left]
  intro w hw hwT
  have h1 := e_le_of_R_J Y hd hL hH a e τ hY hτ hI hTne hr hw
  obtain ⟨h2, -⟩ := box_axis hwT
  rw [hTax, hTs, hTe] at h2
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  have hk0 : (0 : ℤ) ≤ Y.ell * k := by positivity
  rcases hs1 with h | h <;> rw [h] at h1 h2 <;> linarith only [h1, h2, hk0]

end BGNd

end Percolation.Literature

end
