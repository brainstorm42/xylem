import Percolation.Literature.TallRun2
import Percolation.Util.Linter

/-!
# The tall gait, XIX: the exit tokens

For the tall kit (Grimmett, *Percolation*, 2nd ed.
(1999), §7.3, proof of Lemma (7.52)), when the plan is complete: the lengths of the trunk and of the
branches are the scheduled ones; the three exit tokens (beyond the last trunk brick and the last
branch bricks) are admissible for the target cell in the straight and the two lateral directions;
an admissible token's centre lies in its cell; and the zone of an admissible token lies strictly
beyond (twice) the token's plane.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–176.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-! ## Lengths at completion -/

/-- **The trunk has the scheduled length** once the first branch has started. [folklore] -/
theorem length_sT_eq (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hB1 : st.sB1 ≠ []) :
    st.sT.length = legLen Y a e e ((legOf st.sT 0).b (axOf hd e)) + 1 := by
  obtain ⟨hTne, hdone, -⟩ := hI.invT.done hB1
  obtain ⟨h1, -, -, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hTne
  have hs := hI.invT.sched
  have hlen := List.length_pos_of_ne_nil hTne
  rcases Nat.lt_or_ge 1 st.sT.length with h2 | h2
  · have := hs (st.sT.length - 2) (by omega); omega
  · omega

/-- **A complete branch has the scheduled length.** [folklore] -/
theorem length_sB_eq {w : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w (some g) sB D)
    (hdone : legLen Y a e (latDir e (decide ((w : ℤ) = 1))) (g.1.b (latOf hd e)) ≤ sB.length) :
    sB.length = legLen Y a e (latDir e (decide ((w : ℤ) = 1))) (g.1.b (latOf hd e)) := by
  rcases Nat.eq_zero_or_pos sB.length with h0 | hpos
  · omega
  · have := hB.sched g rfl (sB.length - 1) (by omega); omega

/-- The head of a branch list, as an entry of the branch leg `sB ++ [g]`. [folklore] -/
theorem legOf_head_branch {r g : BrickRec d} {t : List (BrickRec d)} : legOf ((r :: t) ++ [g]) (t.length + 1) = r.1 := by
  rw [List.cons_append]
  have := legOf_cons_length r (t ++ [g])
  rwa [List.length_append, List.length_singleton] at this

/-! ## The position of an exit token -/

/-- The position of the exit token of a record: the base of the top step requested towards the trunk's nominal line. [folklore] -/
theorem exitTok_pos (r : BrickRec d) :
    (exitTok hd Y hL hH a e r).pos = (tStep hL hH r (toward (nomT hd Y e (Y.lane (tgtCell a e) e)) r.1.b)).b := rfl

/-- **Coordinates of an exit position**: along the record's axis exactly one brick length on; every
other coordinate within `L'` of the record's base and within `max(previous deviation, L')` of the
nominal line (`y` laterally, the layer vertically, `0` elsewhere). [cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
theorem exitTok_coords {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) :
    (exitTok hd Y hL hH a e r).pos r.1.a = r.1.b r.1.a + (r.1.s : ℤ) * ((Y.H : ℤ) + 1) ∧
      (∀ i, i ≠ r.1.a → |(exitTok hd Y hL hH a e r).pos i - r.1.b i| ≤ Y.Lp) ∧
      (∀ i, i ≠ r.1.a → |(exitTok hd Y hL hH a e r).pos i - nomT hd Y e (Y.lane (tgtCell a e) e) i| ≤
        max |r.1.b i - nomT hd Y e (Y.lane (tgtCell a e) e) i| Y.Lp) := by
  rw [exitTok_pos]
  obtain ⟨h1, h2⟩ := tStep_rel hL hH hg (toward (nomT hd Y e (Y.lane (tgtCell a e) e)) r.1.b)
  refine ⟨h1, fun i hi => ?_, fun i hi => ?_⟩
  · have := (h2 i hi).1; unfold TallLayout.Lp; exact this
  · have := abs_sub_le_of_toward hL hH hg (nom := nomT hd Y e (Y.lane (tgtCell a e) e)) hi rfl
    unfold TallLayout.Lp; exact this

omit [NeZero d] in
/-- Values of the trunk's nominal line. [folklore] -/
theorem nomT_vals (y : ℤ) : nomT hd Y e y (latOf hd e) = y ∧ nomT hd Y e y (ax0 hd) = Y.zOf e ∧
    ∀ j, j ≠ latOf hd e → j ≠ ax0 hd → nomT hd Y e y j = 0 := by
  unfold nomT
  refine ⟨by simp, by simp [(latOf_ne_ax0 hd e).symm], fun j h1 h2 => by simp [h1, h2]⟩

/-! ## The straight exit token is admissible -/

/-- **The straight exit token is admissible** for the target cell. [cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem tAdm_exit_straight (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hB1 : st.sB1 ≠ [])
    {rT : BrickRec d} {tT : List (BrickRec d)} (hT : st.sT = rT :: tT) (hg : GoodRec Y.m Y.L Y.H rT) :
    TAdm hd Y (tgtCell a e) e (exitTok hd Y hL hH a e rT) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hTne : st.sT ≠ [] := by rw [hT]; exact List.cons_ne_nil _ _
  have hlen := length_sT_eq Y hd hL hH a e τ hY hτ hI hB1
  set nE := legLen Y a e e ((legOf st.sT 0).b (axOf hd e)) with hnE
  have hk : nE < st.sT.length := by omega
  have hrT : legOf st.sT nE = rT.1 := by
    have : tT.length = nE := by rw [hT] at hlen; simp at hlen; omega
    rw [hT, ← this]; exact legOf_cons_length rT tT
  obtain ⟨hax, hsx⟩ := hI.invT.axis_sign Y hd hL hH a e hTne hk
  rw [hrT] at hax hsx
  obtain ⟨hbe, -, -, -, hlat, hht, hoth⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ hk
  rw [hrT] at hbe hlat hht hoth
  have hcell := trunk_in_cell Y hd hL hH a e τ hY hτ hI hk
  rw [hrT] at hcell
  obtain ⟨h1, h2, h3⟩ := exitTok_coords Y hd hL hH a e hg
  rw [hax, hsx] at h1
  rw [hax] at h2 h3
  obtain ⟨hny, hnz, hn0⟩ := nomT_vals Y hd e (Y.lane (tgtCell a e) e)
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  -- no room beyond the last trunk brick
  have hnE_lt : nE < Y.Rmax := by
    obtain ⟨-, h2', -, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hTne
    have : Y.NT < Y.Rmax := by
      unfold TallLayout.NT TallLayout.Rmax
      have hP8' : 8 ≤ Y.P := hY.hP
      have : 0 < Y.P ^ 3 := by positivity
      nlinarith
    omega
  have hend := of_firstIdx_lt (p := fun k => ¬roomT Y (tgtCell a e) e ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (k * Y.ell)))
    (N := Y.Rmax) hnE_lt
  change ¬roomT Y (tgtCell a e) e ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (nE * Y.ell)) at hend
  unfold roomT at hend
  have hbe' : (legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (nE * Y.ell) = rT.1.b (axOf hd e) := by rw [hbe]; ring
  rw [hbe'] at hend
  push Not at hend
  set pos := (exitTok hd Y hL hH a e rT).pos with hpos
  refine ⟨hax, ?_, ?_, ?_, ?_, fun h => absurd h (by simp [exitTok])⟩
  · -- longitudinal window
    have e1 : (sgOf e : ℤ) * (pos (axOf hd e) - Y.ctr (tgtCell a e) e.1) =
        (sgOf e : ℤ) * (rT.1.b (axOf hd e) - Y.ctr (tgtCell a e) e.1) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * ((Y.H : ℤ) + 1) := by
      rw [h1]; ring
    have e2 : (sgOf e : ℤ) * (rT.1.b (axOf hd e) + (sgOf e : ℤ) * Y.ell - Y.ctr (tgtCell a e) e.1) =
        (sgOf e : ℤ) * (rT.1.b (axOf hd e) - Y.ctr (tgtCell a e) e.1) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * Y.ell := by ring
    rw [e2, hss] at hend
    rw [e1, hss]
    constructor <;> linarith only [hend, hcell, hell]
  · -- lateral
    have := h3 (latOf hd e) (latOf_ne_axOf hd e)
    rw [hny] at this
    have hl := abs_le.1 hlat
    have hm : max |rT.1.b (latOf hd e) - Y.lane (tgtCell a e) e| Y.Lp ≤ Y.ρp := by
      apply max_le
      · rw [abs_le]; constructor <;> linarith only [hl.1, hl.2, hρp, hLp0, hΔ0, hell, hmH]
      · linarith only [hρp, hLp0, hΔ0, hell, hmH]
    exact this.trans hm
  · -- height
    have := h3 (ax0 hd) (axOf_ne_ax0 hd e).symm
    rw [hnz] at this
    simp only [exitTok, Option.getD_some]
    refine this.trans (max_le hht ?_)
    linarith only [hρv, hell, hmH]
  · intro j hj1 hj2 hj3
    have := h3 j hj1
    rw [hn0 j hj2 hj3, sub_zero, sub_zero] at this
    exact this.trans (max_le (hoth j hj1 hj2 hj3) le_rfl)

/-! ## The lateral exit tokens are admissible -/

omit [NeZero d] in
/-- The number of branch bricks is below the budget. [folklore] -/
theorem NB_lt_Rmax (hY : Y.OK) : Y.NB < Y.Rmax := by
  unfold TallLayout.NB TallLayout.Rmax
  have hP8' : 8 ≤ Y.P := hY.hP
  have : 0 < Y.P ^ 3 := by positivity
  nlinarith

/-- **A lateral exit token is admissible** for the target cell, in the lateral direction of the
branch. [cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem tAdm_exit_side (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {w' : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w' (some g) sB D)
    (hgf : brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
      IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp)
    (hdone : legLen Y a e (latDir e (decide ((w' : ℤ) = 1))) (g.1.b (latOf hd e)) ≤ sB.length)
    {rB : BrickRec d} {tB : List (BrickRec d)} (hBl : sB = rB :: tB) (hg : GoodRec Y.m Y.L Y.H rB) :
    TAdm hd Y (tgtCell a e) (latDir e (decide ((w' : ℤ) = 1))) (exitTok hd Y hL hH a e rB) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  obtain ⟨-, -, -, -, -, -, hallR⟩ := all_length_lt Y hd hL hH a e τ hY hτ hI
  have hlenT : st.sT.length ≤ Y.Rmax := by
    have : st.sT.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  have hTne : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨-, -, hn1, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hTne
  have h12 := n1Of_le_n2Of Y hd a e st.sT
  have hn1' : 1 ≤ brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) := by
    rcases Int.units_eq_one_or w' with rfl | rfl <;> rcases Int.units_eq_one_or (br1Sign e) with h | h
    · rw [← h]; exact hn1
    · have : -br1Sign e = 1 := by rw [h]; simp
      rw [← this]; exact hn1.trans h12
    · have : -br1Sign e = -1 := by rw [h]
      rw [← this]; exact hn1.trans h12
    · rw [← h]; exact hn1
  obtain ⟨hgax, hgs', hface, hTlat, hg0, hg1, -, -⟩ := boundsG Y hd hL hH a e τ hY hI hNR hNJ hlenT hgf rfl hn1'
  set e' := latDir e (decide ((w' : ℤ) = 1)) with he'
  set n := sB.length with hn
  have hlenB := length_sB_eq Y hd hL hH a e hB hdone
  have hrB : legOf (sB ++ [g]) n = rB.1 := by
    have : n = tB.length + 1 := by rw [hn, hBl]; rfl
    rw [hBl, this, legOf_head_branch]
  obtain ⟨hbf, hlng, hht, hoth⟩ := boundsB Y hd hL hH a e hB hgax hgs' (le_refl n)
  rw [hrB] at hbf hlng hht hoth
  have hax : rB.1.a = latOf hd e ∧ rB.1.s = w' := by
    have hne : sB ≠ [] := by rw [hBl]; exact List.cons_ne_nil _ _
    have := (hB.grown g rfl hne).axis_sign (k := n) (by simp [hn])
    rw [legOf_append_singleton_zero, hrB] at this; rw [this.1, this.2]; exact ⟨hgax, hgs'⟩
  have hcell := branch_in_cell Y hd hL hH a e τ hY hτ hI hB hgf (le_refl n)
  rw [hrB] at hcell
  obtain ⟨h1, h2, h3⟩ := exitTok_coords Y hd hL hH a e hg
  rw [hax.1, hax.2] at h1
  rw [hax.1] at h2 h3
  obtain ⟨hny, hnz, hn0⟩ := nomT_vals Y hd e (Y.lane (tgtCell a e) e)
  have hsw : (sgOf e' : ℤ) = w' := by
    rw [he', sgOf_latDir_val]; rcases Int.units_eq_one_or w' with h | h <;> simp [h]
  have hw2 : (w' : ℤ) * (w' : ℤ) = 1 := by rcases Int.units_eq_one_or w' with h | h <;> simp [h]
  have haxe' : axOf hd e' = latOf hd e := axOf_latDir hd e _
  have hlate' : latOf hd e' = axOf hd e := latOf_latDir hd e _
  have hctr : Y.ctr (tgtCell a e) e'.1 = Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ := rfl
  have hlane : Y.lane (tgtCell a e) e' = brLane Y a e w' := rfl
  -- no room beyond the last branch brick
  have hnB_lt : legLen Y a e e' (g.1.b (latOf hd e)) < Y.Rmax := by
    have := (branch_feasible Y hd hL hH a e τ hY hτ hI hlenT hgf rfl).2
    have := NB_lt_Rmax Y hY
    rw [← he'] at *; omega
  have hend := of_firstIdx_lt (p := fun k => ¬roomT Y (tgtCell a e) e' (g.1.b (latOf hd e) + (sgOf e' : ℤ) * (k * Y.ell))) (N := Y.Rmax) hnB_lt
  change ¬roomT Y (tgtCell a e) e' (g.1.b (latOf hd e) + (sgOf e' : ℤ) * (legLen Y a e e' (g.1.b (latOf hd e)) * Y.ell)) at hend
  unfold roomT at hend
  rw [hsw, hctr, ← hlenB] at hend
  have hbf' : g.1.b (latOf hd e) + (w' : ℤ) * (n * Y.ell) = rB.1.b (latOf hd e) := by rw [hbf]; ring
  rw [hbf'] at hend
  push Not at hend
  set pos := (exitTok hd Y hL hH a e rB).pos with hpos
  refine ⟨by rw [haxe']; exact hax.1, ?_, ?_, ?_, ?_, fun h => absurd h (by simp [exitTok])⟩
  · rw [haxe', hsw, hctr]
    have e1 : (w' : ℤ) * (pos (latOf hd e) - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) =
        (w' : ℤ) * (rB.1.b (latOf hd e) - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) +
          ((w' : ℤ) * (w' : ℤ)) * ((Y.H : ℤ) + 1) := by
      rw [h1]; ring
    have e2 : (w' : ℤ) * (rB.1.b (latOf hd e) + (w' : ℤ) * Y.ell - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) =
        (w' : ℤ) * (rB.1.b (latOf hd e) - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) + ((w' : ℤ) * (w' : ℤ)) * Y.ell := by
      ring
    rw [e2, hw2] at hend
    rw [e1, hw2]
    constructor <;> linarith only [hend, hcell, hell]
  · -- lateral: along `e`, near the port lane
    rw [hlate', hlane]
    have hpe := abs_le.1 (h2 (axOf hd e) (latOf_ne_axOf hd e).symm)
    have hl := abs_le.1 hlng
    rw [abs_le]
    rcases Int.units_eq_one_or (sgOf e) with h | h <;> rw [h] at hg0 hg1 <;> push_cast at hg0 hg1 <;> constructor <;>
      linarith only [hpe.1, hpe.2, hl.1, hl.2, hg0, hg1, hρp, hLp0, hΔ0, hell, hmH]
  · -- height
    have := h3 (ax0 hd) (latOf_ne_ax0 hd e).symm
    rw [hnz] at this
    simp only [exitTok, Option.getD_some]
    refine this.trans (max_le hht ?_)
    linarith only [hρv, hell, hmH]
  · intro j hj1 hj2 hj3
    rw [haxe'] at hj1; rw [hlate'] at hj2
    have := h3 j hj1
    rw [hn0 j hj1 hj3, sub_zero, sub_zero] at this
    exact this.trans (max_le (hoth j hj2 hj1 hj3) le_rfl)

/-! ## Admissible tokens lie in their cell -/

omit [NeZero d] in
/-- Floor division in a window: `(r + 2D c) / 2D = c` for `0 ≤ r < 2D`. [folklore] -/
theorem ediv_window {r D c : ℤ} (hD : 0 < D) (h0 : 0 ≤ r) (h1 : r < 2 * D) : (r + 2 * D * c) / (2 * D) = c := by
  rw [Int.add_mul_ediv_left _ _ (by positivity), Int.ediv_eq_zero_of_lt h0 h1, zero_add]

omit [NeZero d] in
/-- **The centre of an admissible token lies in the token's cell.** [folklore] -/
theorem TAdm.cellOf_eq (hY : Y.OK) {c : Site 2} {e' : MDir} {tok : TTok d} (h : TAdm hd Y c e' tok) : Y.cellOf hd tok.pos = c := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  have hl0 : (0 : ℤ) < Y.ell := by linarith only [hell, hmH]
  have hDh0 : 0 < Y.Dh := by rw [hDh]; positivity
  funext i
  unfold TallLayout.cellOf
  by_cases hi : i = e'.1
  · subst hi
    have hax : axOf hd (e'.1, true) = axOf hd e' := rfl
    rw [hax]
    obtain ⟨hlo, hhi⟩ := h.longit
    unfold TallLayout.ctr at hlo hhi
    set x := tok.pos (axOf hd e')
    -- `x + D/2 = r + 2 (D/2) c` with `r` in the window
    have : x + Y.Dh = (x - c e'.1 * (2 * Y.Dh) + Y.Dh) + 2 * Y.Dh * c e'.1 := by ring
    rw [this]
    apply ediv_window hDh0
    · rcases Int.units_eq_one_or (sgOf e') with hs | hs <;> rw [hs] at hlo hhi <;> push_cast at hlo hhi <;>
        linarith only [hlo, hhi, hell, hmH, hDh, hP3, hP2, hPe, hP64]
    · rcases Int.units_eq_one_or (sgOf e') with hs | hs <;> rw [hs] at hlo hhi <;> push_cast at hlo hhi <;>
        linarith only [hlo, hhi, hell, hmH, hDh, hP3, hP2, hPe, hP64]
  · have hi' : i = ⟨1 - e'.1.val, by have := e'.1.isLt; omega⟩ := by
      apply Fin.ext; have h1 := i.isLt; have h2 := e'.1.isLt
      have h3 : i.val ≠ e'.1.val := fun h' => hi (Fin.ext h')
      simp only; omega
    have hax : axOf hd (i, true) = latOf hd e' := by
      rw [hi']; unfold axOf latOf; apply Fin.ext; simp only; have := e'.1.isLt; omega
    rw [hax]
    have hlat := abs_le.1 h.lateral
    unfold TallLayout.lane TallLayout.nu TallLayout.ctr at hlat
    rw [← hi'] at hlat
    set x := tok.pos (latOf hd e')
    have hpar : TallLayout.cpar c = 0 ∨ TallLayout.cpar c = 1 := by unfold TallLayout.cpar; omega
    have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
    have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
    have hsmall : Y.ρp + Y.lam + Y.lamJ < Y.Dh := by
      linarith only [hρp, hlam, hlamJ, hDh, hΔw, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
    have : x + Y.Dh = (x - c i * (2 * Y.Dh) + Y.Dh) + 2 * Y.Dh * c i := by ring
    rw [this]
    apply ediv_window hDh0
    · rcases hpar with hp | hp <;> rw [hp] at hlat <;> split_ifs at hlat <;> linarith only [hlat.1, hlat.2, hsmall, hlam0, hlamJ0]
    · rcases hpar with hp | hp <;> rw [hp] at hlat <;> split_ifs at hlat <;> linarith only [hlat.1, hlat.2, hsmall, hlam0, hlamJ0]

/-! ## Zones lie beyond the token's plane -/

omit [NeZero d] in
/-- **The region of an admissible token lies strictly beyond twice the token's plane.**
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem zoneRegion_forward (hY : Y.OK) {c : Site 2} {e' : MDir} {tok : TTok d} (hτ' : TAdm hd Y c e' tok) {w : Site d}
    (hw : w ∈ zoneRegion Y hd c e' tok) : 1 ≤ (sgOf e' : ℤ) * (w (axOf hd e') - 2 * tok.pos (axOf hd e')) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  obtain ⟨-, hcases⟩ := hw
  rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨w', h1, -⟩
  · exact h1
  · linarith only [h1, hK0, hPwe, hLeq, hLpP, hPe, hell, hmH, hm0, hLp0]
  · linarith only [h1, hK0, hPwe, hLeq, hLpP, hPe, hell, hmH, hm0, hLp0]
  · linarith only [h1, hPwe, hLeq, hLpP, hPe, hell, hmH, hm0, hLp0]
  · -- the branch tube: its lane lies a full cell beyond the token
    have hbl := brLane_eq Y c e' w'
    have hc := ctr_tgtCell_fst Y c e'
    obtain ⟨-, hhi⟩ := hτ'.longit
    have hpar : TallLayout.cpar (tgtCell c e') = 0 ∨ TallLayout.cpar (tgtCell c e') = 1 := by unfold TallLayout.cpar; omega
    have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
    have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
    have hbig : 2 * Y.Lp + Y.K0 + 2 * Y.lam + 2 * Y.lamJ + 1 ≤ 2 * Y.Dh + 2 - 2 * (Y.Dh - 1) + 2 * (Y.Dh - 1) - 2 * Y.Dh + 2 * Y.Dh := by
      rw [hK0]; linarith only [hlam, hlamJ, hDh, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0, hm0]
    have hss : (sgOf e' : ℤ) * (sgOf e' : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e') with h | h <;> simp [h]
    -- `s (brLane - pos) ≥ D/2 + 1 - Λ - Λ_J`
    have key : Y.Dh + 1 - Y.lam - Y.lamJ ≤ (sgOf e' : ℤ) * (brLane Y c e' w' - tok.pos (axOf hd e')) := by
      rw [hbl, hc]
      have e1 : (sgOf e' : ℤ) * (Y.ctr c e'.1 + (sgOf e' : ℤ) * (2 * Y.Dh) + (if (w' : ℤ) = 1 then Y.lam else -Y.lam) +
          TallLayout.cpar (tgtCell c e') * Y.lamJ - tok.pos (axOf hd e')) =
          -((sgOf e' : ℤ) * (tok.pos (axOf hd e') - Y.ctr c e'.1)) + ((sgOf e' : ℤ) * (sgOf e' : ℤ)) * (2 * Y.Dh) +
            (sgOf e' : ℤ) * ((if (w' : ℤ) = 1 then Y.lam else -Y.lam) + TallLayout.cpar (tgtCell c e') * Y.lamJ) := by ring
      rw [e1, hss]
      have hs1 : (sgOf e' : ℤ) = 1 ∨ (sgOf e' : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e') with h | h <;> simp [h]
      rcases hs1 with hs | hs <;> rw [hs] at hhi ⊢ <;> rcases hpar with hp | hp <;> rw [hp] <;> split_ifs <;>
        linarith only [hhi, hlam0, hlamJ0]
    have e2 : (sgOf e' : ℤ) * (w (axOf hd e') - 2 * tok.pos (axOf hd e')) =
        (sgOf e' : ℤ) * (w (axOf hd e') - 2 * brLane Y c e' w') + 2 * ((sgOf e' : ℤ) * (brLane Y c e' w' - tok.pos (axOf hd e'))) := by ring
    rw [e2]
    linarith only [h1, key, hbig]

/-! ## The direction and the reported provenance of admissible tokens -/

omit [NeZero d] in
/-- **An admissible token's direction is read off correctly.** [folklore] -/
theorem dirOf_eq (hY : Y.OK) {c : Site 2} {e' : MDir} {tok : TTok d} (h : TAdm hd Y c e' tok) : dirOf Y hd tok = e' := by
  obtain ⟨-, -, -, hell, hmH, -, -, -, -, -, -, -, -, -, hDh, -, hPe, hP2, hP3, -, -, hP64, -⟩ := hY.facts
  have hax : tok.ax = axOf hd e' := h.ax_eq
  have hi : (⟨(tok.ax.val - 1) % 2, Nat.mod_lt _ Nat.two_pos⟩ : Fin 2) = e'.1 := by
    apply Fin.ext; rw [hax]; unfold axOf; simp only; have := e'.1.isLt; omega
  unfold dirOf
  rw [hi, h.cellOf_eq Y hd hY, hax]
  obtain ⟨hlo, -⟩ := h.longit
  have hpos : 0 < Y.Dh - Y.ell := by linarith only [hDh, hP3, hP2, hPe, hP64, hell, hmH]
  obtain ⟨i, b⟩ := e'
  simp only [Prod.mk.injEq, true_and]
  cases b
  · have hs : (sgOf (i, false) : ℤ) = -1 := rfl
    rw [hs] at hlo
    simp only [decide_eq_false_iff_not, not_lt]
    linarith only [hlo, hpos]
  · have hs : (sgOf (i, true) : ℤ) = 1 := rfl
    rw [hs] at hlo
    simp only [decide_eq_true_eq]
    linarith only [hlo, hpos]

omit [NeZero d] in
/-- **The reported provenance of an admissible token** with a source other than the reverse of its direction. [folklore] -/
theorem srcDirK_of_adm (hY : Y.OK) {c : Site 2} {e' e'' : MDir} {tok : TTok d} (h : TAdm hd Y c e' tok)
    (hs : tok.src = some e'') (hne : e'' ≠ rev e') : srcDirK Y hd tok = some e'' := by
  have hdir := dirOf_eq Y hd hY h
  unfold srcDirK; rw [hs]; simp only [hdir, hne, if_false]

omit [NeZero d] in
/-- **An admissible token with the nominal provenance "from behind" reports none.** [folklore] -/
theorem srcDirK_of_adm_rev (hY : Y.OK) {c : Site 2} {e' : MDir} {tok : TTok d} (h : TAdm hd Y c e' tok)
    (hs : tok.src = some (rev e')) : srcDirK Y hd tok = none := by
  have hdir := dirOf_eq Y hd hY h
  unfold srcDirK; rw [hs]; simp only [hdir, if_true]

omit [NeZero d] in
/-- What a reported provenance tells about the source. [folklore] -/
theorem srcDirK_cases (hY : Y.OK) {c : Site 2} {e' e'' : MDir} {tok : TTok d} (h : TAdm hd Y c e' tok)
    (hs : tok.src = some e'') : srcDirK Y hd tok = some e'' ∨ e'' = rev e' := by
  by_cases hne : e'' = rev e'
  · exact Or.inr hne
  · exact Or.inl (srcDirK_of_adm Y hd hY h hs hne)

end BGNd

end Percolation.Literature

end
