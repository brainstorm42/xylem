import Percolation.Literature.TallBounds
import Percolation.Util.Linter

/-!
# The tall gait, XII: feasibility of the schedules

The riser reaches the band of the target layer and the
jog reaches the band of the trunk lane within `N₁` bricks; the trunk has room, meets the two branch
lanes in order and before its end, within `N_T` bricks; the branches have room and end within `N_B`
bricks; hence an attempt places fewer than `R` bricks (Grimmett, *Percolation*, 2nd ed. (1999),
§7.3 p. 174: "there exists an absolute constant `R` such that … uses no more than `R` bricks").

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

omit [NeZero d] in
/-- **A window sliding by `ℓ` meets a band of width `2ℓ`.** If the band lies at oriented distance
`D ≥ ℓ + m + 1` ahead, some `k ≤ (D + m + 2)/ℓ` steps fit. [folklore] -/
theorem exists_fit (hY : Y.OK) (b z u : ℤ) (hu : u = 1 ∨ u = -1) (hD : (Y.ell : ℤ) + Y.m + 1 ≤ u * (z - b)) :
    ∃ k : ℕ, (k : ℤ) * Y.ell ≤ u * (z - b) + Y.m + 2 ∧ fits Y (b + u * (k * Y.ell)) u z := by
  obtain ⟨-, -, -, hell, hmH, -⟩ := hY.facts
  set D := u * (z - b) with hD'
  have hl0 : (0 : ℤ) < Y.ell := by unfold TallLayout.ell; push_cast; omega
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  set q := (D + Y.m + 2) / Y.ell with hq
  have hq0 : 0 ≤ q := Int.ediv_nonneg (by linarith) hl0.le
  have hq1 : q * Y.ell ≤ D + Y.m + 2 := Int.ediv_mul_le _ hl0.ne'
  have hq2 : D + Y.m + 2 < (q + 1) * Y.ell := by
    have := Int.lt_ediv_add_one_mul_self (D + Y.m + 2) hl0
    linarith
  refine ⟨q.toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hq0]; exact hq1
  · rw [Int.toNat_of_nonneg hq0]
    unfold fits
    rcases hu with rfl | rfl
    · simp only [one_mul] at hD' ⊢
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    · simp only [neg_mul, one_mul, neg_sub] at hD' ⊢
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

omit [NeZero d] in
/-- A fit at `k` bounds the schedule: `firstIdx ≤ k`. [folklore] -/
theorem firstIdx_le_of {p : ℕ → Prop} {N k : ℕ} (hk : p k) : firstIdx p N ≤ k := by
  unfold firstIdx; exact Nat.find_min' _ (Or.inl hk)

omit [NeZero d] in
/-- The layers of two macro-directions differ by a multiple of `W`, at most `3W`. [folklore] -/
theorem zOf_sub_zOf (e e' : MDir) : ∃ j : ℤ, Y.zOf e - Y.zOf e' = j * Y.Wl ∧ -3 ≤ j ∧ j ≤ 3 := by
  have h1 : TallLayout.layerIdx e ≤ 3 := by unfold TallLayout.layerIdx; have := e.1.isLt; split_ifs <;> omega
  have h2 : TallLayout.layerIdx e' ≤ 3 := by unfold TallLayout.layerIdx; have := e'.1.isLt; split_ifs <;> omega
  refine ⟨(TallLayout.layerIdx e : ℤ) - TallLayout.layerIdx e', by unfold TallLayout.zOf; ring, by omega, by omega⟩

/-- **The riser is feasible**: it turns within `N₁` bricks (at a brick whose window fits the band of
the target layer). [cite: GrimmettPercolation1999, §7.3 pp. 172–173] -/
theorem riser_feasible (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hR : st.sR ≠ []) :
    riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁ := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, hΔw, hΔ0, hρv, -, -, -, hWl, -, hN1, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  have hu : riseDir Y e τ ≠ 0 := fun h => hR (hI.invR.nil h)
  have hk : 0 < st.sR.length := List.length_pos_of_ne_nil hR
  obtain ⟨-, hR0, -, -, -, -⟩ := boundsR Y hd hL hH a e τ hY hI hk
  have hlenA := hI.invR.prev hR
  obtain ⟨-, -, -, hAht, -⟩ := boundsA Y hd hL hH a e τ hY hI (show Y.Pw < st.sA.length by omega)
  obtain ⟨hA0, hA1⟩ := hAht hu
  have hτh := hτ.height
  obtain ⟨d', hsrc⟩ : ∃ d', τ.src = some d' := by
    unfold riseDir at hu
    cases h : τ.src with
    | none => rw [h] at hu; exact absurd rfl hu
    | some d' => exact ⟨d', rfl⟩
  rw [hsrc, Option.getD_some] at hτh
  have hτh' := abs_le.1 hτh
  obtain ⟨j, hj, hj1, hj2⟩ := zOf_sub_zOf Y e d'
  have hudef : riseDir Y e τ = (if Y.zOf d' < Y.zOf e then 1 else if Y.zOf e < Y.zOf d' then -1 else 0) := by
    unfold riseDir; rw [hsrc]
  set u := riseDir Y e τ with hu'
  set b := (legOf st.sR 0).b (ax0 hd) with hb
  have hW0 : 0 < Y.Wl := by rw [hWl]; linarith only [hP64, hP2, hPe, hell, hmH]
  -- the riser direction is the sign of `j`
  have huj : (u = 1 ∧ 1 ≤ j) ∨ (u = -1 ∧ j ≤ -1) := by
    rw [hudef]
    split_ifs with h1 h2
    · left; refine ⟨rfl, ?_⟩
      by_contra hj0; push Not at hj0
      have : j * Y.Wl ≤ 0 * Y.Wl := mul_le_mul_of_nonneg_right (by omega) hW0.le
      linarith only [this, h1, hj]
    · right; refine ⟨rfl, ?_⟩
      by_contra hj0; push Not at hj0
      have : 0 * Y.Wl ≤ j * Y.Wl := mul_le_mul_of_nonneg_right (by omega) hW0.le
      linarith only [this, h2, hj]
    · exfalso; apply hu; show u = 0; rw [hudef, if_neg h1, if_neg h2]
  -- the oriented distance to climb is between `W - ρ_v - Δ_w - L - 1` and `3W + ρ_v`
  have hdist : Y.Wl - Y.ρv - Y.Δw - Y.L - 1 ≤ u * (Y.zOf e - b) ∧ u * (Y.zOf e - b) ≤ 3 * Y.Wl + Y.ρv := by
    rcases huj with ⟨hu1, hj'⟩ | ⟨hu1, hj'⟩
    · rw [hu1] at hA0 hA1 hR0 ⊢
      have h3 : Y.Wl ≤ j * Y.Wl := le_mul_of_one_le_left hW0.le hj'
      have h4 : j * Y.Wl ≤ 3 * Y.Wl := mul_le_mul_of_nonneg_right hj2 hW0.le
      constructor <;> linarith only [h3, h4, hj, hA0, hA1, hR0, hτh'.1, hτh'.2]
    · rw [hu1] at hA0 hA1 hR0 ⊢
      have h3 : j * Y.Wl ≤ (-1) * Y.Wl := mul_le_mul_of_nonneg_right hj' hW0.le
      have h4 : (-3) * Y.Wl ≤ j * Y.Wl := mul_le_mul_of_nonneg_right hj1 hW0.le
      constructor <;> linarith only [h3, h4, hj, hA0, hA1, hR0, hτh'.1, hτh'.2]
  have hu1 : u = 1 ∨ u = -1 := huj.imp (·.1) (·.1)
  obtain ⟨k, hk1, hfit⟩ := exists_fit Y hY b (Y.zOf e) u hu1
    (by linarith only [hdist.1, hWl, hρv, hΔw, hLeq, hLpP, hP2, hPe, hP64, hell, hmH])
  have hkN : k ≤ Y.N₁ := by
    have hl0 : (0 : ℤ) < Y.ell := by linarith only [hell, hmH]
    have : (k : ℤ) * Y.ell ≤ (Y.N₁ : ℤ) * Y.ell := by
      rw [hN1]; linarith only [hk1, hdist.2, hWl, hρv, hLpP, hP2, hPe, hell, hmH]
    exact_mod_cast le_of_mul_le_mul_right this hl0
  exact (firstIdx_le_of (N := Y.Rmax) hfit).trans hkN

/-- **The jog is feasible**: it turns within `N₁` bricks. [cite: GrimmettPercolation1999, §7.3 pp. 172–173] -/
theorem jog_feasible (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hJ : st.sJ ≠ []) :
    jogLen Y a e ((legOf st.sJ 0).b (latOf hd e)) ≤ Y.N₁ := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, hΔw, hΔ0, hρv, hρp, -, hlamJ, -, -, hN1, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  have hNR : st.sR ≠ [] → riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁ := fun hR => riser_feasible Y hd hL hH a e τ hY hτ hI hR
  have hk : 0 < st.sJ.length := List.length_pos_of_ne_nil hJ
  obtain ⟨-, hJ0, -, -, -, -, -, -⟩ := boundsJ Y hd hL hH a e τ hY hI hNR hk
  obtain ⟨-, -, hElat⟩ := bounds_entryLast Y hd hL hH a e τ hY hI hJ hNR
  have hτl := abs_le.1 hτ.lateral
  have hEl := abs_le.1 hElat
  have hy := lane_tgtCell Y a e
  set v : ℤ := (jogDir a e : ℤ) with hv
  have hv1 : v = 1 ∨ v = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [hv, h]
  set b := (legOf st.sJ 0).b (latOf hd e) with hb
  have hdist : Y.lamJ - (Y.L + 1) - (Y.Lp + Y.Δw) - Y.ρp ≤ v * (Y.lane (tgtCell a e) e - b) ∧
      v * (Y.lane (tgtCell a e) e - b) ≤ Y.lamJ + (Y.Lp + Y.Δw) + Y.ρp := by
    rw [hy, hJ0]
    rcases hv1 with h | h <;> rw [h] <;> constructor <;> linarith only [hEl.1, hEl.2, hτl.1, hτl.2]
  obtain ⟨k, hk1, hfit⟩ := exists_fit Y hY b (Y.lane (tgtCell a e) e) v hv1
    (by linarith only [hdist.1, hlamJ, hρv, hρp, hΔw, hLeq, hLpP, hP2, hPe, hP64, hell, hmH, hLp0])
  have hkN : k ≤ Y.N₁ := by
    have hl0 : (0 : ℤ) < Y.ell := by linarith only [hell, hmH]
    have : (k : ℤ) * Y.ell ≤ (Y.N₁ : ℤ) * Y.ell := by
      rw [hN1]; linarith only [hk1, hdist.2, hlamJ, hρv, hρp, hΔw, hLpP, hP2, hPe, hP64, hell, hmH, hLp0]
    exact_mod_cast le_of_mul_le_mul_right this hl0
  exact (firstIdx_le_of (N := Y.Rmax) hfit).trans hkN

end BGNd

end Percolation.Literature

end

namespace Percolation.Literature.BGNd

open LatticeModels Contour
open scoped Classical

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

namespace TallLayout
/-- A bound for the length of the trunk, `N_T = 2¹¹ P³ + 3`. [folklore] -/
def NT (Y : TallLayout) : ℕ := 2 ^ 11 * Y.P ^ 3 + 3
/-- A bound for the length of a branch, `N_B = 1536 P³`. [folklore] -/
def NB (Y : TallLayout) : ℕ := 1536 * Y.P ^ 3
end TallLayout

/-- The schedule bounds of the riser and the jog, packaged. [folklore] -/
theorem sched_bounds (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) :
    (st.sR ≠ [] → riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁) ∧
      (st.sJ ≠ [] → jogLen Y a e ((legOf st.sJ 0).b (latOf hd e)) ≤ Y.N₁) :=
  ⟨fun h => riser_feasible Y hd hL hH a e τ hY hτ hI h, fun h => jog_feasible Y hd hL hH a e τ hY hτ hI h⟩

/-- **The start of the trunk relative to the target cell**: far behind the centre along `e`. [folklore] -/
theorem boundsT0_ctr (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hT : st.sT ≠ []) :
    -Y.Dh - Y.ell + Y.Pw * Y.ell + Y.L + 1 ≤ (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - Y.ctr (tgtCell a e) e.1) ∧
      (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - Y.ctr (tgtCell a e) e.1) ≤
        -Y.Dh - 1 + (Y.Pw * Y.ell + Y.H + 2 * Y.N₁ * Y.Lp + Y.ell + Y.Lp + Y.L + 1) := by
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  obtain ⟨-, hlo, hhi, -, -, -, -⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ (List.length_pos_of_ne_nil hT)
  obtain ⟨hτ1, hτ2⟩ := hτ.longit
  have hc := ctr_tgtCell_fst Y a e
  have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have e1 : (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - Y.ctr (tgtCell a e) e.1) =
      (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - τ.pos (axOf hd e)) + (sgOf e : ℤ) * (τ.pos (axOf hd e) - Y.ctr a e.1) -
        ((sgOf e : ℤ) * (sgOf e : ℤ)) * (2 * Y.Dh) := by rw [hc]; ring
  rw [e1, hs]
  constructor <;> linarith

omit [NeZero d] in
/-- The lateral direction of sign `b`: its sign and its centre coordinate. [folklore] -/
theorem sgOf_latDir_val (b : Bool) : (sgOf (latDir e b) : ℤ) = if b then 1 else -1 := by
  rw [sgOf_latDir]; split_ifs <;> rfl

/-- **The trunk is feasible**: it has room at its start, meets the first branch lane after its start,
the second before its end, and ends within `N_T` bricks. [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem trunk_feasible (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hT : st.sT ≠ []) :
    1 ≤ legLen Y a e e ((legOf st.sT 0).b (axOf hd e)) ∧ legLen Y a e e ((legOf st.sT 0).b (axOf hd e)) ≤ Y.NT ∧
      1 ≤ n1Of hd Y a e st.sT ∧ n2Of hd Y a e st.sT ≤ legLen Y a e e ((legOf st.sT 0).b (axOf hd e)) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  obtain ⟨hlo, hhi⟩ := boundsT0_ctr Y hd hL hH a e τ hY hτ hI hT
  set b := (legOf st.sT 0).b (axOf hd e) with hb
  set X := Y.ctr (tgtCell a e) e.1 with hX
  have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hl0 : (0 : ℤ) < Y.ell := by linarith only [hell, hmH]
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  -- room at index k, in terms of `s (b - X) + k ℓ`
  have hroom : ∀ k : ℕ, roomT Y (tgtCell a e) e (b + (sgOf e : ℤ) * (k * Y.ell)) ↔
      (sgOf e : ℤ) * (b - X) + k * Y.ell + Y.ell ≤ Y.Dh - 1 - Y.ell := by
    intro k
    unfold roomT
    have e1 : (sgOf e : ℤ) * (b + (sgOf e : ℤ) * (k * Y.ell) + (sgOf e : ℤ) * Y.ell - X) =
        (sgOf e : ℤ) * (b - X) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * (k * Y.ell + Y.ell) := by ring
    rw [e1, hs]; constructor <;> intro h <;> linarith
  -- passing the lanes at index k
  have hpass : ∀ (w : ℤˣ) (k : ℕ), passed Y e (tgtCell a e) w (b + (sgOf e : ℤ) * (k * Y.ell)) ↔
      -((Y.m : ℤ) + 1) ≤ (sgOf e : ℤ) * (b - X) + k * Y.ell - (sgOf e : ℤ) * ((if (w : ℤ) = 1 then Y.lam else -Y.lam) +
        TallLayout.cpar (tgtCell a e) * Y.lamJ) := by
    intro w k
    rw [passed_iff, ← brLane, brLane_eq]
    have e1 : (sgOf e : ℤ) * (b + (sgOf e : ℤ) * (k * Y.ell) - (X + (if (w : ℤ) = 1 then Y.lam else -Y.lam) +
        TallLayout.cpar (tgtCell a e) * Y.lamJ)) = (sgOf e : ℤ) * (b - X) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * (k * Y.ell) -
        (sgOf e : ℤ) * ((if (w : ℤ) = 1 then Y.lam else -Y.lam) + TallLayout.cpar (tgtCell a e) * Y.lamJ) := by ring
    rw [e1, hs, one_mul]
  have hpar : TallLayout.cpar (tgtCell a e) = 0 ∨ TallLayout.cpar (tgtCell a e) = 1 := by unfold TallLayout.cpar; omega
  -- the lane term is bounded by `Λ + Λ_J`
  have hlane : ∀ w : ℤˣ, |(sgOf e : ℤ) * ((if (w : ℤ) = 1 then Y.lam else -Y.lam) + TallLayout.cpar (tgtCell a e) * Y.lamJ)| ≤
      Y.lam + Y.lamJ := by
    intro w
    have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
    have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
    rcases Int.units_eq_one_or (sgOf e) with h | h <;> rcases hpar with hp | hp <;> simp only [h, hp, Units.val_one, Units.val_neg] <;>
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- room at the start
    by_contra h0
    push Not at h0
    have h0' : legLen Y a e e b = 0 := by omega
    have hsp := of_firstIdx_lt (p := fun k => ¬roomT Y (tgtCell a e) e (b + (sgOf e : ℤ) * (k * Y.ell))) (N := Y.Rmax)
      (by rw [← legLen, h0']; exact hRpos)
    rw [← legLen, h0'] at hsp
    change ¬roomT Y (tgtCell a e) e (b + (sgOf e : ℤ) * ((0 : ℕ) * Y.ell)) at hsp
    rw [hroom] at hsp; push Not at hsp; push_cast at hsp
    linarith only [hsp, hhi, hPwe, hNL, hDh, hP3, hP2, hPe, hLpP, hLeq, hell, hmH, hLp0]
  · -- no room at `N_T`
    apply firstIdx_le_of
    rw [hroom]; push Not
    have : ((Y.NT : ℕ) : ℤ) * Y.ell = 2 * Y.Dh + 3 * Y.ell := by unfold TallLayout.NT; rw [hDh]; push_cast; ring
    linarith only [this, hlo, hPwe, hPe, hLeq, hLp0, hell, hmH, hm0]
  · -- the first lane is not yet passed at the start
    by_contra h0
    push Not at h0
    have h0' : n1Of hd Y a e st.sT = 0 := by omega
    have hsp := of_firstIdx_lt (p := fun k => passed Y e (tgtCell a e) (br1Sign e) (b + (sgOf e : ℤ) * (k * Y.ell))) (N := Y.Rmax)
      (by show n1Of hd Y a e st.sT < Y.Rmax; rw [h0']; exact hRpos)
    rw [← brIdx] at hsp
    have h0'' : brIdx Y a e (br1Sign e) b = 0 := h0'
    rw [h0''] at hsp
    change passed Y e (tgtCell a e) (br1Sign e) (b + (sgOf e : ℤ) * ((0 : ℕ) * Y.ell)) at hsp
    rw [hpass] at hsp; push_cast at hsp
    have := abs_le.1 (hlane (br1Sign e))
    linarith only [hsp, this, hhi, hPwe, hNL, hDh, hlam, hlamJ, hP3, hP2, hPe, hLpP, hLeq, hell, hmH, hLp0, hP32]
  · -- the second lane is passed at the end of the trunk
    set nE := legLen Y a e e b with hnE
    have hnE_lt : nE < Y.Rmax := by
      have h1 : nE ≤ Y.NT := by
        apply firstIdx_le_of
        rw [hroom]; push Not
        have : ((Y.NT : ℕ) : ℤ) * Y.ell = 2 * Y.Dh + 3 * Y.ell := by unfold TallLayout.NT; rw [hDh]; push_cast; ring
        linarith only [this, hlo, hPwe, hPe, hLeq, hLp0, hell, hmH, hm0]
      have h2 : Y.NT < Y.Rmax := by
        unfold TallLayout.NT TallLayout.Rmax
        have hP8' : 8 ≤ Y.P := by exact_mod_cast hP8
        have : 0 < Y.P ^ 3 := by positivity
        nlinarith
      omega
    have hend := of_firstIdx_lt (p := fun k => ¬roomT Y (tgtCell a e) e (b + (sgOf e : ℤ) * (k * Y.ell))) (N := Y.Rmax) hnE_lt
    change ¬roomT Y (tgtCell a e) e (b + (sgOf e : ℤ) * (nE * Y.ell)) at hend
    rw [hroom] at hend; push Not at hend
    apply firstIdx_le_of
    rw [hpass]
    have := abs_le.1 (hlane (-br1Sign e))
    linarith only [hend, this, hDh, hlam, hlamJ, hP3, hP2, hPe, hell, hmH, hm0]

end Percolation.Literature.BGNd

namespace Percolation.Literature.BGNd

open LatticeModels Contour
open scoped Classical

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- **A branch is feasible**: it has room at its start and ends within `N_B` bricks.
[cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem branch_feasible (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hlen : st.sT.length ≤ Y.Rmax)
    {w : ℤˣ} {g : BrickRec d} {n : ℕ}
    (hg : n < st.sT.length ∧ IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w (legOf st.sT n) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp)
    (hn : n = brIdx Y a e w ((legOf st.sT 0).b (axOf hd e))) :
    0 < legLen Y a e (latDir e (decide ((w : ℤ) = 1))) (g.1.b (latOf hd e)) ∧
      legLen Y a e (latDir e (decide ((w : ℤ) = 1))) (g.1.b (latOf hd e)) ≤ Y.NB := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hT : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨-, -, hn1, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hT
  have hn1' : 1 ≤ n := by
    rw [hn]
    rcases Int.units_eq_one_or w with rfl | rfl
    · -- either the first or the second branch sign
      by_cases hb : br1Sign e = 1
      · rw [← hb]; exact hn1
      · have : -br1Sign e = 1 := by rcases Int.units_eq_one_or (br1Sign e) with h | h <;> [exact absurd h hb; (rw [h]; simp)]
        rw [← this]; exact hn1.trans (n1Of_le_n2Of Y hd a e st.sT)
    · by_cases hb : br1Sign e = -1
      · rw [← hb]; exact hn1
      · have : -br1Sign e = -1 := by rcases Int.units_eq_one_or (br1Sign e) with h | h <;> [(rw [h]); exact absurd h hb]
        rw [← this]; exact hn1.trans (n1Of_le_n2Of Y hd a e st.sT)
  obtain ⟨-, -, hface, hTlat, -, -, -, -⟩ := boundsG Y hd hL hH a e τ hY hI hNR hNJ hlen hg hn hn1'
  set b := g.1.b (latOf hd e) with hb
  set Xf := Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ with hXf
  have hsw : (sgOf (latDir e (decide ((w : ℤ) = 1))) : ℤ) = w := by
    rw [sgOf_latDir_val]; rcases Int.units_eq_one_or w with h | h <;> simp [h]
  have hw2 : (w : ℤ) * (w : ℤ) = 1 := by rcases Int.units_eq_one_or w with h | h <;> simp [h]
  have hctr : Y.ctr (tgtCell a e) (latDir e (decide ((w : ℤ) = 1))).1 = Xf := rfl
  have hroom : ∀ k : ℕ, roomT Y (tgtCell a e) (latDir e (decide ((w : ℤ) = 1))) (b + (w : ℤ) * (k * Y.ell)) ↔
      (w : ℤ) * (b - Xf) + k * Y.ell + Y.ell ≤ Y.Dh - 1 - Y.ell := by
    intro k
    unfold roomT
    rw [hsw, hctr]
    have e1 : (w : ℤ) * (b + (w : ℤ) * (k * Y.ell) + (w : ℤ) * Y.ell - Xf) = (w : ℤ) * (b - Xf) + ((w : ℤ) * (w : ℤ)) * (k * Y.ell + Y.ell) := by
      ring
    rw [e1, hw2]; constructor <;> intro h <;> linarith
  -- the lateral position of the branch brick relative to the centre
  have hy : Y.lane (tgtCell a e) e = Xf + Y.nu e + TallLayout.cpar (tgtCell a e) * Y.lamJ := rfl
  have hnu : |Y.nu e| ≤ Y.lam := by
    have : 0 ≤ Y.lam := by rw [hlam]; positivity
    unfold TallLayout.nu; split_ifs <;> simp [abs_le, this]
  have hpar : TallLayout.cpar (tgtCell a e) = 0 ∨ TallLayout.cpar (tgtCell a e) = 1 := by unfold TallLayout.cpar; omega
  have hparJ : |TallLayout.cpar (tgtCell a e) * Y.lamJ| ≤ Y.lamJ := by
    have : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
    rcases hpar with h | h <;> simp [h, abs_le, this]
  have hTl := abs_le.1 hTlat
  have hnu' := abs_le.1 hnu
  have hparJ' := abs_le.1 hparJ
  have hQ : |(w : ℤ) * (b - Xf) - (Y.L + 1)| ≤ Y.ell + Y.Lp + 4 * Y.Δw + Y.lam + Y.lamJ := by
    rw [hface]
    have e1 : (w : ℤ) * ((legOf st.sT n).b (latOf hd e) + (w : ℤ) * ((Y.L : ℤ) + 1) - Xf) - (Y.L + 1) =
        (w : ℤ) * ((legOf st.sT n).b (latOf hd e) - Xf) + ((w : ℤ) * (w : ℤ) - 1) * ((Y.L : ℤ) + 1) := by ring
    rw [e1, hw2, sub_self, zero_mul, add_zero]
    rw [hy] at hTl
    rcases Int.units_eq_one_or w with h | h <;> simp only [h, Units.val_one, Units.val_neg, one_mul, neg_mul] <;> rw [abs_le] <;>
      constructor <;> linarith
  have hQ' := abs_le.1 hQ
  have hsched : (fun k : ℕ => ¬roomT Y (tgtCell a e) (latDir e (decide ((w : ℤ) = 1))) (b + (sgOf (latDir e (decide ((w : ℤ) = 1))) : ℤ) * (k * Y.ell))) =
      fun k : ℕ => ¬roomT Y (tgtCell a e) (latDir e (decide ((w : ℤ) = 1))) (b + (w : ℤ) * (k * Y.ell)) := by
    rw [hsw]
  constructor
  · by_contra h0
    push Not at h0
    have h0' : legLen Y a e (latDir e (decide ((w : ℤ) = 1))) b = 0 := by omega
    have hsp := of_firstIdx_lt (p := fun k : ℕ => ¬roomT Y (tgtCell a e) (latDir e (decide ((w : ℤ) = 1)))
      (b + (sgOf (latDir e (decide ((w : ℤ) = 1))) : ℤ) * (k * Y.ell))) (N := Y.Rmax)
      (by show legLen Y a e (latDir e (decide ((w : ℤ) = 1))) b < Y.Rmax; rw [h0']; exact hRpos)
    rw [← legLen, h0', hsw] at hsp
    change ¬roomT Y (tgtCell a e) (latDir e (decide ((w : ℤ) = 1))) (b + (w : ℤ) * ((0 : ℕ) * Y.ell)) at hsp
    rw [hroom] at hsp; push Not at hsp; push_cast at hsp
    linarith only [hsp, hQ'.2, hDh, hlam, hlamJ, hΔw, hP3, hP2, hPe, hLpP, hLeq, hell, hmH, hLp0, hP32, hP64]
  · unfold legLen
    rw [hsched]
    apply firstIdx_le_of
    rw [hroom]; push Not
    have : ((Y.NB : ℕ) : ℤ) * Y.ell = 1536 * ((Y.P : ℤ) ^ 3 * Y.ell) := by unfold TallLayout.NB; push_cast; ring
    linarith only [this, hQ'.1, hDh, hlam, hlamJ, hΔw, hP3, hP2, hPe, hLpP, hLeq, hell, hmH, hLp0, hP32, hP64]

/-- **The lengths of the segments are bounded**, hence an attempt places fewer than `R` bricks.
[cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem all_length_lt (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) :
    st.sA.length ≤ Y.Pw + 1 ∧ st.sR.length ≤ Y.N₁ + 1 ∧ st.sJ.length ≤ Y.N₁ + 1 ∧ st.sT.length ≤ Y.NT + 1 ∧
      st.sB1.length ≤ Y.NB ∧ st.sB2.length ≤ Y.NB ∧ st.all.length + 1 < Y.Rmax := by
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hA : st.sA.length ≤ Y.Pw + 1 := hI.invA.len
  have hR : st.sR.length ≤ Y.N₁ + 1 := by
    by_cases h : st.sR = []
    · rw [h]; simp
    · have hk : st.sR.length - 1 < st.sR.length := by have := List.length_pos_of_ne_nil h; omega
      have := le_riserLen Y hd hL hH a e τ hI hk
      have := hNR h; omega
  have hJ : st.sJ.length ≤ Y.N₁ + 1 := by
    by_cases h : st.sJ = []
    · rw [h]; simp
    · have hk : st.sJ.length - 1 < st.sJ.length := by have := List.length_pos_of_ne_nil h; omega
      have := le_jogLen Y hd hL hH a e τ hI hk
      have := hNJ h; omega
  have hT : st.sT.length ≤ Y.NT + 1 := by
    by_cases h : st.sT = []
    · rw [h]; simp
    · obtain ⟨-, hle, -, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI h
      have hs := hI.invT.sched
      have hk : st.sT.length - 1 ≤ legLen Y a e e ((legOf st.sT 0).b (axOf hd e)) := by
        rcases Nat.lt_or_ge 1 st.sT.length with h1 | h1
        · have := hs (st.sT.length - 2) (by omega); omega
        · omega
      omega
  have hTR : st.sT.length ≤ Y.Rmax := by
    have : Y.NT + 1 ≤ Y.Rmax := by
      unfold TallLayout.NT TallLayout.Rmax; have := hY.hP; have : 0 < Y.P ^ 3 := by positivity
      nlinarith
    omega
  have hB1 : st.sB1.length ≤ Y.NB := by
    by_cases h : st.sB1 = []
    · rw [h]; simp
    · obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 (hI.invB1.prev h)
      have hgs := hI.invT.g1_some g hg
      obtain ⟨-, hle⟩ := branch_feasible Y hd hL hH a e τ hY hτ hI hTR hgs rfl
      have hs := hI.invB1.sched g hg (st.sB1.length - 1) (by have := List.length_pos_of_ne_nil h; omega)
      have := List.length_pos_of_ne_nil h
      omega
  have hB2 : st.sB2.length ≤ Y.NB := by
    by_cases h : st.sB2 = []
    · rw [h]; simp
    · obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 (hI.invB2.prev h)
      have hgs := hI.invT.g2_some g hg
      obtain ⟨-, hle⟩ := branch_feasible Y hd hL hH a e τ hY hτ hI hTR hgs rfl
      have hs := hI.invB2.sched g hg (st.sB2.length - 1) (by have := List.length_pos_of_ne_nil h; omega)
      have := List.length_pos_of_ne_nil h
      omega
  refine ⟨hA, hR, hJ, hT, hB1, hB2, ?_⟩
  have hg1 : st.g1.toList.length ≤ 1 := by cases st.g1 <;> simp
  have hg2 : st.g2.toList.length ≤ 1 := by cases st.g2 <;> simp
  have hall : st.all.length = st.sA.length + st.sR.length + st.sJ.length + st.sT.length + st.g1.toList.length + st.g2.toList.length +
      st.sB1.length + st.sB2.length := by
    simp only [RS.all, List.length_append]
  rw [hall]
  have hP := hY.hP
  unfold TallLayout.Rmax
  unfold TallLayout.Pw at hA; unfold TallLayout.N₁ at hR hJ; unfold TallLayout.NT at hT; unfold TallLayout.NB at hB1 hB2
  have h8 : 8 * Y.P ^ 2 ≤ Y.P ^ 3 := by nlinarith
  have h8' : 8 * Y.P ≤ Y.P ^ 2 := by nlinarith
  nlinarith

end Percolation.Literature.BGNd

namespace Percolation.Literature.BGNd

open LatticeModels Contour
open scoped Classical

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

omit [NeZero d] in
/-- With a riser, the token came from another layer: `W ≤ u (z_e - z_src) ≤ 3W`. [folklore] -/
theorem riseDir_layers' (hY : Y.OK) (hu : riseDir Y e τ ≠ 0) :
    ∃ d', τ.src = some d' ∧ Y.Wl ≤ riseDir Y e τ * (Y.zOf e - Y.zOf d') ∧ riseDir Y e τ * (Y.zOf e - Y.zOf d') ≤ 3 * Y.Wl := by
  obtain ⟨-, -, -, hell, hmH, -, -, -, -, -, -, -, -, hWl, -, -, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  obtain ⟨d', hsrc⟩ : ∃ d', τ.src = some d' := by
    unfold riseDir at hu
    cases h : τ.src with
    | none => rw [h] at hu; exact absurd rfl hu
    | some d' => exact ⟨d', rfl⟩
  obtain ⟨j, hj, hj1, hj2⟩ := zOf_sub_zOf Y e d'
  have hudef : riseDir Y e τ = (if Y.zOf d' < Y.zOf e then 1 else if Y.zOf e < Y.zOf d' then -1 else 0) := by
    unfold riseDir; rw [hsrc]
  have hW0 : 0 < Y.Wl := by rw [hWl]; linarith only [hP64, hP2, hPe, hell, hmH]
  refine ⟨d', hsrc, ?_⟩
  rw [hudef] at hu ⊢
  split_ifs with h1 h2
  · have hj' : 1 ≤ j := by
      by_contra hj0; push Not at hj0
      have : j * Y.Wl ≤ 0 * Y.Wl := mul_le_mul_of_nonneg_right (by omega) hW0.le
      linarith only [this, h1, hj]
    have h3 : Y.Wl ≤ j * Y.Wl := le_mul_of_one_le_left hW0.le hj'
    have h4 : j * Y.Wl ≤ 3 * Y.Wl := mul_le_mul_of_nonneg_right hj2 hW0.le
    constructor <;> linarith only [h3, h4, hj]
  · have hj' : j ≤ -1 := by
      by_contra hj0; push Not at hj0
      have : 0 * Y.Wl ≤ j * Y.Wl := mul_le_mul_of_nonneg_right (by omega) hW0.le
      linarith only [this, h2, hj]
    have h3 : j * Y.Wl ≤ (-1) * Y.Wl := mul_le_mul_of_nonneg_right hj' hW0.le
    have h4 : (-3) * Y.Wl ≤ j * Y.Wl := mul_le_mul_of_nonneg_right hj1 hW0.le
    constructor <;> linarith only [h3, h4, hj]
  · exact absurd (by rw [if_neg h1, if_neg h2]) hu

/-- **The riser does not overshoot**: `riserLen · ℓ ≤ u (z_e - R₀.b₀) + m + 2`, and the distance to
climb is at most `3W + ρ_v`. [folklore] -/
theorem riserLen_le_dist (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hR : st.sR ≠ []) :
    ((riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) : ℕ) : ℤ) * Y.ell ≤
        riseDir Y e τ * (Y.zOf e - (legOf st.sR 0).b (ax0 hd)) + Y.m + 2 ∧
      riseDir Y e τ * (Y.zOf e - (legOf st.sR 0).b (ax0 hd)) ≤ 3 * Y.Wl + Y.ρv := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, hΔw, hΔ0, hρv, -, -, -, hWl, -, hN1, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  have hu : riseDir Y e τ ≠ 0 := fun h => hR (hI.invR.nil h)
  have hk : 0 < st.sR.length := List.length_pos_of_ne_nil hR
  obtain ⟨-, hR0, -, -, -, -⟩ := boundsR Y hd hL hH a e τ hY hI hk
  have hlenA := hI.invR.prev hR
  obtain ⟨-, -, -, hAht, -⟩ := boundsA Y hd hL hH a e τ hY hI (show Y.Pw < st.sA.length by omega)
  obtain ⟨hA0, hA1⟩ := hAht hu
  obtain ⟨d', hsrc, hW1, hW3⟩ := riseDir_layers' Y e τ hY hu
  have hτh := hτ.height
  rw [hsrc, Option.getD_some] at hτh
  have hτh' := abs_le.1 hτh
  set u := riseDir Y e τ with hu'
  set b := (legOf st.sR 0).b (ax0 hd) with hb
  have hu1 : u = 1 ∨ u = -1 := (riseDir_cases Y e τ).resolve_left hu
  have hdist : Y.Wl - Y.ρv - Y.Δw - Y.L - 1 ≤ u * (Y.zOf e - b) ∧ u * (Y.zOf e - b) ≤ 3 * Y.Wl + Y.ρv := by
    rcases hu1 with h | h <;> rw [h] at hA0 hA1 hR0 hW1 hW3 ⊢ <;> constructor <;>
      linarith only [hW1, hW3, hA0, hA1, hR0, hτh'.1, hτh'.2]
  obtain ⟨k, hk1, hfit⟩ := exists_fit Y hY b (Y.zOf e) u hu1
    (by linarith only [hdist.1, hWl, hρv, hΔw, hLeq, hLpP, hP2, hPe, hP64, hell, hmH])
  have hle : riserLen Y e τ b ≤ k := firstIdx_le_of (N := Y.Rmax) hfit
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  refine ⟨?_, hdist.2⟩
  calc ((riserLen Y e τ b : ℕ) : ℤ) * Y.ell ≤ (k : ℤ) * Y.ell := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hl0
    _ ≤ u * (Y.zOf e - b) + Y.m + 2 := hk1

/-- **The jog does not overshoot**: `jogLen · ℓ ≤ v (y - J₀.b_f) + m + 2`. [folklore] -/
theorem jogLen_le_dist (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hJ : st.sJ ≠ []) :
    ((jogLen Y a e ((legOf st.sJ 0).b (latOf hd e)) : ℕ) : ℤ) * Y.ell ≤
      (jogDir a e : ℤ) * (Y.lane (tgtCell a e) e - (legOf st.sJ 0).b (latOf hd e)) + Y.m + 2 := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, hΔw, hΔ0, hρv, hρp, -, hlamJ, -, -, hN1, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  have hNR : st.sR ≠ [] → riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁ := fun hR => riser_feasible Y hd hL hH a e τ hY hτ hI hR
  have hk : 0 < st.sJ.length := List.length_pos_of_ne_nil hJ
  obtain ⟨-, hJ0, -, -, -, -, -, -⟩ := boundsJ Y hd hL hH a e τ hY hI hNR hk
  obtain ⟨-, -, hElat⟩ := bounds_entryLast Y hd hL hH a e τ hY hI hJ hNR
  have hτl := abs_le.1 hτ.lateral
  have hEl := abs_le.1 hElat
  have hy := lane_tgtCell Y a e
  set v : ℤ := (jogDir a e : ℤ) with hv
  have hv1 : v = 1 ∨ v = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [hv, h]
  set b := (legOf st.sJ 0).b (latOf hd e) with hb
  have hdist : Y.lamJ - (Y.L + 1) - (Y.Lp + Y.Δw) - Y.ρp ≤ v * (Y.lane (tgtCell a e) e - b) := by
    rw [hy, hJ0]
    rcases hv1 with h | h <;> rw [h] <;> linarith only [hEl.1, hEl.2, hτl.1, hτl.2]
  obtain ⟨k, hk1, hfit⟩ := exists_fit Y hY b (Y.lane (tgtCell a e) e) v hv1
    (by linarith only [hdist, hlamJ, hρv, hρp, hΔw, hLeq, hLpP, hP2, hPe, hP64, hell, hmH, hLp0])
  have hle : jogLen Y a e b ≤ k := firstIdx_le_of (N := Y.Rmax) hfit
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  calc ((jogLen Y a e b : ℕ) : ℤ) * Y.ell ≤ (k : ℤ) * Y.ell := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hl0
    _ ≤ v * (Y.lane (tgtCell a e) e - b) + Y.m + 2 := hk1

end Percolation.Literature.BGNd
