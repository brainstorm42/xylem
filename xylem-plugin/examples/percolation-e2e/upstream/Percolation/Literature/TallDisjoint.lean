import Percolation.Literature.TallFeas
import Percolation.Util.Linter

/-!
# The tall gait, XIII: the bricks of an attempt are pairwise disjoint

From the invariant and the feasibility of the
schedules, the support boxes of all bricks recorded in a run state are pairwise disjoint (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 p. 173 (C): "the intersection of a new brick with the region
considered so far must be limited to a subset of its underside"). Within a segment this is the
disjointness of a leg; across segments it is either a turn estimate of `GaitKinematics.lean` or a
separation along one coordinate: the entry segments lie behind the branch region along `e`, the
riser beyond the top face of `A`, the jog beyond the lateral face of the entry segment and above
the far part of the riser, the trunk beyond the forward face of the jog and of the riser and beside
the entry leg, the two branch sides apart along `e`. This first part proves the coordinate bounds
and the separations not involving the trunk's windows.

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

/-! ## Box coordinates -/

omit [NeZero d] in
/-- The axis coordinate of a point of the box. [folklore] -/
theorem box_axis {L H : ℕ} {κ : BrickPos d} {w : Site d} (hw : w ∈ boxOf L H κ) :
    1 ≤ (κ.s : ℤ) * (w κ.a - 2 * κ.b κ.a) ∧ (κ.s : ℤ) * (w κ.a - 2 * κ.b κ.a) ≤ 2 * (H : ℤ) + 2 := (mem_boxOf.1 hw).1

omit [NeZero d] in
/-- A transverse coordinate of a point of the box. [folklore] -/
theorem box_trans {L H : ℕ} {κ : BrickPos d} {w : Site d} (hw : w ∈ boxOf L H κ) {i : Fin d} (hi : i ≠ κ.a) :
    -(2 * (L : ℤ) + 2) ≤ w i - 2 * κ.b i ∧ w i - 2 * κ.b i ≤ 2 * (L : ℤ) + 2 := abs_le.1 ((mem_boxOf.1 hw).2 i hi)

omit [NeZero d] in
/-- Any coordinate of a point of the box is within `2L + 2H + 2` of twice the base (a bound valid for
the axis too, as `1 ≤ 2L + 2`... we use the weaker `max` form). [folklore] -/
theorem box_any {L H : ℕ} {κ : BrickPos d} {w : Site d} (hw : w ∈ boxOf L H κ) (i : Fin d) :
    |w i - 2 * κ.b i| ≤ 2 * (L : ℤ) + 2 * H + 2 := by
  by_cases hi : i = κ.a
  · subst hi
    obtain ⟨h1, h2⟩ := box_axis hw
    have hL0 : (0 : ℤ) ≤ L := by positivity
    rcases Int.units_eq_one_or κ.s with h | h <;> rw [h] at h1 h2 <;> rw [abs_le] <;> constructor <;>
      simp only [Units.val_one, Units.val_neg, one_mul, neg_mul] at h1 h2 <;> linarith
  · have := box_trans hw hi
    have hH0 : (0 : ℤ) ≤ H := by positivity
    rw [abs_le]; constructor <;> linarith [this.1, this.2]

/-! ## The entry segments lie behind the branch region along `e` -/

/-- **Entry bricks are near the entry face along `e`**: for a brick of `A`, `R` or `J`, every point of
its box has `s (w_e - 2 X_e) ≤ -2 D/2 + K_E` with `K_E = 2(P'ℓ + H + 2N₁L' + ℓ + L' + 2L + 2H + 2)`.
[folklore] -/
theorem e_le_of_entry (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {r : BrickRec d} (hr : r ∈ st.sA ∨ r ∈ st.sR ∨ r ∈ st.sJ) {w : Site d} (hw : w ∈ boxOf Y.L Y.H r.1) :
    (sgOf e : ℤ) * (w (axOf hd e) - 2 * Y.ctr (tgtCell a e) e.1) ≤
      -2 * Y.Dh + 2 * (Y.Pw * Y.ell + Y.H + 2 * Y.N₁ * Y.Lp + Y.ell + Y.Lp + 2 * Y.L + 2 * Y.H + 2) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hτe := hτ.longit
  have hc := ctr_tgtCell_fst Y a e
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hany := abs_le.1 (box_any hw (axOf hd e))
  -- it suffices to bound the base: `s (b_e - p_e) ≤ P'ℓ + H + 2N₁L' + ℓ + L'`
  suffices hb : (sgOf e : ℤ) * (r.1.b (axOf hd e) - τ.pos (axOf hd e)) ≤ Y.Pw * Y.ell + Y.H + 2 * Y.N₁ * Y.Lp + Y.ell + Y.Lp by
    rw [hc]
    rcases hs1 with h | h <;> rw [h] at hb hτe ⊢ <;> linarith [hany.1, hany.2, hτe.1, hτe.2]
  have hN0 : (0 : ℤ) ≤ Y.N₁ * Y.Lp := by positivity
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  rcases hr with hr | hr | hr
  · obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr
    obtain ⟨hbe, -, -, -, -⟩ := boundsA Y hd hL hH a e τ hY hI hk
    change (legOf st.sA k).b (axOf hd e) = _ at hbe
    show (sgOf e : ℤ) * ((legOf st.sA k).b (axOf hd e) - τ.pos (axOf hd e)) ≤ _
    rw [hbe]
    have hkPw : (k : ℤ) ≤ Y.Pw := by have := hI.invA.len; exact_mod_cast (by omega : k ≤ Y.Pw)
    have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs1 with h | h <;> simp [h]
    have e1 : (sgOf e : ℤ) * (τ.pos (axOf hd e) + (sgOf e : ℤ) * Y.ell * k - τ.pos (axOf hd e)) = ((sgOf e : ℤ) * (sgOf e : ℤ)) * (Y.ell * k) := by
      ring
    rw [e1, hss, one_mul]
    have : Y.ell * (k : ℤ) ≤ Y.ell * Y.Pw := mul_le_mul_of_nonneg_left hkPw hl0
    have hH0 : (0 : ℤ) ≤ Y.H := by positivity
    linarith
  · obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr
    obtain ⟨-, -, -, hhi, -, -⟩ := boundsR Y hd hL hH a e τ hY hI hk
    have hkn := le_riserLen Y hd hL hH a e τ hI hk
    have hN := hNR (List.ne_nil_of_mem hr)
    have hkN : (k : ℤ) * Y.Lp ≤ Y.N₁ * Y.Lp := mul_le_mul_of_nonneg_right (by exact_mod_cast hkn.trans hN) hLp0
    show (sgOf e : ℤ) * ((legOf st.sR k).b (axOf hd e) - τ.pos (axOf hd e)) ≤ _
    have hm0 : (0 : ℤ) ≤ Y.m := by positivity
    linarith
  · obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr
    obtain ⟨-, -, -, hkhi, -, h0hi, -, -⟩ := boundsJ Y hd hL hH a e τ hY hI hNR hk
    have hkn := le_jogLen Y hd hL hH a e τ hI hk
    have hN := hNJ (List.ne_nil_of_mem hr)
    have hkN : (k : ℤ) * Y.Lp ≤ Y.N₁ * Y.Lp := mul_le_mul_of_nonneg_right (by exact_mod_cast hkn.trans hN) hLp0
    show (sgOf e : ℤ) * ((legOf st.sJ k).b (axOf hd e) - τ.pos (axOf hd e)) ≤ _
    have e1 : (sgOf e : ℤ) * ((legOf st.sJ k).b (axOf hd e) - τ.pos (axOf hd e)) =
        (sgOf e : ℤ) * ((legOf st.sJ k).b (axOf hd e) - (legOf st.sJ 0).b (axOf hd e)) +
          (sgOf e : ℤ) * ((legOf st.sJ 0).b (axOf hd e) - τ.pos (axOf hd e)) := by ring
    rw [e1]; linarith

/-- The records of the branch region: the two branch bricks and the two branch legs. [folklore] -/
def InBranch (st : RS d) (r : BrickRec d) : Prop := r ∈ st.g1.toList ∨ r ∈ st.g2.toList ∨ r ∈ st.sB1 ∨ r ∈ st.sB2

/-- **Branch bricks are near the centre along `e`**: every point of the box of a branch brick or a
branch-leg brick has `s (w_e - 2 X_e) ≥ -2(Λ + Λ_J + L' + 2L + 2H + 2)`. [folklore] -/
theorem e_ge_of_branch (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {r : BrickRec d} (hr : InBranch st r) {w : Site d} (hw : w ∈ boxOf Y.L Y.H r.1) :
    -2 * (Y.lam + Y.lamJ + Y.Lp + 2 * Y.L + 2 * Y.H + 2) ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * Y.ctr (tgtCell a e) e.1) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  obtain ⟨-, -, -, -, -, -, hallR⟩ := all_length_lt Y hd hL hH a e τ hY hτ hI
  have hlenT : st.sT.length ≤ Y.Rmax := by
    have : st.sT.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hany := abs_le.1 (box_any hw (axOf hd e))
  -- the lanes relative to the centre
  have hlane : ∀ w' : ℤˣ, -(Y.lam + Y.lamJ) ≤ (sgOf e : ℤ) * (brLane Y a e w' - Y.ctr (tgtCell a e) e.1) := by
    intro w'
    have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
    have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
    have hpar : TallLayout.cpar (tgtCell a e) = 0 ∨ TallLayout.cpar (tgtCell a e) = 1 := by unfold TallLayout.cpar; omega
    have e1 : brLane Y a e w' - Y.ctr (tgtCell a e) e.1 = (if (w' : ℤ) = 1 then Y.lam else -Y.lam) + TallLayout.cpar (tgtCell a e) * Y.lamJ := by
      rw [brLane_eq]; ring
    have ht1 : -Y.lam ≤ (if (w' : ℤ) = 1 then Y.lam else -Y.lam) ∧ (if (w' : ℤ) = 1 then Y.lam else -Y.lam) ≤ Y.lam := by
      split_ifs <;> constructor <;> linarith only [hlam0]
    have ht2 : 0 ≤ TallLayout.cpar (tgtCell a e) * Y.lamJ ∧ TallLayout.cpar (tgtCell a e) * Y.lamJ ≤ Y.lamJ := by
      rcases hpar with hp | hp <;> rw [hp] <;> constructor <;> linarith only [hlamJ0]
    rw [e1]
    rcases hs1 with h | h <;> rw [h] <;> linarith only [ht1.1, ht1.2, ht2.1, ht2.2]
  -- it suffices to bound the base: `s (b_e - lane) ≥ -L'` for some branch lane
  suffices hb : ∃ w' : ℤˣ, -Y.Lp ≤ (sgOf e : ℤ) * (r.1.b (axOf hd e) - brLane Y a e w') by
    obtain ⟨w', hb⟩ := hb
    have hl := hlane w'
    rcases hs1 with h | h <;> rw [h] at hb hl ⊢ <;> linarith [hany.1, hany.2]
  -- the two branch bricks
  have hG : ∀ (w' : ℤˣ) (g : BrickRec d) (n : ℕ),
      (n < st.sT.length ∧ IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT n) g.1 ∧
        |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp) →
      n = brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) → 0 ≤ (sgOf e : ℤ) * (g.1.b (axOf hd e) - brLane Y a e w') := by
    intro w' g n hg hn
    have hT : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨-, -, hn1, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hT
    have hn1' : 1 ≤ n := by
      rw [hn]
      have h12 := n1Of_le_n2Of Y hd a e st.sT
      rcases Int.units_eq_one_or w' with rfl | rfl <;> rcases Int.units_eq_one_or (br1Sign e) with h | h
      · rw [← h]; exact hn1
      · have : -br1Sign e = 1 := by rw [h]; simp
        rw [← this]; exact hn1.trans h12
      · have : -br1Sign e = -1 := by rw [h]
        rw [← this]; exact hn1.trans h12
      · rw [← h]; exact hn1
    obtain ⟨-, -, -, -, h0, -, -, -⟩ := boundsG Y hd hL hH a e τ hY hI hNR hNJ hlenT hg hn hn1'
    exact h0
  rcases hr with hr | hr | hr | hr
  · cases hg1 : st.g1 with
    | none => rw [hg1] at hr; exact absurd hr (by simp)
    | some g =>
      rw [hg1] at hr; simp only [Option.toList_some, List.mem_singleton] at hr; subst hr
      exact ⟨_, by linarith [hG _ _ _ (hI.invT.g1_some _ hg1) rfl]⟩
  · cases hg2 : st.g2 with
    | none => rw [hg2] at hr; exact absurd hr (by simp)
    | some g =>
      rw [hg2] at hr; simp only [Option.toList_some, List.mem_singleton] at hr; subst hr
      exact ⟨_, by linarith [hG _ _ _ (hI.invT.g2_some _ hg2) rfl]⟩
  · obtain ⟨g, hg1⟩ := Option.ne_none_iff_exists'.1 (hI.invB1.prev (List.ne_nil_of_mem hr))
    have h0 := hG _ _ _ (hI.invT.g1_some g hg1) rfl
    -- `r` is in the leg `sB1 ++ [g]`
    have hr' : r ∈ st.sB1 ++ [g] := List.mem_append_left _ hr
    obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr'
    have hk' : k ≤ st.sB1.length := by simp at hk; omega
    have hgax := (hI.invT.g1_some g hg1).2.1.axis
    have hgs := (hI.invT.g1_some g hg1).2.1.sign
    have hB := hI.invB1; rw [hg1] at hB
    obtain ⟨-, hlng, -, -⟩ := boundsB Y hd hL hH a e hB hgax hgs hk'
    have hl := abs_le.1 hlng
    refine ⟨br1Sign e, ?_⟩
    show -Y.Lp ≤ (sgOf e : ℤ) * ((legOf (st.sB1 ++ [g]) k).b (axOf hd e) - brLane Y a e (br1Sign e))
    rcases hs1 with h | h <;> rw [h] at h0 ⊢ <;> linarith
  · obtain ⟨g, hg2⟩ := Option.ne_none_iff_exists'.1 (hI.invB2.prev (List.ne_nil_of_mem hr))
    have h0 := hG _ _ _ (hI.invT.g2_some g hg2) rfl
    have hr' : r ∈ st.sB2 ++ [g] := List.mem_append_left _ hr
    obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr'
    have hk' : k ≤ st.sB2.length := by simp at hk; omega
    have hgax := (hI.invT.g2_some g hg2).2.1.axis
    have hgs := (hI.invT.g2_some g hg2).2.1.sign
    have hB := hI.invB2; rw [hg2] at hB
    obtain ⟨-, hlng, -, -⟩ := boundsB Y hd hL hH a e hB hgax hgs hk'
    have hl := abs_le.1 hlng
    refine ⟨-br1Sign e, ?_⟩
    show -Y.Lp ≤ (sgOf e : ℤ) * ((legOf (st.sB2 ++ [g]) k).b (axOf hd e) - brLane Y a e (-br1Sign e))
    rcases hs1 with h | h <;> rw [h] at h0 ⊢ <;> linarith

/-- **Entry bricks and branch bricks are disjoint** (separated along `e`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem disjoint_entry_branch (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {r : BrickRec d} (hr : r ∈ st.sA ∨ r ∈ st.sR ∨ r ∈ st.sJ) {r' : BrickRec d} (hr' : InBranch st r') :
    Disjoint (boxOf Y.L Y.H r.1) (boxOf Y.L Y.H r'.1) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  rw [Set.disjoint_left]
  intro w hw hw'
  have h1 := e_le_of_entry Y hd hL hH a e τ hY hτ hI hr hw
  have h2 := e_ge_of_branch Y hd hL hH a e τ hY hτ hI hr' hw'
  linarith only [h1, h2, hDh, hlam, hlamJ, hNL, hPwe, hP3, hP2, hPe, hLpP, hLeq, hell, hmH, hLp0, hP32, hP64]

end BGNd

end Percolation.Literature

end
