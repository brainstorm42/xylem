import Percolation.Literature.TallRun3
import Percolation.Util.Linter

/-!
# The tall gait, XX: the recorded bricks lie behind the exit planes

For the tall kit (Grimmett, *Percolation*, 2nd ed.
(1999), §7.3, proof of Lemma (7.52)): every recorded brick's box lies (weakly) behind twice the plane
of each exit token — far behind, or in the tube ending at that token — whence the supports of the
history avoid the zones of the tokens handed on (Grimmett's (C) across a cell boundary).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 173–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-! ## Classification of the records of a run state -/

/-- **Every record of the state is an entry of `A`, `R`, `J`, `T`, or of one of the two branch legs.** [folklore] -/
theorem mem_all_cases {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {r : BrickRec d} (hr : r ∈ st.all) :
    (∃ k < st.sA.length, r = recOf st.sA k) ∨ (∃ k < st.sR.length, r = recOf st.sR k) ∨ (∃ k < st.sJ.length, r = recOf st.sJ k) ∨
      (∃ k < st.sT.length, r = recOf st.sT k) ∨
      ∃ (w' : ℤˣ) (g : BrickRec d) (sB : List (BrickRec d)) (D : Prop), InvB hd Y hL hH a e w' (some g) sB D ∧
        (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
          IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
          |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp) ∧
        (w' = br1Sign e ∧ st.g1 = some g ∧ sB = st.sB1 ∨ w' = -br1Sign e ∧ st.g2 = some g ∧ sB = st.sB2) ∧
        ∃ k ≤ sB.length, r = recOf (sB ++ [g]) k := by
  simp only [RS.all, List.mem_append] at hr
  have hside : ∀ (w' : ℤˣ) (go : Option (BrickRec d)) (sB : List (BrickRec d)) (D : Prop), InvB hd Y hL hH a e w' go sB D →
      (∀ g, go = some g → brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
        IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
        |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp) →
      (w' = br1Sign e ∧ st.g1 = go ∧ sB = st.sB1 ∨ w' = -br1Sign e ∧ st.g2 = go ∧ sB = st.sB2) →
      (r ∈ go.toList ∨ r ∈ sB) →
      ∃ (w' : ℤˣ) (g : BrickRec d) (sB : List (BrickRec d)) (D : Prop), InvB hd Y hL hH a e w' (some g) sB D ∧
        (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
          IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
          |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp) ∧
        (w' = br1Sign e ∧ st.g1 = some g ∧ sB = st.sB1 ∨ w' = -br1Sign e ∧ st.g2 = some g ∧ sB = st.sB2) ∧
        ∃ k ≤ sB.length, r = recOf (sB ++ [g]) k := by
    intro w' go sB D hB hgs hwh hx
    obtain ⟨g, hgo⟩ : ∃ g, go = some g := by
      rcases hx with hx | hx
      · cases go with
        | none => exact absurd hx (by simp)
        | some g => exact ⟨g, rfl⟩
      · exact Option.ne_none_iff_exists'.1 (hB.prev (List.ne_nil_of_mem hx))
    subst hgo
    have hx' : r ∈ sB ++ [g] := by
      rcases hx with hx | hx
      · simp only [Option.toList_some, List.mem_singleton] at hx; subst hx; simp
      · exact List.mem_append_left _ hx
    obtain ⟨k, hk, hkr⟩ := exists_recOf_of_mem hx'
    exact ⟨w', g, sB, D, hB, hgs g rfl, hwh, k, by simpa using hk, hkr.symm⟩
  rcases hr with ((((((hr | hr) | hr) | hr) | hr) | hr) | hr) | hr
  · obtain ⟨k, hk, hkr⟩ := exists_recOf_of_mem hr; exact Or.inl ⟨k, hk, hkr.symm⟩
  · obtain ⟨k, hk, hkr⟩ := exists_recOf_of_mem hr; exact Or.inr (Or.inl ⟨k, hk, hkr.symm⟩)
  · obtain ⟨k, hk, hkr⟩ := exists_recOf_of_mem hr; exact Or.inr (Or.inr (Or.inl ⟨k, hk, hkr.symm⟩))
  · obtain ⟨k, hk, hkr⟩ := exists_recOf_of_mem hr; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, hkr.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hside _ _ _ _ hI.invB1 (fun g hg => hI.invT.g1_some g hg) (Or.inl ⟨rfl, rfl, rfl⟩) (Or.inl hr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hside _ _ _ _ hI.invB2 (fun g hg => hI.invT.g2_some g hg) (Or.inr ⟨rfl, rfl, rfl⟩) (Or.inl hr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hside _ _ _ _ hI.invB1 (fun g hg => hI.invT.g1_some g hg) (Or.inl ⟨rfl, rfl, rfl⟩) (Or.inr hr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hside _ _ _ _ hI.invB2 (fun g hg => hI.invT.g2_some g hg) (Or.inr ⟨rfl, rfl, rfl⟩) (Or.inr hr)))))

/-! ## Bounds along `e` and laterally for all recorded boxes -/

omit [NeZero d] in
/-- The port lanes are within `Λ + Λ_J` of the target centre. [folklore] -/
theorem abs_brLane_sub_ctr (hY : Y.OK) (w' : ℤˣ) : |brLane Y a e w' - Y.ctr (tgtCell a e) e.1| ≤ Y.lam + Y.lamJ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlam, hlamJ, -⟩ := hY.facts
  rw [brLane_eq]
  have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
  have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
  have hpar : TallLayout.cpar (tgtCell a e) = 0 ∨ TallLayout.cpar (tgtCell a e) = 1 := by unfold TallLayout.cpar; omega
  rcases hpar with hq | hq <;> rw [hq] <;> split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [hlam0, hlamJ0]

omit [NeZero d] in
/-- The source lane is within `Λ + Λ_J` of the target's lateral centre. [folklore] -/
theorem abs_lane_sub_ctr (hY : Y.OK) : |Y.lane a e - Y.ctr (tgtCell a e) (latDir e true).1| ≤ Y.lam + Y.lamJ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlam, hlamJ, -⟩ := hY.facts
  unfold TallLayout.lane latDir
  rw [← ctr_tgtCell_snd Y a e]
  have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
  have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
  have hpar : TallLayout.cpar a = 0 ∨ TallLayout.cpar a = 1 := by unfold TallLayout.cpar; omega
  unfold TallLayout.nu
  rcases hpar with hq | hq <;> rw [hq] <;> split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [hlam0, hlamJ0]

/-- **Along `e`, every recorded box is far behind the far face of the target cell, or in the trunk
tube up to the last trunk brick.** [cite: GrimmettPercolation1999, §7.3 pp. 173–174] -/
theorem e_bound_all (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {r : BrickRec d}
    (hr : r ∈ st.all) {w : Site d} (hw : w ∈ boxOf Y.L Y.H r.1) :
    (sgOf e : ℤ) * w (axOf hd e) ≤ 2 * ((sgOf e : ℤ) * Y.ctr (tgtCell a e) e.1) + 2 * Y.Dh - 2 * Y.ell ∨
      (st.sT ≠ [] ∧ (sgOf e : ℤ) * w (axOf hd e) ≤ 2 * ((sgOf e : ℤ) * (legOf st.sT (st.sT.length - 1)).b (axOf hd e)) + 2 * Y.H + 2) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  have hN0 : (0 : ℤ) ≤ Y.N₁ * Y.Lp := by positivity
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  -- the token's plane is a full cell behind the target centre
  have hp : (sgOf e : ℤ) * τ.pos (axOf hd e) ≤ (sgOf e : ℤ) * Y.ctr (tgtCell a e) e.1 - Y.Dh - 1 := by
    have h2 := hτ.longit.2
    rw [ctr_tgtCell_fst]
    have : (sgOf e : ℤ) * (Y.ctr a e.1 + (sgOf e : ℤ) * (2 * Y.Dh)) = (sgOf e : ℤ) * Y.ctr a e.1 + ((sgOf e : ℤ) * (sgOf e : ℤ)) * (2 * Y.Dh) := by
      ring
    rw [this, hss]; linarith only [h2]
  have hsmall : 2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0 + 2 * Y.lam + 2 * Y.lamJ + 2 * Y.ell ≤ 4 * Y.Dh := by
    rw [hK0]; linarith only [hDh, hPwe, hNL, hlam, hlamJ, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  have hsmall2 : 2 * Y.lam + 2 * Y.lamJ + 4 * Y.ell + 2 * Y.H + 2 * Y.Lp + Y.K0 ≤ 2 * Y.Dh := by
    rw [hK0]; linarith only [hDh, hlam, hlamJ, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  rcases mem_all_cases Y hd hL hH a e τ hI hr with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨w', g, sB, D, hB, hg, -, k, hk, rfl⟩
  · obtain ⟨-, -, h2, -⟩ := boxOf_A_facts Y hd hL hH a e τ hY hτ hI hk hw
    left; linarith only [h2, hp, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hlam, hlamJ, hP2, hPe, hP64, hell, hmH]
  · obtain ⟨-, -, h2, -⟩ := boxOf_R_facts Y hd hL hH a e τ hY hτ hI hk hw
    left; linarith only [h2, hp, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hlam, hlamJ, hP2, hPe, hP64, hell, hmH]
  · obtain ⟨-, -, h2, -⟩ := boxOf_J_facts Y hd hL hH a e τ hY hτ hI hk hw
    left; linarith only [h2, hp, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hlam, hlamJ, hP2, hPe, hP64, hell, hmH]
  · -- a trunk brick: in the tube, below the last one
    right
    obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
    have hTne : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
    refine ⟨hTne, ?_⟩
    obtain ⟨hbe, -⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ hk
    obtain ⟨hbl, -⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ (show st.sT.length - 1 < st.sT.length by omega)
    obtain ⟨hax, hsx⟩ := hI.invT.axis_sign Y hd hL hH a e hTne hk
    obtain ⟨-, h2⟩ := box_axis hw
    change (((recOf st.sT k).1.s : ℤ)) * (w (recOf st.sT k).1.a - 2 * (recOf st.sT k).1.b (recOf st.sT k).1.a) ≤ 2 * (Y.H : ℤ) + 2 at h2
    change (legOf st.sT k).a = axOf hd e at hax
    change (legOf st.sT k).s = sgOf e at hsx
    simp only [show (recOf st.sT k).1 = legOf st.sT k from rfl] at h2
    rw [hax, hsx, hbe] at h2
    rw [hbl]
    have hkl : Y.ell * (k : ℤ) ≤ Y.ell * ((st.sT.length - 1 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : k ≤ st.sT.length - 1)) hl0
    have e1 : (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * Y.ell * ((st.sT.length - 1 : ℕ) : ℤ)) =
        (sgOf e : ℤ) * (legOf st.sT 0).b (axOf hd e) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * (Y.ell * ((st.sT.length - 1 : ℕ) : ℤ)) := by ring
    have e2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * Y.ell * k)) =
        (sgOf e : ℤ) * w (axOf hd e) - 2 * ((sgOf e : ℤ) * (legOf st.sT 0).b (axOf hd e)) - 2 * ((sgOf e : ℤ) * (sgOf e : ℤ)) * (Y.ell * k) := by
      ring
    rw [e2, hss] at h2
    rw [e1, hss]
    linarith only [h2, hkl]
  · -- a branch brick: near a port lane, far behind
    obtain ⟨-, -, h2, -⟩ := boxOf_B_facts Y hd hL hH a e τ hY hτ hI hB hg hk hw
    have hl := abs_le.1 (abs_brLane_sub_ctr Y a e hY w')
    left
    have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    rcases hs1 with h | h <;> rw [h] at h2 ⊢ <;> linarith only [h2, hl.1, hl.2, hsmall2]

/-- Far boxes, laterally: the boxes of `A`, `R`, `J`, `T` are within `D - 2ℓ` of twice the lateral
centre of the target cell. [folklore] -/
theorem f_far_ARJT (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {w : Site d}
    (hw : (∃ k, ∃ _ : k < st.sA.length, w ∈ boxOf Y.L Y.H (legOf st.sA k)) ∨ (∃ k, ∃ _ : k < st.sR.length, w ∈ boxOf Y.L Y.H (legOf st.sR k)) ∨
      (∃ k, ∃ _ : k < st.sJ.length, w ∈ boxOf Y.L Y.H (legOf st.sJ k)) ∨ (∃ k, ∃ _ : k < st.sT.length, w ∈ boxOf Y.L Y.H (legOf st.sT k))) :
    |w (latOf hd e) - 2 * Y.ctr (tgtCell a e) (latDir e true).1| ≤ 2 * Y.Dh - 2 * Y.ell := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  have hla := abs_le.1 (abs_lane_sub_ctr Y a e hY)
  have hτl := abs_le.1 hτ.lateral
  have hy : Y.lane (tgtCell a e) e = Y.lane a e + (jogDir a e : ℤ) * Y.lamJ := lane_tgtCell Y a e
  have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
  have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  -- one small constant dominates every case
  set C := 2 * Y.ρp + 2 * Y.lam + 6 * Y.lamJ + 2 * Y.Lp + 8 * Y.Δw + Y.K0 + 2 * Y.ell + 2 * Y.m + 2 * Y.H + 6 with hC
  have hsmall : C ≤ 2 * Y.Dh - 2 * Y.ell := by
    rw [hC, hK0]; linarith only [hDh, hρp, hΔw, hlam, hlamJ, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  have hC0 : 2 * Y.ρp + 2 * Y.lam + 2 * Y.lamJ + 2 * Y.Lp + 2 * Y.Δw + Y.K0 ≤ C := by
    rw [hC]; linarith only [hlamJ0, hΔ0, hl0, hm0, hell]
  suffices h : |w (latOf hd e) - 2 * Y.ctr (tgtCell a e) (latDir e true).1| ≤ C from h.trans hsmall
  rcases hw with ⟨k, hk, hw⟩ | ⟨k, hk, hw⟩ | ⟨k, hk, hw⟩ | ⟨k, hk, hw⟩
  · obtain ⟨-, -, -, h3, -⟩ := boxOf_A_facts Y hd hL hH a e τ hY hτ hI hk hw
    have h := abs_le.1 h3
    rw [abs_le]; constructor <;> linarith only [h.1, h.2, hτl.1, hτl.2, hla.1, hla.2, hC0]
  · obtain ⟨-, -, -, h3, -⟩ := boxOf_R_facts Y hd hL hH a e τ hY hτ hI hk hw
    have h := abs_le.1 h3
    rw [abs_le]; constructor <;> linarith only [h.1, h.2, hτl.1, hτl.2, hla.1, hla.2, hC0]
  · obtain ⟨-, -, -, h3, h4, -⟩ := boxOf_J_facts Y hd hL hH a e τ hY hτ hI hk hw
    rw [hy] at h4
    rw [abs_le, hC]
    rcases hv1 with hv | hv <;> rw [hv] at h3 h4 <;> constructor <;>
      linarith only [h3, h4, hτl.1, hτl.2, hla.1, hla.2, hlamJ0, hΔ0, hl0, hm0, hLp0, hK0, hLeq, hρp, hell]
  · obtain ⟨-, -, -, h3, -⟩ := boxOf_T_facts Y hd hL hH a e τ hY hτ hI hk hw
    rw [hy] at h3
    have h := abs_le.1 h3
    rw [abs_le, hC]
    rcases hv1 with hv | hv <;> rw [hv] at h <;> constructor <;>
      linarith only [h.1, h.2, hla.1, hla.2, hlamJ0, hΔ0, hl0, hm0, hLp0, hK0, hLeq, hρp, hell]

/-- Branch boxes, laterally: behind the start of the tube in the opposite direction, and below the
last branch brick in the tube's direction. [folklore] -/
theorem f_branch (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {w' : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w' (some g) sB D)
    (hg : brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
      IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp)
    {k : ℕ} (hk : k ≤ sB.length) {w : Site d} (hw : w ∈ boxOf Y.L Y.H (legOf (sB ++ [g]) k)) :
    -((w' : ℤ) * w (latOf hd e)) ≤ 2 * -((w' : ℤ) * Y.ctr (tgtCell a e) (latDir e true).1) + 2 * Y.Dh - 2 * Y.ell ∧
      (w' : ℤ) * w (latOf hd e) ≤ 2 * ((w' : ℤ) * (legOf (sB ++ [g]) sB.length).b (latOf hd e)) + 2 * Y.H + 2 := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  have hla := abs_le.1 (abs_lane_sub_ctr Y a e hY)
  have hy : Y.lane (tgtCell a e) e = Y.lane a e + (jogDir a e : ℤ) * Y.lamJ := lane_tgtCell Y a e
  have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
  have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  have hsmall : 2 * Y.lam + 6 * Y.lamJ + 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw ≤ 2 * Y.Dh - 2 * Y.ell := by
    linarith only [hDh, hΔw, hlam, hlamJ, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  -- axis and sign of the branch bricks
  obtain ⟨hgax, hgs'⟩ : g.1.a = latOf hd e ∧ g.1.s = w' := by
    obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
    obtain ⟨-, -, -, -, -, -, hallR⟩ := all_length_lt Y hd hL hH a e τ hY hτ hI
    have hlenT : st.sT.length ≤ Y.Rmax := by
      have : st.sT.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
      omega
    have hT : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨-, -, hn1, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hT
    have h12 := n1Of_le_n2Of Y hd a e st.sT
    have hn1' : 1 ≤ brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) := by
      rcases Int.units_eq_one_or w' with rfl | rfl <;> rcases Int.units_eq_one_or (br1Sign e) with h | h
      · rw [← h]; exact hn1
      · have : -br1Sign e = 1 := by rw [h]; simp
        rw [← this]; exact hn1.trans h12
      · have : -br1Sign e = -1 := by rw [h]
        rw [← this]; exact hn1.trans h12
      · rw [← h]; exact hn1
    obtain ⟨hgax, hgs', -⟩ := boundsG Y hd hL hH a e τ hY hI hNR hNJ hlenT hg rfl hn1'
    exact ⟨hgax, hgs'⟩
  constructor
  · obtain ⟨-, -, -, h3, -, -⟩ := boxOf_B_facts Y hd hL hH a e τ hY hτ hI hB hg hk hw
    rw [hy] at h3
    have hw1 : (w' : ℤ) = 1 ∨ (w' : ℤ) = -1 := by rcases Int.units_eq_one_or w' with h | h <;> simp [h]
    rcases hw1 with h' | h' <;> rw [h'] at h3 ⊢ <;> rcases hv1 with hv | hv <;> rw [hv] at h3 <;>
      linarith only [h3, hla.1, hla.2, hsmall, hlamJ0]
  · obtain ⟨hbf, -⟩ := boundsB Y hd hL hH a e hB hgax hgs' hk
    obtain ⟨hbl, -⟩ := boundsB Y hd hL hH a e hB hgax hgs' (le_refl sB.length)
    have hax : (legOf (sB ++ [g]) k).a = latOf hd e ∧ (legOf (sB ++ [g]) k).s = w' := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [legOf_append_singleton_zero]; exact ⟨hgax, hgs'⟩
      · have hne : sB ≠ [] := List.ne_nil_of_length_pos (by omega)
        have := (hB.grown g rfl hne).axis_sign (k := k) (by simp; omega)
        rw [legOf_append_singleton_zero] at this; rw [this.1, this.2]; exact ⟨hgax, hgs'⟩
    obtain ⟨-, h2⟩ := box_axis hw
    rw [hax.1, hax.2, hbf] at h2
    have hw2 : (w' : ℤ) * (w' : ℤ) = 1 := by rcases Int.units_eq_one_or w' with h | h <;> simp [h]
    have hkl : Y.ell * (k : ℤ) ≤ Y.ell * (sB.length : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hl0
    have e1 : (w' : ℤ) * (g.1.b (latOf hd e) + (w' : ℤ) * Y.ell * (sB.length : ℕ)) =
        (w' : ℤ) * g.1.b (latOf hd e) + ((w' : ℤ) * (w' : ℤ)) * (Y.ell * sB.length) := by ring
    have e2 : (w' : ℤ) * (w (latOf hd e) - 2 * (g.1.b (latOf hd e) + (w' : ℤ) * Y.ell * k)) =
        (w' : ℤ) * w (latOf hd e) - 2 * ((w' : ℤ) * g.1.b (latOf hd e)) - 2 * ((w' : ℤ) * (w' : ℤ)) * (Y.ell * k) := by ring
    rw [e2, hw2] at h2
    rw [hbl, e1, hw2]; linarith only [h2, hkl]

/-- **Laterally, in the direction `w''`, every recorded box is far behind the lateral face of the
target cell, or in the branch tube of that side up to the last branch brick.**
[cite: GrimmettPercolation1999, §7.3 pp. 173–174] -/
theorem f_bound_all (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (w'' : ℤˣ) {r : BrickRec d}
    (hr : r ∈ st.all) {w : Site d} (hw : w ∈ boxOf Y.L Y.H r.1) :
    (w'' : ℤ) * w (latOf hd e) ≤ 2 * ((w'' : ℤ) * Y.ctr (tgtCell a e) (latDir e true).1) + 2 * Y.Dh - 2 * Y.ell ∨
      (w'' = br1Sign e ∧ ∃ g, st.g1 = some g ∧
        (w'' : ℤ) * w (latOf hd e) ≤ 2 * ((w'' : ℤ) * (legOf (st.sB1 ++ [g]) st.sB1.length).b (latOf hd e)) + 2 * Y.H + 2) ∨
      (w'' = -br1Sign e ∧ ∃ g, st.g2 = some g ∧
        (w'' : ℤ) * w (latOf hd e) ≤ 2 * ((w'' : ℤ) * (legOf (st.sB2 ++ [g]) st.sB2.length).b (latOf hd e)) + 2 * Y.H + 2) := by
  have far : |w (latOf hd e) - 2 * Y.ctr (tgtCell a e) (latDir e true).1| ≤ 2 * Y.Dh - 2 * Y.ell →
      (w'' : ℤ) * w (latOf hd e) ≤ 2 * ((w'' : ℤ) * Y.ctr (tgtCell a e) (latDir e true).1) + 2 * Y.Dh - 2 * Y.ell := by
    intro h
    have h' := abs_le.1 h
    rcases Int.units_eq_one_or w'' with h1 | h1 <;> rw [h1] <;> push_cast <;> linarith only [h'.1, h'.2]
  rcases mem_all_cases Y hd hL hH a e τ hI hr with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨w', g, sB, D, hB, hg, hwh, k, hk, rfl⟩
  · exact Or.inl (far (f_far_ARJT Y hd hL hH a e τ hY hτ hI (Or.inl ⟨k, hk, hw⟩)))
  · exact Or.inl (far (f_far_ARJT Y hd hL hH a e τ hY hτ hI (Or.inr (Or.inl ⟨k, hk, hw⟩))))
  · exact Or.inl (far (f_far_ARJT Y hd hL hH a e τ hY hτ hI (Or.inr (Or.inr (Or.inl ⟨k, hk, hw⟩)))))
  · exact Or.inl (far (f_far_ARJT Y hd hL hH a e τ hY hτ hI (Or.inr (Or.inr (Or.inr ⟨k, hk, hw⟩)))))
  · obtain ⟨hopp, htube⟩ := f_branch Y hd hL hH a e τ hY hτ hI hB hg hk hw
    by_cases hww : w'' = w'
    · subst hww
      rcases hwh with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
      · subst h3'; exact Or.inr (Or.inl ⟨h1', g, h2', htube⟩)
      · subst h3'; exact Or.inr (Or.inr ⟨h1', g, h2', htube⟩)
    · have hww' : (w'' : ℤ) = -(w' : ℤ) := by
        rcases Int.units_eq_one_or w'' with h1 | h1 <;> rcases Int.units_eq_one_or w' with h2 | h2 <;> subst h1 <;> subst h2 <;>
          first | exact absurd rfl hww | simp
      left; rw [hww']; linarith only [hopp]

end BGNd

end Percolation.Literature

end
