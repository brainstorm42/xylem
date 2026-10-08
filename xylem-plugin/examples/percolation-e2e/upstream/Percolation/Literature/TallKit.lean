import Percolation.Literature.TallStatic
import Percolation.Util.Linter

/-!
# The tall gait, XXIII: the tall kit is good; percolation in slabs of `ℤ^d`, tall regime

We discharge the obligations `Kit.Good` of the block kit
`tallKit` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.52), regime
`L + 1 ≤ P (H + 1)`): the initial structure `U₀` lies in the core box of the origin cell
(`dmid_U0_box`), the initial tokens are admissible (`tAdm_initTok`), zones are statically disjoint and
avoid `U₀` (`tall_disjoint_zone`, `tall_disjoint_U₀`, from `TallStatic.lean`), and the dynamic
obligations (`tall_complete`, `tall_connect`, `init_conn`). Hence `tallKit_good`, and by
`Kit.theta_pos`: if bricks are good with probability at least `1 - 1/(64 R)`, `R = 2¹³ P³`, the origin
percolates in `ℤ^d` with positive probability (`theta_pos_tall`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 169–176, Lemma (7.52).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d)

/-! ## The origin cell: lanes and the initial structure -/

omit [NeZero d] in
/-- The lanes of the origin cell are the bare lane offsets. [folklore] -/
theorem lane_zero (e : MDir) : Y.lane 0 e = Y.nu e := by
  unfold TallLayout.lane TallLayout.ctr TallLayout.cpar; simp

omit [NeZero d] in
/-- **`U₀` lies in the core box of the origin cell**: every doubled midpoint of an edge of `U₀` has
both plane coordinates at most `2 · D/2 - 2ℓ` in absolute value. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
theorem dmid_U0_box (hY : Y.OK) {z : Sym2 (Site d)} (hz : z ∈ U0 Y hd) (e' : MDir) : |dmid z (axOf hd e')| ≤ 2 * Y.Dh - 2 * Y.ell := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
  have hbig : 2 * Y.lam + 2 * Y.m + 2 * Y.ell ≤ 2 * Y.Dh := by linarith only [hlam, hDh, hP3, hP2, hPe, hP64, hell, hmH]
  have hD : 0 ≤ Y.Dh - Y.ell := by linarith only [hbig, hlam0, hm0, hl0]
  rw [U0, Finset.mem_biUnion] at hz
  obtain ⟨e, -, hz⟩ := hz
  have hnu : |Y.nu e| ≤ Y.lam := by
    rw [nu_eq]; rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h, abs_of_nonneg hlam0]
  have hnu' := abs_le.1 hnu
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  -- values of the initial points
  have hP0e : initPos Y hd e (axOf hd e) = (sgOf e : ℤ) * (Y.Dh - Y.ell) := by unfold initPos; rw [if_pos rfl]
  have hP0f : initPos Y hd e (latOf hd e) = Y.nu e := by
    unfold initPos; rw [if_neg (latOf_ne_axOf hd e), if_pos rfl, lane_zero]
  have hP1e : initP1 Y hd e (axOf hd e) = 0 := by unfold initP1; rw [shift_apply_of_ne _ (axOf_ne_ax0 hd e)]; rfl
  have hP1f : initP1 Y hd e (latOf hd e) = 0 := by unfold initP1; rw [shift_apply_of_ne _ (latOf_ne_ax0 hd e)]; rfl
  have hP2e : initP2 Y hd e (axOf hd e) = 0 := by unfold initP2; rw [shift_apply_of_ne _ (latOf_ne_axOf hd e).symm, hP1e]
  have hP2f : initP2 Y hd e (latOf hd e) = Y.nu e := by unfold initP2; rw [shift_apply_self, hP1f, lane_zero, zero_add]
  -- the coordinate `axOf e'` is `axOf e` or `latOf e`
  have hax : axOf hd e' = axOf hd e ∨ axOf hd e' = latOf hd e := by
    by_cases h : e'.1 = e.1
    · exact Or.inl (axes_of_fst_eq hd h).1
    · exact Or.inr (axes_of_fst_ne hd h).1
  rw [Finset.mem_union] at hz
  rcases hz with hz | hz
  · -- the port square
    obtain ⟨h1, h2⟩ := dmid_of_mem_sqEdgesAt hz
    rcases hax with h | h <;> rw [h]
    · rw [h1, hP0e]
      rcases hs1 with hs | hs <;> rw [hs] <;> [rw [abs_of_nonneg (by linarith)]; rw [abs_of_nonpos (by linarith)]] <;> linarith
    · have := abs_le.1 (h2 (latOf hd e) (latOf_ne_axOf hd e))
      rw [hP0f] at this
      rw [abs_le]; constructor <;> linarith only [this.1, this.2, hnu'.1, hnu'.2, hbig]
  · rw [initPath, Finset.mem_union, Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · -- up: plane coordinates vanish
      obtain ⟨h1, -, -⟩ := dmid_of_mem_segEdges hz
      rcases hax with h | h <;> rw [h]
      · rw [h1 _ (axOf_ne_ax0 hd e)]; simp only [Pi.zero_apply, mul_zero, abs_zero]; linarith only [hD]
      · rw [h1 _ (latOf_ne_ax0 hd e)]; simp only [Pi.zero_apply, mul_zero, abs_zero]; linarith only [hD]
    · -- sideways to the lane
      obtain ⟨h1, h2, h3⟩ := dmid_of_mem_segEdges hz
      rcases hax with h | h <;> rw [h]
      · rw [h1 _ (latOf_ne_axOf hd e).symm, hP1e]; simp only [mul_zero, abs_zero]; linarith only [hD]
      · rw [hP1f] at h2 h3
        have hn : (((Y.lane 0 e).natAbs : ℕ) : ℤ) = |Y.nu e| := by rw [lane_zero]; exact Int.natCast_natAbs (Y.nu e)
        rw [hn] at h3
        rw [abs_le]
        split_ifs at h2 h3 <;> constructor <;> linarith only [h2, h3, hnu, hbig, hm0, hl0]
    · -- forward to the port
      obtain ⟨h1, h2, h3⟩ := dmid_of_mem_segEdges hz
      rw [Int.toNat_of_nonneg hD] at h3
      rcases hax with h | h <;> rw [h]
      · rw [hP2e] at h2 h3
        rw [abs_le]
        split_ifs at h2 h3 <;> constructor <;> linarith only [h2, h3, hD]
      · rw [h1 _ (latOf_ne_axOf hd e), hP2f, abs_le]
        constructor <;> linarith only [hnu'.1, hnu'.2, hbig, hm0]

/-! ## The initial tokens are admissible -/

omit [NeZero d] in
/-- **The initial tokens are admissible.** [cite: GrimmettPercolation1999, §7.3 p. 171] -/
theorem tAdm_initTok (hY : Y.OK) (e : MDir) : TAdm hd Y 0 e (initTok Y hd e) := by
  obtain ⟨hLp0, -, -, hell, hmH, -, -, -, hΔ0, hρv, hρp, -⟩ := hY.facts
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hP0e : initPos Y hd e (axOf hd e) = (sgOf e : ℤ) * (Y.Dh - Y.ell) := by unfold initPos; rw [if_pos rfl]
  have hP0f : initPos Y hd e (latOf hd e) = Y.lane 0 e := by unfold initPos; rw [if_neg (latOf_ne_axOf hd e), if_pos rfl]
  have hP00 : initPos Y hd e (ax0 hd) = Y.zOf (rev e) := by
    unfold initPos; rw [if_neg (axOf_ne_ax0 hd e).symm, if_neg (latOf_ne_ax0 hd e).symm, if_pos rfl]
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun h => absurd h (by simp [initTok])⟩
  · show Y.Dh - Y.ell ≤ (sgOf e : ℤ) * (initPos Y hd e (axOf hd e) - Y.ctr 0 e.1) ∧ (sgOf e : ℤ) * (initPos Y hd e (axOf hd e) - Y.ctr 0 e.1) ≤ Y.Dh - 1
    rw [hP0e]
    have : Y.ctr 0 e.1 = 0 := by unfold TallLayout.ctr; simp
    rw [this, sub_zero, ← mul_assoc, hss, one_mul]
    constructor <;> linarith only [hell, hmH]
  · show |initPos Y hd e (latOf hd e) - Y.lane 0 e| ≤ Y.ρp
    rw [hP0f, sub_self, abs_zero, hρp]; linarith only [hell, hmH, hΔ0, hLp0]
  · show |initPos Y hd e (ax0 hd) - Y.zOf ((some (rev e) : Option MDir).getD e)| ≤ Y.ρv
    rw [hP00, Option.getD_some, sub_self, abs_zero, hρv]; linarith only [hell, hmH, hLp0]
  · intro j hj1 hj2 hj3
    show |initPos Y hd e j| ≤ Y.Lp
    unfold initPos; rw [if_neg hj1, if_neg hj2, if_neg hj3, abs_zero]; exact hLp0

/-! ## The static obligations, at the level of the kit -/

variable (hY : Y.OK)

/-- **Zones are statically disjoint** (`Kit.Good.disjoint_zone`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem tall_disjoint_zone {a a' : Site 2} {e e' : MDir} {τ τ' : TTok d} (hτ : (tallKit Y hd hY).Adm a e τ) (hτ' : (tallKit Y hd hY).Adm a' e' τ')
    (h1 : (a, e) ≠ (a', e')) (h2 : a' ≠ a + stepVec e) (h3 : ¬(a' + stepVec e' = a ∧ (tallKit Y hd hY).srcDir τ = some e')) :
    Disjoint ((tallKit Y hd hY).zone a e τ) ((tallKit Y hd hY).zone a' e' τ') := by
  rw [tallKit_Adm] at hτ hτ'
  rw [tallKit_srcDir] at h3
  rw [tallKit_zone, tallKit_zone, Finset.disjoint_left]
  intro z hz hz'
  have hr := ((mem_zoneF Y hd a e τ).1 hz).2.2
  have hr' := ((mem_zoneF Y hd a' e' τ').1 hz').2.2
  refine zoneRegion_disjoint Y hd hY hτ.1 hτ'.1 hτ.2 h1 h2 (fun d' hca hs heq => ?_) hr hr'
  subst heq
  rcases srcDirK_cases Y hd hY hτ.1 hs with h | h
  · exact h3 ⟨hca, h⟩
  · exact h2 (eq_tgtCell_of_rev hca h)

/-- **Zones not aimed at the origin cell avoid `U₀`** (`Kit.Good.disjoint_U₀`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem tall_disjoint_U₀ {a : Site 2} {e : MDir} {τ : TTok d} (hτ : (tallKit Y hd hY).Adm a e τ) (h0 : a + stepVec e ≠ 0) :
    Disjoint ((tallKit Y hd hY).zone a e τ) (tallKit Y hd hY).U₀ := by
  rw [tallKit_Adm] at hτ
  rw [tallKit_zone, tallKit_U0, Finset.disjoint_left]
  intro z hz hz'
  have hr := ((mem_zoneF Y hd a e τ).1 hz).2.2
  exact zoneRegion_avoids_origin Y hd hY hτ.1 h0 hr (dmid_U0_box Y hd hY hz')

/-! ## The tall kit is good -/

/-- **The tall kit satisfies the obligations of a good kit.** [cite: GrimmettPercolation1999, §7.3 pp. 169–176] -/
theorem tallKit_good : (tallKit Y hd hY).Good Y.m Y.L Y.H 0 where
  adm_init e := ⟨tAdm_initTok Y hd hY e, by simp [tallKit_init, initTok]⟩
  src_init e := by
    rw [tallKit_srcDir, tallKit_init]
    exact srcDirK_of_adm_rev Y hd hY (tAdm_initTok Y hd hY e) rfl
  disjoint_zone hτ hτ' h1 h2 h3 := tall_disjoint_zone Y hd hY hτ hτ' h1 h2 h3
  disjoint_U₀ hτ h0 := tall_disjoint_U₀ Y hd hY hτ h0
  U₀_subset := by rw [tallKit_U0]; exact U0_subset_edgeSet Y hd
  conn_init ω hω e := by
    rw [tallKit_U0] at hω
    obtain ⟨hseed, hreach⟩ := init_conn Y hd hY hω e
    exact ⟨hseed, hreach⟩
  complete ω hτ hgood := by
    rw [tallKit_Adm] at hτ
    obtain ⟨f, hf, -⟩ := tall_complete Y hd _ _ _ hY hτ.1 ω hgood
    change (tallKit Y hd hY).gfinish Y.m Y.L Y.H _ _ _ ((tallKit Y hd hY).run Y.m Y.L Y.H _ _ _ Y.Rmax ω) ≠ none
    rw [hf]; simp
  connect ω f hτ hpre hf e' he' := by
    rw [tallKit_Adm] at hτ
    exact tall_connect Y hd _ _ _ hY hτ.1 ω hpre hf he'

include hd hY in
/-- **Percolation in slabs, tall regime.** If the layout is admissible (`m + 1 ≤ L`, `2m + 2 ≤ H`,
`L + 1 ≤ P (H + 1)`, `8 ≤ P`) and bricks `B(L, H)` are good (clean rule, seeds `b_k(m)`) with
`P_p`-probability at least `1 - 1/(64 R)`, `R = 2¹³ P³`, then `θ(p) > 0` on `ℤ^d`, `d ≥ 3`.
[cite: GrimmettPercolation1999, Lemma (7.52) p. 169, proof pp. 169–176] -/
theorem theta_pos_tall (p : unitInterval) (hp : 0 < (p : ℝ))
    (hν : (Y.Rmax : ℝ) * (1 - (bondPercolation (zdGraph d) p).real (goodC d Y.m Y.L Y.H)) ≤ 1 / 64) : 0 < theta (zdGraph d) 0 p := by
  have hH : 1 ≤ Y.H := by have := hY.hH; omega
  have hmL : Y.m < Y.L := by have := hY.hL; omega
  exact (tallKit Y hd hY).theta_pos Y.m Y.L Y.H (tallKit_good Y hd hY) hH hmL p hp (by rw [tallKit_R]; exact hν)

end BGNd

end Percolation.Literature

end
