import Ctrllib.RoverWaypointClearance

/-! Finite-step interfaces for connecting a recorded displacement to an ideal
command.  These theorems describe an explicit residual contract.  They do not
state that a logger, simulator, or physical plant satisfies the contract. -/

namespace Ctrllib

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem observed_displacement_norm_le
    {d u e : E} {h Δ W epsP epsT : ℝ}
    (hh : 0 < h) (_hΔ : 0 ≤ Δ) (hW : 0 ≤ W) (_hP : 0 ≤ epsP)
    (_hT : 0 ≤ epsT) (hdisp : d = h • u + e)
    (hu : ‖u‖ ≤ W) (he : ‖e‖ ≤ epsP) (hduration : |h - Δ| ≤ epsT) :
    ‖d‖ ≤ (Δ + epsT) * W + epsP := by
  have hle : h ≤ Δ + epsT := by
    have habs : h - Δ ≤ epsT := (abs_le.mp hduration).2
    linarith
  have hstep : ‖h • u‖ ≤ h * W := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left hu hh.le
  calc
    ‖d‖ = ‖h • u + e‖ := by rw [hdisp]
    _ ≤ ‖h • u‖ + ‖e‖ := norm_add_le _ _
    _ ≤ h * W + epsP := add_le_add hstep he
    _ ≤ (Δ + epsT) * W + epsP := by
      gcongr

theorem observed_displacement_norm_le_ideal
    {d u v e : E} {h Δ V epsU epsP epsT : ℝ}
    (hh : 0 < h) (hΔ : 0 ≤ Δ) (hV : 0 ≤ V) (hU : 0 ≤ epsU)
    (hP : 0 ≤ epsP) (hT : 0 ≤ epsT) (hdisp : d = h • u + e)
    (hideal : ‖v‖ ≤ V) (hcommand : ‖u - v‖ ≤ epsU)
    (he : ‖e‖ ≤ epsP) (hduration : |h - Δ| ≤ epsT) :
    ‖d‖ ≤ (Δ + epsT) * (V + epsU) + epsP := by
  have hu : ‖u‖ ≤ V + epsU := by
    calc
      ‖u‖ = ‖(u - v) + v‖ := by congr 1; abel
      _ ≤ ‖u - v‖ + ‖v‖ := norm_add_le _ _
      _ ≤ epsU + V := add_le_add hcommand hideal
      _ = V + epsU := add_comm _ _
  apply observed_displacement_norm_le hh hΔ (add_nonneg hV hU) hP hT hdisp hu he hduration

theorem reconstructed_trajectory_error_le
    {c₀ d u v e : E} {t₀ h t epsU epsP : ℝ}
    (hh : 0 < h) (ht : t ∈ Set.Icc t₀ (t₀ + h))
    (hdisp : d = h • u + e) (hcommand : ‖u - v‖ ≤ epsU)
    (he : ‖e‖ ≤ epsP) (hU : 0 ≤ epsU) (hP : 0 ≤ epsP) :
    ‖(c₀ + ((t - t₀) / h) • d) - (c₀ + (t - t₀) • v)‖ ≤
      h * epsU + epsP := by
  have hτ0 : 0 ≤ t - t₀ := by linarith [ht.1]
  have hτh : t - t₀ ≤ h := by linarith [ht.2]
  have hq0 : 0 ≤ (t - t₀) / h := div_nonneg hτ0 hh.le
  have hq1 : (t - t₀) / h ≤ 1 := (div_le_iff₀ hh).2 (by linarith)
  rw [hdisp, add_sub_add_left_eq_sub]
  have halg : ((t - t₀) / h) • (h • u + e) - (t - t₀) • v =
      (t - t₀) • (u - v) + ((t - t₀) / h) • e := by
    rw [smul_add, smul_smul]
    have hne : h ≠ 0 := ne_of_gt hh
    field_simp
    module
  rw [halg]
  calc
    ‖(t - t₀) • (u - v) + ((t - t₀) / h) • e‖ ≤
        ‖(t - t₀) • (u - v)‖ + ‖((t - t₀) / h) • e‖ := norm_add_le _ _
    _ ≤ (t - t₀) * epsU + ((t - t₀) / h) * epsP := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcommand hτ0)
        (mul_le_mul_of_nonneg_left he hq0)
    _ ≤ h * epsU + 1 * epsP := by
      exact add_le_add
        (by simpa [mul_comm] using (mul_le_mul_of_nonneg_left hτh hU))
        (mul_le_mul_of_nonneg_right hq1 hP)
    _ = h * epsU + epsP := by ring

theorem reconstructed_disc_clearance
    {c₀ o d : Point3} {t₀ h t a b D required : ℝ}
    (_hh : 0 < h) (_ht : t ∈ Set.Icc t₀ (t₀ + h))
    (hcentre : ‖((t - t₀) / h) • d‖ ≤ D)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hmargin : required ≤ dist c₀ o - D - a - b) :
    ∀ x ∈ (fun z ↦ c₀ + ((t - t₀) / h) • d + z) '' planarDisc a,
      ∀ y ∈ (fun z ↦ o + z) '' planarDisc b,
        required ≤ dist x y := by
  intro x hx y hy
  obtain ⟨ux, hux, rfl⟩ := hx
  obtain ⟨uy, huy, rfl⟩ := hy
  have hxc : dist (c₀ + ((t - t₀) / h) • d + ux) c₀ ≤ D + a := by
    rw [dist_eq_norm]
    have htri := norm_add_le (((t - t₀) / h) • d) ux
    have hu : ‖ux‖ ≤ a := hux.1
    simpa [add_assoc, add_comm, add_left_comm] using
      (show ‖((t - t₀) / h) • d + ux‖ ≤ D + a by linarith)
  have hyo : dist (o + uy) o ≤ b := by
    rw [dist_eq_norm]
    simpa using huy.1
  have herode := dist_actual_ge_dist_nominal_sub
    c₀ (c₀ + ((t - t₀) / h) • d + ux) o (o + uy) hxc hyo
  linarith [hmargin, herode]

/-- The endpoint displacement bound controls every point of the declared
straight reconstruction, not an arbitrary curve with the same endpoints. -/
theorem reconstructed_displacement_le
    {d : E} {t₀ h t D : ℝ}
    (hh : 0 < h) (ht : t ∈ Set.Icc t₀ (t₀ + h)) (hd : ‖d‖ ≤ D) :
    ‖((t - t₀) / h) • d‖ ≤ D := by
  have hs0 : 0 ≤ (t - t₀) / h := div_nonneg (by linarith [ht.1]) hh.le
  have hs1 : (t - t₀) / h ≤ 1 := (div_le_iff₀ hh).2 (by linarith [ht.2])
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  exact (mul_le_mul_of_nonneg_right hs1 (norm_nonneg d)).trans (by simpa using hd)

/-- Command cap, endpoint residual and timing discrepancy compose directly
into all-time whole-disc clearance for a reconstructed recorded step. -/
theorem residual_disc_step_safe
    {c₀ o d u : Point3} {t₀ h Δ W epsP epsT a b required : ℝ}
    (hh : 0 < h) (hΔ : 0 ≤ Δ) (hW : 0 ≤ W)
    (hP : 0 ≤ epsP) (hT : 0 ≤ epsT)
    (hu : ‖u‖ ≤ W) (he : ‖d - h • u‖ ≤ epsP)
    (hduration : |h - Δ| ≤ epsT) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmargin : required ≤ dist c₀ o - ((Δ + epsT) * W + epsP) - a - b) :
    ∀ t ∈ Set.Icc t₀ (t₀ + h),
      ∀ x ∈ (fun z ↦ c₀ + ((t - t₀) / h) • d + z) '' planarDisc a,
        ∀ y ∈ (fun z ↦ o + z) '' planarDisc b, required ≤ dist x y := by
  have hd := observed_displacement_norm_le hh hΔ hW hP hT
    (show d = h • u + (d - h • u) by abel) hu he hduration
  intro t ht
  exact reconstructed_disc_clearance hh ht (reconstructed_displacement_le hh ht hd)
    ha hb hmargin

/-- Closeness to the selected ideal waypoint command supplies the speed cap
for the residual interface. A speed-only check does not establish this premise. -/
theorem waypoint_residual_disc_step_safe
    {c₀ goal o d u : Point3} {t₀ h Δ V tolerance epsU epsP epsT a b required : ℝ}
    (hh : 0 < h) (hΔ : 0 < Δ) (hV : 0 ≤ V) (hU : 0 ≤ epsU)
    (hP : 0 ≤ epsP) (hT : 0 ≤ epsT)
    (hcommand : ‖u - waypointVelocity (goal - c₀) V Δ tolerance‖ ≤ epsU)
    (he : ‖d - h • u‖ ≤ epsP) (hduration : |h - Δ| ≤ epsT)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmargin : required ≤ dist c₀ o - ((Δ + epsT) * (V + epsU) + epsP) - a - b) :
    ∀ t ∈ Set.Icc t₀ (t₀ + h),
      ∀ x ∈ (fun z ↦ c₀ + ((t - t₀) / h) • d + z) '' planarDisc a,
        ∀ y ∈ (fun z ↦ o + z) '' planarDisc b, required ≤ dist x y := by
  have hu : ‖u‖ ≤ V + epsU := by
    have hv : ‖waypointVelocity (goal - c₀) V Δ tolerance‖ ≤ V :=
      waypointVelocity_norm_le hV hΔ
    have htri : ‖u‖ ≤ ‖u - waypointVelocity (goal - c₀) V Δ tolerance‖ +
        ‖waypointVelocity (goal - c₀) V Δ tolerance‖ := by
      simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub u
        (waypointVelocity (goal - c₀) V Δ tolerance) 0
    linarith
  exact residual_disc_step_safe hh hΔ.le (add_nonneg hV hU) hP hT
    hu he hduration ha hb hmargin

end

#print axioms Ctrllib.observed_displacement_norm_le
#print axioms Ctrllib.observed_displacement_norm_le_ideal
#print axioms Ctrllib.reconstructed_trajectory_error_le
#print axioms Ctrllib.reconstructed_disc_clearance
#print axioms Ctrllib.reconstructed_displacement_le
#print axioms Ctrllib.residual_disc_step_safe
#print axioms Ctrllib.waypoint_residual_disc_step_safe

end Ctrllib
