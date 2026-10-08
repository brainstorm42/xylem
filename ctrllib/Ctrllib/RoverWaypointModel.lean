import Ctrllib.RoverPoseGeometry

/-! Real-arithmetic model of the toy's speed-capped waypoint command.
This is not a formal translation of the Python floating-point implementation.
The plant must realize the command as its actual velocity on the step.
-/

namespace Ctrllib

/-- Stop at tolerance, otherwise move toward the goal without exceeding speed
`V` or traversing more than the remaining distance in a step of duration `dt`. -/
noncomputable def waypointVelocity (d : Point3) (V dt tolerance : ℝ) : Point3 :=
  if ‖d‖ ≤ tolerance ∨ d = 0 then 0
  else (min V (‖d‖ / dt) / ‖d‖) • d

/-- The moving branch agrees with the source-inspired distance-first formula
over real arithmetic; this does not assert floating-point equivalence. -/
theorem waypointVelocity_moving_formula {d : Point3} {V dt tolerance : ℝ}
    (hdt : 0 < dt) (hmoving : ¬ (‖d‖ ≤ tolerance ∨ d = 0)) :
    waypointVelocity d V dt tolerance =
      (1 / dt) • ((min ‖d‖ (V * dt) / ‖d‖) • d) := by
  simp only [waypointVelocity, hmoving, ↓reduceIte, smul_smul]
  have hmin : min V (‖d‖ / dt) = min ‖d‖ (V * dt) / dt := by
    rw [← min_div_div_right hdt.le]
    simp [ne_of_gt hdt, min_comm]
  rw [hmin]
  congr 1
  ring

/-- The ideal waypoint command satisfies its speed cap, including the stop branch. -/
theorem waypointVelocity_norm_le {d : Point3} {V dt tolerance : ℝ}
    (hV : 0 ≤ V) (hdt : 0 < dt) :
    ‖waypointVelocity d V dt tolerance‖ ≤ V := by
  unfold waypointVelocity
  split_ifs with h
  · simpa using hV
  · have hd : 0 < ‖d‖ := norm_pos_iff.mpr (not_or.mp h).2
    have hm : 0 ≤ min V (‖d‖ / dt) := le_min hV (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hm hd.le),
      div_mul_cancel₀ _ (ne_of_gt hd)]
    exact min_le_left _ _

/-- Each ideal step is a fraction between zero and one of the displacement to
the waypoint; this states no overshoot without assuming a nonzero distance. -/
theorem waypointVelocity_step_fraction {d : Point3} {V dt tolerance : ℝ}
    (hV : 0 ≤ V) (hdt : 0 < dt) :
    ∃ α ∈ Set.Icc (0 : ℝ) 1,
      dt • waypointVelocity d V dt tolerance = α • d := by
  unfold waypointVelocity
  split_ifs with h
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  · have hd : 0 < ‖d‖ := norm_pos_iff.mpr (not_or.mp h).2
    have hm : 0 ≤ min V (‖d‖ / dt) := le_min hV (by positivity)
    refine ⟨dt * (min V (‖d‖ / dt) / ‖d‖), ⟨by positivity, ?_⟩, ?_⟩
    · have hcap : min V (‖d‖ / dt) * dt ≤ ‖d‖ :=
        (le_div_iff₀ hdt).mp (min_le_right _ _)
      rw [← mul_div_assoc]
      exact (div_le_one hd).mpr (by simpa [mul_comm] using hcap)
    · rw [smul_smul]

/-- Actual affine motion driven by the ideal command has the required
translation displacement bound for arbitrary two times in that same step. -/
theorem waypoint_affine_motion_bound {d c0 : Point3} {V dt tolerance t0 s t : ℝ}
    (hV : 0 ≤ V) (hdt : 0 < dt) :
    ‖(c0 + (s - t0) • waypointVelocity d V dt tolerance) -
      (c0 + (t - t0) • waypointVelocity d V dt tolerance)‖ ≤ V * |s - t| := by
  rw [add_sub_add_left_eq_sub, ← sub_smul]
  simp only [sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs]
  calc
    |s - t| * ‖waypointVelocity d V dt tolerance‖ ≤ |s - t| * V :=
      mul_le_mul_of_nonneg_left (waypointVelocity_norm_le hV hdt) (abs_nonneg _)
    _ = V * |s - t| := mul_comm _ _

end Ctrllib

#print axioms Ctrllib.waypointVelocity_norm_le
#print axioms Ctrllib.waypointVelocity_moving_formula
#print axioms Ctrllib.waypointVelocity_step_fraction
#print axioms Ctrllib.waypoint_affine_motion_bound
