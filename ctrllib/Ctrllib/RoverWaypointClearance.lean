import Ctrllib.RoverWaypointModel
import Ctrllib.RoverConcreteClearance

/-! A complete one-step clearance implication for the ideal waypoint/disc model.
State delivery and timing are exact by construction. The actual plant on the
step is the affine trajectory driven by `waypointVelocity`.
-/

namespace Ctrllib

/-- The toy's ideal waypoint command supplies the motion premise of whole-disc
clearance throughout one step. This does not assert feasibility of later steps. -/
theorem waypoint_disc_step_clearance
    {c0 goal o : Point3} {V dt tolerance t0 a b : ℝ}
    (hV : 0 ≤ V) (hdt : 0 < dt) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    ∀ t ∈ Set.Icc t0 (t0 + dt),
      ∀ x ∈ (fun z ↦ c0 + (t - t0) • waypointVelocity (goal - c0) V dt tolerance + z)
        '' planarDisc a,
      ∀ y ∈ (fun z ↦ o + z) '' planarDisc b,
      dist c0 o - V * dt - a - b ≤ dist x y := by
  have hobs : ∀ y ∈ (fun z ↦ o + z) '' planarDisc b,
      ∃ _ : Unit, dist y o ≤ b := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨(), by simpa [dist_eq_norm] using hz.1⟩
  have h := rover_static_obstacle_interval_clearance
    (S := Set.univ) (Body := planarDisc a)
    (samples := fun _ : Unit ↦ (0 : Point3)) (obstacleSamples := fun _ : Unit ↦ o)
    (c := fun t ↦ c0 + (t - t0) • waypointVelocity (goal - c0) V dt tolerance)
    (Q := fun _ ↦ ContinuousLinearMap.id ℝ Point3)
    (cDelivered := c0) (QDelivered := ContinuousLinearMap.id ℝ Point3)
    (t0 := t0) (ts := t0) (taus := t0) (tau := t0) (H := dt)
    (ct := 0) (age := 0) (cs := 0) (epsC := 0) (epsQ := 0)
    (r := 0) (V := V) (Omega := 0) (rhoB := a) (rhoO := b) (delta := dist c0 o)
    (by norm_num) hV (by norm_num) (by norm_num)
    (Set.mem_univ _) (Set.subset_univ _)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun s _ t _ ↦ waypoint_affine_motion_bound hV hdt)
    (by intros; simp)
    centred_disc_singleton_cover hobs (by intros; simp) (by intros; simp)
  simpa using h

/-- A sufficient margin gives every represented body-point pair the required
separation throughout the ideal step. -/
theorem waypoint_disc_step_safe
    {c0 goal o : Point3} {V dt tolerance t0 a b required : ℝ}
    (hV : 0 ≤ V) (hdt : 0 < dt)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hrequired : 0 < required)
    (hmargin : required ≤ dist c0 o - V * dt - a - b) :
    ∀ t ∈ Set.Icc t0 (t0 + dt),
      ∀ x ∈ (fun z ↦ c0 + (t - t0) • waypointVelocity (goal - c0) V dt tolerance + z)
        '' planarDisc a,
      ∀ y ∈ (fun z ↦ o + z) '' planarDisc b,
      required ≤ dist x y := by
  intro t ht x hx y hy
  exact hmargin.trans (waypoint_disc_step_clearance hV hdt ha hb t ht x hx y hy)

end Ctrllib

#print axioms Ctrllib.waypoint_disc_step_clearance
#print axioms Ctrllib.waypoint_disc_step_safe
