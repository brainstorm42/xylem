import Ctrllib.RoverConcreteCovers
import Ctrllib.RoverIntervalClearance

/-! Concrete finite rectangle geometry composed with interval clearance.

The obstacle is an exact translated planar disc. The rectangle may rotate;
the actual pose, time domain, delivered-pose errors, pose-motion bounds and
delivered separation remain the explicit application obligations.
-/

namespace Ctrllib

/-- The finite rectangle grid discharges the body-cover and lever-arm premises
of interval clearance against an exact static disc. -/
theorem rover_rectangle_disc_interval_clearance
    {A B a : ℝ} {nx ny : ℕ} {S : Set ℝ}
    {c : ℝ → Point3} {Q : ℝ → (Point3 →L[ℝ] Point3)}
    {cDelivered o : Point3} {QDelivered : Point3 →L[ℝ] Point3}
    {t0 ts taus tau H ct age cs epsC epsQ V Omega delta : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_ha : 0 ≤ a) (hnx : 0 < nx) (hny : 0 < ny)
    (hV : 0 ≤ V) (hOmega : 0 ≤ Omega) (hepsQ : 0 ≤ epsQ)
    (htau : tau ∈ S) (hinterval : Set.Icc t0 (t0 + H) ⊆ S)
    (hTargetClock : |t0 - ts| ≤ ct)
    (hAge : |ts - taus| ≤ age) (hSampleClock : |taus - tau| ≤ cs)
    (htrans : ‖cDelivered - c tau‖ ≤ epsC)
    (hrot : ‖QDelivered - Q tau‖ ≤ epsQ)
    (htransTime : ∀ s ∈ S, ∀ u ∈ S, ‖c s - c u‖ ≤ V * |s - u|)
    (hrotTime : ∀ s ∈ S, ∀ u ∈ S, ‖Q s - Q u‖ ≤ Omega * |s - u|)
    (hisometry : ∀ t ∈ Set.Icc t0 (t0 + H), ∀ x y : Point3,
      ‖Q t x - Q t y‖ = ‖x - y‖)
    (hsep : ∀ ij : Fin nx × Fin ny,
      delta ≤ dist (cDelivered + QDelivered (rectangleCellCentre A B nx ny ij)) o) :
    ∀ t ∈ Set.Icc t0 (t0 + H),
      ∀ x ∈ (fun b ↦ c t + Q t b) '' planarRectangle A B,
      ∀ y ∈ (fun b ↦ o + b) '' planarDisc a,
      delta - (epsC + epsQ * Real.sqrt (A ^ 2 + B ^ 2))
        - (V + Omega * Real.sqrt (A ^ 2 + B ^ 2)) * (H + ct + age + cs)
        - Real.sqrt ((A / nx) ^ 2 + (B / ny) ^ 2) - a ≤ dist x y := by
  have hobstacleCover : ∀ y ∈ (fun b ↦ o + b) '' planarDisc a,
      ∃ _ : Unit, dist y o ≤ a := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨u, hu⟩ := centred_disc_singleton_cover b hb
    exact ⟨u, by simpa [dist_eq_norm] using hu⟩
  exact rover_static_obstacle_interval_clearance
    (samples := rectangleCellCentre A B nx ny) (obstacleSamples := fun _ : Unit ↦ o)
    (Real.sqrt_nonneg _) hV hOmega hepsQ htau hinterval
    hTargetClock hAge hSampleClock
    (planar_rectangle_cell_centre_lever_arm hA hB hnx hny)
    htrans hrot htransTime hrotTime
    (planar_rectangle_cell_centre_cover hA hB hnx hny)
    hobstacleCover hisometry (fun ij _ ↦ hsep ij)

end Ctrllib

#print axioms Ctrllib.rover_rectangle_disc_interval_clearance
