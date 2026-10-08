import Ctrllib.RoverPoseGeometry
import Ctrllib.RoverClock

/-! Clearance against an exact static obstacle over a declared future interval.

The delivered pose has one fixed sample time. All clocks use the same real-valued
seconds scale. The time domain, rigid body, actual pose, cover and error/motion
premises remain explicit; no controller or numerical implementation is inferred.
-/

namespace Ctrllib

/-- Decision-clock error, reported sample age, sample-clock error and a future
horizon bound the age of the same delivered pose at every target in the interval. -/
theorem timestamp_error_over_future_interval
    {t t0 ts taus tau H ct age cs : ℝ}
    (ht : t ∈ Set.Icc t0 (t0 + H))
    (hTargetClock : |t0 - ts| ≤ ct)
    (hAge : |ts - taus| ≤ age)
    (hSampleClock : |taus - tau| ≤ cs) :
    |t - tau| ≤ H + ct + age + cs := by
  have hbase := timestamp_error_decomposition hTargetClock hAge hSampleClock
  have hfuture : |t - t0| ≤ H := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  calc
    |t - tau| = |(t - t0) + (t0 - tau)| := by congr 1; ring
    _ ≤ |t - t0| + |t0 - tau| := abs_add_le _ _
    _ ≤ H + ct + age + cs := by linarith

/-- A rigid body stays separated from an exact static obstacle throughout the
given interval, conditional on uniform pose-motion bounds, source covers and
the delivered all-pair separation. Sample lever arm `r` is distinct from cover
radii `rhoB,rhoO`. World bodies are the actual rigid image of `Body`. -/
theorem rover_static_obstacle_interval_clearance
    {I J : Type*} {S : Set ℝ} {Body Obstacle : Set Point3}
    {samples : I → Point3} {obstacleSamples : J → Point3}
    {c : ℝ → Point3} {Q : ℝ → (Point3 →L[ℝ] Point3)}
    {cDelivered : Point3} {QDelivered : Point3 →L[ℝ] Point3}
    {t0 ts taus tau H ct age cs epsC epsQ r V Omega rhoB rhoO delta : ℝ}
    (hr : 0 ≤ r) (hV : 0 ≤ V) (hOmega : 0 ≤ Omega) (hepsQ : 0 ≤ epsQ)
    (htau : tau ∈ S) (hinterval : Set.Icc t0 (t0 + H) ⊆ S)
    (hTargetClock : |t0 - ts| ≤ ct)
    (hAge : |ts - taus| ≤ age) (hSampleClock : |taus - tau| ≤ cs)
    (hsamples : ∀ i, ‖samples i‖ ≤ r)
    (htrans : ‖cDelivered - c tau‖ ≤ epsC)
    (hrot : ‖QDelivered - Q tau‖ ≤ epsQ)
    (htransTime : ∀ s ∈ S, ∀ u ∈ S, ‖c s - c u‖ ≤ V * |s - u|)
    (hrotTime : ∀ s ∈ S, ∀ u ∈ S, ‖Q s - Q u‖ ≤ Omega * |s - u|)
    (hcover : ∀ b ∈ Body, ∃ i, ‖b - samples i‖ ≤ rhoB)
    (hobstacleCover : ∀ y ∈ Obstacle, ∃ j, dist y (obstacleSamples j) ≤ rhoO)
    (hisometry : ∀ t ∈ Set.Icc t0 (t0 + H), ∀ x y : Point3,
      ‖Q t x - Q t y‖ = ‖x - y‖)
    (hsep : ∀ i j, delta ≤ dist (cDelivered + QDelivered (samples i))
      (obstacleSamples j)) :
    ∀ t ∈ Set.Icc t0 (t0 + H),
      ∀ x ∈ (fun b ↦ c t + Q t b) '' Body, ∀ y ∈ Obstacle,
      delta - (epsC + epsQ * r) - (V + Omega * r) * (H + ct + age + cs)
        - rhoB - rhoO ≤ dist x y := by
  intro t ht
  have htime := timestamp_error_over_future_interval ht hTargetClock hAge hSampleClock
  have hspeed : 0 ≤ V + Omega * r := by positivity
  have herror : ∀ i, dist (cDelivered + QDelivered (samples i))
      (c t + Q t (samples i)) ≤
      epsC + epsQ * r + (V + Omega * r) * (H + ct + age + cs) := by
    intro i
    have hpose := rigid_point_error_le (hsamples i) htrans hrot hepsQ
    have hmotion := time_lipschitz_point_error (hsamples i) hOmega htransTime hrotTime
      tau htau t (hinterval ht)
    have hmove : ‖(c tau + Q tau (samples i)) - (c t + Q t (samples i))‖ ≤
        (V + Omega * r) * (H + ct + age + cs) := by
      apply le_trans hmotion
      exact mul_le_mul_of_nonneg_left (by simpa [abs_sub_comm] using htime) hspeed
    have htri := dist_triangle (cDelivered + QDelivered (samples i))
      (c tau + Q tau (samples i)) (c t + Q t (samples i))
    simp only [dist_eq_norm] at htri ⊢
    linarith
  have hsampleSep : ∀ i j,
      delta - (epsC + epsQ * r) - (V + Omega * r) * (H + ct + age + cs) ≤
      dist (c t + Q t (samples i)) (obstacleSamples j) := by
    intro i j
    have htri := dist_triangle (cDelivered + QDelivered (samples i))
      (c t + Q t (samples i)) (obstacleSamples j)
    linarith [herror i, hsep i j]
  have hworldCover : ∀ x ∈ (fun b ↦ c t + Q t b) '' Body,
      ∃ i, dist x (c t + Q t (samples i)) ≤ rhoB := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    simpa only [dist_eq_norm] using
      rigid_cover_transport (t := c t) hcover (hisometry t ht) b hb
  exact rover_body_clearance_of_sample_cover hworldCover hobstacleCover hsampleSep

/-- With positive sample-motion rate, the clearance margin is equivalent to a
future-horizon upper bound. This algebra does not establish the motion/domain
premises, and a negative upper bound permits no nonnegative horizon. -/
theorem clearance_margin_iff_horizon
    {delta error rhoB rhoO required speed H ageBudget : ℝ}
    (hspeed : 0 < speed) :
    required ≤ delta - error - speed * (H + ageBudget) - rhoB - rhoO ↔
      H ≤ (delta - error - rhoB - rhoO - required) / speed - ageBudget := by
  conv_rhs => rw [le_sub_iff_add_le, le_div_iff₀ hspeed]
  constructor <;> intro h <;> nlinarith

end Ctrllib

#print axioms Ctrllib.timestamp_error_over_future_interval
#print axioms Ctrllib.rover_static_obstacle_interval_clearance
#print axioms Ctrllib.clearance_margin_iff_horizon
