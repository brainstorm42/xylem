import Ctrllib.RoverPlanarRotation
import Ctrllib.RoverTranslationMotion
import Ctrllib.RoverConcreteClearance

/-! Heading-based model premises composed with rectangle/disc clearance.
The conservative rotation conversion used here is sqrt(2) times the heading
error or heading variation. Angles are real-valued radians with a coherent lift.
-/

namespace Ctrllib

/-- Planar headings discharge actual-pose isometry and convert angular error
and motion to the operator-norm quantities in the whole-body interval theorem. -/
theorem rover_heading_rectangle_interval_clearance
    {A B a : ℝ} {nx ny : ℕ} {S : Set ℝ}
    {c : ℝ → Point3} {theta : ℝ → ℝ}
    {cDelivered o : Point3} {thetaDelivered : ℝ}
    {t0 ts taus tau H ct age cs epsC epsTheta V omega delta : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (hnx : 0 < nx) (hny : 0 < ny)
    (hV : 0 ≤ V) (homega : 0 ≤ omega) (hepsTheta : 0 ≤ epsTheta)
    (htau : tau ∈ S) (hinterval : Set.Icc t0 (t0 + H) ⊆ S)
    (hTargetClock : |t0 - ts| ≤ ct)
    (hAge : |ts - taus| ≤ age) (hSampleClock : |taus - tau| ≤ cs)
    (htrans : ‖cDelivered - c tau‖ ≤ epsC)
    (hheading : |thetaDelivered - theta tau| ≤ epsTheta)
    (htransTime : ∀ s ∈ S, ∀ u ∈ S, ‖c s - c u‖ ≤ V * |s - u|)
    (hheadingTime : ∀ s ∈ S, ∀ u ∈ S, |theta s - theta u| ≤ omega * |s - u|)
    (hsep : ∀ ij : Fin nx × Fin ny,
      delta ≤ dist (cDelivered + planarRotation thetaDelivered
        (rectangleCellCentre A B nx ny ij)) o) :
    ∀ t ∈ Set.Icc t0 (t0 + H),
      ∀ x ∈ (fun b ↦ c t + planarRotation (theta t) b) '' planarRectangle A B,
      ∀ y ∈ (fun b ↦ o + b) '' planarDisc a,
      delta - (epsC + (Real.sqrt 2 * epsTheta) * Real.sqrt (A ^ 2 + B ^ 2))
        - (V + (Real.sqrt 2 * omega) * Real.sqrt (A ^ 2 + B ^ 2))
          * (H + ct + age + cs)
        - Real.sqrt ((A / nx) ^ 2 + (B / ny) ^ 2) - a ≤ dist x y := by
  apply rover_rectangle_disc_interval_clearance hA hB ha hnx hny hV
    (mul_nonneg (Real.sqrt_nonneg _) homega)
    (mul_nonneg (Real.sqrt_nonneg _) hepsTheta)
    htau hinterval hTargetClock hAge hSampleClock htrans
  · exact planarRotation_heading_error_le hepsTheta hheading
  · exact htransTime
  · intro s hs u hu
    calc
      ‖planarRotation (theta s) - planarRotation (theta u)‖ ≤
          Real.sqrt 2 * |theta s - theta u| := planarRotation_operator_diff_le _ _
      _ ≤ Real.sqrt 2 * (omega * |s - u|) :=
        mul_le_mul_of_nonneg_left (hheadingTime s hs u hu) (Real.sqrt_nonneg _)
      _ = (Real.sqrt 2 * omega) * |s - u| := by ring
  · intro t _ x y
    exact planarRotation_isometry (theta t) x y
  · exact hsep

/-- Finite held-velocity and held-heading-rate segments supply the motion
premises of the heading-based rectangle theorem, including across knots. -/
theorem rover_finite_motion_rectangle_clearance
    {A B a : ℝ} {nx ny N : ℕ} {T : ℕ → ℝ}
    {c : ℝ → Point3} {theta : ℝ → ℝ}
    {vel : ℕ → Point3} {headingRate : ℕ → ℝ}
    {cDelivered o : Point3} {thetaDelivered : ℝ}
    {t0 ts taus tau H ct age cs epsC epsTheta V omega delta : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (hnx : 0 < nx) (hny : 0 < ny)
    (hV : 0 ≤ V) (homega : 0 ≤ omega) (hepsTheta : 0 ≤ epsTheta)
    (_hH : 0 ≤ H) (hT : Monotone T)
    (hcentreModel : ∀ k < N, ∀ t ∈ Set.Icc (T k) (T (k + 1)),
      c t = c (T k) + (t - T k) • vel k)
    (hvel : ∀ k < N, ‖vel k‖ ≤ V)
    (hheadingModel : ∀ k < N, ∀ t ∈ Set.Icc (T k) (T (k + 1)),
      theta t = theta (T k) + (t - T k) * headingRate k)
    (hrate : ∀ k < N, |headingRate k| ≤ omega)
    (htau : tau ∈ Set.Icc (T 0) (T N))
    (hinterval : Set.Icc t0 (t0 + H) ⊆ Set.Icc (T 0) (T N))
    (hTargetClock : |t0 - ts| ≤ ct)
    (hAge : |ts - taus| ≤ age) (hSampleClock : |taus - tau| ≤ cs)
    (htrans : ‖cDelivered - c tau‖ ≤ epsC)
    (hheading : |thetaDelivered - theta tau| ≤ epsTheta)
    (hsep : ∀ ij : Fin nx × Fin ny,
      delta ≤ dist (cDelivered + planarRotation thetaDelivered
        (rectangleCellCentre A B nx ny ij)) o) :
    ∀ t ∈ Set.Icc t0 (t0 + H),
      ∀ x ∈ (fun b ↦ c t + planarRotation (theta t) b) '' planarRectangle A B,
      ∀ y ∈ (fun b ↦ o + b) '' planarDisc a,
      delta - (epsC + (Real.sqrt 2 * epsTheta) * Real.sqrt (A ^ 2 + B ^ 2))
        - (V + (Real.sqrt 2 * omega) * Real.sqrt (A ^ 2 + B ^ 2))
          * (H + ct + age + cs)
        - Real.sqrt ((A / nx) ^ 2 + (B / ny) ^ 2) - a ≤ dist x y := by
  have hcentreTime := finite_piecewise_affine_lipschitz hT hcentreModel hvel hV
  have hthetaModel : ∀ k < N, ∀ t ∈ Set.Icc (T k) (T (k + 1)),
      theta t = theta (T k) + (t - T k) • headingRate k := by
    simpa only [smul_eq_mul] using hheadingModel
  have hthetaBound : ∀ k < N, ‖headingRate k‖ ≤ omega := by
    simpa only [Real.norm_eq_abs] using hrate
  have hthetaTime : ∀ s ∈ Set.Icc (T 0) (T N),
      ∀ t ∈ Set.Icc (T 0) (T N), |theta s - theta t| ≤ omega * |s - t| := by
    simpa only [Real.norm_eq_abs] using
      finite_piecewise_affine_lipschitz hT hthetaModel hthetaBound homega
  exact rover_heading_rectangle_interval_clearance hA hB ha hnx hny
    hV homega hepsTheta htau hinterval hTargetClock hAge hSampleClock
    htrans hheading hcentreTime hthetaTime hsep

end Ctrllib

#print axioms Ctrllib.rover_heading_rectangle_interval_clearance
#print axioms Ctrllib.rover_finite_motion_rectangle_clearance
