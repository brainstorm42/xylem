/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.HandbookPlanarTwoLink

/-!
# Handbook planar world/body velocity bridge

This module gives the same-point planar velocity conversion for the accepted
two-link endpoint.  The world velocity is the derivative of the endpoint
position in the fixed frame used by `handbookTwoLinkPosition`, followed by the
unwrapped heading rate.  The body velocity rotates only the endpoint
translation by `R(-theta)` and retains the out-of-plane angular rate.  It is
not the derivative of a moving-frame position coordinate, and this module does
not claim a general spatial twist, D--H realization, displaced reference
point, or physical robot model.
-/

open Matrix
open scoped BigOperators

namespace Ctrllib

/-- Convert fixed/world-frame endpoint velocity to body axes at heading `theta`.
The vector order is `(v_x, v_y, omega)`, with the same endpoint reference point
on both sides. -/
noncomputable def handbookPlanarWorldToBodyVelocity
    (theta : ℝ) (vWorld : HandbookPlanarEndpoint) : HandbookPlanarEndpoint :=
  planarRotationMatrix (-theta) *ᵥ vWorld

/-- Convert body-axis endpoint velocity back to the fixed/world frame. -/
noncomputable def handbookPlanarBodyToWorldVelocity
    (theta : ℝ) (vBody : HandbookPlanarEndpoint) : HandbookPlanarEndpoint :=
  planarRotationMatrix theta *ᵥ vBody

/-- The world-to-body conversion is the explicit planar `R(-theta)` formula. -/
theorem handbookPlanarWorldToBodyVelocity_formula
    (theta : ℝ) (vWorld : HandbookPlanarEndpoint) :
    handbookPlanarWorldToBodyVelocity theta vWorld =
      ![Real.cos theta * vWorld 0 + Real.sin theta * vWorld 1,
        -Real.sin theta * vWorld 0 + Real.cos theta * vWorld 1,
        vWorld 2] := by
  funext i
  fin_cases i <;>
    simp [handbookPlanarWorldToBodyVelocity, planarRotationMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Real.cos_neg, Real.sin_neg] <;> ring

/-- The body-to-world conversion is the corresponding `R(theta)` formula. -/
theorem handbookPlanarBodyToWorldVelocity_formula
    (theta : ℝ) (vBody : HandbookPlanarEndpoint) :
    handbookPlanarBodyToWorldVelocity theta vBody =
      ![Real.cos theta * vBody 0 - Real.sin theta * vBody 1,
        Real.sin theta * vBody 0 + Real.cos theta * vBody 1,
        vBody 2] := by
  funext i
  fin_cases i <;>
    simp [handbookPlanarBodyToWorldVelocity, planarRotationMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

private theorem planarRotationMatrix_mulVec_neg_mulVec
    (theta : ℝ) (v : HandbookPlanarEndpoint) :
    planarRotationMatrix theta *ᵥ (planarRotationMatrix (-theta) *ᵥ v) = v := by
  funext i
  fin_cases i
  · simp [planarRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Real.cos_neg, Real.sin_neg]
    ring_nf
    linear_combination (v 0) * Real.cos_sq_add_sin_sq theta
  · simp [planarRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Real.cos_neg, Real.sin_neg]
    ring_nf
    linear_combination (v 1) * Real.cos_sq_add_sin_sq theta
  · simp [planarRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Real.cos_neg, Real.sin_neg]

/-- The two conversions are inverse in the world-to-body direction. -/
@[simp] theorem handbookPlanarBodyToWorldVelocity_worldToBodyVelocity
    (theta : ℝ) (vWorld : HandbookPlanarEndpoint) :
    handbookPlanarBodyToWorldVelocity theta
        (handbookPlanarWorldToBodyVelocity theta vWorld) = vWorld := by
  simpa [handbookPlanarBodyToWorldVelocity, handbookPlanarWorldToBodyVelocity] using
    planarRotationMatrix_mulVec_neg_mulVec theta vWorld

/-- The two conversions are inverse in the body-to-world direction. -/
@[simp] theorem handbookPlanarWorldToBodyVelocity_bodyToWorldVelocity
    (theta : ℝ) (vBody : HandbookPlanarEndpoint) :
    handbookPlanarWorldToBodyVelocity theta
        (handbookPlanarBodyToWorldVelocity theta vBody) = vBody := by
  have h := planarRotationMatrix_mulVec_neg_mulVec (-theta) vBody
  simpa [handbookPlanarWorldToBodyVelocity, handbookPlanarBodyToWorldVelocity,
    neg_neg] using h

/-- Body-frame velocity obtained from the existing two-link world-frame
endpoint Jacobian.  The heading is the real, unwrapped `q 0 + q 1`. -/
noncomputable def handbookTwoLinkEndpointBodyVelocity
    (q qdot : HandbookPlanarConfiguration) : HandbookPlanarEndpoint :=
  handbookPlanarWorldToBodyVelocity (q 0 + q 1)
    (handbookTwoLinkJacobian q *ᵥ qdot)

/-- The concrete body-frame formula for the two-link endpoint velocity. -/
theorem handbookTwoLinkEndpointBodyVelocity_formula
    (q qdot : HandbookPlanarConfiguration) :
    handbookTwoLinkEndpointBodyVelocity q qdot =
      ![Real.cos (q 0 + q 1) * (handbookTwoLinkJacobian q *ᵥ qdot) 0 +
          Real.sin (q 0 + q 1) * (handbookTwoLinkJacobian q *ᵥ qdot) 1,
        -Real.sin (q 0 + q 1) * (handbookTwoLinkJacobian q *ᵥ qdot) 0 +
          Real.cos (q 0 + q 1) * (handbookTwoLinkJacobian q *ᵥ qdot) 1,
        (handbookTwoLinkJacobian q *ᵥ qdot) 2] := by
  simpa [handbookTwoLinkEndpointBodyVelocity] using
    handbookPlanarWorldToBodyVelocity_formula
      (q 0 + q 1) (handbookTwoLinkJacobian q *ᵥ qdot)

/-- The existing endpoint path derivative is a world-frame velocity witness;
the same witness can be converted to body axes by the actual `R(-theta)` map.
This does not differentiate a moving-frame position coordinate. -/
theorem hasDerivAt_handbookTwoLinkEndpoint_with_body_velocity
    {q : ℝ → HandbookPlanarConfiguration} {qdot : HandbookPlanarConfiguration} {t : ℝ}
    (hq : HasDerivAt q qdot t) :
    HasDerivAt (fun s => handbookTwoLinkEndpoint (q s))
      (handbookTwoLinkJacobian (q t) *ᵥ qdot) t ∧
    handbookTwoLinkEndpointBodyVelocity (q t) qdot =
      ![Real.cos ((q t) 0 + (q t) 1) *
          (handbookTwoLinkJacobian (q t) *ᵥ qdot) 0 +
          Real.sin ((q t) 0 + (q t) 1) *
            (handbookTwoLinkJacobian (q t) *ᵥ qdot) 1,
        -Real.sin ((q t) 0 + (q t) 1) *
            (handbookTwoLinkJacobian (q t) *ᵥ qdot) 0 +
          Real.cos ((q t) 0 + (q t) 1) *
            (handbookTwoLinkJacobian (q t) *ᵥ qdot) 1,
        (handbookTwoLinkJacobian (q t) *ᵥ qdot) 2] := by
  refine ⟨hasDerivAt_handbookTwoLinkEndpoint_path hq, ?_⟩
  exact handbookTwoLinkEndpointBodyVelocity_formula (q t) qdot

end Ctrllib
