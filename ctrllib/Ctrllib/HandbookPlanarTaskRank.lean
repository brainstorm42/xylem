/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.HandbookPlanarTwoLink
import Ctrllib.WeightedRightInverse

/-!
# Handbook planar task/rank adapter

The local *Springer Handbook of Robotics*, 2nd ed., Ch. 10, §10.2.1--§10.2.2
defines the task map and its analytic Jacobian in Eq. (10.2), relates task and
geometric velocities in Eq. (10.4), gives the geometric Jacobian velocity map
in Eq. (10.6), and states `J_t(q) = T(t) J(q)` in Eq. (10.7).  The adjacent
singularity discussion (local PDF pp. 292--293 / book pp. 225--226) identifies
full task rank with a full feasible-velocity range and identifies rank loss
with unfeasible task velocities.

This module chooses the concrete two-dimensional world-position task given by
the first two rows of the accepted unit-link two-link endpoint Jacobian.  Its
determinant is exactly `sin (q 1)`, so the task is surjective precisely on the
domain `sin (q 1) ≠ 0`.  The existing weighted right-inverse consumer is then
reused with its required SPD weight and surjectivity premises.  This is a
2-by-2 position task, not the full 3-by-2 `(x,y,theta)` pose map (which cannot
be surjective onto a three-coordinate task), and it is not a general chart or
physical-singularity theorem.

Source locators: local PDF p. 291 / book p. 224, Eqs. (10.2), (10.4), and
(10.6); local PDF p. 292 / book p. 225, Eq. (10.7) and the representation /
kinematic singularity distinction; local PDF p. 293 / book p. 226, the full-rank
range/null-space discussion.  No textbook prose, figures, or source code are
copied here.
-/

open Matrix
open scoped BigOperators

namespace Ctrllib

/-- The world-frame `(x,y)` position task extracted from the endpoint map. -/
abbrev HandbookPlanarPositionTask := Fin 2 → ℝ

noncomputable def handbookTwoLinkPositionTask
    (q : HandbookPlanarConfiguration) : HandbookPlanarPositionTask :=
  ![(handbookTwoLinkEndpoint q) 0, (handbookTwoLinkEndpoint q) 1]

/-- The 2-by-2 analytic position-task Jacobian, using the accepted endpoint
Jacobian's first two world-position rows. -/
noncomputable def handbookTwoLinkPositionTaskJacobian
    (q : HandbookPlanarConfiguration) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-Real.sin (q 0) - Real.sin (q 0 + q 1), -Real.sin (q 0 + q 1);
      Real.cos (q 0) + Real.cos (q 0 + q 1), Real.cos (q 0 + q 1)]

/-- The selected task really is the first two rows of the accepted endpoint
Jacobian; no new kinematics is introduced by this adapter. -/
theorem handbookTwoLinkPositionTaskJacobian_eq_endpoint_rows
    (q : HandbookPlanarConfiguration) :
    handbookTwoLinkPositionTaskJacobian q =
      !![(handbookTwoLinkJacobian q) 0 0, (handbookTwoLinkJacobian q) 0 1;
         (handbookTwoLinkJacobian q) 1 0, (handbookTwoLinkJacobian q) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [handbookTwoLinkPositionTaskJacobian, handbookTwoLinkJacobian]

/-- The accepted endpoint path derivative projects to the selected position
task and its 2-by-2 Jacobian. -/
theorem hasDerivAt_handbookTwoLinkPositionTask_path
    {q : ℝ → HandbookPlanarConfiguration} {qdot : HandbookPlanarConfiguration}
    {t : ℝ} (hq : HasDerivAt q qdot t) :
    HasDerivAt (fun s => handbookTwoLinkPositionTask (q s))
      (handbookTwoLinkPositionTaskJacobian (q t) *ᵥ qdot) t := by
  have hendpoint := hasDerivAt_handbookTwoLinkEndpoint_path hq
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · have h0 :=
      (hasDerivAt_const t
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0)).clm_apply
        hendpoint
    simpa [handbookTwoLinkPositionTask, handbookTwoLinkPositionTaskJacobian,
      handbookTwoLinkEndpoint, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      handbookTwoLinkJacobian] using h0
  · have h1 :=
      (hasDerivAt_const t
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1)).clm_apply
        hendpoint
    simpa [handbookTwoLinkPositionTask, handbookTwoLinkPositionTaskJacobian,
      handbookTwoLinkEndpoint, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      handbookTwoLinkJacobian] using h1

/-- The exact determinant of the selected world-position task Jacobian. -/
theorem handbookTwoLinkPositionTaskJacobian_det
    (q : HandbookPlanarConfiguration) :
    Matrix.det (handbookTwoLinkPositionTaskJacobian q) = Real.sin (q 1) := by
  change Matrix.det
      !![-Real.sin (q 0) - Real.sin (q 0 + q 1), -Real.sin (q 0 + q 1);
          Real.cos (q 0) + Real.cos (q 0 + q 1), Real.cos (q 0 + q 1)] =
    Real.sin (q 1)
  rw [Matrix.det_fin_two_of]
  simp [handbookTwoLinkPositionTaskJacobian]
  rw [Real.sin_add, Real.cos_add]
  linear_combination Real.sin_sq_add_cos_sq (q 0) * Real.sin (q 1)

/-- Full row rank/surjectivity is exactly the non-singular joint-domain
condition for the selected 2-by-2 position task. -/
theorem handbookTwoLinkPositionTaskJacobian_surjective_iff
    (q : HandbookPlanarConfiguration) :
    Function.Surjective (handbookTwoLinkPositionTaskJacobian q).mulVec ↔
      Real.sin (q 1) ≠ 0 := by
  constructor
  · intro hsurj
    have hunit : IsUnit (handbookTwoLinkPositionTaskJacobian q) :=
      Matrix.mulVec_surjective_iff_isUnit.mp hsurj
    have hdet : (handbookTwoLinkPositionTaskJacobian q).det ≠ 0 :=
      isUnit_iff_ne_zero.mp
        ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
    rwa [handbookTwoLinkPositionTaskJacobian_det] at hdet
  · intro hsin
    apply Matrix.mulVec_surjective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [handbookTwoLinkPositionTaskJacobian_det]
    exact hsin

/-- At `sin(q 1) = 0`, the selected position task is singular and cannot
serve as an exact two-coordinate velocity task. -/
theorem handbookTwoLinkPositionTaskJacobian_not_surjective_of_sin_eq_zero
    (q : HandbookPlanarConfiguration) (hsin : Real.sin (q 1) = 0) :
    ¬ Function.Surjective (handbookTwoLinkPositionTaskJacobian q).mulVec := by
  intro hsurj
  exact ((handbookTwoLinkPositionTaskJacobian_surjective_iff q).mp hsurj) hsin

/-- The existing weighted-right-inverse algebra consumes the selected task
on the exact domain, with the SPD weight premise kept explicit. -/
theorem handbookTwoLinkPositionTask_weighted_right_inverse_mul
    {W : Matrix (Fin 2) (Fin 2) ℝ} (q : HandbookPlanarConfiguration)
    (hW : W.PosDef) (hsin : Real.sin (q 1) ≠ 0) :
    handbookTwoLinkPositionTaskJacobian q *
        weightedRightInverse W (handbookTwoLinkPositionTaskJacobian q) = 1 := by
  exact weighted_right_inverse_mul hW
    ((handbookTwoLinkPositionTaskJacobian_surjective_iff q).mpr hsin)

/-- Every two-coordinate target is feasible through the existing weighted
right-inverse consumer on the same rank domain. -/
theorem handbookTwoLinkPositionTask_weighted_right_inverse_feasible
    {W : Matrix (Fin 2) (Fin 2) ℝ} (q : HandbookPlanarConfiguration)
    (hW : W.PosDef) (hsin : Real.sin (q 1) ≠ 0)
    (b : HandbookPlanarPositionTask) :
    handbookTwoLinkPositionTaskJacobian q *ᵥ
        (weightedRightInverse W (handbookTwoLinkPositionTaskJacobian q) *ᵥ b) = b := by
  exact weighted_right_inverse_feasible hW
    ((handbookTwoLinkPositionTaskJacobian_surjective_iff q).mpr hsin) b

end Ctrllib

#print axioms Ctrllib.handbookTwoLinkPositionTaskJacobian_det
#print axioms Ctrllib.handbookTwoLinkPositionTaskJacobian_surjective_iff
#print axioms Ctrllib.handbookTwoLinkPositionTask_weighted_right_inverse_feasible
