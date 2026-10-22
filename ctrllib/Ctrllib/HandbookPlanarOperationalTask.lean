/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.HandbookPlanarTaskRank

/-!
# Handbook planar conditional operational task map

Chapter 10 of the local *Springer Handbook of Robotics*, 2nd ed., gives the
task-rate relation `t_dot = J_t(q) qdot` in Eq. (10.2), the inverse
differential-kinematics construction in §10.3.1, and the low-rectangular
full-rank formula `J_t^+ = J_tᵀ (J_t J_tᵀ)⁻¹` in Eq. (10.11).  The source says
that, under full task rank, the resulting joint velocity exactly realizes the
assigned task velocity.

This module instantiates that conditional interface for the already accepted
2-by-2 world-position task.  It names the existing weighted-right-inverse
command and composes it with the accepted path derivative theorem: if a path
has the commanded joint derivative, its task derivative equals the requested
two-coordinate target on the explicit domain `sin (q 1) ≠ 0`.  The matrix
`W` is an abstract SPD weight; this does not identify it with a physical mass
or inertia matrix, and no 6-D/12-D operational-space or dynamic realization is
claimed.

Source locators: local PDF p. 291 / book p. 224, Eq. (10.2); local PDF p. 293
/ book p. 226, full-rank feasible-velocity discussion; local PDF p. 294 /
book p. 227, §10.3.1 and Eqs. (10.10)--(10.13).  The task/rank input is the
accepted `HandbookPlanarTaskRank` adapter, which traces Ch. 10 §§10.2.1--10.2.2
and Eqs. (10.2), (10.4), (10.6), and (10.7).
-/

open Matrix

namespace Ctrllib

/-- The weighted kinematic joint command for a two-coordinate position target.
This is an algebraic command map, not a dynamics or actuator model. -/
noncomputable def handbookTwoLinkPositionWeightedCommand
    (W : Matrix (Fin 2) (Fin 2) ℝ)
    (q : HandbookPlanarConfiguration)
    (b : HandbookPlanarPositionTask) : HandbookPlanarConfiguration :=
  weightedRightInverse W (handbookTwoLinkPositionTaskJacobian q) *ᵥ b

/-- On the explicit full-rank domain, the weighted command realizes its task
velocity exactly. -/
theorem handbookTwoLinkPositionWeightedCommand_realizes
    {W : Matrix (Fin 2) (Fin 2) ℝ} (q : HandbookPlanarConfiguration)
    (hW : W.PosDef) (hsin : Real.sin (q 1) ≠ 0)
    (b : HandbookPlanarPositionTask) :
    handbookTwoLinkPositionTaskJacobian q *ᵥ
        handbookTwoLinkPositionWeightedCommand W q b = b := by
  simpa [handbookTwoLinkPositionWeightedCommand] using
    (handbookTwoLinkPositionTask_weighted_right_inverse_feasible q hW hsin b)

/-- Concrete operational-task bridge: a path whose joint derivative is the
weighted command has the requested task derivative.  The theorem is
conditional on the supplied path derivative and makes no physical existence,
stability, actuator, or mass/inertia claim. -/
theorem hasDerivAt_handbookTwoLinkPositionTask_weighted_command
    {W : Matrix (Fin 2) (Fin 2) ℝ}
    {q : ℝ → HandbookPlanarConfiguration}
    {b : HandbookPlanarPositionTask} {t : ℝ}
    (hW : W.PosDef) (hsin : Real.sin ((q t) 1) ≠ 0)
    (hq : HasDerivAt q
      (handbookTwoLinkPositionWeightedCommand W (q t) b) t) :
    HasDerivAt (fun s => handbookTwoLinkPositionTask (q s)) b t := by
  have htask := hasDerivAt_handbookTwoLinkPositionTask_path hq
  convert htask using 1
  exact (handbookTwoLinkPositionWeightedCommand_realizes (q t) hW hsin b).symm

end Ctrllib

#print axioms Ctrllib.handbookTwoLinkPositionWeightedCommand_realizes
#print axioms Ctrllib.hasDerivAt_handbookTwoLinkPositionTask_weighted_command
