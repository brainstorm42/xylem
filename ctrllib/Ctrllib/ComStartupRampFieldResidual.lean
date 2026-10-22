/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonia Hoffman
-/
import Ctrllib.ComStartupRampComposition

/-!
# Command-residual to point-mass vector-field residual

The startup-ramped closed-loop field and the nominal point-mass field use the
velocity-first state order `(v, x)`.  This module adapts their same-state
force residual to the exact field residual: the force residual is multiplied
by `m⁻¹` in the acceleration component and the position component is zero.

The algebraic identity is separated from the physical hypotheses `m > 0`,
`τ > 0`, and `t ≥ 0`.  The latter are used only for norm equalities and
bounds.  No trajectory, ODE, stability, convergence, or generic forcing
interface identification is asserted here.
-/

namespace Ctrllib.ComStartupRampFieldResidual

open Ctrllib.ComControllerPlantComposition
open Ctrllib.ComStartupRampComposition

/-- Convert a point-mass force residual into its acceleration/position field residual. -/
noncomputable def forceResidualToFieldResidual (m : ℝ) (δf : PointMassCoord) : PointMassState :=
  (m⁻¹ • δf, 0)

/-- Exact velocity-first field residual induced by a same-state force residual. -/
theorem rampedField_residual_eq_forceResidual
    (m τ d k : ℝ) (tz : TimedState) :
    rampedPointMassField m τ d k tz - pointMassField m d k tz.2 =
      forceResidualToFieldResidual m
        (rampedForce τ d k tz - controllerForce d k tz.2) := by
  rw [← closedLoop_eq_rampedPointMassField,
    ← ComControllerPlantComposition.closedLoop_eq_pointMassField]
  simp only [plantDerivative, stateForceWire, forceResidualToFieldResidual]
  apply Prod.ext
  · simp [smul_sub]
  · simp

/-- The field-residual norm is the inverse-mass-scaled force-residual norm. -/
theorem norm_rampedPointMassField_sub_pointMassField_eq
    (m τ d k : ℝ) (tz : TimedState) (hm : 0 < m) :
    ‖rampedPointMassField m τ d k tz - pointMassField m d k tz.2‖ =
      m⁻¹ * ‖rampedForce τ d k tz - controllerForce d k tz.2‖ := by
  rw [rampedField_residual_eq_forceResidual]
  simp only [forceResidualToFieldResidual, Prod.norm_def, norm_zero]
  rw [max_eq_left (norm_nonneg _), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hm)]

/-- Exact acceleration-residual suppression inherited from the force residual. -/
theorem rampedPointMassField_residual_norm_eq
    (m τ d k : ℝ) (tz : TimedState) (hm : 0 < m) :
    ‖rampedPointMassField m τ d k tz - pointMassField m d k tz.2‖ =
      m⁻¹ * (Real.exp (-tz.1 / τ) * ‖controllerForce d k tz.2‖) := by
  calc
    ‖rampedPointMassField m τ d k tz - pointMassField m d k tz.2‖ =
        m⁻¹ * ‖rampedForce τ d k tz - controllerForce d k tz.2‖ :=
      norm_rampedPointMassField_sub_pointMassField_eq m τ d k tz hm
    _ = m⁻¹ * (Real.exp (-tz.1 / τ) * ‖controllerForce d k tz.2‖) := by
      rw [force_difference_norm]

/-- Physical startup hypotheses turn the exact residual into a nominal-force bound. -/
theorem rampedPointMassField_residual_norm_le_nominal
    (m τ d k : ℝ) (tz : TimedState) (hm : 0 < m) (hτ : 0 < τ)
    (ht : 0 ≤ tz.1) :
    ‖rampedPointMassField m τ d k tz - pointMassField m d k tz.2‖ ≤
      m⁻¹ * ‖controllerForce d k tz.2‖ := by
  rw [rampedPointMassField_residual_norm_eq m τ d k tz hm]
  have hexp : Real.exp (-tz.1 / τ) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hτ.le)
  calc
    m⁻¹ * (Real.exp (-tz.1 / τ) * ‖controllerForce d k tz.2‖) ≤
        m⁻¹ * (1 * ‖controllerForce d k tz.2‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) (inv_nonneg.mpr hm.le)
    _ = m⁻¹ * ‖controllerForce d k tz.2‖ := by ring

/-- At `t = 0`, the ramped field residual has the full nominal acceleration size. -/
theorem rampedPointMassField_residual_norm_at_zero
    (m τ d k : ℝ) (z : PointMassState) (hm : 0 < m) :
    ‖rampedPointMassField m τ d k (0, z) - pointMassField m d k z‖ =
      m⁻¹ * ‖controllerForce d k z‖ := by
  simpa using
    rampedPointMassField_residual_norm_eq m τ d k (0, z) hm

/-- A zero nominal force produces a zero field residual at the same state. -/
theorem rampedField_residual_eq_zero_of_nominalForce_eq_zero
    (m τ d k : ℝ) (tz : TimedState)
    (hzero : controllerForce d k tz.2 = 0) :
    rampedPointMassField m τ d k tz - pointMassField m d k tz.2 = 0 := by
  rw [rampedField_residual_eq_forceResidual]
  simp [forceResidualToFieldResidual, rampedForce, hzero]

end Ctrllib.ComStartupRampFieldResidual

#print axioms Ctrllib.ComStartupRampFieldResidual.forceResidualToFieldResidual
#print axioms
  Ctrllib.ComStartupRampFieldResidual.rampedField_residual_eq_forceResidual
#print axioms Ctrllib.ComStartupRampFieldResidual.norm_rampedPointMassField_sub_pointMassField_eq
#print axioms Ctrllib.ComStartupRampFieldResidual.rampedPointMassField_residual_norm_eq
#print axioms Ctrllib.ComStartupRampFieldResidual.rampedPointMassField_residual_norm_le_nominal
#print axioms Ctrllib.ComStartupRampFieldResidual.rampedPointMassField_residual_norm_at_zero
#print axioms
  Ctrllib.ComStartupRampFieldResidual.rampedField_residual_eq_zero_of_nominalForce_eq_zero
