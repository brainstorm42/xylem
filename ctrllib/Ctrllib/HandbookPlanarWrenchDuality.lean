/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.HandbookPlanarGeometricVelocity
import Ctrllib.NullspaceMotion

/-!
# Handbook planar wrench/velocity duality

This module supplies the same-point planar duality missing from the accepted
world/body velocity adapter.  A wrench is explicitly force-first,
`(f_x, f_y, m_z)`, so it is dual to the translation-first velocity
`(v_x, v_y, omega)` at the same endpoint reference point `N`.  Both world and
body quantities use the fixed/world and body axes from the velocity adapter;
the body translation and wrench are related by `R(-theta)`, while the scalar
moment/angular-rate component is retained.  The six-dimensional source
moment-first convention is not silently identified with this planar order.
No contact model, displaced-point transport, or physical realization is
introduced.
-/

open Matrix
open scoped BigOperators

namespace Ctrllib

/-- A planar force-first wrench `(f_x, f_y, m_z)` at endpoint `N`. -/
abbrev HandbookPlanarForceFirstWrench := Fin 3 → ℝ

/-- Express a same-point force-first wrench in body axes. -/
noncomputable def handbookPlanarWorldToBodyWrench
    (theta : ℝ) (fWorld : HandbookPlanarForceFirstWrench) :
    HandbookPlanarForceFirstWrench :=
  planarRotationMatrix (-theta) *ᵥ fWorld

/-- Express a same-point force-first wrench in the fixed/world frame. -/
noncomputable def handbookPlanarBodyToWorldWrench
    (theta : ℝ) (fBody : HandbookPlanarForceFirstWrench) :
    HandbookPlanarForceFirstWrench :=
  planarRotationMatrix theta *ᵥ fBody

/-- The planar wrench conversion has the same component formula as the
translation-first velocity conversion, with force and moment labels. -/
theorem handbookPlanarWorldToBodyWrench_formula
    (theta : ℝ) (fWorld : HandbookPlanarForceFirstWrench) :
    handbookPlanarWorldToBodyWrench theta fWorld =
      ![Real.cos theta * fWorld 0 + Real.sin theta * fWorld 1,
        -Real.sin theta * fWorld 0 + Real.cos theta * fWorld 1,
        fWorld 2] := by
  change handbookPlanarWorldToBodyVelocity theta fWorld = _
  exact handbookPlanarWorldToBodyVelocity_formula theta fWorld

/-- Rotation preserves the force-first planar power pairing at the same point. -/
theorem handbookPlanarWorldBodyPower_preserved
    (theta : ℝ) (vWorld : HandbookPlanarEndpoint)
    (fWorld : HandbookPlanarForceFirstWrench) :
    handbookPlanarWorldToBodyVelocity theta vWorld ⬝ᵥ
        handbookPlanarWorldToBodyWrench theta fWorld =
      vWorld ⬝ᵥ fWorld := by
  rw [handbookPlanarWorldToBodyVelocity_formula,
    handbookPlanarWorldToBodyWrench_formula]
  simp [dotProduct, Fin.sum_univ_succ]
  ring_nf
  linear_combination
    (vWorld 0 * fWorld 0 + vWorld 1 * fWorld 1) *
      Real.cos_sq_add_sin_sq theta

/-- The wrench conversion is inverse in the world-to-body direction. -/
@[simp] theorem handbookPlanarBodyToWorldWrench_worldToBodyWrench
    (theta : ℝ) (fWorld : HandbookPlanarForceFirstWrench) :
    handbookPlanarBodyToWorldWrench theta
        (handbookPlanarWorldToBodyWrench theta fWorld) = fWorld := by
  change handbookPlanarBodyToWorldVelocity theta
      (handbookPlanarWorldToBodyVelocity theta fWorld) = fWorld
  exact handbookPlanarBodyToWorldVelocity_worldToBodyVelocity theta fWorld

/-- The wrench conversion is inverse in the body-to-world direction. -/
@[simp] theorem handbookPlanarWorldToBodyWrench_bodyToWorldWrench
    (theta : ℝ) (fBody : HandbookPlanarForceFirstWrench) :
    handbookPlanarWorldToBodyWrench theta
        (handbookPlanarBodyToWorldWrench theta fBody) = fBody := by
  change handbookPlanarWorldToBodyVelocity theta
      (handbookPlanarBodyToWorldVelocity theta fBody) = fBody
  exact handbookPlanarWorldToBodyVelocity_bodyToWorldVelocity theta fBody

/-- Rotate the rows of a world-frame planar Jacobian into body axes. -/
noncomputable def handbookPlanarBodyJacobian
    (theta : ℝ) (JWorld : Matrix (Fin 3) (Fin 2) ℝ) :
    Matrix (Fin 3) (Fin 2) ℝ :=
  planarRotationMatrix (-theta) * JWorld

/-- The body Jacobian maps joint rates to the converted same-point velocity. -/
theorem handbookPlanarBodyJacobian_mulVec
    (theta : ℝ) (JWorld : Matrix (Fin 3) (Fin 2) ℝ)
    (qdot : HandbookPlanarConfiguration) :
    handbookPlanarBodyJacobian theta JWorld *ᵥ qdot =
      handbookPlanarWorldToBodyVelocity theta (JWorld *ᵥ qdot) := by
  simp only [handbookPlanarBodyJacobian, handbookPlanarWorldToBodyVelocity]
  rw [Matrix.mulVec_mulVec]

/-- Body-frame virtual work equals world-frame virtual work after the matched
force-first wrench conversion. -/
theorem handbookPlanarBodyJacobian_virtualWork_eq_world
    (theta : ℝ) (JWorld : Matrix (Fin 3) (Fin 2) ℝ)
    (qdot : HandbookPlanarConfiguration)
    (fWorld : HandbookPlanarForceFirstWrench) :
    qdot ⬝ᵥ
        ((handbookPlanarBodyJacobian theta JWorld)ᵀ *ᵥ
          handbookPlanarWorldToBodyWrench theta fWorld) =
      (JWorld *ᵥ qdot) ⬝ᵥ fWorld := by
  rw [Matrix.dotProduct_transpose_mulVec, handbookPlanarBodyJacobian_mulVec,
    dotProduct_comm]
  exact handbookPlanarWorldBodyPower_preserved theta (JWorld *ᵥ qdot) fWorld

/-- A world-frame task-null velocity remains null after row rotation, so the
existing transpose/virtual-work consumer cancels the matched body wrench. -/
theorem handbookPlanarBodyTaskWrench_dot_null_eq_zero
    (theta : ℝ) (JWorld : Matrix (Fin 3) (Fin 2) ℝ)
    (k : HandbookPlanarConfiguration)
    (fWorld : HandbookPlanarForceFirstWrench)
    (hk : JWorld *ᵥ k = 0) :
    k ⬝ᵥ
        ((handbookPlanarBodyJacobian theta JWorld)ᵀ *ᵥ
          handbookPlanarWorldToBodyWrench theta fWorld) = 0 := by
  apply taskWrench_dot_null_eq_zero (J := handbookPlanarBodyJacobian theta JWorld)
  rw [handbookPlanarBodyJacobian_mulVec, hk]
  simp [handbookPlanarWorldToBodyVelocity]

end Ctrllib
