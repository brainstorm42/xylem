/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.HandbookPlanarWrenchDuality

/-!
# Handbook planar shifted-reference-point adapter

This module is the bounded planar reduction of the spatial point-shift
convention in *Springer Handbook of Robotics*, 2nd ed., Ch. 3, Sect. 3.2:
Eqs. (3.2)--(3.5) use angular-first motion coordinates `(!, v_O)` and
moment-first force coordinates `(n_O, f)`; Eqs. (3.6)--(3.11) define the
motion transform, its force dual, and the position-vector convention.  For
`r = ^N p_Q`, the source transform from point `Q` coordinates to point `N`
coordinates gives

`v_N = v_Q + r × omega` and `n_N = n_Q + r × f`.

Solving these equations gives the translation-first/force-first planar
coordinates used by the preceding Handbook modules:

`v_Q = v_N + omega × r` and `m_Q = m_N - r × f`.

The adapter uses the same body, axes, and reference-point conventions on both
sides.  It proves the resulting same-body power identity, shifts a planar
Jacobian, and reconnects the result to the generic NullspaceMotion consumer.
The exact source convention is not silently generalized to 3-D, a DH chain,
contact mechanics, or a physical realization.

Source trace: local PDF book pp. 40--44, Ch. 3 Eqs. (3.1)--(3.16), especially
(3.5), (3.8)--(3.11), and Table 3.1; the chapter's reference 3.16 is R.
Featherstone, *Spatial v2* (2012), retained as a comparison/oracle source.
-/

open Matrix
open scoped BigOperators

namespace Ctrllib

/-- A planar offset `r = (r_x, r_y)` in the common frame of points `N` and `Q`. -/
abbrev HandbookPlanarOffset := Fin 2 → ℝ

/-- Translation-first velocity shift from point `N` to point `Q`.

The source's angular-first transform is reduced to
`v_Q = v_N + omega × r`, with velocity order `(v_x, v_y, omega)`. -/
noncomputable def handbookPlanarPointShiftVelocityMatrix
    (r : HandbookPlanarOffset) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, -r 1], ![0, 1, r 0], ![0, 0, 1]]

/-- Force-first wrench shift from point `N` to point `Q`.

The source's moment-first dual transform is reduced to
`m_Q = m_N - r × f`, with wrench order `(f_x, f_y, m_z)`. -/
noncomputable def handbookPlanarPointShiftWrenchMatrix
    (r : HandbookPlanarOffset) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, 0], ![0, 1, 0], ![r 1, -r 0, 1]]

/-- Shift a translation-first planar velocity from the reference point `N` to `Q`. -/
noncomputable def handbookPlanarPointShiftVelocity
    (r : HandbookPlanarOffset) (vN : HandbookPlanarEndpoint) :
    HandbookPlanarEndpoint :=
  handbookPlanarPointShiftVelocityMatrix r *ᵥ vN

/-- Shift a force-first planar wrench from the reference point `N` to `Q`. -/
noncomputable def handbookPlanarPointShiftWrench
    (r : HandbookPlanarOffset) (fN : HandbookPlanarForceFirstWrench) :
    HandbookPlanarForceFirstWrench :=
  handbookPlanarPointShiftWrenchMatrix r *ᵥ fN

/-- Explicit velocity formula for the source-supported point-shift convention. -/
theorem handbookPlanarPointShiftVelocity_formula
    (r : HandbookPlanarOffset) (vN : HandbookPlanarEndpoint) :
    handbookPlanarPointShiftVelocity r vN =
      ![vN 0 - r 1 * vN 2, vN 1 + r 0 * vN 2, vN 2] := by
  funext i
  fin_cases i <;>
    simp [handbookPlanarPointShiftVelocity, handbookPlanarPointShiftVelocityMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Explicit wrench formula for the dual point-shift convention. -/
theorem handbookPlanarPointShiftWrench_formula
    (r : HandbookPlanarOffset) (fN : HandbookPlanarForceFirstWrench) :
    handbookPlanarPointShiftWrench r fN =
      ![fN 0, fN 1, fN 2 + r 1 * fN 0 - r 0 * fN 1] := by
  funext i
  fin_cases i <;>
    simp [handbookPlanarPointShiftWrench, handbookPlanarPointShiftWrenchMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Shifting both factors preserves same-body planar power. -/
theorem handbookPlanarPointShift_power_preserved
    (r : HandbookPlanarOffset) (vN : HandbookPlanarEndpoint)
    (fN : HandbookPlanarForceFirstWrench) :
    handbookPlanarPointShiftVelocity r vN ⬝ᵥ
        handbookPlanarPointShiftWrench r fN =
      vN ⬝ᵥ fN := by
  rw [handbookPlanarPointShiftVelocity_formula,
    handbookPlanarPointShiftWrench_formula]
  norm_num [dotProduct, Fin.sum_univ_succ]
  ring

/-- The reverse offset undoes the velocity shift. -/
@[simp] theorem handbookPlanarPointShiftVelocity_neg
    (r : HandbookPlanarOffset) (vN : HandbookPlanarEndpoint) :
    handbookPlanarPointShiftVelocity (-r)
        (handbookPlanarPointShiftVelocity r vN) = vN := by
  rw [handbookPlanarPointShiftVelocity_formula,
    handbookPlanarPointShiftVelocity_formula]
  funext i
  fin_cases i <;> simp <;> ring

/-- The reverse offset undoes the wrench shift. -/
@[simp] theorem handbookPlanarPointShiftWrench_neg
    (r : HandbookPlanarOffset) (fN : HandbookPlanarForceFirstWrench) :
    handbookPlanarPointShiftWrench (-r)
        (handbookPlanarPointShiftWrench r fN) = fN := by
  rw [handbookPlanarPointShiftWrench_formula,
    handbookPlanarPointShiftWrench_formula]
  funext i
  fin_cases i <;> simp <;> ring

/-- Shift the rows of a planar Jacobian from point `N` to point `Q`. -/
noncomputable def handbookPlanarPointShiftJacobian
    (r : HandbookPlanarOffset) (JN : Matrix (Fin 3) (Fin 2) ℝ) :
    Matrix (Fin 3) (Fin 2) ℝ :=
  handbookPlanarPointShiftVelocityMatrix r * JN

/-- The shifted Jacobian maps joint rates to the shifted velocity. -/
theorem handbookPlanarPointShiftJacobian_mulVec
    (r : HandbookPlanarOffset) (JN : Matrix (Fin 3) (Fin 2) ℝ)
    (qdot : HandbookPlanarConfiguration) :
    handbookPlanarPointShiftJacobian r JN *ᵥ qdot =
      handbookPlanarPointShiftVelocity r (JN *ᵥ qdot) := by
  simp only [handbookPlanarPointShiftJacobian, handbookPlanarPointShiftVelocity]
  rw [Matrix.mulVec_mulVec]

/-- Virtual work at `Q` equals virtual work at `N` under the matched shift. -/
theorem handbookPlanarPointShiftJacobian_virtualWork_eq
    (r : HandbookPlanarOffset) (JN : Matrix (Fin 3) (Fin 2) ℝ)
    (qdot : HandbookPlanarConfiguration)
    (fN : HandbookPlanarForceFirstWrench) :
    qdot ⬝ᵥ
        ((handbookPlanarPointShiftJacobian r JN)ᵀ *ᵥ
          handbookPlanarPointShiftWrench r fN) =
      (JN *ᵥ qdot) ⬝ᵥ fN := by
  rw [Matrix.dotProduct_transpose_mulVec,
    handbookPlanarPointShiftJacobian_mulVec, dotProduct_comm]
  exact handbookPlanarPointShift_power_preserved r (JN *ᵥ qdot) fN

/-- A task-null velocity remains null after a same-body point shift, so the
existing transpose/virtual-work consumer cancels the shifted wrench. -/
theorem handbookPlanarPointShiftTaskWrench_dot_null_eq_zero
    (r : HandbookPlanarOffset) (JN : Matrix (Fin 3) (Fin 2) ℝ)
    (k : HandbookPlanarConfiguration)
    (fN : HandbookPlanarForceFirstWrench)
    (hk : JN *ᵥ k = 0) :
    k ⬝ᵥ
        ((handbookPlanarPointShiftJacobian r JN)ᵀ *ᵥ
          handbookPlanarPointShiftWrench r fN) = 0 := by
  apply taskWrench_dot_null_eq_zero
    (J := handbookPlanarPointShiftJacobian r JN)
  rw [handbookPlanarPointShiftJacobian_mulVec, hk]
  simp [handbookPlanarPointShiftVelocity]

/-- Exact arithmetic witness for the signs and component order.

With `r = (2,-1)`, `v_N = (3,4,5)`, and `f_N = (7,-2,11)`, the shifted
values are `v_Q = (8,14,5)` and `f_Q = (7,-2,8)`, and both power pairings
equal `68`. -/
theorem handbookPlanarPointShift_example :
    let r : HandbookPlanarOffset := ![2, -1]
    let vN : HandbookPlanarEndpoint := ![3, 4, 5]
    let fN : HandbookPlanarForceFirstWrench := ![7, -2, 11]
    handbookPlanarPointShiftVelocity r vN = ![8, 14, 5] ∧
      handbookPlanarPointShiftWrench r fN = ![7, -2, 8] ∧
      handbookPlanarPointShiftVelocity r vN ⬝ᵥ
          handbookPlanarPointShiftWrench r fN = 68 := by
  dsimp
  rw [handbookPlanarPointShiftVelocity_formula,
    handbookPlanarPointShiftWrench_formula]
  simp [dotProduct, Fin.sum_univ_succ]
  constructor
  · constructor <;> norm_num
  · constructor <;> norm_num

end Ctrllib
