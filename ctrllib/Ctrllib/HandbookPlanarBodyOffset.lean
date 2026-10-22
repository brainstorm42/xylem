/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.HandbookPlanarReferencePointShift

/-!
# Handbook planar body-attached offset bridge

The local *Springer Handbook of Robotics*, 2nd ed., Ch. 3, Sect. 3.2,
Eq. (3.22) distinguishes a body-fixed point from a fixed spatial point.  In
the planar reduction used here, a constant body-coordinate offset `rB` is
rotated into world coordinates by the body's unwrapped heading
`theta = q 0 + q 1`.  The resulting point is

`p_Q(q) = p_N(q) + R(theta) rB`.

This module proves the corresponding two-link path derivative and identifies
its Jacobian with the accepted same-body point-shift adapter.  The offset is
constant in body coordinates, not in world coordinates; this is distinct from
differentiating a moving-frame position coordinate.  The result remains a
planar algebraic/analytic interface: no general 3-D, D--H, contact, or
physical-realization claim is made.

Source locators: Ch. 3 book p. 42 / local PDF p. 112, Eqs. (3.17)--(3.22);
Ch. 2 book p. 21 / local PDF p. 92, Eqs. (2.36)--(2.40).  The source's
angular-first spatial convention is reduced here to the existing
translation-first planar endpoint order `(v_x, v_y, omega)`.
-/

open Matrix
open scoped BigOperators

namespace Ctrllib

/-- A constant body-coordinate offset expressed in the fixed/world axes. -/
noncomputable def handbookPlanarBodyOffsetWorld
    (theta : ℝ) (rB : HandbookPlanarOffset) : HandbookPlanarOffset :=
  ![Real.cos theta * rB 0 - Real.sin theta * rB 1,
    Real.sin theta * rB 0 + Real.cos theta * rB 1]

/-- The preceding definition is the planar part of `R(theta) rB`. -/
theorem handbookPlanarBodyOffsetWorld_matrix
    (theta : ℝ) (rB : HandbookPlanarOffset) :
    handbookPlanarBodyOffsetWorld theta rB =
      ![(planarRotationMatrix theta *ᵥ ![rB 0, rB 1, 0]) 0,
        (planarRotationMatrix theta *ᵥ ![rB 0, rB 1, 0]) 1] := by
  funext i
  fin_cases i <;>
    simp [handbookPlanarBodyOffsetWorld, planarRotationMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

/-- World position of a point fixed at body offset `rB`. -/
noncomputable def handbookTwoLinkBodyOffsetPosition
    (rB : HandbookPlanarOffset) (q : HandbookPlanarConfiguration) : Fin 3 → ℝ :=
  handbookTwoLinkPosition q +
    ![handbookPlanarBodyOffsetWorld (q 0 + q 1) rB 0,
      handbookPlanarBodyOffsetWorld (q 0 + q 1) rB 1, 0]

/-- The point map `p_Q = p_N + R(theta) rB` in the source convention. -/
noncomputable def handbookTwoLinkBodyOffsetEndpoint
    (rB : HandbookPlanarOffset) (q : HandbookPlanarConfiguration) :
    HandbookPlanarEndpoint :=
  ![Real.cos (q 0) + (1 + rB 0) * Real.cos (q 0 + q 1) -
        rB 1 * Real.sin (q 0 + q 1),
    Real.sin (q 0) + (1 + rB 0) * Real.sin (q 0 + q 1) +
        rB 1 * Real.cos (q 0 + q 1),
    q 0 + q 1]

/-- The explicit endpoint map agrees with the position-plus-rotated-offset map. -/
theorem handbookTwoLinkBodyOffsetEndpoint_position_relation
    (rB : HandbookPlanarOffset) (q : HandbookPlanarConfiguration) :
    handbookTwoLinkBodyOffsetEndpoint rB q =
      ![(handbookTwoLinkBodyOffsetPosition rB q) 0,
        (handbookTwoLinkBodyOffsetPosition rB q) 1, q 0 + q 1] := by
  funext i
  fin_cases i
  · simp [handbookTwoLinkBodyOffsetEndpoint, handbookTwoLinkBodyOffsetPosition,
      handbookPlanarBodyOffsetWorld, handbookTwoLinkPosition_coord0]
    ring
  · simp [handbookTwoLinkBodyOffsetEndpoint, handbookTwoLinkBodyOffsetPosition,
      handbookPlanarBodyOffsetWorld, handbookTwoLinkPosition_coord1]
    ring
  · simp [handbookTwoLinkBodyOffsetEndpoint]

/-- Jacobian of the body-attached offset endpoint in joint coordinates. -/
noncomputable def handbookTwoLinkBodyOffsetJacobian
    (rB : HandbookPlanarOffset) (q : HandbookPlanarConfiguration) :
    Matrix (Fin 3) (Fin 2) ℝ :=
  !![-Real.sin (q 0) - (1 + rB 0) * Real.sin (q 0 + q 1) -
        rB 1 * Real.cos (q 0 + q 1),
      -(1 + rB 0) * Real.sin (q 0 + q 1) - rB 1 * Real.cos (q 0 + q 1);
    Real.cos (q 0) + (1 + rB 0) * Real.cos (q 0 + q 1) -
        rB 1 * Real.sin (q 0 + q 1),
      (1 + rB 0) * Real.cos (q 0 + q 1) - rB 1 * Real.sin (q 0 + q 1);
    1, 1]

/-- The body-offset Jacobian is the accepted point-shift Jacobian at the
current world offset. -/
theorem handbookTwoLinkBodyOffsetJacobian_eq_shifted
    (rB : HandbookPlanarOffset) (q : HandbookPlanarConfiguration) :
    handbookTwoLinkBodyOffsetJacobian rB q =
      handbookPlanarPointShiftJacobian
        (handbookPlanarBodyOffsetWorld (q 0 + q 1) rB)
        (handbookTwoLinkJacobian q) := by
  change handbookTwoLinkBodyOffsetJacobian rB q =
    handbookPlanarPointShiftVelocityMatrix
      (handbookPlanarBodyOffsetWorld (q 0 + q 1) rB) *
      handbookTwoLinkJacobian q
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply] <;>
    simp [handbookTwoLinkBodyOffsetJacobian,
      handbookPlanarPointShiftVelocityMatrix, handbookPlanarBodyOffsetWorld,
      handbookTwoLinkJacobian, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Path derivative of the body-attached offset endpoint, expressed through
the shifted Jacobian at the instantaneous world offset. -/
theorem hasDerivAt_handbookTwoLinkBodyOffsetEndpoint_path
    {rB : HandbookPlanarOffset} {q : ℝ → HandbookPlanarConfiguration}
    {qdot : HandbookPlanarConfiguration} {t : ℝ}
    (hq : HasDerivAt q qdot t) :
    HasDerivAt (fun s => handbookTwoLinkBodyOffsetEndpoint rB (q s))
      (handbookPlanarPointShiftJacobian
        (handbookPlanarBodyOffsetWorld ((q t) 0 + (q t) 1) rB)
        (handbookTwoLinkJacobian (q t)) *ᵥ qdot) t := by
  have hq0 : HasDerivAt (fun s => (q s) 0) (qdot 0) t := by
    change HasDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) ∘ q)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) qdot) t
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t hq
  have hq1 : HasDerivAt (fun s => (q s) 1) (qdot 1) t := by
    change HasDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) ∘ q)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) qdot) t
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt.comp_hasDerivAt t hq
  have htheta : HasDerivAt (fun s => (q s) 0 + (q s) 1)
      (qdot 0 + qdot 1) t := hq0.add hq1
  have hcos0 : HasDerivAt (fun s => Real.cos ((q s) 0))
      (-Real.sin ((q t) 0) * qdot 0) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cos ((q t) 0)).comp t hq0
  have hsin0 : HasDerivAt (fun s => Real.sin ((q s) 0))
      (Real.cos ((q t) 0) * qdot 0) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sin ((q t) 0)).comp t hq0
  have hcostheta : HasDerivAt
      (fun s => Real.cos ((q s) 0 + (q s) 1))
      (-Real.sin ((q t) 0 + (q t) 1) * (qdot 0 + qdot 1)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cos ((q t) 0 + (q t) 1)).comp t htheta
  have hsintheta : HasDerivAt
      (fun s => Real.sin ((q s) 0 + (q s) 1))
      (Real.cos ((q t) 0 + (q t) 1) * (qdot 0 + qdot 1)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sin ((q t) 0 + (q t) 1)).comp t htheta
  have hx : HasDerivAt
      (fun s => Real.cos ((q s) 0) +
        (1 + rB 0) * Real.cos ((q s) 0 + (q s) 1) -
        rB 1 * Real.sin ((q s) 0 + (q s) 1))
      ((-Real.sin ((q t) 0) * qdot 0) +
        (1 + rB 0) * (-Real.sin ((q t) 0 + (q t) 1) *
          (qdot 0 + qdot 1)) -
        rB 1 * (Real.cos ((q t) 0 + (q t) 1) *
          (qdot 0 + qdot 1))) t := by
    convert ((hcos0.add (hcostheta.const_mul (1 + rB 0))).sub
      (hsintheta.const_mul (rB 1))) using 1
  have hy : HasDerivAt
      (fun s => Real.sin ((q s) 0) +
        (1 + rB 0) * Real.sin ((q s) 0 + (q s) 1) +
        rB 1 * Real.cos ((q s) 0 + (q s) 1))
      ((Real.cos ((q t) 0) * qdot 0) +
        (1 + rB 0) * (Real.cos ((q t) 0 + (q t) 1) *
          (qdot 0 + qdot 1)) +
        rB 1 * (-Real.sin ((q t) 0 + (q t) 1) *
          (qdot 0 + qdot 1))) t := by
    convert ((hsin0.add (hsintheta.const_mul (1 + rB 0))).add
      (hcostheta.const_mul (rB 1))) using 1
  have hendpoint : HasDerivAt
      (fun s => handbookTwoLinkBodyOffsetEndpoint rB (q s))
      ![(-Real.sin ((q t) 0) * qdot 0) +
          (1 + rB 0) * (-Real.sin ((q t) 0 + (q t) 1) *
            (qdot 0 + qdot 1)) -
          rB 1 * (Real.cos ((q t) 0 + (q t) 1) *
            (qdot 0 + qdot 1)),
        (Real.cos ((q t) 0) * qdot 0) +
          (1 + rB 0) * (Real.cos ((q t) 0 + (q t) 1) *
            (qdot 0 + qdot 1)) +
          rB 1 * (-Real.sin ((q t) 0 + (q t) 1) *
            (qdot 0 + qdot 1)),
        qdot 0 + qdot 1] t := by
    change HasDerivAt (fun s =>
      ![Real.cos ((q s) 0) + (1 + rB 0) * Real.cos ((q s) 0 + (q s) 1) -
          rB 1 * Real.sin ((q s) 0 + (q s) 1),
        Real.sin ((q s) 0) + (1 + rB 0) * Real.sin ((q s) 0 + (q s) 1) +
          rB 1 * Real.cos ((q s) 0 + (q s) 1),
        (q s) 0 + (q s) 1]) _ t
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact htheta
  rw [← handbookTwoLinkBodyOffsetJacobian_eq_shifted]
  convert hendpoint using 1
  funext i
  fin_cases i <;> simp [handbookTwoLinkBodyOffsetJacobian, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ] <;> ring

end Ctrllib
