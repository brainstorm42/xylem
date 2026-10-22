/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.HandbookPlanarEndpointJacobian
import Ctrllib.RoverPlanarRotation

/-!
# Handbook two-link endpoint/Jacobian correspondence

This module gives a source-level two-link planar endpoint map, its geometric
endpoint Jacobian, and the corresponding path derivative.  The source
alignment is Springer Handbook of Robotics, second edition (2016), Part A,
Chapter 2, Sections 2.4 and 2.6 (local PDF pp. 97--99; book pp. 26--28).
Only the mathematical interface is encoded here: no textbook prose, figures,
or external code are copied, and no physical-realization claim is made.
-/

open Matrix
open scoped BigOperators

namespace Ctrllib

def handbookTwoLinkLinkOffset : Fin 3 → ℝ := ![1, 0, 0]

noncomputable def handbookTwoLinkPosition
    (q : HandbookPlanarConfiguration) : Fin 3 → ℝ :=
  planarRotationMatrix (q 0) *ᵥ
    (handbookTwoLinkLinkOffset + planarRotationMatrix (q 1) *ᵥ handbookTwoLinkLinkOffset)

noncomputable def handbookTwoLinkEndpoint
    (q : HandbookPlanarConfiguration) : HandbookPlanarEndpoint :=
  ![(handbookTwoLinkPosition q) 0,
    (handbookTwoLinkPosition q) 1,
    q 0 + q 1]

theorem handbookTwoLinkPosition_coord0 (q : HandbookPlanarConfiguration) :
    (handbookTwoLinkPosition q) 0 =
      Real.cos (q 0) + Real.cos (q 0 + q 1) := by
  simp [handbookTwoLinkPosition, handbookTwoLinkLinkOffset, planarRotationMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [Real.cos_add]
  ring

theorem handbookTwoLinkPosition_coord1 (q : HandbookPlanarConfiguration) :
    (handbookTwoLinkPosition q) 1 =
      Real.sin (q 0) + Real.sin (q 0 + q 1) := by
  simp [handbookTwoLinkPosition, handbookTwoLinkLinkOffset, planarRotationMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [Real.sin_add]
  ring

noncomputable def handbookTwoLinkComposeDerivative
    (a : ℝ) (L : HandbookPlanarConfiguration →L[ℝ] ℝ) :
    HandbookPlanarConfiguration →L[ℝ] ℝ :=
  a • L

noncomputable def handbookTwoLinkEndpointDerivative
    (q : HandbookPlanarConfiguration) :
    HandbookPlanarConfiguration →L[ℝ] HandbookPlanarEndpoint :=
  let p0 : HandbookPlanarConfiguration →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let p1 : HandbookPlanarConfiguration →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  let ps := p0 + p1
  ContinuousLinearMap.pi ![
    handbookTwoLinkComposeDerivative (-Real.sin (q 0)) p0 +
      handbookTwoLinkComposeDerivative (-Real.sin (q 0 + q 1)) ps,
    handbookTwoLinkComposeDerivative (Real.cos (q 0)) p0 +
      handbookTwoLinkComposeDerivative (Real.cos (q 0 + q 1)) ps,
    ps]

noncomputable def handbookTwoLinkJacobian
    (q : HandbookPlanarConfiguration) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![-Real.sin (q 0) - Real.sin (q 0 + q 1), -Real.sin (q 0 + q 1);
      Real.cos (q 0) + Real.cos (q 0 + q 1), Real.cos (q 0 + q 1);
      1, 1]

theorem hasFDerivAt_handbookTwoLinkEndpoint
    (q : HandbookPlanarConfiguration) :
    HasFDerivAt handbookTwoLinkEndpoint (handbookTwoLinkEndpointDerivative q) q := by
  have hq0 : HasFDerivAt (fun x : HandbookPlanarConfiguration => x 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) q :=
    hasFDerivAt_apply 0 q
  have hq1 : HasFDerivAt (fun x : HandbookPlanarConfiguration => x 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) q :=
    hasFDerivAt_apply 1 q
  have hsum : HasFDerivAt (fun x : HandbookPlanarConfiguration => x 0 + x 1)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) +
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)) q := hq0.add hq1
  have hcos0 : HasFDerivAt (fun x : HandbookPlanarConfiguration => Real.cos (x 0))
      (handbookTwoLinkComposeDerivative (-Real.sin (q 0)) (ContinuousLinearMap.proj 0)) q := by
    simpa [handbookTwoLinkComposeDerivative, Function.comp_def, ← neg_smul] using
      (Real.hasDerivAt_cos (q 0)).comp_hasFDerivAt q hq0
  have hcosSum : HasFDerivAt
      (fun x : HandbookPlanarConfiguration => Real.cos (x 0 + x 1))
      (handbookTwoLinkComposeDerivative (-Real.sin (q 0 + q 1))
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) +
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1))) q := by
    simpa [handbookTwoLinkComposeDerivative, Function.comp_def, ← neg_smul] using
      (Real.hasDerivAt_cos (q 0 + q 1)).comp_hasFDerivAt q hsum
  have hsin0 : HasFDerivAt (fun x : HandbookPlanarConfiguration => Real.sin (x 0))
      (handbookTwoLinkComposeDerivative (Real.cos (q 0)) (ContinuousLinearMap.proj 0)) q := by
    simpa [handbookTwoLinkComposeDerivative, Function.comp_def] using
      (Real.hasDerivAt_sin (q 0)).comp_hasFDerivAt q hq0
  have hsinSum : HasFDerivAt
      (fun x : HandbookPlanarConfiguration => Real.sin (x 0 + x 1))
      (handbookTwoLinkComposeDerivative (Real.cos (q 0 + q 1))
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) +
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1))) q := by
    simpa [handbookTwoLinkComposeDerivative, Function.comp_def] using
      (Real.hasDerivAt_sin (q 0 + q 1)).comp_hasFDerivAt q hsum
  have hpx := hcos0.add hcosSum
  have hpy := hsin0.add hsinSum
  have hpx' : HasFDerivAt (fun x : HandbookPlanarConfiguration =>
      (handbookTwoLinkPosition x) 0)
      (handbookTwoLinkComposeDerivative (-Real.sin (q 0)) (ContinuousLinearMap.proj 0) +
        handbookTwoLinkComposeDerivative (-Real.sin (q 0 + q 1))
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) +
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1))) q := by
    convert hpx using 1
    funext x
    simp only [handbookTwoLinkPosition_coord0, Pi.add_apply]
  have hpy' : HasFDerivAt (fun x : HandbookPlanarConfiguration =>
      (handbookTwoLinkPosition x) 1)
      (handbookTwoLinkComposeDerivative (Real.cos (q 0)) (ContinuousLinearMap.proj 0) +
        handbookTwoLinkComposeDerivative (Real.cos (q 0 + q 1))
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) +
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1))) q := by
    convert hpy using 1
    funext x
    simp only [handbookTwoLinkPosition_coord1, Pi.add_apply]
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [handbookTwoLinkEndpoint, handbookTwoLinkEndpointDerivative] using hpx'
  · simpa [handbookTwoLinkEndpoint, handbookTwoLinkEndpointDerivative] using hpy'
  · simpa [handbookTwoLinkEndpoint, handbookTwoLinkEndpointDerivative] using hsum

theorem handbookTwoLinkEndpointDerivative_matrix (q : HandbookPlanarConfiguration) :
    handbookPlanarJacobianMatrix (handbookTwoLinkEndpointDerivative q) =
      handbookTwoLinkJacobian q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [handbookPlanarJacobianMatrix, handbookTwoLinkEndpointDerivative,
      handbookTwoLinkComposeDerivative, handbookTwoLinkJacobian,
      LinearMap.toMatrix'_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, Pi.single_apply] <;> ring

theorem hasDerivAt_handbookTwoLinkEndpoint_path
    {q : ℝ → HandbookPlanarConfiguration} {qdot : HandbookPlanarConfiguration} {t : ℝ}
    (hq : HasDerivAt q qdot t) :
    HasDerivAt (fun s => handbookTwoLinkEndpoint (q s))
      (handbookTwoLinkJacobian (q t) *ᵥ qdot) t := by
  have hmap := hasFDerivAt_handbookTwoLinkEndpoint (q t)
  have hpath := hasDerivAt_handbookPlanarEndpoint
    (g := handbookTwoLinkEndpoint)
    (L := handbookTwoLinkEndpointDerivative (q t)) hmap hq
  simpa only [handbookTwoLinkEndpointDerivative_matrix] using hpath

end Ctrllib
