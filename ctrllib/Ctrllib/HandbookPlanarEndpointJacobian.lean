/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.ManipulatorEnergy
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Handbook planar endpoint/Jacobian interface

This module supplies the typed conversion needed between a Fréchet derivative
of a two-coordinate, three-output geometric endpoint map and the matrix shape
used by the strict-storage consumer.  It does not define a Denavit--Hartenberg
endpoint map, identify a physical frame, or differentiate the Jacobian path.
-/

open Matrix
open scoped BigOperators

namespace Ctrllib

abbrev HandbookPlanarConfiguration := Fin 2 → ℝ
abbrev HandbookPlanarEndpoint := Fin 3 → ℝ

/--
The matrix representation of a supplied endpoint-map Fréchet derivative.

Rows are the ordered endpoint components and columns are the ordered joint
coordinates.  This is only a representation adapter; it does not assert that
`L` came from a particular robot or frame convention.
-/
noncomputable def handbookPlanarJacobianMatrix
    (L : HandbookPlanarConfiguration →L[ℝ] HandbookPlanarEndpoint) :
    Matrix (Fin 3) (Fin 2) ℝ :=
  LinearMap.toMatrix' L.toLinearMap

/-- The adapter preserves the matrix row/column action on a joint velocity. -/
@[simp] theorem handbookPlanarJacobianMatrix_mulVec
    (L : HandbookPlanarConfiguration →L[ℝ] HandbookPlanarEndpoint)
    (v : HandbookPlanarConfiguration) :
    handbookPlanarJacobianMatrix L *ᵥ v = L v := by
  exact LinearMap.toMatrix'_mulVec L.toLinearMap v

/--
The matrix-valued endpoint velocity follows from supplied Fréchet and path
derivative witnesses.  The composition step reuses the existing generic
configuration-path theorem; no Jacobian-path derivative is supplied here.
-/
theorem hasDerivAt_handbookPlanarEndpoint
    {g : HandbookPlanarConfiguration → HandbookPlanarEndpoint}
    {L : HandbookPlanarConfiguration →L[ℝ] HandbookPlanarEndpoint}
    {q : ℝ → HandbookPlanarConfiguration}
    {qdot : HandbookPlanarConfiguration} {t : ℝ}
    (hg : HasFDerivAt g L (q t)) (hq : HasDerivAt q qdot t) :
    HasDerivAt (fun s => g (q s))
      (handbookPlanarJacobianMatrix L *ᵥ qdot) t := by
  have hpath := hasDerivAt_inertia_of_configuration hg hq
  convert hpath using 1
  exact handbookPlanarJacobianMatrix_mulVec L qdot

end Ctrllib
