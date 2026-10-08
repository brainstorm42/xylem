/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Spherical-helix formulas and regularity

The coordinate type is the raw finite function space `Fin 3 → ℝ`. The
isometric `PiLp` wrapper used by `PointMassCoord`, and the `HasDerivAt` bridge
for these coordinates, are intentionally left to a later correspondence
layer. The explicit formulas and nonvanishing result are sealed here without
that representational complication.
-/

open scoped BigOperators Matrix

namespace Ctrllib

/-- Three scalar coordinates used for the explicit spherical helix. -/
abbrev SphericalHelixCoord := Fin 3 → ℝ

/-- Spherical helix with affine azimuth and elevation parameters. -/
noncomputable def sphericalHelix (center : SphericalHelixCoord)
    (radius thetaRate phiZero phiRate u : ℝ) : SphericalHelixCoord :=
  center + ![
    radius * Real.cos (phiZero + phiRate * u) * Real.cos (thetaRate * u),
    radius * Real.cos (phiZero + phiRate * u) * Real.sin (thetaRate * u),
    radius * Real.sin (phiZero + phiRate * u)]

/-- Explicit first derivative of `sphericalHelix` with respect to phase. -/
noncomputable def sphericalHelixD1
    (radius thetaRate phiZero phiRate u : ℝ) : SphericalHelixCoord := ![
  radius * (-phiRate * Real.sin (phiZero + phiRate * u) * Real.cos (thetaRate * u)
    - thetaRate * Real.cos (phiZero + phiRate * u) * Real.sin (thetaRate * u)),
  radius * (-phiRate * Real.sin (phiZero + phiRate * u) * Real.sin (thetaRate * u)
    + thetaRate * Real.cos (phiZero + phiRate * u) * Real.cos (thetaRate * u)),
  radius * phiRate * Real.cos (phiZero + phiRate * u)]

/-- Explicit second derivative of `sphericalHelix` with respect to phase. -/
noncomputable def sphericalHelixD2
    (radius thetaRate phiZero phiRate u : ℝ) : SphericalHelixCoord := ![
  radius * (-(thetaRate ^ 2 + phiRate ^ 2) * Real.cos (phiZero + phiRate * u) *
      Real.cos (thetaRate * u)
    + 2 * thetaRate * phiRate * Real.sin (phiZero + phiRate * u) *
      Real.sin (thetaRate * u)),
  radius * (-(thetaRate ^ 2 + phiRate ^ 2) * Real.cos (phiZero + phiRate * u) *
      Real.sin (thetaRate * u)
    - 2 * thetaRate * phiRate * Real.sin (phiZero + phiRate * u) *
      Real.cos (thetaRate * u)),
  -radius * phiRate ^ 2 * Real.sin (phiZero + phiRate * u)]

/-- Exact squared coordinate speed of the spherical helix. -/
theorem sphericalHelixD1_sq_sum
    (radius thetaRate phiZero phiRate u : ℝ) :
    ∑ i : Fin 3, (sphericalHelixD1 radius thetaRate phiZero phiRate u i) ^ 2 =
      radius ^ 2 * (phiRate ^ 2 + thetaRate ^ 2 * Real.cos (phiZero + phiRate * u) ^ 2) := by
  simp only [Fin.sum_univ_three]
  simp only [sphericalHelixD1, neg_mul, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  calc
    _ = radius ^ 2 *
        (phiRate ^ 2 * Real.sin (phiZero + phiRate * u) ^ 2 *
            (Real.cos (thetaRate * u) ^ 2 + Real.sin (thetaRate * u) ^ 2) +
          thetaRate ^ 2 * Real.cos (phiZero + phiRate * u) ^ 2 *
            (Real.sin (thetaRate * u) ^ 2 + Real.cos (thetaRate * u) ^ 2) +
          phiRate ^ 2 * Real.cos (phiZero + phiRate * u) ^ 2) := by ring
    _ = radius ^ 2 *
        (phiRate ^ 2 * (Real.sin (phiZero + phiRate * u) ^ 2 +
          Real.cos (phiZero + phiRate * u) ^ 2) +
          thetaRate ^ 2 * Real.cos (phiZero + phiRate * u) ^ 2) := by
      rw [Real.cos_sq_add_sin_sq, Real.sin_sq_add_cos_sq]
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

/-- Positive radius and nonzero elevation rate make the spherical helix
regular in the componentwise Euclidean sense. -/
theorem sphericalHelixD1_sq_sum_pos
    (radius thetaRate phiZero phiRate u : ℝ)
    (hradius : 0 < radius) (hphiRate : phiRate ≠ 0) :
    0 < ∑ i : Fin 3, (sphericalHelixD1 radius thetaRate phiZero phiRate u i) ^ 2 := by
  rw [sphericalHelixD1_sq_sum]
  have hradiusSq : 0 < radius ^ 2 := sq_pos_of_pos hradius
  have hphiSq : 0 < phiRate ^ 2 := sq_pos_of_ne_zero hphiRate
  have htheta : 0 ≤ thetaRate ^ 2 * Real.cos (phiZero + phiRate * u) ^ 2 :=
    mul_nonneg (sq_nonneg thetaRate) (sq_nonneg _)
  positivity

end Ctrllib

#print axioms Ctrllib.sphericalHelixD1_sq_sum
#print axioms Ctrllib.sphericalHelixD1_sq_sum_pos
