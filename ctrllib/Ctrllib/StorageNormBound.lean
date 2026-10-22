/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonia Hoffman
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Sqrt

/-!
# Storage-to-norm conversion

This module isolates the scalar algebra that converts a quadratic storage decay
estimate and two quadratic norm bounds into a norm estimate.  It deliberately
does not mention a trajectory, a differential equation, or a model-specific
storage function.
-/

namespace Ctrllib

/-- Convert a quadratic storage decay estimate into the corresponding norm bound. -/
theorem norm_le_sqrt_ratio_mul_of_storage_decay
    {E : Type*} [SeminormedAddCommGroup E]
    {z z0 : E} {W W0 c_lo c_hi κ Δ : ℝ}
    (hc_lo : 0 < c_lo) (hc_hi : 0 < c_hi)
    (hlow : c_lo * ‖z‖ ^ 2 ≤ W)
    (hupper : W0 ≤ c_hi * ‖z0‖ ^ 2)
    (hdecay : W ≤ W0 * Real.exp (-(κ / c_hi) * Δ)) :
    ‖z‖ ≤ Real.sqrt (c_hi / c_lo) * ‖z0‖ *
      Real.exp (-(κ / (2 * c_hi)) * Δ) := by
  have hexp_nonneg : 0 ≤ Real.exp (-(κ / c_hi) * Δ) := (Real.exp_pos _).le
  have hquad : c_lo * ‖z‖ ^ 2 ≤
      c_hi * ‖z0‖ ^ 2 * Real.exp (-(κ / c_hi) * Δ) := by
    calc
      c_lo * ‖z‖ ^ 2 ≤ W := hlow
      _ ≤ W0 * Real.exp (-(κ / c_hi) * Δ) := hdecay
      _ ≤ c_hi * ‖z0‖ ^ 2 * Real.exp (-(κ / c_hi) * Δ) :=
        mul_le_mul_of_nonneg_right hupper hexp_nonneg
  have hquad' : ‖z‖ ^ 2 ≤
      (c_hi / c_lo) * ‖z0‖ ^ 2 * Real.exp (-(κ / c_hi) * Δ) := by
    have hmul := mul_le_mul_of_nonneg_left hquad (inv_nonneg.mpr hc_lo.le)
    calc
      ‖z‖ ^ 2 = c_lo⁻¹ * (c_lo * ‖z‖ ^ 2) := by
        field_simp [ne_of_gt hc_lo]
      _ ≤ c_lo⁻¹ * (c_hi * ‖z0‖ ^ 2 * Real.exp (-(κ / c_hi) * Δ)) := hmul
      _ = (c_hi / c_lo) * ‖z0‖ ^ 2 * Real.exp (-(κ / c_hi) * Δ) := by
        field_simp [ne_of_gt hc_lo]
  have hratio : 0 ≤ c_hi / c_lo := div_nonneg hc_hi.le hc_lo.le
  have hsqrt_ratio : (Real.sqrt (c_hi / c_lo)) ^ 2 = c_hi / c_lo :=
    Real.sq_sqrt hratio
  have hsqrt_exp :
      (Real.exp (-(κ / (2 * c_hi)) * Δ)) ^ 2 =
        Real.exp (-(κ / c_hi) * Δ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp [ne_of_gt hc_hi]
    ring
  have htarget_sq : ‖z‖ ^ 2 ≤
      (Real.sqrt (c_hi / c_lo) * ‖z0‖ *
        Real.exp (-(κ / (2 * c_hi)) * Δ)) ^ 2 := by
    calc
      ‖z‖ ^ 2 ≤ (c_hi / c_lo) * ‖z0‖ ^ 2 *
          Real.exp (-(κ / c_hi) * Δ) := hquad'
      _ = (Real.sqrt (c_hi / c_lo) * ‖z0‖ *
          Real.exp (-(κ / (2 * c_hi)) * Δ)) ^ 2 := by
        rw [mul_pow, mul_pow, hsqrt_ratio, hsqrt_exp]
  have htarget_nonneg : 0 ≤ Real.sqrt (c_hi / c_lo) * ‖z0‖ *
      Real.exp (-(κ / (2 * c_hi)) * Δ) := by
    positivity
  exact (sq_le_sq₀ (norm_nonneg z) htarget_nonneg).mp htarget_sq

end Ctrllib

#print axioms Ctrllib.norm_le_sqrt_ratio_mul_of_storage_decay
