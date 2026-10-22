import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar quadratic cross-term bounds

This low-level module contains the scalar completing-the-square machinery used by
the tracking, cascade, and startup-ramp developments.  The declarations retain
the original `Ctrllib` names and exact statements so `TrackingStrictBound` can
continue to provide the compatibility import for existing callers.
-/

namespace Ctrllib

/-- Young's inequality in the form used for the cross term: `C s t ≤ (Cλ/2) s² + (C/(2λ)) t²`. -/
theorem young_cross {C lam s t : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) :
    C * s * t ≤ C * lam / 2 * s ^ 2 + C / (2 * lam) * t ^ 2 := by
  have hkey : 0 ≤ C / (2 * lam) * (lam * s - t) ^ 2 := by positivity
  have hexp : C / (2 * lam) * (lam * s - t) ^ 2
      = C * lam / 2 * s ^ 2 - C * s * t + C / (2 * lam) * t ^ 2 := by
    field_simp
    ring
  linarith

/-- **Quadratic-form domination.** For `A, B > 0`-type margins after Young,
`A s² + B t² − C s t ≥ min(A − Cλ/2, B − C/(2λ)) (s² + t²)`. -/
theorem quad_form_dominates {A B C lam s t : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) :
    min (A - C * lam / 2) (B - C / (2 * lam)) * (s ^ 2 + t ^ 2)
      ≤ A * s ^ 2 + B * t ^ 2 - C * s * t := by
  have hy := young_cross (s := s) (t := t) hC hlam
  have h1 : min (A - C * lam / 2) (B - C / (2 * lam)) * s ^ 2 ≤ (A - C * lam / 2) * s ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg s)
  have h2 : min (A - C * lam / 2) (B - C / (2 * lam)) * t ^ 2 ≤ (B - C / (2 * lam)) * t ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg t)
  nlinarith [h1, h2, hy]

#print axioms Ctrllib.young_cross
#print axioms Ctrllib.quad_form_dominates

end Ctrllib
