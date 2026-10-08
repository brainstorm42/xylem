import Ctrllib.TikhonovUniformBound
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Equality case of the scalar Tikhonov bound

For a nonnegative singular value `sigma` and a positive regularization shift
`lam`, the modal gain `sigma / (sigma ^ 2 + lam)` reaches the universal bound
`1 / (2 * sqrt lam)` exactly when `sigma = sqrt lam`.  This is the scalar
equality characterization corresponding to `tikhonov_uniform_bound`; it does
not add a matrix, rectangular, weighted, or application-specific claim.
-/

namespace Ctrllib

/-- Equality in the universal scalar Tikhonov gain bound occurs exactly at
`sigma = √lam`. -/
theorem tikhonov_uniform_bound_eq_iff {sigma lam : ℝ}
    (hsigma : 0 ≤ sigma) (hlam : 0 < lam) :
    sigma / (sigma ^ 2 + lam) = 1 / (2 * Real.sqrt lam) ↔
      sigma = Real.sqrt lam := by
  have hsigma_sq : 0 ≤ sigma * sigma := mul_nonneg hsigma hsigma
  have hden : 0 < sigma ^ 2 + lam := by
    nlinarith [hsigma_sq]
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hsq : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam.le
  have htwo : 0 < (2 : ℝ) * Real.sqrt lam := by
    positivity
  constructor
  · intro h
    have hcross : sigma * (2 * Real.sqrt lam) = 1 * (sigma ^ 2 + lam) :=
      (div_eq_div_iff hden.ne' htwo.ne').mp h
    nlinarith [sq_nonneg (sigma - Real.sqrt lam)]
  · intro h
    rw [h, hsq]
    field_simp
    nlinarith [hsq]

end Ctrllib

#print axioms Ctrllib.tikhonov_uniform_bound_eq_iff
