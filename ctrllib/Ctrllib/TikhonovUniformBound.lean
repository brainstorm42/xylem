/-
Universal scalar modal bound for the normal-equations Tikhonov filter.

For a nonnegative singular value `σ` and a positive Gram shift `λ`, the
coefficient `σ / (σ² + λ)` is nonnegative and is at most
`1 / (2 * sqrt λ)`.  This is the scalar inequality behind the conventional
universal amplification estimate; no matrix norm or application statement is
made here.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Ctrllib

/-- The universal scalar gain bound for the Tikhonov modal coefficient. -/
theorem tikhonov_uniform_bound {sigma lam : ℝ} (hsigma : 0 ≤ sigma) (hlam : 0 < lam) :
    0 ≤ sigma / (sigma ^ 2 + lam) ∧
      sigma / (sigma ^ 2 + lam) ≤ 1 / (2 * Real.sqrt lam) := by
  have hden : 0 < sigma ^ 2 + lam := by
    nlinarith [sq_nonneg sigma]
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hsqrt_sq : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam.le
  have htwo : 0 < (2 : ℝ) * Real.sqrt lam := by
    positivity
  constructor
  · exact div_nonneg hsigma hden.le
  · apply (div_le_div_iff₀ hden htwo).2
    nlinarith [sq_nonneg (sigma - Real.sqrt lam), hsqrt_sq]

end Ctrllib

#print axioms Ctrllib.tikhonov_uniform_bound
