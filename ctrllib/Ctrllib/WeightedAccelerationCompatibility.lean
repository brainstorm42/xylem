import Ctrllib.EqualityConstrainedQuadratic

/-!
# Weighted acceleration and feasible nullspace motion

The acceleration-level weighted solve realizes the requested task acceleration
once the actual velocity and Jacobian derivative are supplied. Any other
compatible acceleration differs by a kernel vector; its exact weighted cost
gap is the cost of that kernel component. No derivative of a velocity optimum
is silently identified with this separate minimization.
-/

open Matrix
namespace Ctrllib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The acceleration-level solve supplies the requested task acceleration
including the Jacobian-rate contribution from the actual velocity. -/
theorem weighted_acceleration_task_equation
    {J : Matrix m n ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) (hJ : Function.Surjective J.mulVec)
    (J₁ : Matrix m n ℝ) (v : n → ℝ) (Ad : m → ℝ) :
    J *ᵥ (weightedRightInverse W J *ᵥ (Ad - J₁ *ᵥ v)) + J₁ *ᵥ v = Ad := by
  rw [weighted_right_inverse_feasible hW hJ]
  exact sub_add_cancel _ _

/-- Every other task-compatible acceleration differs from the weighted
acceleration optimum by a vector in the instantaneous Jacobian kernel. -/
theorem compatible_acceleration_difference_in_kernel
    {J : Matrix m n ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) (hJ : Function.Surjective J.mulVec)
    (J₁ : Matrix m n ℝ) (v a : n → ℝ) (Ad : m → ℝ)
    (hacc : J *ᵥ a + J₁ *ᵥ v = Ad) :
    J *ᵥ (a - weightedRightInverse W J *ᵥ (Ad - J₁ *ᵥ v)) = 0 := by
  rw [mulVec_sub, weighted_right_inverse_feasible hW hJ]
  have ha : J *ᵥ a = Ad - J₁ *ᵥ v := eq_sub_of_add_eq hacc
  rw [ha, sub_self]

/-- The exact weighted cost difference is the cost of the feasible nullspace
component. This is an algebraic statement at one state, not trajectory or
actuator-limit feasibility. -/
theorem compatible_acceleration_cost_gap
    {J : Matrix m n ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) (hJ : Function.Surjective J.mulVec)
    (J₁ : Matrix m n ℝ) (v a : n → ℝ) (Ad : m → ℝ)
    (hacc : J *ᵥ a + J₁ *ᵥ v = Ad) :
    weightedQuadratic W a =
      weightedQuadratic W (weightedRightInverse W J *ᵥ (Ad - J₁ *ᵥ v)) +
      weightedQuadratic W (a - weightedRightInverse W J *ᵥ (Ad - J₁ *ᵥ v)) := by
  let z := weightedRightInverse W J *ᵥ (Ad - J₁ *ᵥ v)
  have hker := compatible_acceleration_difference_in_kernel hW hJ J₁ v a Ad hacc
  have hcross := weighted_right_inverse_cross_term_zero hW (Ad - J₁ *ᵥ v) hker
  have heq : a = z + (a - z) := by abel
  calc
    weightedQuadratic W a = weightedQuadratic W (z + (a - z)) := congrArg _ heq
    _ = weightedQuadratic W z + weightedQuadratic W (a - z) := by
      rw [weightedQuadratic_add (posDef_transpose_eq hW)]
      simp only [z, hcross, add_zero]

end Ctrllib

#print axioms Ctrllib.weighted_acceleration_task_equation
#print axioms Ctrllib.compatible_acceleration_difference_in_kernel
#print axioms Ctrllib.compatible_acceleration_cost_gap
