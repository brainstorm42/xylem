import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr

/-!
# Physical and centre-of-mass-referenced twist errors

Algebraic reconstruction of the selected FFSM source equation (3.44c).
All linear maps must be expressed in the declared compatible frames. The
physical kinematic identities and their derivatives remain premises, not
consequences of this algebra. The reference uses Gd evaluated on the lift,
while the actual-state map G may differ.
-/

namespace Ctrllib
variable {C T E : Type*}
variable [NormedAddCommGroup C] [NormedSpace ℝ C]
variable [NormedAddCommGroup T] [NormedSpace ℝ T]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Converting a CoM-referenced twist error to physical twist error retains
both the CoM velocity error and the change of the CoM-to-twist map. -/
theorem physical_twist_error_decomposition
    (G Gd : C →L[ℝ] T) (vc vcd : C) (nu nud nuReduced nudReduced : T)
    (hactual : nu = G vc + nuReduced) (hdesired : nud = Gd vcd + nudReduced) :
    nu - nud = (nuReduced - nudReduced) +
      G (vc - vcd) + (G - Gd) vcd := by
  rw [hactual, hdesired, map_sub, sub_apply]
  abel

/-- The physical-twist rate equation becomes the selected CoM-referenced
equation with all three residual terms present. -/
theorem reference_frame_rate_decomposition
    (G Gd : C →L[ℝ] T) (J N : T →L[ℝ] E)
    (vc vcd : C) (nu nud nuReduced nudReduced : T) (rate : E)
    (hactual : nu = G vc + nuReduced) (hdesired : nud = Gd vcd + nudReduced)
    (hrate : rate = J (nu - nud) + N nud) :
    rate = J (nuReduced - nudReduced) +
      (N nud + J (G (vc - vcd)) + J ((G - Gd) vcd)) := by
  rw [hrate, physical_twist_error_decomposition G Gd vc vcd nu nud
    nuReduced nudReduced hactual hdesired, map_add, map_add]
  abel

/-- Operator gains bound the residual without identifying CoM velocity error
with reference speed or discarding the actual/reference map discrepancy. -/
theorem reference_frame_residual_bound
    (G Gd : C →L[ℝ] T) (J N : T →L[ℝ] E) (wc vcd : C) (nud : T) :
    ‖N nud + J (G wc) + J ((G - Gd) vcd)‖ ≤
      ‖N‖ * ‖nud‖ + ‖J‖ * ‖G‖ * ‖wc‖ + ‖J‖ * ‖G - Gd‖ * ‖vcd‖ := by
  calc
    _ ≤ ‖N nud‖ + ‖J (G wc)‖ + ‖J ((G - Gd) vcd)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖N‖ * ‖nud‖ + ‖J‖ * (‖G‖ * ‖wc‖) +
        ‖J‖ * (‖G - Gd‖ * ‖vcd‖) := by
      gcongr
      · exact N.le_opNorm nud
      · exact (J.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (G.le_opNorm wc) (norm_nonneg J))
      · exact (J.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((G - Gd).le_opNorm vcd) (norm_nonneg J))
    _ = _ := by simp only [mul_assoc]

end Ctrllib

#print axioms Ctrllib.physical_twist_error_decomposition
#print axioms Ctrllib.reference_frame_rate_decomposition
#print axioms Ctrllib.reference_frame_residual_bound
