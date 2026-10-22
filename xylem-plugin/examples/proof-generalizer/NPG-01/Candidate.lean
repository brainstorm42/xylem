import Mathlib

theorem npg01_affine_error_norm_le
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T : E →L[ℝ] E} {L : F →L[ℝ] E}
    {z z' e w : E} {v : F}
    (hidentity : z - z' = T e + (w - L v)) :
    ‖z - z'‖ ≤ ‖T‖ * ‖e‖ + ‖w‖ + ‖L‖ * ‖v‖ := by
  rw [hidentity]
  calc
    ‖T e + (w - L v)‖
        ≤ ‖T e‖ + ‖w - L v‖ := norm_add_le _ _
    _ ≤ ‖T‖ * ‖e‖ + (‖w‖ + ‖L‖ * ‖v‖) := by
      exact add_le_add (T.le_opNorm e)
        ((norm_sub_le w (L v)).trans
          (add_le_add (le_refl _) (L.le_opNorm v)))
    _ = ‖T‖ * ‖e‖ + ‖w‖ + ‖L‖ * ‖v‖ :=
      (add_assoc _ _ _).symm
