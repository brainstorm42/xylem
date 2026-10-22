import Candidate
import Mathlib

namespace NPG01Independent

variable {E F U : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def localPlantStep (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (x : E) (u : U) (w : E) : E := A x + B u + w

def localObserverStep (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : E →L[ℝ] F) (L : F →L[ℝ] E) (xhat : E) (u : U) (y : F) : E :=
  A xhat + B u + L (y - C xhat)

theorem positive_client
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : E →L[ℝ] F) (L : F →L[ℝ] E)
    (x xhat w : E) (u : U) (v : F) :
    ‖localPlantStep A B x u w - localObserverStep A B C L xhat u (C x + v)‖ ≤
      ‖A - L.comp C‖ * ‖x - xhat‖ + ‖w‖ + ‖L‖ * ‖v‖ := by
  have hidentity :
      localPlantStep A B x u w - localObserverStep A B C L xhat u (C x + v) =
        (A - L.comp C) (x - xhat) + (w - L v) := by
    simp only [localPlantStep, localObserverStep, map_add, map_sub,
      sub_apply, ContinuousLinearMap.comp_apply]
    abel
  exact npg01_affine_error_norm_le hidentity

theorem specialization_back
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : E →L[ℝ] F) (L : F →L[ℝ] E)
    (x xhat w : E) (u : U) (v : F) :
    ‖localPlantStep A B x u w - localObserverStep A B C L xhat u (C x + v)‖ ≤
      ‖A - L.comp C‖ * ‖x - xhat‖ + ‖w‖ + ‖L‖ * ‖v‖ := by
  exact positive_client A B C L x xhat w u v

section Negative

variable {T : E →L[ℝ] E} {M : F →L[ℝ] E}
  {z z' e w : E} {v : F}
variable (hidentity : z - z' = T e + (w - M v))

#check_failure
  (show ‖z - z'‖ ≤ ‖T‖ * ‖w‖ + ‖e‖ + ‖M‖ * ‖v‖ from
    npg01_affine_error_norm_le (T := T) (L := M) (z := z) (z' := z')
      (e := e) (w := w) (v := v) hidentity)

end Negative

#print axioms npg01_affine_error_norm_le
#print axioms positive_client
#print axioms specialization_back

end NPG01Independent
