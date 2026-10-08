/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Ctrllib.ReferenceCalculus

/-!
# Norm bounds for a reference curve

These lemmas pair the local derivative identities in `ReferenceCalculus` with
pointwise norm bounds. They remain statements about the encoded reference
functions: they do not establish path feasibility, a controller realization,
or a domain lift.
Conventional derivation: the corresponding derivation record's
the corresponding local note.
-/

namespace Ctrllib

section ReferenceAdmissibility

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p p₁ p₂ : ℝ → E} {u s s₁ : ℝ → ℝ} {t : ℝ}
variable {vmax amax P₁ P₂ : ℝ}

private theorem norm_smul_le_of_abs_le {a A : ℝ} {x : E} {X : ℝ}
    (ha : |a| ≤ A) (hx : ‖x‖ ≤ X) (hA : 0 ≤ A) :
    ‖a • x‖ ≤ A * X := by
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |a| * ‖x‖ ≤ A * ‖x‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg x)
    _ ≤ A * X := mul_le_mul_of_nonneg_left hx hA

/-- The reference velocity has the norm bound obtained from scalar speed and
the norm bound on the phase derivative. -/
theorem norm_reference_velocity_le
    (hspeed : |s (u t)| ≤ vmax) (hp₁ : ‖p₁ (u t)‖ ≤ P₁)
    (hvmax : 0 ≤ vmax) :
    ‖s (u t) • p₁ (u t)‖ ≤ P₁ * vmax := by
  have h := norm_smul_le_of_abs_le hspeed hp₁ hvmax
  simpa [mul_comm] using h

/-- The reference acceleration has the triangle-inequality bound obtained from
speed, scalar acceleration, and the two phase derivatives. -/
theorem norm_reference_acceleration_le
    (hspeed : |s (u t)| ≤ vmax) (hscalar : |s₁ (u t) * s (u t)| ≤ amax)
    (hp₁ : ‖p₁ (u t)‖ ≤ P₁) (hp₂ : ‖p₂ (u t)‖ ≤ P₂)
    (hvmax : 0 ≤ vmax) (hamax : 0 ≤ amax) :
    ‖(s (u t)) ^ 2 • p₂ (u t) + (s₁ (u t) * s (u t)) • p₁ (u t)‖ ≤
      P₂ * vmax ^ 2 + P₁ * amax := by
  have hsquare : |(s (u t)) ^ 2| ≤ vmax ^ 2 := by
    have hspeed' : |s (u t)| ≤ |vmax| := by simpa [abs_of_nonneg hvmax] using hspeed
    simpa [abs_sq, abs_of_nonneg hvmax] using
      (sq_le_sq (a := s (u t)) (b := vmax)).mpr hspeed'
  have h₂ := norm_smul_le_of_abs_le hsquare hp₂ (sq_nonneg vmax)
  have h₁ := norm_smul_le_of_abs_le hscalar hp₁ hamax
  calc
    ‖(s (u t)) ^ 2 • p₂ (u t) + (s₁ (u t) * s (u t)) • p₁ (u t)‖ ≤
        ‖(s (u t)) ^ 2 • p₂ (u t)‖ +
          ‖(s₁ (u t) * s (u t)) • p₁ (u t)‖ := norm_add_le _ _
    _ ≤ P₂ * vmax ^ 2 + P₁ * amax := by
      simpa [mul_comm] using add_le_add h₂ h₁

/-- Derivative witnesses and norm bounds for the encoded reference velocity and
acceleration at one phase point. -/
theorem reference_derivatives_and_bounds
    (hu : HasDerivAt u (s (u t)) t)
    (hp : HasDerivAt p (p₁ (u t)) (u t))
    (hs : HasDerivAt s (s₁ (u t)) (u t))
    (hp₁' : HasDerivAt p₁ (p₂ (u t)) (u t))
    (hspeed : |s (u t)| ≤ vmax)
    (hscalar : |s₁ (u t) * s (u t)| ≤ amax)
    (hP₁ : ‖p₁ (u t)‖ ≤ P₁) (hP₂ : ‖p₂ (u t)‖ ≤ P₂)
    (hvmax : 0 ≤ vmax) (hamax : 0 ≤ amax) :
    HasDerivAt (fun τ => p (u τ)) (s (u t) • p₁ (u t)) t ∧
    HasDerivAt (fun τ => s (u τ) • p₁ (u τ))
        ((s (u t)) ^ 2 • p₂ (u t) + (s₁ (u t) * s (u t)) • p₁ (u t)) t ∧
      ‖s (u t) • p₁ (u t)‖ ≤ P₁ * vmax ∧
      ‖(s (u t)) ^ 2 • p₂ (u t) + (s₁ (u t) * s (u t)) • p₁ (u t)‖ ≤
        P₂ * vmax ^ 2 + P₁ * amax := by
  refine ⟨hasDerivAt_reference_comp hu hp, hasDerivAt_reference_velocity hu hs hp₁',
    norm_reference_velocity_le hspeed hP₁ hvmax,
    norm_reference_acceleration_le hspeed hscalar hP₁ hP₂ hvmax hamax⟩

end ReferenceAdmissibility

end Ctrllib

#print axioms Ctrllib.norm_reference_velocity_le
#print axioms Ctrllib.norm_reference_acceleration_le
#print axioms Ctrllib.reference_derivatives_and_bounds
