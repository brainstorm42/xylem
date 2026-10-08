/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Generic reference calculus

These lemmas deliberately stop at source correspondence. They say how the
derivatives of `p (u t)` and `s (u t) • p₁ (u t)` follow from explicit local
derivative hypotheses; they do not assert that a controller realizes the
reference or that a physical model matches the encoded functions.
-/

namespace Ctrllib

section ReferenceCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p p₁ p₂ : ℝ → E} {u s s₁ : ℝ → ℝ} {t : ℝ}

/-- Chain rule for a vector-valued reference `p` along a scalar phase `u`.

The assumptions encode `u̇(t) = s(u(t))` and `p'(u(t)) = p₁(u(t))`.
The conclusion is the desired velocity identity
`d/dt p(u(t)) = s(u(t)) • p₁(u(t))`. -/
theorem hasDerivAt_reference_comp
    (hu : HasDerivAt u (s (u t)) t)
    (hp : HasDerivAt p (p₁ (u t)) (u t)) :
    HasDerivAt (fun τ => p (u τ)) (s (u t) • p₁ (u t)) t := by
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply] using
    (hp.hasFDerivAt.comp t hu.hasFDerivAt).hasDerivAt

/-- Product and chain rules for the desired velocity
`v_d(t) = s(u(t)) • p₁(u(t))`.

The assumptions encode `u̇ = s ∘ u`, `s' = s₁`, and `p₁' = p₂` at the
current phase. The conclusion is the generic acceleration identity

`v̇_d = s(u)² • p₂(u) + (s₁(u) s(u)) • p₁(u)`.
-/
theorem hasDerivAt_reference_velocity
    (hu : HasDerivAt u (s (u t)) t)
    (hs : HasDerivAt s (s₁ (u t)) (u t))
    (hp₁ : HasDerivAt p₁ (p₂ (u t)) (u t)) :
    HasDerivAt (fun τ => s (u τ) • p₁ (u τ))
      ((s (u t)) ^ 2 • p₂ (u t) + (s₁ (u t) * s (u t)) • p₁ (u t)) t := by
  have hs_comp : HasDerivAt (fun τ => s (u τ)) (s₁ (u t) * s (u t)) t := by
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, mul_comm] using
      (hs.hasFDerivAt.comp t hu.hasFDerivAt).hasDerivAt
  have hp₁_comp : HasDerivAt (fun τ => p₁ (u τ)) (s (u t) • p₂ (u t)) t :=
    hasDerivAt_reference_comp hu hp₁
  change HasDerivAt ((fun τ => s (u τ)) • fun τ => p₁ (u τ)) _ t
  simpa only [smul_smul, pow_two, mul_comm, mul_left_comm, mul_assoc] using
    hs_comp.smul hp₁_comp

end ReferenceCalculus

end Ctrllib

#print axioms Ctrllib.hasDerivAt_reference_comp
#print axioms Ctrllib.hasDerivAt_reference_velocity
