/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import Ctrllib.PointMassComFlow

/-!
# Moving-reference product flow

This module gives the scalar terminal-rest phase flow and its product with the
sealed isotropic point-mass flow. It proves convergence only for the encoded
autonomous product system. It does not prove arbitrary matrix gains,
reference/controller source correspondence, saturation, sampling, switching,
regularization, or any other live-controller modification.
-/

open Filter Topology

namespace Ctrllib

section PhaseError

/-- Scalar phase-error field `q̇ = -λ q`. -/
def phaseErrorField (rate : ℝ) (q : ℝ) : ℝ := -rate * q

/-- Explicit global flow for `q̇ = -λ q`. -/
noncomputable def phaseErrorFlow (rate : ℝ) : Flow ℝ ℝ where
  toFun t q := Real.exp (-rate * t) * q
  cont' := by
    fun_prop
  map_add' t₁ t₂ q := by
    rw [show -rate * (t₁ + t₂) = -rate * t₁ + -rate * t₂ by ring, Real.exp_add]
    ring
  map_zero' q := by simp

/-- The explicit scalar phase flow solves `q̇ = -λ q`. -/
theorem phaseErrorFlow_hasDerivAt (rate q t : ℝ) :
    HasDerivAt (fun τ => phaseErrorFlow rate τ q)
      (phaseErrorField rate (phaseErrorFlow rate t q)) t := by
  change HasDerivAt (fun τ => Real.exp (-rate * τ) * q)
    (-rate * (Real.exp (-rate * t) * q)) t
  simpa only [Function.comp_apply, mul_one, mul_comm, mul_left_comm, mul_assoc] using
    ((Real.hasDerivAt_exp (-rate * t)).comp t
      ((hasDerivAt_id t).const_mul (-rate))).mul_const q

/-- Interface form: the scalar phase flow solves its field everywhere. -/
theorem phaseError_isSolutionTo (rate : ℝ) :
    IsSolutionTo (phaseErrorFlow rate) (phaseErrorField rate) := by
  intro q t
  exact phaseErrorFlow_hasDerivAt rate q t

/-- For positive `λ`, every scalar phase error converges to zero. -/
theorem phaseError_tendsto_zero (rate : ℝ) (hrate : 0 < rate) (q₀ : ℝ) :
    Tendsto (fun t : ℝ => phaseErrorFlow rate t q₀) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => -rate * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hrate)
  simpa only [phaseErrorFlow, Function.comp_apply, zero_mul] using
    (Real.tendsto_exp_atBot.comp hlin).mul_const q₀

end PhaseError

section AugmentedPointMass

/-- Isotropic point-mass tracking error augmented by one scalar phase error. -/
abbrev AugmentedPointMassState := PointMassState × ℝ

/-- Product field `(f_point_mass(z), -λ q)`. -/
noncomputable def augmentedPointMassField (m d k rate : ℝ) :
    AugmentedPointMassState → AugmentedPointMassState :=
  fun z => (pointMassField m d k z.1, phaseErrorField rate z.2)

/-- Product of the sealed point-mass flow and explicit phase-error flow. -/
noncomputable def augmentedPointMassFlow (m d k rate : ℝ) (hm : 0 < m) :
    Flow ℝ AugmentedPointMassState where
  toFun t z := (pointMassFlow m d k hm t z.1, phaseErrorFlow rate t z.2)
  cont' := by
    exact (pointMassFlow m d k hm).continuous continuous_fst continuous_snd.fst |>.prodMk
      ((phaseErrorFlow rate).continuous continuous_fst continuous_snd.snd)
  map_add' t₁ t₂ z := by
    apply Prod.ext
    · exact (pointMassFlow m d k hm).map_add t₁ t₂ z.1
    · exact (phaseErrorFlow rate).map_add t₁ t₂ z.2
  map_zero' z := by
    apply Prod.ext
    · exact (pointMassFlow m d k hm).map_zero_apply z.1
    · exact (phaseErrorFlow rate).map_zero_apply z.2

/-- The product flow solves the augmented field. -/
theorem augmentedPointMass_isSolutionTo
    (m d k rate : ℝ) (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) :
    IsSolutionTo (augmentedPointMassFlow m d k rate hm)
      (augmentedPointMassField m d k rate) := by
  intro z t
  exact (pointMass_isSolutionTo m d k hm hd hk z.1 t).prodMk
    (phaseError_isSolutionTo rate z.2 t)

/-- The augmented isotropic point-mass and positive-rate phase errors converge
jointly to zero. This is a product convergence theorem, not a general
matrix-gain moving-reference theorem. -/
theorem augmentedPointMass_tendsto_zero
    (m d k rate : ℝ) (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) (hrate : 0 < rate)
    (z₀ : AugmentedPointMassState) :
    Tendsto (fun t : ℝ => augmentedPointMassFlow m d k rate hm t z₀) atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => augmentedPointMassFlow m d k rate hm t z₀) atTop
    (𝓝 ((0 : PointMassState), (0 : ℝ)))
  simpa only [augmentedPointMassFlow, ← nhds_prod_eq] using
    (pointMass_tendsto_zero m d k hm hd hk z₀.1).prodMk
      (phaseError_tendsto_zero rate hrate z₀.2)

end AugmentedPointMass

end Ctrllib

#print axioms Ctrllib.phaseErrorFlow_hasDerivAt
#print axioms Ctrllib.phaseError_isSolutionTo
#print axioms Ctrllib.phaseError_tendsto_zero
#print axioms Ctrllib.augmentedPointMass_isSolutionTo
#print axioms Ctrllib.augmentedPointMass_tendsto_zero
