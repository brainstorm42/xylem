import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential reference phase

The phase law is the concrete timing choice `u' = rate (1 - u)` used by the
reference-to-tracking interface.  This file proves only its scalar calculus
and interval bounds; it does not establish finite-horizon actuator or domain
feasibility for an FFSM configuration lift.
-/

namespace Ctrllib

noncomputable def referencePhase (rate u₀ t : ℝ) : ℝ := 1 - (1 - u₀) * Real.exp (-rate * t)

noncomputable def referenceSpeed (rate u₀ t : ℝ) : ℝ := rate * (1 - referencePhase rate u₀ t)

theorem hasDerivAt_referencePhase (rate u₀ t : ℝ) :
    HasDerivAt (fun τ => referencePhase rate u₀ τ)
      (referenceSpeed rate u₀ t) t := by
  unfold referencePhase referenceSpeed
  have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-rate * τ))
      (-rate * Real.exp (-rate * t)) t := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (-rate * t)).comp t
      ((hasDerivAt_id t).const_mul (-rate))
  convert (hexp.const_mul (-(1 - u₀))).const_add 1 using 1 <;>
  simp [referencePhase] <;> ring_nf

theorem referencePhase_residual {rate u₀ t : ℝ} :
    1 - referencePhase rate u₀ t = (1 - u₀) * Real.exp (-rate * t) := by
  simp [referencePhase]

theorem referencePhase_bounds {rate u₀ t : ℝ}
    (hrate : 0 < rate) (hu₀ : 0 ≤ u₀) (hu₀1 : u₀ < 1) (ht : 0 ≤ t) :
    0 ≤ referencePhase rate u₀ t ∧ referencePhase rate u₀ t < 1 := by
  have hexp : 0 < Real.exp (-rate * t) := Real.exp_pos _
  have hexp_le : Real.exp (-rate * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hres : 0 < (1 - u₀) * Real.exp (-rate * t) := mul_pos (by linarith) hexp
  have hres_le : (1 - u₀) * Real.exp (-rate * t) ≤ 1 := by
    have : 0 ≤ 1 - u₀ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hexp_le this]
  change 0 ≤ 1 - (1 - u₀) * Real.exp (-rate * t) ∧
    1 - (1 - u₀) * Real.exp (-rate * t) < 1
  constructor <;> linarith

theorem referenceSpeed_bounds {rate u₀ t : ℝ}
    (hrate : 0 < rate) (hu₀ : 0 ≤ u₀) (hu₀1 : u₀ < 1) (ht : 0 ≤ t) :
    0 ≤ referenceSpeed rate u₀ t ∧ referenceSpeed rate u₀ t ≤ rate := by
  have hphase := referencePhase_bounds hrate hu₀ hu₀1 ht
  unfold referenceSpeed
  change 0 ≤ rate * (1 - referencePhase rate u₀ t) ∧
    rate * (1 - referencePhase rate u₀ t) ≤ rate
  constructor
  · exact mul_nonneg hrate.le (sub_nonneg.mpr hphase.2.le)
  · nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.mpr hphase.2.le) hrate.le,
      mul_le_mul_of_nonneg_left (sub_nonneg.mpr hphase.1) hrate.le]

theorem referenceAcceleration_abs_le {rate u₀ t : ℝ}
    (hrate : 0 < rate) (hu₀ : 0 ≤ u₀) (hu₀1 : u₀ < 1) (ht : 0 ≤ t) :
    |-(rate * referenceSpeed rate u₀ t)| ≤ rate ^ 2 := by
  have hs := referenceSpeed_bounds hrate hu₀ hu₀1 ht
  have hprod : 0 ≤ rate * referenceSpeed rate u₀ t := mul_nonneg hrate.le hs.1
  rw [abs_neg, abs_of_nonneg hprod]
  nlinarith [mul_le_mul_of_nonneg_left hs.2 (le_of_lt hrate)]

#print axioms Ctrllib.hasDerivAt_referencePhase
#print axioms Ctrllib.referencePhase_residual
#print axioms Ctrllib.referencePhase_bounds
#print axioms Ctrllib.referenceSpeed_bounds
#print axioms Ctrllib.referenceAcceleration_abs_le

end Ctrllib
