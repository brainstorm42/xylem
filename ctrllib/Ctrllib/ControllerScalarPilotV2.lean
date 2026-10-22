import Ctrllib.ComStartupRampCrossTermDecay

namespace ControllerScalarPilotV2

open Ctrllib
open Ctrllib.ComStartupRampCrossTermStorage

/-- Every real beta in the frozen interval satisfies the target storage premise. -/
theorem beta_interval_certificate {β : ℝ}
    (hβ_lo : (1 / 5 : ℝ) ≤ β) (hβ_hi : β ≤ (1 / 4 : ℝ)) :
    0 < β ∧ β < min (1 : ℝ) 1 := by
  have hmin : min (1 : ℝ) 1 = 1 := by norm_num
  constructor
  · linarith
  · rw [hmin]
    linarith

/-- The interval certificate feeds an arbitrary beta into the unchanged theorem. -/
theorem beta_interval_consumed_by_existing_decay
    {β : ℝ} (hβ_lo : (1 / 5 : ℝ) ≤ β) (hβ_hi : β ≤ (1 / 4 : ℝ))
    (τ d T κ μ : ℝ)
    (hτ : 0 < τ) (hd : 0 < d) (hT : 0 ≤ T)
    (hκ : 0 < κ) (hμ : 0 < μ)
    (hA : κ + (Real.exp (-T / τ) * (1 : ℝ) + β * d / 1) * μ / 2
      ≤ (1 - Real.exp (-T / τ)) * d - β)
    (hB : κ + (Real.exp (-T / τ) * (1 : ℝ) + β * d / 1) / (2 * μ)
      ≤ β * (1 - Real.exp (-T / τ)) * (1 : ℝ) / 1)
    {t : ℝ} (ht : T ≤ t) (z : PointMassState) :
    rampedCrossStorageRate (1 : ℝ) τ d 1 β t z ≤
      -κ * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ∧
      ((min (1 : ℝ) 1 / 2 - β / 2) * ‖z‖ ^ 2 ≤
          rampedCrossStorage (1 : ℝ) 1 β z ∧
        rampedCrossStorage (1 : ℝ) 1 β z ≤
          (max (1 : ℝ) 1 + β) * ‖z‖ ^ 2) := by
  have hcert := beta_interval_certificate hβ_lo hβ_hi
  have hβpos : 0 < β := hcert.1
  have hβstorage : β < min (1 : ℝ) 1 := hcert.2
  simpa using
    Ctrllib.ComStartupRampCrossTermDecay.rampedCrossStorageRate_strict_decay_with_storage
      (1 : ℝ) τ d (1 : ℝ) β T κ μ
      (by norm_num) hτ hd (by norm_num) hT hβpos hβstorage hκ hμ hA hB ht z

/-- The invalid endpoint beta = 1 is outside the frozen interval. -/
theorem invalid_beta_endpoint_rejected :
    ¬ ((1 : ℝ) ≤ (1 / 4 : ℝ)) := by
  norm_num

/-- The invalid endpoint beta = 1 also fails the target storage premise. -/
theorem invalid_beta_endpoint_storage_rejected :
    ¬ ((1 : ℝ) < min (1 : ℝ) 1) := by
  norm_num

/-- A falsely widened interval [1/5, 1] cannot support the universal claim. -/
theorem falsely_widened_interval_rejected :
    ¬ (∀ β : ℝ, ((1 / 5 : ℝ) ≤ β ∧ β ≤ (1 : ℝ)) →
      β < min (1 : ℝ) 1) := by
  intro hwide
  have hbad := hwide (1 : ℝ) (by norm_num)
  norm_num at hbad

end ControllerScalarPilotV2

#print axioms ControllerScalarPilotV2.beta_interval_certificate
#print axioms ControllerScalarPilotV2.beta_interval_consumed_by_existing_decay
#print axioms ControllerScalarPilotV2.invalid_beta_endpoint_rejected
#print axioms ControllerScalarPilotV2.invalid_beta_endpoint_storage_rejected
#print axioms ControllerScalarPilotV2.falsely_widened_interval_rejected
