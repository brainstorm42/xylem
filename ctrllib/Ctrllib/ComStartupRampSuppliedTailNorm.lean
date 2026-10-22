/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonia Hoffman
-/
import Ctrllib.ComStartupRampTrajectoryAdapter
import Ctrllib.StorageNormBound

/-!
# Supplied-tail state-norm estimate for the startup-ramped trajectory

This module translates the accepted storage estimate into the actual sup
product norm on `PointMassState`.  It performs no new ODE or trajectory work:
the supplied-tail continuity and realized-field derivative are passed directly
to `rampedCrossStorage_trajectory_storage_exp_decay`.

The same scalar budget is also shown to persist when a later start `T` is
chosen after an earlier budget start `T₀`; this is only coefficient monotonicity,
not a uniform trajectory or stability theorem.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib.ComStartupRampSuppliedTailNorm

open Ctrllib
open Ctrllib.ComStartupRampComposition
open Ctrllib.ComStartupRampCrossTermStorage
open Ctrllib.ComStartupRampTrajectoryAdapter

/-- The accepted late-start budget persists when the start time is moved right. -/
theorem rampedCrossStorage_tail_budget_persists
    (m τ d k β T₀ T κ μ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    (hT₀ : 0 ≤ T₀) (hβ : 0 < β) (hκ : 0 < κ) (hμ : 0 < μ)
    (hT₀T : T₀ ≤ T)
    (hA₀ : κ + (Real.exp (-T₀ / τ) * k + β * d / m) * μ / 2
      ≤ (1 - Real.exp (-T₀ / τ)) * d - β)
    (hB₀ : κ + (Real.exp (-T₀ / τ) * k + β * d / m) / (2 * μ)
      ≤ β * (1 - Real.exp (-T₀ / τ)) * k / m) :
    κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2
        ≤ (1 - Real.exp (-T / τ)) * d - β ∧
      κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
        ≤ β * (1 - Real.exp (-T / τ)) * k / m := by
  have hT : 0 ≤ T := hT₀.trans hT₀T
  have hq : Real.exp (-T / τ) ≤ Real.exp (-T₀ / τ) := by
    have hdiv : T₀ / τ ≤ T / τ := (div_le_div_iff_of_pos_right hτ).2 hT₀T
    simpa only [neg_div] using Real.exp_le_exp.mpr (neg_le_neg hdiv)
  have hq_nonneg : 0 ≤ Real.exp (-T / τ) := (Real.exp_pos _).le
  have hq₀_nonneg : 0 ≤ Real.exp (-T₀ / τ) := (Real.exp_pos _).le
  have hD : Real.exp (-T / τ) * k + β * d / m ≤
      Real.exp (-T₀ / τ) * k + β * d / m := by
    exact add_le_add (mul_le_mul_of_nonneg_right hq hk.le) le_rfl
  have hAcoef : (1 - Real.exp (-T₀ / τ)) * d - β ≤
      (1 - Real.exp (-T / τ)) * d - β := by
    have hqsub : 1 - Real.exp (-T₀ / τ) ≤ 1 - Real.exp (-T / τ) := by linarith
    exact sub_le_sub_right (mul_le_mul_of_nonneg_right hqsub hd.le) β
  have hBcoef : β * (1 - Real.exp (-T₀ / τ)) * k / m ≤
      β * (1 - Real.exp (-T / τ)) * k / m := by
    have hqsub : 1 - Real.exp (-T₀ / τ) ≤ 1 - Real.exp (-T / τ) := by linarith
    have hβsub : β * (1 - Real.exp (-T₀ / τ)) ≤
        β * (1 - Real.exp (-T / τ)) :=
      mul_le_mul_of_nonneg_left hqsub hβ.le
    have hβsubk := mul_le_mul_of_nonneg_right hβsub hk.le
    exact (div_le_div_iff_of_pos_right hm).2 hβsubk
  have hDμ : (Real.exp (-T / τ) * k + β * d / m) * μ / 2 ≤
      (Real.exp (-T₀ / τ) * k + β * d / m) * μ / 2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD hμ.le) (by norm_num)
  have hDμ' : (Real.exp (-T / τ) * k + β * d / m) / (2 * μ) ≤
      (Real.exp (-T₀ / τ) * k + β * d / m) / (2 * μ) := by
    exact div_le_div_of_nonneg_right hD (by positivity)
  have hκ_nonneg : 0 ≤ κ := hκ.le
  constructor
  · linarith [hA₀, hAcoef, hDμ, hκ_nonneg]
  · linarith [hB₀, hBcoef, hDμ', hκ_nonneg]

/-- Exponential norm bound for the supplied realized tail trajectory. -/
theorem rampedCrossStorage_supplied_tail_norm_exp_bound
    (m τ d k β T κ μ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    (hT : 0 ≤ T) (hβ : 0 < β) (hβstorage : β < min m k)
    (hκ : 0 < κ) (hμ : 0 < μ)
    (hA : κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2
      ≤ (1 - Real.exp (-T / τ)) * d - β)
    (hB : κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
      ≤ β * (1 - Real.exp (-T / τ)) * k / m)
    {z : ℝ → PointMassState}
    (hzc : ContinuousOn z (Ici T))
    (hzdot : ∀ t ∈ Ici T,
      HasDerivAt z (rampedPointMassField m τ d k (t, z t)) t)
    {t : ℝ} (ht : T ≤ t) :
    ‖z t‖ ≤ Real.sqrt ((max m k + β) / ((min m k - β) / 2)) * ‖z T‖ *
      Real.exp (-(κ / (2 * (max m k + β))) * (t - T)) := by
  let c_lo : ℝ := (min m k - β) / 2
  let c_hi : ℝ := max m k + β
  have hc_lo : 0 < c_lo := by
    dsimp [c_lo]
    linarith [hβstorage]
  have hc_hi : 0 < c_hi := by
    dsimp [c_hi]
    positivity
  have hc_lo_eq : c_lo = min m k / 2 - β / 2 := by
    dsimp [c_lo]
    ring
  have hstorage := rampedCrossStorage_trajectory_storage_exp_decay m τ d k β T κ μ hm hτ hd hk
    hT hβ hβstorage hκ hμ hA hB hzc hzdot t (mem_Ici.mpr ht)
  have hsand_t := rampedCrossStorage_norm_sandwich m k β hm hk hβ.le hβstorage (z t)
  have hsand_T := rampedCrossStorage_norm_sandwich m k β hm hk hβ.le hβstorage (z T)
  have hlow_t : c_lo * ‖z t‖ ^ 2 ≤ rampedCrossStorage m k β (z t) := by
    rw [hc_lo_eq]
    exact hsand_t.1
  have hupper_T : rampedCrossStorage m k β (z T) ≤ c_hi * ‖z T‖ ^ 2 := by
    simpa [c_hi] using hsand_T.2
  have hnorm :=
    Ctrllib.norm_le_sqrt_ratio_mul_of_storage_decay
      (z := z t) (z0 := z T)
      (W := rampedCrossStorage m k β (z t))
      (W0 := rampedCrossStorage m k β (z T))
      (c_lo := c_lo) (c_hi := c_hi) (κ := κ) (Δ := t - T)
      (hc_lo := hc_lo) (hc_hi := hc_hi) (hlow := hlow_t) (hupper := hupper_T)
      (hdecay := by simpa [c_hi] using hstorage)
  simpa [c_lo, c_hi] using hnorm

end Ctrllib.ComStartupRampSuppliedTailNorm

#print axioms Ctrllib.ComStartupRampSuppliedTailNorm.rampedCrossStorage_tail_budget_persists
#print axioms Ctrllib.ComStartupRampSuppliedTailNorm.rampedCrossStorage_supplied_tail_norm_exp_bound
