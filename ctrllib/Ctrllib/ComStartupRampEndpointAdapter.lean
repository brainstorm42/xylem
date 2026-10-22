/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonia Hoffman
-/
import Mathlib.Analysis.ODE.Basic
import Ctrllib.ProdNorm
import Ctrllib.ComStartupRampTrajectoryAdapter
import Ctrllib.StorageNormBound

/-!
# Endpoint-compatible forward adapter for the startup-ramped trajectory

This module keeps the accepted full-derivative APIs unchanged and adds a
forward endpoint interface using Mathlib's exact `IsIntegralCurveOn` predicate
on `Ici T`.  The endpoint therefore needs only a right derivative.  The
storage derivative is re-established with within-calculus at that endpoint;
the accepted pointwise decay, comparison-shift, norm, and filter inequalities
are reused for the quantitative conclusions.

This remains a supplied-trajectory adapter.  It makes no existence,
globality, uniqueness, or nonautonomous flow claim.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib.ComStartupRampEndpointAdapter

open Ctrllib
open Ctrllib.ComStartupRampComposition
open Ctrllib.ComStartupRampCrossTermStorage
open Ctrllib.ComStartupRampCrossTermDecay

private lemma continuous_rampedCrossStorage (m k β : ℝ) :
    Continuous (rampedCrossStorage m k β) := by
  unfold rampedCrossStorage
  fun_prop

private theorem rampedCrossStorage_hasDerivWithinAt_of_components
    (m τ d k β : ℝ) (hm : 0 < m) (_hτ : 0 < τ) (_hd : 0 < d) (_hk : 0 < k)
    {v x : ℝ → PointMassCoord} {vdot xdot : PointMassCoord} {S : Set ℝ} {t : ℝ}
    (hv : HasDerivWithinAt v vdot S t) (hx : HasDerivWithinAt x xdot S t)
    (hfield : (vdot, xdot) = rampedPointMassField m τ d k (t, (v t, x t))) :
    HasDerivWithinAt (fun s => rampedCrossStorage m k β (v s, x s))
      (rampedCrossStorageRate m τ d k β t (v t, x t)) S t := by
  have hvnorm : HasDerivWithinAt (fun s => ‖v s‖ ^ 2)
      (⟪v t, vdot⟫_ℝ + ⟪vdot, v t⟫_ℝ) S t := by
    simpa only [real_inner_self_eq_norm_sq] using hv.inner ℝ hv
  have hxnorm : HasDerivWithinAt (fun s => ‖x s‖ ^ 2)
      (⟪x t, xdot⟫_ℝ + ⟪xdot, x t⟫_ℝ) S t := by
    simpa only [real_inner_self_eq_norm_sq] using hx.inner ℝ hx
  have hbasev := hvnorm.const_mul (m / 2)
  have hbasex := hxnorm.const_mul (k / 2)
  have hcross := (hv.inner ℝ hx).const_mul β
  have hsum := hbasev.add (hbasex.add hcross)
  have hsum' : HasDerivWithinAt
      (fun s => rampedCrossStorage m k β (v s, x s))
      ((m / 2) * (⟪v t, vdot⟫_ℝ + ⟪vdot, v t⟫_ℝ) +
        (k / 2) * (⟪x t, xdot⟫_ℝ + ⟪xdot, x t⟫_ℝ) +
        β * (⟪v t, xdot⟫_ℝ + ⟪vdot, x t⟫_ℝ)) S t := by
    convert hsum using 1
    · funext s
      simp [rampedCrossStorage]
      ring_nf
    · ring
  apply hsum'.congr_deriv
  unfold rampedCrossStorageRate
  have hvdot : vdot = (rampedPointMassField m τ d k (t, (v t, x t))).1 := by
    simpa only [Prod.fst] using congrArg Prod.fst hfield
  have hxdot : xdot = (rampedPointMassField m τ d k (t, (v t, x t))).2 := by
    simpa only [Prod.snd] using congrArg Prod.snd hfield
  rw [hvdot, hxdot]
  dsimp [rampedPointMassField]
  rw [real_inner_comm (v t), real_inner_comm (v t), real_inner_comm (v t)]
  rw [show Real.exp (-t / τ) = 1 - ramp τ t by simp [ramp]]
  simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_neg_left, inner_neg_right]
  field_simp [ne_of_gt hm]
  ring_nf

private theorem rampedCrossStorage_hasDerivWithinAt_of_realized
    (m τ d k β T : ℝ) (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    {z : ℝ → PointMassState} {t : ℝ} (ht : T ≤ t)
    (hz : HasDerivWithinAt z (rampedPointMassField m τ d k (t, z t)) (Ici T) t) :
    HasDerivWithinAt (fun s => rampedCrossStorage m k β (z s))
      (rampedCrossStorageRate m τ d k β t (z t)) (Ici t) t := by
  have hz' : HasDerivWithinAt z (rampedPointMassField m τ d k (t, z t)) (Ici t) t :=
    hz.mono (Ici_subset_Ici.mpr ht)
  have hv : HasDerivWithinAt (fun s => (z s).1)
      ((rampedPointMassField m τ d k (t, z t)).1) (Ici t) t := by
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
      using hz'.hasFDerivWithinAt.fst.hasDerivWithinAt
  have hx : HasDerivWithinAt (fun s => (z s).2)
      ((rampedPointMassField m τ d k (t, z t)).2) (Ici t) t := by
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
      using hz'.hasFDerivWithinAt.snd.hasDerivWithinAt
  exact rampedCrossStorage_hasDerivWithinAt_of_components m τ d k β hm hτ hd hk hv hx (by simp)

private theorem rampedCrossStorageRate_le_storage_decay
    (m τ d k β T κ μ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    (hT : 0 ≤ T) (hβ : 0 < β) (hβstorage : β < min m k)
    (hκ : 0 < κ) (hμ : 0 < μ)
    (hA : κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2
      ≤ (1 - Real.exp (-T / τ)) * d - β)
    (hB : κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
      ≤ β * (1 - Real.exp (-T / τ)) * k / m)
    {t : ℝ} (ht : T ≤ t) (z : PointMassState) :
    rampedCrossStorageRate m τ d k β t z ≤
      -(κ / (max m k + β)) * rampedCrossStorage m k β z := by
  have hrate := rampedCrossStorageRate_strict_decay_with_storage m τ d k β T κ μ hm hτ hd hk
    hT hβ hβstorage hκ hμ hA hB ht z
  have hsum : -κ * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ≤ -κ * ‖z‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left (prod_norm_sq_le_sum_sq z) hκ.le
    linarith
  have hsand := rampedCrossStorage_norm_sandwich m k β hm hk hβ.le hβstorage z
  have hc_hi : 0 < max m k + β := by positivity
  have hupper : rampedCrossStorage m k β z ≤ (max m k + β) * ‖z‖ ^ 2 := hsand.2
  have hmul := mul_le_mul_of_nonneg_left hupper
    (div_nonneg hκ.le hc_hi.le)
  have hscale : -κ * ‖z‖ ^ 2 ≤
      -(κ / (max m k + β)) * rampedCrossStorage m k β z := by
    calc
      -κ * ‖z‖ ^ 2 =
          -(κ / (max m k + β) * ((max m k + β) * ‖z‖ ^ 2)) := by
            field_simp [ne_of_gt hc_hi]
      _ ≤ -(κ / (max m k + β) * rampedCrossStorage m k β z) := neg_le_neg hmul
      _ = -(κ / (max m k + β)) * rampedCrossStorage m k β z := by ring
  exact hrate.1.trans (hsum.trans hscale)

/-- Convert a full-derivative realization into the endpoint-compatible predicate. -/
theorem isIntegralCurveOn_of_hasDerivAt
    (m τ d k : ℝ) {T : ℝ} {z : ℝ → PointMassState}
    (hzdot : ∀ t ∈ Ici T,
      HasDerivAt z (rampedPointMassField m τ d k (t, z t)) t) :
    IsIntegralCurveOn z (fun t z => rampedPointMassField m τ d k (t, z)) (Ici T) := by
  intro t ht
  exact (hzdot t ht).hasDerivWithinAt

/-- Storage decay for the exact right-derivative `IsIntegralCurveOn` interface. -/
theorem rampedCrossStorage_trajectory_storage_exp_decay_within
    (m τ d k β T κ μ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    (hT : 0 ≤ T) (hβ : 0 < β) (hβstorage : β < min m k)
    (hκ : 0 < κ) (hμ : 0 < μ)
    (hA : κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2
      ≤ (1 - Real.exp (-T / τ)) * d - β)
    (hB : κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
      ≤ β * (1 - Real.exp (-T / τ)) * k / m)
    {z : ℝ → PointMassState}
    (hzdot : IsIntegralCurveOn z
      (fun t z => rampedPointMassField m τ d k (t, z)) (Ici T)) :
    ∀ t ∈ Ici T,
      rampedCrossStorage m k β (z t) ≤
        rampedCrossStorage m k β (z T) *
          Real.exp (-(κ / (max m k + β)) * (t - T)) := by
  have hzc : ContinuousOn z (Ici T) := hzdot.continuousOn
  intro t ht
  have hWc : ContinuousOn (fun s => rampedCrossStorage m k β (z s)) (Icc T t) := by
    exact (continuous_rampedCrossStorage m k β).continuousOn.comp (hzc.mono Icc_subset_Ici_self)
      (fun _ _ => mem_univ _)
  have hWderiv : ∀ s ∈ Ico T t,
      HasDerivWithinAt (fun u => rampedCrossStorage m k β (z u))
        (rampedCrossStorageRate m τ d k β s (z s)) (Ici s) s := by
    intro s hs
    exact rampedCrossStorage_hasDerivWithinAt_of_realized m τ d k β T hm hτ hd hk hs.1
      (hzdot s (mem_Ici.mpr hs.1))
  have hbound : ∀ s ∈ Ico T t,
      rampedCrossStorageRate m τ d k β s (z s) ≤
        -(κ / (max m k + β)) * rampedCrossStorage m k β (z s) := by
    intro s hs
    exact rampedCrossStorageRate_le_storage_decay m τ d k β T κ μ hm hτ hd hk hT hβ
      hβstorage hκ hμ hA hB hs.1 (z s)
  have hgron : rampedCrossStorage m k β (z t) ≤
      gronwallBound (rampedCrossStorage m k β (z T))
        (-(κ / (max m k + β))) 0 (t - T) :=
    comparison_shift hWc hWderiv
      (fun s hs => by simpa using hbound s hs) t ⟨ht, le_rfl⟩
  rwa [gronwallBound_ε0] at hgron

/-- The full-derivative API feeds the endpoint-compatible storage adapter. -/
theorem rampedCrossStorage_trajectory_storage_exp_decay_of_hasDerivAt
    (m τ d k β T κ μ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    (hT : 0 ≤ T) (hβ : 0 < β) (hβstorage : β < min m k)
    (hκ : 0 < κ) (hμ : 0 < μ)
    (hA : κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2
      ≤ (1 - Real.exp (-T / τ)) * d - β)
    (hB : κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
      ≤ β * (1 - Real.exp (-T / τ)) * k / m)
    {z : ℝ → PointMassState}
    (_hzc : ContinuousOn z (Ici T))
    (hzdot : ∀ t ∈ Ici T,
      HasDerivAt z (rampedPointMassField m τ d k (t, z t)) t) :
    ∀ t ∈ Ici T,
      rampedCrossStorage m k β (z t) ≤
        rampedCrossStorage m k β (z T) *
          Real.exp (-(κ / (max m k + β)) * (t - T)) := by
  exact rampedCrossStorage_trajectory_storage_exp_decay_within m τ d k β T κ μ hm hτ hd hk hT
    hβ hβstorage hκ hμ hA hB (isIntegralCurveOn_of_hasDerivAt m τ d k hzdot)

/-- Exponential norm decay under the right-derivative endpoint interface. -/
theorem rampedCrossStorage_supplied_tail_norm_exp_bound_within
    (m τ d k β T κ μ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    (hT : 0 ≤ T) (hβ : 0 < β) (hβstorage : β < min m k)
    (hκ : 0 < κ) (hμ : 0 < μ)
    (hA : κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2
      ≤ (1 - Real.exp (-T / τ)) * d - β)
    (hB : κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
      ≤ β * (1 - Real.exp (-T / τ)) * k / m)
    {z : ℝ → PointMassState}
    (hzdot : IsIntegralCurveOn z
      (fun t z => rampedPointMassField m τ d k (t, z)) (Ici T))
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
  have hstorage :=
    rampedCrossStorage_trajectory_storage_exp_decay_within m τ d k β T κ μ hm hτ hd hk hT hβ
      hβstorage hκ hμ hA hB hzdot t (mem_Ici.mpr ht)
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

/-- Convergence of a supplied endpoint-compatible forward trajectory. -/
theorem rampedCrossStorage_trajectory_tendsto_zero_within
    (m τ d k β T κ μ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    (hT : 0 ≤ T) (hβ : 0 < β) (hβstorage : β < min m k)
    (hκ : 0 < κ) (hμ : 0 < μ)
    (hA : κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2
      ≤ (1 - Real.exp (-T / τ)) * d - β)
    (hB : κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
      ≤ β * (1 - Real.exp (-T / τ)) * k / m)
    {z : ℝ → PointMassState}
    (hzdot : IsIntegralCurveOn z
      (fun t z => rampedPointMassField m τ d k (t, z)) (Ici T)) :
    Tendsto z atTop (𝓝 0) := by
  have ha : 0 < κ / (2 * (max m k + β)) := by positivity
  have hlin : Tendsto (fun t : ℝ => t - T) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T) tendsto_id
  have harg : Tendsto (fun t : ℝ => -(κ / (2 * (max m k + β))) * (t - T)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr ha)).mpr hlin
  have hexp : Tendsto
      (fun t : ℝ => Real.exp (-(κ / (2 * (max m k + β))) * (t - T))) atTop (𝓝 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr harg
  have hupper : Tendsto
      (fun t : ℝ => Real.sqrt ((max m k + β) / ((min m k - β) / 2)) * ‖z T‖ *
        Real.exp (-(κ / (2 * (max m k + β))) * (t - T))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul
      (Real.sqrt ((max m k + β) / ((min m k - β) / 2)) * ‖z T‖)
  have hnorm_zero : Tendsto (fun t : ℝ => ‖z t‖) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop T] with t ht
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop T] with t ht
      exact rampedCrossStorage_supplied_tail_norm_exp_bound_within m τ d k β T κ μ hm hτ hd hk
        hT hβ hβstorage hκ hμ hA hB hzdot (mem_Ici.mpr ht)
    · exact hupper
  apply (NormedAddGroup.tendsto_nhds_zero).2
  intro ε hε
  have hnorm_eventually := (NormedAddGroup.tendsto_nhds_zero).1 hnorm_zero ε hε
  simpa using hnorm_eventually

/-- The zero trajectory is a valid right-derivative supplied trajectory. -/
theorem zero_isIntegralCurveOn_rampedPointMassField (m τ d k T : ℝ) :
    IsIntegralCurveOn (fun _ : ℝ => (0 : PointMassState))
      (fun t z => rampedPointMassField m τ d k (t, z)) (Ici T) := by
  intro t ht
  have hz : HasDerivAt (fun _ : ℝ => (0 : PointMassState)) 0 t := hasDerivAt_const t 0
  convert hz.hasDerivWithinAt using 1
  simp [rampedPointMassField]

end Ctrllib.ComStartupRampEndpointAdapter

#print axioms Ctrllib.ComStartupRampEndpointAdapter.isIntegralCurveOn_of_hasDerivAt
#print axioms Ctrllib.ComStartupRampEndpointAdapter.rampedCrossStorage_trajectory_storage_exp_decay_within
#print axioms Ctrllib.ComStartupRampEndpointAdapter.rampedCrossStorage_trajectory_storage_exp_decay_of_hasDerivAt
#print axioms Ctrllib.ComStartupRampEndpointAdapter.rampedCrossStorage_supplied_tail_norm_exp_bound_within
#print axioms Ctrllib.ComStartupRampEndpointAdapter.rampedCrossStorage_trajectory_tendsto_zero_within
#print axioms Ctrllib.ComStartupRampEndpointAdapter.zero_isIntegralCurveOn_rampedPointMassField
