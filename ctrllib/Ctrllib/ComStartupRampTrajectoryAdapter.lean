/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonia Hoffman
-/
import Ctrllib.ComStartupRampCrossTermDecay
import Ctrllib.Cascade
import Ctrllib.CoupledSandwich
import Ctrllib.ProdNorm
import Ctrllib.TimeVaryingComparison

/-!
# Supplied-tail trajectory adapter for the ramped cross-storage

This module consumes a supplied trajectory on a tail `[T, ∞)` whose derivative
is explicitly realized by the nonautonomous `rampedPointMassField`.  The
accepted cross-storage derivative and strict-decay lemmas then feed the
existing scalar `comparison_shift` API, restarted at `T`.

The resulting quantitative storage estimate and `z t → 0` conclusion are
trajectory-level consequences only.  Existence, globality, uniqueness, and
any nonautonomous `LyapStable` theorem remain explicit downstream obligations;
none is hidden in this adapter.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib.ComStartupRampTrajectoryAdapter

open Ctrllib
open Ctrllib.ComStartupRampComposition
open Ctrllib.ComStartupRampCrossTermStorage
open Ctrllib.ComStartupRampCrossTermDecay

private lemma continuous_rampedCrossStorage (m k β : ℝ) :
    Continuous (rampedCrossStorage m k β) := by
  unfold rampedCrossStorage
  fun_prop

private theorem rampedCrossStorage_hasDerivAt_of_realized
    (m τ d k β : ℝ) (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    {z : ℝ → PointMassState} {t : ℝ}
    (hz : HasDerivAt z (rampedPointMassField m τ d k (t, z t)) t) :
    HasDerivAt (fun s => rampedCrossStorage m k β (z s))
      (rampedCrossStorageRate m τ d k β t (z t)) t := by
  have hv : HasDerivAt (fun s => (z s).1)
      ((rampedPointMassField m τ d k (t, z t)).1) t := by
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
      using hz.hasFDerivAt.fst.hasDerivAt
  have hx : HasDerivAt (fun s => (z s).2)
      ((rampedPointMassField m τ d k (t, z t)).2) t := by
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
      using hz.hasFDerivAt.snd.hasDerivAt
  simpa using
    rampedCrossStorage_hasDerivAt m τ d k β hm hτ hd hk hv hx (by simp)

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
  have hrate := rampedCrossStorageRate_strict_decay m τ d k β T κ μ hm hτ hd hk hT hβ hκ hμ
    hA hB ht z
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
  exact hrate.trans (hsum.trans hscale)

private theorem tail_comparison_exp_decay
    {W W' : ℝ → ℝ} {T a : ℝ}
    (hWc : ContinuousOn W (Ici T))
    (hWderiv : ∀ t ∈ Ici T, HasDerivWithinAt W (W' t) (Ici t) t)
    (hbound : ∀ t ∈ Ici T, W' t ≤ -a * W t) :
    ∀ t ∈ Ici T, W t ≤ W T * Real.exp (-a * (t - T)) := by
  intro t ht
  have hsub : Icc T t ⊆ Ici T := Icc_subset_Ici_self
  have hgron : W t ≤ gronwallBound (W T) (-a) 0 (t - T) :=
    comparison_shift (v := W) (v' := W') (a := a) (c := 0)
      (hWc.mono hsub)
      (fun s hs => hWderiv s (mem_Ici.mpr hs.1))
      (fun s hs => by simpa using hbound s (mem_Ici.mpr hs.1))
      t ⟨ht, le_rfl⟩
  rwa [gronwallBound_ε0] at hgron

/-- Quantitative storage decay for a supplied realized trajectory on `[T, ∞)`. -/
theorem rampedCrossStorage_trajectory_storage_exp_decay
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
      HasDerivAt z (rampedPointMassField m τ d k (t, z t)) t) :
    ∀ t ∈ Ici T,
      rampedCrossStorage m k β (z t) ≤
        rampedCrossStorage m k β (z T) *
          Real.exp (-(κ / (max m k + β)) * (t - T)) := by
  have hWc : ContinuousOn (fun t => rampedCrossStorage m k β (z t)) (Ici T) := by
    exact (continuous_rampedCrossStorage m k β).continuousOn.comp hzc
      (fun _ _ => mem_univ _)
  have hWderiv : ∀ t ∈ Ici T,
      HasDerivWithinAt (fun s => rampedCrossStorage m k β (z s))
        (rampedCrossStorageRate m τ d k β t (z t)) (Ici t) t := by
    intro t ht
    exact (rampedCrossStorage_hasDerivAt_of_realized m τ d k β hm hτ hd hk
      (hzdot t ht)).hasDerivWithinAt
  have hbound : ∀ t ∈ Ici T,
      rampedCrossStorageRate m τ d k β t (z t) ≤
        -(κ / (max m k + β)) * rampedCrossStorage m k β (z t) := by
    intro t ht
    exact rampedCrossStorageRate_le_storage_decay m τ d k β T κ μ hm hτ hd hk hT hβ
      hβstorage hκ hμ hA hB ht (z t)
  exact tail_comparison_exp_decay (a := κ / (max m k + β)) hWc hWderiv
    hbound

/-- A supplied realized tail trajectory converges to the origin under the accepted budget. -/
theorem rampedCrossStorage_trajectory_tendsto_zero
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
      HasDerivAt z (rampedPointMassField m τ d k (t, z t)) t) :
    Tendsto z atTop (𝓝 0) := by
  let W : ℝ → ℝ := fun t => rampedCrossStorage m k β (z t)
  let c_lo : ℝ := (min m k - β) / 2
  let c_hi : ℝ := max m k + β
  have hc_lo : 0 < c_lo := by
    dsimp [c_lo]
    have hmin : β < min m k := hβstorage
    linarith
  have hc_lo_eq : c_lo = min m k / 2 - β / 2 := by
    dsimp [c_lo]
    ring
  have hc_hi : 0 < c_hi := by
    dsimp [c_hi]
    positivity
  have hWexp : ∀ t ∈ Ici T,
      W t ≤ W T * Real.exp (-(κ / c_hi) * (t - T)) := by
    intro t ht
    simpa [W, c_hi] using
      (rampedCrossStorage_trajectory_storage_exp_decay m τ d k β T κ μ hm hτ hd hk hT hβ
        hβstorage hκ hμ hA hB hzc hzdot t ht)
  have hWnn : ∀ t ∈ Ici T, 0 ≤ W t := by
    intro t ht
    have hsand := rampedCrossStorage_norm_sandwich m k β hm hk hβ.le hβstorage (z t)
    have hlow : c_lo * ‖z t‖ ^ 2 ≤ W t := by
      change c_lo * ‖z t‖ ^ 2 ≤ rampedCrossStorage m k β (z t)
      rw [hc_lo_eq]
      exact hsand.1
    exact (mul_nonneg hc_lo.le (sq_nonneg _)).trans hlow
  have ha : 0 < κ / c_hi := div_pos hκ hc_hi
  have htime : Tendsto (fun t : ℝ => t - T) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T) tendsto_id
  have harg : Tendsto (fun t : ℝ => -(κ / c_hi) * (t - T)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr ha)).mpr htime
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(κ / c_hi) * (t - T))) atTop (𝓝 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr harg
  have hupper : Tendsto (fun t => W T * Real.exp (-(κ / c_hi) * (t - T))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul (W T)
  have hWzero : Tendsto W atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop T] with t ht
      exact hWnn t (mem_Ici.mpr ht)
    · filter_upwards [eventually_ge_atTop T] with t ht
      exact hWexp t (mem_Ici.mpr ht)
    · exact hupper
  have hα : IsClassKInfinity (fun s : ℝ => c_lo * s ^ 2) :=
    isClassKInfinity_sq.const_mul hc_lo
  have hsand : ∀ᶠ t in atTop, (fun s : ℝ => c_lo * s ^ 2) ‖z t‖ ≤ W t := by
    filter_upwards [eventually_ge_atTop T] with t ht
    have hsand' := rampedCrossStorage_norm_sandwich m k β hm hk hβ.le hβstorage (z t)
    change c_lo * ‖z t‖ ^ 2 ≤ rampedCrossStorage m k β (z t)
    rw [hc_lo_eq]
    exact hsand'.1
  exact hα.tendsto_zero_of_sandwich hsand hWzero

end Ctrllib.ComStartupRampTrajectoryAdapter

#print axioms Ctrllib.ComStartupRampTrajectoryAdapter.rampedCrossStorage_trajectory_storage_exp_decay
#print axioms Ctrllib.ComStartupRampTrajectoryAdapter.rampedCrossStorage_trajectory_tendsto_zero
