/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonia Hoffman
-/
import Ctrllib.ComStartupRampCrossTermStorage
import Ctrllib.TrackingStrictBound

/-!
# Pointwise strict decay after startup ramping

For `qT = exp (-T / τ)`, set

`A = (1 - qT) * d - β`, `B = β * (1 - qT) * k / m`, and
`D = qT * k + β * d / m`.

This module proves the trajectory-free pointwise implication

`κ + D * μ / 2 ≤ A` and `κ + D / (2 * μ) ≤ B`

`⟹ rampedCrossStorageRate t z ≤ -κ (‖v‖² + ‖x‖²)` for `T ≤ t`.
The proof uses the existing ramp bounds, Cauchy--Schwarz, and `young_cross`.
The separate companion theorem keeps the storage coercivity assumptions and
conclusion explicit.  No trajectory, ODE, stability, convergence, or gain-wide
claim is made.
-/

open scoped InnerProductSpace

namespace Ctrllib.ComStartupRampCrossTermDecay

open Ctrllib
open Ctrllib.ComStartupRampComposition
open Ctrllib.ComStartupRampCrossTermStorage

/-- Late-time bounds for the exponential and startup ramp. -/
theorem late_ramp_exponential_bounds
    (τ T t : ℝ) (hτ : 0 < τ) (hT : 0 ≤ T) (hTt : T ≤ t) :
    Real.exp (-t / τ) ≤ Real.exp (-T / τ) ∧
      1 - Real.exp (-T / τ) ≤ ramp τ t ∧
      0 ≤ Real.exp (-t / τ) ∧ 0 ≤ ramp τ t ∧ ramp τ t ≤ 1 := by
  have ht : 0 ≤ t := hT.trans hTt
  have hr := ramp_bounds τ t hτ ht
  have hdiv : T / τ ≤ t / τ := (div_le_div_iff_of_pos_right hτ).2 hTt
  have hq : Real.exp (-t / τ) ≤ Real.exp (-T / τ) := by
    simpa only [neg_div] using Real.exp_le_exp.mpr (neg_le_neg hdiv)
  have hrt : 1 - Real.exp (-T / τ) ≤ ramp τ t := by
    dsimp [ramp]
    linarith
  exact ⟨hq, hrt, (Real.exp_pos _).le, hr.1, hr.2.le⟩

/-- Pointwise strict decay of the ramped cross-storage rate after time `T`. -/
theorem rampedCrossStorageRate_strict_decay
    (m τ d k β T κ μ : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    (hT : 0 ≤ T) (hβ : 0 < β) (hκ : 0 < κ) (hμ : 0 < μ)
    (hA : κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2
      ≤ (1 - Real.exp (-T / τ)) * d - β)
    (hB : κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
      ≤ β * (1 - Real.exp (-T / τ)) * k / m)
    {t : ℝ} (ht : T ≤ t) (z : PointMassState) :
    rampedCrossStorageRate m τ d k β t z ≤
      -κ * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := by
  have hlate := late_ramp_exponential_bounds τ T t hτ hT ht
  have hqT : 0 ≤ Real.exp (-T / τ) := (Real.exp_pos _).le
  have hκ_nonneg : 0 ≤ κ := hκ.le
  have hq : 0 ≤ Real.exp (-t / τ) := hlate.2.2.1
  have hr : 0 ≤ ramp τ t := hlate.2.2.2.1
  have hr_upper : ramp τ t ≤ 1 := hlate.2.2.2.2
  have hAcoeff : (1 - Real.exp (-T / τ)) * d - β ≤ ramp τ t * d - β := by
    have hmul := mul_le_mul_of_nonneg_right hlate.2.1 hd.le
    linarith
  have hBcoeff : β * (1 - Real.exp (-T / τ)) * k / m ≤
      β * ramp τ t * k / m := by
    have hβr : β * (1 - Real.exp (-T / τ)) ≤ β * ramp τ t :=
      mul_le_mul_of_nonneg_left hlate.2.1 hβ.le
    have hβrk := mul_le_mul_of_nonneg_right hβr hk.le
    exact (div_le_div_iff_of_pos_right hm).2 hβrk
  have hD : 0 ≤ Real.exp (-T / τ) * k + β * d / m := by positivity
  have hcross_coeff :
      |Real.exp (-t / τ) * k - β * ramp τ t * d / m| ≤
        Real.exp (-T / τ) * k + β * d / m := by
    have hqk : Real.exp (-t / τ) * k ≤ Real.exp (-T / τ) * k :=
      mul_le_mul_of_nonneg_right hlate.1 hk.le
    have hβrd : β * ramp τ t * d ≤ β * d := by
      have hβr := mul_le_mul_of_nonneg_left hr_upper hβ.le
      have hβrd' := mul_le_mul_of_nonneg_right hβr hd.le
      simpa [mul_assoc] using hβrd'
    have hβrd_div : β * ramp τ t * d / m ≤ β * d / m :=
      (div_le_div_iff_of_pos_right hm).2 hβrd
    calc
      |Real.exp (-t / τ) * k - β * ramp τ t * d / m| ≤
          |Real.exp (-t / τ) * k| + |β * ramp τ t * d / m| :=
        abs_sub _ _
      _ = Real.exp (-t / τ) * k + β * ramp τ t * d / m := by
        rw [abs_of_nonneg (mul_nonneg hq hk.le),
          abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg hβ.le hr) hd.le) hm.le)]
      _ ≤ Real.exp (-T / τ) * k + β * d / m := by
        exact add_le_add hqk hβrd_div
  have hinner : |⟪z.2, z.1⟫_ℝ| ≤ ‖z.1‖ * ‖z.2‖ := by
    simpa [real_inner_comm] using abs_real_inner_le_norm z.1 z.2
  have hcross :
      (Real.exp (-t / τ) * k - β * ramp τ t * d / m) * ⟪z.2, z.1⟫_ℝ ≤
        (Real.exp (-T / τ) * k + β * d / m) * (‖z.1‖ * ‖z.2‖) := by
    calc
      (Real.exp (-t / τ) * k - β * ramp τ t * d / m) * ⟪z.2, z.1⟫_ℝ ≤
          |Real.exp (-t / τ) * k - β * ramp τ t * d / m| *
            |⟪z.2, z.1⟫_ℝ| := by
        calc
          _ ≤ |(Real.exp (-t / τ) * k - β * ramp τ t * d / m) *
              ⟪z.2, z.1⟫_ℝ| := le_abs_self _
          _ = _ := by rw [abs_mul]
      _ ≤ (Real.exp (-T / τ) * k + β * d / m) * |⟪z.2, z.1⟫_ℝ| :=
        mul_le_mul_of_nonneg_right hcross_coeff (abs_nonneg _)
      _ ≤ (Real.exp (-T / τ) * k + β * d / m) * (‖z.1‖ * ‖z.2‖) :=
        mul_le_mul_of_nonneg_left hinner hD
  have hyoung := young_cross (C := Real.exp (-T / τ) * k + β * d / m)
    (lam := μ) (s := ‖z.1‖) (t := ‖z.2‖) hD hμ
  have hrate_v :
      -(ramp τ t * d - β) * ‖z.1‖ ^ 2 ≤
        -((1 - Real.exp (-T / τ)) * d - β) * ‖z.1‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hAcoeff (sq_nonneg ‖z.1‖)
    linarith
  have hrate_x :
      -β * ramp τ t * k / m * ‖z.2‖ ^ 2 ≤
        -(β * (1 - Real.exp (-T / τ)) * k / m) * ‖z.2‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hBcoeff (sq_nonneg ‖z.2‖)
    calc
      -β * ramp τ t * k / m * ‖z.2‖ ^ 2 =
          -(β * ramp τ t * k / m * ‖z.2‖ ^ 2) := by ring
      _ ≤ -(β * (1 - Real.exp (-T / τ)) * k / m * ‖z.2‖ ^ 2) :=
        neg_le_neg hmul
      _ = -(β * (1 - Real.exp (-T / τ)) * k / m) * ‖z.2‖ ^ 2 := by ring
  unfold rampedCrossStorageRate
  calc
    -(ramp τ t * d - β) * ‖z.1‖ ^ 2
          + (Real.exp (-t / τ) * k - β * ramp τ t * d / m) *
              ⟪z.2, z.1⟫_ℝ
          - β * ramp τ t * k / m * ‖z.2‖ ^ 2 ≤
        -((1 - Real.exp (-T / τ)) * d - β) * ‖z.1‖ ^ 2
          + (Real.exp (-T / τ) * k + β * d / m) * (‖z.1‖ * ‖z.2‖)
          - (β * (1 - Real.exp (-T / τ)) * k / m) * ‖z.2‖ ^ 2 := by
      nlinarith [hrate_v, hcross, hrate_x]
    _ ≤ -((1 - Real.exp (-T / τ)) * d - β) * ‖z.1‖ ^ 2
          + (Real.exp (-T / τ) * k + β * d / m) * μ / 2 * ‖z.1‖ ^ 2
          + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ) * ‖z.2‖ ^ 2
          - (β * (1 - Real.exp (-T / τ)) * k / m) * ‖z.2‖ ^ 2 := by
      nlinarith [hcross, hyoung]
    _ ≤ -κ * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := by
      have hA' :
          (Real.exp (-T / τ) * k + β * d / m) * μ / 2
              - ((1 - Real.exp (-T / τ)) * d - β) ≤ -κ := by
        linarith [hA]
      have hB' :
          (Real.exp (-T / τ) * k + β * d / m) / (2 * μ)
              - β * (1 - Real.exp (-T / τ)) * k / m ≤ -κ := by
        linarith [hB]
      have hAv := mul_le_mul_of_nonneg_right hA' (sq_nonneg ‖z.1‖)
      have hBx := mul_le_mul_of_nonneg_right hB' (sq_nonneg ‖z.2‖)
      nlinarith [hAv, hBx, hκ_nonneg]

/-- Strict decay together with the accepted coercive storage sandwich. -/
theorem rampedCrossStorageRate_strict_decay_with_storage
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
        -κ * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ∧
      ((min m k / 2 - β / 2) * ‖z‖ ^ 2 ≤ rampedCrossStorage m k β z ∧
        rampedCrossStorage m k β z ≤ (max m k + β) * ‖z‖ ^ 2) := by
  constructor
  · exact rampedCrossStorageRate_strict_decay m τ d k β T κ μ hm hτ hd hk hT hβ hκ hμ
      hA hB ht z
  · exact rampedCrossStorage_norm_sandwich m k β hm hk hβ.le hβstorage z

/-- A concrete feasible set of strict-decay constants (`m=d=k=τ=1`, `β=1/4`). -/
theorem concrete_feasible_parameter_example :
    let m : ℝ := 1
    let τ : ℝ := 1
    let d : ℝ := 1
    let k : ℝ := 1
    let β : ℝ := 1 / 4
    let T : ℝ := Real.log 10
    let κ : ℝ := 1 / 25
    let μ : ℝ := 1
    0 < m ∧ 0 < τ ∧ 0 < d ∧ 0 < k ∧ 0 ≤ T ∧ 0 < β ∧ β < min m k ∧ 0 < κ ∧ 0 < μ ∧
      κ + (Real.exp (-T / τ) * k + β * d / m) * μ / 2 ≤
        (1 - Real.exp (-T / τ)) * d - β ∧
      κ + (Real.exp (-T / τ) * k + β * d / m) / (2 * μ) ≤
        β * (1 - Real.exp (-T / τ)) * k / m := by
  have hlog : 0 ≤ Real.log (10 : ℝ) := Real.log_nonneg (by norm_num)
  have hexp : Real.exp (-Real.log (10 : ℝ) / 1) = (1 / 10 : ℝ) := by
    rw [div_one, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hexp' : Real.exp (-Real.log (10 : ℝ)) = (1 / 10 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  dsimp
  norm_num [hexp, hexp', hlog]

end Ctrllib.ComStartupRampCrossTermDecay

#print axioms Ctrllib.ComStartupRampCrossTermDecay.late_ramp_exponential_bounds
#print axioms Ctrllib.ComStartupRampCrossTermDecay.rampedCrossStorageRate_strict_decay
#print axioms Ctrllib.ComStartupRampCrossTermDecay.rampedCrossStorageRate_strict_decay_with_storage
#print axioms Ctrllib.ComStartupRampCrossTermDecay.concrete_feasible_parameter_example
