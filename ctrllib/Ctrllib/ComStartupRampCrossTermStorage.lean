/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonia Hoffman
-/
import Ctrllib.ComStartupRampFieldResidual
import Ctrllib.PointMassComFlow
import Ctrllib.TrackingStorageDerivative
import Ctrllib.TrackingStrictBound
import Ctrllib.ProdNorm

/-!
# Cross-term storage for the startup-ramped point-mass field

For the velocity-first state `z = (v, x)`, this module defines the classical
cross-term storage

`Wβ(v,x) = m/2 ‖v‖² + k/2 ‖x‖² + β ⟪v,x⟫`.

The derivative theorem is conditional on supplied differentiable paths and an
explicit realization of `rampedPointMassField`; it is not an ODE existence,
flow, stability, or convergence theorem.  The storage sandwich reuses the
generic `strict_storage_sandwich` at scalar identity matrices, then translates
its component-square bounds to the actual sup product norm on `PointMassState`.
The generic `blockLyap_hasDerivAt` calculus bridge remains the corresponding
base-storage interface, but its matrix-path premise cannot be instantiated by
the constant scalar matrix here because this checkout has no normed-matrix
instance; the point-mass derivative is therefore discharged directly with
`HasDerivAt.inner`.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib.ComStartupRampCrossTermStorage

open Matrix
open Ctrllib.ComStartupRampComposition

/-! ## Storage and scalar identities -/

/-- The cross-term Lyapunov candidate for the velocity-first point-mass state. -/
noncomputable def rampedCrossStorage (m k β : ℝ) (z : PointMassState) : ℝ :=
  (m / 2) * ‖z.1‖ ^ 2 + (k / 2) * ‖z.2‖ ^ 2 + β * ⟪z.1, z.2⟫_ℝ

/-- The exact scalar rate expression produced by the ramped field. -/
noncomputable def rampedCrossStorageRate
    (m τ d k β t : ℝ) (z : PointMassState) : ℝ :=
  -(ramp τ t * d - β) * ‖z.1‖ ^ 2
    + (Real.exp (-t / τ) * k - β * ramp τ t * d / m) * ⟪z.2, z.1⟫_ℝ
    - β * ramp τ t * k / m * ‖z.2‖ ^ 2

private lemma euclidean_self_dot (v : PointMassCoord) :
    v.ofLp ⬝ᵥ v.ofLp = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

private lemma euclidean_cross_dot (v x : PointMassCoord) :
    x.ofLp ⬝ᵥ v.ofLp = ⟪v, x⟫_ℝ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- At `β = 0`, the rate is the ordinary mechanical-energy rate of the ramped field. -/
theorem rampedCrossStorageRate_beta_zero
    (m τ d k t : ℝ) (z : PointMassState) :
    rampedCrossStorageRate m τ d k 0 t z =
      -(ramp τ t * d) * ‖z.1‖ ^ 2
        + Real.exp (-t / τ) * k * ⟪z.2, z.1⟫_ℝ := by
  simp [rampedCrossStorageRate]

/-- At startup, the derivative expression is `k⟪x,v⟫ + β‖v‖²`. -/
theorem rampedCrossStorageRate_at_zero
    (m τ d k β : ℝ) (z : PointMassState) :
    rampedCrossStorageRate m τ d k β 0 z =
      k * ⟪z.2, z.1⟫_ℝ + β * ‖z.1‖ ^ 2 := by
  simp [rampedCrossStorageRate, ramp_zero]
  ring

/-- The formal nominal-coefficient limit `r = 1`, `q = 0` of the rate expression. -/
theorem rampedCrossStorageRate_nominal
    (m d k β : ℝ) (z : PointMassState) :
    (-(1 * d - β) * ‖z.1‖ ^ 2
        + (0 * k - β * 1 * d / m) * ⟪z.2, z.1⟫_ℝ
        - β * 1 * k / m * ‖z.2‖ ^ 2) =
      -(d - β) * ‖z.1‖ ^ 2
        - β * d / m * ⟪z.2, z.1⟫_ℝ
        - β * k / m * ‖z.2‖ ^ 2 := by
  ring

/-- The storage vanishes at the zero state, independently of the gains. -/
theorem rampedCrossStorage_zero (m k β : ℝ) :
    rampedCrossStorage m k β (0 : PointMassState) = 0 := by
  simp [rampedCrossStorage]

/-- The rate vanishes at the zero state. -/
theorem rampedCrossStorageRate_zero
    (m τ d k β t : ℝ) :
    rampedCrossStorageRate m τ d k β t (0 : PointMassState) = 0 := by
  simp [rampedCrossStorageRate]

/-! ## Derivative along a supplied realized ramped trajectory -/

set_option linter.unusedVariables false in
/--
The exact derivative of `rampedCrossStorage` along a supplied ramped trajectory.

The state order is explicitly `(v, x)`.  The positive assumptions are kept in
the physical interface even though only `m > 0` is needed to clear the mass
denominator in this algebraic identity.  The premise `hfield` is the supplied
trajectory realization; no existence or uniqueness theorem is hidden here.
-/
theorem rampedCrossStorage_hasDerivAt
    (m τ d k β : ℝ) (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    {v x : ℝ → PointMassCoord} {vdot xdot : PointMassCoord} {t : ℝ}
    (hv : HasDerivAt v vdot t) (hx : HasDerivAt x xdot t)
    (hfield : (vdot, xdot) = rampedPointMassField m τ d k (t, (v t, x t))) :
    HasDerivAt (fun s => rampedCrossStorage m k β (v s, x s))
      (rampedCrossStorageRate m τ d k β t (v t, x t)) t := by
  have hvnorm : HasDerivAt (fun s => ‖v s‖ ^ 2)
      (⟪v t, vdot⟫_ℝ + ⟪vdot, v t⟫_ℝ) t := by
    simpa only [real_inner_self_eq_norm_sq] using hv.inner ℝ hv
  have hxnorm : HasDerivAt (fun s => ‖x s‖ ^ 2)
      (⟪x t, xdot⟫_ℝ + ⟪xdot, x t⟫_ℝ) t := by
    simpa only [real_inner_self_eq_norm_sq] using hx.inner ℝ hx
  have hbasev := hvnorm.const_mul (m / 2)
  have hbasex := hxnorm.const_mul (k / 2)
  have hcross := (hv.inner ℝ hx).const_mul β
  have hsum := hbasev.add (hbasex.add hcross)
  have hsum' : HasDerivAt
      (fun s => rampedCrossStorage m k β (v s, x s))
      ((m / 2) * (⟪v t, vdot⟫_ℝ + ⟪vdot, v t⟫_ℝ) +
        (k / 2) * (⟪x t, xdot⟫_ℝ + ⟪xdot, x t⟫_ℝ) +
        β * (⟪v t, xdot⟫_ℝ + ⟪vdot, x t⟫_ℝ)) t := by
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

/-- One-sided derivative form for comparison arguments on `Ici t`. -/
theorem rampedCrossStorage_hasDerivWithinAt
    (m τ d k β : ℝ) (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hk : 0 < k)
    {v x : ℝ → PointMassCoord} {vdot xdot : PointMassCoord} {t : ℝ}
    (hv : HasDerivAt v vdot t) (hx : HasDerivAt x xdot t)
    (hfield : (vdot, xdot) = rampedPointMassField m τ d k (t, (v t, x t))) :
    HasDerivWithinAt (fun s => rampedCrossStorage m k β (v s, x s))
      (rampedCrossStorageRate m τ d k β t (v t, x t)) (Ici t) t :=
  (rampedCrossStorage_hasDerivAt m τ d k β hm hτ hd hk hv hx hfield).hasDerivWithinAt

/-! ## Coercive and upper storage bounds -/

private lemma scalar_diagonal_mulVec (a : ℝ) (w : Fin 3 → ℝ) :
    Matrix.diagonal (fun _ : Fin 3 => a) *ᵥ w = a • w := by
  ext i
  rw [Matrix.mulVec_diagonal]
  simp

private lemma scalar_storage_eq_strictStorage
    (m k β : ℝ) (hm : 0 < m) (hk : 0 < k) (z : PointMassState) :
    strictStorage (Matrix.scalar (Fin 3) m) (Matrix.scalar (Fin 3) k)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) (β / (m * k)) z.1.ofLp z.2.ofLp =
      rampedCrossStorage m k β z := by
  simp only [strictStorage, blockLyap, stiffForce, Matrix.transpose_one, Matrix.one_mulVec,
    Matrix.scalar_apply]
  simp_rw [scalar_diagonal_mulVec]
  rw [dotProduct_smul, dotProduct_smul, dotProduct_smul]
  simp [smul_eq_mul]
  rw [euclidean_self_dot z.1, euclidean_self_dot z.2, euclidean_cross_dot z.1 z.2]
  field_simp [ne_of_gt hm, ne_of_gt hk]
  simp [rampedCrossStorage]
  ring

private lemma scalar_storage_component_sandwich
    (m k β : ℝ) (hm : 0 < m) (hk : 0 < k) (hβ : 0 ≤ β) (z : PointMassState) :
    (min m k / 2 - β / 2) *
        (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ≤ rampedCrossStorage m k β z ∧
      rampedCrossStorage m k β z ≤ (max m k / 2 + β / 2) *
        (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := by
  have hM1 : m * (z.1.ofLp ⬝ᵥ z.1.ofLp) ≤
      z.1.ofLp ⬝ᵥ (Matrix.scalar (Fin 3) m *ᵥ z.1.ofLp) := by
    simp only [Matrix.scalar_apply]
    rw [scalar_diagonal_mulVec]
    simp [smul_eq_mul]
  have hM2 : z.1.ofLp ⬝ᵥ (Matrix.scalar (Fin 3) m *ᵥ z.1.ofLp) ≤
      m * (z.1.ofLp ⬝ᵥ z.1.ofLp) := by
    simp only [Matrix.scalar_apply]
    rw [scalar_diagonal_mulVec]
    simp [smul_eq_mul]
  have hK1 : k * (z.2.ofLp ⬝ᵥ z.2.ofLp) ≤
      z.2.ofLp ⬝ᵥ (Matrix.scalar (Fin 3) k *ᵥ z.2.ofLp) := by
    simp only [Matrix.scalar_apply]
    rw [scalar_diagonal_mulVec]
    simp [smul_eq_mul]
  have hK2 : z.2.ofLp ⬝ᵥ (Matrix.scalar (Fin 3) k *ᵥ z.2.ofLp) ≤
      k * (z.2.ofLp ⬝ᵥ z.2.ofLp) := by
    simp only [Matrix.scalar_apply]
    rw [scalar_diagonal_mulVec]
    simp [smul_eq_mul]
  have hcross : |z.2.ofLp ⬝ᵥ z.1.ofLp| ≤
      Real.sqrt (z.1.ofLp ⬝ᵥ z.1.ofLp) * Real.sqrt (z.2.ofLp ⬝ᵥ z.2.ofLp) := by
    calc
      |z.2.ofLp ⬝ᵥ z.1.ofLp| = |⟪z.1, z.2⟫_ℝ| := by rw [euclidean_cross_dot]
      _ ≤ ‖z.1‖ * ‖z.2‖ := abs_real_inner_le_norm _ _
      _ = Real.sqrt (z.1.ofLp ⬝ᵥ z.1.ofLp) *
          Real.sqrt (z.2.ofLp ⬝ᵥ z.2.ofLp) := by
        rw [euclidean_self_dot, euclidean_self_dot, Real.sqrt_sq (norm_nonneg _),
          Real.sqrt_sq (norm_nonneg _)]
  have hg : |stiffForce (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (Matrix.scalar (Fin 3) k) z.2.ofLp ⬝ᵥ
        (Matrix.scalar (Fin 3) m *ᵥ z.1.ofLp)| ≤
      (m * k) * (Real.sqrt (z.1.ofLp ⬝ᵥ z.1.ofLp) *
        Real.sqrt (z.2.ofLp ⬝ᵥ z.2.ofLp)) := by
    simp only [stiffForce, Matrix.transpose_one, Matrix.one_mulVec,
      Matrix.scalar_apply]
    simp_rw [scalar_diagonal_mulVec]
    rw [dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    calc
      |m * (k * (z.2.ofLp ⬝ᵥ z.1.ofLp))| =
          (m * k) * |z.2.ofLp ⬝ᵥ z.1.ofLp| := by
        rw [abs_mul, abs_of_pos hm, abs_mul, abs_of_pos hk]
        ring
      _ ≤ (m * k) * (Real.sqrt (z.1.ofLp ⬝ᵥ z.1.ofLp) *
          Real.sqrt (z.2.ofLp ⬝ᵥ z.2.ofLp)) :=
        mul_le_mul_of_nonneg_left hcross (mul_nonneg hm.le hk.le)
  have hs := strict_storage_sandwich (M := Matrix.scalar (Fin 3) m)
    (K := Matrix.scalar (Fin 3) k) (J := (1 : Matrix (Fin 3) (Fin 3) ℝ))
    (e := z.1.ofLp) (x := z.2.ofLp) (α := β / (m * k))
    (m₁ := m) (m₂ := m) (k₁ := k) (k₂ := k) (c₆ := m * k)
    (by positivity) (by positivity) hM1 hM2 hK1 hK2 hg
  have hs' :
      (min m k / 2 - (β / (m * k)) * (m * k) / 2) *
          (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ≤ rampedCrossStorage m k β z ∧
        rampedCrossStorage m k β z ≤
          (max m k / 2 + (β / (m * k)) * (m * k) / 2) *
            (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := by
    rw [scalar_storage_eq_strictStorage m k β hm hk z] at hs
    simpa only [euclidean_self_dot] using hs
  constructor
  · have h := hs'.1
    convert h using 1; field_simp [ne_of_gt hm, ne_of_gt hk]
  · have h := hs'.2
    convert h using 1; field_simp [ne_of_gt hm, ne_of_gt hk]

private lemma pointMassState_sum_le_norm_sq (z : PointMassState) :
    ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h
  · rw [max_eq_right h]
    have hsq := mul_nonneg (sub_nonneg.mpr h)
      (add_nonneg (norm_nonneg z.1) (norm_nonneg z.2))
    nlinarith
  · rw [max_eq_left h]
    have hsq := mul_nonneg (sub_nonneg.mpr h)
      (add_nonneg (norm_nonneg z.2) (norm_nonneg z.1))
    nlinarith

/-- Coercive lower and upper bounds in the actual sup product norm on `PointMassState`. -/
theorem rampedCrossStorage_norm_sandwich
    (m k β : ℝ) (hm : 0 < m) (hk : 0 < k) (hβ : 0 ≤ β) (hβlt : β < min m k)
    (z : PointMassState) :
    (min m k / 2 - β / 2) * ‖z‖ ^ 2 ≤ rampedCrossStorage m k β z ∧
      rampedCrossStorage m k β z ≤ (max m k + β) * ‖z‖ ^ 2 := by
  have hcomp := scalar_storage_component_sandwich m k β hm hk hβ z
  have hclo : 0 < min m k / 2 - β / 2 := by
    have hmin : 0 < min m k := lt_min hm hk
    linarith
  have hchi : 0 ≤ max m k / 2 + β / 2 := by positivity
  constructor
  · exact (mul_le_mul_of_nonneg_left (prod_norm_sq_le_sum_sq z) hclo.le).trans hcomp.1
  · calc
      rampedCrossStorage m k β z ≤
          (max m k / 2 + β / 2) * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := hcomp.2
      _ ≤ (max m k / 2 + β / 2) * (2 * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (pointMassState_sum_le_norm_sq z) hchi
      _ = (max m k + β) * ‖z‖ ^ 2 := by ring

end Ctrllib.ComStartupRampCrossTermStorage

#print axioms Ctrllib.ComStartupRampCrossTermStorage.rampedCrossStorage
#print axioms Ctrllib.ComStartupRampCrossTermStorage.rampedCrossStorageRate
#print axioms Ctrllib.ComStartupRampCrossTermStorage.rampedCrossStorage_hasDerivAt
#print axioms Ctrllib.ComStartupRampCrossTermStorage.rampedCrossStorage_hasDerivWithinAt
#print axioms Ctrllib.ComStartupRampCrossTermStorage.rampedCrossStorage_norm_sandwich
