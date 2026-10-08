/-
Lyapunov stability and global asymptotic stability for the ideal point-mass
centre-of-mass loop.

The existing `PointMassComFlow` module proves convergence by LaSalle. This
module closes the separate stability half using the same mechanical energy.
The derivative is only semidefinite because damping vanishes whenever the
velocity is zero, so the strict-derivative asymptotic theorem is deliberately
not used. Lyapunov stability comes from the nonincreasing positive-definite
energy; global convergence is reused from `pointMass_tendsto_zero`.
-/
import Ctrllib.PointMassComFlow
import Ctrllib.KhalilStability

set_option maxSynthPendingDepth 3

open Set Filter Topology

namespace Ctrllib

section PointMassStability

/- The mechanical energy is positive away from the origin under the physical
   hypotheses already carried by the point-mass model. -/
theorem pointMassEnergy_pos (m k : ℝ) (hm : 0 < m) (hk : 0 < k)
    (z : PointMassState) (hz : z ≠ 0) : 0 < pointMassEnergy m k z := by
  rcases z with ⟨v, x⟩
  unfold pointMassEnergy
  by_cases hv : v = 0
  · have hx : x ≠ 0 := by
      intro hx
      apply hz
      simp [hv, hx]
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hx2 : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hxn
    have hk2 : 0 < k / 2 := by positivity
    simpa [hv] using mul_pos hk2 hx2
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hv2 : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hvn
    have hm2 : 0 < m / 2 := by positivity
    nlinarith [sq_nonneg ‖x‖,
      mul_nonneg (by positivity : 0 ≤ k / 2) (sq_nonneg ‖x‖)]

/- The CoM energy lemmas are stated through the scalar-operator realization;
   these equalities move them to the point-mass names used by the stability
   theorem. -/
private theorem pointMassEnergy_differentiable (m k : ℝ) :
    Differentiable ℝ (pointMassEnergy m k) := by
  have hVeq : pointMassEnergy m k = comEnergy (pmM m) (pmK k) :=
    funext (pointMassEnergy_eq_comEnergy m k)
  rw [hVeq]
  exact comEnergy_differentiable

private theorem pointMassEnergy_decrease (m d k : ℝ)
    (hm : 0 < m) (hd : 0 < d) :
    ∀ y, fderiv ℝ (pointMassEnergy m k) y (pointMassField m d k y) ≤ 0 := by
  intro y
  have hVeq : pointMassEnergy m k = comEnergy (pmM m) (pmK k) :=
    funext (pointMassEnergy_eq_comEnergy m k)
  have hfeq : pointMassField m d k =
      comField (pmD d) (pmK k) (pmMinv m) :=
    funext (pointMassField_eq_comField m d k)
  rw [hVeq, hfeq]
  exact com_decrease (M := pmM m) (D := pmD d) (K := pmK k) (Minv := pmMinv m)
    pmM_selfAdjoint pmK_selfAdjoint (pmM_inv hm) (pmD_nonneg hd) y

/-- Lyapunov stability of the origin for the positive damped point-mass loop.
The proof uses nonincreasing positive-definite energy; the semidefinite damping
derivative is sufficient for this stability conclusion. -/
theorem pointMass_lyapStable (m d k : ℝ) (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) :
    LyapStable (pointMassFlow m d k hm) := by
  refine lyapunov_stable (ϕ := pointMassFlow m d k hm)
    (f := pointMassField m d k) (V := pointMassEnergy m k)
    (pointMass_isSolutionTo m d k hm hd hk) (pointMassEnergy_differentiable m k) ?_ ?_ ?_
  · simp [pointMassEnergy]
  · exact pointMassEnergy_pos m k hm hk
  · exact pointMassEnergy_decrease m d k hm hd

/-- The requested global endpoint: Lyapunov stability together with convergence
of every initial state. -/
theorem pointMass_globally_asymptotically_stable (m d k : ℝ)
    (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) :
    LyapStable (pointMassFlow m d k hm) ∧
      ∀ z₀, Tendsto (fun t : ℝ => pointMassFlow m d k hm t z₀) atTop (𝓝 0) := by
  refine ⟨pointMass_lyapStable m d k hm hd hk, ?_⟩
  intro z₀
  exact pointMass_tendsto_zero m d k hm hd hk z₀

/-- Optional local asymptotic-stability corollary, obtained from the global
convergence endpoint rather than from the strict-derivative theorem. -/
theorem pointMass_asympStable (m d k : ℝ) (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) :
    AsympStable (pointMassFlow m d k hm) := by
  refine ⟨pointMass_lyapStable m d k hm hd hk, 1, one_pos, ?_⟩
  intro z₀ hz₀
  exact pointMass_tendsto_zero m d k hm hd hk z₀

end PointMassStability

end Ctrllib

#print axioms Ctrllib.pointMass_lyapStable
#print axioms Ctrllib.pointMass_globally_asymptotically_stable
#print axioms Ctrllib.pointMass_asympStable
