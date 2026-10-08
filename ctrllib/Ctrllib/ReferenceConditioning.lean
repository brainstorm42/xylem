import Ctrllib.ReferenceLift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Quantitative robustness of the configuration Jacobian

A certified lower gain at a reference operator and an operator-norm perturbation
budget give a lower gain throughout a supplied region. This supplies the inverse
estimate consumed by the reference-lift defect theorem. It proves neither the
existence of a lift nor a uniform perturbation bound for a physical model.
-/

namespace Ctrllib
variable {Q Y V : Type*}
variable [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Operator perturbations erode a certified lower gain by at most their norm. -/
theorem reference_jacobian_lower_gain
    {A A₀ : Q →L[ℝ] Y} {σ δ : ℝ}
    (hbase : ∀ w, σ * ‖w‖ ≤ ‖A₀ w‖) (hpert : ‖A - A₀‖ ≤ δ) (w : Q) :
    (σ - δ) * ‖w‖ ≤ ‖A w‖ := by
  have hb := hbase w
  have hp : ‖(A - A₀) w‖ ≤ δ * ‖w‖ :=
    (A - A₀).le_opNorm w |>.trans (mul_le_mul_of_nonneg_right hpert (norm_nonneg w))
  have ht : ‖A₀ w‖ ≤ ‖A w‖ + ‖(A - A₀) w‖ := by
    simpa only [sub_apply] using (norm_le_insert (A w) (A₀ w))
  nlinarith

/-- Strictly positive surviving lower gain yields the required inverse estimate;
no surjectivity assertion or inverse construction is needed. -/
theorem reference_jacobian_inverse_bound
    {A A₀ : Q →L[ℝ] Y} {σ δ : ℝ}
    (hbase : ∀ w, σ * ‖w‖ ≤ ‖A₀ w‖) (hpert : ‖A - A₀‖ ≤ δ)
    (hgap : δ < σ) (w : Q) : ‖w‖ ≤ (σ - δ)⁻¹ * ‖A w‖ := by
  have h := reference_jacobian_lower_gain hbase hpert w
  have hp : 0 < σ - δ := sub_pos.mpr hgap
  have hd : ‖w‖ ≤ ‖A w‖ / (σ - δ) :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv, mul_comm] using hd

/-- A positive lower gain also proves injectivity of the perturbed map. -/
theorem reference_jacobian_injective
    {A A₀ : Q →L[ℝ] Y} {σ δ : ℝ}
    (hbase : ∀ w, σ * ‖w‖ ≤ ‖A₀ w‖) (hpert : ‖A - A₀‖ ≤ δ)
    (hgap : δ < σ) : Function.Injective A := by
  intro x y hxy
  have h := reference_jacobian_lower_gain hbase hpert (x - y)
  have hz : A (x - y) = 0 := by simp [map_sub, hxy]
  rw [hz, norm_zero] at h
  have hn : ‖x - y‖ = 0 := by
    have hp : 0 < σ - δ := sub_pos.mpr hgap
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Differential defects are amplified by the reciprocal surviving lower gain. -/
theorem reference_lift_conditioned_defect_bound
    {L : (Q × ℝ) →L[ℝ] Y} {A A₀ : Q →L[ℝ] Y} {B : V →L[ℝ] Q}
    {qd : Q} {v : V} {s σ δ εlift εframe : ℝ}
    (hA : ∀ w, A w = L (w, 0))
    (hbase : ∀ w, σ * ‖w‖ ≤ ‖A₀ w‖) (hpert : ‖A - A₀‖ ≤ δ)
    (hgap : δ < σ) (hlift : ‖L (qd, s)‖ ≤ εlift)
    (hframe : ‖L (B v, s)‖ ≤ εframe) :
    ‖qd - B v‖ ≤ (σ - δ)⁻¹ * (εlift + εframe) := by
  apply reference_lift_velocity_defect_bound (inv_nonneg.mpr (sub_pos.mpr hgap).le)
    (fun w ↦ ?_) hlift hframe
  simpa only [← hA] using reference_jacobian_inverse_bound hbase hpert hgap w

end Ctrllib

#print axioms Ctrllib.reference_jacobian_lower_gain
#print axioms Ctrllib.reference_jacobian_inverse_bound
#print axioms Ctrllib.reference_jacobian_injective
#print axioms Ctrllib.reference_lift_conditioned_defect_bound
