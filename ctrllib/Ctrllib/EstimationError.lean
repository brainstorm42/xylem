import Ctrllib.CvarPopulation
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Deterministic observer error and population loss

A linear measurement correction is analyzed from its displayed plant and
observer equations. No Gaussian noise, Kalman optimality, or stochastic
independence is assumed. A uniform norm contraction and bounded disturbances
give a geometric error bound. A Lipschitz episode loss then transfers an
almost-sure state or trajectory error certificate to population CVaR.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace Ctrllib

section Observer

variable {E F U : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- One declared linear plant step with additive process disturbance. -/
def linearPlantStep (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (x : E) (u : U) (w : E) : E := A x + B u + w

/-- One measurement-correction observer step. -/
def linearObserverStep (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : E →L[ℝ] F) (L : F →L[ℝ] E) (xhat : E) (u : U) (y : F) : E :=
  A xhat + B u + L (y - C xhat)

/-- Derive the estimation-error update using the same known control in plant
and observer, with measurement `C x + v`. -/
theorem linearObserver_error_identity
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : E →L[ℝ] F) (L : F →L[ℝ] E)
    (x xhat w : E) (u : U) (v : F) :
    linearPlantStep A B x u w - linearObserverStep A B C L xhat u (C x + v) =
      (A - L.comp C) (x - xhat) + (w - L v) := by
  simp only [linearPlantStep, linearObserverStep, map_add, map_sub,
    sub_apply, ContinuousLinearMap.comp_apply]
  abel

/-- Operator-norm one-step error estimate before choosing any contraction or
disturbance bounds. -/
theorem linearObserver_error_norm_le
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : E →L[ℝ] F) (L : F →L[ℝ] E)
    (x xhat w : E) (u : U) (v : F) :
    ‖linearPlantStep A B x u w - linearObserverStep A B C L xhat u (C x + v)‖ ≤
      ‖A - L.comp C‖ * ‖x - xhat‖ + ‖w‖ + ‖L‖ * ‖v‖ := by
  rw [linearObserver_error_identity]
  calc
    _ ≤ ‖(A - L.comp C) (x - xhat)‖ + ‖w - L v‖ := norm_add_le _ _
    _ ≤ ‖A - L.comp C‖ * ‖x - xhat‖ + (‖w‖ + ‖L‖ * ‖v‖) :=
      add_le_add ((A - L.comp C).le_opNorm _) ((norm_sub_le _ _).trans
        (add_le_add le_rfl (L.le_opNorm _)))
    _ = _ := by ring

omit [NormedSpace ℝ E] in
/-- Solve the scalar inequality induced by a deterministic error recursion.
This finite-time estimate only needs nonnegative `r`, not `r < 1`. -/
theorem norm_error_le_geometric {e : ℕ → E} {r b : ℝ}
    (hr : 0 ≤ r) (hstep : ∀ k, ‖e (k + 1)‖ ≤ r * ‖e k‖ + b) (k : ℕ) :
    ‖e k‖ ≤ r ^ k * ‖e 0‖ + b * ∑ j ∈ Finset.range k, r ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := (hstep k).trans (add_le_add (mul_le_mul_of_nonneg_left ih hr) le_rfl)
    calc
      _ ≤ r * (r ^ k * ‖e 0‖ + b * ∑ j ∈ Finset.range k, r ^ j) + b := hh
      _ = r ^ (k + 1) * ‖e 0‖ + b * ∑ j ∈ Finset.range (k + 1), r ^ j := by
        rw [geom_sum_succ, pow_succ]
        ring

omit [NormedSpace ℝ E] in
/-- Under strict contraction the finite geometric sum has its usual closed
form. The estimate retains both initial error and disturbance amplification. -/
theorem norm_error_le_contraction_bound {e : ℕ → E} {r b : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ k, ‖e (k + 1)‖ ≤ r * ‖e k‖ + b) (k : ℕ) :
    ‖e k‖ ≤ r ^ k * ‖e 0‖ + b * ((1 - r ^ k) / (1 - r)) := by
  have hgeom : (∑ j ∈ Finset.range k, r ^ j) = (1 - r ^ k) / (1 - r) := by
    apply (eq_div_iff (by linarith : (1 - r : ℝ) ≠ 0)).2
    exact geom_sum_mul_neg r k
  simpa [hgeom] using norm_error_le_geometric hr0 hstep k

/-- The complete time-varying observer implication, retaining the displayed
plant and observation equations. The contraction bound is a uniform operator
norm premise, not an inference from pointwise eigenvalues. -/
theorem linearObserver_error_le_geometric
    (A : ℕ → E →L[ℝ] E) (B : ℕ → U →L[ℝ] E)
    (C : ℕ → E →L[ℝ] F) (L : ℕ → F →L[ℝ] E)
    {x xhat w : ℕ → E} {u : ℕ → U} {v : ℕ → F}
    {r wmax vmax lmax : ℝ} (hr : 0 ≤ r) (hl : 0 ≤ lmax)
    (hplant : ∀ k, x (k + 1) = linearPlantStep (A k) (B k) (x k) (u k) (w k))
    (hobserver : ∀ k, xhat (k + 1) =
      linearObserverStep (A k) (B k) (C k) (L k) (xhat k) (u k) (C k (x k) + v k))
    (hclosed : ∀ k, ‖A k - (L k).comp (C k)‖ ≤ r)
    (hw : ∀ k, ‖w k‖ ≤ wmax) (hv : ∀ k, ‖v k‖ ≤ vmax)
    (hL : ∀ k, ‖L k‖ ≤ lmax) (k : ℕ) :
    ‖x k - xhat k‖ ≤ r ^ k * ‖x 0 - xhat 0‖ +
      (wmax + lmax * vmax) * ∑ j ∈ Finset.range k, r ^ j := by
  apply norm_error_le_geometric (e := fun k => x k - xhat k) hr
  intro j
  rw [hplant j, hobserver j]
  have hraw := linearObserver_error_norm_le (A j) (B j) (C j) (L j)
    (x j) (xhat j) (w j) (u j) (v j)
  have hc := mul_le_mul_of_nonneg_right (hclosed j) (norm_nonneg (x j - xhat j))
  have hn : ‖L j‖ * ‖v j‖ ≤ lmax * vmax :=
    (mul_le_mul_of_nonneg_right (hL j) (norm_nonneg (v j))).trans
      (mul_le_mul_of_nonneg_left (hv j) hl)
  linarith [hw j]

end Observer

section Loss

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A Lipschitz loss on a common normalized state or trajectory space turns
an almost-sure norm error into a population CVaR upper certificate. -/
theorem cvarPop_le_of_estimation_error {loss : E → ℝ} {K : ℝ≥0}
    (hLoss : LipschitzWith K loss) {x xhat : Ω → E}
    (hx : Integrable (fun ω => loss (x ω)) μ)
    (hhat : Integrable (fun ω => loss (xhat ω)) μ)
    {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (herr : ∀ᵐ ω ∂μ, ‖x ω - xhat ω‖ ≤ ε) :
    cvarPop α μ (fun ω => loss (x ω)) ≤
      cvarPop α μ (fun ω => loss (xhat ω)) + (K : ℝ) * ε := by
  apply cvarPop_le_of_ae_le_add hx hhat hα0 hα1
  filter_upwards [herr] with ω hω
  have h := hLoss.le_add_mul (x ω) (xhat ω)
  rw [dist_eq_norm] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hω K.coe_nonneg))

/-- Two-sided version of the population loss certificate. -/
theorem abs_cvarPop_sub_le_of_estimation_error {loss : E → ℝ} {K : ℝ≥0}
    (hLoss : LipschitzWith K loss) {x xhat : Ω → E}
    (hx : Integrable (fun ω => loss (x ω)) μ)
    (hhat : Integrable (fun ω => loss (xhat ω)) μ)
    {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (herr : ∀ᵐ ω ∂μ, ‖x ω - xhat ω‖ ≤ ε) :
    |cvarPop α μ (fun ω => loss (x ω)) -
      cvarPop α μ (fun ω => loss (xhat ω))| ≤ (K : ℝ) * ε := by
  apply abs_cvarPop_sub_le_of_ae_abs_sub_le hx hhat hα0 hα1
  filter_upwards [herr] with ω hω
  have h := hLoss.dist_le_mul (x ω) (xhat ω)
  rw [Real.dist_eq, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left hω K.coe_nonneg)

end Loss

end Ctrllib

#print axioms Ctrllib.linearObserver_error_identity
#print axioms Ctrllib.linearObserver_error_norm_le
#print axioms Ctrllib.norm_error_le_geometric
#print axioms Ctrllib.norm_error_le_contraction_bound
#print axioms Ctrllib.linearObserver_error_le_geometric
#print axioms Ctrllib.cvarPop_le_of_estimation_error
#print axioms Ctrllib.abs_cvarPop_sub_le_of_estimation_error
