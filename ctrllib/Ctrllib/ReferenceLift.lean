import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.Basic
import Ctrllib.ReferencePhase
import Ctrllib.ReferenceCalculus

/-!
# Configuration-lift velocity compatibility

For an error map E(q,u), a supplied differentiable zero-error lift determines
its tangent velocity. Injectivity of the configuration Jacobian then identifies
that tangent with a generalized velocity through the declared coordinate map.
Existence of the lift, the frame-specific error map, and uniform domain bounds
are not inferred. See the corresponding derivation record's FFSM contract the corresponding local note companion.
-/

open Filter Topology
namespace Ctrllib
variable {Q Y V : Type*}
variable [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Differentiating a locally exact configuration lift of a phase-dependent
error map gives its tangent constraint. Pointwise zero error is insufficient. -/
theorem reference_lift_tangent
    {err : Q × ℝ → Y} {q : ℝ → Q} {q₁ : Q} {u : ℝ}
    {L : (Q × ℝ) →L[ℝ] Y}
    (hq : HasDerivAt q q₁ u) (hE : HasFDerivAt err L (q u, u))
    (hzero : (fun w ↦ err (q w, w)) =ᶠ[𝓝 u] fun _ ↦ 0) :
    L (q₁, 1) = 0 := by
  have hc := hE.comp_hasDerivAt (f := fun w ↦ (q w, w)) u
    (hq.prodMk (hasDerivAt_id u))
  have hz : HasDerivAt (fun w ↦ err (q w, w)) 0 u :=
    (hasDerivAt_const u (0 : Y)).congr_of_eventuallyEq hzero
  exact hc.unique hz

/-- Relative derivatives allow a lift specified on a phase interval, including
an endpoint with a unique relative derivative; no two-sided extension is assumed. -/
theorem reference_lift_tangent_within
    {err : Q × ℝ → Y} {q : ℝ → Q} {q₁ : Q} {u : ℝ} {S : Set ℝ}
    {L : (Q × ℝ) →L[ℝ] Y}
    (hu : u ∈ S) (hunique : UniqueDiffWithinAt ℝ S u)
    (hq : HasDerivWithinAt q q₁ S u) (hE : HasFDerivAt err L (q u, u))
    (hzero : ∀ w ∈ S, err (q w, w) = 0) :
    L (q₁, 1) = 0 := by
  have hc := hE.comp_hasDerivWithinAt (f := fun w ↦ (q w, w)) u
    (hq.prodMk (hasDerivAt_id u).hasDerivWithinAt)
  have hz : HasDerivWithinAt (fun w ↦ err (q w, w)) 0 S u :=
    (hasDerivAt_const u (0 : Y)).hasDerivWithinAt.congr_of_mem hzero hu
  exact (hc.derivWithin hunique).symm.trans (hz.derivWithin hunique)

/-- Injectivity of the configuration part of the error differential identifies
coordinate velocity from compatible output velocities and the same phase rate. -/
theorem reference_lift_velocity_compatible
    {L : (Q × ℝ) →L[ℝ] Y} {B : V →L[ℝ] Q} {q₁ : Q} {v : V} {s : ℝ}
    (htangent : L (q₁, 1) = 0)
    (hframe : L (B v, s) = 0)
    (hinj : Function.Injective (fun w : Q ↦ L (w, 0))) :
    s • q₁ = B v := by
  have hs : L (s • q₁, s) = 0 := by
    have hh := congrArg (fun y : Y ↦ s • y) htangent
    simpa only [← map_smul, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using hh
  apply hinj
  have hp : (s • q₁, (0 : ℝ)) - (B v, 0) =
      (s • q₁, s) - (B v, s) := by simp
  have hh := congrArg L hp
  simp only [map_sub, hs, hframe, sub_self] at hh
  exact sub_eq_zero.mp hh

/-- Exponential timing of a supplied lift has exactly the declared coordinate
velocity when the tangent, frame and injectivity obligations are supplied. -/
theorem reference_lift_phase_hasDerivAt
    {err : Q × ℝ → Y} {q : ℝ → Q} {q₁ : Q} {rate u₀ t : ℝ}
    {L : (Q × ℝ) →L[ℝ] Y} {B : V →L[ℝ] Q} {v : V}
    (hq : HasDerivAt q q₁ (referencePhase rate u₀ t))
    (hE : HasFDerivAt err L (q (referencePhase rate u₀ t), referencePhase rate u₀ t))
    (hzero : (fun w ↦ err (q w, w)) =ᶠ[𝓝 (referencePhase rate u₀ t)] fun _ ↦ 0)
    (hframe : L (B v, referenceSpeed rate u₀ t) = 0)
    (hinj : Function.Injective (fun w : Q ↦ L (w, 0))) :
    HasDerivAt (fun τ ↦ q (referencePhase rate u₀ τ)) (B v) t := by
  have htan := reference_lift_tangent hq hE hzero
  have heq := reference_lift_velocity_compatible htan hframe hinj
  have hd := hasDerivAt_reference_comp
    (s := fun u ↦ rate * (1 - u)) (p₁ := fun _ ↦ q₁)
    (hasDerivAt_referencePhase rate u₀ t) hq
  exact hd.congr_deriv heq

/-- A bounded inverse gain turns differential lift/frame defects into a
coordinate-velocity discrepancy. A small pose residual is not this premise. -/
theorem reference_lift_velocity_defect_bound
    {L : (Q × ℝ) →L[ℝ] Y} {B : V →L[ℝ] Q} {qd : Q} {v : V}
    {s κ εlift εframe : ℝ} (hκ : 0 ≤ κ)
    (hinv : ∀ w : Q, ‖w‖ ≤ κ * ‖L (w, 0)‖)
    (hlift : ‖L (qd, s)‖ ≤ εlift) (hframe : ‖L (B v, s)‖ ≤ εframe) :
    ‖qd - B v‖ ≤ κ * (εlift + εframe) := by
  have heq : L (qd - B v, 0) = L (qd, s) - L (B v, s) := by
    rw [← map_sub]
    congr 1
    simp
  calc
    ‖qd - B v‖ ≤ κ * ‖L (qd - B v, 0)‖ := hinv _
    _ = κ * ‖L (qd, s) - L (B v, s)‖ := by rw [heq]
    _ ≤ κ * (‖L (qd, s)‖ + ‖L (B v, s)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hκ
    _ ≤ κ * (εlift + εframe) :=
      mul_le_mul_of_nonneg_left (add_le_add hlift hframe) hκ

/-- A supplied continuous linear inverse gives the local inverse gain. Its
uniform bound along a lift remains a separate quantitative obligation. -/
theorem reference_lift_inverse_gain
    (A : Q ≃L[ℝ] Y) (L : (Q × ℝ) →L[ℝ] Y)
    (hA : ∀ w, A w = L (w, 0)) (w : Q) :
    ‖w‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖L (w, 0)‖ := by
  simpa only [← hA w, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using
    A.symm.toContinuousLinearMap.le_opNorm (A w)

end Ctrllib
#print axioms Ctrllib.reference_lift_tangent
#print axioms Ctrllib.reference_lift_tangent_within
#print axioms Ctrllib.reference_lift_velocity_compatible
#print axioms Ctrllib.reference_lift_phase_hasDerivAt
#print axioms Ctrllib.reference_lift_velocity_defect_bound
#print axioms Ctrllib.reference_lift_inverse_gain
