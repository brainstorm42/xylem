import Ctrllib.ComControllerPlantComposition

/-!
# Component B: continuous-time startup force ramp

Builds on `ComControllerPlantComposition` without changing its declarations.
The stationary-reference state is velocity-first: `z = (v, x)`.
The ramp scales both nominal damping and stiffness; the ideal plant is unchanged.
Contracts concern instantaneous algebraic outputs, not trajectories or flow existence.
No integral action, saturation, stability result, or physical verification is asserted.
See `AssumeGuarantee` for satisfaction, enabledness, wiring, and refinement semantics.
-/

namespace Ctrllib.ComStartupRampComposition

open Ctrllib.AssumeGuarantee
open Ctrllib.ComControllerPlantComposition

/-- Continuous time and stationary-reference velocity/position error. -/
abbrev TimedState := ℝ × PointMassState

/-- Forward the input with the force; the plant wire explicitly drops time. -/
abbrev TimedAppliedForce := TimedState × PointMassCoord

/-- Defined on all reals; the contract requires `t ≥ 0` and `τ > 0`. -/
noncomputable def ramp (τ t : ℝ) : ℝ := 1 - Real.exp (-t / τ)

theorem ramp_zero (τ : ℝ) : ramp τ 0 = 0 := by simp [ramp]

theorem ramp_bounds (τ t : ℝ) (hτ : 0 < τ) (ht : 0 ≤ t) :
    0 ≤ ramp τ t ∧ ramp τ t < 1 := by
  have he : Real.exp (-t / τ) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hτ.le)
  have hp := Real.exp_pos (-t / τ)
  constructor <;> dsimp [ramp] <;> linarith

/-- The startup ramp approaches the nominal gain as time tends to infinity. -/
theorem ramp_tendsto_one (τ : ℝ) (hτ : 0 < τ) :
    Filter.Tendsto (fun t : ℝ => ramp τ t) Filter.atTop (nhds 1) := by
  have hdiv : Filter.Tendsto (fun t : ℝ => t / τ) Filter.atTop Filter.atTop :=
    (Filter.tendsto_div_const_atTop_of_pos hτ).2 Filter.tendsto_id
  have hneg : Filter.Tendsto (fun t : ℝ => -t / τ) Filter.atTop Filter.atBot := by
    simpa only [Function.comp_def, neg_div] using
      Filter.tendsto_neg_atTop_atBot.comp hdiv
  have hexp := Real.tendsto_exp_atBot.comp hneg
  simpa only [ramp, Function.comp_def, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hexp

/-- Same-state nominal force scaled by the startup ramp. -/
noncomputable def rampedForce (τ d k : ℝ) (tz : TimedState) : PointMassCoord :=
  ramp τ tz.1 • controllerForce d k tz.2

noncomputable def controllerRel (τ d k : ℝ) (tz : TimedState)
    (out : TimedAppliedForce) : Prop := out = (tz, rampedForce τ d k tz)

noncomputable def controllerContract (τ d k : ℝ) :
    Contract TimedState TimedAppliedForce where
  assumption := fun tz => 0 < τ ∧ 0 ≤ tz.1 ∧ 0 < d ∧ 0 < k
  guarantee := controllerRel τ d k

/-- Preserve the state and force exactly; time is not a plant input. -/
def stateForceWire (out : TimedAppliedForce) : AppliedForce := (out.1.2, out.2)

theorem controller_satisfies (τ d k : ℝ) :
    Satisfies (controllerRel τ d k) (controllerContract τ d k) := by
  intro tz out _ h
  exact h

theorem controller_enabled (τ d k : ℝ) :
    Enabled (controllerRel τ d k) (controllerContract τ d k).assumption := by
  intro tz _
  exact ⟨(tz, rampedForce τ d k tz), rfl⟩

/-- Reuses Component A's unchanged plant relation and contract. -/
theorem plant_satisfies (m : ℝ) : Satisfies (plantRel m) (plantContract m) :=
  ComControllerPlantComposition.plant_satisfies m

theorem plant_enabled (m : ℝ) : Enabled (plantRel m) (plantContract m).assumption :=
  ComControllerPlantComposition.plant_enabled m

def environment (m τ d k : ℝ) (tz : TimedState) : Prop :=
  0 < m ∧ (controllerContract τ d k).assumption tz

theorem downstream_compatible (m τ d k : ℝ) (tz : TimedState)
    (out : TimedAppliedForce) (h : environment m τ d k tz)
    (_ : (controllerContract τ d k).guarantee tz out) :
    (plantContract m).assumption (stateForceWire out) := h.1

theorem environment_meets_sequential (m τ d k : ℝ) :
    ∀ tz, environment m τ d k tz →
      (sequential (controllerContract τ d k) (plantContract m) stateForceWire).assumption tz := by
  exact sequential_assumption_of_environment stateForceWire (environment m τ d k)
    (fun _ h => h.2) (fun tz out h hg => downstream_compatible m τ d k tz out h hg)

theorem composed_satisfies (m τ d k : ℝ) :
    Satisfies (connected (controllerRel τ d k) (plantRel m) stateForceWire)
      (sequential (controllerContract τ d k) (plantContract m) stateForceWire) :=
  satisfies_sequential stateForceWire (controller_satisfies τ d k) (plant_satisfies m)

theorem composed_enabled (m τ d k : ℝ) :
    Enabled (connected (controllerRel τ d k) (plantRel m) stateForceWire)
      (sequential (controllerContract τ d k) (plantContract m) stateForceWire).assumption :=
  enabled_sequential stateForceWire (controller_satisfies τ d k)
    (controller_enabled τ d k) (plant_enabled m)

/-- Exact time-varying field `(v̇, ẋ)`; mass stays constant. -/
noncomputable def rampedPointMassField (m τ d k : ℝ) (tz : TimedState) : PointMassState :=
  ((-(ramp τ tz.1 * d / m)) • tz.2.1 - (ramp τ tz.1 * k / m) • tz.2.2, tz.2.1)

theorem closedLoop_eq_rampedPointMassField (m τ d k : ℝ) (tz : TimedState) :
    plantDerivative m (stateForceWire (tz, rampedForce τ d k tz)) =
      rampedPointMassField m τ d k tz := by
  apply Prod.ext
  · change m⁻¹ • (ramp τ tz.1 • ((-d) • tz.2.1 + (-k) • tz.2.2)) = _
    simp only [smul_add, smul_smul, rampedPointMassField, sub_eq_add_neg, ← neg_smul]
    congr 1 <;> congr 1 <;> simp only [div_eq_mul_inv] <;> ring
  · rfl

theorem connected_iff_rampedPointMassField (m τ d k : ℝ) (tz : TimedState)
    (zdot : PointMassState) :
    connected (controllerRel τ d k) (plantRel m) stateForceWire tz zdot ↔
      zdot = rampedPointMassField m τ d k tz := by
  constructor
  · rintro ⟨out, hC, hP⟩
    change out = (tz, rampedForce τ d k tz) at hC
    subst out
    change zdot = plantDerivative m (stateForceWire (tz, rampedForce τ d k tz)) at hP
    simpa only [closedLoop_eq_rampedPointMassField] using hP
  · intro h
    refine ⟨(tz, rampedForce τ d k tz), rfl, ?_⟩
    change zdot = plantDerivative m (stateForceWire (tz, rampedForce τ d k tz))
    simpa only [closedLoop_eq_rampedPointMassField] using h

/-- Compare forces at the same state, not along different trajectories. -/
theorem force_norm_le_nominal (τ d k : ℝ) (tz : TimedState)
    (hτ : 0 < τ) (ht : 0 ≤ tz.1) :
    ‖rampedForce τ d k tz‖ ≤ ‖controllerForce d k tz.2‖ := by
  obtain ⟨hr, hr1⟩ := ramp_bounds τ tz.1 hτ ht
  rw [rampedForce, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_of_le_one_left (norm_nonneg _) hr1.le

/-- Exact force suppression at a common state. -/
theorem force_difference_norm (τ d k : ℝ) (tz : TimedState) :
    ‖rampedForce τ d k tz - controllerForce d k tz.2‖ =
      Real.exp (-tz.1 / τ) * ‖controllerForce d k tz.2‖ := by
  have hdiff : rampedForce τ d k tz - controllerForce d k tz.2 =
      (-Real.exp (-tz.1 / τ)) • controllerForce d k tz.2 := by
    calc
      rampedForce τ d k tz - controllerForce d k tz.2 =
          (ramp τ tz.1 - 1) • controllerForce d k tz.2 := by
        simpa only [rampedForce, one_smul] using
          (sub_smul (ramp τ tz.1) 1 (controllerForce d k tz.2)).symm
      _ = _ := by congr 1; simp [ramp]
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]

/-- Original exact-force contract lifted to the same time/state interface.
Its guarantee is precisely Component A's controller guarantee after the wire;
its assumptions include the same startup domain, so failure is a force mismatch. -/
noncomputable def nominalTimedContract (τ d k : ℝ) :
    Contract TimedState TimedAppliedForce where
  assumption := (controllerContract τ d k).assumption
  guarantee := fun tz out => out.1 = tz ∧
    (ComControllerPlantComposition.controllerContract d k).guarantee tz.2 (stateForceWire out)

/-- At startup, zero velocity and nonzero position give zero ramped force,
while positive stiffness gives a nonzero nominal restoring force. -/
theorem startup_force_mismatch (τ d k : ℝ) (x : PointMassCoord)
    (hk : 0 < k) (hx : x ≠ 0) :
    rampedForce τ d k (0, (0, x)) ≠ controllerForce d k (0, x) := by
  simp only [rampedForce, ramp_zero, zero_smul, ComControllerPlantComposition.controllerForce,
    smul_zero, zero_add]
  exact Ne.symm (smul_ne_zero (neg_ne_zero.mpr (ne_of_gt hk)) hx)

/-- An admissible startup output witnesses failure of exact-force refinement. -/
theorem startup_not_refines (τ d k : ℝ) (hτ : 0 < τ) (hd : 0 < d)
    (hk : 0 < k) (x : PointMassCoord) (hx : x ≠ 0) :
    ¬ Refines (controllerContract τ d k) (nominalTimedContract τ d k) := by
  intro h
  have hg := h.2 (0, (0, x)) ((0, (0, x)), rampedForce τ d k (0, (0, x)))
    ⟨hτ, le_rfl, hd, hk⟩ rfl
  have hf : rampedForce τ d k (0, (0, x)) = controllerForce d k (0, x) :=
    congrArg Prod.snd hg.2
  exact startup_force_mismatch τ d k x hk hx hf

/-- Concrete startup position `(1, 0, 0)` in the point-mass coordinate space. -/
noncomputable def startupPosition : PointMassCoord := PiLp.single 2 0 1

theorem startupPosition_ne_zero : startupPosition ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : PointMassCoord => x 0) h
  simp [startupPosition] at h0

/-- With `τ = d = k = 1`, the explicit nonzero position witnesses non-refinement. -/
theorem concrete_startup_not_refines :
    ¬ Refines (controllerContract 1 1 1) (nominalTimedContract 1 1 1) :=
  startup_not_refines 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    startupPosition startupPosition_ne_zero

end Ctrllib.ComStartupRampComposition

-- Audit every declaration introduced by Component B.
#print axioms Ctrllib.ComStartupRampComposition.TimedState
#print axioms Ctrllib.ComStartupRampComposition.TimedAppliedForce
#print axioms Ctrllib.ComStartupRampComposition.ramp
#print axioms Ctrllib.ComStartupRampComposition.ramp_zero
#print axioms Ctrllib.ComStartupRampComposition.ramp_bounds
#print axioms Ctrllib.ComStartupRampComposition.ramp_tendsto_one
#print axioms Ctrllib.ComStartupRampComposition.rampedForce
#print axioms Ctrllib.ComStartupRampComposition.controllerRel
#print axioms Ctrllib.ComStartupRampComposition.controllerContract
#print axioms Ctrllib.ComStartupRampComposition.stateForceWire
#print axioms Ctrllib.ComStartupRampComposition.controller_satisfies
#print axioms Ctrllib.ComStartupRampComposition.controller_enabled
#print axioms Ctrllib.ComStartupRampComposition.plant_satisfies
#print axioms Ctrllib.ComStartupRampComposition.plant_enabled
#print axioms Ctrllib.ComStartupRampComposition.environment
#print axioms Ctrllib.ComStartupRampComposition.downstream_compatible
#print axioms Ctrllib.ComStartupRampComposition.environment_meets_sequential
#print axioms Ctrllib.ComStartupRampComposition.composed_satisfies
#print axioms Ctrllib.ComStartupRampComposition.composed_enabled
#print axioms Ctrllib.ComStartupRampComposition.rampedPointMassField
#print axioms Ctrllib.ComStartupRampComposition.closedLoop_eq_rampedPointMassField
#print axioms Ctrllib.ComStartupRampComposition.connected_iff_rampedPointMassField
#print axioms Ctrllib.ComStartupRampComposition.force_norm_le_nominal
#print axioms Ctrllib.ComStartupRampComposition.force_difference_norm
#print axioms Ctrllib.ComStartupRampComposition.nominalTimedContract
#print axioms Ctrllib.ComStartupRampComposition.startup_force_mismatch
#print axioms Ctrllib.ComStartupRampComposition.startup_not_refines
#print axioms Ctrllib.ComStartupRampComposition.startupPosition
#print axioms Ctrllib.ComStartupRampComposition.startupPosition_ne_zero
#print axioms Ctrllib.ComStartupRampComposition.concrete_startup_not_refines
