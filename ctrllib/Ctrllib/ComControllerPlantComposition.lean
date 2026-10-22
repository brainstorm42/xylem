import Ctrllib.AssumeGuarantee
import Ctrllib.PointMassStability

/-!
# Component A: ideal point-mass CoM controller/plant composition

Scope: stationary-reference position/velocity error, exact state measurement,
continuous force application, constant positive mass, and isotropic gains.

This module makes two mathematical components explicit:
* controller: state `z = (v, x)` ↦ `(z, force)`, where `force = -d v - k x`;
* plant: `(z, force)` ↦ state derivative `(force / m, v)`.

The state is forwarded with the force because `AssumeGuarantee.sequential`
uses a wire from the first component's output to the second one's input.

The new proof identifies the composed *vector field* with `pointMassField`.
It reuses the pre-existing canonical operator-exponential flow and its
stability theorem. It does NOT verify numerical solvers, sampled controllers,
actuator limits, disturbances, moving references, or spacecraft hardware.
-/

namespace Ctrllib.ComControllerPlantComposition

open Ctrllib.AssumeGuarantee
open Filter Topology

/-- The controller forwards `(velocity, position error)` alongside its force. -/
abbrev AppliedForce := PointMassState × PointMassCoord

/-- Ideal feedback `f = -d v - k x`, with `z = (v, x)`. -/
noncomputable def controllerForce (d k : ℝ) (z : PointMassState) : PointMassCoord :=
  (-d) • z.1 + (-k) • z.2

/-- Ideal plant derivative `(v̇, ẋ) = (f/m, v)`; no actuation saturation. -/
noncomputable def plantDerivative (m : ℝ) (sf : AppliedForce) : PointMassState :=
  ((m⁻¹) • sf.2, sf.1.1)

/-- Relational controller: the output carries the unchanged state and force. -/
noncomputable def controllerRel (d k : ℝ) (z : PointMassState)
    (sf : AppliedForce) : Prop := sf = (z, controllerForce d k z)

/-- Relational ideal point-mass plant. -/
noncomputable def plantRel (m : ℝ) (sf : AppliedForce)
    (zdot : PointMassState) : Prop := zdot = plantDerivative m sf

/-- Controller contract: positive stiffness and damping, exact feedback. -/
noncomputable def controllerContract (d k : ℝ) :
    Contract PointMassState AppliedForce where
  assumption := fun _ => 0 < d ∧ 0 < k
  guarantee := controllerRel d k

/-- Plant contract: positive mass, ideal Newtonian acceleration. -/
noncomputable def plantContract (m : ℝ) :
    Contract AppliedForce PointMassState where
  assumption := fun _ => 0 < m
  guarantee := plantRel m

/-- Algebraic implementation satisfies the controller's guarantee. -/
theorem controller_satisfies (d k : ℝ) :
    Satisfies (controllerRel d k) (controllerContract d k) := by
  intro z sf _ h
  exact h

/-- Algebraic implementation satisfies the plant's guarantee. -/
theorem plant_satisfies (m : ℝ) :
    Satisfies (plantRel m) (plantContract m) := by
  intro sf zdot _ h
  exact h

/-- Controller has an output for each admissible input. -/
theorem controller_enabled (d k : ℝ) :
    Enabled (controllerRel d k) (controllerContract d k).assumption := by
  intro z _
  exact ⟨(z, controllerForce d k z), rfl⟩

/-- The ideal plant always supplies its uniquely defined derivative. -/
theorem plant_enabled (m : ℝ) :
    Enabled (plantRel m) (plantContract m).assumption := by
  intro sf _
  exact ⟨plantDerivative m sf, rfl⟩

/-- The external hypotheses needed by the two components. -/
def environment (m d k : ℝ) (_ : PointMassState) : Prop :=
  0 < m ∧ 0 < d ∧ 0 < k

/-- The environment supplies both contracts' assumptions, including wiring. -/
theorem environment_meets_sequential (m d k : ℝ) :
    ∀ z, environment m d k z →
      (sequential (controllerContract d k) (plantContract m)
        (fun sf : AppliedForce => sf)).assumption z := by
  apply sequential_assumption_of_environment
    (fun sf : AppliedForce => sf) (environment m d k)
  · intro z h
    exact ⟨h.2.1, h.2.2⟩
  · intro z sf h _
    exact h.1

/-- Two verified component contracts satisfy the sequential contract. -/
theorem composed_satisfies (m d k : ℝ) :
    Satisfies
      (connected (controllerRel d k) (plantRel m) (fun sf : AppliedForce => sf))
      (sequential (controllerContract d k) (plantContract m)
        (fun sf : AppliedForce => sf)) := by
  exact satisfies_sequential (fun sf : AppliedForce => sf)
    (controller_satisfies d k) (plant_satisfies m)

/-- The composite relation admits a derivative for each admissible state. -/
theorem composed_enabled (m d k : ℝ) :
    Enabled
      (connected (controllerRel d k) (plantRel m) (fun sf : AppliedForce => sf))
      (sequential (controllerContract d k) (plantContract m)
        (fun sf : AppliedForce => sf)).assumption := by
  exact enabled_sequential (fun sf : AppliedForce => sf)
    (controller_satisfies d k) (controller_enabled d k) (plant_enabled m)

/-- The connected controller and plant give the original point-mass field.
    This equality is algebraic; the environment enforces physical positivity. -/
theorem closedLoop_eq_pointMassField (m d k : ℝ) (z : PointMassState) :
    plantDerivative m (z, controllerForce d k z) = pointMassField m d k z := by
  apply Prod.ext
  · change (m⁻¹) • ((-d) • z.1 + (-k) • z.2) =
      (-(d / m)) • z.1 - (k / m) • z.2
    rw [smul_add, smul_smul, smul_smul]
    have hd : m⁻¹ * (-d) = -(d / m) := by
      rw [div_eq_mul_inv]
      ring
    have hk : m⁻¹ * (-k) = -(k / m) := by
      rw [div_eq_mul_inv]
      ring
    rw [hd, hk]
    simp only [sub_eq_add_neg, neg_smul]
  · rfl

/-- The connected relation has *exactly* the derivatives of the existing field. -/
theorem connected_iff_pointMassField (m d k : ℝ)
    (z zdot : PointMassState) :
    connected (controllerRel d k) (plantRel m) (fun sf : AppliedForce => sf)
      z zdot ↔ zdot = pointMassField m d k z := by
  constructor
  · rintro ⟨sf, hC, hP⟩
    change sf = (z, controllerForce d k z) at hC
    change zdot = plantDerivative m sf at hP
    subst sf
    simpa only [closedLoop_eq_pointMassField] using hP
  · intro h
    refine ⟨(z, controllerForce d k z), ?_, ?_⟩
    · rfl
    · change zdot = plantDerivative m (z, controllerForce d k z)
      simpa only [closedLoop_eq_pointMassField] using h

/-- The already-built canonical flow solves the *composed* controller/plant
    derivative, rather than merely a syntactically similar equation. -/
theorem canonicalFlow_solves_composed (m d k : ℝ) (hm : 0 < m)
    (z₀ : PointMassState) (t : ℝ) :
    HasDerivAt (fun s => pointMassFlow m d k hm s z₀)
      (plantDerivative m
        ((pointMassFlow m d k hm t z₀),
          controllerForce d k (pointMassFlow m d k hm t z₀))) t := by
  have h := pointMassFlow_hasDerivAt m d k hm z₀ t
  rw [pointMassCLM_apply] at h
  simpa only [closedLoop_eq_pointMassField] using h

/-- Reuses the established Lyapunov-stability and global-convergence result
    *for the canonical flow*. It does not assert a numerical realization. -/
theorem canonicalFlow_stability (m d k : ℝ)
    (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) :
    LyapStable (pointMassFlow m d k hm) ∧
      ∀ z₀, Tendsto (fun t : ℝ => pointMassFlow m d k hm t z₀) atTop (𝓝 0) := by
  exact pointMass_globally_asymptotically_stable m d k hm hd hk

end Ctrllib.ComControllerPlantComposition

#print axioms Ctrllib.ComControllerPlantComposition.connected_iff_pointMassField
#print axioms Ctrllib.ComControllerPlantComposition.canonicalFlow_stability
